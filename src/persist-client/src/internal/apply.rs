// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

//! Implementation of persist command application.

use std::collections::BTreeMap;
use std::fmt::Debug;
use std::ops::ControlFlow::{self, Break, Continue};
use std::sync::Arc;
use std::time::Instant;

use differential_dataflow::difference::Semigroup;
use differential_dataflow::lattice::Lattice;
use mz_ore::cast::CastFrom;
use mz_persist::location::{CaSResult, Indeterminate, SeqNo, VersionedData};
use mz_persist_types::schema::SchemaId;
use mz_persist_types::{Codec, Codec64};
use timely::progress::{Antichain, Timestamp};
use tracing::debug;

use crate::cache::{LockingTypedState, StateCache};
use crate::error::{CodecMismatch, InvalidUsage};
use crate::internal::gc::GcReq;
use crate::internal::maintenance::RoutineMaintenance;
use crate::internal::metrics::{CmdMetrics, Metrics, ShardMetrics};
use crate::internal::paths::{PartialRollupKey, RollupId};
use crate::internal::state::{
    ActiveGc, ActiveRollup, EncodedSchemas, ExpiryMetrics, GC_FALLBACK_THRESHOLD_MS,
    GC_MAX_VERSIONS, GC_MIN_VERSIONS, GC_USE_ACTIVE_GC, GcConfig, HollowBatch, LeasedReaderState,
    ROLLUP_FALLBACK_THRESHOLD_MS, ROLLUP_THRESHOLD, ROLLUP_USE_ACTIVE_ROLLUP, Since, SnapshotErr,
    StateCollections, TypedState, Upper,
};
use crate::internal::state_diff::StateDiff;
use crate::internal::state_versions::{EncodedRollup, StateVersions};
use crate::internal::trace::FueledMergeReq;
use crate::internal::watch::StateWatch;
use crate::read::LeasedReaderId;
use crate::rpc::{PUBSUB_PUSH_DIFF_ENABLED, PubSubSender};
use crate::schema::SchemaCache;
use crate::{Diagnostics, PersistConfig, ShardId};

/// An applier of persist commands.
///
/// This struct exists mainly to allow us to very narrowly bound the surface
/// area that directly interacts with state.
#[derive(Debug)]
pub struct Applier<K, V, T, D> {
    pub(crate) cfg: PersistConfig,
    pub(crate) metrics: Arc<Metrics>,
    pub(crate) shard_metrics: Arc<ShardMetrics>,
    pub(crate) state_versions: Arc<StateVersions>,
    shared_states: Arc<StateCache>,
    pubsub_sender: Arc<dyn PubSubSender>,
    pub(crate) shard_id: ShardId,

    // Access to the shard's state, shared across all handles created by the same
    // PersistClientCache. The state is wrapped in LockingTypedState, disallowing
    // access across await points. Access should be always be kept brief, and it
    // is expected that other handles may advance the state at any time this Applier
    // is not holding the lock.
    //
    // NB: This is very intentionally not pub(crate) so that it's easy to reason
    //     very locally about the duration of locks.
    state: Arc<LockingTypedState<K, V, T, D>>,
}

// Impl Clone regardless of the type params.
impl<K, V, T: Clone, D> Clone for Applier<K, V, T, D> {
    fn clone(&self) -> Self {
        Self {
            cfg: self.cfg.clone(),
            metrics: Arc::clone(&self.metrics),
            shard_metrics: Arc::clone(&self.shard_metrics),
            state_versions: Arc::clone(&self.state_versions),
            shared_states: Arc::clone(&self.shared_states),
            pubsub_sender: Arc::clone(&self.pubsub_sender),
            shard_id: self.shard_id,
            state: Arc::clone(&self.state),
        }
    }
}

impl<K, V, T, D> Applier<K, V, T, D>
where
    K: Debug + Codec,
    V: Debug + Codec,
    T: Timestamp + Lattice + Codec64 + Sync,
    D: Semigroup + Codec64,
{
    pub async fn new(
        cfg: PersistConfig,
        shard_id: ShardId,
        metrics: Arc<Metrics>,
        state_versions: Arc<StateVersions>,
        shared_states: Arc<StateCache>,
        pubsub_sender: Arc<dyn PubSubSender>,
        diagnostics: Diagnostics,
    ) -> Result<Self, Box<CodecMismatch>> {
        let shard_metrics = metrics.shards.shard(&shard_id, &diagnostics.shard_name);
        let state = shared_states
            .get::<K, V, T, D, _, _>(
                shard_id,
                || {
                    metrics.cmds.init_state.run_cmd(&shard_metrics, || {
                        state_versions.maybe_init_shard(&shard_metrics)
                    })
                },
                &diagnostics,
            )
            .await?;
        let ret = Applier {
            cfg,
            metrics,
            shard_metrics,
            state_versions,
            shared_states,
            pubsub_sender,
            shard_id,
            state,
        };
        Ok(ret)
    }

    /// Returns a new [StateWatch] for changes to this Applier's State.
    pub fn watch(&self) -> StateWatch<K, V, T, D> {
        StateWatch::new(Arc::clone(&self.state), Arc::clone(&self.metrics))
    }

    /// Fetches the latest state from Consensus and passes its `upper` to the provided closure.
    pub async fn fetch_upper<R, F: FnMut(&Antichain<T>) -> R>(&self, mut f: F) -> R {
        self.metrics.cmds.fetch_upper_count.inc();
        self.fetch_and_update_state(None).await;
        self.upper(|_seqno, upper| f(upper))
    }

    /// A point-in-time read/clone of `upper` from the current state.
    ///
    /// Due to sharing state with other handles, successive reads to this fn or any other may
    /// see a different version of state, even if this Applier has not explicitly fetched and
    /// updated to the latest state. Successive calls will always return values such that
    /// `PartialOrder::less_equal(call1, call2)` hold true.
    pub fn clone_upper(&self) -> Antichain<T> {
        self.upper(|_seqno, upper| upper.clone())
    }

    pub(crate) fn upper<R, F: FnMut(SeqNo, &Antichain<T>) -> R>(&self, mut f: F) -> R {
        self.state
            .read_lock(&self.metrics.locks.applier_read_cacheable, move |state| {
                f(state.seqno, state.upper())
            })
    }

    pub(crate) fn schemas<R>(
        &self,
        mut f: impl FnMut(SeqNo, &BTreeMap<SchemaId, EncodedSchemas>) -> R,
    ) -> R {
        self.state
            .read_lock(&self.metrics.locks.applier_read_cacheable, move |state| {
                f(state.seqno, &state.collections.schemas)
            })
    }

    pub(crate) fn schema_cache(&self) -> SchemaCache<K, V, T, D> {
        SchemaCache::new(self.state.schema_cache(), self.clone())
    }

    /// A point-in-time read of `since` from the current state.
    ///
    /// Due to sharing state with other handles, successive reads to this fn or any other may
    /// see a different version of state, even if this Applier has not explicitly fetched and
    /// updated to the latest state. Successive calls will always return values such that
    /// `PartialOrder::less_equal(call1, call2)` hold true.
    #[cfg(test)]
    pub fn since(&self) -> Antichain<T> {
        self.state
            .read_lock(&self.metrics.locks.applier_read_cacheable, |state| {
                state.since().clone()
            })
    }

    /// Does a lease for the provided reader exist in the current state?
    ///
    /// This is useful when we encounter a condition that should only be possible when the lease
    /// has expired, so we can distinguish between scary bugs and expected-but-unusual cases.
    /// This returns whatever lease is present in the latest version of state - so to avoid false
    /// positives, this should be checked only after the surprising condition has occurred.
    pub fn reader_lease(&self, id: LeasedReaderId) -> Option<LeasedReaderState<T>> {
        self.state
            .read_lock(&self.metrics.locks.applier_read_cacheable, |state| {
                state.state.collections.leased_readers.get(&id).cloned()
            })
    }

    /// A point-in-time read of `seqno` from the current state.
    ///
    /// Due to sharing state with other handles, successive reads to this fn or any other may
    /// see a different version of state, even if this Applier has not explicitly fetched and
    /// updated to the latest state. Successive calls will always return values such that
    /// `call1 <= call2` hold true.
    pub fn seqno(&self) -> SeqNo {
        self.state
            .read_lock(&self.metrics.locks.applier_read_cacheable, |state| {
                state.seqno
            })
    }

    /// A point-in-time read of `seqno_since` from the current state.
    ///
    /// Due to sharing state with other handles, successive reads to this fn or any other may
    /// see a different version of state, even if this Applier has not explicitly fetched and
    /// updated to the latest state. Successive calls will always return values such that
    /// `call1 <= call2` hold true.
    pub fn seqno_since(&self) -> SeqNo {
        self.state
            .read_lock(&self.metrics.locks.applier_read_cacheable, |state| {
                state.seqno_since()
            })
    }

    /// A point-in-time read from the current state. (We declare a shard 'finalized' if it's
    /// both become an unreadable tombstone and the state itself is has been emptied out.)
    ///
    /// Due to sharing state with other handles, successive reads to this fn or any other may
    /// see a different version of state, even if this Applier has not explicitly fetched and
    /// updated to the latest state. Once this fn returns true, it will always return true.
    pub fn is_finalized(&self) -> bool {
        self.state
            .read_lock(&self.metrics.locks.applier_read_cacheable, |state| {
                state.collections.is_tombstone() && state.collections.is_single_empty_batch()
            })
    }

    /// See [crate::PersistClient::get_schema].
    pub fn get_schema(&self, schema_id: SchemaId) -> Option<(K::Schema, V::Schema)> {
        self.state
            .read_lock(&self.metrics.locks.applier_read_cacheable, |state| {
                let x = state.collections.schemas.get(&schema_id)?;
                Some((K::decode_schema(&x.key), V::decode_schema(&x.val)))
            })
    }

    /// See [crate::PersistClient::latest_schema].
    pub fn latest_schema(&self) -> Option<(SchemaId, K::Schema, V::Schema)> {
        self.state
            .read_lock(&self.metrics.locks.applier_read_cacheable, |state| {
                let (id, x) = state.collections.schemas.last_key_value()?;
                Some((*id, K::decode_schema(&x.key), V::decode_schema(&x.val)))
            })
    }

    /// Returns whether the current's state `since` and `upper` are both empty.
    ///
    /// Due to sharing state with other handles, successive reads to this fn or any other may
    /// see a different version of state, even if this Applier has not explicitly fetched and
    /// updated to the latest state. Once this fn returns true, it will always return true.
    pub fn check_since_upper_both_empty(&self) -> Result<(), InvalidUsage<T>> {
        self.state
            .read_lock(&self.metrics.locks.applier_read_cacheable, |state| {
                if state.since().is_empty() && state.upper().is_empty() {
                    Ok(())
                } else {
                    Err(InvalidUsage::FinalizationError {
                        since: state.since().clone(),
                        upper: state.upper().clone(),
                    })
                }
            })
    }

    /// Returns all rollups that are <= the given `seqno`.
    ///
    /// Due to sharing state with other handles, successive reads to this fn or any other may
    /// see a different version of state, even if this Applier has not explicitly fetched and
    /// updated to the latest state.
    pub fn rollups_lte_seqno(&self, seqno: SeqNo) -> Vec<(SeqNo, PartialRollupKey)> {
        self.state
            .read_lock(&self.metrics.locks.applier_read_noncacheable, |state| {
                state
                    .collections
                    .rollups
                    .range(..=seqno)
                    .map(|(seqno, rollup)| (*seqno, rollup.key.clone()))
                    .collect::<Vec<(SeqNo, PartialRollupKey)>>()
            })
    }

    pub fn all_fueled_merge_reqs(&self) -> Vec<FueledMergeReq<T>> {
        self.state
            .read_lock(&self.metrics.locks.applier_read_noncacheable, |state| {
                state
                    .collections
                    .trace
                    .fueled_merge_reqs_before_ms(u64::MAX, None)
                    .collect()
            })
    }

    pub fn snapshot(&self, as_of: &Antichain<T>) -> Result<Vec<HollowBatch<T>>, SnapshotErr<T>> {
        self.state
            .read_lock(&self.metrics.locks.applier_read_noncacheable, |state| {
                state.snapshot(as_of)
            })
    }

    pub fn all_batches(&self) -> Vec<HollowBatch<T>> {
        self.state
            .read_lock(&self.metrics.locks.applier_read_noncacheable, |state| {
                state.state.collections.trace.batches().cloned().collect()
            })
    }

    pub fn verify_listen(&self, as_of: &Antichain<T>) -> Result<Result<(), Upper<T>>, Since<T>> {
        self.state
            .read_lock(&self.metrics.locks.applier_read_noncacheable, |state| {
                state.verify_listen(as_of)
            })
    }

    pub fn next_listen_batch(&self, frontier: &Antichain<T>) -> Result<HollowBatch<T>, SeqNo> {
        self.state
            .read_lock(&self.metrics.locks.applier_read_noncacheable, |state| {
                state.next_listen_batch(frontier)
            })
    }

    pub async fn write_rollup_for_state(&self) -> Option<EncodedRollup> {
        let state = self
            .state
            .read_lock(&self.metrics.locks.applier_read_noncacheable, |state| {
                state.clone_for_rollup()
            });

        self.state_versions
            .write_rollup_for_state(self.shard_metrics.as_ref(), state, &RollupId::new())
            .await
    }

    pub async fn apply_unbatched_cmd<
        R,
        E,
        WorkFn: FnMut(SeqNo, &PersistConfig, &mut StateCollections<T>) -> ControlFlow<E, R>,
    >(
        &self,
        cmd: &CmdMetrics,
        mut work_fn: WorkFn,
    ) -> Result<(SeqNo, Result<R, E>, RoutineMaintenance), Indeterminate> {
        loop {
            cmd.started.inc();
            let now = Instant::now();
            let ret = Self::apply_unbatched_cmd_locked(
                &self.state,
                cmd,
                &mut work_fn,
                &self.cfg,
                &self.metrics,
                &self.shard_metrics,
                &self.state_versions,
            )
            .await;
            cmd.seconds.inc_by(now.elapsed().as_secs_f64());

            match ret {
                ApplyCmdResult::Committed((diff, new_state, res, maintenance)) => {
                    cmd.succeeded.inc();
                    self.shard_metrics.cmd_succeeded.inc();
                    self.update_state(new_state);
                    if PUBSUB_PUSH_DIFF_ENABLED.get(&self.cfg) {
                        self.pubsub_sender.push_diff(&self.shard_id, &diff);
                    }
                    return Ok((diff.seqno, Ok(res), maintenance));
                }
                ApplyCmdResult::SkippedStateTransition((seqno, err, maintenance)) => {
                    cmd.succeeded.inc();
                    self.shard_metrics.cmd_succeeded.inc();
                    return Ok((seqno, Err(err), maintenance));
                }
                ApplyCmdResult::Indeterminate(err) => {
                    cmd.failed.inc();
                    return Err(err);
                }
                ApplyCmdResult::ExpectationMismatch(seqno) => {
                    cmd.cas_mismatch.inc();
                    self.fetch_and_update_state(Some(seqno)).await;
                }
            }
        }
    }

    // work_fn fails to compile without mut, false positive
    #[allow(clippy::needless_pass_by_ref_mut)]
    async fn apply_unbatched_cmd_locked<
        R,
        E,
        WorkFn: FnMut(SeqNo, &PersistConfig, &mut StateCollections<T>) -> ControlFlow<E, R>,
    >(
        state: &LockingTypedState<K, V, T, D>,
        cmd: &CmdMetrics,
        work_fn: &mut WorkFn,
        cfg: &PersistConfig,
        metrics: &Metrics,
        shard_metrics: &ShardMetrics,
        state_versions: &StateVersions,
    ) -> ApplyCmdResult<K, V, T, D, R, E> {
        let computed_next_state = state
            .read_lock(&metrics.locks.applier_read_noncacheable, |state| {
                Self::compute_next_state_locked(state, work_fn, metrics, cmd, cfg)
            });

        let next_state = match computed_next_state {
            Ok(x) => x,
            Err((seqno, err)) => {
                return ApplyCmdResult::SkippedStateTransition((
                    seqno,
                    err,
                    RoutineMaintenance::default(),
                ));
            }
        };

        let NextState {
            expected,
            diff,
            state,
            expiry_metrics,
            garbage_collection,
            write_rollup,
            work_ret,
        } = next_state;

        // SUBTLE! Unlike the other consensus and blob uses, we can't
        // automatically retry indeterminate ExternalErrors here. However,
        // if the state change itself is _idempotent_, then we're free to
        // retry even indeterminate errors. See
        // [Self::apply_unbatched_idempotent_cmd].
        let cas_res = state_versions
            .try_compare_and_set_current(&cmd.name, shard_metrics, Some(expected), &state, &diff)
            .await;

        match cas_res {
            Ok((CaSResult::Committed, diff)) => {
                assert!(
                    expected <= state.seqno,
                    "state seqno regressed: {} vs {}",
                    expected,
                    state.seqno
                );

                metrics
                    .lease
                    .timeout_read
                    .inc_by(u64::cast_from(expiry_metrics.readers_expired));

                metrics
                    .state
                    .writer_removed
                    .inc_by(u64::cast_from(expiry_metrics.writers_expired));

                if let Some(gc) = garbage_collection.as_ref() {
                    debug!("Assigned gc request: {:?}", gc);
                }

                let maintenance = RoutineMaintenance {
                    garbage_collection,
                    write_rollup,
                };

                ApplyCmdResult::Committed((diff, state, work_ret, maintenance))
            }
            Ok((CaSResult::ExpectationMismatch, _diff)) => {
                ApplyCmdResult::ExpectationMismatch(expected)
            }
            Err(err) => ApplyCmdResult::Indeterminate(err),
        }
    }

    fn compute_next_state_locked<
        R,
        E,
        WorkFn: FnMut(SeqNo, &PersistConfig, &mut StateCollections<T>) -> ControlFlow<E, R>,
    >(
        state: &TypedState<K, V, T, D>,
        work_fn: &mut WorkFn,
        metrics: &Metrics,
        cmd: &CmdMetrics,
        cfg: &PersistConfig,
    ) -> Result<NextState<K, V, T, D, R>, (SeqNo, E)> {
        let is_write = cmd.name == metrics.cmds.compare_and_append.name;
        let is_rollup = cmd.name == metrics.cmds.add_rollup.name;
        let is_become_tombstone = cmd.name == metrics.cmds.become_tombstone.name;

        let gc_config = GcConfig {
            use_active_gc: GC_USE_ACTIVE_GC.get(cfg),
            fallback_threshold_ms: u64::cast_from(GC_FALLBACK_THRESHOLD_MS.get(cfg)),
            min_versions: GC_MIN_VERSIONS.get(cfg),
            max_versions: GC_MAX_VERSIONS.get(cfg),
        };

        let use_active_rollup = ROLLUP_USE_ACTIVE_ROLLUP.get(cfg);
        let rollup_threshold = ROLLUP_THRESHOLD.get(cfg);
        let rollup_fallback_threshold_ms = u64::cast_from(ROLLUP_FALLBACK_THRESHOLD_MS.get(cfg));

        let expected = state.seqno;
        let was_tombstone_before = state.collections.is_tombstone();

        let (work_ret, mut new_state) = match state.clone_apply(cfg, work_fn) {
            Continue(x) => x,
            Break(err) => {
                return Err((expected, err));
            }
        };
        let expiry_metrics = new_state.expire_at((cfg.now)());
        new_state.state.collections.trace.roundtrip_structure = true;

        // Sanity check that all state transitions have special case for
        // being a tombstone. The ones that do will return a Break and
        // return out of this method above. The one exception is adding
        // a rollup, because we want to be able to add a rollup for the
        // tombstone state.
        //
        // TODO: Even better would be to write the rollup in the
        // tombstone transition so it's a single terminal state
        // transition, but it'll be tricky to get right.
        if was_tombstone_before && !(is_rollup || is_become_tombstone) {
            panic!(
                "cmd {} unexpectedly tried to commit a new state on a tombstone: {:?}",
                cmd.name, state
            );
        }

        let now = (cfg.now)();
        let write_rollup = new_state.need_rollup(
            rollup_threshold,
            use_active_rollup,
            rollup_fallback_threshold_ms,
            now,
        );

        if let Some(write_rollup_seqno) = write_rollup {
            if use_active_rollup {
                new_state.collections.active_rollup = Some(ActiveRollup {
                    seqno: write_rollup_seqno,
                    start_ms: now,
                });
            }
        }

        // Find out if this command has been selected to perform gc, so
        // that it will fire off a background request to the
        // GarbageCollector to delete eligible blobs and truncate the
        // state history. This is dependant both on `maybe_gc` returning
        // Some _and_ on this state being successfully compare_and_set.
        let garbage_collection = new_state.maybe_gc(is_write, now, gc_config);

        if let Some(gc) = garbage_collection.as_ref() {
            if gc_config.use_active_gc {
                new_state.collections.active_gc = Some(ActiveGc {
                    seqno: gc.new_seqno_since,
                    start_ms: now,
                });
            }
        }

        // Make sure `new_state` is not modified after this point!
        // The new state and the diff must be consistent with each other for correctness.
        let diff = StateDiff::from_diff(&state.state, &new_state);
        // Sanity check that our diff logic roundtrips and adds back up
        // correctly.
        #[cfg(any(test, debug_assertions))]
        {
            if let Err(err) = StateDiff::validate_roundtrip(metrics, state, &diff, &new_state) {
                panic!("validate_roundtrips failed: {}", err);
            }
        }

        Ok(NextState {
            expected,
            diff,
            state: new_state,
            expiry_metrics,
            garbage_collection,
            write_rollup,
            work_ret,
        })
    }

    pub fn update_state(&self, new_state: TypedState<K, V, T, D>) {
        let (seqno_before, seqno_after) =
            self.state
                .write_lock(&self.metrics.locks.applier_write, |state| {
                    let seqno_before = state.seqno;
                    if seqno_before < new_state.seqno {
                        *state = new_state;
                    }
                    let seqno_after = state.seqno;
                    (seqno_before, seqno_after)
                });

        assert!(
            seqno_before <= seqno_after,
            "state seqno regressed: {} vs {}",
            seqno_before,
            seqno_after
        );
    }

    /// Fetches and updates to the latest state. Uses an optional hint to early-out if
    /// any more recent version of state is observed (e.g. updated by another handle),
    /// without making any calls to Consensus or Blob.
    pub async fn fetch_and_update_state(&self, seqno_hint: Option<SeqNo>) {
        let current_seqno = self.seqno();
        let seqno_before = match seqno_hint {
            None => current_seqno,
            Some(hint) => {
                // state is already more recent than our hint due to
                // advancement by another handle to the same shard.
                if hint < current_seqno {
                    self.metrics.state.update_state_noop_path.inc();
                    return;
                }
                current_seqno
            }
        };

        let diffs_to_current = self
            .state_versions
            .fetch_all_live_diffs_gt_seqno::<K, V, T, D>(&self.shard_id, seqno_before)
            .await;

        // no new diffs past our current seqno, nothing to do
        if diffs_to_current.is_empty() {
            self.metrics.state.update_state_empty_path.inc();
            return;
        }

        let new_seqno = self
            .state
            .write_lock(&self.metrics.locks.applier_write, |state| {
                state.apply_encoded_diffs(&self.cfg, &self.metrics, &diffs_to_current);
                state.seqno
            });

        assert!(
            seqno_before <= new_seqno,
            "state seqno regressed: {} vs {}",
            seqno_before,
            new_seqno
        );

        // whether the seqno advanced from diffs and/or because another handle
        // already updated it, we can assume it is now up-to-date
        if seqno_before < new_seqno {
            self.metrics.state.update_state_fast_path.inc();
            return;
        }

        // our state is so old there aren't any diffs we can use to
        // catch up directly. fall back to fully refetching state.
        // we can reuse the recent diffs we already have as a hint.
        let new_state = self
            .state_versions
            .fetch_current_state(&self.shard_id, diffs_to_current)
            .await
            .check_codecs::<K, V, D>(&self.shard_id)
            .expect("shard codecs should not change");

        let new_seqno = self
            .state
            .write_lock(&self.metrics.locks.applier_write, |state| {
                if state.seqno < new_state.seqno {
                    *state = new_state;
                }
                state.seqno
            });

        self.metrics.state.update_state_slow_path.inc();
        assert!(
            seqno_before <= new_seqno,
            "state seqno regressed: {} vs {}",
            seqno_before,
            new_seqno
        );
    }
}

enum ApplyCmdResult<K, V, T, D, R, E> {
    Committed((VersionedData, TypedState<K, V, T, D>, R, RoutineMaintenance)),
    SkippedStateTransition((SeqNo, E, RoutineMaintenance)),
    Indeterminate(Indeterminate),
    ExpectationMismatch(SeqNo),
}

struct NextState<K, V, T, D, R> {
    expected: SeqNo,
    diff: StateDiff<T>,
    state: TypedState<K, V, T, D>,
    expiry_metrics: ExpiryMetrics,
    write_rollup: Option<SeqNo>,
    garbage_collection: Option<GcReq>,
    work_ret: R,
}
