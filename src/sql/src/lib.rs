// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

// BEGIN LINT CONFIG
// DO NOT EDIT. Automatically generated by bin/gen-lints.
// Have complaints about the noise? See the note in misc/python/materialize/cli/gen-lints.py first.
#![allow(unknown_lints)]
#![allow(clippy::style)]
#![allow(clippy::complexity)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::mutable_key_type)]
#![allow(clippy::stable_sort_primitive)]
#![allow(clippy::map_entry)]
#![allow(clippy::box_default)]
#![allow(clippy::drain_collect)]
#![warn(clippy::bool_comparison)]
#![warn(clippy::clone_on_ref_ptr)]
#![warn(clippy::no_effect)]
#![warn(clippy::unnecessary_unwrap)]
#![warn(clippy::dbg_macro)]
#![warn(clippy::todo)]
#![warn(clippy::wildcard_dependencies)]
#![warn(clippy::zero_prefixed_literal)]
#![warn(clippy::borrowed_box)]
#![warn(clippy::deref_addrof)]
#![warn(clippy::double_must_use)]
#![warn(clippy::double_parens)]
#![warn(clippy::extra_unused_lifetimes)]
#![warn(clippy::needless_borrow)]
#![warn(clippy::needless_question_mark)]
#![warn(clippy::needless_return)]
#![warn(clippy::redundant_pattern)]
#![warn(clippy::redundant_slicing)]
#![warn(clippy::redundant_static_lifetimes)]
#![warn(clippy::single_component_path_imports)]
#![warn(clippy::unnecessary_cast)]
#![warn(clippy::useless_asref)]
#![warn(clippy::useless_conversion)]
#![warn(clippy::builtin_type_shadow)]
#![warn(clippy::duplicate_underscore_argument)]
#![warn(clippy::double_neg)]
#![warn(clippy::unnecessary_mut_passed)]
#![warn(clippy::wildcard_in_or_patterns)]
#![warn(clippy::crosspointer_transmute)]
#![warn(clippy::excessive_precision)]
#![warn(clippy::overflow_check_conditional)]
#![warn(clippy::as_conversions)]
#![warn(clippy::match_overlapping_arm)]
#![warn(clippy::zero_divided_by_zero)]
#![warn(clippy::must_use_unit)]
#![warn(clippy::suspicious_assignment_formatting)]
#![warn(clippy::suspicious_else_formatting)]
#![warn(clippy::suspicious_unary_op_formatting)]
#![warn(clippy::mut_mutex_lock)]
#![warn(clippy::print_literal)]
#![warn(clippy::same_item_push)]
#![warn(clippy::useless_format)]
#![warn(clippy::write_literal)]
#![warn(clippy::redundant_closure)]
#![warn(clippy::redundant_closure_call)]
#![warn(clippy::unnecessary_lazy_evaluations)]
#![warn(clippy::partialeq_ne_impl)]
#![warn(clippy::redundant_field_names)]
#![warn(clippy::transmutes_expressible_as_ptr_casts)]
#![warn(clippy::unused_async)]
#![warn(clippy::disallowed_methods)]
#![warn(clippy::disallowed_macros)]
#![warn(clippy::disallowed_types)]
#![warn(clippy::from_over_into)]
// END LINT CONFIG

//! SQL-dataflow translation.
//!
//! There are two main parts of the SQL–dataflow translation process:
//!
//!   * **Purification** eliminates any external state from a SQL AST. It is an
//!     asynchronous process that may make network calls to external services.
//!     The input and output of purification is a SQL AST.
//!
//!   * **Planning** converts a purified AST to a [`Plan`], which describes an
//!     action that the system should take to effect the results of the query.
//!     Planning is a fast, pure function that always produces the same plan for
//!     a given input.
//!
//! # Details
//!
//! The purification step is, to our knowledge, unique to Materialize. In other
//! SQL databases, there is no concept of purifying a statement before planning
//! it. The reason for this difference is that in Materialize SQL statements can
//! depend on external state: local files, Confluent Schema Registries, etc.
//!
//! Presently only `CREATE SOURCE` statements can depend on external state,
//! though this could change in the future. Consider, for example:
//!
//! ```sql
//! CREATE SOURCE ... FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY 'http://csr:8081'
//! ```
//!
//! The shape of the created source is dependent on the Avro schema that is
//! stored in the schema registry running at `csr:8081`.
//!
//! This is problematic, because we need planning to be a pure function of its
//! input. Why?
//!
//!   * Planning locks the catalog while it operates. Therefore it needs to be
//!     fast, because only one SQL query can be planned at a time. Depending on
//!     external state while holding a lock on the catalog would be seriously
//!     detrimental to the latency of other queries running on the system.
//!
//!   * The catalog persists SQL ASTs across restarts of Materialize. If those
//!     ASTs depend on external state, then changes to that external state could
//!     corrupt Materialize's catalog.
//!
//! Purification is the escape hatch. It is a transformation from SQL AST to SQL
//! AST that "inlines" any external state. For example, we purify the schema
//! above by fetching the schema from the schema registry and inlining it.
//!
//! ```sql
//! CREATE SOURCE ... FORMAT AVRO USING SCHEMA '{"name": "foo", "fields": [...]}'
//! ```
//!
//! Importantly, purification cannot hold its reference to the catalog across an
//! await point. That means it can run in its own Tokio task so that it does not
//! block any other SQL commands on the server.
//!
//! [`Plan`]: crate::plan::Plan

#![warn(missing_debug_implementations)]

macro_rules! bail_unsupported {
    ($feature:expr) => {
        return Err(crate::plan::error::PlanError::Unsupported {
            feature: $feature.to_string(),
            issue_no: None,
        }
        .into())
    };
    ($issue:expr, $feature:expr) => {
        return Err(crate::plan::error::PlanError::Unsupported {
            feature: $feature.to_string(),
            issue_no: Some($issue),
        }
        .into())
    };
}

macro_rules! bail_never_supported {
    ($feature:expr, $docs:expr, $details:expr) => {
        return Err(crate::plan::error::PlanError::NeverSupported {
            feature: $feature.to_string(),
            documentation_link: Some($docs.to_string()),
            details: Some($details.to_string()),
        }
        .into())
    };
    ($feature:expr, $docs:expr) => {
        return Err(crate::plan::error::PlanError::NeverSupported {
            feature: $feature.to_string(),
            documentation_link: Some($docs.to_string()),
            details: None,
        }
        .into())
    };
    ($feature:expr) => {
        return Err(crate::plan::error::PlanError::NeverSupported {
            feature: $feature.to_string(),
            documentation_link: None,
            details: None,
        }
        .into())
    };
}

// TODO(benesch): delete these macros once we use structured errors everywhere.
macro_rules! sql_bail {
    ($($e:expr),* $(,)?) => {
        return Err(sql_err!($($e),*))
    }
}
macro_rules! sql_err {
    ($($e:expr),* $(,)?) => {
        crate::plan::error::PlanError::Unstructured(format!($($e),*))
    }
}

pub const DEFAULT_SCHEMA: &str = "public";

/// The number of concurrent requests we allow at once for webhook sources.
pub const WEBHOOK_CONCURRENCY_LIMIT: usize = 250;

pub mod ast;
pub mod catalog;
pub mod func;
pub mod kafka_util;
pub mod names;
#[macro_use]
pub mod normalize;
pub mod parse;
pub mod plan;
pub mod pure;
pub mod rbac;
pub mod session;
