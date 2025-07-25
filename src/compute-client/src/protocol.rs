// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

//! The compute protocol defines the communication between the compute controller and indiviual
//! compute replicas.
//!
//! # Overview
//!
//! The compute protocol consists of [`ComputeCommand`]s and [`ComputeResponse`]s.
//! [`ComputeCommand`]s are sent from the compute controller to the replicas and instruct the
//! receivers to perform some action. [`ComputeResponse`]s are sent in the opposite direction and
//! inform the receiver about status changes of their senders.
//!
//! The compute protocol is an asynchronous protocol. Both participants must expect and be able to
//! gracefully handle messages that don’t reflect the state of the world described by the messages
//! they have previously sent. In other words, messages sent take effect only eventually. For
//! example, after the compute controller has instructed the replica to cancel a peek (by sending a
//! [`CancelPeek`] command, it must still be ready to accept non-[`Canceled`] responses to the
//! peek. Similarly, if a replica receives a [`CancelPeek`] command for a peek it has already
//! answered, it must handle that command gracefully (e.g., by ignoring it).
//!
//! While the protocol does not provide any guarantees about the delay between sending a message
//! and it being received and processed, it does guarantee that messages are delivered in the same
//! order they are sent in. For example, if the compute controller sends a [`Peek`] command
//! followed by a [`CancelPeek`] command, it is guaranteed that [`CancelPeek`] is only received by
//! the replica after the [`Peek`] command.
//!
//! # Message Transport and Encoding
//!
//! To initiate communication, the replica starts listening on a known host and port, to which the
//! compute controller then connects. We use the gRPC framework for transmitting Protobuf-encoded
//! messages. The replica exposes a single gRPC service (`ProtoCompute`) which contains a single
//! RPC (`CommandResponseStream`). The compute controller invokes this RPC to finalize the
//! connection setup. After the streams have been established, compute commands and responses are
//! transmitted over these streams.
//!
//! # Protocol Stages
//!
//! The compute protocol consists of four stages that must be transitioned in order:
//!
//!   1. Creation
//!   2. Initialization
//!   3. Computation (read-only)
//!   4. Computation (read-write)
//!
//! ## Creation Stage
//!
//! The creation stage is the first stage of the compute protocol. It is initiated by the
//! successful establishment of a gRPC connection between compute controller and replica. In this
//! stage, the compute controller must send two creation commands in order:
//!
//!   1. A [`Hello`] command, which provides the replica with connection metadata.
//!   2. A [`CreateInstance`] command, which instructs the replica to initialize the rest of its
//!      state.
//!
//! The replica must not send any responses.
//!
//! ## Initialization Stage
//!
//! The initialization stage begins as soon as the compute controller has sent the
//! [`CreateInstance`] command. In this stage, the compute controller informs the replica about its
//! expected dataflow state. It does so by sending any number of [computation
//! commands](#computation-stage), followed by an [`InitializationComplete`] command, which marks
//! the end of the initialization stage.
//!
//! Upon receiving computation commands during the initialization phase, the replica is obligated
//! to ensure its state matches what is requested through the commands. It is up to the replica
//! whether it ensures that by initializing new state or by reusing existing state (through a
//! reconciliation process).
//!
//! The replica may send responses to computation commands it receives. It may also opt to defer
//! sending responses to the computation stages instead.
//!
//! ## Computation Stage (read-only)
//!
//! This computation stage begins as soon as the compute controller has sent the
//! [`InitializationComplete`] command. In this stage, the compute controller instructs the replica
//! to create and maintain dataflows, and to perform peeks on indexes exported by dataflows.
//!
//! While in the read-only computation stage, the replica must not affect
//! changes to external systems (writes). For the most part this means it cannot
//! write to persist. The replica can transition out of the read-only stage when
//! receiving an [`AllowWrites`] command.
//!
//! The compute controller may send any number of computation commands:
//!
//!   - [`CreateDataflow`]
//!   - [`Schedule`]
//!   - [`AllowCompaction`]
//!   - [`Peek`]
//!   - [`CancelPeek`]
//!   - [`UpdateConfiguration`]
//!
//! The compute controller must respect dependencies between commands. For example, it must send a
//! [`CreateDataflow`] command before it sends [`AllowCompaction`] or [`Peek`] commands that target
//! the created dataflow.
//!
//! The replica must send the required responses to computation commands. This includes commands it
//! has received in the initialization phase that have not already been responded to.
//!
//! ## Computation Stage (read-write)
//!
//! The read-write computation stage is exactly like the read-only computation stage, with the
//! addition that now the replica _can_ affect writes to external systems. This stage begins once
//! the controller has sent the [`AllowWrites`] command.
//!
//! The replica cannot transition back to the read-only computation stage from the read-write stage.
//!
//! [`ComputeCommand`]: self::command::ComputeCommand
//! [`Hello`]: self::command::ComputeCommand::Hello
//! [`CreateInstance`]: self::command::ComputeCommand::CreateInstance
//! [`InitializationComplete`]: self::command::ComputeCommand::InitializationComplete
//! [`CreateDataflow`]: self::command::ComputeCommand::CreateDataflow
//! [`Schedule`]: self::command::ComputeCommand::Schedule
//! [`AllowCompaction`]: self::command::ComputeCommand::AllowCompaction
//! [`AllowWrites`]: self::command::ComputeCommand::AllowWrites
//! [`Peek`]: self::command::ComputeCommand::Peek
//! [`CancelPeek`]: self::command::ComputeCommand::CancelPeek
//! [`UpdateConfiguration`]: self::command::ComputeCommand::UpdateConfiguration
//! [`ComputeResponse`]: self::response::ComputeResponse
//! [`Canceled`]: self::response::PeekResponse::Canceled
//! [`SubscribeResponse::DroppedAt`]: self::response::SubscribeResponse::DroppedAt

pub mod command;
pub mod history;
pub mod response;
