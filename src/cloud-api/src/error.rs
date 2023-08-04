// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

//! This module defines custom error types and structs related to the Materialize cloud API.
//!
//! [`ApiError`] is an error struct that represents an error returned by the
//! Materialize cloud API. It contains information about the HTTP status code and
//! a vector of error messages.
//!
//! [`Error`](`enum@Error`) is a custom error type
//!
//! It contains three variants:
//! * [`Error::Transport`]: indicates a transport error from the `reqwest`
//!   crate during a network request.
//! * [`Error::Api`]: indicates a Materialize cloud API error while
//!   processing the request.
//! * [`Error::EmptyRegion`]: indicates an error when no region is
//!   available in a requested cloud region.
//! * [`Error::CloudProviderRegionParseError`]: indicates an error trying to parse
//!   a cloud provider region. Always make sure the string is correctly formatted.

use std::fmt;

use reqwest::StatusCode;
use thiserror::Error;
use url::ParseError;

/// An error returned by the Materialize cloud API.
#[derive(Debug, Clone)]
pub struct ApiError {
    /// The HTTP status code.
    pub status_code: StatusCode,
    /// A detailed message about the error conditions.
    pub messages: Vec<String>,
}

impl fmt::Display for ApiError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} (status {})",
            self.messages.join(","),
            self.status_code
        )
    }
}

impl std::error::Error for ApiError {}

/// A custom error type containing all the possible errors in the crate for the Materialize cloud API.
#[derive(Error, Debug)]
pub enum Error {
    /// Indicates a transport error from the `reqwest`
    /// crate during a network request.
    #[error("Network error during a Materialize cloud API request: {0}")]
    Transport(#[from] reqwest::Error),
    /// Indicates a Materialize cloud API error from a request.
    #[error("API error during a Materialize cloud API request: {0}")]
    Api(#[from] ApiError),
    /// Indicates a Materialize admin error from a request.
    #[error("API error during a Materialize cloud API request: {0}")]
    AdminApi(#[from] mz_frontegg_client::error::Error),
    /// Indicates an error when no customer region is
    /// available in a requested region.
    #[error("No region available in this cloud region.")]
    EmptyRegion,
    /// Indicates an error trying to parse a
    /// cloud provider region.
    /// Always make sure the string is correctly formatted.
    #[error("Error parsing cloud provider.")]
    CloudProviderRegionParseError,
    /// Indicates an error when trying to retrieve the
    /// domain from the client endpoint
    #[error("Failed to retrieve domain from client endpoint.")]
    InvalidEndpointDomain,
    /// Indicates a Materialize cloud API error from a request.
    #[error("Error trying to parse the url: {0}")]
    UrlParseError(#[from] ParseError),
    /// Indicates the URL is cannot-be-a-base.
    #[error("Error while manipulating URL. The URL is cannot-be-a-base.")]
    UrlBaseError,
    /// Indicates that a timeout has been reached.
    #[error("Timeout reached.")]
    TimeoutError,
    /// Indicates that the request was executed successfully but returns no content (204).
    /// E.g.: It happens when trying to request information from a not enabled region.
    #[error("Succesfull but no content.")]
    SuccesfullButNoContent,
}
