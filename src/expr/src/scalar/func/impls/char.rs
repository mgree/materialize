// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

use std::fmt;

use mz_lowertest::MzReflect;
use mz_repr::adt::char::{Char, CharLength, format_str_pad};
use mz_repr::{ColumnType, ScalarType};
use proptest_derive::Arbitrary;
use serde::{Deserialize, Serialize};

use crate::scalar::func::EagerUnaryFunc;

/// All Char data is stored in Datum::String with its blank padding removed
/// (i.e. trimmed), so this function provides a means of restoring any
/// removed padding.
#[derive(
    Arbitrary, Ord, PartialOrd, Clone, Debug, Eq, PartialEq, Serialize, Deserialize, Hash, MzReflect,
)]
pub struct PadChar {
    pub length: Option<CharLength>,
}

impl<'a> EagerUnaryFunc<'a> for PadChar {
    type Input = &'a str;
    type Output = Char<String>;

    fn call(&self, a: &'a str) -> Char<String> {
        Char(format_str_pad(a, self.length))
    }

    fn output_type(&self, input: ColumnType) -> ColumnType {
        ScalarType::Char {
            length: self.length,
        }
        .nullable(input.nullable)
    }
}

impl fmt::Display for PadChar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("padchar")
    }
}

// This function simply allows the expression of changing a's type from char to
// string
sqlfunc!(
    #[sqlname = "char_to_text"]
    #[preserves_uniqueness = true]
    #[inverse = to_unary!(super::CastStringToChar{
        length: None,
        fail_on_len: false,
    })]
    fn cast_char_to_string<'a>(a: Char<&'a str>) -> &'a str {
        a.0
    }
);
