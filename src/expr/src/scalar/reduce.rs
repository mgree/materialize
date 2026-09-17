// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

//! Rewrite-rule-driven simplification of `MirScalarExpr`.
//!
//! `reduce` repeatedly applies a fixed set of local rewrite rules to an
//! expression until reaching a fixed point. The per-variant rules live in
//! sibling modules (`unary`, `binary`, `variadic`, `if_then`); this file
//! owns the fixed-point loop, the pre/post-pass dispatch, and the folding of
//! whole constant subtrees.
//!
//! Rule order and the pre-/post-pass split are preserved across refactors,
//! since the sibling rules assume their predecessors have already fired.

use mz_repr::{ReprColumnType, RowArena};

use crate::scalar::func::UnaryFunc;
use crate::visit::Visit;
use crate::{Eval, MirScalarExpr};

mod binary;
mod if_then;
mod unary;
mod variadic;

/// Reduce `expr` to a simpler equivalent form by repeatedly applying local
/// rewrite rules until reaching a fixed point.
pub fn reduce(expr: &mut MirScalarExpr, column_types: &[ReprColumnType]) {
    let temp_storage = &RowArena::new();

    // Constness of the visited nodes whose parent is still pending, in
    // visitation order. A node's children are always the last entries.
    let mut constant: Vec<bool> = Vec::new();

    // Simplifications run in a loop until `expr` no longer changes.
    let mut old = MirScalarExpr::column(0);
    while old != *expr {
        old = expr.clone();
        expr.visit_mut_pre_post(
            &mut |e| {
                reduce_pre(e, column_types);
                None
            },
            &mut |e| reduce_post(e, column_types, temp_storage, &mut constant),
        );
        // The root has no parent to fold it, so it is folded here.
        let root_constant = constant.pop().expect("root was visited");
        debug_assert!(constant.is_empty());
        if root_constant && !expr.is_literal() {
            fold_constant(expr, column_types, temp_storage);
        }
    }
}

/// Replaces the constant expression `e` with the literal it evaluates to.
fn fold_constant(e: &mut MirScalarExpr, column_types: &[ReprColumnType], temp_storage: &RowArena) {
    *e = MirScalarExpr::literal(e.eval(&[], temp_storage), e.typ(column_types).scalar_type);
}

/// Pre-order rewrites, applied before children are visited.
///
/// `IsNull` and `Not` need to fire pre-order: if they push themselves inward
/// (e.g. `Not(Not(x)) → x`), the result is the new node at this position,
/// which the visitor will then descend into for normal post-order handling.
fn reduce_pre(e: &mut MirScalarExpr, column_types: &[ReprColumnType]) {
    match e {
        MirScalarExpr::CallUnary { func, expr } => match func {
            UnaryFunc::IsNull(_) => {
                if !expr.typ(column_types).nullable {
                    *e = MirScalarExpr::literal_false();
                } else if let Some(rewritten) = expr.decompose_is_null() {
                    // Try to at least decompose IsNull into a disjunction of
                    // simpler IsNull subexpressions.
                    *e = rewritten;
                }
            }
            UnaryFunc::Not(_) => match &mut **expr {
                // Push down not expressions
                // Two negates cancel each other out.
                MirScalarExpr::CallUnary {
                    expr: inner_expr,
                    func: UnaryFunc::Not(_),
                } => {
                    *e = inner_expr.take();
                }
                // Transforms `NOT(a <op> b)` to `a negate(<op>) b` if a
                // negation exists.
                MirScalarExpr::CallBinary {
                    expr1,
                    expr2,
                    func: bf,
                } => {
                    if let Some(negated) = bf.negate() {
                        *e = MirScalarExpr::CallBinary {
                            expr1: Box::new(expr1.take()),
                            expr2: Box::new(expr2.take()),
                            func: negated,
                        };
                    }
                }
                MirScalarExpr::CallVariadic { .. } => e.demorgans(),
                _ => {}
            },
            _ => {}
        },
        _ => {}
    }
}

/// Post-order rewrites, applied after children have been reduced.
///
/// A constant subtree (one that reads no column, calls no unmaterializable
/// function, and contains no `mz_panic`, which must reach runtime to fire) is
/// folded as a whole by evaluating it once, at the point where it meets its
/// non-constant parent. Folding node by node would pack each intermediate
/// value into a `Row`, and row packing canonicalizes numerics by trimming
/// trailing zeros. That discards the scale `AdjustNumericScale` established
/// before a scale-sensitive consumer such as the text cast sees it. Whole
/// evaluation matches runtime evaluation, so `1.5::numeric(5,2)::text` folds to
/// `'1.50'`. Constness travels upward on `constant`, which keeps the pass
/// linear in the size of the expression.
fn reduce_post(
    e: &mut MirScalarExpr,
    column_types: &[ReprColumnType],
    temp_storage: &RowArena,
    constant: &mut Vec<bool>,
) {
    let start = constant.len() - e.children().count();
    let is_constant = match e {
        MirScalarExpr::Literal(..) => true,
        MirScalarExpr::Column(..) | MirScalarExpr::CallUnmaterializable(_) => false,
        MirScalarExpr::CallUnary {
            func: UnaryFunc::Panic(_),
            ..
        } => false,
        _ => constant[start..].iter().all(|c| *c),
    };
    if !is_constant {
        // Each constant child is a maximal constant subtree.
        for (child, &child_constant) in e.children_mut().zip(&constant[start..]) {
            if child_constant && !child.is_literal() {
                fold_constant(child, column_types, temp_storage);
            }
        }
    }
    constant.truncate(start);

    // A constant node waits for its parent to fold it, or for `reduce` to fold
    // it as the root, so the per-node rules only run on non-constant nodes.
    if !is_constant {
        match e {
            MirScalarExpr::Column(_, _)
            | MirScalarExpr::Literal(_, _)
            | MirScalarExpr::CallUnmaterializable(_) => {}
            MirScalarExpr::CallUnary { .. } => {
                unary::reduce_call_unary(e, column_types, temp_storage)
            }
            MirScalarExpr::CallBinary { .. } => {
                binary::reduce_call_binary(e, column_types, temp_storage)
            }
            MirScalarExpr::CallVariadic { .. } => {
                variadic::reduce_call_variadic(e, column_types, temp_storage)
            }
            MirScalarExpr::If { .. } => if_then::reduce_if(e, column_types),
        }
    }
    // A rule may have rewritten a non-constant node into a literal. Any other
    // rewrite is conservatively kept non-constant; the fixed-point loop
    // revisits it.
    constant.push(is_constant || e.is_literal());
}

#[cfg(test)]
mod tests {
    use mz_repr::adt::numeric::NumericMaxScale;
    use mz_repr::{Datum, ReprScalarType, strconv};

    use crate::MirScalarExpr;
    use crate::scalar::func;

    #[mz_ore::test]
    fn numeric_scale_survives_constant_folding() {
        let scale = NumericMaxScale::try_from(2i64).unwrap();
        let one_point_five = strconv::parse_numeric("1.5").unwrap();
        let mut e =
            MirScalarExpr::literal_ok(Datum::Numeric(one_point_five), ReprScalarType::Numeric {})
                .call_unary(func::AdjustNumericScale(scale))
                .call_unary(func::CastNumericToString);
        e.reduce(&[]);
        assert_eq!(e.as_literal_str(), Some("1.50"));
    }

    #[mz_ore::test]
    fn constant_call_folds_but_column_call_stays() {
        let int32 = [ReprScalarType::Int32.nullable(false)];
        let mut e = MirScalarExpr::literal_ok(Datum::Int32(-1), ReprScalarType::Int32)
            .call_unary(func::NegInt32);
        e.reduce(&int32);
        assert_eq!(
            e,
            MirScalarExpr::literal_ok(Datum::Int32(1), ReprScalarType::Int32)
        );

        let mut e = MirScalarExpr::column(0).call_unary(func::NegInt32);
        e.reduce(&int32);
        assert_eq!(e, MirScalarExpr::column(0).call_unary(func::NegInt32));
    }
}
