= Simplifying assumptions

 - Just bools and unbounded integers.

 - All joins are binary inner joins with a single predicate; all
   unions are binary.

 - We use $"Distinct"$ to stand in for general reductions and top-K.

 - No recursion (yet).

 - We take the order of relation expressions as fixed---but SQL has a
   much more open-minded view of when different parts of the query are
   evaluated.

== TODO

 - $mono("null")$ and $mono("coalesce")$. (Default
   $mono("null")$-lifting semantics, with a special case. Probably
   want an $mono("is-null")$ predicate, too.)

 - $"TopK"$ for its weird ordering/complement issues.

= Notes on SQL semantics

== SQL evaluation order is under specified

#quote(block:true, attribution: [ISO/IEC 9075-1:2023, Section 6.3.3.3 Rule evaluation order])[

A conforming SQL-implementation is not required to perform the exact sequence of actions defined in the General Rules, provided its effect on SQL-data and schemas, on host parameters and host variable, and on SQL parameters and SQL variables is identical to the effect of that sequence. The term effectively is used to emphasize actions whose effect might be achieved in other ways by an SQL-implementation.

    ...

Where the precedence of operators is determined by the Formats of the ISO/IEC 9075 series or by parentheses, those operators are effectively applied in the order specified by that precedence.  Where the precedence is not determined by the Formats or by parentheses, effective evaluation of expressions is generally performed from left to right. However, it is implementation-dependent (US001) whether expressions are actually evaluated left to right, particularly when operands or operators might cause conditions to be raised or if the results of the expressions can be determined without completely evaluating all parts of the expression.

]

#quote(block:true, attribution: [ISO/IEC 9075-2:2016, Section 7.4 `<table expression>`])[

```
<table expression> ::=
    <from clause>
    [ <where clause> ]
    [ <group by clause> ]
    [ <having clause> ]
```

    If all optional clauses are omitted, then the result of the `<table expression>` is the same as the result of the `<from clause>`. Otherwise, each specified clause is applied to the result of the previously specified clause and the result of the `<table expression>` is the result of the application of the last specified clause.
]

#quote(block:true, attribution: [ISO/IEC 9075-2:2016, Section 4.35.2 Status parameters])[

    Exception conditions or completion conditions may be raised during the execution of an `<SQL procedure statement>`. One of the conditions becomes the active condition when the `<SQL procedure statement>` terminates.

    ...

    For the purpose of choosing status parameter values to be returned, exception conditions for transaction rollback have precedence over exception conditions for statement failure. Similarly, the completion condition 'no data' has precedence over the completion condition 'warning', which has precedence over the completion condition 'successful completion'. All exception conditions have precedence over all completion conditions. The values assigned to SQLSTATE shall obey these precedence requirements.

]

In general (a) optimizers may do what they like that are "effectively
the same" as (b) a fairly fixed specification of evaluation order that
(c) seems to require eager propagation of errors (but multiple
plausible evaluation orders).

== Plan of attack

- Extend #cite(<Guagliardo2017sql>, form: "prose") to support
  errors. NB their semantics is deterministic.
    - Introducing failing operations on its own will not introduce
      nondeterminism.
    - Introducing arbitrary evaluation order will _also_ not introduce
      nondeterminism---since there are no effects and the underlying
      operations are deterministic.
    - Introducing _both_ failing operations and arbitrary evaluation
      order will induce nondeterminism: a failure may or may not occur
      due to evaluation order.
- Correctness becomes more general: transforms need not refine the
  semantics of their inputs, but simply stay within the guardrails of
  the original term.

*Candidate correctness criterion.* A relation expression $R$ _implements_ a SQL query $Q$ if $[|R|](d) subset.eq [|Q|](d)$ for all databases $d$. A transform $psi : "Relations" arrow "Relations"$ is _sound_ when for all queries $Q$ and relation expressions $R$, if $R$ implements $Q$, then $psi(R)$ implements $Q$, i.e., for all databases $d$, if $[|R|](d) subset.eq [|Q|](d)$ then $[|psi(R)|](d) subset.eq [|Q|}(d)$.

= Syntax

== Values

=== Constants

#let null = math.mono("null")
#let t = math.mono("true")
#let f = math.mono("false")
#let utf8 = math.mono("UTF-8")

We abreviate the booleans as $bb(B) = { #t, #f }$.

$\
c in "Constants" ::=
//  #null |
  b in bb(B) |
  z in bb(Z) // |
//  r in bb(R) |
//  s in #utf8
$


=== Errors

#let err = $mono("err")$
#let NoSuchColumn = $mono("NoSuchColumn")$
#let TypeError = $mono("TypeError")$
#let DivisionByZero = $mono("DivisionByZero")$

$\
#err in "Errors" ::= #NoSuchColumn | #TypeError | #DivisionByZero
$

=== Rows and counts

A _row_ is a tuple $t$ of constants, of arity 0 or higher:

$\
t in "Rows" = (c_0, ..., c_n)
$

We write the empty row as $()$.

=== Databases and outputs

A _bag_ $B in "Bags"$ is modeled by its characteristic counting function:

$
B : "Rows" arrow bb(Z)
$

We define the usual bag operations:

 - The _domain_ of a bag $"dom"(B) = { t in "Rows" | B(t) != 0 }$ is
   the set of elements with a non-zero count. We write $B(t) = z$ as a
   proposition to bind both $t$ and $z$---noting that $z$ binds to 0
   when $t$ is not in the bag $B$.

 - The _union_ of two bags combines the counts: $(B_1 union B_2)(t) = B_1(t) + B_2(t)$.

 - We use the bag-builder notation $B = { t mapsto z | P }$ to create
   the bag $B$ that maps $t$ to $z$ when $P$ holds, and to 0
   otherwise, i.e., $B(t') = cases(z & "when" t = t' and P, 0 & "otherwise")$.

An _output_ is either a bag or an error $#err$.

$\
o in "Outputs" = B | #err
$

#let normalize(o) = $mono("normalize")(#o)$

A _database_ is a map from table names $T in "Tables"$ to "Bags":

$\
"DB" : "Tables" arrow "Bags"
$

If a table isn't defined, we map it to the empty bag.

== Scalar Expressions

#let col(n) = $mono("#") #n$
#let ite(c, t, e) = $mono("if") #c mono("then") #t mono("else") #e$

$\
e && ::= & c | col(n)                                      & "constants and column reference"\
  &&   | & not e | e_1 and e_2 | e_1 or e_2                & "boolean operators" \
  &&   | & e_1 + e_2 | e_1 - e_2 | e_1 * e_2 | e_1 div e_2 & "arithmetic" \
  &&   | & e_1 == e_2 | e_1 < e_2                          & "comparators" \
  &&   | & ite(e_"cond", e_"then", e_"else")               & "conditionals" \
$

Column references are to natural-numbered columns (i.e., $n in bb(N)$).

#let typeof(op) = $"typeof"(#op)$
#let dom(ty) = $"dom"(#ty)$

$\
typeof(not) &=& bb(B) arrow & bb(B) \
typeof(and) = typeof(or) &=& bb(B) times bb(B) arrow & bb(B) \
typeof(+) = typeof(-) = typeof(*) &=& bb(Z) times bb(Z) arrow & bb(Z) \
typeof(div) &=& bb(Z) times bb(Z) arrow & bb(Z) union {#DivisionByZero} \
typeof(==) = typeof(<) &=& bb(Z) times bb(Z) arrow & bb(B) \
$

We abbreviate $dom(typeof(times.circle))$ to $dom(times.circle)$, using subscripts to identify parts, e.g., $dom(div)_1 = dom(div)_2 = bb(Z)$.

== Table Functions

#let generateseries(from, to) = $mono("generate_series")(#from, #to)$

$\
f_t && ::= & generateseries(z_"from", z_"to") \
$

== Relation Expressions

#let Let(x, binding, body) = $mono("let") x = binding mono("in") body$
#let Map(R, e) = $"Map"(#R, #e)$
#let Filter(R, e) = $"Filter"(#R, #e)$
#let Project(R, cols) = $"Project"(#R, #cols)$
#let FlatMap(R, ft) = $"FlatMap"(#R, #ft)$
#let Join(Rl, Rr, e) = $"Join"(#Rl, #Rr, #e)$
#let Distinct(R, cols) = $"Distinct"(#R, #cols)$
#let Union(Rl, Rr) = $"Union"(#Rl, #Rr)$
#let Negate(R) = $"Negate"(#R)$
#let Threshold(R) = $"Threshold"(#R)$

$\
R && ::= & {t_0, ..., t_n}                 & "constant rows" \
  &&   | & x                               & "variable reference" \
  &&   | & T                               & "table reference" \
  &&   | & Let(x, R_1, R_2)                & "binding" \
  &&   | & Map(R, e)                       & "computed column" \
  &&   | & Filter(R, e)                    & "filtered rows" \
  &&   | & Project(R, accent(n, harpoon))  & "selected columns" \
  &&   | & FlatMap(R, f_t)                 & "table-valued function" \
  &&   | & Join(R_1, R_2, e)               & "binary inner join" \
  &&   | & Distinct(R, accent(n, harpoon)) & "distinct rows (by given columns)" \
  &&   | & Union(R_1, R_2)                 & "binary union" \
  &&   | & Negate(R)                       & "negate counts" \
  &&   | & Threshold(R)                    & "restrict to positive counts" \
$

= Semantics

== Scalar Expressions

Scalar expressions operate row-by-row, taking a row and yielding a set of possible outputs, i.e., a set of values and errors (@scalar-semantics). Each result in the set is a possible output of that scalar on that tuple.

#figure(
  [#align(left)[#box(inset: (x: 0.25em, y:0.25em), outset: (x: 0em, y: 0.25em), stroke: 1pt, $[|e|] : "Row" -> cal(P)("Constants" union.plus "Errors")$)]

   $\
   [|c|](t)      &=&& { c } \

   [|col(i)|](t) &=&& { c_i | t = (c_0, ..., c_n) } union \
                  &&& {#NoSuchColumn | t = (c_0, ..., c_n) and n < i} \

   [|times.circle e|](t)  &=&& { times.circle c | c in [|e|](t) inter dom(times.circle)} union \
                           &&& {#TypeError | c in [|e|](t) backslash dom(times.circle)} union \
                           &&& {#err | #err in [|e|](t)} \


   [|e_1 times.circle e_2|](t)  &=&& { c_1 times.circle c_2 | c_1 in [|e_1|](t) inter dom(times.circle)_1 and c_2 in [|e_2|](t) inter dom(times.circle)_2 } union \
                        &&& {#TypeError | c_1 in [|e_1|](t) backslash dom(times.circle)_1 } union \
                        &&& {#TypeError | c_2 in [|e_2|](t) backslash dom(times.circle)_2 } union \
                        &&& {#err | #err in [|e_1|](t)} union {#err | #err in [|e_2|](t)} \

   [|ite(e_"cond",e_"then",e_"else")|](t) &=&& { r | r in [|e_"then"|](t) and #t in [|e_"cond"|](t) } union \
                                           &&& { r | r in [|e_"else"|](t) and #f in [|e_"cond"|](t) } union \
                                           &&& { #TypeError | c in [|e_"cond"|] backslash bb(B) } union \
                                           &&& { #err | #err in [|e_"cond"|](t)} \
   $
  ],
  caption: [Scalar expressions are denoted as functions from tuples to sets of constants and errors.],
) <scalar-semantics>

Note that $[|e_1 div e_2|]$ can produce #DivisionByZero in the $c_1 div c_2$ case, in addition to the usual #TypeError (and propagated errors from $e_1$ and $e_2$).

Binary operations are our primary source of nondeterminism. Consider the following scalar expression:

$
e colon.eq not (col(0) == 0) and (col(1) div col(0) == 10)
$

One might think that this expression is safe: we require that $col(0)$ is non-zero, so it's okay to use it as a divisor.
But evaluation order is not fixed: we return $#err in [|e_2|](t)$ independently of $e_1$, so $#DivisionByZero in [|e|]((0, 0))$, because $#DivisionByZero in [|(col(1) div col(0) == 10)|]((0, 0))$, because $#DivisionByZero in [|col(1) div col(0)|]((0,0))$.

== Table Functions

A table function takes a row $t$ and returns an output, i.e., a bag or an error.

#figure(
 [#align(left)[#box(inset: (x: 0.25em, y:0.25em), outset: (x: 0em, y: 0.25em), stroke: 1pt, $[|t_f|] : "Row" -> cal(P)("Outputs")$)]

$\
[|generateseries(z_"from", z_"to")|]((c_0, dots, c_n)) = { (c_0, dots, c_n,z) mapsto 1 | z_"from" <= z <= z_"to" }
$
],
 caption: [Table functions are denoted as functions from tuple to sets of outputs.],
) <table-semantics>

== Relation Expressions

A relation takes a database $"DB"$ (i.e., a mapping from table names to rows) and produces an _output_.

#figure(
  [#align(left)[#box(inset: (x: 0.25em, y:0.25em), outset: (x: 0em, y: 0.25em), stroke: 1pt, $[|R|] : "DB" -> cal(P)("Outputs")$)]

$\
[|{t_0, ... t_n}|](d) &=&& { { t_i mapsto 1 | 0 <= i <= n } } \

[|T|](d) &=&& { d(T) } \

[|Let(x, R_1, R_2)|](d) &=&&
  { #err | #err in [|R_1|](d) } union
    union.big_(B in [|R_1|](d)) [|R_2[x mapsto B]|](d) \

[|Map(R, e)|](d) &=&&
  { #err | #err in [|R|](d) } union \ &&&
    union.big_(B in [|R|](d))
      { #err | t in dom(B) and [|e|](t) = err} union \ &&&
    union.big_(B in [|R|](d)) { (c_0, dots, c_n, c) mapsto z | B((c_0, dots, c_n)) = z and [|e|](t) = c }
  \

[|Filter(R, e)|](d) &=&&
  { #err | #err in [|R|](d) } union \ &&&
    union.big_(B in [|R|](d)) { #err | t in dom(B) and [|e|](t) = err} union \ &&&
    union.big_(B in [|R|](d)) { t mapsto z | B(t) = z and [|e|](t) = #t }
  \

[|Project(R, harpoon(i_0 dots i_j))|](d) &=&&
  { #err | #err in [|R|](d) } union \ &&&
  union.big_(B in [|R|](d)) { #NoSuchColumn | (c_0, dots, c_n) in dom(B) and exists k, i_k > n } union \ &&&
  union.big_(B in [|R|](d)) { (c_(i_0), dots, c_(i_j)) mapsto z | B((c_0, dots, c_n)) = z } } \

[|FlatMap(R, f_t)|](d) &=&&
  { #err | #err in [|R|](d) } union \ &&&
  union.big_(B in [|R|](d)) { #err | t in dom(B) and #err in [|f_t|](t) } union \ &&&
  union.big_(B in [|R|](d)){ t' mapsto z * z' | B(t) = z and B' = [|f_t|](t) and B'(t') = z' }
  \

[|Join(R_1, R_2, e)|](d) &=&&
  { #err | #err in [|R_1|](d) } union { #err | #err in [|R_2|](d) } union \ &&&
  union.big_(B_1 in [|R_1|](d)) union.big_(B_2 in [|R_2|](d))
    { #err | \ &&& "    "
      B_1((c_0, dots, c_n)) = z_1)  and B_2((c_(n+1), dots, c_(n+m))) = z_2 and [|e|]((c_0,dots,c_(n+m))) = #err } \ &&&
  union.big_(B_1 in [|R_1|](d)) union.big_(B_2 in [|R_2|](d))
    { (c_0, dots, c_(n+m)) mapsto  z_1*z_2 | \ &&& "    "
      B_1((c_0, dots, c_n)) = z_1 and B_2((c_(n+1), dots, c_(n+m))) = z_2 and [|e|]((c_0,dots,c_(n+m))) = #t }
  \

[|Distinct(R, harpoon(i_0 dots i_j))|](d) &=&&
  { #err | #err in [|R|](d) } union \ &&&
  union.big_(B in [|R|](d)) { #NoSuchColumn | (c_0, dots, c_n), in dom(B) and exists k, i_k > n} union \ &&&
  union.big_(B in [|R|](d)) { t_i mapsto 1 | {t_0, dots, t_n} in "EqClassRepresentatives"_harpoon(i_0 dots i_j)(B) }
  \

[|Union(R_1, R_2)|](d) &=&&
  { #err | #err in [|R_1|](d) } union { #err | #err in [|R_2|](d) } \ &&&
  union.big_(B_1 in [|R_1|](d)) union.big_(B_2 in [|R_2|](d)) { t mapsto z_1 + z_2 | B_1(t) = z_1 and B_2(t) = z_2 }
  \

[|Negate(R)|](d) &=&&
  { #err | #err in [|R|](d) } union
  union.big_(B in [|R|](d)) { t mapsto -z | B(t) = z }
  \

[|Threshold(R)|](d) &=&&
  { #err | #err in [|R|](d) } union
  union.big_(B in [|R|](d)) { t mapsto z | B(t) = z and z > 0 }
  \

$
],
caption: [Relation expressions are denoted as functions from databases to sets of (sets of) rows and errors. Note that we do not assign a semantics for variables, which are substituted out at their $mono("let")$-definition site.],) <relation-semantics>

= Properties of the Semantics

The semantics defined above (@scalar-semantics, @table-semantics, @relation-semantics) are non-deterministic, returning sets of results and errors. We expect them to be deterministic on non-error results.

*Conjecture: scalar functions are deterministic up to errors.* For all scalar functions $e$ and rows $t$, if $c_1, c_2 in [|e|](t)$, then $c_1 = c_2$.

*Conjecture: table functions are deterministic up to errors.* For all table functions $t_f$ and rows $t$, if $B_1, B_2 in [|t_f|](t)$ then $B_1 = B_2$.

*Conjecture: relation expressions functions are deterministic up to errors.* For all relation expressions $R$ and databases $d$, if $B_1, B_2 in [|R|](d)$ then $B_1 = B_2$.

That is, we can think of each syntactic form denoting zero or one answers (constants for scalars, bags for table functions and relation expressions) and zero or more errors.

= Correctness Criteria for Evaluation Strategies

#let eval(R, d) = $mono("eval")(#R, #d)$

We have defined nondeterministic specifications of behavior, but they are not evaluation strategies. That is $[|R|]$ is a mathematical function, not code.

An evaluation strategy for relation expressions is a computable function that takes a relation expression and a database to an output, i.e., $mono("eval") : "Relations" times "DB" arrow "Outputs"$.

We say an evaluation function $mono("eval")$ is sound when it only produces valid behaviors, i.e., for all databases $d$ we have that $eval(R, d) subset.eq [|R|](d)$.

= Correctness Criteria for Transformations

Sound transformations are exactly refinements: transformations that may narrow behavior---but not introduce new behaviors.

We say that scalar-expression transform $phi : "Scalars" arrow "Scalars"$ is _sound_ when for all scalar expressions $e$ and rows $t$, $[|phi(e)|](t) subset.eq [|e|](t)$.

Similarly, a relation-expression transformation $psi : "Relations" arrow "Relations"$ is _sound_ when for all relation expressions $R$ and databases $d$, $[|psi(R)|](d) subset.eq [|R|](d)$.

#bibliography("mir-semantics.bib", style: "ieee")
