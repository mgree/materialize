= Simplifying assumptions

 - Just bools and unbounded integers.
 - All joins are binary inner joins with a single predicate; all unions are binary.
 - We use $"Distinct"$ to stand in for general reductions and top-K.
 - No recursion (yet).

== TODO

 - $mono("null")$ and $mono("coalesce")$.
 - Counts in semantics.
 - $"TopK"$ for its weird ordering/complement issues.


= Values

== Constants

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



== Errors

#let err = $mono("err")$

$\
#err in "Errors" ::= mono("NoSuchColumn") | mono("TypeError") | mono("DivisionByZero")
$

== Rows

A _row_ is a tuple $t$ of constants, of arity 0 or higher:

$\
t in "Rows" = (c_1, ...)
$

We write the empty row as $()$.

== Databases and outputs

A _database_ is a partial map from table names $T in "Tables"$ to rows:

$\
"DB" : "Tables" harpoon.rt "Rows"
$

An _output_ is either a set of rows ${ t_1, ..., t_n } subset.eq "Rows"$ or an error $#err$.

$\
o in "Outputs" = { t_1, ... t_n } | #err
$

= Scalar Expressions

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
typeof(div) &=& bb(Z) times bb(Z) arrow & bb(Z) union {mono("DivideByZero")} \
typeof(==) = typeof(<) &=& bb(Z) times bb(Z) arrow & bb(B) \
$

We abbreviate $dom(typeof(times.circle))$ to $dom(times.circle)$, using subscripts to identify parts, e.g., $dom(div)_1 = dom(div)_2 = bb(Z)$.

== Table Functions

#let generateseries(from, to) = $mono("generate_series")(#from, #to)$

$\
f_t && ::= & generateseries(z_"from", z_"to") \
$

= Relation Expressions

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

Scalar expressions operator row-by-row, taking a row and yielding a set of possible outputs, i.e., a set of values and errors. Each is a possible output of that scalar on that tuple.

$[|e|] : "Row" -> cal(P)("Constants" union.plus "Errors")$

$\
[|c|](t)      &=&& { (c) } \

[|col(i)|](t) &=&& { c_i | t = (c_0, ..., c_n) } union \
               &&& {mono("NoSuchColumn") | t = (c_0, ..., c_n) and n < i} \

[|times.circle e|](t)  &=&& { times.circle c | c in [|e|](t) inter dom(times.circle)} union \
                        &&& {mono("TypeError") | c in [|e|](t) backslash dom(times.circle)} union \
                        &&& {#err | #err in [|e|](t)} \


[|e_1 times.circle e_2|](t)  &=&& { c_1 times.circle c_2 | c_1 in [|e_1|](t) inter dom(times.circle)_1 and c_2 in [|e_2|](t) inter dom(times.circle)_2 } union \
                     &&& {mono("TypeError") | c_1 in [|e_1|](t) backslash dom(times.circle)_1 } union \
                     &&& {mono("TypeError") | c_2 in [|e_2|](t) backslash dom(times.circle)_2 } union \
                     &&& {#err | #err in [|e_1|](t)} union {#err | #err in [|e_2|](t)} \

[|ite(e_"cond",e_"then",e_"else")|](t) &=&& { o | o in [|e_"then"|](t) and #t in [|e_"cond"|](t) } union \
                                        &&& { o | o in [|e_"else"|](t) and #f in [|e_"cond"|](t) } union \
                                        &&& { mono("TypeError") | c in [|e_"cond"|] backslash bb(B) } union \
                                        &&& { #err | #err in [|e_"cond"|](t)} \
$

Note that $[|e_1 div e_2|]$ can produce $mono("DivideByZero")$ in the $c_1 div c_2$ case, in addition to the usual $mono("TypeError")$ (and propagated errors from $e_1$ and $e_2$).

== Relation Expressions

A relation takes a database $"DB"$ (i.e., a mapping from table names to rows) and produces an _output_

$[|R|] : "DB" -> cal(P)("Outputs")$

$\
[|{t_0, ... t_n}|](d) = { {t_0, ... t_n} }
$

= Correctness criteria for transformations

== Scalar expressions

We say that $phi : "Scalar" arrow "Scalar"$ is _sound_ when for all scalar expressions $e$ and rows $t$, $[|phi(e)|](t) subset.eq [|e|](t)$.