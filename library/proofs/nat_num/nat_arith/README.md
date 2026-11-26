# nat_arith — the arithmetic of ℕ

This chapter develops addition, multiplication, exponentiation and
factorial on `num`, together with the binary numeral encoding. It sits
above `peano` and below `nat_order`: its statements and proofs use no
order relation. Truncated subtraction and natural distance belong to
`nat_monus`, Euclidean division to `nat_div_mod`, and growth estimates to
`nat_order`.

## Reading the chapter

- **Recursion and addition.** `PrimRecursion` supplies a recursively
  defined function, and `DependentChoice` a sequence chosen term by
  term: a start satisfying an invariant, and for each state a successor
  that keeps it, give a sequence keeping the invariant with each term
  linked to the next. `Add` defines addition by recursion on its first
  argument; `AddZero` and `AddSuc` establish the corresponding laws on
  the right. Associativity, commutativity, cancellation and the
  vanishing criterion follow. `AddEqSelfLeft` and `AddEqSelfRight` say
  when a sum equals one of its summands.
- **Multiplication.** `Mul` also recurses on its first argument. Its
  successor clause adds the second argument to the previous product,
  so its laws use the addition theory. The chapter proves the unit
  laws, commutativity, distributivity, associativity, cancellation,
  and the criteria for a product to be zero or one. Zero/successor
  cases handle these criteria; cancellation retains the induction it
  needs. Equal doubles are compared by cancelling their common factor
  two.
- **Powers and factorial.** `NatPow` recurses on the exponent. The
  fixed-base and fixed-exponent laws lead to `PowAdd`,
  `MulPowDistrib` and `PowPow`; `PowEqZero` gives the vanishing
  criterion. `PowTwoNonzero` and `PowTwoSuc` expose the nonvanishing
  and doubling laws used by binary arithmetic. `FactorialNonzero`
  follows from the recursion defining `Factorial`.
- **Numerals.** `Bit0` and `Bit1` relate binary digits to doubling
  and successors. `OneIsSucZero`, `Two` and `Add1` connect numeral
  notation with Peano recursion. `NumeralSuc`, `NumeralAdd`,
  `NumeralMul` and `NumeralEq` are the evaluation laws; the equality
  table uses injectivity of doubling and disjointness of even and odd
  doubles.

Names distinguish the two slots of exponentiation: `OnePow` fixes the
base, while `PowOne` fixes the exponent. The same distinction matters
for the recursive clauses: `AddLeftZeroClause` is the defining
left-zero law, while `AddZero` is the derived right-zero law.

## Reading and citing proofs

The [chapter constitution](../../../chapter_constitution.md) gives the
shared authoring rules. Each `By` lists the facts used by that close;
induction hypotheses and case assumptions travel as named facts.
Equation chains use `CalcEq`, and an AC rearrangement is supplied by
`AddAC` or `MulAC` with its laws explicit.

`AddClauses` and `MulClauses` collect the simplification laws of their
operations. Where a proof needs a single clause, cite its atomic home:
`AddLeftZeroClause`, `AddLeftSucClause`, `AddZero`, `AddSuc`,
`MulLeftZeroClause`, `mulLeftSucClause`, `MulZero`, `MulSuc`, `OneMul`,
`MulOne`, `powRightZeroClause` or `powRightSucClause`. A bare cite is
appropriate when the law rewrites all its occurrences in the goal;
otherwise witnesses follow the cited statement's own binder order.
The projection names retain the recursion slot because the defining
clauses and the derived laws are different theorems.

The operations and `bit0` are minted through recursive definition
doors; `bit1` is defined directly. Each definition's headline contains
its characterizing equations. The stand-ins `plus` and `times` in the
defining equations name the operators whose text notation is `+` and
`*`.

Public entry names describe the chapter's reusable arithmetic laws.
Internal entries carry proof support such as the two doubling facts
used by the numeral equality table.
