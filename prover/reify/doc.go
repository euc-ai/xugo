// Package reify is the pure half of the elementarity step: it reads a
// higher-order proposition about a field record and writes the
// first-order formula that says the same thing of the field, in the
// integer-polynomial language of the corpus's first_order and
// polynomial_formula chapters. Nothing here derives a theorem. The
// output is the formula as a HOL term, the names the formula's
// variables were given, the obligations a caller discharges for the
// two to agree, and a plan naming the corpus lemma each node's bridge
// cites. The closer that cites them and transfers the sentence is
// built above this package, in the proof calculus.
//
// The grammar. A scalar term is the field's zero, one or integer, a
// scalar bound in the carrier or named as a parameter, a coordinate of
// a tuple term at an index, a sum, product, negation or difference of
// scalar terms, a finite sum module_sum(F.add, F.zero, {j | j < k},
// λj. t) of a scalar term over the indices below k (the record's parts
// spelled F.add or field_ring(F).add), a polynomial evaluated at a
// tuple, or a polynomial in one variable — a tuple term, its
// coefficients — evaluated at a scalar binder or parameter
// (polynomial_eval, the univariate code of the tuple's block at the
// scalar's name); it reifies to an integer polynomial over the
// formula's names, a finite sum to the integer polynomial ring's sum of
// t's polynomials over the same indices, t read with j an index binder
// below k. A polynomial term is a polynomial variable guarded by
// polynomial_bound, a polynomial parameter, or a member of a family at
// an index. An index is a natural-number term built from numerals and
// variables — index binders and the numeric data — by +, * and suc,
// and it stays below the tuple's length or the family's count: it is a
// binder that length bounds, a numeral below a numeral length, or a
// term the input's Arithmetic derives below it from the bounds of the
// index binders in scope (j * N + c < r * N from j < r and c < N);
// without an Arithmetic only the first two are read. A tuple term is a
// variable guarded by ring_tuple, a tuple parameter, or the polynomial
// map of a family at a tuple; it enters an atom by a coordinate or by
// equality, which reifies coordinatewise to a finite conjunction. An
// atom is an equality or disequality of scalars, a tuple equality, or,
// in the ordered theory, a strict or weak comparison. The connectives
// are the classical ones; the quantifiers are those of the design's
// table: a scalar bound in the carrier, a tuple guarded by ring_tuple, a
// polynomial guarded by polynomial_bound, a family guarded by a bounded
// conjunction of polynomial_bound, and a bounded index — a universal
// one becomes a finite conjunction, and an existential one,
// ∃j. j < k ∧ φ, the negation of the finite conjunction of φ's
// negations. A defined predicate or set outside the grammar is unfolded
// through the caller's Unfolder and read again; a term that still
// falls outside is refused, with the subterm and the reason.
//
// Names are allocated as a function of the proposition's syntax:
// parameters first, in the order given, then every binder from the
// outside in, each a block of consecutive names starting at the sum of
// the lengths allocated before it; binders in sibling scopes share the
// names past their common enclosing blocks. Two calls on one input
// produce one output: nothing reads a map's iteration order or the
// clock.
package reify
