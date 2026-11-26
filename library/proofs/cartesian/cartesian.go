// Package cartesian is the aggregator for the cartesian product's
// chapters.
//
// The domain groups by SUBJECT — the cartesian product in its guises.
// The type-level chapters (dimensions, powers, concat, products)
// retired with the term-level migration; what remains is the pair of
// poles the migration chose, and two chapters on the power of ℕ:
//
// - pairs — the binary product `prod(A, B)` as a type: its
// constructor and projections, and the binder transports that let a
// statement about pairs be stated over components. Closed in pure
// HOL and dimension-orthogonal, so the migration left it untouched.
// - carrier — the finite power in its TERM-LEVEL guise: a
// dimensioned tuple as a `num → A` function junk-normalized past
// an active range, the dimension an ordinary num. Its members are
// mechanical twins of the type-level statements (the
// dimension translation), and the family is where any wider
// term-level re-founding of the domain grows.
// - kuhn — the grid {0, …, p}ⁿ, its points carrier's tuples of naturals,
// and its triangulation into Kuhn simplices.
// - kuhn_labelling — Kuhn's lemma on that triangulation: a labelling ⊥
// on the cube's lower faces and ⊤ on its upper ones labels an odd number
// of the simplices fully. Pure combinatorics, no real number, which is
// what lets ℝⁿ's chapters read it for Brouwer's theorem.
package cartesian

import (
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/carrier"
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/kuhn"
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/kuhn_labelling"
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
)
