// records.go — the simplicial set of free algebras a polynomial
// simplicial algebra is, as one value.

package simplicial_ring

import "github.com/euc-ai/xugo/library/registry"

// PolynomialSimplicialSetDef — `polynomial_simplicial_set(R, X, d, s)`:
// the free algebras on the names X(n), with the faces and degeneracies
// d and s of the host.
var PolynomialSimplicialSetDef = polynomialSimplicialSetDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialSimplicialSetDef",
	Key:   "prop_75b267d1cb39c52e",
	Const: "polynomial_simplicial_set",
	Type: "ring_ops(A) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(num → num → U → U) → " +
		"simplicial_ops(U)",
	Equations: []string{
		"∀R:ring_ops(A). ∀X:(num → set(U)). ∀d s:(num → num → U → U). " +
			"    polynomial_simplicial_set(R, X, d, s) = " +
			"    mk_simplicial(λn:num. universe_algebra(R, X(n)), d, s)",
	},
	Deps: []registry.EntryLike{UniverseAlgebraDef},
})}
