// definitions.go — twisting a lattice pair inside a field by an ideal pair,
// and the regular points of a biaffine datum: the rational points whose
// ideals are invertible.

package lattice_pair_twist

import (
	_ "github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/registry"
)

// LatticePairTwistDef — `lattice_pair_twist(R, A₀, A₁, M, P)`, written
// M(P): M multiplied by the inverse of the point's ideal pair, the
// sections allowed a simple pole at P.
var LatticePairTwistDef = latticePairTwistDefThm{family.Define(registry.DefEntry{
	Name:  "LatticePairTwistDef",
	Key:   "prop_7d9bc95d705d85a3",
	Const: "lattice_pair_twist",
	Type: "ring_ops(A) → " +
		"set(A) → " +
		"set(A) → " +
		"prod(set(A), set(A)) → " +
		"prod(set(A), set(A)) → " +
		"prod(set(A), set(A))",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀:set(A). ∀A₁:set(A). ∀M:prod(set(A), set(A)). ∀P:prod(set(A), set(A)). " +
			"    lattice_pair_twist(R, A₀, A₁, M, P) = " +
			"    lattice_pair_mul(R, A₀, A₁, lattice_pair_inverse(R, A₀, A₁, P), M)",
	},
	Deps: []registry.EntryLike{},
})}

// BiaffineRegularPointDef — `biaffine_regular_point(R, k, A₀, A₁, A₀₁,
// P)`: a rational point of the datum inside the field whose ideal in each
// chart is invertible.
var BiaffineRegularPointDef = biaffineRegularPointDefThm{family.Define(registry.DefEntry{
	Name:     "BiaffineRegularPointDef",
	Key:      "prop_c26ecf458bd806f0",
	Const:    "biaffine_regular_point",
	Type:     "ring_ops(A) → set(A) → set(A) → set(A) → set(A) → prod(set(A), set(A)) → bool",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀A₀:set(A). ∀A₁:set(A). ∀A₀₁:set(A). ∀P:prod(set(A), set(A)). " +
			"    biaffine_regular_point(R, k, A₀, A₁, A₀₁, P) ⇔ " +
			"    biaffine_rational_point(restrict_ring(R, A₀₁), k, A₀, A₁, P) ∧ " +
			"    invertible_lattice_pair(R, A₀, A₁, A₀₁, P)",
	},
	Deps: []registry.EntryLike{},
})}
