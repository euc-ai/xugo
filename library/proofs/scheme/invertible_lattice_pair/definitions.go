// definitions.go — the operations on lattice pairs inside a field: the
// chartwise product and inverse of fractional ideals, the invertible pairs,
// and scaling by a member of the field.

package invertible_lattice_pair

import (
	_ "github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/registry"
)

// LatticePairMulDef — `lattice_pair_mul(R, A₀, A₁, M, N)`, written M · N:
// the chartwise products of fractional ideals.
var LatticePairMulDef = latticePairMulDefThm{family.Define(registry.DefEntry{
	Name:  "LatticePairMulDef",
	Key:   "prop_d0b3fa8db9010e64",
	Const: "lattice_pair_mul",
	Type: "ring_ops(A) → " +
		"set(A) → " +
		"set(A) → " +
		"prod(set(A), set(A)) → " +
		"prod(set(A), set(A)) → " +
		"prod(set(A), set(A))",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀:set(A). ∀A₁:set(A). ∀M:prod(set(A), set(A)). ∀N:prod(set(A), set(A)). " +
			"    lattice_pair_mul(R, A₀, A₁, M, N) = " +
			"    (fractional_mul(R, A₀, fst(M), fst(N)), fractional_mul(R, A₁, snd(M), snd(N)))",
	},
})}

// LatticePairInverseDef — `lattice_pair_inverse(R, A₀, A₁, M)`, written
// M⁻¹: the chartwise inverses of fractional ideals.
var LatticePairInverseDef = latticePairInverseDefThm{family.Define(registry.DefEntry{
	Name:     "LatticePairInverseDef",
	Key:      "prop_f03737e17206de20",
	Const:    "lattice_pair_inverse",
	Type:     "ring_ops(A) → set(A) → set(A) → prod(set(A), set(A)) → prod(set(A), set(A))",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀:set(A). ∀A₁:set(A). ∀M:prod(set(A), set(A)). " +
			"    lattice_pair_inverse(R, A₀, A₁, M) = " +
			"    (fractional_inverse(R, A₀, fst(M)), fractional_inverse(R, A₁, snd(M)))",
	},
})}

// InvertibleLatticePairDef — `invertible_lattice_pair(R, A₀, A₁, A₀₁, M)`:
// each chart of M is an invertible fractional ideal of its chart ring,
// and the two agree on the overlap A₀₁ — M is a lattice pair in the
// field over the overlap's ring.
var InvertibleLatticePairDef = invertibleLatticePairDefThm{family.Define(registry.DefEntry{
	Name:     "InvertibleLatticePairDef",
	Key:      "prop_fe3aff4c7ba4c167",
	Const:    "invertible_lattice_pair",
	Type:     "ring_ops(A) → set(A) → set(A) → set(A) → prod(set(A), set(A)) → bool",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀:set(A). ∀A₁:set(A). ∀A₀₁:set(A). ∀M:prod(set(A), set(A)). " +
			"    invertible_lattice_pair(R, A₀, A₁, A₀₁, M) ⇔ " +
			"    invertible_fractional(R, A₀, fst(M)) ∧ " +
			"    invertible_fractional(R, A₁, snd(M)) ∧ " +
			"    lattice_pair(restrict_ring(R, A₀₁), A₀, A₁, regular_module(R), M)",
	},
	Deps: []registry.EntryLike{},
})}

// LatticePairScaleDef — `lattice_pair_scale(a, M)`, written a · M: both
// charts multiplied by the element a of the field.
var LatticePairScaleDef = latticePairScaleDefThm{family.Define(registry.DefEntry{
	Name:     "LatticePairScaleDef",
	Key:      "prop_ef6254a6b19cf777",
	Const:    "lattice_pair_scale",
	Type:     "(A → A → A) → A → prod(set(A), set(A)) → prod(set(A), set(A))",
	Implicit: []string{"mul"},
	Equations: []string{
		"∀mul:(A → A → A). ∀a:A. ∀M:prod(set(A), set(A)). " +
			"    lattice_pair_scale(mul, a, M) = (image(mul(a), fst(M)), image(mul(a), snd(M)))",
	},
})}
