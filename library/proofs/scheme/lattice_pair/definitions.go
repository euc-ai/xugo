// definitions.go — the chapter's definitional layer: the biaffine datum,
// and lattice pairs over it with their two cohomology modules, their
// dimensions and the Euler characteristic.
//
// A biaffine datum is a ring R with two subrings A₀ and A₁ and an
// element t of A₀ whose inverse s lies in A₁, R being A₀[1/t] and A₁[1/s]
// at once: the two charts of a curve and their overlap. A lattice pair
// is a module V over R and a pair M = (M₀, M₁), M₀ an A₀-submodule and
// M₁ an A₁-submodule of V that span the same R-submodule, the ambient of
// M. Its H⁰ is M₀ ∩ M₁, its H¹ the ambient modulo M₀ + M₁: the Čech
// complex of the two-chart cover has two terms. V is a container, not
// the ambient, so that lattice pairs inside a field take V to be the
// field itself, and the dualizing pair and the derivation pair take
// V to be a module of functions.

package lattice_pair

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The biaffine datum
// ---------------------------------------------------------------------------

// BiaffineDef — `biaffine(R, A₀, A₁, t, s)`: A₀ and A₁ are subrings of
// the commutative ring R, t ∈ A₀ and s ∈ A₁ are inverse to each other,
// and R is A₀ with t inverted and A₁ with s inverted.
var BiaffineDef = biaffineDefThm{family.Define(registry.DefEntry{
	Name:  "BiaffineDef",
	Key:   "prop_b46b6dfa0e6ee49b",
	Const: "biaffine",
	Type:  "ring_ops(A) → set(A) → set(A) → A → A → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A. " +
			"    biaffine(R, A₀, A₁, t, s) ⇔ " +
			"    comm_ring_on(R) ∧ " +
			"    subring(R, A₀) ∧ " +
			"    subring(R, A₁) ∧ " +
			"    t ∈ A₀ ∧ " +
			"    s ∈ A₁ ∧ " +
			"    R.mul(t, s) = R.one ∧ " +
			"    R.carrier = ring_away(R, A₀, t) ∧ " +
			"    R.carrier = ring_away(R, A₁, s)",
	},
})}

// ---------------------------------------------------------------------------
// Lattice pairs and their cohomology
// ---------------------------------------------------------------------------

// LatticePairDef — `lattice_pair(R, A₀, A₁, V, M)`: V is a module over R,
// fst(M) an A₀-submodule and snd(M) an A₁-submodule of V, and the two
// span the same R-submodule of V.
var LatticePairDef = latticePairDefThm{family.Define(registry.DefEntry{
	Name:  "LatticePairDef",
	Key:   "prop_42ca56be1ae99fd5",
	Const: "lattice_pair",
	Type:  "ring_ops(A) → set(A) → set(A) → module_ops(A, B) → prod(set(B), set(B)) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)). " +
			"    lattice_pair(R, A₀, A₁, V, M) ⇔ " +
			"    module_on(R, V) ∧ " +
			"    submodule(restrict_ring(R, A₀), V, fst(M)) ∧ " +
			"    submodule(restrict_ring(R, A₁), V, snd(M)) ∧ " +
			"    module_span(R, V, fst(M)) = module_span(R, V, snd(M))",
	},
})}

// LatticePairAmbientDef — `lattice_pair_ambient(R, V, M)`: the
// R-submodule of V that fst(M) spans, the module the pair glues to on the
// overlap.
var LatticePairAmbientDef = latticePairAmbientDefThm{family.Define(registry.DefEntry{
	Name:  "LatticePairAmbientDef",
	Key:   "prop_e3c81f8643031f8d",
	Const: "lattice_pair_ambient",
	Type:  "ring_ops(A) → module_ops(A, B) → prod(set(B), set(B)) → set(B)",
	Equations: []string{
		"∀R:ring_ops(A). ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)). " +
			"    lattice_pair_ambient(R, V, M) = module_span(R, V, fst(M))",
	},
})}

// LatticePairH0Def — `lattice_pair_h0(V, M)`, written H⁰(M): the
// sections on both charts, fst(M) ∩ snd(M), with V's operations.
var LatticePairH0Def = latticePairH0DefThm{family.Define(registry.DefEntry{
	Name:  "LatticePairH0Def",
	Key:   "prop_da8073ce0cae119a",
	Const: "lattice_pair_h0",
	Type:  "module_ops(A, B) → prod(set(B), set(B)) → module_ops(A, B)",
	Equations: []string{
		"∀V:module_ops(A, B). ∀M:prod(set(B), set(B)). " +
			"    lattice_pair_h0(V, M) = restrict_module(V, fst(M) ∩ snd(M))",
	},
})}

// LatticePairH1Def — `lattice_pair_h1(R, V, M)`, written H¹(M): the
// ambient modulo fst(M) + snd(M), the cokernel of the difference map of
// the two-chart Čech complex.
var LatticePairH1Def = latticePairH1DefThm{family.Define(registry.DefEntry{
	Name:  "LatticePairH1Def",
	Key:   "prop_26dd239ad04d2666",
	Const: "lattice_pair_h1",
	Type:  "ring_ops(A) → module_ops(A, B) → prod(set(B), set(B)) → module_ops(A, set(B))",
	Equations: []string{
		"∀R:ring_ops(A). ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)). " +
			"    lattice_pair_h1(R, V, M) = " +
			"    quotient_module(restrict_module(V, lattice_pair_ambient(R, V, M)), " +
			"        set_mul(V.add, fst(M), snd(M)))",
	},
	Deps: []registry.EntryLike{LatticePairAmbientDef},
})}

// LatticePairDifferenceDef — `lattice_pair_difference(V, z)`: the Čech
// difference m₀ − m₁ of a pair z = (m₀, m₁) of sections on the two charts.
var LatticePairDifferenceDef = latticePairDifferenceDefThm{family.Define(registry.DefEntry{
	Name:  "LatticePairDifferenceDef",
	Key:   "prop_921bee72c97304ae",
	Const: "lattice_pair_difference",
	Type:  "module_ops(A, B) → prod(B, B) → B",
	Equations: []string{
		"∀V:module_ops(A, B). ∀z:prod(B, B). lattice_pair_difference(V, z) = V.add(fst(z), V.neg(snd(z)))",
	},
})}

// LatticePairH0DimDef — `lattice_pair_h0_dim(R, k, V, M)`, written ℓ(M):
// the dimension of H⁰(M) over the subfield k of R.
var LatticePairH0DimDef = latticePairH0DimDefThm{family.Define(registry.DefEntry{
	Name:  "LatticePairH0DimDef",
	Key:   "prop_62ea773af8f3b6bd",
	Const: "lattice_pair_h0_dim",
	Type:  "ring_ops(A) → set(A) → module_ops(A, B) → prod(set(B), set(B)) → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)). " +
			"    lattice_pair_h0_dim(R, k, V, M) = module_dim(restrict_ring(R, k), lattice_pair_h0(V, M))",
	},
	Deps: []registry.EntryLike{LatticePairH0Def},
})}

// LatticePairH1DimDef — `lattice_pair_h1_dim(R, k, V, M)`: the dimension
// of H¹(M) over the subfield k of R.
var LatticePairH1DimDef = latticePairH1DimDefThm{family.Define(registry.DefEntry{
	Name:  "LatticePairH1DimDef",
	Key:   "prop_552bdb076a2b52d5",
	Const: "lattice_pair_h1_dim",
	Type:  "ring_ops(A) → set(A) → module_ops(A, B) → prod(set(B), set(B)) → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)). " +
			"    lattice_pair_h1_dim(R, k, V, M) = module_dim(restrict_ring(R, k), lattice_pair_h1(R, V, M))",
	},
	Deps: []registry.EntryLike{LatticePairH1Def},
})}

// LatticePairFiniteDef — `lattice_pair_finite(R, k, V, M)`: H⁰(M) and
// H¹(M) are finite-dimensional over k. Only then are the dimensions above
// and the Euler characteristic below determined numbers.
var LatticePairFiniteDef = latticePairFiniteDefThm{family.Define(registry.DefEntry{
	Name:  "LatticePairFiniteDef",
	Key:   "prop_b57370139f44aefe",
	Const: "lattice_pair_finite",
	Type:  "ring_ops(A) → set(A) → module_ops(A, B) → prod(set(B), set(B)) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)). " +
			"    lattice_pair_finite(R, k, V, M) ⇔ " +
			"    finite_dimensional(restrict_ring(R, k), lattice_pair_h0(V, M)) ∧ " +
			"    finite_dimensional(restrict_ring(R, k), lattice_pair_h1(R, V, M))",
	},
	Deps: []registry.EntryLike{LatticePairH0Def, LatticePairH1Def},
})}

// LatticePairEulerDef — `lattice_pair_euler(R, k, V, M)`, written χ(M):
// dim H⁰(M) − dim H¹(M), an integer.
var LatticePairEulerDef = latticePairEulerDefThm{family.Define(registry.DefEntry{
	Name:  "LatticePairEulerDef",
	Key:   "prop_44720d874d8fa215",
	Const: "lattice_pair_euler",
	Type:  "ring_ops(A) → set(A) → module_ops(A, B) → prod(set(B), set(B)) → int",
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)). " +
			"    lattice_pair_euler(R, k, V, M) = " +
			"    int_of_num(lattice_pair_h0_dim(R, k, V, M)) - int_of_num(lattice_pair_h1_dim(R, k, V, M))",
	},
	Deps: []registry.EntryLike{LatticePairH0DimDef, LatticePairH1DimDef},
})}
