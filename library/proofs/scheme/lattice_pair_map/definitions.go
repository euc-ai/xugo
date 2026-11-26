// definitions.go — maps of lattice pairs: the linear maps of the ambients
// carrying each chart into the same chart, the module of them, and the
// isomorphisms among them.

package lattice_pair_map

import (
	_ "github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/registry"
)

// LatticePairMapsDef — `lattice_pair_maps(R, V, M, W, N)`, written
// Hom(M, N): the R-linear maps from the ambient of M into W that carry
// each chart of M into the same chart of N, zero off the ambient.
var LatticePairMapsDef = latticePairMapsDefThm{family.Define(registry.DefEntry{
	Name:  "LatticePairMapsDef",
	Key:   "prop_ca8a9a455a404f14",
	Const: "lattice_pair_maps",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"prod(set(B), set(B)) → " +
		"module_ops(A, C) → " +
		"prod(set(C), set(C)) → " +
		"set(B → C)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀W:module_ops(A, C). " +
			"∀N:prod(set(C), set(C)). " +
			"    lattice_pair_maps(R, V, M, W, N) = " +
			"    {f:B → C | " +
			"        f ∈ hom_set(R, restrict_module(V, lattice_pair_ambient(R, V, M)), W) ∧ " +
			"        image(f, fst(M)) ⊆ fst(N) ∧ " +
			"        image(f, snd(M)) ⊆ snd(N)}",
	},
	Deps: []registry.EntryLike{},
})}

// LatticePairHomDef — `lattice_pair_hom(R, V, M, W, N)`, written Hom(M, N)
// as a module: the maps of lattice_pair_maps with the operations of the
// R-linear maps from the ambient of M into W.
var LatticePairHomDef = latticePairHomDefThm{family.Define(registry.DefEntry{
	Name:  "LatticePairHomDef",
	Key:   "prop_5f1425541cc9831a",
	Const: "lattice_pair_hom",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"prod(set(B), set(B)) → " +
		"module_ops(A, C) → " +
		"prod(set(C), set(C)) → " +
		"module_ops(A, B → C)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀W:module_ops(A, C). " +
			"∀N:prod(set(C), set(C)). " +
			"    lattice_pair_hom(R, V, M, W, N) = " +
			"    restrict_module(hom_module(R, restrict_module(V, lattice_pair_ambient(R, V, M)), W), " +
			"        lattice_pair_maps(R, V, M, W, N))",
	},
	Deps: []registry.EntryLike{LatticePairMapsDef},
})}

// LatticePairIsomorphismDef — `lattice_pair_isomorphism(R, V, M, W, N,
// f)`: f is a map of lattice pairs, one-to-one on the ambient of M, onto
// each chart of N.
var LatticePairIsomorphismDef = latticePairIsomorphismDefThm{family.Define(registry.DefEntry{
	Name:  "LatticePairIsomorphismDef",
	Key:   "prop_843d5f0ea2ca1386",
	Const: "lattice_pair_isomorphism",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"prod(set(B), set(B)) → " +
		"module_ops(A, C) → " +
		"prod(set(C), set(C)) → " +
		"(B → C) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀W:module_ops(A, C). " +
			"∀N:prod(set(C), set(C)). " +
			"∀f:(B → C). " +
			"    lattice_pair_isomorphism(R, V, M, W, N, f) ⇔ " +
			"    f ∈ lattice_pair_maps(R, V, M, W, N) ∧ " +
			"    injective_on(lattice_pair_ambient(R, V, M), f) ∧ " +
			"    image(f, fst(M)) = fst(N) ∧ " +
			"    image(f, snd(M)) = snd(N)",
	},
	Deps: []registry.EntryLike{LatticePairMapsDef},
})}
