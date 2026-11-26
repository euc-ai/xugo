package polish_space

import (
	_ "github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	_ "github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	_ "github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	_ "github.com/euc-ai/xugo/library/proofs/topology/borel_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PolishSpaceDef — Completeness is existence of a compatible complete metric, not completeness of every compatible metric.
var PolishSpaceDef = polishSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "PolishSpaceDef",
	Key:   "prop_471e0742d6ddfd76",
	Const: "polish_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    polish_space(T) ⇔ " +
			"    is_topology(T) ∧ " +
			"    separable_space(T) ∧ " +
			"    (∃d:(A → A → real). " +
			"        metric_space(⋃T, d) ∧ metric_complete(⋃T, d) ∧ metric_topology(⋃T, d) = T)",
	},
	Reading: "Completeness is existence of a compatible " +
		"complete metric, not completeness of every compatible metric.",
})}

// IndexedDiscreteTopologyDef — The discrete coordinate carriers and inactive values may vary with the index.
var IndexedDiscreteTopologyDef = indexedDiscreteTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "IndexedDiscreteTopologyDef",
	Key:   "prop_e192a7d9780c3c2b",
	Const: "indexed_discrete_topology",
	Type:  "set(I) → (I → A) → (I → set(A)) → set(set(I → A))",
	Equations: []string{
		"∀J:set(I). ∀z:(I → A). ∀X:(I → set(A)). " +
			"    indexed_discrete_topology(J, z, X) = " +
			"    indexed_product_topology(J, z, λi:I. {u:set(A) | u ⊆ X(i)})",
	},
	Reading: "This is a topology on indexed_functions(J, z, X). Empty active factors " +
		"are allowed, and an empty index set gives the singleton prescribed function.",
})}

// StandardBorelDef — `standard_borel_on(V, T)`: T is the Borel σ-algebra
// of a Polish topology on V. The carrier is the topology's, so a
// standard Borel space is a measurable space, and the topology that
// witnesses it is not part of its data.
var StandardBorelDef = standardBorelDefThm{family.Define(registry.DefEntry{
	Name:  "StandardBorelDef",
	Key:   "prop_dfaf9b529f0f7528",
	Const: "standard_borel_on",
	Type:  "set(A) → set(set(A)) → bool",
	Deps:  []registry.EntryLike{PolishSpaceDef},
	Equations: []string{
		"∀V:set(A). ∀T:set(set(A)). " +
			"    standard_borel_on(V, T) ⇔ (∃τ:set(set(A)). polish_space(τ) ∧ ⋃τ = V ∧ borel_sets(τ) = T)",
	},
})}
