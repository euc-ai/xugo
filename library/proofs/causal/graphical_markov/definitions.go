// definitions.go — the structural σ-algebra family on a DAG: the one
// object through which graph separation becomes conditional
// independence.

package graphical_markov

import (
	"github.com/euc-ai/xugo/library/registry"
)

// StructuralSigmaFamilyDef — `structural_sigma_family(Ω, S, μ, V, E, G,
// N)`: (V, E) is a DAG, the noise σ-algebras N(j), j ∈ V, are an
// independent family of the probability space, and each information
// σ-algebra G(j) is a σ-algebra on Ω inside the one that the G(k) of the
// parents k of j and N(j) generate.
var StructuralSigmaFamilyDef = structuralSigmaFamilyDefThm{family.Define(registry.DefEntry{
	Name:  "StructuralSigmaFamilyDef",
	Key:   "prop_9f7cf942bb2efbd",
	Const: "structural_sigma_family",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"set(I) → " +
		"(I → I → bool) → " +
		"(I → set(set(A))) → " +
		"(I → set(set(A))) → " +
		"bool",
	Equations: []string{
		"∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(I). " +
			"∀E:(I → I → bool). " +
			"∀G N:(I → set(set(A))). " +
			"    structural_sigma_family(Ω, S, μ, V, E, G, N) ⇔ " +
			"    dag_on(V, E) ∧ " +
			"    independent_sigma_family(Ω, S, μ, V, N) ∧ " +
			"    (∀j:I. " +
			"        j ∈ V ⇒ " +
			"        sigma_algebra_on(Ω, G(j)) ∧ " +
			"        G(j) ⊆ generated_sigma(Ω, ⋃image(G, dag_parents(E, j)) ∪ N(j)))",
	},
})}
