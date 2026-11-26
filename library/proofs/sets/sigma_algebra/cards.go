package sigma_algebra

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var SigmaCountableIntersection = sigmaCountableIntersectionThm{family.Add(registry.ProofEntry{
	Name: "SigmaCountableIntersection",
	Reading: "The index type num makes the family nonempty, so the intersection " +
		"lies inside a(0) ⊆ Ω. An empty family would give the universal set.",
	Deps: []registry.EntryLike{SigmaFiniteOperations},
	Key:  "prop_5e1409ff2bdcc8e3",
	Build: family.Card(Statement{Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀a:(num → set(A)).",
		Hypotheses: []string{"sigma_algebra_on(Ω, S)", "∀n:num. a(n) ∈ S"},
		Conclusion: "⋂image(a, 𝕌) ∈ S"},
		"Use the relative De Morgan identity; the sequence has "+
			"a first term, so its intersection lies in the carrier."),
})}

var SigmaJoinUnion = sigmaJoinUnionThm{family.Add(registry.ProofEntry{
	Name: "SigmaJoinUnion",
	Key:  "prop_2ff95374383d25f4",
	Reading: "No carrier condition is needed: if some F(i) holds a set that is not a subset of " +
		"Ω, no σ-algebra on Ω contains the generators, the join over K ∪ L is the universal family, " +
		"and so is the join over K or L that holds it, so the right side is the universal family too.",
	Deps: []registry.EntryLike{GeneratedSigmaAlgebra, GeneratedSigmaLeast},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀F:(I → set(set(A))). ∀K L:set(I).",
		Conclusion: "sigma_join(Ω, F, K ∪ L) = " +
			"generated_sigma(Ω, sigma_join(Ω, F, K) ∪ sigma_join(Ω, F, L))",
	},
		"When the generators lie in Ω, each side is the least σ-algebra on Ω containing every "+
			"F(i), i ∈ K ∪ L: both contain those generators (GeneratedSigmaAlgebra), and each is "+
			"contained in any σ-algebra that contains the other's generators (GeneratedSigmaLeast, "+
			"twice for the right side). When one leaves Ω, both sides are the universal family."),
})}

var SigmaJoinEmpty = sigmaJoinEmptyThm{family.Add(registry.ProofEntry{
	Name: "SigmaJoinEmpty",
	Reading: "An empty Ω gives {∅}; no hypothesis is needed, since " +
		"generated_sigma(Ω, ∅) is the intersection of every σ-algebra on Ω.",
	Key:  "prop_c11b24558a8672e9",
	Deps: []registry.EntryLike{GeneratedSigmaAlgebra, GeneratedSigmaLeast, SigmaFiniteOperations},
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀F:(I → set(set(A))).",
		Conclusion: "sigma_join(Ω, F, ∅) = {∅, Ω}",
	},
		"With no generators the join is the least σ-algebra on Ω: {∅, Ω} is "+
			"one, and every σ-algebra on Ω contains Ω and ∅ (SigmaFiniteOperations)."),
})}
