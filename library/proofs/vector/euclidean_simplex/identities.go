// identities.go — the cosimplicial identities: the relations among the
// cofaces and the codegeneracies that, read through precomposition,
// become the simplicial identities of the singular simplices. Each is an
// equation of maps of sequences, true at every sequence, and each is index
// arithmetic on the three cases of the two definitions.

package euclidean_simplex

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// CofaceCoface — δʲ ∘ δⁱ = δⁱ ∘ δʲ⁻¹ for i < j.
var CofaceCoface = cofaceCofaceThm{family.Add(registry.ProofEntry{
	Name: "CofaceCoface",
	Key:  "prop_3d3656c207ee32ae",
	Reading: "i < j makes j − 1 an honest predecessor and is load-bearing: " +
		"at i = j = 1 the two sides are (t₀, 0, 0, t₁, …) and (0, 0, t₀, t₁, …).",
	Deps: []registry.EntryLike{EuclideanCofaceDef, functions.ComposeApply},
	Build: family.Card(Statement{
		Binders: "∀i j:num.",
		Hypotheses: []string{
			"i < j",
		},
		Conclusion: "euclidean_coface(j) ∘ euclidean_coface(i) = " +
			"euclidean_coface(i) ∘ euclidean_coface(j - 1)",
	},
		"both insert zeros at i and at j into a sequence: compare the two at every "+
			"index, in the five ranges below i, at i, between i and j, at j and above j"),
})}

// CodegeneracyCodegeneracy — σʲ ∘ σⁱ = σⁱ ∘ σʲ⁺¹ for i ≤ j.
var CodegeneracyCodegeneracy = codegeneracyCodegeneracyThm{family.Add(registry.ProofEntry{
	Name: "CodegeneracyCodegeneracy",
	Key:  "prop_abbcca65c374bad5",
	Reading: "i ≤ j; at i = j both sides add the three " +
		"coordinates t(i), t(i + 1), t(i + 2) at place i.",
	Deps: []registry.EntryLike{EuclideanCodegeneracyDef, functions.ComposeApply},
	Build: family.Card(Statement{
		Binders: "∀i j:num.",
		Hypotheses: []string{
			"i ≤ j",
		},
		Conclusion: "euclidean_codegeneracy(j) ∘ euclidean_codegeneracy(i) = " +
			"euclidean_codegeneracy(i) ∘ euclidean_codegeneracy(j + 1)",
	},
		"both add coordinates i and i + 1 together and coordinates j + 1 and j "+
			"+ 2 together, three of them at once when i = j: compare at every index"),
})}

// CodegeneracyCofaceBelow — σʲ ∘ δⁱ = δⁱ ∘ σʲ⁻¹ for i < j.
var CodegeneracyCofaceBelow = codegeneracyCofaceBelowThm{family.Add(registry.ProofEntry{
	Name:    "CodegeneracyCofaceBelow",
	Key:     "prop_bb830a8d51628765",
	Reading: "i < j makes j − 1 honest; at i = 0, j = 1 both sides are (0, t₀ + t₁, t₂, …).",
	Deps:    []registry.EntryLike{EuclideanCofaceDef, EuclideanCodegeneracyDef, functions.ComposeApply},
	Build: family.Card(Statement{
		Binders: "∀i j:num.",
		Hypotheses: []string{
			"i < j",
		},
		Conclusion: "euclidean_codegeneracy(j) ∘ euclidean_coface(i) = " +
			"euclidean_coface(i) ∘ euclidean_codegeneracy(j - 1)",
	},
		"both insert a zero at i and add the coordinates that land at j and j + 1: compare at every index"),
})}

// CodegeneracyCofaceIdentity — σʲ ∘ δʲ and σʲ ∘ δʲ⁺¹ are the identity.
var CodegeneracyCofaceIdentity = codegeneracyCofaceIdentityThm{family.Add(registry.ProofEntry{
	Name:    "CodegeneracyCofaceIdentity",
	Key:     "prop_9eeb006733be44ba",
	Reading: "Unconditional: the inserted zero is the summand added in at place j.",
	Deps:    []registry.EntryLike{EuclideanCofaceDef, EuclideanCodegeneracyDef, functions.ComposeApply},
	Build: family.Card(Statement{
		Binders: "∀j:num.",
		Conclusion: "euclidean_codegeneracy(j) ∘ euclidean_coface(j) = (λt:(num → real). t) ∧ " +
			"euclidean_codegeneracy(j) ∘ euclidean_coface(j + 1) = (λt:(num → real). t)",
	},
		"the zero inserted at j, or at j + 1, is added to its neighbour "+
			"and the sequence closes up again: compare at every index"),
})}

// CodegeneracyCofaceAbove — σʲ ∘ δⁱ = δⁱ⁻¹ ∘ σʲ for j + 1 < i.
var CodegeneracyCofaceAbove = codegeneracyCofaceAboveThm{family.Add(registry.ProofEntry{
	Name: "CodegeneracyCofaceAbove",
	Key:  "prop_c4b44adc5f91fcef",
	Reading: "j + 1 < i makes i − 1 honest; the excluded " +
		"case i = j + 1 is CodegeneracyCofaceIdentity's.",
	Deps: []registry.EntryLike{EuclideanCofaceDef, EuclideanCodegeneracyDef, functions.ComposeApply},
	Build: family.Card(Statement{
		Binders: "∀i j:num.",
		Hypotheses: []string{
			"j + 1 < i",
		},
		Conclusion: "euclidean_codegeneracy(j) ∘ euclidean_coface(i) = " +
			"euclidean_coface(i - 1) ∘ euclidean_codegeneracy(j)",
	},
		"both add coordinates j and j + 1 of the sequence and put a "+
			"zero at place i − 1 of the result: compare at every index"),
})}
