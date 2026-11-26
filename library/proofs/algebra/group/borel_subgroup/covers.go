package borel_subgroup

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/topology/baire_category"
	"github.com/euc-ai/xugo/library/registry"
)

var PolishCoverCountableIffOpen = polishCoverCountableIffOpenThm{family.Add(registry.ProofEntry{
	Name: "PolishCoverCountableIffOpen",
	Key:  "prop_c48bc6c9701367b8",
	Build: family.Card(
		Statement{
			Binders:    "∀G:group_ops(A). ∀T:set(set(A)). ∀N:set(A).",
			Hypotheses: []string{"polish_cover_on(G, T, N)"},
			Conclusion: "(countable(left_cosets(G.mul, G.carrier, N)) ⇔ N ∈ T) ∧ " +
				"(countable(left_cosets(G.mul, G.carrier, N)) ∨ " +
				"    card_le(𝕌⟨A:set(num)⟩, left_cosets(G.mul, G.carrier, N)))",
		},
		"A Polishable subgroup is Borel. Apply CountableIndexBorelSubgroupClopen, "+
			"OpenSubgroupCountableIndex and BorelSubgroupIndexDichotomy."),
	Deps: []registry.EntryLike{
		CountableIndexBorelSubgroupClopen,
		OpenSubgroupCountableIndex,
		BorelSubgroupIndexDichotomy,
	},
	Reading: "A Polishable subgroup is Borel. Apply CountableIndexBorelSubgroupClopen, " +
		"OpenSubgroupCountableIndex and BorelSubgroupIndexDichotomy.",
})}

var ClosedCoverQuotientPolish = closedCoverQuotientPolishThm{family.Add(registry.ProofEntry{
	Name: "ClosedCoverQuotientPolish",
	Key:  "prop_e5b5262fc94271ed",
	Build: family.Card(
		Statement{
			Binders:    "∀G:group_ops(A). ∀T:set(set(A)). ∀N:set(A).",
			Hypotheses: []string{"polish_cover_on(G, T, N)", "closed_in(T, N)"},
			Conclusion: "polish_abelian_group(quotient_group(G, N), " +
				"    quotient_topology(T, λx:A. left_coset(G.mul, x, N))) ∧ " +
				"(N ∉ T ⇒ " +
				"    (∀c:set(A). " +
				"        c ∈ left_cosets(G.mul, G.carrier, N) ⇒ " +
				"        ¬({c} ∈ quotient_topology(T, λx:A. left_coset(G.mul, x, N)))))",
		},
		"The quotient of a Polish group by a closed subgroup is Polish (ClosedSubgroupQuotientPolish). "+
			"The quotient map is open; an isolated coset would make its inverse image, hence N, open."),
	Deps: []registry.EntryLike{
		polish_group.PolishCoverOnDef,
		polish_group.ClosedSubgroupQuotientPolish,
	},
	Reading: "The quotient of a Polish group by a closed subgroup is Polish. The " +
		"quotient map is open; an isolated coset would make its inverse image, hence N, open.",
})}

var NonclosedCoverCantorRepresentatives = nonclosedCoverCantorRepresentativesThm{family.Add(registry.ProofEntry{
	Name: "NonclosedCoverCantorRepresentatives",
	Key:  "prop_f1cb47ac4c5b6be0",
	Build: family.Card(
		Statement{
			Binders:    "∀G:group_ops(A). ∀T:set(set(A)). ∀N:set(A).",
			Hypotheses: []string{"polish_cover_on(G, T, N)", "¬closed_in(T, N)"},
			Conclusion: "meager(subtopology(T, closure(T, N)), N) ∧ " +
				"(∃c:((num → bool) → A). " +
				"    continuous_map(indexed_discrete_topology(𝕌, λk:num. ⊥, λk:num. 𝕌), " +
				"        subtopology(T, closure(T, N)), " +
				"        c) ∧ " +
				"    injective_on(𝕌, c) ∧ " +
				"    (∀x y:(num → bool). ¬(x = y) ⇒ G.mul(c(x), G.inv(c(y))) ∉ N))",
		},
		"In the closed Polish subgroup closure(N), N is dense, proper and Borel, hence "+
			"meager. The Cantor fusion construction for the meager coset relation gives a "+
			"continuous injection of binary sequences with pairwise inequivalent images."),
	Deps: []registry.EntryLike{
		NonmeagerBorelSubgroupOpen,
		polish_group.ClosedSubgroupPolish,
		baire_category.MycielskiIndependentCantorSet,
	},
	Reading: "The continuous Cantor parametrization is an additional " +
		"conclusion beyond the existing cardinal-only Mycielski card; its " +
		"finite-cylinder fusion proof must establish continuity explicitly.",
})}
