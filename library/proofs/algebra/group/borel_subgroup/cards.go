package borel_subgroup

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/topology/baire_category"
	"github.com/euc-ai/xugo/library/registry"
)

// PettisLemma — A non-meager set with the Baire property has an identity neighbourhood inside its difference set.
var PettisLemma = pettisLemmaThm{family.Add(registry.ProofEntry{
	Name: "PettisLemma",
	Key:  "prop_1384006170a38433",
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀T:set(set(A)). ∀s:set(A).",
		Hypotheses: []string{
			"polish_abelian_group(G, T)",
			"baire_property(T, s)",
			"¬meager(T, s)",
		},
		Conclusion: "∃u:set(A). u ∈ T ∧ G.one ∈ u ∧ u ⊆ set_mul(G.mul, s, set_inv(G.inv, s))",
	},
		"Pettis: s differs from an open set v by a meager set, and v is nonempty since s "+
			"is not meager. The set v·v⁻¹ is open, a union of translates of v, and contains "+
			"the identity. For g in it the translate g·v meets v in a nonempty open set, not "+
			"meager by PolishBaire, while (g·v ∩ v) ∖ (g·s ∩ s) lies in (g·v ∖ g·s) ∪ (v ∖ "+
			"s), meager since translation is a homeomorphism. So g·s meets s, and g ∈ s·s⁻¹."),
	Deps: []registry.EntryLike{
		baire_category.PolishBaire,
		baire_category.MeagerCountableUnion,
		polish_group.PolishAbelianGroupDef,
	},
	Reading: "The group is abelian only because polish_abelian_group says so; the " +
		"argument reads only continuity of the operations. Translation by a group " +
		"element is a homeomorphism of T, which carries meager sets to meager sets.",
})}

// NonmeagerBorelSubgroupOpen — A non-meager Borel subgroup is open and closed.
var NonmeagerBorelSubgroupOpen = nonmeagerBorelSubgroupOpenThm{family.Add(registry.ProofEntry{
	Name: "NonmeagerBorelSubgroupOpen",
	Key:  "prop_bc9fccf5c6aa590f",
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀T:set(set(A)). ∀N:set(A).",
		Hypotheses: []string{
			"polish_abelian_group(G, T)",
			"subgroup(G, N)",
			"N ∈ borel_sets(T)",
			"¬meager(T, N)",
		},
		Conclusion: "N ∈ T ∧ closed_in(T, N)",
	},
		"BorelBaireProperty gives N the Baire property and PettisLemma an open neighbourhood of the "+
			"identity inside N·N⁻¹, which is N. A subgroup containing a neighbourhood of the identity is "+
			"the union of the translates of that neighbourhood by its elements, hence open; the complement "+
			"of an open subgroup is the union of its other cosets, each open, so the subgroup is closed."),
	Deps:    []registry.EntryLike{PettisLemma, baire_category.BorelBaireProperty},
	Reading: "Borel is used only for the Baire property; the conclusion is both open and closed.",
})}

// CountableIndexBorelSubgroupClopen — A Borel subgroup of countable index is open and closed.
var CountableIndexBorelSubgroupClopen = countableIndexBorelSubgroupClopenThm{family.Add(registry.ProofEntry{
	Name: "CountableIndexBorelSubgroupClopen",
	Key:  "prop_8d4820966a0396fa",
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀T:set(set(A)). ∀N:set(A).",
		Hypotheses: []string{
			"polish_abelian_group(G, T)",
			"subgroup(G, N)",
			"N ∈ borel_sets(T)",
			"countable(left_cosets(G.mul, G.carrier, N))",
		},
		Conclusion: "N ∈ T ∧ closed_in(T, N)",
	},
		"The carrier is the union of countably many cosets, each a translate of N. Were N "+
			"meager, every translate would be meager and MeagerCountableUnion would make the "+
			"carrier meager; the carrier is a nonempty open set, containing the identity, which "+
			"PolishBaire forbids. So N is not meager and NonmeagerBorelSubgroupOpen applies."),
	Deps: []registry.EntryLike{
		NonmeagerBorelSubgroupOpen,
		baire_category.MeagerCountableUnion,
		baire_category.PolishBaire,
	},
	Reading: "Countable index includes finite index. The converse is " +
		"OpenSubgroupCountableIndex, so for a Borel subgroup countable index and openness coincide.",
})}

// MeagerSubgroupContinuumIndex — A meager subgroup has at least continuum many cosets.
var MeagerSubgroupContinuumIndex = meagerSubgroupContinuumIndexThm{family.Add(registry.ProofEntry{
	Name: "MeagerSubgroupContinuumIndex",
	Key:  "prop_d2778bbf256f4c73",
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀T:set(set(A)). ∀N:set(A).",
		Hypotheses: []string{
			"polish_abelian_group(G, T)",
			"subgroup(G, N)",
			"meager(T, N)",
		},
		Conclusion: "card_le(𝕌⟨A:set(num)⟩, left_cosets(G.mul, G.carrier, N))",
	},
		"The coset relation, the pairs (x, y) of the carrier with x·y⁻¹ ∈ N, is the preimage of N under "+
			"(x, y) ↦ x·y⁻¹, a continuous open map of the product onto G, so OpenMapMeagerPreimage makes it "+
			"meager in the product topology. The group has no isolated point: an isolated point would make "+
			"the identity open and N, which contains it, non-meager. MycielskiIndependentCantorSet gives "+
			"continuum many points in pairwise distinct cosets, and the coset map is injective on them."),
	Deps: []registry.EntryLike{
		baire_category.OpenMapMeagerPreimage,
		baire_category.MycielskiIndependentCantorSet,
		baire_category.PolishBaire,
	},
	Reading: "The carrier is nonempty, as it contains the identity, which " +
		"Mycielski's theorem needs. The map (x, y) ↦ x·y⁻¹ is open because the " +
		"image of a product of open sets is a union of translates of an open set.",
})}

// NonclosedBorelSubgroupContinuumIndex — A Borel subgroup that is not closed has at least continuum many cosets.
var NonclosedBorelSubgroupContinuumIndex = nonclosedBorelSubgroupContinuumIndexThm{family.Add(registry.ProofEntry{
	Name: "NonclosedBorelSubgroupContinuumIndex",
	Key:  "prop_98ddedc52dbf469b",
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀T:set(set(A)). ∀N:set(A).",
		Hypotheses: []string{
			"polish_abelian_group(G, T)",
			"subgroup(G, N)",
			"N ∈ borel_sets(T)",
			"¬closed_in(T, N)",
		},
		Conclusion: "card_le(𝕌⟨A:set(num)⟩, left_cosets(G.mul, G.carrier, N))",
	},
		"A Borel subgroup that is not closed is not both open and closed, so by "+
			"NonmeagerBorelSubgroupOpen it is meager, and MeagerSubgroupContinuumIndex applies."),
	Deps: []registry.EntryLike{NonmeagerBorelSubgroupOpen, MeagerSubgroupContinuumIndex},
	Reading: "Closed is read in T; a closed Borel subgroup may still " +
		"have continuum many cosets, so only one direction is a dichotomy.",
})}

// BorelSubgroupIndexDichotomy — A Borel subgroup has countably many cosets or at least continuum many.
var BorelSubgroupIndexDichotomy = borelSubgroupIndexDichotomyThm{family.Add(registry.ProofEntry{
	Name: "BorelSubgroupIndexDichotomy",
	Key:  "prop_fa68627ac16217c5",
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀T:set(set(A)). ∀N:set(A).",
		Hypotheses: []string{
			"polish_abelian_group(G, T)",
			"subgroup(G, N)",
			"N ∈ borel_sets(T)",
		},
		Conclusion: "countable(left_cosets(G.mul, G.carrier, N)) ∨ " +
			"card_le(𝕌⟨A:set(num)⟩, left_cosets(G.mul, G.carrier, N))",
	},
		"If N is not meager it is open by NonmeagerBorelSubgroupOpen and has countable index by "+
			"OpenSubgroupCountableIndex; if it is meager, MeagerSubgroupContinuumIndex gives the continuum."),
	Deps: []registry.EntryLike{
		NonmeagerBorelSubgroupOpen,
		OpenSubgroupCountableIndex,
		MeagerSubgroupContinuumIndex,
	},
	Reading: "The two cases are decided by meagerness of N, not by closedness: a closed " +
		"subgroup of uncountable index falls under the second case. Both cases can hold only " +
		"when the continuum is countable, which it is not, but the statement does not need that.",
})}
