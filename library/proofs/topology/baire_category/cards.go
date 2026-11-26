package baire_category

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/topology/borel_space"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// MeagerCountableUnion — A countable union of meager sets is meager.
var MeagerCountableUnion = meagerCountableUnionThm{family.Add(registry.ProofEntry{
	Name: "MeagerCountableUnion",
	Key:  "prop_1abb1df59fc21cc8",
	Deps: []registry.EntryLike{
		cardinal.PairNumBijection,
		cardinal.CardEqSym,
		cardinal.CardEqDef,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀a:(num → set(A)).",
		Hypotheses: []string{
			"∀n:num. meager(T, a(n))",
		},
		Conclusion: "meager(T, ⋃image(a, 𝕌))",
	},
		"Choose for each n a sequence of nowhere dense sets covering a(n) and enumerate the pairs "+
			"of indices along a bijection of ℕ × ℕ with ℕ (PairNumBijection, read through CardEqSym and "+
			"CardEqDef); the union of the countably many countable families is one countable family."),
	Reading: "No hypothesis on T is needed: the definition " +
		"of meager reads nowhere_dense in T, whatever T is.",
})}

// BorelBaireProperty — Every Borel set has the Baire property.
var BorelBaireProperty = borelBairePropertyThm{family.Add(registry.ProofEntry{
	Name: "BorelBaireProperty",
	Key:  "prop_3e74eaf4a21e7573",
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(A).",
		Hypotheses: []string{
			"is_topology(T)",
			"s ∈ borel_sets(T)",
		},
		Conclusion: "baire_property(T, s)",
	},
		"The sets with the Baire property form a sigma algebra on the carrier containing the open "+
			"sets, and borel_sets(T) is the least such sigma algebra. An open set is its own witness. "+
			"If s differs from the open u by a meager set, the complement of s differs from the "+
			"interior of the complement of u by a meager set, since the frontier of an open set is "+
			"closed with empty interior, and so nowhere dense (ClosedNowhereDenseIffEmptyInterior). A "+
			"countable union is witnessed by the union of the witnesses, its symmetric difference "+
			"lying in the union of the meager differences, meager by MeagerCountableUnion."),
	Deps: []registry.EntryLike{
		MeagerCountableUnion,
		borel_space.BorelSetsDef,
		topological_space.FrontierClosed,
		topological_space.InteriorOpen,
		ClosedNowhereDenseIffEmptyInterior,
	},
	Reading: "The carrier itself is open, so the sigma algebra has " +
		"the carrier as its top. No separability or metrizability enters.",
})}
