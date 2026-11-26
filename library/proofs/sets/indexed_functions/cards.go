package indexed_functions

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

var OverrideIndexedFunctions = overrideIndexedFunctionsThm{family.Add(registry.ProofEntry{
	Name: "OverrideIndexedFunctions",
	Key:  "prop_d22a3c6f5a78bcc4",
	Build: family.Card(Statement{
		Binders:    "∀J:set(I). ∀v z:(I → A). ∀X:(I → set(A)).",
		Hypotheses: []string{"∀i:I. i ∈ J ⇒ v(i) ∈ X(i)"},
		Conclusion: "override_on(J, v, z) ∈ indexed_functions(J, z, X)",
	},
		"Restricting v to J with the prescribed values z off J gives an indexed "+
			"function: on J it is v, in the factors by hypothesis; off J it is z."),
})}

var IndexedFunctionsFinite = indexedFunctionsFiniteThm{family.Add(registry.ProofEntry{
	Name: "IndexedFunctionsFinite",
	Reading: "finite(J) is load-bearing: an infinite J with two-point factors " +
		"gives uncountably many maps. An empty factor on J makes the set empty.",
	Key:  "prop_b0805b3594c93f78",
	Deps: []registry.EntryLike{cardinality.FiniteFunspace},
	Build: family.Card(Statement{
		Binders:    "∀J:set(I). ∀z:(I → A). ∀X:(I → set(A)).",
		Hypotheses: []string{"finite(J)", "∀i:I. i ∈ J ⇒ finite(X(i))"},
		Conclusion: "finite(indexed_functions(J, z, X))",
	},
		"The indexed functions lie among the maps from J into the finite union "+
			"of the factors that take z off J; shift z to a constant default by a "+
			"bijection or induct on J, and read the finite count off FiniteFunspace."),
})}
