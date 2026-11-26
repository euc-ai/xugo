package real_product

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var ProductOfBinomials = productOfBinomialsThm{family.Add(registry.ProofEntry{
	Name: "ProductOfBinomials",
	Key:  "prop_ad04d9fd303ef85d",
	Reading: "The sum is over every subset of F, the one that takes b; with a constantly " +
		"1 it is the sum over the subsets of the products of b. finite(F) is load-bearing: " +
		"over ℕ with a constantly 1 and b nonzero at one point the left side is 2 and the " +
		"right side, heard at infinitely many subsets, is 0. With F empty both sides are 1.",
	Deps: []registry.EntryLike{ProductClauses},
	Build: family.Card(Statement{
		Binders: "∀F:set(A). ∀a b:(A → real).",
		Hypotheses: []string{
			"finite(F)",
		},
		Conclusion: "Π_{v∈F} (a(v) + b(v)) = Σ_{S∈{S:set(A) | S ⊆ F}} (Π_{v∈F ∖ S} a(v)) * Π_{v∈S} b(v)",
	},
		"A finite product of binomials is the sum, over the subsets that take the second term, of the "+
			"mixed products. Induct on F. The subsets of insert(v, F) are the subsets of F and their images "+
			"under insert(v), disjointly (PowersetClauses; hypercube's SumInsert is the same split, stated "+
			"above this chapter): on the first the factor a(v) joins the product over the complement, on the "+
			"second b(v) joins the product over the subset, insert(v) being injective on the subsets of F."),
})}
