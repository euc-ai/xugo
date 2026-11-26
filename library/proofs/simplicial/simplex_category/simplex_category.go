// simplex_category.go — the simplex category Δ. Its objects are the
// natural numbers, [n] standing for the ordered set 0, …, n, and its
// morphisms from [m] to [n] the monotone maps, which the simplicial_set
// chapter already holds as the m-simplices of the standard simplex Δⁿ:
// `standard_simplex(n, m)`, the monotone sequences `num → num` into
// 0 .. n padded with zero past m. The padding is the normalization of
// a map off 0 .. m, so the identity of [n] is the identity map
// normalized and a composite is the composite normalized again. The
// category is assembled from this hom data, so a simplicial set is a
// functor on its opposite and the nerve a functor into those, both
// stated in the simplicial_operator chapter.

package simplex_category

import (
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// SimplexCategoryDef — `simplex_category`: the category Δ, assembled
// from the monotone maps [m] → [n] padded with zero past m.
var SimplexCategoryDef = simplexCategoryDefThm{family.Define(registry.DefEntry{
	Name:  "SimplexCategoryDef",
	Key:   "prop_743461cc37898f80",
	Const: "simplex_category",
	Type:  "category_ops(num, morphism_triple(num, num → num))",
	Equations: []string{
		"simplex_category = " +
			"category_from_hom(𝕌, " +
			"    λm:num. λn:num. standard_simplex_simplices(n, m), " +
			"    λn:num. normalize_on(0 .. n, 0, λa:num. a), " +
			"    λl:num. λm:num. λn:num. λg:(num → num). λf:(num → num). normalize_on(0 .. l, 0, g ∘ f))",
	},
	Reading: "Δ([m], [n]) is standard_simplex(n, m), the monotone maps [m] → [n] " +
		"with zero past m — their normalization off 0 .. m. A composite is normalized " +
		"again: past l the inner map is zero and the outer map need not vanish at zero.",
})}

// SimplexCategory — Δ is a category.
var SimplexCategory = simplexCategoryThm{family.Add(registry.ProofEntry{
	Name: "SimplexCategory",
	Key:  "prop_dc1bea68deda2ed7",
	Deps: []registry.EntryLike{
		SimplexCategoryDef,
		category.CategoryFromHom,
		simplicial_set.InStandardSimplex,
	},
	Build: family.Card("category(simplex_category)",
		"CategoryFromHom at the hom data: the normalized identity of [n] is monotone on 0 .. n, "+
			"bounded by n and zero past n, so it lies in standard_simplex(n, n); the normalized "+
			"composite of monotone maps [l] → [m] and [m] → [n] is monotone on 0 .. l, bounded by n "+
			"and zero past l; the unit and associativity laws hold on 0 .. l pointwise, since a "+
			"normalized map reads its map there (NormalizeOnIn) and a composite normalized reads the "+
			"composite (NormalizeOnComposeInner), and past l both sides are zero (NormalizeOnEqIff)"),
})}
