// Canonical atlases on Euclidean open sets, open submanifolds and
// products. Product coordinates concatenate two finite blocks.

package smooth_manifold

import "github.com/euc-ai/xugo/library/registry"

// EuclideanAtlasDef — the single identity chart on an open set.
var EuclideanAtlasDef = euclideanAtlasDefThm{family.Define(registry.DefEntry{
	Name:      "EuclideanAtlasDef",
	Key:       "prop_370378167849ab42",
	Const:     "euclidean_atlas",
	Type:      "set(num → real) → set(prod(set(num → real), (num → real) → num → real))",
	Equations: []string{"∀U:set(num → real). euclidean_atlas(U) = {(U, identity_map)}"},
})}

// OpenAtlasDef — all compatible charts whose domains lie in U.
var OpenAtlasDef = openAtlasDefThm{family.Define(registry.DefEntry{
	Name:  "OpenAtlasDef",
	Key:   "prop_4971e452a2303235",
	Const: "open_submanifold_atlas",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(A) → " +
		"set(prod(set(A), A → num → real))",
	Dim:  "n",
	Deps: []registry.EntryLike{CompatibleChartDef},
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U:set(A). " +
			"    open_submanifold_atlas⟨n⟩(T, 𝒜, U) = " +
			"    {c:prod(set(A), A → num → real) | compatible_chart⟨n⟩(T, 𝒜, c) ∧ fst(c) ⊆ U}",
	},
})}

// ProductAtlasDef — chart pairs with n source coordinates followed
// by m target coordinates and a zero tail after n+m.
var ProductAtlasDef = productAtlasDefThm{family.Define(registry.DefEntry{
	Name:  "ProductAtlasDef",
	Key:   "prop_6f9b948ad4ee72d7",
	Const: "smooth_product_atlas",
	Type: "num → " +
		"num → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"set(prod(set(prod(A, B)), prod(A, B) → num → real))",
	Reading: "The suffix holds the two factor dimensions; the resulting chart has dimension n+m. " +
		"The shifted index i-n is read only in the second block. Both factor dimensions may be zero.",
	Dimensions: []string{"n", "m"},
	Equations: []string{
		"∀n m:num. ∀𝒜:set(prod(set(A), A → num → real)). ∀ℬ:set(prod(set(B), B → num → real)). " +
			"    smooth_product_atlas⟨n, m⟩(𝒜, ℬ) = " +
			"    {e:prod(set(prod(A, B)), prod(A, B) → num → real) | " +
			"        ∃c:prod(set(A), A → num → real). ∃d:prod(set(B), B → num → real). " +
			"            c ∈ 𝒜 ∧ " +
			"            d ∈ ℬ ∧ " +
			"            e = " +
			"            (set_cross(fst(c), fst(d)), " +
			"                λp:prod(A, B). λi:num. " +
			"                    COND(i < n, snd(c)(fst(p), i), COND(i < n + m, snd(d)(snd(p), i - n), &0)))}",
	},
})}
