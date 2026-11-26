// The two-open-cover complex and its maps fix the difference convention α|U∩V − β|U∩V.

package de_rham_cover

import (
	"github.com/euc-ai/xugo/library/registry"
)

var CoverComplexDef = coverComplexDefThm{family.Define(registry.DefEntry{
	Name:  "CoverComplexDef",
	Key:   "prop_fbd135651a835fe0",
	Const: "de_rham_cover_complex",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(A) → " +
		"set(A) → " +
		"complex_ops(real, " +
		"    prod(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real, " +
		"        prod(set(A), A → num → real) → (num → real) → (num → num → real) → real))",
	Dim:  "n",
	Deps: []registry.EntryLike{},
	Reading: "The middle complex is a pair of forms, with the U and V degree " +
		"carriers separately guarded. All form hosts have the same pointwise " +
		"operations; the differential uses the respective open-submanifold structures.",
	Equations: []string{"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U V:set(A). " +
		"    de_rham_cover_complex⟨n⟩(T, 𝒜, U, V) = " +
		"    pack_complex((λz:prod( " +
		"                prod(set(A), A → num → real) → (num → real) → (num → num → real) → real, " +
		"                prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
		"        λw:prod(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real, " +
		"                prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
		"            (de_rham_complex⟨n⟩(T, 𝒜).add(fst(z), fst(w)), " +
		"                de_rham_complex⟨n⟩(T, 𝒜).add(snd(z), snd(w)))), " +
		"        (de_rham_complex⟨n⟩(T, 𝒜).zero, de_rham_complex⟨n⟩(T, 𝒜).zero), " +
		"        (λz:prod(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real, " +
		"                prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
		"            (de_rham_complex⟨n⟩(T, 𝒜).neg(fst(z)), de_rham_complex⟨n⟩(T, 𝒜).neg(snd(z)))), " +
		"        (λa:real. " +
		"        λz:prod(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real, " +
		"                prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
		"            (de_rham_complex⟨n⟩(T, 𝒜).smul(a, fst(z)), " +
		"                de_rham_complex⟨n⟩(T, 𝒜).smul(a, snd(z)))), " +
		"        (λq:num. " +
		"            set_cross(de_rham_complex⟨n⟩(subtopology(T, U), " +
		"                    open_submanifold_atlas⟨n⟩(T, 𝒜, U)).terms(q), " +
		"                de_rham_complex⟨n⟩(subtopology(T, V), " +
		"                    open_submanifold_atlas⟨n⟩(T, 𝒜, V)).terms(q))), " +
		"        (λq:num. " +
		"        λz:prod(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real, " +
		"                prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
		"            (de_rham_complex⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U)).d(q)( " +
		"                    fst(z)), " +
		"                de_rham_complex⟨n⟩(subtopology(T, V), open_submanifold_atlas⟨n⟩(T, 𝒜, V)).d(q)( " +
		"                    snd(z)))))"},
})}

var CoverRestrictionDef = coverRestrictionDefThm{family.Define(registry.DefEntry{
	Name:  "CoverRestrictionDef",
	Key:   "prop_f3d545a2b970a2fb",
	Const: "de_rham_cover_restriction",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(A) → " +
		"set(A) → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"prod(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real, " +
		"    prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Dim:  "n",
	Deps: []registry.EntryLike{},
	Reading: "This map restricts the same global form to both opens. It does " +
		"not depend on the degree, which enters only through the complex carriers.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U V:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    de_rham_cover_restriction⟨n⟩(T, 𝒜, U, V)(ω) = " +
			"    (manifold_form_restrict⟨n⟩(T, 𝒜, U, ω), manifold_form_restrict⟨n⟩(T, 𝒜, V, ω))",
	},
})}

var CoverDifferenceDef = coverDifferenceDefThm{family.Define(registry.DefEntry{
	Name:  "CoverDifferenceDef",
	Key:   "prop_52a13cc87765f63a",
	Const: "de_rham_cover_difference",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(A) → " +
		"set(A) → " +
		"prod(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real, " +
		"    prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim:  "n",
	Deps: []registry.EntryLike{},
	Reading: "The order is U minus V. Reversing this convention reverses the connecting " +
		"homomorphism. Both restrictions are normalized families on the intersection.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U V:set(A). " +
			"∀z:prod(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real, " +
			"        prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    de_rham_cover_difference⟨n⟩(T, 𝒜, U, V)(z) = " +
			"    de_rham_complex⟨n⟩(T, 𝒜).add(«open restriction»(U, U ∩ V, fst(z)), " +
			"        de_rham_complex⟨n⟩(T, 𝒜).neg(«open restriction»(V, U ∩ V, snd(z))))",
	},
})}

var ConnectingDef = connectingDefThm{family.Define(registry.DefEntry{
	Name:  "ConnectingDef",
	Key:   "prop_566ac1d3ec9e866e",
	Const: "de_rham_connecting",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(A) → " +
		"set(A) → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Dim:  "n",
	Deps: []registry.EntryLike{CoverComplexDef, CoverRestrictionDef, CoverDifferenceDef},
	Reading: "The connecting map raises degree by one. It uses the generic lift, " +
		"differentiate and glue construction; its value on a genuine class is characterized " +
		"only under the short-exactness hypothesis, independently of all choices.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U V:set(A). " +
			"∀k:num. " +
			"∀s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    de_rham_connecting⟨n⟩(T, 𝒜, U, V)(k, s) = " +
			"    coconnecting_hom(de_rham_complex⟨n⟩(T, 𝒜), " +
			"        de_rham_cover_complex⟨n⟩(T, 𝒜, U, V), " +
			"        (λq:num. de_rham_cover_restriction⟨n⟩(T, 𝒜, U, V)), " +
			"        (λq:num. de_rham_cover_difference⟨n⟩(T, 𝒜, U, V)), " +
			"        k, " +
			"        s)",
	},
})}
