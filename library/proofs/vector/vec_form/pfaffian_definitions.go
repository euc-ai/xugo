// The form Pfaffian is the homogeneous component of the algebraic Pfaffian.

package vec_form

import (
	_ "github.com/euc-ai/xugo/library/proofs/vector/pfaffian"
	"github.com/euc-ai/xugo/library/registry"
)

var FormPfaffianDef = formPfaffianDefThm{family.Define(registry.DefEntry{
	Name:  "FormPfaffianDef",
	Key:   "prop_41b39fec69bd6369",
	Const: "vec_form_pfaffian",
	Type: "num → " +
		"set(num → real) → " +
		"num → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"((num → real) → (num → num → real) → real)",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{evenFormRingDef, formDegreeTermDef},
	Reading: "For an r by r matrix of two-forms, each matching contributes r/2 factors " +
		"and hence degree r. The empty Pfaffian is the normalized unit zero-form, and odd orders " +
		"give zero. The ordered-matching sign convention is the algebraic Pfaffian convention.",
	Equations: []string{
		"∀n r:num. ∀U:set(num → real). ∀B:(num → num → (num → real) → (num → num → real) → real). " +
			"    vec_form_pfaffian⟨n⟩(U, r, B) = " +
			"    pfaffian(vec_even_form_ring⟨n⟩(U), r, (λi:num. λj:num. vec_form_degree_term(2, B(i, j))), r)",
	},
})}
