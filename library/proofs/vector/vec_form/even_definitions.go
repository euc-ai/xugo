// Even inhomogeneous forms use actual degrees and the finite wedge convolution.

package vec_form

import (
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/registry"
)

var evenFormOnDef = evenFormOnDefThm{family.Define(registry.DefEntry{
	Name:       "evenFormOnDef",
	Key:        "prop_913ecfeddd71f17",
	Const:      "vec_even_form_on",
	Type:       "num → set(num → real) → (num → (num → real) → (num → num → real) → real) → bool",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{FormOnDef},
	Reading: "The component index is the actual form degree, not half the degree. Every " +
		"component is normalized on U; odd components vanish, and FormAboveDimension forces all " +
		"components above n to vanish. The carrier over the empty open set contains only zero.",
	Equations: []string{
		"∀n:num. ∀U:set(num → real). ∀α:(num → (num → real) → (num → num → real) → real). " +
			"    vec_even_form_on⟨n⟩(U, α) ⇔ " +
			"    U ∈ euclidean_topology(n) ∧ " +
			"    (∀q:num. vec_form_on⟨n⟩(U, q, α(q)) ∧ (¬nat_even(q) ⇒ α(q) = «zero»))",
	},
})}

var formDegreeTermDef = formDegreeTermDefThm{family.Define(registry.DefEntry{
	Name:  "formDegreeTermDef",
	Key:   "prop_9c809faec69bc4b7",
	Const: "vec_form_degree_term",
	Type: "num → " +
		"((num → real) → (num → num → real) → real) → " +
		"(num → (num → real) → (num → num → real) → real)",
	Reading: "This insertion is defined for every degree. Membership in the " +
		"even-form ring is asserted only for even degrees and normalized forms.",
	Equations: []string{
		"∀k:num. ∀ω:((num → real) → (num → num → real) → real). ∀q:num. " +
			"    vec_form_degree_term(k, ω, q) = COND(q = k, ω, «zero»)",
	},
})}

var evenFormRingDef = evenFormRingDefThm{family.Define(registry.DefEntry{
	Name:       "evenFormRingDef",
	Key:        "prop_c89d32466e0b9e30",
	Const:      "vec_even_form_ring",
	Type:       "num → set(num → real) → ring_ops((num → (num → real) → (num → num → real) → real))",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{evenFormOnDef, formDegreeTermDef, WedgeDef},
	Reading: "Multiplication is convolution by wedge, with p ≤ q guarding natural " +
		"subtraction. Commutativity is on the even carrier only; one is the degree-zero " +
		"form equal to one on U and zero elsewhere. The empty domain gives the zero ring.",
	Equations: []string{
		"∀n:num. ∀U:set(num → real). " +
			"    vec_even_form_ring⟨n⟩(U) = " +
			"    mk_ring((λα:(num → (num → real) → (num → num → real) → real). " +
			"        λβ:(num → (num → real) → (num → num → real) → real). " +
			"        λq:num. " +
			"        λx:(num → real). " +
			"        λP:(num → num → real). " +
			"            α(q, x, P) + β(q, x, P)), " +
			"        (λq:num. «zero»), " +
			"        (λα:(num → (num → real) → (num → num → real) → real). " +
			"        λq:num. " +
			"        λx:(num → real). " +
			"        λP:(num → num → real). " +
			"            -α(q, x, P)), " +
			"        (λα:(num → (num → real) → (num → num → real) → real). " +
			"        λβ:(num → (num → real) → (num → num → real) → real). " +
			"        λq:num. " +
			"        λx:(num → real). " +
			"        λP:(num → num → real). " +
			"            real_sum({p:num | p ≤ q}, " +
			"                λp:num. vec_form_wedge⟨n⟩(U, p, q - p, α(p), β(q - p), x, P))), " +
			"        vec_form_degree_term(0, «unit»), " +
			"        (λα:(num → (num → real) → (num → num → real) → real). " +
			"        λβ:(num → (num → real) → (num → num → real) → real). " +
			"        λq:num. " +
			"        λx:(num → real). " +
			"        λP:(num → num → real). " +
			"            α(q, x, P) - β(q, x, P)), " +
			"        {α:(num → (num → real) → (num → num → real) → real) | vec_even_form_on⟨n⟩(U, α)})",
	},
})}
