// The shuffle product makes forms into a graded commutative algebra.

package vec_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var WedgeForm = wedgeFormThm{family.Add(registry.ProofEntry{
	Name: "WedgeForm",
	Key:  "prop_d5c8899ff962edb0",
	Deps: []registry.EntryLike{WedgeDef, FormOnDef, vec_smooth.SmoothAdd, vec_smooth.SmoothMul},
	Build: family.Card(Statement{
		Binders:    "∀n p q:num. ∀U:set(num → real). ∀α β:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_on⟨n⟩(U, p, α)", "vec_form_on⟨n⟩(U, q, β)"},
		Conclusion: "vec_form_on⟨n⟩(U, p + q, vec_form_wedge⟨n⟩(U, p, q, α, β))",
	},
		"Expand each factor in increasing coordinate minors and group the shuffle terms by their "+
			"combined coordinate list. Repeated coordinates cancel and the surviving coefficients "+
			"are finite sums of products of smooth coefficients; the defining guard gives zero off U."),
})}

var WedgeBilinear = wedgeBilinearThm{family.Add(registry.ProofEntry{
	Name: "WedgeBilinear",
	Key:  "prop_2061c61b6d5e03c",
	Deps: []registry.EntryLike{WedgeForm, FormModule, WedgeDef},
	Build: family.Card(Statement{
		Binders:    "∀n p q:num. ∀U:set(num → real).",
		Hypotheses: []string{"U ∈ euclidean_topology(n)"},
		Conclusion: "bilinear_map(real_ring, " +
			"    vec_form_module⟨n⟩(U, p), " +
			"    vec_form_module⟨n⟩(U, q), " +
			"    vec_form_module⟨n⟩(U, p + q), " +
			"    vec_form_wedge⟨n⟩(U, p, q))",
	},
		"Distribute the finite shuffle sum through pointwise addition and scalar "+
			"multiplication in either factor. WedgeForm gives the target carrier, and "+
			"FormModule supplies the three module structures required by bilinear_map."),
})}

var WedgeAssociative = wedgeAssociativeThm{family.Add(registry.ProofEntry{
	Name: "WedgeAssociative",
	Key:  "prop_7c673f2a0e0b2398",
	Deps: []registry.EntryLike{WedgeForm, WedgeDef},
	Build: family.Card(Statement{
		Binders: "∀n p q r:num. ∀U:set(num → real). ∀α β γ:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"vec_form_on⟨n⟩(U, p, α)",
			"vec_form_on⟨n⟩(U, q, β)",
			"vec_form_on⟨n⟩(U, r, γ)",
		},
		Conclusion: "vec_form_wedge⟨n⟩(U, p + q, r, vec_form_wedge⟨n⟩(U, p, q, α, β), γ) = " +
			"vec_form_wedge⟨n⟩(U, p, q + r, α, vec_form_wedge⟨n⟩(U, q, r, β, γ))",
	},
		"Both iterated sums index ordered partitions of the columns into three increasing "+
			"blocks of sizes p, q and r. The bijection between the two nestings preserves the "+
			"product of permutation signs and the three evaluations; normalization agrees outside U."),
})}

var WedgeGradedCommutative = wedgeGradedCommutativeThm{family.Add(registry.ProofEntry{
	Name: "WedgeGradedCommutative",
	Key:  "prop_7cdf6c58bd206e6e",
	Deps: []registry.EntryLike{WedgeDef},
	Build: family.Card(Statement{
		Binders:    "∀n p q:num. ∀U:set(num → real). ∀α β:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_on⟨n⟩(U, p, α)", "vec_form_on⟨n⟩(U, q, β)"},
		Conclusion: "vec_form_wedge⟨n⟩(U, p, q, α, β) = " +
			"(λx:(num → real). λP:(num → num → real). (-&1)^(p * q) * vec_form_wedge⟨n⟩(U, q, p, β, α, x, P))",
	},
		"Exchange the two ordered shuffle blocks. Moving p columns past q columns contributes the "+
			"sign (-1)^(pq), and the real-valued factors commute; this includes either block being empty."),
})}

var WedgeUnit = wedgeUnitThm{family.Add(registry.ProofEntry{
	Name: "WedgeUnit",
	Key:  "prop_57dc8591452bc0bb",
	Reading: "The multiplicative unit is one on U and zero off U. A globally constant-one " +
		"function would violate the form normalization whenever U is a proper open set.",
	Deps: []registry.EntryLike{WedgeDef, FormZeroDegree, vec_smooth.SmoothConst},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀U:set(num → real). ∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_on⟨n⟩(U, k, ω)"},
		Conclusion: "vec_form_on⟨n⟩(U, 0, «unit») ∧ " +
			"vec_form_wedge⟨n⟩(U, 0, k, «unit», ω) = ω ∧ " +
			"vec_form_wedge⟨n⟩(U, k, 0, ω, «unit») = ω",
	},
		"The normalized constant one is locally constant on the open U and is a zero-form by "+
			"FormZeroDegree. With one shuffle block empty the identity is the sole shuffle, and "+
			"the other factor reads exactly its active matrix block; both sides are zero off U."),
})}
