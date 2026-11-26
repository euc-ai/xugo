// The explicit skew connection solves the first structure equation uniquely.

package riemannian

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var StructureCoefficientsSmooth = structureCoefficientsSmoothThm{family.Add(registry.ProofEntry{
	Name: "StructureCoefficientsSmooth",
	Key:  "prop_2787192f74d09234",
	Deps: []registry.EntryLike{
		structureCoefficientsDef,
		CoframeForm,
		PositiveFrameDef,
		vec_form.ExteriorDerivativeForm,
		vec_form.FormOnDef,
		vec_smooth.SmoothSum,
		vec_smooth.SmoothMul,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real).",
		Hypotheses: []string{"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)"},
		Conclusion: "(∀a b d:num. " +
			"    vec_smooth_on⟨n⟩(«chart image»(c), " +
			"        λy:(num → real). riemannian_structure_coefficients⟨n⟩(g, c, E, y, a, b, d))) ∧ " +
			"(∀y:(num → real). ∀a b d:num. " +
			"    riemannian_structure_coefficients⟨n⟩(g, c, E, y, a, b, d) = " +
			"    -riemannian_structure_coefficients⟨n⟩(g, c, E, y, a, d, b))",
	},
		"The coordinate expansion of dθ has smooth coefficients, and evaluation on smooth frame "+
			"columns uses finite sums and products. Alternation exchanges the last two indices with "+
			"a minus sign; the guards make every inactive index or exterior point zero."),
})}

var CoframeStructureEquation = coframeStructureEquationThm{family.Add(registry.ProofEntry{
	Name: "CoframeStructureEquation",
	Key:  "prop_aed2e8f08da489bf",
	Deps: []registry.EntryLike{
		CoframeTwoFormExpansion,
		CoframeForm,
		structureCoefficientsDef,
		vec_form.ExteriorDerivativeForm,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"∀a:num.",
		Hypotheses: []string{"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)", "a < n"},
		Conclusion: "vec_exterior_derivative⟨n⟩(«chart image»(c), " +
			"    1, " +
			"    riemannian_coframe⟨n⟩(g, c, E, a, 0)) = " +
			"(λy:(num → real). λP:(num → num → real). " +
			"    (&1 / &2) * " +
			"    (Σ_{b<n} Σ_{d<n} riemannian_structure_coefficients⟨n⟩(g, c, E, y, a, b, d) * " +
			"        vec_form_wedge⟨n⟩(«chart image»(c), " +
			"            1, " +
			"            1, " +
			"            riemannian_coframe⟨n⟩(g, c, E, b, 0), " +
			"            riemannian_coframe⟨n⟩(g, c, E, d, 0), " +
			"            y, " +
			"            P)))",
	},
		"Apply the two-form expansion to dθ^a. Its values on two frame columns are exactly the defined "+
			"structure coefficients, and normalization handles points outside the coordinate image."),
})}

var ConnectionSkew = connectionSkewThm{family.Add(registry.ProofEntry{
	Name: "ConnectionSkew",
	Key:  "prop_e2252b8c0bd7400f",
	Deps: []registry.EntryLike{
		ConnectionDef,
		StructureCoefficientsSmooth,
		CoframeForm,
		vec_form.FormOnDef,
		vec_form.FormSkewMatrixOnDef,
		vec_smooth.SmoothSum,
		vec_smooth.SmoothMul,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real).",
		Hypotheses: []string{"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)"},
		Conclusion: "vec_form_skew_matrix_on⟨n⟩(«chart image»(c), 1, n, riemannian_connection⟨n⟩(g, c, E))",
	},
		"Smooth structure coefficients multiply the coframe one-forms, giving a "+
			"normalized matrix of one-forms. Antisymmetry in the last two coefficient indices "+
			"makes the formula negate when a and b are exchanged, including a zero diagonal."),
})}

var ConnectionTorsionFree = connectionTorsionFreeThm{family.Add(registry.ProofEntry{
	Name: "ConnectionTorsionFree",
	Key:  "prop_9fe83cacbc3c532",
	Deps: []registry.EntryLike{
		ConnectionDef,
		ConnectionSkew,
		CoframeStructureEquation,
		CoframeDual,
		StructureCoefficientsSmooth,
		vec_form.WedgeDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real).",
		Hypotheses: []string{"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)"},
		Conclusion: "(λi:num. λj:num. λy:(num → real). λP:(num → num → real). " +
			"    vec_form_matrix_derivative⟨n⟩(«chart image»(c), " +
			"        1, " +
			"        n, " +
			"        1, " +
			"        riemannian_coframe⟨n⟩(g, c, E), " +
			"        i, " +
			"        j, " +
			"        y, " +
			"        P) + " +
			"    vec_form_matrix_product⟨n⟩(«chart image»(c), " +
			"        1, " +
			"        1, " +
			"        n, " +
			"        n, " +
			"        1, " +
			"        riemannian_connection⟨n⟩(g, c, E), " +
			"        riemannian_coframe⟨n⟩(g, c, E), " +
			"        i, " +
			"        j, " +
			"        y, " +
			"        P)) = " +
			"«zero matrix»",
	},
		"Evaluate dθ^a+A_ab∧θ^b on each pair of frame vectors. The connection coefficient "+
			"difference is exactly the negative structure coefficient, so all two-form "+
			"entries vanish; matrix padding gives equality also outside the n by 1 block."),
})}

var ConnectionUnique = connectionUniqueThm{family.Add(registry.ProofEntry{
	Name: "ConnectionUnique",
	Key:  "prop_93dad0b4144c8435",
	Deps: []registry.EntryLike{
		ConnectionTorsionFree,
		ConnectionSkew,
		CoframeExpansion,
		CoframeDual,
		vec_form.FormSkewMatrixOnDef,
		vec_form.WedgeDef,
	},
	Reading: "Both skewness and the whole torsion equation are essential. " +
		"Normalization and matrix padding give literal uniqueness as a total " +
		"matrix-valued form, including the zero-dimensional empty matrix.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"∀B:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"vec_form_skew_matrix_on⟨n⟩(«chart image»(c), 1, n, B)",
			"(λi:num. λj:num. λy:(num → real). λP:(num → num → real). " +
				"    vec_form_matrix_derivative⟨n⟩(«chart image»(c), " +
				"        1, " +
				"        n, " +
				"        1, " +
				"        riemannian_coframe⟨n⟩(g, c, E), " +
				"        i, " +
				"        j, " +
				"        y, " +
				"        P) + " +
				"    vec_form_matrix_product⟨n⟩(«chart image»(c), " +
				"        1, " +
				"        1, " +
				"        n, " +
				"        n, " +
				"        1, " +
				"        B, " +
				"        riemannian_coframe⟨n⟩(g, c, E), " +
				"        i, " +
				"        j, " +
				"        y, " +
				"        P)) = " +
				"«zero matrix»",
		},
		Conclusion: "B = riemannian_connection⟨n⟩(g, c, E)",
	},
		"Subtract the explicit connection. For the difference, skewness makes its "+
			"frame coefficients antisymmetric in the first two indices, while zero "+
			"torsion makes them symmetric in the last two; cycling these symmetries "+
			"makes each coefficient its own negative and hence zero over the reals."),
})}
