// Exterior differentiation preserves overlap compatibility by the
// Euclidean pullback law and locality on open coordinate overlaps. It is
// linear, hence additive, squares to zero and obeys the graded Leibniz
// rule; against a closed factor ω it takes β ∧ ω to dβ ∧ ω.

package differential_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var ExteriorDerivativeForm = exteriorDerivativeFormThm{family.Add(registry.ProofEntry{
	Name: "ExteriorDerivativeForm",
	Key:  "prop_645d27646dea1bb2",
	Reading: "Restriction to an open overlap agrees locally with the original " +
		"component, so differentiation does not see the zero extension across the " +
		"overlap boundary. No smoothness across a chart boundary is claimed.",
	Deps: []registry.EntryLike{
		ExteriorDerivativeDef,
		FormOnDef,
		vec_form.ExteriorDerivativeForm,
		vec_form.PullbackExteriorDerivative,
		vec_form.FormRestrict,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, k, ω)"},
		Conclusion: "manifold_form_on⟨n⟩(T, 𝒜, k + 1, manifold_exterior_derivative⟨n⟩(T, 𝒜, k, ω))",
	},
		"Each coordinate exterior derivative is a Euclidean form of degree k+1. On an open "+
			"overlap, derivative locality identifies differentiation of the restricted component "+
			"with restriction of its derivative; PullbackExteriorDerivative then differentiates "+
			"the overlap equation. The incompatible-chart guard retains normalization."),
})}

var ExteriorDerivativeLinear = exteriorDerivativeLinearThm{family.Add(registry.ProofEntry{
	Name: "ExteriorDerivativeLinear",
	Key:  "prop_f2025c56c4ece96",
	Deps: []registry.EntryLike{
		ExteriorDerivativeForm,
		FormModule,
		ExteriorDerivativeDef,
		vec_form.ExteriorDerivativeLinear,
	},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "module_homomorphism(real_ring, " +
			"    manifold_form_module⟨n⟩(T, 𝒜, k), " +
			"    manifold_form_module⟨n⟩(T, 𝒜, k + 1), " +
			"    manifold_exterior_derivative⟨n⟩(T, 𝒜, k))",
	},
		"The Euclidean derivative commutes with addition and real scalar multiplication on every "+
			"compatible chart. These are the pointwise operations of the family modules, and both operations "+
			"yield zero on incompatible charts. ExteriorDerivativeForm supplies the output carrier."),
})}

// ExteriorDerivativeAdd — the exterior derivative of a sum of two k-forms
// is the sum of their exterior derivatives: d is a module homomorphism of
// the k-forms into the (k + 1)-forms, so it carries the module sum to the
// module sum, and the module sums are the pointwise sums.
var ExteriorDerivativeAdd = exteriorDerivativeAddThm{family.Add(registry.ProofEntry{
	Name: "ExteriorDerivativeAdd",
	Key:  "prop_b2573234c52a0239",
	Build: family.Theorem(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, k, α)",
			"manifold_form_on⟨n⟩(T, 𝒜, k, β)",
		},
		Conclusion: "manifold_exterior_derivative⟨n⟩(T, " +
			"    𝒜, " +
			"    k, " +
			"    λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"        α(c, y, P) + β(c, y, P)) = " +
			"(λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"    manifold_exterior_derivative⟨n⟩(T, 𝒜, k, α, c, y, P) + " +
			"    manifold_exterior_derivative⟨n⟩(T, 𝒜, k, β, c, y, P))",
	},
		func(
			a *Argument,
			n, k *Expr[Nat],
			T *Expr[Set[Set[A]]],
			𝒜 *Expr[Set[Prod[Set[A], Fun2[A, Nat, Real]]]],
			α, β *Expr[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]],
			αForm, βForm Fact,
		) {
			linear := a.Have(
				"d is linear in degree k",
				"module_homomorphism(real_ring, "+
					"    manifold_form_module⟨n⟩(T, 𝒜, k), "+
					"    manifold_form_module⟨n⟩(T, 𝒜, k + 1), "+
					"    manifold_exterior_derivative⟨n⟩(T, 𝒜, k))",
				By(αForm, FormOnDef, ExteriorDerivativeLinear))
			additive := a.Have(
				"d(α + β) = dα + dβ in the modules",
				"manifold_exterior_derivative⟨n⟩(T, 𝒜, k, manifold_form_module⟨n⟩(T, 𝒜, k).add(α, β)) = "+
					"manifold_form_module⟨n⟩(T, 𝒜, k + 1).add(manifold_exterior_derivative⟨n⟩(T, 𝒜, k, α), "+
					"    manifold_exterior_derivative⟨n⟩(T, 𝒜, k, β))",
				By(αForm, βForm, FormModulePointwise, module_homomorphism.HomAdd.Read(linear)))
			a.Show(
				"the module sums are the pointwise sums",
				By(a.Simplified(additive, Fwd(FormModulePointwise))))
		}),
})}

var ExteriorDerivativeSquareZero = exteriorDerivativeSquareZeroThm{family.Add(registry.ProofEntry{
	Name: "ExteriorDerivativeSquareZero",
	Key:  "prop_fcc86226b5c6145d",
	Deps: []registry.EntryLike{
		ExteriorDerivativeDef,
		ExteriorDerivativeForm,
		vec_form.ExteriorDerivativeSquareZero,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, k, ω)"},
		Conclusion: "manifold_exterior_derivative⟨n⟩(T, " +
			"    𝒜, " +
			"    k + 1, " +
			"    manifold_exterior_derivative⟨n⟩(T, 𝒜, k, ω)) = " +
			"«zero family»",
	},
		"On each compatible chart this is the Euclidean d-squared identity from "+
			"equality of mixed partials. The definition already gives zero on incompatible "+
			"charts, so the identity is equality of total chart families in every degree."),
})}

var ExteriorDerivativeLeibniz = exteriorDerivativeLeibnizThm{family.Add(registry.ProofEntry{
	Name: "ExteriorDerivativeLeibniz",
	Key:  "prop_c108ef7391ba4441",
	Deps: []registry.EntryLike{
		ExteriorDerivativeDef,
		WedgeDef,
		WedgeForm,
		ExteriorDerivativeForm,
		vec_form.ExteriorDerivativeLeibniz,
	},
	Build: family.Card(Statement{
		Binders: "∀n p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, p, α)", "manifold_form_on⟨n⟩(T, 𝒜, q, β)"},
		Conclusion: "manifold_exterior_derivative⟨n⟩(T, " +
			"    𝒜, " +
			"    p + q, " +
			"    manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α, β)) = " +
			"(λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"    manifold_form_wedge⟨n⟩(T, " +
			"        𝒜, " +
			"        p + 1, " +
			"        q, " +
			"        manifold_exterior_derivative⟨n⟩(T, 𝒜, p, α), " +
			"        β, " +
			"        c, " +
			"        y, " +
			"        P) + " +
			"    (-&1)^p * " +
			"    manifold_form_wedge⟨n⟩(T, " +
			"        𝒜, " +
			"        p, " +
			"        q + 1, " +
			"        α, " +
			"        manifold_exterior_derivative⟨n⟩(T, 𝒜, q, β), " +
			"        c, " +
			"        y, " +
			"        P))",
	},
		"On each compatible chart apply the Euclidean graded Leibniz rule, whose "+
			"sign is determined by the first factor's degree p. The carrier results "+
			"justify both differentiated factors and products; every expression is zero "+
			"on incompatible charts. Function extensionality assembles the formula."),
})}

// ExteriorDerivativeWedgeClosed — the exterior derivative of β ∧ ω, for a
// closed q-form ω, is dβ ∧ ω: the Leibniz rule gives dβ ∧ ω plus
// (-1)^k β ∧ dω, and β wedged with dω, the zero family, is zero.
var ExteriorDerivativeWedgeClosed = exteriorDerivativeWedgeClosedThm{family.Add(registry.ProofEntry{
	Name: "ExteriorDerivativeWedgeClosed",
	Key:  "prop_67f574e9e32b57a6",
	Build: family.Theorem(Statement{
		Binders: "∀n k q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀β ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, k, β)",
			"manifold_form_on⟨n⟩(T, 𝒜, q, ω)",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, q, ω) = «zero family»",
		},
		Conclusion: "manifold_exterior_derivative⟨n⟩(T, " +
			"    𝒜, " +
			"    k + q, " +
			"    manifold_form_wedge⟨n⟩(T, 𝒜, k, q, β, ω)) = " +
			"manifold_form_wedge⟨n⟩(T, 𝒜, k + 1, q, manifold_exterior_derivative⟨n⟩(T, 𝒜, k, β), ω)",
	},
		func(
			a *Argument,
			n, k, q *Expr[Nat],
			T *Expr[Set[Set[A]]],
			𝒜 *Expr[Set[Prod[Set[A], Fun2[A, Nat, Real]]]],
			β, ω *Expr[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]],
			βForm, ωForm, ωClosed Fact,
		) {
			leibniz := a.Have(
				"by the Leibniz rule, with dω = 0 and β ∧ 0 = 0",
				"manifold_exterior_derivative⟨n⟩(T, 𝒜, k + q, manifold_form_wedge⟨n⟩(T, 𝒜, k, q, β, ω)) = "+
					"(λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). "+
					"    manifold_form_wedge⟨n⟩(T, "+
					"        𝒜, "+
					"        k + 1, "+
					"        q, "+
					"        manifold_exterior_derivative⟨n⟩(T, 𝒜, k, β), "+
					"        ω, "+
					"        c, "+
					"        y, "+
					"        P) + "+
					"    (-&1) ^ k * &0)",
				By(
					βForm,
					ωForm,
					ωClosed,
					WedgeZeroRight.At(n, k, a.TermAs[Nat]("q + 1"), T, 𝒜, β),
					ExteriorDerivativeLeibniz.At(n, k, q, T, 𝒜, β, ω)))
			a.Show(
				"(-1)^k · 0 vanishes",
				ByArith(leibniz))
		}),
})}
