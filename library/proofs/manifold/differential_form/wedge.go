// The Euclidean shuffle product descends through coordinate compatibility
// to the graded algebra of normalized manifold forms.

package differential_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/registry"
)

var WedgeForm = wedgeFormThm{family.Add(registry.ProofEntry{
	Name: "WedgeForm",
	Key:  "prop_a8796a69c9733794",
	Deps: []registry.EntryLike{WedgeDef, FormOnDef, vec_form.WedgeForm, vec_form.PullbackWedge},
	Build: family.Card(Statement{
		Binders: "∀n p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, p, α)", "manifold_form_on⟨n⟩(T, 𝒜, q, β)"},
		Conclusion: "manifold_form_on⟨n⟩(T, 𝒜, p + q, manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α, β))",
	},
		"Each compatible component is a Euclidean form of degree p+q. PullbackWedge transports "+
			"the two overlap equations to the product equation, since normalized restriction commutes "+
			"with the pointwise shuffle formula. Incompatible components vanish by the defining guard."),
})}

var WedgeBilinear = wedgeBilinearThm{family.Add(registry.ProofEntry{
	Name: "WedgeBilinear",
	Key:  "prop_cecf1b01be2f8f53",
	Deps: []registry.EntryLike{WedgeForm, FormModule, WedgeDef, vec_form.WedgeBilinear},
	Build: family.Card(Statement{
		Binders:    "∀n p q:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "bilinear_map(real_ring, " +
			"    manifold_form_module⟨n⟩(T, 𝒜, p), " +
			"    manifold_form_module⟨n⟩(T, 𝒜, q), " +
			"    manifold_form_module⟨n⟩(T, 𝒜, p + q), " +
			"    manifold_form_wedge⟨n⟩(T, 𝒜, p, q))",
	},
		"Apply Euclidean wedge bilinearity on each compatible chart and use zero "+
			"on all other charts. The module operations are pointwise and independent "+
			"of degree; WedgeForm provides preservation of the degree carriers."),
})}

// WedgeAddLeft — the wedge of a sum of two p-forms with a q-form is the
// sum of their wedges with it: the wedge is bilinear on the form modules,
// so wedging with the q-form on the right is linear, hence additive, and
// the module sums are the pointwise sums.
var WedgeAddLeft = wedgeAddLeftThm{family.Add(registry.ProofEntry{
	Name: "WedgeAddLeft",
	Key:  "prop_9050ed9aa520977c",
	Build: family.Theorem(Statement{
		Binders: "∀n p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀φ ψ ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, p, φ)",
			"manifold_form_on⟨n⟩(T, 𝒜, p, ψ)",
			"manifold_form_on⟨n⟩(T, 𝒜, q, ω)",
		},
		Conclusion: "manifold_form_wedge⟨n⟩(T, " +
			"    𝒜, " +
			"    p, " +
			"    q, " +
			"    λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"        φ(c, y, P) + ψ(c, y, P), " +
			"    ω) = " +
			"(λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"    manifold_form_wedge⟨n⟩(T, 𝒜, p, q, φ, ω, c, y, P) + " +
			"    manifold_form_wedge⟨n⟩(T, 𝒜, p, q, ψ, ω, c, y, P))",
	},
		func(
			a *Argument,
			n, p, q *Expr[Nat],
			T *Expr[Set[Set[A]]],
			𝒜 *Expr[Set[Prod[Set[A], Fun2[A, Nat, Real]]]],
			φ, ψ, ω *Expr[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]],
			φForm, ψForm, ωForm Fact,
		) {
			bilinear := a.Have(
				"the wedge is bilinear",
				"bilinear_map(real_ring, "+
					"    manifold_form_module⟨n⟩(T, 𝒜, p), "+
					"    manifold_form_module⟨n⟩(T, 𝒜, q), "+
					"    manifold_form_module⟨n⟩(T, 𝒜, p + q), "+
					"    manifold_form_wedge⟨n⟩(T, 𝒜, p, q))",
				By(φForm, FormOnDef, WedgeBilinear))
			wedgeω := a.Have(
				"wedging with ω on the right is linear",
				"module_homomorphism(real_ring, "+
					"    manifold_form_module⟨n⟩(T, 𝒜, p), "+
					"    manifold_form_module⟨n⟩(T, 𝒜, p + q), "+
					"    λu:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). "+
					"        manifold_form_wedge⟨n⟩(T, 𝒜, p, q, u, ω))",
				By(bilinear, ωForm, FormModulePointwise, module_homomorphism.BilinearMapDef))
			additive := a.Have(
				"so it is additive",
				"manifold_form_wedge⟨n⟩(T, 𝒜, p, q, manifold_form_module⟨n⟩(T, 𝒜, p).add(φ, ψ), ω) = "+
					"manifold_form_module⟨n⟩(T, 𝒜, p + q).add(manifold_form_wedge⟨n⟩(T, 𝒜, p, q, φ, ω), "+
					"    manifold_form_wedge⟨n⟩(T, 𝒜, p, q, ψ, ω))",
				By(φForm, ψForm, FormModulePointwise, module_homomorphism.HomAdd.Read(wedgeω)))
			a.Show(
				"the module sums are the pointwise sums",
				By(a.Simplified(additive, Fwd(FormModulePointwise))))
		}),
})}

// WedgeZeroRight — a p-form wedged with the zero family is the zero
// family: wedging with a fixed p-form is linear on the q-forms, since the
// wedge is bilinear, and a linear map keeps zero, the zero of the form
// modules being the zero family.
var WedgeZeroRight = wedgeZeroRightThm{family.Add(registry.ProofEntry{
	Name: "WedgeZeroRight",
	Key:  "prop_2f0f1c576b535ba9",
	Build: family.Theorem(Statement{
		Binders: "∀n p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀α:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, p, α)",
		},
		Conclusion: "manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α, «zero family») = «zero family»",
	},
		func(
			a *Argument,
			n, p, q *Expr[Nat],
			T *Expr[Set[Set[A]]],
			𝒜 *Expr[Set[Prod[Set[A], Fun2[A, Nat, Real]]]],
			α *Expr[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]],
			αForm Fact,
		) {
			bilinear := a.Have(
				"the wedge is bilinear",
				"bilinear_map(real_ring, "+
					"    manifold_form_module⟨n⟩(T, 𝒜, p), "+
					"    manifold_form_module⟨n⟩(T, 𝒜, q), "+
					"    manifold_form_module⟨n⟩(T, 𝒜, p + q), "+
					"    manifold_form_wedge⟨n⟩(T, 𝒜, p, q))",
				By(αForm, FormOnDef, WedgeBilinear))
			wedgeα := a.Have(
				"wedging with α is linear",
				"module_homomorphism(real_ring, "+
					"    manifold_form_module⟨n⟩(T, 𝒜, q), "+
					"    manifold_form_module⟨n⟩(T, 𝒜, p + q), "+
					"    manifold_form_wedge⟨n⟩(T, 𝒜, p, q)(α))",
				By(bilinear, αForm, FormModulePointwise, module_homomorphism.BilinearMapDef))
			a.Show(
				"a linear map keeps zero, and the zero of the form modules is the zero family",
				By(module_homomorphism.HomZero.Read(wedgeα), FormModulePointwise))
		}),
})}

var WedgeAssociative = wedgeAssociativeThm{family.Add(registry.ProofEntry{
	Name: "WedgeAssociative",
	Key:  "prop_63530b6e054e6232",
	Deps: []registry.EntryLike{WedgeForm, WedgeDef, vec_form.WedgeAssociative},
	Build: family.Card(Statement{
		Binders: "∀n p q r:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀α β γ:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, p, α)",
			"manifold_form_on⟨n⟩(T, 𝒜, q, β)",
			"manifold_form_on⟨n⟩(T, 𝒜, r, γ)",
		},
		Conclusion: "manifold_form_wedge⟨n⟩(T, " +
			"    𝒜, " +
			"    p + q, " +
			"    r, " +
			"    manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α, β), " +
			"    γ) = " +
			"manifold_form_wedge⟨n⟩(T, 𝒜, p, q + r, α, manifold_form_wedge⟨n⟩(T, 𝒜, q, r, β, γ))",
	},
		"Evaluate at an arbitrary chart. For compatible charts the two sides are the Euclidean "+
			"associative wedge expressions, with their intermediate carriers supplied by WedgeForm; "+
			"for other charts both sides are zero. Extensionality gives equality of families."),
})}

var WedgeGradedCommutative = wedgeGradedCommutativeThm{family.Add(registry.ProofEntry{
	Name: "WedgeGradedCommutative",
	Key:  "prop_381ab7a06e5ac9f0",
	Deps: []registry.EntryLike{WedgeDef, vec_form.WedgeGradedCommutative},
	Build: family.Card(Statement{
		Binders: "∀n p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, p, α)", "manifold_form_on⟨n⟩(T, 𝒜, q, β)"},
		Conclusion: "manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α, β) = " +
			"(λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"    (-&1)^(p * q) * manifold_form_wedge⟨n⟩(T, 𝒜, q, p, β, α, c, y, P))",
	},
		"On compatible charts use the Euclidean sign (-1)^(pq), coming from interchanging the "+
			"two shuffle blocks. On incompatible charts the guarded products vanish. This yields "+
			"the total function equality, including zero degrees and degrees above the dimension."),
})}

var WedgeUnit = wedgeUnitThm{family.Add(registry.ProofEntry{
	Name: "WedgeUnit",
	Key:  "prop_18fd035715b01b5",
	Deps: []registry.EntryLike{
		UnitDef,
		FormOnDef,
		WedgeDef,
		vec_form.WedgeUnit,
		vec_form.PullbackDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, k, ω)"},
		Conclusion: "manifold_form_on⟨n⟩(T, 𝒜, 0, manifold_form_unit⟨n⟩(T, 𝒜)) ∧ " +
			"manifold_form_wedge⟨n⟩(T, 𝒜, 0, k, manifold_form_unit⟨n⟩(T, 𝒜), ω) = ω ∧ " +
			"manifold_form_wedge⟨n⟩(T, 𝒜, k, 0, ω, manifold_form_unit⟨n⟩(T, 𝒜)) = ω",
	},
		"The normalized constant-one coefficient is the Euclidean zero-form unit on each "+
			"coordinate image. Pullback of this zero-form is one on the overlap because transitions "+
			"land in the target image; hence the units are compatible. The two unit laws then hold "+
			"componentwise by the Euclidean WedgeUnit, with zero on incompatible charts."),
})}
