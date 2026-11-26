// Restriction is pullback by an open inclusion, and therefore preserves
// the wedge product and commutes with exterior differentiation.

package differential_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var PullbackOpenInclusion = pullbackOpenInclusionThm{family.Add(registry.ProofEntry{
	Name: "PullbackOpenInclusion",
	Key:  "prop_d82d1375cecc2ae4",
	Deps: []registry.EntryLike{
		PullbackCoordinate,
		RestrictDef,
		smooth_manifold.SmoothOpenInclusion,
		smooth_manifold.OpenCompatibleChart,
		vec_form.PullbackIdentity,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, k, ω)", "U ∈ T"},
		Conclusion: "manifold_form_pullback⟨n, n⟩(subtopology(T, U), " +
			"    open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"    T, " +
			"    𝒜, " +
			"    k, " +
			"    identity_map, " +
			"    ω) = " +
			"manifold_form_restrict⟨n⟩(T, 𝒜, U, ω)",
	},
		"Each compatible submanifold chart is an original compatible chart with domain "+
			"in U. Use that same chart as target in PullbackCoordinate; the coordinate "+
			"inclusion is locally the identity and its pullback fixes the component. Both "+
			"sides are zero at every other chart, exactly as RestrictDef prescribes."),
})}

// RestrictionPullback — restricting a pulled-back form f*ω to an open
// subset U is pulling ω back along f from U itself: restriction to U is
// pullback along the inclusion of U, and pulling back along the inclusion
// and then along f is pulling back along f ∘ identity_map, which is f.
var RestrictionPullback = restrictionPullbackThm{family.Add(registry.ProofEntry{
	Name: "RestrictionPullback",
	Key:  "prop_97c6e9e92fba29c3",
	Build: family.Theorem(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀U:set(A). " +
			"∀f:(A → B). " +
			"∀ω:(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"manifold_form_on⟨m⟩(S, ℬ, k, ω)",
			"U ∈ T",
		},
		Conclusion: "manifold_form_restrict⟨n⟩(T, " +
			"    𝒜, " +
			"    U, " +
			"    manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f, ω)) = " +
			"manifold_form_pullback⟨n, m⟩(subtopology(T, U), " +
			"    open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"    S, " +
			"    ℬ, " +
			"    k, " +
			"    f, " +
			"    ω)",
	},
		func(
			a *Argument,
			n, m, k *Expr[Nat],
			T *Expr[Set[Set[A]]],
			𝒜 *Expr[Set[Prod[Set[A], Fun2[A, Nat, Real]]]],
			S *Expr[Set[Set[B]]],
			ℬ *Expr[Set[Prod[Set[B], Fun2[B, Nat, Real]]]],
			U *Expr[Set[A]],
			f *Arrow[A, B],
			ω *Expr[Fun3[Prod[Set[B], Fun2[B, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]],
			smooth, form, uOpen Fact,
		) {
			inclusion := a.Have(
				"the source of f is a smooth manifold, so the inclusion of its open subset U is smooth",
				"smooth_manifold_map⟨n, n⟩(subtopology(T, U), "+
					"    open_submanifold_atlas⟨n⟩(T, 𝒜, U), "+
					"    T, "+
					"    𝒜, "+
					"    identity_map)",
				By(
					smooth,
					smooth_manifold.SmoothMapDef.At(n, m, T, 𝒜, S, ℬ, f),
					uOpen,
					smooth_manifold.SmoothOpenInclusion))
			a.Show(
				"restriction to U is pullback along the inclusion, and the inclusion followed by f is f",
				CalcEq(
					Leg(
						a.Term("manifold_form_pullback⟨n, n⟩(subtopology(T, U), "+
							"    open_submanifold_atlas⟨n⟩(T, 𝒜, U), "+
							"    T, "+
							"    𝒜, "+
							"    k, "+
							"    identity_map, "+
							"    manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f, ω))"),
						"f*ω is a k-form on the source, and restricting it to U is pulling it back along the inclusion",
						By(smooth, form, PullbackForm, uOpen, PullbackOpenInclusion)),
					Leg(
						a.Term("manifold_form_pullback⟨n, m⟩(subtopology(T, U), "+
							"    open_submanifold_atlas⟨n⟩(T, 𝒜, U), "+
							"    S, "+
							"    ℬ, "+
							"    k, "+
							"    f ∘ identity_map, "+
							"    ω)"),
						"pulling back along the inclusion and then along f is pulling back along the composite",
						By(inclusion, smooth, form, PullbackCompose)),
					FinalLeg(
						"the inclusion followed by f is f",
						Simp(Fwd(functions.ComposeIdentity))),
				))
		}),
})}

var RestrictionWedge = restrictionWedgeThm{family.Add(registry.ProofEntry{
	Name: "RestrictionWedge",
	Key:  "prop_d38176dbb9421083",
	Deps: []registry.EntryLike{
		PullbackOpenInclusion,
		PullbackWedge,
		WedgeForm,
		smooth_manifold.SmoothOpenInclusion,
	},
	Build: family.Card(Statement{
		Binders: "∀n p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, p, α)",
			"manifold_form_on⟨n⟩(T, 𝒜, q, β)",
			"U ∈ T",
		},
		Conclusion: "manifold_form_restrict⟨n⟩(T, 𝒜, U, manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α, β)) = " +
			"manifold_form_wedge⟨n⟩(subtopology(T, U), " +
			"    open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"    p, " +
			"    q, " +
			"    manifold_form_restrict⟨n⟩(T, 𝒜, U, α), " +
			"    manifold_form_restrict⟨n⟩(T, 𝒜, U, β))",
	},
		"Apply PullbackWedge to the smooth open inclusion. PullbackOpenInclusion "+
			"identifies its three pullbacks with the corresponding restrictions, "+
			"giving the wedge law on the open-submanifold atlas."),
})}

var RestrictionExteriorDerivative = restrictionExteriorDerivativeThm{family.Add(registry.ProofEntry{
	Name: "RestrictionExteriorDerivative",
	Key:  "prop_26669e82a1f8b024",
	Deps: []registry.EntryLike{
		PullbackOpenInclusion,
		PullbackExteriorDerivative,
		ExteriorDerivativeForm,
		smooth_manifold.SmoothOpenInclusion,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, k, ω)", "U ∈ T"},
		Conclusion: "manifold_exterior_derivative⟨n⟩(subtopology(T, U), " +
			"    open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"    k, " +
			"    manifold_form_restrict⟨n⟩(T, 𝒜, U, ω)) = " +
			"manifold_form_restrict⟨n⟩(T, 𝒜, U, manifold_exterior_derivative⟨n⟩(T, 𝒜, k, ω))",
	},
		"Apply PullbackExteriorDerivative to the smooth open inclusion. "+
			"PullbackOpenInclusion identifies pullback with restriction for both degrees k and "+
			"k+1, so the exterior derivative commutes with normalized chart-family restriction."),
})}

// RestrictionZero — restricting the zero family to a set U gives the zero
// family: restriction keeps a family on the charts of U and puts zero
// everywhere else, and the zero family is zero on those charts already.
var RestrictionZero = restrictionZeroThm{family.Add(registry.ProofEntry{
	Name: "RestrictionZero",
	Key:  "prop_4acf248ec99266c",
	Build: family.Theorem("∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U:set(A). "+
		"    manifold_form_restrict⟨n⟩(T, 𝒜, U, «zero family») = «zero family»",
		func(
			a *Argument,
			n *Expr[Nat],
			T *Expr[Set[Set[A]]],
			𝒜 *Expr[Set[Prod[Set[A], Fun2[A, Nat, Real]]]],
			U *Expr[Set[A]],
		) {
			a.Show(
				"on the charts of U and off them alike, the restricted family is zero",
				Simp(Fwd(RestrictDef), Fwd(functions.NormalizeOnDef)),
				Basic())
		}),
})}
