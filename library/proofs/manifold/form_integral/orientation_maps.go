// A diffeomorphism preserves orientation on a connected source once one local sign is positive.

package form_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/connected"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var DiffeomorphismOrientationAtPoint = diffeomorphismOrientationAtPointThm{family.Add(registry.ProofEntry{
	Name: "DiffeomorphismOrientationAtPoint",
	Key:  "prop_eb1c58dc0df63db6",
	Reading: "Connectedness and invertibility throughout the source are essential: a positive " +
		"determinant at one point alone does not control other components or pass through a " +
		"singularity. Positive source and target charts make the local signs agree on overlaps.",
	Deps: []registry.EntryLike{
		OrientedDiffeomorphismDef,
		PositiveTransition,
		smooth_manifold.DiffeomorphismDef,
		smooth_manifold.SmoothMapCompatibleCharts,
		vec_smooth.DiffeomorphismJacobianNonzero,
		vec_smooth.JacobianDeterminantChain,
		vec_smooth.SmoothPartial,
		vec_smooth.SmoothDeterminant,
		connected.ConnectedIffNoClopen,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀x:A. " +
			"∀c:prod(set(A), A → num → real). " +
			"∀d:prod(set(B), B → num → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨n⟩(S, ℬ)",
			"smooth_manifold_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f)",
			"connected_in(T, ⋃T)",
			"positive_manifold_chart⟨n⟩(T, 𝒜, c)",
			"positive_manifold_chart⟨n⟩(S, ℬ, d)",
			"x ∈ fst(c)",
			"f(x) ∈ fst(d)",
			"&0 < vec_jacobian_determinant⟨n⟩(«coordinate map»(c, d, f), snd(c)(x))",
		},
		Conclusion: "oriented_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f)",
	},
		"A smooth diffeomorphism has nonzero coordinate Jacobian determinants. Their sign is "+
			"continuous locally and agrees under positive chart changes, so the positive-sign "+
			"locus is both open and closed in the source. ConnectedIffNoClopen and the supplied "+
			"positive point make this locus the whole source, giving OrientedDiffeomorphismDef."),
})}

var OrientedDiffeomorphismOpenRestrict = orientedDiffeomorphismOpenRestrictThm{family.Add(registry.ProofEntry{
	Name: "OrientedDiffeomorphismOpenRestrict",
	Key:  "prop_5785a049d025eccd",
	Reading: "The restricted atlases consist of positive charts. The " +
		"all-compatible open atlas gives the same smooth structure but generally " +
		"does not itself carry the chosen orientation. Empty opens are allowed.",
	Deps: []registry.EntryLike{
		OrientedDiffeomorphismDef,
		OrientedOpenSubmanifold,
		smooth_manifold.DiffeomorphismDef,
		smooth_manifold.DiffeomorphismOpenRestrict,
		smooth_manifold.SmoothMapCompatibleCharts,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀V:set(A).",
		Hypotheses: []string{
			"oriented_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f)",
			"V ∈ T",
		},
		Conclusion: "image(f, V) ∈ S ∧ " +
			"oriented_diffeomorphism⟨n⟩(subtopology(T, V), " +
			"    oriented_open_atlas⟨n⟩(T, 𝒜, V), " +
			"    subtopology(S, image(f, V)), " +
			"    oriented_open_atlas⟨n⟩(S, ℬ, image(f, V)), " +
			"    f)",
	},
		"The underlying smooth diffeomorphism restricts to V and its open image. OrientedOpenSubmanifold "+
			"identifies the positive charts of these opens with the ambient positive charts contained there; "+
			"their coordinate Jacobians agree locally with the original map and remain positive."),
})}
