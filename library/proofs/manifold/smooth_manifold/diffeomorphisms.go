// Equal-dimensional immersions give local diffeomorphisms and injective ones give open images.

package smooth_manifold

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var DiffeomorphismInverse = diffeomorphismInverseThm{family.Add(registry.ProofEntry{
	Name: "DiffeomorphismInverse",
	Key:  "prop_e0892d64a5568b61",
	Deps: []registry.EntryLike{DiffeomorphismDef, SmoothMapCongruence, continuous.HomeomorphismInverse},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{
			"smooth_manifold_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f)",
		},
		Conclusion: "smooth_manifold_diffeomorphism⟨n⟩(S, ℬ, T, 𝒜, inverse_on(⋃T, f))",
	},
		"HomeomorphismInverse gives the inverse homeomorphism and both carrier "+
			"inverse equations. The inverse of inverse_on agrees with f on the "+
			"source carrier, so SmoothMapCongruence supplies its smoothness."),
})}

var DiffeomorphismOpenRestrict = diffeomorphismOpenRestrictThm{family.Add(registry.ProofEntry{
	Name: "DiffeomorphismOpenRestrict",
	Key:  "prop_5787d86886f68c4",
	Reading: "The target is the actual image of U, with the ambient restricted compatible " +
		"atlas. An empty U gives the diffeomorphism between empty open submanifolds.",
	Deps: []registry.EntryLike{
		DiffeomorphismDef,
		SmoothMapRestrict,
		SmoothMapCongruence,
		continuous.HomeomorphismIffOpenBijection,
		continuous.HomeomorphismSubtopologies,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀U:set(A).",
		Hypotheses: []string{
			"smooth_manifold_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f)",
			"U ∈ T",
		},
		Conclusion: "image(f, U) ∈ S ∧ " +
			"smooth_manifold_diffeomorphism⟨n⟩(subtopology(T, U), " +
			"    open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"    subtopology(S, image(f, U)), " +
			"    open_submanifold_atlas⟨n⟩(S, ℬ, image(f, U)), " +
			"    f)",
	},
		"The homeomorphism sends U to an open set and restricts to a homeomorphism onto that "+
			"image. Restrict both smooth directions to these opens; their inverse equations "+
			"identify the restricted inverse_on with the original inverse on the image."),
})}

var ImmersionLocalDiffeomorphism = immersionLocalDiffeomorphismThm{family.Add(registry.ProofEntry{
	Name: "ImmersionLocalDiffeomorphism",
	Key:  "prop_f89890d97430dd2",
	Reading: "Equal source and target dimensions are essential. The " +
		"zero-dimensional case is the inverse map between singleton chart neighbourhoods.",
	Deps: []registry.EntryLike{
		ImmersionDef,
		SmoothMapCompatibleCharts,
		OpenCompatibleChart,
		vec_smooth.SmoothInverseFunction,
		determinant.DeterminantZeroIffDependent,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀x:A.",
		Hypotheses: []string{
			"smooth_manifold_immersion⟨n, n⟩(T, 𝒜, S, ℬ, f)",
			"x ∈ ⋃T",
		},
		Conclusion: "∃U:set(A). ∃V:set(B). " +
			"    U ∈ T ∧ " +
			"    V ∈ S ∧ " +
			"    x ∈ U ∧ " +
			"    f(x) ∈ V ∧ " +
			"    smooth_manifold_diffeomorphism⟨n⟩(subtopology(T, U), " +
			"        open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"        subtopology(S, V), " +
			"        open_submanifold_atlas⟨n⟩(S, ℬ, V), " +
			"        f)",
	},
		"Choose compatible charts at x and f(x). The injective square Jacobian has nonzero "+
			"determinant, so SmoothInverseFunction gives a coordinate diffeomorphism on smaller opens; "+
			"transport it back through the two charts and identify the restricted compatible atlases."),
})}

var InjectiveImmersionDiffeomorphism = injectiveImmersionDiffeomorphismThm{family.Add(registry.ProofEntry{
	Name: "InjectiveImmersionDiffeomorphism",
	Key:  "prop_b4358fb59e4daf26",
	Reading: "No compactness is required. The image atlas is restricted " +
		"from the target, and global injectivity is needed to glue one inverse.",
	Deps: []registry.EntryLike{
		DiffeomorphismDef,
		ImmersionDef,
		ImmersionLocalDiffeomorphism,
		SmoothMapLocal,
		SmoothMapRestrict,
		SmoothMapCongruence,
		continuous.HomeomorphismIffOpenBijection,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{
			"smooth_manifold_immersion⟨n, n⟩(T, 𝒜, S, ℬ, f)",
			"injective_on(⋃T, f)",
		},
		Conclusion: "image(f, ⋃T) ∈ S ∧ " +
			"smooth_manifold_diffeomorphism⟨n⟩(T, " +
			"    𝒜, " +
			"    subtopology(S, image(f, ⋃T)), " +
			"    open_submanifold_atlas⟨n⟩(S, ℬ, image(f, ⋃T)), " +
			"    f)",
	},
		"ImmersionLocalDiffeomorphism makes f locally open and provides smooth local inverses. "+
			"Global injectivity makes these inverses agree on their overlaps; the image is open, "+
			"the induced bijection is a homeomorphism, and SmoothMapLocal glues its inverse."),
})}
