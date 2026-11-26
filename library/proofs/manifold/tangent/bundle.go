// The induced charts identify the total space locally with an open
// base-coordinate set times R^n, with smooth Jacobian transitions.

package tangent

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/topology/countability"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var TangentChartImage = tangentChartImageThm{family.Add(registry.ProofEntry{
	Name: "TangentChartImage",
	Key:  "prop_a46a1cc3c425ed33",
	Deps: []registry.EntryLike{
		TangentChartDef,
		TangentFromChart,
		TangentChartReconstruct,
		functions.InverseOnIn,
		functions.InverseOnRight,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "compatible_chart⟨n⟩(T, 𝒜, c)"},
		Conclusion: "image(snd(«lift»(c)), fst(«lift»(c))) = " +
			"{z:(num → real) | vec⟨2 * n⟩(z) ∧ «base block»(z) ∈ image(snd(c), fst(c))}",
	},
		"The forward inclusion reads the two blocks of an induced coordinate vector. Conversely recover "+
			"the base point with the chart inverse and propagate the padded fiber block by TangentFromChart. "+
			"The two block projections and concatenation then recover the given padded 2n-vector."),
})}

var TangentChartInverse = tangentChartInverseThm{family.Add(registry.ProofEntry{
	Name: "TangentChartInverse",
	Key:  "prop_6a6fc6a85cee50bb",
	Deps: []registry.EntryLike{
		TangentChartImage,
		TangentFromChart,
		TangentChartReconstruct,
		functions.InverseOnUnique,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀z:(num → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"z ∈ image(snd(«lift»(c)), fst(«lift»(c)))",
		},
		Conclusion: "inverse_on(fst(«lift»(c)), snd(«lift»(c)), z) = " +
			"(inverse_on(fst(c), snd(c), «base block»(z)), " +
			"    tangent_from_chart⟨n⟩(T, " +
			"        𝒜, " +
			"        c, " +
			"        inverse_on(fst(c), snd(c), «base block»(z)), " +
			"        «fiber block»(z)))",
	},
		"The displayed pair belongs to the induced chart domain and maps back to z by "+
			"TangentFromChart and the base inverse identities. Equality of induced coordinates "+
			"determines the base by chart injectivity and the tangent family by TangentChartReconstruct. "+
			"Thus this pair is the unique inverse_on value on the coordinate image."),
})}

var TangentChartTransition = tangentChartTransitionThm{family.Add(registry.ProofEntry{
	Name: "TangentChartTransition",
	Key:  "prop_fa441372174e669f",
	Reading: "The coordinate formula is asserted only on the overlap image of the " +
		"two induced charts. There the base block lies in the original chart overlap, so " +
		"both the chosen inverse and transition Jacobian have the required local meaning.",
	Deps: []registry.EntryLike{
		TangentChartInverse,
		TangentVectorDef,
		TangentChartDef,
		functions.InverseOnRight,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c d:prod(set(A), A → num → real). " +
			"∀z:(num → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"compatible_chart⟨n⟩(T, 𝒜, d)",
			"z ∈ image(snd(«lift»(c)), fst(«lift»(c)) ∩ fst(«lift»(d)))",
		},
		Conclusion: "«lift transition»(c, d, z) = " +
			"«join»(«transition»(c, d, «base block»(z)), " +
			"    matrix_act⟨n⟩(vec_jacobian_matrix⟨n, n⟩(«transition»(c, d), «base block»(z)), " +
			"        «fiber block»(z)))",
	},
		"Use TangentChartInverse to recover the base point and tangent vector from z. The first "+
			"output block is the original transition; the second is exactly its Jacobian acting on "+
			"the original fiber block by tangent compatibility. Both blocks retain zero tails."),
})}

var TangentManifold = tangentManifoldThm{family.Add(registry.ProofEntry{
	Name: "TangentManifold",
	Key:  "prop_caab1c8331f66ecf",
	Reading: "Hausdorffness separates different base points using the base topology and " +
		"separates vectors over one point inside a common induced chart. Second countability " +
		"comes from a countable covering subatlas of the base, not from countability of the " +
		"full compatible-chart set. The empty manifold and n=0 are included.",
	Deps: []registry.EntryLike{
		TangentTopologyDef,
		TangentAtlasDef,
		TangentChartImage,
		TangentChartInverse,
		TangentChartTransition,
		smooth_manifold.CompatibleTransition,
		smooth_manifold.CountableAtlas,
		euclidean_topology.EuclideanHausdorff,
		euclidean_topology.EuclideanSecondCountable,
		countability.SecondCountableSubtopology,
		countability.SecondCountableOpenCover,
		vec_smooth.SmoothPartial,
		vec_smooth.SmoothMul,
		vec_smooth.SmoothSum,
		vec_smooth.SmoothCompose,
		vec_smooth.LinearSmoothMap,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "smooth_manifold⟨2 * n⟩(tangent_topology⟨n⟩(T, 𝒜), tangent_atlas⟨n⟩(T, 𝒜)) ∧ " +
			"⋃tangent_topology⟨n⟩(T, 𝒜) = tangent_bundle⟨n⟩(T, 𝒜)",
	},
		"The image and inverse formulas give bijective induced charts onto open base-image "+
			"cylinders. Their transition (y,u)↦(tau(y),D tau(y)u) and its inverse are smooth by "+
			"smooth partial derivatives, products and finite sums; these compatible chart "+
			"homeomorphisms make the declared open-set family a topology with exactly the tangent "+
			"carrier. Separate points by their bases or by one fiber chart, and use the lifted "+
			"countable base subatlas together with SecondCountableOpenCover for second countability."),
})}

var TangentProjection = tangentProjectionThm{family.Add(registry.ProofEntry{
	Name: "TangentProjection",
	Key:  "prop_db219c44fc9ca52b",
	Deps: []registry.EntryLike{
		TangentManifold,
		TangentChartInverse,
		smooth_manifold.CompatibleTransition,
		vec_smooth.LinearSmoothMap,
		vec_smooth.SmoothMapCompose,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "smooth_manifold_map⟨2 * n, n⟩(tangent_topology⟨n⟩(T, 𝒜), " +
			"    tangent_atlas⟨n⟩(T, 𝒜), " +
			"    T, " +
			"    𝒜, " +
			"    fst)",
	},
		"In an aligned base chart the projection is the padded first-block linear map. "+
			"For another target chart it composes that projection with the base transition "+
			"on its overlap. These local formulas give continuity and all smooth chart tests."),
})}

var TangentZeroSection = tangentZeroSectionThm{family.Add(registry.ProofEntry{
	Name: "TangentZeroSection",
	Key:  "prop_e9ba430f3142cfde",
	Deps: []registry.EntryLike{
		ZeroSectionDef,
		TangentModule,
		TangentManifold,
		smooth_manifold.CompatibleTransition,
		vec_smooth.SmoothConst,
		vec_smooth.SmoothMapCompose,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "smooth_manifold_map⟨n, 2 * n⟩(T, " +
			"    𝒜, " +
			"    tangent_topology⟨n⟩(T, 𝒜), " +
			"    tangent_atlas⟨n⟩(T, 𝒜), " +
			"    tangent_zero_section)",
	},
		"The zero vector belongs to every fiber over a carrier point. In each "+
			"induced chart the zero section has coordinate expression y↦(tau(y),0), "+
			"with tau the relevant base transition; hence it is continuous and smooth. "+
			"Its first component is the original base point, even in dimension zero."),
})}
