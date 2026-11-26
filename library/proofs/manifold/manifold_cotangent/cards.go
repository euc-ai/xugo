package manifold_cotangent

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	"github.com/euc-ai/xugo/library/registry"
)

var CoordinateCovector = coordinateCovectorThm{family.Add(registry.ProofEntry{
	Name: "CoordinateCovector",
	Key:  "prop_770c285121e3cc60",
	Deps: []registry.EntryLike{
		CovectorDef,
		FromChartDef,
		tangent.TangentVectorDef,
		tangent.TangentFromChart,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A. " +
			"∀u:(num → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compatible_chart⟨n⟩(T, 𝒜, c) ∧ x ∈ fst(c)",
			"vec⟨n⟩(&0, u)",
		},
		Conclusion: "cotangent_covector(n, T, 𝒜, x, cotangent_from_chart(n, T, 𝒜, c, x, u)) ∧ " +
			"cotangent_from_chart(n, T, 𝒜, c, x, u, c) = u",
	},
		"The component in an active chart d is the transpose of the Jacobian of c∘d⁻¹ at d(x) "+
			"applied to u; no inverse enters. Paired with a tangent vector v it is Σ_j u_j v(c, j), by "+
			"the tangent law from d to c (tangent.TangentVectorDef), so the pairing is the same in every "+
			"chart. The component in c is u because the self-transition's Jacobian acts as the identity "+
			"on padded vectors: tangent.TangentFromChart on the basis vectors gives its entries δ_ji."),
})}

var CoordinateReconstruction = coordinateReconstructionThm{family.Add(registry.ProofEntry{
	Name: "CoordinateReconstruction",
	Key:  "prop_3c77bd11b799924e",
	Deps: []registry.EntryLike{CoordinateCovector},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A. " +
			"∀ξ:(prod(set(A), A → num → real) → num → real).",
		Hypotheses: []string{
			"cotangent_covector(n, T, 𝒜, x, ξ)",
			"compatible_chart⟨n⟩(T, 𝒜, c) ∧ x ∈ fst(c)",
		},
		Conclusion: "cotangent_from_chart(n, T, 𝒜, c, x, ξ(c)) = ξ",
	}, "Every chart value is determined by pairing with the coordinate basis tangent vectors."),
})}

var CotangentManifold = cotangentManifoldThm{family.Add(registry.ProofEntry{
	Name: "CotangentManifold",
	Key:  "prop_8fda2e8210e044db",
	Deps: []registry.EntryLike{CoordinateCovector, CoordinateReconstruction},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "smooth_manifold⟨2 * n⟩(cotangent_topology(n, T, 𝒜), cotangent_atlas(n, T, 𝒜)) ∧ " +
			"⋃cotangent_topology(n, T, 𝒜) = cotangent_bundle(n, T, 𝒜)",
	},
		"The induced charts have open cylinder images and smooth inverse-transpose "+
			"transitions. A countable base subatlas gives second countability; base "+
			"points or a common fibre chart separate distinct points."),
})}

var ProjectionSmooth = projectionSmoothThm{family.Add(registry.ProofEntry{
	Name: "ProjectionSmooth",
	Key:  "prop_1bb05d599efc30d9",
	Deps: []registry.EntryLike{CotangentManifold},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "smooth_manifold_map⟨2 * n, n⟩(cotangent_topology(n, T, 𝒜), " +
			"    cotangent_atlas(n, T, 𝒜), " +
			"    T, " +
			"    𝒜, " +
			"    λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p))",
	}, "In induced coordinates the bundle projection is the linear first-block map."),
})}

var MetricIdentification = metricIdentificationThm{family.Add(registry.ProofEntry{
	Name: "MetricIdentification",
	Key:  "prop_ba8427bd9986ddac",
	Deps: []registry.EntryLike{CotangentManifold},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real).",
		Hypotheses: []string{"riemannian_metric⟨n⟩(T, 𝒜, g)"},
		Conclusion: "smooth_manifold_map⟨2 * n, 2 * n⟩(tangent_topology⟨n⟩(T, 𝒜), " +
			"    tangent_atlas⟨n⟩(T, 𝒜), " +
			"    cotangent_topology(n, T, 𝒜), " +
			"    cotangent_atlas(n, T, 𝒜), " +
			"    cotangent_metric_flat(n, T, 𝒜, g)) ∧ " +
			"homeomorphic_map(tangent_topology⟨n⟩(T, 𝒜), " +
			"    cotangent_topology(n, T, 𝒜), " +
			"    cotangent_metric_flat(n, T, 𝒜, g)) ∧ " +
			"kc_proper_map(tangent_topology⟨n⟩(T, 𝒜), " +
			"    cotangent_topology(n, T, 𝒜), " +
			"    cotangent_metric_flat(n, T, 𝒜, g))",
	},
		"Positive definite metric matrices have smooth inverses. They give inverse bundle "+
			"maps and hence a homeomorphism, whose compact inverse images prove properness."),
})}
