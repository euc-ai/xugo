// Embedded tangent disks are open, and compact bases give compact bounds and uniform radii.

package manifold_diagonal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix_norm"
	"github.com/euc-ai/xugo/library/registry"
)

var EmbeddedTangentDiskOpen = embeddedTangentDiskOpenThm{family.Add(registry.ProofEntry{
	Name: "EmbeddedTangentDiskOpen",
	Key:  "prop_23af50d9197e8c7",
	Reading: "No immersion or positive-radius hypothesis " +
		"is needed for openness. For δ≤0 the disk is empty.",
	Deps: []registry.EntryLike{
		EmbeddedTangentDiskDef,
		tangent.EuclideanDifferentialBundleSmooth,
		tangent.TangentManifold,
		euclidean_topology.NormContinuous,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀δ:real.",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    i)",
		},
		Conclusion: "embedded_tangent_disk⟨n, N⟩(T, 𝒜, i, δ) ∈ tangent_topology⟨n⟩(T, 𝒜)",
	},
		"EuclideanDifferentialBundleSmooth is continuous, and NormContinuous makes its norm "+
			"continuous. The strict sublevel set on the tangent-bundle carrier is therefore open."),
})}

var EmbeddedTangentDiskZeroSection = embeddedTangentDiskZeroSectionThm{family.Add(registry.ProofEntry{
	Name: "EmbeddedTangentDiskZeroSection",
	Key:  "prop_c9e09a79ed5a2168",
	Deps: []registry.EntryLike{
		EmbeddedTangentDiskDef,
		tangent.EuclideanDifferentialLinear,
		tangent.TangentZeroSection,
		tangent.TangentModuleDef,
		module_homomorphism.HomZero,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀δ:real.",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    i)",
			"&0 < δ",
		},
		Conclusion: "image(tangent_zero_section, ⋃T) ⊆ embedded_tangent_disk⟨n, N⟩(T, 𝒜, i, δ)",
	},
		"TangentZeroSection supplies valid zero tangent vectors. EuclideanDifferentialLinear "+
			"sends them to the zero Euclidean vector, whose norm is less than the positive radius."),
})}

var CompactEmbeddedTangentDisk = compactEmbeddedTangentDiskThm{family.Add(registry.ProofEntry{
	Name: "CompactEmbeddedTangentDisk",
	Key:  "prop_16db555d92b0ecba",
	Reading: "Compactness of the base and injectivity of the differential " +
		"are both essential for a uniform fiber bound. The radius may be zero " +
		"or negative; this is the closed norm sublevel set, not the open disk.",
	Deps: []registry.EntryLike{
		tangent.EuclideanDifferentialCoordinate,
		tangent.EuclideanDifferentialBundleSmooth,
		tangent.TangentChartInverse,
		tangent.TangentManifold,
		matrix_norm.CompactInjectiveMatrixBounds,
		euclidean_topology.CompactIffClosedBounded,
		compact.ClosedSubsetCompact,
		product_topology.CompactProduct,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀δ:real.",
		Hypotheses: []string{
			"smooth_manifold_immersion⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    i)",
			"compact_in(T, ⋃T)",
		},
		Conclusion: "compact_in(tangent_topology⟨n⟩(T, 𝒜), " +
			"    {p:prod(A, prod(set(A), A → num → real) → num → real) | " +
			"        p ∈ tangent_bundle⟨n⟩(T, 𝒜) ∧ " +
			"        ‖manifold_euclidean_differential⟨n, N⟩(T, 𝒜, i)(fst(p), snd(p))‖_N ≤ δ})",
	},
		"Use finitely many compact chart patches covering the base. CompactInjectiveMatrixBounds "+
			"bounds the chart fiber coordinates by the embedded tangent norm, so over each patch the "+
			"closed disk is a closed subset of a compact product of that patch and a bounded "+
			"Euclidean ball; tangent chart inverses transport this compactness. The finite union "+
			"covers the disk; a negative radius gives the empty set."),
})}

var CompactZeroSectionDisk = compactZeroSectionDiskThm{family.Add(registry.ProofEntry{
	Name: "CompactZeroSectionDisk",
	Key:  "prop_2ef427317175bde4",
	Reading: "O is any open neighbourhood of the whole zero section. The conclusion concerns the " +
		"chosen immersion norm; no global tangent metric or trivialization is assumed. Outside O the " +
		"closed unit disk is compact and the norm is positive by injectivity, so its minimum gives a " +
		"radius. An empty complement permits radius one; empty bases permit any positive radius.",
	Deps: []registry.EntryLike{
		EmbeddedTangentDiskDef,
		CompactEmbeddedTangentDisk,
		tangent.EuclideanDifferentialInjective,
		tangent.EuclideanDifferentialBundleSmooth,
		tangent.TangentZeroSection,
		compact.CompactInterClosed,
		euclidean_topology.NormContinuous,
		real_valued.ContinuousCompactMinimum,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀O:set(prod(A, prod(set(A), A → num → real) → num → real)).",
		Hypotheses: []string{
			"smooth_manifold_immersion⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    i)",
			"compact_in(T, ⋃T)",
			"O ∈ tangent_topology⟨n⟩(T, 𝒜)",
			"image(tangent_zero_section, ⋃T) ⊆ O",
		},
		Conclusion: "∃δ:real. &0 < δ ∧ embedded_tangent_disk⟨n, N⟩(T, 𝒜, i, δ) ⊆ O",
	},
		"CompactEmbeddedTangentDisk makes the closed unit disk compact. Its closed part outside O has "+
			"strictly positive continuous embedded norm, since EuclideanDifferentialInjective identifies "+
			"the zero-norm points with the zero section. If this part is nonempty, ContinuousCompactMinimum "+
			"gives a positive lower bound and hence a radius at most one; if it is empty, radius one works."),
})}
