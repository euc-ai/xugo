// Compact top-form integration is linear and respects charts, atlases and open extension.

package form_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/registry"
)

var IntegralSingleChart = integralSingleChartThm{family.Add(registry.ProofEntry{
	Name: "IntegralSingleChart",
	Key:  "prop_b12df1dc02a753de",
	Deps: []registry.EntryLike{
		IntegralByPartition,
		IntegralPartitionExists,
		ChartIntegralChange,
		chartIntegralDef,
		differential_form.FormPartitionDecomposition,
		differential_form.WeightSupport,
		differential_form.ChartCoefficientCompact,
		vec_integral.IntegralSum,
		vec_integral.CcRapid,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀c:prod(set(A), A → num → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"manifold_form_on⟨n⟩(T, 𝒜, n, ω)",
			"compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω))",
			"positive_manifold_chart⟨n⟩(T, 𝒜, c)",
			"manifold_form_support⟨n⟩(T, 𝒜, ω) ⊆ fst(c)",
		},
		Conclusion: "manifold_form_integral⟨n⟩(T, 𝒜, ω) = manifold_chart_integral⟨n⟩(c, ω)",
	},
		"Take a positive-chart partition of the support. Each weighted summand is supported in its "+
			"assigned chart and in c, so ChartIntegralChange moves every integral to c. Finite linearity "+
			"and the partition decomposition then give the integral of the original coefficient in c."),
})}

var IntegralZero = integralZeroThm{family.Add(registry.ProofEntry{
	Name: "IntegralZero",
	Key:  "prop_130c84e2e4a747fc",
	Deps: []registry.EntryLike{
		IntegralValue,
		HasIntegralDef,
		integralPartitionDef,
		OrientedManifoldDef,
		differential_form.FormModule,
		differential_form.SupportEmpty,
		smooth_manifold.PartitionOfUnityDef,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"oriented_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "manifold_form_integral⟨n⟩(T, 𝒜, «zero family») = &0",
	},
		"The zero family is a top form with empty support. The empty partition "+
			"witnesses integral value zero, so IntegralValue gives the operator value."),
})}

var IntegralAdd = integralAddThm{family.Add(registry.ProofEntry{
	Name: "IntegralAdd",
	Key:  "prop_148b0b00d9529f5d",
	Deps: []registry.EntryLike{
		IntegralByPartition,
		IntegralPartitionExists,
		chartIntegralDef,
		differential_form.FormModule,
		differential_form.SupportDef,
		differential_form.SupportClosed,
		differential_form.WeightDef,
		differential_form.ChartCoefficientCompact,
		compact.CompactUnion,
		compact.ClosedSubsetCompact,
		vec_integral.IntegralAdd,
		vec_integral.CcRapid,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω η:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"manifold_form_on⟨n⟩(T, 𝒜, n, ω)",
			"manifold_form_on⟨n⟩(T, 𝒜, n, η)",
			"compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω))",
			"compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, η))",
		},
		Conclusion: "manifold_form_integral⟨n⟩(T, " +
			"    𝒜, " +
			"    λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"        ω(c, y, P) + η(c, y, P)) = " +
			"manifold_form_integral⟨n⟩(T, 𝒜, ω) + manifold_form_integral⟨n⟩(T, 𝒜, η)",
	},
		"Use one finite positive-chart partition near the compact union of the "+
			"two supports. The pointwise sum is a form with support inside that "+
			"union. Each weighted coefficient is continuous and compactly supported, "+
			"so Euclidean IntegralAdd and finite distributivity give the asserted sum."),
})}

var IntegralScale = integralScaleThm{family.Add(registry.ProofEntry{
	Name: "IntegralScale",
	Key:  "prop_f28a010ffdbf610a",
	Deps: []registry.EntryLike{
		IntegralByPartition,
		IntegralPartitionExists,
		chartIntegralDef,
		differential_form.FormModule,
		differential_form.SupportDef,
		differential_form.SupportClosed,
		differential_form.WeightDef,
		differential_form.ChartCoefficientCompact,
		compact.ClosedSubsetCompact,
		vec_integral.IntegralScale,
		vec_integral.CcRapid,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀a:real.",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"manifold_form_on⟨n⟩(T, 𝒜, n, ω)",
			"compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω))",
		},
		Conclusion: "manifold_form_integral⟨n⟩(T, " +
			"    𝒜, " +
			"    λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). a * ω(c, y, P)) = " +
			"a * manifold_form_integral⟨n⟩(T, 𝒜, ω)",
	},
		"The scaled form has support inside the original compact support, "+
			"including a = 0. Use a partition near that support and apply Euclidean "+
			"IntegralScale to each weighted coefficient before taking the finite sum."),
})}

var IntegralFiniteSum = integralFiniteSumThm{family.Add(registry.ProofEntry{
	Name: "IntegralFiniteSum",
	Key:  "prop_e5dcfd230449ddb3",
	Reading: "Orientation is a separate hypothesis even when " +
		"N = 0; the summand assumptions alone are then vacuous.",
	Deps: []registry.EntryLike{
		IntegralZero,
		IntegralAdd,
		differential_form.FormModule,
		differential_form.SupportDef,
		differential_form.SupportClosed,
		compact.CompactUnion,
		compact.ClosedSubsetCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀N:num. " +
			"∀ω:(num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"∀i:num. " +
				"    i < N ⇒ " +
				"    manifold_form_on⟨n⟩(T, 𝒜, n, ω(i)) ∧ compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω(i)))",
		},
		Conclusion: "manifold_form_integral⟨n⟩(T, " +
			"    𝒜, " +
			"    λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"        Σ_{i<N} ω(i, c, y, P)) = " +
			"Σ_{i<N} manifold_form_integral⟨n⟩(T, 𝒜, ω(i))",
	},
		"Induct on the number of summands using IntegralZero and IntegralAdd. At each stage the sum "+
			"is a form whose closed support lies in the finite compact union of the summand supports."),
})}

var IntegralAtlasInvariant = integralAtlasInvariantThm{family.Add(registry.ProofEntry{
	Name: "IntegralAtlasInvariant",
	Key:  "prop_9f4ad2092513fe68",
	Deps: []registry.EntryLike{
		OrientedAtlasChange,
		IntegralSpec,
		IntegralValue,
		HasIntegralDef,
		integralPartitionDef,
		differential_form.FormOnDef,
		differential_form.SupportDef,
		differential_form.WeightDef,
		smooth_manifold.SmoothFunctionDef,
		smooth_manifold.PartitionOfUnityDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ℬ:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨n⟩(T, ℬ)",
			"∀c:prod(set(A), A → num → real). c ∈ ℬ ⇒ positive_manifold_chart⟨n⟩(T, 𝒜, c)",
			"manifold_form_on⟨n⟩(T, 𝒜, n, ω)",
			"compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω))",
		},
		Conclusion: "manifold_form_integral⟨n⟩(T, 𝒜, ω) = manifold_form_integral⟨n⟩(T, ℬ, ω)",
	},
		"OrientedAtlasChange identifies both the smooth compatible charts and the "+
			"positive charts. Consequently the form carrier, support, scalar functions, "+
			"weights and permitted partitions coincide. A witness for either integral "+
			"relation is a witness for the other, so the selected integral values agree."),
})}

var IntegralRestriction = integralRestrictionThm{family.Add(registry.ProofEntry{
	Name: "IntegralRestriction",
	Key:  "prop_d21d27e9f1c5ad16",
	Reading: "The right integral uses the positive open atlas. Its smooth completion agrees with " +
		"the usual open atlas used by manifold_form_restrict, so the same normalized restricted " +
		"family is a form for both. A scalar weight supported inside U is already zero outside U as " +
		"a total function: support vanishing handles points in the ambient carrier, and scalar " +
		"normalization handles points outside it. The same weights can therefore serve both integrals.",
	Deps: []registry.EntryLike{
		OrientedOpenSubmanifold,
		IntegralByPartition,
		integralPartitionDef,
		differential_form.FormRestrict,
		differential_form.SupportRestrict,
		differential_form.RestrictDef,
		smooth_manifold.PartitionOfUnity,
		smooth_manifold.FunctionRestrict,
		compact.CompactInSubtopology,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"manifold_form_on⟨n⟩(T, 𝒜, n, ω)",
			"compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω))",
			"manifold_form_support⟨n⟩(T, 𝒜, ω) ⊆ U",
		},
		Conclusion: "manifold_form_integral⟨n⟩(T, 𝒜, ω) = " +
			"manifold_form_integral⟨n⟩(subtopology(T, U), " +
			"    oriented_open_atlas⟨n⟩(T, 𝒜, U), " +
			"    manifold_form_restrict⟨n⟩(T, 𝒜, U, ω))",
	},
		"Choose a partition near the compact support subordinate to positive chart domains contained "+
			"in U. Its weights vanish outside U and give the same partition on the open submanifold. The "+
			"retained chart components and coordinate integral sums are identical, yielding the equality."),
})}

var IntegralExtension = integralExtensionThm{family.Add(registry.ProofEntry{
	Name: "IntegralExtension",
	Key:  "prop_1ffd1f230634694f",
	Reading: "Compactness in the open subspace gives ambient compactness. " +
		"Ambient Hausdorffness then makes the source support closed in the " +
		"whole manifold, exactly as required by the zero-extension cards.",
	Deps: []registry.EntryLike{
		OrientedOpenSubmanifold,
		IntegralRestriction,
		differential_form.ExtendZeroForm,
		differential_form.ExtendZeroRestrict,
		differential_form.ExtendZeroSupport,
		compact.CompactInSubtopology,
		compact.CompactClosed,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"manifold_form_on⟨n⟩(subtopology(T, U), oriented_open_atlas⟨n⟩(T, 𝒜, U), n, ω)",
			"compact_in(subtopology(T, U), " +
				"    manifold_form_support⟨n⟩(subtopology(T, U), oriented_open_atlas⟨n⟩(T, 𝒜, U), ω))",
		},
		Conclusion: "manifold_form_integral⟨n⟩(T, 𝒜, manifold_form_extend_zero⟨n⟩(T, 𝒜, U, ω)) = " +
			"manifold_form_integral⟨n⟩(subtopology(T, U), oriented_open_atlas⟨n⟩(T, 𝒜, U), ω)",
	},
		"Compact submanifold support is compact and closed in the ambient Hausdorff manifold. The common "+
			"smooth completion of the two open atlases lets the zero-extension cards apply. Restricting the "+
			"resulting ambient form recovers ω, and IntegralRestriction proves the integral equality."),
})}

var IntegralReverseOrientation = integralReverseOrientationThm{family.Add(registry.ProofEntry{
	Name: "IntegralReverseOrientation",
	Key:  "prop_e1ba292b165c9e22",
	Reading: "The condition 0 < n is essential. In dimension zero the empty determinant " +
		"is one and the reflected atlas gives the same canonical positive orientation.",
	Deps: []registry.EntryLike{
		ReflectedAtlas,
		reflectedAtlasDef,
		IntegralByPartition,
		IntegralPartitionExists,
		chartIntegralDef,
		differential_form.FormOnDef,
		differential_form.WeightDef,
		differential_form.ChartCoefficientCompact,
		vec_form.TopDegreeDeterminant,
		vec_form.PullbackDef,
		vec_integral.ChangeOfVariables,
		vec_integral.IntegralScale,
		vec_integral.CcRapid,
		determinant.DeterminantDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"0 < n",
			"manifold_form_on⟨n⟩(T, 𝒜, n, ω)",
			"compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω))",
		},
		Conclusion: "manifold_form_integral⟨n⟩(T, reflected_manifold_atlas(𝒜), ω) = " +
			"-manifold_form_integral⟨n⟩(T, 𝒜, ω)",
	},
		"Reflect every chart in a partition while keeping its base weights. The "+
			"reflected atlas has the same smooth compatibility class, so these are still "+
			"the same form and weights. In positive dimension the reflection determinant "+
			"is minus one, while its absolute Jacobian is one; top-degree transformation "+
			"and Euclidean change of variables therefore negate every coordinate integral."),
})}
