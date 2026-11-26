package bott_periodicity

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/k_compact_support"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/projection_bundle"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/registry"
)

var CompactInverse = compactInverseThm{family.Add(registry.ProofEntry{
	Name: "CompactInverse",
	Key:  "prop_acbecfb5957e3229",
	Deps: []registry.EntryLike{k_compact_support.CompactComparison},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀a:set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))). " +
			"∀b:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, ⋃T)",
			"hausdorff(T)",
			"a ∈ (k_ring(T)).carrier",
			"b ∈ (kc_group(T)).carrier",
		},
		Conclusion: "kc_to_k(T, k_to_kc(T, a)) = a ∧ k_to_kc(T, kc_to_k(T, b)) = b",
	},
		"On a compact base the straight-line homotopy from the triple map to zero "+
			"has compact support; stable virtual differences give the inverse comparison."),
})}

var BottTriple = bottTripleThm{family.Add(registry.ProofEntry{
	Name: "BottTriple",
	Key:  "prop_1e3cceabc55d6baf",
	Deps: []registry.EntryLike{
		projection_bundle.TrivialBundle,
		continuous.Identity,
		continuous.Constant,
		module.ModuleSumSingle,
		compact.FiniteCompact,
	},
	Build: family.Card("kc_supported_in(complex_topology, {complex_of_real(&0)}, bott_triple)",
		"Multiplication by z is invertible away from zero, with inverse multiplication by its "+
			"reciprocal. Both projections are the trivial line (TrivialBundle); the map's one entry is "+
			"z itself and the others are zero (continuous.Identity, continuous.Constant), its products "+
			"with the projections have one term (ModuleSumSingle), and {0} is compact (FiniteCompact)."),
})}

var ClutchingTriple = clutchingTripleThm{family.Add(registry.ProofEntry{
	Name: "ClutchingTriple",
	Key:  "prop_148805113f3467db",
	Deps: []registry.EntryLike{
		projection_bundle.TrivialBundle,
		complex_topology.ContinuousComplexMul,
		continuous.Compose,
		product_topology.PairedContinuousIff,
		product_topology.CompactProduct,
		complex_topology.CircleCompact,
		real_valued.ContinuousCompactMaximum,
		compact.FiniteCompact,
		complex_topology.ContinuousComplexInv,
		complex_topology.ModulusContinuous,
		compact.CompactInSubtopology,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀r:num. ∀g:(A → complex → num → num → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, ⋃T)",
			"bott_clutching(T, r, g)",
		},
		Conclusion: "kc_supported_in(product_topology(T, complex_topology), " +
			"    set_cross(⋃T, {complex_of_real(&0)}), " +
			"    bott_clutching_triple(T, r, g))",
	},
		"Radial multiplication extends the clutching map continuously across zero, uniformly on the "+
			"compact base and circle; it is invertible at every nonzero radius. The projections are trivial "+
			"(TrivialBundle). Away from zero the map is |z| times g at (x, z/|z|), continuous by composition "+
			"(ContinuousComplexMul, continuous.Compose, product_topology.PairedContinuousIff); g is bounded "+
			"on the compact base times the circle (CompactProduct, CircleCompact, "+
			"real_valued.ContinuousCompactMaximum), so the map tends to zero at z = 0. The support ⋃T × {0} "+
			"is compact (CompactProduct, FiniteCompact). z/|z| is continuous off zero (ContinuousComplexInv, "+
			"ModulusContinuous); the bound on |g| is the maximum of |g| (ContinuousCompactMaximum) on the "+
			"product of the base and the circle, a compact space (CompactInSubtopology, CompactProduct)."),
})}

var LaurentApproximation = laurentApproximationThm{family.Add(registry.ProofEntry{
	Name: "LaurentApproximation",
	Key:  "prop_b069f3a9aefcd99",
	Deps: []registry.EntryLike{ClutchingTriple},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀r:num. ∀g:(A → complex → num → num → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, ⋃T)",
			"hausdorff(T)",
			"bott_clutching(T, r, g)",
		},
		Conclusion: "∃p:(A → complex → num → num → complex). " +
			"    bott_laurent_matrix(T, r, p) ∧ " +
			"    bott_clutching(T, r, p) ∧ " +
			"    kc_triple_homotopic(product_topology(T, complex_topology), " +
			"        bott_clutching_triple(T, r, g), " +
			"        bott_clutching_triple(T, r, p))",
	},
		"Parameter-dependent trigonometric approximation is uniform on the compact base times "+
			"the circle. A uniform inverse bound keeps the straight-line interpolation invertible "+
			"on the circle, and radial extension gives a homotopy with support at zero."),
})}

var ClutchingRepresentation = clutchingRepresentationThm{family.Add(registry.ProofEntry{
	Name: "ClutchingRepresentation",
	Key:  "prop_1f0b2b336e03ae7f",
	Deps: []registry.EntryLike{projection_bundle.HomotopicPullbacks},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀a:set(prod(prod(num, prod(A, complex) → num → num → complex), " +
			"            prod(prod(num, prod(A, complex) → num → num → complex), " +
			"                prod(A, complex) → num → num → complex))).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, ⋃T)",
			"hausdorff(T)",
			"a ∈ (kc_group(product_topology(T, complex_topology))).carrier",
		},
		Conclusion: "∃r:num. ∃g:(A → complex → num → num → complex). " +
			"    bott_clutching(T, r, g) ∧ " +
			"    a = kc_class(product_topology(T, complex_topology), bott_clutching_triple(T, r, g))",
	},
		"Compress compact singular support into a disk. Both bundles on the disk retract to bundles on "+
			"X; add complements and use their isomorphism on the boundary to obtain trivial clutching data."),
})}

var BottHomomorphism = bottHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "BottHomomorphism",
	Key:  "prop_3725911113e578c1",
	Deps: []registry.EntryLike{CompactInverse, BottTriple, k_compact_support.ExternalAdditive},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)).",
		Hypotheses: []string{"is_topology(T)", "compact_in(T, ⋃T)", "hausdorff(T)"},
		Conclusion: "group_homomorphism(additive_group(k_ring(T)), " +
			"    kc_group(product_topology(T, complex_topology)), " +
			"    bott_map(T))",
	}, "The compact comparison and external product preserve addition."),
})}

var BottSurjective = bottSurjectiveThm{family.Add(registry.ProofEntry{
	Name: "BottSurjective",
	Key:  "prop_b675642ceeffe99f",
	Deps: []registry.EntryLike{ClutchingRepresentation, LaurentClutchingFormula, BottHomomorphism},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)).",
		Hypotheses: []string{"is_topology(T)", "compact_in(T, ⋃T)", "hausdorff(T)"},
		Conclusion: "image(bott_map(T), (k_ring(T)).carrier) = " +
			"(kc_group(product_topology(T, complex_topology))).carrier",
	},
		"Represent the class by a clutching matrix and approximate it by Laurent "+
			"polynomials. Clear negative powers, add a small highest monomial to make the "+
			"polynomial monic, and linearize. Its spectral subbundles inside and outside "+
			"the circle express the class as a virtual bundle times the chosen Bott class."),
})}

var BottInjective = bottInjectiveThm{family.Add(registry.ProofEntry{
	Name: "BottInjective",
	Key:  "prop_5b6d912669cd3540",
	Deps: []registry.EntryLike{InverseBottNormalization, BottHomomorphism},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)).",
		Hypotheses: []string{"is_topology(T)", "compact_in(T, ⋃T)", "hausdorff(T)"},
		Conclusion: "injective_on((k_ring(T)).carrier, bott_map(T))",
	},
		"The finite polynomial-quotient construction gives a virtual bundle for each clutching "+
			"class. Stabilization, polynomial linearization and spectral splitting make it independent "+
			"of all choices; applied to the z representative it returns the original virtual bundle."),
})}

var BottPeriodicity = bottPeriodicityThm{family.Add(registry.ProofEntry{
	Name: "BottPeriodicity",
	Key:  "prop_1020a3517b202270",
	Deps: []registry.EntryLike{BottSurjective, BottInjective, BottHomomorphism},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)).",
		Hypotheses: []string{"is_topology(T)", "compact_in(T, ⋃T)", "hausdorff(T)"},
		Conclusion: "group_isomorphism(additive_group(k_ring(T)), " +
			"    kc_group(product_topology(T, complex_topology)), " +
			"    bott_map(T))",
	}, "The Bott product is an isomorphism for every compact Hausdorff parameter space."),
})}

var CompanionInsideBundle = companionInsideBundleThm{family.Add(registry.ProofEntry{
	Name: "CompanionInsideBundle",
	Key:  "prop_f4298f5fbff3b345",
	Deps: []registry.EntryLike{CompanionLinearLoop, InsideProjectionBundle},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀r d:num. ∀a:(A → num → num → num → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"bott_polynomial_coefficients(T, r, d, a)",
			"bott_clutching(T, r, bott_polynomial_loop(T, r, d, a))",
		},
		Conclusion: "continuous_projection_bundle(T, " +
			"    bott_inside_projection(T, r * d, bott_companion(T, r, d, a)))",
	},
		"Companion linearization identifies the unit-circle resolvent with that of the polynomial. "+
			"The Riesz idempotent selects generalized eigenspaces inside the circle; its image has a "+
			"continuous Hermitian orthogonal projection. The invariant complementary spectral space need "+
			"not be the orthogonal complement. CompanionLinearLoop carries the clutching hypothesis to "+
			"the companion's linear loop, and InsideProjectionBundle gives the continuous projection."),
})}

// CompanionLinearLoop — the block companion of a monic matrix polynomial
// that is invertible on the circle has no eigenvalue on the circle.
var CompanionLinearLoop = companionLinearLoopThm{family.Add(registry.ProofEntry{
	Name: "CompanionLinearLoop",
	Key:  "prop_9853e7caf12bc0ca",
	Deps: []registry.EntryLike{
		complex_topology.ContinuousComplexAdd,
		complex_topology.ContinuousComplexMul,
		continuous.Compose,
		continuous.Constant,
		product_topology.FstContinuous,
		product_topology.SndContinuous,
		nat_div_mod.Division,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀r d:num. ∀a:(A → num → num → num → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"bott_polynomial_coefficients(T, r, d, a)",
			"bott_clutching(T, r, bott_polynomial_loop(T, r, d, a))",
		},
		Conclusion: "bott_clutching(T, r * d, bott_linear_loop(T, r * d, bott_companion(T, r, d, a)))",
	},
		"Block companion linearization. Read in blocks of size r, z·1 − C(x) has z on the "+
			"diagonal blocks, −1 below them and the coefficients a(x, k) in the last block "+
			"column; eliminating the blocks in turn leaves p(x, z) = z^d + Σ a(x, k) z^k, so an "+
			"inverse of p(x, z) gives one of z·1 − C(x) by back substitution on the block rows. "+
			"The entries are continuous on the base times the circle: z, the coefficients along "+
			"fst, and constants (ContinuousComplexAdd, ContinuousComplexMul, FstContinuous, "+
			"SndContinuous). The difference z − C(x, i, j) is read as z plus −1 times the entry."),
	Reading: "At d = 0 the companion has size zero and the conclusion is the empty " +
		"clutching function. The coefficients' continuity is read for the companion's " +
		"entries; the polynomial loop's own continuity holds only on the circle.",
})}

// InsideProjectionBundle — for a continuous matrix with no eigenvalue on
// the circle, the orthogonal projection onto the vectors whose iterates
// tend to zero is a continuous projection bundle.
var InsideProjectionBundle = insideProjectionBundleThm{family.Add(registry.ProofEntry{
	Name: "InsideProjectionBundle",
	Key:  "prop_6d54dea23ec5341d",
	Deps: []registry.EntryLike{
		complex_topology.ContinuousComplexSum,
		complex_topology.ContinuousComplexMul,
		complex_topology.CircleCompact,
		product_topology.TubeLemma,
		complex_topology.ContinuousComplexInv,
		complex_topology.ContinuousComplexProduct,
		determinant.AdjugateIdentity,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀r:num. ∀C:(A → num → num → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"bott_clutching(T, r, bott_linear_loop(T, r, C))",
		},
		Conclusion: "continuous_projection_bundle(T, bott_inside_projection(T, r, C))",
	},
		"With no eigenvalue of C(x) on the circle, the vectors whose iterates tend to zero are the "+
			"sum of the generalized eigenspaces inside it, the image of the Riesz idempotent "+
			"(1/2πi)∮(z − C(x))⁻¹ dz; on the others the iterates grow. Near a point of the base the "+
			"resolvent is invertible uniformly over the compact circle (TubeLemma, CircleCompact), so "+
			"the idempotent is continuous, and the orthogonal projection onto its image is a "+
			"continuous expression in it and its adjoint (ContinuousComplexSum, ContinuousComplexMul). "+
			"A Hermitian idempotent is fixed by its image, so the choice in bott_inside_projection is "+
			"that projection. With E the idempotent, E + E* − 1 is invertible, its square being 1 + (E "+
			"− E*)(E − E*)*, and E(E + E* − 1)⁻¹ is the orthogonal projection onto the image of E; the "+
			"inverses here and of the resolvent are adjugates over nowhere-zero determinants "+
			"(AdjugateIdentity, ContinuousComplexProduct, ContinuousComplexInv). The splitting into "+
			"generalized eigenspaces is the Jordan decomposition at each x."),
	Reading: "The continuity of C is part of the hypothesis: the clutching " +
		"function's entries off the diagonal are −C(x, i, j) on the base times the circle.",
})}

var PolynomializationExists = polynomializationExistsThm{family.Add(registry.ProofEntry{
	Name: "PolynomializationExists",
	Key:  "prop_ce2a0adeaa535bf5",
	Deps: []registry.EntryLike{LaurentApproximation},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀r:num. ∀g:(A → complex → num → num → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, ⋃T)",
			"hausdorff(T)",
			"bott_clutching(T, r, g)",
		},
		Conclusion: "∃N d:num. ∃c:real. ∃a:(A → num → num → num → complex). " +
			"    bott_polynomialization(T, r, g, N, d, c, a)",
	},
		"Choose a sufficiently close Laurent approximation, clear its negative powers, and add a "+
			"small highest scalar monomial. The common inverse bound preserves invertibility along the "+
			"straight interpolation; division by its positive leading scalar makes the polynomial monic."),
})}

var PolynomializationIndependent = polynomializationIndependentThm{family.Add(registry.ProofEntry{
	Name: "PolynomializationIndependent",
	Key:  "prop_13636d32241df0e0",
	Deps: []registry.EntryLike{CompanionInsideBundle},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀r N d M e:num. " +
			"∀g:(A → complex → num → num → complex). " +
			"∀c b:real. " +
			"∀a q:(A → num → num → num → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, ⋃T)",
			"hausdorff(T)",
			"bott_clutching(T, r, g)",
			"bott_polynomialization(T, r, g, N, d, c, a)",
			"bott_polynomialization(T, r, g, M, e, b, q)",
		},
		Conclusion: "k_class(T, " +
			"    (bott_inside_projection(T, r * d, bott_companion(T, r, d, a)), " +
			"        projection_trivial(T, N * r))) = " +
			"k_class(T, " +
			"    (bott_inside_projection(T, r * e, bott_companion(T, r, e, q)), projection_trivial(T, M * r)))",
	},
		"Polynomial continuation allows singular leading coefficients between monic endpoints, by "+
			"using the finite quotient for roots inside the circle. Multiplying by z adds one trivial "+
			"rank-r summand. Common Laurent powers and stabilization therefore cancel the correction terms."),
})}

var ClutchingIndexOnPolynomialization = clutchingIndexOnPolynomializationThm{family.Add(registry.ProofEntry{
	Name: "ClutchingIndexOnPolynomialization",
	Key:  "prop_c6de47fdea45caa0",
	Deps: []registry.EntryLike{PolynomializationExists, PolynomializationIndependent},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀r N d:num. " +
			"∀g:(A → complex → num → num → complex). " +
			"∀c:real. " +
			"∀a:(A → num → num → num → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, ⋃T)",
			"hausdorff(T)",
			"bott_clutching(T, r, g)",
			"bott_polynomialization(T, r, g, N, d, c, a)",
		},
		Conclusion: "bott_clutching_index(T, r, g) = " +
			"k_class(T, " +
			"    (bott_inside_projection(T, r * d, bott_companion(T, r, d, a)), projection_trivial(T, N * r)))",
	}, "Existence and polynomialization independence characterize the selected finite virtual bundle."),
})}

var RelativeClutchingIndex = relativeClutchingIndexThm{family.Add(registry.ProofEntry{
	Name: "RelativeClutchingIndex",
	Key:  "prop_7a714388b626c264",
	Deps: []registry.EntryLike{ClutchingIndexOnPolynomialization, k_compact_support.Equivalence},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀r s:num. ∀g h:(A → complex → num → num → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, ⋃T)",
			"hausdorff(T)",
			"bott_clutching(T, r, g)",
			"bott_clutching(T, s, h)",
			"kc_equivalent(product_topology(T, complex_topology), " +
				"    bott_clutching_triple(T, r, g), " +
				"    bott_clutching_triple(T, s, h))",
		},
		Conclusion: "bott_clutching_index(T, r, g) = bott_clutching_index(T, s, h)",
	},
		"Present each compactly supported triple on a disk using a common complement of "+
			"both bundles. Changes of disk frames multiply the boundary map by "+
			"disk-extendible gauges; continuation gives them zero correction. Stabilization, "+
			"direct sum, degenerate triples and uniformly supported homotopies preserve the "+
			"resulting virtual bundle, so it descends through the actual relative relation."),
})}

var LaurentClutchingFormula = laurentClutchingFormulaThm{family.Add(registry.ProofEntry{
	Name: "LaurentClutchingFormula",
	Key:  "prop_4d23e5c613a473fb",
	Deps: []registry.EntryLike{ClutchingIndexOnPolynomialization},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀r:num. ∀g:(A → complex → num → num → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, ⋃T)",
			"hausdorff(T)",
			"bott_clutching(T, r, g)",
		},
		Conclusion: "kc_class(product_topology(T, complex_topology), bott_clutching_triple(T, r, g)) = " +
			"bott_map(T, bott_clutching_index(T, r, g))",
	},
		"Linearize the monic polynomial and split its pencil into inside and outside "+
			"spectral subbundles. The outside pencil contracts to an invertible map, while the "+
			"inside pencil contracts to z on its subbundle. Radial clutching of a product is "+
			"the sum, so removing the Laurent power subtracts N trivial rank-r Bott summands."),
})}

var InverseBottNormalization = inverseBottNormalizationThm{family.Add(registry.ProofEntry{
	Name: "InverseBottNormalization",
	Key:  "prop_fab8efb52ca67a47",
	Deps: []registry.EntryLike{RelativeClutchingIndex},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀a:set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, ⋃T)",
			"hausdorff(T)",
			"a ∈ (k_ring(T)).carrier",
		},
		Conclusion: "bott_inverse(T, bott_map(T, a)) = a",
	},
		"For a projection P regularize its loop I-P+zP to the monic quadratic z^2 I + "+
			"epsilon^-1(I-P+zP), with 0<epsilon<1. Its inside-root bundle is im P. Direct sums and reverse "+
			"loops give arbitrary virtual differences; relative descent removes the chosen disk presentation."),
})}

var CompactSupportBott = compactSupportBottThm{family.Add(registry.ProofEntry{
	Name: "CompactSupportBott",
	Key:  "prop_38fe05243cf80760",
	Deps: []registry.EntryLike{
		BottPeriodicity,
		k_compact_support.Excision,
		k_compact_support.OpenExtensionHomomorphism,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)).",
		Hypotheses: []string{"is_topology(T)", "locally_compact_space(T)", "hausdorff(T)"},
		Conclusion: "group_isomorphism(kc_group(T), " +
			"    kc_group(product_topology(T, complex_topology)), " +
			"    kc_bott_map(T))",
	},
		"Apply compact Bott on the one-point compactification. The split relative sequence for "+
			"removing the infinity fibre identifies the kernels of restriction to that fibre, "+
			"before and after product with C; external product commutes with open extension and "+
			"restriction. This special comparison concerns compact support and does not redefine Kc."),
})}
