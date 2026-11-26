package projection_bundle

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/registry"
)

var TrivialBundle = trivialBundleThm{family.Add(registry.ProofEntry{
	Name: "TrivialBundle",
	Key:  "prop_a842e4983f01a65",
	Deps: []registry.EntryLike{
		continuous.Constant,
		continuous.Eq,
		module.ModuleSumSingle,
		complex_field.ConjOfReal,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀r:num.",
		Hypotheses: []string{"is_topology(T)"},
		Conclusion: "continuous_projection_bundle(T, projection_trivial(T, r))",
	},
		"The identity on the finite coordinate block is a continuous Hermitian "+
			"projection. Each entry is constant on the carrier, one on the diagonal below r "+
			"and zero elsewhere (continuous.Constant, continuous.Eq); conjugation fixes both "+
			"(ConjOfReal), and an entry of its square has one nonzero term (ModuleSumSingle)."),
})}

var IsomorphismEquivalence = isomorphismEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismEquivalence",
	Key:  "prop_90a06157f4daeaf9",
	Deps: []registry.EntryLike{
		complex_topology.ContinuousComplexSum,
		complex_topology.ContinuousComplexMul,
		module.ModuleSumSwap,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀P Q R:prod(num, A → num → num → complex).",
		Hypotheses: []string{
			"continuous_projection_bundle(T, P)",
			"continuous_projection_bundle(T, Q)",
			"continuous_projection_bundle(T, R)",
		},
		Conclusion: "projection_isomorphic(T, P, P) ∧ " +
			"(projection_isomorphic(T, P, Q) ⇒ projection_isomorphic(T, Q, P)) ∧ " +
			"(projection_isomorphic(T, P, Q) ∧ projection_isomorphic(T, Q, R) ⇒ " +
			"    projection_isomorphic(T, P, R))",
	},
		"Compose the rectangular bundle maps and reverse their inverses; the projections are the "+
			"identities on their images. P is its own map and inverse by idempotence. A composite's entries "+
			"are finite sums of products of continuous entries (ContinuousComplexSum, ContinuousComplexMul), "+
			"and matrix products associate by exchanging two finite sums (ModuleSumSwap)."),
})}

var SumBundle = sumBundleThm{family.Add(registry.ProofEntry{
	Name: "SumBundle",
	Key:  "prop_a4b1167d678a0e6",
	Deps: []registry.EntryLike{
		continuous.Constant,
		continuous.Eq,
		module.ModuleSumDisjointUnion,
		module.ModuleSumImage,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀P Q:prod(num, A → num → num → complex).",
		Hypotheses: []string{"continuous_projection_bundle(T, P)", "continuous_projection_bundle(T, Q)"},
		Conclusion: "continuous_projection_bundle(T, projection_sum(P, Q))",
	},
		"The block diagonal projection is continuous, self-adjoint and idempotent. Each entry "+
			"is an entry of P, a shifted entry of Q or zero (continuous.Constant, continuous.Eq). "+
			"The sum over k < fst(P) + fst(Q) splits at fst(P) (ModuleSumDisjointUnion), its upper "+
			"part read down by the shift (ModuleSumImage); the off-diagonal blocks contribute zero."),
})}

var TensorBundle = tensorBundleThm{family.Add(registry.ProofEntry{
	Name: "TensorBundle",
	Key:  "prop_d5a9727ed989a1da",
	Deps: []registry.EntryLike{
		complex_topology.ContinuousComplexMul,
		continuous.Constant,
		module.ModuleSumCross,
		module.ModuleSumImage,
		nat_div_mod.Division,
		nat_div_mod.DivMultAdd,
		nat_div_mod.ModMultAdd,
		complex_field.ConjMul,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀P Q:prod(num, A → num → num → complex).",
		Hypotheses: []string{"continuous_projection_bundle(T, P)", "continuous_projection_bundle(T, Q)"},
		Conclusion: "continuous_projection_bundle(T, projection_tensor(P, Q))",
	},
		"Finite double sums give idempotence of the Kronecker projection; zero ambient dimension "+
			"gives the zero projection. An entry is a product of an entry of P and one of Q "+
			"(ContinuousComplexMul). The index k below fst(P)·fst(Q) is the pair (div(k, fst(Q)), rem(k, "+
			"fst(Q))), a bijection onto the product of the two ranges (Division, DivMultAdd, ModMultAdd), "+
			"so the sum over k is the double sum (ModuleSumImage, ModuleSumCross) and factors."),
})}

var SumIsomorphism = sumIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "SumIsomorphism",
	Key:  "prop_1b79b2bda6b5d4d2",
	Deps: []registry.EntryLike{SumBundle, module.ModuleSumDisjointUnion, module.ModuleSumImage},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀P Q R S:prod(num, A → num → num → complex).",
		Hypotheses: []string{"projection_isomorphic(T, P, Q)", "projection_isomorphic(T, R, S)"},
		Conclusion: "projection_isomorphic(T, projection_sum(P, R), projection_sum(Q, S))",
	},
		"Block sum of the maps and their inverses gives the bundle isomorphism. Its "+
			"two ends are bundles by SumBundle; the block products split as in SumBundle."),
})}

var TensorIsomorphism = tensorIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "TensorIsomorphism",
	Key:  "prop_e8a43caa160d6224",
	Deps: []registry.EntryLike{
		TensorBundle,
		complex_topology.ContinuousComplexMul,
		module.ModuleSumCross,
		module.ModuleSumImage,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀P Q R S:prod(num, A → num → num → complex).",
		Hypotheses: []string{"projection_isomorphic(T, P, Q)", "projection_isomorphic(T, R, S)"},
		Conclusion: "projection_isomorphic(T, projection_tensor(P, R), projection_tensor(Q, S))",
	},
		"Tensor the inverse bundle maps; normalization makes the padded coordinates "+
			"vanish. The ends are bundles by TensorBundle, and the Kronecker products "+
			"of the maps multiply blockwise through the reindexing of TensorBundle."),
})}

var PullbackBundle = pullbackBundleThm{family.Add(registry.ProofEntry{
	Name: "PullbackBundle",
	Key:  "prop_b081fe3f70dd2c6c",
	Deps: []registry.EntryLike{continuous.Compose, continuous.Eq, continuous.MapsInto},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). ∀P:prod(num, B → num → num → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"continuous_map(T, S, f)",
			"continuous_projection_bundle(S, P)",
		},
		Conclusion: "continuous_projection_bundle(T, projection_pullback(T, f, P))",
	},
		"Continuity of each component is preserved by pullback, followed by normalization outside the "+
			"source carrier. On ⋃T an entry is the entry of P at f(x) (continuous.Compose, continuous.Eq), "+
			"and f(x) lies in ⋃S (continuous.MapsInto), where P is Hermitian and idempotent."),
})}

// RankTrace — the rank of a projection at a point is its trace, a whole
// number at most the ambient dimension.
var RankTrace = rankTraceThm{family.Add(registry.ProofEntry{
	Name: "RankTrace",
	Key:  "prop_63bb63206eda843b",
	Deps: []registry.EntryLike{
		module_dimension.IdempotentTraceIsRank,
		module_dimension.TraceFromBasis,
		module_dimension.SubmoduleDim,
		module_dimension.DimBasis,
	},
	Build: family.Card(Statement{
		Binders: "∀P:prod(num, A → num → num → complex). ∀x:A.",
		Hypotheses: []string{
			"∀i j:num. " +
				"    i < fst(P) ∧ j < fst(P) ⇒ " +
				"    module_sum(complex_add, " +
				"        complex_of_real(&0), " +
				"        {k:num | k < fst(P)}, " +
				"        λk:num. snd(P)(x, i, k) * snd(P)(x, k, j)) = " +
				"    snd(P)(x, i, j)",
		},
		Conclusion: "projection_rank(P, x) ≤ fst(P) ∧ " +
			"Σ_{i<fst(P)} re(snd(P, x, i, i)) = &(projection_rank(P, x))",
	},
		"At x the matrix is an idempotent endomorphism of the coordinate space ℂ^fst(P). "+
			"Its trace, read in the coordinate basis (TraceFromBasis), is the dimension of "+
			"its image (IdempotentTraceIsRank), at most fst(P), the dimension of ℂ^fst(P) by "+
			"its coordinate basis (SubmoduleDim, DimBasis); the trace is that whole number, "+
			"so its real part is too, and the choice in projection_rank picks it."),
	Reading: "Only the idempotence of the matrix at x is read: neither continuity, nor " +
		"the Hermitian symmetry, nor any other point. A projection bundle at a point of " +
		"its base meets it, and so does a smooth one. It makes projection_rank the " +
		"dimension of the image, where its definition only chooses a number when one exists.",
})}

// PointIsomorphicIffRank — over a one-point base two projection bundles are
// isomorphic exactly when their ranks agree.
var PointIsomorphicIffRank = pointIsomorphicIffRankThm{family.Add(registry.ProofEntry{
	Name: "PointIsomorphicIffRank",
	Key:  "prop_3a57a05464396681",
	Deps: []registry.EntryLike{
		RankTrace,
		module.ModuleSumSwap,
		module_dimension.IdempotentTraceIsRank,
		module_dimension.DimBasis,
		module_dimension.TraceFromBasis,
		module_dimension.SubmoduleDim,
		continuous.Constant,
		continuous.Eq,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀x:A. ∀P Q:prod(num, A → num → num → complex).",
		Hypotheses: []string{
			"⋃T = {x}",
			"continuous_projection_bundle(T, P)",
			"continuous_projection_bundle(T, Q)",
		},
		Conclusion: "projection_isomorphic(T, P, Q) ⇔ projection_rank(P, x) = projection_rank(Q, x)",
	},
		"Forward: VU = P(x) and UV = Q(x), and the trace of a product does not depend on the order of "+
			"its factors, the two finite sums of its entries exchanged (ModuleSumSwap), so P(x) and Q(x) "+
			"have one trace, which is the rank (RankTrace). Backward: each image has dimension the trace "+
			"read in the coordinate basis (TraceFromBasis, IdempotentTraceIsRank), the rank (RankTrace); "+
			"each is finite-dimensional (SubmoduleDim), so the two have finite bases of one size "+
			"(DimBasis), and matching them gives a linear isomorphism L between them. U = L·P(x) and V = "+
			"L⁻¹·Q(x) satisfy QU = UP = U, PV = VQ = V, VU = P(x) and UV = Q(x). Over the one point every "+
			"entry is constant on the carrier, so continuous (continuous.Constant, continuous.Eq)."),
	Reading: "The classification of bundles over a point by rank. The two ambient dimensions " +
		"may differ. The forward half holds at every point of any base; the backward half needs " +
		"the one point, since over a larger base bundles of one rank need not be isomorphic.",
})}

// ProjectionsCloseIsomorphic — two projection bundles of one ambient
// dimension that are uniformly within distance one are isomorphic.
var ProjectionsCloseIsomorphic = projectionsCloseIsomorphicThm{family.Add(registry.ProofEntry{
	Name: "ProjectionsCloseIsomorphic",
	Key:  "prop_75a90d0df175ce0f",
	Deps: []registry.EntryLike{
		complex_topology.ContinuousComplexSum,
		complex_topology.ContinuousComplexMul,
		module.ModuleSumSwap,
		complex_topology.ContinuousComplexInv,
		complex_topology.ContinuousComplexProduct,
		determinant.AdjugateIdentity,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀P Q:prod(num, A → num → num → complex).",
		Hypotheses: []string{
			"continuous_projection_bundle(T, P)",
			"continuous_projection_bundle(T, Q)",
			"fst(Q) = fst(P)",
			"∀x:A. x ∈ ⋃T ⇒ Σ_{i<fst(P)} Σ_{j<fst(P)} |snd(P, x, i, j) - snd(Q, x, i, j)| ^ 2 < &1",
		},
		Conclusion: "projection_isomorphic(T, P, Q)",
	},
		"The bound on the sum of squares bounds the operator norm of P(x) − Q(x) below one. Then "+
			"W = QP + (1 − Q)(1 − P) is invertible, its inverse continuous in x through the adjugate, "+
			"and WP = QW. U = QP is a map from P to Q, V = PW⁻¹ one back, with VU = P and UV = Q on "+
			"⋃T; their entries are continuous (ContinuousComplexSum, ContinuousComplexMul). The "+
			"operator norm is at most the Hilbert–Schmidt norm by Cauchy–Schwarz, and W*W = 1 − (P − "+
			"Q)², so W is invertible; its inverse is the adjugate over a nowhere-zero determinant "+
			"(AdjugateIdentity, ContinuousComplexProduct, ContinuousComplexInv)."),
	Reading: "The sum of squares is the Hilbert–Schmidt norm, which dominates the " +
		"operator norm; any bound below one serves. Equal ambient dimension makes the " +
		"difference a square matrix; the conclusion also forces the two ranks to agree.",
})}

var HomotopicPullbacks = homotopicPullbacksThm{family.Add(registry.ProofEntry{
	Name: "HomotopicPullbacks",
	Key:  "prop_3d5ad0c87b25b6a9",
	Deps: []registry.EntryLike{
		ProjectionsCloseIsomorphic,
		PullbackBundle,
		IsomorphismEquivalence,
		product_topology.TubeLemma,
		product_topology.CompactProduct,
		continuous.Compose,
		product_topology.PairedContinuousIff,
		real_topology.ClosedIntervalCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀f g:(A → B). ∀P:prod(num, B → num → num → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, ⋃T)",
			"continuous_projection_bundle(S, P)",
			"homotopic_rel(T, S, ∅, f, g)",
		},
		Conclusion: "projection_isomorphic(T, projection_pullback(T, f, P), projection_pullback(T, g, P))",
	},
		"Subdivide the homotopy uniformly on the compact base so successive projections are close, and "+
			"compose the resulting image isomorphisms. The entries of P along the homotopy H are continuous "+
			"on T × [0, 1] (continuous.Compose); compactness of the base (TubeLemma, CompactProduct) gives "+
			"one step size for which pullbacks at neighbouring times satisfy ProjectionsCloseIsomorphic. "+
			"Each is a bundle (PullbackBundle), and IsomorphismEquivalence chains the steps. Each time slice "+
			"x ↦ (x, t) is continuous (PairedContinuousIff), and [0, 1] is compact (ClosedIntervalCompact)."),
})}

var TotalSpaceLocallyCompact = totalSpaceLocallyCompactThm{family.Add(registry.ProofEntry{
	Name: "TotalSpaceLocallyCompact",
	Key:  "prop_65f44bda1d9f96e0",
	Deps: []registry.EntryLike{
		product_topology.LocallyCompactProduct,
		complex_topology.CoordinateLocallyCompact,
		product_topology.HausdorffProduct,
		product_topology.HausdorffIffDiagonalClosed,
		product_topology.FstContinuous,
		product_topology.SndContinuous,
		product_topology.IndexedProjectionContinuous,
		complex_topology.ContinuousComplexSum,
		complex_topology.ContinuousComplexMul,
		compact.LocallyCompactClosedSubtopology,
		topological_space.HausdorffSubtopology,
		continuous.ClosedPreimage,
		complex_topology.ComplexHausdorff,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀P:prod(num, A → num → num → complex).",
		Hypotheses: []string{
			"continuous_projection_bundle(T, P)",
			"locally_compact_space(T)",
			"hausdorff(T)",
		},
		Conclusion: "is_topology(projection_total_topology(T, P)) ∧ " +
			"locally_compact_space(projection_total_topology(T, P)) ∧ " +
			"hausdorff(projection_total_topology(T, P))",
	},
		"The image of a continuous projection is a closed subspace of the base times finite complex "+
			"coordinates. Its equations P(x)v = v compare continuous functions of (x, v) (FstContinuous, "+
			"SndContinuous, IndexedProjectionContinuous, ContinuousComplexSum, ContinuousComplexMul) in the "+
			"Hausdorff plane, so they cut a closed set (HausdorffIffDiagonalClosed). T × ℂ^fst(P) is locally "+
			"compact and Hausdorff (LocallyCompactProduct, CoordinateLocallyCompact, HausdorffProduct), and "+
			"so is a closed subspace of it (LocallyCompactClosedSubtopology, HausdorffSubtopology)."),
})}
