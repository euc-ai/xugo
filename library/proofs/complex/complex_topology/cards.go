package complex_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// ContinuousComplexAdd — the sum of two continuous complex functions on a
// space is continuous.
var ContinuousComplexAdd = continuousComplexAddThm{family.Add(registry.ProofEntry{
	Name: "ContinuousComplexAdd",
	Key:  "prop_493d507cf5997ad0",
	Deps: []registry.EntryLike{
		ContinuousIffParts,
		real_valued.ContinuousRealAdd,
		complex_field.PartsAdd,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀f g:(A → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"continuous_map(T, complex_topology, f)",
			"continuous_map(T, complex_topology, g)",
		},
		Conclusion: "continuous_map(T, complex_topology, λx:A. f(x) + g(x))",
	},
		"Read the maps by their parts (ContinuousIffParts): the parts of the sum are "+
			"the sums of the parts (PartsAdd), continuous by real_valued.ContinuousRealAdd."),
	Reading: "The complex counterpart of real_valued.ContinuousRealAdd. Nothing " +
		"is read off T beyond the two maps: a point outside ⋃T is never asked about.",
})}

// ContinuousComplexMul — the product of two continuous complex functions
// on a space is continuous.
var ContinuousComplexMul = continuousComplexMulThm{family.Add(registry.ProofEntry{
	Name: "ContinuousComplexMul",
	Key:  "prop_3cc2b57b6403d10e",
	Deps: []registry.EntryLike{
		ContinuousIffParts,
		real_valued.ContinuousRealMul,
		real_valued.ContinuousRealAdd,
		real_valued.ContinuousRealSub,
		complex_field.PartsMul,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀f g:(A → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"continuous_map(T, complex_topology, f)",
			"continuous_map(T, complex_topology, g)",
		},
		Conclusion: "continuous_map(T, complex_topology, λx:A. f(x) * g(x))",
	},
		"Read the maps by their parts (ContinuousIffParts): the product's real part is re "+
			"f·re g − im f·im g and its imaginary part re f·im g + im f·re g (PartsMul), "+
			"continuous by real_valued.ContinuousRealMul, ContinuousRealSub and ContinuousRealAdd."),
	Reading: "The complex counterpart of real_valued.ContinuousRealMul.",
})}

// ContinuousComplexInv — the reciprocal of a continuous complex function
// on a space that vanishes nowhere on the carrier is continuous.
var ContinuousComplexInv = continuousComplexInvThm{family.Add(registry.ProofEntry{
	Name: "ContinuousComplexInv",
	Key:  "prop_75807e08dc1b6735",
	Deps: []registry.EntryLike{
		ContinuousAtInv,
		ContinuousAtId,
		ContinuousAtOn,
		ContinuousOnIffMap,
		continuous.IntoSubtopology,
		continuous.Compose,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀f:(A → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"continuous_map(T, complex_topology, f)",
			"∀x:A. x ∈ ⋃T ⇒ f(x) ≠ complex_of_real(&0)",
		},
		Conclusion: "continuous_map(T, complex_topology, λx:A. complex_inv(f(x)))",
	},
		"The reciprocal is continuous at every nonzero point (ContinuousAtInv, "+
			"ContinuousAtId), so on the punctured plane (ContinuousAtOn), which is continuity "+
			"from its subspace topology (ContinuousOnIffMap). f maps T into that subspace "+
			"(IntoSubtopology), and the composite is the reciprocal of f (continuous.Compose)."),
	Reading: "The nonvanishing is read on ⋃T only; off it complex_inv(f(x)) is " +
		"never asked about. With ContinuousComplexProduct and the adjugate it makes the " +
		"inverse of a continuous matrix with nowhere-vanishing determinant continuous.",
})}

// ContinuousComplexSum — a finite sum of continuous complex functions on a
// space is continuous.
var ContinuousComplexSum = continuousComplexSumThm{family.Add(registry.ProofEntry{
	Name: "ContinuousComplexSum",
	Key:  "prop_70411fa236799610",
	Deps: []registry.EntryLike{
		ContinuousComplexAdd,
		continuous.Constant,
		module.ModuleSumInsertMonoid,
		comm_ring.AddMonoidOn,
		complex_field.CommRingOn,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(B). ∀f:(B → A → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"finite(s)",
			"∀k:B. k ∈ s ⇒ continuous_map(T, complex_topology, f(k))",
		},
		Conclusion: "continuous_map(T, " +
			"    complex_topology, " +
			"    λx:A. module_sum(complex_add, complex_of_real(&0), s, λk:B. f(k, x)))",
	},
		"Induct on the finite set. The empty sum is the constant zero (continuous.Constant); inserting "+
			"an index adds one continuous term (ContinuousComplexAdd), the sum read at ℂ's additive monoid "+
			"(ModuleSumInsertMonoid at comm_ring.AddMonoidOn of complex_field.CommRingOn). finite(s) is "+
			"load-bearing: off a finite set the fold is an unspecified value that may vary with x."),
	Reading: "The form the matrix products of projection_bundle are read in: an entry " +
		"of a product of continuous matrices is such a sum over the indices below the size.",
})}

// ContinuousComplexProduct — a finite product of continuous complex
// functions on a space is continuous.
var ContinuousComplexProduct = continuousComplexProductThm{family.Add(registry.ProofEntry{
	Name: "ContinuousComplexProduct",
	Key:  "prop_cd3d96f5e53fb1c6",
	Deps: []registry.EntryLike{
		ContinuousComplexMul,
		continuous.Constant,
		module.ModuleSumInsertMonoid,
		comm_ring.MulMonoidOn,
		complex_field.CommRingOn,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(B). ∀f:(B → A → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"finite(s)",
			"∀k:B. k ∈ s ⇒ continuous_map(T, complex_topology, f(k))",
		},
		Conclusion: "continuous_map(T, " +
			"    complex_topology, " +
			"    λx:A. module_sum(complex_mul, complex_of_real(&1), s, λk:B. f(k, x)))",
	},
		"Induct on the finite set. The empty product is the constant one "+
			"(continuous.Constant); inserting an index multiplies by one continuous "+
			"factor (ContinuousComplexMul), the product read at ℂ's multiplicative monoid "+
			"(ModuleSumInsertMonoid at comm_ring.MulMonoidOn of complex_field.CommRingOn)."),
	Reading: "With ContinuousComplexSum it makes a determinant of continuous entries " +
		"continuous: the Leibniz sum runs over the finite symmetric group of products of entries.",
})}

// CoordinateLocallyCompact — ℂ^r is locally compact and Hausdorff.
var CoordinateLocallyCompact = coordinateLocallyCompactThm{family.Add(registry.ProofEntry{
	Name: "CoordinateLocallyCompact",
	Key:  "prop_8e9fa7aafd06ae8f",
	Deps: []registry.EntryLike{
		CoordinateRealHomeomorphism,
		euclidean_topology.OpenBoxOpen,
		euclidean_topology.BoxCompact,
		euclidean_topology.EuclideanHausdorff,
		continuous.HomeomorphismIffOpenBijection,
		continuous.ImageCompact,
		continuous.HomeomorphicHausdorff,
		euclidean.ComponentLeNorm,
	},
	Build: family.Card("∀r:num. "+
		"    locally_compact_space(complex_coordinate_topology(r)) ∧ "+
		"    hausdorff(complex_coordinate_topology(r))",
		"Carry ℝ^{2r} over by its homeomorphism onto ℂ^r (CoordinateRealHomeomorphism). About "+
			"the preimage w of a point, with B = ‖w‖ + 1, the open box with every bound −B and B is "+
			"open (OpenBoxOpen) and holds w, each coordinate being at most the norm "+
			"(ComponentLeNorm), and lies in the cube [−B, B] in every coordinate, which is compact "+
			"(BoxCompact); the homeomorphism is open and onto (HomeomorphismIffOpenBijection) and "+
			"keeps compact sets compact (ImageCompact), so their images are the open and the compact "+
			"set the definition asks for. Hausdorff by HomeomorphicHausdorff over EuclideanHausdorff."),
	Reading: "At r = 0 the carrier is the one point λi. 0, which is compact.",
})}

// CoordinateRealHomeomorphism — complex N-space is real 2N-space, the real
// parts in the first N coordinates and the imaginary parts in the next N.
var CoordinateRealHomeomorphism = coordinateRealHomeomorphismThm{family.Add(registry.ProofEntry{
	Name: "CoordinateRealHomeomorphism",
	Key:  "prop_c3d15ce69abfd6cc",
	Deps: []registry.EntryLike{
		CoordinateTopologyDef,
		ContinuousIffParts,
		product_topology.IndexedProductCarrier,
		product_topology.IndexedContinuousIff,
		product_topology.IndexedProjectionContinuous,
		euclidean_topology.EuclideanSpace,
		euclidean_topology.CoordinateContinuous,
		euclidean_topology.ContinuousIffCoordinates,
	},
	Build: family.Card(
		"∀N:num. "+
			"    homeomorphic_map(euclidean_topology(2 * N), "+
			"        complex_coordinate_topology(N), "+
			"        λw:(num → real). λi:num. "+
			"            COND(i < N, "+
			"                complex_of_real(w(i)) + complex_i * complex_of_real(w(N + i)), "+
			"                complex_of_real(&0)))",
		"The inverse sends z to the real vector with re(z(j)) at j < N, im(z(j − N)) at N ≤ j < 2N "+
			"and 0 beyond; the two undo each other on ℝ²ᴺ (euclidean_topology.EuclideanSpace) and on "+
			"the coordinate carrier (product_topology.IndexedProductCarrier). The map is continuous by "+
			"IndexedContinuousIff with ContinuousIffParts at each coordinate, whose parts are "+
			"coordinates of w (CoordinateContinuous); the inverse by ContinuousIffCoordinates, each "+
			"coordinate a part of a projection (IndexedProjectionContinuous, ContinuousIffParts)."),
	Reading: "The COND's else-branch matters: the indexed product's carrier pins every " +
		"coordinate at or beyond N to 0. At N = 0 both spaces are the single zero function.",
})}
