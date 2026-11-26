package polish_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/countability"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ClosedSubspacePolish — Restrict a compatible complete metric and a countable base to the closed subset.
var ClosedSubspacePolish = closedSubspacePolishThm{family.Add(registry.ProofEntry{
	Name: "ClosedSubspacePolish",
	Key:  "prop_78ba21bf3ecc0ad7",
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀X:set(A).",
		Hypotheses: []string{
			"polish_space(T)",
			"closed_in(T, X)",
		},
		Conclusion: "polish_space(subtopology(T, X))",
	},
		"Restrict a compatible complete metric and a countable base to the closed "+
			"subset. The metric restricts to a metric (SubMetricSpace) whose topology is the "+
			"subspace topology (MetricTopologySubspace) and which stays complete on a closed "+
			"set (ClosedComplete); the subspace is a topology (SubtopologyTopology) whose "+
			"carrier is the closed subset (SubtopologySpace). A metric topology is separable "+
			"exactly when it is second countable (MetricSeparableIffSecondCountable), and a "+
			"subspace inherits second countability (SecondCountableSubtopology)."),
	Deps: []registry.EntryLike{
		metric_space.SubMetricSpace,
		metric_space.MetricTopologySubspace,
		complete_metric.ClosedComplete,
		topological_space.SubtopologyTopology,
		topological_space.SubtopologySpace,
		metric_space.MetricSeparableIffSecondCountable,
		countability.SecondCountableSubtopology,
	},
})}

// CountableDiscretePolish — Use the zero-one metric
var CountableDiscretePolish = countableDiscretePolishThm{family.Add(registry.ProofEntry{
	Name: "CountableDiscretePolish",
	Key:  "prop_49ae7c5cdd7e8e26",
	Build: family.Card(Statement{
		Binders: "∀X:set(A).",
		Hypotheses: []string{
			"countable(X)",
		},
		Conclusion: "polish_space({u:set(A) | u ⊆ X})",
	},
		"Use the zero-one metric. Every subset of the countable discrete carrier is open. The subsets of "+
			"the carrier are a topology (Discrete) on it (DiscreteSpace), and the carrier, closed in its own "+
			"topology (SpaceClosed), is its own closure (ClosureOfClosed): a countable dense set. A ball of "+
			"radius one about a point is that point, so every subset of the carrier is open for the zero-one "+
			"metric (OpenIff); a Cauchy sequence is eventually constant and converges to its constant value."),
	Deps: []registry.EntryLike{
		topological_space.Discrete,
		topological_space.DiscreteSpace,
		topological_space.SpaceClosed,
		topological_space.ClosureOfClosed,
		metric_space.OpenIff,
	},
})}

// FiniteCoordinateContinuous — Finite dependence of each output coordinate gives continuity between subspaces of normalized discrete products.
var FiniteCoordinateContinuous = finiteCoordinateContinuousThm{family.Add(registry.ProofEntry{
	Name: "FiniteCoordinateContinuous",
	Key:  "prop_9730062c88918083",
	Build: family.Card(Statement{
		Binders: "∀J:set(I). " +
			"∀K:set(D). " +
			"∀z:(I → A). " +
			"∀w:(D → B). " +
			"∀X:(I → set(A)). " +
			"∀Y:(D → set(B)). " +
			"∀C:set(I → A). " +
			"∀E:set(D → B). " +
			"∀f:((I → A) → D → B).",
		Hypotheses: []string{
			"C ⊆ indexed_functions(J, z, X)",
			"E ⊆ indexed_functions(K, w, Y)",
			"image(f, C) ⊆ E",
			"∀j:D. j ∈ K ⇒ finite_coordinate_dependence(J, C, λx:(I → A). f(x, j))",
		},
		Conclusion: "continuous_map(subtopology(indexed_discrete_topology(J, z, X), C), " +
			"    subtopology(indexed_discrete_topology(K, w, Y), E), " +
			"    f)",
	},
		"For each output coordinate, a finite cylinder fixing its determining input coordinates lies "+
			"inside the inverse image of its value. These cylinders prove continuity into the generated "+
			"product topology; the stated image containment permits restriction to the target subspace."),
	Deps: []registry.EntryLike{
		product_topology.IndexedProductCarrier,
		continuous.ContinuousIntoGenerated,
		continuous.IntoSubtopology,
		topological_space.GeneratedOnTopology,
		topological_space.GeneratedOnContains,
		topological_space.IntersOpen,
		topological_space.OpenPointwise,
		topological_space.TraceOpen,
	},
	Reading: "No countability or group structure is required. Coordinate carriers may vary, " +
		"and both spaces may be subspaces. Empty determining supports give constant coordinates " +
		"on C, using C itself as the cylinder. Image containment includes inactive-coordinate " +
		"normalization and remains necessary when the target index set is empty.",
})}

// FiniteCoordinateProductContinuous — a map between subspaces of indexed
// products whose active output coordinates each read a fixed finite set
// of input coordinates through a continuous function is continuous.
var FiniteCoordinateProductContinuous = finiteCoordinateProductContinuousThm{family.Add(registry.ProofEntry{
	Name: "FiniteCoordinateProductContinuous",
	Key:  "prop_70a2320be4ef7b8",
	Build: family.Card(
		Statement{
			Binders: "∀J:set(I). " +
				"∀z:(I → A). " +
				"∀T:(I → set(set(A))). " +
				"∀K:set(D). " +
				"∀w:(D → B). " +
				"∀U:(D → set(set(B))). " +
				"∀C:set(I → A). " +
				"∀E:set(D → B). " +
				"∀f:((I → A) → D → B). " +
				"∀F:(D → set(I)). " +
				"∀h:(D → (I → A) → B).",
			Hypotheses: []string{
				"∀i:I. i ∈ J ⇒ is_topology(T(i))",
				"∀j:D. j ∈ K ⇒ is_topology(U(j))",
				"C ⊆ indexed_functions(J, z, λi:I. ⋃T(i))",
				"E ⊆ indexed_functions(K, w, λj:D. ⋃U(j))",
				"image(f, C) ⊆ E",
				"∀j:D. " +
					"    j ∈ K ⇒ " +
					"    finite(F(j)) ∧ F(j) ⊆ J ∧ continuous_map(indexed_product_topology(F(j), z, T), U(j), h(j))",
				"∀x:(I → A). ∀j:D. x ∈ C ∧ j ∈ K ⇒ f(x, j) = h(j, λi:I. COND(i ∈ F(j), x(i), z(i)))",
			},
			Conclusion: "continuous_map(subtopology(indexed_product_topology(J, z, T), C), " +
				"    subtopology(indexed_product_topology(K, w, U), E), " +
				"    f)",
		},
		"Coordinate projection onto a fixed finite set is continuous. Compose with the given continuous "+
			"coordinate function, use the cylinder basis, and restrict to the specified carriers."),
	Deps: []registry.EntryLike{product_topology.IndexedProductCarrier},
	Reading: "Fixed finite dependence alone is insufficient for nondiscrete factors; " +
		"continuity of each finite-coordinate function is an explicit hypothesis.",
})}

// LusinSouslin — A continuous map of Polish spaces carries a Borel set on which it is injective to a Borel set.
var LusinSouslin = lusinSouslinThm{family.Add(registry.ProofEntry{
	Name: "LusinSouslin",
	Key:  "prop_fd14b9eb17da70e8",
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀U:set(set(B)). ∀f:(A → B). ∀s:set(A).",
		Hypotheses: []string{
			"polish_space(T)",
			"polish_space(U)",
			"continuous_map(T, U, f)",
			"s ∈ borel_sets(T)",
			"injective_on(s, f)",
		},
		Conclusion: "image(f, s) ∈ borel_sets(U)",
	},
		"Kechris, Classical Descriptive Set Theory, Theorem 15.1. The topology refines to a Polish "+
			"one with the same Borel sets in which the set is open and closed: a closed set becomes open "+
			"in the sum of itself and its complement, both Polish, and countably many refinements combine "+
			"as a closed diagonal of their product (CountableProductPolish, ClosedSubspacePolish). A "+
			"Polish space is the injective continuous image of a closed set of the Baire space, by a "+
			"scheme of sets of vanishing diameter, each a countable union of closed sets, the disjoint "+
			"union of its children and holding their closures; a branch of non-empty pieces has one "+
			"point, the closures along it being nested closed sets (CantorIntersection). So the set may "+
			"be taken a closed set of the Baire space, which is Polish (CountableDiscretePolish, "+
			"CountableProductPolish). The images of its pieces over the finite sequences of one length "+
			"are pairwise disjoint analytic sets, which Lusin's separation theorem encloses in pairwise "+
			"disjoint Borel sets; cut down to the closures of those images and nested along extension, "+
			"these have the image as the intersection over the lengths of their unions."),
	Deps: []registry.EntryLike{
		CountableProductPolish,
		ClosedSubspacePolish,
		complete_metric.CantorIntersection,
		CountableDiscretePolish,
	},
	Reading: "Injectivity is asked on the Borel set alone, not on the space, and is " +
		"load-bearing: the continuous image of a Polish space is analytic and need not " +
		"be Borel. The source must be Polish: a set of reals that is not Borel is Borel " +
		"in its own subspace topology, and its inclusion in the line is continuous and " +
		"injective. A Borel set lies inside the carrier, so the values of the map off " +
		"the carrier do not enter. The empty set has the empty image, which is Borel.",
})}

var CountableDiscreteStandardBorel = countableDiscreteStandardBorelThm{family.Add(registry.ProofEntry{
	Name: "CountableDiscreteStandardBorel",
	Key:  "prop_5d417a62748a5645",
	Reading: "countable(V) is load-bearing: the discrete topology on an uncountable set is not " +
		"separable. A finite carrier with all its subsets, the observed nodes' carriers, is an instance.",
	Deps: []registry.EntryLike{CountableDiscretePolish},
	Build: family.Card(Statement{
		Binders:    "∀V:set(A).",
		Hypotheses: []string{"countable(V)"},
		Conclusion: "standard_borel_on(V, {s:set(A) | s ⊆ V})",
	},
		"A countable set with all its subsets is standard Borel: the "+
			"discrete topology on it is Polish (CountableDiscretePolish), its "+
			"union is V, and its Borel sets are all the subsets, each being open."),
})}

var IndexedProductStandardBorel = indexedProductStandardBorelThm{family.Add(registry.ProofEntry{
	Name: "IndexedProductStandardBorel",
	Key:  "prop_2a5c466e973544d3",
	Reading: "countable(J) is load-bearing: the Borel σ-algebra of an " +
		"uncountable product is larger than the product σ-algebra. Off J " +
		"the functions take z's values, so an empty J gives the point {z}.",
	Deps: []registry.EntryLike{CountableProductPolish},
	Build: family.Card(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀D:(I → set(A)). ∀T:(I → set(set(A))).",
		Hypotheses: []string{
			"countable(J)",
			"∀i:I. i ∈ J ⇒ standard_borel_on(D(i), T(i))",
		},
		Conclusion: "standard_borel_on(indexed_functions(J, z, D), indexed_product_sigma(J, z, D, T))",
	},
		"A countable product of standard Borel spaces is standard Borel for the product "+
			"σ-algebra: choose for each factor a Polish topology with those Borel sets; their product "+
			"topology is Polish (CountableProductPolish) on the indexed functions, and since each "+
			"factor is second countable the Borel sets of a countable product are generated by the "+
			"coordinate preimages of the factors' open sets, which generate the product σ-algebra."),
})}

var RealStandardBorel = realStandardBorelThm{family.Add(registry.ProofEntry{
	Name: "RealStandardBorel",
	Key:  "prop_751089b2b0ea9878",
	Deps: []registry.EntryLike{real_topology.RealTopologyMetric, real_topology.RealComplete},
	Build: family.Card(Statement{
		Conclusion: "standard_borel_on(𝕌⟨A:real⟩, borel_sets(real_topology))",
	},
		"The line with its Borel sets is standard Borel: its topology is the metric "+
			"topology of the distance |x − y| (RealTopologyMetric), complete (RealComplete), "+
			"with the rationals dense, so it is Polish and its union is the line."),
})}
