// simplex.go — the standard simplex as a space: compact and convex; the
// coface and the codegeneracy carry the standard simplices into one
// another and are continuous; the image of the i-th coface is the face
// where coordinate i vanishes; and the simplex retracts onto each of its
// horns, the union of the faces but one.

package euclidean_simplex

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/vector/convex"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// SimplexCompact — the standard simplex is compact.
var SimplexCompact = simplexCompactThm{family.Add(registry.ProofEntry{
	Name:    "SimplexCompact",
	Key:     "prop_e084c45ba98dcd94",
	Reading: "Δⁿ lies in ℝⁿ⁺¹ through vec⟨n + 1⟩ and every coordinate is in ⟦0, 1⟧. Δ⁰ = {e₀}.",
	Deps: []registry.EntryLike{
		EuclideanSimplexDef,
		euclidean_topology.HeineBorel,
		euclidean_topology.CoordinateContinuous,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num.",
		Conclusion: "compact_in(euclidean_topology(n + 1), euclidean_simplex(n))",
	},
		"closed, cut out of ℝⁿ⁺¹ by finitely many inequalities and one equation "+
			"in continuous functions of the coordinates (CoordinateContinuous), and "+
			"bounded, every coordinate lying in ⟦0, 1⟧; HeineBorel"),
})}

// SimplexConvex — the standard simplex is convex.
var SimplexConvex = simplexConvexThm{family.Add(registry.ProofEntry{
	Name:    "SimplexConvex",
	Key:     "prop_a4dc95998e3212dc",
	Reading: "Convexity reads no dimension; Δ⁰ is one point.",
	Deps:    []registry.EntryLike{EuclideanSimplexDef, convex.ConvexDef},
	Build: family.Card(Statement{
		Binders:    "∀n:num.",
		Conclusion: "convex(euclidean_simplex(n))",
	},
		"a weighted average of two points keeps the coordinates past n zero and the "+
			"others nonnegative, and its coordinates sum to the same average of 1 and 1"),
})}

// CofaceSimplex — every coface carries Δⁿ into Δⁿ⁺¹.
var CofaceSimplex = cofaceSimplexThm{family.Add(registry.ProofEntry{
	Name: "CofaceSimplex",
	Key:  "prop_d6e205f5157eb4a",
	Reading: "No bound on i: past n + 1 the coface inserts its zero in the " +
		"padding and leaves t, already a point of Δⁿ⁺¹ with last coordinate 0.",
	Deps: []registry.EntryLike{EuclideanSimplexDef, EuclideanCofaceDef},
	Build: family.Card(Statement{
		Binders: "∀n i:num. ∀t:(num → real).",
		Hypotheses: []string{
			"t ∈ euclidean_simplex(n)",
		},
		Conclusion: "euclidean_coface(i, t) ∈ euclidean_simplex(n + 1)",
	},
		"the inserted coordinate is 0 and the others are those of t moved, so they are nonnegative, "+
			"vanish past n + 1, and sum to the sum of t's; for i > n + 1 the zero is inserted in the "+
			"padding and the coface leaves t as it is, a point of Δⁿ⁺¹ with last coordinate 0"),
})}

// CofaceImage — the image of Δⁿ under the i-th coface is the face of Δⁿ⁺¹
// where coordinate i vanishes.
var CofaceImage = cofaceImageThm{family.Add(registry.ProofEntry{
	Name: "CofaceImage",
	Key:  "prop_c9504ebbf5f66c14",
	Reading: "i ≤ n + 1 is load-bearing: past it the left side is Δⁿ " +
		"while the right side is all of Δⁿ⁺¹, e_(n+1) lying only in the second.",
	Deps: []registry.EntryLike{
		CofaceSimplex,
		EuclideanSimplexDef,
		EuclideanCofaceDef,
		EuclideanCodegeneracyDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n i:num.",
		Hypotheses: []string{
			"i ≤ n + 1",
		},
		Conclusion: "image(euclidean_coface(i), euclidean_simplex(n)) = " +
			"{t:(num → real) | t ∈ euclidean_simplex(n + 1) ∧ t(i) = &0}",
	},
		"one inclusion is CofaceSimplex, the inserted coordinate being 0; a point "+
			"of the face is the coface of itself with coordinate i deleted, which is "+
			"a point of Δⁿ, the deleted coordinate contributing nothing to the sum"),
})}

// CofaceContinuous — the coface is continuous from ℝⁿ⁺¹ to ℝⁿ⁺².
var CofaceContinuous = cofaceContinuousThm{family.Add(registry.ProofEntry{
	Name:    "CofaceContinuous",
	Key:     "prop_c78656c817e5f36e",
	Reading: "No bound on i: past n + 1 the coface is the inclusion of ℝⁿ⁺¹ in ℝⁿ⁺².",
	Deps: []registry.EntryLike{
		EuclideanCofaceDef,
		euclidean_topology.ContinuousIffCoordinates,
		euclidean_topology.CoordinateContinuous,
		continuous.Constant,
	},
	Build: family.Card(Statement{
		Binders: "∀n i:num.",
		Conclusion: "continuous_map(euclidean_topology(n + 1), " +
			"    euclidean_topology(n + 2), " +
			"    euclidean_coface(i))",
	},
		"each coordinate of the image is a coordinate of the argument or 0 (ContinuousIffCoordinates, "+
			"CoordinateContinuous, Constant); an (n + 1)-vector goes to an (n + 2)-vector, the coordinate "+
			"shifted up being at most n + 1 when i ≤ n + 1, and the vector itself when i > n + 1"),
})}

// CodegeneracySimplex — the i-th codegeneracy carries Δⁿ⁺¹ into Δⁿ for
// i ≤ n.
var CodegeneracySimplex = codegeneracySimplexThm{family.Add(registry.ProofEntry{
	Name:    "CodegeneracySimplex",
	Key:     "prop_4cb6e83109cede81",
	Reading: "i ≤ n is load-bearing: σ^(n+1) sends e_(n+1) to itself, not a point of Δⁿ.",
	Deps:    []registry.EntryLike{EuclideanSimplexDef, EuclideanCodegeneracyDef},
	Build: family.Card(Statement{
		Binders: "∀n i:num. ∀t:(num → real).",
		Hypotheses: []string{
			"i ≤ n",
			"t ∈ euclidean_simplex(n + 1)",
		},
		Conclusion: "euclidean_codegeneracy(i, t) ∈ euclidean_simplex(n)",
	},
		"the merged coordinate is a sum of two nonnegative ones, the others are t's moved "+
			"down, past n they are t's past n + 1, which vanish, and the sum is unchanged"),
})}

// CodegeneracyContinuous — the i-th codegeneracy is continuous from ℝⁿ⁺²
// to ℝⁿ⁺¹ for i ≤ n.
var CodegeneracyContinuous = codegeneracyContinuousThm{family.Add(registry.ProofEntry{
	Name:    "CodegeneracyContinuous",
	Key:     "prop_9068409986cb3739",
	Reading: "i ≤ n is load-bearing: σ^(n+1) keeps e_(n+1) of ℝⁿ⁺², which is outside ℝⁿ⁺¹.",
	Deps: []registry.EntryLike{
		EuclideanCodegeneracyDef,
		euclidean_topology.ContinuousIffCoordinates,
		euclidean_topology.CoordinateContinuous,
	},
	Build: family.Card(Statement{
		Binders: "∀n i:num.",
		Hypotheses: []string{
			"i ≤ n",
		},
		Conclusion: "continuous_map(euclidean_topology(n + 2), " +
			"    euclidean_topology(n + 1), " +
			"    euclidean_codegeneracy(i))",
	},
		"each coordinate of the image is a coordinate of the argument or the sum of "+
			"two (ContinuousIffCoordinates, CoordinateContinuous); with i ≤ n, coordinate "+
			"n + 1 of the image is coordinate n + 2 of the argument, which vanishes on ℝⁿ⁺²"),
})}

// HornRetraction — the simplex Δⁿ⁺¹ retracts onto its k-th horn, the
// points where some coordinate other than the k-th vanishes.
var HornRetraction = hornRetractionThm{family.Add(registry.ProofEntry{
	Name: "HornRetraction",
	Key:  "prop_2f0426a4be859caf",
	Reading: "k ≤ n + 1 is load-bearing: past it the set is the whole boundary of Δⁿ⁺¹, no retract " +
		"— at n = 0 two points of the connected Δ¹. At n = 0 the horn is the one vertex e_(1−k).",
	Deps: []registry.EntryLike{
		EuclideanSimplexDef,
		continuous.RetractOfDef,
		euclidean_topology.ContinuousIffCoordinates,
		euclidean_topology.CoordinateContinuous,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num.",
		Hypotheses: []string{
			"k ≤ n + 1",
		},
		Conclusion: "retract_of(subtopology(euclidean_topology(n + 2), euclidean_simplex(n + 1)), " +
			"    {t:(num → real) | t ∈ euclidean_simplex(n + 1) ∧ ∃i:num. i ≤ n + 1 ∧ i ≠ k ∧ t(i) = &0})",
	},
		"with m(t) the least of the n + 1 coordinates tᵢ, i ≤ n + 1 and i ≠ k, the "+
			"retraction subtracts m(t) from each of them and adds (n + 1) · m(t) to t_k: the "+
			"coordinates stay nonnegative and keep their sum, the least of the others becomes "+
			"0, a point of the horn has m(t) = 0 and stays put, and the map is continuous, a "+
			"minimum of finitely many coordinates being continuous (ContinuousIffCoordinates)"),
})}
