// euclidean_topology.go — ℝⁿ as a topological space: the open sets form
// a topology whose points are the n-vectors, a set is open when each of
// its points has a radius about it inside the set, the balls are open,
// and two distinct n-vectors lie in disjoint open sets. Each is the metric
// chapter's theorem read at the n-vectors and the distance; the last two
// read the distance's axioms, through the instance
// euclidean.EuclideanMetric.

package euclidean_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/countability"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/registry"
)

// EuclideanTopology — the open sets of ℝⁿ form a topology: the metric
// topology of any distance does.
var EuclideanTopology = euclideanTopologyThm{family.Add(registry.ProofEntry{
	Name: "EuclideanTopology",
	Key:  "prop_2da2309986ca2889",
	Build: family.Theorem("∀n:num. is_topology(euclidean_topology(n))",
		func(a *Argument, n *Expr[Nat]) {
			a.Show(
				"the metric topology of any distance is a topology",
				Unfold(EuclideanTopologyDef),
				By(metric_space.MetricTopology))
		}),
})}

// EuclideanSpace — the points of ℝⁿ are the n-vectors: the space of a
// metric topology is its carrier.
var EuclideanSpace = euclideanSpaceThm{family.Add(registry.ProofEntry{
	Name: "EuclideanSpace",
	Key:  "prop_f6f6431aae914950",
	Build: family.Theorem("∀n:num. ⋃euclidean_topology(n) = {u:(num → real) | vec⟨n⟩(u)}",
		func(a *Argument, n *Expr[Nat]) {
			a.Show(
				"the space of a metric topology is its carrier",
				Unfold(EuclideanTopologyDef),
				By(metric_space.MetricTopologySpace))
		}),
})}

// EuclideanSecondCountable — every finite-dimensional Euclidean space
// has a countable base, including the one-point space ℝ⁰.
var EuclideanSecondCountable = euclideanSecondCountableThm{family.Add(registry.ProofEntry{
	Name: "EuclideanSecondCountable",
	Key:  "prop_37d25f9341b1f93",
	Deps: []registry.EntryLike{
		BoxCompact,
		countability.CompactImpLindelof,
		countability.LindelofCountableCover,
		metric_space.MetricLindelofIffSecondCountable,
		euclidean.EuclideanMetric,
	},
	Build: family.Card("∀n:num. second_countable_space(euclidean_topology(n))",
		"The boxes [-k,k]ⁿ for natural k cover ℝⁿ by the Archimedean property. Each is compact "+
			"(BoxCompact), hence its subspace is Lindelöf (countability.CompactImpLindelof); "+
			"countability.LindelofCountableCover makes ℝⁿ Lindelöf, and "+
			"metric_space.MetricLindelofIffSecondCountable at euclidean.EuclideanMetric gives a "+
			"countable base. The zero-dimensional box is the singleton zero vector."),
})}

// OpenIff — a set of n-vectors is open exactly when each of its points
// has a radius about it inside the set: the metric chapter's reading of
// openness, with the ball about x written as the n-vectors within r of
// it.
var OpenIff = openIffThm{family.Add(registry.ProofEntry{
	Name: "OpenIff",
	Key:  "prop_5f1b957bec807428",
	Build: family.Theorem("∀n:num. ∀u:set(num → real). "+
		"    u ∈ euclidean_topology(n) ⇔ "+
		"    (∀x:(num → real). x ∈ u ⇒ vec⟨n⟩(x)) ∧ "+
		"    (∀x:(num → real). "+
		"        x ∈ u ⇒ ∃r:real. &0 < r ∧ ∀y:(num → real). vec⟨n⟩(y) ∧ dist⟨n⟩(x, y) < r ⇒ y ∈ u)",
		func(a *Argument, n *Expr[Nat], u *Expr[Set[Fun[Nat, Real]]]) {
			a.Show(
				"openness in the metric topology, the ball unfolded",
				Unfold(EuclideanTopologyDef),
				Simp(Fwd(metric_space.OpenIff.Inst[Fun[Nat, Real]]())),
				Unfold(metric_space.BallDef),
				BySets())
		}),
})}

// BallOpen — the n-vectors within r of an n-vector c form an open set:
// the metric chapter's BallOpen at the instance.
var BallOpen = ballOpenThm{family.Add(registry.ProofEntry{
	Name: "BallOpen",
	Key:  "prop_2f44f2e753cef342",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀c:(num → real). ∀r:real.",
		Hypotheses: []string{
			"vec⟨n⟩(c)",
		},
		Conclusion: "{y:num → real | vec⟨n⟩(y) ∧ dist⟨n⟩(c, y) < r} ∈ euclidean_topology(n)",
	},
		func(a *Argument, n *Expr[Nat], c *Expr[Fun[Nat, Real]], r *Expr[Real], centre Fact) {
			// Open in ℝⁿ is open in the metric topology of the n-vectors.
			a.Do(Unfold(EuclideanTopologyDef))
			ball := a.Have(
				"the set is the ball of the metric about c",
				"{y:(num → real) | vec⟨n⟩(y) ∧ dist⟨n⟩(c, y) < r} = "+
					"ball({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩, c, r)",
				Unfold(metric_space.BallDef),
				BySets())
			a.Do(ball.Rw())
			inCarrier := a.Have(
				"c, an n-vector, is a point of the carrier",
				"c ∈ {u:(num → real) | vec⟨n⟩(u)}",
				BySets(centre))
			a.Show(
				"and a ball about a point of the carrier is open, the n-vectors being a metric space",
				By(metric_space.BallOpen, euclidean.EuclideanMetric.At(n), inCarrier))
		}),
})}

// EuclideanHausdorff — two distinct n-vectors lie in disjoint open sets:
// the open sets of a metric space separate points, and the n-vectors
// are one.
var EuclideanHausdorff = euclideanHausdorffThm{family.Add(registry.ProofEntry{
	Name: "EuclideanHausdorff",
	Key:  "prop_916e5b84db97d056",
	Build: family.Theorem("∀n:num. hausdorff(euclidean_topology(n))",
		func(a *Argument, n *Expr[Nat]) {
			a.Show(
				"the metric topology of a metric space is Hausdorff",
				Unfold(EuclideanTopologyDef),
				By(metric_space.MetricHausdorff, euclidean.EuclideanMetric.At(n)))
		}),
})}
