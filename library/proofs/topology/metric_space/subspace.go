// subspace.go — a subset of a metric space with the same distance, and
// the topology it carries: the subspace topology.

package metric_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// SubMetricSpace — a subset of a metric space, with the same distance,
// is a metric space: each axiom, asked of points of the subset, is asked
// of points of M.
var SubMetricSpace = subMetricSpaceThm{family.Add(registry.ProofEntry{
	Name: "SubMetricSpace",
	Key:  "prop_f1ef94f4f409f92e",
	Build: MetricSpace.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ M",
		},
		Conclusion: "metric_space(s, d)",
	},
		func(a *Argument, metric MetricSpaceFact[on.M], s *Expr[Set[A]], within Fact) {
			// The goal asks the three axioms of the points of s; the definition
			// is opened in the goal alone, so the structure fact stays whole.
			a.Do(Simp(Fwd(MetricSpace)), SplitConjAll(
				Case(
					"points of s at distance zero are equal",
					BySets(DistZeroIff.Read(metric), within)),
				Case(
					"the distance between points of s is symmetric",
					BySets(DistSym.Read(metric), within)),
				Case(
					"and obeys the triangle inequality",
					BySets(DistTriangle.Read(metric), within)),
			))
		}),
})}

// MetricTopologySubspace — a subset s of M, measured with the same
// distance, carries the subspace topology. A ball of s is the ball of M
// about the same point, cut to s. So an open set t of s is the trace of
// ⋃F, F the family of open sets of M whose trace lies in t: ⋃F is open,
// its trace lies in t, and a point of t has a ball of s inside t, whose
// ball of M is a member of F holding the point. Conversely the trace
// u ∩ s of an open set u of M is open in s: a point of it has a ball of M
// inside u, and the ball of s of the same radius is that ball cut to s.
var MetricTopologySubspace = metricTopologySubspaceThm{family.Add(registry.ProofEntry{
	Name: "MetricTopologySubspace",
	Key:  "prop_700a1989e364852c",
	Build: MetricSpace.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ M",
		},
		Conclusion: "metric_topology(s, d) = subtopology(metric_topology, s)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric MetricSpaceFact[on.M],
			s *Expr[Set[A]],
			within Fact,
		) {
			cut := a.Have(
				"a ball of s is the ball of M about the same point with the same radius, cut to s",
				"∀x:A. ∀r:real. ball(s, d, x, r) = ball(M, d, x, r) ∩ s",
				Unfold(BallDef),
				BySets(within))

			// Two families are equal when they have the same members, and a
			// member of the subspace topology is the trace of an open set.
			a.Do(Simp(Fwd(set_basic.Extension.Inst[Set[A]]()), Fwd(topological_space.OpenInSubtopology)))
			t := a.FixAs[Set[A]]("t")
			a.Iff()

			a.Forward(
				"an open set of s is the trace of the union of the open sets of M whose trace lies in it",
				func(b *Argument, open Fact) {
					tOpen := b.Conjuncts(
						b.Have(
							"what it is for t to be open in s",
							"t ⊆ s ∧ ∀x:A. x ∈ t ⇒ ∃r:real. &0 < r ∧ ball(s, d, x, r) ⊆ t",
							Simp(Rev(OpenIff)),
							By(open)),
						"t lies in s",
						"each point of t has a ball of s about it inside t")
					F, inF := b.LetAs[Set[Set[A]]]("F", "{v:set(A) | v ∈ metric_topology(M, d) ∧ v ∩ s ⊆ t}")

					covered := b.Have(
						"each point of t lies in a member of F: the ball of M whose trace is its ball of s inside t",
						"∀y:A. y ∈ t ⇒ y ∈ ⋃F",
						Derive(func(c *Argument) {
							y := c.FixAs[A]("y")
							inT := c.Assume()
							r0, radius := c.ObtainAs[Real](
								"t is open in s, so a ball of s about y lies in t",
								"∃r:real. &0 < r ∧ ball(s, d, y, r) ⊆ t",
								By(tOpen[1].At(y), inT))
							about := c.Conjuncts(
								radius,
								"r₀ is positive",
								"the ball of s of radius r₀ lies in t")
							inM := c.Have(
								"y is a point of M, as t lies in s and s in M",
								"y ∈ M",
								BySets(inT, tOpen[0], within))
							yM := c.MemberOf[on.M](y, inM)
							ball := c.TermAs[Set[A]]("ball(M, d, y, r₀)")
							ballOpen := c.Have(
								"the ball of M about y of radius r₀ is open",
								"ball(M, d, y, r₀) ∈ metric_topology(M, d)",
								By(BallOpen.Read(metric).At(yM, r0)))
							ballTrace := c.Have(
								"its trace on s is the ball of s, which lies in t",
								"ball(M, d, y, r₀) ∩ s ⊆ t",
								BySets(cut.At(y, r0), about[1]))
							member := c.Have(
								"so it is a member of F",
								"ball(M, d, y, r₀) ∈ F",
								BySets(inF, ballOpen, ballTrace))
							centre := c.Have(
								"and it holds its centre y",
								"y ∈ ball(M, d, y, r₀)",
								By(CentreInBall.Read(metric).At(yM, r0), about[0]))
							inside := c.Have(
								"so it lies in the union of F",
								"ball(M, d, y, r₀) ⊆ ⋃F",
								By(set_order.MemberSubsetUnions.At(F, ball), member))
							c.Show(
								"and y, its centre, lies in the union of F",
								BySets(centre, inside))
						}))
					inTrace := b.Have(
						"so t lies in the trace of ⋃F on s, t lying in s",
						"t ⊆ ⋃F ∩ s",
						BySets(covered, tOpen[0]))
					traceIn := b.Have(
						"and the trace of ⋃F on s lies in t, as the trace of each member does",
						"⋃F ∩ s ⊆ t",
						BySets(inF))
					familyOpen := b.Have(
						"every member of F is open in M",
						"F ⊆ metric_topology(M, d)",
						BySets(inF))

					b.Take(b.TermAs[Set[A]]("⋃F"))
					b.Do(SplitConj(
						Case(
							"t is the trace of ⋃F, each lying in the other",
							By(set_order.SubsetAntisym.At(t, b.TermAs[Set[A]]("⋃F ∩ s")), inTrace, traceIn)),
						Case(
							"and ⋃F is open in M, a union of open sets",
							By(topological_space.UnionsOpen, MetricTopology.At(M, d), familyOpen)),
					))
				})

			a.Backward(
				"the trace of an open set of M is open in s",
				func(b *Argument, trace Fact) {
					_, traced := b.Unpack(trace, "u")
					parts := b.Conjuncts(
						traced,
						"t is the trace of u on s",
						"u is open in M")
					b.Do(parts[0].Rw(), Simp(Fwd(OpenIff)), SplitConj(
						Case(
							"the trace lies in s",
							BySets()),
						Case(
							"a point x of the trace keeps in s the radius u gives it in M",
							Derive(func(c *Argument) {
								x := c.FixAs[A]("x")
								inTrace := c.Assume()
								inU := c.Have(
									"x lies in u",
									"x ∈ u",
									BySets(inTrace))
								r0, radius := c.ObtainAs[Real](
									"u is open in M, so a ball of M about x lies in u",
									"∃r:real. &0 < r ∧ ball(M, d, x, r) ⊆ u",
									By(parts[1], inU, OpenIff),
									Named("r₀"))
								about := c.Conjuncts(
									radius,
									"r₀ is positive",
									"the ball of M of radius r₀ lies in u")
								c.Take(r0)
								c.Do(SplitConj(
									Case(
										"the radius is positive",
										By(about[0])),
									Case(
										"and the ball of s of radius r₀, the ball of M cut to s, lies in the trace",
										BySets(cut.At(x, r0), about[1])),
								))
							})),
					))
				})
		}),
})}
