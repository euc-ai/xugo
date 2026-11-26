// topology.go — the open sets a distance determines: that they form a
// topology whose space is the carrier, that the balls are open and the
// closed balls closed, and that two distinct points lie in disjoint open
// sets. Most of it asks nothing of the distance; the triangle inequality
// is what makes a ball open and a closed ball closed, and what keeps the
// balls about two points apart.

package metric_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The open sets
// ---------------------------------------------------------------------------

// OpenIff — a subset of M is open exactly when each of its points has a
// ball about it inside the set: the family's definition read as
// membership in the family. It is the form every member reads openness
// in, and it asks nothing of the distance, so the carrier and the
// distance are spelled.
var OpenIff = openIffThm{family.Add(registry.ProofEntry{
	Name: "OpenIff",
	Key:  "prop_90954ef020c51a59",
	Build: family.Theorem("∀M:set(A). ∀d:(A → A → real). ∀u:set(A). "+
		"    u ∈ metric_topology(M, d) ⇔ u ⊆ M ∧ ∀x:A. x ∈ u ⇒ ∃r:real. &0 < r ∧ ball(M, d, x, r) ⊆ u",
		func(a *Argument, M *Expr[Set[A]], d *Expr[Fun2[A, A, Real]], u *Expr[Set[A]]) {
			a.Show(
				"membership in the family is the condition it is built from",
				Unfold(MetricTopologyDef),
				BySets())
		}),
})}

// MetricTopology — the open sets form a topology, whatever the
// distance. Two open sets meet in an open set: a point of both has a
// ball about it inside each, and the ball of the smaller radius lies in
// both. A family of open sets unites to an open set: a point of the
// union lies in some member, and the ball that member gives it lies in
// the union. Neither step reads an axiom — the balls about one point are
// nested by their radii whatever d is — so the carrier and the distance
// are spelled. The instance is parametric in M and d, and its cases
// cite laws AT M and d — the door's parametric form binds the prefix by
// name for a case's text but hands no Go value to a Case — so the
// door's body is written out here, with the components as typed
// binders: the predicate unfolded, one case per axiom.
var MetricTopology = metricTopologyThm{family.Add(registry.ProofEntry{
	Name: "MetricTopology",
	Key:  "prop_a5eaba268fd84f9b",
	Build: family.Theorem("∀M:set(A). ∀d:(A → A → real). is_topology(metric_topology(M, d))",
		func(a *Argument, M *Expr[Set[A]], d *Expr[Fun2[A, A, Real]]) {
			a.Do(Unfold(topological_space.IsTopology), SplitConjAll(
				Case(
					"two open sets meet in an open set",
					Simp(Fwd(OpenIff)),
					Derive(func(b *Argument) {
						b.FixAs[Set[A]]("u")
						b.FixAs[Set[A]]("v")
						open := b.Conjuncts(
							b.Assume(),
							"u lies in M",
							"each point of u has a ball about it inside u",
							"v lies in M",
							"each point of v has a ball about it inside v")
						b.Do(SplitConj(
							Case(
								"the meet lies in M, as u does",
								BySets(open[0])),
							Case(
								"a point of the meet has a ball about it inside both",
								Derive(func(c *Argument) {
									x := c.FixAs[A]("x")
									inBoth := c.Assume()
									inU := c.Have(
										"x lies in u",
										"x ∈ u",
										BySets(inBoth))
									inV := c.Have(
										"and in v",
										"x ∈ v",
										BySets(inBoth))
									r0, ballU := c.ObtainAs[Real](
										"u, being open, gives x a ball of radius r₀ inside u",
										"∃r:real. &0 < r ∧ ball(M, d, x, r) ⊆ u",
										By(open[1].At(x), inU))
									r1, ballV := c.ObtainAs[Real](
										"and v gives it a ball of radius r₁ inside v",
										"∃r:real. &0 < r ∧ ball(M, d, x, r) ⊆ v",
										By(open[3].At(x), inV))
									aboutU := c.Conjuncts(
										ballU,
										"r₀ is positive",
										"the ball of radius r₀ lies in u")
									aboutV := c.Conjuncts(
										ballV,
										"r₁ is positive",
										"the ball of radius r₁ lies in v")
									smaller := c.TermAs[Real]("min(r₀, r₁)")
									below := c.Have(
										"the smaller radius is at most each",
										"min(r₀, r₁) ≤ r₀ ∧ min(r₀, r₁) ≤ r₁",
										By(real_sup_inf.MinLowerBound.At(r0, r1)))
									toU := c.Have(
										"so its ball lies in the ball of radius r₀",
										"ball(M, d, x, min(r₀, r₁)) ⊆ ball(M, d, x, r₀)",
										By(BallConcentric.At(M, d, x, smaller, r0), below))
									toV := c.Have(
										"and in the ball of radius r₁",
										"ball(M, d, x, min(r₀, r₁)) ⊆ ball(M, d, x, r₁)",
										By(BallConcentric.At(M, d, x, smaller, r1), below))
									c.Take(smaller)
									c.Do(SplitConj(
										Case(
											"the smaller radius is positive, both radii being positive",
											By(real_sup_inf.LessThanMin.At(r0, r1, c.TermAs[Real]("&0")), aboutU[0], aboutV[0])),
										Case(
											"and its ball lies in u and in v",
											BySets(toU, toV, aboutU[1], aboutV[1])),
									))
								})),
						))
					})),
				Case(
					"a family of open sets unites to an open set",
					// The union axiom reads s ⊆ T; unfolding the inclusion exposes
					// each member's openness for OpenIff to read.
					Unfold(set_basic.SubsetDef),
					Simp(Fwd(OpenIff)),
					Derive(func(b *Argument) {
						s := b.FixAs[Set[Set[A]]]("s")
						open := b.Assume()
						b.Do(SplitConj(
							Case(
								"the union lies in M, as every member does",
								Derive(func(c *Argument) {
									within := c.Have(
										"every member of s lies in M, being open",
										"∀w:set(A). w ∈ s ⇒ w ⊆ M",
										By(open))
									c.Show(
										"so their union does",
										By(set_order.UnionsSubset.At(s, M), within))
								})),
							Case(
								"a point of the union has a ball about it inside the union",
								Derive(func(c *Argument) {
									x := c.FixAs[A]("x")
									inUnion := c.Assume()
									w, member := c.ObtainAs[Set[A]](
										"x lies in some member w of s",
										"∃w:set(A). w ∈ s ∧ x ∈ w",
										BySets(inUnion))
									holds := c.Conjuncts(
										member,
										"w is a member of s",
										"x lies in w")
									wOpen := c.Conjuncts(
										c.Have(
											"w is open, being a member of s",
											"w ⊆ M ∧ ∀y:A. y ∈ w ⇒ ∃r:real. &0 < r ∧ ball(M, d, y, r) ⊆ w",
											By(Normalized, open.At(w), holds[0])),
										"w lies in M",
										"each point of w has a ball about it inside w")
									r0, radius := c.ObtainAs[Real](
										"so w gives x a ball of radius r₀ inside it",
										"∃r:real. &0 < r ∧ ball(M, d, x, r) ⊆ w",
										By(wOpen[1].At(x), holds[1]))
									about := c.Conjuncts(
										radius,
										"r₀ is positive",
										"the ball of radius r₀ lies in w")
									inside := c.Have(
										"w lies in the union of s",
										"w ⊆ ⋃s",
										By(set_order.MemberSubsetUnions.At(s, w), holds[0]))
									c.Take(r0)
									c.Do(SplitConj(
										Case(
											"the radius is positive",
											By(about[0])),
										Case(
											"and the ball lies in w, hence in ⋃s",
											By(
												set_order.SubsetTrans.At(c.TermAs[Set[A]]("ball(M, d, x, r₀)"), w, c.TermAs[Set[A]]("⋃s")),
												about[1],
												inside)),
									))
								})),
						))
					})),
			))
		}),
})}

// MetricTopologySpace — the points of the space are the points of M.
// Every open set lies in M by definition, and M itself is open, since
// a ball is drawn from the points of M and so lies in M whatever its
// radius. Nothing is asked of the distance.
var MetricTopologySpace = metricTopologySpaceThm{family.Add(registry.ProofEntry{
	Name: "MetricTopologySpace",
	Key:  "prop_735d0e9f76f017e2",
	Build: family.Theorem("∀M:set(A). ∀d:(A → A → real). ⋃metric_topology(M, d) = M",
		func(a *Argument, M *Expr[Set[A]], d *Expr[Fun2[A, A, Real]]) {
			within := a.Have(
				"every open set lies in M",
				"∀u:set(A). u ∈ metric_topology(M, d) ⇒ u ⊆ M",
				Simp(Fwd(OpenIff)),
				BySets())
			spaceOpen := a.Have(
				"M is open: the unit ball about a point of M lies in M",
				"M ∈ metric_topology(M, d)",
				Simp(Fwd(OpenIff)),
				SplitConj(
					Case(
						"M lies in itself",
						BySets()),
					Case(
						"the unit ball about each point of M lies in M",
						Derive(func(b *Argument) {
							b.FixAs[A]()
							b.Assume()
							b.Take(b.TermAs[Real]("&1"))
							b.Do(SplitConj(
								Case(
									"one is positive",
									ByArith()),
								Case(
									"a ball is drawn from the points of M",
									Unfold(BallDef),
									BySets()),
							))
						})),
				))
			open := a.TermAs[Set[Set[A]]]("metric_topology(M, d)")
			below := a.Have(
				"so the union of the open sets lies in M",
				"⋃metric_topology(M, d) ⊆ M",
				By(set_order.UnionsSubset.At(open, M), within))
			above := a.Have(
				"and M, one of them, lies in their union",
				"M ⊆ ⋃metric_topology(M, d)",
				By(set_order.MemberSubsetUnions.At(open, M), spaceOpen))
			a.Show(
				"so the union is M",
				By(set_order.SubsetAntisym.At(a.TermAs[Set[A]]("⋃metric_topology(M, d)"), M), below, above))
		}),
})}

// ClosedIff — a subset of M is closed exactly when each point of M
// outside it has a ball about it missing the set. Closedness asks that
// the complement in the space be open; the space is M, and a ball,
// being drawn from M, lies in the complement of c exactly when it
// misses c. Nothing is asked of the distance.
var ClosedIff = closedIffThm{family.Add(registry.ProofEntry{
	Name: "ClosedIff",
	Key:  "prop_93e0d3a22a386486",
	Build: family.Theorem("∀M:set(A). ∀d:(A → A → real). ∀c:set(A). "+
		"    closed_in(metric_topology(M, d), c) ⇔ "+
		"    c ⊆ M ∧ ∀x:A. x ∈ M ∧ x ∉ c ⇒ ∃r:real. &0 < r ∧ ball(M, d, x, r) ∩ c = ∅",
		func(a *Argument, M *Expr[Set[A]], d *Expr[Fun2[A, A, Real]], c *Expr[Set[A]]) {
			// Closed: c lies in the space and its complement there is open.
			// The space is M, and the complement is open when each of its
			// points has a ball about it inside the complement.
			a.Do(Unfold(topological_space.ClosedInDef), Simp(Fwd(MetricTopologySpace)), Simp(Fwd(OpenIff)))
			a.Iff()

			a.Forward(
				"a ball inside the complement of c misses c",
				func(b *Argument, closed Fact) {
					b.Do(SplitConj(
						Case(
							"c lies in M",
							By(closed)),
						Case(
							"a point of M outside c has a ball about it missing c",
							Derive(func(e *Argument) {
								e.FixAs[A]("x")
								outside := e.Assume()
								r, inside := e.ObtainAs[Real](
									"x lies in the complement, which is open, so a ball about x lies inside it",
									"∃r:real. &0 < r ∧ ball(M, d, x, r) ⊆ M ∖ c",
									BySets(closed, outside))
								e.Take(r)
								e.Do(SplitConj(
									Case(
										"its radius is positive",
										By(inside)),
									Case(
										"and it misses c",
										BySets(inside)),
								))
							})),
					))
				})

			a.Backward(
				"a ball missing c lies in the complement of c, a ball being drawn from M",
				func(b *Argument, apart Fact) {
					b.Do(SplitConjAll(
						Case(
							"c lies in M",
							By(apart)),
						Case(
							"the complement of c lies in M",
							BySets()),
						Case(
							"a point of the complement has a ball about it inside the complement",
							Derive(func(e *Argument) {
								e.FixAs[A]("x")
								outside := e.Assume()
								r, misses := e.ObtainAs[Real](
									"x is a point of M outside c, so a ball about x misses c",
									"∃r:real. &0 < r ∧ ball(M, d, x, r) ∩ c = ∅",
									BySets(apart, outside))
								within := e.Have(
									"the ball is drawn from M",
									"ball(M, d, x, r) ⊆ M",
									Unfold(BallDef),
									BySets())
								e.Take(r)
								e.Do(SplitConj(
									Case(
										"its radius is positive",
										By(misses)),
									Case(
										"and it lies in M and misses c",
										BySets(within, misses)),
								))
							})),
					))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The balls are open
// ---------------------------------------------------------------------------

// BallOpen — a ball about a point of M is open. A point y of the ball is
// within r of x, and the ball about y of radius r − d(x, y) lies inside
// it: a point z of M that close to y is within r of x, by the triangle
// inequality through y.
var BallOpen = ballOpenThm{family.Add(registry.ProofEntry{
	Name: "BallOpen",
	Key:  "prop_ee308183f08921a2",
	Build: MetricSpace.Law(Statement{
		Binders: "∀x:A. ∀r:real.",
		Hypotheses: []string{
			"x ∈ M",
		},
		Conclusion: "ball(x, r) ∈ metric_topology",
	},
		func(a *Argument, metric MetricSpaceFact[on.M], x *Member[A, on.M], r *Expr[Real]) {
			a.Do(Simp(Fwd(OpenIff)))
			a.Do(SplitConj(
				Case(
					"the ball lies in M",
					Unfold(BallDef),
					BySets()),
				Case(
					"a point y of the ball keeps the radius r − d(x, y) inside it",
					Derive(func(b *Argument) {
						y := b.FixAs[A]("y")
						inBall := b.Assume()
						near := b.Have(
							"y is a point of M within r of x",
							"y ∈ M ∧ d(x, y) < r",
							Unfold(BallDef),
							BySets(inBall))
						yM := b.MemberOf[on.M](y, b.Conjuncts(
							near,
							"y lies in M",
							"y is within r of x")[0])
						closer := b.Have(
							"a point of M within r − d(x, y) of y is within r of x",
							"∀z:A. z ∈ M ∧ d(y, z) < r - d(x, y) ⇒ d(x, z) < r",
							Derive(func(c *Argument) {
								z := c.FixAs[A]("z")
								h := c.Assume()
								zM := c.MemberOf[on.M](z, c.Conjuncts(
									h,
									"z lies in M",
									"z is within the remaining radius of y")[0])
								detour := c.Have(
									"the way from x to z through y",
									"d(x, z) ≤ d(x, y) + d(y, z)",
									By(DistTriangle.Read(metric).At(x, yM, zM)))
								c.Show(
									"is shorter than r",
									ByArith(detour, h))
							}))
						b.Take(b.TermAs[Real]("r - d(x, y)"))
						b.Do(SplitConj(
							Case(
								"the radius is positive, y being within r of x",
								ByArith(near)),
							Case(
								"and the smaller ball lies in the larger",
								Unfold(BallDef),
								BySets(closer)),
						))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Closed balls
// ---------------------------------------------------------------------------

// ClosedBallClosed — a closed ball about a point of M is closed. A point
// y of M outside it is not within r of x, and the ball about y of radius
// d(x, y) − r misses it: a point z of M in both would give, by the
// triangle inequality through z, d(x, y) ≤ d(x, z) + d(z, y) <
// r + (d(x, y) − r).
var ClosedBallClosed = closedBallClosedThm{family.Add(registry.ProofEntry{
	Name: "ClosedBallClosed",
	Key:  "prop_6dc37be7e6c214dd",
	Build: MetricSpace.Law(Statement{
		Binders: "∀x:A. ∀r:real.",
		Hypotheses: []string{
			"x ∈ M",
		},
		Conclusion: "closed_in(metric_topology, closed_ball(x, r))",
	},
		func(a *Argument, metric MetricSpaceFact[on.M], x *Member[A, on.M], r *Expr[Real]) {
			// Closed: the closed ball lies in M, and each point of M outside it
			// has a ball about it missing it. Both balls are read as the points
			// of M near their centres.
			a.Do(Simp(Fwd(ClosedIff)), Unfold(ClosedBallDef), Unfold(BallDef), SplitConj(
				Case(
					"the closed ball lies in M",
					BySets()),
				Case(
					"a point y of M outside it has the ball of radius d(x, y) − r about it missing it",
					Derive(func(b *Argument) {
						y := b.FixAs[A]("y")
						outside := b.Assume()
						far := b.Have(
							"y, a point of M outside the closed ball, is not within r of x",
							"¬(d(x, y) ≤ r)",
							BySets(outside))
						apart := b.Have(
							"no point of M is within d(x, y) − r of y and within r "+
								"of x: the way from x to y through it would be too short",
							"∀z:A. ¬((z ∈ M ∧ d(y, z) < d(x, y) - r) ∧ (z ∈ M ∧ d(x, z) ≤ r))",
							// z's membership is a conjunct of the negated goal, not a
							// resident fact, so the two laws are cited untyped and the
							// closer discharges the memberships itself.
							b.ForEach(func(z *Expr[A]) Action {
								return ByArith(
									DistTriangle.Read(metric).AsFact().At(x, z, y),
									DistSym.Read(metric).AsFact().At(z, y),
									x,
									outside)
							}))
						b.Take(b.TermAs[Real]("d(x, y) - r"))
						b.Do(SplitConj(
							Case(
								"the radius is positive, y not being within r of x",
								ByArith(far)),
							Case(
								"and no point lies in both balls",
								BySets(apart)),
						))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Separation
// ---------------------------------------------------------------------------

// MetricHausdorff — the open sets of a metric space separate points. Two
// distinct points x and y of M are a positive distance apart, and the
// balls of half that distance about each are open, hold their centres
// and are disjoint: a point z of M in both would be within half the
// distance of x and of y, and the detour from x to y through z would be
// shorter than the distance itself.
var MetricHausdorff = metricHausdorffThm{family.Add(registry.ProofEntry{
	Name: "MetricHausdorff",
	Key:  "prop_6c463142e687726",
	Build: MetricSpace.Law("hausdorff(metric_topology)",
		func(a *Argument, metric MetricSpaceFact[on.M]) {
			// Two distinct points of the space, which is M.
			a.Do(Unfold(topological_space.HausdorffDef), Simp(Fwd(MetricTopologySpace)))
			x := a.FixAs[A]("x")
			y := a.FixAs[A]("y")
			points := a.Conjuncts(
				a.Assume(),
				"x is a point of M",
				"so is y",
				"and the two are distinct")
			xM, yM := a.MemberOf[on.M](x, points[0]), a.MemberOf[on.M](y, points[1])
			half := a.TermAs[Real]("d(x, y) / &2")
			a.Take(a.TermAs[Set[A]]("ball(x, d(x, y) / &2)"))
			a.Take(a.TermAs[Set[A]]("ball(y, d(x, y) / &2)"))
			apart := a.Have(
				"they are a positive distance apart: a distance is never "+
					"negative, and vanishes only between a point and itself",
				"&0 < d(x, y)",
				By(
					real_order_ring.LessThanSplit.At(a.TermAs[Real]("&0"), a.TermAs[Real]("d(x, y)")),
					DistNonneg.Read(metric).At(xM, yM),
					DistZeroIff.Read(metric).At(xM, yM),
					points[2]))
			positive := a.Have(
				"so half their distance is positive",
				"&0 < d(x, y) / &2",
				ByArith(apart))
			a.Do(SplitConjAll(
				Case(
					"the ball about x is open",
					By(BallOpen.Read(metric).At(xM, half))),
				Case(
					"the ball about y is open",
					By(BallOpen.Read(metric).At(yM, half))),
				Case(
					"x lies in its ball",
					By(CentreInBall.Read(metric).At(xM, half), positive)),
				Case(
					"y lies in its ball",
					By(CentreInBall.Read(metric).At(yM, half), positive)),
				Case(
					"and the two balls are disjoint",
					Derive(func(b *Argument) {
						// The two balls read as the points of M near their centres.
						b.Do(Unfold(BallDef))
						separated := b.Have(
							"no point of M is within half the distance of both: the "+
								"detour from x to y through it would be shorter than d(x, y)",
							"∀z:A. ¬((z ∈ M ∧ d(x, z) < d(x, y) / &2) ∧ (z ∈ M ∧ d(y, z) < d(x, y) / &2))",
							// As in ClosedBallClosed: z's membership is part of the goal,
							// so the laws are cited untyped.
							b.ForEach(func(z *Expr[A]) Action {
								return ByArith(
									DistTriangle.Read(metric).AsFact().At(x, z, y),
									DistSym.Read(metric).AsFact().At(z, y),
									points[0],
									points[1])
							}))
						b.Show(
							"so the two balls share no point",
							BySets(separated))
					})),
			))
		}),
})}
