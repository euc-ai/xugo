// bounded.go — bounded sets: a subset of M the distances between whose
// points are bounded. A non-empty set is bounded exactly when it lies in
// a closed ball; a subset of a bounded set, a union of two or of
// finitely many, and a ball are bounded; and a compact set is bounded.

package metric_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Bounded sets
// ---------------------------------------------------------------------------

// BoundedIffInBall — a set is bounded exactly when it lies in M and is
// empty or inside a closed ball about a point of M. A point of a
// non-empty bounded set serves as a centre and the bound as a radius.
// Conversely two points of a closed ball of radius r are within 2r of
// each other, the way from one to the other through the centre being no
// shorter; and the empty set is bounded by anything.
var BoundedIffInBall = boundedIffInBallThm{family.Add(registry.ProofEntry{
	Name: "BoundedIffInBall",
	Key:  "prop_9e55cd8af536117f",
	Build: MetricSpace.Law("∀s:set(A). "+
		"    metric_bounded(s) ⇔ s ⊆ M ∧ (s = ∅ ∨ ∃c:A. ∃r:real. c ∈ M ∧ s ⊆ closed_ball(c, r))",
		func(a *Argument, metric MetricSpaceFact[on.M], s *Expr[Set[A]]) {
			a.Iff()
			a.Forward(
				"a point of a non-empty bounded set is a centre, and the bound a radius",
				func(b *Argument, bounded Fact) {
					parts := b.Conjuncts(
						b.Unfolded(bounded, MetricBoundedDef),
						"s lies in M",
						"some K bounds the distances between points of s")
					_, bound := b.Unpack(parts[1], "K")
					b.Cases(b.Term("s = ∅"))
					b.When(
						"an empty s is the first alternative",
						func(c *Argument, empty Fact) {
							c.Show(
								"s lies in M and is empty",
								By(Normalized, empty, parts[0]))
						})
					b.Otherwise(
						"a non-empty s lies in the closed ball of radius K about any of its points",
						func(c *Argument, nonEmpty Fact) {
							_, xIn := c.Obtain(
								"s has a point x",
								"∃x:A. x ∈ s",
								By(nonEmpty, set_basic.MemberNotEmpty))
							ball := c.Have(
								"every point of s is a point of M within K of x",
								"s ⊆ closed_ball(x, K)",
								BySets(bound, xIn, parts[0], ClosedBallDef))
							c.Show(
								"so x, a point of M, is a centre and K a radius",
								BySets(parts[0], xIn, ball))
						})
				})
			a.Backward(
				"two points of a closed ball of radius r are within 2r of each other, through its centre",
				func(b *Argument, given Fact) {
					parts := b.Conjuncts(
						given,
						"s lies in M",
						"s is empty or lies in a closed ball about a point of M")
					b.Show(
						"s lies in M, and the distances between its points are bounded",
						Simp(Fwd(MetricBoundedDef)),
						parts[1].SplitDisj(
							LeftHolds(
								"the empty set is bounded by anything",
								Given(func(e *Argument, empty Fact) {
									e.Show(
										"the empty set lies in M, and has no two points to bound",
										BySets(empty))
								})),
							RightHolds(
								"a closed ball of radius r bounds by 2r",
								Given(func(e *Argument, inBall Fact) {
									centre, _, ball := e.Unpack2As[A, Real](inBall, "c", "r")
									held := e.Conjuncts(
										ball,
										"c lies in M",
										"s lies in the closed ball of radius r about c")
									cM := e.MemberOf[on.M](centre, held[0])
									near := e.Have(
										"each point of s is a point of M within r of c",
										"∀x:A. x ∈ s ⇒ x ∈ M ∧ d(c, x) ≤ r",
										BySets(e.Unfolded(held[1], ClosedBallDef)))
									within := e.Have(
										"two points of s are within 2r of each other: the way through c is no shorter",
										"∀x y:A. x ∈ s ∧ y ∈ s ⇒ d(x, y) ≤ &2 * r",
										Derive(func(f *Argument) {
											x := f.FixAs[A]("x")
											y := f.FixAs[A]("y")
											both := f.Assume()
											// x and y are in M only through near, so the laws
											// are cited untyped and the closer discharges
											// their memberships.
											f.Show(
												"d(x, y) is at most d(x, c) + d(c, y), each at most r",
												ByArith(
													near.At(x),
													near.At(y),
													both,
													cM,
													DistTriangle.Read(metric).AsFact().At(x, centre, y),
													DistSym.Read(metric).AsFact().At(x, centre)))
										}))
									e.Show(
										"so 2r bounds the distances between points of s",
										By(within, parts[0]))
								})),
						))
				})
		}),
})}

// BoundedSubset — a subset of a bounded set is bounded: it lies in M
// because the larger set does, and a bound on the distances between
// points of the larger set bounds those between points of the smaller.
// No axiom enters, so the carrier and the distance are spelled.
var BoundedSubset = boundedSubsetThm{family.Add(registry.ProofEntry{
	Name: "BoundedSubset",
	Key:  "prop_51dad6b52384bb23",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀s t:set(A).",
		Hypotheses: []string{
			"metric_bounded(M, d, t)",
			"s ⊆ t",
		},
		Conclusion: "metric_bounded(M, d, s)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			s, t *Expr[Set[A]],
			bounded, inside Fact,
		) {
			held := a.Unfolded(bounded, MetricBoundedDef)
			a.Show(
				"s lies in M through t, and the bound on the distances in t serves for s",
				Simp(Fwd(MetricBoundedDef)),
				BySets(held, inside))
		}),
})}

// BoundedUnion — two bounded sets unite to a bounded set. An empty one
// leaves the other. Otherwise s lies in a closed ball of radius r₁ about
// a point c₁ of M and t in one of radius r₂ about c₂; a point of t is
// within d(c₁, c₂) + r₂ of c₁, through c₂, so the union lies in the
// closed ball about c₁ whose radius is the larger of r₁ and
// d(c₁, c₂) + r₂.
var BoundedUnion = boundedUnionThm{family.Add(registry.ProofEntry{
	Name: "BoundedUnion",
	Key:  "prop_bfdab7a07e74782f",
	Build: MetricSpace.Law(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"metric_bounded(s)",
			"metric_bounded(t)",
		},
		Conclusion: "metric_bounded(s ∪ t)",
	},
		func(a *Argument, metric MetricSpaceFact[on.M], s, t *Expr[Set[A]], sBounded, tBounded Fact) {
			// Each set, and the union, read as lying in M and being empty
			// or inside a closed ball about a point of M.
			inBall := BoundedIffInBall.Read(metric)
			sIn := a.Conjuncts(
				a.Simplified(sBounded, Fwd(inBall)),
				"s lies in M",
				"s is empty or lies in a closed ball about a point of M")
			tIn := a.Conjuncts(
				a.Simplified(tBounded, Fwd(inBall)),
				"t lies in M",
				"t is empty or lies in a closed ball about a point of M")
			a.Do(Simp(Fwd(inBall)))
			sOccupied := a.Unless(
				a.Term("s = ∅"),
				"an empty s leaves the union t",
				Given(func(b *Argument, empty Fact) {
					b.Show(
						"which lies in M and is empty or inside a closed ball",
						BySets(empty, tIn[0], tIn[1]))
				}))
			tOccupied := a.Unless(
				a.Term("t = ∅"),
				"an empty t leaves the union s",
				Given(func(b *Argument, empty Fact) {
					b.Show(
						"which lies in M and is empty or inside a closed ball",
						BySets(empty, sIn[0], sIn[1]))
				}))
			c1, r1, sBall := a.Obtain2As[A, Real](
				"s lies in a closed ball of radius r₁ about a point c₁ of M",
				"∃c₁:A. ∃r₁:real. c₁ ∈ M ∧ s ⊆ closed_ball(c₁, r₁)",
				By(sIn[1], sOccupied))
			c2, _, tBall := a.Obtain2As[A, Real](
				"and t in one of radius r₂ about a point c₂ of M",
				"∃c₂:A. ∃r₂:real. c₂ ∈ M ∧ t ⊆ closed_ball(c₂, r₂)",
				By(tIn[1], tOccupied))
			sAbout := a.Conjuncts(
				sBall,
				"c₁ lies in M",
				"s lies in the closed ball of radius r₁ about c₁")
			tAbout := a.Conjuncts(
				tBall,
				"c₂ lies in M",
				"t lies in the closed ball of radius r₂ about c₂")
			c1M := a.MemberOf[on.M](c1, sAbout[0])
			c2M := a.MemberOf[on.M](c2, tAbout[0])
			nearS := a.Have(
				"each point of s is a point of M within r₁ of c₁",
				"∀x:A. x ∈ s ⇒ x ∈ M ∧ d(c₁, x) ≤ r₁",
				BySets(a.Unfolded(sAbout[1], ClosedBallDef)))
			nearT := a.Have(
				"each point of t is a point of M within r₂ of c₂",
				"∀x:A. x ∈ t ⇒ x ∈ M ∧ d(c₂, x) ≤ r₂",
				BySets(a.Unfolded(tAbout[1], ClosedBallDef)))
			_, radius := a.LetAs[Real]("R", "max(r₁, d(c₁, c₂) + r₂)")
			larger := real_sup_inf.MaxUpperBound.At(r1, a.TermAs[Real]("d(c₁, c₂) + r₂"))
			fromS := a.Have(
				"a point of s is within R of c₁, R being at least r₁",
				"∀x:A. x ∈ s ⇒ d(c₁, x) ≤ R",
				a.ForEach(func(x *Expr[A]) Action {
					return ByArith(nearS.At(x), larger, radius)
				}))
			fromT := a.Have(
				"a point of t is within d(c₁, c₂) + r₂ of c₁, through c₂, and so within R",
				"∀x:A. x ∈ t ⇒ d(c₁, x) ≤ R",
				// x lies in M only through nearT, so the triangle inequality
				// is cited untyped and the closer discharges its membership.
				a.ForEach(func(x *Expr[A]) Action {
					return ByArith(
						nearT.At(x),
						larger,
						radius,
						c1M,
						c2M,
						DistTriangle.Read(metric).AsFact().At(c1, c2, x))
				}))
			ball := a.Have(
				"so the union lies in the closed ball of radius R about c₁",
				"s ∪ t ⊆ closed_ball(c₁, R)",
				Unfold(ClosedBallDef),
				BySets(sIn[0], tIn[0], fromS, fromT))
			a.Show(
				"and c₁, a point of M, is a centre for it",
				BySets(c1M, sIn[0], tIn[0], ball))
		}),
})}

// BoundedUnions — finitely many bounded sets unite to a bounded set. By
// induction on the family: no sets unite to the empty set, which is
// bounded, and one more bounded set x unites with the union of the rest,
// bounded by the induction hypothesis, to a union of two bounded sets.
var BoundedUnions = boundedUnionsThm{family.Add(registry.ProofEntry{
	Name: "BoundedUnions",
	Key:  "prop_7669e6deca48cd2",
	Build: MetricSpace.Law(Statement{
		Binders: "∀f:set(set(A)).",
		Hypotheses: []string{
			"finite(f)",
			"∀u:set(A). u ∈ f ⇒ metric_bounded(u)",
		},
		Conclusion: "metric_bounded(⋃f)",
	},
		func(a *Argument, metric MetricSpaceFact[on.M], f *Expr[Set[Set[A]]], finite, boundedMembers Fact) {
			a.Show(
				"the induction carries the property to f, which is finite with bounded members",
				ByInduction(finite_set.FiniteInduct, finite, Generalizing(boundedMembers),
					Case(
						"no sets unite to the empty set, which has no two points to bound",
						BySets(MetricBoundedDef)),
					Case(
						"one more bounded set x unites with the union of the rest, bounded by the induction hypothesis",
						Derive(func(b *Argument) {
							x := b.FixAs[Set[A]]()
							b.FixAs[Set[Set[A]]]("s")
							carried := b.Assume() // the induction hypothesis, itself conditional
							given := b.Assume()   // every member of insert(x, s) is bounded
							members := b.Have(
								"x is bounded, and so is every member of s",
								"metric_bounded(x) ∧ (∀u:set(A). u ∈ s ⇒ metric_bounded(u))",
								By(given, set_basic.ForallInInsert))
							b.Show(
								"⋃insert(x, s) is x ∪ ⋃s, a union of two bounded sets",
								Simp(Fwd(set_algebra.UnionsInsert)),
								By(carried, members, BoundedUnion.Read(metric).At(x, b.TermAs[Set[A]]("⋃s"))))
						}))))
		}),
})}

// BallBounded — a ball about a point of M is bounded: it lies in M and
// in the closed ball of the same radius, so its centre and radius serve
// as a closed ball's.
var BallBounded = ballBoundedThm{family.Add(registry.ProofEntry{
	Name: "BallBounded",
	Key:  "prop_36a0db64d2b9ec7c",
	Build: MetricSpace.Law(Statement{
		Binders: "∀x:A. ∀r:real.",
		Hypotheses: []string{
			"x ∈ M",
		},
		Conclusion: "metric_bounded(ball(x, r))",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric MetricSpaceFact[on.M],
			x *Member[A, on.M],
			r *Expr[Real],
		) {
			inM := a.Have(
				"the ball lies in M",
				"ball(x, r) ⊆ M",
				Unfold(BallDef),
				BySets())
			a.Show(
				"and in the closed ball of the same radius, so x, a "+
					"point of M, is a centre for the ball and r a radius",
				By(
					BoundedIffInBall.Read(metric).At(a.TermAs[Set[A]]("ball(x, r)")),
					inM,
					BallSubsetClosedBall.At(M, d, x, r),
					x))
		}),
})}

// CompactBounded — a compact set of a metric space is bounded. The balls
// of radius 1 about the points of k are open and cover k, each holding
// its centre; finitely many of them already cover k. Each is bounded, so
// their union is, and k lies in it.
var CompactBounded = compactBoundedThm{family.Add(registry.ProofEntry{
	Name: "CompactBounded",
	Key:  "prop_5bff9aa1a6c5bd0",
	Build: MetricSpace.Law(Statement{
		Binders: "∀k:set(A).",
		Hypotheses: []string{
			"compact_in(metric_topology, k)",
		},
		Conclusion: "metric_bounded(k)",
		Abbrev: Abbrev{
			{Name: "unitBalls", Text: "{ball(x, &1) | x:A | x ∈ k}"},
		},
	},
		func(a *Argument, metric MetricSpaceFact[on.M], k *Expr[Set[A]], kCompact Fact) {
			parts := a.Conjuncts(
				a.Unfolded(kCompact, compact.CompactInDef),
				"k lies in the space of the topology",
				"every open cover of k has a finite subcover")
			kInM := a.Have(
				"k lies in M, the space of the topology",
				"k ⊆ M",
				By(parts[0], MetricTopologySpace))
			one := a.TermAs[Real]("&1")
			open := a.Have(
				"a ball of radius 1 about a point of k is open, the point lying in M",
				"∀x:A. x ∈ k ⇒ ball(x, &1) ∈ metric_topology",
				a.ForEach(func(x *Expr[A]) Action {
					return By(kInM, BallOpen.Read(metric), set_basic.SubsetDef)
				}))
			centred := a.Have(
				"and holds its centre",
				"∀x:A. x ∈ k ⇒ x ∈ ball(x, &1)",
				// x lies in M only through k, so the law is cited untyped
				// and the closer discharges its membership.
				a.ForEach(func(x *Expr[A]) Action {
					return By(kInM, CentreInBall.Read(metric).AsFact().At(x, one), set_basic.SubsetDef)
				}))
			ballsOpen := a.Have(
				"so the balls of radius 1 about the points of k are open sets",
				"«unitBalls» ⊆ metric_topology",
				BySets(open))
			ballsCover := a.Have(
				"and they cover k",
				"k ⊆ ⋃«unitBalls»",
				BySets(centred))
			e, subcover := a.ObtainAs[Set[Set[A]]](
				"compactness at that cover: finitely many of the balls, a family e, already cover k",
				"∃e:set(set(A)). e ⊆ «unitBalls» ∧ finite(e) ∧ k ⊆ ⋃e",
				By(parts[1], ballsOpen, ballsCover))
			held := a.Conjuncts(
				subcover,
				"e is made of the balls",
				"e is finite",
				"e covers k")
			each := a.Have(
				"each member of e is a ball about a point of M, and so bounded",
				"∀u:set(A). u ∈ e ⇒ metric_bounded(u)",
				a.ForEach(func(u *Expr[Set[A]]) Action {
					return BySets(kInM, held[0], BallBounded.Read(metric))
				}))
			union := a.Have(
				"finitely many bounded sets unite to a bounded set",
				"metric_bounded(⋃e)",
				By(BoundedUnions.Read(metric).At(e), held[1], each))
			a.Show(
				"and k lies in that union",
				By(BoundedSubset, union, held[2]))
		}),
})}
