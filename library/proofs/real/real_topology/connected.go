// connected.go — the connected sets of the line are its intervals: an
// interval cannot be split by two open sets, and a set that skips a point
// is split at it. An interval holds every point t·x + (1 − t)·y between
// two of its points x and y, the form a convex combination reads it in.

package real_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/topology/connected"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// An interval holds the points between two of its points
// ---------------------------------------------------------------------------

// IntervalSegment — an interval holds every point t·x + (1 − t)·y with
// x and y in it and t between 0 and 1: that point lies between x and y.
var IntervalSegment = intervalSegmentThm{family.Add(registry.ProofEntry{
	Name: "IntervalSegment",
	Key:  "prop_7823206c83e34573",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀x y t:real.",
		Hypotheses: []string{
			"real_interval(s)",
			"x ∈ s",
			"y ∈ s",
			"&0 ≤ t",
			"t ≤ &1",
		},
		Conclusion: "t * x + (&1 - t) * y ∈ s",
	}, func(
		a *Argument,
		s *Expr[Set[Real]],
		x, y, t *Expr[Real],
		interval, xIn, yIn, nonneg, atMostOne Fact,
	) {
		between := a.Unfolded(interval, RealIntervalDef)
		point := a.TermAs[Real]("t * x + (&1 - t) * y")
		a.Cases(a.Term("x ≤ y"))
		a.When(
			"x ≤ y: the point lies between x and y",
			func(b *Argument, xy Fact) {
				b.Show(
					"so s holds it",
					ByArith(between.At(x, point, y), xIn, yIn, xy, nonneg, atMostOne),
				)
			})
		a.Otherwise(
			"y < x: the point lies between y and x",
			func(b *Argument, notXY Fact) {
				yx := b.Have(
					"y is at most x",
					"y ≤ x",
					ByArith(notXY))
				b.Show(
					"so s holds it",
					ByArith(between.At(y, point, x), yIn, xIn, yx, nonneg, atMostOne),
				)
			})
	}),
})}

// ---------------------------------------------------------------------------
// Intervals are connected
// ---------------------------------------------------------------------------

// IntervalConnected — an interval of reals is connected.
//
// The heart is a least-upper-bound argument: two open sets u and v
// covering an interval s, with a point p of s in u and a point q ≥ p of s
// in v, share a point of s. The points of ⟦p, q⟧ — which lies in s —
// that lie in u form a set t holding p and capped by q, so its supremum m
// has p ≤ m ≤ q. If m lies in v, a radius δ around m stays in v, and a
// point of t within δ below m — there is one, m being the least upper
// bound — lies in v as well as in u. Otherwise m lies in u and short of
// q, and a radius δ around m stays in u; the point min(m + δ/2, q) is
// then a point of t above m, which no upper bound allows.
//
// An interval lies in the line, which is the space. Two open sets
// covering it and each meeting it hand over a point p in the first and a
// point q in the second; the order being total, the argument runs from
// the first to the second or from the second to the first.
var IntervalConnected = intervalConnectedThm{family.Add(registry.ProofEntry{
	Name: "IntervalConnected",
	Key:  "prop_df4da784565cb92d",
	Build: family.Sections(Statement{
		Binders: "∀s:set(real).",
		Hypotheses: []string{
			"real_interval(s)",
		},
		Conclusion: "connected_in(real_topology, s)",
		Abbrev: Abbrev{
			{Name: "halfwayText", Text: "sup(t) + δ / &2"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// The least-upper-bound argument, from a point p of s in u to a
			// point q ≥ p of s in v.
			overlap := ctx.Lemma(Statement{
				Binders: "∀s u v:set(real). ∀p q:real.",
				Hypotheses: []string{
					"real_interval(s)",
					"u ∈ real_topology",
					"v ∈ real_topology",
					"s ⊆ u ∪ v",
					"p ∈ s",
					"p ∈ u",
					"q ∈ s",
					"q ∈ v",
					"p ≤ q",
				},
				Conclusion: "¬(s ∩ u ∩ v = ∅)",
			},
				func(a *Argument, s, u, v *Expr[Set[Real]], p, q *Expr[Real], assumptions Fact) {
					parts := a.Conjuncts(
						assumptions,
						"s is an interval",
						"u is open",
						"v is open",
						"u and v cover s",
						"p lies in s",
						"and in u",
						"q lies in s",
						"and in v",
						"p ≤ q")
					interval, uOpen, vOpen, covers := parts[0], parts[1], parts[2], parts[3]
					pInS, pInU, qInS, qInV, pq := parts[4], parts[5], parts[6], parts[7], parts[8]
					between := a.Unfolded(interval, RealIntervalDef)
					cover := a.Have(
						"⟦p, q⟧ lies in s, so in u ∪ v",
						"∀x:real. p ≤ x ∧ x ≤ q ⇒ x ∈ u ∨ x ∈ v",
						a.ForEach(func(x *Expr[Real]) Action {
							return BySets(between.At(p, x, q), pInS, qInS, covers)
						}))

					t, points := a.ObtainAs[Set[Real]](
						"the points of ⟦p, q⟧ lying in u form a set t",
						"∃t:set(real). ∀x:real. x ∈ t ⇔ p ≤ x ∧ x ≤ q ∧ x ∈ u",
						Derive(func(b *Argument) {
							b.Take(b.TermAs[Set[Real]]("{x:real | p ≤ x ∧ x ≤ q ∧ x ∈ u}"))
							b.Show(
								"the comprehension holds exactly those points",
								BySets())
						}))
					pInT := a.Have(
						"p is one of them",
						"p ∈ t",
						By(points.At(p), real_order_ring.LessEqRefl.At(p), pq, pInU))
					nonEmpty := a.Have(
						"so t is not empty",
						"t ≠ ∅",
						BySets(pInT))
					capped := a.Have(
						"and q caps it",
						"∀x:real. x ∈ t ⇒ x ≤ q",
						a.ForEach(func(x *Expr[Real]) Action { return By(points.At(x)) }))
					bounded := a.Have(
						"so t is bounded above",
						"∃b:real. ∀x:real. x ∈ t ⇒ x ≤ b",
						Derive(func(b *Argument) {
							b.Take(q)
							b.Show(
								"q is such a bound",
								By(capped))
						}))
					m := a.TermAs[Real]("sup(t)")
					above := a.Have(
						"its supremum is at least p, a member",
						"p ≤ sup(t)",
						By(real_sup_inf.MemberLessEqSup.At(t, p), bounded, pInT))
					below := a.Have(
						"and at most q, a bound",
						"sup(t) ≤ q",
						By(real_sup_inf.SupLessEqBound.At(t, q), nonEmpty, capped))

					a.Cases(a.Term("sup(t) ∈ v"))
					a.When(
						"the supremum lies in v: a point of t just below it lies in v too",
						func(b *Argument, mInV Fact) {
							vRadii := b.Have(
								"v is open: each of its points has a radius inside v",
								"∀x:real. x ∈ v ⇒ ∃δ:real. &0 < δ ∧ ∀y:real. |y - x| < δ ⇒ y ∈ v",
								Simp(Rev(OpenIff)),
								By(vOpen))
							d, radius := b.ObtainAs[Real](
								"so some radius δ around sup(t) stays in v",
								"∃δ:real. &0 < δ ∧ ∀y:real. |y - sup(t)| < δ ⇒ y ∈ v",
								By(vRadii.At(m), mInV))
							ball := b.Conjuncts(
								radius,
								"δ is positive",
								"and every real within δ of sup(t) lies in v")
							x, approach := b.ObtainAs[Real](
								"so, t being bounded, one of its points x lies within δ below sup(t)",
								"∃x:real. x ∈ t ∧ sup(t) - δ < x ∧ x ≤ sup(t)",
								By(real_sup_inf.SupApproachWithin.At(t, d), nonEmpty, bounded, ball[0]))
							xAt := b.Conjuncts(
								approach,
								"x is a point of t",
								"above sup(t) − δ",
								"at most sup(t)")
							near := b.Have(
								"so x is within δ of sup(t)",
								"|x - sup(t)| < δ",
								ByArith(xAt[1], xAt[2]))
							xInV := b.Have(
								"and so lies in v",
								"x ∈ v",
								By(ball[1].At(x), near))
							xIn := b.Have(
								"x is a point of ⟦p, q⟧ in u, being a point of t",
								"p ≤ x ∧ x ≤ q ∧ x ∈ u",
								By(points.At(x), xAt[0]))
							xInS := b.Have(
								"so it lies in s, which holds ⟦p, q⟧",
								"x ∈ s",
								By(between.At(p, x, q), pInS, qInS, xIn))
							b.Show(
								"x is a point of s in u and in v",
								BySets(xInS, xIn, xInV))
						})
					a.Otherwise(
						"the supremum lies outside v: a point of t beyond it contradicts its bound",
						func(b *Argument, mOutV Fact) {
							mInU := b.Have(
								"sup(t) lies in ⟦p, q⟧, so in u or in v — and it is not in v",
								"sup(t) ∈ u",
								By(cover.At(m), above, below, mOutV))
							mNotQ := b.Have(
								"so it is not q, which lies in v",
								"sup(t) ≠ q",
								By(Normalized, qInV, mOutV))
							short := b.Have(
								"and falls short of q",
								"sup(t) < q",
								ByArith(below, mNotQ))
							uRadii := b.Have(
								"u is open: each of its points has a radius inside u",
								"∀x:real. x ∈ u ⇒ ∃δ:real. &0 < δ ∧ ∀y:real. |y - x| < δ ⇒ y ∈ u",
								Simp(Rev(OpenIff)),
								By(uOpen))
							_, radius := b.ObtainAs[Real](
								"so some radius δ around sup(t) stays in u",
								"∃δ:real. &0 < δ ∧ ∀y:real. |y - sup(t)| < δ ⇒ y ∈ u",
								By(uRadii.At(m), mInU))
							ball := b.Conjuncts(
								radius,
								"δ is positive",
								"and every real within δ of sup(t) lies in u")
							w, past := b.ObtainAs[Real](
								"some w lies above sup(t), within δ of it, and not past q",
								"∃w:real. sup(t) < w ∧ w ≤ q ∧ |w - sup(t)| < δ",
								Derive(func(c *Argument) {
									halfway := c.TermAs[Real]("«halfwayText»")
									c.Take(c.TermAs[Real]("min(«halfwayText», q)"))
									c.Show(
										"the smaller of sup(t) + δ/2 and q: above sup(t), since both are, and at most either",
										ByArith(
											real_sup_inf.LessThanMin.At(halfway, q, m),
											real_sup_inf.MinLessEq.At(halfway, q, q),
											real_sup_inf.MinLessEq.At(halfway, q, halfway),
											ball[0],
											short))
								}))
							wAt := b.Conjuncts(
								past,
								"w lies above sup(t)",
								"w is at most q",
								"w is within δ of sup(t)")
							wInU := b.Have(
								"so w lies in u",
								"w ∈ u",
								By(ball[1].At(w), wAt[2]))
							pBelowW := b.Have(
								"and w is at least p",
								"p ≤ w",
								ByArith(above, wAt[0]))
							wInT := b.Have(
								"so w is a point of t",
								"w ∈ t",
								By(points.At(w), pBelowW, wAt[1], wInU))
							wBelow := b.Have(
								"and at most its supremum",
								"w ≤ sup(t)",
								By(real_sup_inf.MemberLessEqSup.At(t, w), bounded, wInT))
							b.Show(
								"a point of t above its supremum: no such point exists",
								ByArith(wAt[0], wBelow))
						})
				})

			return ctx.Theorem(headline, func(a *Argument, s *Expr[Set[Real]], interval Fact) {
				a.Do(Unfold(connected.ConnectedInDef))
				a.Do(SplitConj(
					Case(
						"s lies in the space, which is the whole line",
						BySets(RealSpace)),
					Case(
						"two open sets covering s and each meeting it share a point of s",
						Derive(func(b *Argument) {
							u := b.FixAs[Set[Real]]()
							v := b.FixAs[Set[Real]]()
							parts := b.Conjuncts(
								b.Assume(),
								"u is open",
								"v is open",
								"u and v cover s",
								"u meets s",
								"v meets s")
							uOpen, vOpen, covers, meetsU, meetsV := parts[0], parts[1], parts[2], parts[3], parts[4]
							p, pAt := b.ObtainAs[Real](
								"u meets s at a point p",
								"∃p:real. p ∈ s ∧ p ∈ u",
								BySets(meetsU))
							q, qAt := b.ObtainAs[Real](
								"v meets s at a point q",
								"∃q:real. q ∈ s ∧ q ∈ v",
								BySets(meetsV))
							pIn := b.Conjuncts(
								pAt,
								"p lies in s",
								"and in u")
							qIn := b.Conjuncts(
								qAt,
								"q lies in s",
								"and in v")

							order := b.Have(
								"the order is total",
								"p ≤ q ∨ q ≤ p",
								By(real_construction.LessEqTotal.At(p, q)))
							b.Do(order.SplitDisj(
								LeftHolds(
									"p ≤ q: the argument runs from u to v",
									Given(func(c *Argument, pq Fact) {
										c.Show(
											"so u and v share a point of s",
											By(At(overlap, s, u, v, p, q), interval, uOpen, vOpen, covers, pIn[0], pIn[1], qIn[0], qIn[1], pq))
									})),
								RightHolds(
									"q ≤ p: the argument runs from v to u",
									Given(func(c *Argument, qp Fact) {
										// The lemma read from v to u: its cover and its meet
										// spell the two open sets the other way round.
										commuted := c.Have(
											"a union reads either way round",
											"v ∪ u = u ∪ v",
											By(set_algebra.UnionComm.At(v, u)))
										coversSwapped := c.Have(
											"so v and u cover s",
											"s ⊆ v ∪ u",
											commuted.Rw(),
											By(covers))
										shared := c.Have(
											"so v and u share a point of s",
											"¬(s ∩ v ∩ u = ∅)",
											By(
												At(overlap, s, v, u, q, p),
												interval,
												vOpen,
												uOpen,
												coversSwapped,
												qIn[0],
												qIn[1],
												pIn[0],
												pIn[1],
												qp))
										meet := c.Have(
											"a meet reads in any order",
											"s ∩ u ∩ v = s ∩ v ∩ u",
											BySets())
										c.Show(
											"a point of s in v and in u is one in u and in v",
											meet.Rw(),
											By(shared))
									})),
							))
						})),
				))
			})
		}),
})}

// ---------------------------------------------------------------------------
// A connected set is an interval
// ---------------------------------------------------------------------------

// ConnectedImpInterval — a connected set of reals is an interval.
//
// Let x and z lie in s with x ≤ y ≤ z, and suppose y is not in s. The
// two open rays below and above y split s: every point of s differs
// from y, so lies in one of them; x, a point of s at most y and not y
// itself, lies in the lower ray, and z likewise in the upper; and no
// real lies in both. But connectedness says two open sets covering s
// and each meeting it share a point of s.
var ConnectedImpInterval = connectedImpIntervalThm{family.Add(registry.ProofEntry{
	Name: "ConnectedImpInterval",
	Key:  "prop_1fd74ab63aa0033c",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real).",
		Hypotheses: []string{
			"connected_in(real_topology, s)",
		},
		Conclusion: "real_interval(s)",
		Abbrev: Abbrev{
			{Name: "lowerRay", Text: "{t:real | t < y}"},
			{Name: "upperRay", Text: "{t:real | y < t}"},
		},
	},
		func(a *Argument, s *Expr[Set[Real]], sConnected Fact) {
			// The two rays that split s at a point y it skips, each
			// spelled once for the claims that must agree on them.
			const lowerRay, upperRay = "{t:real | t < y}", "{t:real | y < t}"

			unsplit := a.Conjuncts(
				a.Unfolded(sConnected, connected.ConnectedInDef),
				"s lies in the space",
				"and no two open sets split it")[1]
			a.Do(Unfold(RealIntervalDef))
			x := a.FixAs[Real]("x")
			y := a.FixAs[Real]("y")
			z := a.FixAs[Real]("z")
			between := a.Conjuncts(
				a.Assume(),
				"x lies in s",
				"z lies in s",
				"x ≤ y",
				"y ≤ z")
			skipped := a.SupposeNot()

			covers := a.Have(
				"every point of s differs from y, so lies in one of the rays",
				"s ⊆ «lowerRay» ∪ «upperRay»",
				BySets(skipped, real_order_ring.LessThanTrichotomy))
			meetsLower := a.Have(
				"x is a point of s in the lower ray: x ≤ y, and x is not y, y not being in s",
				"¬(s ∩ «lowerRay» = ∅)",
				BySets(skipped, between[0], between[2], real_order_ring.LessEqSplit.At(x, y)))
			meetsUpper := a.Have(
				"and z a point of s in the upper ray: y ≤ z, and z is not y",
				"¬(s ∩ «upperRay» = ∅)",
				BySets(skipped, between[1], between[3], real_order_ring.LessEqSplit.At(y, z)))
			disjoint := a.Have(
				"and no point of s lies in both, no real being both below and above y",
				"s ∩ «lowerRay» ∩ «upperRay» = ∅",
				BySets(real_order_ring.LessThanAsym))

			lower, upper := a.TermAs[Set[Real]]("«lowerRay»"), a.TermAs[Set[Real]]("«upperRay»")
			a.Show(
				"so the two open rays split s, which connectedness forbids",
				By(
					unsplit.At(lower, upper),
					RayBelowOpen.At(y),
					RayAboveOpen.At(y),
					covers,
					meetsLower,
					meetsUpper,
					disjoint))
		}),
})}

// ---------------------------------------------------------------------------
// The connected sets of the line
// ---------------------------------------------------------------------------

// ConnectedIffInterval — a set of reals is connected exactly when it is
// an interval: the two directions above, met.
var ConnectedIffInterval = connectedIffIntervalThm{family.Add(registry.ProofEntry{
	Name: "ConnectedIffInterval",
	Key:  "prop_13fb59af7154e18a",
	Build: family.Theorem("∀s:set(real). connected_in(real_topology, s) ⇔ real_interval(s)",
		func(a *Argument, s *Expr[Set[Real]]) {
			a.Show(
				"a connected set is an interval, and an interval is connected",
				By(Normalized, ConnectedImpInterval.At(s), IntervalConnected.At(s)))
		}),
})}
