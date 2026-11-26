// compact.go — the compact sets of the line: a closed bounded interval is
// compact and a compact set is bounded; a non-empty closed set bounded
// above holds its supremum (below, its infimum), and so a non-empty
// compact set — closed, the line being Hausdorff — holds both.

package real_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Closed intervals are compact
// ---------------------------------------------------------------------------

// ClosedIntervalCompact — a closed bounded interval ⟦a, b⟧ is compact
// (Heine–Borel on the line).
//
// The interval lies in the line, the whole space. Fix an open cover c.
// If b < a the interval is empty and the empty subfamily covers it.
// Otherwise let S be the set of points x of ⟦a, b⟧ such that finitely
// many members of c cover ⟦a, x⟧. S holds a — one member of c holds
// a, and covers ⟦a, a⟧ — and b bounds it, so its supremum sup S lies
// in ⟦a, b⟧. Some member v of c holds sup S; being open, v holds a
// whole radius δ around it, and a point x of S lies above sup S − δ,
// with a finite d ⊆ c covering ⟦a, x⟧. Adding v to d covers every
// ⟦a, z⟧ with z < sup S + δ: a point up to x is covered by d, and one
// past x lies within δ of sup S, in v — the extension step, a section
// of its own. If sup S + δ did not pass b, then sup S + δ/2 would be
// such a z inside ⟦a, b⟧, a point of S above its supremum; so it
// passes b, and insert(v, d) is a finite subcover of ⟦a, b⟧.
var ClosedIntervalCompact = closedIntervalCompactThm{family.Add(registry.ProofEntry{
	Name: "ClosedIntervalCompact",
	Key:  "prop_5ce5fe7ac2da1058",
	Build: family.Sections("∀a b:real. compact_in(real_topology, ⟦a, b⟧)",
		func(ctx *Script, headline string) *GoalStackNode {
			// The extension step. A point of ⟦a, z⟧ either lies in ⟦a, x⟧,
			// where d covers it, or lies past x — and then between m − δ
			// and m + δ, inside the ball v holds.
			extend := ctx.Lemma(Statement{
				Binders: "∀a x z:real. ∀d:set(set(real)). ∀v:set(real). ∀m δ:real.",
				Hypotheses: []string{
					"⟦a, x⟧ ⊆ ⋃d",
					"∀y:real. |y - m| < δ ⇒ y ∈ v",
					"m - δ < x",
					"z < m + δ",
				},
				Conclusion: "⟦a, z⟧ ⊆ ⋃insert(v, d)",
			},
				func(
					arg *Argument,
					a, x, z *Expr[Real],
					d *Expr[Set[Set[Real]]],
					v *Expr[Set[Real]],
					m, δ *Expr[Real],
					h Fact,
				) {
					parts := arg.Conjuncts(
						h,
						"d covers ⟦a, x⟧",
						"v holds every point within δ of m",
						"x lies above m − δ",
						"z lies below m + δ")
					covered, ball, xAbove, zBelow := parts[0], parts[1], parts[2], parts[3]
					pointwise := arg.Have(
						"each point of ⟦a, z⟧ lies in a member of insert(v, d)",
						"∀y:real. a ≤ y ∧ y ≤ z ⇒ y ∈ ⋃insert(v, d)",
						Derive(func(point *Argument) {
							y := point.FixAs[Real]()
							yIn := point.Assume()
							point.Cases(point.Term("y ≤ x"))
							point.When(
								"y lies in ⟦a, x⟧, which d covers",
								func(branch *Argument, yLeX Fact) {
									branch.Show(
										"so y lies in a member of d",
										BySets(covered, yIn, yLeX))
								})
							point.Otherwise(
								"y lies past x, so m − δ < x < y ≤ z < m + δ",
								func(branch *Argument, yPastX Fact) {
									near := branch.Have(
										"y is within δ of m",
										"|y - m| < δ",
										ByArith(yPastX, yIn, xAbove, zBelow))
									branch.Show(
										"so y lies in v",
										BySets(ball.At(y), near))
								})
						}))
					arg.Show(
						"hence insert(v, d) covers ⟦a, z⟧",
						BySets(pointwise))
				})

			return ctx.Theorem(headline, func(arg *Argument, a, b *Expr[Real]) {
				arg.Do(Unfold(compact.CompactInDef))
				arg.Do(SplitConj(
					Case(
						"the interval lies in the line, the whole space",
						BySets(RealSpace)),
					Case(
						"every open cover of the interval has a finite subcover",
						Derive(func(cover *Argument) {
							cover.FixAs[Set[Set[Real]]]()
							parts := cover.Conjuncts(
								cover.Assume(),
								"c is a family of open sets",
								"whose union holds ⟦a, b⟧")
							open, covers := parts[0], parts[1]
							cover.Cases(cover.Term("a ≤ b"))
							cover.Otherwise(
								"b < a: the interval is empty, and the empty subfamily covers it",
								func(branch *Argument, notLe Fact) {
									empty := branch.Have(
										"no real lies between a and b",
										"∀x:real. ¬(a ≤ x ∧ x ≤ b)",
										ByArith(notLe))
									emptyInterval := branch.Have(
										"so ⟦a, b⟧ is empty",
										"⟦a, b⟧ = ∅",
										BySets(empty))
									// The empty family, its element type written out: ∅ alone is
									// polymorphic, and here it is a family of sets of reals.
									branch.Take(branch.TermAs[Set[Set[Real]]]("∅⟨A:set(real)⟩"))
									branch.Show(
										"the empty family lies in c, is finite, and covers the empty interval",
										BySets(emptyInterval, finite_set.FiniteRules))
								})
							cover.When(
								"a ≤ b: the least-upper-bound argument",
								func(branch *Argument, aLeB Fact) {
									reached := branch.Let(
										"S", branch.Term("{x:real | a ≤ x ∧ x ≤ b ∧ (∃d:set(set(real)). d ⊆ c ∧ finite(d) ∧ ⟦a, x⟧ ⊆ ⋃d)}"))
									member := branch.Have(
										"a point lies in S exactly when finitely many members of c cover ⟦a, x⟧",
										"∀x:real. x ∈ S ⇔ a ≤ x ∧ x ≤ b ∧ (∃d:set(set(real)). d ⊆ c ∧ finite(d) ∧ ⟦a, x⟧ ⊆ ⋃d)",
										BySets(reached))

									// S holds a, and b caps it: one member u of c holds a
									// and covers ⟦a, a⟧, and S lies in ⟦a, b⟧.
									sFacts := branch.Conjuncts(
										branch.Have(
											"S holds a, and b caps it",
											"a ∈ S ∧ (∀x:real. x ∈ S ⇒ x ≤ b)",
											Derive(func(inner *Argument) {
												u, holdsA := inner.ObtainAs[Set[Real]](
													"a lies in ⟦a, b⟧, so in some member u of c",
													"∃u:set(real). u ∈ c ∧ a ∈ u",
													BySets(covers, aLeB, real_order_ring.LessEqRefl.At(a)))
												uParts := inner.Conjuncts(
													holdsA,
													"u is a member of c",
													"holding a")
												uInC, aInU := uParts[0], uParts[1]
												onlyA := inner.Have(
													"⟦a, a⟧ holds a alone",
													"∀y:real. a ≤ y ∧ y ≤ a ⇒ y = a",
													ByArith())
												start := inner.Have(
													"the single member u covers ⟦a, a⟧",
													"∃d:set(set(real)). d ⊆ c ∧ finite(d) ∧ ⟦a, a⟧ ⊆ ⋃d",
													Derive(func(witness *Argument) {
														witness.Take(witness.Term("{u}"))
														witness.Do(SplitConjAll(
															Case(
																"{u} lies in c",
																By(uInC, set_order.SingSubset)),
															Case(
																"a singleton is finite",
																By(finite_set.FiniteSing.At(u))),
															Case(
																"and u covers ⟦a, a⟧",
																BySets(onlyA, aInU)),
														))
													}))
												aInS := inner.Have(
													"so a lies in S",
													"a ∈ S",
													By(member.At(a), start, aLeB, real_order_ring.LessEqRefl.At(a)))
												capped := inner.Have(
													"S lies in ⟦a, b⟧, so b caps it",
													"∀x:real. x ∈ S ⇒ x ≤ b",
													inner.ForEach(func(x *Expr[Real]) Action { return By(member.At(x)) }))
												inner.Show(
													"both",
													By(aInS, capped))
											})),
										"a lies in S",
										"b caps S")
									aInS, capped := sFacts[0], sFacts[1]
									nonempty := branch.Have(
										"so S is not empty",
										"S ≠ ∅",
										BySets(aInS))
									bounded := branch.Have(
										"and it is bounded above",
										"∃β:real. ∀x:real. x ∈ S ⇒ x ≤ β",
										Derive(func(inner *Argument) {
											inner.Take(b)
											inner.Show(
												"by b",
												By(capped))
										}))

									// Its supremum lies in ⟦a, b⟧.
									aBelowSup := branch.Have(
										"a lies below sup S",
										"a ≤ sup(S)",
										By(real_sup_inf.MemberLessEqSup, bounded, aInS))
									supBelowB := branch.Have(
										"and b caps S, so sup S lies below b",
										"sup(S) ≤ b",
										By(real_sup_inf.SupLessEqBound, nonempty, capped))

									// A member v of c holds sup S, and a whole radius δ
									// around it.
									_, _, heldBall := branch.Obtain2As[Set[Real], Real](
										"sup S lies in some member v of c, which holds a whole radius δ around it",
										"∃v:set(real). ∃δ:real. v ∈ c ∧ &0 < δ ∧ ∀y:real. |y - sup(S)| < δ ⇒ y ∈ v",
										Derive(func(inner *Argument) {
											vW, holdsSup := inner.ObtainAs[Set[Real]](
												"sup S lies in ⟦a, b⟧, so in some member v of c",
												"∃v:set(real). v ∈ c ∧ sup(S) ∈ v",
												BySets(covers, aBelowSup, supBelowB))
											vParts := inner.Conjuncts(
												holdsSup,
												"v is a member of c",
												"holding sup S")
											vOpen := inner.Have(
												"v is open, as every member of c is",
												"v ∈ real_topology",
												BySets(open, vParts[0]))
											radii := inner.Have(
												"so each point of v has a radius inside v",
												"∀x:real. x ∈ v ⇒ ∃δ:real. &0 < δ ∧ (∀y:real. |y - x| < δ ⇒ y ∈ v)",
												Simp(Rev(OpenIff)),
												By(vOpen))
											δW, radius := inner.ObtainAs[Real](
												"in particular a radius δ around sup S stays in v",
												"∃δ:real. &0 < δ ∧ ∀y:real. |y - sup(S)| < δ ⇒ y ∈ v",
												By(radii.At(inner.TermAs[Real]("sup(S)")), vParts[1]))
											inner.Take(vW)
											inner.Take(δW)
											inner.Show(
												"v, and that radius",
												By(vParts[0], radius))
										}))
									vBall := branch.Conjuncts(
										heldBall,
										"v is a member of c",
										"δ is positive",
										"and the δ-ball around sup S lies in v")
									vInC, δPositive, ball := vBall[0], vBall[1], vBall[2]

									// A point x of S within δ below sup S, with a finite
									// subfamily d of c covering ⟦a, x⟧; adding v to d keeps
									// the family finite and inside c.
									_, _, nearSup := branch.Obtain2As[Real, Set[Set[Real]]](
										"a point x of S lies within δ below sup S, and finitely many members d of c cover ⟦a, x⟧",
										"∃x:real. ∃d:set(set(real)). sup(S) - δ < x ∧ d ⊆ c ∧ finite(d) ∧ ⟦a, x⟧ ⊆ ⋃d",
										Derive(func(inner *Argument) {
											xW, within := inner.ObtainAs[Real](
												"S is approached from inside: a point x of S lies within δ below sup S",
												"∃x:real. x ∈ S ∧ sup(S) - δ < x ∧ x ≤ sup(S)",
												By(real_sup_inf.SupApproachWithin, nonempty, bounded, δPositive))
											xParts := inner.Conjuncts(
												within,
												"x lies in S",
												"above sup S − δ",
												"at most sup S")
											dW, coverX := inner.ObtainAs[Set[Set[Real]]](
												"finitely many members d of c cover ⟦a, x⟧, x being a point of S",
												"∃d:set(set(real)). d ⊆ c ∧ finite(d) ∧ ⟦a, x⟧ ⊆ ⋃d",
												By(member.At(xW), xParts[0]))
											inner.Take(xW)
											inner.Take(dW)
											inner.Show(
												"x, and d",
												By(xParts[1], coverX))
										}))
									xd := branch.Conjuncts(
										nearSup,
										"x lies above sup S − δ",
										"d lies in c",
										"d is finite",
										"d covers ⟦a, x⟧")
									xAbove, dInC, dFinite, dCovers := xd[0], xd[1], xd[2], xd[3]
									extendedInC := branch.Have(
										"insert(v, d) lies in c",
										"insert(v, d) ⊆ c",
										By(set_order.InsertSubset, vInC, dInC))
									extendedFinite := branch.Have(
										"and is finite",
										"finite(insert(v, d))",
										By(dFinite, finite_set.FiniteInsert))

									// The ball around sup S reaches past b: otherwise
									// sup S + δ/2 would be a point of S above its supremum.
									pastB := branch.Have(
										"the δ-ball around sup S reaches past b",
										"b < sup(S) + δ",
										Derive(func(inner *Argument) {
											short := inner.SupposeNot()
											halfway := inner.Have(
												"sup S + δ/2 lies below sup S + δ",
												"sup(S) + δ / &2 < sup(S) + δ",
												ByArith(δPositive))
											coversHalfway := inner.Have(
												"insert(v, d) covers ⟦a, sup S + δ/2⟧, by the extension step",
												"⟦a, sup(S) + δ / &2⟧ ⊆ ⋃insert(v, d)",
												By(extend, dCovers, ball, xAbove, halfway))
											finiteHalfway := inner.Have(
												"a finite subfamily of c covers ⟦a, sup S + δ/2⟧",
												"∃d:set(set(real)). d ⊆ c ∧ finite(d) ∧ ⟦a, sup(S) + δ / &2⟧ ⊆ ⋃d",
												Derive(func(witness *Argument) {
													witness.Take(witness.Term("insert(v, d)"))
													witness.Show(
														"namely insert(v, d)",
														By(extendedInC, extendedFinite, coversHalfway))
												}))
											inInterval := inner.Have(
												"sup S + δ/2 lies in ⟦a, b⟧, since sup S + δ does not pass b",
												"a ≤ sup(S) + δ / &2 ∧ sup(S) + δ / &2 ≤ b",
												ByArith(short, aBelowSup, δPositive))
											halfwayInS := inner.Have(
												"so sup S + δ/2 lies in S",
												"sup(S) + δ / &2 ∈ S",
												By(member.At(inner.TermAs[Real]("sup(S) + δ / &2")), finiteHalfway, inInterval))
											belowSup := inner.Have(
												"so it lies below sup S",
												"sup(S) + δ / &2 ≤ sup(S)",
												By(real_sup_inf.MemberLessEqSup, bounded, halfwayInS))
											inner.Show(
												"which δ > 0 forbids",
												ByArith(belowSup, δPositive))
										}))

									// So insert(v, d) covers ⟦a, b⟧.
									coversAll := branch.Have(
										"insert(v, d) covers ⟦a, b⟧, by the extension step",
										"⟦a, b⟧ ⊆ ⋃insert(v, d)",
										By(extend, dCovers, ball, xAbove, pastB))
									branch.Take(branch.Term("insert(v, d)"))
									branch.Show(
										"insert(v, d) is a finite subfamily of c covering ⟦a, b⟧",
										By(extendedInC, extendedFinite, coversAll))
								})
						})),
				))
			})
		}),
})}

// ---------------------------------------------------------------------------
// A compact set is bounded
// ---------------------------------------------------------------------------

// CompactBounded — a compact set of reals is bounded.
//
// The balls about 0 cover k, a point x lying in the ball of radius
// |x| + 1, and each of them is open, so compactness picks finitely many
// of them, a family d, still covering k. Two balls about 0 are nested —
// the one of smaller radius lies inside the other — so d is a finite
// chain. If d is empty, k lies in the empty union and has no point to
// bound. Otherwise the finite chain holds its union, which is therefore
// itself a ball about 0, of some radius r, and every point of k lies
// within r of 0.
var CompactBounded = compactBoundedThm{family.Add(registry.ProofEntry{
	Name: "CompactBounded",
	Key:  "prop_87b3d67813819d3f",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(real).",
		Hypotheses: []string{
			"compact_in(real_topology, k)",
		},
		Conclusion: "∃B:real. ∀x:real. x ∈ k ⇒ |x| ≤ B",
		Abbrev: Abbrev{
			{Name: "ballsAboutZero", Text: "{b:set(real) | ∃r:real. b = {y:real | |y - &0| < r}}"},
		},
	},
		func(a *Argument, k *Expr[Set[Real]], kCompact Fact) {
			subcover := a.Conjuncts(
				a.Unfolded(kCompact, compact.CompactInDef),
				"k lies in the line",
				"every open cover of k has a finite subcover")[1]

			ballOpen := a.Have(
				"a ball about 0 is open",
				"∀b:set(real). (∃r:real. b = {y:real | |y - &0| < r}) ⇒ b ∈ real_topology",
				Derive(func(b *Argument) {
					b.FixAs[Set[Real]]()
					r, isBall := b.UnpackAs[Real](b.Assume())
					b.Show(
						"it is the ball of radius r about 0",
						By(Normalized, isBall, BallOpen.At(b.TermAs[Real]("&0"), r)))
				}))
			ballsOpen := a.Have(
				"so the cover is made of open sets",
				"«ballsAboutZero» ⊆ real_topology",
				BySets(ballOpen))
			pointwise := a.Have(
				"a point x of k lies in the ball of radius |x| + 1 about 0, a member of the cover",
				"∀x:real. x ∈ k ⇒ x ∈ ⋃«ballsAboutZero»",
				Derive(func(b *Argument) {
					b.FixAs[Real]()
					near := b.Have(
						"x lies within |x| + 1 of 0",
						"|x - &0| < |x| + &1",
						ByArith())
					b.Show(
						"so x lies in the ball of radius |x| + 1, a member of the cover",
						BySets(near))
				}))
			ballsCoverK := a.Have(
				"the balls about 0 cover k",
				"k ⊆ ⋃«ballsAboutZero»",
				BySets(pointwise))

			d, finiteSubcover := a.ObtainAs[Set[Set[Real]]](
				"compactness at that cover: finitely many balls about 0 already cover k",
				"∃d:set(set(real)). d ⊆ «ballsAboutZero» ∧ finite(d) ∧ k ⊆ ⋃d",
				// Grounded at the cover, its two guards the facts just
				// shown, the subcover clause states the claim.
				GroupPremises(ballsOpen, ballsCoverK, subcover.At(a.TermAs[Set[Set[Real]]]("«ballsAboutZero»"))),
				Assumption())
			parts := a.Conjuncts(
				finiteSubcover,
				"d is made of balls about 0",
				"d is finite",
				"d covers k")
			finiteD, coversK := parts[1], parts[2]
			balls := a.Have(
				"each member of d is a ball about 0, of some radius",
				"∀b:set(real). b ∈ d ⇒ ∃r:real. b = {y:real | |y - &0| < r}",
				BySets(parts[0]))

			chain := a.Have(
				"d is a chain: of two balls about 0, the one of smaller radius lies inside the other",
				"∀s t:set(real). s ∈ d ∧ t ∈ d ⇒ s ⊆ t ∨ t ⊆ s",
				Derive(func(b *Argument) {
					s := b.FixAs[Set[Real]]()
					t := b.FixAs[Set[Real]]()
					members := b.Conjuncts(
						b.Assume(),
						"s is a member of d",
						"and so is t")
					_, sBall := b.ObtainAs[Real](
						"s is the ball about 0 of some radius r",
						"∃r:real. s = {y:real | |y - &0| < r}",
						By(balls.At(s), members[0]))
					_, tBall := b.ObtainAs[Real](
						"and t the ball about 0 of some radius q",
						"∃q:real. t = {y:real | |y - &0| < q}",
						By(balls.At(t), members[1]))
					b.Cases(b.Term("r ≤ q"))
					b.When(
						"r ≤ q: a real within r of 0 is within q of 0, so s lies inside t",
						func(c *Argument, le Fact) {
							inside := c.Have(
								"the reals within r of 0 are within q of 0",
								"∀y:real. |y - &0| < r ⇒ |y - &0| < q",
								ByArith(le))
							c.Show(
								"so s, the ball of radius r, lies inside t, the ball of radius q",
								Left(),
								sBall.Rw(),
								tBall.Rw(),
								BySets(inside))
						})
					b.Otherwise(
						"q < r: a real within q of 0 is within r of 0, so t lies inside s",
						func(c *Argument, notLe Fact) {
							inside := c.Have(
								"the reals within q of 0 are within r of 0",
								"∀y:real. |y - &0| < q ⇒ |y - &0| < r",
								ByArith(notLe))
							c.Show(
								"so t, the ball of radius q, lies inside s, the ball of radius r",
								Right(),
								sBall.Rw(),
								tBall.Rw(),
								BySets(inside))
						})
				}))

			a.Cases(a.Term("d = ∅"))
			a.When(
				"no ball at all: k lies in the empty union, so it has no point to bound",
				func(b *Argument, empty Fact) {
					b.Take(b.TermAs[Real]("&0"))
					b.Show(
						"any bound serves for a set with no points",
						BySets(empty, coversK))
				})
			a.Otherwise(
				"some ball: the largest of them, their union, bounds k",
				func(b *Argument, nonEmpty Fact) {
					largest := b.Have(
						"a finite non-empty chain holds its union",
						"⋃d ∈ d",
						By(finite_set.UnionsInChain.At(d), finiteD, nonEmpty, chain))
					r, unionBall := b.ObtainAs[Real](
						"so the union is itself a ball about 0, of some radius r",
						"∃r:real. ⋃d = {y:real | |y - &0| < r}",
						By(balls.At(b.TermAs[Set[Real]]("⋃d")), largest))
					b.Take(r)
					b.FixAs[Real]()
					inK := b.Assume()
					within := b.Have(
						"a point x of k lies in the union, within r of 0",
						"|x - &0| < r",
						BySets(unionBall, inK, coversK))
					b.Show(
						"so |x| ≤ r",
						ByArith(within))
				})
		}),
})}

// ---------------------------------------------------------------------------
// A closed set holds its bounds
// ---------------------------------------------------------------------------

// SupClosedAttained — a non-empty closed set of reals that is bounded
// above holds its supremum.
//
// Suppose sup s lies outside s. The set is closed, so some radius δ about
// sup s misses it. But the supremum is approached from inside: a member x
// of s lies within δ below sup s, and so within δ of it — missing s,
// though it is a member.
var SupClosedAttained = supClosedAttainedThm{family.Add(registry.ProofEntry{
	Name: "SupClosedAttained",
	Key:  "prop_c91ae3fba3e94e0b",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real).",
		Hypotheses: []string{
			"closed_in(real_topology, s)",
			"s ≠ ∅",
			"∃b:real. ∀x:real. x ∈ s ⇒ x ≤ b",
		},
		Conclusion: "sup(s) ∈ s",
	},
		func(a *Argument, s *Expr[Set[Real]], given Fact) {
			parts := a.Conjuncts(
				given,
				"s is closed",
				"s is non-empty",
				"s is bounded above")
			closed, nonEmpty, bounded := parts[0], parts[1], parts[2]
			outside := a.SupposeNot()
			missing := a.Have(
				"s is closed: a real outside it has a radius missing it",
				"∀x:real. x ∉ s ⇒ ∃δ:real. &0 < δ ∧ ∀y:real. |y - x| < δ ⇒ y ∉ s",
				Simp(Rev(ClosedIff)),
				By(closed))
			d, radius := a.ObtainAs[Real](
				"so a radius δ about sup s misses s",
				"∃δ:real. &0 < δ ∧ ∀y:real. |y - sup(s)| < δ ⇒ y ∉ s",
				By(missing.At(a.TermAs[Real]("sup(s)")), outside))
			ball := a.Conjuncts(
				radius,
				"δ is positive",
				"the reals within δ of sup s miss s")
			x, approach := a.ObtainAs[Real](
				"but a member x of s lies within δ below sup s",
				"∃x:real. x ∈ s ∧ sup(s) - δ < x ∧ x ≤ sup(s)",
				By(real_sup_inf.SupApproachWithin.At(s, d), nonEmpty, bounded, ball[0]))
			member := a.Conjuncts(
				approach,
				"x is a member of s",
				"above sup s − δ",
				"at most sup s")
			near := a.Have(
				"so x is within δ of sup s",
				"|x - sup(s)| < δ",
				ByArith(member[1], member[2]))
			a.Show(
				"and misses s, though it is a member",
				By(ball[1].At(x), near, member[0]))
		}),
})}

// InfClosedAttained — a non-empty closed set of reals that is bounded
// below holds its infimum: SupClosedAttained's mirror. Were inf s outside
// s, a radius δ about it would stay outside s, yet a member x of s lies
// below inf s + δ and at or above inf s, so within δ of it.
var InfClosedAttained = infClosedAttainedThm{family.Add(registry.ProofEntry{
	Name: "InfClosedAttained",
	Key:  "prop_443efc50160fe59f",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real).",
		Hypotheses: []string{
			"closed_in(real_topology, s)",
			"s ≠ ∅",
			"∃b:real. ∀x:real. x ∈ s ⇒ b ≤ x",
		},
		Conclusion: "inf(s) ∈ s",
	},
		func(a *Argument, s *Expr[Set[Real]], given Fact) {
			parts := a.Conjuncts(
				given,
				"s is closed",
				"s is non-empty",
				"s is bounded below")
			closed, nonEmpty, bounded := parts[0], parts[1], parts[2]
			outside := a.SupposeNot()
			missing := a.Have(
				"s is closed: a real outside it has a radius missing it",
				"∀x:real. x ∉ s ⇒ ∃δ:real. &0 < δ ∧ ∀y:real. |y - x| < δ ⇒ y ∉ s",
				Simp(Rev(ClosedIff)),
				By(closed))
			d, radius := a.ObtainAs[Real](
				"so a radius δ about inf s misses s",
				"∃δ:real. &0 < δ ∧ ∀y:real. |y - inf(s)| < δ ⇒ y ∉ s",
				By(missing.At(a.TermAs[Real]("inf(s)")), outside))
			ball := a.Conjuncts(
				radius,
				"δ is positive",
				"the reals within δ of inf s miss s")
			x, approach := a.ObtainAs[Real](
				"but a member x of s lies within δ above inf s",
				"∃x:real. x ∈ s ∧ inf(s) ≤ x ∧ x < inf(s) + δ",
				By(real_sup_inf.InfApproachWithin.At(s, d), nonEmpty, bounded, ball[0]))
			member := a.Conjuncts(
				approach,
				"x is a member of s",
				"at least inf s",
				"below inf s + δ")
			near := a.Have(
				"so x is within δ of inf s",
				"|x - inf(s)| < δ",
				ByArith(member[1], member[2]))
			a.Show(
				"and misses s, though it is a member",
				By(ball[1].At(x), near, member[0]))
		}),
})}

// ---------------------------------------------------------------------------
// A compact set holds its bounds
// ---------------------------------------------------------------------------

// SupCompactAttained — a non-empty compact set of reals holds its
// supremum, which is then its greatest element. A compact set is bounded,
// and closed because the line is Hausdorff; a non-empty closed set
// bounded above holds its supremum, and every member lies at or below it.
var SupCompactAttained = supCompactAttainedThm{family.Add(registry.ProofEntry{
	Name: "SupCompactAttained",
	Key:  "prop_1f506930b93e0a90",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(real).",
		Hypotheses: []string{
			"compact_in(real_topology, k)",
			"k ≠ ∅",
		},
		Conclusion: "sup(k) ∈ k ∧ (∀x:real. x ∈ k ⇒ x ≤ sup(k))",
	},
		func(a *Argument, k *Expr[Set[Real]], given Fact) {
			parts := a.Conjuncts(
				given,
				"k is compact",
				"k is non-empty")
			bound, size := a.ObtainAs[Real](
				"a compact set is bounded: some B bounds the size of its points",
				"∃B:real. ∀x:real. x ∈ k ⇒ |x| ≤ B",
				By(CompactBounded.At(k), parts[0]))
			above := a.Have(
				"so k is bounded above, by that B",
				"∃b:real. ∀x:real. x ∈ k ⇒ x ≤ b",
				Derive(func(b *Argument) {
					b.Take(bound)
					x := b.FixAs[Real]()
					in := b.Assume()
					sized := b.Have(
						"x has size at most B",
						"|x| ≤ B",
						By(size.At(x), in))
					b.Show(
						"a real of size at most B is at most B",
						ByArith(sized))
				}))
			closed := a.Have(
				"the line is Hausdorff, so the compact set k is closed",
				"closed_in(real_topology, k)",
				By(parts[0], compact.CompactClosed.Read(RealTopology).At(k), RealHausdorff))
			a.Do(SplitConj(
				Case(
					"a non-empty closed set bounded above holds its supremum",
					By(SupClosedAttained.At(k), closed, parts[1], above)),
				Case(
					"and every member lies at or below the supremum",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						in := b.Assume()
						b.Show(
							"a member of a set bounded above is at most its supremum",
							By(real_sup_inf.MemberLessEqSup.At(k, x), above, in))
					})),
			))
		}),
})}

// InfCompactAttained — a non-empty compact set of reals holds its
// infimum, which is then its least element: SupCompactAttained's mirror,
// the set bounded below by −B.
var InfCompactAttained = infCompactAttainedThm{family.Add(registry.ProofEntry{
	Name: "InfCompactAttained",
	Key:  "prop_f394c508aa8d7296",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(real).",
		Hypotheses: []string{
			"compact_in(real_topology, k)",
			"k ≠ ∅",
		},
		Conclusion: "inf(k) ∈ k ∧ (∀x:real. x ∈ k ⇒ inf(k) ≤ x)",
	},
		func(a *Argument, k *Expr[Set[Real]], given Fact) {
			parts := a.Conjuncts(
				given,
				"k is compact",
				"k is non-empty")
			_, size := a.ObtainAs[Real](
				"a compact set is bounded: some B bounds the size of its points",
				"∃B:real. ∀x:real. x ∈ k ⇒ |x| ≤ B",
				By(CompactBounded.At(k), parts[0]))
			below := a.Have(
				"so k is bounded below, by −B",
				"∃b:real. ∀x:real. x ∈ k ⇒ b ≤ x",
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Real]("-B"))
					x := b.FixAs[Real]()
					in := b.Assume()
					sized := b.Have(
						"x has size at most B",
						"|x| ≤ B",
						By(size.At(x), in))
					b.Show(
						"a real of size at most B is at least −B",
						ByArith(sized))
				}))
			closed := a.Have(
				"the line is Hausdorff, so the compact set k is closed",
				"closed_in(real_topology, k)",
				By(parts[0], compact.CompactClosed.Read(RealTopology).At(k), RealHausdorff))
			a.Do(SplitConj(
				Case(
					"a non-empty closed set bounded below holds its infimum",
					By(InfClosedAttained.At(k), closed, parts[1], below)),
				Case(
					"and every member lies at or above the infimum",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						in := b.Assume()
						b.Show(
							"a member of a set bounded below is at least its infimum",
							By(real_sup_inf.InfLessEqMember.At(k, x), below, in))
					})),
			))
		}),
})}
