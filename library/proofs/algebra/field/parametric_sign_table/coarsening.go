// coarsening.go — a sign table coarsened to the cuts where one of its first
// members vanishes: between two such cuts no nonzero one of those members
// has a root, so each keeps one sign there.

package parametric_sign_table

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_sign_table"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/registry"
)

// VanishingCutsTable — the cuts of a sign table at which one of its first m
// members that is a nonzero polynomial over the carrier vanishes, listed in
// increasing order by e, carry a sign table of those m members. On a listed
// cut a member has the sign it has there in the old table. Every root of a
// nonzero member is a listed cut, so between two listed cuts none of them
// has a root, and each keeps the sign it has on the old open cell just past
// the lower one; a zero member has sign zero throughout. Which members are
// zero is read off t at cell 0: that cell is open, and a polynomial with
// sign zero on an open cell is the zero polynomial (VanishingOnOpenCell), so
// the listed cuts are fixed by t alone.
var VanishingCutsTable = vanishingCutsTableThm{family.Add(registry.ProofEntry{
	Name: "VanishingCutsTable",
	Key:  "prop_b62cb8df9bea4fe3",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀M m:num. " +
			"∀f:(num → num → A). " +
			"∀k:num. " +
			"∀r:(num → A). " +
			"∀t:(num → num → int). " +
			"∀q:num. " +
			"∀e:(num → num).",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"polynomial_family_sign_table(F, lt, M, f, k, r, t)",
			"m ≤ M",
			"∀i:num. i < m ⇒ polynomial_over(F.zero, F.carrier, f(i))",
			"∀a b:num. a < b ∧ b < q ⇒ e(a) < e(b)",
			"∀a:num. a < q ⇒ «vanishing»(m, k, t, e(a))",
			"∀l:num. «vanishing»(m, k, t, l) ⇒ ∃a:num. a < q ∧ e(a) = l",
		},
		Conclusion: "polynomial_family_sign_table(F, lt, m, f, q, λa:num. r(e(a)), «coarse»(t, e))",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		M, m *Expr[Nat],
		f *Arrow[Nat, Fun[Nat, A]],
		k *Expr[Nat],
		r *Arrow[Nat, A],
		t *Arrow2[Nat, Nat, Int],
		q *Expr[Nat],
		e *Arrow[Nat, Nat],
		closed, table, mLe, polynomials, ordering, vanish, listed Fact,
	) {
		ordered := real_closed_field.OrderedFieldOn.Read(closed)
		parts := a.Conjuncts(
			a.Unfolded(table, polynomial_sign_table.PolynomialFamilySignTableDef),
			"the cuts increase in the carrier",
			"every cell is nonempty",
			"each member keeps the sign t(j, i) on cell j")
		oldCuts, nonempty, rows := parts[0], parts[1], parts[2]
		bounds := a.Conjuncts(
			a.Unfolded(oldCuts, ordered_field.IncreasingCutsDef),
			"the cuts lie in the carrier",
			"the cuts increase")
		cutsIn, increasing := bounds[0], bounds[1]
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
		transitive := ordered_field.Transitive.Read(ordered).AsFact()
		irreflexive := ordered_field.Irreflexive.Read(ordered).AsFact()
		signValues := ordered_field.SignValues.Read(ordered).AsFact()
		zero := a.MemberOf[on.Any](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		zeroSign := a.Have(
			"zero has the sign zero",
			"ordered_sign(F, lt, F.zero) = &0",
			By(zero, signValues.At(zero)))
		cuts := a.TermAs[Fun[Nat, A]]("λa:num. r(e(a))")
		arithmetic := a.Have(
			"2 · 0 = 0 and 0 ≤ k",
			"2 * 0 = 0 ∧ 0 ≤ k ∧ 0 ≤ 2 * k",
			ByArith())
		w, firstPoint := a.ObtainAs[A](
			"a point w of the old cell 0",
			"∃w:A. w ∈ polynomial_sign_cell(F, lt, k, r, 0)",
			BySets(nonempty, arithmetic))
		zeroMember := a.Have(
			"one of the first m members is the zero polynomial exactly when its sign on cell 0 is zero",
			"∀i:num. i < m ⇒ (f(i) = vec_zero ⇔ t(0, i) = &0)",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				iLt := b.Assume()
				iM := b.Have(
					"i indexes a member of the old table",
					"i < M",
					ByArith(iLt, mLe))
				wIn := b.Have(
					"w lies in the carrier",
					"w ∈ F.carrier",
					By(firstPoint, polynomial_sign_table.SignCellInCarrier.At(F, lt, k, r, b.TermAs[Nat]("0"), w)))
				first := b.Have(
					"f(i) has the sign t(0, i) at w",
					"ordered_sign(F, lt, polynomial_eval(f(i), w)) = t(0, i)",
					By(rows.At(b.TermAs[Nat]("0"), i, w), arithmetic, iM, firstPoint))
				b.Iff()
				b.Forward(
					"the zero polynomial vanishes at w",
					func(c *Argument, isZero Fact) {
						c.Show(
							"so its sign there is zero",
							By(
								Normalized,
								first,
								isZero,
								zeroSign,
								polynomial_evaluation.EvalVecZero.Read(ring).At(c.MemberOf[on.Any](w, wIn))))
					})
				b.Backward(
					"sign zero on the open cell 0 makes f(i) the zero polynomial",
					func(c *Argument, zeroFirst Fact) {
						c.Show(
							"by VanishingOnOpenCell",
							By(
								polynomial_sign_table.VanishingOnOpenCell.At(F, lt, M, f, k, r, t, i, c.TermAs[Nat]("0")),
								ordered,
								table,
								iM,
								polynomials.At(i),
								iLt,
								arithmetic,
								zeroFirst))
					})
			}))
		rootsAtCuts := a.Have(
			"a root of a nonzero one of the first m members is a listed cut",
			Statement{
				Binders: "∀i:num. ∀x:A.",
				Hypotheses: []string{
					"i < m",
					"¬(t(0, i) = &0)",
					"x ∈ F.carrier",
					"polynomial_eval(f(i), x) = F.zero",
				},
				Conclusion: "∃c:num. c < q ∧ x = r(e(c))",
			},
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"i indexes one of the first m members",
					"f(i) is not zero",
					"x lies in the carrier",
					"f(i) vanishes at x")
				iM := b.Have(
					"i indexes a member of the old table",
					"i < M",
					ByArith(given[0], mLe))
				j, placed := b.UnpackAs[Nat](
					GroupPremises(ordered, oldCuts, given[2], polynomial_sign_table.SignCellsCover.At(F, lt, k, r, x)),
					"j")
				jParts := b.Conjuncts(
					placed,
					"j is at most 2k",
					"x lies in old cell j")
				zeroHere := b.Have(
					"so f(i) has the sign zero on old cell j",
					"t(j, i) = &0",
					By(rows.At(j, i, x), jParts[0], iM, jParts[1], given[3], zeroSign))
				b.Do(GroupPremises(jParts[0], nat_parity.DoubleOrSucDoubleBelow.At(k, j)).SplitDisj(
					LeftHolds(
						"an open cell: f(i) would be the zero polynomial",
						Given(func(c *Argument, even Fact) {
							l, shape := c.UnpackAs[Nat](even, "l")
							c.Show(
								"contradicting t(0, i) ≠ 0",
								By(
									polynomial_sign_table.VanishingOnOpenCell.At(F, lt, M, f, k, r, t, i, l),
									ordered,
									table,
									iM,
									polynomials.At(i),
									given[0],
									shape,
									zeroHere,
									zeroMember.At(i),
									given[1]))
						})),
					RightHolds(
						"a cut cell: x is an old cut where f(i) vanishes, so a listed cut",
						Given(func(c *Argument, odd Fact) {
							l, index := c.UnpackAs[Nat](odd, "l")
							atCut := c.Have(
								"x is the old cut r(l)",
								"x = r(l)",
								By(Normalized, jParts[1], index, polynomial_sign_table.CutCellMember.At(F, lt, k, r, l, x)))
							isVanishing := c.Have(
								"f(i) vanishes at the old cut r(l)",
								"«vanishing»(m, k, t, l)",
								By(index, given[0], given[1], zeroHere))
							c.Show(
								"so r(l) is listed",
								By(listed.At(l), isVanishing, atCut))
						}))))
			}))
		coarseIn := a.Have(
			"the listed cuts lie in the carrier",
			"∀c:num. c < q ⇒ r(e(c)) ∈ F.carrier",
			By(vanish, cutsIn))
		coarseIncreasing := a.Have(
			"the listed cuts increase",
			"∀c d:num. c < d ∧ d < q ⇒ lt(r(e(c)), r(e(d)))",
			By(ordering, vanish, increasing))
		reflect := a.Have(
			"the listed cuts reflect their order to their indices",
			"∀c d:num. c < q ∧ d < q ∧ lt(r(e(c)), r(e(d))) ⇒ c < d",
			Derive(func(b *Argument) {
				c := b.FixAs[Nat]("c")
				d := b.FixAs[Nat]("d")
				given := b.Conjuncts(
					b.Assume(),
					"c is a listed index",
					"d is a listed index",
					"the c-th listed cut lies below the d-th")
				cIn := b.Have(
					"the c-th listed cut lies in the carrier",
					"r(e(c)) ∈ F.carrier",
					By(coarseIn.At(c), given[0]))
				dIn := b.Have(
					"the d-th listed cut lies in the carrier",
					"r(e(d)) ∈ F.carrier",
					By(coarseIn.At(d), given[1]))
				distinct := b.Have(
					"irreflexivity separates the indices",
					"¬(c = d)",
					By(given[2], irreflexive.At(b.TermAs[A]("r(e(c))")), cIn))
				notAfter := b.Have(
					"d before c would put the d-th cut below the c-th as well",
					"¬(d < c)",
					By(
						given[0],
						given[2],
						coarseIncreasing.At(d, c),
						transitive.At(b.TermAs[A]("r(e(c))"), b.TermAs[A]("r(e(d))"), b.TermAs[A]("r(e(c))")),
						irreflexive.At(b.TermAs[A]("r(e(c))")),
						cIn,
						dIn))
				b.Show(
					"so c comes first",
					ByArith(distinct, notAfter))
			}))
		openRows := a.Have(
			"between listed cuts each of the first m members has the sign it has just past the lower one",
			Statement{
				Binders: "∀c i:num. ∀x:A.",
				Hypotheses: []string{
					"c ≤ q",
					"i < m",
					"x ∈ polynomial_sign_cell(F, lt, q, λa:num. r(e(a)), 2 * c)",
				},
				Conclusion: "ordered_sign(F, lt, polynomial_eval(f(i), x)) = " +
					"t(COND(c = 0, 0, 2 * e(c - 1) + 2), i)",
			},
			Derive(func(b *Argument) {
				c := b.FixAs[Nat]("c")
				i := b.FixAs[Nat]("i")
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"c indexes an open coarse cell",
					"i indexes one of the first m members",
					"x lies in the open coarse cell 2c")
				iM := b.Have(
					"i indexes a member of the old table",
					"i < M",
					ByArith(given[1], mLe))
				reference := b.TermAs[Nat]("COND(c = 0, 0, 2 * e(c - 1) + 2)")
				referenceCell := b.Have(
					"the old cell just past the lower listed cut is an open cell of the old table",
					"COND(c = 0, 0, 2 * e(c - 1) + 2) ≤ 2 * k",
					Derive(func(d *Argument) {
						d.Cases(d.TermAs[Bool]("c = 0"))
						d.When(
							"the first coarse cell starts at old cell 0",
							func(g *Argument, first Fact) {
								g.Show(
									"0 ≤ 2k",
									ByArith(first))
							})
						d.Otherwise(
							"a later coarse cell starts past the listed cut r(e(c − 1))",
							func(g *Argument, later Fact) {
								listedIndex := g.Have(
									"c − 1 is a listed index",
									"c - 1 < q",
									ByArith(later, given[0]))
								previous := g.Have(
									"e(c − 1) is an old cut index",
									"e(c - 1) < k",
									By(vanish.At(g.TermAs[Nat]("c - 1")), listedIndex))
								g.Show(
									"2e(c − 1) + 2 ≤ 2k",
									ByArith(later, previous))
							})
					}))
				y, yIs := b.ObtainAs[A](
					"a point y of the old cell just past the lower listed cut, which lies in the coarse cell",
					"∃y:A. "+
						"    y ∈ polynomial_sign_cell(F, lt, k, r, COND(c = 0, 0, 2 * e(c - 1) + 2)) ∧ "+
						"    y ∈ polynomial_sign_cell(F, lt, q, λa:num. r(e(a)), 2 * c)",
					Derive(func(d *Argument) {
						d.Cases(d.TermAs[Bool]("c = 0"))
						d.When(
							"the first coarse cell holds the points of old cell 0",
							func(g *Argument, first Fact) {
								wIn := g.Have(
									"w lies in the carrier, below r(0) when there is a cut",
									"w ∈ F.carrier ∧ (0 = k ∨ lt(w, r(0)))",
									By(
										Normalized,
										firstPoint,
										arithmetic,
										polynomial_sign_table.OpenCellMember.At(F, lt, k, r, g.TermAs[Nat]("0"), w)))
								upper := g.Have(
									"so w lies below the first listed cut, if any",
									"0 = q ∨ lt(w, r(e(0)))",
									Derive(func(h *Argument) {
										some := h.Unless(
											h.TermAs[Bool]("0 = q"),
											"no listed cut",
											Given(func(v *Argument, none Fact) {
												v.Show(
													"nothing to stay below",
													By(none))
											}))
										positive := h.Have(
											"there is a listed cut",
											"0 < q",
											ByArith(some))
										firstIndex := h.Have(
											"the first listed cut is an old cut",
											"e(0) < k",
											By(vanish.At(h.TermAs[Nat]("0")), positive))
										someCut := h.Have(
											"so there is an old cut",
											"0 < k ∧ ¬(0 = k)",
											ByArith(firstIndex))
										firstOrLater := h.Have(
											"the first listed cut is r(0) or a later old cut",
											"e(0) = 0 ∨ 0 < e(0)",
											ByArith())
										atOrAbove := h.Have(
											"r(0) is at or below r(e(0))",
											"r(0) = r(e(0)) ∨ lt(r(0), r(e(0)))",
											By(Normalized, firstOrLater, firstIndex, increasing.At(h.TermAs[Nat]("0"), h.TermAs[Nat]("e(0)"))))
										wBelow := h.Have(
											"w lies below r(0)",
											"lt(w, r(0))",
											By(wIn, someCut))
										bothIn := h.Have(
											"r(0) and r(e(0)) lie in the carrier",
											"r(0) ∈ F.carrier ∧ r(e(0)) ∈ F.carrier",
											By(cutsIn.At(h.TermAs[Nat]("0")), cutsIn.At(h.TermAs[Nat]("e(0)")), someCut, firstIndex))
										h.Show(
											"by transitivity",
											By(
												Normalized,
												wBelow,
												atOrAbove,
												bothIn,
												wIn,
												transitive.At(w, h.TermAs[A]("r(0)"), h.TermAs[A]("r(e(0))"))))
									}))
								g.Take(w)
								g.Show(
									"w lies in both cells",
									By(
										firstPoint,
										first,
										wIn,
										upper,
										given[0],
										polynomial_sign_table.OpenCellMember.At(F, lt, q, cuts, c, w)))
							})
						d.Otherwise(
							"a later coarse cell holds the old open cell just past the listed cut r(e(c − 1))",
							func(g *Argument, later Fact) {
								listedIndex := g.Have(
									"c − 1 is a listed index",
									"c - 1 < q",
									ByArith(later, given[0]))
								previous := g.Have(
									"e(c − 1) is an old cut index",
									"e(c - 1) < k",
									By(vanish.At(g.TermAs[Nat]("c - 1")), listedIndex))
								next := g.TermAs[Nat]("e(c - 1) + 1")
								nextIndex := g.Have(
									"the old open cell just past r(e(c − 1)) has index e(c − 1) + 1",
									"e(c - 1) + 1 ≤ k ∧ "+
										"2 * (e(c - 1) + 1) ≤ 2 * k ∧ "+
										"¬(e(c - 1) + 1 = 0) ∧ "+
										"e(c - 1) + 1 - 1 = e(c - 1) ∧ "+
										"COND(c = 0, 0, 2 * e(c - 1) + 2) = 2 * (e(c - 1) + 1)",
									ByArith(previous, later))
								u, uNext := g.ObtainAs[A](
									"a point u of that old open cell",
									"∃u:A. u ∈ polynomial_sign_cell(F, lt, k, r, 2 * (e(c - 1) + 1))",
									BySets(nonempty, nextIndex))
								uOpen := g.Have(
									"u lies above r(e(c − 1)), and below r(e(c − 1) + 1) unless there is no such cut",
									"u ∈ F.carrier ∧ lt(r(e(c - 1)), u) ∧ (e(c - 1) + 1 = k ∨ lt(u, r(e(c - 1) + 1)))",
									By(uNext, nextIndex, polynomial_sign_table.OpenCellMember.At(F, lt, k, r, next, u)))
								upper := g.Have(
									"so u lies below the listed cut r(e(c)), if c < q",
									"c = q ∨ lt(u, r(e(c)))",
									Derive(func(h *Argument) {
										h.Cases(h.TermAs[Bool]("c = q"))
										h.When(
											"the last coarse cell has no upper cut",
											func(v *Argument, last Fact) {
												v.Show(
													"nothing to stay below",
													By(last))
											})
										h.Otherwise(
											"the next listed cut r(e(c)) lies at or above r(e(c − 1) + 1)",
											func(v *Argument, notLast Fact) {
												steps := v.Have(
													"c − 1 < c < q",
													"c - 1 < c ∧ c < q",
													ByArith(later, notLast, given[0]))
												order := v.Have(
													"the listed indices increase",
													"e(c - 1) < e(c) ∧ e(c) < k",
													By(ordering.At(v.TermAs[Nat]("c - 1"), c), vanish.At(c), steps))
												bounds := v.Have(
													"so e(c − 1) + 1 is an old cut index at or below e(c)",
													"¬(e(c - 1) + 1 = k) ∧ e(c - 1) + 1 < k ∧ (e(c - 1) + 1 = e(c) ∨ e(c - 1) + 1 < e(c))",
													ByArith(order))
												atOrAbove := v.Have(
													"r(e(c − 1) + 1) is at or below r(e(c))",
													"r(e(c - 1) + 1) = r(e(c)) ∨ lt(r(e(c - 1) + 1), r(e(c)))",
													By(bounds, order, increasing.At(next, v.TermAs[Nat]("e(c)"))))
												bothIn := v.Have(
													"both cuts lie in the carrier",
													"r(e(c - 1) + 1) ∈ F.carrier ∧ r(e(c)) ∈ F.carrier",
													By(cutsIn.At(next), cutsIn.At(v.TermAs[Nat]("e(c)")), bounds, order))
												uBelow := v.Have(
													"u lies below r(e(c − 1) + 1)",
													"lt(u, r(e(c - 1) + 1))",
													By(uOpen, bounds))
												v.Show(
													"by transitivity",
													By(
														uBelow,
														atOrAbove,
														bothIn,
														uOpen,
														transitive.At(u, v.TermAs[A]("r(e(c - 1) + 1)"), v.TermAs[A]("r(e(c))"))))
											})
									}))
								g.Take(u)
								g.Show(
									"u lies in both cells",
									By(
										uNext,
										nextIndex,
										later,
										uOpen,
										upper,
										given[0],
										polynomial_sign_table.OpenCellMember.At(F, lt, q, cuts, c, u)))
							})
					}))
				yParts := b.Conjuncts(
					yIs,
					"y lies in the old reference cell",
					"y lies in the coarse cell")
				yValue := b.Have(
					"f(i) has the sign t at the reference cell at y",
					"ordered_sign(F, lt, polynomial_eval(f(i), y)) = t(COND(c = 0, 0, 2 * e(c - 1) + 2), i)",
					By(rows.At(reference, i, y), referenceCell, iM, yParts[0]))
				points := b.Have(
					"x and y lie in the carrier",
					"x ∈ F.carrier ∧ y ∈ F.carrier",
					By(
						given[2],
						yParts[1],
						polynomial_sign_table.SignCellInCarrier.At(F, lt, q, cuts, b.TermAs[Nat]("2 * c"), x),
						polynomial_sign_table.SignCellInCarrier.At(F, lt, q, cuts, b.TermAs[Nat]("2 * c"), y)))
				b.Cases(b.TermAs[Bool]("t(0, i) = &0"))
				b.When(
					"a zero member has the sign zero throughout",
					func(d *Argument, zeroFirst Fact) {
						isZero := d.Have(
							"f(i) is the zero polynomial",
							"f(i) = vec_zero",
							By(zeroMember.At(i), given[1], zeroFirst))
						d.Show(
							"so its sign is zero at x and at y",
							By(
								yValue,
								isZero,
								zeroSign,
								points,
								polynomial_evaluation.EvalVecZero.Read(ring).AsFact().At(x),
								polynomial_evaluation.EvalVecZero.Read(ring).AsFact().At(y)))
					})
				b.Otherwise(
					"a nonzero member has no root between listed cuts",
					func(d *Argument, nonzeroFirst Fact) {
						rootFree := d.Have(
							"f(i) has no root in the coarse cell",
							Statement{
								Binders: "∀z:A.",
								Hypotheses: []string{
									"z ∈ polynomial_sign_cell(F, lt, q, λa:num. r(e(a)), 2 * c)",
								},
								Conclusion: "polynomial_eval(f(i), z) ≠ F.zero",
							},
							Derive(func(g *Argument) {
								z := g.FixAs[A]("z")
								zIn := g.Assume()
								root := g.Have(
									"suppose f(i) vanished at z",
									"polynomial_eval(f(i), z) = F.zero",
									By(g.SupposeNot()))
								zOpen := g.Have(
									"z lies between the listed cuts around the coarse cell",
									"z ∈ F.carrier ∧ (c = 0 ∨ lt(r(e(c - 1)), z)) ∧ (c = q ∨ lt(z, r(e(c))))",
									By(zIn, given[0], polynomial_sign_table.OpenCellMember.At(F, lt, q, cuts, c, z)))
								_, atD := g.UnpackAs[Nat](
									GroupPremises(given[1], nonzeroFirst, zOpen, root, rootsAtCuts.At(i, z)),
									"d")
								dParts := g.Conjuncts(
									atD,
									"d is a listed index",
									"z is the d-th listed cut")
								indexFacts := g.Have(
									"c − 1 and c are listed indices unless c is 0 or q",
									"(c = 0 ∨ c - 1 < q) ∧ (c = q ∨ c < q)",
									ByArith(given[0]))
								low := g.Have(
									"d lies past c − 1",
									"c = 0 ∨ c - 1 < d",
									By(
										Normalized,
										zOpen,
										dParts[0],
										dParts[1],
										indexFacts,
										reflect.At(g.TermAs[Nat]("c - 1"), g.TermAs[Nat]("d"))))
								high := g.Have(
									"d lies before c",
									"c = q ∨ d < c",
									By(Normalized, zOpen, dParts[0], dParts[1], indexFacts, reflect.At(g.TermAs[Nat]("d"), c)))
								g.Show(
									"no listed index lies strictly between c − 1 and c",
									ByArith(low, high, dParts[0], given[0]))
							}))
						d.Show(
							"so f(i) keeps one sign on the coarse cell",
							By(
								polynomial_sign_table.RootFreeCellSign.At(F, lt, q, cuts, c, f.Apply(i), x, y),
								closed,
								coarseIn,
								given[0],
								polynomials.At(i),
								given[1],
								rootFree,
								given[2],
								yParts[1],
								yValue))
					})
			}))
		coarseRows := a.Have(
			"each of the first m members has the sign «coarse»(t, e, j, i) on the coarse cell j",
			Statement{
				Binders: "∀j i:num. ∀x:A.",
				Hypotheses: []string{
					"j ≤ 2 * q",
					"i < m",
					"x ∈ polynomial_sign_cell(F, lt, q, λa:num. r(e(a)), j)",
				},
				Conclusion: "ordered_sign(F, lt, polynomial_eval(f(i), x)) = «coarse»(t, e, j, i)",
			},
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				i := b.FixAs[Nat]("i")
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"j is a coarse cell index",
					"i indexes one of the first m members",
					"x lies in the coarse cell j")
				iM := b.Have(
					"i indexes a member of the old table",
					"i < M",
					ByArith(given[1], mLe))
				b.Do(GroupPremises(given[0], nat_parity.DoubleOrSucDoubleBelow.At(q, j)).SplitDisj(
					LeftHolds(
						"an even index names an interval between listed cuts",
						Given(func(c *Argument, even Fact) {
							cc, shape := c.UnpackAs[Nat](even, "c")
							halves := c.Have(
								"2c is even with half c, and zero only when c is",
								"nat_mod(2 * c, 2) = 0 ∧ "+
									"nat_div(2 * c, 2) = c ∧ "+
									"(2 * c = 0 ⇔ c = 0) ∧ "+
									"nat_mod(0, 2) = 0 ∧ "+
									"¬(0 = 1)",
								ByArith())
							c.Show(
								"the row of the old open cell just past the lower listed cut",
								By(openRows.At(cc, i, x), shape, halves, given[1], given[2]))
						})),
					RightHolds(
						"an odd index names a listed cut",
						Given(func(c *Argument, odd Fact) {
							cc, index := c.UnpackAs[Nat](odd, "c")
							halves := c.Have(
								"2c + 1 is odd with half c",
								"nat_mod(2 * c + 1, 2) = 1 ∧ nat_div(2 * c + 1, 2) = c",
								ByArith())
							atCut := c.Have(
								"x is the c-th listed cut",
								"x ∈ F.carrier ∧ x = r(e(c))",
								By(Normalized, given[2], index, polynomial_sign_table.CutCellMember.At(F, lt, q, cuts, cc, x)))
							oldIndex := c.Have(
								"e(c) is an old cut index",
								"e(c) < k",
								By(vanish.At(cc), index))
							oldBound := c.Have(
								"so 2e(c) + 1 is an old cell index",
								"2 * e(c) + 1 ≤ 2 * k",
								ByArith(oldIndex))
							xOld := c.Have(
								"x lies in the old cut cell 2e(c) + 1",
								"x ∈ polynomial_sign_cell(F, lt, k, r, 2 * e(c) + 1)",
								By(atCut, oldIndex, polynomial_sign_table.CutCellMember.At(F, lt, k, r, c.TermAs[Nat]("e(c)"), x)))
							c.Show(
								"the row of the old cut r(e(c))",
								By(rows.At(c.TermAs[Nat]("2 * e(c) + 1"), i, x), xOld, oldBound, iM, index, halves))
						}))))
			}))
		coarseCuts := a.Have(
			"so the listed cuts increase in the carrier",
			"increasing_cuts(F, lt, q, λa:num. r(e(a)))",
			By(coarseIn, coarseIncreasing, ordered_field.IncreasingCutsDef))
		nonemptyCoarse := a.Have(
			"every coarse cell is nonempty",
			"∀j:num. j ≤ 2 * q ⇒ polynomial_sign_cell(F, lt, q, λa:num. r(e(a)), j) ≠ ∅",
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				bound := b.Assume()
				b.Show(
					"increasing cuts have nonempty cells",
					By(polynomial_sign_table.SignCellsNonempty.At(F, lt, q, cuts, j), ordered, coarseCuts, bound))
			}))
		a.Show(
			"the listed cuts carry a sign table of the first m members",
			Simp(Fwd(polynomial_sign_table.PolynomialFamilySignTableDef)),
			By(coarseCuts, nonemptyCoarse, coarseRows))
	}),
})}
