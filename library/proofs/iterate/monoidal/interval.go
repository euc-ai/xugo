// interval.go — the fold read along a ℕ-interval `m .. n`: its recursion
// on the upper bound, and the laws every Σ or Π over an interval
// computes with. A file of its own because every carrier of a fold reads
// these laws, and reads nothing else of the chapter's ℕ.

package monoidal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The fold along an interval
// ---------------------------------------------------------------------------
//
// Each law is proved once, for every operation that folds; a carrier of a
// fold (Σ over ℕ, over ℝ, a product, …) reads each in one line at its own
// operation.

// IntervalClauses — the recursion clauses of a fold whose index set is
// an interval of numbers, recursing on the interval's upper bound
// rather than on an insert. This is the clause pair every Σ over
// `m .. n` computes with.
//
// Two recursions meet here and the proof is their composition: the
// interval chapter says what each interval IS as a set, and the fold's
// own recursion evaluates whatever set that turns out to be. The Case
// labels below carry the walkthrough.
//
// The one thing neither recursion supplies is that the new point is
// fresh — the sole place the order laws are spent, and what settles
// the recursion clause's own conditional; the `fresh` claim carries
// the argument.
//
// The recursion then hands the shed factor back on the LEFT of the
// operation where the statement wants it on the right, so the last step
// is commutativity — `MonoidalAC` is where the chapter keeps it.
//
// Note the name collision the body has to be deliberate about: the bare
// `Clauses` here is this chapter's fold recursion, while
// `num_segment.Clauses` is the interval's. Both are cited below, one
// per half of the argument.
var IntervalClauses = intervalClausesThm{family.Add(registry.ProofEntry{
	Name: "IntervalClauses",
	Key:  "prop_c98426d0a598184d",
	Build: MonoidalOp.Law(Statement{
		Binders: "∀f:(num → B).",
		Conclusion: "(∀m:num. iterated_op(op, m .. 0, f) = COND(m = 0, f(0), neutral_elem(op))) ∧ " +
			"(∀m n:num. " +
			"    iterated_op(op, m .. suc(n), f) = " +
			"    COND(m ≤ suc(n), op(iterated_op(op, m .. n, f), f(suc(n))), iterated_op(op, m .. n, f)))",
	},
		func(a *Argument, op *Arrow2[carrier, carrier, carrier], mon Fact, f *Arrow[Nat, carrier]) {
			zero := a.Ctx().Nat(0)

			a.Do(SplitConj(
				Case(
					"the bound 0: the interval can hold no point but 0, and "+
						"holds that one exactly when the lower bound is 0 as well",
					Derive(func(b *Argument) {
						b.FixAs[Nat]() // m — the lower bound, spelled by the statement

						b.Cases(b.Term("m = 0"))
						b.When(
							"the lower bound is 0 too, so the interval is that single point",
							func(c *Argument, isZero Fact) {
								// The interval's recursion is cited BARE at all
								// three of its uses below: it packs two clauses
								// under separate binder prefixes, so a tuple
								// would ground only part of one. Each cite's
								// instance is the claim it is proving.
								onePoint := c.Have(
									"the interval is the one-point set {0}",
									"m .. 0 = insert(0, «emptyNumbers»)",
									By(isZero, num_segment.Clauses))

								c.Show(
									"and a one-point fold is the summand read there, which is "+
										"the branch the conditional takes under the same hypothesis",
									By(
										mon,
										isZero,
										onePoint,
										// iterated_op(op, {0}, f) = f(0)
										Sing.At(op, f, zero)))
							})
						b.Otherwise(
							"the lower bound is past 0, so the interval is empty and the fold never starts",
							func(c *Argument, notZero Fact) {
								empty := c.Have(
									"the interval holds nothing",
									"m .. 0 = «emptyNumbers»",
									By(notZero, num_segment.Clauses))

								c.Show(
									"folding nothing returns the neutral — the recursion's "+
										"∅ clause — and that is the branch the conditional takes",
									// The fold's own recursion, bare for the reason
									// its entry gives: its inner binders hoist out
									// from under `monoidal_op(op) ⇒`, leaving nothing a
									// full tuple could ground.
									By(Normalized, mon, notZero, empty, Clauses))
							})
					})),

				Case(
					"the bound raised to suc n: the interval either "+
						"gains that one further point or does not grow at all",
					Derive(func(b *Argument) {
						m := b.FixAs[Nat]()
						n := b.FixAs[Nat]()

						below := b.TermAs[Set[Nat]]("m .. n") // the interval before the bound is raised
						top := b.TermAs[Nat]("suc(n)")        // the point raising it can admit

						b.Cases(b.Term("m ≤ suc(n)"))
						b.When(
							"the lower bound reaches the new top, so the interval gains "+
								"exactly that point and the fold sheds its factor there",
							func(c *Argument, reaches Fact) {
								grown := c.Have(
									"with the top within reach the interval gains suc n and nothing else",
									"m .. suc(n) = insert(suc(n), m .. n)",
									// m ≤ suc(n) ⇒ m .. suc(n) = insert(suc(n), m .. n)
									By(reaches, num_segment.Rec.At(m, n)))

								fresh := c.Have(
									"and suc n was not already in it: membership below bounds "+
										"a point above by n, and no number reaches past itself",
									"suc(n) ∉ m .. n",
									By(
										// suc(n) ∈ m .. n ⇔ m ≤ suc(n) ∧ suc(n) ≤ n
										num_segment.Membership.At(top, m, n),
										// suc(n) < suc(n) ⇔ suc(n) ≤ n — the bridge that
										// turns the bound the membership law leaves into
										// a strict inequality at one and the same number.
										nat_order.LessThanSucIffLessEq.At(top, n),
										// Bare: irreflexivity's ∀-install absorbs the
										// premise obligation, so there is no instance
										// left for a witness to reach.
										nat_order.LessThanIrrefl))

								turn := c.Have(
									"so one turn of the recursion lifts the factor at suc n back out of the fold",
									"iterated_op(op, insert(suc(n), m .. n), f) = op(f(suc(n)), iterated_op(op, m .. n, f))",
									By(
										mon,
										fresh,
										// finite(m .. n) — the clause's own guard
										num_segment.Finite.At(m, n),
										// the guard-resolved insert clause, at the
										// interval below as its set and suc n as the
										// point being laid in: exactly the claim above
										OneTurn.At(op, below, top, f)))

								c.Show(
									"which is the claim once the operation is read the other way round",
									// Ground at the operation alone: the five laws bind
									// their own factors, so `op` is the whole of what a
									// caller has to say.
									By(mon, reaches, grown, turn, MonoidalAC.At(op)))
							})
						b.Otherwise(
							"the lower bound never reaches the new top, so the interval is unchanged and neither is the fold",
							func(c *Argument, misses Fact) {
								same := c.Have(
									"out of reach, the raised bound admits nothing new",
									"m .. suc(n) = m .. n",
									By(misses, num_segment.Clauses))

								c.Show(
									"so both sides fold over one and the same set",
									By(Normalized, misses, same))
							})
					})),
			))
		}),
})}

// IntervalPoint — an interval whose bounds coincide is the single point
// they name, and a fold over one point is the summand's value there.
var IntervalPoint = intervalPointThm{family.Add(registry.ProofEntry{
	Name: "IntervalPoint",
	Key:  "prop_825fec876da8310b",
	Build: MonoidalOp.Law("∀n:num. ∀f:(num → B). iterated_op(op, n .. n, f) = f(n)",
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			n *Expr[Nat],
			f *Arrow[Nat, carrier],
		) {
			a.Do(
				// ↦ iterated_op(op, {n₀}, f₀) = f₀(n₀): the interval as its one point
				Simp(Fwd(num_segment.Sing)))
			a.Show(
				"a fold over one point is the summand's value there",
				By(mon, Sing.At(op, f, n)))
		}),
})}

// PeelLeft — the lowest point of a non-empty interval comes off the
// front of its fold. The point shed is new to what remains because
// nothing above the lower bound is the lower bound.
var PeelLeft = peelLeftThm{family.Add(registry.ProofEntry{
	Name: "PeelLeft",
	Key:  "prop_721c7ca2b944f578",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀m n:num. ∀f:(num → B).",
			Hypotheses: []string{
				"m ≤ n",
			},
			Conclusion: "iterated_op(op, m .. n, f) = op(f(m), iterated_op(op, m + 1 .. n, f))",
		},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			m, n *Expr[Nat],
			f *Arrow[Nat, carrier],
			reaches Fact,
		) {
			above := a.TermAs[Nat]("m + 1")
			rest := a.TermAs[Set[Nat]]("m + 1 .. n")

			peel := a.Have(
				"the interval is its lowest point together with what lies above it",
				"m .. n = insert(m, m + 1 .. n)",
				By(reaches, num_segment.RecLeft.At(m, n)))
			a.Do(peel.Rw())

			fresh := a.Have(
				"and that point is not among what lies above it",
				"m ∉ m + 1 .. n",
				By(nat_arith.Add1, nat_order.SucLessEqIffLessThan, nat_order.LessThanIrrefl))
			a.Show(
				"so one turn of the recursion sheds exactly the value there",
				By(mon, fresh, num_segment.Finite.At(above, n), OneTurn.At(op, rest, m, f)))
		}),
})}

// PeelRight — and the highest point comes off the back, which needs the
// interval to have a highest point at all: past 0 the upper bound is one
// more than something, and that something is where the rest of the
// interval stops. The recursion hands the shed value back on the LEFT of
// the operation, where a fold read to its top wants it on the right, so
// the last thing spent is commutativity.
var PeelRight = peelRightThm{family.Add(registry.ProofEntry{
	Name: "PeelRight",
	Key:  "prop_91dcfad662bf09eb",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀n m:num. ∀f:(num → B).",
			Hypotheses: []string{
				"0 < n",
				"m ≤ n",
			},
			Conclusion: "iterated_op(op, m .. n, f) = op(iterated_op(op, m .. n - 1, f), f(n))",
		},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			n, m *Expr[Nat],
			f *Arrow[Nat, carrier],
			bounds Fact,
		) {
			previous := a.TermAs[Nat]("n - 1")
			rest := a.TermAs[Set[Nat]]("m .. n - 1")

			peel := a.Have(
				"the interval is its highest point together with what lies below it",
				"m .. n = insert(n, m .. n - 1)",
				By(bounds, num_segment.RecRight.At(m, n)))
			a.Do(peel.Rw())

			fresh := a.Have(
				"and that point is not among what lies below it",
				"n ∉ m .. n - 1",
				By(
					bounds,
					num_segment.Membership.At(n, m, previous),
					nat_monus.SucOfSubOne,
					nat_order.PosIffNonzero,
					nat_order.SucLessEqIffLessThan,
					nat_order.LessThanIrrefl))
			a.Show(
				"so one turn of the recursion sheds exactly the value there, on the other side of the operation",
				By(mon, fresh, num_segment.Finite.At(m, previous), OneTurn.At(op, rest, n, f), MonoidalAC.At(op)))
		}),
})}

// Shift — moving every index of a fold up by p moves its interval up by
// p. The shifted interval is the image of the original under the shift,
// and the shift tells its points apart, so reindexing reads one fold as
// the other.
var Shift = shiftThm{family.Add(registry.ProofEntry{
	Name: "Shift",
	Key:  "prop_9c5f36a19ca21d56",
	Build: MonoidalOp.Law(
		"∀m n p:num. ∀f:(num → B). "+
			"    iterated_op(op, m .. n, λi:num. f(i + p)) = iterated_op(op, m + p .. n + p, f)",
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			m, n, p *Expr[Nat],
			f *Arrow[Nat, carrier],
		) {
			source := a.TermAs[Set[Nat]]("m .. n")
			shift := a.TermAs[Fun[Nat, Nat]]("λi:num. i + p")

			// m + p .. n + p ↦ image(λi:num. i + p, m .. n)
			a.Do(Simp(Fwd(num_segment.OffsetImage)))

			composed := a.Have(
				"reading the summand after the shift is reading the shifted summand",
				"f ∘ (λi:num. i + p) = (λi:num. f(i + p))",
				Unfold(functions.ComposeApply))
			apart := a.Have(
				"the shift tells the points of m .. n apart: i + p = j + p only where i = j",
				"injective_on(m .. n, λi:num. i + p)",
				Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]()))),
				By(nat_arith.AddEqLCancel, nat_arith.AddSym))
			a.Show(
				"so the two readings are one fold, the shift telling its points apart",
				By(mon, composed, apart, Image.At(op, shift, f, source)))
		}),
})}

// IntervalCongruence — two summands agreeing between the bounds have the
// same fold. What the general law asks about the points of the index
// set, the interval's membership law states about the bounds.
var IntervalCongruence = intervalCongruenceThm{family.Add(registry.ProofEntry{
	Name: "IntervalCongruence",
	Key:  "prop_6fb86ff4365e796d",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀m n:num. ∀f g:(num → B).",
			Hypotheses: []string{
				"∀i:num. m ≤ i ∧ i ≤ n ⇒ f(i) = g(i)",
			},
			Conclusion: "iterated_op(op, m .. n, f) = iterated_op(op, m .. n, g)",
		},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			m, n *Expr[Nat],
			f, g *Arrow[Nat, carrier],
			agree Fact,
		) {
			a.Show(
				"the bounds say which points the index set holds",
				By(mon, agree, Congruence))
		}),
})}

// IntervalEvenOdd — a fold over an interval from 0 to an odd bound splits
// by the parity of the index, into the fold over the even points and the
// fold over the odd ones. By induction on n. At 0 the interval is the even
// point 0 and the odd point 1. Raising n by one puts two points on top of
// the interval, 2(n + 1) and 2(n + 1) + 1, and these are exactly the points
// raising n adds to the even fold and to the odd one. Peeling the two
// points off, splitting what is left by the hypothesis and swapping the
// middle two of the four factors puts each new value next to its own fold.
var IntervalEvenOdd = intervalEvenOddThm{family.Add(registry.ProofEntry{
	Name: "IntervalEvenOdd",
	Key:  "prop_82d53ff07d2a4da4",
	Build: MonoidalOp.Law(
		"∀n:num. ∀f:(num → B). "+
			"    iterated_op(op, 0 .. 2 * n + 1, f) = "+
			"    op(iterated_op(op, 0 .. n, λk:num. f(2 * k)), iterated_op(op, 0 .. n, λk:num. f(2 * k + 1)))",
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			n *Expr[Nat],
			f *Arrow[Nat, carrier],
		) {
			zero := a.Ctx().Nat(0)
			evens := a.TermAs[Fun[Nat, carrier]]("λk:num. f(2 * k)")
			odds := a.TermAs[Fun[Nat, carrier]]("λk:num. f(2 * k + 1)")

			a.Induct(n)
			a.Base(
				"n = 0: the interval 0 .. 1 is the even point 0 and the "+
					"odd point 1, and a fold over 0 .. 0 is its one value",
				ByArith(
					mon,
					PeelRight.At(op, a.TermAs[Nat]("2 * 0 + 1"), zero, f),
					IntervalPoint.At(op, zero, f),
					IntervalPoint.At(op, zero, evens),
					IntervalPoint.At(op, zero, odds)))
			a.Step(
				"n → suc n: the interval gains the points 2·suc n and 2·suc "+
					"n + 1, the new tops of the even fold and of the odd one",
				func(b *Argument, ih Fact) {
					even := b.TermAs[Nat]("2 * suc(n)")
					odd := b.TermAs[Nat]("2 * suc(n) + 1")
					evenFold := b.TermAs[carrier]("iterated_op(op, 0 .. n, λk:num. f(2 * k))")
					oddFold := b.TermAs[carrier]("iterated_op(op, 0 .. n, λk:num. f(2 * k + 1))")

					next := b.Have(
						"the new even point is the one after the old top",
						"2 * suc(n) = suc(2 * n + 1)",
						ByArith())
					interchange := b.Have(
						"the operation interchanges the middle two of four factors",
						"∀x y u v:B. op(op(op(x, y), u), v) = op(op(x, u), op(y, v))",
						By(mon, MonoidalAC.At(op)))

					b.Show(
						"peel the two new points off the top, split the rest by the "+
							"hypothesis, and hand each new point to the fold of its parity",
						CalcEq(
							Leg(
								b.TermAs[carrier]("op(iterated_op(op, 0 .. 2 * suc(n), f), f(2 * suc(n) + 1))"),
								"peel the top point, 2·suc n + 1, off the interval",
								By(
									mon,
									IntervalClauses.At(op, f),
									nat_arith.Add1.At(even),
									nat_order.ZeroLessEq.At(b.TermAs[Nat]("suc(2 * suc(n))")))),
							Leg(
								b.TermAs[carrier]("op(op(iterated_op(op, 0 .. 2 * n + 1, f), f(2 * suc(n))), f(2 * suc(n) + 1))"),
								"then the point below it, 2·suc n, which is the successor of the old top 2n + 1",
								By(mon, next, IntervalClauses.At(op, f), nat_order.ZeroLessEq.At(even))),
							Leg(
								b.TermAs[carrier](
									"op(op(op(iterated_op(op, 0 .. n, λk:num. f(2 * k)), "+
										"            iterated_op(op, 0 .. n, λk:num. f(2 * k + 1))), "+
										"        f(2 * suc(n))), "+
										"    f(2 * suc(n) + 1))"),
								"the hypothesis splits the interval up to the old top by parity",
								By(ih)),
							Leg(
								b.TermAs[carrier](
									"op(op(iterated_op(op, 0 .. n, λk:num. f(2 * k)), f(2 * suc(n))), "+
										"    op(iterated_op(op, 0 .. n, λk:num. f(2 * k + 1)), f(2 * suc(n) + 1)))"),
								"swap the middle two factors, so each new value stands next to the fold of its parity",
								By(interchange.At(evenFold, oddFold, f.Apply(even), f.Apply(odd)))),
							FinalLeg(
								"where it is that fold's value at suc n, the new top point of 0 .. suc n",
								By(
									mon,
									IntervalClauses.At(op, evens),
									IntervalClauses.At(op, odds),
									nat_order.ZeroLessEq.At(b.TermAs[Nat]("suc(n)")))),
						))
				})
		}),
})}
