// interval.go — Σ read over a segment `m .. n`. An indexed series is
// written that way and not as a sum over an abstract index set, so
// every law the chapter has proved has to be available in this form;
// supplying them is what this file is for.
//
// Two parts, each under a banner that carries the method its members
// share: the chapter's laws read over an interval, and then the series
// tools — the telescope, summation by parts as its corollary, Abel's
// inequality, and a sum over a triangle taken in its two orders.
//
// Closes marked `Normalized` land by simplification once the cited law
// is read at the goal's own point; the marker records that no
// refutation is wanted.

package real_sum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The chapter's laws, read over an interval
// ---------------------------------------------------------------------------
//
// Almost nothing here is a new theorem about sums. The recursion on the
// upper bound, the sum over one point, peeling either end off, shifting
// the indices, agreeing between the bounds and splitting by parity are
// the fold mechanism's interval laws, each read here at real addition in
// one line — unfolding `real_sum` turns the goal into a statement about
// the fold this one is.
//
// The rest take a law of the chapter proved of an arbitrary index set
// and read it at `m .. n`, the interval chapter supplying what the law
// asks of its index set — that it is finite, or which points it holds.
// Cutting an interval in two rewrites it into the shape a law of the
// chapter is stated over. Lengthening one either leaves the interval
// alone and silences the summand on the extension, so that the chapter's
// law about a summand vanishing off the index set applies, or, where the
// terms the extension adds are nonnegative, reads the shorter interval as
// a subset of the longer, so that the chapter's law for a subset compares
// the two sums.

// IntervalClauses — how a sum over an interval computes. Against an
// upper bound of 0 the interval holds nothing unless the lower bound
// is 0 as well; raising the bound by one adds the new point's value,
// or, where the bound has not yet reached the lower one, changes
// nothing.
var IntervalClauses = intervalClausesThm{family.Add(registry.ProofEntry{
	Name: "IntervalClauses",
	Key:  "prop_65b382ec7a8e5bd6",
	Build: family.Theorem(
		"∀m n:num. ∀f:(num → real). "+
			"    sum(m .. 0, f) = COND(m = 0, f(0), &0) ∧ "+
			"    sum(m .. suc(n), f) = COND(m ≤ suc(n), sum(m .. n, f) + f(suc(n)), sum(m .. n, f))",
		func(a *Argument) {
			a.Do(Unfold(RealSumDef),
				By(monoidal.IntervalClauses, real_ring.MonoidalAdd, real_ring.NeutralAdd))
		}),
})}

// IntervalPoint — a sum over an interval whose bounds coincide is the
// summand's value at the point they name.
var IntervalPoint = intervalPointThm{family.Add(registry.ProofEntry{
	Name: "IntervalPoint",
	Key:  "prop_a0ce5990482c38e5",
	Build: family.Theorem("∀n:num. ∀f:(num → real). sum(n .. n, f) = f(n)",
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.IntervalPoint, real_ring.MonoidalAdd))
		}),
})}

// PeelLeft — the lowest point of a non-empty interval comes off the
// front of its sum.
var PeelLeft = peelLeftThm{family.Add(registry.ProofEntry{
	Name: "PeelLeft",
	Key:  "prop_94a26cc27acbad0b",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num. ∀f:(num → real).",
		Hypotheses: []string{
			"m ≤ n",
		},
		Conclusion: "sum(m .. n, f) = f(m) + sum(m + 1 .. n, f)",
	},
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.PeelLeft, real_ring.MonoidalAdd))
		}),
})}

// PeelRight — and the highest point off the back, once the interval
// reaches past 0.
var PeelRight = peelRightThm{family.Add(registry.ProofEntry{
	Name: "PeelRight",
	Key:  "prop_2a84d51ddfbd6d77",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀f:(num → real).",
		Hypotheses: []string{
			"0 < n",
			"m ≤ n",
		},
		Conclusion: "sum(m .. n, f) = sum(m .. n - 1, f) + f(n)",
	},
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.PeelRight, real_ring.MonoidalAdd))
		}),
})}

// IntervalCongruence — two summands agreeing between the bounds have
// the same sum.
var IntervalCongruence = intervalCongruenceThm{family.Add(registry.ProofEntry{
	Name: "IntervalCongruence",
	Key:  "prop_c939aa01cedf5309",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num. ∀f g:(num → real).",
		Hypotheses: []string{
			"∀i:num. m ≤ i ∧ i ≤ n ⇒ f(i) = g(i)",
		},
		Conclusion: "sum(m .. n, f) = sum(m .. n, g)",
	},
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.IntervalCongruence, real_ring.MonoidalAdd))
		}),
})}

// Shift — moving the summand's argument by a fixed amount is moving the
// interval by that amount.
var Shift = shiftThm{family.Add(registry.ProofEntry{
	Name: "Shift",
	Key:  "prop_d64bcb2156084762",
	Build: family.Theorem("∀m n p:num. ∀f:(num → real). "+
		"    sum(m .. n, λi:num. f(i + p)) = sum(m + p .. n + p, f)",
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.Shift, real_ring.MonoidalAdd))
		}),
})}

// IntervalEvenOdd — a sum from 0 to an odd bound splits by the parity
// of the index, into the sum of the even-indexed terms and the sum of
// the odd-indexed ones.
var IntervalEvenOdd = intervalEvenOddThm{family.Add(registry.ProofEntry{
	Name: "IntervalEvenOdd",
	Key:  "prop_f31e0cfe9abcff45",
	Build: family.Theorem("∀n:num. ∀f:(num → real). "+
		"    sum(0 .. 2 * n + 1, f) = sum(0 .. n, λk:num. f(2 * k)) + sum(0 .. n, λk:num. f(2 * k + 1))",
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.IntervalEvenOdd, real_ring.MonoidalAdd))
		}),
})}

// IntervalEqZero — a summand vanishing between the bounds sums to
// zero: what the chapter's vanishing law asks about the points of the
// index set, the interval's membership law states about the bounds.
var IntervalEqZero = intervalEqZeroThm{family.Add(registry.ProofEntry{
	Name: "IntervalEqZero",
	Key:  "prop_dfa9f9fdad1ea4c0",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:num. ∀f:(num → real).",
			Hypotheses: []string{
				"∀i:num. m ≤ i ∧ i ≤ n ⇒ f(i) = &0",
			},
			Conclusion: "sum(m .. n, f) = &0",
		},
		func(a *Argument) {
			a.Do(By(EqZero))
		}),
})}

// EmptyInterval — with its bounds out of order an interval has no
// points and its sum is zero.
//
// Nothing is said here about the empty set. The vanishing law above
// asks the summand to be zero between the bounds, and between bounds
// in this order there is nowhere to check: a point above the lower one
// and below the upper one would put the two back in order.
var EmptyInterval = emptyIntervalThm{family.Add(registry.ProofEntry{
	Name: "EmptyInterval",
	Key:  "prop_ee02d5c3855d78a0",
	Build: family.Theorem(
		Statement{
			Binders: "∀n m:num. ∀f:(num → real).",
			Hypotheses: []string{
				"n < m",
			},
			Conclusion: "sum(m .. n, f) = &0",
		},
		func(a *Argument) {
			a.Do(By(IntervalEqZero, nat_order.LessEqTrans, nat_order.NotLessThan))
		}),
})}

// IntervalAdd — two summands over one interval may be added before or
// after summing. The general law asks the index set to be finite, and
// an interval always is.
var IntervalAdd = intervalAddThm{family.Add(registry.ProofEntry{
	Name: "IntervalAdd",
	Key:  "prop_5adcd8d2bf58526b",
	Build: family.Theorem(
		"∀m n:num. ∀f g:(num → real). sum(m .. n, f) + sum(m .. n, g) = sum(m .. n, λi:num. f(i) + g(i))",
		func(a *Argument) {
			a.Do(By(Add, num_segment.Finite))
		}),
})}

// IntervalSub — and subtracted, on the same terms.
var IntervalSub = intervalSubThm{family.Add(registry.ProofEntry{
	Name: "IntervalSub",
	Key:  "prop_ebaefd1e0bd394db",
	Build: family.Theorem(
		"∀m n:num. ∀f g:(num → real). sum(m .. n, λi:num. f(i) - g(i)) = sum(m .. n, f) - sum(m .. n, g)",
		func(a *Argument) {
			a.Do(By(Sub, num_segment.Finite))
		}),
})}

// IntervalConst — a constant summand contributes its value once per
// point, and how many points an interval holds is read off its bounds.
// The subtraction is truncated, so the count is right where the bounds
// are out of order too: the interval is empty and no copies are taken.
var IntervalConst = intervalConstThm{family.Add(registry.ProofEntry{
	Name: "IntervalConst",
	Key:  "prop_3c15ab27adefe3b9",
	Build: family.Theorem(
		"∀c:real. ∀k m:num. &(k + 1 - m) * c = sum(m .. k, λn:num. c)",
		func(a *Argument) {
			// Normalized: substituting the count into the general law
			// leaves the two sides the same product, so nothing is left to
			// refute.
			a.Do(By(Normalized, Const, num_segment.Finite, num_segment.Card))
		}),
})}

// IntervalSwap — a doubly-indexed summand over two intervals may be
// summed in either order. Both index sets are finite, which is all the
// general law wants of them.
var IntervalSwap = intervalSwapThm{family.Add(registry.ProofEntry{
	Name: "IntervalSwap",
	Key:  "prop_7178f78bb0e02ddd",
	Build: family.Theorem(
		"∀a b c d:num. ∀f:(num → num → real). "+
			"    sum(a .. b, λi:num. sum(c .. d, f(i))) = sum(c .. d, λj:num. sum(a .. b, λi:num. f(i, j)))",
		func(a *Argument) {
			a.Do(By(Swap, num_segment.Finite))
		}),
})}

// SplitAt — an interval cut in two sums as its two pieces. The one
// thing asked of the cut is that the piece after it start no lower
// than the interval itself does; below that the piece would reach
// outside what is being cut, and the two sides would not be the same
// sum at all.
var SplitAt = splitAtThm{family.Add(registry.ProofEntry{
	Name: "SplitAt",
	Key:  "prop_d5c1f14e6ccf3b34",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n p:num. ∀f:(num → real).",
			Hypotheses: []string{
				"m ≤ n + 1",
			},
			Conclusion: "sum(m .. n + p, f) = sum(m .. n, f) + sum(n + 1 .. n + p, f)",
		},
		func(a *Argument, m, n, p *Expr[Nat], f *Arrow[Nat, Real], room Fact) {
			lower := a.TermAs[Set[Nat]]("m .. n")
			upper := a.TermAs[Set[Nat]]("n + 1 .. n + p")

			cut := a.Have(
				"the interval splits at n into the part up to it and the part beyond",
				"m .. n + p = (m .. n) ∪ (n + 1 .. n + p)",
				By(room, num_segment.AddSplit.At(m, n, p)))
			a.Do(cut.Rw())

			apart := a.Have(
				"the cut falls between n and n + 1, so the two pieces share no point",
				"disjoint(m .. n, n + 1 .. n + p)",
				By(num_segment.Disjoint, nat_arith.Add1, nat_order.LessThanSucIffLessEq, nat_order.LessEqRefl))
			a.Show(
				"so the sum over the whole runs as the sum over each piece",
				By(apart, num_segment.Finite, Union.At(lower, upper, f)))
		}),
})}

// ZeroPad — a sum from 0 up to m may be read over any longer interval
// 0 .. n once the summand is silenced past m: guarded by `i ≤ m`, it
// reads as itself up to m and as &0 beyond. Within 0 .. m the guard
// holds, so the silenced summand is the summand and the two sums over
// the short interval agree; on the rest of 0 .. n the guard fails, so
// the summand vanishes there, and a sum never hears a summand that
// vanishes off its index set. This is what a coefficient list padded
// with zeros to a greater length sums to.
var ZeroPad = zeroPadThm{family.Add(registry.ProofEntry{
	Name: "ZeroPad",
	Key:  "prop_b836b37966b613e9",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:num. ∀f:(num → real).",
			Hypotheses: []string{
				"m ≤ n",
			},
			Conclusion: "sum(0 .. m, f) = sum(0 .. n, λi:num. COND(i ≤ m, f(i), &0))",
		},
		func(a *Argument, m, n *Expr[Nat], f *Arrow[Nat, Real], reaches Fact) {
			zero := a.TermAs[Nat]("0")
			short := a.TermAs[Set[Nat]]("0 .. m")
			long := a.TermAs[Set[Nat]]("0 .. n")
			silenced := a.TermAs[Fun[Nat, Real]]("λi:num. COND(i ≤ m, f(i), &0)")

			inside := a.Have(
				"the short interval lies within the long one",
				"0 .. m ⊆ 0 .. n",
				By(reaches, num_segment.Subset.At(zero, m, zero, n), nat_order.LessEqRefl.At(zero)))
			silent := a.Have(
				"and on the rest of the long one the guard fails, so the summand is &0",
				"∀i:num. i ∈ 0 .. n ∧ i ∉ 0 .. m ⇒ COND(i ≤ m, f(i), &0) = &0",
				By(Normalized, num_segment.Membership))
			a.Do(CalcEq(
				Leg(
					a.TermAs[Real]("sum(0 .. m, λi:num. COND(i ≤ m, f(i), &0))"),
					"within the short interval the guard holds, so the silenced summand reads as the summand",
					By(IntervalCongruence.At(zero, m, f, silenced))),
				FinalLeg(
					"and the sum reaches over the long interval, its summand silent on the rest",
					By(inside, silent, Superset.At(short, long, silenced))),
			))
		}),
})}

// IntervalTriangle — the triangle inequality over a segment, whose
// finiteness is the interval chapter's to give.
var IntervalTriangle = intervalTriangleThm{family.Add(registry.ProofEntry{
	Name: "IntervalTriangle",
	Key:  "prop_f248dffd6ce58ea6",
	Build: family.Theorem(
		"∀m n:num. ∀f:(num → real). |sum(m .. n, f)| ≤ sum(m .. n, λi:num. |f(i)|)",
		func(a *Argument) {
			a.Do(By(Triangle, num_segment.Finite))
		}),
})}

// IntervalMonotone — a summand nowhere above another between the bounds
// sums to no more over the segment: Monotone, with the segment's
// finiteness given and its membership read as the bounds.
var IntervalMonotone = intervalMonotoneThm{family.Add(registry.ProofEntry{
	Name: "IntervalMonotone",
	Key:  "prop_1c4df7ad99539b8c",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:num. ∀f g:(num → real).",
			Hypotheses: []string{
				"∀i:num. m ≤ i ∧ i ≤ n ⇒ f(i) ≤ g(i)",
			},
			Conclusion: "sum(m .. n, f) ≤ sum(m .. n, g)",
		},
		func(a *Argument, m, n *Expr[Nat], f, g *Arrow[Nat, Real], below Fact) {
			inSegment := a.Have(
				"Monotone asks about the members of the segment, and they are the numbers between the bounds",
				"∀i:num. i ∈ m .. n ⇒ f(i) ≤ g(i)",
				By(below))
			a.Show(
				"so Monotone over the finite segment compares the sums",
				By(num_segment.Finite.At(m, n), inSegment, Monotone.At(a.TermAs[Set[Nat]]("m .. n"), f, g)))
		}),
})}

// IntervalDominated — a summand dominated in size between the bounds
// has a sum dominated in size over the segment: Dominated, with the
// segment's finiteness given and its membership read as the bounds.
var IntervalDominated = intervalDominatedThm{family.Add(registry.ProofEntry{
	Name: "IntervalDominated",
	Key:  "prop_2a5a1d8ff1494bd5",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:num. ∀f g:(num → real).",
			Hypotheses: []string{
				"∀i:num. m ≤ i ∧ i ≤ n ⇒ |f(i)| ≤ g(i)",
			},
			Conclusion: "|sum(m .. n, f)| ≤ sum(m .. n, g)",
		},
		func(a *Argument, m, n *Expr[Nat], f, g *Arrow[Nat, Real], dominated Fact) {
			inSegment := a.Have(
				"Dominated asks about the members of the segment, and they are the numbers between the bounds",
				"∀i:num. i ∈ m .. n ⇒ |f(i)| ≤ g(i)",
				By(dominated))
			a.Show(
				"so Dominated over the finite segment bounds the sum",
				By(num_segment.Finite.At(m, n), inSegment, Dominated.At(a.TermAs[Set[Nat]]("m .. n"), f, g)))
		}),
})}

// IntervalExtend — extending a segment past its upper bound by
// nonnegative terms does not decrease the sum: the shorter segment lies
// inside the longer, and every point the longer adds lies past n.
var IntervalExtend = intervalExtendThm{family.Add(registry.ProofEntry{
	Name: "IntervalExtend",
	Key:  "prop_f0ae7458d9bbd897",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n p:num. ∀f:(num → real).",
			Hypotheses: []string{
				"n ≤ p",
				"∀i:num. n < i ∧ i ≤ p ⇒ &0 ≤ f(i)",
			},
			Conclusion: "sum(m .. n, f) ≤ sum(m .. p, f)",
		},
		func(a *Argument, m, n, p *Expr[Nat], f *Arrow[Nat, Real], hyps Fact) {
			short, long := a.TermAs[Set[Nat]]("m .. n"), a.TermAs[Set[Nat]]("m .. p")
			conditions := a.Conjuncts(
				hyps,
				"n is at most p",
				"past n and up to p the summand is nonnegative")
			reaches, nonneg := conditions[0], conditions[1]
			inside := a.Have(
				"the shorter segment lies inside the longer",
				"m .. n ⊆ m .. p",
				Simp(Fwd(num_segment.Subset)),
				ByArith(reaches))
			added := a.Have(
				"every point the longer segment adds lies past n, where the summand is nonnegative",
				"∀i:num. i ∈ (m .. p) ∖ (m .. n) ⇒ &0 ≤ f(i)",
				Simp(Fwd(set_basic.InDiff.Inst[Nat]())),
				a.ForEach(func(i *Expr[Nat]) Action {
					return Derive(func(d *Argument) {
						between := d.Assume()
						past := d.Have(
							"a point of m .. p outside m .. n lies past n",
							"n < i ∧ i ≤ p",
							ByArith(between))
						d.Show(
							"where the summand is nonnegative",
							By(past, nonneg.At(i)))
					})
				}))
			a.Show(
				"so the sum over the longer segment adds only nonnegative terms",
				By(num_segment.Finite.At(m, p), inside, added, Subset.At(short, long, f)))
		}),
})}

// ---------------------------------------------------------------------------
// The series tools: telescoping, summation by parts, and the
// antidiagonal regrouping
// ---------------------------------------------------------------------------
//
// An indexed series is as often cancelled as summed. When the summand
// is the difference of consecutive values of one function, every value
// strictly between the ends is added once and subtracted once, and only
// the two ends survive: the sum telescopes. That is the primitive of
// this part, proved by an induction of its own — on the upper bound,
// since the interval recursion above adds one term at a time, and each
// new term cancels against the last one the sum had kept. It is stated
// with the conditional the recursion itself carries, so that an
// interval with its bounds out of order reads as an empty sum and not
// as a side condition.
//
// The next two members are its corollaries through the linearity of
// Σ: the downward telescope, and summation by parts. Abel's inequality
// follows from the two: summation by parts against the partial sums of
// one sequence, bounded in size, leaves the drops of a decreasing second
// sequence, and those telescope.
//
// The last member regroups a double sum instead of cancelling one. A
// summand indexed by the triangle i + j ≤ N may be summed along its
// antidiagonals i + j = n or along its rows i, and the two orders agree.
// It is the other induction on the upper bound here, since raising the
// bound adds one antidiagonal to the first order and one term to every
// row, and one new row, to the second.

// TelescopeUp — the forward differences f(k + 1) - f(k) over m .. n sum
// to f(n + 1) - f(m), and to zero when the interval is empty.
//
// Induction on the upper bound, reading each conditional through
// `nat_order.LessEq` — ≤'s two defining clauses, at 0 and at suc. At 0
// the recursion and the order's zero clause say the same thing about
// the lower bound — the interval holds the one point 0 exactly when m
// is 0 — so the two conditionals agree.
// Raising the bound to suc n, the recursion adds the term at suc n when
// m reaches it, and the order's successor clause says what the sum held
// before: the telescope up to n when m ≤ n, nothing when m is suc n
// itself. In the first case the new term carries the telescope one step
// up; in the second it is the whole answer.
var TelescopeUp = telescopeUpThm{family.Add(registry.ProofEntry{
	Name: "TelescopeUp",
	Key:  "prop_9105f5fd3040679f",
	Build: family.Theorem(
		"∀m n:num. ∀f:(num → real). "+
			"    sum(m .. n, λk:num. f(k + 1) - f(k)) = COND(m ≤ n, f(n + 1) - f(m), &0)",
		func(a *Argument) {
			// The closure binds nothing: binding m as a parameter α-renames
			// the binders left standing, and the induction on n must name
			// it; so m and f are fixed inside the step.
			a.Induct("n")
			a.Base(
				"n = 0: the interval holds the point 0 exactly when m is 0, and both conditionals say so",
				By(IntervalClauses, nat_order.LessEq))
			a.Step(
				"n → suc n: the recursion adds the term at suc n to "+
					"what the sum held, which the hypothesis evaluates",
				func(b *Argument, ih Fact) {
					m := b.FixAs[Nat]()
					f := b.FixAs[Fun[Nat, Real]]()

					reaches := b.Assuming(
						b.Term("m ≤ suc(n)"),
						"m past suc n: the interval gains no point, the sum stays empty, and both sides are zero",
						Given(func(c *Argument, beyond Fact) {
							c.Show(
								"nothing is added, and the hypothesis's own conditional is on its zero arm",
								By(beyond, ih.At(m, f), IntervalClauses, nat_order.LessEq))
						}))
					below := b.Assuming(
						b.Term("m ≤ n"),
						"m = suc n: the sum below was empty, and the term at suc n is the whole answer",
						Given(func(c *Argument, notBelow Fact) {
							c.Show(
								"zero plus the new term f(suc n + 1) - f(suc n), with m for suc n",
								By(reaches, notBelow, ih.At(m, f), IntervalClauses, nat_order.LessEq, real_construction.AddLeftId))
						}))

					top := b.TermAs[Real]("f(suc(n) + 1)")
					last := b.TermAs[Real]("f(n + 1)")
					bottom := b.TermAs[Real]("f(m)")
					b.Show(
						"m ≤ n: the sum so far is f(n + 1) - f(m), and the new "+
							"term f(suc n + 1) - f(suc n) carries it one step up",
						By(
							reaches,
							below,
							ih.At(m, f),
							IntervalClauses,
							nat_arith.Add1,
							real_construction.AddSym,
							real_ring.SubTriangle.At(top, last, bottom)))
				})
		}),
})}

// TelescopeDown — the backward differences f(k) - f(k + 1) over m .. n
// sum to f(m) - f(n + 1), and to zero when the interval is empty.
//
// No second induction. The backward difference is the negation of the
// forward one at every point, so the sum is the negated forward sum,
// and the forward sum has already been evaluated by TelescopeUp above.
// What remains is to carry the sign through both arms of the
// conditional: the difference turns round, and zero stays zero.
var TelescopeDown = telescopeDownThm{family.Add(registry.ProofEntry{
	Name: "TelescopeDown",
	Key:  "prop_fda0e460882afb6c",
	Build: family.Theorem(
		"∀m n:num. ∀f:(num → real). "+
			"    sum(m .. n, λk:num. f(k) - f(k + 1)) = COND(m ≤ n, f(m) - f(n + 1), &0)",
		func(a *Argument, m, n *Expr[Nat], f *Arrow[Nat, Real]) {
			backward := a.TermAs[Fun[Nat, Real]]("λk:num. f(k) - f(k + 1)")
			negForward := a.TermAs[Fun[Nat, Real]]("λk:num. -(f(k + 1) - f(k))")
			above := a.TermAs[Nat]("n + 1")

			a.Do(CalcEq(
				Leg(
					a.TermAs[Real]("sum(m .. n, λk:num. -(f(k + 1) - f(k)))"),
					"at every point the backward difference is the negated forward one",
					By(IntervalCongruence.At(m, n, backward, negForward), real_ring.NegSub)),
				Leg(
					a.TermAs[Real]("-sum(m .. n, λk:num. f(k + 1) - f(k))"),
					"and the sign comes out of the sum",
					Cite(Neg)),
				Leg(
					a.TermAs[Real]("-COND(m ≤ n, f(n + 1) - f(m), &0)"),
					"whose forward differences telescope",
					By(TelescopeUp.At(m, n, f))),
				FinalLeg(
					"and the sign passes into both arms: the difference turns round, and zero stays zero",
					By(real_ring.NegSub.At(f.Apply(above), f.Apply(m)), real_ring.NegZero)),
			))
		}),
})}

// SummationByParts — summing f against the forward differences of g
// over m .. n gives the boundary term f(n + 1)·g(n + 1) - f(m)·g(m)
// less the sum of g, read one step ahead, against the forward
// differences of f; and zero when the interval is empty.
//
// Term by term, f(k)·(g(k + 1) - g(k)) is the difference of the
// products f·g at k + 1 and at k, less g(k + 1)·(f(k + 1) - f(k)) —
// both sides expand to f(k)g(k + 1) - f(k)g(k). That is the discrete
// Leibniz rule, and it is a fact about four real numbers at each point.
// Summed, the first piece is the telescope of f·g and the second is
// the sum carried to the other side; that the two may be summed
// separately is the linearity of Σ over the interval.
var SummationByParts = summationByPartsThm{family.Add(registry.ProofEntry{
	Name: "SummationByParts",
	Key:  "prop_edf39d576830f0af",
	Build: family.Theorem(
		"∀m n:num. ∀f g:(num → real). "+
			"    sum(m .. n, λk:num. f(k) * (g(k + 1) - g(k))) = "+
			"    COND(m ≤ n, "+
			"        (f(n + 1) * g(n + 1) - f(m) * g(m)) - "+
			"        sum(m .. n, λk:num. g(k + 1) * (f(k + 1) - f(k))), "+
			"        &0)",
		func(a *Argument, m, n *Expr[Nat], f, g *Arrow[Nat, Real]) {
			fDeltaG := a.TermAs[Fun[Nat, Real]]("λk:num. f(k) * (g(k + 1) - g(k))")
			leibniz := a.TermAs[Fun[Nat, Real]](
				"λk:num. (f(k + 1) * g(k + 1) - f(k) * g(k)) - g(k + 1) * (f(k + 1) - f(k))")
			product := a.TermAs[Fun[Nat, Real]]("λk:num. f(k) * g(k)")

			reaches := a.Assuming(
				a.Term("m ≤ n"),
				"bounds out of order: the interval is empty, its "+
					"sum is zero, and the conditional is on its zero arm",
				Given(func(b *Argument, empty Fact) {
					// Normalized: with the guard resident the conditional is
					// read off, and both sides are the same zero.
					b.Show(
						"an empty interval sums to zero, and zero is what the conditional reads",
						By(empty, EmptyInterval.At(n, m, fDeltaG), nat_order.NotLessEq.At(m, n)))
				}))

			rule := a.Have(
				"term by term, f·Δg is Δ(f·g) less g·Δf read one step ahead — the discrete Leibniz rule",
				"∀k:num. "+
					"    f(k) * (g(k + 1) - g(k)) = (f(k + 1) * g(k + 1) - f(k) * g(k)) - g(k + 1) * (f(k + 1) - f(k))",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					next := b.TermAs[Nat]("k + 1")
					// The three products the identity moves between: f·g one
					// step ahead, f·g here, and the cross product f here with
					// g one step ahead.
					ahead := b.TermAs[Real]("f(k + 1) * g(k + 1)")
					here := b.TermAs[Real]("f(k) * g(k)")
					cross := b.TermAs[Real]("f(k) * g(k + 1)")
					crossLessHere := b.TermAs[Real]("f(k) * g(k + 1) - f(k) * g(k)")
					aheadLessHere := b.TermAs[Real]("f(k + 1) * g(k + 1) - f(k) * g(k)")
					aheadLessCross := b.TermAs[Real]("f(k + 1) * g(k + 1) - f(k) * g(k + 1)")
					// The drop from ahead to here, less the drop from ahead to
					// the cross product.
					dropsApart := b.TermAs[Real](
						"(f(k + 1) * g(k + 1) - f(k) * g(k)) - (f(k + 1) * g(k + 1) - f(k) * g(k + 1))")

					b.Do(CalcEq(
						Leg(
							crossLessHere,
							"f(k) distributes over the difference of g",
							Cite(real_ring.SubLeftDistrib)),
						Leg(
							dropsApart,
							"and the drop from the cross product to the product here is the drop "+
								"from ahead to here, less the drop from ahead to the cross product",
							By(
								real_ring.EqSubRightAdd.At(aheadLessHere, aheadLessCross, crossLessHere),
								real_construction.AddSym.At(crossLessHere, aheadLessCross),
								real_ring.SubTriangle.At(ahead, cross, here))),
						FinalLeg(
							"that last drop is g(k + 1) distributed over the difference of f, its factors commuted",
							By(
								real_ring.SubLeftDistrib.At(g.Apply(next), f.Apply(next), f.Apply(k)),
								real_construction.MulSym.At(g.Apply(next), f.Apply(next)),
								real_construction.MulSym.At(g.Apply(next), f.Apply(k)))),
					))
				}))

			a.Do(CalcEq(
				Leg(
					a.TermAs[Real](
						"sum(m .. n, λk:num. (f(k + 1) * g(k + 1) - f(k) * g(k)) - g(k + 1) * (f(k + 1) - f(k)))"),
					"so the summand may be read in its Leibniz form throughout the interval",
					By(rule, IntervalCongruence.At(m, n, fDeltaG, leibniz))),
				Leg(
					a.TermAs[Real]("sum(m .. n, λk:num. f(k + 1) * g(k + 1) - f(k) * g(k)) - "+
						"sum(m .. n, λk:num. g(k + 1) * (f(k + 1) - f(k)))"),
					"the two pieces are summed separately",
					Cite(IntervalSub)),
				Leg(
					a.TermAs[Real]("(f(n + 1) * g(n + 1) - f(m) * g(m)) - "+
						"sum(m .. n, λk:num. g(k + 1) * (f(k + 1) - f(k)))"),
					"and the first, the forward differences of f·g, telescopes to the boundary term",
					By(reaches, TelescopeUp.At(m, n, product))),
				// Normalized: the same reading of the conditional, on its
				// other arm.
				FinalLeg(
					"which is the conditional on its m ≤ n arm",
					By(reaches)),
			))
		}),
})}

// AbelInequality — Abel's inequality: for N ≥ 1, if every partial sum
// a(1) + … + a(n) with 1 ≤ n ≤ N is at most B in size, and the weights
// b(1), …, b(N + 1) decrease to a nonnegative b(N + 1), then the weighted sum
// a(1)b(1) + … + a(N)b(N) is at most B·b(1) in size.
//
// Write A(k) for the prefix a(1) + … + a(k − 1): it is 0 at k = 1 and steps
// up by a(k), so summation by parts turns the weighted sum into the endpoint
// b(N + 1)A(N + 1) less the sum of A(k + 1)(b(k + 1) − b(k)). The endpoint
// is at most b(N + 1)·B in size; each term of the remainder is at most B
// times the drop b(k) − b(k + 1), and the drops telescope to
// b(1) − b(N + 1). The two bounds add up to B·b(1).
var AbelInequality = abelInequalityThm{family.Add(registry.ProofEntry{
	Name: "AbelInequality",
	Key:  "prop_f90444c69fa52c15",
	Reading: "The weights are read one index past the sum, at b(N + 1); the form with b(N) ≥ 0 and " +
		"no b(N + 1) is this one at the weights set to 0 past N, which the sum does not read. With N = " +
		"0 the bound would fail: the empty sum asks 0 ≤ B·b(1), and no partial sum then bounds B.",
	Build: family.Theorem(Statement{
		Binders: "∀N:num. ∀a b:(num → real). ∀B:real.",
		Hypotheses: []string{
			"0 < N",
			"∀n:num. 1 ≤ n ∧ n ≤ N ⇒ |Σ_{k∈1 .. n} a(k)| ≤ B",
			"∀k:num. 1 ≤ k ∧ k ≤ N ⇒ b(k + 1) ≤ b(k)",
			"&0 ≤ b(N + 1)",
		},
		Conclusion: "|Σ_{k∈1 .. N} a(k) * b(k)| ≤ B * b(1)",
		Abbrev: Abbrev{
			{Name: "prefix", Text: "λk:num. Σ_{i∈1 .. k - 1} a(i)"},
		},
	}, func(
		arg *Argument,
		N *Expr[Nat],
		a, b *Arrow[Nat, Real],
		B *Expr[Real],
		positive, bounded, decreasing, lastNonneg Fact,
	) {
		one := arg.TermAs[Nat]("1")
		reaches := arg.Have(
			"the interval 1 .. N is not empty",
			"1 ≤ N",
			ByArith(positive))
		empty := arg.Have(
			"before the first index the prefix is the empty sum",
			"«prefix»(1) = &0",
			By(EmptyInterval.At(arg.TermAs[Nat]("0"), one, a)))
		steps := arg.Have(
			"each term a(k)·b(k) is b(k) times the step A(k + 1) − A(k) of the prefix",
			"∀k:num. 1 ≤ k ∧ k ≤ N ⇒ a(k) * b(k) = b(k) * («prefix»(k + 1) - «prefix»(k))",
			Derive(func(c *Argument) {
				k := c.FixAs[Nat]("k")
				inRange := c.Assume()
				indices := c.Have(
					"k is positive, and k + 1 − 1 is k",
					"0 < k ∧ k + 1 - 1 = k",
					ByArith(inRange))
				step := c.Have(
					"peeling a(k) off the end of 1 .. k leaves the prefix before k",
					"«prefix»(k + 1) - «prefix»(k) = a(k)",
					ByArith(inRange, indices, PeelRight.At(k, one, a)))
				c.Show(
					"so a(k)·b(k) is b(k) times the step",
					By(step, real_construction.MulSym.At(a.Apply(k), b.Apply(k))))
			}))
		ahead := arg.Have(
			"one index ahead the prefix is a partial sum of a, at most B in size",
			"∀k:num. 1 ≤ k ∧ k ≤ N ⇒ |«prefix»(k + 1)| ≤ B",
			Derive(func(c *Argument) {
				k := c.FixAs[Nat]("k")
				inRange := c.Assume()
				index := c.Have(
					"k + 1 − 1 is k",
					"k + 1 - 1 = k",
					ByArith())
				c.Show(
					"the partial sum through k",
					By(Normalized, index, inRange, bounded.At(k)))
			}))
		prefix := arg.TermAs[Fun[Nat, Real]]("«prefix»")
		byParts := arg.Have(
			"summation by parts against the prefix, which vanishes at 1, leaves an endpoint and a sum of drops",
			"Σ_{k∈1 .. N} a(k) * b(k) = "+
				"b(N + 1) * «prefix»(N + 1) - Σ_{k∈1 .. N} «prefix»(k + 1) * (b(k + 1) - b(k))",
			By(
				steps,
				reaches,
				empty,
				IntervalCongruence.At(
					one,
					N,
					arg.TermAs[Fun[Nat, Real]]("λk:num. a(k) * b(k)"),
					arg.TermAs[Fun[Nat, Real]]("λk:num. b(k) * («prefix»(k + 1) - «prefix»(k))")),
				SummationByParts.At(one, N, b, prefix),
				real_ring.MulRightZero.At(b.Apply(one)),
				real_ring.SubRightZero.At(arg.TermAs[Real]("b(N + 1) * «prefix»(N + 1)"))))
		last := arg.TermAs[Real]("b(N + 1)")
		lastPrefix := arg.TermAs[Real]("«prefix»(N + 1)")
		endpoint := arg.Have(
			"the endpoint is at most b(N + 1)·B in size",
			"|b(N + 1) * «prefix»(N + 1)| ≤ b(N + 1) * B",
			ByArith(
				reaches,
				lastNonneg,
				ahead.At(N),
				real_sgn_abs.AbsMul.At(last, lastPrefix),
				real_sgn_abs.AbsFixedIffNonneg.At(last),
				real_order_ring.LessEqMulLeft.At(last, arg.TermAs[Real]("|«prefix»(N + 1)|"), B)))
		drops := arg.Have(
			"each term of the remainder is at most B times the drop b(k) − b(k + 1) in size",
			"∀k:num. 1 ≤ k ∧ k ≤ N ⇒ |«prefix»(k + 1) * (b(k + 1) - b(k))| ≤ B * (b(k) - b(k + 1))",
			Derive(func(c *Argument) {
				k := c.FixAs[Nat]("k")
				inRange := c.Assume()
				signs := c.Have(
					"b(k + 1) − b(k) is not positive, and its size is the drop b(k) − b(k + 1)",
					"b(k + 1) - b(k) ≤ &0 ∧ &0 ≤ b(k) - b(k + 1) ∧ -(b(k + 1) - b(k)) = b(k) - b(k + 1)",
					ByArith(inRange, decreasing.At(k)))
				prefixAhead := c.TermAs[Real]("«prefix»(k + 1)")
				signedDrop := c.TermAs[Real]("b(k + 1) - b(k)")
				c.Show(
					"the prefix one index ahead is at most B in size",
					By(
						inRange,
						signs,
						ahead.At(k),
						real_sgn_abs.AbsMul.At(prefixAhead, signedDrop),
						real_sgn_abs.AbsNegatedIffNonpos.At(signedDrop),
						real_order_ring.LessEqMulRight.At(
							c.TermAs[Real]("|«prefix»(k + 1)|"),
							B,
							c.TermAs[Real]("b(k) - b(k + 1)"))))
			}))
		telescoped := arg.Have(
			"the drops telescope to b(1) − b(N + 1)",
			"Σ_{k∈1 .. N} B * (b(k) - b(k + 1)) = B * (b(1) - b(N + 1))",
			By(
				reaches,
				ScalarLeft.At(
					B, arg.TermAs[Fun[Nat, Real]]("λk:num. b(k) - b(k + 1)"), arg.TermAs[Set[Nat]]("1 .. N")),
				TelescopeDown.At(one, N, b)))
		remainder := arg.Have(
			"so the remainder is at most B·(b(1) − b(N + 1)) in size",
			"|Σ_{k∈1 .. N} «prefix»(k + 1) * (b(k + 1) - b(k))| ≤ B * (b(1) - b(N + 1))",
			By(
				drops,
				telescoped,
				IntervalDominated.At(
					one,
					N,
					arg.TermAs[Fun[Nat, Real]]("λk:num. «prefix»(k + 1) * (b(k + 1) - b(k))"),
					arg.TermAs[Fun[Nat, Real]]("λk:num. B * (b(k) - b(k + 1))"))))
		endpointTerm := arg.TermAs[Real]("b(N + 1) * «prefix»(N + 1)")
		remainderSum := arg.TermAs[Real]("Σ_{k∈1 .. N} «prefix»(k + 1) * (b(k + 1) - b(k))")
		triangle := arg.Have(
			"the triangle inequality splits the weighted sum between the endpoint and the remainder",
			"|Σ_{k∈1 .. N} a(k) * b(k)| ≤ "+
				"|b(N + 1) * «prefix»(N + 1)| + |Σ_{k∈1 .. N} «prefix»(k + 1) * (b(k + 1) - b(k))|",
			By(
				byParts,
				real_ring.RealSubDef.At(endpointTerm, remainderSum),
				real_sgn_abs.AbsTriangle.At(
					endpointTerm,
					arg.TermAs[Real]("-Σ_{k∈1 .. N} «prefix»(k + 1) * (b(k + 1) - b(k))")),
				real_sgn_abs.AbsEven.At(remainderSum)))
		arg.Show(
			"b(N + 1)·B and B·(b(1) − b(N + 1)) add up to B·b(1)",
			ByArith(triangle, endpoint, remainder))
	}),
})}

// Antidiagonal — a doubly-indexed f summed over the triangle i + j ≤ N
// by its antidiagonals i + j = n is the same f summed by its rows i.
// This is the finite identity behind the Cauchy product of two series.
//
// Induction on N, with f fixed. Raising the bound to suc N, the left
// side gains one antidiagonal, n = suc N. The right side gains a term in
// each row i ≤ N, whose range 0 .. suc N - i is one point longer than
// 0 .. N - i, and a new row i = suc N holding the single term
// f(suc N, 0). These are the same points: the new antidiagonal crosses
// each old row once, at j = suc N - i, and ends at k = suc N in the new
// row.
var Antidiagonal = antidiagonalThm{family.Add(registry.ProofEntry{
	Name: "Antidiagonal",
	Key:  "prop_daf958b0c68b46cf",
	Build: family.Theorem(
		"∀N:num. ∀f:(num → num → real). "+
			"    Σ_{n∈0 .. N} Σ_{k∈0 .. n} f(k, n - k) = Σ_{i∈0 .. N} Σ_{j∈0 .. N - i} f(i, j)",
		func(a *Argument, N *Expr[Nat], f *Arrow2[Nat, Nat, Real]) {
			a.Induct(N)
			a.Base(
				"N = 0: both sides are the one term f(0, 0)",
				By(nat_monus.SubRefl, IntervalPoint))
			a.Step(
				"N → suc N: the new antidiagonal on the left is the "+
					"new term of every row and the new row on the right",
				func(b *Argument, ih Fact) {
					zero := b.TermAs[Nat]("0")
					next := b.TermAs[Nat]("suc(N)")

					// Stated over 0 ≤ i ≤ N, the range on which the congruence
					// law below asks the two summands to agree.
					rowGains := b.Have(
						"each row 0 ≤ i ≤ N reaches one point further, to j = suc N - i",
						Statement{
							Binders: "∀i:num.",
							Hypotheses: []string{
								"0 ≤ i",
								"i ≤ N",
							},
							Conclusion: "Σ_{j∈0 .. suc(N) - i} f(i, j) = Σ_{j∈0 .. N - i} f(i, j) + f(i, suc(N) - i)",
						},
						Derive(func(c *Argument) {
							c.FixAs[Nat]()
							inRange := c.Assume()
							shorter := c.TermAs[Nat]("N - i")
							row := c.TermAs[Fun[Nat, Real]]("λj:num. f(i, j)")
							longer := c.Have(
								"below the new bound, suc N - i is one more than N - i",
								"suc(N) - i = suc(N - i)",
								ByArith(inRange))
							c.Do(longer.Rw())
							c.Show(
								"so the row's range is 0 .. N - i and one point more",
								By(IntervalClauses.At(zero, shorter, row), nat_order.ZeroLessEq.At(c.TermAs[Nat]("suc(N - i)"))))
						}))

					diagonals := b.BigOpAs[Nat, Real]("Σ_{n∈0 .. N} Σ_{k∈0 .. n} f(k, n - k)")
					antidiagonal := b.BigOpAs[Nat, Real]("Σ_{k∈0 .. suc(N)} f(k, suc(N) - k)")
					oldRows := b.BigOpAs[Nat, Real]("Σ_{i∈0 .. N} Σ_{j∈0 .. N - i} f(i, j)")
					gained := b.BigOpAs[Nat, Real]("Σ_{i∈0 .. N} f(i, suc(N) - i)")
					rowsPlusGain := b.BigOpAs[Nat, Real]("Σ_{i∈0 .. N} (Σ_{j∈0 .. N - i} f(i, j) + f(i, suc(N) - i))")
					oldRowsAtNext := b.BigOpAs[Nat, Real]("Σ_{i∈0 .. N} Σ_{j∈0 .. suc(N) - i} f(i, j)")
					lastRow := b.TermAs[Fun[Nat, Real]]("λj:num. f(suc(N), j)")

					lengthen := b.Have(
						"so, row by row, the old rows at suc N are the old rows at N each with its gained term",
						"Σ_{i∈0 .. N} Σ_{j∈0 .. suc(N) - i} f(i, j) = "+
							"Σ_{i∈0 .. N} (Σ_{j∈0 .. N - i} f(i, j) + f(i, suc(N) - i))",
						By(rowGains, IntervalCongruence.At(zero, N, oldRowsAtNext.Summand(), rowsPlusGain.Summand())))

					b.Do(CalcEq(
						Leg(
							b.TermAs[Real]("Σ_{n∈0 .. N} Σ_{k∈0 .. n} f(k, n - k) + Σ_{k∈0 .. suc(N)} f(k, suc(N) - k)"),
							"the left side gains the antidiagonal n = suc N",
							By(IntervalClauses.At(zero, N, diagonals.Summand()), nat_order.ZeroLessEq.At(next))),
						Leg(
							b.TermAs[Real]("Σ_{i∈0 .. N} Σ_{j∈0 .. N - i} f(i, j) + Σ_{k∈0 .. suc(N)} f(k, suc(N) - k)"),
							"below it lies the triangle up to N, which the hypothesis sums by rows",
							By(ih)),
						Leg(
							b.TermAs[Real](
								"Σ_{i∈0 .. N} Σ_{j∈0 .. N - i} f(i, j) + (Σ_{i∈0 .. N} f(i, suc(N) - i) + f(suc(N), 0))"),
							"the antidiagonal ends at k = suc N, where its term is f(suc N, 0)",
							By(
								IntervalClauses.At(zero, N, antidiagonal.Summand()),
								nat_order.ZeroLessEq.At(next),
								nat_monus.SubRefl.At(next))),
						Leg(
							b.TermAs[Real](
								"Σ_{i∈0 .. N} Σ_{j∈0 .. N - i} f(i, j) + Σ_{i∈0 .. N} f(i, suc(N) - i) + f(suc(N), 0)"),
							"set that last term apart",
							Cite(real_construction.AddAssoc)),
						Leg(
							b.TermAs[Real]("Σ_{i∈0 .. N} Σ_{j∈0 .. suc(N) - i} f(i, j) + f(suc(N), 0)"),
							"the rest of the antidiagonal is one term for each "+
								"old row, and joined to their rows they lengthen them",
							By(IntervalAdd.At(zero, N, oldRows.Summand(), gained.Summand()), lengthen)),
						Leg(
							b.TermAs[Real](
								"Σ_{i∈0 .. N} Σ_{j∈0 .. suc(N) - i} f(i, j) + Σ_{j∈0 .. suc(N) - suc(N)} f(suc(N), j)"),
							"f(suc N, 0) is the whole of the new row i = suc N, whose range is 0 .. 0",
							By(nat_monus.SubRefl.At(next), IntervalPoint.At(zero, lastRow))),
						FinalLeg(
							"and the new row is the last of the rows up to suc N",
							By(IntervalClauses.At(zero, N, oldRowsAtNext.Summand()), nat_order.ZeroLessEq.At(next))),
					))
				})
		}),
})}
