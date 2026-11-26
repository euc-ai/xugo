// real_completeness.go — the chapter: the completeness spur.
//
// Three parts, marked by banners:
//
// - The Archimedean chain
// - The completeness of the slope (nadd) layer
// - The climb from the slope layer to ℝ, in the README's order

package real_completeness

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/internal/eudoxus_slope"
	"github.com/euc-ai/xugo/library/proofs/real/tower/internal/nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/tower/internal/nonneg_real_formal_diff"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/algebra"
)

// ---------------------------------------------------------------------------
// The Archimedean chain
// ---------------------------------------------------------------------------
//
// the Archimedean chain: three snapshots of one argument at increasing
// strength, and the base of the completeness climb.
//
// - Arch — every slope is dominated by some embedded natural. The
// analytic content is entirely inherited from eudoxus_slope.LinearBound and
// eudoxus_slope.OfNum; this is the observation that nadd_le unfolds to
// precisely LinearBound's pointwise statement with the coefficient
// re-used as the ∃n witness.
// - ArchZero — Arch bounds the fixed upper bound by a natural;
// eudoxus_slope.ArchMult then contradicts bounded multiples of a nonzero slope.
// - ArchLemma — both packaged into an ε-flavoured comparison: if a
// fixed slack z absorbs every multiplied gap between x and y, then
// x ≤ y.
//
// README §"The chain", first two bullets, and §"The Archimedean chain,
// in one paragraph".

// Arch — every Cauchy-slope is bounded above by some embedded natural:
//
//	⊢ ∀x:nadd. ∃n:num. (x ≤ nadd_of_num(n))
//
// eudoxus_slope.LinearBound hands x a linear coefficient A and an additive
// slack B. Reading nadd_le(x, nadd_of_num(A)) through its definition
// and eudoxus_slope.OfNum, the coefficient A doubles as the ∃n witness, the
// slack B discharges nadd_le's own ∃-slack, and the pointwise leaf
// IS LinearBound's fact.
var Arch = archThm{family.Add(registry.ProofEntry{
	Name: "Arch",
	Key:  "prop_e5c64376c83af9fb",
	Build: family.Theorem("∀x:nadd. ∃n:num. x ≤ nadd_of_num(n)",
		func(a *Argument, x Term) {

			A_0 := a.Ctx().Var("A_0", NumType) // linear coefficient from eudoxus_slope.LinearBound
			B_0 := a.Ctx().Var("B_0", NumType) // additive slack from eudoxus_slope.LinearBound

			a.Do( // eudoxus_slope.LinearBound gives (A₀, B₀) with
				// dest_nadd(x, n) ≤ A₀·n + B₀ for every n.
				Cite(eudoxus_slope.LinearBound, x),
				StripQuant(),

				// The same A₀ serves as the ∃n witness; nadd_le then unfolds
				// to a pointwise bound over its own slack ∃B, which the same
				// B₀ discharges.
				Witness(A_0),
				Unfold(eudoxus_slope.NaddLeDef),
				Witness(B_0),

				// eudoxus_slope.OfNum rewrites dest_nadd(nadd_of_num(A₀), n) to A₀·n;
				// the pointwise leaf coincides with LinearBound's fact and
				// closes reflexively.
				Cite(eudoxus_slope.OfNum),
			)
		}),
})}

// ArchZero — choose a natural bound for k. If x is nonzero, ArchMult
// puts a multiple of x above the successor of that bound. Boundedness
// then forces the successor below its predecessor, contradicting natural order.
var ArchZero = archZeroThm{family.Add(registry.ProofEntry{
	Name: "ArchZero",
	Key:  "prop_867ae0b25f15993b",
	Build: family.Theorem(
		Statement{
			Hypotheses: []string{
				"∀n:num. nadd_of_num(n) * x ≤ k",
			},
			Conclusion: "nadd_eq(x, nadd_of_num(0))",
		},
		func(a *Argument, bounded Fact) {
			x := a.Ctx().VarAs[Nadd]("x")
			k := a.Ctx().VarAs[Nadd]("k")
			nonzero := a.SupposeNot()
			n, archBound := a.UnpackAs[Nat](Arch.At(k), "n")
			next := a.TermAs[Nat]("suc(n)")
			N, lowerBound := a.ObtainAs[Nat](
				"a multiple reaches the successor bound",
				"∃N:num. nadd_of_num(suc(n)) ≤ nadd_of_num(N) * x",
				By(nonzero, eudoxus_slope.ArchMult.At(x, next)))
			nSlope := a.TermAs[Nadd]("nadd_of_num(n)")
			nextSlope := a.TermAs[Nadd]("nadd_of_num(suc(n))")
			multiple := a.TermAs[Nadd]("nadd_of_num(N) * x")
			trapped := a.Have(
				"the successor bound is trapped below the original bound",
				"nadd_of_num(suc(n)) ≤ nadd_of_num(n)",
				By(
					lowerBound,
					archBound,
					bounded.At(N),
					eudoxus_slope.LessEqTrans.At(nextSlope, multiple, k),
					eudoxus_slope.LessEqTrans.At(nextSlope, k, nSlope)))
			descended := a.Have(
				"reflect the inequality to natural numbers",
				"suc(n) ≤ n",
				By(trapped, eudoxus_slope.OfNumLessEq.At(next, n)))
			a.Show(
				"no natural number precedes itself",
				By(descended, nat_order.SucLessEqIffLessThan.At(n, n), nat_order.LessThanIrrefl.At(n)))
		}),
})}

// ArchLemma — the ε-approximate Archimedean comparison on slopes:
//
//	∀x y z:nadd. (∀n:num. n·x ≤ n·y + z) ⇒ x ≤ y
//
// Read n as scale and z as slack: if every scaled copy of x fits
// inside the same scaled copy of y with a FIXED slack z (independent
// of n), the two slopes are ordered x ≤ y in the slope preorder.
//
// Trichotomy first: LessEqTotal gives y ≤ x ∨ x ≤ y and the x ≤ y
// branch IS the goal. The analytic content lives in the y ≤ x branch:
//
// - LessEqExists inverts the flipped inequality — under y ≤ x, some
// slope d realizes the gap: x ≈ y + d.
// - cancelBound (the section below) pushes the boundedness hyp
// through the sum: with x ≈ y + d resident, every multiple of d
// stays under the same slack z.
// - ArchZero (of complete) reads that as d ≈ 0 — a slope whose
// every multiple is bounded by a fixed constant IS zero.
// - The ring identity chain x ≈ y+d ≈ y+0 ≈ 0+y ≈ y collapses to
// x ≈ y, and EqImpliesLessEq closes the ≤ direction.
var ArchLemma = archLemmaThm{family.Add(registry.ProofEntry{
	Name: "ArchLemma",
	Key:  "prop_c1d9321b876cf48a",
	// The proof is two sections written as a linear script: `cancelBound`
	// is a Go local the goal cites by closure capture.
	Build: family.Sections(
		Statement{
			Binders: "∀x y z:nadd.",
			Hypotheses: []string{
				"∀n:num. nadd_of_num(n) * x ≤ nadd_of_num(n) * y + z",
			},
			Conclusion: "x ≤ y",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			d_0 := ctx.Var("d_0", MakeType("nadd")) // Skolem from LessEqExists

			// cancelBound: distribute the boundedness hypothesis through
			// x ≈ y+d to reveal an independent bound on d's multiples.
			//
			//	∀x y z d:nadd. (∀n:num. n·x ≤ n·y + z) ⇒ x ≈ y + d ⇒ ∀n:num. n·d ≤ z
			//
			// Fix n. Ground the boundedness hyp: n·x ≤ n·y + z. LeftDistrib
			// rewrites n·(y+d) ≈ n·y + n·d. MulWellDef bridges n·x ≈ n·(y+d)
			// via the x ≈ y+d hyp (with n≈n reflexive on the outer factor).
			// EqTrans chains those two into n·x ≈ n·y + n·d. LessEqWellDef then
			// transports the boundedness across that equivalence, giving
			// n·y + n·d ≤ n·y + z. LessEqAddLeft cancels the common n·y
			// summand and the residual n·d ≤ z closes.
			//
			// The two premises arrive as Facts, so grounding the bound at the
			// fixed scale is `.At(n)` rather than a second copy of its
			// statement text.
			cancelBound := ctx.Lemma(
				"∀x y z d:nadd. "+
					"    (∀n:num. nadd_of_num(n) * x ≤ nadd_of_num(n) * y + z) ⇒ "+
					"    nadd_eq(x, y + d) ⇒ "+
					"    ∀n:num. nadd_of_num(n) * d ≤ z",
				func(a *Argument, x, y, z, d Term, bounded, gap Fact, n Term) {
					// Named intermediate terms — the waypoints of the chain below.
					ofn := v.NaddOfNum.Apply(n)             // nadd_of_num(n₀)
					nx := v.NaddMul.Apply(ofn, x)           // n₀·x
					ny := v.NaddMul.Apply(ofn, y)           // n₀·y
					nd := v.NaddMul.Apply(ofn, d)           // n₀·d
					yPlusD := v.NaddAdd.Apply(y, d)         // y + d
					nyPlusD := v.NaddMul.Apply(ofn, yPlusD) // n₀·(y + d)
					nyPlusNd := v.NaddAdd.Apply(ny, nd)     // n₀·y + n₀·d
					nyPlusZ := v.NaddAdd.Apply(ny, z)       // n₀·y + z

					// EqRefl fires the reflexive premise of both well-def lemmas;
					// the terminal LessEqAddLeft closes on install.
					a.Show(
						"n₀·d ≤ z — cancel n₀·y from n₀·y + n₀·d ≤ n₀·y + z",
						By(
							gap,
							bounded.At(n),
							At(eudoxus_slope.LeftDistrib, ofn, y, d),
							At(eudoxus_slope.MulWellDef, ofn, ofn, x, yPlusD),
							eudoxus_slope.NaddEqRefl,
							At(eudoxus_slope.NaddEqTrans, nx, nyPlusD, nyPlusNd),
							At(eudoxus_slope.LessEqWellDef, nx, nyPlusNd, nyPlusZ, nyPlusZ),
							eudoxus_slope.LessEqAddLeft))
				})

			// The theorem.
			//
			// LessEqTotal splits nadd on the flipped-order pair (y, x). The
			// x ≤ y case is direct — the disjunction's own witness IS the goal.
			// The y ≤ x case is the analytic content and lives in archLemmaYLeqX,
			// which drops the boundedness premise once cancelBound has spent it.
			return ctx.Theorem(headline,
				func(a *Argument, x, y, z Term, bounded Fact) {
					a.Do(
						// LessEqTotal @ (y, x): resident disjunction y≤x ∨ x≤y.
						Cite(eudoxus_slope.LessEqTotal, y, x),
					)
					a.Do(SplitDisj(
						LeftHolds(
							"y ≤ x: extract the gap slope d, cancelBound + ArchZero force d ≈ 0, ring-chain closes x ≈ y",
							archLemmaYLeqX(ctx, v, cancelBound, bounded, x, y, z, d_0),
						),
						RightHolds(
							"x ≤ y: the disjunction's own witness IS the goal — auto-close",
							TrivialNormalized(),
						),
					))
				})
		}),
})}

// archLemmaYLeqX: the analytic branch of the theorem — under y ≤ x, the
// slope order's own subtraction gives a gap d with x ≈ y + d;
// cancelBound turns the goal's boundedness hyp into ∀n. n·d ≤ z;
// ArchZero forces d ≈ 0; the ring identity chain then collapses
// y + d_0 to y, the gap joins it to x ≈ y, and EqImpliesLessEq
// closes. The chain is a CalcRel over nadd_eq: its legs carry the
// waypoints and their justifications, and the combinator computes the
// EqTrans groundings.
func archLemmaYLeqX(
	ctx *Script,
	v *completeVocab,
	cancelBound *GoalStackNode,
	bounded Fact,
	x, y, z, d_0 Term,
) Action {
	zero := v.NaddOfNum.Apply(ctx.Numeral(0))

	// The eq-chain's waypoints: y+d_0 ≈ y+0 ≈ 0+y ≈ y.
	yPlusD0 := v.NaddAdd.Apply(y, d_0)
	yPlusZero := v.NaddAdd.Apply(y, zero)
	zeroPlusY := v.NaddAdd.Apply(zero, y)

	return Derive(func(a *Argument) {
		a.Do(
			// LessEqExists @ (y, x): the branch hyp y ≤ x is its guard, so
			// the cite lands ∃d. nadd_eq(x, y+d); StripQuant fixes d as d_0.
			Cite(eudoxus_slope.LessEqExists, y, x),
			StripQuant(),
		)

		// x ≈ y + d_0 — the gap LessEqExists realized.
		gap := a.Hyp("nadd_eq(x, y + d_0)")

		// cancelBound @ (x, y, z, d_0): the boundedness premise and the gap
		// the branch hyp y ≤ x selects bound every multiple of d_0.
		a.Have(
			"every multiple of the gap d_0 stays under the slack z",
			"∀n:num. nadd_of_num(n) * d_0 ≤ z",
			By(bounded, gap, At(cancelBound, x, y, z, d_0)))

		// Drop the spent boundedness premise so the ArchZero chain below
		// doesn't refute-poison.
		a.Do(Clear(bounded))

		a.Do(
			// ArchZero @ (d_0, z): its guard ∀n. n·d_0 ≤ z is resident, so
			// the cite lands nadd_eq(d_0, 0) itself.
			Cite(ArchZero, d_0, z),
		)

		// The ring identity chain — collapse y+d_0 to y using d_0 ≈ 0 and
		// the additive identity + commutativity. Each leg is an
		// independently closed link; CalcRel folds them through EqTrans,
		// computing the grounding triples.
		collapsed := a.Calc(CalcRel{
			Rel:   func(x, y Term) Prop { return MakeProp(v.NaddEq.Apply(x, y)) },
			Trans: eudoxus_slope.NaddEqTrans,
		}, yPlusD0,
			Leg(
				yPlusZero,
				"y + d_0 ≈ y + 0 — AddWellDef @ (y, y, d_0, 0): EqRefl fixes "+
					"the left summand, ArchZero's d_0 ≈ 0 replaces the right",
				Cite(eudoxus_slope.AddWellDef, y, y, d_0, zero),
				Cite(eudoxus_slope.NaddEqRefl)),
			// The last two legs ARE instances of their lemmas: the
			// install matches the leg goal and closes it outright, so
			// neither needs a refute — and neither can be spelled
			// ground (the witness form rejects a cite whose witnesses go
			// unused). The leg's `to` term carries the waypoint.
			Leg(
				zeroPlusY,
				"y + 0 ≈ 0 + y — AddSym",
				Cite(eudoxus_slope.AddSym)),
			Leg(
				y,
				"0 + y ≈ y — AddLeftId",
				Cite(eudoxus_slope.AddLeftId)))
		a.Show(
			"x ≤ y — the gap and the collapsed chain give x ≈ y, which EqImpliesLE reads as the goal's order",
			By(gap, collapsed, At(eudoxus_slope.NaddEqTrans, x, yPlusD0, y), eudoxus_slope.NaddEqImpliesLessEq))
	})
}

// ---------------------------------------------------------------------------
// The completeness of the slope (nadd) layer
// ---------------------------------------------------------------------------
//
// every non-empty set of slopes bounded above has a least upper bound
// (up to nadd_eq). The analytic workhorse of the completeness spur —
// every subsequent member (HrealComplete, RealComplete) is a transport
// of this fact across quotients.
//
// The supremum is built by counting. At a fixed scale n, the naturals r
// with of(r) ≤ n·x for some x in the set are bounded above, so there is
// a largest one; call it r_fn(n). That function turns out to be a slope
// itself, and mk_nadd(r_fn) is the least upper bound: it dominates every
// member because one past the maximum is unattainable, and it sits under
// every competing bound because the maximum is attained inside the set.
// Both halves reach the slope order through ArchLemma, which trades an
// exact comparison for a pointwise bound with a fixed slack.
//
// The sections construct the maxima, prove their slope estimate, and
// establish the upper-bound and leastness properties.

// The vocabulary of the construction. These builders also supply the
// display patterns, so each named property has one statement text.

// attainableText says some x in set satisfies of(value) ≤ scale·x.
func attainableText(set, value, scale string) string {
	return "(∃x:nadd.(" + set + "(x) ∧ (nadd_of_num(" + value +
		") ≤ nadd_of_num(" + scale + ") * x)))"
}

// maximalText says value dominates every attainable natural at scale.
func maximalText(set, value, scale string) string {
	return "∀s:num.(" + attainableText(set, "s", scale) + " ⇒ (s ≤ " + value + "))"
}

// isMaxAtText combines attainability and maximality.
func isMaxAtText(set, value, scale string) string {
	return "(" + attainableText(set, value, scale) +
		" ∧ (" + maximalText(set, value, scale) + "))"
}

// isNumericalMaxText says fn picks a maximum at every scale.
func isNumericalMaxText(set, fn string) string {
	return "∀n:num." + isMaxAtText(set, fn+"(n)", "n")
}

// isTightBoundText bounds each scaled member by one past the maximum.
func isTightBoundText(set, fn string) string {
	return "∀n:num.∀x:nadd.(" + set +
		"(x) ⇒ (nadd_of_num(n) * x ≤ nadd_of_num(suc(" + fn + "(n)))))"
}

// isSlopeEstimateText is the cross-scale estimate for fn.
func isSlopeEstimateText(fn string) string {
	return "∀n:num.∀i:num.((i * " + fn + "(n)) ≤ ((n * " + fn + "(i)) + n))"
}

// destComputesText reads the mk_nadd round trip pointwise.
func destComputesText(fn string) string {
	return "∀n:num.(dest_nadd(mk_nadd(" + fn + "), n) = " + fn + "(n))"
}

// isUpperBoundText — `bound` dominates every member of `set`.
func isUpperBoundText(set, bound string) string {
	return "∀x:nadd.(" + set + "(x) ⇒ (x ≤ " + bound + "))"
}

// tightBoundText also supplies the display test's standalone statement.
var tightBoundText = "∀P:(nadd → bool).∀r_fn:(num → num).((" + isNumericalMaxText("P", "r_fn") +
	") ⇒ (" + isTightBoundText("P", "r_fn") + "))"

// destSimpRig computes dest_nadd through sums, products, and numerals.
func destSimpRig() Action {
	return Simp(
		Rev(eudoxus_slope.Add),   // dest(x + y, n) → dest(x, n) + dest(y, n)
		Rev(eudoxus_slope.Mul),   // dest(x * y, n) → dest(x, dest(y, n))
		Rev(eudoxus_slope.OfNum), // dest(of_num(k), n) → k * n
	)
}

// naddOrderCalc composes slope inequalities and equivalences.
func naddOrderCalc(ctx *Script, v *completeVocab) CalcOrder {
	return CalcOrder{
		Le: func(x, y Term) Prop { return MakeProp(v.NaddLe.Apply(x, y)) },
		Eq: func(x, y Term) Prop { return MakeProp(v.NaddEq.Apply(x, y)) },

		LeTrans: eudoxus_slope.LessEqTrans,
		EqTrans: eudoxus_slope.NaddEqTrans,
		EqToLe:  eudoxus_slope.NaddEqImpliesLessEq,
	}
}

// NaddComplete constructs the supremum from the per-scale maxima.
var NaddComplete = naddCompleteThm{family.Add(registry.ProofEntry{
	Name: "NaddComplete",
	Key:  "prop_42c4d5f9d9371236",
	Build: family.Sections(
		Statement{
			Binders: "∀P:(nadd → bool).",
			Hypotheses: []string{
				"∃x:nadd. P(x)",
				"∃M:nadd. ∀x:nadd. P(x) ⇒ x ≤ M",
			},
			Conclusion: "∃M:nadd. (∀x:nadd. P(x) ⇒ x ≤ M) ∧ (∀M':nadd. (∀x:nadd. P(x) ⇒ x ≤ M') ⇒ M ≤ M')",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			of := func(t Term) Term { return v.NaddOfNum.Apply(t) }
			mul := func(x, y Term) Term { return v.NaddMul.Apply(x, y) }
			times := func(x, y Term) *TermWrapper { return v.Times.Apply(x, y) }

			// At scale n, 0 is attainable and a natural ceiling for n·M bounds
			// every attainable natural. Take their maximum.
			numericalMax := ctx.Lemma(
				Statement{
					Binders: "∀P:(nadd → bool). ∀n:num.",
					Hypotheses: []string{
						"∃x:nadd. P(x)",
						"∃M:nadd. ∀x:nadd. P(x) ⇒ x ≤ M",
					},
					Conclusion: "∃r:num. " +
						"    (∃x:nadd. P(x) ∧ nadd_of_num(r) ≤ nadd_of_num(n) * x) ∧ " +
						"    (∀s:num. (∃x:nadd. P(x) ∧ nadd_of_num(s) ≤ nadd_of_num(n) * x) ⇒ s ≤ r)",
				},
				func(a *Argument, P, n Term, bounded Fact) {
					// λr. ∃x ∈ P₀. of(r) ≤ n₀·x — the predicate MaximumExists
					// is applied to below.
					attainable := a.Term("λr:num. ∃x:nadd. P(x) ∧ nadd_of_num(r) ≤ nadd_of_num(n) * x")

					boundEx := a.Have(
						"choose an upper bound",
						"∃M:nadd. ∀x:nadd. P(x) ⇒ x ≤ M",
						By(bounded))
					_, ub := a.Unpack(boundEx)
					_, ceilingBound := a.Obtain(
						"cap the scaled upper bound by a natural",
						"∃c:num. nadd_of_num(n) * M ≤ nadd_of_num(c)",
						By(Arch),
						Named("c"))

					ceiling := a.Have(
						"every attainable natural lies below the cap",
						"∀r:num. (∃x:nadd. P(x) ∧ nadd_of_num(r) ≤ nadd_of_num(n) * x) ⇒ r ≤ c",
						Derive(func(b *Argument) {
							b.Fix()
							_, attained := b.Unpack(b.Assume())
							b.Show(
								"scale the upper bound and descend the resulting cap to ℕ",
								By(
									Normalized,
									attained,
									ub,
									ceilingBound,
									eudoxus_slope.LessEqMulLeft,
									eudoxus_slope.LessEqTrans,
									eudoxus_slope.OfNumLessEq))
						}))

					a.Show(
						"take a maximum of the nonempty bounded attainability predicate",
						By(
							PreNormalized,
							DenotedAs("attainable", attainable),
							At(nat_order.MaximumExists, attainable),
							bounded,
							ctx.DepNormalized(eudoxus_slope.ZeroLessEq),
							ceiling))
				})

			// One past the maximum is unattainable.
			tightBound := ctx.Lemma("∀P:(nadd → bool). ∀r_fn:(num → num). "+
				"    (∀n:num. "+
				"        (∃x:nadd. P(x) ∧ nadd_of_num(r_fn(n)) ≤ nadd_of_num(n) * x) ∧ "+
				"        (∀s:num. (∃x:nadd. P(x) ∧ nadd_of_num(s) ≤ nadd_of_num(n) * x) ⇒ s ≤ r_fn(n))) ⇒ "+
				"    ∀n:num. ∀x:nadd. P(x) ⇒ nadd_of_num(n) * x ≤ nadd_of_num(suc(r_fn(n)))",
				func(a *Argument, P Term, r_fn *TermWrapper, maxAll Fact, n, x Term, member Fact) {
					sucRfn := v.Suc.Apply(r_fn.Apply(n)) // suc(r_fn₀(n₀))

					notTight := a.SupposeNot()
					attains := a.Have(
						"a failed tight bound makes the successor attainable",
						"∃x:nadd. P(x) ∧ nadd_of_num(suc(r_fn(n))) ≤ nadd_of_num(n) * x",
						By(notTight, member, At(eudoxus_slope.LessEqTotal, mul(of(n), x), of(sucRfn))))
					capped := a.Have(
						"maximality bounds the successor",
						"suc(r_fn(n)) ≤ r_fn(n)",
						By(attains, maxAll.At(n)))
					a.Show(
						"the successor cannot lie below the maximum",
						ByArith(capped))
				})

			// If x attains the maximum at n, scale its bound by i and its
			// tight bound at i by n. Commuting the factors compares the two:
			// of(i·r_fn(n)) ≤ i·(n·x) ≈ n·(i·x) ≤ of(n·suc(r_fn(i))).
			slopeIneq := ctx.Lemma(
				Statement{
					Binders: "∀P:(nadd → bool). ∀r_fn:(num → num).",
					Hypotheses: []string{
						"∀n:num. " +
							"    (∃x:nadd. P(x) ∧ nadd_of_num(r_fn(n)) ≤ nadd_of_num(n) * x) ∧ " +
							"    (∀s:num. (∃x:nadd. P(x) ∧ nadd_of_num(s) ≤ nadd_of_num(n) * x) ⇒ s ≤ r_fn(n))",
					},
					Conclusion: "∀n i:num. i * r_fn(n) ≤ n * r_fn(i) + n",
				},
				func(a *Argument, P Term, r_fn *TermWrapper, maxAll Fact, n, i Term) {
					rN, rI := r_fn.Apply(n), r_fn.Apply(i)
					sucRI := v.Suc.Apply(rI)

					tight := a.Have(
						"r_fn₀ tightly bounds P₀",
						"∀n:num. ∀x:nadd. P(x) ⇒ nadd_of_num(n) * x ≤ nadd_of_num(suc(r_fn(n)))",
						By(maxAll, tightBound))
					x, attained := a.Obtain(
						"choose a member attaining the maximum at n",
						"∃x:nadd. P(x) ∧ nadd_of_num(r_fn(n)) ≤ nadd_of_num(n) * x",
						By(maxAll.At(n)))

					estimate := a.CalcOrder(naddOrderCalc(ctx, v), of(times(i, rN)),
						EqLeg(
							mul(of(i), of(rN)),
							"split the numeral product",
							By(At(eudoxus_slope.OfNumMul, i, rN), eudoxus_slope.NaddEqSym)),
						LeLeg(
							mul(of(i), mul(of(n), x)),
							"scale the attained bound by i",
							By(attained, At(eudoxus_slope.LessEqMulLeft, of(i), of(rN), mul(of(n), x)))),
						EqLeg(
							mul(of(n), mul(of(i), x)),
							"commute the two numeral factors",
							By(
								At(eudoxus_slope.MulAssoc, of(i), of(n), x),
								At(eudoxus_slope.MulAssoc, of(n), of(i), x),
								At(eudoxus_slope.MulSym, of(i), of(n)),
								At(eudoxus_slope.MulWellDef, mul(of(i), of(n)), mul(of(n), of(i)), x, x),
								eudoxus_slope.NaddEqRefl,
								eudoxus_slope.NaddEqSym,
								eudoxus_slope.NaddEqTrans)),
						LeLeg(
							mul(of(n), of(sucRI)),
							"scale the tight bound by n",
							By(attained, tight.At(i, x), At(eudoxus_slope.LessEqMulLeft, of(n), mul(of(i), x), of(sucRI)))),
						EqLeg(
							of(times(n, sucRI)),
							"refold the numeral product",
							By(eudoxus_slope.OfNumMul)))

					descended := a.Have(
						"descend the comparison to ℕ",
						"i * r_fn(n) ≤ n * suc(r_fn(i))",
						By(estimate, eudoxus_slope.OfNumLessEq))
					a.Show(
						"expand the successor to obtain the cross-scale estimate",
						ByArith(descended, At(nat_arith.MulSuc, n, rI)))
				})

			// The estimate in both directions gives the slope defect with B = 1.
			isNaddRfn := ctx.Lemma(
				Statement{
					Binders: "∀r_fn:(num → num).",
					Hypotheses: []string{
						"∀n i:num. i * r_fn(n) ≤ n * r_fn(i) + n",
					},
					Conclusion: "is_nadd(r_fn)",
				},
				func(a *Argument, r_fn Term, estimate Fact) {
					a.Do(
						Unfold(eudoxus_slope.IsNaddDef),
						Witness(v.Suc.Apply(v.Zero)), // the Cauchy constant B := 1
					)
					m, n := a.Fix(), a.Fix()
					a.Do(Expect(Simp(Fwd(nat_monus.DistLessEqCases)), // nat_dist(m,n) ≤ p → m ≤ n+p ∧ n ≤ m+p
						Case(
							"the two estimates bound the distance",
							ByArith(estimate.At(n, m), estimate.At(m, n)))))
				})

			// The tight bound lies below n·mk_nadd(r_fn) with fixed slack 2;
			// ArchLemma removes that slack to give the upper bound.
			upperBoundLemma := ctx.Lemma(
				"∀P:(nadd → bool). ∀r_fn:(num → num). "+
					"    (∀n:num. ∀x:nadd. P(x) ⇒ nadd_of_num(n) * x ≤ nadd_of_num(suc(r_fn(n)))) ⇒ "+
					"    ((∀n i:num. i * r_fn(n) ≤ n * r_fn(i) + n) ⇒ "+
					"        ((∀n:num. dest_nadd(mk_nadd(r_fn), n) = r_fn(n)) ⇒ ∀x:nadd. P(x) ⇒ x ≤ mk_nadd(r_fn)))",
				func(a *Argument, P Term, r_fn *TermWrapper, tight, estimate, destAll Fact, x Term, member Fact) {
					mkR := v.MkNadd.Apply(r_fn)
					two := ctx.Numeral(2)
					// At every scale n, x sits within slack 2 of the proposed
					// supremum; ArchLemma removes the slack.
					bound := a.Have(
						"every scaled copy of x fits within slack 2 of the scaled supremum",
						"∀n:num. nadd_of_num(n) * x ≤ nadd_of_num(n) * mk_nadd(r_fn) + nadd_of_num(2)",
						Derive(func(c *Argument) {
							n := c.Fix()

							// In the pointwise order take B = n; the cross-scale estimate
							// supplies the remaining natural inequality.
							slack := c.Have(
								"the tight bound is within slack 2 of the proposed supremum",
								"nadd_of_num(suc(r_fn(n))) ≤ nadd_of_num(n) * mk_nadd(r_fn) + nadd_of_num(2)",
								Derive(func(b *Argument) {
									b.Do(Unfold(eudoxus_slope.NaddLeDef))
									b.Take(n)     // the slope order's own slack constant B := n₀
									n1 := b.Fix() // the point at which the pointwise bound is read
									b.Do(destSimpRig())

									destAt := b.Have(
										"compute the representative at this point",
										MakeProp(v.DestNadd.Apply(mkR, n1).Eq(r_fn.Apply(n1))),
										By(destAll.At(n1)))
									b.Do(destAt.Rw())

									// suc(r_fn₀(n₀))·n₁ = n₁·r_fn₀(n₀) + n₁
									expand := b.Have(
										"expand the successor factor and align the two products",
										MakeProp(times(v.Suc.Apply(r_fn.Apply(n)), n1).Eq(
											v.Plus.Apply(times(n1, r_fn.Apply(n)), n1))),
										ByArith(nat_arith.MulSuc, nat_arith.MulSym))
									b.Show(
										"the cross-scale estimate fits within the slack",
										ByArith(expand, estimate.At(n, n1)))
								}))

							c.Show(
								"the tight bound and the slack bound chain at this scale",
								By(slack, member, tight.At(n, x), eudoxus_slope.LessEqTrans))
						}))

					a.Show(
						"ArchLemma removes the fixed slack, giving the upper bound",
						By(bound, At(ArchLemma, x, mkR, of(two))))
				})

			// The maximum is attained below every competing upper bound.
			// A slack of 1 and ArchLemma then give leastness.
			leastUBLemma := ctx.Lemma(
				"∀P:(nadd → bool). ∀r_fn:(num → num). "+
					"    (∀n:num. "+
					"        (∃x:nadd. P(x) ∧ nadd_of_num(r_fn(n)) ≤ nadd_of_num(n) * x) ∧ "+
					"        (∀s:num. (∃x:nadd. P(x) ∧ nadd_of_num(s) ≤ nadd_of_num(n) * x) ⇒ s ≤ r_fn(n))) ⇒ "+
					"    ((∀n i:num. i * r_fn(n) ≤ n * r_fn(i) + n) ⇒ "+
					"        ((∀n:num. dest_nadd(mk_nadd(r_fn), n) = r_fn(n)) ⇒ "+
					"            ∀M₂:nadd. (∀x:nadd. P(x) ⇒ x ≤ M₂) ⇒ mk_nadd(r_fn) ≤ M₂))",
				func(a *Argument, P Term, r_fn *TermWrapper, maxAll, estimate, destAll Fact, M2 Term, bounds Fact) {
					mkR := v.MkNadd.Apply(r_fn)
					one := ctx.Numeral(1)
					// At every scale n, the proposed supremum sits within slack 1
					// of the competing bound; ArchLemma removes the slack.
					bound := a.Have(
						"every scaled copy of the supremum fits within slack 1 of the scaled bound",
						"∀n:num. nadd_of_num(n) * mk_nadd(r_fn) ≤ nadd_of_num(n) * M₂ + nadd_of_num(1)",
						Derive(func(c *Argument) {
							n := c.Fix()
							x, attained := c.Obtain(
								"choose a member attaining the maximum",
								"∃x:nadd. P(x) ∧ nadd_of_num(r_fn(n)) ≤ nadd_of_num(n) * x",
								By(maxAll.At(n)))

							slack := c.Have(
								"the proposed supremum is within slack 1 of the maximum",
								"nadd_of_num(n) * mk_nadd(r_fn) ≤ nadd_of_num(r_fn(n)) + nadd_of_num(1)",
								Derive(func(b *Argument) {
									b.Do(Unfold(eudoxus_slope.NaddLeDef))
									b.Take(n)     // the slope order's own slack constant B := n₀
									n1 := b.Fix() // the point at which the pointwise bound is read
									b.Do(destSimpRig())

									destAt := b.Have(
										"compute the representative at this point",
										MakeProp(v.DestNadd.Apply(mkR, n1).Eq(r_fn.Apply(n1))),
										By(destAll.At(n1)))
									b.Do(destAt.Rw())

									// r_fn₀(n₀)·n₁ = n₁·r_fn₀(n₀)
									swap := b.Have(
										"align the two products",
										MakeProp(times(r_fn.Apply(n), n1).Eq(times(n1, r_fn.Apply(n)))),
										Cite(nat_arith.MulSym))
									b.Show(
										"the reverse cross-scale estimate fits within the slack",
										ByArith(swap, estimate.At(n1, n)))
								}))

							c.Show(
								"the attained maximum lies below the competing bound at this scale",
								By(
									slack,
									attained,
									bounds.At(x),
									At(eudoxus_slope.LessEqMulLeft, of(n), x, M2),
									At(eudoxus_slope.LessEqTrans, of(r_fn.Apply(n)), mul(of(n), x), mul(of(n), M2)),
									At(eudoxus_slope.LessEqAddRight, of(r_fn.Apply(n)), mul(of(n), M2), of(one)),
									At(eudoxus_slope.LessEqTrans, mul(of(n), mkR),
										v.NaddAdd.Apply(of(r_fn.Apply(n)), of(one)),
										v.NaddAdd.Apply(mul(of(n), M2), of(one)))))
						}))

					a.Show(
						"ArchLemma removes the fixed slack, giving leastness",
						By(bound, At(ArchLemma, mkR, M2, of(one))))
				})

			// Choose the maxima and assemble their least upper bound.
			return ctx.Theorem(headline, func(a *Argument, P Term, bounded Fact) {
				maxEx := a.Have(
					"the per-scale maximum exists at every scale",
					"∀n:num. ∃r:num. "+
						"    (∃x:nadd. P(x) ∧ nadd_of_num(r) ≤ nadd_of_num(n) * x) ∧ "+
						"    (∀s:num. (∃x:nadd. P(x) ∧ nadd_of_num(s) ≤ nadd_of_num(n) * x) ⇒ s ≤ r)",
					Derive(func(b *Argument) {
						n := b.Fix()
						b.Show(
							"take the maximum at this scale",
							By(At(numericalMax, P, n), bounded))
					}))
				rfn, rfnAll := a.Obtain(
					"choose one maximum per scale",
					"∃r_fn:(num → num). ∀n:num. "+
						"    (∃x:nadd. P(x) ∧ nadd_of_num(r_fn(n)) ≤ nadd_of_num(n) * x) ∧ "+
						"    (∀s:num. (∃x:nadd. P(x) ∧ nadd_of_num(s) ≤ nadd_of_num(n) * x) ⇒ s ≤ r_fn(n))",
					By(maxEx))

				tight := a.Have(
					"r_fn₀ tightly bounds P₀",
					"∀n:num. ∀x:nadd. P(x) ⇒ nadd_of_num(n) * x ≤ nadd_of_num(suc(r_fn(n)))",
					By(rfnAll, tightBound))
				estimate := a.Have(
					"r_fn₀ satisfies the Cauchy estimate",
					"∀n i:num. i * r_fn(n) ≤ n * r_fn(i) + n",
					By(rfnAll, slopeIneq))
				isSlope := a.Have(
					"so r_fn₀ is a slope",
					"is_nadd(r_fn)",
					By(estimate, At(isNaddRfn, rfn)))
				destAll := a.Have(
					"the round trip preserves the maximum function",
					"∀n:num. dest_nadd(mk_nadd(r_fn), n) = r_fn(n)",
					By(Normalized, isSlope, At(eudoxus_slope.NaddDef.Membership, rfn)))

				ubAll := a.Have(
					"mk_nadd(r_fn₀) dominates every member of P₀",
					"∀x:nadd. P(x) ⇒ x ≤ mk_nadd(r_fn)",
					By(tight, estimate, destAll, upperBoundLemma))
				least := a.Have(
					"and sits under every competing bound",
					"∀M₂:nadd. (∀x:nadd. P(x) ⇒ x ≤ M₂) ⇒ mk_nadd(r_fn) ≤ M₂",
					By(rfnAll, estimate, destAll, leastUBLemma))

				a.Take(v.MkNadd.Apply(rfn)) // the supremum is mk_nadd(r_fn₀)
				a.Show(
					"take the proposed supremum",
					By(ubAll, least))
			})
		}),
})}

// ---------------------------------------------------------------------------
// The climb from the slope layer to ℝ, in the README's order
// ---------------------------------------------------------------------------
//
// the climb from the slope layer to ℝ, in the README's order: the quotient
// transport (HrealComplete), the two cross-representation bridges
// (RealHrealLemma1 / RealHrealLemma2), completeness for sets that contain
// a nonnegative element (RealCompleteSomePos), and the tower's crown,
// RealComplete.
//
// The completeness theorems carry NaddComplete across the representation
// changes. The bridge lemmas establish the order correspondence between
// hreal and the nonnegative reals that this transport needs.
//
// README §"The chain", last four bullets.

// HrealComplete — the LUB property of the hreal order: a nonempty set
// of nonnegative-real classes with an upper bound has a least upper
// bound, the exact hreal mirror of NaddComplete.
//
// Proof: completeness transported across the nadd_eq quotient onto
// hreal, the nonnegative-real class layer. One section, built on the
// nonneg_real Internal bridges with Skolemized representatives:
//
//	pull each hreal quantity back to a slope representative
//	(surjectivity), instantiate NaddComplete at the representatives
//	with the pulled-back set P := λxn. Q(cls xn), push its slope-level
//	supremum forward as cls(N₀), and rewrite the residual goal down to
//	the representative level (class equations + leOnImage) — where it
//	IS the NaddComplete instance, and β-reduction closes it.
//
// That transport is carried out on the Skolemized clause form of the
// LUB property (lubClauses), which is the shape whose ∃-witnesses the
// representatives directly supply; the headline states the LUB
// property itself and cites it. The slope-side equivalence laws never
// appear here — they are absorbed inside the nonneg_real bridges.
var HrealComplete = hrealCompleteThm{family.Add(registry.ProofEntry{
	Name: "HrealComplete",
	Key:  "prop_d47b8231a92f37c9",
	// The proof is two sections written as a linear script: `lubClauses` is
	// a Go local the headline cites by closure capture.
	Build: family.Sections(
		Statement{
			Binders: "∀Q:(hreal → bool).",
			Hypotheses: []string{
				"∃x:hreal. Q(x)",
				"∃M:hreal. ∀x:hreal. Q(x) ⇒ x ≤ M",
			},
			Conclusion: "∃M:hreal. (∀x:hreal. Q(x) ⇒ x ≤ M) ∧ (∀M':hreal. (∀x:hreal. Q(x) ⇒ x ≤ M') ⇒ M ≤ M')",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			// The order at classes is consumed as an explicit rewrite, so it
			// is held as a cert; Surjectivity is cited at each use.
			leIm := ctx.Dep(nonneg_real.HrealLeDef)

			hreal := MakeType("hreal")
			nadd := MakeType("nadd")

			// cls — the class ⁅t⁆ of a slope t.
			cls := func(t Term) Term {
				return v.HrealOfNadd.Apply(t)
			}

			// StripQuant Skolem mints read by Go code (Cite witnesses) — the
			// slope representatives.
			xn_0 := Var("xn_0", nadd)
			Mn_0 := Var("Mn_0", nadd)
			Mn_1 := Var("Mn_1", nadd)
			y_0 := Var("y_0", nadd)
			// The hreal-level Skolem M'_0 appears only in a claim TEXT —
			// registered unstored.
			ctx.Var("M'_0", hreal)

			// lubClauses: the transport, on the Skolemized clause form of the
			// LUB property. x₀ names a member of Q₀, M₀ an upper bound; N is the
			// supremum the section produces, M'₀ an arbitrary competitor bound
			// and y₀ the member that violates it when it is not one.
			lubClauses := ctx.Lemma(
				"∀x M:hreal. ∀Q:(hreal → bool). ∃N:hreal. ∀M':hreal. ∃y:hreal. "+
					"    ¬Q(x) ∨ (Q(y) ∧ ¬(y ≤ M)) ∨ ((¬Q(M') ∨ M' ≤ N) ∧ (N ≤ M' ∨ (Q(y) ∧ ¬(y ≤ M'))))",
				func(a *Argument, x, M Term, Q *TermWrapper) {
					// The pullback of Q₀ along the class map: P := λxn. Q₀(cls xn).
					xn := Var("xn", nadd)
					pullback := xn.To(Q.Apply(cls(xn)))

					clsX := a.Have(
						"x₀ is the class of a slope (every hreal is)",
						ctx.MakePropText("∃xn:nadd. x₀ = hreal_of_nadd(xn)"),
						By(nonneg_real.HrealDef.Surjectivity))
					a.Do(StripQuant()) // Skolemize the representative xn₀

					clsM := a.Have(
						"M₀ is the class of a slope",
						ctx.MakePropText("∃Mn:nadd. M₀ = hreal_of_nadd(Mn)"),
						By(nonneg_real.HrealDef.Surjectivity))

					a.Do(StripQuant()) // Skolemize the representative Mn₀

					// The slope-level completeness fact at the representatives, for
					// the pulled-back set, unpacked at its ∃N into the slope
					// supremum N₀.
					// NaddComplete's statement ∀-binds only P — x and M are
					// ∃-bound inside its antecedent, pulled into the install
					// prefix by normalization — so no statement-order witness
					// map exists and the tuple is POSITIONAL against the
					// install prefix (x, M, P), the residual class of
					// TestWitnessOrderCensus [prefix-merged].
					N_0, naddLub := a.Unpack(At(MakeFact(ctx.DepNormalized(NaddComplete)), xn_0, Mn_0, pullback))

					a.Do(
						Witness(cls(N_0)), // the hreal supremum is its class
						StripQuant(),      // peel the goal's ∀M' → M'₀
					)

					clsMp := a.Have(
						"M'₀ is the class of a slope",
						ctx.MakePropText("∃Mn:nadd. M'₀ = hreal_of_nadd(Mn)"),
						By(nonneg_real.HrealDef.Surjectivity))

					a.Do(
						StripQuant(),      // Skolemize the representative Mn₁
						naddLub.At(Mn_1),  // the instance's ∀M' at the representative of M'₀
						StripQuant(),      // Skolemize the slope-level LUB witness y₀
						Witness(cls(y_0)), // the hreal witness is its class

						// Rewrite the goal down to representative level: the class
						// equations replace x₀, M₀, M'₀ …
						clsX.Rw(),
						clsM.Rw(),
						clsMp.Rw(),
					)

					a.Show(
						"… and the order at classes turns every hreal_le on classes into "+
							"nadd_le — the goal IS the NaddComplete instance; β-reduction closes",
						Expect(LeanRw(leIm),
							Case(
								"the order at classes, ⁅x⁆ ≤ ⁅y⁆ ⇔ x ≤ y",
								CiteKnown(leIm),
							),
							Case(
								"the goal's clauses are the instance's clauses up to β",
								Basic(),
							),
						),
					)
				})

			// The headline — a nonempty set of hreals with an upper bound has a
			// least one. Its clause form is lubClauses, whose Skolem witnesses
			// (the supremum N, the violator y on a failed premise) are exactly
			// what the quantifier alternation of this statement asks for, so the
			// single cite discharges it.
			return ctx.Theorem(headline,
				CiteNode(lubClauses))
		}),
})}

// RealHrealLemma1 — the cross-representation bridge from nonneg hreals
// to nonneg reals. Establishes that the map
//
//	r : hreal → real, r(y) := mk_real(treal_eq((y, hreal_of_num(0))))
//
// embeds hreal into real as exactly the nonnegative reals, preserving
// the order. Two conjuncts behind a single ∃r witness:
//
// - image characterization: ∀x:real. &0 ≤ x ⇔ ∃y:hreal. x = r(y)
// - order preservation: ∀y z:hreal. (y ≤ z) ⇔ r(y) ≤ r(z)
//
// All the quotient machinery is inherited from the axioms bridges:
// Surjectivity turns an arbitrary real into a class
// mk_real(treal_eq(p)); LessEqOnImage identifies real_le on classes
// with treal_le on representatives; ClassEqIff identifies class
// equality with treal_eq. What remains is hreal-side arithmetic: a
// canonical pair (y, 0) is ≥ the zero pair (LessEqSelfAdd), and a pair
// p with snd(p) ≤ fst(p) — which is what treal_of_num(0) ≤ p unfolds
// to — is treal_eq to a canonical pair at the gap d realized by
// LessEqExists.
//
// What it cites: the axioms bridges (Surjectivity / LessEqOnImage /
// ClassEqIff) deliver every real↔treal transport; nonneg_real supplies the
// hreal-side
// arithmetic (identities + LessEqSelfAdd for nonnegativity,
// LessEqExists for the gap witness, AddSym for the ring collapse);
// pairs.Fst/Snd are the projections the refuter needs after
// treal_le/treal_eq unfold over pair literals.
var RealHrealLemma1 = realHrealLemma1Thm{family.Add(registry.ProofEntry{
	Name: "RealHrealLemma1",
	Key:  "prop_757e0f49bbba958",
	// The proof is three sections written as a linear script, in dependency
	// order: nonneg (bwd image half) → imageFwd (fwd image half) → goal
	// (witness + conjunction assembly); the first two are Go locals the
	// goal cites by closure capture.
	Build: family.Sections(
		"∃r:(hreal → real). (∀x:real. &0 ≤ x ⇔ ∃y:hreal. x = r(y)) ∧ (∀y z:hreal. y ≤ z ⇔ r(y) ≤ r(z))",
		func(ctx *Script, headline string) *GoalStackNode {
			v := registerRealHrealVocab(ctx)

			hreal := MakeType("hreal")
			pair := pairs.ProdType(hreal, hreal)
			// The fixed real in the goal section's image conjunct.
			x_0 := ctx.Var("x_0", MakeType("real"))
			// Parse-scope-only Skolem declarations (claim texts mention them):
			// y_0, p_0 and d_0 (the order gap fst(p_0) = snd(p_0) + d_0).
			ctx.Var("d_0", hreal)
			ctx.Var("y_0", hreal)
			ctx.Var("p_0", pair)

			// nonneg: every canonical class is a nonneg real — the bwd half
			// of the image characterization.
			//
			//	⊢ ∀y:hreal. &0 ≤ mk_real(treal_eq((y, hreal_of_num(0))))
			//
			// The treal-side pre-image ((0,0) ≤ (y₀,0) in treal_le) is pure hreal
			// arithmetic: treal_le unfolds to hreal_le(0+0, y₀+0), the additive
			// identities collapse both sums, and LessEqSelfAdd@(0, y₀) delivers
			// hreal_le(0, y₀). leOnImage (+ the real_of_num / treal_of_num
			// definitional bridges) then carries the treal_le fact back up to the
			// real inequality.
			nonneg := ctx.Lemma("∀y:hreal. &0 ≤ real_of_treal((y, hreal_of_num(0)))",
				func(a *Argument, y Term) {
					trealLe := a.Have(
						"treal_le unfolds to (0+0 ≤ y_0+0); the additive identities + LessEqSelfAdd@(0, y_0) close",
						ctx.MakePropText("(hreal_of_num(0), hreal_of_num(0)) ≤ (y₀, hreal_of_num(0))"),
						Unfold(nonneg_real_formal_diff.TrealLeDef),
						// Fst alone keeps the destructive install: its equation has
						// to rewrite the RESIDENT pair, which is the whole-context
						// simplify ApplyLemma runs and ApplyLemmaPreserve
						// deliberately does not — a different move, not merely a
						// different verb. UseLemma is that install (the bare
						// lemma step plus the close), taking a ThmCert — hence
						// the ctx.Dep round-trip where its neighbours pass the
						// entry.
						UseLemma(ctx.Dep(pairs.Fst)),
						Cite(pairs.Snd),
						Cite(nonneg_real.AddRightId),
						Cite(nonneg_real.AddLeftId),
						Cite(nonneg_real.LessEqSelfAdd),
						CnfRefute())
					a.Show(
						"the order at classes + the real_of_num/treal_of_num bridges "+
							"carry the treal_le fact up to &0 ≤ real_of_treal((y_0, 0))",
						By(
							trealLe,
							ctx.Dep(real_construction.RealLeDef),
							ctx.ConstDefNormalized("real_of_num"),
							ctx.ConstDefNormalized("treal_of_num")))
				})

			// imageFwd: a nonneg real is a canonical class — the fwd half.
			//
			//	⊢ ∀x:real. (&0 ≤ x) ⇒ ∃y:hreal. x = mk_real(treal_eq((y, hreal_of_num(0))))
			//
			// The chain, one Have per transport step:
			// surjectivity makes x₀ a class mk_real(treal_eq(p₀)); leOnImage
			// transports &0 ≤ x₀ down to (treal_of_num(0) ≤ p₀); that
			// unfolds to hreal_le(snd(p₀), fst(p₀)); LessEqExists realizes the
			// gap d₀ with fst(p₀) = snd(p₀) + d₀; then p₀ is treal_eq to the
			// canonical pair (d₀, 0) — the cross-sums fst(p₀)+0 and d₀+snd(p₀)
			// coincide by the gap equation + AddSym — and classEqIff lifts that
			// to the class equation with witness y := d₀.
			imageFwd := ctx.Lemma(Statement{
				Binders: "∀x:real.",
				Hypotheses: []string{
					"&0 ≤ x",
				},
				Conclusion: "∃y:hreal. x = real_of_treal((y, hreal_of_num(0)))",
			},
				// The nonnegativity antecedent is assumed at the boundary; the
				// transport steps below reach it by content.
				func(a *Argument, x Term, _ Fact) {
					// x₀ is the class of a pre-real (every real is).
					_, classOfX := a.Obtain(
						"x₀ is the class of a pre-real p₀",
						ctx.MakePropText("∃p:prod(hreal, hreal). x₀ = real_of_treal(p)"),
						By(real_construction.RealDef.Surjectivity))

					a.Have(
						"transport the nonneg hyp: the order at classes + "+
							"real_of_num-def turn &0 ≤ x_0 into (treal_of_num(0) ≤ p_0)",
						ctx.MakePropText("treal_of_num(0) ≤ p₀"),
						Cite(real_construction.RealLeDef),
						Unfold(real_construction.RealOfNumDef),
						CnfRefute())

					components := a.Have(
						"read the order on components: treal_le/treal_of_num "+
							"unfold + additive identities give snd(p_0) ≤ fst(p_0)",
						ctx.MakePropText("snd(p₀) ≤ fst(p₀)"),
						Unfold(nonneg_real_formal_diff.TrealLeDef),
						Unfold(nonneg_real_formal_diff.TrealOfNumDef),
						Cite(pairs.Fst),
						Cite(pairs.Snd),
						Cite(nonneg_real.AddLeftId),
						// AddRightId's install-simplify collapses fst(p_0)+0 and the
						// claim closes on the cite — no residual refute.
						Cite(nonneg_real.AddRightId))

					// Realize the gap: LessEqExists @ (snd(p_0), fst(p_0)) delivers d
					// with fst(p_0) = snd(p_0) + d.
					d0, _ := a.Obtain(
						"the component order realizes the gap fst(p₀) − snd(p₀)",
						ctx.MakePropText("∃d:hreal. fst(p₀) = snd(p₀) + d"),
						By(components, ctx.Dep(nonneg_real.LessEqExists)))

					canonical := a.Have(
						"p_0 is treal_eq to the canonical pair at the gap: cross-sums "+
							"fst(p_0)+0 and d_0+snd(p_0) coincide by the gap equation + AddSym",
						ctx.MakePropText("treal_eq(p₀, (d₀, hreal_of_num(0)))"),
						Unfold(nonneg_real_formal_diff.TrealEqDef),
						Cite(pairs.Fst),
						Cite(pairs.Snd),
						Cite(nonneg_real.AddRightId),
						Cite(nonneg_real.AddSym))

					a.Take(d0)
					a.Show(
						"witness y := d_0; class equality is treal_eq, which "+
							"lifts the representative equivalence to the class equation",
						By(Normalized, classOfX, canonical, ctx.Dep(real_construction.RealDef.Eq)))
				})

			// The theorem.
			//
			//	⊢ ∃r:(hreal → real). ((∀x. &0 ≤ x ⇔ ∃y. x = r(y))
			//	 ∧ (∀y z. (y ≤ z) ⇔ r(y) ≤ r(z)))
			//
			// Witness r := λy. mk_real(treal_eq((y, hreal_of_num(0)))). The image
			// conjunct splits into the two proved halves — NOTE the engine
			// normalizes the iff with the ∃-side on the left, so the ⇒ direction
			// is nonneg's and the ⇐ direction is imageFwd's. The order conjunct
			// is leOnImage at the canonical pairs — treal_le((y₀,0), (z₀,0))
			// unfolds to hreal_le(y₀+0, z₀+0) and AddRightId collapses both sums
			// to hreal_le(y₀, z₀), closing on the lemma install — no residual
			// refute.
			return ctx.Theorem(headline, func(a *Argument) {
				// The witness map λy. real_of_treal((y, 0)).
				yBind := ctx.Var("y_wit", hreal)
				zero := v.hreal_of_num.Apply(ctx.Numeral(0))
				rWitness := yBind.To(v.real_of_treal.Apply(v.pair.Apply(yBind, zero)))

				a.Do(Witness(rWitness))
				a.Do(SplitConj(
					Case(
						"image: &0 ≤ x_0 ⇔ ∃y. x_0 = r(y) — the two proved halves",
						StripQuant(),
						SplitIff(
							Forward(
								"a nonneg x_0 is a canonical class — the imageFwd instance at x_0 closes by resolution",
								Cite(imageFwd, x_0),
								Basic(),
							),
							Backward(
								"an ∃-witnessed canonical class is nonneg — nonneg's ∀-fact + the witness equation carry it to x_0",
								Cite(nonneg),
								CnfRefute(),
							),
						),
					),
					Case(
						"order: (y₀ ≤ z₀) ⇔ r(y₀) ≤ r(z₀) — the order at classes → "+
							"treal_le on canonical pairs; treal_le-def + AddRightId close",
						StripQuant(),
						Derive(func(a *Argument) {
							a.Show(
								"the order at classes sends the class order to treal_le((y₀,0), "+
									"(z₀,0)), which unfolds to hreal_le(y₀+0, z₀+0) with both sums collapsed",
								Cite(real_construction.RealLeDef),
								Unfold(nonneg_real_formal_diff.TrealLeDef),
								Cite(pairs.Fst),
								Cite(pairs.Snd),
								Cite(nonneg_real.AddRightId))
						}),
					),
				))
			})
		}),
})}

// realHrealVocab — the statement vocabulary this file's proofs read
// programmatically (the witness-map builders). Consts the
// section/claim texts or Unfolds name but no Go code touches
// (dest_real, real_le, hreal_add, hreal_le, fst, snd, real_of_num,
// treal_le, treal_of_num, treal_eq) are registered unstored —
// parse-scope only. Distinct from the family's completeVocab because
// the file crosses the real/treal boundary (the class map
// real_of_treal) and needs the hreal-pair "," constructor —
// polymorphic vs the num-prod "," other members declare.
type realHrealVocab struct {
	real_of_treal *TermWrapper
	hreal_of_num  *TermWrapper
	pair          *TermWrapper // (,) at hreal × hreal
}

func registerRealHrealVocab(ctx *Script) *realHrealVocab {
	hreal := MakeType("hreal")
	real := MakeType("real")
	pair := pairs.ProdType(hreal, hreal)
	pairToBool := MakeFun(pair, TypeBool)
	pairRel := MakeFun(pair, MakeFun(pair, TypeBool))

	// Parse-scope-only registrations.
	ctx.Const("dest_real", MakeFun(real, pairToBool))
	ctx.Const("real_le", MakeFun(real, MakeFun(real, TypeBool)))
	ctx.Const("hreal_add", MakeFun(hreal, MakeFun(hreal, hreal)))
	ctx.Const("hreal_le", MakeFun(hreal, MakeFun(hreal, TypeBool)))
	ctx.Const("treal_le", pairRel)
	ctx.Const("treal_of_num", MakeFun(NumType, pair))
	ctx.Const("real_of_num", MakeFun(NumType, real))
	ctx.Const("treal_eq", pairRel)
	pairs.ProjectionsAt(ctx, hreal, hreal)

	return &realHrealVocab{
		real_of_treal: ctx.Const("real_of_treal", MakeFun(pair, real)),
		hreal_of_num:  ctx.Const("hreal_of_num", MakeFun(NumType, hreal)),
		pair:          ctx.Const(",", MakeFun(hreal, MakeFun(hreal, pair))),
	}
}

// RealHrealLemma2 — order faithfulness makes the embedding injective,
// so functions.InjectiveLeftInverse supplies h. On the nonnegative
// reals, the image characterization turns its left inverse into a
// right inverse as well.
var RealHrealLemma2 = realHrealLemma2Thm{family.Add(registry.ProofEntry{
	Name: "RealHrealLemma2",
	Key:  "prop_7fd9727f5a47d108",
	Build: family.Theorem(
		"∃h:(real → hreal). ∃r:(hreal → real). "+
			"    (∀x:hreal. h(r(x)) = x) ∧ "+
			"    ((∀x:real. &0 ≤ x ⇒ r(h(x)) = x) ∧ "+
			"        ((∀x:hreal. &0 ≤ r(x)) ∧ (∀x y:hreal. x ≤ y ⇔ r(x) ≤ r(y))))",
		func(a *Argument) {
			r, rLaws := a.UnpackAs[Fun[nonneg_real.Hreal, Real]](RealHrealLemma1, "r")
			laws := a.Conjuncts(
				rLaws,
				"the nonnegative reals are exactly the image of r",
				"r preserves and reflects order")

			injective := a.Have(
				"equal images force both hreal inequalities, hence equality",
				"injective_on(𝕌, r)",
				Derive(func(b *Argument) {
					b.Do(Unfold(functions.InjectiveOnDef))
					x := b.FixAs[nonneg_real.Hreal]()
					y := b.FixAs[nonneg_real.Hreal]()
					equal := b.Assume()
					b.Show(
						"order faithfulness and antisymmetry identify the two preimages",
						By(
							equal,
							laws[1].At(x, x),
							laws[1].At(x, y),
							laws[1].At(y, x),
							nonneg_real.LessEqAntisym.At(x, x),
							nonneg_real.LessEqAntisym.At(x, y)))
				}))
			h, leftInverse := a.ObtainAs[Fun[Real, nonneg_real.Hreal]](
				"an injective map has a left inverse",
				"∃h:(real → hreal). ∀x:hreal. h(r(x)) = x",
				By(injective, functions.InjectiveLeftInverse.At(r)))

			rightInverse := a.Have(
				"r undoes h on the nonnegative reals",
				"∀u:real. &0 ≤ u ⇒ r(h(u)) = u",
				Derive(func(b *Argument) {
					u := b.FixAs[Real]()
					nonnegative := b.Assume()
					y, preimage := b.ObtainAs[nonneg_real.Hreal](
						"a nonnegative real has an hreal preimage",
						"∃y:hreal. u = r(y)",
						By(nonnegative, laws[0].At(u)))
					b.Show(
						"the left inverse identifies h(u) with its preimage",
						By(Normalized, preimage, leftInverse.At(y)))
				}))
			nonnegative := a.Have(
				"every value of r is nonnegative",
				"∀x:hreal. &0 ≤ r(x)",
				Derive(func(b *Argument) {
					b.FixAs[nonneg_real.Hreal]("z")
					b.Show(
						"r(z) belongs to the image of r",
						By(laws[0].At(b.TermAs[Real]("r(z)"))))
				}))

			a.Take(h)
			a.Take(r)
			a.Show(
				"the two inverse laws and the embedding laws give the correspondence",
				By(leftInverse, rightInverse, nonnegative, laws[1]))
		}),
})}

// RealCompleteSomePos — a set of reals that contains a nonnegative
// element and is bounded above has a least upper bound: the
// hreal→real transport step.
//
// RealHrealLemma2 packages the correspondence between the two
// representations — an embedding r : hreal → real (order-faithful,
// nonnegative-valued) with a one-sided inverse h : real → real's
// nonnegative part. A set P of reals that contains some x₀ ≥ 0 pulls
// back along r to the hreal set Q := λy. P(r(y)), which inherits
// "nonempty" (h(x₀) ∈ Q, since r(h(x₀)) = x₀) and "bounded"
// (candidates above the bound transport through h). HrealComplete
// applied to Q at the anchors h(x₀), h(M₀) yields an hreal supremum
// N₀; its image r(N₀) is the real supremum. Totality + transitivity of
// real_le glue the two order languages in the final refutation (an
// arbitrary candidate bound M' need not be nonnegative — totality
// against &0 ≤ x₀ splits the cases the correspondence doesn't cover).
//
// That transport is carried out on the Skolemized clause form of the
// LUB property (lubClauses), which is the shape whose ∃-witnesses the
// pullback directly supplies; the headline states the LUB property
// itself and cites it.
var RealCompleteSomePos = realCompleteSomePosThm{family.Add(registry.ProofEntry{
	Name: "RealCompleteSomePos",
	Key:  "prop_a8decae8c4608f61",
	// The proof is two sections written as a linear script: `lubClauses` is
	// a Go local the headline cites by closure capture.
	Build: family.Sections(
		Statement{
			Binders: "∀P:(real → bool).",
			Hypotheses: []string{
				"∃x:real. P(x) ∧ &0 ≤ x",
				"∃M:real. ∀x:real. P(x) ⇒ x ≤ M",
			},
			Conclusion: "∃M:real. (∀x:real. P(x) ⇒ x ≤ M) ∧ (∀M':real. (∀x:real. P(x) ⇒ x ≤ M') ⇒ M ≤ M')",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			hreal := MakeType("hreal")

			// lubClauses: the transport, on the Skolemized clause form of the
			// LUB property. x names the nonnegative member of P, M an upper
			// bound; N is the supremum the section produces, M' an arbitrary
			// competitor bound and y the member that violates it when it is not
			// one.
			lubClauses := ctx.Lemma(
				"∀x M:real. ∀P:(real → bool). ∃N:real. ∀M':real. ∃y:real. "+
					"    ¬P(x) ∨ ¬(&0 ≤ x) ∨ (P(y) ∧ ¬(y ≤ M)) ∨ ((¬P(M') ∨ M' ≤ N) ∧ (N ≤ M' ∨ (P(y) ∧ ¬(y ≤ M'))))",
				func(a *Argument, x, M Term, P *TermWrapper) {
					// The correspondence delivers the maps h, r and their laws,
					// read as three facts so the close grounds each at its points.
					h, r, laws := a.Unpack2(ctx.DepNormalized(RealHrealLemma2), "h", "r")
					back := a.Have(
						"r undoes h on the nonnegative reals",
						"∀u:real. &0 ≤ u ⇒ r(h(u)) = u",
						By(Normalized, laws))
					nonneg := a.Have(
						"every value of r is nonnegative",
						"∀a:hreal. &0 ≤ r(a)",
						By(Normalized, laws))
					order := a.Have(
						"r preserves and reflects the order",
						"∀a b:hreal. a ≤ b ⇔ r(a) ≤ r(b)",
						By(Normalized, laws))

					// The pullback of P along the embedding: Q := λy:hreal. P(r(y)).
					y := Var("y", hreal)
					pullback := y.To(P.Apply(r.Apply(y)))

					// hreal completeness of the pullback set, anchored at h(x)
					// (the nonnegative member's class) and h(M) (the bound's);
					// N is the hreal supremum.
					N, sup := a.Unpack(At(MakeFact(ctx.DepNormalized(HrealComplete)),
						h.Apply(x), h.Apply(M), pullback))

					// The real supremum is its image r(N), tested against an
					// arbitrary competitor M'.
					a.Take(r.Apply(N))
					Mp := a.Fix()
					zero := a.Term("&0")
					a.Show(
						"the hreal supremum's property at h(M') transports through r; "+
							"totality and transitivity at &0 settle a competitor below &0",
						By(
							sup.At(h.Apply(Mp)),
							order,
							back.At(x),
							back.At(M),
							back.At(Mp),
							nonneg.At(N),
							At(real_construction.LessEqTotal, zero, Mp),
							At(real_construction.LessEqTrans, zero, x, M),
							At(real_construction.LessEqTrans, zero, x, Mp),
							At(real_construction.LessEqTrans, Mp, zero, r.Apply(N))))
				})

			// The headline — a set of reals with a nonnegative element and an
			// upper bound has a least one. Its clause form is lubClauses, whose
			// Skolem witnesses (the supremum N, the violator y on a failed
			// premise) are exactly what the quantifier alternation of this
			// statement asks for, so the single cite discharges it.
			return ctx.Theorem(headline,
				CiteNode(lubClauses))
		}),
})}

// RealComplete — Dedekind completeness of ℝ, the tower's crown: every
// nonempty set of reals bounded above has a least upper bound.
//
// RealCompleteSomePos already proves this for sets containing a
// NONNEGATIVE element. The general case reduces to it by translation:
// a set P with member x₀ shifts to Q := λy. P(y + x₀), which contains
// &0 (since &0 + x₀ = x₀ ∈ P) — nonnegative regardless of x₀'s sign —
// and is bounded by M₀ - x₀ whenever M₀ bounds P. SomePos gives Q a
// supremum N₀; translating back, N₀ + x₀ is the supremum of P.
//
// The translation algebra is derived just above from the
// real_construction ordered-field basis: subAdd cancels the shift on members, shiftLe /
// shiftRe move the shift across ≤ in the two directions the transport
// needs.
var RealComplete = realCompleteThm{family.Add(registry.ProofEntry{
	Name: "RealComplete",
	Key:  "prop_ad2ad9c255530e8c",
	// The proof is five sections written as a linear script: the three
	// translation-algebra lemmas and the transport section are Go locals
	// the headline reaches by closure capture.
	Build: family.Sections(
		Statement{
			Binders: "∀P:(real → bool).",
			Hypotheses: []string{
				"∃x:real. P(x)",
				"∃M:real. ∀x:real. P(x) ⇒ x ≤ M",
			},
			Conclusion: "∃M:real. (∀x:real. P(x) ⇒ x ≤ M) ∧ (∀M':real. (∀x:real. P(x) ⇒ x ≤ M') ⇒ M ≤ M')",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// real vocabulary (term builders; ≤/+/- in section texts parse as
			// sugar over the same consts).
			real := MakeType("real")
			rr := MakeFun(real, MakeFun(real, real))
			radd := ctx.Const("real_add", rr)
			rsub := ctx.Const("real_sub", rr)
			rneg := ctx.Const("real_neg", MakeFun(real, real))
			ofNum := ctx.Const("real_of_num", MakeFun(NumType, real))
			zero := ofNum.Apply(ctx.Const("_0", NumType)) // &0, the additive identity on real

			add := func(a, b Term) Term { return radd.Apply(a).Apply(b) }
			sub := func(a, b Term) Term { return rsub.Apply(a).Apply(b) }
			neg := func(a Term) Term { return rneg.Apply(a) }

			// StripQuant Skolem mints, resolved by name: N₀ (the shifted set's
			// supremum), M'₀ (candidate bound), y₀ (SomePos's violating witness
			// for the M'₀-x₀ instance).
			N0 := ctx.Var("N_0", real)
			Mp0 := ctx.Var("M'_0", real)
			y0 := ctx.Var("y_0", real)

			sym := ctx.DepNormalized(real_construction.AddSym)
			assoc := ctx.DepNormalized(real_construction.AddAssoc)
			linv := ctx.DepNormalized(real_construction.AddLeftInv)
			lid := ctx.DepNormalized(real_construction.AddLeftId)
			grp := algebra.Group{Op: radd, Neg: rneg,
				Sym: sym, Assoc: assoc, LInv: linv, LId: lid}

			// subAdd: subtracting then adding back a shift is the identity —
			// (a - b) + b = a. Pure additive-group algebra: expand real_sub, then
			// (a + -b) + b = a + (-b + b) = a + &0 = &0 + a = a by ground
			// instances of assoc / left-inverse / sym / left-identity.
			subAdd := ctx.Lemma("∀a b:real. a - b + b = a",
				func(arg *Argument, a, b Term) {
					arg.Do(Unfold(real_ring.RealSubDef), // (a₀ + -b₀) + b₀ = a₀
						// Each cite's eqSimplify rewrites the goal a step down the
						// chain (a₀+-b₀)+b₀ → a₀+(-b₀+b₀) → a₀+&0 → &0+a₀; the
						// left-identity cite then closes the residual identity outright.
						Cite(real_construction.AddAssoc, a, neg(b), b),
						Cite(real_construction.AddLeftInv, b),
						Cite(real_construction.AddSym, a, zero),
						Cite(real_construction.AddLeftId),
					)
				})

			// shiftLe: a shift moves across ≤ into a subtraction on the bound —
			// (a + z) ≤ M ⇔ a ≤ (M - z). Each direction is one ground instance of
			// LessEqAddLeftImp (adding -z resp. z on the left) plus the group
			// algebra that cancels the shift.
			shiftLe := ctx.Lemma("∀z a M:real. a + z ≤ M ⇔ a ≤ M - z",
				func(arg *Argument, z, a, M Term) {
					arg.Do(Unfold(real_ring.RealSubDef)) // iff over a₀ ≤ (M₀ + -z₀)
					// SplitIff case order is (B ⊢ A, A ⊢ B) for a goal A ⇔ B. The
					// cancellation ladders are the algebra kit's computed micro-folds.
					arg.Iff()
					arg.Forward(
						"from (a₀ + z₀) ≤ M₀, add -z₀ on the left and cancel -z₀+(a₀+z₀) to a₀",
						Cite(real_construction.LessEqAddLeftImp, neg(z), add(a, z), M),
						Cite(real_construction.AddSym, a, z),
						grp.CancelShiftNeg(z, a),
						Cite(real_construction.AddSym, neg(z), M),
						CnfRefute(),
					)
					arg.Backward(
						"from a₀ ≤ M₀ - z₀, add z₀ on the left and cancel z₀+(M₀+-z₀) to M₀",
						Cite(real_construction.LessEqAddLeftImp, z, a, add(M, neg(z))),
						Cite(real_construction.AddSym, z, a),
						Cite(real_construction.AddSym, M, neg(z)),
						grp.CancelShift(z, M),
						CnfRefute(),
					)
				})

			// shiftRe: the reverse transport — (x - z) ≤ B ⇒ x ≤ (B + z). Adding z
			// on the left of the hypothesis and cancelling z + (x + -z) to x. Only
			// this direction is used (translating a member of the shifted set back
			// up), so the section states the implication, not the iff.
			shiftRe := ctx.Lemma(Statement{
				Binders: "∀z x B:real.",
				Hypotheses: []string{
					"x - z ≤ B",
				},
				Conclusion: "x ≤ B + z",
			},
				func(a *Argument, z, x, B Term) {
					a.Do(Unfold(real_ring.RealSubDef),
						Cite(real_construction.LessEqAddLeftImp, z, add(x, neg(z)), B),
						Cite(MakeFact(grp.Sym), x, neg(z)),
						grp.CancelShift(z, x),
						Cite(MakeFact(grp.Sym), z, B),
						CnfRefute(),
					)
				})

			// lubClauses: the transport. Bind the member x₀, bound M₀, set P₀;
			// apply SomePos to the shifted set λy.P₀(y + x₀) anchored at &0 (its
			// nonnegative member) and M₀ - x₀ (its bound); the real supremum is
			// N₀ + x₀. Ground the instance at the one candidate the residual
			// quantifies over (M'₀ - x₀, the candidate bound pushed down), ground
			// the algebra at every atom the case analysis touches, and let
			// resolution do the case analysis.
			lubClauses := ctx.Lemma(
				"∀x M:real. ∀P:(real → bool). ∃N:real. ∀M':real. ∃y:real. "+
					"    ¬P(x) ∨ (P(y) ∧ ¬(y ≤ M)) ∨ ((¬P(M') ∨ M' ≤ N) ∧ (N ≤ M' ∨ (P(y) ∧ ¬(y ≤ M'))))",
				func(a *Argument, x, M Term, P *TermWrapper) {
					// The shifted set: Q := λy:real. P₀(y + x₀).
					y := Var("y", real)
					shifted := y.To(P.Apply(add(y, x)))

					// The SomePos instance for Q. A handle rather than a Fact
					// because its spine grounding is consumed by a STEP that
					// RENAMES it: the StripQuant below Skolemizes the ground
					// instance's ∃y, so the hyp the closing By cites is neither
					// the source nor `f.At(w…)` but their Skolemized descendant,
					// which only capture tracking can follow. (`a.Do(f.At(w…))`
					// materializes a ground instance on the spine, but there is
					// no Fact for what a subsequent ∃-peel leaves behind, and
					// Unpack rejects a resident fact carrying witnesses.)
					somePosAt := NewHypHandle("somePosAt")

					a.Do( // SomePos on the shifted set: nonnegative member &0, bound M₀-x₀.
						somePosAt.From(Cite(MakeFact(ctx.DepNormalized(RealCompleteSomePos)),
							zero, sub(M, x), shifted)),
						StripQuant(),                  // Skolemize the shifted supremum N₀
						Witness(add(N0, x)),           // P₀'s supremum is N₀ + x₀
						StripQuant(),                  // Skolemize the candidate bound M'₀
						somePosAt.Ground(sub(Mp0, x)), // the instance at the pushed-down candidate
						StripQuant(),                  // Skolemize its violating witness y₀
						// The translation algebra, ground at every atom the refutation
						// visits: members translate up via subAdd/shiftRe, bounds
						// translate down via shiftLe; &0 ∈ Q via AddLeftId, &0 ≤ &0 via
						// totality at (&0, &0).
						By(
							somePosAt,
							At(subAdd, Mp0, x),
							At(shiftLe, x, N0, Mp0),
							At(shiftLe, x, y0, Mp0),
							At(shiftLe, x, y0, M),
							At(shiftRe, x, Mp0, N0),
							At(real_construction.AddLeftId, x),
							At(real_construction.LessEqTotal, zero, zero)),
					)
				})

			// The headline — every nonempty set of reals with an upper bound
			// has a least one. Its clause form is lubClauses, whose Skolem
			// witnesses (the supremum N, the violator y on a failed premise) are
			// exactly what the quantifier alternation of this statement asks for,
			// so the single cite discharges it.
			return ctx.Theorem(headline,
				CiteNode(lubClauses))
		}),
})}
