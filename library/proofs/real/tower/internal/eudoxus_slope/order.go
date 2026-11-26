// order.go — the ordering of slopes.

package eudoxus_slope

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The slope order (`nadd_le`
// ---------------------------------------------------------------------------
//
// the slope order (`nadd_le`: pointwise up to a bound), its
// equivalence-compatibility, and its compatibility with the ring
// operations: the preorder laws and totality, the bottom element, the
// order's defining subtraction, and monotonicity in + and ·.
//
// README: the "order" bullet.

// LessEqWellDef — equivalent slopes bound one another in both directions,
// so transitivity transports the order along either pair.
var LessEqWellDef = lessEqWellDefThm{family.Add(registry.ProofEntry{
	Name: "LessEqWellDef",
	Key:  "prop_9547e6e77946f063",
	Build: family.Theorem(
		Statement{
			Binders: "∀x x' y y':nadd.",
			Hypotheses: []string{
				"nadd_eq(x, x')",
				"nadd_eq(y, y')",
			},
			Conclusion: "x ≤ y ⇔ x' ≤ y'",
		},
		func(a *Argument, x, xp, y, yp *Expr[Nadd], equivs Fact) {
			xOrders := a.Have(
				"equivalent x slopes bound each other",
				"x ≤ x' ∧ x' ≤ x",
				By(equivs, LessEqAntisym.At(x, xp)))
			yOrders := a.Have(
				"equivalent y slopes bound each other",
				"y ≤ y' ∧ y' ≤ y",
				By(equivs, LessEqAntisym.At(y, yp)))
			a.Iff()
			a.Forward(
				"transport through the original slopes",
				func(b *Argument, xy Fact) {
					xpy := b.Have(
						"x' ≤ x ≤ y",
						"x' ≤ y",
						By(xy, xOrders, LessEqTrans.At(xp, x, y)))
					b.Show(
						"x' ≤ y ≤ y'",
						By(xpy, yOrders, LessEqTrans.At(xp, y, yp)))
				})
			a.Backward(
				"transport through the primed slopes",
				func(b *Argument, xpyp Fact) {
					xyp := b.Have(
						"x ≤ x' ≤ y'",
						"x ≤ y'",
						By(xpyp, xOrders, LessEqTrans.At(x, xp, yp)))
					b.Show(
						"x ≤ y' ≤ y",
						By(xyp, yOrders, LessEqTrans.At(x, yp, y)))
				})
		}),
})}

// LessEqTrans — the slope order is transitive:
//
//	⊢ ∀x y z : nadd. (x ≤ y) ∧ (y ≤ z) ⇒ (x ≤ z)
//
// nadd_le(x, y) unfolds to "x is bounded by y up to a constant":
// ∃B. ∀n. x(n) ≤ y(n) + B (writing x(n) for dest_nadd(x, n)). Two
// such bounds chain through the middle slope y: from
// x(n) ≤ y(n) + B₁ and y(n) ≤ z(n) + B₂ pointwise,
// x(n) ≤ z(n) + (B₁ + B₂). That one sentence is the whole proof,
// split into 2 sections:
//
// - chain: the bound-chaining step, stated over the unfolded bounds;
// witness B := B₁ + B₂, then pointwise arith.
// - goal: assume the two order facts, unfold nadd_le, and hand the two
// bounds to chain.
//
// No lemma deps at all: the ≤/+ chaining is a single gated-arith
// close.
var LessEqTrans = lessEqTransThm{family.Add(registry.ProofEntry{
	Name: "LessEqTrans",
	Key:  "prop_64b95af6e8e1a15e",
	// The proof is two sections written as a linear script: `chain` is a Go
	// local the goal cites by closure capture.
	Build: family.Sections(
		Statement{
			Binders: "∀x y z:nadd.",
			Hypotheses: []string{
				"x ≤ y",
				"y ≤ z",
			},
			Conclusion: "x ≤ z",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// chain — the chaining step, on the unfolded bounds: the sum of the
			// two constants bounds the composite defect at every point. The two
			// premises arrive as Facts, so grounding them at the evaluation
			// point is `.At(n)` rather than a second copy of their statement
			// text.
			chain := ctx.Lemma(
				"∀x y z:nadd. ∀B₁ B₂:num. "+
					"    (∀n:num. dest_nadd(x, n) ≤ dest_nadd(y, n) + B₁) ⇒ "+
					"    (∀n:num. dest_nadd(y, n) ≤ dest_nadd(z, n) + B₂) ⇒ "+
					"    ∃B:num. ∀n:num. dest_nadd(x, n) ≤ dest_nadd(z, n) + B",
				func(a *Argument, x, y, z, B1, B2 Term, xy, yz Fact) {
					a.Take(v.sum(B1, B2)) // B := B₁ + B₂ witnesses the chained bound
					n := a.Fix()          // at the fixed point n₀ …
					a.Show(
						"x(n₀) ≤ y(n₀) + B₁ ≤ (z(n₀) + B₂) + B₁ — the two bounds at n₀, chained by linear arithmetic",
						ByArith(xy.At(n), yz.At(n)))
				})

			// goal: assume the two order facts and unfold nadd_le in them and in
			// the conclusion — what is left IS chain, at the slopes just fixed
			// and the two bounds' constants.
			return ctx.Theorem(headline,
				// The trailing `_ Fact` absorbs the ⇒: the pair of order facts is
				// assumed at the boundary, then split by the simplify below, so
				// the body never needs it by name.
				func(a *Argument, x, y, z Term, _ Fact) {
					a.Do(
						TrivialSimplify(), // split the assumption into nadd_le(x₀, y₀) and nadd_le(y₀, z₀)
						// Both assumptions and the conclusion become bound
						// statements ∃B. ∀n. ·(n) ≤ ·(n) + B.
						Unfold(NaddLeDef),
					)
					bXY, xy := a.Unpack(a.Hyp("∃B:num. ∀n:num. dest_nadd(x, n) ≤ dest_nadd(y, n) + B"))
					bYZ, yz := a.Unpack(a.Hyp("∃B:num. ∀n:num. dest_nadd(y, n) ≤ dest_nadd(z, n) + B"))
					a.Show(
						"the two bounds chain through y",
						By(xy, yz, At(chain, x, y, z, bXY, bYZ)))
				})
		}),
})}

// LessEqAntisym — antisymmetry-up-to-equivalence of the slope order:
//
//	⊢ ∀x y : nadd. nadd_eq(x, y) ⇔ ((x ≤ y) ∧ (y ≤ x))
//
// Both sides unfold to uniform bounds on the underlying functions
// f = dest_nadd(x, ·), g = dest_nadd(y, ·): equivalence bounds the
// defect nat_dist(f n, g n), order bounds one side. The two directions
// are the two readings of nat_monus.DistLessEqCases
// (nat_dist(m, n) ≤ p ⇔ (m ≤ n+p ∧ n ≤ m+p)):
//
// - a defect bound B splits into the two one-sided bounds at the
// same B, which witness nadd_le(x, y) and nadd_le(y, x);
// - one-sided bounds B₀, B₁ rebuild a defect bound at B₀ + B₁,
// each estimate absorbing the other's slack.
var LessEqAntisym = lessEqAntisymThm{family.Add(registry.ProofEntry{
	Name: "LessEqAntisym",
	Key:  "prop_c5b43435042c71f2",
	// goal — unfold both relations to their bounds, then split the iff into
	// its two nat_monus.DistLessEqCases readings.
	Build: family.Theorem("∀x y:nadd. nadd_eq(x, y) ⇔ x ≤ y ∧ y ≤ x",
		func(a *Argument, x, y Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			// B₀, B₁ the two one-sided bounds and n₀ the index minted by the
			// rebuild direction's StripQuants.
			B0 := ctx.Var("B_0", NumType)
			B1 := ctx.Var("B_1", NumType)
			n0 := ctx.Var("n_0", NumType)

			// rebuildDefectBound proves the ⇐ direction after unfolding:
			//
			//	∃B.∀n. f n ≤ g n + B, ∃B.∀n. g n ≤ f n + B ⊢ ∃B.∀n. nat_dist(f n, g n) ≤ B
			//
			// with f = dest_nadd(x₀, ·), g = dest_nadd(y₀, ·): Skolemize the
			// two one-sided bounds as B₀, B₁, take B := B₀ + B₁, and settle
			// the ground instance at each index n₀ by linear arithmetic.
			rebuildDefectBound := Derive(func(b *Argument) {
				fn0 := v.at(x, n0) // f(n₀)
				gn0 := v.at(y, n0) // g(n₀)
				b.Do(
					// nat_dist(m, n) ≤ p ⇔ (m ≤ n + p ∧ n ≤ m + p).
					Cite(nat_monus.DistLessEqCases),
					// Split the ∧ of the two one-sided bounds into separate hyps.
					Basic(),
					// Skolemize their bounds: B₀ (x-side), B₁ (y-side).
					StripQuant(),
					StripQuant(),
				)
				// The two-sided reading of a dist bound — located by the cited
				// statement itself, not by a restatement of it.
				distCases := b.Hyp(ctx.DepNormalized(nat_monus.DistLessEqCases))
				boundXY := b.Hyp("∀n:num. dest_nadd(x₀, n) ≤ dest_nadd(y₀, n) + B₀")
				boundYX := b.Hyp("∀n:num. dest_nadd(y₀, n) ≤ dest_nadd(x₀, n) + B₁")
				b.Do(
					// The defect bound: B := B₀ + B₁.
					Witness(v.sum(B0, B1)),
					// The index the bound must hold at: n₀.
					StripQuant(),
				)
				b.Show(
					"each one-sided estimate holds with the other's slack "+
						"to spare — linear arithmetic over the ground atoms",
					ByArith(
						// the two one-sided bounds at n₀:
						// f(n₀) ≤ g(n₀) + B₀ and g(n₀) ≤ f(n₀) + B₁
						boundXY.At(n0),
						boundYX.At(n0),
						// nat_monus.DistLessEqCases at the defect pair and combined slack:
						// nat_dist(f(n₀), g(n₀)) ≤ B₀ + B₁ ⇔ (f(n₀) ≤ g(n₀) + (B₀ + B₁) ∧ …)
						distCases.At(fn0, gn0, v.sum(B0, B1))))
			})

			a.Do(
				// nadd_eq(x₀, y₀) becomes its defect bound
				// ∃B. ∀n. nat_dist(dest_nadd(x₀, n), dest_nadd(y₀, n)) ≤ B; each
				// nadd_le becomes its one-sided bound ∃B. ∀n. … ≤ … + B.
				Unfold(NaddEqDef),
				Unfold(NaddLeDef),
				SplitIff(
					Forward(
						"a defect bound B splits (nat_monus.DistLessEqCases) into the two "+
							"one-sided bounds at the same B — B witnesses both nadd_le sides",
						// nat_dist(m, n) ≤ p ⇔ (m ≤ n + p ∧ n ≤ m + p).
						Cite(nat_monus.DistLessEqCases),
						// Separate the two order bounds into their own leaves.
						Basic(),
						// Each leaf: the defect's B, read one-sidedly through
						// nat_monus.DistLessEqCases, is verbatim the order bound's witness.
						Finally(CnfRefute()),
					),
					Backward(
						"the one-sided bounds B₀, B₁ rebuild the defect bound at B₀+B₁ — "+
							"nat_monus.DistLessEqCases splits it, each side holding with slack",
						rebuildDefectBound,
					),
				),
			)
		}),
})}

// LessEqTotal — the slope order is total:
//
//	⊢ ∀y x : nadd. (y ≤ x) ∨ (x ≤ y)
//
// nadd_le(x, y) unfolds to "x is bounded by y up to a constant":
// ∃B. ∀n. x(n) ≤ y(n) + B (writing x(n) for dest_nadd(x, n)). The
// proof, in 3 sections:
//
// - dichotomy: either (x ≤ y), or x exceeds y past EVERY
// threshold: ∀C. ∃m. y(m) + C < x(m). Definitional unfolding plus
// the classical ¬∃∀ → ∀∃¬ swap; the only place the nadd_le
// definition and the ≤/< duality (nat_order.NotLessEq) are touched.
// - margin: either (x ≤ y), or a SINGLE point n ≠ 0 already
// witnesses a B-margin violation: y(n) + B < x(n). Reading the
// dichotomy's excess at threshold C := B + x(0) pins both
// conjuncts: the violation exceeds the B-margin by a spare x(0),
// and it cannot sit at 0 where the threshold absorbs x(0) itself.
// (An anonymous lemma of this member — no standalone entry.)
// - goal: totality. If ¬(y ≤ x), the margin at B := B₀ + B₁ —
// the sum of the two slopes' Cauchy constants (Cauchy) —
// yields n₀ ≠ 0 with x(n₀) + (B₀ + B₁) < y(n₀). That one excess
// persists at every scale n₁: cross-multiplying the violation and
// the two Cauchy bounds at (n₀, n₁) gives
// n₀·x(n₁) ≤ n₀·(y(n₁) + (B₀ + B₁)), and cancelling n₀ ≠ 0 shows
// x(n₁) ≤ y(n₁) + (B₀ + B₁) — exactly (x ≤ y) with witness
// B₀ + B₁.
//
// The only lemma deps are nat_monus.DistLessEqCases, nat_order.LessEqMulCancel, and nat_order.NotLessEq:
// all ring/order bookkeeping (distributivity, commutativity,
// ≤-chaining) is decided by gated arith, with the one nonlinear
// regrouping stated as a ring identity that arithmetic decides.
// nat_order.LessEqMulCancel serves both multiplicative moves — its ⇐ direction
// scales (valid for any factor) and its ⇒ direction cancels (given
// n₀ ≠ 0).
var LessEqTotal = lessEqTotalThm{family.Add(registry.ProofEntry{
	Name: "LessEqTotal",
	Key:  "prop_4b7fd8926468a351",
	// The proof is three sections written as a linear script: `dichotomy`
	// and `margin` are Go locals the later sections cite by closure capture.
	Build: family.Sections(
		"∀y x:nadd. y ≤ x ∨ x ≤ y",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			zero := ctx.Numeral(0) // the margin threshold's x(0) and the m₀ = 0 split

			// In order of appearance: the margin's (B₀, x₀, y₀, m₀), the goal's
			// Cauchy constants (B₀ for x₀, B₁ for y₀), its margin point n₀ and
			// arbitrary scale n₁.
			B_0 := ctx.Var("B_0", NumType)
			B_1 := ctx.Var("B_1", NumType)
			m_0 := ctx.Var("m_0", NumType)
			n_0 := ctx.Var("n_0", NumType)
			n_1 := ctx.Var("n_1", NumType)
			x_0 := ctx.Var("x_0", MakeType("nadd"))
			y_0 := ctx.Var("y_0", MakeType("nadd"))

			// fx / fy are the slopes' underlying functions at t: dest_nadd(x₀, t)
			// and dest_nadd(y₀, t).
			fx := func(t Term) Term { return v.at(x_0, t) }
			fy := func(t Term) Term { return v.at(y_0, t) }

			// dichotomy — either x is boundedly below y, or it exceeds y past
			// every threshold.
			dichotomy := ctx.Lemma("∀x y:nadd. x ≤ y ∨ (∀C:num. ∃m:num. dest_nadd(y, m) + C < dest_nadd(x, m))",
				func(a *Argument) {
					a.Do(
						// ≤/< duality bridge, resident for the refute below.
						Cite(nat_order.NotLessEq),
						StripQuant(),
						Unfold(NaddLeDef),
						// One refute: ¬(∃B.∀n. x(n) ≤ y(n) + B) prenexes to
						// ∀B.∃n.¬(x(n) ≤ y(n) + B); at each threshold C the witnessed
						// failure flips through nat_order.NotLessEq into the strict excess
						// y(n) + C < x(n).
						CnfRefute(),
					)
				})

			// margin — the margin dichotomy: either le holds, or one point n ≠ 0
			// already violates the B-margin. From the dichotomy at threshold
			// C := B + x(0).
			margin := ctx.Lemma("∀B:num. ∀x y:nadd. ∃n:num. "+
				"    x ≤ y ∨ (n ≠ 0 ∧ dest_nadd(y, n) + B < dest_nadd(x, n))",
				func(a *Argument) {
					a.Do(
						Cite(dichotomy),
						StripQuant(),
					)
					// Ground the dichotomy at (x₀, y₀) — through its partial
					// instance at x₀ — then drop both spent ∀-sources.
					dichotomyAll := a.Hyp(dichotomy.PromisedThm())
					a.Do(dichotomyAll.At(x_0))
					dichotomyAtX := a.Hyp("∀y:nadd. x₀ ≤ y ∨ (∀C:num. ∃m:num. dest_nadd(y, m) + C < dest_nadd(x₀, m))")
					a.Do(
						dichotomyAtX.At(y_0),
						Clear(dichotomyAll, dichotomyAtX),
						// We may assume x₀ is not bounded by y₀.
						Unless(
							v.NaddLe.Apply(x_0, y_0),
							"(x₀ ≤ y₀) holds — the left disjunct settles the margin claim at any witness point",
							TrivialNormalized(),
						),
						// ¬nadd_le(x₀, y₀): the all-threshold excess survives; read it at
						// C := B₀ + x₀(0).
						lessEqTotalMarginFalse(v, x_0, y_0, m_0, B_0, zero, fx),
					)
				})

			// Totality: if ¬nadd_le(y, x), the margin at the canonical bound
			// B₀ + B₁ hands the persistence argument one violating point, and
			// nadd_le(x, y) follows with that same bound as witness.
			return ctx.Theorem(headline,
				func(a *Argument) {
					a.Do(
						StripQuant(),
						// We may assume the left disjunct fails.
						Unless(
							v.NaddLe.Apply(y_0, x_0),
							"(y₀ ≤ x₀) holds — that is the goal's left disjunct outright",
							TrivialNormalized(),
						),
						// ¬nadd_le(y₀, x₀): prove nadd_le(x₀, y₀) with witness B₀ + B₁, the
						// sum of the two Cauchy constants.
						lessEqTotalGoalFalse(v, margin, x_0, y_0, n_0, n_1, B_0, B_1, fx, fy),
					)
				})
		}),
})}

// lessEqTotalMarginFalse: with ¬nadd_le(x₀, y₀), the dichotomy leaves
// ∀C.∃m. y₀(m) + C < x₀(m). The instance C := B₀ + x₀(0) gives a
// point m₀ whose excess carries a spare x₀(0) — enough for both
// conjuncts of the margin claim.
func lessEqTotalMarginFalse(v *slopeVocab, x_0, y_0 Term, m_0 *TermWrapper, B_0, zero Term,
	fx func(Term) Term) Action {
	return Derive(func(a *Argument) {
		// The case hypothesis resolves the dichotomy disjunction: only
		// the all-threshold excess remains against ¬nadd_le(x₀, y₀).
		a.Do(TrivialSimplify())
		caseNotLe := a.Hyp(Not(v.NaddLe.Apply(x_0, y_0)))
		excessAll := a.Hyp("∀C:num. ∃m:num. dest_nadd(y₀, m) + C < dest_nadd(x₀, m)")
		// The excess at the witnessed point: y₀(m₀) + (B₀ + x₀(0)) < x₀(m₀).
		excess := ResidentHyp(MakeProp(v.LtOp.Apply(
			v.sum(v.at(y_0, m_0), v.sum(B_0, fx(zero))), fx(m_0))))
		a.Do(
			// Excess at threshold B₀ + x₀(0); StripQuant Skolemizes the
			// witnessed point as m₀.
			excessAll.At(v.sum(B_0, fx(zero))),
			// Drop the spent ¬le case hypothesis and ∀C source.
			Clear(caseNotLe, excessAll),
			StripQuant(),
			Witness(m_0),
			// The witnessed point cannot sit at 0, where the threshold
			// absorbs x₀(0) itself.
			Unless(
				m_0.Eq(zero),
				"m₀ = 0: substituting collapses the excess to y₀(0) + (B₀ + x₀(0)) < x₀(0) — numerically absurd",
				Given(func(b *Argument, m0Zero Fact) {
					b.Do(ByArith(m0Zero, excess))
				}),
			),
			// m₀ ≠ 0: the ≠-conjunct is the case hypothesis; the strict
			// excess sheds its spare x₀(0) to the bare B₀-margin.
			TrivialSimplify(),
			ByArith(excess),
		)
	})
}

// lessEqTotalGoalFalse: the persistence argument. Fix the Cauchy
// constants B₀ (for x₀) and B₁ (for y₀), extract the margin point
// n₀ ≠ 0 with x₀(n₀) + (B₀ + B₁) < y₀(n₀), unfold the goal to the
// pointwise bound at an arbitrary scale n₁, and chain three
// cross-multiplied estimates into n₀·x₀(n₁) ≤ n₀·(y₀(n₁) + (B₀ + B₁));
// cancel n₀.
func lessEqTotalGoalFalse(v *slopeVocab, margin *GoalStackNode,
	x_0, y_0, n_0, n_1, B_0, B_1 Term,
	fx, fy func(Term) Term) Action {
	sum := v.sum(B_0, B_1) // B₀ + B₁, the margin and the le-witness
	// The four cross-multiplied quantities at the pair (n₀, n₁):
	n0x1 := v.mul(n_0, fx(n_1)) // n₀·x₀(n₁)
	n1x0 := v.mul(n_1, fx(n_0)) // n₁·x₀(n₀)
	n0y1 := v.mul(n_0, fy(n_1)) // n₀·y₀(n₁)
	n1y0 := v.mul(n_1, fy(n_0)) // n₁·y₀(n₀)
	// The two Cauchy defects B₀·(n₀+n₁), B₁·(n₀+n₁):
	defX := v.mul(B_0, v.sum(n_0, n_1))
	defY := v.mul(B_1, v.sum(n_0, n_1))
	// The margin-shifted values: the violated threshold x₀(n₀)+(B₀+B₁)
	// and the goal's slack side y₀(n₁)+(B₀+B₁).
	xMargin := v.sum(fx(n_0), sum)
	ySlack := v.sum(fy(n_1), sum)

	return Derive(func(a *Argument) {
		// The case hypothesis prunes the settled left disjunct.
		a.Do(TrivialSimplify())

		// Cauchy for each slope; Unpack Skolemizes the bounds as B₀
		// (for x₀) and B₁ (for y₀).
		_, cauchyX := a.Unpack(At(Cauchy, x_0))
		_, cauchyY := a.Unpack(At(Cauchy, y_0))
		// The margin at B₀ + B₁, oriented y₀-vs-x₀; its point
		// Skolemizes as n₀.
		_, marginDisj := a.Unpack(At(margin, sum, y_0, x_0))

		a.Do(
			marginDisj.DismissLeft(
				"the margin's (y₀ ≤ x₀) disjunct contradicts the case hypothesis",
				TrivialNormalized(),
			),
			// The surviving disjunct: n₀ ≠ 0 violates the (B₀+B₁)-margin,
			// x₀(n₀) + (B₀ + B₁) < y₀(n₀). Show that excess persists at
			// every scale.
			//
			// ¬nadd_le(y₀, x₀) is spent; unfold the goal and commit
			// to the witness B₀ + B₁. StripQuant then fixes the
			// arbitrary scale n₁.
			Clear(a.Hyp(Not(v.NaddLe.Apply(y_0, x_0)))),
			Unfold(NaddLeDef),
			Witness(sum),
			StripQuant(),
			// Ground both Cauchy bounds at the pair (n₀, n₁) — through
			// their partial instances at n₀ — then drop the ∀-sources
			// so nothing re-absorbs the instances.
			cauchyX.At(n_0),
		)
		cauchyXAtN0 := a.Hyp("∀n:num. dist((n₀ * dest_nadd(x₀, n), n * dest_nadd(x₀, n₀))) ≤ B₀ * (n₀ + n)")
		a.Do(cauchyXAtN0.At(n_1), cauchyY.At(n_0))
		cauchyYAtN0 := a.Hyp("∀n:num. dist((n₀ * dest_nadd(y₀, n), n * dest_nadd(y₀, n₀))) ≤ B₁ * (n₀ + n)")
		a.Do(
			cauchyYAtN0.At(n_1),
			Clear(cauchyX, cauchyY, cauchyXAtN0, cauchyYAtN0),
			// nat_dist(a, b) ≤ c splits into the two one-sided bounds;
			// one instance per grounded Cauchy fact.
			Cite(nat_monus.DistLessEqCases, n0x1, n1x0, defX),
			Cite(nat_monus.DistLessEqCases, n0y1, n1y0, defY),
		)
		// x₀'s and y₀'s Cauchy estimates at the pair (n₀, n₁), and the
		// two-sided reading of each.
		cauchyXPair := a.Hyp(v.le(v.d(n0x1, n1x0), defX))
		cauchyYPair := a.Hyp(v.le(v.d(n0y1, n1y0), defY))
		distCasesX := a.Hyp(v.le(v.d(n0x1, n1x0), defX).Eq(
			v.le(n0x1, v.sum(n1x0, defX)).And(v.le(n1x0, v.sum(n0x1, defX)))))
		distCasesY := a.Hyp(v.le(v.d(n0y1, n1y0), defY).Eq(
			v.le(n0y1, v.sum(n1y0, defY)).And(v.le(n1y0, v.sum(n0y1, defY)))))
		legX := a.Have(
			"x₀'s Cauchy leg — n₀·x₀(n₁) exceeds n₁·x₀(n₀) by at most the defect B₀·(n₀+n₁)",
			MakeProp(v.le(n0x1, v.sum(n1x0, defX))),
			ByArith(cauchyXPair, distCasesX))
		legY := a.Have(
			"y₀'s opposite Cauchy leg — n₁·y₀(n₀) exceeds n₀·y₀(n₁) by at most the defect B₁·(n₀+n₁)",
			MakeProp(v.le(n1y0, v.sum(n0y1, defY))),
			ByArith(cauchyYPair, distCasesY))
		// The margin point: n₀ ≠ 0 with x₀(n₀) + (B₀+B₁) < y₀(n₀).
		pointNonzero := a.Hyp("n₀ ≠ 0")
		violation := a.Hyp(v.LtOp.Apply(xMargin, fy(n_0)))
		scaled := a.Have(
			"the margin violation scaled by n₁ — the ⇐ direction "+
				"of nat_order.LessEqMulCancel, sound for any factor",
			MakeProp(v.le(v.mul(n_1, xMargin), n1y0)),
			ByArith(violation, At(nat_order.LessEqMulCancel, n_1, xMargin, fy(n_0))))
		scaledBound := a.Have(
			"n₀·x₀(n₁) ≤ n₀·(y₀(n₁) + (B₀+B₁)) — linear once one ring "+
				"identity regroups (B₀+B₁)·(n₀+n₁) between the two scalings",
			MakeProp(v.le(n0x1, v.mul(n_0, ySlack))),
			Derive(func(b *Argument) {
				ring := b.Have(
					"the ring identity — all distributivity/commutativity content, decided by gated arith",
					MakeProp(v.sum(v.mul(n_1, xMargin), v.mul(n_0, ySlack)).
						Eq(v.sum(v.sum(n1x0, n0y1), v.sum(defX, defY)))),
					ByArith())
				b.Show(
					"Cauchy leg + scaled violation + Cauchy leg + identity — a pure linear combination",
					ByArith(legX, legY, scaled, ring))
			}))
		a.Show(
			"cancel the factor n₀ — the ⇒ direction of nat_order.LessEqMulCancel, using n₀ ≠ 0",
			ByArith(scaledBound, pointNonzero, At(nat_order.LessEqMulCancel, n_0, fx(n_1), ySlack)))
	})
}

// NaddEqImpliesLessEq — equivalence implies order:
//
//	⊢ ∀x y : nadd. nadd_eq(x, y) ⇒ (x ≤ y)
//
// Both relations are uniform bounds on the slopes' underlying
// functions. Equivalence bounds the distance — ∃B. ∀n.
// nat_dist(dest_nadd(x, n), dest_nadd(y, n)) ≤ B — while the order asks
// only the one-sided estimate ∃B. ∀n. dest_nadd(x, n) ≤
// dest_nadd(y, n) + B. nat_monus.DistLessEqCases reads a distance bound as the
// conjunction of the two one-sided estimates, so the equivalence
// defect's bound B already witnesses the order bound: drop the second
// conjunct. (This is the ⇒-half of LessEqAntisym's equivalence,
// derived standalone — the direct two-step estimate is cheaper than
// citing the ⇔ and projecting a conjunct.)
var NaddEqImpliesLessEq = naddEqImpliesLessEqThm{family.Add(registry.ProofEntry{
	Name: "NaddEqImpliesLessEq",
	Key:  "prop_74dfbb1a2392ffd7",
	// The closure binds NOTHING: both unfolds and the refute work under the
	// ∀-prefix, so there is no leading strip for a parameter to absorb.
	Build: family.Theorem(Statement{
		Binders: "∀x y:nadd.",
		Hypotheses: []string{
			"nadd_eq(x, y)",
		},
		Conclusion: "x ≤ y",
	},
		func(a *Argument) {
			a.Do(
				// The assumed equivalence becomes its distance bound:
				// ∃B. ∀n. nat_dist(dest_nadd(x, n), dest_nadd(y, n)) ≤ B.
				Unfold(NaddEqDef),
				// The order to show becomes its one-sided bound:
				// ∃B. ∀n. dest_nadd(x, n) ≤ dest_nadd(y, n) + B.
				Unfold(NaddLeDef),
				// nat_dist(m, n) ≤ p ⇔ (m ≤ n + p ∧ n ≤ m + p): a distance bound is the
				// conjunction of the two one-sided bounds.
				Cite(nat_monus.DistLessEqCases),
				// One refute: the equivalence's B, read one-sidedly through
				// nat_monus.DistLessEqCases, is verbatim the order's witness.
				CnfRefute(),
			)
		}),
})}

// ZeroLessEq — the zero slope is the bottom element of the slope
// preorder:
//
//	⊢ ∀x : nadd. (nadd_of_num(0) ≤ x)
//
// The mirror of nat_order.ZeroLessEq one layer up; the completeness
// chapter's arch lemmas consume it.
//
// nadd_le(a, b) unfolds to a uniform pointwise bound
// ∃B. ∀n. dest_nadd(a, n) ≤ dest_nadd(b, n) + B; at a = nadd_of_num(0)
// the left side collapses:
//
//	dest_nadd(nadd_of_num(0), n) = 0 · n -- OfNum
//	 = 0 -- Mul (zero clause)
//
// so any bound serves — B := 0 leaves 0 ≤ dest_nadd(x, n) + 0, which
// nat_order.ZeroLessEq closes (0 is the bottom of ℕ ≤).
var ZeroLessEq = zeroLessEqThm{family.Add(registry.ProofEntry{
	Name: "ZeroLessEq",
	Key:  "prop_cba546341889d63d",
	// Unfold nadd_le, witness B := 0, name the collapse of the left side as
	// a claim, then close with the ℕ-level 0 ≤ …
	Build: family.Theorem("∀x:nadd. nadd_of_num(0) ≤ x",
		func(a *Argument, x Term) {
			ctx := a.Ctx()
			ops(ctx)
			zero := ctx.Numeral(0)
			ctx.Var("n_0", NumType)
			a.Do(
				// nadd_le unfolds to ∃B. ∀n. dest_nadd(nadd_of_num(0), n)
				// ≤ dest_nadd(x₀, n) + B.
				Unfold(NaddLeDef),
				Witness(zero), // the LHS collapses to 0, so B := 0 serves
				StripQuant(),  // fix the pointwise index n₀
				Derive(func(d *Argument) {
					// The header's two-leg ladder, as one named intermediate.
					// Neither equation can carry witnesses: both arrive as goal
					// REWRITES rather than premises (OfNum reads the left side as
					// 0·n₀, Mul's zero clause — cited as the recursion pack —
					// collapses that to 0), so there is no resident hyp to ground.
					// The claim is what puts the collapse in the checked layer.
					collapse := d.Have(
						"the embedded zero is pointwise zero — OfNum then Mul's zero clause",
						"dest_nadd(nadd_of_num(0), n₀) = 0",
						By(OfNum, nat_arith.Mul))
					d.Show(
						"0 ≤ dest_nadd(x₀, n₀) + 0 — ℕ's bottom element at the bound-shifted right side",
						By(collapse, nat_order.ZeroLessEq))
				}),
			)
		}),
})}

// LessEqSelfAdd — a slope is below itself plus anything:
//
//	⊢ ∀x y : nadd. (x ≤ (x + y))
//
// nadd_le(x, w) unfolds to "x is bounded by w up to a constant":
// ∃B. ∀n. x(n) ≤ w(n) + B (writing x(n) for dest_nadd(x, n)). Against
// the sum x + y the bound holds already at B := 0: pointwise the
// sum's value IS x(n) + y(n) (the Add dest equation), and
// x(n) ≤ (x(n) + y(n)) + 0 is linear arithmetic over ℕ — a summand
// never exceeds the sum, which the gated arith close covers directly
// (no nat_order.LessEqAdd dep), leaving Add as the only dep.
var LessEqSelfAdd = lessEqSelfAddThm{family.Add(registry.ProofEntry{
	Name: "LessEqSelfAdd",
	Key:  "prop_2beecd79cf31ac0e",
	// goal — unfold the order, then bound the defect by zero.
	Build: family.Theorem("∀x y:nadd. x ≤ x + y",
		func(a *Argument, x, y Term) {
			ctx := a.Ctx()
			// n₀ is the challenge index — the Add instance is taken at
			// (n₀, x, y).
			n0 := ctx.Var("n_0", NumType)
			a.Do(
				// x₀ ≤ x₀ + y₀ unfolds to
				// ∃B. ∀n. dest_nadd(x₀, n) ≤ dest_nadd((x₀ + y₀), n) + B.
				Unfold(NaddLeDef),
				// The bound holds with nothing to spare: B := 0.
				Witness(ctx.Numeral(0)),
				StripQuant(),
				// At the index n₀, the sum's value is the pointwise sum:
				// dest_nadd(x₀, n₀) + dest_nadd(y₀, n₀) = dest_nadd((x₀ + y₀), n₀),
				// and x₀(n₀) ≤ (x₀(n₀) + y₀(n₀)) + 0 — a summand never
				// exceeds the sum; linear arithmetic.
				ByArith(At(Add, n0, x, y)),
			)
		}),
})}

// LessEqExists — the preorder gap is witnessed by slope addition:
//
//	⊢ ∀x y : nadd. (x ≤ y) ⇒ ∃d. nadd_eq(y, (x + d))
//
// (x ≤ y) unfolds to a uniform bound x(n) ≤ y(n) + B (writing
// x(n) for dest_nadd(x, n)). The witness is the pointwise difference:
// choose d(n) with y(n) + B = x(n) + d(n) — nat_order.LessEqExists
// gives the per-point choice, Skolemization assembles the choices into
// one function — and package d as a slope via mk_nadd. Four stages:
//
// - realizes: the heart. If d satisfies the slack equation
// y(n) + B = x(n) + d(n) at EVERY n, then y ≈ x + mk_nadd(d).
// Its analytic core proves d is a slope: cross-multiplying the
// slack equation at m and n turns d's Cauchy defect
// nat_dist(m·d(n), n·d(m)) into a shifted copy of the defects of x
// and y plus a constant-slack dist, so B₁ + (B₂ + B₀) — the two
// carriers' Cauchy constants plus the slack — bounds it. The
// membership axiom of the nadd typedef then lets mk_nadd carry d,
// and the slack equation read through dest(x + mk_nadd(d)) shows
// every pointwise dist equals the constant B₀.
// - weaken: existentially quantify the realizing slope (mk_nadd(d)
// becomes some e), so the assembly step needs no term surgery.
// - assemble: from the pointwise bound, per-point choice + Skolem
// produce the slack function d; weaken applies.
// - goal: assume the order, unfold nadd_le, hand the bound to
// assemble.
//
// Cauchy supplies the two carriers' bounds; Add is the pointwise
// dest equation of slope addition and is_nadd_0 the typedef's
// nonemptiness witness; nat_order.LessEqExists drives the choice
// assembly. LessEqRefl / LessEqTrans are the ℕ-level order facts, not
// this package's slope-order siblings.
var LessEqExists = lessEqExistsThm{family.Add(registry.ProofEntry{
	Name: "LessEqExists",
	Key:  "prop_dfea450850e28a8d",
	// The proof is four sections written as a linear script: each stage is a
	// Go local the next one cites by closure capture, and the estimate's
	// sub-arguments are closure-local Action builders over the same terms.
	Build: family.Sections(
		Statement{
			Binders: "∀x y:nadd.",
			Hypotheses: []string{
				"x ≤ y",
			},
			Conclusion: "∃d:nadd. nadd_eq(y, x + d)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// Engine-minted Skolems, in order of appearance inside realizes:
			// the section binders (B₀, x₀, y₀, d₀), the carriers' Cauchy
			// constants (B₁ for x₀, B₂ for y₀), the defect's index pair
			// (m₀, n₀). k is the fresh binder of the CongrArg contexts.
			// Claim construction references them by these names. (d_0 is a
			// FUNCTION here — num → num — so it stays a per-member declaration.)
			B_0 := ctx.Var("B_0", NumType)
			B_1 := ctx.Var("B_1", NumType)
			B_2 := ctx.Var("B_2", NumType)
			k := ctx.Var("k", NumType)
			m_0 := ctx.Var("m_0", NumType)
			n_0 := ctx.Var("n_0", NumType)
			d_0 := ctx.Var("d_0", MakeFun(NumType, NumType))
			x_0 := ctx.Var("x_0", MakeType("nadd"))
			y_0 := ctx.Var("y_0", MakeType("nadd"))

			// Both axioms are claimed — the retraction feeds the refuter's cache
			// for the membership-route refutes; only membership is read back by
			// name (realizes: mk_nadd must carry the difference).
			membershipThm := naddMembership(ctx)

			// The named estimate terms.
			var t estTerms
			fx := func(i Term) Term { return v.at(x_0, i) }
			fy := func(i Term) Term { return v.at(y_0, i) }
			mn := v.sum(m_0, n_0)

			t.mdn = v.mul(m_0, d_0.Apply(n_0))
			t.ndm = v.mul(n_0, d_0.Apply(m_0))
			t.mxn = v.mul(m_0, fx(n_0))
			t.nxm = v.mul(n_0, fx(m_0))
			t.myn = v.mul(m_0, fy(n_0))
			t.nym = v.mul(n_0, fy(m_0))
			t.mB = v.mul(m_0, B_0)
			t.nB = v.mul(n_0, B_0)

			t.distD = v.d(t.mdn, t.ndm)
			t.distX = v.d(t.mxn, t.nxm)
			t.distY = v.d(t.myn, t.nym)
			t.distB = v.d(t.mB, t.nB)

			t.shiftL = v.sum(t.mdn, t.mxn)
			t.shiftR = v.sum(t.ndm, t.nxm)
			t.sumL = v.sum(t.mxn, t.mdn)
			t.sumR = v.sum(t.nxm, t.ndm)
			t.distShift = v.d(t.shiftL, t.shiftR)

			t.defX = v.mul(B_1, mn)
			t.defY = v.mul(B_2, mn)
			t.defB = v.mul(B_0, mn)

			t.distYB = v.sum(t.distY, t.distB)
			t.distXY = v.sum(t.distX, t.distY)
			t.distYBX = v.sum(t.distYB, t.distX)
			t.distXYB = v.sum(t.distXY, t.distB)
			t.defXY = v.sum(t.defX, t.defY)
			t.defXYB = v.sum(t.defXY, t.defB)
			t.defSum = v.sum(t.defX, v.sum(t.defY, t.defB))
			t.defAll = v.mul(v.sum(B_1, v.sum(B_2, B_0)), mn)

			// constantLeg: nat_dist(m₀·B₀, n₀·B₀) ≤ B₀·(m₀ + n₀). Pull the common
			// factor B₀ out of the dist, then scale nat_dist(m₀, n₀) ≤ m₀ + n₀.
			constantLeg := Derive(func(a *Argument) {
				factored := a.Have(
					"commute both products so nat_monus.DistLeftMul factors B₀ out of the dist",
					MakeProp(t.distB.Eq(v.mul(B_0, v.d(m_0, n_0)))),
					By(
						At(nat_arith.MulSym, m_0, B_0),
						At(nat_arith.MulSym, n_0, B_0),
						At(nat_monus.DistLeftMul, B_0, m_0, n_0)))
				a.Show(
					"dist(m₀, n₀) ≤ m₀ + n₀ scales by B₀ — the multiplication-cancellation law, one refute to chain",
					By(
						factored,
						At(nat_monus.DistAddBound, m_0, n_0),
						At(nat_order.LessEqMulCancel, B_0, v.d(m_0, n_0), v.sum(m_0, n_0))))
			})

			// triangleStep: nat_dist(m₀·d(n₀), n₀·d(m₀)) ≤ distX + (distY + distB).
			// First: the SHIFTED dist — both defect terms plus the matching x
			// terms — equals, through the scaled slack equations, a dist of
			// y-terms + slack-terms, which nat_monus.DistAdd2 splits into distY + distB.
			// Then nat_monus.DistAdd2Rev recovers d's bare defect from the shifted dist at
			// the cost of one extra distX, and the pieces chain by transitivity.
			triangleStep := func(scaledAtN, scaledAtM Fact) Action {
				return Derive(func(a *Argument) {
					// The ℕ-addition AC deriver: pure permute-and-reassociate
					// steps below are one self-proving `ac` premise each, so the
					// rearrangement is written once — as its two endpoints.
					addAC := nat_arith.AddAC(ctx)
					split := a.Have(
						"rewrite both sides through the scaled slack equations; "+
							"nat_monus.DistAdd2 splits the resulting dist of sums",
						MakeProp(v.le(v.d(t.sumL, t.sumR), t.distYB)),
						scaledAtN.CongrArg(k.To(v.d(k, t.sumR))),
						scaledAtM.CongrArg(k.To(v.d(v.sum(t.myn, t.mB), k))),
						Cite(nat_monus.DistAdd2))
					commuteL := a.Have(
						"commute the left shifted sum",
						MakeProp(t.shiftL.Eq(t.sumL)),
						Cite(nat_arith.AddSym))
					commuteR := a.Have(
						"commute the right shifted sum the same way",
						MakeProp(t.shiftR.Eq(t.sumR)),
						Cite(nat_arith.AddSym))
					commuted := a.Have(
						"the split bound in commuted spelling",
						MakeProp(v.le(t.distShift, t.distYB)),
						By(split, commuteL, commuteR))
					widened := a.Have(
						"add distX to both sides of the shifted bound — "+
							"nat_order.LessEqAdd2 with reflexivity on the added leg",
						MakeProp(v.le(v.sum(t.distShift, t.distX), t.distYBX)),
						By(
							commuted,
							nat_order.LessEqRefl,
							At(nat_order.LessEqAdd2, t.distShift, t.distX, t.distYB, t.distX)))
					// Recover d's bare defect from the shifted dist — nat_monus.DistAdd2Rev
					// pays one distX.
					a.Show(
						"chain — d's defect ≤ shifted + distX = rotated legs (ℕ-level transitivity)",
						By(
							widened,
							// rotate (distY + distB) + distX onto distX + (distY + distB)
							addAC.Eq(t.distYBX, t.distXYB),
							At(nat_monus.DistAdd2Rev, t.mdn, t.mxn, t.ndm, t.nxm),
							At(nat_order.LessEqTrans, t.distD, v.sum(t.distShift, t.distX), t.distYBX)))
				})
			}

			// combineLegs: from the triangle bound and the three per-leg bounds,
			// conclude nat_dist(m₀·d(n₀), n₀·d(m₀)) ≤ (B₁ + (B₂ + B₀))·(m₀ + n₀):
			// expand the composite constant, add the legs pairwise, reassociate,
			// and chain.
			combineLegs := func(triangle, constLegFact, cauchyXmn, cauchyYmn Fact) Action {
				return Derive(func(a *Argument) {
					addAC := nat_arith.AddAC(ctx)
					expand := a.Have(
						"expand the composite constant over (m₀ + n₀)",
						MakeProp(t.defAll.Eq(t.defSum)),
						Cite(nat_arith.RightAddDistrib))
					legsXY := a.Have(
						"x's and y's defect legs add — nat_order.LessEqAdd2 on the two grounded Cauchy bounds",
						MakeProp(v.le(t.distXY, t.defXY)),
						By(cauchyXmn, cauchyYmn, At(nat_order.LessEqAdd2, t.distX, t.distY, t.defX, t.defY)))
					legsAll := a.Have(
						"nat_order.LessEqAdd2 again — the two-leg sum against the constant leg",
						MakeProp(v.le(t.distXYB, t.defXYB)),
						By(legsXY, constLegFact, At(nat_order.LessEqAdd2, t.distXY, t.distB, t.defXY, t.defB)))
					// The triangle bound, the summed leg bounds, and the two ring
					// identities knit into the witnessed slope bound.
					a.Show(
						"transitivity (ℕ-level) closes: defect ≤ three legs = expanded composite bound",
						By(
							triangle,
							legsAll,
							expand,
							// reassociate the three per-leg bounds
							addAC.Eq(t.defXYB, t.defSum),
							At(nat_order.LessEqTrans, t.distD, t.distXYB, t.defXYB)))
				})
			}

			// differenceIsSlope — the analytic core. With the slack equation
			// resident, bound d's Cauchy defect at an arbitrary index pair
			// (m₀, n₀):
			//
			//	nat_dist(m₀·d(n₀), n₀·d(m₀)) ≤ (B₁ + (B₂ + B₀))·(m₀ + n₀)
			//
			// The route: scale the slack equation by m₀ (at n₀) and by n₀ (at m₀);
			// then d's defect equals a SHIFTED copy of x's defect, and the shifted
			// pair rewrites — through the scaled slack equations — into y's defect
			// against the constant pair (m₀·B₀, n₀·B₀). Three legs result
			// (x's defect, y's defect, the constant leg), each bounded by its own
			// B·(m₀+n₀); adding and regrouping gives the stated bound.
			differenceIsSlope := func(slackEq Fact) Action {
				return Derive(func(a *Argument) {
					// Cauchy for each carrier; grounding at (x₀, y₀) Skolemizes the
					// constants as B₁ and B₂.
					a.Do(Cite(Cauchy))
					cauchy := a.Hyp(ctx.DepNormalized(Cauchy))
					a.Do(cauchy.At(x_0))
					a.Do(cauchy.At(y_0))
					a.Do(StripQuant())
					a.Do(StripQuant())
					cauchyX := a.Hyp("∀m n:num. dist((m * dest_nadd(x₀, n), n * dest_nadd(x₀, m))) ≤ B₁ * (m + n)")
					cauchyY := a.Hyp("∀m n:num. dist((m * dest_nadd(y₀, n), n * dest_nadd(y₀, m))) ≤ B₂ * (m + n)")
					// The slope bound for d: the carriers' constants plus the slack.
					a.Take(v.sum(B_1, v.sum(B_2, B_0)))
					a.Do(StripQuant())
					// The slack equation, grounded at n₀ and at m₀ — the scaled
					// copies below rewrite through these instances.
					a.Do(slackEq.At(n_0))
					slackAtN := a.Hyp("dest_nadd(y₀, n₀) + B₀ = dest_nadd(x₀, n₀) + d₀(n₀)")
					a.Do(slackEq.At(m_0))
					slackAtM := a.Hyp("dest_nadd(y₀, m₀) + B₀ = dest_nadd(x₀, m₀) + d₀(m₀)")
					scaledAtN := a.Have(
						"the slack equation at n₀ scaled by m₀ — congruence under m₀·(—), then distribute",
						MakeProp(v.sum(t.myn, t.mB).Eq(v.sum(t.mxn, t.mdn))),
						slackAtN.CongrArg(k.To(v.Times.Apply(m_0, k))),
						Cite(nat_arith.LeftAddDistrib))
					scaledAtM := a.Have(
						"the slack equation at m₀ scaled by n₀ — same congruence at the other index",
						MakeProp(v.sum(t.nym, t.nB).Eq(v.sum(t.nxm, t.ndm))),
						slackAtM.CongrArg(k.To(v.Times.Apply(n_0, k))),
						Cite(nat_arith.LeftAddDistrib))
					// With both scaled equations in hand, bound the three legs.
					constLegFact := a.Have(
						"the constant leg — the slack's own dist obeys the linear bound",
						MakeProp(v.le(t.distB, t.defB)),
						constantLeg)
					triangle := a.Have(
						"the triangle step — d's defect is bounded by x's defect + y's defect + the constant leg",
						MakeProp(v.le(t.distD, t.distXYB)),
						triangleStep(scaledAtN, scaledAtM))
					a.Show(
						"each leg carries its own B·(m₀+n₀); add and regroup into the composite bound",
						combineLegs(triangle, constLegFact,
							cauchyX.At(m_0, n_0), cauchyY.At(m_0, n_0)))
				})
			}

			// slackRealized: with d₀'s Cauchy bound established, mk_nadd honestly
			// carries d₀ (typedef membership), and the slack equation read through
			// dest(x₀ + mk_nadd(d₀)) makes every pointwise dist the constant B₀ —
			// which is nadd_eq(y₀, x₀ + mk_nadd(d₀)) with witness B₀.
			slackRealized := func(slackEq Fact, slopeBound Fact) Action {
				// The pointwise retraction the closing choreography grounds and
				// rewrites through; stated once, asserted and re-found below.
				retrProp := ctx.MakePropText("∀k:num. d₀(k) = dest_nadd(mk_nadd(d₀), k)")
				return Derive(func(a *Argument) {
					// is_nadd's definition, grounded at d₀ — the Cauchy bound IS
					// the membership predicate.
					isNadd := a.Have(
						"the established Cauchy bound matches the grounded is_nadd definition — one refute",
						ctx.MakePropText("is_nadd(d₀)"),
						By(slopeBound, ctx.ConstDefNormalized("is_nadd")))
					// Membership converts is_nadd(d₀) into the pointwise retraction.
					// It is re-bound to a handle right after: the closing
					// choreography grounds it at n₀ and rewrites through the instance.
					a.Have(
						"is_nadd(d₀) + the membership axiom give d₀(k) = dest_nadd(mk_nadd(d₀), k) — one refute",
						retrProp,
						By(isNadd, ctx.NormalizedThm(membershipThm)))
					retraction := a.Hyp(retrProp)
					a.Show(
						"unfold nadd_eq; at each n₀ the sum's pointwise value is "+
							"x₀(n₀) + d₀(n₀) = y₀(n₀) + B₀, so the dist is the constant B₀",
						Derive(func(b *Argument) {
							// nadd_eq unfolds to ∃B. ∀n. nat_dist(y₀(n), (x₀+mk d₀)(n)) ≤ B;
							// its denied copy is resident as ∀B. ∃n. ¬(… ≤ B) — find that
							// unfolding by content, commit it to the witness B₀ and fix
							// the point n₀.
							b.Do(Rewrite(ctx.ConstDef("nadd_eq"), v.NaddEq))
							deniedEq := b.Hyp("∀B:num. ∃n:num. ¬(dist((dest_nadd(y₀, n), dest_nadd(x₀ + mk_nadd(d₀), n))) ≤ B)")
							b.Do(
								deniedEq.At(B_0),
								StripQuant(),
								// The pointwise dest equation of slope addition, at
								// (n₀, x₀, mk_nadd(d₀)).
								Cite(Add),
							)
							addEq := b.Hyp(ctx.DepNormalized(Add))
							b.Do(addEq.At(n_0))
							addAtN := b.Hyp("∀x y:nadd. dest_nadd(x, n₀) + dest_nadd(y, n₀) = dest_nadd(x + y, n₀)")
							b.Do(
								addEq.At(n_0, x_0, v.MkNadd.Apply(d_0)),
								Clear(addEq, addAtN),
								// Ground the retraction and the slack equation at n₀.
								retraction.At(n_0),
								slackEq.At(n_0),
								// B₀ = nat_dist(y₀(n₀), y₀(n₀) + B₀) — the constant dist.
								Cite(nat_monus.DistRightAdd, v.at(y_0, n_0), B_0),
							)
							destSumAtN := b.Hyp(
								"dest_nadd(x₀, n₀) + dest_nadd(mk_nadd(d₀), n₀) = dest_nadd(x₀ + mk_nadd(d₀), n₀)")
							retrAtN := b.Hyp("d₀(n₀) = dest_nadd(mk_nadd(d₀), n₀)")
							slackAtN := b.Hyp("dest_nadd(y₀, n₀) + B₀ = dest_nadd(x₀, n₀) + d₀(n₀)")
							b.Do(
								// Rewrite the goal's dist argument step by step:
								// dest(x₀+mk d₀)(n₀) → x₀(n₀)+d₀(n₀) → y₀(n₀)+B₀.
								destSumAtN.CongrArg(k.To(v.d(v.at(y_0, n_0), k))),
								retrAtN.CongrArg(k.To(v.d(v.at(y_0, n_0), v.sum(v.at(x_0, n_0), k)))),
								slackAtN.CongrArg(k.To(v.d(v.at(y_0, n_0), k))),
								// dist = B₀ ≤ B₀ — reflexivity (ℕ-level).
								Cite(nat_order.LessEqRefl))
						}))
				})
			}

			// realizesFromSlack: under ¬nadd_eq(y₀, x₀ + mk_nadd(d₀)), establish
			// the implication (∀n. y₀(n) + B₀ = x₀(n) + d₀(n)) ⇒ nadd_eq(…); the
			// denied conclusion then forces a point where the slack equation
			// fails, which is the ∃n the section claims.
			realizesFromSlack := func() Action {
				return Chain(
					// The case hypothesis settles the nadd_eq disjunct; only the
					// ∃n inequality leaf remains.
					TrivialSimplify(),
					Given(func(a *Argument, denied Fact) {
						realized := a.Have(
							"an everywhere-exact slack function d₀ realizes the gap — d₀ is a slope, and mk_nadd carries it",
							ctx.MakePropText(
								"(∀n:num. dest_nadd(y₀, n) + B₀ = dest_nadd(x₀, n) + d₀(n)) ⇒ nadd_eq(y₀, x₀ + mk_nadd(d₀))"),
							Derive(func(b *Argument) {
								// ∀n. y₀(n) + B₀ = x₀(n) + d₀(n) — the slack equation.
								slackEq := b.Assume()
								slopeBound := b.Have(
									"d₀ is a slope — its Cauchy defect is bounded by B₁ "+
										"+ (B₂ + B₀), the carriers' constants plus the slack",
									ctx.MakePropText("∃B:num. ∀m n:num. dist((m * d₀(n), n * d₀(m))) ≤ B * (m + n)"),
									differenceIsSlope(slackEq))
								b.Show(
									"a Cauchy-bounded d₀ satisfies is_nadd, so mk_nadd carries it and the slack equation transfers",
									slackRealized(slackEq, slopeBound))
							}))
						a.Show(
							"¬nadd_eq refutes the implication's conclusion, so its ∀-antecedent fails at some point",
							By(Normalized, denied, realized))
					}),
				)
			}

			// realizes: the heart, in contrapositive dress — if the slack equation
			// y(n) + B = x(n) + d(n) holds at every point, the packaged difference
			// mk_nadd(d) realizes the gap: y ≈ x + mk_nadd(d).
			realizes := ctx.Lemma("∀B:num. ∀x y:nadd. ∀d:(num → num). ∃n:num. "+
				"    dest_nadd(x, n) + d(n) ≠ dest_nadd(y, n) + B ∨ nadd_eq(y, x + mk_nadd(d))",
				func(a *Argument) {
					a.Do(
						StripQuant(),
						ByCaseStep(v.NaddEq.Apply(y_0, v.NaddAdd.Apply(x_0, v.MkNadd.Apply(d_0))),
							Case(
								"the equivalence already holds — any point witnesses the disjunction",
								TrivialNormalized(),
							),
							Case(
								"with the equivalence denied, the contrapositive of (∀n. "+
									"slack) ⇒ nadd_eq gives a point where the slack fails",
								realizesFromSlack(),
							),
						),
					)
				})

			// weaken: existential weakening of realizes — the specific mk_nadd(d)
			// becomes some slope e, so the assembly step below cites a term-free
			// form.
			weaken := ctx.Lemma("∀B:num. ∀x y:nadd. ∀d:(num → num). ∃n:num. ∃e:nadd. "+
				"    dest_nadd(x, n) + d(n) ≠ dest_nadd(y, n) + B ∨ nadd_eq(y, x + e)",
				func(a *Argument) {
					a.Do(Cite(realizes), a.Ctx().CloseByAuto())
				})

			// assemble: from the uniform bound to the realized gap — per-point
			// choice (nat_order.LessEqExists: x(n) ≤ y(n) + B gives d with
			// y(n) + B = x(n) + d)
			// is Skolemized into a single slack function, and weaken realizes it.
			assemble := ctx.Lemma("∀B:num. ∀x y:nadd. ∃d:nadd. ∃n:num. "+
				"    ¬(dest_nadd(x, n) ≤ dest_nadd(y, n) + B) ∨ nadd_eq(y, x + d)",
				func(a *Argument) {
					a.Do(StripQuant())
					perPoint := a.Have(
						"per-point choice: wherever the bound holds, y₀(n) + B₀ exceeds x₀(n) by some difference",
						ctx.MakePropText(
							"∀n:num. ∃dd:num. "+
								"    ¬(dest_nadd(x₀, n) ≤ dest_nadd(y₀, n) + B₀) ∨ dest_nadd(y₀, n) + B₀ = dest_nadd(x₀, n) + dd"),
						By(nat_order.LessEqExists))
					a.Show(
						"the per-point differences Skolemize into one slack function, and weaken realizes it",
						By(perPoint, weaken))
				})

			// goal: assume the order and unfold it to its uniform pointwise bound;
			// assemble turns that bound into the difference slope.
			return ctx.Theorem(headline,
				// The trailing `_ Fact` absorbs the ⇒: the order assumption is
				// unfolded in place by the DefExpand below, never cited by name.
				func(a *Argument, x, y Term, _ Fact) {
					a.Do(
						Unfold(NaddLeDef), // the assumption becomes ∃B. ∀n. x₀(n) ≤ y₀(n) + B
						UseLemma(assemble.PromisedThm()),
						CnfRefute(),
					)
				})
		}),
})}

// estTerms names the recurring quantities of the difference estimate at
// the index pair (m₀, n₀), writing x(n) for dest_nadd(x₀, n) and d(n)
// for d₀(n). Everything the estimate touches is one of these.
type estTerms struct {
	mdn, ndm Term // m₀·d(n₀), n₀·d(m₀) — d's Cauchy defect pair
	mxn, nxm Term // m₀·x(n₀), n₀·x(m₀)
	myn, nym Term // m₀·y(n₀), n₀·y(m₀)
	mB, nB   Term // m₀·B₀, n₀·B₀ — the constant-slack pair

	distD Term         // nat_dist(m₀·d(n₀), n₀·d(m₀)) — the defect to bound
	distX Term         // nat_dist(m₀·x(n₀), n₀·x(m₀)) — x's defect
	distY Term         // nat_dist(m₀·y(n₀), n₀·y(m₀)) — y's defect
	distB *TermWrapper // nat_dist(m₀·B₀, n₀·B₀) — the constant leg

	shiftL, shiftR *TermWrapper // m₀·d(n₀)+m₀·x(n₀), n₀·d(m₀)+n₀·x(m₀)
	sumL, sumR     Term         // m₀·x(n₀)+m₀·d(n₀), n₀·x(m₀)+n₀·d(m₀)
	distShift      Term         // nat_dist(shiftL, shiftR)

	defX, defY, defB Term // B₁·(m₀+n₀), B₂·(m₀+n₀), B₀·(m₀+n₀)

	distYB, distXY   Term // distY+distB, distX+distY
	distYBX, distXYB Term // (distY+distB)+distX, (distX+distY)+distB
	defXY, defXYB    Term // defX+defY, (defX+defY)+defB
	defSum           Term
	defAll           *TermWrapper // defX+(defY+defB); the composite (B₁+(B₂+B₀))·(m₀+n₀)
}

// LessEqAddLeft — the slope order is invariant under adding a slope
// on the LEFT:
//
//	⊢ ∀x y z : nadd. (y ≤ z) ⇔ ((x + y) ≤ (x + z))
//
// All the content is LessEqAddRight's; the left-add form is the
// right-add form read through commutativity:
//
//	(y ≤ z) ⇔ (y+x ≤ z+x) ⇔ (x+y ≤ x+z)
//
// the first ⇔ being LessEqAddRight itself, the second the transport of
// nadd_le along the two AddSym flips y+x ≈ x+y and z+x ≈ x+z.
var LessEqAddLeft = lessEqAddLeftThm{family.Add(registry.ProofEntry{
	Name: "LessEqAddLeft",
	Key:  "prop_98b0a44d4e6a3cea",
	Build: family.Theorem("∀x y z:nadd. y ≤ z ⇔ x + y ≤ x + z",
		func(a *Argument, x, y, z Term) {
			ctx := a.Ctx()
			v := ops(ctx)

			add := func(p, q Term) Term { return v.NaddAdd.Apply(p, q) }
			// The mirror's two sums, and the goal's two sums.
			yx, zx := add(y, x), add(z, x)
			xy, xz := add(x, y), add(x, z)

			a.Do(
				// The mirror at (y₀, z₀, x₀): (y₀ ≤ z₀) ⇔ (y₀+x₀ ≤ z₀+x₀).
				Cite(LessEqAddRight),
				GroundHyp(ctx.DepNormalized(LessEqAddRight), y, z, x),

				// The two flips the transport rides on.
				Cite(AddSym, y, x), // y₀+x₀ ≈ x₀+y₀
				Cite(AddSym, z, x), // z₀+x₀ ≈ x₀+z₀

				// Well-definedness of nadd_le pinned at exactly those four
				// slopes: (y₀+x₀ ≤ z₀+x₀) ⇔ (x₀+y₀ ≤ x₀+z₀).
				Cite(LessEqWellDef, yx, xy, zx, xz),

				// With all four instances ground, composing them into the goal
				// ⇔ is propositional — no refute needed.
				Basic(),
			)
		}),
})}

// LessEqAddRight — the slope order is invariant under adding a slope
// on the right:
//
//	⊢ ∀x y z : nadd. (x ≤ y) ⇔ ((x + z) ≤ (y + z))
//
// Both sides unfold to constant-defect bounds on the underlying
// functions (writing x(n) for dest_nadd(x, n)):
// ∃B. ∀n. x(n) ≤ y(n) + B versus ∃B. ∀n. (x+z)(n) ≤ (y+z)(n) + B.
// Pointwise, (x+z)(n) IS x(n) + z(n) (the Add dest equation), so
// the two estimates differ by z(n) added to both sides of a ≤ — the
// SAME bound B₀ transfers either way. Both ⇔ directions are the one
// ladder transferBound; only the reading differs (adding z(n₀) versus
// cancelling it). The nat_order.LessEqAddRightCancel + nat_arith.AddSym +
// nat_arith.AddAssoc regrouping is absorbed by the gated arith close,
// leaving Add as the only dep.
var LessEqAddRight = lessEqAddRightThm{family.Add(registry.ProofEntry{
	Name: "LessEqAddRight",
	Key:  "prop_4aa3d2dba743b956",
	// goal — unfold both orders to their bounds, then split the iff; each
	// direction is the same bound transfer read the other way around.
	Build: family.Theorem("∀x y z:nadd. x ≤ y ⇔ x + z ≤ y + z",
		func(a *Argument, x, y, z Term) {
			ctx := a.Ctx()
			// addPointwise is the Add dest equation
			// ∀n x y. x(n) + y(n) = dest_nadd((x + y), n) — both
			// directions take its (x₀,z₀) and (y₀,z₀) instances.
			// n₀ is the challenge index of whichever side is goal; the
			// bound B₀ arrives from the Skolemization below.
			n0 := ctx.Var("n_0", NumType)

			// transferBound proves either direction of the unfolded iff:
			//
			//	∃B.∀n. lhs(n) ≤ rhs(n) + B ⊢ ∃B.∀n. lhs'(n) ≤ rhs'(n) + B
			//
			// where {lhs, rhs} and {lhs', rhs'} are the plain pair x₀, y₀ and
			// the shifted pair x₀+z₀, y₀+z₀ in one order or the other. The
			// given bound is the answer: Skolemize it as B₀, reuse it as
			// witness, ground the hypothesis at the challenge index n₀,
			// expand the two slope-sum values through Add, and the two
			// estimates differ by z₀(n₀) on both sides of a ≤ — linear
			// arithmetic.
			transferBound := Given(func(b *Argument, given Fact) {
				// Skolemize the given side's bound: B₀.
				B0, givenBound := b.Unpack(given)
				b.Do(
					// The transferred bound is the same constant: B := B₀.
					Witness(B0),
					// The index the bound must hold at: n₀.
					StripQuant(),
				)
				b.Show(
					"one estimate is the other with z₀(n₀) added to "+
						"both sides — linear arithmetic over the ground atoms",
					ByArith(
						// the given estimate at n₀
						givenBound.At(n0),
						// the two slope-sum values at n₀ are the pointwise
						// sums: x₀(n₀) + z₀(n₀) = (x₀+z₀)(n₀), likewise for y₀
						At(Add, n0, x, z),
						At(Add, n0, y, z)))
			})

			a.Do(
				// Each nadd_le becomes its one-sided bound ∃B. ∀n. … ≤ … + B.
				Unfold(NaddLeDef),
				SplitIff(
					Forward(
						"a bound B₀ for the plain pair transfers to the shifted "+
							"pair — add z₀(n₀) to both sides of the pointwise estimate",
						transferBound,
					),
					Backward(
						"a bound B₀ for the shifted pair transfers to the plain pair "+
							"— cancel z₀(n₀) from both sides of the pointwise estimate",
						transferBound,
					),
				),
			)
		}),
})}

// LessEqMulLeft — left-multiplication respects the slope preorder:
//
//	⊢ ∀x y z : nadd. (y ≤ z) ⇒ ((x * y) ≤ (x * z))
//
// Only the RIGHT slot moves; it mirrors the left-slot ladder, and the
// completeness chapter's chain fans in through this slot alone.
//
// Skolemizing the gap y ≤ z as z ≈ y + d turns the bound into a single
// mixed chain — self-addition bounds it, distributivity refolds it,
// well-definedness transports the gap under x·(−):
//
//	x·y ≤ x·y + x·d ≈ x·(y + d) ≈ x·z
var LessEqMulLeft = lessEqMulLeftThm{family.Add(registry.ProofEntry{
	Name: "LessEqMulLeft",
	Key:  "prop_7b26ba4c3beaca42",
	// Fix the three slopes, assume the premise, Skolemize the gap d₀ with
	// z₀ ≈ y₀ + d₀, then walk the chain. Each link is asserted and closed
	// on its own; the ≈ links are lifted into ≤ by NaddEqImpliesLessEq and
	// knit through LessEqTrans.
	// The trailing `_ Fact` absorbs the ⇒: the premise y₀ ≤ z₀ is assumed
	// at the boundary and consumed by the LessEqExists specialization
	// below, so the body never needs it by name.
	Build: family.Theorem(
		Statement{
			Binders: "∀x y z:nadd.",
			Hypotheses: []string{
				"y ≤ z",
			},
			Conclusion: "x * y ≤ x * z",
		},
		func(a *Argument, x, y, z Term, _ Fact) {
			ctx := a.Ctx()
			v := ops(ctx)
			d0 := ctx.Var("d_0", MakeType("nadd")) // the Skolem gap: z₀ ≈ y₀ + d₀

			// The chain's four terms: x·y ≤ x·y + x·d ≈ x·(y + d) ≈ x·z.
			yd := v.NaddAdd.Apply(y, d0) // y₀ + d₀
			xy := v.NaddMul.Apply(x, y)
			xd := v.NaddMul.Apply(x, d0)
			xyPlusXd := v.NaddAdd.Apply(xy, xd)
			xTimesYd := v.NaddMul.Apply(x, yd)
			xz := v.NaddMul.Apply(x, z)

			a.Do(
				// LessEqExists at (y₀, z₀): ∃d. z₀ ≈ y₀ + d. Skolemize d₀.
				Cite(LessEqExists, y, z),
				StripQuant(),

				// The chain. Its endpoint IS the goal, so it closes it.
				CalcOrder{
					Le:      v.rel(v.NaddLe),
					Eq:      v.rel(v.NaddEq),
					LeTrans: LessEqTrans,
					EqToLe:  NaddEqImpliesLessEq,
				}.Calc(xy,
					LeLeg(
						xyPlusXd,
						"x·y ≤ x·y + x·d — LessEqSelfAdd, whose ∀-form is the link itself",
						Cite(LessEqSelfAdd)),
					EqLeg(
						xTimesYd,
						"x·y + x·d ≈ x·(y + d) — LeftDistrib at (x₀, y₀, d₀), read right-to-left through NaddEqSym",
						Cite(LeftDistrib, x, y, d0),
						Cite(NaddEqSym)),
					EqLeg(
						xz,
						"x·(y + d) ≈ x·z — MulWellDef transports the gap z₀ ≈ "+
							"y₀ + d₀ under x₀·(−), NaddEqRefl fixing the left factor",
						Cite(MulWellDef, x, x, yd, z),
						Cite(NaddEqRefl, x),
						Cite(NaddEqSym, z, yd),
						CnfRefute()),
				),
			)
		}),
})}

// LessEqMulRight — right-multiplication respects the slope preorder:
//
//	⊢ ∀x y z : nadd. (x ≤ y) ⇒ ((x * z) ≤ (y * z))
//
// The moving pair sits in the LEFT slot here, so the proof conjugates
// LessEqMulLeft above by MulSym rather than repeating its ladder:
//
//	x·z ≈ z·x ≤ z·y ≈ y·z
//
// The middle link is where the premise x ≤ y is spent — in the right
// slot, which is the slot LessEqMulLeft moves — and the two ≈ links
// carry the standing factor z across and back. Lifted into ≤ by
// NaddEqImpliesLessEq and knit by LessEqTrans, the chain stays entirely
// inside the slope preorder: no numerical estimate, no ℕ-arithmetic.
var LessEqMulRight = lessEqMulRightThm{family.Add(registry.ProofEntry{
	Name: "LessEqMulRight",
	Key:  "prop_1aa6737c6663af65",
	// The premise x ≤ y arrives as the closure's Fact and is spent at the
	// one order link; the two equivalence links need nothing but MulSym.
	Build: family.Theorem(
		Statement{
			Binders: "∀x y z:nadd.",
			Hypotheses: []string{
				"x ≤ y",
			},
			Conclusion: "x * z ≤ y * z",
		},
		func(a *Argument, x, y, z Term, premise Fact) {
			ctx := a.Ctx()
			v := ops(ctx)

			mul := func(p, q Term) Term { return v.NaddMul.Apply(p, q) }
			// The chain's four terms: x·z ≈ z·x ≤ z·y ≈ y·z.
			xz, zx := mul(x, z), mul(z, x)
			zy, yz := mul(z, y), mul(y, z)

			a.Do(
				// The chain's endpoint IS the goal, so it closes it.
				CalcOrder{
					Le:      v.rel(v.NaddLe),
					Eq:      v.rel(v.NaddEq),
					LeTrans: LessEqTrans,
					EqToLe:  NaddEqImpliesLessEq,
				}.Calc(xz,
					EqLeg(
						zx,
						"x·z ≈ z·x — MulSym at (x₀, z₀), moving the varying factor into the slot LessEqMulLeft acts on",
						Cite(MulSym, x, z)),
					LeLeg(
						zy,
						"z·x ≤ z·y — LessEqMulLeft at (z₀, x₀, y₀) on the premise x₀ ≤ y₀",
						By(premise, At(LessEqMulLeft, z, x, y))),
					EqLeg(
						yz,
						"z·y ≈ y·z — MulSym at (z₀, y₀), moving it back",
						Cite(MulSym, z, y)),
				),
			)
		}),
})}
