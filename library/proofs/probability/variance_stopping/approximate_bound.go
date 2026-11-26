// approximate_bound.go — a row of martingale differences whose conditional variances sum
// only to about 1, stopped where they first pass 1 + δ and compared with the standard normal.

package variance_stopping

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	"github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/product_measure"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/probability/filtration"
	"github.com/euc-ai/xugo/library/proofs/probability/lindeberg_bound"
	"github.com/euc-ai/xugo/library/proofs/probability/martingale/martingale"
	"github.com/euc-ai/xugo/library/proofs/probability/normal_distribution"
	"github.com/euc-ai/xugo/library/proofs/probability/normal_moments"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// stoppedRowSums — the stopped variance lies between zero and the cutoff, and
// both sums are unchanged where the original variance is below it: on each
// sample the stop cuts the prefix sums of the variances at c, a cutoff of real
// sequences (cappedSum, retainedTerm).
func stoppedRowSums(ctx *Script) *GoalStackNode {
	// cappedSum — retaining nonnegative increments whose prefix sum is at most
	// c bounds their sum by c and by the original sum.
	cappedSum := ctx.Lemma(Statement{
		Binders: "∀a:(num → real). ∀c:real. ∀n:num.",
		Hypotheses: []string{
			"&0 ≤ c",
			"∀j:num. j < n ⇒ &0 ≤ a(j)",
		},
		Conclusion: "«prefixSum»(λk:num. «cutSummand»(a, a, c, k), n) ≤ c ∧ " +
			"«prefixSum»(λk:num. «cutSummand»(a, a, c, k), n) ≤ «prefixSum»(a, n)",
	}, func(arg *Argument, a *Arrow[Nat, Real], c *Expr[Real], n *Expr[Nat]) {
		arg.Induct(n)
		arg.Base(
			"both sums are zero at the empty prefix",
			func(b *Argument) {
				nonnegative := b.Assume()
				b.Show(
					"the cap bounds zero",
					Simp(Fwd(real_sum.BelowClauses)),
					By(nonnegative, real_order_ring.LessEqRefl))
			})
		arg.Step(
			"extend the sums by one increment",
			func(b *Argument, previous Fact) {
				assumptions := b.Assume()
				signs := b.Conjuncts(
					assumptions,
					"&0 ≤ c",
					"∀j:num. j < suc(n) ⇒ &0 ≤ a(j)")
				stopped := b.TermAs[Fun[Nat, Real]]("λk:num. «cutSummand»(a, a, c, k)")
				bounds := b.Have(
					"the shorter stopped sum satisfies both bounds",
					"«prefixSum»(λk:num. «cutSummand»(a, a, c, k), n) ≤ c ∧ "+
						"«prefixSum»(λk:num. «cutSummand»(a, a, c, k), n) ≤ «prefixSum»(a, n)",
					ByArith(signs[1], signs[0], previous, nat_order.LessThanSucIffLessEq, nat_order.LessEqRefl))
				lastNonnegative := b.Have(
					"the last increment is nonnegative",
					"&0 ≤ a(n)",
					By(signs[1].At(n), nat_order.LessThanSucIffLessEq, nat_order.LessEqRefl))
				stoppedStep := b.Have(
					"the stopped sum adds the retained term",
					"«prefixSum»(λk:num. «cutSummand»(a, a, c, k), suc(n)) = "+
						"«prefixSum»(λk:num. «cutSummand»(a, a, c, k), n) + «cutSummand»(a, a, c, n)",
					By(real_sum.BelowClauses.At(stopped)))
				originalStep := b.Have(
					"the original sum adds the last increment",
					"«prefixSum»(a, suc(n)) = «prefixSum»(a, n) + a(n)",
					By(real_sum.BelowClauses.At(a)))
				fullPrefix := b.Have(
					"the cutoff tests the full successor prefix",
					"«prefixSum»(a, n + 1) = «prefixSum»(a, suc(n))",
					By(nat_arith.Add1.At(n)))
				b.Cases(b.Term("«prefixSum»(a, n + 1) ≤ c"))
				b.When(
					"retain the last increment within the cap",
					func(d *Argument, within Fact) {
						retained := d.Have(
							"the last increment is retained",
							"«cutSummand»(a, a, c, n) = a(n)",
							By(within))
						d.Show(
							"both sums gain the same increment and the full original sum is within the cap",
							ByArith(originalStep, stoppedStep, fullPrefix, retained, within, bounds))
					})
				b.Otherwise(
					"discard the last increment beyond the cap",
					func(d *Argument, exceeds Fact) {
						discarded := d.Have(
							"the last increment is zeroed",
							"«cutSummand»(a, a, c, n) = &0",
							By(exceeds))
						d.Show(
							"the stopped sum stays fixed and the original sum can only increase",
							ByArith(originalStep, stoppedStep, discarded, lastNonnegative, bounds))
					})
			})
	})
	// retainedTerm — when the total of the nonnegative increments is within
	// the cap, no term of the companion sum is discarded.
	retainedTerm := ctx.Lemma(Statement{
		Binders: "∀a b:(num → real). ∀c:real. ∀n k:num.",
		Hypotheses: []string{
			"∀j:num. j < n ⇒ &0 ≤ a(j)",
			"«prefixSum»(a, n) ≤ c",
			"k < n",
		},
		Conclusion: "«cutSummand»(a, b, c, k) = b(k)",
	}, func(arg *Argument, a, b *Arrow[Nat, Real], c *Expr[Real], n, k *Expr[Nat], assumptions Fact) {
		initial := arg.TermAs[Set[Nat]]("{i:num | i < k + 1}")
		row := arg.TermAs[Set[Nat]]("{i:num | i < n}")
		indexBound := arg.Have(
			"indices in the prefix are in the row",
			"∀i:num. i < k + 1 ⇒ i < n",
			ByArith(assumptions))
		nested := arg.Have(
			"the prefix is an initial segment of the row",
			"{i:num | i < k + 1} ⊆ {i:num | i < n}",
			BySets(indexBound))
		tailNonnegative := arg.Have(
			"each omitted increment is nonnegative",
			"∀i:num. i ∈ {j:num | j < n} ∖ {j:num | j < k + 1} ⇒ &0 ≤ a(i)",
			Derive(func(d *Argument) {
				d.FixAs[Nat]()
				inTail := d.Assume()
				inRow := d.Have(
					"the index lies in the row",
					"i < n",
					BySets(inTail))
				d.Show(
					"nonnegativity holds throughout the row",
					By(inRow, assumptions))
			}))
		monotone := arg.Have(
			"the prefix sum is bounded by the total",
			"«prefixSum»(a, k + 1) ≤ «prefixSum»(a, n)",
			By(
				tailNonnegative,
				nested,
				real_sum.Subset.At(initial, row, a),
				num_segment.FiniteBelowStrict.At(n)))
		within := arg.Have(
			"the prefix passes the cutoff",
			"«prefixSum»(a, k + 1) ≤ c",
			ByArith(monotone, assumptions))
		arg.Show(
			"the cutoff retains the term",
			By(within))
	})
	pointwiseCut := ctx.Lemma(Statement{
		Binders: "∀Ω:set(A). ∀v b:(num → A → real). ∀c:real. ∀x:A.",
		Hypotheses: []string{
			"x ∈ Ω",
		},
		Conclusion: "(λk:num. «stoppedRow»(Ω, v, b, c, k, x)) = " +
			"(λk:num. «cutSummand»(λj:num. v(j, x), λj:num. b(j, x), c, k))",
	},
		func(
			a *Argument,
			Ω *Expr[Set[A]],
			v, b *Arrow[Nat, Fun[A, Real]],
			c *Expr[Real],
			x *Expr[A],
			inSpace Fact,
		) {
			a.Do(Funext())
			a.FixAs[Nat]("k")
			membership := a.Have(
				"on the sample space the event tests exactly the prefix bound",
				"x ∈ «stopEvent»(Ω, v, c, k) ⇔ (Σ_{j<k + 1} v(j, x)) ≤ c",
				BySets(inSpace))
			a.Show(
				"the two cuts agree",
				membership.Rw(),
				Basic())
		})
	exactSum := ctx.Lemma(Statement{
		Binders: "∀a b:(num → real). ∀c:real. ∀n:num.",
		Hypotheses: []string{
			"∀j:num. j < n ⇒ &0 ≤ a(j)",
			"«prefixSum»(a, n) ≤ c",
		},
		Conclusion: "(Σ_{k<n} «cutSummand»(a, b, c, k)) = «prefixSum»(b, n)",
	},
		func(arg *Argument, a, b *Arrow[Nat, Real], c *Expr[Real], n *Expr[Nat], within Fact) {
			terms := arg.Have(
				"every summand in the row is retained",
				"∀k:num. k ∈ {j:num | j < n} ⇒ «cutSummand»(a, b, c, k) = b(k)",
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]()
					inRange := d.Assume()
					below := d.Have(
						"the index precedes the row length",
						"k < n",
						BySets(inRange))
					d.Show(
						"the total controls every prefix",
						By(below, within, At(retainedTerm, a, b, c, n, k)))
				}))
			arg.Show(
				"agreement of summands gives agreement of totals",
				By(
					terms,
					real_sum.Congruence.At(arg.TermAs[Set[Nat]]("{j:num | j < n}"),
						arg.TermAs[Fun[Nat, Real]]("λk:num. «cutSummand»(a, b, c, k)"), b)))
		})
	nonnegativeSum := ctx.Lemma(Statement{
		Binders: "∀a:(num → real). ∀c:real. ∀n:num.",
		Hypotheses: []string{
			"∀j:num. j < n ⇒ &0 ≤ a(j)",
		},
		Conclusion: "&0 ≤ Σ_{k<n} «cutSummand»(a, a, c, k)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], c *Expr[Real], n *Expr[Nat], signs Fact) {
			terms := arg.Have(
				"the cutoff leaves each term nonnegative",
				"∀k:num. k ∈ {j:num | j < n} ⇒ &0 ≤ «cutSummand»(a, a, c, k)",
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]()
					inRange := d.Assume()
					below := d.Have(
						"the index precedes the row length",
						"k < n",
						BySets(inRange))
					d.Cases(d.Term("«prefixSum»(a, k + 1) ≤ c"))
					d.When(
						"retain the nonnegative term",
						func(e *Argument, retain Fact) {
							e.Show(
								"use the original sign",
								By(signs.At(k), below, retain))
						})
					d.Otherwise(
						"discard the term",
						func(e *Argument, discard Fact) {
							e.Show(
								"zero is nonnegative",
								By(discard, real_order_ring.LessEqRefl))
						})
				}))
			arg.Show(
				"summing nonnegative terms preserves the sign",
				By(
					terms,
					real_sum.Nonneg.At(arg.TermAs[Set[Nat]]("{j:num | j < n}"),
						arg.TermAs[Fun[Nat, Real]]("λk:num. «cutSummand»(a, a, c, k)"))))
		})
	return ctx.Lemma(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀n:num. " +
			"∀ξ v:(num → A → real). " +
			"∀c:real.",
		Hypotheses: []string{"&0 ≤ c", "measure_ae(Ω, S, μ, λx:A. ∀k:num. k < n ⇒ &0 ≤ v(k, x))"},
		Conclusion: "measure_ae(Ω, S, μ, «stoppedProperties»)",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], n *Expr[Nat], ξ, v *Arrow[Nat, Fun[A, Real]],
		c *Expr[Real], assumptions Fact) {
		pointwise := a.Have(
			"apply the deterministic cutoff bounds wherever all variances are nonnegative",
			"∀x:A. x ∈ Ω ∧ (∀k:num. k < n ⇒ &0 ≤ v(k, x)) ⇒ «stoppedProperties»(x)",
			Derive(func(b *Argument) {
				b.FixAs[A]()
				sample := b.Assume()
				variances := b.TermAs[Fun[Nat, Real]]("λk:num. v(k, x)")
				increments := b.TermAs[Fun[Nat, Real]]("λk:num. ξ(k, x)")
				b.Show(
					"the two sums read the deterministic cutoff on this sample",
					Simp(Fwd(pointwiseCut)),
					SplitConj(
						Case(
							"the stopped variance is nonnegative and capped",
							By(assumptions, sample, At(nonnegativeSum, variances, c, n), At(cappedSum, variances, c, n))),
						Case(
							"if the original variance is within the cap all terms are retained",
							Derive(func(d *Argument) {
								within := d.Assume()
								d.Show(
									"the two original sums are preserved",
									By(
										sample,
										within,
										At(exactSum, variances, variances, c, n),
										At(exactSum, variances, increments, c, n)))
							}))))
			}))
		a.Show(
			"the cutoff properties hold wherever every conditional variance has its sign",
			By(
				pointwise,
				assumptions,
				measure_space.AEMono.At(Ω, S, μ,
					a.TermAs[Set[A]]("λx:A. ∀k:num. k < n ⇒ &0 ≤ v(k, x)"),
					a.TermAs[Set[A]]("«stoppedProperties»"))))
	})
}

// lindebergCutBound — cutting each summand of a row to an event can only
// decrease the Lindeberg sum: on each tail event the cut square is at most the
// original square.
func lindebergCutBound(ctx *Script) *GoalStackNode {
	squareCut := cutSquare(ctx)
	tailCut := ctx.Lemma(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀E:set(A). " +
			"∀X:(A → real). " +
			"∀ε:real.",
		Hypotheses: []string{
			"real_integrable(Ω, S, μ, λx:A. X(x) * X(x))",
			"real_integrable(Ω, S, μ, λx:A. «cutEvent»(E, X, x) * «cutEvent»(E, X, x))",
		},
		Conclusion: "«tailIntegral»(Ω, S, μ, «cutEvent»(E, X), ε) ≤ «tailIntegral»(Ω, S, μ, X, ε)",
		Abbrev: Abbrev{
			{Name: "originalTailEvent", Text: "{u:A | ε < |X(u)|}"},
			{Name: "retainedTailEvent", Text: "{u:A | ε < |«cutEvent»(E, X, u)|}"},
			{Name: "retainedSquare", Text: "λx:A. «cutEvent»(E, X, x) * «cutEvent»(E, X, x)"},
		},
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		E *Expr[Set[A]], X *Arrow[A, Real], ε *Expr[Real], integrable Fact) {
		sameEvents := a.Have(
			"the tail events coincide after intersection with the retention event",
			"«retainedTailEvent» ∩ E = «originalTailEvent» ∩ E",
			BySets())
		commonTail := a.Have(
			"the stopped square integrates over either threshold event",
			"«tailIntegral»(Ω, S, μ, «cutEvent»(E, X), ε) = "+
				"event_integral(Ω, S, μ, «originalTailEvent», «retainedSquare»)",
			Simp(Fwd(squareCut), Fwd(event_integral.EventIntegralRestrict)),
			sameEvents.Rw(),
			Basic())
		dominated := a.Have(
			"the retained square is pointwise no larger",
			"∀x:A. x ∈ Ω ∩ «originalTailEvent» ⇒ «retainedSquare»(x) ≤ X(x) * X(x)",
			Derive(func(b *Argument) {
				b.FixAs[A]()
				b.Assume()
				b.Cases(b.Term("x ∈ E"))
				b.When(
					"the squared increment is retained",
					func(d *Argument, included Fact) {
						d.Show(
							"the two squares agree",
							ByArith(included))
					})
				b.Otherwise(
					"the squared increment is discarded",
					func(d *Argument, excluded Fact) {
						d.Show(
							"zero is bounded by the original square",
							ByArith(excluded))
					})
			}))
		a.Show(
			"the smaller retained squares control the tail integral",
			ByArith(
				commonTail,
				dominated,
				integrable,
				event_integral.EventIntegralMono.At(Ω, S, μ, a.TermAs[Set[A]]("«originalTailEvent»"),
					a.TermAs[Fun[A, Real]]("«retainedSquare»"), a.TermAs[Fun[A, Real]]("λx:A. X(x) * X(x)"))))
	})
	return ctx.Lemma(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀n:num. " +
			"∀E:(num → set(A)). " +
			"∀ξ:(num → A → real). " +
			"∀ε:real.",
		Hypotheses: []string{
			"∀k:num. " +
				"    k < n ⇒ " +
				"    real_integrable(Ω, S, μ, λx:A. ξ(k, x) * ξ(k, x)) ∧ " +
				"    real_integrable(Ω, S, μ, λx:A. «eventCutRow»(E, ξ, k, x) * «eventCutRow»(E, ξ, k, x))",
		},
		Conclusion: "lindeberg_sum(Ω, S, μ, n, «eventCutRow»(E, ξ), ε) ≤ lindeberg_sum(Ω, S, μ, n, ξ, ε)",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], n *Expr[Nat], E *Arrow[Nat, Set[A]],
		ξ *Arrow[Nat, Fun[A, Real]], ε *Expr[Real], integrable Fact) {
		terms := a.Have(
			"the square-integrable retained summands have smaller tails",
			Statement{
				Binders:    "∀k:num.",
				Hypotheses: []string{"k ∈ {j:num | j < n}"},
				Conclusion: "«tailIntegral»(Ω, S, μ, «eventCutRow»(E, ξ, k), ε) ≤ «tailIntegral»(Ω, S, μ, ξ(k), ε)",
			},
			Derive(func(b *Argument) {
				k := b.FixAs[Nat]()
				inRow := b.Assume()
				below := b.Have(
					"the summand index precedes the row length",
					"k < n",
					BySets(inRow))
				b.Show(
					"both squares are integrable at this index",
					By(
						below,
						integrable.At(k),
						At(tailCut, Ω, S, μ,
							b.TermAs[Set[A]]("E(k)"), b.TermAs[Fun[A, Real]]("ξ(k)"), ε)))
			}))
		indices := a.TermAs[Set[Nat]]("{j:num | j < n}")
		retained := a.TermAs[Fun[Nat, Real]]("λk:num. «tailIntegral»(Ω, S, μ, «eventCutRow»(E, ξ, k), ε)")
		original := a.TermAs[Fun[Nat, Real]]("λk:num. «tailIntegral»(Ω, S, μ, ξ(k), ε)")
		a.Show(
			"the finite sum preserves the termwise bounds",
			Simp(Fwd(lindeberg_bound.LindebergSumDef)),
			By(terms, num_segment.FiniteBelowStrict.At(n), real_sum.Monotone.At(indices, retained, original)))
	})
}

// cutSquare — the square of a cut is the cut of the square: off the event
// both sides are zero, on it both square the original value.
func cutSquare(ctx *Script) *GoalStackNode {
	return ctx.Lemma(
		"∀E:set(A). ∀X:(A → real). "+
			"    (λx:A. «cutEvent»(E, X, x) * «cutEvent»(E, X, x)) = «cutEvent»(E, λx:A. X(x) * X(x))",
		func(a *Argument, E *Expr[Set[A]], X *Arrow[A, Real]) {
			a.Do(Funext())
			a.FixAs[A]()
			a.Cases(a.Term("x ∈ E"))
			a.When(
				"the square is retained on the event",
				func(b *Argument, included Fact) {
					b.Show(
						"both sides square the original value",
						By(included))
				})
			a.Otherwise(
				"the square vanishes off the event",
				func(b *Argument, excluded Fact) {
					b.Show(
						"both sides are zero",
						ByArith(excluded))
				})
		})
}

// independentNoiseComparison — a bounded Lipschitz test changes by at most
// the mean size of an independent perturbation off the exceptional event, and
// by its oscillation on that event.
func independentNoiseComparison(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀ν:(set(B) → extended_nonneg_real). " +
			"∀s t:(A → real). " +
			"∀Y:(B → real). " +
			"∀f:(real → real). " +
			"∀E:set(A). " +
			"∀B a:real.",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"probability_on(V, T, ν)",
			"real_measurable(Ω, S, s)",
			"real_measurable(Ω, S, t)",
			"real_measurable(V, T, Y)",
			"real_integrable(V, T, ν, λy:B. |Y(y)|)",
			"real_measurable(𝕌, borel_sets(real_topology), f)",
			"&0 ≤ B",
			"&0 ≤ a",
			"∀u:real. |f(u)| ≤ B",
			"∀u w:real. |f(w) - f(u)| ≤ B * |w - u|",
			"E ∈ S",
			"∀x:A. x ∈ Ω ∧ x ∉ E ⇒ |t(x)| ≤ a",
		},
		Conclusion: "|expectation(Ω, S, μ, λx:A. expectation(V, T, ν, λy:B. f(s(x) + t(x) * Y(y)))) - " +
			"expectation(Ω, S, μ, λx:A. f(s(x)))| ≤ " +
			"B * a * expectation(V, T, ν, λy:B. |Y(y)|) + &2 * B * extended_to_real(μ(E))",
		Abbrev: Abbrev{
			{Name: "lawProduct", Text: "product_measure(Ω, S, μ, ν)"},
			{Name: "productIntegral", Text: "λH:(prod(A, B) → real). " +
				"    measure_integral(set_cross(Ω, V), product_sigma(Ω, S, V, T), «lawProduct», H)"},
			{Name: "liftedNoiseAbs", Text: "λp:prod(A, B). |Y(snd(p))|"},
			{Name: "shiftedScore", Text: "λp:prod(A, B). f(s(fst(p)) + t(fst(p)) * Y(snd(p)))"},
			{Name: "plainScore", Text: "λp:prod(A, B). f(s(fst(p)))"},
			{Name: "productMajorant", Text: "λp:prod(A, B). " +
				"    B * a * «liftedNoiseAbs»(p) + COND(p ∈ set_cross(E, V), &2*B, &0)"},
		},
	},
		func(
			arg *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			V *Expr[Set[B]],
			T *Expr[Set[Set[B]]],
			ν *Arrow[Set[B], ExtendedNonnegReal],
			s, t *Arrow[A, Real],
			Y *Arrow[B, Real],
			f *Arrow[Real, Real],
			E *Expr[Set[A]],
			_, a *Expr[Real],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"the first law is a probability",
				"the second law is a probability",
				"the location is measurable",
				"the coefficient is measurable",
				"the noise is measurable",
				"the noise has a finite first absolute moment",
				"the test is Borel",
				"the bound is nonnegative",
				"the radius is nonnegative",
				"the test is bounded",
				"the test is Lipschitz",
				"the exceptional event is measurable",
				"off the exceptional event the coefficient is within the radius")
			space := arg.TermAs[Set[Prod[A, B]]]("set_cross(Ω, V)")
			events := arg.TermAs[Set[Set[Prod[A, B]]]]("product_sigma(Ω, S, V, T)")
			law := arg.TermAs[Fun[Set[Prod[A, B]], ExtendedNonnegReal]]("«lawProduct»")
			exception := arg.TermAs[Set[Prod[A, B]]]("set_cross(E, V)")
			plain := arg.TermAs[Fun[Prod[A, B], Real]]("«plainScore»")
			shifted := arg.TermAs[Fun[Prod[A, B], Real]]("«shiftedScore»")
			noiseSize := arg.TermAs[Fun[Prod[A, B], Real]]("«liftedNoiseAbs»")
			majorant := arg.TermAs[Fun[Prod[A, B], Real]]("«productMajorant»")
			fst := arg.TermAs[Fun[Prod[A, B], A]]("λp:prod(A, B). fst(p)")
			snd := arg.TermAs[Fun[Prod[A, B], B]]("λp:prod(A, B). snd(p)")
			absoluteNoise := arg.TermAs[Fun[B, Real]]("λy:B. |Y(y)|")
			location := arg.TermAs[Fun[Prod[A, B], Real]]("λp:prod(A, B). s(fst(p))")
			coefficient := arg.TermAs[Fun[Prod[A, B], Real]]("λp:prod(A, B). t(fst(p))")
			noise := arg.TermAs[Fun[Prod[A, B], Real]]("λp:prod(A, B). Y(snd(p))")
			borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")

			leftFactor := arg.Have(
				"the first probability gives measurable subsets and total mass one",
				"measure_on(Ω, S, μ) ∧ sigma_algebra_on(Ω, S) ∧ Ω ∈ S ∧ μ(Ω) = extended_of_real(&1)",
				By(
					hyp[0],
					probability_space.ProbabilityOnDef.At(Ω, S, μ),
					measure_space.MeasureOn.At(Ω, S, μ),
					sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)),
			)
			rightFactor := arg.Have(
				"the second probability gives measurable subsets and total mass one",
				"measure_on(V, T, ν) ∧ sigma_algebra_on(V, T) ∧ V ∈ T ∧ ν(V) = extended_of_real(&1)",
				By(
					hyp[1],
					probability_space.ProbabilityOnDef.At(V, T, ν),
					measure_space.MeasureOn.At(V, T, ν),
					sigma_algebra.SigmaAlgebraOnDef.At(V, T)),
			)
			productStructure := arg.Have(
				"measurable rectangles generate the product and its projections are measurable",
				"sigma_algebra_on(set_cross(Ω, V), product_sigma(Ω, S, V, T)) ∧ "+
					"(∀s:set(A). ∀t:set(B). s ∈ S ∧ t ∈ T ⇒ set_cross(s, t) ∈ product_sigma(Ω, S, V, T)) ∧ "+
					"measurable_map(set_cross(Ω, V), product_sigma(Ω, S, V, T), Ω, S, λp:prod(A, B). fst(p)) ∧ "+
					"measurable_map(set_cross(Ω, V), product_sigma(Ω, S, V, T), V, T, λp:prod(A, B). snd(p))",
				By(leftFactor, rightFactor, measurable_space.ProductSigmaProjections.At(Ω, S, V, T)),
			)
			leftSigmaFinite := arg.Have(
				"the first probability is σ-finite",
				"sigma_finite_on(Ω, S, μ)",
				By(hyp[0], probability_space.ProbabilitySigmaFinite.At(Ω, S, μ)))
			rightSigmaFinite := arg.Have(
				"the second probability is σ-finite",
				"sigma_finite_on(V, T, ν)",
				By(hyp[1], probability_space.ProbabilitySigmaFinite.At(V, T, ν)))
			productMeasure := arg.Have(
				"the product law is a measure",
				"measure_on(set_cross(Ω, V), product_sigma(Ω, S, V, T), «lawProduct»)",
				By(leftFactor, rightSigmaFinite, product_measure.ProductMeasureOn.At(Ω, S, μ, V, T, ν)),
			)
			totalMass := arg.Have(
				"the product carrier has total mass one",
				"«lawProduct»(set_cross(Ω, V)) = extended_of_real(&1)",
				By(
					Normalized,
					leftFactor,
					rightFactor,
					measure_space.MeasureOn.At(V, T, ν),
					product_measure.ProductMeasureRectangle.At(Ω, S, μ, ν, Ω, V),
					extended_nonneg_real.MulOne.At(arg.TermAs[ExtendedNonnegReal]("μ(Ω)"))),
			)
			exceptionMass := arg.Have(
				"the exceptional cylinder has the mass of its first factor",
				"«lawProduct»(set_cross(E, V)) = μ(E)",
				By(
					Normalized,
					leftFactor,
					rightFactor,
					hyp[11],
					measure_space.MeasureOn.At(V, T, ν),
					product_measure.ProductMeasureRectangle.At(Ω, S, μ, ν, E, V),
					extended_nonneg_real.MulOne.At(arg.TermAs[ExtendedNonnegReal]("μ(E)"))),
			)
			productProbability := arg.Have(
				"the product law is a probability",
				"probability_on(set_cross(Ω, V), product_sigma(Ω, S, V, T), «lawProduct»)",
				By(productMeasure, totalMass, probability_space.ProbabilityOnDef.At(space, events, law)),
			)
			locationMeasurable := arg.Have(
				"the location lifts along the first coordinate",
				"real_measurable(set_cross(Ω, V), product_sigma(Ω, S, V, T), λp:prod(A, B). s(fst(p)))",
				By(
					productStructure,
					hyp[2],
					measurable_space.MeasurableCompose.At(space,
						events,
						Ω,
						S,
						arg.TermAs[Set[Real]]("𝕌"),
						borel,
						fst,
						s),
					measurable_function.RealMeasurableDef.At(Ω, S, s),
					measurable_function.RealMeasurableDef.At(space,
						events,
						location),
					functions.ComposeApply.At(s,
						fst)),
			)
			coefficientMeasurable := arg.Have(
				"the coefficient lifts along the first coordinate",
				"real_measurable(set_cross(Ω, V), product_sigma(Ω, S, V, T), λp:prod(A, B). t(fst(p)))",
				By(
					productStructure,
					hyp[3],
					measurable_space.MeasurableCompose.At(space,
						events,
						Ω,
						S,
						arg.TermAs[Set[Real]]("𝕌"),
						borel,
						fst,
						t),
					measurable_function.RealMeasurableDef.At(Ω, S, t),
					measurable_function.RealMeasurableDef.At(space,
						events,
						coefficient),
					functions.ComposeApply.At(t,
						fst)),
			)
			noiseMeasurable := arg.Have(
				"the noise lifts along the second coordinate",
				"real_measurable(set_cross(Ω, V), product_sigma(Ω, S, V, T), λp:prod(A, B). Y(snd(p)))",
				By(
					productStructure,
					hyp[4],
					measurable_space.MeasurableCompose.At(space,
						events,
						V,
						T,
						arg.TermAs[Set[Real]]("𝕌"),
						borel,
						snd,
						Y),
					measurable_function.RealMeasurableDef.At(V, T, Y),
					measurable_function.RealMeasurableDef.At(space,
						events,
						noise),
					functions.ComposeApply.At(Y,
						snd)),
			)
			perturbationMeasurable := arg.Have(
				"the weighted noise is measurable on the product",
				"real_measurable(set_cross(Ω, V), product_sigma(Ω, S, V, T), λp:prod(A, B). t(fst(p)) * Y(snd(p)))",
				By(
					productStructure,
					coefficientMeasurable,
					noiseMeasurable,
					measurable_function.RealMeasurableMul.At(space,
						events,
						coefficient,
						noise)),
			)
			locationShiftMeasurable := arg.Have(
				"adding the perturbation preserves measurability",
				"real_measurable(set_cross(Ω, V), "+
					"    product_sigma(Ω, S, V, T), "+
					"    λp:prod(A, B). s(fst(p)) + t(fst(p)) * Y(snd(p)))",
				By(
					productStructure,
					locationMeasurable,
					perturbationMeasurable,
					measurable_function.RealMeasurableAdd.At(space,
						events,
						location,
						arg.TermAs[Fun[Prod[A, B], Real]]("λp:prod(A, B). t(fst(p)) * Y(snd(p))"))),
			)
			noiseSizeMeasurable := arg.Have(
				"the absolute noise is measurable on the product",
				"real_measurable(set_cross(Ω, V), product_sigma(Ω, S, V, T), «liftedNoiseAbs»)",
				By(
					productStructure,
					noiseMeasurable,
					measurable_function.RealMeasurableAbs.At(space, events, noise)),
			)
			plainMeasurable := arg.Have(
				"the plain test is measurable on the product",
				"real_measurable(set_cross(Ω, V), product_sigma(Ω, S, V, T), «plainScore»)",
				By(locationMeasurable, hyp[6], borel_function.RealMeasurableCompose.At(space, events, location, f)),
			)
			shiftedMeasurable := arg.Have(
				"the shifted test is measurable on the product",
				"real_measurable(set_cross(Ω, V), product_sigma(Ω, S, V, T), «shiftedScore»)",
				By(
					locationShiftMeasurable,
					hyp[6],
					borel_function.RealMeasurableCompose.At(
						space,
						events,
						arg.TermAs[Fun[Prod[A, B], Real]]("λp:prod(A, B). s(fst(p)) + t(fst(p)) * Y(snd(p))"),
						f)),
			)
			plainBound := arg.Have(
				"the plain test obeys the uniform bound",
				"∀p:prod(A, B). p ∈ set_cross(Ω, V) ⇒ |«plainScore»(p)| ≤ B",
				Derive(func(b *Argument) {
					b.FixAs[Prod[A, B]]("p")
					b.Assume()
					b.Show(
						"apply the uniform bound at the test argument",
						By(hyp[9].At(b.TermAs[Real]("s(fst(p))"))))
				}))
			plainIntegrable := arg.Have(
				"the plain test is integrable",
				"real_integrable(set_cross(Ω, V), product_sigma(Ω, S, V, T), «lawProduct», «plainScore»)",
				By(
					productProbability,
					plainMeasurable,
					plainBound,
					probability_space.BoundedIntegrable.At(space, events, law, plain, arg.TermAs[Real]("B"))),
			)
			shiftedBound := arg.Have(
				"the shifted test obeys the uniform bound",
				"∀p:prod(A, B). p ∈ set_cross(Ω, V) ⇒ |«shiftedScore»(p)| ≤ B",
				Derive(func(b *Argument) {
					b.FixAs[Prod[A, B]]("p")
					b.Assume()
					b.Show(
						"apply the uniform bound at the test argument",
						By(hyp[9].At(b.TermAs[Real]("s(fst(p)) + t(fst(p)) * Y(snd(p))"))))
				}))
			shiftedIntegrable := arg.Have(
				"the shifted test is integrable",
				"real_integrable(set_cross(Ω, V), product_sigma(Ω, S, V, T), «lawProduct», «shiftedScore»)",
				By(
					productProbability,
					shiftedMeasurable,
					shiftedBound,
					probability_space.BoundedIntegrable.At(space, events, law, shifted, arg.TermAs[Real]("B"))),
			)
			embeddedNoiseMeasurable := arg.Have(
				"Tonelli applies to the embedded absolute noise",
				"extended_measurable(set_cross(Ω, V), "+
					"    product_sigma(Ω, S, V, T), "+
					"    λp:prod(A, B). extended_of_real(«liftedNoiseAbs»(p)))",
				By(
					productStructure,
					noiseSizeMeasurable,
					measurable_function.ExtendedMeasurableOfReal.At(space,
						events,
						noiseSize)),
			)
			finiteNoiseMoment := arg.Have(
				"the second law has a finite absolute first moment",
				"nonneg_integral(V, T, ν, λy:B. extended_of_real(|Y(y)|)) ≠ extended_infinity",
				By(hyp[5], measure_integral.IntegrablePartsFinite.At(V, T, ν, absoluteNoise)),
			)
			embeddedMoment := arg.Have(
				"the finite moment is recovered by embedding its real value",
				"extended_of_real(extended_to_real(nonneg_integral(V, T, ν, λy:B. extended_of_real(|Y(y)|)))) = "+
					"nonneg_integral(V, T, ν, λy:B. extended_of_real(|Y(y)|))",
				By(
					finiteNoiseMoment,
					extended_nonneg_real.OfRealToReal.At(
						arg.TermAs[ExtendedNonnegReal]("nonneg_integral(V, T, ν, λy:B. extended_of_real(|Y(y)|))"))),
			)
			momentNonnegative := arg.Have(
				"the real value of the moment is nonnegative",
				"∀x:A. x ∈ Ω ⇒ &0 ≤ extended_to_real(nonneg_integral(V, T, ν, λy:B. extended_of_real(|Y(y)|)))",
				By(
					extended_nonneg_real.ToRealNonneg.At(
						arg.TermAs[ExtendedNonnegReal]("nonneg_integral(V, T, ν, λy:B. extended_of_real(|Y(y)|))"))),
			)
			constantMoment := arg.Have(
				"the first law integrates the constant moment to itself",
				"nonneg_integral(Ω, "+
					"    S, "+
					"    μ, "+
					"    λx:A. "+
					"        extended_of_real( "+
					"            extended_to_real(nonneg_integral(V, T, ν, λy:B. extended_of_real(|Y(y)|))))) = "+
					"extended_of_real(extended_to_real(nonneg_integral(V, T, ν, λy:B. extended_of_real(|Y(y)|))))",
				By(
					hyp[0],
					momentNonnegative,
					probability_space.ExpectationConstant.At(Ω,
						S,
						μ,
						arg.TermAs[Real]("extended_to_real(nonneg_integral(V, T, ν, λy:B. extended_of_real(|Y(y)|)))")),
					probability_space.ExpectationDef.At(Ω,
						S,
						μ,
						arg.TermAs[Fun[A, Real]](
							"λx:A. extended_to_real(nonneg_integral(V, T, ν, λy:B. extended_of_real(|Y(y)|)))")),
					measure_integral.IntegralNonnegEmbedding.At(Ω,
						S,
						μ,
						arg.TermAs[Fun[A, Real]](
							"λx:A. extended_to_real(nonneg_integral(V, T, ν, λy:B. extended_of_real(|Y(y)|)))"))),
			)
			tonelliNoise := arg.Have(
				"Tonelli identifies the lifted moment with the integral of the constant moment",
				"nonneg_integral(set_cross(Ω, V), "+
					"    product_sigma(Ω, S, V, T), "+
					"    «lawProduct», "+
					"    λp:prod(A, B). extended_of_real(«liftedNoiseAbs»(p))) = "+
					"nonneg_integral(Ω, S, μ, λx:A. nonneg_integral(V, T, ν, λy:B. extended_of_real(|Y(y)|)))",
				By(
					leftSigmaFinite,
					rightSigmaFinite,
					embeddedNoiseMeasurable,
					product_measure.ProductNonnegIntegral.At(Ω,
						S,
						μ,
						V,
						T,
						ν,
						arg.TermAs[Fun2[A, B, ExtendedNonnegReal]]("λx:A. λy:B. extended_of_real(|Y(y)|)"))),
			)
			liftedMoment := arg.Have(
				"the lifted moment equals the second-law moment",
				"nonneg_integral(set_cross(Ω, V), "+
					"    product_sigma(Ω, S, V, T), "+
					"    «lawProduct», "+
					"    λp:prod(A, B). extended_of_real(«liftedNoiseAbs»(p))) = "+
					"nonneg_integral(V, T, ν, λy:B. extended_of_real(|Y(y)|))",
				By(embeddedMoment, constantMoment, tonelliNoise),
			)
			liftedNoiseIntegrable := arg.Have(
				"the lifted noise is integrable",
				"real_integrable(set_cross(Ω, V), "+
					"    product_sigma(Ω, S, V, T), "+
					"    «lawProduct», "+
					"    λp:prod(A, B). Y(snd(p)))",
				By(
					noiseMeasurable,
					liftedMoment,
					finiteNoiseMoment,
					measure_integral.RealIntegrableDef.At(space,
						events,
						law,
						noise)),
			)
			noiseSizeIntegrable := arg.Have(
				"the lifted absolute noise is integrable",
				"real_integrable(set_cross(Ω, V), product_sigma(Ω, S, V, T), «lawProduct», «liftedNoiseAbs»)",
				By(
					liftedNoiseIntegrable,
					productStructure,
					measure_integral.IntegrableAbs.At(space,
						events,
						law,
						noise)),
			)
			noiseSizeIntegral := arg.Have(
				"the real absolute moment is unchanged by lifting",
				"measure_integral(set_cross(Ω, V), product_sigma(Ω, S, V, T), «lawProduct», «liftedNoiseAbs») = "+
					"measure_integral(V, T, ν, λy:B. |Y(y)|)",
				ByArith(
					Normalized,
					liftedMoment,
					measure_integral.IntegralOfNonneg.At(space,
						events,
						law,
						noiseSize),
					measure_integral.IntegralOfNonneg.At(V, T, ν, absoluteNoise)),
			)
			product := arg.Conjuncts(
				productStructure,
				"the product σ-algebra is a σ-algebra",
				"the measurable rectangles belong to the product σ-algebra",
				"the first projection is measurable",
				"the second projection is measurable")
			exceptionMeasurable := arg.Have(
				"the exceptional cylinder is a measurable rectangle",
				"set_cross(E, V) ∈ product_sigma(Ω, S, V, T)",
				By(hyp[11], rightFactor, product[1].At(E, V)),
			)
			weightedNoiseIntegrable := arg.Have(
				"the weighted absolute noise is integrable",
				"real_integrable(set_cross(Ω, V), "+
					"    product_sigma(Ω, S, V, T), "+
					"    «lawProduct», "+
					"    λp:prod(A, B). B * a * «liftedNoiseAbs»(p))",
				By(
					productMeasure,
					noiseSizeIntegrable,
					measure_integral.IntegrableScale.At(space,
						events,
						law,
						noiseSize,
						arg.TermAs[Real]("B * a"))),
			)
			penaltyIntegrable := arg.Have(
				"the exceptional penalty is integrable",
				"real_integrable(set_cross(Ω, V), "+
					"    product_sigma(Ω, S, V, T), "+
					"    «lawProduct», "+
					"    λp:prod(A, B). COND(p ∈ set_cross(E, V), &2 * B, &0))",
				By(
					productProbability,
					exceptionMeasurable,
					probability_space.ExpectationIndicator.At(
						space, events, law, exception, arg.TermAs[Real]("&2 * B"))),
			)
			majorantIntegrable := arg.Have(
				"the sum of the two error terms is integrable",
				"real_integrable(set_cross(Ω, V), product_sigma(Ω, S, V, T), «lawProduct», «productMajorant»)",
				By(
					productMeasure,
					weightedNoiseIntegrable,
					penaltyIntegrable,
					measure_integral.IntegrableAdd.At(space,
						events,
						law,
						arg.TermAs[Fun[Prod[A, B], Real]]("λp:prod(A, B). B * a * «liftedNoiseAbs»(p)"),
						arg.TermAs[Fun[Prod[A, B], Real]]("λp:prod(A, B). COND(p ∈ set_cross(E, V), &2 * B, &0)"))),
			)
			penaltyCost := arg.Have(
				"the penalty integrates to the oscillation times the exceptional mass",
				"measure_integral(set_cross(Ω, V), "+
					"    product_sigma(Ω, S, V, T), "+
					"    «lawProduct», "+
					"    λp:prod(A, B). COND(p ∈ set_cross(E, V), &2 * B, &0)) = "+
					"&2 * B * extended_to_real(μ(E))",
				ByArith(
					Normalized,
					productMeasure,
					exceptionMeasurable,
					exceptionMass,
					event_integral.EventIntegralConst.At(space,
						events,
						law,
						exception,
						arg.TermAs[Real]("&2 * B")),
					event_integral.EventIntegralDef.At(space,
						events,
						law,
						exception,
						arg.TermAs[Fun[Prod[A, B], Real]]("λp:prod(A, B). &2 * B"))),
			)
			noiseCost := arg.Have(
				"the weighted noise integrates to its scaled first moment",
				"measure_integral(set_cross(Ω, V), "+
					"    product_sigma(Ω, S, V, T), "+
					"    «lawProduct», "+
					"    λp:prod(A, B). B * a * «liftedNoiseAbs»(p)) = "+
					"B * a * expectation(V, T, ν, λy:B. |Y(y)|)",
				By(
					noiseSizeIntegral,
					productMeasure,
					measure_integral.IntegralScale.At(space,
						events,
						law,
						noiseSize,
						arg.TermAs[Real]("B * a")),
					probability_space.ExpectationDef.At(V, T, ν, absoluteNoise)),
			)
			majorantCost := arg.Have(
				"integrating the majorant adds the two error costs",
				"measure_integral(set_cross(Ω, V), product_sigma(Ω, S, V, T), «lawProduct», «productMajorant») = "+
					"B * a * expectation(V, T, ν, λy:B. |Y(y)|) + &2 * B * extended_to_real(μ(E))",
				By(
					noiseCost,
					penaltyCost,
					weightedNoiseIntegrable,
					penaltyIntegrable,
					productMeasure,
					measure_integral.IntegralAdd.At(space,
						events,
						law,
						arg.TermAs[Fun[Prod[A, B], Real]]("λp:prod(A, B). B * a * «liftedNoiseAbs»(p)"),
						arg.TermAs[Fun[Prod[A, B], Real]]("λp:prod(A, B). COND(p ∈ set_cross(E, V), &2 * B, &0)"))),
			)
			shiftedFubini := arg.Have(
				"Fubini integrates the shifted test in the second variable first",
				"«productIntegral»(«shiftedScore») = "+
					"measure_integral(Ω, S, μ, λx:A. measure_integral(V, T, ν, λy:B. f(s(x) + t(x) * Y(y))))",
				By(
					leftSigmaFinite,
					rightSigmaFinite,
					shiftedIntegrable,
					product_measure.ProductIntegral.At(Ω,
						S,
						μ,
						V,
						T,
						ν,
						arg.TermAs[Fun2[A, B, Real]]("λx:A. λy:B. f(s(x) + t(x) * Y(y))"))),
			)
			plainFubini := arg.Have(
				"Fubini integrates the plain test in the second variable first",
				"«productIntegral»(«plainScore») = "+
					"measure_integral(Ω, S, μ, λx:A. measure_integral(V, T, ν, λy:B. f(s(x))))",
				By(
					leftSigmaFinite,
					rightSigmaFinite,
					plainIntegrable,
					product_measure.ProductIntegral.At(Ω,
						S,
						μ,
						V,
						T,
						ν,
						arg.TermAs[Fun2[A, B, Real]]("λx:A. λy:B. f(s(x))"))),
			)
			shiftedMean := arg.Have(
				"the shifted product integral is the nested expectation",
				"«productIntegral»(«shiftedScore») = "+
					"expectation(Ω, S, μ, λx:A. expectation(V, T, ν, λy:B. f(s(x) + t(x) * Y(y))))",
				Simp(Fwd(probability_space.ExpectationDef)),
				By(shiftedFubini),
			)
			constantSlices := arg.Have(
				"the plain test is constant in the second variable",
				"(λx:A. measure_integral(V, T, ν, λy:B. f(s(x)))) = λx:A. f(s(x))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[A]("x")
					b.Show(
						"integrating a constant against a probability leaves its value",
						By(
							hyp[1],
							probability_space.ExpectationConstant.At(V, T, ν, b.TermAs[Real]("f(s(x))")),
							probability_space.ExpectationDef.At(V, T, ν, b.TermAs[Fun[B, Real]]("λy:B. f(s(x))"))))
				}))
			plainMean := arg.Have(
				"the plain product integral is the original expectation",
				"«productIntegral»(«plainScore») = expectation(Ω, S, μ, λx:A. f(s(x)))",
				By(
					plainFubini,
					constantSlices,
					probability_space.ExpectationDef.At(Ω,
						S,
						μ,
						arg.TermAs[Fun[A, Real]]("λx:A. f(s(x))"))),
			)
			pointwise := arg.Have(
				"the majorant bounds the absolute test difference",
				"∀p:prod(A, B). p ∈ set_cross(Ω, V) ⇒ |«shiftedScore»(p) - «plainScore»(p)| ≤ «productMajorant»(p)",
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[A, B]]("p")
					inSpace := b.Assume()
					b.Cases(b.Term("p ∈ set_cross(E, V)"))
					b.When(
						"on the exceptional cylinder",
						func(c *Argument, onEvent Fact) {
							oscillation := c.Have(
								"the uniform test bounds give an oscillation of at most twice the bound",
								"|«shiftedScore»(p) - «plainScore»(p)| ≤ &2 * B",
								ByArith(inSpace, shiftedBound.At(p), plainBound.At(p)))
							coefficientNonnegative := c.Have(
								"the product of the bound and radius is nonnegative",
								"&0 ≤ B * a",
								ByArith(
									hyp[7],
									hyp[8],
									real_order_ring.LessEqMulRight.At(c.TermAs[Real]("&0"), c.TermAs[Real]("B"), a)))
							weightedNoiseNonnegative := c.Have(
								"the noise part of the majorant is nonnegative",
								"&0 ≤ B * a * «liftedNoiseAbs»(p)",
								ByArith(
									coefficientNonnegative,
									real_sgn_abs.AbsNonneg.At(c.TermAs[Real]("Y(snd(p))")),
									real_order_ring.LessEqMulRight.At(c.TermAs[Real]("&0"), c.TermAs[Real]("B * a"),
										c.TermAs[Real]("«liftedNoiseAbs»(p)"))))
							c.Show(
								"the exceptional penalty covers the oscillation",
								ByArith(onEvent, oscillation, weightedNoiseNonnegative))
						})
					b.Otherwise(
						"off the exceptional cylinder",
						func(c *Argument, offEvent Fact) {
							firstOutside := c.Have(
								"the first coordinate lies outside the exceptional event",
								"fst(p) ∈ Ω ∧ fst(p) ∉ E",
								By(
									offEvent,
									inSpace,
									set_product.InCrossProjections.At(Ω, V, p),
									set_product.InCrossProjections.At(E, V, p)))
							localCoefficient := c.Have(
								"the smoothing coefficient is bounded by the radius",
								"|t(fst(p))| ≤ a",
								By(firstOutside, hyp[12]))
							localOscillation := c.Have(
								"the test difference is bounded by the perturbation times the Lipschitz constant",
								"|«shiftedScore»(p) - «plainScore»(p)| ≤ B * |t(fst(p)) * Y(snd(p))|",
								ByArith(hyp[10].At(c.TermAs[Real]("s(fst(p))"),
									c.TermAs[Real]("s(fst(p)) + t(fst(p)) * Y(snd(p))"))))
							localNoise := c.Have(
								"the perturbation has size at most the radius times the absolute noise",
								"|t(fst(p)) * Y(snd(p))| ≤ a * «liftedNoiseAbs»(p)",
								By(
									localCoefficient,
									real_sgn_abs.AbsNonneg.At(c.TermAs[Real]("Y(snd(p))")),
									real_sgn_abs.AbsMul.At(c.TermAs[Real]("t(fst(p))"), c.TermAs[Real]("Y(snd(p))")),
									real_order_ring.LessEqMulRight.At(c.TermAs[Real]("|t(fst(p))|"),
										a,
										c.TermAs[Real]("«liftedNoiseAbs»(p)"))))
							weightedLocalNoise := c.Have(
								"the Lipschitz constant preserves the perturbation bound",
								"B * |t(fst(p)) * Y(snd(p))| ≤ B * a * «liftedNoiseAbs»(p)",
								ByArith(
									localNoise,
									hyp[7],
									real_order_ring.LessEqMulLeft.At(c.TermAs[Real]("B"),
										c.TermAs[Real]("|t(fst(p)) * Y(snd(p))|"), c.TermAs[Real]("a * «liftedNoiseAbs»(p)"))))
							c.Show(
								"the weighted noise covers the error off the cylinder",
								ByArith(offEvent, localOscillation, weightedLocalNoise))
						})
				}))
			distance := arg.Have(
				"the majorant's integral bounds the distance of the two integrals",
				"|«productIntegral»(«shiftedScore») - «productIntegral»(«plainScore»)| ≤ "+
					"«productIntegral»(«productMajorant»)",
				By(
					productMeasure,
					shiftedIntegrable,
					plainIntegrable,
					majorantIntegrable,
					pointwise,
					measure_integral.IntegralAbsSubLe.At(space, events, law, shifted, plain, majorant)))
			arg.Show(
				"the bound on the integrals bounds the absolute difference of expectations",
				ByArith(Normalized, distance, shiftedMean, plainMean, majorantCost),
			)
		})
}

// normalScaleComparison — evaluating the same Lipschitz test at two multiples
// of one standard normal variable bounds the difference of their means.
func normalScaleComparison(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀f:(real → real). ∀B p q:real.",
		Hypotheses: []string{
			"real_measurable(𝕌, borel_sets(real_topology), f)",
			"∀z:real. |f(z)| ≤ B",
			"∀z w:real. |f(w) - f(z)| ≤ B * |w - z|",
		},
		Conclusion: "|«normalMean»(«scaleTest»(p)) - «normalMean»(«scaleTest»(q))| ≤ " +
			"B * |p - q| * «normalAbsMoment»",
		Abbrev: Abbrev{
			{Name: "normalIntegral", Text: "λg:(real → real). " +
				"    measure_integral(𝕌, borel_sets(real_topology), «standardNormal», g)"},
			{Name: "scaleTest", Text: "λr:real. λy:real. f(r * y)"},
			{Name: "scalingMajorant", Text: "λy:real. B * |p - q| * |y|"},
		},
	}, func(
		a *Argument,
		f *Arrow[Real, Real],
		B, p, q *Expr[Real],
		measurable, bounded, lipschitz Fact,
	) {
		line := a.TermAs[Set[Real]]("𝕌")
		borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
		normal := a.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("«standardNormal»")
		id := a.TermAs[Fun[Real, Real]]("λy:real. y")
		absolute := a.TermAs[Fun[Real, Real]]("λy:real. |y|")
		left := a.TermAs[Fun[Real, Real]]("«scaleTest»(p)")
		right := a.TermAs[Fun[Real, Real]]("«scaleTest»(q)")
		majorant := a.TermAs[Fun[Real, Real]]("«scalingMajorant»")
		coefficient := a.TermAs[Real]("B * |p - q|")
		probability := a.Have(
			"the standard normal is a probability",
			"probability_on(𝕌, borel_sets(real_topology), «standardNormal»)",
			By(normal_distribution.NormalDistributionProbability.At(
				a.TermAs[Real]("&0"), a.TermAs[Real]("&1"))))
		measure := a.Have(
			"the standard normal is a measure on the Borel sets",
			"measure_on(𝕌, borel_sets(real_topology), «standardNormal») ∧ "+
				"sigma_algebra_on(𝕌, borel_sets(real_topology))",
			By(
				probability,
				probability_space.ProbabilityOnDef.At(line, borel, normal),
				borel_function.LineBorelSigmaAlgebra))
		scalings := a.Have(
			"each rescaled test is integrable",
			"∀r:real. real_integrable(𝕌, borel_sets(real_topology), «standardNormal», «scaleTest»(r))",
			Derive(func(b *Argument) {
				r := b.FixAs[Real]("r")
				scale := b.TermAs[Fun[Real, Real]]("λy:real. r * y")
				score := b.TermAs[Fun[Real, Real]]("«scaleTest»(r)")
				scaleBorel := b.Have(
					"multiplying the identity by a constant preserves measurability",
					"real_measurable(𝕌, borel_sets(real_topology), λy:real. r * y)",
					By(
						measure,
						borel_function.RealMeasurableIdentity,
						measurable_function.RealMeasurableScale.At(line, borel, id, r)))
				scoreBorel := b.Have(
					"composing with the Borel test preserves measurability",
					"real_measurable(𝕌, borel_sets(real_topology), «scaleTest»(r))",
					By(measurable, scaleBorel, borel_function.RealMeasurableCompose.At(line, borel, scale, f)))
				pointwise := b.Have(
					"each scaled value of the test remains bounded",
					"∀y:real. y ∈ 𝕌 ⇒ |«scaleTest»(r, y)| ≤ B",
					Derive(func(c *Argument) {
						c.FixAs[Real]("y")
						c.Assume()
						c.Show(
							"apply the bound at the scaled argument",
							By(At(bounded, c.TermAs[Real]("r * y"))))
					}))
				b.Show(
					"a bounded Borel test is integrable under a probability",
					By(
						probability,
						scoreBorel,
						pointwise,
						probability_space.BoundedIntegrable.At(line, borel, normal, score, B)))
			}))
		majorantIntegrable := a.Have(
			"the weighted first absolute moment is integrable",
			"real_integrable(𝕌, borel_sets(real_topology), «standardNormal», «scalingMajorant»)",
			By(
				measure,
				normal_moments.StandardNormalAbsoluteMoment,
				measure_integral.IntegrableScale.At(line, borel, normal,
					absolute, coefficient)))
		majorantCost := a.Have(
			"the integral of the majorant scales the first absolute moment",
			"«normalIntegral»(«scalingMajorant») = B * |p - q| * «normalAbsMoment»",
			By(
				measure,
				measure_integral.IntegralScale.At(line, borel, normal, absolute, coefficient),
				probability_space.ExpectationDef.At(line, borel, normal, absolute)))
		pointwise := a.Have(
			"the coupled test difference is pointwise dominated",
			"∀y:real. y ∈ 𝕌 ⇒ |«scaleTest»(p, y) - «scaleTest»(q, y)| ≤ «scalingMajorant»(y)",
			Derive(func(b *Argument) {
				y := b.FixAs[Real]("y")
				b.Assume()
				factor := b.Have(
					"factor the scale difference",
					"p * y - q * y = (p - q) * y",
					ByArith())
				size := b.Have(
					"absolute value multiplies across the two factors",
					"|p * y - q * y| = |p - q| * |y|",
					By(Normalized, factor, real_sgn_abs.AbsMul.At(b.TermAs[Real]("p - q"), y)))
				b.Show(
					"apply the Lipschitz bound at the two scaled arguments",
					ByArith(size, At(lipschitz, b.TermAs[Real]("q * y"), b.TermAs[Real]("p * y"))))
			}))
		distance := a.Have(
			"the majorant's integral bounds the distance of the two integrals",
			"|«normalIntegral»(«scaleTest»(p)) - «normalIntegral»(«scaleTest»(q))| ≤ "+
				"«normalIntegral»(«scalingMajorant»)",
			By(
				measure,
				At(scalings, p),
				At(scalings, q),
				majorantIntegrable,
				pointwise,
				measure_integral.IntegralAbsSubLe.At(line, borel, normal, left, right, majorant)))
		a.Show(
			"the bound on the integrals controls the absolute difference of the means",
			ByArith(
				distance,
				majorantCost,
				probability_space.ExpectationDef.At(line, borel, normal, left),
				probability_space.ExpectationDef.At(line, borel, normal, right)))
	})
}

// rowErrorCombination — the cutoff, added noise, stopped-row estimate, and
// normal scaling give four errors that add by the triangle inequality.
func rowErrorCombination(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀u v w z y B C δ ε P K L:real.",
		Hypotheses: []string{
			"&0 ≤ B", "&0 ≤ δ", "&0 ≤ K", "K ≤ L",
			"|u - v| ≤ &2 * B * P",
			"|w - v| ≤ «noiseCost» + &2 * B * P",
			"|w - z| ≤ «smoothingError»(K)",
			"|z - y| ≤ «scaleCost»",
		},
		Conclusion: "|u - y| ≤ B * (real_sqrt(&2 * δ) + δ) * C + &4 * B * P + «smoothingError»(L)",
		Abbrev: Abbrev{
			{Name: "noiseCost", Text: "B * real_sqrt(&2 * δ) * C"},
			{Name: "scaleCost", Text: "B * δ * C"},
		},
	}, func(a *Argument, u, v, w, z, y, B, C, δ, ε, P, K, L *Expr[Real], h Fact) {
		parts := a.Conjuncts(
			h,
			"the test bound is nonnegative",
			"the variance tolerance is nonnegative",
			"the stopped Lindeberg mass is nonnegative",
			"the original Lindeberg mass is larger",
			"the stop changes the expectation on the exceptional event",
			"the added noise changes the stopped test",
			"the stopped smoothing estimate",
			"the variance scaling changes the normal expectation")
		lower := a.TermAs[Real]("real_sqrt(ε ^ 2 + K)")
		upper := a.TermAs[Real]("real_sqrt(ε ^ 2 + L)")
		weight := a.TermAs[Real]("B / &3 * (&1 + δ)")
		nonnegative := a.Have(
			"the square plus the stopped mass is nonnegative",
			"&0 ≤ ε ^ 2 + K",
			ByArith(parts[2], real_pow.PowTwoNonneg.At(ε)))
		squared := a.Have(
			"the smaller root squares to its argument",
			"real_sqrt(ε ^ 2 + K) ^ 2 = ε ^ 2 + K",
			By(nonnegative, real_sqrt.SqrtPowTwo.At(a.TermAs[Real]("ε ^ 2 + K"))))
		ordered := a.Have(
			"the square root term grows with the mass",
			"real_sqrt(ε ^ 2 + K) ≤ real_sqrt(ε ^ 2 + L)",
			ByArith(parts[3], squared, real_sqrt.SqrtLowerBound.At(lower, a.TermAs[Real]("ε ^ 2 + L"))))
		nonnegativeWeight := a.Have(
			"the coefficient on the square root is nonnegative",
			"&0 ≤ B / &3 * (&1 + δ)",
			ByArith(
				parts[0],
				parts[1],
				real_order_ring.LessEqMulRight.At(a.TermAs[Real]("&0"),
					a.TermAs[Real]("B / &3"), a.TermAs[Real]("&1 + δ"))))
		monotone := a.Have(
			"the smoothing budget grows with the Lindeberg mass",
			"«smoothingError»(K) ≤ «smoothingError»(L)",
			ByArith(
				parts[0],
				parts[3],
				ordered,
				nonnegativeWeight,
				real_order_ring.LessEqMulLeft.At(B, K, L),
				real_order_ring.LessEqMulLeft.At(weight, lower, upper)))
		triangle := a.Have(
			"absolute distance satisfies the triangle inequality",
			"∀left middle right:real. |left - right| ≤ |left - middle| + |middle - right|",
			Derive(func(b *Argument) {
				b.FixAs[Real]("left")
				b.FixAs[Real]("middle")
				b.FixAs[Real]("right")
				b.Show(
					"add the two signed differences before taking absolute values",
					ByArith(real_sgn_abs.AbsTriangle.At(b.TermAs[Real]("left - middle"),
						b.TermAs[Real]("middle - right"))))
			}))
		cutoff := a.Have(
			"stopping and adding the remaining noise charge the exceptional event twice",
			"|u - w| ≤ «noiseCost» + &4 * B * P",
			ByArith(parts[4], parts[5], At(triangle, u, v, w)))
		normal := a.Have(
			"the smoothing estimate and final normal scaling give the other two costs",
			"|w - y| ≤ «smoothingError»(L) + «scaleCost»",
			ByArith(parts[6], parts[7], monotone, At(triangle, w, z, y)))
		a.Show(
			"sum the costs of the four comparisons",
			ByArith(cutoff, normal, At(triangle, u, w, y)))
	})
}

// stoppedRowAnalytics — an expectation u within 2B·μ(E) of the test's
// expectation at a row's sum is within four errors of the standard normal mean.
// Adding a noise t·Y, |t| ≤ √(2δ) off E, moves the row's expectation by at most
// B·√(2δ)·E|Y| + 2B·μ(E) (standardNoise); with t the noise the clock 1 + δ has
// left, the smoothed row is within the Lindeberg bound of the normal at
// √(1 + δ) (lindeberg_bound.MartingaleLindebergSmoothing at c = 1 + δ); and rescaling √(1 + δ)
// to 1 costs B·δ·E|Y| (normalClock). rowErrorCombination adds the four.
var stoppedRowAnalytics = stoppedRowAnalyticsThm{family.Add(registry.ProofEntry{
	Name: "stoppedRowAnalytics",
	Key:  "prop_e2ee55851daa9114",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀n:num. " +
			"∀ξ v:(num → A → real). " +
			"∀D:(num → real → real). " +
			"∀t:(A → real). " +
			"∀E:set(A). " +
			"∀B δ ε L u:real.",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"martingale_difference_row(Ω, S, μ, F, n, ξ, v)",
			"measure_ae(Ω, S, μ, λx:A. «rowTotal»(v, n, x) ≤ &1 + δ)",
			"(∀k:num. ∀y:real. k ≤ 2 ⇒ real_derivative_at(D(k), y, D(k + 1)(y))) ∧ " +
				"(∀y:real. |D(0)(y)| ≤ B) ∧ " +
				"(∀y:real. |D(2)(y)| ≤ B ∧ |D(3)(y)| ≤ B) ∧ " +
				"real_measurable(𝕌, borel_sets(real_topology), D(0)) ∧ " +
				"(∀z w:real. |D(0)(w) - D(0)(z)| ≤ B * |w - z|) ∧ " +
				"&0 ≤ B",
			"&0 < δ ∧ " +
				"&0 < ε ∧ " +
				"real_measurable(Ω, S, «rowTotal»(ξ, n)) ∧ " +
				"real_measurable(Ω, S, t) ∧ " +
				"E ∈ S ∧ " +
				"(∀x:A. x ∈ Ω ∧ x ∉ E ⇒ |t(x)| ≤ real_sqrt(&2 * δ)) ∧ " +
				"«noiseAverage»(t) = «noiseAverage»(«remainderNoise») ∧ " +
				"|u - «plainAverage»| ≤ &2 * B * extended_to_real(μ(E)) ∧ " +
				"&0 ≤ «smallRemainder» ∧ " +
				"«smallRemainder» ≤ L",
		},
		Conclusion: "|u - «normalMean»(D(0))| ≤ " +
			"B * (real_sqrt(&2 * δ) + δ) * «normalAbsMoment» + " +
			"&4 * B * extended_to_real(μ(E)) + " +
			"«smoothingError»(L)",
		Abbrev: Abbrev{
			{Name: "standardNormal", Text: "normal_distribution(&0, &1)"},
			{Name: "normalMean", Text: "λf:(real → real). " +
				"    expectation(𝕌, borel_sets(real_topology), «standardNormal», f)"},
			{Name: "normalAbsMoment", Text: "«normalMean»(λy:real. |y|)"},
			{Name: "rowTotal", Text: "λξ:(num → A → real). λn:num. λx:A. Σ_{k<n} ξ(k, x)"},
			{Name: "cappedNormalTest", Text: "λy:real. D(0)(real_sqrt(&1 + δ) * y)"},
			{Name: "remainderNoise", Text: "λx:A. real_sqrt(&1 + δ - «rowTotal»(v, n, x))"},
			{Name: "noiseAverage", Text: "λq:(A → real). " +
				"    expectation(Ω, S, μ, λx:A. «normalMean»(λy:real. D(0)(«rowTotal»(ξ, n, x) + q(x) * y)))"},
			{Name: "plainAverage", Text: "expectation(Ω, S, μ, λx:A. D(0)(«rowTotal»(ξ, n, x)))"},
			{Name: "smallRemainder", Text: "lindeberg_sum(Ω, S, μ, n, ξ, ε)"},
			{Name: "smoothingError", Text: "λK:real. " +
				"    B * ε / &6 * (&1 + δ) + B * K + B / &3 * (&1 + δ) * real_sqrt(ε ^ 2 + K)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		noiseComparison := independentNoiseComparison(ctx)
		errorSum := rowErrorCombination(ctx)
		scaleComparison := normalScaleComparison(ctx)
		sqrtClockGap := ctx.Lemma(Statement{
			Binders:    "∀δ:real.",
			Hypotheses: []string{"&0 < δ"},
			Conclusion: "|real_sqrt(&1 + δ) - &1| ≤ δ",
		}, func(a *Argument, δ *Expr[Real], positive Fact) {
			clock := a.TermAs[Real]("&1 + δ")
			a.Show(
				"the root of 1 + δ lies between 1 and 1 + δ",
				ByArith(positive, real_sqrt.SqrtNonneg.At(clock), real_sqrt.SqrtPowTwo.At(clock)))
		})
		standardNoise := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀s t:(A → real). " +
				"∀f:(real → real). " +
				"∀E:set(A). " +
				"∀B a:real.",
			Hypotheses: []string{
				"probability_on(Ω, S, μ)",
				"real_measurable(Ω, S, s)",
				"real_measurable(Ω, S, t)",
				"real_measurable(𝕌, borel_sets(real_topology), f)",
				"&0 ≤ B",
				"&0 ≤ a",
				"∀y:real. |f(y)| ≤ B",
				"∀u w:real. |f(w) - f(u)| ≤ B * |w - u|",
				"E ∈ S",
				"∀x:A. x ∈ Ω ∧ x ∉ E ⇒ |t(x)| ≤ a",
			},
			Conclusion: "|expectation(Ω, S, μ, λx:A. «normalMean»(λy:real. f(s(x) + t(x) * y))) - " +
				"expectation(Ω, S, μ, λx:A. f(s(x)))| ≤ " +
				"B * a * «normalAbsMoment» + &2 * B * extended_to_real(μ(E))",
		}, func(
			arg *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			s, t *Arrow[A, Real],
			f *Arrow[Real, Real],
			E *Expr[Set[A]],
			B, a *Expr[Real],
			h Fact,
		) {
			line := arg.TermAs[Set[Real]]("𝕌")
			borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			identity := arg.TermAs[Fun[Real, Real]]("λy:real. y")
			arg.Show(
				"the standard normal is a noise law with a finite first absolute moment",
				By(
					h,
					borel_function.RealMeasurableIdentity,
					normal_distribution.NormalDistributionProbability.At(
						arg.TermAs[Real]("&0"), arg.TermAs[Real]("&1")),
					normal_moments.StandardNormalAbsoluteMoment,
					At(
						noiseComparison,
						Ω,
						S,
						μ,
						line,
						borel,
						arg.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("«standardNormal»"),
						s,
						t,
						identity,
						f,
						E,
						B,
						a)))
		})
		normalClock := ctx.Lemma(Statement{
			Binders: "∀f:(real → real). ∀B δ:real.",
			Hypotheses: []string{
				"real_measurable(𝕌, borel_sets(real_topology), f)",
				"&0 ≤ B",
				"&0 < δ",
				"∀y:real. |f(y)| ≤ B",
				"∀u w:real. |f(w) - f(u)| ≤ B * |w - u|",
			},
			Conclusion: "|«normalMean»(λy:real. f(real_sqrt(&1 + δ) * y)) - «normalMean»(f)| ≤ " +
				"B * δ * «normalAbsMoment»",
		}, func(a *Argument, f *Arrow[Real, Real], B, δ *Expr[Real], h Fact) {
			line := a.TermAs[Set[Real]]("𝕌")
			borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			normal := a.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("«standardNormal»")
			absolute := a.TermAs[Fun[Real, Real]]("λy:real. |y|")
			root := a.TermAs[Real]("real_sqrt(&1 + δ)")
			gap := a.TermAs[Real]("|real_sqrt(&1 + δ) - &1|")
			unitScaling := a.Have(
				"scaling by one gives the same test",
				"«normalMean»(λy:real. f(&1 * y)) = «normalMean»(f)",
				Simp(Fwd(real_construction.MulLeftId)),
				Basic())
			scaleDistance := a.Have(
				"the normal test changes by the absolute scale difference",
				"|«normalMean»(λy:real. f(real_sqrt(&1 + δ) * y)) - «normalMean»(f)| ≤ "+
					"B * |real_sqrt(&1 + δ) - &1| * «normalAbsMoment»",
				By(h, unitScaling, At(scaleComparison, f, B, root, a.TermAs[Real]("&1"))))
			clockGap := a.Have(
				"the enlarged clock changes the square root by at most the tolerance",
				"|real_sqrt(&1 + δ) - &1| ≤ δ",
				By(h, At(sqrtClockGap, δ)))
			absoluteMean := a.Have(
				"the first absolute normal moment is nonnegative",
				"&0 ≤ «normalAbsMoment»",
				ByArith(
					Normalized,
					probability_space.ExpectationDef.At(line, borel, normal, absolute),
					measure_integral.IntegralNonneg.At(line, borel, normal, absolute)))
			a.Show(
				"combine the change in scale with the first absolute normal moment",
				ByArith(
					Normalized,
					h,
					scaleDistance,
					clockGap,
					absoluteMean,
					real_order_ring.LessEqMulLeft.At(B, gap, δ),
					real_order_ring.LessEqMulRight.At(
						a.TermAs[Real]("B * |real_sqrt(&1 + δ) - &1|"),
						a.TermAs[Real]("B * δ"),
						a.TermAs[Real]("«normalAbsMoment»"))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			F *Arrow[Nat, Set[Set[A]]],
			n *Expr[Nat],
			ξ, v *Arrow2[Nat, A, Real],
			D *Arrow[Nat, Fun[Real, Real]],
			t *Arrow[A, Real],
			E *Expr[Set[A]],
			B, δ, ε, L, u *Expr[Real],
			probability, row, varianceCap, test, clipping Fact,
		) {
			smooth := a.Conjuncts(
				test,
				"the test carries a tower of three derivatives",
				"the test is bounded by B",
				"its second and third derivatives are bounded by B",
				"the test is Borel",
				"the test is B-Lipschitz",
				"the bound B is nonnegative")
			clip := a.Conjuncts(
				clipping,
				"the variance tolerance is positive",
				"the Lindeberg level is positive",
				"the row sum is measurable",
				"the clipped noise is measurable",
				"the exceptional event is measurable",
				"off the exceptional event the clipped noise is at most the root of 2δ",
				"the clipped noise and the remaining clock give the same smoothed average",
				"u is within twice the bound times the exceptional mass of the plain average",
				"the Lindeberg sum is nonnegative",
				"the Lindeberg sum is at most L")
			test0 := a.TermAs[Fun[Real, Real]]("D(0)")
			radius := a.TermAs[Real]("real_sqrt(&2 * δ)")
			noiseRadius := a.Have(
				"the clipping radius is nonnegative",
				"&0 ≤ real_sqrt(&2 * δ)",
				ByArith(Normalized, clip[0], real_sqrt.SqrtNonneg.At(a.TermAs[Real]("&2 * δ"))))
			noiseDistance := a.Have(
				"the added noise changes the stopped-row expectation",
				"|«noiseAverage»(t) - «plainAverage»| ≤ "+
					"B * real_sqrt(&2 * δ) * «normalAbsMoment» + &2 * B * extended_to_real(μ(E))",
				By(
					probability,
					clip[2],
					clip[3],
					smooth[3],
					smooth[5],
					noiseRadius,
					smooth[1],
					smooth[4],
					clip[4],
					clip[5],
					At(standardNoise, Ω, S, μ, a.TermAs[Fun[A, Real]]("«rowTotal»(ξ, n)"), t, test0, E, B, radius)))
			normalClockDistance := a.Have(
				"the enlarged clock changes the standard normal expectation",
				"|«normalMean»(«cappedNormalTest») - «normalMean»(D(0))| ≤ B * δ * «normalAbsMoment»",
				By(smooth[3], smooth[5], clip[0], smooth[1], smooth[4], At(normalClock, test0, B, δ)))
			smoothingDistance := a.Have(
				"the smoothed stopped row and the enlarged normal satisfy the Lindeberg bound",
				"|«noiseAverage»(«remainderNoise») - «normalMean»(«cappedNormalTest»)| ≤ "+
					"«smoothingError»(«smallRemainder»)",
				By(
					probability,
					row,
					varianceCap,
					smooth[0],
					smooth[2],
					clip[1],
					lindeberg_bound.MartingaleLindebergSmoothing.At(
						Ω, S, μ, F, n, ξ, v, D, a.TermAs[Real]("&1 + δ"), B, B, ε)))
			clippedDistance := a.Have(
				"the clipped clock gives the same smoothing estimate",
				"|«noiseAverage»(t) - «normalMean»(«cappedNormalTest»)| ≤ «smoothingError»(«smallRemainder»)",
				By(clip[6], smoothingDistance))
			nonnegativeBounds := a.Have(
				"the comparison coefficients are nonnegative",
				"&0 ≤ B ∧ &0 ≤ δ",
				ByArith(smooth[5], clip[0]))
			a.Show(
				"add the four comparison distances",
				By(
					nonnegativeBounds,
					clip[8],
					clip[9],
					clip[7],
					noiseDistance,
					clippedDistance,
					normalClockDistance,
					At(
						errorSum,
						u,
						a.TermAs[Real]("«plainAverage»"),
						a.TermAs[Real]("«noiseAverage»(t)"),
						a.TermAs[Real]("«normalMean»(«cappedNormalTest»)"),
						a.TermAs[Real]("«normalMean»(D(0))"),
						B,
						a.TermAs[Real]("«normalAbsMoment»"),
						δ,
						ε,
						a.TermAs[Real]("extended_to_real(μ(E))"),
						a.TermAs[Real]("«smallRemainder»"),
						L)))
		})
	}),
})}

// stoppedRowCutoffData — stopping the row when its conditional variances first
// pass 1 + δ gives a row of martingale differences whose variances stay below
// the clock; one event E of the mass of {|Σv − 1| > δ} carries every failure:
// off E the stopped and the original sums agree and the clipped remaining clock
// is at most 2δ, and stopping moves the expectation of a bounded Borel test by at
// most 2B·μ(E). The clipped noise √max(1 + δ − Σ stopped variances, 0) smooths
// as the unclipped one does, since the two agree wherever the stopped clock is
// within the cap, which is almost everywhere.
var stoppedRowCutoffData = stoppedRowCutoffDataThm{family.Add(registry.ProofEntry{
	Name: "stoppedRowCutoffData",
	Key:  "prop_196786f87474a3cc",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀n:num. " +
			"∀ξ v:(num → A → real). " +
			"∀D:(num → real → real). " +
			"∀B δ:real.",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"martingale_difference_row(Ω, S, μ, F, n, ξ, v)",
			"∀y:real. |D(0)(y)| ≤ B",
			"real_measurable(𝕌, borel_sets(real_topology), D(0))",
			"&0 ≤ B",
			"&0 < δ",
		},
		Conclusion: "∃E:set(A). " +
			"    martingale_difference_row(Ω, S, μ, F, n, «stoppedIncrement», «stoppedVariance») ∧ " +
			"    (∀k:num. " +
			"        k < n ⇒ " +
			"        real_integrable(Ω, S, μ, λx:A. ξ(k, x) * ξ(k, x)) ∧ " +
			"        real_integrable(Ω, S, μ, λx:A. «stoppedIncrement»(k, x) * «stoppedIncrement»(k, x))) ∧ " +
			"    measure_ae(Ω, S, μ, λx:A. «rowTotal»(«stoppedVariance», n, x) ≤ «clock») ∧ " +
			"    real_measurable(Ω, S, «rowTotal»(«stoppedIncrement», n)) ∧ " +
			"    real_measurable(Ω, S, «clippedNoise») ∧ " +
			"    (∀x:A. " +
			"        x ∈ Ω ∧ x ∉ E ⇒ " +
			"        «rowTotal»(«stoppedIncrement», n, x) = «rowTotal»(ξ, n, x) ∧ " +
			"        |«clippedNoise»(x)| ≤ real_sqrt(&2 * δ)) ∧ " +
			"    E ∈ S ∧ " +
			"    μ(E) = μ(«badVarianceEvent») ∧ " +
			"    expectation(Ω, S, μ, «clippedScore») = expectation(Ω, S, μ, «smoothedScore») ∧ " +
			"    |expectation(Ω, S, μ, «originalScore») - expectation(Ω, S, μ, «stoppedScore»)| ≤ " +
			"    &2 * B * extended_to_real(μ(E))",
		Abbrev: Abbrev{
			{Name: "rowTotal", Text: "λξ:(num → A → real). λn:num. λx:A. Σ_{k<n} ξ(k, x)"},
			{Name: "cutEvent", Text: "λE:set(A). λX:(A → real). λx:A. COND(x ∈ E, X(x), &0)"},
			{Name: "stopEvent", Text: "λΩ:set(A). λv:(num → A → real). λc:real. λk:num. " +
				"    {x:A | x ∈ Ω ∧ Σ_{j<k + 1} v(j, x) ≤ c}"},
			{Name: "stoppedRow", Text: "λΩ:set(A). " +
				"λv:(num → A → real). " +
				"λξ:(num → A → real). " +
				"λc:real. " +
				"λk:num. " +
				"    «cutEvent»(«stopEvent»(Ω, v, c, k), ξ(k))"},
			{Name: "standardNormal", Text: "normal_distribution(&0, &1)"},
			{Name: "clock", Text: "&1 + δ"},
			{Name: "stoppedIncrement", Text: "«stoppedRow»(Ω, v, ξ, «clock»)"},
			{Name: "stoppedVariance", Text: "«stoppedRow»(Ω, v, v, «clock»)"},
			{Name: "badVarianceEvent", Text: "{x:A | x ∈ Ω ∧ δ < |«rowTotal»(v, n, x) - &1|}"},
			{Name: "varianceRemainder", Text: "λx:A. «clock» - «rowTotal»(«stoppedVariance», n, x)"},
			{Name: "clippedRemainder", Text: "λx:A. max(«varianceRemainder»(x), &0)"},
			{Name: "clippedNoise", Text: "λx:A. real_sqrt(«clippedRemainder»(x))"},
			{Name: "originalScore", Text: "λx:A. D(0)(«rowTotal»(ξ, n, x))"},
			{Name: "stoppedScore", Text: "λx:A. D(0)(«rowTotal»(«stoppedIncrement», n, x))"},
			{Name: "smoothedScore", Text: "λx:A. " +
				"    expectation(𝕌, " +
				"        borel_sets(real_topology), " +
				"        «standardNormal», " +
				"        λy:real. " +
				"            D(0)(«rowTotal»(«stoppedIncrement», n, x) + real_sqrt(«varianceRemainder»(x)) * y))"},
			{Name: "clippedScore", Text: "λx:A. " +
				"    expectation(𝕌, " +
				"        borel_sets(real_topology), " +
				"        «standardNormal», " +
				"        λy:real. D(0)(«rowTotal»(«stoppedIncrement», n, x) + «clippedNoise»(x) * y))"},
			{Name: "stoppedBounds", Text: "λx:A. " +
				"    &0 ≤ «rowTotal»(«stoppedVariance», n, x) ∧ " +
				"    «rowTotal»(«stoppedVariance», n, x) ≤ «clock» ∧ " +
				"    («rowTotal»(v, n, x) ≤ «clock» ⇒ " +
				"        «rowTotal»(«stoppedVariance», n, x) = «rowTotal»(v, n, x) ∧ " +
				"        «rowTotal»(«stoppedIncrement», n, x) = «rowTotal»(ξ, n, x))"},
			{Name: "prefixSum", Text: "λa:(num → real). λn:num. Σ_{j<n} a(j)"},
			{Name: "cutSummand", Text: "λa:(num → real). λb:(num → real). λc:real. λk:num. " +
				"    COND(Σ_{j<k + 1} a(j) ≤ c, b(k), &0)"},
			{Name: "stoppedTotal", Text: "λΩ:set(A). " +
				"λv:(num → A → real). " +
				"λξ:(num → A → real). " +
				"λc:real. " +
				"λn:num. " +
				"    «rowTotal»(«stoppedRow»(Ω, v, ξ, c), n)"},
			{Name: "stoppedProperties", Text: "λx:A. " +
				"    &0 ≤ «stoppedTotal»(Ω, v, v, c, n, x) ∧ " +
				"    «stoppedTotal»(Ω, v, v, c, n, x) ≤ c ∧ " +
				"    («rowTotal»(v, n, x) ≤ c ⇒ " +
				"        «stoppedTotal»(Ω, v, v, c, n, x) = «rowTotal»(v, n, x) ∧ " +
				"        «stoppedTotal»(Ω, v, ξ, c, n, x) = «rowTotal»(ξ, n, x))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		cutoffSums := stoppedRowSums(ctx)
		expectationAE := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀f g:(A → real). " +
				"∀P:(A → bool).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"measure_ae(Ω, S, μ, P)",
				"∀x:A. x ∈ Ω ∧ P(x) ⇒ f(x) = g(x)",
			},
			Conclusion: "expectation(Ω, S, μ, f) = expectation(Ω, S, μ, g)",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			f, g *Arrow[A, Real],
			P *Expr[Set[A]],
			h Fact,
		) {
			agree := a.Have(
				"f and g agree almost everywhere",
				"measure_ae(Ω, S, μ, λx:A. f(x) = g(x))",
				By(h, measure_space.AEMono.At(Ω, S, μ, P, a.TermAs[Set[A]]("λx:A. f(x) = g(x)"))))
			equalAE := a.Have(
				"so they are equal as classes",
				"measure_ae_eq(Ω, S, μ, f, g)",
				By(agree, measure_space.AEEqualDef.At(Ω, S, μ, f, g)))
			integrals := a.Have(
				"functions equal almost everywhere have one integral",
				"measure_integral(Ω, S, μ, f) = measure_integral(Ω, S, μ, g)",
				By(h, equalAE, measure_integral.IntegralAE.At(Ω, S, μ, f, g)))
			a.Show(
				"the expectations are the integrals",
				By(
					integrals,
					probability_space.ExpectationDef.At(Ω, S, μ, f),
					probability_space.ExpectationDef.At(Ω, S, μ, g)))
		})
		conditionalVarianceNonnegative := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀G:set(set(A)). " +
				"∀X V:(A → real).",
			Hypotheses: []string{
				"probability_on(Ω, S, μ)",
				"is_cond_exp(Ω, S, μ, G, λx:A. X(x) * X(x), V)",
			},
			Conclusion: "measure_ae(Ω, S, μ, λx:A. &0 ≤ V(x))",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			G *Expr[Set[Set[A]]],
			X, V *Arrow[A, Real],
			probability, variance Fact,
		) {
			square := a.TermAs[Fun[A, Real]]("λx:A. X(x) * X(x)")
			zero := a.TermAs[Fun[A, Real]]("λx:A. &0")
			base := a.Have(
				"the conditioning σ-algebra lies in S",
				"measure_on(Ω, S, μ) ∧ sigma_algebra_on(Ω, G) ∧ G ⊆ S",
				By(variance, conditional_expectation.IsCondExpDef.At(Ω, S, μ, G, square, V)))
			zeroExpectation := a.Have(
				"zero is its own conditional expectation",
				"is_cond_exp(Ω, S, μ, G, λx:A. &0, λx:A. &0)",
				By(
					base,
					probability,
					conditional_expectation.CondExpIdentity.At(Ω, S, μ, G, zero),
					probability_space.ExpectationConstant.At(Ω, S, μ, a.TermAs[Real]("&0")),
					measurable_function.RealMeasurableConst.At(Ω, G, a.TermAs[Real]("&0"))))
			squares := a.Have(
				"a square is nonnegative",
				"∀x:A. &0 ≤ X(x) * X(x)",
				ByArith())
			squaresAE := a.Have(
				"so it is nonnegative almost everywhere",
				"measure_ae(Ω, S, μ, λx:A. &0 ≤ X(x) * X(x))",
				By(
					base,
					squares,
					measure_space.AEOfEverywhere.At(Ω, S, μ, a.TermAs[Set[A]]("λx:A. &0 ≤ X(x) * X(x)"))))
			a.Show(
				"conditional expectation preserves the order of zero and the square",
				By(
					zeroExpectation,
					squaresAE,
					variance,
					conditional_expectation.CondExpMono.At(Ω, S, μ, G, zero, zero, square, V)))
		})
		rowSumMeasurable := measurableRowSum(ctx)
		sqrtThreshold := ctx.Lemma(Statement{
			Binders:    "∀r t:real.",
			Hypotheses: []string{"&0 ≤ r", "&0 ≤ t"},
			Conclusion: "r < real_sqrt(t) ⇔ r * r < t",
		}, func(a *Argument, r, t *Expr[Real], signs Fact) {
			a.Show(
				"for nonnegative numbers the order of the root is the order of the square",
				ByArith(signs, real_sqrt.SqrtNonneg.At(t), real_sqrt.SqrtPowTwo.At(t)))
		})
		measurableSqrt := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀q:(A → real).",
			Hypotheses: []string{
				"sigma_algebra_on(Ω, S)",
				"real_measurable(Ω, S, q)",
				"∀x:A. x ∈ Ω ⇒ &0 ≤ q(x)",
			},
			Conclusion: "real_measurable(Ω, S, λx:A. real_sqrt(q(x)))",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			q *Arrow[A, Real],
			sigma, measurable, nonnegative Fact,
		) {
			root := a.TermAs[Fun[A, Real]]("λx:A. real_sqrt(q(x))")
			rootNonnegative := a.Have(
				"the root is nonnegative on Ω",
				"∀x:A. x ∈ Ω ⇒ &0 ≤ real_sqrt(q(x))",
				Derive(func(b *Argument) {
					b.FixAs[A]()
					inSpace := b.Assume()
					b.Show(
						"the root of a nonnegative number is nonnegative",
						By(inSpace, nonnegative, real_sqrt.SqrtNonneg.At(b.TermAs[Real]("q(x)"))))
				}))
			rays := a.Have(
				"each nonnegative ray of the root is an event",
				"∀r:real. &0 ≤ r ⇒ {x:A | x ∈ Ω ∧ r < real_sqrt(q(x))} ∈ S",
				Derive(func(b *Argument) {
					r := b.FixAs[Real]()
					rNonnegative := b.Assume()
					threshold := b.Have(
						"the root of q exceeds r exactly where q exceeds r · r",
						"∀x:A. x ∈ Ω ⇒ (r < real_sqrt(q(x)) ⇔ r * r < q(x))",
						Derive(func(c *Argument) {
							c.FixAs[A]()
							inSpace := c.Assume()
							c.Show(
								"compare the squares at this point",
								By(inSpace, nonnegative, rNonnegative, At(sqrtThreshold, r, c.TermAs[Real]("q(x)"))))
						}))
					sameRay := b.Have(
						"the ray of the root is a ray of q",
						"{x:A | x ∈ Ω ∧ r < real_sqrt(q(x))} = {x:A | x ∈ Ω ∧ r * r < q(x)}",
						BySets(threshold))
					b.Show(
						"the rays of a measurable function are events",
						sameRay.Rw(),
						By(sigma, measurable, measurable_function.RealMeasurableIffRay.At(Ω, S, q)))
				}))
			a.Show(
				"a nonnegative function whose nonnegative rays are events is measurable",
				By(rays, rootNonnegative, sigma, measurable_function.RealMeasurableIffNonnegRay.At(Ω, S, root)))
		})
		enlargeByNullEvent := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀U P:(A → bool).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"U ∈ S",
				"measure_ae(Ω, S, μ, P)",
			},
			Conclusion: "∃E:set(A). E ∈ S ∧ μ(E) = μ(U) ∧ (∀x:A. x ∈ Ω ∧ x ∉ E ⇒ x ∉ U ∧ P(x))",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			U, P *Expr[Set[A]],
			measure, event, almost Fact,
		) {
			N, null := a.ObtainAs[Set[A]](
				"a null event covers the points where P fails",
				"∃N:set(A). N ∈ S ∧ μ(N) = extended_of_real(&0) ∧ {x:A | x ∈ Ω ∧ ¬P(x)} ⊆ N",
				By(
					almost,
					measure_space.AlmostEverywhereDef.At(Ω, S, μ, P),
					measure_space.NullSetDef.At(Ω, S, μ, a.TermAs[Set[A]]("{x:A | x ∈ Ω ∧ ¬P(x)}"))))
			extra := a.TermAs[Set[A]]("U ∪ N ∖ U")
			a.Take(a.TermAs[Set[A]]("U ∪ N"))
			events := a.Have(
				"U ∪ N and its part outside U are events",
				"U ∪ N ∈ S ∧ U ∪ N ∖ U ∈ S",
				By(
					measure,
					event,
					null,
					measure_space.MeasureOn.At(Ω, S, μ),
					sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
			extraBelow := a.Have(
				"the part outside U lies in N",
				"μ(U ∪ N ∖ U) ≤ μ(N)",
				BySets(measure, null, events, measure_space.MeasureMono.At(Ω, S, μ, extra, N)))
			extraNull := a.Have(
				"so the part outside U is null",
				"μ(U ∪ N ∖ U) = extended_of_real(&0)",
				By(
					null,
					extraBelow,
					extended_nonneg_real.LeAntisym.At(
						a.TermAs[ExtendedNonnegReal]("μ(U ∪ N ∖ U)"),
						a.TermAs[ExtendedNonnegReal]("extended_of_real(&0)")),
					extended_nonneg_real.ZeroLe.At(a.TermAs[ExtendedNonnegReal]("μ(U ∪ N ∖ U)"))))
			split := a.Have(
				"U ∪ N splits into U and its part outside U",
				"μ(U ∪ N) = μ(U) + μ(U ∪ N ∖ U)",
				BySets(
					measure,
					event,
					events,
					measure_space.MeasureAddDiff.At(Ω, S, μ, U, a.TermAs[Set[A]]("U ∪ N"))))
			outside := a.Have(
				"off U ∪ N a point is off U and satisfies P",
				"∀x:A. x ∈ Ω ∧ x ∉ U ∪ N ⇒ x ∉ U ∧ P(x)",
				BySets(null))
			a.Show(
				"U ∪ N is an event of the mass of U carrying every failure of P",
				By(
					Normalized,
					outside,
					events,
					split,
					extraNull,
					extended_nonneg_real.AddZero.At(a.TermAs[ExtendedNonnegReal]("μ(U)"))))
		})
		measurableDifference := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f g:(A → real).",
			Hypotheses: []string{
				"sigma_algebra_on(Ω, S)",
				"real_measurable(Ω, S, f)",
				"real_measurable(Ω, S, g)",
			},
			Conclusion: "real_measurable(Ω, S, λx:A. f(x) - g(x))",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], f, g *Arrow[A, Real], h Fact) {
			a.Show(
				"f − g is f plus the negative of g",
				Simp(Fwd(real_ring.RealSubDef)),
				By(
					h,
					measurable_function.RealMeasurableNeg.At(Ω, S, g),
					measurable_function.RealMeasurableAdd.At(Ω, S, f, a.TermAs[Fun[A, Real]]("λx:A. -g(x)"))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			F *Arrow[Nat, Set[Set[A]]],
			n *Expr[Nat],
			ξ, v *Arrow2[Nat, A, Real],
			D *Arrow[Nat, Fun[Real, Real]],
			B, δ *Expr[Real],
			probability, differenceRow, bounded, testBorel, boundNonnegative, positive Fact,
		) {
			clock := a.TermAs[Real]("«clock»")
			test0 := a.TermAs[Fun[Real, Real]]("D(0)")
			stoppedIncrement := a.TermAs[Fun2[Nat, A, Real]]("«stoppedIncrement»")
			stoppedVariance := a.TermAs[Fun2[Nat, A, Real]]("«stoppedVariance»")
			originalScore := a.TermAs[Fun[A, Real]]("«originalScore»")
			stoppedScore := a.TermAs[Fun[A, Real]]("«stoppedScore»")
			measure := a.Have(
				"the probability law is a measure on a σ-algebra",
				"measure_on(Ω, S, μ) ∧ sigma_algebra_on(Ω, S)",
				By(
					probability,
					probability_space.ProbabilityOnDef.At(Ω, S, μ),
					measure_space.MeasureOn.At(Ω, S, μ)))
			clockNonnegative := a.Have(
				"the enlarged variance clock is nonnegative",
				"&0 ≤ «clock»",
				ByArith(positive))
			conditions := a.Conjuncts(
				a.Unfolded(differenceRow, martingale.MartingaleDifferenceRowDef),
				"F is a filtration",
				"below n each increment is a martingale difference with conditional variance v")
			isFiltration, row := conditions[0], conditions[1]
			stoppedRow := a.Have(
				"stopped at the clock it stays one, with the stopped conditional variances",
				"martingale_difference_row(Ω, S, μ, F, n, «stoppedIncrement», «stoppedVariance»)",
				By(differenceRow, martingale.StoppedMartingaleDifferences.At(Ω, S, μ, F, n, ξ, v, clock)))
			stoppedLaw := a.Conjuncts(
				a.Unfolded(stoppedRow, martingale.MartingaleDifferenceRowDef),
				"the stopped row runs along F",
				"the stopped increments and their conditional variances form a row of martingale differences")[1]
			varianceSigns := a.Have(
				"each conditional variance of the row is almost everywhere nonnegative",
				"∀k:num. measure_ae(Ω, S, μ, λx:A. k < n ⇒ &0 ≤ v(k, x))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					sign := b.TermAs[Set[A]]("λx:A. k < n ⇒ &0 ≤ v(k, x)")
					b.Cases(b.Term("k < n"))
					b.When(
						"in the row v(k) is the conditional expectation of a square",
						func(c *Argument, inRow Fact) {
							c.Show(
								"the conditional expectation of a square is almost everywhere nonnegative",
								By(
									inRow,
									probability,
									row,
									At(
										conditionalVarianceNonnegative,
										Ω,
										S,
										μ,
										c.TermAs[Set[Set[A]]]("F(k)"),
										c.TermAs[Fun[A, Real]]("ξ(k)"),
										c.TermAs[Fun[A, Real]]("v(k)")),
									measure_space.AEMono.At(Ω, S, μ, c.TermAs[Set[A]]("λx:A. &0 ≤ v(k, x)"), sign)))
						})
					b.Otherwise(
						"outside the row the implication holds everywhere",
						func(c *Argument, outside Fact) {
							c.Show(
								"what holds everywhere holds almost everywhere",
								By(outside, measure, measure_space.AEOfEverywhere.At(Ω, S, μ, sign)))
						})
				}))
			rowNonnegative := a.Have(
				"all the conditional variances of the row are nonnegative off one null set",
				"measure_ae(Ω, S, μ, λx:A. ∀k:num. k < n ⇒ &0 ≤ v(k, x))",
				By(
					varianceSigns,
					measure,
					measure_space.AECountable.At(
						Ω, S, μ, a.TermAs[Fun2[Nat, A, Bool]]("λk:num. λx:A. k < n ⇒ &0 ≤ v(k, x)"))))
			stoppedSums := a.Have(
				"the stopped clock stays within the cap, and below the cap stopping changes neither row sum",
				"measure_ae(Ω, S, μ, «stoppedBounds»)",
				By(rowNonnegative, clockNonnegative, At(cutoffSums, Ω, S, μ, n, ξ, v, clock)))
			measurableSums := a.Have(
				"the original and the stopped increment sums are measurable",
				"real_measurable(Ω, S, «rowTotal»(ξ, n)) ∧ "+
					"real_measurable(Ω, S, «rowTotal»(«stoppedIncrement», n))",
				By(
					isFiltration,
					row,
					stoppedLaw,
					At(rowSumMeasurable, Ω, S, F, n, ξ),
					At(rowSumMeasurable, Ω, S, F, n, stoppedIncrement)))
			squareIntegrability := a.Have(
				"the original and the stopped variances and squares are integrable",
				Statement{
					Binders:    "∀k:num.",
					Hypotheses: []string{"k < n"},
					Conclusion: "real_integrable(Ω, S, μ, v(k)) ∧ " +
						"real_integrable(Ω, S, μ, «stoppedVariance»(k)) ∧ " +
						"real_integrable(Ω, S, μ, λx:A. ξ(k, x) * ξ(k, x)) ∧ " +
						"real_integrable(Ω, S, μ, λx:A. «stoppedIncrement»(k, x) * «stoppedIncrement»(k, x))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					inRow := b.Assume()
					here := b.TermAs[Set[Set[A]]]("F(k)")
					b.Show(
						"a conditional expectation and its integrand are integrable",
						By(
							inRow,
							row,
							stoppedLaw,
							conditional_expectation.IsCondExpDef.At(
								Ω,
								S,
								μ,
								here,
								b.TermAs[Fun[A, Real]]("λx:A. ξ(k, x) * ξ(k, x)"),
								b.TermAs[Fun[A, Real]]("v(k)")),
							conditional_expectation.IsCondExpDef.At(
								Ω,
								S,
								μ,
								here,
								b.TermAs[Fun[A, Real]]("λx:A. «stoppedIncrement»(k, x) * «stoppedIncrement»(k, x)"),
								b.TermAs[Fun[A, Real]]("«stoppedVariance»(k)"))))
				}))
			measurableVariances := a.Have(
				"each original and stopped conditional variance is measurable",
				"∀k:num. k < n ⇒ real_measurable(Ω, S, v(k)) ∧ real_measurable(Ω, S, «stoppedVariance»(k))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					inRow := b.Assume()
					b.Show(
						"an integrable function is measurable",
						By(
							inRow,
							squareIntegrability,
							measure_integral.RealIntegrableDef.At(Ω, S, μ, b.TermAs[Fun[A, Real]]("v(k)")),
							measure_integral.RealIntegrableDef.At(Ω, S, μ, b.TermAs[Fun[A, Real]]("«stoppedVariance»(k)"))))
				}))
			measurableVarianceSums := a.Have(
				"the original and the stopped variance sums are measurable",
				"real_measurable(Ω, S, «rowTotal»(v, n)) ∧ real_measurable(Ω, S, «rowTotal»(«stoppedVariance», n))",
				By(
					measurableVariances,
					measure,
					measurable_function.RealMeasurableSum.At(Ω, S, v, n),
					measurable_function.RealMeasurableSum.At(Ω, S, stoppedVariance, n)))
			measurableVarianceDistance := a.Have(
				"the distance of the original clock from one is measurable",
				"real_measurable(Ω, S, λx:A. |«rowTotal»(v, n, x) - &1|)",
				By(
					measurableVarianceSums,
					measure,
					measurable_function.RealMeasurableConst.At(Ω, S, a.TermAs[Real]("&1")),
					At(
						measurableDifference,
						Ω,
						S,
						a.TermAs[Fun[A, Real]]("«rowTotal»(v, n)"),
						a.TermAs[Fun[A, Real]]("λx:A. &1")),
					measurable_function.RealMeasurableAbs.At(
						Ω, S, a.TermAs[Fun[A, Real]]("λx:A. «rowTotal»(v, n, x) - &1"))))
			badEventMeasurable := a.Have(
				"the event where the clock misses one by more than δ is an event",
				"«badVarianceEvent» ∈ S",
				By(
					measurableVarianceDistance,
					measure,
					measurable_function.RealMeasurableIffRay.At(
						Ω, S, a.TermAs[Fun[A, Real]]("λx:A. |«rowTotal»(v, n, x) - &1|"))))
			measurableClippedClock := a.Have(
				"the clipped remaining clock is measurable",
				"real_measurable(Ω, S, «clippedRemainder»)",
				By(
					measurableVarianceSums,
					measure,
					measurable_function.RealMeasurableConst.At(Ω, S, clock),
					measurable_function.RealMeasurableConst.At(Ω, S, a.TermAs[Real]("&0")),
					At(
						measurableDifference,
						Ω,
						S,
						a.TermAs[Fun[A, Real]]("λx:A. «clock»"),
						a.TermAs[Fun[A, Real]]("«rowTotal»(«stoppedVariance», n)")),
					measurable_function.RealMeasurableMax.At(
						Ω,
						S,
						a.TermAs[Fun[A, Real]]("«varianceRemainder»"),
						a.TermAs[Fun[A, Real]]("λx:A. &0"))))
			nonnegativeClippedClock := a.Have(
				"the clipped remaining clock is nonnegative",
				"∀x:A. x ∈ Ω ⇒ &0 ≤ «clippedRemainder»(x)",
				By(real_sup_inf.MaxUpperBound))
			measurableClippedNoise := a.Have(
				"the root of the clipped clock is measurable",
				"real_measurable(Ω, S, «clippedNoise»)",
				By(
					measurableClippedClock,
					measure,
					nonnegativeClippedClock,
					At(measurableSqrt, Ω, S, a.TermAs[Fun[A, Real]]("«clippedRemainder»"))))
			varianceCap := a.Have(
				"the stopped variance sum is almost everywhere at most the clock",
				"measure_ae(Ω, S, μ, λx:A. «rowTotal»(«stoppedVariance», n, x) ≤ «clock»)",
				By(
					stoppedSums,
					measure_space.AEMono.At(
						Ω,
						S,
						μ,
						a.TermAs[Set[A]]("«stoppedBounds»"),
						a.TermAs[Set[A]]("λx:A. «rowTotal»(«stoppedVariance», n, x) ≤ «clock»"))))
			scoreAgreement := a.Have(
				"the clipped and the unclipped scores agree where the stopped clock is within the cap",
				Statement{
					Binders:    "∀x:A.",
					Hypotheses: []string{"x ∈ Ω", "«rowTotal»(«stoppedVariance», n, x) ≤ «clock»"},
					Conclusion: "«clippedScore»(x) = «smoothedScore»(x)",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]()
					within := b.Assume()
					unclipped := b.Have(
						"clipping leaves a nonnegative remaining clock unchanged",
						"«clippedRemainder»(x) = «varianceRemainder»(x)",
						ByArith(within))
					b.Show(
						"equal clocks give equal Gaussian scores",
						By(unclipped))
				}))
			smoothedEquality := a.Have(
				"the clipped and the unclipped smoothing expectations agree",
				"expectation(Ω, S, μ, «clippedScore») = expectation(Ω, S, μ, «smoothedScore»)",
				By(
					scoreAgreement,
					varianceCap,
					measure,
					At(
						expectationAE,
						Ω,
						S,
						μ,
						a.TermAs[Fun[A, Real]]("«clippedScore»"),
						a.TermAs[Fun[A, Real]]("«smoothedScore»"),
						a.TermAs[Set[A]]("λx:A. «rowTotal»(«stoppedVariance», n, x) ≤ «clock»"))))
			E, exceptional := a.ObtainAs[Set[A]](
				"one event of the mass of the bad clock event carries every failure",
				"∃E:set(A). "+
					"    E ∈ S ∧ "+
					"    μ(E) = μ(«badVarianceEvent») ∧ "+
					"    (∀x:A. x ∈ Ω ∧ x ∉ E ⇒ x ∉ «badVarianceEvent» ∧ «stoppedBounds»(x))",
				By(
					measure,
					badEventMeasurable,
					stoppedSums,
					At(
						enlargeByNullEvent,
						Ω,
						S,
						μ,
						a.TermAs[Set[A]]("«badVarianceEvent»"),
						a.TermAs[Set[A]]("«stoppedBounds»"))))
			outsideException := a.Have(
				"off the exceptional event the sums agree and the clipped noise is small",
				Statement{
					Binders:    "∀x:A.",
					Hypotheses: []string{"x ∈ Ω", "x ∉ E"},
					Conclusion: "«rowTotal»(«stoppedIncrement», n, x) = «rowTotal»(ξ, n, x) ∧ " +
						"|«clippedNoise»(x)| ≤ real_sqrt(&2 * δ)",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]()
					offEvent := b.Assume()
					good := b.Have(
						"the point is off the bad clock event and the stopped sums obey their bounds there",
						"x ∉ «badVarianceEvent» ∧ «stoppedBounds»(x)",
						By(offEvent, exceptional))
					nearOne := b.Have(
						"the original clock at the point is within δ of one",
						"¬(δ < |«rowTotal»(v, n, x) - &1|)",
						BySets(offEvent, good))
					clockBounds := b.Have(
						"the original clock is within the cap and leaves at most twice the tolerance",
						"«rowTotal»(v, n, x) ≤ «clock» ∧ «clock» - «rowTotal»(v, n, x) ≤ &2 * δ ∧ &0 ≤ &2 * δ",
						ByArith(nearOne, positive))
					sumsAgree := b.Have(
						"below the cap the stopped sums are the original ones",
						"«rowTotal»(«stoppedIncrement», n, x) = «rowTotal»(ξ, n, x) ∧ "+
							"«rowTotal»(«stoppedVariance», n, x) = «rowTotal»(v, n, x)",
						By(good, clockBounds))
					clipped := b.Have(
						"the clipped remaining clock is between zero and twice the tolerance",
						"&0 ≤ «clippedRemainder»(x) ∧ «clippedRemainder»(x) ≤ &2 * δ",
						ByArith(clockBounds, sumsAgree))
					remainder := b.TermAs[Real]("«clippedRemainder»(x)")
					noise := b.TermAs[Real]("«clippedNoise»(x)")
					b.Show(
						"a clock of at most 2δ leaves noise of size at most the root of 2δ",
						ByArith(
							clipped,
							sumsAgree,
							real_sqrt.SqrtNonneg.At(remainder),
							real_sqrt.SqrtPowTwo.At(remainder),
							real_sqrt.SqrtLowerBound.At(noise, b.TermAs[Real]("&2 * δ")),
							real_sgn_abs.AbsFixedIffNonneg.At(noise)))
				}))
			boundedScores := a.Have(
				"both scores are bounded by B",
				"∀x:A. x ∈ Ω ⇒ |«originalScore»(x)| ≤ B ∧ |«stoppedScore»(x)| ≤ B",
				By(bounded))
			measurableScores := a.Have(
				"both scores are measurable",
				"real_measurable(Ω, S, «originalScore») ∧ real_measurable(Ω, S, «stoppedScore»)",
				By(
					measurableSums,
					testBorel,
					borel_function.RealMeasurableCompose.At(Ω, S, a.TermAs[Fun[A, Real]]("«rowTotal»(ξ, n)"), test0),
					borel_function.RealMeasurableCompose.At(
						Ω,
						S,
						a.TermAs[Fun[A, Real]]("«rowTotal»(«stoppedIncrement», n)"),
						test0)))
			integrableScores := a.Have(
				"both bounded scores are integrable",
				"real_integrable(Ω, S, μ, «originalScore») ∧ real_integrable(Ω, S, μ, «stoppedScore»)",
				By(
					boundedScores,
					probability,
					measurableScores,
					probability_space.BoundedIntegrable.At(Ω, S, μ, originalScore, B),
					probability_space.BoundedIntegrable.At(Ω, S, μ, stoppedScore, B)))
			boundedDifference := a.Have(
				"the two scores differ by at most twice the bound",
				"∀x:A. x ∈ Ω ⇒ |«originalScore»(x) - «stoppedScore»(x)| ≤ &2 * B",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					inSpace := b.Assume()
					b.Show(
						"both scores lie in [−B, B]",
						ByArith(inSpace, boundedScores.At(x)))
				}))
			scoresAgreeOffException := a.Have(
				"off the exceptional event the two scores agree",
				"∀x:A. x ∈ Ω ∧ x ∉ E ⇒ |«originalScore»(x) - «stoppedScore»(x)| ≤ &0",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					offEvent := b.Assume()
					b.Show(
						"the two sums agree there",
						ByArith(offEvent, outsideException.At(x)))
				}))
			lossOnEvent := a.Have(
				"the scores differ only on the exceptional event, and there by at most twice the bound",
				"|expectation(Ω, S, μ, «originalScore») - expectation(Ω, S, μ, «stoppedScore»)| ≤ "+
					"&0 + &2 * B * extended_to_real(μ(E))",
				By(
					probability,
					exceptional,
					integrableScores,
					boundedDifference,
					scoresAgreeOffException,
					real_order_ring.LessEqRefl,
					probability_space.ExpectationDifferenceOnEvent.At(
						Ω,
						S,
						μ,
						E,
						originalScore,
						stoppedScore,
						a.TermAs[Real]("&2 * B"),
						a.TermAs[Real]("&0"))))
			stoppedLoss := a.Have(
				"stopping moves the test expectation by at most twice the bound times the exceptional mass",
				"|expectation(Ω, S, μ, «originalScore») - expectation(Ω, S, μ, «stoppedScore»)| ≤ "+
					"&2 * B * extended_to_real(μ(E))",
				ByArith(lossOnEvent))
			a.Take(E)
			a.Show(
				"the exceptional event witnesses the stopped-row bounds",
				By(
					stoppedRow,
					squareIntegrability,
					varianceCap,
					measurableSums,
					measurableClippedNoise,
					outsideException,
					exceptional,
					smoothedEquality,
					stoppedLoss))
		})
	}),
})}

// measurableRowSum — the sum of a row adapted to a filtration on S is
// S-measurable: each increment is measurable at a level inside S.
func measurableRowSum(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀F:(num → set(set(A))). ∀n:num. ∀ξ:(num → A → real).",
		Hypotheses: []string{
			"filtration_on(Ω, S, F)",
			"∀k:num. k < n ⇒ real_measurable(Ω, F(k + 1), ξ(k))",
		},
		Conclusion: "real_measurable(Ω, S, «rowTotal»(ξ, n))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		F *Arrow[Nat, Set[Set[A]]],
		n *Expr[Nat],
		ξ *Arrow2[Nat, A, Real],
		isFiltration, adapted Fact,
	) {
		levels := a.Have(
			"S is a σ-algebra containing every level of the filtration",
			"sigma_algebra_on(Ω, S) ∧ (∀k:num. F(k) ⊆ S)",
			By(isFiltration, filtration.FiltrationDef.At(Ω, S, F)))
		increments := a.Have(
			"each increment is S-measurable",
			"∀k:num. k < n ⇒ real_measurable(Ω, S, ξ(k))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]()
				inRow := b.Assume()
				b.Show(
					"measurability passes up from F(k + 1) to S",
					By(
						inRow,
						adapted,
						levels,
						measurable_function.RealMeasurableSourceMono.At(
							Ω,
							b.TermAs[Set[Set[A]]]("F(k + 1)"),
							S,
							b.TermAs[Fun[A, Real]]("ξ(k)"))))
			}))
		a.Show(
			"a finite sum of measurable functions is measurable",
			By(levels, increments, measurable_function.RealMeasurableSum.At(Ω, S, ξ, n)))
	})
}

// MartingaleLindebergApproximateBound — for one row of martingale differences whose
// conditional variances sum only to about 1, the expectation of a test with three bounded
// derivatives at the row's sum is within B·(√(2δ) + δ)·E|Y| + 4B·μ(|Σv − 1| > δ), Y standard
// normal, plus the Lindeberg smoothing error, of the test's standard normal mean. The row is
// stopped where its conditional variances first pass 1 + δ (stoppedRowCutoffData): off one
// event E of the mass of {|Σv − 1| > δ} the stopped and the original sums agree and the clock
// the stopped row leaves is at most 2δ. The stopped row, smoothed by a normal variable of that
// remaining variance, is compared with the standard normal (stoppedRowAnalytics).
var MartingaleLindebergApproximateBound = martingaleLindebergApproximateBoundThm{family.Add(registry.ProofEntry{
	Name: "MartingaleLindebergApproximateBound",
	Key:  "prop_6d5266bc05fab14e",
	Reading: "The conditional variances need not sum to 1: a miss of " +
		"more than δ is paid for by 4B times the mass of the event where " +
		"it happens, a smaller one by B·(√(2δ) + δ)·E|Y|, Y standard normal.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀n:num. " +
			"∀ξ v:(num → A → real). " +
			"∀D:(num → real → real). " +
			"∀B δ ε:real.",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"martingale_difference_row(Ω, S, μ, F, n, ξ, v)",
			"∀k:num. ∀y:real. k ≤ 2 ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
			"∀k:num. ∀y:real. k ≤ 3 ⇒ |D(k)(y)| ≤ B",
			"&0 < δ",
			"&0 < ε",
		},
		Conclusion: "|«originalTestAverage» - «normalTest»| ≤ " +
			"B * (real_sqrt(&2 * δ) + δ) * «normalAbsMoment» + " +
			"&4 * B * extended_to_real(μ(«badVarianceEvent»)) + " +
			"«smoothingError»(lindeberg_sum(Ω, S, μ, n, ξ, ε))",
		Abbrev: Abbrev{
			{Name: "rowTotal", Text: "λξ:(num → A → real). λn:num. λx:A. Σ_{k<n} ξ(k, x)"},
			{Name: "cutEvent", Text: "λE:set(A). λX:(A → real). λx:A. COND(x ∈ E, X(x), &0)"},
			{Name: "stopEvent", Text: "λΩ:set(A). λv:(num → A → real). λc:real. λk:num. " +
				"    {x:A | x ∈ Ω ∧ Σ_{j<k + 1} v(j, x) ≤ c}"},
			{Name: "stoppedRow", Text: "λΩ:set(A). " +
				"λv:(num → A → real). " +
				"λξ:(num → A → real). " +
				"λc:real. " +
				"λk:num. " +
				"    «cutEvent»(«stopEvent»(Ω, v, c, k), ξ(k))"},
			{Name: "standardNormal", Text: "normal_distribution(&0, &1)"},
			{Name: "normalAbsMoment", Text: "expectation(𝕌, " +
				"    borel_sets(real_topology), " +
				"    «standardNormal», " +
				"    λy:real. |y|)"},
			{Name: "clock", Text: "&1 + δ"},
			{Name: "stoppedIncrement", Text: "«stoppedRow»(Ω, v, ξ, «clock»)"},
			{Name: "stoppedVariance", Text: "«stoppedRow»(Ω, v, v, «clock»)"},
			{Name: "badVarianceEvent", Text: "{x:A | x ∈ Ω ∧ δ < |«rowTotal»(v, n, x) - &1|}"},
			{Name: "varianceRemainder", Text: "λx:A. «clock» - «rowTotal»(«stoppedVariance», n, x)"},
			{Name: "clippedRemainder", Text: "λx:A. max(«varianceRemainder»(x), &0)"},
			{Name: "clippedNoise", Text: "λx:A. real_sqrt(«clippedRemainder»(x))"},
			{Name: "normalTest", Text: "expectation(𝕌, borel_sets(real_topology), «standardNormal», D(0))"},
			{Name: "originalTestAverage", Text: "expectation(Ω, S, μ, λx:A. D(0)(«rowTotal»(ξ, n, x)))"},
			{Name: "smoothingError", Text: "λL:real. " +
				"    B * ε / &6 * «clock» + B * L + B / &3 * «clock» * real_sqrt(ε ^ 2 + L)"},
			{Name: "eventCutRow", Text: "λE:(num → set(A)). λξ:(num → A → real). λk:num. " +
				"    «cutEvent»(E(k), ξ(k))"},
			{Name: "tailIntegral", Text: "λΩ:set(A). " +
				"λS:set(set(A)). " +
				"λμ:(set(A) → extended_nonneg_real). " +
				"λX:(A → real). " +
				"λε:real. " +
				"    event_integral(Ω, S, μ, {x:A | ε < |X(x)|}, λx:A. X(x) * X(x))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		stoppingShrinksLindeberg := lindebergCutBound(ctx)
		boundedDerivativeLipschitz := ctx.Lemma(Statement{
			Binders: "∀f g:(real → real). ∀B:real.",
			Hypotheses: []string{
				"∀t:real. real_derivative_at(f, t, g(t))",
				"∀t:real. |g(t)| ≤ B",
			},
			Conclusion: "∀u w:real. |f(w) - f(u)| ≤ B * |w - u|",
		}, func(a *Argument, f, g *Arrow[Real, Real], B *Expr[Real], derivative, bounded Fact) {
			u := a.FixAs[Real]()
			w := a.FixAs[Real]()
			inside := a.Have(
				"both points lie inside an open interval around them",
				"min(u, w) - &1 < u ∧ u < max(u, w) + &1 ∧ min(u, w) - &1 < w ∧ w < max(u, w) + &1",
				ByArith(real_sup_inf.MinLowerBound.At(u, w), real_sup_inf.MaxUpperBound.At(u, w)))
			a.Show(
				"the mean value inequality on that interval",
				By(
					derivative,
					bounded,
					inside,
					real_derivative.MeanValueInequality.At(
						f,
						g,
						a.TermAs[Real]("min(u, w) - &1"),
						a.TermAs[Real]("max(u, w) + &1"),
						B,
						u,
						w)))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			F *Arrow[Nat, Set[Set[A]]],
			n *Expr[Nat],
			ξ, v *Arrow2[Nat, A, Real],
			D *Arrow[Nat, Fun[Real, Real]],
			B, δ, ε *Expr[Real],
			probability, row, tower, bounded, δPositive, εPositive Fact,
		) {
			test0 := a.TermAs[Fun[Real, Real]]("D(0)")
			stoppedIncrement := a.TermAs[Fun2[Nat, A, Real]]("«stoppedIncrement»")
			testContinuous := a.Have(
				"the first derivative makes the test continuous",
				"∀y:real. real_continuous_at(D(0), y)",
				Derive(func(b *Argument) {
					y := b.FixAs[Real]()
					b.Show(
						"a differentiable function is continuous",
						By(tower, real_derivative.DerivativeContinuous.At(test0, y, b.TermAs[Real]("D(1)(y)"))))
				}))
			testBorel := a.Have(
				"continuous on the line, the test is Borel",
				"real_measurable(𝕌, borel_sets(real_topology), D(0))",
				By(
					testContinuous,
					real_continuous.ContinuousAtOn.At(test0, a.TermAs[Set[Real]]("𝕌")),
					borel_function.ContinuousBorelMeasurable.At(test0)))
			boundNonnegative := a.Have(
				"the uniform bound is nonnegative",
				"&0 ≤ B",
				ByArith(Normalized, bounded.At(a.TermAs[Nat]("0"), a.TermAs[Real]("&0"))))
			testBound := a.Have(
				"the test itself is bounded by B",
				"∀y:real. |D(0)(y)| ≤ B",
				Derive(func(b *Argument) {
					y := b.FixAs[Real]()
					b.Show(
						"the bound at the rung 0",
						ByArith(Normalized, bounded.At(b.TermAs[Nat]("0"), y)))
				}))
			higherBounds := a.Have(
				"the second and third derivatives are bounded by B",
				"∀y:real. |D(2)(y)| ≤ B ∧ |D(3)(y)| ≤ B",
				Derive(func(b *Argument) {
					y := b.FixAs[Real]()
					b.Show(
						"the bound at the rungs 2 and 3",
						ByArith(Normalized, bounded.At(b.TermAs[Nat]("2"), y), bounded.At(b.TermAs[Nat]("3"), y)))
				}))
			firstDerivative := a.Have(
				"D(1) is the derivative of the test",
				"∀y:real. real_derivative_at(D(0), y, D(1)(y))",
				Derive(func(b *Argument) {
					y := b.FixAs[Real]()
					b.Show(
						"the first rung of the tower",
						ByArith(Normalized, tower.At(b.TermAs[Nat]("0"), y)))
				}))
			boundedFirstDerivative := a.Have(
				"the first derivative is bounded by B",
				"∀y:real. |D(1)(y)| ≤ B",
				Derive(func(b *Argument) {
					y := b.FixAs[Real]()
					b.Show(
						"the bound at the rung 1",
						ByArith(Normalized, bounded.At(b.TermAs[Nat]("1"), y)))
				}))
			lipschitz := a.Have(
				"a bounded first derivative makes the test B-Lipschitz",
				"∀u w:real. |D(0)(w) - D(0)(u)| ≤ B * |w - u|",
				By(
					firstDerivative,
					boundedFirstDerivative,
					At(boundedDerivativeLipschitz, test0, a.TermAs[Fun[Real, Real]]("D(1)"), B)))
			E, data := a.UnpackAs[Set[A]](
				GroupPremises(
					probability,
					row,
					testBound,
					testBorel,
					boundNonnegative,
					δPositive,
					stoppedRowCutoffData.At(Ω, S, μ, F, n, ξ, v, D, B, δ)),
				"E")
			stopped := a.Conjuncts(
				data,
				"the stopped increments form a row of martingale differences",
				"the original and the stopped squares are integrable",
				"the stopped variance sum is almost everywhere at most the clock",
				"the stopped increment sum is measurable",
				"the clipped noise is measurable",
				"off E the sums agree and the clipped noise is at most the root of 2δ",
				"E is an event",
				"E has the mass of the bad clock event",
				"the clipped noise smooths as the remaining clock does",
				"stopping moves the test expectation by at most twice the bound times the mass of E")
			cutLindeberg := a.Have(
				"stopping can only shrink the Lindeberg sum",
				"lindeberg_sum(Ω, S, μ, n, «stoppedIncrement», ε) ≤ lindeberg_sum(Ω, S, μ, n, ξ, ε)",
				By(
					stopped[1],
					At(
						stoppingShrinksLindeberg,
						Ω,
						S,
						μ,
						n,
						a.TermAs[Fun2[Nat, A, Bool]]("λk:num. «stopEvent»(Ω, v, «clock», k)"),
						ξ,
						ε)))
			smallNoise := a.Have(
				"off E the clipped noise is at most the root of 2δ",
				"∀x:A. x ∈ Ω ∧ x ∉ E ⇒ |«clippedNoise»(x)| ≤ real_sqrt(&2 * δ)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					offEvent := b.Assume()
					b.Show(
						"the noise half of the bound off E",
						By(offEvent, stopped[5].At(x)))
				}))
			exceptionalMass := a.Have(
				"E and the bad clock event have the same real mass",
				"extended_to_real(μ(E)) = extended_to_real(μ(«badVarianceEvent»))",
				By(stopped[7]))
			analytics := a.Have(
				"the stopped row with its clipped noise compares the test with the standard normal",
				"|«originalTestAverage» - «normalTest»| ≤ "+
					"B * (real_sqrt(&2 * δ) + δ) * «normalAbsMoment» + "+
					"&4 * B * extended_to_real(μ(E)) + "+
					"«smoothingError»(lindeberg_sum(Ω, S, μ, n, ξ, ε))",
				By(
					probability,
					stopped[0],
					stopped[2],
					tower,
					testBound,
					higherBounds,
					testBorel,
					lipschitz,
					boundNonnegative,
					δPositive,
					εPositive,
					stopped[3],
					stopped[4],
					stopped[6],
					smallNoise,
					stopped[8],
					stopped[9],
					lindeberg_bound.LindebergSumNonnegative.At(Ω, S, μ, n, stoppedIncrement, ε),
					cutLindeberg,
					stoppedRowAnalytics.At(
						Ω,
						S,
						μ,
						F,
						n,
						stoppedIncrement,
						a.TermAs[Fun2[Nat, A, Real]]("«stoppedVariance»"),
						D,
						a.TermAs[Fun[A, Real]]("«clippedNoise»"),
						E,
						B,
						δ,
						ε,
						a.TermAs[Real]("lindeberg_sum(Ω, S, μ, n, ξ, ε)"),
						a.TermAs[Real]("«originalTestAverage»"))))
			a.Show(
				"E has the mass of the bad clock event",
				ByArith(Normalized, analytics, exceptionalMass))
		})
	}),
})}
