package measure_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// MeasureAddDiff — a measurable set inside another cuts it in two: the
// measure of the larger set is that of the smaller plus that of the rest.
// The larger set is the disjoint union of the smaller one and the rest, and
// the rest is measurable, a difference of measurable sets.
var MeasureAddDiff = measureAddDiffThm{family.Add(registry.ProofEntry{
	Name: "MeasureAddDiff",
	Key:  "prop_8a1e5bf23f2388de",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"s ∈ S",
			"t ∈ S",
			"s ⊆ t",
		},
		Conclusion: "μ(t) = μ(s) + μ(t ∖ s)",
	}), func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], measure Fact,
		s, t *Expr[Set[A]], measurableS, measurableT, inside Fact) {
		measurableRest := a.Have(
			"the part of t outside s is measurable",
			"t ∖ s ∈ S",
			By(
				a.Unfolded(measure, MeasureOn),
				sigma_algebra.SigmaFiniteOperations.At(Ω, S),
				measurableS,
				measurableT))
		split := a.Have(
			"t is s together with the part of t outside s, and the two are disjoint",
			"s ∪ (t ∖ s) = t ∧ s ∩ (t ∖ s) = ∅",
			BySets(inside))
		a.Show(
			"additivity splits μ(t) along the two parts",
			By(
				Normalized,
				MeasureAdditive.At(Ω, S, μ, s, a.TermAs[Set[A]]("t ∖ s")),
				measure,
				measurableS,
				measurableRest,
				split))
	}),
})}

// MeasureMono — a measurable set inside another measures at most as much:
// the larger measure is the smaller one plus the measure of the rest.
var MeasureMono = measureMonoThm{family.Add(registry.ProofEntry{
	Name: "MeasureMono",
	Key:  "prop_a0260a95f9013d0",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"s ∈ S",
			"t ∈ S",
			"s ⊆ t",
		},
		Conclusion: "μ(s) ≤ μ(t)",
	}), func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], measure Fact,
		s, t *Expr[Set[A]], measurableS, measurableT, inside Fact) {
		a.Show(
			"μ(t) is μ(s) plus the measure of the part of t outside s",
			By(
				Normalized,
				MeasureAddDiff.At(Ω, S, μ, s, t),
				measure,
				measurableS,
				measurableT,
				inside,
				extended_nonneg_real.LeAddRight.At(μ.Apply(s), μ.Apply(a.TermAs[Set[A]]("t ∖ s")))))
	}),
})}

// MeasureContinuousIncreasing — along an increasing sequence of measurable
// sets, the measure of the union is the supremum of the measures. Each a(n)
// lies in the union, so the supremum is at most its measure. For the other
// bound, the union is a(0) together with the rings a(n + 1) ∖ a(n), which
// are disjoint from a(0) and from each other, so its measure is μ(a(0))
// plus the series of the rings' measures. μ(a(0)) and the measures of the
// first n + 1 rings add up to μ(a(n + 1)), so that sum is at most the
// supremum.
var MeasureContinuousIncreasing = measureContinuousIncreasingThm{family.Add(registry.ProofEntry{
	Name: "MeasureContinuousIncreasing",
	Key:  "prop_7b97a7fcb326dc0e",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Binders: "∀a:(num → set(A)).",
		Hypotheses: []string{
			"∀n:num. a(n) ∈ S",
			"∀n:num. a(n) ⊆ a(n + 1)",
		},
		Conclusion: "μ(⋃image(a, 𝕌)) = extended_sup(image(λn:num. μ(a(n)), 𝕌))",
		Abbrev: Abbrev{
			{Name: "ring", Text: "λn:num. a(n + 1) ∖ a(n)"},
			{Name: "rings", Text: "⋃image(«ring», 𝕌)"},
			{Name: "ringSum", Text: "extended_series(λk:num. μ(«ring»(k)))"},
			{Name: "sup", Text: "extended_sup(image(λn:num. μ(a(n)), 𝕌))"},
		},
	}), func(arg *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], measure Fact,
		a *Arrow[Nat, Set[A]], measurable, increasing Fact) {
		laws := arg.Conjuncts(
			arg.Unfolded(measure, MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigma, countable := laws[0], laws[2]
		closure := arg.Unfolded(sigma, sigma_algebra.SigmaAlgebraOnDef)
		operations := sigma_algebra.SigmaFiniteOperations.At(Ω, S)
		union := arg.TermAs[Set[A]]("⋃image(a, 𝕌)")
		rings := arg.TermAs[Set[A]]("«rings»")
		first := arg.TermAs[ExtendedNonnegReal]("μ(a(0))")
		ringSum := arg.TermAs[ExtendedNonnegReal]("«ringSum»")
		sup := arg.TermAs[ExtendedNonnegReal]("«sup»")
		measures := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. μ(a(n))")
		ringMeasures := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λk:num. μ(«ring»(k))")
		zero := arg.TermAs[Nat]("0")
		inside := arg.Have(
			"each a(n) lies in the union",
			"∀n:num. a(n) ⊆ ⋃image(a, 𝕌)",
			BySets())
		within := arg.Have(
			"so each a(n) measures at most the union, a measurable set",
			"∀n:num. μ(a(n)) ≤ μ(⋃image(a, 𝕌))",
			arg.ForEach(func(n *Expr[Nat]) Action {
				return By(
					MeasureMono.At(Ω, S, μ, a.Apply(n), union),
					measure,
					measurable.At(n),
					closure,
					measurable,
					inside.At(n))
			}))
		below := arg.Have(
			"and so does their supremum",
			"«sup» ≤ μ(⋃image(a, 𝕌))",
			By(within, extended_nonneg_real.SupSequenceLeast.At(measures, μ.Apply(union))))
		measurableRing := arg.Have(
			"each ring a(n + 1) ∖ a(n) is measurable",
			"∀n:num. «ring»(n) ∈ S",
			Derive(func(d *Argument) {
				n := d.FixAs[Nat]("n")
				d.Show(
					"a difference of measurable sets is measurable",
					By(sigma, operations, measurable.At(d.TermAs[Nat]("n + 1")), measurable.At(n)))
			}))
		step := arg.Have(
			"a(n) lies in a(n + 1), so it cuts off the ring at n",
			"∀n:num. μ(a(n + 1)) = μ(a(n)) + μ(«ring»(n))",
			Derive(func(d *Argument) {
				n := d.FixAs[Nat]("n")
				next := d.TermAs[Nat]("n + 1")
				d.Show(
					"the ring at n is the rest of a(n + 1)",
					By(
						MeasureAddDiff.At(Ω, S, μ, a.Apply(n), a.Apply(next)),
						measure,
						measurable.At(n),
						measurable.At(next),
						increasing.At(n)))
			}))
		telescope := arg.Have(
			"so μ(a(0)) and the measures of the first n + 1 rings add up to μ(a(n + 1))",
			"∀n:num. Σ_{k∈0 .. n} μ(«ring»(k)) + μ(a(0)) = μ(a(n + 1))",
			Derive(func(d *Argument) {
				d.Induct("n")
				d.Base(
					"the first ring and a(0) make up a(1)",
					By(
						step.At(zero),
						extended_nonneg_real.SumSegmentZero,
						extended_nonneg_real.AddComm.At(d.TermAs[ExtendedNonnegReal]("μ(«ring»(0))"), first)))
				d.Step(
					"one more ring takes a(n + 1) to a(n + 2)",
					func(e *Argument, ih Fact) {
						e.Do(Simp(Fwd(nat_arith.Add1)))
						sum := e.TermAs[ExtendedNonnegReal]("Σ_{k∈0 .. n} μ(«ring»(k))")
						newRing := e.TermAs[ExtendedNonnegReal]("μ(«ring»(n + 1))")
						e.Show(
							"the sum up to n + 1 is the sum up to n and the ring at n + 1",
							By(
								ih,
								step.At(e.TermAs[Nat]("n + 1")),
								extended_nonneg_real.SumSegmentPeel.At(ringMeasures, e.TermAs[Nat]("n")),
								extended_nonneg_real.AddAssoc.At(sum, newRing, first),
								extended_nonneg_real.AddComm.At(newRing, first),
								extended_nonneg_real.AddAssoc.At(sum, first, newRing)))
					})
			}))
		growing := arg.Have(
			"the sequence increases between any two indices",
			"∀m n:num. m ≤ n ⇒ a(m) ⊆ a(n)",
			Derive(func(d *Argument) {
				m := d.FixAs[Nat]("m")
				n := d.FixAs[Nat]("n")
				ordered := d.Assume()
				d.Show(
					"chain the steps from m to n",
					By(increasing, ordered, At(order.IncreasingFromSteps, a, m, n)))
			}))
		disjoint := arg.Have(
			"distinct rings are disjoint",
			"∀i j:num. i ≠ j ⇒ «ring»(i) ∩ «ring»(j) = ∅",
			Derive(func(d *Argument) {
				i := d.FixAs[Nat]("i")
				j := d.FixAs[Nat]("j")
				distinct := d.Assume()
				apart := d.Have(
					"one index lies past the other",
					"i + 1 ≤ j ∨ j + 1 ≤ i",
					ByArith(distinct))
				d.Show(
					"the earlier ring lies in the set the later one leaves out",
					BySets(apart, growing.At(d.TermAs[Nat]("i + 1"), j), growing.At(d.TermAs[Nat]("j + 1"), i)))
			}))
		ringsMeasure := arg.Have(
			"countable additivity gives the measure of the union of the rings",
			"μ(«rings») = «ringSum»",
			By(countable.At(arg.TermAs[Fun[Nat, Set[A]]]("«ring»")), measurableRing, disjoint))
		cover := arg.Have(
			"every a(n) lies in a(0) together with the rings",
			"∀n:num. a(n) ⊆ a(0) ∪ «rings»",
			Derive(func(d *Argument) {
				d.Induct("n")
				d.Base(
					"a(0) lies there",
					BySets())
				d.Step(
					"a(n + 1) lies in a(n) together with the ring at n",
					func(e *Argument, ih Fact) {
						e.Do(Simp(Fwd(nat_arith.Add1)))
						e.Show(
							"so it lies there too",
							BySets(ih))
					})
			}))
		fromFirst := arg.Have(
			"a(0) lies in every a(k)",
			"∀k:num. a(0) ⊆ a(k)",
			arg.ForEach(func(k *Expr[Nat]) Action {
				return By(growing.At(zero, k), nat_order.ZeroLessEq.At(k))
			}))
		parts := arg.Have(
			"the union is a(0) together with the rings, which miss a(0)",
			"⋃image(a, 𝕌) = a(0) ∪ «rings» ∧ a(0) ∩ «rings» = ∅",
			BySets(cover, fromFirst))
		total := arg.Have(
			"so the measure of the union is μ(a(0)) plus the series of the rings' measures",
			"μ(⋃image(a, 𝕌)) = μ(a(0)) + «ringSum»",
			By(
				MeasureAdditive.At(Ω, S, μ, a.Apply(zero), rings),
				measure,
				measurable.At(zero),
				closure,
				measurableRing,
				parts,
				ringsMeasure))
		partial := arg.Have(
			"μ(a(0)) plus that series is at most the supremum, "+
				"each partial sum plus μ(a(0)) being some μ(a(n + 1))",
			"μ(a(0)) + «ringSum» ≤ «sup»",
			By(
				telescope,
				extended_nonneg_real.SeriesAddLe.At(ringMeasures, first, sup),
				extended_nonneg_real.SupSequenceUpper,
				extended_nonneg_real.AddComm.At(first, ringSum)))
		arg.Show(
			"the two bounds meet",
			By(total, partial, below, extended_nonneg_real.LeAntisym.At(μ.Apply(union), sup)))
	}),
})}

// MeasureFromContinuousIncreasing — a set function on a σ-algebra that
// vanishes on ∅, adds over two disjoint measurable sets and is continuous
// along increasing sequences is a measure. By induction the partial unions
// of a disjoint sequence are measurable with the partial sums as their
// masses; they increase to the union, so its mass is the supremum of the
// partial sums, which is the series.
var MeasureFromContinuousIncreasing = measureFromContinuousIncreasingThm{family.Add(registry.ProofEntry{
	Name: "MeasureFromContinuousIncreasing",
	Key:  "prop_da875af668934066",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"μ(∅) = &0",
			"∀E F:set(A). E ∈ S ∧ F ∈ S ∧ E ∩ F = ∅ ⇒ μ(E ∪ F) = μ(E) + μ(F)",
			"∀a:(num → set(A)). " +
				"    (∀n:num. a(n) ∈ S) ∧ (∀n:num. a(n) ⊆ a(n + 1)) ⇒ " +
				"    μ(⋃image(a, 𝕌)) = extended_sup(image(λn:num. μ(a(n)), 𝕌))",
		},
		Conclusion: "measure_on(Ω, S, μ)",
		Abbrev: Abbrev{
			{Name: "prefix", Text: "λn:num. ⋃image(a, 0 .. n)"},
			{Name: "masses", Text: "λn:num. μ(a(n))"},
			{Name: "prefixMass", Text: "λn:num. μ(«prefix»(n))"},
			{Name: "partialMass", Text: "λn:num. Σ_{i∈0 .. n} «masses»(i)"},
		},
	}, func(
		arg *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		sigma, empty, additive, continuous Fact,
	) {
		countable := arg.Have(
			"the mass of a disjoint countable union is the series of the masses",
			Statement{
				Binders: "∀a:(num → set(A)).",
				Hypotheses: []string{
					"∀n:num. a(n) ∈ S",
					"∀i j:num. i ≠ j ⇒ a(i) ∩ a(j) = ∅",
				},
				Conclusion: "μ(⋃image(a, 𝕌)) = extended_series(λn:num. μ(a(n)))",
			},
			Derive(func(c *Argument) {
				c.FixAs[Fun[Nat, Set[A]]]("a")
				guards := c.Conjuncts(
					c.Assume(),
					"each event is measurable",
					"the events are pairwise disjoint")
				events, disjoint := guards[0], guards[1]
				masses := c.TermAs[Fun[Nat, ExtendedNonnegReal]]("«masses»")
				partials := c.Have(
					"the partial unions are measurable and have the partial sums as their masses",
					"∀n:num. «prefix»(n) ∈ S ∧ «prefixMass»(n) = «partialMass»(n)",
					Derive(func(d *Argument) {
						d.Induct("n")
						d.Base(
							"the partial union at zero is the first event",
							func(e *Argument) {
								zero := e.TermAs[Nat]("0")
								first := e.Have(
									"the segment contains only zero",
									"«prefix»(0) = a(0)",
									BySets(num_segment.Sing.At(zero)))
								e.Show(
									"the first event is measurable and contributes its own mass",
									By(Normalized, events.At(zero), first, extended_nonneg_real.SumSegmentZero.At(masses)))
							})
						d.Step(
							"adjoin the next event to the preceding union",
							func(e *Argument, previous Fact) {
								n := e.TermAs[Nat]("n")
								next := e.TermAs[Nat]("suc(n)")
								union := e.Have(
									"the next partial union adjoins the next event",
									"«prefix»(suc(n)) = «prefix»(n) ∪ a(suc(n))",
									BySets(num_segment.Rec.At(e.TermAs[Nat]("0"), n), nat_order.ZeroLessEq.At(next)))
								separate := e.Have(
									"the next event is disjoint from each earlier event",
									"∀i:num. i ∈ 0 .. n ⇒ a(i) ∩ a(suc(n)) = ∅",
									Derive(func(f *Argument) {
										i := f.FixAs[Nat]("i")
										in := f.Assume()
										distinct := f.Have(
											"every earlier index differs from the successor",
											"i ≠ suc(n)",
											ByArith(in, num_segment.MembershipFromZero.At(i, n), nat_arith.Add1.At(n)))
										f.Show(
											"use pairwise disjointness",
											By(disjoint.At(i, next), distinct))
									}))
								apart := e.Have(
									"the next event is disjoint from the preceding union",
									"«prefix»(n) ∩ a(suc(n)) = ∅",
									BySets(separate))
								sum := e.Have(
									"the masses add over the two disjoint events",
									"μ(«prefix»(n) ∪ a(suc(n))) = «prefixMass»(n) + «masses»(suc(n))",
									By(
										previous,
										events.At(next),
										apart,
										additive.At(e.TermAs[Set[A]]("«prefix»(n)"), e.TermAs[Set[A]]("a(suc(n))"))))
								e.Show(
									"the new union is measurable and has the next partial sum",
									SplitConj(
										Case(
											"measurable sets have measurable union",
											By(union, sigma, previous, events.At(next), sigma_algebra.SigmaFiniteOperations.At(Ω, S))),
										Case(
											"peel the last term from the partial sum",
											By(sum, union, previous, extended_nonneg_real.SumSegmentPeel.At(masses, n), nat_arith.Add1.At(n)))))
							})
					}))
				exhaustion := c.Have(
					"the partial unions exhaust the full union",
					"⋃image(«prefix», 𝕌) = ⋃image(a, 𝕌)",
					BySets(nat_order.ZeroLessEq, nat_order.LessEqRefl))
				rising := c.Have(
					"the partial unions increase",
					"∀n:num. «prefix»(n) ⊆ «prefix»(n + 1)",
					BySets(nat_order.LessEqAdd, nat_order.LessEqTrans))
				supremum := c.Have(
					"continuity from below gives the full union the supremum of the partial union masses",
					"μ(⋃image(«prefix», 𝕌)) = extended_sup(image(«prefixMass», 𝕌))",
					By(partials, rising, continuous.At(c.TermAs[Fun[Nat, Set[A]]]("«prefix»"))))
				sums := c.Have(
					"the sequence of partial union masses is the sequence of partial sums",
					"«prefixMass» = «partialMass»",
					Funext(),
					By(partials))
				c.Show(
					"the supremum of the partial sums is the series",
					Simp(Fwd(extended_nonneg_real.ExtendedSeriesDef)),
					sums.RwRev(),
					By(exhaustion, supremum))
			}))
		arg.Show(
			"the σ-algebra, the empty set and countable additivity are the measure laws",
			By(sigma, empty, countable, MeasureOn.At(Ω, S, μ)))
	}),
})}

// MeasureContinuousDecreasing — along a decreasing sequence of measurable
// sets, the first of finite measure, the measure of the intersection is the
// infimum of the measures. The intersection lies in every b(n), so its
// measure is at most the infimum. For the other bound, the differences
// b(0) ∖ b(n) increase to the rest of b(0) outside the intersection, so
// the measure of the rest is the supremum of theirs. b(n) and the
// intersection lie in b(0), so μ(b(0)) is μ(b(n)) + μ(b(0) ∖ b(n)), and it
// is the measure of the intersection plus that of the rest. The infimum
// plus each μ(b(0) ∖ b(n)) is at most μ(b(0)), so the infimum plus their
// supremum is, and the finite measure of the rest cancels.
var MeasureContinuousDecreasing = measureContinuousDecreasingThm{family.Add(registry.ProofEntry{
	Name: "MeasureContinuousDecreasing",
	Key:  "prop_827002811f30748f",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Binders: "∀b:(num → set(A)).",
		Hypotheses: []string{
			"∀n:num. b(n) ∈ S",
			"∀n:num. b(n + 1) ⊆ b(n)",
			"μ(b(0)) ≠ extended_infinity",
		},
		Conclusion: "μ(⋂image(b, 𝕌)) = extended_inf(image(λn:num. μ(b(n)), 𝕌))",
		Abbrev: Abbrev{
			{Name: "inf", Text: "extended_inf(image(λn:num. μ(b(n)), 𝕌))"},
			{Name: "outside", Text: "λn:num. b(0) ∖ b(n)"},
			{Name: "outsideMeasures", Text: "image(λn:num. μ(«outside»(n)), 𝕌)"},
		},
	}), func(arg *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], measure Fact,
		b *Arrow[Nat, Set[A]], measurable, decreasing, finite Fact) {
		laws := arg.Conjuncts(
			arg.Unfolded(measure, MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigma := laws[0]
		closure := arg.Unfolded(sigma, sigma_algebra.SigmaAlgebraOnDef)
		operations := sigma_algebra.SigmaFiniteOperations.At(Ω, S)
		zero := arg.TermAs[Nat]("0")
		first := b.Apply(zero)
		meet := arg.TermAs[Set[A]]("⋂image(b, 𝕌)")
		rest := arg.TermAs[Set[A]]("b(0) ∖ ⋂image(b, 𝕌)")
		outside := arg.TermAs[Fun[Nat, Set[A]]]("«outside»")
		inf := arg.TermAs[ExtendedNonnegReal]("«inf»")
		measures := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. μ(b(n))")
		inside := arg.Have(
			"the intersection lies in every b(n)",
			"∀n:num. ⋂image(b, 𝕌) ⊆ b(n)",
			BySets())
		chain := arg.Have(
			"every b(n) lies in b(0), the sequence decreasing",
			"∀n:num. b(n) ⊆ b(0)",
			arg.ForEach(func(n *Expr[Nat]) Action {
				return By(decreasing, nat_order.ZeroLessEq.At(n), At(order.DecreasingFromSteps, b, zero, n))
			}))
		measurableOutside := arg.Have(
			"each b(0) ∖ b(n) is measurable",
			"∀n:num. «outside»(n) ∈ S",
			arg.ForEach(func(n *Expr[Nat]) Action {
				return By(sigma, operations, measurable.At(zero), measurable.At(n))
			}))
		growing := arg.Have(
			"and they increase with n",
			"∀n:num. «outside»(n) ⊆ «outside»(n + 1)",
			BySets(decreasing))
		union := arg.Have(
			"their union is what the intersection leaves of b(0)",
			"⋃image(«outside», 𝕌) = b(0) ∖ ⋂image(b, 𝕌)",
			BySets())
		limit := arg.Have(
			"so the measure of the rest is the supremum of their measures",
			"μ(b(0) ∖ ⋂image(b, 𝕌)) = extended_sup(«outsideMeasures»)",
			By(union, MeasureContinuousIncreasing.At(Ω, S, μ, outside), measure, measurableOutside, growing))
		measurableMeet := arg.Have(
			"the intersection is measurable",
			"⋂image(b, 𝕌) ∈ S",
			Derive(func(d *Argument) {
				complement := d.Have(
					"it is what the union of the differences leaves of b(0)",
					"⋂image(b, 𝕌) = b(0) ∖ ⋃image(«outside», 𝕌)",
					BySets())
				d.Show(
					"a countable union of measurable sets is measurable, and so is a difference",
					By(complement, closure, measurableOutside, sigma, operations, measurable.At(zero)))
			}))
		splitN := arg.Have(
			"b(n) lies in b(0), so it cuts off b(0) ∖ b(n)",
			"∀n:num. μ(b(0)) = μ(b(n)) + μ(«outside»(n))",
			arg.ForEach(func(n *Expr[Nat]) Action {
				return By(
					MeasureAddDiff.At(Ω, S, μ, b.Apply(n), first),
					measure,
					measurable.At(n),
					measurable.At(zero),
					chain.At(n))
			}))
		splitMeet := arg.Have(
			"and the intersection, lying in b(0), cuts off the rest",
			"μ(b(0)) = μ(⋂image(b, 𝕌)) + μ(b(0) ∖ ⋂image(b, 𝕌))",
			By(
				MeasureAddDiff.At(Ω, S, μ, meet, first),
				measure,
				measurableMeet,
				measurable.At(zero),
				inside.At(zero)))
		lower := arg.Have(
			"so the intersection measures at most every μ(b(n))",
			"∀n:num. μ(⋂image(b, 𝕌)) ≤ μ(b(n))",
			arg.ForEach(func(n *Expr[Nat]) Action {
				return By(
					MeasureMono.At(Ω, S, μ, meet, b.Apply(n)),
					measure,
					measurableMeet,
					measurable.At(n),
					inside.At(n))
			}))
		below := arg.Have(
			"and so at most their infimum",
			"μ(⋂image(b, 𝕌)) ≤ «inf»",
			By(lower, extended_nonneg_real.InfSequenceGreatest.At(measures, μ.Apply(meet))))
		each := arg.Have(
			"each μ(b(0) ∖ b(n)) plus the infimum is at most μ(b(0) ∖ b(n)) + μ(b(n)) = μ(b(0))",
			"∀n:num. μ(«outside»(n)) + «inf» ≤ μ(b(0))",
			Derive(func(d *Argument) {
				n := d.FixAs[Nat]("n")
				measureN := μ.Apply(b.Apply(n))
				outsideMeasure := d.TermAs[ExtendedNonnegReal]("μ(«outside»(n))")
				infimum := d.Have(
					"the infimum is at most μ(b(n)), one of the measures",
					"«inf» ≤ μ(b(n))",
					By(set_image.FunInRange.At(measures, n), extended_nonneg_real.InfLower))
				d.Show(
					"so μ(b(0) ∖ b(n)) plus the infimum is at most μ(b(0))",
					By(
						infimum,
						splitN.At(n),
						extended_nonneg_real.AddLeAdd.At(outsideMeasure, inf, outsideMeasure, measureN),
						extended_nonneg_real.LeRefl.At(outsideMeasure),
						extended_nonneg_real.AddComm.At(outsideMeasure, measureN)))
			}))
		eachValue := arg.Have(
			"that is, every measure x of some b(0) ∖ b(n) has x plus the infimum at most μ(b(0))",
			"∀x:extended_nonneg_real. x ∈ «outsideMeasures» ⇒ x + «inf» ≤ μ(b(0))",
			By(each, set_basic.InImage))
		nonempty := arg.Have(
			"the measures of the b(0) ∖ b(n) form a nonempty set",
			"«outsideMeasures» ≠ ∅",
			BySets())
		sum := arg.Have(
			"so the measure of the rest plus the infimum is at most μ(b(0))",
			"μ(b(0) ∖ ⋂image(b, 𝕌)) + «inf» ≤ μ(b(0))",
			Derive(func(d *Argument) {
				d.Do(limit.Rw())
				d.Show(
					"a supremum plus the infimum lies below every bound of its members plus the infimum",
					By(
						nonempty,
						eachValue,
						extended_nonneg_real.SupAddLe.At(
							d.TermAs[Set[ExtendedNonnegReal]]("«outsideMeasures»"),
							inf,
							μ.Apply(first))))
			}))
		finiteRest := arg.Have(
			"the rest has finite measure, a part of the finite μ(b(0))",
			"μ(b(0) ∖ ⋂image(b, 𝕌)) ≠ extended_infinity",
			By(splitMeet, finite, extended_nonneg_real.AddEqInfinity))
		above := arg.Have(
			"so the infimum is at most the measure of the "+
				"intersection, the finite measure of the rest cancelling",
			"«inf» ≤ μ(⋂image(b, 𝕌))",
			By(
				sum,
				splitMeet,
				finiteRest,
				extended_nonneg_real.AddComm.At(μ.Apply(rest), inf),
				extended_nonneg_real.AddLeCancel.At(inf, μ.Apply(meet), μ.Apply(rest))))
		arg.Show(
			"the two bounds meet",
			By(below, above, extended_nonneg_real.LeAntisym.At(μ.Apply(meet), inf)))
	}),
})}

// MeasureCountableSubadditive — the measure of a countable union of
// measurable sets is at most the series of their measures. Cut each a(n)
// down to its part outside the earlier sets: the parts are measurable and
// disjoint, and they have the same union, a point of the union lying in
// the part at the first index whose set holds it. Countable additivity
// over the parts and monotonicity term by term give the bound.
var MeasureCountableSubadditive = measureCountableSubadditiveThm{family.Add(registry.ProofEntry{
	Name: "MeasureCountableSubadditive",
	Key:  "prop_f85aa143d5ec3fd7",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Binders:    "∀a:(num → set(A)).",
		Hypotheses: []string{"∀n:num. a(n) ∈ S"},
		Conclusion: "μ(⋃image(a, 𝕌)) ≤ extended_series(λn:num. μ(a(n)))",
		Abbrev: Abbrev{
			{Name: "earlier", Text: "λn:num. ⋃image(a, {k:num | k < n})"},
			{Name: "part", Text: "λn:num. a(n) ∖ «earlier»(n)"},
		},
	}), func(arg *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], measure Fact,
		a *Arrow[Nat, Set[A]], measurable Fact) {
		laws := arg.Conjuncts(
			arg.Unfolded(measure, MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigma, countable := laws[0], laws[2]
		operations := sigma_algebra.SigmaFiniteOperations.At(Ω, S)
		measurableEarlier := arg.Have(
			"the union of the sets before each index is measurable",
			"∀n:num. «earlier»(n) ∈ S",
			Derive(func(d *Argument) {
				d.Induct("n")
				d.Base(
					"no index lies below 0, so the union before it is empty",
					func(e *Argument) {
						empty := e.Have(
							"no set comes before index 0",
							"«earlier»(0) = ∅",
							BySets(nat_order.LessThanZeroClause))
						e.Show(
							"and the empty set is measurable",
							By(empty, sigma, operations))
					})
				d.Step(
					"the sets before suc(n) are those before n together with a(n)",
					func(e *Argument, ih Fact) {
						grown := e.Have(
							"one more set joins the union",
							"«earlier»(suc(n)) = «earlier»(n) ∪ a(n)",
							BySets(nat_order.LessThanSucClause))
						e.Show(
							"a union of two measurable sets is measurable",
							By(measurable.At(e.TermAs[Nat]("n")), grown, ih, sigma, operations))
					})
			}))
		measurablePart := arg.Have(
			"so the part of each a(n) outside the earlier sets is measurable",
			"∀n:num. «part»(n) ∈ S",
			By(measurable, measurableEarlier, sigma, operations))
		disjoint := arg.Have(
			"distinct parts are disjoint",
			"∀i j:num. i ≠ j ⇒ «part»(i) ∩ «part»(j) = ∅",
			Derive(func(d *Argument) {
				d.FixAs[Nat]("i")
				d.FixAs[Nat]("j")
				distinct := d.Assume()
				apart := d.Have(
					"one index lies below the other",
					"i < j ∨ j < i",
					ByArith(distinct))
				d.Show(
					"the later part leaves out the set the earlier part lies in",
					BySets(apart))
			}))
		least := arg.Have(
			"a point of the union lies in a first set of the sequence",
			"∀x:A. (∃n:num. x ∈ a(n)) ⇒ ∃m:num. x ∈ a(m) ∧ (∀k:num. k < m ⇒ x ∉ a(k))",
			By(nat_order.WellOrdering))
		cover := arg.Have(
			"and so in the part at that index: the parts have the same union as the sets",
			"⋃image(«part», 𝕌) = ⋃image(a, 𝕌)",
			BySets(least))
		additive := arg.Have(
			"countable additivity over the disjoint parts measures the union",
			"μ(⋃image(a, 𝕌)) = extended_series(λn:num. μ(«part»(n)))",
			By(countable.At(arg.TermAs[Fun[Nat, Set[A]]]("«part»")), measurablePart, disjoint, cover))
		termwise := arg.Have(
			"each part lies in its set, so measures at most as much",
			"∀n:num. μ(«part»(n)) ≤ μ(a(n))",
			By(measure, measurable, measurablePart, MeasureMono, set_order.SubsetDiff))
		arg.Show(
			"so the series of the parts' measures is at most that of the sets' measures",
			By(
				additive,
				termwise,
				extended_nonneg_real.SeriesMono.At(
					arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. μ(«part»(n))"),
					arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. μ(a(n))"))))
	}),
})}
