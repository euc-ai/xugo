// borel.go — the Borel sets are measurable. A half-line ⟬c, ∞⟭ cuts every
// set additively: it cuts each interval of a cover into two intervals as
// long together as the one they come from. The measurable sets form a
// σ-algebra, whose complements, countable unions and intersections then
// give every half-line and interval; the open sets are countable unions of
// open intervals, and the Borel sets are the smallest σ-algebra holding the
// open sets.

package lebesgue_measure

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/caratheodory"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/proofs/topology/borel_space"
	"github.com/euc-ai/xugo/library/registry"
)

// OuterMeasureIntervalCut — a point c cuts an open interval ⟬a, b⟭ into
// the piece right of c and the piece left of it, whose outer measures add
// up to at most b − a. When c ≤ a nothing of ⟬a, b⟭ lies left of c, and
// when b ≤ c nothing lies right of it: one piece is empty and the other
// lies in ⟬a, b⟭. Otherwise the right piece lies in ⟬c, b⟭ and the left
// one in ⟦a, c⟧, whose lengths add up to b − a.
var OuterMeasureIntervalCut = outerMeasureIntervalCutThm{family.Add(registry.ProofEntry{
	Name: "OuterMeasureIntervalCut",
	Key:  "prop_96277d4a72397752",
	Build: family.Theorem(Statement{
		Binders: "∀a b c:real.",
		Conclusion: "lebesgue_outer_measure(⟬a, b⟭ ∩ «halfLine») + " +
			"lebesgue_outer_measure(⟬a, b⟭ ∖ «halfLine») ≤ " +
			"extended_of_real(b - a)",
		Abbrev: Abbrev{
			{Name: "halfLine", Text: "{x:real | c < x}"},
		},
	}, func(arg *Argument, a, b, c *Expr[Real]) {
		right := arg.TermAs[Set[Real]]("⟬a, b⟭ ∩ «halfLine»")
		left := arg.TermAs[Set[Real]]("⟬a, b⟭ ∖ «halfLine»")
		pastA := arg.Unless(
			arg.Term("c ≤ a"),
			"when c ≤ a nothing of ⟬a, b⟭ lies left of c",
			Given(func(d *Argument, atMostA Fact) {
				beyond := d.Have(
					"every point right of a lies right of c",
					"∀x:real. a < x ⇒ c < x",
					ByArith(atMostA))
				empty := d.Have(
					"so the piece left of c is empty",
					"⟬a, b⟭ ∖ «halfLine» = ∅",
					BySets(beyond))
				inside := d.Have(
					"and the piece right of c lies in ⟬a, b⟭",
					"⟬a, b⟭ ∩ «halfLine» ⊆ ⟬a, b⟭",
					BySets())
				d.Do(empty.Rw())
				d.Show(
					"so the two measure at most b − a and 0",
					By(
						inside,
						At(OuterMeasureInsideInterval, right, a, b),
						OuterMeasureEmpty,
						extended_nonneg_real.AddZero))
			}))
		beforeB := arg.Unless(
			arg.Term("b ≤ c"),
			"when b ≤ c nothing of ⟬a, b⟭ lies right of c",
			Given(func(d *Argument, atLeastB Fact) {
				short := d.Have(
					"no point left of b lies right of c",
					"∀x:real. x < b ⇒ ¬(c < x)",
					ByArith(atLeastB))
				empty := d.Have(
					"so the piece right of c is empty",
					"⟬a, b⟭ ∩ «halfLine» = ∅",
					BySets(short))
				inside := d.Have(
					"and the piece left of c lies in ⟬a, b⟭",
					"⟬a, b⟭ ∖ «halfLine» ⊆ ⟬a, b⟭",
					BySets())
				d.Do(empty.Rw())
				d.Show(
					"so the two measure at most 0 and b − a",
					By(
						inside,
						At(OuterMeasureInsideInterval, left, a, b),
						OuterMeasureEmpty,
						extended_nonneg_real.AddComm.At(
							d.TermAs[extended_nonneg_real.ExtendedNonnegReal]("lebesgue_outer_measure(∅)"),
							d.TermAs[extended_nonneg_real.ExtendedNonnegReal]("lebesgue_outer_measure(⟬a, b⟭ ∖ «halfLine»)")),
						extended_nonneg_real.AddZero))
			}))
		ends := arg.Have(
			"otherwise a < c < b: the lengths b − c and c − a are nonnegative and add up to b − a",
			"a ≤ c ∧ &0 ≤ b - c ∧ &0 ≤ c - a ∧ (b - c) + (c - a) = b - a",
			ByArith(pastA, beforeB))
		rightInside := arg.Have(
			"the piece right of c lies in ⟬c, b⟭",
			"⟬a, b⟭ ∩ «halfLine» ⊆ ⟬c, b⟭",
			BySets())
		rightMeasure := arg.Have(
			"so it measures at most b − c",
			"lebesgue_outer_measure(⟬a, b⟭ ∩ «halfLine») ≤ extended_of_real(b - c)",
			By(rightInside, At(OuterMeasureInsideInterval, right, c, b)))
		leftPoints := arg.Have(
			"a point right of a and not right of c lies in ⟦a, c⟧",
			"∀x:real. a < x ∧ ¬(c < x) ⇒ a ≤ x ∧ x ≤ c",
			ByArith())
		leftInside := arg.Have(
			"so the piece left of c lies in ⟦a, c⟧",
			"⟬a, b⟭ ∖ «halfLine» ⊆ ⟦a, c⟧",
			BySets(leftPoints))
		leftMeasure := arg.Have(
			"and measures at most the length c − a of ⟦a, c⟧",
			"lebesgue_outer_measure(⟬a, b⟭ ∖ «halfLine») ≤ extended_of_real(c - a)",
			By(
				ends,
				leftInside,
				OuterMeasureMono.At(left, arg.TermAs[Set[Real]]("⟦a, c⟧")),
				At(OuterMeasureClosedInterval, a, c)))
		arg.Show(
			"so the two measure at most (b − c) + (c − a) = b − a",
			By(
				rightMeasure,
				leftMeasure,
				ends,
				extended_nonneg_real.OfRealAdd.At(arg.TermAs[Real]("b - c"), arg.TermAs[Real]("c - a")),
				extended_nonneg_real.AddLeAdd.At(
					arg.TermAs[extended_nonneg_real.ExtendedNonnegReal]("lebesgue_outer_measure(⟬a, b⟭ ∩ «halfLine»)"),
					arg.TermAs[extended_nonneg_real.ExtendedNonnegReal]("lebesgue_outer_measure(⟬a, b⟭ ∖ «halfLine»)"),
					arg.TermAs[extended_nonneg_real.ExtendedNonnegReal]("extended_of_real(b - c)"),
					arg.TermAs[extended_nonneg_real.ExtendedNonnegReal]("extended_of_real(c - a)"))))
	}),
})}

// OuterMeasureHalfLineCut — the half-line ⟬c, ∞⟭ cuts a set t covered by
// the intervals ⟬a(n), b(n)⟭ into two pieces whose outer measures add up
// to at most the total length of the cover. The pieces of the intervals
// right of c cover the piece of t right of c, and the pieces left of c
// the piece left of c; by countable subadditivity each piece of t
// measures at most the sum of the measures of its covering pieces, and
// the two pieces of one interval measure at most its length together.
var OuterMeasureHalfLineCut = outerMeasureHalfLineCutThm{family.Add(registry.ProofEntry{
	Name: "OuterMeasureHalfLineCut",
	Key:  "prop_b0a7b56be225fc8a",
	Build: family.Theorem(Statement{
		Binders:    "∀a b:(num → real). ∀c:real. ∀t:set(real).",
		Hypotheses: []string{"∀x:real. x ∈ t ⇒ ∃n:num. a(n) < x ∧ x < b(n)"},
		Conclusion: "lebesgue_outer_measure(t ∩ «halfLine») + lebesgue_outer_measure(t ∖ «halfLine») ≤ " +
			"extended_series(λn:num. extended_of_real(b(n) - a(n)))",
		Abbrev: Abbrev{
			{Name: "halfLine", Text: "{x:real | c < x}"},
			{Name: "right", Text: "λn:num. ⟬a(n), b(n)⟭ ∩ «halfLine»"},
			{Name: "left", Text: "λn:num. ⟬a(n), b(n)⟭ ∖ «halfLine»"},
			{Name: "rightSum", Text: "extended_series(λn:num. lebesgue_outer_measure(«right»(n)))"},
			{Name: "leftSum", Text: "extended_series(λn:num. lebesgue_outer_measure(«left»(n)))"},
		},
	}, func(arg *Argument, a, b *Arrow[Nat, Real], c *Expr[Real], t *Expr[Set[Real]], covered Fact) {
		rightCover := arg.Have(
			"the pieces of the intervals right of c cover the piece of t right of c",
			"t ∩ «halfLine» ⊆ {x:real | ∃n:num. x ∈ «right»(n)}",
			BySets(covered))
		leftCover := arg.Have(
			"and their pieces left of c cover the piece of t left of c",
			"t ∖ «halfLine» ⊆ {x:real | ∃n:num. x ∈ «left»(n)}",
			BySets(covered))
		rightMeasure := arg.Have(
			"so by countable subadditivity the piece of t right "+
				"of c measures at most the sum over the right pieces",
			"lebesgue_outer_measure(t ∩ «halfLine») ≤ «rightSum»",
			By(
				rightCover,
				OuterMeasureMono.At(
					arg.TermAs[Set[Real]]("t ∩ «halfLine»"),
					arg.TermAs[Set[Real]]("{x:real | ∃n:num. x ∈ «right»(n)}")),
				At(OuterMeasureCountableSubadditive, arg.TermAs[Fun[Nat, Set[Real]]]("«right»")),
				Where(
					extended_nonneg_real.LeTrans,
					"y",
					arg.TermAs[extended_nonneg_real.ExtendedNonnegReal](
						"lebesgue_outer_measure({x:real | ∃n:num. x ∈ «right»(n)})"))))
		leftMeasure := arg.Have(
			"and the piece left of c at most the sum over the left pieces",
			"lebesgue_outer_measure(t ∖ «halfLine») ≤ «leftSum»",
			By(
				leftCover,
				OuterMeasureMono.At(
					arg.TermAs[Set[Real]]("t ∖ «halfLine»"),
					arg.TermAs[Set[Real]]("{x:real | ∃n:num. x ∈ «left»(n)}")),
				At(OuterMeasureCountableSubadditive, arg.TermAs[Fun[Nat, Set[Real]]]("«left»")),
				Where(
					extended_nonneg_real.LeTrans,
					"y",
					arg.TermAs[extended_nonneg_real.ExtendedNonnegReal](
						"lebesgue_outer_measure({x:real | ∃n:num. x ∈ «left»(n)})"))))
		pieces := arg.Have(
			"the two pieces of each interval measure at most its length together",
			"∀n:num. "+
				"    lebesgue_outer_measure(«right»(n)) + lebesgue_outer_measure(«left»(n)) ≤ "+
				"    extended_of_real(b(n) - a(n))",
			By(OuterMeasureIntervalCut))
		sums := arg.Have(
			"so the two sums, added interval by interval, are at most the total length",
			"«rightSum» + «leftSum» ≤ extended_series(λn:num. extended_of_real(b(n) - a(n)))",
			By(
				pieces,
				extended_nonneg_real.SeriesAdd.At(
					arg.TermAs[Fun[Nat, extended_nonneg_real.ExtendedNonnegReal]](
						"λn:num. lebesgue_outer_measure(«right»(n))"),
					arg.TermAs[Fun[Nat, extended_nonneg_real.ExtendedNonnegReal]](
						"λn:num. lebesgue_outer_measure(«left»(n))")),
				extended_nonneg_real.SeriesMono.At(
					arg.TermAs[Fun[Nat, extended_nonneg_real.ExtendedNonnegReal]](
						"λn:num. lebesgue_outer_measure(«right»(n)) + lebesgue_outer_measure(«left»(n))"),
					arg.TermAs[Fun[Nat, extended_nonneg_real.ExtendedNonnegReal]](
						"λn:num. extended_of_real(b(n) - a(n))"))))
		arg.Show(
			"and the two pieces of t measure at most the two sums",
			By(
				rightMeasure,
				leftMeasure,
				sums,
				extended_nonneg_real.AddLeAdd.At(
					arg.TermAs[extended_nonneg_real.ExtendedNonnegReal]("lebesgue_outer_measure(t ∩ «halfLine»)"),
					arg.TermAs[extended_nonneg_real.ExtendedNonnegReal]("lebesgue_outer_measure(t ∖ «halfLine»)"),
					arg.TermAs[extended_nonneg_real.ExtendedNonnegReal]("«rightSum»"),
					arg.TermAs[extended_nonneg_real.ExtendedNonnegReal]("«leftSum»")),
				Where(
					extended_nonneg_real.LeTrans,
					"y",
					arg.TermAs[extended_nonneg_real.ExtendedNonnegReal]("«rightSum» + «leftSum»"))))
	}),
})}

// MeasurableHalfLine — the half-line ⟬c, ∞⟭ is measurable: it cuts every
// set t into two pieces of total outer measure at most λ*(t). When λ*(t)
// is ∞ there is nothing to prove. Otherwise, for every e > 0, t has a
// cover by intervals of total length at most λ*(t) + e, and the half-line
// cuts t into pieces of total at most that length; a bound by λ*(t) + e
// for every e > 0 is a bound by λ*(t).
var MeasurableHalfLine = measurableHalfLineThm{family.Add(registry.ProofEntry{
	Name: "MeasurableHalfLine",
	Key:  "prop_4f2f050832dabcc8",
	Build: family.Theorem(Statement{
		Binders:    "∀c:real.",
		Conclusion: "lebesgue_measurable({x:real | c < x})",
		Abbrev: Abbrev{
			{Name: "halfLine", Text: "{x:real | c < x}"},
		},
	}, func(arg *Argument, c *Expr[Real]) {
		splits := arg.Have(
			"the half-line cuts every set t into two pieces of total outer measure at most λ*(t)",
			"∀t:set(real). "+
				"    lebesgue_outer_measure(t ∩ «halfLine») + lebesgue_outer_measure(t ∖ «halfLine») ≤ "+
				"    lebesgue_outer_measure(t)",
			Derive(func(d *Argument) {
				t := d.FixAs[Set[Real]]("t")
				finite := d.Unless(
					d.Term("lebesgue_outer_measure(t) = extended_infinity"),
					"everything lies below ∞",
					Given(func(top *Argument, infinite Fact) {
						top.Show(
							"the two pieces measure at most ∞",
							By(infinite, extended_nonneg_real.LeInfinity))
					}))
				near := d.Have(
					"for every e > 0 the two pieces measure at most λ*(t) + e",
					Statement{
						Binders:    "∀e:real.",
						Hypotheses: []string{"&0 < e"},
						Conclusion: "lebesgue_outer_measure(t ∩ «halfLine») + lebesgue_outer_measure(t ∖ «halfLine») ≤ " +
							"lebesgue_outer_measure(t) + extended_of_real(e)",
					},
					Derive(func(ep *Argument) {
						e := ep.FixAs[Real]()
						positive := ep.Assume()
						a, b, cover := ep.Obtain2As[Fun[Nat, Real], Fun[Nat, Real]](
							"t has a cover by intervals of total length at most λ*(t) + e",
							"∃a b:(num → real). "+
								"    (∀x:real. x ∈ t ⇒ ∃n:num. a(n) < x ∧ x < b(n)) ∧ "+
								"    extended_series(λn:num. extended_of_real(b(n) - a(n))) ≤ "+
								"    lebesgue_outer_measure(t) + extended_of_real(e)",
							By(finite, positive, OuterMeasureCoverApprox.At(t, e)))
						ep.Show(
							"and the half-line cuts t into pieces of total at most the cover's length",
							By(
								cover,
								At(OuterMeasureHalfLineCut, a, b, c, t),
								Where(
									extended_nonneg_real.LeTrans,
									"y",
									ep.TermAs[extended_nonneg_real.ExtendedNonnegReal](
										"extended_series(λn:num. extended_of_real(b(n) - a(n)))"))))
					}))
				d.Show(
					"so they measure at most λ*(t)",
					By(near, extended_nonneg_real.LeOfLeAddPositive))
			}))
		halfLine := arg.TermAs[Set[Real]]("«halfLine»")
		arg.Show(
			"so by Carathéodory's one-inequality criterion, read on the line, the half-line is measurable",
			By(
				splits,
				caratheodory.MeasurableIffLe.Read(LebesgueOuterMeasureOn).At(halfLine),
				set_order.SubsetUniv,
				MeasurableIffCaratheodory.At(halfLine)))
	}),
})}

// MeasurableAtMost — the closed half-line ⟬−∞, c⟧ is measurable: it is
// the complement of ⟬c, ∞⟭.
var MeasurableAtMost = measurableAtMostThm{family.Add(registry.ProofEntry{
	Name: "MeasurableAtMost",
	Key:  "prop_fef19d35ccb5262b",
	Build: family.Theorem("∀c:real. lebesgue_measurable({x:real | x ≤ c})", func(
		arg *Argument,
		c *Expr[Real],
	) {
		complement := arg.Have(
			"the points at most c are those not right of c",
			"{x:real | x ≤ c} = 𝕌 ∖ {x:real | c < x}",
			BySets(real_order_ring.NotLessThan))
		arg.Do(complement.Rw())
		arg.Show(
			"the measurable sets form a σ-algebra on the line, "+
				"closed under complements, and ⟬c, ∞⟭ is one of them",
			By(arg.Unfolded(LebesgueSigmaAlgebra, sigma_algebra.SigmaAlgebraOnDef), At(MeasurableHalfLine, c)))
	}),
})}

// MeasurableBelow — the open half-line ⟬−∞, c⟭ is measurable: it is the
// union of the closed half-lines ⟬−∞, c − 1/(n + 1)⟧. Each of them lies
// below c, 1/(n + 1) being positive, and a point x below c lies in the
// one where n·(c − x) exceeds 1, which some n does by Archimedes.
var MeasurableBelow = measurableBelowThm{family.Add(registry.ProofEntry{
	Name: "MeasurableBelow",
	Key:  "prop_195311da8f958869",
	Build: family.Theorem("∀c:real. lebesgue_measurable({x:real | x < c})", func(
		arg *Argument,
		c *Expr[Real],
	) {
		pointwise := arg.Have(
			"a point lies below c exactly when it lies at most c − 1/(n + 1) for some n",
			"∀x:real. x < c ⇔ ∃n:num. x ≤ c - &1 / (&n + &1)",
			Derive(func(d *Argument) {
				d.FixAs[Real]("x")
				d.Iff()
				d.Forward(
					"below c, x is at most c − 1/(n + 1) once n·(c − x) exceeds 1",
					func(fw *Argument, below Fact) {
						n, large := fw.ObtainAs[Nat](
							"by Archimedes some n has n·(c − x) above 1",
							"∃n:num. &1 < &n * (c - x)",
							ByArith(below, real_archimedean.Archimedean.At(fw.TermAs[Real]("c - x"), fw.TermAs[Real]("&1"))))
						fw.Take(n)
						unit := fw.Have(
							"1/(n + 1) times the positive n + 1 is 1",
							"&0 < &n + &1 ∧ &1 / (&n + &1) * (&n + &1) = &1",
							ByArith())
						fw.Show(
							"so 1/(n + 1) lies below c − x",
							ByArith(below, large, unit))
					})
				d.Backward(
					"a point at most c − 1/(n + 1) lies below c",
					func(bw *Argument, within Fact) {
						_, atMost := bw.UnpackAs[Nat](within, "n")
						bw.Show(
							"so x lies below c, 1/(n + 1) being positive",
							ByArith(atMost, real_order_field.DivPos.At(bw.TermAs[Real]("&1"), bw.TermAs[Real]("&n + &1"))))
					})
			}))
		union := arg.Have(
			"so ⟬−∞, c⟭ is the union of the half-lines ⟬−∞, c − 1/(n + 1)⟧",
			"{x:real | x < c} = ⋃image(λn:num. {y:real | y ≤ c - &1 / (&n + &1)}, 𝕌)",
			BySets(pointwise))
		arg.Do(union.Rw())
		arg.Show(
			"the measurable sets form a σ-algebra on the line, closed under "+
				"countable unions, and every closed half-line is one of them",
			By(arg.Unfolded(LebesgueSigmaAlgebra, sigma_algebra.SigmaAlgebraOnDef), MeasurableAtMost))
	}),
})}

// MeasurableAtLeast — the closed half-line ⟦c, ∞⟭ is measurable: it is
// the complement of ⟬−∞, c⟭.
var MeasurableAtLeast = measurableAtLeastThm{family.Add(registry.ProofEntry{
	Name: "MeasurableAtLeast",
	Key:  "prop_63ecf56950280ddf",
	Build: family.Theorem("∀c:real. lebesgue_measurable({x:real | c ≤ x})", func(
		arg *Argument,
		c *Expr[Real],
	) {
		complement := arg.Have(
			"the points at least c are those not below c",
			"{x:real | c ≤ x} = 𝕌 ∖ {x:real | x < c}",
			BySets(real_order_ring.NotLessThan))
		arg.Do(complement.Rw())
		arg.Show(
			"the measurable sets form a σ-algebra on the line, "+
				"closed under complements, and ⟬−∞, c⟭ is one of them",
			By(arg.Unfolded(LebesgueSigmaAlgebra, sigma_algebra.SigmaAlgebraOnDef), At(MeasurableBelow, c)))
	}),
})}

// MeasurableOpenInterval — the open interval ⟬a, b⟭ is measurable: it is
// the intersection of ⟬a, ∞⟭ and ⟬−∞, b⟭.
var MeasurableOpenInterval = measurableOpenIntervalThm{family.Add(registry.ProofEntry{
	Name: "MeasurableOpenInterval",
	Key:  "prop_e9e97f3f664a34c0",
	Build: family.Theorem("∀a b:real. lebesgue_measurable(⟬a, b⟭)", func(
		arg *Argument,
		a, b *Expr[Real],
	) {
		meet := arg.Have(
			"⟬a, b⟭ is the intersection of ⟬a, ∞⟭ and ⟬−∞, b⟭",
			"⟬a, b⟭ = {x:real | a < x} ∩ {x:real | x < b}",
			BySets())
		arg.Do(meet.Rw())
		arg.Show(
			"the measurable sets form a σ-algebra on the line, closed "+
				"under intersections, and ⟬a, ∞⟭ and ⟬−∞, b⟭ are among them",
			By(
				LebesgueSigmaAlgebra,
				sigma_algebra.SigmaFiniteOperations.At(
					arg.TermAs[Set[Real]]("𝕌"),
					arg.TermAs[Set[Set[Real]]]("{s:set(real) | lebesgue_measurable(s)}")),
				At(MeasurableHalfLine, a),
				At(MeasurableBelow, b)))
	}),
})}

// MeasurableClosedInterval — the closed interval ⟦a, b⟧ is measurable: it
// is the intersection of ⟦a, ∞⟭ and ⟬−∞, b⟧.
var MeasurableClosedInterval = measurableClosedIntervalThm{family.Add(registry.ProofEntry{
	Name: "MeasurableClosedInterval",
	Key:  "prop_a43a189b3c37bd4d",
	Build: family.Theorem("∀a b:real. lebesgue_measurable(⟦a, b⟧)", func(
		arg *Argument,
		a, b *Expr[Real],
	) {
		meet := arg.Have(
			"⟦a, b⟧ is the intersection of ⟦a, ∞⟭ and ⟬−∞, b⟧",
			"⟦a, b⟧ = {x:real | a ≤ x} ∩ {x:real | x ≤ b}",
			BySets())
		arg.Do(meet.Rw())
		arg.Show(
			"the measurable sets form a σ-algebra on the line, closed "+
				"under intersections, and ⟦a, ∞⟭ and ⟬−∞, b⟧ are among them",
			By(
				LebesgueSigmaAlgebra,
				sigma_algebra.SigmaFiniteOperations.At(
					arg.TermAs[Set[Real]]("𝕌"),
					arg.TermAs[Set[Set[Real]]]("{s:set(real) | lebesgue_measurable(s)}")),
				At(MeasurableAtLeast, a),
				At(MeasurableAtMost, b)))
	}),
})}

// MeasurableOpen — an open set of reals is measurable: it is the union of
// countably many open intervals, each of them measurable.
var MeasurableOpen = measurableOpenThm{family.Add(registry.ProofEntry{
	Name: "MeasurableOpen",
	Key:  "prop_306f5bcabfeeb0fe",
	Build: family.Theorem(Statement{
		Binders:    "∀u:set(real).",
		Hypotheses: []string{"u ∈ real_topology"},
		Conclusion: "lebesgue_measurable(u)",
	}, func(arg *Argument, u *Expr[Set[Real]], open Fact) {
		_, _, intervals := arg.Obtain2As[Fun[Nat, Real], Fun[Nat, Real]](
			"u is the union of countably many open intervals ⟬a(n), b(n)⟭",
			"∃a b:(num → real). ∀x:real. x ∈ u ⇔ ∃n:num. a(n) < x ∧ x < b(n)",
			By(open, real_topology.OpenCountableIntervalUnion))
		union := arg.Have(
			"so u is the union of the intervals ⟬a(n), b(n)⟭",
			"u = ⋃image(λn:num. ⟬a(n), b(n)⟭, 𝕌)",
			BySets(intervals))
		arg.Do(union.Rw())
		arg.Show(
			"the measurable sets form a σ-algebra on the line, closed "+
				"under countable unions, and every open interval is one of them",
			By(arg.Unfolded(LebesgueSigmaAlgebra, sigma_algebra.SigmaAlgebraOnDef), MeasurableOpenInterval))
	}),
})}

// MeasurableBorel — every Borel set of reals is measurable. A Borel set
// lies in every σ-algebra on the line that holds the open sets, and the
// measurable sets form such a σ-algebra.
var MeasurableBorel = measurableBorelThm{family.Add(registry.ProofEntry{
	Name: "MeasurableBorel",
	Key:  "prop_276cb9b83e74d26d",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(real).",
		Hypotheses: []string{"s ∈ borel_sets(real_topology)"},
		Conclusion: "lebesgue_measurable(s)",
	}, func(arg *Argument, s *Expr[Set[Real]], borel Fact) {
		everySigma := arg.Simplified(
			arg.Unfolded(borel, borel_space.BorelSetsDef),
			Fwd(real_topology.RealSpace))
		containing := arg.Have(
			"s lies in every σ-algebra on the line that holds the open sets",
			"∀S:set(set(real)). sigma_algebra_on(𝕌, S) ∧ real_topology ⊆ S ⇒ s ∈ S",
			BySets(everySigma))
		opens := arg.Have(
			"the open sets are measurable",
			"real_topology ⊆ {u:set(real) | lebesgue_measurable(u)}",
			BySets(MeasurableOpen))
		arg.Show(
			"and the measurable sets are such a σ-algebra",
			By(
				containing.At(arg.TermAs[Set[Set[Real]]]("{u:set(real) | lebesgue_measurable(u)}")),
				LebesgueSigmaAlgebra,
				opens))
	}),
})}
