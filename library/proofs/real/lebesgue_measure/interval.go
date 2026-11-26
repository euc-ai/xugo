// interval.go — the outer measure of an interval is its length, and a
// point has outer measure 0.

package lebesgue_measure

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// OuterMeasureClosedInterval — the closed interval ⟦a, b⟧ has outer
// measure b - a. From above: for every e > 0, ⟦a, b⟧ lies inside
// ⟬a - e/2, b + e/2⟭, so its outer measure is at most b - a + e. From
// below: a cover of ⟦a, b⟧ by open intervals is longer than b - a already
// in an initial segment of its intervals (CountableCoverLength), an empty
// interval counting 0, and its total length is at least that partial sum.
var OuterMeasureClosedInterval = outerMeasureClosedIntervalThm{family.Add(registry.ProofEntry{
	Name: "OuterMeasureClosedInterval",
	Key:  "prop_3747bb280edd6392",
	Build: family.Theorem(Statement{
		Binders:    "∀a b:real.",
		Hypotheses: []string{"a ≤ b"},
		Conclusion: "lebesgue_outer_measure(⟦a, b⟧) = extended_of_real(b - a)",
		Abbrev: Abbrev{
			{Name: "coverLengths", Text: "λu:set(real). " +
				"    {m:extended_nonneg_real | " +
				"        ∃c d:(num → real). " +
				"            (∀x:real. x ∈ u ⇒ ∃n:num. c(n) < x ∧ x < d(n)) ∧ " +
				"            m = extended_series(λn:num. extended_of_real(d(n) - c(n)))}"},
		},
	}, func(arg *Argument, a, b *Expr[Real], ordered Fact) {
		interval := arg.TermAs[Set[Real]]("⟦a, b⟧")
		measure := arg.TermAs[extended_nonneg_real.ExtendedNonnegReal]("lebesgue_outer_measure(⟦a, b⟧)")
		length := arg.TermAs[extended_nonneg_real.ExtendedNonnegReal]("extended_of_real(b - a)")
		approximations := arg.Have(
			"for every e > 0 the outer measure is at most b - a + e",
			"∀e:real. &0 < e ⇒ lebesgue_outer_measure(⟦a, b⟧) ≤ extended_of_real(b - a) + extended_of_real(e)",
			Derive(func(ep *Argument) {
				e := ep.FixAs[Real]()
				positive := ep.Assume()
				pointwise := ep.Have(
					"each point of ⟦a, b⟧ lies in ⟬a - e/2, b + e/2⟭",
					"∀x:real. a ≤ x ∧ x ≤ b ⇒ a - e / &2 < x ∧ x < b + e / &2",
					ByArith(positive))
				inside := ep.Have(
					"so ⟦a, b⟧ lies inside ⟬a - e/2, b + e/2⟭",
					"⟦a, b⟧ ⊆ ⟬a - e / &2, b + e / &2⟭",
					BySets(pointwise))
				lengths := ep.Have(
					"b - a and e are nonnegative, and the length of ⟬a - e/2, b + e/2⟭ is their sum",
					"&0 ≤ b - a ∧ &0 ≤ e ∧ (b + e / &2) - (a - e / &2) = (b - a) + e",
					ByArith(ordered, positive))
				split := ep.Have(
					"so that length is b - a plus e in ⟦0, ∞⟧",
					"extended_of_real((b + e / &2) - (a - e / &2)) = extended_of_real(b - a) + extended_of_real(e)",
					By(lengths, extended_nonneg_real.OfRealAdd.At(ep.TermAs[Real]("b - a"), e)))
				ep.Show(
					"and the outer measure of ⟦a, b⟧ is at most that length",
					By(
						inside,
						split,
						At(
							OuterMeasureInsideInterval,
							interval,
							ep.TermAs[Real]("a - e / &2"),
							ep.TermAs[Real]("b + e / &2"))))
			}))
		upper := arg.Have(
			"so the outer measure is at most b - a",
			"lebesgue_outer_measure(⟦a, b⟧) ≤ extended_of_real(b - a)",
			By(extended_nonneg_real.LeOfLeAddPositive, approximations))
		zero := arg.TermAs[Real]("&0")
		clamp := arg.Have(
			"a length clamped at 0 embeds in ⟦0, ∞⟧ as the length itself",
			"∀r:real. extended_of_real(max(r, &0)) = extended_of_real(r)",
			arg.ForEach(func(r *Expr[Real]) Action {
				return By(
					Normalized,
					real_sup_inf.MaxIsArgument.At(r, zero),
					real_sup_inf.MaxUpperBound.At(r, zero),
					extended_nonneg_real.OfRealNeg.At(r))
			}))
		longer := arg.Have(
			"every cover of ⟦a, b⟧ is at least b - a long",
			"∀m:extended_nonneg_real. m ∈ «coverLengths»(⟦a, b⟧) ⇒ extended_of_real(b - a) ≤ m",
			Derive(func(cv *Argument) {
				cv.FixAs[extended_nonneg_real.ExtendedNonnegReal]("m")
				lengthOf := cv.Assume()
				c, d, cover := cv.Unpack2As[Fun[Nat, Real], Fun[Nat, Real]](lengthOf, "c", "d")
				parts := cv.Conjuncts(
					cover,
					"the intervals ⟬c(n), d(n)⟭ cover ⟦a, b⟧",
					"m is their total length")
				N, beyond := cv.ObtainAs[Nat](
					"already the intervals at 0 .. N are longer than b - a",
					"∃N:num. b - a < Σ_{n∈0 .. N} max(d(n) - c(n), &0)",
					By(CountableCoverLength.At(c, d, a, b), ordered, parts[0]))
				clamped := cv.TermAs[Fun[Nat, Real]]("λn:num. max(d(n) - c(n), &0)")
				segment := cv.TermAs[Set[Nat]]("0 .. N")
				sum := cv.Have(
					"the clamped lengths add up in ⟦0, ∞⟧ as they do in ℝ",
					"Σ_{n∈0 .. N} extended_of_real(max(d(n) - c(n), &0)) = "+
						"extended_of_real(Σ_{n∈0 .. N} max(d(n) - c(n), &0))",
					By(
						extended_nonneg_real.SumOfReal.At(clamped, segment),
						num_segment.Finite,
						real_sup_inf.MaxUpperBound))
				partial := cv.Simplified(sum, Fwd(clamp))
				below := cv.Have(
					"b - a lies below that sum",
					"extended_of_real(b - a) ≤ extended_of_real(Σ_{n∈0 .. N} max(d(n) - c(n), &0))",
					ByArith(
						ordered,
						beyond,
						extended_nonneg_real.OfRealLe.At(
							cv.TermAs[Real]("b - a"),
							cv.TermAs[Real]("Σ_{n∈0 .. N} max(d(n) - c(n), &0)"))))
				cv.Show(
					"and the partial sum lies below the total length m",
					By(
						parts[1],
						partial,
						below,
						extended_nonneg_real.SeriesPartialLe.At(
							cv.TermAs[Fun[Nat, extended_nonneg_real.ExtendedNonnegReal]](
								"λn:num. extended_of_real(d(n) - c(n))"),
							N),
						extended_nonneg_real.LeTrans))
			}))
		lower := arg.Have(
			"so b - a lies below the infimum over the covers",
			"extended_of_real(b - a) ≤ lebesgue_outer_measure(⟦a, b⟧)",
			Unfold(LebesgueOuterMeasureDef),
			By(extended_nonneg_real.InfGreatest, longer))
		arg.Show(
			"each side lies below the other",
			By(upper, lower, extended_nonneg_real.LeAntisym.At(measure, length)))
	}),
})}

// OuterMeasureOpenInterval — the open interval ⟬a, b⟭ has outer measure
// b - a. It lies inside ⟦a, b⟧, so its outer measure is at most b - a.
// For every e > 0 it contains ⟦a + e/2, b - e/2⟧ when e ≤ b - a, whose
// outer measure is b - a - e; so b - a is at most its outer measure plus
// e, and for a larger e this holds already because b - a < e.
var OuterMeasureOpenInterval = outerMeasureOpenIntervalThm{family.Add(registry.ProofEntry{
	Name: "OuterMeasureOpenInterval",
	Key:  "prop_83a78aa17539ccda",
	Build: family.Theorem(Statement{
		Binders:    "∀a b:real.",
		Hypotheses: []string{"a ≤ b"},
		Conclusion: "lebesgue_outer_measure(⟬a, b⟭) = extended_of_real(b - a)",
	}, func(arg *Argument, a, b *Expr[Real], ordered Fact) {
		open := arg.TermAs[Set[Real]]("⟬a, b⟭")
		measure := arg.TermAs[extended_nonneg_real.ExtendedNonnegReal]("lebesgue_outer_measure(⟬a, b⟭)")
		inClosed := arg.Have(
			"⟬a, b⟭ lies inside ⟦a, b⟧",
			"⟬a, b⟭ ⊆ ⟦a, b⟧",
			BySets(real_order_ring.LessEqOfLessThan))
		upper := arg.Have(
			"so its outer measure is at most that of ⟦a, b⟧, b - a",
			"lebesgue_outer_measure(⟬a, b⟭) ≤ extended_of_real(b - a)",
			By(
				OuterMeasureMono.At(open, arg.TermAs[Set[Real]]("⟦a, b⟧")),
				inClosed,
				At(OuterMeasureClosedInterval, a, b),
				ordered))
		approximations := arg.Have(
			"for every e > 0, b - a is at most the outer measure of ⟬a, b⟭ plus e",
			"∀e:real. &0 < e ⇒ extended_of_real(b - a) ≤ lebesgue_outer_measure(⟬a, b⟭) + extended_of_real(e)",
			Derive(func(ep *Argument) {
				e := ep.FixAs[Real]()
				positive := ep.Assume()
				eReal := ep.TermAs[extended_nonneg_real.ExtendedNonnegReal]("extended_of_real(e)")
				small := ep.Assuming(
					ep.Term("e ≤ b - a"),
					"for e beyond b - a, already b - a lies below e",
					Given(func(lg *Argument, large Fact) {
						belowE := lg.Have(
							"b - a lies below e",
							"extended_of_real(b - a) ≤ extended_of_real(e)",
							ByArith(large, positive, extended_nonneg_real.OfRealLe.At(lg.TermAs[Real]("b - a"), e)))
						lg.Show(
							"and e below the outer measure plus e",
							By(
								belowE,
								extended_nonneg_real.LeAddRight.At(eReal, measure),
								extended_nonneg_real.AddComm.At(eReal, measure),
								extended_nonneg_real.LeTrans))
					}))
				pointwise := ep.Have(
					"each point of ⟦a + e/2, b - e/2⟧ lies in ⟬a, b⟭",
					"∀x:real. a + e / &2 ≤ x ∧ x ≤ b - e / &2 ⇒ a < x ∧ x < b",
					ByArith(positive))
				inside := ep.Have(
					"so ⟦a + e/2, b - e/2⟧ lies inside ⟬a, b⟭",
					"⟦a + e / &2, b - e / &2⟧ ⊆ ⟬a, b⟭",
					BySets(pointwise))
				lengths := ep.Have(
					"⟦a + e/2, b - e/2⟧ is an interval, and its length plus e is b - a",
					"&0 ≤ (b - e / &2) - (a + e / &2) ∧ "+
						"&0 ≤ e ∧ "+
						"a + e / &2 ≤ b - e / &2 ∧ "+
						"b - a = ((b - e / &2) - (a + e / &2)) + e",
					ByArith(small, positive))
				lo := ep.TermAs[Real]("a + e / &2")
				hi := ep.TermAs[Real]("b - e / &2")
				inner := ep.Have(
					"the length of ⟦a + e/2, b - e/2⟧ lies below the outer measure of ⟬a, b⟭",
					"extended_of_real((b - e / &2) - (a + e / &2)) ≤ lebesgue_outer_measure(⟬a, b⟭)",
					By(
						OuterMeasureMono.At(ep.TermAs[Set[Real]]("⟦a + e / &2, b - e / &2⟧"), open),
						inside,
						At(OuterMeasureClosedInterval, lo, hi),
						lengths))
				innerLength := ep.TermAs[extended_nonneg_real.ExtendedNonnegReal](
					"extended_of_real((b - e / &2) - (a + e / &2))")
				ep.Show(
					"adding e to both sides gives b - a on the left",
					By(
						inner,
						lengths,
						extended_nonneg_real.OfRealAdd.At(ep.TermAs[Real]("(b - e / &2) - (a + e / &2)"), e),
						extended_nonneg_real.AddLeMono.At(innerLength, measure, eReal)))
			}))
		arg.Show(
			"each side lies below the other",
			By(approximations, upper, extended_nonneg_real.LeOfLeAddPositive, extended_nonneg_real.LeAntisym))
	}),
})}

// OuterMeasureSingleton — a point has outer measure 0: {c} is the closed
// interval ⟦c, c⟧, of length 0.
var OuterMeasureSingleton = outerMeasureSingletonThm{family.Add(registry.ProofEntry{
	Name: "OuterMeasureSingleton",
	Key:  "prop_1031d535a8bdccc0",
	Build: family.Theorem("∀c:real. lebesgue_outer_measure({c}) = &0",
		func(arg *Argument, c *Expr[Real]) {
			pointwise := arg.Have(
				"x is c exactly when c ≤ x ≤ c",
				"∀x:real. x = c ⇔ c ≤ x ∧ x ≤ c",
				ByArith())
			degenerate := arg.Have(
				"so {c} is the closed interval ⟦c, c⟧",
				"{c} = ⟦c, c⟧",
				BySets(pointwise))
			arg.Show(
				"whose outer measure is its length c - c = 0",
				ByArith(
					degenerate,
					At(OuterMeasureClosedInterval, c, c),
					extended_nonneg_real.OfRealNeg.At(arg.TermAs[Real]("c - c"))))
		}),
})}
