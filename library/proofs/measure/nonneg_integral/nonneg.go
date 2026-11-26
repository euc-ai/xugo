// nonneg.go — the integral of a [0, ∞]-valued function on a measure space:
// the supremum of the integrals of the simple functions lying below it on
// Ω. It is monotone in the function, sees the function on Ω only, vanishes
// on the zero function, is a simple function's own simple integral, and
// takes a nonnegative factor out.

package nonneg_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_simple"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// NonnegIntegralMono — the integral is monotone: a simple function below f
// on Ω lies below g there, so the integrals the supremum for f ranges over
// are among those for g. No structure is asked of Ω, S or μ.
var NonnegIntegralMono = nonnegIntegralMonoThm{family.Add(registry.ProofEntry{
	Name: "NonnegIntegralMono",
	Key:  "prop_dfbfadbb0737984",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f g:(A → extended_nonneg_real).",
		Hypotheses: []string{"∀x:A. x ∈ Ω ⇒ f(x) ≤ g(x)"},
		Conclusion: "nonneg_integral(Ω, S, μ, f) ≤ nonneg_integral(Ω, S, μ, g)",
		Abbrev: Abbrev{
			{Name: "minorants", Text: "λh:(A → extended_nonneg_real). " +
				"    {r:extended_nonneg_real | " +
				"        ∃s:(A → real). " +
				"            measure_simple(Ω, S, s) ∧ " +
				"            (∀x:A. x ∈ Ω ⇒ extended_of_real(s(x)) ≤ h(x)) ∧ " +
				"            r = measure_simple_integral(Ω, μ, s)}"},
		},
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		f, g *Arrow[A, ExtendedNonnegReal], below Fact) {
		a.Do(Unfold(NonnegIntegralDef))
		fewer := a.Have(
			"a simple function below f on Ω lies below g there",
			"«minorants»(f) ⊆ «minorants»(g)",
			BySets(below, extended_nonneg_real.LeTrans))
		a.Show(
			"so the supremum for f is at most the supremum for g",
			By(fewer, extended_nonneg_real.SupMono))
	}),
})}

// NonnegIntegralEqOn — the integral sees a function on Ω only: two functions
// equal on Ω have the same integral, each lying below the other there. No
// structure is asked of Ω, S or μ.
var NonnegIntegralEqOn = nonnegIntegralEqOnThm{family.Add(registry.ProofEntry{
	Name: "NonnegIntegralEqOn",
	Key:  "prop_25cab5a3806726d3",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f g:(A → extended_nonneg_real).",
		Hypotheses: []string{"∀x:A. x ∈ Ω ⇒ f(x) = g(x)"},
		Conclusion: "nonneg_integral(Ω, S, μ, f) = nonneg_integral(Ω, S, μ, g)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		f, g *Arrow[A, ExtendedNonnegReal],
		equal Fact,
	) {
		a.Show(
			"each lies below the other on Ω, so each integral lies below the other",
			By(
				equal,
				extended_nonneg_real.LeRefl,
				NonnegIntegralMono.At(Ω, S, μ, f, g),
				NonnegIntegralMono.At(Ω, S, μ, g, f),
				extended_nonneg_real.LeAntisym))
	}),
})}

// NonnegIntegralZero — the zero function has integral 0: a simple function
// at most 0 on Ω, being nonnegative there, is 0 on Ω, so each term of its
// simple integral is 0 times a measure. No structure is asked of Ω, S or μ.
var NonnegIntegralZero = nonnegIntegralZeroThm{family.Add(registry.ProofEntry{
	Name: "NonnegIntegralZero",
	Key:  "prop_24eab9c3c87f1681",
	Build: family.Theorem("∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). "+
		"    nonneg_integral(Ω, S, μ, λx:A. &0) = &0",
		func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal]) {
			vanishing := a.Have(
				"a simple function at most 0 on Ω has integral 0",
				Statement{
					Binders: "∀s:(A → real).",
					Hypotheses: []string{
						"measure_simple(Ω, S, s)",
						"∀x:A. x ∈ Ω ⇒ extended_of_real(s(x)) ≤ &0",
					},
					Conclusion: "measure_simple_integral(Ω, μ, s) = &0",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[A, Real]]("s")
					given := b.Conjuncts(
						b.Assume(),
						"s is simple",
						"s is at most 0 on Ω")
					zeroOn := b.Have(
						"being nonnegative there too, s is 0 on Ω",
						"∀x:A. x ∈ Ω ⇒ s(x) = &0",
						ByArith(given[1], given[0], measure_simple.NonnegSimpleDef, extended_nonneg_real.OfRealLe))
					values := b.Have(
						"so its only value on Ω is 0",
						"image(s, Ω) ⊆ {&0}",
						BySets(zeroOn))
					b.Do(Unfold(measure_simple.SimpleIntegralDef))
					b.Show(
						"each term of its simple integral is 0 times a measure",
						By(
							values,
							set_basic.SubsetDef,
							set_basic.InSing,
							extended_nonneg_real.MulComm,
							extended_nonneg_real.MulZero,
							extended_nonneg_real.ExtendedSumZero))
				}))
			a.Do(Unfold(NonnegIntegralDef))
			a.Show(
				"so the supremum of those integrals is 0",
				By(
					vanishing,
					extended_nonneg_real.SupLeast,
					extended_nonneg_real.ZeroLe,
					extended_nonneg_real.LeAntisym,
					extended_nonneg_real.LeRefl))
		}),
})}

// NonnegIntegralSimple — on a simple function the integral is its simple
// integral: s lies below itself, so its simple integral is among those the
// supremum ranges over, and a simple function below s on Ω has a simple
// integral at most that of s (SimpleIntegralMono).
var NonnegIntegralSimple = nonnegIntegralSimpleThm{family.Add(registry.ProofEntry{
	Name: "NonnegIntegralSimple",
	Key:  "prop_a3f6fa3de4f668ea",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders:    "∀s:(A → real).",
		Hypotheses: []string{"measure_simple(Ω, S, s)"},
		Conclusion: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(s(x))) = " +
			"measure_simple_integral(Ω, μ, s)",
		Abbrev: Abbrev{
			{Name: "below", Text: "{r:extended_nonneg_real | " +
				"    ∃t:(A → real). " +
				"        measure_simple(Ω, S, t) ∧ " +
				"        (∀x:A. x ∈ Ω ⇒ extended_of_real(t(x)) ≤ extended_of_real(s(x))) ∧ " +
				"        r = measure_simple_integral(Ω, μ, t)}"},
		},
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		s *Arrow[A, Real],
		simple Fact,
	) {
		bounded := a.Have(
			"a simple function below s on Ω has a simple integral at most that of s",
			Statement{
				Binders: "∀t:(A → real).",
				Hypotheses: []string{
					"measure_simple(Ω, S, t)",
					"∀x:A. x ∈ Ω ⇒ extended_of_real(t(x)) ≤ extended_of_real(s(x))",
				},
				Conclusion: "measure_simple_integral(Ω, μ, t) ≤ measure_simple_integral(Ω, μ, s)",
			},
			Derive(func(b *Argument) {
				b.FixAs[Fun[A, Real]]("t")
				given := b.Conjuncts(
					b.Assume(),
					"t is simple",
					"t lies below s on Ω")
				below := b.Have(
					"so t is at most s on Ω, s being nonnegative there",
					"∀x:A. x ∈ Ω ⇒ t(x) ≤ s(x)",
					By(given[1], simple, measure_simple.NonnegSimpleDef, extended_nonneg_real.OfRealLe))
				b.Show(
					"and the simple integral is monotone",
					By(below, measure, simple, given[0], measure_simple.SimpleIntegralMono))
			}))
		a.Do(Unfold(NonnegIntegralDef))
		attained := a.Have(
			"s lies below itself, so its simple integral is among those the supremum ranges over",
			"measure_simple_integral(Ω, μ, s) ∈ «below»",
			By(simple, extended_nonneg_real.LeRefl))
		a.Show(
			"so the supremum is the simple integral of s",
			By(
				bounded,
				attained,
				extended_nonneg_real.SupUpper,
				extended_nonneg_real.SupLeast,
				extended_nonneg_real.LeAntisym))
	}),
})}

// NonnegIntegralScale — a nonnegative factor moves through the integral. At
// c = 0 both sides are 0, by the convention 0 · ∞ = 0. For c > 0, a simple t
// below c·f on Ω is c times the simple function t/c, which lies below f
// there, so the integral of c·f is at most c times that of f; that bound
// read at 1/c and c·f, multiplied through by c, is the other inequality.
var NonnegIntegralScale = nonnegIntegralScaleThm{family.Add(registry.ProofEntry{
	Name: "NonnegIntegralScale",
	Key:  "prop_4889c7d55a95cb76",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders:    "∀f:(A → extended_nonneg_real). ∀c:real.",
		Hypotheses: []string{"&0 ≤ c"},
		Conclusion: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(c) * f(x)) = " +
			"extended_of_real(c) * nonneg_integral(Ω, S, μ, f)",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		f *Arrow[A, ExtendedNonnegReal],
		c *Expr[Real],
		nonneg Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigma := laws[0]
		atMost := a.Have(
			"a positive factor d raises the integral by at most d",
			Statement{
				Binders:    "∀d:real. ∀h:(A → extended_nonneg_real).",
				Hypotheses: []string{"&0 < d"},
				Conclusion: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(d) * h(x)) ≤ " +
					"extended_of_real(d) * nonneg_integral(Ω, S, μ, h)",
			},
			Derive(func(b *Argument) {
				d := b.FixAs[Real]("d")
				h := b.FixAs[Fun[A, ExtendedNonnegReal]]("h")
				dPositive := b.Assume()
				inverse := b.TermAs[Real]("real_inv(d)")
				signs := b.Have(
					"1/d is nonnegative, and d is positive",
					"&0 ≤ real_inv(d) ∧ &0 ≤ d ∧ d ≠ &0",
					ByArith(dPositive, real_order_field.InvNonneg.At(d)))
				unit := b.Have(
					"1/d times d is 1",
					"extended_of_real(real_inv(d)) * extended_of_real(d) = &1",
					By(
						Normalized,
						signs,
						extended_nonneg_real.OfRealMul.At(inverse, d),
						real_construction.MulLeftInverse.At(d)))
				every := b.Have(
					"a simple t below d·h on Ω is d times t/d, which lies below h there",
					Statement{
						Binders: "∀t:(A → real).",
						Hypotheses: []string{
							"measure_simple(Ω, S, t)",
							"∀x:A. x ∈ Ω ⇒ extended_of_real(t(x)) ≤ extended_of_real(d) * h(x)",
						},
						Conclusion: "measure_simple_integral(Ω, μ, t) ≤ extended_of_real(d) * nonneg_integral(Ω, S, μ, h)",
					},
					Derive(func(e *Argument) {
						t := e.FixAs[Fun[A, Real]]("t")
						given := e.Conjuncts(
							e.Assume(),
							"t is simple",
							"t lies below d·h on Ω")
						down := e.TermAs[Fun[A, Real]]("λx:A. real_inv(d) * t(x)")
						downSimple := e.Have(
							"t/d is simple",
							"measure_simple(Ω, S, λx:A. real_inv(d) * t(x))",
							By(sigma, signs, given[0], measure_simple.SimpleScale.At(Ω, S, t, inverse)))
						downBelow := e.Have(
							"and lies below h on Ω",
							"∀x:A. x ∈ Ω ⇒ extended_of_real(real_inv(d) * t(x)) ≤ h(x)",
							Derive(func(g *Argument) {
								g.FixAs[A]("x")
								inΩ := g.Assume()
								value := g.TermAs[ExtendedNonnegReal]("extended_of_real(t(x))")
								scale := g.TermAs[ExtendedNonnegReal]("extended_of_real(real_inv(d))")
								hx := g.TermAs[ExtendedNonnegReal]("h(x)")
								g.Show(
									"t(x) ≤ d·h(x), multiplied through by 1/d",
									By(
										inΩ,
										given[1],
										given[0],
										unit,
										signs,
										measure_simple.NonnegSimpleDef.At(Ω, S, t),
										extended_nonneg_real.OfRealMul.At(inverse, g.TermAs[Real]("t(x)")),
										extended_nonneg_real.MulLeMono.At(
											value,
											g.TermAs[ExtendedNonnegReal]("extended_of_real(d) * h(x)"),
											scale),
										extended_nonneg_real.MulAssoc.At(scale, g.TermAs[ExtendedNonnegReal]("extended_of_real(d)"), hx),
										extended_nonneg_real.MulComm,
										extended_nonneg_real.MulOne.At(hx)))
							}))
						downIntegral := e.Have(
							"so the integral of t/d is at most that of h",
							"measure_simple_integral(Ω, μ, λx:A. real_inv(d) * t(x)) ≤ nonneg_integral(Ω, S, μ, h)",
							By(downBelow, downSimple, NonnegIntegralDef.At(Ω, S, μ, h), extended_nonneg_real.SupUpper))
						restored := e.Have(
							"d times t/d is t",
							"(λx:A. d * (real_inv(d) * t(x))) = t",
							Funext(),
							ByArith(dPositive))
						e.Show(
							"so the integral of t, d times that of t/d, is at most d times that of h",
							By(
								restored,
								downIntegral,
								signs,
								measure,
								downSimple,
								measure_simple.SimpleIntegralScale.At(Ω, S, μ, down, d),
								extended_nonneg_real.MulLeMono.At(
									e.TermAs[ExtendedNonnegReal]("measure_simple_integral(Ω, μ, λx:A. real_inv(d) * t(x))"),
									e.TermAs[ExtendedNonnegReal]("nonneg_integral(Ω, S, μ, h)"),
									e.TermAs[ExtendedNonnegReal]("extended_of_real(d)"))))
					}))
				b.Show(
					"and so is their supremum, the integral of d·h",
					By(
						every,
						NonnegIntegralDef.At(
							Ω, S, μ, b.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(d) * h(x)")),
						extended_nonneg_real.SupLeast))
			}))
		nonzero := a.Unless(
			a.Term("c = &0"),
			"at c = 0, c·f is the zero function, and both sides are 0",
			Given(func(b *Argument, zero Fact) {
				b.Do(zero.Rw())
				vanish := b.Have(
					"0 times any value is 0",
					"(λx:A. extended_of_real(&0) * f(x)) = (λx:A. &0)",
					Funext(),
					By(Normalized, extended_nonneg_real.MulComm, extended_nonneg_real.MulZero))
				b.Show(
					"the integral of the zero function is 0, and so is 0 times any value",
					vanish.Rw(),
					By(NonnegIntegralZero.At(Ω, S, μ), extended_nonneg_real.MulComm, extended_nonneg_real.MulZero))
			}))
		inverse := a.TermAs[Real]("real_inv(c)")
		factor := a.TermAs[ExtendedNonnegReal]("extended_of_real(c)")
		inverseFactor := a.TermAs[ExtendedNonnegReal]("extended_of_real(real_inv(c))")
		scaledIntegral := a.TermAs[ExtendedNonnegReal](
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(c) * f(x))")
		positive := a.Have(
			"so c is positive, and so is 1/c",
			"&0 < c ∧ &0 ≤ real_inv(c) ∧ &0 < real_inv(c)",
			ByArith(nonneg, nonzero, real_order_field.InvPos.At(c)))
		undone := a.Have(
			"1/c times c·f is f",
			"(λx:A. extended_of_real(real_inv(c)) * (extended_of_real(c) * f(x))) = f",
			Funext(),
			By(
				nonzero,
				nonneg,
				positive,
				extended_nonneg_real.OfRealMul.At(inverse, c),
				real_construction.MulLeftInverse.At(c),
				extended_nonneg_real.MulAssoc,
				extended_nonneg_real.MulComm,
				extended_nonneg_real.MulOne))
		back := a.Have(
			"the bound at 1/c and c·f: the integral of f is at most 1/c times that of c·f",
			"nonneg_integral(Ω, S, μ, f) ≤ "+
				"extended_of_real(real_inv(c)) * nonneg_integral(Ω, S, μ, λx:A. extended_of_real(c) * f(x))",
			By(
				undone,
				positive,
				At(atMost, inverse, a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(c) * f(x)"))))
		lower := a.Have(
			"so c times the integral of f is at most c · (1/c) times that of c·f, which is that of c·f",
			"extended_of_real(c) * nonneg_integral(Ω, S, μ, f) ≤ "+
				"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(c) * f(x))",
			By(
				nonzero,
				back,
				nonneg,
				positive,
				extended_nonneg_real.OfRealMul.At(inverse, c),
				real_construction.MulLeftInverse.At(c),
				extended_nonneg_real.MulLeMono.At(
					a.TermAs[ExtendedNonnegReal]("nonneg_integral(Ω, S, μ, f)"),
					a.TermAs[ExtendedNonnegReal](
						"extended_of_real(real_inv(c)) * nonneg_integral(Ω, S, μ, λx:A. extended_of_real(c) * f(x))"),
					factor),
				extended_nonneg_real.MulAssoc.At(factor, inverseFactor, scaledIntegral),
				extended_nonneg_real.MulComm,
				extended_nonneg_real.MulOne.At(scaledIntegral)))
		a.Show(
			"the bound at c itself is the other inequality",
			By(At(atMost, c, f), lower, positive, extended_nonneg_real.LeAntisym))
	}),
})}
