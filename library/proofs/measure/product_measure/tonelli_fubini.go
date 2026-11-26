package product_measure

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_simple"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// ProductNonnegIntegral gives both orders of the nonnegative iterated integral.
// The first-order identity starts with sums over the levels of simple functions
// and extends by monotone convergence. Swapping the coordinates carries the
// reversed product measure to the original measure.
var ProductNonnegIntegral = productNonnegIntegralThm{family.Add(registry.ProofEntry{
	Name: "ProductNonnegIntegral",
	Key:  "prop_eb437690a7a22af1",
	Reading: "Tonelli. σ-finiteness of both factors is load-bearing for the order in which " +
		"ν is integrated last; f is curried, the product reading it through the two projections.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀ν:(set(B) → extended_nonneg_real). " +
			"∀f:(A → B → extended_nonneg_real).",
		Hypotheses: []string{
			"sigma_finite_on(Ω, S, μ)",
			"sigma_finite_on(V, T, ν)",
			"extended_measurable(set_cross(Ω, V), product_sigma(Ω, S, V, T), λp:prod(A, B). f(fst(p), snd(p)))",
		},
		Conclusion: "extended_measurable(Ω, S, λx:A. nonneg_integral(V, T, ν, λy:B. f(x, y))) ∧ " +
			"extended_measurable(V, T, λy:B. nonneg_integral(Ω, S, μ, λx:A. f(x, y))) ∧ " +
			"nonneg_integral(set_cross(Ω, V), " +
			"    product_sigma(Ω, S, V, T), " +
			"    product_measure(Ω, S, μ, ν), " +
			"    λp:prod(A, B). f(fst(p), snd(p))) = " +
			"nonneg_integral(Ω, S, μ, λx:A. nonneg_integral(V, T, ν, λy:B. f(x, y))) ∧ " +
			"nonneg_integral(set_cross(Ω, V), " +
			"    product_sigma(Ω, S, V, T), " +
			"    product_measure(Ω, S, μ, ν), " +
			"    λp:prod(A, B). f(fst(p), snd(p))) = " +
			"nonneg_integral(V, T, ν, λy:B. nonneg_integral(Ω, S, μ, λx:A. f(x, y)))",
		Abbrev: Abbrev{
			{Name: "P", Text: "product_sigma(Ω, S, V, T)"},
			{Name: "mass", Text: "product_measure(Ω, S, μ, ν)"},

			{Name: "reverseP", Text: "product_sigma(V, T, Ω, S)"},
			{Name: "reverseMass", Text: "product_measure(V, T, ν, μ)"},
			{Name: "section", Text: "λE:set(prod(A, B)). λx:A. {y:B | (x, y) ∈ E}"},
			{Name: "level", Text: "λs:(prod(A, B) → real). λr:real. " +
				"    {p:prod(A, B) | p ∈ set_cross(Ω, V) ∧ s(p) = r}"},
			{Name: "levelMass", Text: "λs:(prod(A, B) → real). λr:real. λx:A. " +
				"    extended_of_real(r) * ν(«section»(«level»(s, r), x))"},
			{Name: "sumOfLevels", Text: "λs:(prod(A, B) → real). λx:A. " +
				"    Σ_{r∈image(s, set_cross(Ω, V))} «levelMass»(s, r, x)"},
			{Name: "simpleInner", Text: "λs:(prod(A, B) → real). λx:A. " +
				"    nonneg_integral(V, T, ν, λy:B. extended_of_real(s((x, y))))"},
			{Name: "inner", Text: "λh:(prod(A, B) → extended_nonneg_real). λx:A. " +
				"    nonneg_integral(V, T, ν, λy:B. h((x, y)))"},
			{Name: "swap", Text: "λq:prod(B, A). (snd(q), fst(q))"},
			{Name: "pushed", Text: "pushforward_measure(set_cross(V, Ω), «reverseMass», «swap»)"},
			{Name: "uncurried", Text: "λp:prod(A, B). f(fst(p), snd(p))"},
			{Name: "reversed", Text: "λq:prod(B, A). f(snd(q), fst(q))"},
			{Name: "firstInner", Text: "λx:A. nonneg_integral(V, T, ν, λy:B. f(x, y))"},
			{Name: "secondInner", Text: "λy:B. nonneg_integral(Ω, S, μ, λx:A. f(x, y))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		measurableEqOn := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f g:(A → extended_nonneg_real).",
			Hypotheses: []string{
				"sigma_algebra_on(Ω, S)",
				"extended_measurable(Ω, S, f)",
				"∀x:A. x ∈ Ω ⇒ f(x) = g(x)",
			},
			Conclusion: "extended_measurable(Ω, S, g)",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			f, g *Arrow[A, ExtendedNonnegReal], sigma, measurable, agree Fact) {
			rays := a.Have(
				"all upper rays of f are measurable",
				"∀r:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < f(x)} ∈ S",
				By(sigma, measurable, measurable_function.ExtendedMeasurableIffRay.At(Ω, S, f)))
			pulled := a.Have(
				"the functions have the same upper rays on Ω",
				"∀r:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < g(x)} ∈ S",
				Derive(func(b *Argument) {
					r := b.FixAs[Real]("r")
					ray := b.Have(
						"the upper rays agree inside the carrier",
						"{x:A | x ∈ Ω ∧ extended_of_real(r) < g(x)} = {x:A | x ∈ Ω ∧ extended_of_real(r) < f(x)}",
						BySets(agree))
					b.Show(
						"use the corresponding upper ray of f",
						By(rays.At(r), ray))
				}))
			a.Show(
				"the upper rays decide measurability",
				By(sigma, pulled, measurable_function.ExtendedMeasurableIffRay.At(Ω, S, g)))
		})

		measurableScale := ctx.Lemma(Statement{
			Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → extended_nonneg_real). ∀c:real.",
			Hypotheses: []string{"sigma_algebra_on(Ω, S)", "extended_measurable(Ω, S, f)", "&0 ≤ c"},
			Conclusion: "extended_measurable(Ω, S, λx:A. extended_of_real(c) * f(x))",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], f *Arrow[A, ExtendedNonnegReal],
			c *Expr[Real], sigma, measurable, sign Fact) {
			_, approximation := a.UnpackAs[Fun2[Nat, A, Real]](
				GroupPremises(sigma, measurable, measure_simple.SimpleApproximation.At(Ω, S, f)), "u")
			parts := a.Conjuncts(
				approximation,
				"each term is simple",
				"the terms increase",
				"the terms lie below f",
				"f is the pointwise supremum on the carrier")
			scaled := a.TermAs[Fun2[Nat, A, ExtendedNonnegReal]]("λn:num. λx:A. extended_of_real(c * u(n, x))")
			limit := a.TermAs[Fun[A, ExtendedNonnegReal]](
				"λx:A. extended_sup(image(λn:num. extended_of_real(c * u(n, x)), 𝕌))")
			product := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(c) * f(x)")
			cConstant := a.TermAs[Fun[A, Real]]("λx:A. c")
			terms := a.Have(
				"each scaled simple function embeds as a measurable function",
				"∀n:num. extended_measurable(Ω, S, λx:A. extended_of_real(c * u(n, x)))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					u := b.TermAs[Fun[A, Real]]("u(n)")
					cu := b.TermAs[Fun[A, Real]]("λx:A. c * u(n, x)")
					productMeasurable := b.Have(
						"a real constant times a measurable real function is measurable",
						"real_measurable(Ω, S, λx:A. c * u(n, x))",
						By(
							sigma,
							parts[0].At(n),
							measure_simple.NonnegSimpleDef.At(Ω, S, u),
							measurable_function.RealMeasurableConst.At(Ω, S, c),
							measurable_function.RealMeasurableMul.At(Ω, S, cConstant, u)))
					b.Show(
						"embedding preserves measurability",
						By(sigma, productMeasurable, measurable_function.ExtendedMeasurableOfReal.At(Ω, S, cu)))
				}))
			agree := a.Have(
				"scaling commutes with the pointwise supremum",
				Statement{
					Binders:    "∀x:A.",
					Hypotheses: []string{"x ∈ Ω"},
					Conclusion: "extended_sup(image(λn:num. extended_of_real(c * u(n, x)), 𝕌)) = " +
						"extended_of_real(c) * f(x)",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					member := b.Assume()
					factors := b.Have(
						"embedding respects the products of the nonnegative values",
						"(λn:num. extended_of_real(c * u(n, x))) = "+
							"(λn:num. extended_of_real(c) * extended_of_real(u(n, x)))",
						Funext(),
						Derive(func(d *Argument) {
							d.FixAs[Nat]("n")
							d.Show(
								"the factor is nonnegative",
								By(sign, extended_nonneg_real.OfRealMul.At(c, d.TermAs[Real]("u(n, x)"))))
						}))
					b.Show(
						"take the supremum of the terms with the factor outside",
						factors.Rw(),
						By(
							member,
							sign,
							parts[3].At(x),
							extended_nonneg_real.SupSequenceScale.At(c, b.TermAs[Fun[Nat, ExtendedNonnegReal]](
								"λn:num. extended_of_real(u(n, x))"))))
				}))
			a.Show(
				"the product agrees on the carrier with a measurable supremum",
				By(
					sigma,
					terms,
					agree,
					measurable_function.ExtendedMeasurableSup.At(Ω, S, scaled),
					At(measurableEqOn, Ω, S, limit, product)))
		})

		measurableAdd := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f g:(A → extended_nonneg_real).",
			Hypotheses: []string{
				"sigma_algebra_on(Ω, S)",
				"extended_measurable(Ω, S, f)",
				"extended_measurable(Ω, S, g)",
			},
			Conclusion: "extended_measurable(Ω, S, λx:A. f(x) + g(x))",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], f, g *Arrow[A, ExtendedNonnegReal],
			sigma, fMeas, gMeas Fact) {
			_, first := a.UnpackAs[Fun2[Nat, A, Real]](
				GroupPremises(sigma, fMeas, measure_simple.SimpleApproximation.At(Ω, S, f)), "u")
			_, second := a.UnpackAs[Fun2[Nat, A, Real]](
				GroupPremises(sigma, gMeas, measure_simple.SimpleApproximation.At(Ω, S, g)), "v")
			up := a.Conjuncts(
				first,
				"the first terms are simple",
				"the first terms increase",
				"the first terms lie below f",
				"f is their supremum on Ω")
			vp := a.Conjuncts(
				second,
				"the second terms are simple",
				"the second terms increase",
				"the second terms lie below g",
				"g is their supremum on Ω")
			terms := a.Have(
				"each embedded sum is measurable",
				"∀n:num. extended_measurable(Ω, S, λx:A. extended_of_real(u(n, x) + v(n, x)))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					u := b.TermAs[Fun[A, Real]]("u(n)")
					v := b.TermAs[Fun[A, Real]]("v(n)")
					sum := b.TermAs[Fun[A, Real]]("λx:A. u(n, x) + v(n, x)")
					b.Show(
						"real sums are measurable and embedding preserves measurability",
						By(
							sigma,
							up[0].At(n),
							vp[0].At(n),
							measure_simple.NonnegSimpleDef.At(Ω, S, u),
							measure_simple.NonnegSimpleDef.At(Ω, S, v),
							measurable_function.RealMeasurableAdd.At(Ω, S, u, v),
							measurable_function.ExtendedMeasurableOfReal.At(Ω, S, sum)))
				}))
			agree := a.Have(
				"taking the supremum of the sums gives the sum of the pointwise suprema",
				"∀x:A. x ∈ Ω ⇒ extended_sup(image(λn:num. extended_of_real(u(n, x) + v(n, x)), 𝕌)) = f(x) + g(x)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					member := b.Assume()
					embedded := b.Have(
						"embedding respects the sums of nonnegative terms",
						"(λn:num. extended_of_real(u(n, x) + v(n, x))) = "+
							"(λn:num. extended_of_real(u(n, x)) + extended_of_real(v(n, x)))",
						Funext(),
						Derive(func(d *Argument) {
							n := d.FixAs[Nat]("n")
							d.Show(
								"simple functions are nonnegative on the carrier",
								By(
									member,
									up[0].At(n),
									vp[0].At(n),
									measure_simple.NonnegSimpleDef.At(Ω, S, d.TermAs[Fun[A, Real]]("u(n)")),
									measure_simple.NonnegSimpleDef.At(Ω, S, d.TermAs[Fun[A, Real]]("v(n)")),
									extended_nonneg_real.OfRealAdd.At(d.TermAs[Real]("u(n, x)"), d.TermAs[Real]("v(n, x)"))))
						}))
					rising := b.Have(
						"both sequences still increase after embedding",
						"(∀n:num. extended_of_real(u(n, x)) ≤ extended_of_real(u(n + 1, x))) ∧ "+
							"(∀n:num. extended_of_real(v(n, x)) ≤ extended_of_real(v(n + 1, x)))",
						SplitConj(
							Case(
								"embedding preserves the first ordering",
								Derive(func(d *Argument) {
									n := d.FixAs[Nat]("n")
									d.Show(
										"use the order of real terms",
										By(
											member,
											up[1].At(n, x),
											extended_nonneg_real.OfRealMono.At(
												d.TermAs[Real]("u(n, x)"), d.TermAs[Real]("u(n + 1, x)"))))
								})),
							Case(
								"embedding preserves the second ordering",
								Derive(func(d *Argument) {
									n := d.FixAs[Nat]("n")
									d.Show(
										"use the order of real terms",
										By(
											member,
											vp[1].At(n, x),
											extended_nonneg_real.OfRealMono.At(
												d.TermAs[Real]("v(n, x)"), d.TermAs[Real]("v(n + 1, x)"))))
								}))))
					b.Show(
						"use the sum law for increasing suprema",
						embedded.Rw(),
						By(
							member,
							up[3].At(x),
							vp[3].At(x),
							rising,
							extended_nonneg_real.SupSequenceAdd.At(
								b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_of_real(u(n, x))"),
								b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_of_real(v(n, x))"))))
				}))
			sequence := a.TermAs[Fun2[Nat, A, ExtendedNonnegReal]](
				"λn:num. λx:A. extended_of_real(u(n, x) + v(n, x))")
			limit := a.TermAs[Fun[A, ExtendedNonnegReal]](
				"λx:A. extended_sup(image(λn:num. extended_of_real(u(n, x) + v(n, x)), 𝕌))")
			sum := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. f(x) + g(x)")
			a.Show(
				"the sum agrees with the measurable supremum on the carrier",
				By(
					sigma,
					terms,
					agree,
					measurable_function.ExtendedMeasurableSup.At(Ω, S, sequence),
					At(measurableEqOn, Ω, S, limit, sum)))
		})

		finiteSum := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀f:(real → A → extended_nonneg_real). " +
				"∀k:set(real).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"finite(k)",
				"∀r:real. r ∈ k ⇒ extended_measurable(Ω, S, f(r))",
			},
			Conclusion: "extended_measurable(Ω, S, λx:A. Σ_{r∈k} f(r, x)) ∧ " +
				"nonneg_integral(Ω, S, μ, λx:A. Σ_{r∈k} f(r, x)) = Σ_{r∈k} nonneg_integral(Ω, S, μ, f(r))",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
			f *Arrow2[Real, A, ExtendedNonnegReal], k *Expr[Set[Real]], measure, finite, measurable Fact) {
			sigma := a.Have(
				"the measurable sets form a sigma algebra",
				"sigma_algebra_on(Ω, S)",
				By(measure, measure_space.MeasureOn.At(Ω, S, μ)))
			sumLaws := extended_nonneg_real.SumClauses.Inst(TypeBinder.BindA[Real](), TypeBinder.BindC[Real]())
			a.Show(
				"a finite sum of measurable functions is measurable and integrates term by term",
				ByInduction(finite_set.FiniteInductFresh.Inst[Real](), finite, Generalizing(measurable),
					Case(
						"the empty sum is the measurable zero function",
						Derive(func(b *Argument) {
							b.Assume()
							zero := b.TermAs[Fun[A, Real]]("λx:A. &0")
							sums := b.Have(
								"both empty sums are zero",
								"(λx:A. Σ_{r∈∅⟨A:real⟩} f(r, x)) = (λx:A. extended_of_real(&0)) ∧ "+
									"Σ_{r∈∅⟨A:real⟩} nonneg_integral(Ω, S, μ, f(r)) = &0",
								By(sumLaws))
							b.Show(
								"zero is measurable with zero integral",
								By(
									Normalized,
									sigma,
									sums,
									measurable_function.RealMeasurableConst.At(Ω, S, b.TermAs[Real]("&0")),
									measurable_function.ExtendedMeasurableOfReal.At(Ω, S, zero),
									nonneg_integral.NonnegIntegralZero.At(Ω, S, μ)))
						})),
					Case(
						"a new term adds one measurable summand",
						Derive(func(b *Argument) {
							b.FixAs[Real]("x")
							b.FixAs[Set[Real]]("s")
							previous := b.Assume()
							allMeasurable := b.Assume()
							terms := b.Have(
								"the new term and all earlier terms are measurable",
								"extended_measurable(Ω, S, f(x)) ∧ (∀r:real. r ∈ s ⇒ extended_measurable(Ω, S, f(r)))",
								BySets(allMeasurable))
							earlier := b.Have(
								"the previous sum is measurable and integrates term by term",
								"extended_measurable(Ω, S, λy:A. Σ_{r∈s} f(r, y)) ∧ "+
									"nonneg_integral(Ω, S, μ, λy:A. Σ_{r∈s} f(r, y)) = Σ_{r∈s} nonneg_integral(Ω, S, μ, f(r))",
								By(previous, terms))
							peel := b.Have(
								"the sum over insert includes the new term once",
								"∀q:(real → extended_nonneg_real). Σ_{r∈insert(x, s)} q(r) = q(x) + Σ_{r∈s} q(r)",
								By(previous, sumLaws))
							peelFunctions := b.Have(
								"the sum of the functions adds the new function",
								"(λy:A. Σ_{r∈insert(x, s)} f(r, y)) = (λy:A. f(x, y) + Σ_{r∈s} f(r, y))",
								Funext(),
								Derive(func(c *Argument) {
									c.FixAs[A]("y")
									c.Show(
										"apply the sum law at this point",
										By(peel.At(c.TermAs[Fun[Real, ExtendedNonnegReal]]("λr:real. f(r, y)"))))
								}))
							old := b.TermAs[Fun[A, ExtendedNonnegReal]]("λy:A. Σ_{r∈s} f(r, y)")
							add := b.TermAs[Fun[A, ExtendedNonnegReal]]("f(x)")
							b.Show(
								"add the new measurable function and its integral",
								SplitConj(
									Case(
										"a sum of two measurable functions is measurable",
										By(sigma, terms, earlier, peelFunctions, At(measurableAdd, Ω, S, add, old))),
									Case(
										"additivity integrates the new term separately",
										By(
											measure,
											terms,
											earlier,
											peelFunctions,
											nonneg_integral.NonnegIntegralAdd.At(Ω, S, μ, add, old),
											peel.At(b.TermAs[Fun[Real, ExtendedNonnegReal]]("λr:real. nonneg_integral(Ω, S, μ, f(r))"))))))
						}))))
		})

		simpleIteration := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀V:set(B). " +
				"∀T:set(set(B)). " +
				"∀ν:(set(B) → extended_nonneg_real). " +
				"∀s:(prod(A, B) → real).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"sigma_finite_on(V, T, ν)",
				"measure_simple(set_cross(Ω, V), «P», s)",
			},
			Conclusion: "(∀x:A. x ∈ Ω ⇒ measure_simple(V, T, λy:B. s((x, y)))) ∧ " +
				"extended_measurable(Ω, S, «simpleInner»(s)) ∧ " +
				"nonneg_integral(set_cross(Ω, V), «P», «mass», λp:prod(A, B). extended_of_real(s(p))) = " +
				"nonneg_integral(Ω, S, μ, «simpleInner»(s))",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
			V *Expr[Set[B]], T *Expr[Set[Set[B]]], ν *Arrow[Set[B], ExtendedNonnegReal],
			s *Arrow[Prod[A, B], Real], left, right, simple Fact) {
			K := a.TermAs[Set[Prod[A, B]]]("set_cross(Ω, V)")
			P := a.TermAs[Set[Set[Prod[A, B]]]]("«P»")
			m := a.TermAs[Fun[Set[Prod[A, B]], ExtendedNonnegReal]]("«mass»")
			R := a.TermAs[Set[Real]]("image(s, set_cross(Ω, V))")
			factors := a.Have(
				"the product measure and both factor sigma algebras",
				"measure_on(V, T, ν) ∧ "+
					"measure_on(set_cross(Ω, V), «P», «mass») ∧ "+
					"sigma_algebra_on(Ω, S) ∧ "+
					"sigma_algebra_on(V, T) ∧ "+
					"sigma_algebra_on(set_cross(Ω, V), «P»)",
				By(
					left,
					right,
					measure_space.SigmaFiniteDef.At(V, T, ν),
					ProductMeasureOn.At(Ω, S, μ, V, T, ν),
					measure_space.MeasureOn.At(Ω, S, μ),
					measure_space.MeasureOn.At(V, T, ν),
					measurable_space.ProductSigmaProjections.At(Ω, S, V, T)))
			data := a.Have(
				"a simple function is measurable, nonnegative and has finite range",
				"real_measurable(set_cross(Ω, V), «P», s) ∧ "+
					"finite(image(s, set_cross(Ω, V))) ∧ "+
					"(∀p:prod(A, B). p ∈ set_cross(Ω, V) ⇒ &0 ≤ s(p))",
				By(simple, measure_simple.NonnegSimpleDef.At(K, P, s)))
			rays := a.Have(
				"the upper rays of the simple function are product events",
				"∀r:real. {p:prod(A, B) | p ∈ set_cross(Ω, V) ∧ r < s(p)} ∈ «P»",
				By(data, factors, measurable_function.RealMeasurableIffRay.At(K, P, s)))
			cross := set_product.InCross.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]())
			simpleSections := a.Have(
				"the sections of the simple function are simple on the second carrier",
				"∀x:A. x ∈ Ω ⇒ measure_simple(V, T, λy:B. s((x, y)))",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					member := b.Assume()
					sx := b.TermAs[Fun[B, Real]]("λy:B. s((x, y))")
					sectionRays := b.Have(
						"each upper ray of the section is measurable",
						"∀r:real. {y:B | y ∈ V ∧ r < s((x, y))} ∈ T",
						Derive(func(c *Argument) {
							r := c.FixAs[Real]("r")
							ray := c.TermAs[Set[Prod[A, B]]]("{p:prod(A, B) | p ∈ set_cross(Ω, V) ∧ r < s(p)}")
							section := c.Have(
								"the upper ray of the section is the section of the product ray",
								"«section»({p:prod(A, B) | p ∈ set_cross(Ω, V) ∧ r < s(p)}, x) = {y:B | y ∈ V ∧ r < s((x, y))}",
								BySets(member, cross))
							c.Show(
								"sections of product events are measurable",
								By(
									factors,
									rays.At(r),
									section,
									sigma_algebra.SigmaAlgebraOnDef.At(Ω, S),
									ProductSectionMeasurable.At(Ω, S, V, T, ray, x)))
						}))
					rangeData := b.Have(
						"the section takes only nonnegative values already attained on the product",
						"image(λy:B. s((x, y)), V) ⊆ image(s, set_cross(Ω, V)) ∧ (∀y:B. y ∈ V ⇒ &0 ≤ s((x, y)))",
						BySets(member, data, cross))
					b.Show(
						"measurability and finite nonnegative range make the section simple",
						By(
							factors,
							data,
							rangeData,
							sectionRays,
							measurable_function.RealMeasurableIffRay.At(V, T, sx),
							measure_simple.NonnegSimpleDef.At(V, T, sx),
							finite_set.FiniteSubset.At(b.TermAs[Set[Real]]("image(λy:B. s((x, y)), V)"), R)))
				}))
			op := a.TermAs[Fun2[ExtendedNonnegReal, ExtendedNonnegReal, ExtendedNonnegReal]]("extended_add")
			inner := a.TermAs[Fun[A, ExtendedNonnegReal]]("«simpleInner»(s)")
			sum := a.TermAs[Fun[A, ExtendedNonnegReal]]("«sumOfLevels»(s)")
			sectionSums := a.Have(
				"the inner integral equals the sum over the product levels on Ω",
				"∀x:A. x ∈ Ω ⇒ «simpleInner»(s, x) = «sumOfLevels»(s, x)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					member := b.Assume()
					sx := b.TermAs[Fun[B, Real]]("λy:B. s((x, y))")
					local := b.TermAs[Set[Real]]("image(λy:B. s((x, y)), V)")
					weights := b.TermAs[Fun[Real, ExtendedNonnegReal]]("λr:real. «levelMass»(s, r, x)")
					subset := b.Have(
						"each value of the section is a product value",
						"image(λy:B. s((x, y)), V) ⊆ image(s, set_cross(Ω, V))",
						BySets(member, cross))
					levels := b.Have(
						"the level sets of the section are sections of the product level sets",
						"∀r:real. «section»(«level»(s, r), x) = {y:B | y ∈ V ∧ s((x, y)) = r}",
						BySets(member, cross))
					sectionIntegral := b.Have(
						"the simple integral sums over the values attained in the section",
						"«simpleInner»(s, x) = "+
							"Σ_{r∈image(λy:B. s((x, y)), V)} extended_of_real(r) * ν({y:B | y ∈ V ∧ s((x, y)) = r})",
						By(
							member,
							factors,
							simpleSections.At(x),
							nonneg_integral.NonnegIntegralSimple.At(V, T, ν, sx),
							measure_simple.SimpleIntegralDef.At(V, ν, sx)))
					weightsAgree := b.Have(
						"the section summands are the corresponding product level weights",
						"(λr:real. extended_of_real(r) * ν({y:B | y ∈ V ∧ s((x, y)) = r})) = "+
							"(λr:real. «levelMass»(s, r, x))",
						Funext(),
						Derive(func(c *Argument) {
							r := c.FixAs[Real]("r")
							c.Show(
								"read the level set as a section",
								By(levels.At(r)))
						}))
					silent := b.Have(
						"levels omitted from the section have empty level sets and contribute zero",
						Statement{
							Binders: "∀r:real.",
							Hypotheses: []string{
								"r ∈ image(s, set_cross(Ω, V))",
								"r ∉ image(λy:B. s((x, y)), V)",
							},
							Conclusion: "«levelMass»(s, r, x) = neutral_elem(extended_add)",
						},
						Derive(func(c *Argument) {
							r := c.FixAs[Real]("r")
							omitted := c.Assume()
							empty := c.Have(
								"the section does not attain the omitted level",
								"{y:B | y ∈ V ∧ s((x, y)) = r} = ∅",
								BySets(omitted))
							c.Show(
								"the measure gives the empty level zero mass",
								By(
									factors,
									levels.At(r),
									empty,
									measure_space.MeasureOn.At(V, T, ν),
									extended_nonneg_real.MulZero.At(c.TermAs[ExtendedNonnegReal]("extended_of_real(r)")),
									extended_nonneg_real.NeutralAdd))
						}))
					enlarge := b.Have(
						"adding unattained values leaves the section sum unchanged",
						"extended_sum(image(λy:B. s((x, y)), V), λr:real. «levelMass»(s, r, x)) = "+
							"extended_sum(image(s, set_cross(Ω, V)), λr:real. «levelMass»(s, r, x))",
						Simp(Fwd(extended_nonneg_real.ExtendedSumDef.Inst[Real]())),
						By(subset, silent, monoidal.Superset.At(op, local, R, weights)))
					b.Show(
						"use the same weights and enlarge to the product range",
						By(b.Simplified(sectionIntegral, Fwd(weightsAgree)), enlarge))
				}))
			levelIntegrals := a.Have(
				"the section mass at each product level is measurable and integrates to the weighted product mass",
				Statement{
					Binders:    "∀r:real.",
					Hypotheses: []string{"r ∈ image(s, set_cross(Ω, V))"},
					Conclusion: "extended_measurable(Ω, S, «levelMass»(s, r)) ∧ " +
						"nonneg_integral(Ω, S, μ, «levelMass»(s, r)) = extended_of_real(r) * «mass»(«level»(s, r))",
				},
				Derive(func(b *Argument) {
					r := b.FixAs[Real]("r")
					attained := b.Assume()
					event := b.TermAs[Set[Prod[A, B]]]("«level»(s, r)")
					sectionMass := b.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. ν(«section»(«level»(s, r), x))")
					sign := b.Have(
						"an attained value is nonnegative",
						"&0 ≤ r",
						BySets(attained, data))
					measurable := b.Have(
						"the product level set is measurable",
						"«level»(s, r) ∈ «P»",
						By(factors, simple, measure_simple.SimpleLevelSets.At(K, P, s, r)))
					sections := b.Have(
						"the corresponding section mass function is measurable",
						"extended_measurable(Ω, S, λx:A. ν(«section»(«level»(s, r), x)))",
						By(factors, right, measurable, ProductSectionMassMeasurable.At(Ω, S, V, T, ν, event)))
					b.Show(
						"multiply by the nonnegative real level and use the product formula",
						SplitConj(
							Case(
								"scaling preserves measurability",
								By(factors, sections, sign, At(measurableScale, Ω, S, sectionMass, r))),
							Case(
								"the finite factor comes outside the integral",
								By(
									left,
									sign,
									nonneg_integral.NonnegIntegralScale.At(Ω, S, μ, sectionMass, r),
									ProductMeasureDef.At(Ω, S, μ, ν, event)))))
				}))
			weights := a.TermAs[Fun2[Real, A, ExtendedNonnegReal]]("«levelMass»(s)")
			measurableWeights := a.Have(
				"all attained-level weights are measurable in the first variable",
				"∀r:real. r ∈ image(s, set_cross(Ω, V)) ⇒ extended_measurable(Ω, S, «levelMass»(s, r))",
				By(levelIntegrals))
			integratedSum := a.Have(
				"the sum is measurable and the outer integral integrates each weight",
				"extended_measurable(Ω, S, «sumOfLevels»(s)) ∧ "+
					"nonneg_integral(Ω, S, μ, «sumOfLevels»(s)) = "+
					"Σ_{r∈image(s, set_cross(Ω, V))} nonneg_integral(Ω, S, μ, «levelMass»(s, r))",
				By(left, data, measurableWeights, At(finiteSum, Ω, S, μ, weights, R)))
			sameSum := a.Have(
				"each integrated weight equals the weighted product level mass",
				"(Σ_{r∈image(s, set_cross(Ω, V))} nonneg_integral(Ω, S, μ, «levelMass»(s, r))) = "+
					"Σ_{r∈image(s, set_cross(Ω, V))} extended_of_real(r) * «mass»(«level»(s, r))",
				Simp(Fwd(extended_nonneg_real.ExtendedSumDef.Inst[Real]())),
				By(
					levelIntegrals,
					extended_nonneg_real.MonoidalAdd,
					monoidal.Congruence.At(op, R,
						a.TermAs[Fun[Real, ExtendedNonnegReal]]("λr:real. nonneg_integral(Ω, S, μ, «levelMass»(s, r))"),
						a.TermAs[Fun[Real, ExtendedNonnegReal]]("λr:real. extended_of_real(r) * «mass»(«level»(s, r))"))))
			productIntegral := a.Have(
				"the product simple integral is the sum of weighted product level masses",
				"nonneg_integral(set_cross(Ω, V), «P», «mass», λp:prod(A, B). extended_of_real(s(p))) = "+
					"Σ_{r∈image(s, set_cross(Ω, V))} extended_of_real(r) * «mass»(«level»(s, r))",
				By(
					factors,
					simple,
					nonneg_integral.NonnegIntegralSimple.At(K, P, m, s),
					measure_simple.SimpleIntegralDef.At(K, m, s)))
			agree := a.Have(
				"the measurable sum agrees with the inner integral on Ω",
				"∀x:A. x ∈ Ω ⇒ «sumOfLevels»(s, x) = «simpleInner»(s, x)",
				By(sectionSums))
			a.Show(
				"the inner integral is measurable and the integrals agree",
				By(
					simpleSections,
					factors,
					integratedSum,
					sameSum,
					productIntegral,
					agree,
					At(measurableEqOn, Ω, S, sum, inner),
					nonneg_integral.NonnegIntegralEqOn.At(Ω, S, μ, sum, inner)))
		})

		firstOrder := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀V:set(B). " +
				"∀T:set(set(B)). " +
				"∀ν:(set(B) → extended_nonneg_real). " +
				"∀h:(prod(A, B) → extended_nonneg_real).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"sigma_finite_on(V, T, ν)",
				"extended_measurable(set_cross(Ω, V), «P», h)",
			},
			Conclusion: "extended_measurable(Ω, S, «inner»(h)) ∧ " +
				"nonneg_integral(set_cross(Ω, V), «P», «mass», h) = nonneg_integral(Ω, S, μ, «inner»(h))",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
			V *Expr[Set[B]], T *Expr[Set[Set[B]]], ν *Arrow[Set[B], ExtendedNonnegReal],
			h *Arrow[Prod[A, B], ExtendedNonnegReal], left, right, measurable Fact) {
			K := a.TermAs[Set[Prod[A, B]]]("set_cross(Ω, V)")
			P := a.TermAs[Set[Set[Prod[A, B]]]]("«P»")
			m := a.TermAs[Fun[Set[Prod[A, B]], ExtendedNonnegReal]]("«mass»")
			factors := a.Have(
				"the second measure and the product measure are available",
				"measure_on(V, T, ν) ∧ "+
					"measure_on(set_cross(Ω, V), «P», «mass») ∧ "+
					"sigma_algebra_on(Ω, S) ∧ "+
					"sigma_algebra_on(set_cross(Ω, V), «P»)",
				By(
					left,
					right,
					measure_space.SigmaFiniteDef.At(V, T, ν),
					ProductMeasureOn.At(Ω, S, μ, V, T, ν),
					measure_space.MeasureOn.At(Ω, S, μ),
					measure_space.MeasureOn.At(V, T, ν),
					measurable_space.ProductSigmaProjections.At(Ω, S, V, T)))
			u, approximation := a.UnpackAs[Fun2[Nat, Prod[A, B], Real]](
				GroupPremises(factors, measurable, measure_simple.SimpleApproximation.At(K, P, h)), "u")
			parts := a.Conjuncts(
				approximation,
				"the terms are simple on the product",
				"the terms increase on the product",
				"the terms lie below h",
				"their pointwise supremum is h on the product")
			each := a.Have(
				"each approximation is simple on sections and satisfies the one-order formula",
				"∀n:num. "+
					"    (∀x:A. x ∈ Ω ⇒ measure_simple(V, T, λy:B. u(n, (x, y)))) ∧ "+
					"    extended_measurable(Ω, S, «simpleInner»(u(n))) ∧ "+
					"    nonneg_integral(set_cross(Ω, V), «P», «mass», λp:prod(A, B). extended_of_real(u(n, p))) = "+
					"    nonneg_integral(Ω, S, μ, «simpleInner»(u(n)))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"use the formula for simple functions",
						By(
							left,
							right,
							parts[0].At(n),
							At(simpleIteration, Ω, S, μ, V, T, ν,
								b.TermAs[Fun[Prod[A, B], Real]]("u(n)"))))
				}))
			innerTerms := a.TermAs[Fun2[Nat, A, ExtendedNonnegReal]]("λn:num. «simpleInner»(u(n))")
			inner := a.TermAs[Fun[A, ExtendedNonnegReal]]("«inner»(h)")
			limit := a.TermAs[Fun[A, ExtendedNonnegReal]](
				"λx:A. extended_sup(image(λn:num. «simpleInner»(u(n), x), 𝕌))")
			innerMeasurable := a.Have(
				"the inner integrals of the approximations are measurable",
				"∀n:num. extended_measurable(Ω, S, «simpleInner»(u(n)))",
				By(each))
			cross := set_product.InCross.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]())
			innerSup := a.Have(
				"the inner integral is the pointwise supremum of the inner integrals of the approximations",
				"∀x:A. x ∈ Ω ⇒ «inner»(h, x) = extended_sup(image(λn:num. «simpleInner»(u(n), x), 𝕌))",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					member := b.Assume()
					sections := b.TermAs[Fun2[Nat, B, Real]]("λn:num. λy:B. u(n, (x, y))")
					hx := b.TermAs[Fun[B, ExtendedNonnegReal]]("λy:B. h((x, y))")
					simple := b.Have(
						"all simple terms restrict to simple sections",
						"∀n:num. measure_simple(V, T, λy:B. u(n, (x, y)))",
						Derive(func(c *Argument) {
							n := c.FixAs[Nat]("n")
							c.Show(
								"use the simple section law",
								By(member, each.At(n)))
						}))
					sequence := b.Have(
						"both pointwise properties hold after fixing the first coordinate",
						"(∀n:num. ∀y:B. y ∈ V ⇒ u(n, (x, y)) ≤ u(n + 1, (x, y))) ∧ "+
							"(∀y:B. y ∈ V ⇒ h((x, y)) = extended_sup(image(λn:num. extended_of_real(u(n, (x, y))), 𝕌)))",
						BySets(member, parts[1], parts[3], cross))
					convergence := b.Have(
						"monotone convergence computes the section integral from simple integrals",
						"«inner»(h, x) = extended_sup(image(λn:num. measure_simple_integral(V, ν, λy:B. u(n, (x, y))), 𝕌))",
						By(factors, simple, sequence, nonneg_integral.MonotoneConvergenceSimple.At(V, T, ν, sections, hx)))
					termwise := b.Have(
						"the simple integrals equal the inner integrals of the embedded terms",
						"(λn:num. measure_simple_integral(V, ν, λy:B. u(n, (x, y)))) = (λn:num. «simpleInner»(u(n), x))",
						Funext(),
						Derive(func(c *Argument) {
							n := c.FixAs[Nat]("n")
							c.Show(
								"read the nonnegative integral of a simple section",
								By(
									factors,
									simple.At(n),
									nonneg_integral.NonnegIntegralSimple.At(V, T, ν,
										c.TermAs[Fun[B, Real]]("λy:B. u(n, (x, y))"))))
						}))
					b.Show(
						"both sequences have the same supremum",
						By(b.Simplified(convergence, Fwd(termwise))))
				}))
			growing := a.Have(
				"the inner integrals of the approximations increase pointwise on Ω",
				"∀n:num. ∀x:A. x ∈ Ω ⇒ «simpleInner»(u(n), x) ≤ «simpleInner»(u(n + 1), x)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.FixAs[A]("x")
					member := b.Assume()
					raise := b.Have(
						"the embedded terms increase on the second carrier",
						"∀y:B. y ∈ V ⇒ extended_of_real(u(n, (x, y))) ≤ extended_of_real(u(n + 1, (x, y)))",
						Derive(func(c *Argument) {
							c.FixAs[B]("y")
							inV := c.Assume()
							pair := c.TermAs[Prod[A, B]]("(x, y)")
							order := c.Have(
								"the points lie in the product carrier",
								"u(n, (x, y)) ≤ u(n + 1, (x, y))",
								BySets(member, inV, parts[1].At(n, pair), cross))
							c.Show(
								"the embedding preserves the order",
								By(
									order,
									extended_nonneg_real.OfRealMono.At(c.TermAs[Real]("u(n, (x, y))"),
										c.TermAs[Real]("u(n + 1, (x, y))"))))
						}))
					b.Show(
						"integrate the pointwise inequality over the section",
						By(
							raise,
							nonneg_integral.NonnegIntegralMono.At(V, T, ν,
								b.TermAs[Fun[B, ExtendedNonnegReal]]("λy:B. extended_of_real(u(n, (x, y)))"),
								b.TermAs[Fun[B, ExtendedNonnegReal]]("λy:B. extended_of_real(u(n + 1, (x, y)))"))))
				}))
			agree := a.Have(
				"the measurable supremum equals the inner integral on the first carrier",
				"∀x:A. x ∈ Ω ⇒ extended_sup(image(λn:num. «simpleInner»(u(n), x), 𝕌)) = «inner»(h, x)",
				By(innerSup))
			outer := a.Have(
				"monotone convergence writes the iterated integral as a supremum",
				"nonneg_integral(Ω, S, μ, «inner»(h)) = "+
					"extended_sup(image(λn:num. nonneg_integral(Ω, S, μ, «simpleInner»(u(n))), 𝕌))",
				By(
					left,
					innerMeasurable,
					growing,
					agree,
					nonneg_integral.MonotoneConvergence.At(Ω, S, μ, innerTerms),
					nonneg_integral.NonnegIntegralEqOn.At(Ω, S, μ, limit, inner)))
			joint := a.Have(
				"the product integral is the supremum of the simple approximating integrals",
				"nonneg_integral(set_cross(Ω, V), «P», «mass», h) = "+
					"extended_sup(image(λn:num. measure_simple_integral(set_cross(Ω, V), «mass», u(n)), 𝕌))",
				By(
					factors,
					parts[0],
					parts[1],
					parts[3],
					nonneg_integral.MonotoneConvergenceSimple.At(K, P, m, u, h)))
			terms := a.Have(
				"the approximating integrals agree term by term",
				"(λn:num. measure_simple_integral(set_cross(Ω, V), «mass», u(n))) = "+
					"(λn:num. nonneg_integral(Ω, S, μ, «simpleInner»(u(n))))",
				Funext(),
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"the simple approximating function satisfies the formula",
						By(
							factors,
							parts[0].At(n),
							each.At(n),
							nonneg_integral.NonnegIntegralSimple.At(K, P, m,
								b.TermAs[Fun[Prod[A, B], Real]]("u(n)"))))
				}))
			a.Show(
				"the inner integral is measurable and the limits agree",
				SplitConj(
					Case(
						"use the measurable supremum on the carrier",
						By(
							factors,
							innerMeasurable,
							agree,
							measurable_function.ExtendedMeasurableSup.At(Ω, S, innerTerms),
							At(measurableEqOn, Ω, S, limit, inner))),
					Case(
						"the two suprema agree",
						By(a.Simplified(joint, Fwd(terms)), outer))))
		})

		transport := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀V:set(B). " +
				"∀T:set(set(B)). " +
				"∀ν:(set(B) → extended_nonneg_real). " +
				"∀F:(A → B). " +
				"∀h:(B → extended_nonneg_real).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"measure_on(V, T, ν)",
				"measurable_map(Ω, S, V, T, F)",
				"∀E:set(B). E ∈ T ⇒ ν(E) = μ(preimage_on(Ω, F, E))",
				"extended_measurable(V, T, h)",
			},
			Conclusion: "extended_measurable(Ω, S, λx:A. h(F(x))) ∧ " +
				"nonneg_integral(V, T, ν, h) = nonneg_integral(Ω, S, μ, λx:A. h(F(x)))",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			V *Expr[Set[B]],
			T *Expr[Set[Set[B]]],
			ν *Arrow[Set[B], ExtendedNonnegReal],
			F *Arrow[A, B],
			h *Arrow[B, ExtendedNonnegReal],
			source, target, fmap, masses, measurable Fact,
		) {
			pulled := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. h(F(x))")
			pulledMeasurable := a.Have(
				"the pullback is measurable as a composition",
				"extended_measurable(Ω, S, λx:A. h(F(x)))",
				By(
					Normalized,
					fmap,
					measurable,
					functions.ComposeApply.At(h, F),
					measurable_function.ExtendedMeasurableDef.At(V, T, h),
					measurable_function.ExtendedMeasurableDef.At(Ω, S, pulled),
					measurable_space.MeasurableCompose.At(Ω, S, V, T, a.TermAs[Set[ExtendedNonnegReal]]("𝕌"),
						a.TermAs[Set[Set[ExtendedNonnegReal]]]("extended_borel"), F, h)))
			a.Show(
				"the pullback is measurable, and the change of variables gives the integral",
				By(
					pulledMeasurable,
					source,
					target,
					fmap,
					masses,
					measurable,
					nonneg_integral.NonnegIntegralPushforward.At(Ω, S, μ, V, T, ν, F, h)))
		})

		swapProduct := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀V:set(B). " +
				"∀T:set(set(B)). " +
				"∀ν:(set(B) → extended_nonneg_real).",
			Hypotheses: []string{"sigma_finite_on(Ω, S, μ)", "sigma_finite_on(V, T, ν)"},
			Conclusion: "measurable_map(set_cross(V, Ω), «reverseP», set_cross(Ω, V), «P», «swap») ∧ " +
				"image(«swap», set_cross(V, Ω)) = set_cross(Ω, V) ∧ " +
				"(∀E:set(prod(A, B)). " +
				"    E ∈ «P» ⇒ «mass»(E) = «reverseMass»(preimage_on(set_cross(V, Ω), «swap», E)))",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
			V *Expr[Set[B]], T *Expr[Set[Set[B]]], ν *Arrow[Set[B], ExtendedNonnegReal], first, second Fact) {
			K := a.TermAs[Set[Prod[A, B]]]("set_cross(Ω, V)")
			P := a.TermAs[Set[Set[Prod[A, B]]]]("«P»")
			Krev := a.TermAs[Set[Prod[B, A]]]("set_cross(V, Ω)")
			Prev := a.TermAs[Set[Set[Prod[B, A]]]]("«reverseP»")
			mrev := a.TermAs[Fun[Set[Prod[B, A]], ExtendedNonnegReal]]("«reverseMass»")
			swap := a.TermAs[Fun[Prod[B, A], Prod[A, B]]]("«swap»")
			factors := a.Have(
				"both sigma-finite factors are measures with sigma algebras",
				"measure_on(Ω, S, μ) ∧ measure_on(V, T, ν) ∧ sigma_algebra_on(Ω, S) ∧ sigma_algebra_on(V, T)",
				By(
					first,
					second,
					measure_space.SigmaFiniteDef.At(Ω, S, μ),
					measure_space.SigmaFiniteDef.At(V, T, ν),
					measure_space.MeasureOn.At(Ω, S, μ),
					measure_space.MeasureOn.At(V, T, ν)))
			subsets := a.Have(
				"each measurable factor lies in its carrier",
				"S ⊆ {s:set(A) | s ⊆ Ω} ∧ T ⊆ {t:set(B) | t ⊆ V}",
				By(factors, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S), sigma_algebra.SigmaAlgebraOnDef.At(V, T)))
			rectangles := a.Have(
				"the rectangles lie in their carriers and the swap pulls back a rectangle to the reverse rectangle",
				Statement{
					Binders:    "∀s:set(A). ∀t:set(B).",
					Hypotheses: []string{"s ∈ S", "t ∈ T"},
					Conclusion: "set_cross(s, t) ⊆ set_cross(Ω, V) ∧ " +
						"set_cross(t, s) ⊆ set_cross(V, Ω) ∧ " +
						"preimage_on(set_cross(V, Ω), «swap», set_cross(s, t)) = set_cross(t, s)",
				},
				Derive(func(b *Argument) {
					s := b.FixAs[Set[A]]("s")
					t := b.FixAs[Set[B]]("t")
					member := b.Assume()
					within := b.Have(
						"the factors lie in their carriers",
						"s ⊆ Ω ∧ t ⊆ V",
						BySets(subsets, member))
					carriers := b.Have(
						"take products in both orders",
						"set_cross(s, t) ⊆ set_cross(Ω, V) ∧ set_cross(t, s) ⊆ set_cross(V, Ω)",
						BySets(
							within,
							set_product.CrossSubsetIff.At(s, Ω, t, V),
							set_product.CrossSubsetIff.At(t, V, s, Ω)))
					identity := b.Have(
						"membership in the inverse image is membership in the reversed rectangle",
						"preimage_on(set_cross(V, Ω), «swap», set_cross(s, t)) = set_cross(t, s)",
						BySets(
							carriers,
							set_product.InCross.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]()),
							set_product.InCrossProjections.Inst(TypeBinder.BindA[B](), TypeBinder.BindB[A]())))
					b.Show(
						"the two inclusions and the inverse image identity",
						By(carriers, identity))
				}))
			onto := a.Have(
				"the swap maps the reverse carrier onto the target carrier",
				"image(«swap», set_cross(V, Ω)) = set_cross(Ω, V)",
				By(set_product.CrossSwap.At(Ω, V)))
			reversed := a.Have(
				"the reversed product is a measure",
				"measure_on(set_cross(V, Ω), «reverseP», «reverseMass»)",
				By(factors, first, ProductMeasureOn.At(V, T, ν, Ω, S, μ)))
			measurable := a.Have(
				"exchanging the coordinates is measurable",
				"measurable_map(set_cross(V, Ω), «reverseP», set_cross(Ω, V), «P», «swap»)",
				By(factors, measurable_space.ProductSigmaSwap.At(Ω, S, V, T)))
			targetSigma := a.Have(
				"the target product measurable sets form a sigma algebra",
				"sigma_algebra_on(set_cross(Ω, V), «P»)",
				By(factors, measurable_space.ProductSigmaProjections.At(Ω, S, V, T)))
			pushed := a.TermAs[Fun[Set[Prod[A, B]], ExtendedNonnegReal]]("«pushed»")
			pushMeasure := a.Have(
				"the pushforward of the reverse product is a measure on the target product",
				"measure_on(set_cross(Ω, V), «P», «pushed»)",
				By(
					reversed,
					targetSigma,
					measurable,
					measure_space.PushforwardMeasure.At(Krev, Prev, mrev, K, P, swap)))
			rectangleMass := a.Have(
				"the pushed measure has the product masses on rectangles",
				"∀s:set(A). ∀t:set(B). s ∈ S ∧ t ∈ T ⇒ «pushed»(set_cross(s, t)) = μ(s) * ν(t)",
				Derive(func(b *Argument) {
					s := b.FixAs[Set[A]]("s")
					t := b.FixAs[Set[B]]("t")
					member := b.Assume()
					b.Show(
						"the inverse image has the reverse product mass",
						By(
							member,
							factors,
							rectangles.At(s, t),
							measure_space.MeasureOn.At(Ω, S, μ),
							ProductMeasureRectangle.At(V, T, ν, μ, t, s),
							extended_nonneg_real.MulComm.At(ν.Apply(t), μ.Apply(s)),
							measure_space.PushforwardMeasureDef.At(
								Krev, mrev, swap, b.TermAs[Set[Prod[A, B]]]("set_cross(s, t)"))))
				}))
			masses := a.Have(
				"product measure uniqueness identifies the pushforward on all product events",
				"∀E:set(prod(A, B)). E ∈ «P» ⇒ «mass»(E) = «reverseMass»(preimage_on(set_cross(V, Ω), «swap», E))",
				Derive(func(b *Argument) {
					E := b.FixAs[Set[Prod[A, B]]]("E")
					event := b.Assume()
					unique := b.Have(
						"the pushed measure agrees with the target product measure",
						"«pushed»(E) = «mass»(E)",
						By(
							first,
							second,
							pushMeasure,
							rectangleMass,
							event,
							ProductMeasureUnique.At(Ω, S, μ, V, T, ν, pushed, E)))
					b.Show(
						"read the definition of the pushforward",
						By(unique, measure_space.PushforwardMeasureDef.At(Krev, mrev, swap, E)))
				}))
			a.Show(
				"the swap is measurable, onto and preserves product masses",
				By(measurable, onto, masses))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			V *Expr[Set[B]],
			T *Expr[Set[Set[B]]],
			ν *Arrow[Set[B], ExtendedNonnegReal],
			f *Arrow2[A, B, ExtendedNonnegReal],
			first, second, measurable Fact,
		) {
			K := a.TermAs[Set[Prod[A, B]]]("set_cross(Ω, V)")
			P := a.TermAs[Set[Set[Prod[A, B]]]]("«P»")
			m := a.TermAs[Fun[Set[Prod[A, B]], ExtendedNonnegReal]]("«mass»")
			Krev := a.TermAs[Set[Prod[B, A]]]("set_cross(V, Ω)")
			Prev := a.TermAs[Set[Set[Prod[B, A]]]]("«reverseP»")
			mrev := a.TermAs[Fun[Set[Prod[B, A]], ExtendedNonnegReal]]("«reverseMass»")
			swap := a.TermAs[Fun[Prod[B, A], Prod[A, B]]]("«swap»")
			h := a.TermAs[Fun[Prod[A, B], ExtendedNonnegReal]]("«uncurried»")
			hrev := a.TermAs[Fun[Prod[B, A], ExtendedNonnegReal]]("«reversed»")
			factors := a.Have(
				"both factors and both products are measures",
				"measure_on(Ω, S, μ) ∧ "+
					"measure_on(V, T, ν) ∧ "+
					"measure_on(set_cross(Ω, V), «P», «mass») ∧ "+
					"measure_on(set_cross(V, Ω), «reverseP», «reverseMass»)",
				By(
					first,
					second,
					measure_space.SigmaFiniteDef.At(Ω, S, μ),
					measure_space.SigmaFiniteDef.At(V, T, ν),
					ProductMeasureOn.At(Ω, S, μ, V, T, ν),
					ProductMeasureOn.At(V, T, ν, Ω, S, μ)))
			swapping := a.Have(
				"the swap is measurable and onto, and preserves product masses",
				"measurable_map(set_cross(V, Ω), «reverseP», set_cross(Ω, V), «P», «swap») ∧ "+
					"image(«swap», set_cross(V, Ω)) = set_cross(Ω, V) ∧ "+
					"(∀E:set(prod(A, B)). "+
					"    E ∈ «P» ⇒ «mass»(E) = «reverseMass»(preimage_on(set_cross(V, Ω), «swap», E)))",
				By(first, second, At(swapProduct, Ω, S, μ, V, T, ν)))
			transfer := a.Have(
				"the product integral is invariant under exchanging the factors and coordinates",
				"extended_measurable(set_cross(V, Ω), «reverseP», λq:prod(B, A). «uncurried»(«swap»(q))) ∧ "+
					"nonneg_integral(set_cross(Ω, V), «P», «mass», «uncurried») = "+
					"nonneg_integral(set_cross(V, Ω), "+
					"    «reverseP», "+
					"    «reverseMass», "+
					"    λq:prod(B, A). «uncurried»(«swap»(q)))",
				By(
					factors,
					swapping,
					measurable,
					At(ctx.AtTypeVars(transport, TypeBinder.BindA[Prod[B, A]](), TypeBinder.BindB[Prod[A, B]]()),
						Krev, Prev, mrev, K, P, m, swap, h)))
			reverse := a.Have(
				"pulling back the uncurried function exchanges its coordinates",
				"(λq:prod(B, A). «uncurried»(«swap»(q))) = «reversed»",
				Funext(),
				By(Normalized, pairs.Fst, pairs.Snd))
			innerA := a.Have(
				"the first inner integral reads the original curried function",
				"«inner»(«uncurried») = «firstInner»",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.Show(
						"the projections of a pair are its two coordinates",
						Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
						Basic())
				}))
			innerB := a.Have(
				"the second inner integral reads the original curried function",
				"(λy:B. nonneg_integral(Ω, S, μ, λx:A. «reversed»((y, x)))) = «secondInner»",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[B]("y")
					b.Show(
						"the reverse projections restore the two coordinates",
						Simp(
							Fwd(pairs.Fst.Inst(TypeBinder.BindA[B](), TypeBinder.BindB[A]())),
							Fwd(pairs.Snd.Inst(TypeBinder.BindA[B](), TypeBinder.BindB[A]()))),
						Refl())
				}))
			firstOrderIdentity := a.Have(
				"integrating the second variable first gives a measurable function and the same integral",
				"extended_measurable(Ω, S, «firstInner») ∧ "+
					"nonneg_integral(set_cross(Ω, V), «P», «mass», «uncurried») = "+
					"nonneg_integral(Ω, S, μ, «firstInner»)",
				By(factors, second, measurable, innerA, At(firstOrder, Ω, S, μ, V, T, ν, h)))
			reverseOrderIdentity := a.Have(
				"integrating the first variable first gives the reversed product integral",
				"extended_measurable(V, T, «secondInner») ∧ "+
					"nonneg_integral(set_cross(V, Ω), «reverseP», «reverseMass», «reversed») = "+
					"nonneg_integral(V, T, ν, «secondInner»)",
				By(
					factors,
					first,
					transfer,
					reverse,
					innerB,
					At(
						ctx.AtTypeVars(firstOrder, TypeBinder.BindA[B](), TypeBinder.BindB[A]()), V, T, ν, Ω, S, μ, hrev)))
			a.Show(
				"both inner integrals are measurable and either order gives the product integral",
				By(firstOrderIdentity, reverseOrderIdentity, transfer, reverse))
		})
	}),
})}

// ProductIntegral applies Tonelli to the positive and negative parts. The
// finite outer integrals identify the re-embedded real section values almost
// everywhere, and the integral of their difference gives each iteration.
var ProductIntegral = productIntegralThm{family.Add(registry.ProofEntry{
	Name: "ProductIntegral",
	Key:  "prop_78d0aecd2ee481fa",
	Reading: "Fubini. The inner integral is a total function: where a " +
		"section is not integrable it takes the integral's conventional " +
		"value, on a null set of points, which the outer integral does not see.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀ν:(set(B) → extended_nonneg_real). " +
			"∀f:(A → B → real).",
		Hypotheses: []string{
			"sigma_finite_on(Ω, S, μ)",
			"sigma_finite_on(V, T, ν)",
			"real_integrable(set_cross(Ω, V), " +
				"    product_sigma(Ω, S, V, T), " +
				"    product_measure(Ω, S, μ, ν), " +
				"    λp:prod(A, B). f(fst(p), snd(p)))",
		},
		Conclusion: "measure_integral(set_cross(Ω, V), " +
			"    product_sigma(Ω, S, V, T), " +
			"    product_measure(Ω, S, μ, ν), " +
			"    λp:prod(A, B). f(fst(p), snd(p))) = " +
			"measure_integral(Ω, S, μ, λx:A. measure_integral(V, T, ν, λy:B. f(x, y))) ∧ " +
			"measure_integral(set_cross(Ω, V), " +
			"    product_sigma(Ω, S, V, T), " +
			"    product_measure(Ω, S, μ, ν), " +
			"    λp:prod(A, B). f(fst(p), snd(p))) = " +
			"measure_integral(V, T, ν, λy:B. measure_integral(Ω, S, μ, λx:A. f(x, y)))",
		Abbrev: Abbrev{
			{Name: "productSigma", Text: "product_sigma(Ω, S, V, T)"},
			{Name: "productMass", Text: "product_measure(Ω, S, μ, ν)"},
			{Name: "productFunction", Text: "λp:prod(A, B). f(fst(p), snd(p))"},
			{Name: "positiveProduct", Text: "λp:prod(A, B). extended_of_real(«productFunction»(p))"},
			{Name: "negativeProduct", Text: "λp:prod(A, B). extended_of_real(-«productFunction»(p))"},
			{Name: "positiveMass", Text: "nonneg_integral(set_cross(Ω, V), " +
				"    «productSigma», " +
				"    «productMass», " +
				"    «positiveProduct»)"},
			{Name: "negativeMass", Text: "nonneg_integral(set_cross(Ω, V), " +
				"    «productSigma», " +
				"    «productMass», " +
				"    «negativeProduct»)"},
			{Name: "firstPositive", Text: "λx:A. nonneg_integral(V, T, ν, λy:B. extended_of_real(f(x, y)))"},
			{Name: "secondPositive", Text: "λy:B. nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x, y)))"},
			{Name: "firstNegative", Text: "λx:A. nonneg_integral(V, T, ν, λy:B. extended_of_real(-f(x, y)))"},
			{Name: "secondNegative", Text: "λy:B. nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-f(x, y)))"},
			{Name: "firstSection", Text: "λx:A. measure_integral(V, T, ν, λy:B. f(x, y))"},
			{Name: "secondSection", Text: "λy:B. measure_integral(Ω, S, μ, λx:A. f(x, y))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		finiteReading := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀g:(A → extended_nonneg_real).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"extended_measurable(Ω, S, g)",
				"nonneg_integral(Ω, S, μ, g) ≠ extended_infinity",
			},
			Conclusion: "real_measurable(Ω, S, λx:A. extended_to_real(g(x))) ∧ " +
				"(∀x:A. x ∈ Ω ⇒ &0 ≤ extended_to_real(g(x))) ∧ " +
				"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(extended_to_real(g(x)))) = " +
				"nonneg_integral(Ω, S, μ, g)",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
			g *Arrow[A, ExtendedNonnegReal], measure, measurable, finite Fact) {
			sigma := a.Have(
				"the measurable sets form a sigma algebra",
				"sigma_algebra_on(Ω, S)",
				By(measure, measure_space.MeasureOn.At(Ω, S, μ)))
			finiteAE := a.Have(
				"the function is finite almost everywhere",
				"measure_ae(Ω, S, μ, λx:A. g(x) ≠ extended_infinity)",
				By(measure, measurable, finite, nonneg_integral.FiniteIntegralAEFinite.At(Ω, S, μ, g)))
			read := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(extended_to_real(g(x)))")
			finiteness := a.TermAs[Fun[A, Bool]]("λx:A. g(x) ≠ extended_infinity")
			agreement := a.TermAs[Fun[A, Bool]]("λx:A. extended_of_real(extended_to_real(g(x))) = g(x)")
			pointwise := a.Have(
				"a finite value embeds back as itself",
				"∀x:A. x ∈ Ω ∧ g(x) ≠ extended_infinity ⇒ extended_of_real(extended_to_real(g(x))) = g(x)",
				By(extended_nonneg_real.OfRealToReal))
			equalAE := a.Have(
				"the re-embedded reading agrees with the function almost everywhere",
				"measure_ae_eq(Ω, S, μ, λx:A. extended_of_real(extended_to_real(g(x))), g)",
				By(
					finiteAE,
					pointwise,
					measure_space.AEMono.At(Ω, S, μ, finiteness, agreement),
					measure_space.AEEqualDef.At(Ω, S, μ, read, g)))
			a.Show(
				"the real reading is measurable and nonnegative, and re-embedding preserves the integral",
				By(
					sigma,
					measurable,
					measure,
					equalAE,
					measurable_function.ExtendedMeasurableToReal.At(Ω, S, g),
					extended_nonneg_real.ToRealNonneg,
					nonneg_integral.NonnegIntegralAE.At(Ω, S, μ, read, g)))
		})

		integralDifference := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀h:(A → real). " +
				"∀p q:(A → extended_nonneg_real).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"extended_measurable(Ω, S, p)",
				"extended_measurable(Ω, S, q)",
				"nonneg_integral(Ω, S, μ, p) ≠ extended_infinity",
				"nonneg_integral(Ω, S, μ, q) ≠ extended_infinity",
				"∀x:A. x ∈ Ω ⇒ h(x) = extended_to_real(p(x)) - extended_to_real(q(x))",
			},
			Conclusion: "measure_integral(Ω, S, μ, h) = " +
				"extended_to_real(nonneg_integral(Ω, S, μ, p)) - extended_to_real(nonneg_integral(Ω, S, μ, q))",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			h *Arrow[A, Real],
			p, q *Arrow[A, ExtendedNonnegReal],
			measure, pMeas, qMeas, pFinite, qFinite, difference Fact,
		) {
			pr := a.TermAs[Fun[A, Real]]("λx:A. extended_to_real(p(x))")
			qr := a.TermAs[Fun[A, Real]]("λx:A. extended_to_real(q(x))")
			positive := a.Have(
				"the positive integral comes from a nonnegative real measurable function",
				"real_measurable(Ω, S, λx:A. extended_to_real(p(x))) ∧ "+
					"(∀x:A. x ∈ Ω ⇒ &0 ≤ extended_to_real(p(x))) ∧ "+
					"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(extended_to_real(p(x)))) = "+
					"nonneg_integral(Ω, S, μ, p)",
				By(measure, pMeas, pFinite, At(finiteReading, Ω, S, μ, p)))
			negative := a.Have(
				"the negative integral comes from a nonnegative real measurable function",
				"real_measurable(Ω, S, λx:A. extended_to_real(q(x))) ∧ "+
					"(∀x:A. x ∈ Ω ⇒ &0 ≤ extended_to_real(q(x))) ∧ "+
					"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(extended_to_real(q(x)))) = "+
					"nonneg_integral(Ω, S, μ, q)",
				By(measure, qMeas, qFinite, At(finiteReading, Ω, S, μ, q)))
			a.Show(
				"integrate the difference of the nonnegative real readings",
				By(
					measure,
					positive,
					negative,
					pFinite,
					qFinite,
					difference,
					measure_integral.IntegralNonnegDifference.At(Ω, S, μ, h, pr, qr)))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
			V *Expr[Set[B]], T *Expr[Set[Set[B]]], ν *Arrow[Set[B], ExtendedNonnegReal],
			f *Arrow2[A, B, Real], first, second, integrable Fact,
		) {
			carrier := a.TermAs[Set[Prod[A, B]]]("set_cross(Ω, V)")
			productSigma := a.TermAs[Set[Set[Prod[A, B]]]]("«productSigma»")
			productMass := a.TermAs[Fun[Set[Prod[A, B]], ExtendedNonnegReal]]("«productMass»")
			uncurried := a.TermAs[Fun[Prod[A, B], Real]]("«productFunction»")
			negated := a.TermAs[Fun[Prod[A, B], Real]]("λz:prod(A, B). -«productFunction»(z)")
			factors := a.Have(
				"both sigma-finite factors are measures",
				"measure_on(Ω, S, μ) ∧ measure_on(V, T, ν)",
				By(
					first,
					second,
					measure_space.SigmaFiniteDef.At(Ω, S, μ),
					measure_space.SigmaFiniteDef.At(V, T, ν)))
			sigma := a.Have(
				"the product measure is defined on its product sigma algebra",
				"sigma_algebra_on(set_cross(Ω, V), «productSigma»)",
				By(
					factors,
					measure_space.MeasureOn.At(Ω, S, μ),
					measure_space.MeasureOn.At(V, T, ν),
					measurable_space.ProductSigmaProjections.At(Ω, S, V, T)))
			measurable := a.Have(
				"the integrable product function is measurable",
				"real_measurable(set_cross(Ω, V), «productSigma», «productFunction»)",
				By(
					integrable,
					measure_integral.RealIntegrableDef.At(carrier, productSigma, productMass, uncurried)))
			negativeMeasurable := a.Have(
				"its negative is also measurable",
				"real_measurable(set_cross(Ω, V), «productSigma», λz:prod(A, B). -«productFunction»(z))",
				By(sigma, measurable, measurable_function.RealMeasurableNeg.At(carrier, productSigma, uncurried)))
			embeddings := a.Have(
				"both parts embed as measurable nonnegative functions",
				"extended_measurable(set_cross(Ω, V), «productSigma», «positiveProduct») ∧ "+
					"extended_measurable(set_cross(Ω, V), «productSigma», «negativeProduct»)",
				By(
					sigma,
					measurable,
					negativeMeasurable,
					measurable_function.ExtendedMeasurableOfReal.At(carrier, productSigma, uncurried),
					measurable_function.ExtendedMeasurableOfReal.At(carrier, productSigma, negated)))
			finite := a.Have(
				"the product integrals of both parts are finite",
				"«positiveMass» ≠ extended_infinity ∧ «negativeMass» ≠ extended_infinity",
				By(
					integrable,
					measure_integral.IntegrablePartsFinite.At(carrier, productSigma, productMass, uncurried)))
			positive := a.Have(
				"Tonelli identifies the two iterated integrals of the positive part",
				"extended_measurable(Ω, S, «firstPositive») ∧ "+
					"extended_measurable(V, T, «secondPositive») ∧ "+
					"«positiveMass» = nonneg_integral(Ω, S, μ, «firstPositive») ∧ "+
					"«positiveMass» = nonneg_integral(V, T, ν, «secondPositive»)",
				By(
					first,
					second,
					embeddings,
					ProductNonnegIntegral.At(Ω, S, μ, V, T, ν,
						a.TermAs[Fun2[A, B, ExtendedNonnegReal]]("λx:A. λy:B. extended_of_real(f(x, y))"))))
			negative := a.Have(
				"Tonelli also identifies the iterated integrals of the negative part",
				"extended_measurable(Ω, S, «firstNegative») ∧ "+
					"extended_measurable(V, T, «secondNegative») ∧ "+
					"«negativeMass» = nonneg_integral(Ω, S, μ, «firstNegative») ∧ "+
					"«negativeMass» = nonneg_integral(V, T, ν, «secondNegative»)",
				By(
					first,
					second,
					embeddings,
					ProductNonnegIntegral.At(Ω, S, μ, V, T, ν,
						a.TermAs[Fun2[A, B, ExtendedNonnegReal]]("λx:A. λy:B. extended_of_real(-f(x, y))"))))
			firstSections := a.Have(
				"integrating the second variable first reads the difference of the two parts",
				Statement{
					Binders:    "∀x:A.",
					Hypotheses: []string{"x ∈ Ω"},
					Conclusion: "«firstSection»(x) = " +
						"extended_to_real(«firstPositive»(x)) - extended_to_real(«firstNegative»(x))",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.Show(
						"read the section's real integral",
						By(measure_integral.RealIntegralDef.At(V, T, ν, b.TermAs[Fun[B, Real]]("λy:B. f(x, y)"))))
				}))
			secondSections := a.Have(
				"integrating the first variable first reads the difference of the two parts",
				Statement{
					Binders:    "∀y:B.",
					Hypotheses: []string{"y ∈ V"},
					Conclusion: "«secondSection»(y) = " +
						"extended_to_real(«secondPositive»(y)) - extended_to_real(«secondNegative»(y))",
				},
				Derive(func(b *Argument) {
					b.FixAs[B]("y")
					b.Show(
						"read the other section's real integral",
						By(measure_integral.RealIntegralDef.At(Ω, S, μ, b.TermAs[Fun[A, Real]]("λx:A. f(x, y)"))))
				}))
			product := a.Have(
				"the product integral is the difference of its two finite readings",
				"measure_integral(set_cross(Ω, V), «productSigma», «productMass», «productFunction») = "+
					"extended_to_real(«positiveMass») - extended_to_real(«negativeMass»)",
				By(measure_integral.RealIntegralDef.At(carrier, productSigma, productMass, uncurried)))
			a.Show(
				"both integrations give the same difference",
				SplitConj(
					Case(
						"integrate the second variable first",
						By(
							factors,
							finite,
							positive,
							negative,
							firstSections,
							product,
							At(integralDifference, Ω, S, μ,
								a.TermAs[Fun[A, Real]]("«firstSection»"), a.TermAs[Fun[A, ExtendedNonnegReal]]("«firstPositive»"),
								a.TermAs[Fun[A, ExtendedNonnegReal]]("«firstNegative»")))),
					Case(
						"integrate the first variable first",
						By(
							factors,
							finite,
							positive,
							negative,
							secondSections,
							product,
							At(ctx.AtTypeVars(integralDifference, TypeBinder.BindA[B]()), V, T, ν,
								a.TermAs[Fun[B, Real]]("«secondSection»"), a.TermAs[Fun[B, ExtendedNonnegReal]]("«secondPositive»"),
								a.TermAs[Fun[B, ExtendedNonnegReal]]("«secondNegative»"))))))
		})
	}),
})}
