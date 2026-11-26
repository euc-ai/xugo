// approximation.go — every measurable function with values in [0, ∞] is
// the increasing supremum of simple functions. The approximation at level
// n rounds the truncation min(f, n) down to the grid of step 2⁻ⁿ: an
// integer part of a bounded measurable real function, which is what makes
// it simple.

package measure_simple

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/rational"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// SimpleApproximation — every measurable [0, ∞]-valued function on a
// measurable space is the pointwise supremum of an increasing sequence of
// simple functions lying below it. Truncate f at n, reading the value n
// where f is infinite, to the real hₙ(x); round 2ⁿ·hₙ(x) down to an integer
// kₙ(x) and take sₙ(x) = kₙ(x)/2ⁿ. Each hₙ is measurable (its rays are
// empty, all of Ω, or rays of f) and at most n, so sₙ is simple; it lies
// below hₙ, hence below f. Raising the cap and halving the step at least
// doubles the integer part, so the sₙ increase. A real level t below f(x)
// lies, from some n on, a fixed margin below hₙ(x), and the step 2⁻ⁿ
// eventually falls under that margin, so some sₙ(x) passes t: the supremum
// of the sₙ(x) is f(x), infinite or not.
var SimpleApproximation = simpleApproximationThm{family.Add(registry.ProofEntry{
	Name: "SimpleApproximation",
	Key:  "prop_ef87838da12778b2",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → extended_nonneg_real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"extended_measurable(Ω, S, f)",
		},
		Conclusion: "∃s:(num → A → real). " +
			"    (∀n:num. measure_simple(Ω, S, s(n))) ∧ " +
			"    (∀n:num. ∀x:A. x ∈ Ω ⇒ s(n, x) ≤ s(n + 1, x)) ∧ " +
			"    (∀n:num. ∀x:A. x ∈ Ω ⇒ extended_of_real(s(n, x)) ≤ f(x)) ∧ " +
			"    (∀x:A. x ∈ Ω ⇒ f(x) = extended_sup(image(λn:num. extended_of_real(s(n, x)), 𝕌)))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		f *Arrow[A, ExtendedNonnegReal],
		sigma, measurable Fact,
	) {
		two := a.TermAs[Real]("&2")
		_, truncation := a.LetAs[Fun[Nat, Fun[A, Real]]](
			"h",
			"λn:num. λx:A. COND(f(x) = extended_infinity, &n, min(&n, extended_to_real(f(x))))")
		atInfinity := a.Have(
			"where f is infinite, hₙ is n",
			"∀n:num. ∀x:A. f(x) = extended_infinity ⇒ h(n, x) = &n",
			By(truncation))
		atFinite := a.Have(
			"where f is finite, hₙ is the smaller of n and the value of f",
			"∀n:num. ∀x:A. f(x) ≠ extended_infinity ⇒ h(n, x) = min(&n, extended_to_real(f(x)))",
			By(truncation))
		bounds := a.Have(
			"hₙ lies between 0 and n",
			"∀n:num. ∀x:A. &0 ≤ h(n, x) ∧ h(n, x) ≤ &n",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				value := b.TermAs[Real]("extended_to_real(f(x))")
				ceiling := b.TermAs[Real]("&n")
				b.Show(
					"n is not negative, and neither is the value of f",
					By(
						Normalized,
						atInfinity.At(n, x),
						atFinite.At(n, x),
						extended_nonneg_real.ToRealNonneg.At(f.Apply(x)),
						real_order_ring.NumNonneg.At(n),
						real_order_ring.LessEqRefl.At(ceiling),
						real_sup_inf.LessEqMin.At(ceiling, value, b.TermAs[Real]("&0")),
						real_sup_inf.MinLowerBound.At(ceiling, value)))
			}))
		capped := a.Have(
			"hₙ lies below f",
			"∀n:num. ∀x:A. extended_of_real(h(n, x)) ≤ f(x)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				value := b.TermAs[Real]("extended_to_real(f(x))")
				b.Show(
					"everything lies below ∞, and min(n, r) lies below r",
					By(
						Normalized,
						atInfinity.At(n, x),
						atFinite.At(n, x),
						extended_nonneg_real.LeInfinity.At(b.TermAs[ExtendedNonnegReal]("extended_of_real(h(n, x))")),
						extended_nonneg_real.OfRealToReal.At(f.Apply(x)),
						extended_nonneg_real.ToRealNonneg.At(f.Apply(x)),
						real_sup_inf.MinLowerBound.At(b.TermAs[Real]("&n"), value),
						extended_nonneg_real.OfRealLe.At(b.TermAs[Real]("h(n, x)"), value)))
			}))
		raised := a.Have(
			"hₙ increases with n",
			"∀n:num. ∀x:A. h(n, x) ≤ h(n + 1, x)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				next := b.TermAs[Nat]("n + 1")
				b.Cases(b.Term("f(x) = extended_infinity"))
				b.When(
					"where f is infinite, hₙ is n",
					func(c *Argument, infinite Fact) {
						c.Show(
							"and n ≤ n + 1",
							ByArith(infinite, atInfinity.At(n, x), atInfinity.At(next, x)))
					})
				b.Otherwise(
					"where f is finite, raising the cap from n to n + 1 lowers nothing",
					func(c *Argument, finite Fact) {
						value := c.TermAs[Real]("extended_to_real(f(x))")
						c.Show(
							"min(n, r) ≤ min(n + 1, r)",
							ByArith(
								finite,
								atFinite.At(n, x),
								atFinite.At(next, x),
								real_sup_inf.LessEqMin.At(
									c.TermAs[Real]("&(n + 1)"),
									value,
									c.TermAs[Real]("min(&n, extended_to_real(f(x)))")),
								real_sup_inf.MinLowerBound.At(c.TermAs[Real]("&n"), value)))
					})
			}))
		levels := a.Have(
			"t lies below hₙ(x) exactly when t < n and t lies below f(x) or below 0",
			"∀n:num. ∀x:A. ∀t:real. t < h(n, x) ⇔ t < &n ∧ (t < &0 ∨ extended_of_real(t) < f(x))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				t := b.FixAs[Real]("t")
				level := b.TermAs[ExtendedNonnegReal]("extended_of_real(t)")
				infinity := b.TermAs[ExtendedNonnegReal]("extended_infinity")
				b.Cases(b.Term("f(x) = extended_infinity"))
				b.When(
					"where f is infinite, hₙ is n and every real lies below f",
					func(c *Argument, infinite Fact) {
						c.Show(
							"the image of t is finite, so it lies strictly below ∞",
							By(
								Normalized,
								infinite,
								atInfinity.At(n, x),
								extended_nonneg_real.LtIffNotLe.At(level, infinity),
								extended_nonneg_real.LeInfinity.At(level),
								extended_nonneg_real.LeAntisym.At(level, infinity),
								extended_nonneg_real.OfRealNotInfinity.At(t)))
					})
				b.Otherwise(
					"where f is finite with value r, hₙ is min(n, r)",
					func(c *Argument, finite Fact) {
						value := c.TermAs[Real]("extended_to_real(f(x))")
						image := c.Have(
							"f(x) is the image of its value r, which is not negative",
							"f(x) = extended_of_real(extended_to_real(f(x))) ∧ &0 ≤ extended_to_real(f(x))",
							By(
								finite,
								extended_nonneg_real.OfRealToReal.At(f.Apply(x)),
								extended_nonneg_real.ToRealNonneg.At(f.Apply(x))))
						reals := c.Have(
							"t < min(n, r) exactly when t < n and t lies below 0 or below a positive r",
							"t < min(&n, extended_to_real(f(x))) ⇔ "+
								"t < &n ∧ (t < &0 ∨ t < extended_to_real(f(x)) ∧ &0 < extended_to_real(f(x)))",
							ByArith(image, real_sup_inf.LessThanMin.At(c.TermAs[Real]("&n"), value, t)))
						c.Show(
							"and the image of t lies below the image of r exactly when t < r and r is positive",
							By(finite, image, reals, atFinite.At(n, x), extended_nonneg_real.OfRealLt.At(t, value)))
					})
			}))
		rays := a.Have(
			"the rays of f are measurable",
			"∀t:real. {x:A | x ∈ Ω ∧ extended_of_real(t) < f(x)} ∈ S",
			By(sigma, measurable, measurable_function.ExtendedMeasurableIffRay.At(Ω, S, f)))
		truncationRays := a.Have(
			"so are the rays of hₙ: each is empty, all of Ω, or a ray of f",
			"∀n:num. ∀c:real. {x:A | x ∈ Ω ∧ c < h(n, x)} ∈ S",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				c := b.FixAs[Real]("c")
				b.Cases(b.Term("c < &n"))
				b.When(
					"below n, the ray depends on the sign of c",
					func(d *Argument, belowCap Fact) {
						d.Cases(d.Term("c < &0"))
						d.When(
							"below 0, hₙ exceeds c everywhere",
							func(e *Argument, negative Fact) {
								whole := e.Have(
									"so the ray is Ω",
									"{x:A | x ∈ Ω ∧ c < h(n, x)} = Ω",
									BySets(levels, belowCap, negative))
								e.Show(
									"and the carrier is measurable",
									By(whole, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
							})
						d.Otherwise(
							"between 0 and n, hₙ exceeds c exactly where f does",
							func(e *Argument, nonnegative Fact) {
								same := e.Have(
									"so the ray is the ray of f at c",
									"{x:A | x ∈ Ω ∧ c < h(n, x)} = {x:A | x ∈ Ω ∧ extended_of_real(c) < f(x)}",
									BySets(levels, belowCap, nonnegative))
								e.Show(
									"which is measurable",
									By(rays.At(c), same))
							})
					})
				b.Otherwise(
					"at or above n, hₙ exceeds c nowhere",
					func(d *Argument, aboveCap Fact) {
						empty := d.Have(
							"so the ray is empty",
							"{x:A | x ∈ Ω ∧ c < h(n, x)} = ∅",
							BySets(levels, aboveCap))
						d.Show(
							"and the empty set is measurable",
							By(empty, sigma, sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
					})
			}))
		truncationMeasurable := a.Have(
			"each hₙ is measurable",
			"∀n:num. real_measurable(Ω, S, h(n))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"upper rays decide measurability",
					By(
						truncationRays.At(n),
						sigma,
						measurable_function.RealMeasurableIffRay.At(Ω, S, b.TermAs[Fun[A, Real]]("h(n)"))))
			}))

		positive := a.Have(
			"every 2ⁿ is positive",
			"∀n:num. &0 < &(2 ^ n)",
			a.ForEach(func(n *Expr[Nat]) Action {
				return ByArith(real_pow.PowPos.At(two, n))
			}))
		parts := a.Have(
			"2ⁿ·hₙ(x) has an integer part at every n and x",
			"∀n:num. ∀x:A. ∃m:num. &m ≤ &(2 ^ n) * h(n, x) ∧ &(2 ^ n) * h(n, x) < &m + &1",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				scaledNonneg := b.Have(
					"2ⁿ·hₙ(x) is not negative",
					"&0 ≤ &(2 ^ n) * h(n, x)",
					ByArith(bounds.At(n, x), positive.At(n)))
				b.Show(
					"so it has an integer part",
					By(scaledNonneg, rational.NonnegIntegerPart.At(b.TermAs[Real]("&(2 ^ n) * h(n, x)"))))
			}))
		_, integerPart := a.ObtainAs[Fun[Nat, Fun[A, Nat]]](
			"choose one, kₙ(x), at every n and x",
			"∃k:(num → A → num). ∀n:num. ∀x:A. "+
				"    &k(n, x) ≤ &(2 ^ n) * h(n, x) ∧ &(2 ^ n) * h(n, x) < &k(n, x) + &1",
			By(parts))

		simple := a.Have(
			"each sₙ = kₙ/2ⁿ is simple: the integer part of the measurable 2ⁿ·hₙ, at most n·2ⁿ, over 2ⁿ",
			"∀n:num. measure_simple(Ω, S, λx:A. &k(n, x) / &(2 ^ n))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				scale := b.TermAs[Real]("&(2 ^ n)")
				bounded := b.Have(
					"2ⁿ·hₙ is at most n·2ⁿ",
					"∀x:A. &(2 ^ n) * h(n, x) ≤ &(n * 2 ^ n)",
					b.ForEach(func(x *Expr[A]) Action {
						return ByArith(bounds.At(n, x), positive.At(n))
					}))
				b.Show(
					"so its integer part over 2ⁿ is simple",
					By(
						bounded,
						integerPart.At(n),
						positive.At(n),
						truncationMeasurable.At(n),
						sigma,
						measurable_function.RealMeasurableScale.At(Ω, S, b.TermAs[Fun[A, Real]]("h(n)"), scale),
						IntegerPartSimple.At(
							Ω,
							S,
							b.TermAs[Fun[A, Real]]("λx:A. &(2 ^ n) * h(n, x)"),
							b.TermAs[Fun[A, Nat]]("k(n)"),
							b.TermAs[Nat]("n * 2 ^ n"),
							scale)))
			}))
		below := a.Have(
			"each sₙ lies below f",
			"∀n:num. ∀x:A. extended_of_real(&k(n, x) / &(2 ^ n)) ≤ f(x)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				approximation := b.TermAs[Real]("&k(n, x) / &(2 ^ n)")
				truncated := b.TermAs[Real]("h(n, x)")
				underCap := b.Have(
					"kₙ(x)/2ⁿ ≤ hₙ(x)",
					"&k(n, x) / &(2 ^ n) ≤ h(n, x)",
					ByArith(integerPart.At(n, x), positive.At(n)))
				b.Show(
					"and hₙ lies below f",
					By(
						underCap,
						capped.At(n, x),
						bounds.At(n, x),
						extended_nonneg_real.OfRealLe.At(approximation, truncated),
						extended_nonneg_real.LeTrans.At(
							b.TermAs[ExtendedNonnegReal]("extended_of_real(&k(n, x) / &(2 ^ n))"),
							b.TermAs[ExtendedNonnegReal]("extended_of_real(h(n, x))"),
							f.Apply(x))))
			}))
		increasing := a.Have(
			"the sₙ increase with n",
			"∀n:num. ∀x:A. &k(n, x) / &(2 ^ n) ≤ &k(n + 1, x) / &(2 ^ (n + 1))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				next := b.TermAs[Nat]("n + 1")
				scaledRaise := b.Have(
					"2ⁿ·hₙ(x) ≤ 2ⁿ·hₙ₊₁(x)",
					"&(2 ^ n) * h(n, x) ≤ &(2 ^ n) * h(n + 1, x)",
					ByArith(raised.At(n, x), positive.At(n)))
				doubled := b.Have(
					"so the integer part at n + 1 is at least twice the one at n",
					"2 * k(n, x) ≤ k(n + 1, x)",
					ByArith(
						scaledRaise,
						integerPart.At(n, x),
						integerPart.At(next, x),
						real_pow.PowAddOne.At(two, n),
						nat_order.NotLessEq.At(b.TermAs[Nat]("2 * k(n, x)"), b.TermAs[Nat]("k(n + 1, x)"))))
				b.Show(
					"so kₙ(x)/2ⁿ = 2·kₙ(x)/2ⁿ⁺¹ ≤ kₙ₊₁(x)/2ⁿ⁺¹",
					ByArith(doubled, positive.At(n), real_pow.PowAddOne.At(two, n)))
			}))

		eventually := a.Have(
			"a level t below f(x) is passed, from some N on, by every hₙ(x) with room to spare",
			"∀x:A. ∀t:real. extended_of_real(t) < f(x) ⇒ ∃u:real. ∃N:num. t < u ∧ ∀n:num. N ≤ n ⇒ u ≤ h(n, x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				t := b.FixAs[Real]("t")
				above := b.Assume()
				b.Cases(b.Term("f(x) = extended_infinity"))
				b.When(
					"where f is infinite, hₙ(x) = n passes t + 1 once n does",
					func(c *Argument, infinite Fact) {
						N, beyond := c.ObtainAs[Nat](
							"some N lies at or above t + 1",
							"∃N:num. t + &1 ≤ &N",
							By(real_archimedean.ExistsNumAbove.At(c.TermAs[Real]("t + &1"))))
						c.Take(c.TermAs[Real]("t + &1"))
						c.Take(N)
						c.Show(
							"t < t + 1, and from N on hₙ(x) = n ≥ N ≥ t + 1",
							SplitConj(
								Case(
									"t lies below t + 1",
									ByArith()),
								Case(
									"from N on, hₙ(x) passes t + 1",
									Derive(func(d *Argument) {
										n := d.FixAs[Nat]("n")
										past := d.Assume()
										d.Show(
											"hₙ(x) = n ≥ N ≥ t + 1",
											ByArith(past, beyond, infinite, atInfinity.At(n, x)))
									}))))
					})
				b.Otherwise(
					"where f is finite with value r, t < r and hₙ(x) = r once n passes r",
					func(c *Argument, finite Fact) {
						value := c.TermAs[Real]("extended_to_real(f(x))")
						N, beyond := c.ObtainAs[Nat](
							"some N lies at or above r",
							"∃N:num. extended_to_real(f(x)) ≤ &N",
							By(real_archimedean.ExistsNumAbove.At(value)))
						belowValue := c.Have(
							"t lies below r, the image of t lying below the image of r",
							"t < extended_to_real(f(x))",
							By(
								Normalized,
								finite,
								above,
								extended_nonneg_real.OfRealToReal.At(f.Apply(x)),
								extended_nonneg_real.OfRealLt.At(t, value)))
						c.Take(value)
						c.Take(N)
						c.Show(
							"t < r, and from N on hₙ(x) = min(n, r) = r",
							SplitConj(
								Case(
									"t lies below r",
									By(belowValue)),
								Case(
									"from N on, the cap n is idle",
									Derive(func(d *Argument) {
										n := d.FixAs[Nat]("n")
										past := d.Assume()
										d.Show(
											"r ≤ N ≤ n, so min(n, r) = r",
											ByArith(
												past,
												beyond,
												finite,
												atFinite.At(n, x),
												real_sup_inf.LessEqMin.At(d.TermAs[Real]("&n"), value, value)))
									}))))
					})
			}))
		approach := a.Have(
			"so some sₙ(x) passes every level t below f(x)",
			"∀x:A. ∀t:real. extended_of_real(t) < f(x) ⇒ ∃n:num. t < &k(n, x) / &(2 ^ n)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				t := b.FixAs[Real]("t")
				above := b.Assume()
				_, _, level := b.Obtain2As[Real, Nat](
					"take a level u above t that every hₙ(x) passes from some N on",
					"∃u:real. ∃N:num. t < u ∧ ∀n:num. N ≤ n ⇒ u ≤ h(n, x)",
					By(eventually.At(x, t), above))
				margin := b.Conjuncts(
					level,
					"t lies below u",
					"from N on, hₙ(x) passes u")
				gap := b.Have(
					"the gap u − t is positive",
					"&0 < u - t",
					ByArith(margin[0]))
				_, multiple := b.ObtainAs[Nat](
					"some multiple m·(u − t) exceeds 1",
					"∃m:num. &1 < &m * (u - t)",
					By(gap, real_archimedean.Archimedean.At(b.TermAs[Real]("u - t"), b.TermAs[Real]("&1"))))
				n := b.TermAs[Nat]("N + m")
				b.Take(n)
				power := b.Have(
					"m ≤ N + m < 2ᴺ⁺ᵐ",
					"&m ≤ &(2 ^ (N + m))",
					ByArith(nat_order.LessThanPowTwoSelf.At(n)))
				scaledGap := b.Have(
					"so 2ᴺ⁺ᵐ·(u − t) exceeds 1",
					"&1 < &(2 ^ (N + m)) * (u - t)",
					ByArith(multiple, gap, power))
				b.Show(
					"kₙ(x) + 1 > 2ⁿ·hₙ(x) ≥ 2ⁿ·u > 2ⁿ·t + 1 at n = N + m",
					ByArith(scaledGap, integerPart.At(n, x), positive.At(n), margin[1].At(n)))
			}))

		supremum := a.Have(
			"f(x) is the supremum of the sₙ(x)",
			"∀x:A. f(x) = extended_sup(image(λn:num. extended_of_real(&k(n, x) / &(2 ^ n)), 𝕌))",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				fx := f.Apply(x)
				approximations := b.TermAs[Fun[Nat, ExtendedNonnegReal]](
					"λn:num. extended_of_real(&k(n, x) / &(2 ^ n))")
				σ, σDef := b.LetAs[ExtendedNonnegReal](
					"σ",
					"extended_sup(image(λn:num. extended_of_real(&k(n, x) / &(2 ^ n)), 𝕌))")
				lower := b.Have(
					"σ lies below f(x), as every sₙ(x) does",
					"σ ≤ f(x)",
					By(Normalized, σDef, below, extended_nonneg_real.SupSequenceLeast.At(approximations, fx)))
				upper := b.Have(
					"f(x) lies below σ",
					"f(x) ≤ σ",
					Derive(func(c *Argument) {
						c.Cases(c.Term("σ = extended_infinity"))
						c.When(
							"an infinite σ lies above everything",
							func(d *Argument, infinite Fact) {
								d.Show(
									"f(x) ≤ ∞",
									By(Normalized, infinite, extended_nonneg_real.LeInfinity.At(fx)))
							})
						c.Otherwise(
							"a finite σ is the image of its value c",
							func(d *Argument, finite Fact) {
								value := d.TermAs[Real]("extended_to_real(σ)")
								image := d.Have(
									"σ is the image of c, which is not negative",
									"σ = extended_of_real(extended_to_real(σ)) ∧ &0 ≤ extended_to_real(σ)",
									By(finite, extended_nonneg_real.OfRealToReal.At(σ), extended_nonneg_real.ToRealNonneg.At(σ)))
								d.Cases(d.Term("extended_of_real(extended_to_real(σ)) < f(x)"))
								d.When(
									"were the image of c below f(x), some sₘ(x) would pass c",
									func(e *Argument, short Fact) {
										m, passes := e.ObtainAs[Nat](
											"some sₘ(x) passes c",
											"∃m:num. extended_to_real(σ) < &k(m, x) / &(2 ^ m)",
											By(approach.At(x, value), short))
										bounded := e.Have(
											"but sₘ(x) lies below σ, the image of c",
											"&k(m, x) / &(2 ^ m) ≤ extended_to_real(σ)",
											By(
												image,
												σDef,
												extended_nonneg_real.SupSequenceUpper.At(approximations, m),
												extended_nonneg_real.OfRealLe.At(e.TermAs[Real]("&k(m, x) / &(2 ^ m)"), value)))
										e.Show(
											"sₘ(x) cannot both pass c and lie below it",
											ByArith(passes, bounded))
									})
								d.Otherwise(
									"so f(x) lies below the image of c, which is σ",
									func(e *Argument, notShort Fact) {
										e.Show(
											"f(x) ≤ σ",
											By(
												Normalized,
												notShort,
												image,
												extended_nonneg_real.LtIffNotLe.At(
													e.TermAs[ExtendedNonnegReal]("extended_of_real(extended_to_real(σ))"),
													fx)))
									})
							})
					}))
				b.Show(
					"so f(x) = σ",
					By(σDef, lower, upper, extended_nonneg_real.LeAntisym.At(fx, σ)))
			}))

		a.Take(a.TermAs[Fun[Nat, Fun[A, Real]]]("λn:num. λx:A. &k(n, x) / &(2 ^ n)"))
		a.Show(
			"the sₙ = kₙ/2ⁿ are simple, increase, stay below f and have f as their supremum",
			By(simple, increasing, below, supremum))
	}),
})}
