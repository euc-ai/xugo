package measurable_function

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/rational"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_cardinality"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// RealMeasurableSourceMono — enlarging the source family of measurable events
// preserves measurability: every Borel preimage in the smaller family belongs
// to the larger one.
var RealMeasurableSourceMono = realMeasurableSourceMonoThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableSourceMono",
	Key:  "prop_a1d17fde38ba4b9",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S T:set(set(A)). ∀f:(A → real).",
		Hypotheses: []string{"S ⊆ T", "real_measurable(Ω, S, f)"},
		Conclusion: "real_measurable(Ω, T, f)",
	}, func(a *Argument, Ω *Expr[Set[A]], S, T *Expr[Set[Set[A]]], f *Arrow[A, Real], premises Fact) {
		a.Show(
			"each S-measurable preimage belongs to T",
			By(
				premises,
				RealMeasurableDef.At(Ω, S, f),
				RealMeasurableDef.At(Ω, T, f),
				measurable_space.MeasurableMapDef,
				set_basic.SubsetDef))
	}),
})}

// RealMeasurableConst — a constant function is measurable: the set where it
// exceeds c is all of Ω when c lies below the constant, and empty otherwise.
var RealMeasurableConst = realMeasurableConstThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableConst",
	Key:  "prop_c9cea9baf87a9c00",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀k:real.",
		Hypotheses: []string{"sigma_algebra_on(Ω, S)"},
		Conclusion: "real_measurable(Ω, S, λx:A. k)",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], k *Expr[Real], sigma Fact) {
		rays := a.Have(
			"every upper ray of the constant is measurable",
			"∀c:real. {x:A | x ∈ Ω ∧ c < k} ∈ S",
			Derive(func(b *Argument) {
				b.FixAs[Real]("c")
				b.Cases(b.Term("c < k"))
				b.When(
					"below k, the constant exceeds c on all of Ω",
					func(d *Argument, below Fact) {
						whole := d.Have(
							"so the ray is the carrier",
							"{x:A | x ∈ Ω ∧ c < k} = Ω",
							BySets(below))
						d.Show(
							"and the carrier is measurable",
							By(whole, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
					})
				b.Otherwise(
					"at or above k, the constant exceeds c nowhere",
					func(d *Argument, notBelow Fact) {
						empty := d.Have(
							"so the ray is empty",
							"{x:A | x ∈ Ω ∧ c < k} = ∅",
							BySets(notBelow))
						d.Show(
							"and the empty set is measurable",
							By(empty, sigma, sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
					})
			}))
		a.Show(
			"upper rays decide measurability",
			By(sigma, rays, RealMeasurableIffRay.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. k"))))
	}),
})}

// RealMeasurableAtMost — where a measurable function is at most c is a
// measurable set: what the set where it exceeds c leaves of Ω.
var RealMeasurableAtMost = realMeasurableAtMostThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableAtMost",
	Key:  "prop_fcfbd7f129c72692",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real). ∀c:real.",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, f)",
		},
		Conclusion: "{x:A | x ∈ Ω ∧ f(x) ≤ c} ∈ S",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], f *Arrow[A, Real], c *Expr[Real],
		sigma, measurable Fact) {
		above := a.Have(
			"the set where f exceeds c is measurable",
			"{x:A | x ∈ Ω ∧ c < f(x)} ∈ S",
			By(sigma, measurable, RealMeasurableIffRay.At(Ω, S, f)))
		complement := a.Have(
			"f is at most c exactly where it does not exceed c",
			"{x:A | x ∈ Ω ∧ f(x) ≤ c} = Ω ∖ {x:A | x ∈ Ω ∧ c < f(x)}",
			BySets(real_order_ring.NotLessThan))
		a.Show(
			"so the set is the relative complement of a measurable one",
			By(sigma, above, complement, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
	}),
})}

// RealMeasurableBelow — where a measurable function lies below c is a
// measurable set. f(x) < c exactly when f(x) ≤ c − 1/(n + 1) for some n,
// so the set is the countable union of the sets where f is at most
// c − 1/(n + 1).
var RealMeasurableBelow = realMeasurableBelowThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableBelow",
	Key:  "prop_adb9a2d40c59ab30",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real). ∀c:real.",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, f)",
		},
		Conclusion: "{x:A | x ∈ Ω ∧ f(x) < c} ∈ S",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], f *Arrow[A, Real], c *Expr[Real],
		sigma, measurable Fact) {
		steps := a.Have(
			"y < c exactly when y ≤ c − 1/(n + 1) for some n",
			"∀y:real. y < c ⇔ ∃n:num. y ≤ c - real_inv(&n + &1)",
			Derive(func(b *Argument) {
				b.FixAs[Real]("y")
				b.Iff()
				b.Forward(
					"the gap c − y holds some 1/(n + 1)",
					func(d *Argument, below Fact) {
						n, small := d.ObtainAs[Nat](
							"some 1/(n + 1) lies below c − y",
							"∃n:num. real_inv(&n + &1) < c - y",
							ByArith(below, real_archimedean.ExistsReciprocalBelow.At(d.TermAs[Real]("c - y"))))
						d.Take(n)
						d.Show(
							"so y ≤ c − 1/(n + 1)",
							ByArith(small))
					})
				b.Backward(
					"c − 1/(n + 1) lies below c",
					func(d *Argument, some Fact) {
						_, atMost := d.Unpack(some)
						positive := d.Have(
							"1/(n + 1) is positive",
							"&0 < real_inv(&n + &1)",
							ByArith(real_order_field.InvPos.At(d.TermAs[Real]("&n + &1"))))
						d.Show(
							"so y < c",
							ByArith(atMost, positive))
					})
			}))
		union := a.Have(
			"so the set is the union of the sets where f is at most c − 1/(n + 1)",
			"{x:A | x ∈ Ω ∧ f(x) < c} = ⋃image(λn:num. {x:A | x ∈ Ω ∧ f(x) ≤ c - real_inv(&n + &1)}, 𝕌)",
			BySets(steps))
		terms := a.Have(
			"each of those sets is measurable",
			"∀n:num. {x:A | x ∈ Ω ∧ f(x) ≤ c - real_inv(&n + &1)} ∈ S",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				b.Show(
					"a closed lower ray of a measurable function is measurable",
					By(sigma, measurable, RealMeasurableAtMost.At(Ω, S, f, b.TermAs[Real]("c - real_inv(&n + &1)"))))
			}))
		a.Show(
			"and so is their countable union",
			By(union, terms, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
	}),
})}

// RealMeasurableAtLeast — where a measurable function is at least c is a
// measurable set: what the set where it lies below c leaves of Ω.
var RealMeasurableAtLeast = realMeasurableAtLeastThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableAtLeast",
	Key:  "prop_a2cb7c496b1bec3a",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real). ∀c:real.",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, f)",
		},
		Conclusion: "{x:A | x ∈ Ω ∧ c ≤ f(x)} ∈ S",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], f *Arrow[A, Real], c *Expr[Real],
		sigma, measurable Fact) {
		complement := a.Have(
			"f is at least c exactly where it does not lie below c",
			"{x:A | x ∈ Ω ∧ c ≤ f(x)} = Ω ∖ {x:A | x ∈ Ω ∧ f(x) < c}",
			BySets(real_order_ring.NotLessThan))
		a.Show(
			"so the set is the relative complement of a measurable one",
			By(
				sigma,
				measurable,
				RealMeasurableBelow.At(Ω, S, f, c),
				complement,
				sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
	}),
})}

// RealMeasurableNeg — the negative of a measurable function is measurable:
// −f exceeds c exactly where f lies below −c.
var RealMeasurableNeg = realMeasurableNegThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableNeg",
	Key:  "prop_5196dfa782cbe1ca",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, f)",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. -f(x))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		f *Arrow[A, Real],
		sigma, measurable Fact,
	) {
		rays := a.Have(
			"every upper ray of −f is measurable",
			"∀c:real. {x:A | x ∈ Ω ∧ c < -f(x)} ∈ S",
			Derive(func(b *Argument) {
				b.FixAs[Real]("c")
				flip := b.Have(
					"negating both sides reverses the comparison",
					"∀y:real. c < -y ⇔ y < -c",
					b.ForEach(func(y *Expr[Real]) Action { return ByArith() }))
				same := b.Have(
					"so −f exceeds c where f lies below −c",
					"{x:A | x ∈ Ω ∧ c < -f(x)} = {x:A | x ∈ Ω ∧ f(x) < -c}",
					BySets(flip))
				b.Do(same.Rw())
				b.Show(
					"which is a measurable set",
					By(sigma, measurable, RealMeasurableBelow.At(Ω, S, f, b.TermAs[Real]("-c"))))
			}))
		a.Show(
			"upper rays decide measurability",
			By(sigma, rays, RealMeasurableIffRay.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. -f(x)"))))
	}),
})}

// RealMeasurableScale — a constant multiple of a measurable function is
// measurable. For k positive, k · f exceeds c where f exceeds c / k; for k
// negative, where f lies below c / k; and for k = 0 the multiple is the
// constant 0.
var RealMeasurableScale = realMeasurableScaleThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableScale",
	Key:  "prop_8c1df5e984be7781",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real). ∀k:real.",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, f)",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. k * f(x))",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], f *Arrow[A, Real], k *Expr[Real],
		sigma, measurable Fact) {
		above := a.Have(
			"every upper ray of f is measurable",
			"∀t:real. {x:A | x ∈ Ω ∧ t < f(x)} ∈ S",
			By(sigma, measurable, RealMeasurableIffRay.At(Ω, S, f)))
		rays := a.Have(
			"every upper ray of k · f is measurable",
			"∀c:real. {x:A | x ∈ Ω ∧ c < k * f(x)} ∈ S",
			Derive(func(b *Argument) {
				b.FixAs[Real]("c")
				b.Cases(b.Term("&0 < k"))
				b.When(
					"for k positive, k · f exceeds c where f exceeds c / k",
					func(d *Argument, positive Fact) {
						divide := d.Have(
							"dividing by k keeps the comparison",
							"∀y:real. c < k * y ⇔ c / k < y",
							d.ForEach(func(y *Expr[Real]) Action { return ByArith(positive) }))
						same := d.Have(
							"so the set is the one where f exceeds c / k",
							"{x:A | x ∈ Ω ∧ c < k * f(x)} = {x:A | x ∈ Ω ∧ c / k < f(x)}",
							BySets(divide))
						d.Do(same.Rw())
						d.Show(
							"which is measurable, f being measurable",
							By(above.At(d.TermAs[Real]("c / k"))))
					})
				b.Otherwise(
					"for k at most 0, k · f exceeds c where f lies below c / k, or nowhere or everywhere",
					func(d *Argument, notPositive Fact) {
						d.Cases(d.Term("k < &0"))
						d.When(
							"for k negative, k · f exceeds c where f lies below c / k",
							func(e *Argument, negative Fact) {
								divide := e.Have(
									"dividing by k reverses the comparison",
									"∀y:real. c < k * y ⇔ y < c / k",
									e.ForEach(func(y *Expr[Real]) Action { return ByArith(negative) }))
								same := e.Have(
									"so the set is the one where f lies below c / k",
									"{x:A | x ∈ Ω ∧ c < k * f(x)} = {x:A | x ∈ Ω ∧ f(x) < c / k}",
									BySets(divide))
								e.Do(same.Rw())
								e.Show(
									"which is measurable",
									By(sigma, measurable, RealMeasurableBelow.At(Ω, S, f, e.TermAs[Real]("c / k"))))
							})
						d.Otherwise(
							"for k = 0, k · f is the constant 0",
							func(e *Argument, notNegative Fact) {
								zero := e.Have(
									"so k is 0",
									"k = &0",
									ByArith(notPositive, notNegative))
								vanish := e.Have(
									"k · y is 0 at every y",
									"∀y:real. c < k * y ⇔ c < &0",
									e.ForEach(func(y *Expr[Real]) Action {
										return By(zero, real_ring.MulLeftZero)
									}))
								same := e.Have(
									"so the set is the one where the constant 0 exceeds c",
									"{x:A | x ∈ Ω ∧ c < k * f(x)} = {x:A | x ∈ Ω ∧ c < &0}",
									BySets(vanish))
								e.Do(same.Rw())
								e.Show(
									"which is measurable, the constant 0 being measurable",
									By(
										sigma,
										RealMeasurableConst.At(Ω, S, e.TermAs[Real]("&0")),
										RealMeasurableIffRay.At(Ω, S, e.TermAs[Fun[A, Real]]("λx:A. &0"))))
							})
					})
			}))
		a.Show(
			"upper rays decide measurability",
			By(sigma, rays, RealMeasurableIffRay.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. k * f(x)"))))
	}),
})}

// RealMeasurableAdd — the sum of two measurable functions is measurable.
// u + v exceeds c exactly when some rational lies between c − v and u. A
// sequence e runs through the rationals, so the set where f + g exceeds c
// is the countable union over n of the sets where f exceeds e(n) and g
// exceeds c − e(n).
var RealMeasurableAdd = realMeasurableAddThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableAdd",
	Key:  "prop_e7e4fb5e028de4a2",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f g:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, f)",
			"real_measurable(Ω, S, g)",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. f(x) + g(x))",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], f, g *Arrow[A, Real],
		sigma, fMeasurable, gMeasurable Fact) {
		fAbove := a.Have(
			"every upper ray of f is measurable",
			"∀t:real. {x:A | x ∈ Ω ∧ t < f(x)} ∈ S",
			By(sigma, fMeasurable, RealMeasurableIffRay.At(Ω, S, f)))
		gAbove := a.Have(
			"and every upper ray of g",
			"∀t:real. {x:A | x ∈ Ω ∧ t < g(x)} ∈ S",
			By(sigma, gMeasurable, RealMeasurableIffRay.At(Ω, S, g)))
		_, enumerates := a.ObtainAs[Fun[Nat, Real]](
			"the rationals are countable, so a sequence e runs through all of them",
			"∃e:(num → real). {x:real | rational(x)} ⊆ image(e, 𝕌)",
			By(
				real_cardinality.CountableRational,
				cardinal.CountableCover.At(a.TermAs[Set[Real]]("{x:real | rational(x)}"))))
		rays := a.Have(
			"every upper ray of f + g is measurable",
			"∀c:real. {x:A | x ∈ Ω ∧ c < f(x) + g(x)} ∈ S",
			Derive(func(b *Argument) {
				b.FixAs[Real]("c")
				split := b.Have(
					"u + v exceeds c exactly when some e(n) lies below u and above c − v",
					"∀u v:real. c < u + v ⇔ ∃n:num. e(n) < u ∧ c - e(n) < v",
					Derive(func(d *Argument) {
						d.FixAs[Real]("u")
						d.FixAs[Real]("v")
						d.Iff()
						d.Forward(
							"a rational lies between c − v and u, and it is some e(n)",
							func(e *Argument, above Fact) {
								_, between := e.ObtainAs[Real](
									"some rational q lies between c − v and u",
									"∃q:real. rational(q) ∧ c - v < q ∧ q < u",
									ByArith(above, rational.RationalBetween.At(e.TermAs[Real]("c - v"), e.TermAs[Real]("u"))))
								n, listed := e.ObtainAs[Nat](
									"q is a value of e",
									"∃n:num. q = e(n)",
									BySets(enumerates, between))
								e.Take(n)
								e.Show(
									"so e(n) lies below u, and c − e(n) below v",
									ByArith(between, listed))
							})
						d.Backward(
							"the two comparisons add up",
							func(e *Argument, some Fact) {
								_, both := e.Unpack(some)
								e.Show(
									"e(n) < u and c − e(n) < v give c < u + v",
									ByArith(both))
							})
					}))
				union := b.Have(
					"so the set is the union over n of the sets where f exceeds e(n) and g exceeds c − e(n)",
					"{x:A | x ∈ Ω ∧ c < f(x) + g(x)} = "+
						"⋃image(λn:num. {x:A | x ∈ Ω ∧ e(n) < f(x)} ∩ {x:A | x ∈ Ω ∧ c - e(n) < g(x)}, 𝕌)",
					BySets(split))
				pieces := b.Have(
					"each of those sets is the intersection of two measurable sets",
					"∀n:num. {x:A | x ∈ Ω ∧ e(n) < f(x)} ∩ {x:A | x ∈ Ω ∧ c - e(n) < g(x)} ∈ S",
					By(fAbove, gAbove, sigma, sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
				b.Do(union.Rw())
				b.Show(
					"and their countable union is measurable",
					By(pieces, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
			}))
		a.Show(
			"upper rays decide measurability",
			By(sigma, rays, RealMeasurableIffRay.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. f(x) + g(x)"))))
	}),
})}

// RealMeasurableSum — a finite sum of measurable functions is measurable:
// the empty sum is constant, and each further summand is added to a
// measurable sum.
var RealMeasurableSum = realMeasurableSumThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableSum",
	Key:  "prop_f0f5bcf1c1f02e02",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀f:(num → A → real). ∀n:num.",
		Hypotheses: []string{"sigma_algebra_on(Ω, S)", "∀j:num. j < n ⇒ real_measurable(Ω, S, f(j))"},
		Conclusion: "real_measurable(Ω, S, λx:A. Σ_{j<n} f(j, x))",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], f *Arrow2[Nat, A, Real], n *Expr[Nat]) {
		a.Induct(n)
		a.Base(
			"the empty sum is measurable",
			func(b *Argument) {
				sigma := b.Assume()
				b.Show(
					"the empty sum is constant",
					Simp(Fwd(real_sum.BelowClauses)),
					By(sigma, RealMeasurableConst))
			})
		a.Step(
			"adjoin one measurable summand",
			func(b *Argument, previous Fact) {
				data := b.Assume()
				parts := b.Conjuncts(
					data,
					"sigma_algebra_on(Ω, S)",
					"∀j:num. j < suc(n) ⇒ real_measurable(Ω, S, f(j))")
				earlier := b.Have(
					"the preceding sum is measurable",
					"real_measurable(Ω, S, λx:A. Σ_{j<n} f(j, x))",
					ByArith(parts[1], parts[0], previous, nat_order.LessThanSucIffLessEq, nat_order.LessEqRefl))
				last := b.Have(
					"the last summand is measurable",
					"real_measurable(Ω, S, f(n))",
					By(parts[1].At(n), nat_order.LessThanSucIffLessEq, nat_order.LessEqRefl))
				b.Show(
					"addition preserves measurability",
					Simp(Fwd(real_sum.BelowClauses)),
					By(parts[0], earlier, last, RealMeasurableAdd))
			})
	}),
})}

// RealMeasurableMax — the larger of two measurable functions is measurable:
// it exceeds c exactly where one of them does.
var RealMeasurableMax = realMeasurableMaxThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableMax",
	Key:  "prop_4d16f9f4fcdec4df",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f g:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, f)",
			"real_measurable(Ω, S, g)",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. max(f(x), g(x)))",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], f, g *Arrow[A, Real],
		sigma, fMeasurable, gMeasurable Fact) {
		fAbove := a.Have(
			"every upper ray of f is measurable",
			"∀t:real. {x:A | x ∈ Ω ∧ t < f(x)} ∈ S",
			By(sigma, fMeasurable, RealMeasurableIffRay.At(Ω, S, f)))
		gAbove := a.Have(
			"and every upper ray of g",
			"∀t:real. {x:A | x ∈ Ω ∧ t < g(x)} ∈ S",
			By(sigma, gMeasurable, RealMeasurableIffRay.At(Ω, S, g)))
		rays := a.Have(
			"every upper ray of max(f, g) is measurable",
			"∀c:real. {x:A | x ∈ Ω ∧ c < max(f(x), g(x))} ∈ S",
			Derive(func(b *Argument) {
				c := b.FixAs[Real]("c")
				union := b.Have(
					"max(f, g) exceeds c exactly where f or g does",
					"{x:A | x ∈ Ω ∧ c < max(f(x), g(x))} = {x:A | x ∈ Ω ∧ c < f(x)} ∪ {x:A | x ∈ Ω ∧ c < g(x)}",
					BySets(real_sup_inf.MaxLessEq, real_order_ring.NotLessThan))
				b.Do(union.Rw())
				b.Show(
					"and the union of two measurable sets is measurable",
					By(fAbove.At(c), gAbove.At(c), sigma, sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
			}))
		a.Show(
			"upper rays decide measurability",
			By(sigma, rays, RealMeasurableIffRay.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. max(f(x), g(x))"))))
	}),
})}

// RealMeasurableMin — the smaller of two measurable functions is measurable:
// it exceeds c exactly where both of them do.
var RealMeasurableMin = realMeasurableMinThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableMin",
	Key:  "prop_3c84d050fd1542d8",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f g:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, f)",
			"real_measurable(Ω, S, g)",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. min(f(x), g(x)))",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], f, g *Arrow[A, Real],
		sigma, fMeasurable, gMeasurable Fact) {
		fAbove := a.Have(
			"every upper ray of f is measurable",
			"∀t:real. {x:A | x ∈ Ω ∧ t < f(x)} ∈ S",
			By(sigma, fMeasurable, RealMeasurableIffRay.At(Ω, S, f)))
		gAbove := a.Have(
			"and every upper ray of g",
			"∀t:real. {x:A | x ∈ Ω ∧ t < g(x)} ∈ S",
			By(sigma, gMeasurable, RealMeasurableIffRay.At(Ω, S, g)))
		rays := a.Have(
			"every upper ray of min(f, g) is measurable",
			"∀c:real. {x:A | x ∈ Ω ∧ c < min(f(x), g(x))} ∈ S",
			Derive(func(b *Argument) {
				c := b.FixAs[Real]("c")
				inter := b.Have(
					"min(f, g) exceeds c exactly where both f and g do",
					"{x:A | x ∈ Ω ∧ c < min(f(x), g(x))} = {x:A | x ∈ Ω ∧ c < f(x)} ∩ {x:A | x ∈ Ω ∧ c < g(x)}",
					BySets(real_sup_inf.LessThanMin))
				b.Do(inter.Rw())
				b.Show(
					"and the intersection of two measurable sets is measurable",
					By(fAbove.At(c), gAbove.At(c), sigma, sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
			}))
		a.Show(
			"upper rays decide measurability",
			By(sigma, rays, RealMeasurableIffRay.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. min(f(x), g(x))"))))
	}),
})}

// RealMeasurableAbs — the absolute value of a measurable function is
// measurable: |f| is the larger of f and −f.
var RealMeasurableAbs = realMeasurableAbsThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableAbs",
	Key:  "prop_38b801ef7928c666",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, f)",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. |f(x)|)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		f *Arrow[A, Real],
		sigma, measurable Fact,
	) {
		larger := a.Have(
			"|f| is the larger of f and −f",
			"(λx:A. |f(x)|) = (λx:A. max(f(x), -f(x)))",
			Funext(),
			ByArith())
		a.Show(
			"and the larger of two measurable functions is measurable",
			larger.Rw(),
			By(
				sigma,
				measurable,
				RealMeasurableNeg.At(Ω, S, f),
				RealMeasurableMax.At(Ω, S, f, a.TermAs[Fun[A, Real]]("λx:A. -f(x)"))))
	}),
})}

// RealMeasurableSquare — the square of a measurable function is measurable.
// A square is nonnegative, so its rays at levels c ≥ 0 decide its
// measurability, and a square exceeds a level c ≥ 0 exactly where |f|
// exceeds √c, a set where a measurable function exceeds a level.
var RealMeasurableSquare = realMeasurableSquareThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableSquare",
	Key:  "prop_fdab1aa97e5e629c",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, f)",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. f(x) * f(x))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		f *Arrow[A, Real],
		sigma, measurable Fact,
	) {
		absRays := a.Have(
			"|f| exceeds each level on a measurable set",
			"∀r:real. {x:A | x ∈ Ω ∧ r < |f(x)|} ∈ S",
			By(
				sigma,
				measurable,
				RealMeasurableAbs.At(Ω, S, f),
				RealMeasurableIffRay.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. |f(x)|"))))
		rays := a.Have(
			"so does the square of f, at each level c ≥ 0",
			"∀c:real. &0 ≤ c ⇒ {x:A | x ∈ Ω ∧ c < f(x) * f(x)} ∈ S",
			Derive(func(b *Argument) {
				c := b.FixAs[Real]("c")
				nonneg := b.Assume()
				root := b.Have(
					"√c is nonnegative and squares to c",
					"&0 ≤ real_sqrt(c) ∧ real_sqrt(c) * real_sqrt(c) = c",
					ByArith(nonneg, real_sqrt.SqrtNonneg.At(c), real_sqrt.SqrtPowTwo.At(c)))
				pointwise := b.Have(
					"c < f(x)² exactly when √c < |f(x)|, both sides nonnegative",
					"∀x:A. c < f(x) * f(x) ⇔ real_sqrt(c) < |f(x)|",
					Derive(func(e *Argument) {
						e.FixAs[A]("x")
						e.Iff()
						e.Forward(
							"at most √c, |f(x)| would square to at most c",
							func(g *Argument, above Fact) {
								g.Show(
									"compare the squares",
									ByArith(root, above))
							})
						e.Backward(
							"above √c, |f(x)| squares to above c",
							func(g *Argument, beyond Fact) {
								g.Show(
									"compare the squares",
									ByArith(root, beyond))
							})
					}))
				same := b.Have(
					"so the two sets agree",
					"{x:A | x ∈ Ω ∧ c < f(x) * f(x)} = {x:A | x ∈ Ω ∧ real_sqrt(c) < |f(x)|}",
					BySets(pointwise))
				b.Show(
					"and the second is measurable",
					By(same, absRays.At(b.TermAs[Real]("real_sqrt(c)"))))
			}))
		a.Show(
			"a square is nonnegative, so its rays at levels c ≥ 0 decide its measurability",
			ByArith(
				sigma,
				rays,
				RealMeasurableIffNonnegRay.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. f(x) * f(x)"))))
	}),
})}

// RealMeasurableMul — the product of two measurable functions is
// measurable: by polarization, f·g is a quarter of (f + g)² − (f − g)², and
// sums, negatives, squares and multiples of measurable functions are
// measurable.
var RealMeasurableMul = realMeasurableMulThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableMul",
	Key:  "prop_f26162dbd05261d0",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f g:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, f)",
			"real_measurable(Ω, S, g)",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. f(x) * g(x))",
		Abbrev: Abbrev{
			{Name: "plus", Text: "λx:A. f(x) + g(x)"},
			{Name: "minus", Text: "λx:A. f(x) + -g(x)"},
			{Name: "polarized", Text: "λx:A. " +
				"    real_inv(&4) * ((f(x) + g(x)) * (f(x) + g(x)) + -((f(x) + -g(x)) * (f(x) + -g(x))))"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		f, g *Arrow[A, Real],
		sigma, measurableF, measurableG Fact,
	) {
		plus := a.TermAs[Fun[A, Real]]("«plus»")
		minus := a.TermAs[Fun[A, Real]]("«minus»")
		negG := a.TermAs[Fun[A, Real]]("λx:A. -g(x)")
		plusSquare := a.TermAs[Fun[A, Real]]("λx:A. (f(x) + g(x)) * (f(x) + g(x))")
		minusSquare := a.TermAs[Fun[A, Real]]("λx:A. (f(x) + -g(x)) * (f(x) + -g(x))")
		negMinusSquare := a.TermAs[Fun[A, Real]]("λx:A. -((f(x) + -g(x)) * (f(x) + -g(x)))")
		difference := a.TermAs[Fun[A, Real]](
			"λx:A. (f(x) + g(x)) * (f(x) + g(x)) + -((f(x) + -g(x)) * (f(x) + -g(x)))")
		sums := a.Have(
			"f + g and f − g are measurable",
			"real_measurable(Ω, S, «plus») ∧ real_measurable(Ω, S, «minus»)",
			By(
				sigma,
				measurableF,
				measurableG,
				RealMeasurableAdd.At(Ω, S, f, g),
				RealMeasurableNeg.At(Ω, S, g),
				RealMeasurableAdd.At(Ω, S, f, negG)))
		squares := a.Have(
			"so are their squares",
			"real_measurable(Ω, S, λx:A. (f(x) + g(x)) * (f(x) + g(x))) ∧ "+
				"real_measurable(Ω, S, λx:A. (f(x) + -g(x)) * (f(x) + -g(x)))",
			By(sigma, sums, RealMeasurableSquare.At(Ω, S, plus), RealMeasurableSquare.At(Ω, S, minus)))
		polarized := a.Have(
			"and so is a quarter of their difference",
			"real_measurable(Ω, S, «polarized»)",
			By(
				sigma,
				squares,
				RealMeasurableNeg.At(Ω, S, minusSquare),
				RealMeasurableAdd.At(Ω, S, plusSquare, negMinusSquare),
				RealMeasurableScale.At(Ω, S, difference, a.TermAs[Real]("real_inv(&4)"))))
		identity := a.Have(
			"which is f·g at every point",
			"∀x:A. "+
				"    real_inv(&4) * ((f(x) + g(x)) * (f(x) + g(x)) + -((f(x) + -g(x)) * (f(x) + -g(x)))) = "+
				"    f(x) * g(x)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				b.Show(
					"expand the squares",
					ByArith())
			}))
		a.Show(
			"so f·g is measurable",
			By(a.Simplified(polarized, Fwd(identity))))
	}),
})}

// RealMeasurableParts — the positive and negative parts of a measurable
// function are measurable: each is the larger of a measurable function, f
// or −f, and the constant 0.
var RealMeasurableParts = realMeasurablePartsThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableParts",
	Key:  "prop_9c23ae0e458b8ffd",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, f)",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. max(f(x), &0)) ∧ " +
			"real_measurable(Ω, S, λx:A. max(-f(x), &0))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		f *Arrow[A, Real],
		sigma, measurable Fact,
	) {
		zero := a.TermAs[Fun[A, Real]]("λx:A. &0")
		a.Show(
			"each part is the larger of f or −f and the constant 0",
			By(
				sigma,
				measurable,
				RealMeasurableNeg.At(Ω, S, f),
				RealMeasurableConst.At(Ω, S, a.TermAs[Real]("&0")),
				RealMeasurableMax.At(Ω, S, f, zero),
				RealMeasurableMax.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. -f(x)"), zero)))
	}),
})}

// RealMeasurableSup — the pointwise supremum on Ω of a sequence of
// measurable functions is measurable. Where g(x) is the least upper bound of
// the values f(n)(x), g exceeds c exactly where some f(n) does, so the set
// is the countable union of the sets where each f(n) exceeds c.
var RealMeasurableSup = realMeasurableSupThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableSup",
	Key:  "prop_28e534d4f3e27e6f",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(num → A → real). ∀g:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"∀n:num. real_measurable(Ω, S, f(n))",
			"∀x:A. x ∈ Ω ⇒ ∀n:num. f(n)(x) ≤ g(x)",
			"∀x:A. ∀b:real. x ∈ Ω ∧ (∀n:num. f(n)(x) ≤ b) ⇒ g(x) ≤ b",
		},
		Conclusion: "real_measurable(Ω, S, g)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		f *Arrow[Nat, Fun[A, Real]],
		g *Arrow[A, Real],
		sigma, measurable, upper, least Fact,
	) {
		rays := a.Have(
			"every upper ray of g is measurable",
			"∀c:real. {x:A | x ∈ Ω ∧ c < g(x)} ∈ S",
			Derive(func(b *Argument) {
				c := b.FixAs[Real]("c")
				some := b.Have(
					"on Ω, g(x) exceeds c exactly when some f(n)(x) does",
					"∀x:A. x ∈ Ω ⇒ (c < g(x) ⇔ ∃n:num. c < f(n)(x))",
					Derive(func(d *Argument) {
						x := d.FixAs[A]("x")
						inΩ := d.Assume()
						d.Iff()
						d.Forward(
							"were every f(n)(x) at most c, so would be their least upper bound g(x)",
							func(e *Argument, above Fact) {
								e.Show(
									"so some f(n)(x) exceeds c",
									By(above, inΩ, least.At(x, c), real_order_ring.NotLessThan))
							})
						d.Backward(
							"g(x) bounds every f(n)(x)",
							func(e *Argument, exceeds Fact) {
								n, over := e.UnpackAs[Nat](exceeds)
								e.Show(
									"so g(x) exceeds c too",
									ByArith(over, inΩ, upper.At(x, n)))
							})
					}))
				union := b.Have(
					"so the ray of g is the union of the rays where each f(n) exceeds c",
					"{x:A | x ∈ Ω ∧ c < g(x)} = ⋃image(λn:num. {x:A | x ∈ Ω ∧ c < f(n)(x)}, 𝕌)",
					BySets(some))
				levels := b.Have(
					"each f(n) exceeds c on a measurable set",
					"∀n:num. {x:A | x ∈ Ω ∧ c < f(n)(x)} ∈ S",
					Derive(func(d *Argument) {
						n := d.FixAs[Nat]("n")
						d.Show(
							"f(n) is measurable",
							By(sigma, measurable.At(n), RealMeasurableIffRay.At(Ω, S, f.Apply(n))))
					}))
				b.Do(union.Rw())
				b.Show(
					"and the countable union of those sets is measurable",
					By(levels, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
			}))
		a.Show(
			"upper rays decide measurability",
			By(sigma, rays, RealMeasurableIffRay.At(Ω, S, g)))
	}),
})}

// RealMeasurableInf — the pointwise infimum on Ω of a sequence of measurable
// functions is measurable. Where g(x) is the greatest lower bound of the
// values f(n)(x), −g(x) is the least upper bound of the values −f(n)(x), so
// −g is measurable (RealMeasurableSup); and g exceeds c exactly where −g lies
// below −c.
var RealMeasurableInf = realMeasurableInfThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableInf",
	Key:  "prop_8a6c3d4bd429becc",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(num → A → real). ∀g:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"∀n:num. real_measurable(Ω, S, f(n))",
			"∀x:A. x ∈ Ω ⇒ ∀n:num. g(x) ≤ f(n)(x)",
			"∀x:A. ∀b:real. x ∈ Ω ∧ (∀n:num. b ≤ f(n)(x)) ⇒ b ≤ g(x)",
		},
		Conclusion: "real_measurable(Ω, S, g)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		f *Arrow[Nat, Fun[A, Real]],
		g *Arrow[A, Real],
		sigma, measurable, lower, greatest Fact,
	) {
		negMeasurable := a.Have(
			"each −f(n) is measurable",
			"∀n:num. real_measurable(Ω, S, λx:A. -f(n)(x))",
			Derive(func(d *Argument) {
				n := d.FixAs[Nat]("n")
				d.Show(
					"the negative of a measurable function is measurable",
					By(sigma, measurable.At(n), RealMeasurableNeg.At(Ω, S, f.Apply(n))))
			}))
		negUpper := a.Have(
			"−g(x) bounds every −f(n)(x) on Ω",
			"∀x:A. x ∈ Ω ⇒ ∀n:num. -f(n)(x) ≤ -g(x)",
			Derive(func(d *Argument) {
				x := d.FixAs[A]("x")
				inΩ := d.Assume()
				n := d.FixAs[Nat]("n")
				d.Show(
					"negation reverses g(x) ≤ f(n)(x)",
					ByArith(inΩ, lower.At(x, n)))
			}))
		negLeast := a.Have(
			"and lies below each of their upper bounds b, −b being a lower bound of the f(n)(x)",
			"∀x:A. ∀b:real. x ∈ Ω ∧ (∀n:num. -f(n)(x) ≤ b) ⇒ -g(x) ≤ b",
			Derive(func(d *Argument) {
				x := d.FixAs[A]("x")
				d.FixAs[Real]("b")
				given := d.Conjuncts(
					d.Assume(),
					"x lies in Ω",
					"b bounds every −f(n)(x)")
				inΩ, above := given[0], given[1]
				below := d.Have(
					"−b lies below every f(n)(x)",
					"∀n:num. -b ≤ f(n)(x)",
					d.ForEach(func(n *Expr[Nat]) Action { return ByArith(above.At(n)) }))
				d.Show(
					"so −b lies below their greatest lower bound g(x)",
					ByArith(inΩ, below, greatest.At(x, d.TermAs[Real]("-b"))))
			}))
		negG := a.TermAs[Fun[A, Real]]("λx:A. -g(x)")
		negSup := a.Have(
			"so −g, the least upper bound of the −f(n), is measurable",
			"real_measurable(Ω, S, λx:A. -g(x))",
			By(
				sigma,
				negMeasurable,
				negUpper,
				negLeast,
				RealMeasurableSup.At(Ω, S, a.TermAs[Fun[Nat, Fun[A, Real]]]("λn:num. λx:A. -f(n)(x)"), negG)))
		rays := a.Have(
			"every upper ray of g is measurable",
			"∀c:real. {x:A | x ∈ Ω ∧ c < g(x)} ∈ S",
			Derive(func(b *Argument) {
				b.FixAs[Real]("c")
				flip := b.Have(
					"negating both sides reverses the comparison",
					"∀y:real. c < y ⇔ -y < -c",
					b.ForEach(func(y *Expr[Real]) Action { return ByArith() }))
				same := b.Have(
					"so g exceeds c where −g lies below −c",
					"{x:A | x ∈ Ω ∧ c < g(x)} = {x:A | x ∈ Ω ∧ -g(x) < -c}",
					BySets(flip))
				b.Do(same.Rw())
				b.Show(
					"which is a measurable set, −g being measurable",
					By(sigma, negSup, RealMeasurableBelow.At(Ω, S, negG, b.TermAs[Real]("-c"))))
			}))
		a.Show(
			"upper rays decide measurability",
			By(sigma, rays, RealMeasurableIffRay.At(Ω, S, g)))
	}),
})}

// RealMeasurableLimit — the pointwise limit on Ω of a sequence of measurable
// functions is measurable. g(x) exceeds c exactly when, for some k, the
// values f(n)(x) from some N on all exceed c + 1/(k + 1)
// (real_sequences.LimitAboveIff). So the set where g exceeds c is a union
// over k and N of the points where every f(N + m) exceeds c + 1/(k + 1),
// which is what the sets where some f(N + m) stays at most c + 1/(k + 1)
// leave of Ω.
var RealMeasurableLimit = realMeasurableLimitThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableLimit",
	Key:  "prop_6cc17340926405a4",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(num → A → real). ∀g:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"∀n:num. real_measurable(Ω, S, f(n))",
			"∀x:A. x ∈ Ω ⇒ (λn:num. f(n)(x)) ⟶ g(x)",
		},
		Conclusion: "real_measurable(Ω, S, g)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		f *Arrow[Nat, Fun[A, Real]],
		g *Arrow[A, Real],
		sigma, measurable, converges Fact,
	) {
		rays := a.Have(
			"every upper ray of g is measurable",
			"∀c:real. {x:A | x ∈ Ω ∧ c < g(x)} ∈ S",
			Derive(func(b *Argument) {
				c := b.FixAs[Real]("c")
				eventually := b.Have(
					"on Ω, g(x) exceeds c exactly when the late values f(n)(x) clear c by some 1/(k + 1)",
					"∀x:A. x ∈ Ω ⇒ (c < g(x) ⇔ ∃k N:num. ∀m:num. c + real_inv(&k + &1) < f(N + m)(x))",
					Derive(func(d *Argument) {
						x := d.FixAs[A]("x")
						inΩ := d.Assume()
						d.Show(
							"the values f(n)(x) tend to g(x)",
							By(
								inΩ,
								converges.At(x),
								real_sequences.LimitAboveIff.At(d.TermAs[Fun[Nat, Real]]("λn:num. f(n)(x)"), g.Apply(x), c)))
					}))
				union := b.Have(
					"so the ray of g is the union over k and N of the points where every f(N + m) clears c + 1/(k + 1)",
					"{x:A | x ∈ Ω ∧ c < g(x)} = "+
						"⋃image(λk:num. ⋃image(λN:num. {x:A | x ∈ Ω ∧ ∀m:num. c + real_inv(&k + &1) < f(N + m)(x)}, 𝕌), 𝕌)",
					BySets(eventually))
				tails := b.Have(
					"each such set is measurable",
					"∀k N:num. {x:A | x ∈ Ω ∧ ∀m:num. c + real_inv(&k + &1) < f(N + m)(x)} ∈ S",
					Derive(func(d *Argument) {
						d.FixAs[Nat]("k")
						d.FixAs[Nat]("N")
						complement := d.Have(
							"it is what the sets where some f(N + m) stays at most c + 1/(k + 1) leave of Ω",
							"{x:A | x ∈ Ω ∧ ∀m:num. c + real_inv(&k + &1) < f(N + m)(x)} = "+
								"Ω ∖ ⋃image(λm:num. {x:A | x ∈ Ω ∧ f(N + m)(x) ≤ c + real_inv(&k + &1)}, 𝕌)",
							BySets(real_order_ring.NotLessThan))
						closed := d.Have(
							"each of those sets is measurable",
							"∀m:num. {x:A | x ∈ Ω ∧ f(N + m)(x) ≤ c + real_inv(&k + &1)} ∈ S",
							Derive(func(e *Argument) {
								e.FixAs[Nat]("m")
								later := e.TermAs[Nat]("N + m")
								e.Show(
									"a closed lower ray of the measurable f(N + m)",
									By(
										sigma,
										measurable.At(later),
										RealMeasurableAtMost.At(Ω, S, f.Apply(later), e.TermAs[Real]("c + real_inv(&k + &1)"))))
							}))
						union := d.Have(
							"so is their countable union",
							"⋃image(λm:num. {x:A | x ∈ Ω ∧ f(N + m)(x) ≤ c + real_inv(&k + &1)}, 𝕌) ∈ S",
							By(closed, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
						d.Show(
							"and what it leaves of Ω",
							By(complement, union, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
					}))
				stages := b.Have(
					"for each k, their union over N is measurable",
					"∀k:num. ⋃image(λN:num. {x:A | x ∈ Ω ∧ ∀m:num. c + real_inv(&k + &1) < f(N + m)(x)}, 𝕌) ∈ S",
					By(tails, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
				b.Do(union.Rw())
				b.Show(
					"and so is the union of those over k",
					By(stages, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
			}))
		a.Show(
			"upper rays decide measurability",
			By(sigma, rays, RealMeasurableIffRay.At(Ω, S, g)))
	}),
})}

// RealMeasurableIntegerPart — the integer part of a measurable function is
// measurable: below 0 every integer part exceeds c, and at or above 0, c has
// an integer part m of its own, an integer part exceeds c exactly when it is
// past m, and that is where h reaches m + 1 — a level set of h.
var RealMeasurableIntegerPart = realMeasurableIntegerPartThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableIntegerPart",
	Key:  "prop_7e3b28b7e4fd3fec",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀h:(A → real). ∀k:(A → num).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, h)",
			"∀x:A. x ∈ Ω ⇒ &k(x) ≤ h(x) ∧ h(x) < &k(x) + &1",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. &k(x))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		h *Arrow[A, Real],
		k *Arrow[A, Nat],
		sigma, measurable, integerPart Fact,
	) {
		rays := a.Have(
			"every upper ray of the integer part is measurable",
			"∀c:real. {x:A | x ∈ Ω ∧ c < &k(x)} ∈ S",
			Derive(func(b *Argument) {
				c := b.FixAs[Real]("c")
				nonneg := b.Assuming(
					b.TermAs[Bool]("&0 ≤ c"),
					"below 0 every integer part exceeds c, so the ray is all of Ω",
					Given(func(d *Argument, negative Fact) {
						everywhere := d.Have(
							"c lies below every &k(x)",
							"∀x:A. c < &k(x)",
							ByArith(negative))
						whole := d.Have(
							"so the ray is the carrier",
							"{x:A | x ∈ Ω ∧ c < &k(x)} = Ω",
							BySets(everywhere))
						d.Show(
							"which is measurable",
							By(whole, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
					}))
				m, bounds := b.ObtainAs[Nat](
					"c has an integer part m",
					"∃m:num. &m ≤ c ∧ c < &m + &1",
					By(nonneg, rational.NonnegIntegerPart.At(c)))
				crossing := b.Have(
					"on Ω, an integer part exceeds c exactly where h reaches m + 1",
					"∀x:A. x ∈ Ω ⇒ (c < &k(x) ⇔ &m + &1 ≤ h(x))",
					Derive(func(d *Argument) {
						x := d.FixAs[A]("x")
						inΩ := d.Assume()
						d.Cases(d.TermAs[Bool]("m < k(x)"))
						d.When(
							"past m, k(x) ≥ m + 1 exceeds c and h(x) ≥ k(x) reaches m + 1",
							func(e *Argument, past Fact) {
								e.Show(
									"both sides hold",
									ByArith(inΩ, integerPart.At(x), past, bounds))
							})
						d.Otherwise(
							"at or below m, k(x) ≤ m ≤ c and h(x) < k(x) + 1 ≤ m + 1",
							func(e *Argument, notPast Fact) {
								atMost := e.Have(
									"k(x) is at most m",
									"k(x) ≤ m",
									By(notPast, nat_order.NotLessThan.At(m, k.Apply(x))))
								e.Show(
									"both sides fail",
									ByArith(inΩ, integerPart.At(x), atMost, bounds))
							})
					}))
				levelSet := b.Have(
					"so the ray is the closed upper ray of h at m + 1",
					"{x:A | x ∈ Ω ∧ c < &k(x)} = {x:A | x ∈ Ω ∧ &m + &1 ≤ h(x)}",
					BySets(crossing))
				b.Do(levelSet.Rw())
				b.Show(
					"which is measurable, h being measurable",
					By(sigma, measurable, RealMeasurableAtLeast.At(Ω, S, h, b.TermAs[Real]("&m + &1"))))
			}))
		a.Show(
			"upper rays decide measurability",
			By(sigma, rays, RealMeasurableIffRay.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. &k(x)"))))
	}),
})}

// RealMeasurableIndicator — c times the indicator of a measurable set E is a
// measurable function: the set where it exceeds d is all of Ω, the part of
// Ω in E, the part of Ω outside E, or empty, as d lies below both of its
// values, below c alone, below 0 alone, or below neither.
var RealMeasurableIndicator = realMeasurableIndicatorThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableIndicator",
	Key:  "prop_ddb2c74c3e19e83e",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀E:set(A). ∀c:real.",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"E ∈ S",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. COND(x ∈ E, c, &0))",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], E *Expr[Set[A]], c *Expr[Real],
		sigma, measurable Fact) {
		laws := sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)
		operations := sigma_algebra.SigmaFiniteOperations.At(Ω, S)
		rays := a.Have(
			"every upper ray of the scaled indicator is measurable",
			"∀d:real. {x:A | x ∈ Ω ∧ d < COND(x ∈ E, c, &0)} ∈ S",
			Derive(func(b *Argument) {
				b.FixAs[Real]("d")
				b.Cases(b.Term("d < c"))
				b.When(
					"d lies below c",
					func(e *Argument, belowC Fact) {
						e.Cases(e.Term("d < &0"))
						e.When(
							"and below 0: the function exceeds d on all of Ω",
							func(f *Argument, belowZero Fact) {
								whole := f.Have(
									"so the ray is the carrier",
									"{x:A | x ∈ Ω ∧ d < COND(x ∈ E, c, &0)} = Ω",
									BySets(belowC, belowZero))
								f.Show(
									"which is measurable",
									By(whole, sigma, laws))
							})
						e.Otherwise(
							"but not below 0: the function exceeds d exactly on E",
							func(f *Argument, notBelowZero Fact) {
								onE := f.Have(
									"so the ray is the part of Ω in E",
									"{x:A | x ∈ Ω ∧ d < COND(x ∈ E, c, &0)} = Ω ∩ E",
									BySets(belowC, notBelowZero))
								f.Show(
									"which is measurable",
									By(onE, sigma, laws, operations, measurable))
							})
					})
				b.Otherwise(
					"d does not lie below c",
					func(e *Argument, notBelowC Fact) {
						e.Cases(e.Term("d < &0"))
						e.When(
							"but below 0: the function exceeds d exactly off E",
							func(f *Argument, belowZero Fact) {
								offE := f.Have(
									"so the ray is the part of Ω outside E",
									"{x:A | x ∈ Ω ∧ d < COND(x ∈ E, c, &0)} = Ω ∖ E",
									BySets(notBelowC, belowZero))
								f.Show(
									"which is measurable",
									By(offE, sigma, laws, measurable))
							})
						e.Otherwise(
							"nor below 0: the function exceeds d nowhere",
							func(f *Argument, notBelowZero Fact) {
								empty := f.Have(
									"so the ray is empty",
									"{x:A | x ∈ Ω ∧ d < COND(x ∈ E, c, &0)} = ∅",
									BySets(notBelowC, notBelowZero))
								f.Show(
									"which is measurable",
									By(empty, sigma, operations))
							})
					})
			}))
		a.Show(
			"upper rays decide measurability",
			By(sigma, rays, RealMeasurableIffRay.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ E, c, &0)"))))
	}),
})}

// RealMeasurableOnEvent — a measurable function kept on a measurable event
// and set to zero elsewhere stays measurable: it is the product of the function
// and the event's indicator.
var RealMeasurableOnEvent = realMeasurableOnEventThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableOnEvent",
	Key:  "prop_d830486a79cd9b5",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀E:set(A). ∀f:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"E ∈ S",
			"real_measurable(Ω, S, f)",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. COND(x ∈ E, f(x), &0))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		cutProduct := ctx.Lemma(
			"∀E:set(A). ∀u:(A → real). ∀x:A. COND(x ∈ E, u(x), &0) = u(x) * COND(x ∈ E, &1, &0)",
			func(a *Argument, E *Expr[Set[A]], u *Arrow[A, Real], x *Expr[A]) {
				a.Cases(a.TermAs[Bool]("x ∈ E"))
				a.When(
					"on the event the indicator is one",
					func(b *Argument, inside Fact) {
						b.Show(
							"the cut keeps the value of u",
							ByArith(inside))
					})
				a.Otherwise(
					"off the event the indicator is zero",
					func(b *Argument, outside Fact) {
						b.Show(
							"the cut and the product both vanish",
							ByArith(outside))
					})
			})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			E *Expr[Set[A]],
			f *Arrow[A, Real],
			sigma, event, measurable Fact,
		) {
			a.Show(
				"the cut is a product of measurable functions",
				By(
					sigma,
					event,
					measurable,
					At(cutProduct, E, f),
					RealMeasurableIndicator.At(Ω, S, E, a.TermAs[Real]("&1")),
					RealMeasurableMul.At(
						Ω, S, f, a.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ E, &1, &0)"))))
		})
	}),
})}

// RealMeasurableCut — a measurable function set to 0 on a measurable set N
// stays measurable. On Ω the cut function exceeds a negative level on N and
// wherever f does, and any other level off N where f does: the upper rays of
// the cut function are a union, or a difference, of measurable sets.
var RealMeasurableCut = realMeasurableCutThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableCut",
	Key:  "prop_cee9d6f806e1be77",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀N:set(A). ∀f:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"N ∈ S",
			"real_measurable(Ω, S, f)",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. COND(x ∉ N, f(x), &0))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		N *Expr[Set[A]],
		f *Arrow[A, Real],
		sigma, measurableN, measurable Fact,
	) {
		above := a.Have(
			"every upper ray of f is measurable",
			"∀t:real. {x:A | x ∈ Ω ∧ t < f(x)} ∈ S",
			By(sigma, measurable, RealMeasurableIffRay.At(Ω, S, f)))
		rays := a.Have(
			"every upper ray of the cut function is measurable",
			"∀d:real. {x:A | x ∈ Ω ∧ d < COND(x ∉ N, f(x), &0)} ∈ S",
			Derive(func(b *Argument) {
				d := b.FixAs[Real]("d")
				b.Cases(b.Term("d < &0"))
				b.When(
					"a negative level the cut function exceeds on N and wherever f does",
					func(c *Argument, negative Fact) {
						split := c.Have(
							"the ray is that of f together with the points of Ω in N",
							"{x:A | x ∈ Ω ∧ d < COND(x ∉ N, f(x), &0)} = {x:A | x ∈ Ω ∧ d < f(x)} ∪ (Ω ∩ N)",
							BySets(negative))
						c.Show(
							"a union of measurable sets, Ω being one",
							By(
								split,
								measurableN,
								above.At(d),
								sigma,
								sigma_algebra.SigmaAlgebraOnDef.At(Ω, S),
								sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
					})
				b.Otherwise(
					"any other level it exceeds off N where f does",
					func(c *Argument, notNegative Fact) {
						split := c.Have(
							"the ray is that of f less N",
							"{x:A | x ∈ Ω ∧ d < COND(x ∉ N, f(x), &0)} = {x:A | x ∈ Ω ∧ d < f(x)} ∖ N",
							BySets(notNegative))
						c.Show(
							"a difference of measurable sets",
							By(split, measurableN, above.At(d), sigma, sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
					})
			}))
		a.Show(
			"its rays decide its measurability",
			By(
				sigma,
				rays,
				RealMeasurableIffRay.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. COND(x ∉ N, f(x), &0)"))))
	}),
})}
