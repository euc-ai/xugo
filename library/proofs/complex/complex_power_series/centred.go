// centred.go — a power series about a centre c. Its sum on the disc of radius
// R about c has the derived series' sum as its derivative there, so it is
// holomorphic on the disc; at c it sums to its constant coefficient. A series
// whose sum is 0 near c, off c, has every coefficient 0, so two series with
// one sum near c have the same coefficients; and a series whose first m
// coefficients vanish is (z − c)ᵐ times the series of the rest.

package complex_power_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// PowerSeriesDerivativeDisc — the sum of a power series about c converging on
// the disc of radius R has, at each point w of the disc, the sum of the derived
// series as its derivative: moved to 0 the series is one in u = z − c, whose
// sum F(u) = f(u + c) has that derivative at w − c term by term, and f is F
// after z ↦ z − c, whose derivative is 1.
var PowerSeriesDerivativeDisc = powerSeriesDerivativeDiscThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesDerivativeDisc",
	Key:  "prop_418b0e10a4269666",
	Build: family.Theorem(Statement{
		Binders: "∀a:num → complex. ∀f:(complex → complex). ∀c:complex. ∀R:real. ∀w:complex.",
		Hypotheses: []string{
			"∀z:complex. |z - c| < R ⇒ complex_sums(λn:num. a(n) * (z - c) ^ n, f(z))",
			"|w - c| < R",
		},
		Conclusion: "∃d:complex. " +
			"    complex_sums(λn:num. &(n + 1) * a(n + 1) * (w - c) ^ n, d) ∧ complex_derivative_at(f, w, d)",
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Complex],
			f *Arrow[Complex, Complex],
			c *Expr[Complex],
			R *Expr[Real],
			w *Expr[Complex],
			sums, inside Fact,
		) {
			shifted := arg.Have(
				"moved to 0, the series in u sums to f(u + c) for |u| < R",
				"∀u:complex. |u| < R ⇒ complex_sums(λn:num. a(n) * u ^ n, f(u + c))",
				Derive(func(e *Argument) {
					e.FixAs[Complex]("u")
					small := e.Assume()
					back := e.Have(
						"u + c lies at u from c",
						"u + c - c = u",
						ByArith())
					e.Show(
						"this is the series at z = u + c",
						By(Normalized, sums.At(e.TermAs[Complex]("u + c")), back, small))
				}))
			moved := arg.TermAs[Fun[Complex, Complex]]("λu:complex. f(u + c)")
			translate := arg.TermAs[Fun[Complex, Complex]]("λz:complex. z - c")
			one := arg.TermAs[Complex]("complex_of_real(&1)")
			d, derived := arg.UnpackAs[Complex](
				GroupPremises(
					shifted,
					inside,
					PowerSeriesDerivative.At(a, moved, R, arg.TermAs[Complex]("w - c"))),
				"d")
			units := arg.Have(
				"1 − 0 is 1, and d·1 is d",
				"complex_of_real(&1) - &0 = &1 ∧ d * &1 = d",
				ByArith())
			translation := arg.Have(
				"z ↦ z − c has derivative 1, the identity's 1 less the constant's 0",
				"complex_derivative_at(λz:complex. z - c, w, &1)",
				By(
					units,
					complex_derivative.DerivativeSub.At(
						arg.TermAs[Fun[Complex, Complex]]("λz:complex. z"),
						arg.TermAs[Fun[Complex, Complex]]("λz:complex. c"),
						w,
						one,
						arg.TermAs[Complex]("complex_of_real(&0)")),
					complex_derivative.DerivativeId.At(w),
					complex_derivative.DerivativeConst.At(w, c)))
			chained := arg.Have(
				"so by the chain rule u ↦ f(u + c) after z ↦ z − c has derivative d·1 = d at w",
				"complex_derivative_at((λu:complex. f(u + c)) ∘ (λz:complex. z - c), w, d)",
				By(units, derived, translation, complex_derivative.DerivativeChain.At(moved, translate, w, d, one)))
			undo := arg.Have(
				"that composite takes z to f((z − c) + c) = f(z)",
				"∀z:complex. f(z - c + c) = f(z)",
				Derive(func(e *Argument) {
					e.FixAs[Complex]("z")
					back := e.Have(
						"(z − c) + c is z",
						"z - c + c = z",
						ByArith())
					e.Show(
						"so f takes the same value at both",
						By(Normalized, back))
				}))
			arg.Take(d)
			arg.Show(
				"so f has derivative d at w, the derived series' sum",
				By(derived, chained, undo, functions.ComposeApply))
		}),
})}

// PowerSeriesHolomorphicDisc — the sum of a power series about c that
// converges on the disc of radius R about c is holomorphic there: at each
// point of the disc it has a derivative, the sum of the derived series.
var PowerSeriesHolomorphicDisc = powerSeriesHolomorphicDiscThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesHolomorphicDisc",
	Key:  "prop_a20b4edfb7e16155",
	Build: family.Theorem(Statement{
		Binders: "∀a:num → complex. ∀f:(complex → complex). ∀c:complex. ∀R:real.",
		Hypotheses: []string{
			"∀z:complex. |z - c| < R ⇒ complex_sums(λn:num. a(n) * (z - c) ^ n, f(z))",
		},
		Conclusion: "holomorphic_on({z:complex | |z - c| < R}, f)",
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Complex],
			f *Arrow[Complex, Complex],
			c *Expr[Complex],
			R *Expr[Real],
			sums Fact,
		) {
			arg.Do(Unfold(complex_derivative.HolomorphicOnDef))
			z := arg.FixAs[Complex]("z")
			inDisc := arg.Assume()
			inside := arg.Have(
				"z is within R of c",
				"|z - c| < R",
				By(inDisc))
			d, derived := arg.UnpackAs[Complex](
				GroupPremises(sums, inside, PowerSeriesDerivativeDisc.At(a, f, c, R, z)),
				"d")
			arg.Take(d)
			arg.Show(
				"at z the derived series sums to a derivative d of f",
				By(derived))
		}),
})}

// PowerSeriesAtCentre — at its centre a power series sums to its constant
// coefficient: every later term carries a factor c − c = 0, so the series with
// its first term dropped sums to 0.
var PowerSeriesAtCentre = powerSeriesAtCentreThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesAtCentre",
	Key:  "prop_6acd235662b2cdb1",
	Build: family.Theorem("∀a:num → complex. ∀c:complex. "+
		"    complex_sums(λn:num. a(n) * (c - c) ^ n, a(0))",
		func(arg *Argument, a *Arrow[Nat, Complex], c *Expr[Complex]) {
			later := arg.Have(
				"every term after the first carries the factor c − c = 0",
				"∀n:num. a(n + 1) * (c - c) ^ (n + 1) = &0",
				Derive(func(d *Argument) {
					d.FixAs[Nat]("n")
					d.Show(
						"(c − c)ⁿ⁺¹ is (c − c)ⁿ·(c − c), a multiple of 0",
						Simp(
							Fwd(comm_monoid.PowAdd.Read(complex_field.MulMonoid)),
							Fwd(comm_monoid.PowOne.Read(complex_field.MulMonoid))),
						ByArith())
				}))
			first := arg.Have(
				"the first term is a(0)·(c − c)⁰ = a(0)",
				"a(0) - a(0) * (c - c) ^ 0 = &0",
				Simp(Fwd(comm_monoid.MonoidPowDef.Inst[Complex]())),
				ByArith())
			arg.Show(
				"so the series with its first term dropped sums to a(0) − a(0) = 0, a series of zeros",
				By(
					later,
					first,
					complex_series.SumsShift.At(
						arg.TermAs[Fun[Nat, Complex]]("λn:num. a(n) * (c - c) ^ n"), a.Apply(arg.TermAs[Nat]("0"))),
					complex_series.SumsOfReal,
					real_series.SumsZero))
		}),
})}

// CoefficientsVanish — a power series about c whose sum is 0 at every point of
// a punctured disc about c has every coefficient 0. The constant coefficient
// is 0: the function H equal to a(0) at c and to 0 elsewhere is the sum of the
// series on the whole disc, so it is holomorphic there and continuous at c,
// while it is 0 at points as near c as we like, which forces a(0) = 0.
// Dropping the first term and dividing the rest by z − c gives a series of the
// same kind whose coefficients are the remaining ones, so induction on the
// index, over every such series at once, carries the vanishing to every
// coefficient.
var CoefficientsVanish = coefficientsVanishThm{family.Add(registry.ProofEntry{
	Name: "CoefficientsVanish",
	Key:  "prop_9b394bdd308e6410",
	Build: family.Sections(Statement{
		Binders: "∀a:num → complex. ∀c:complex. ∀ρ:real. ∀n:num.",
		Hypotheses: []string{
			"&0 < ρ",
			"∀z:complex. &0 < |z - c| ∧ |z - c| < ρ ⇒ complex_sums(λk:num. a(k) * (z - c) ^ k, &0)",
		},
		Conclusion: "a(n) = &0",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			constant := ctx.Lemma(Statement{
				Binders: "∀x:num → complex. ∀c:complex. ∀ρ:real.",
				Hypotheses: []string{
					"&0 < ρ",
					"∀z:complex. &0 < |z - c| ∧ |z - c| < ρ ⇒ complex_sums(λn:num. x(n) * (z - c) ^ n, &0)",
				},
				Conclusion: "x(0) = &0",
			},
				func(
					arg *Argument,
					x *Arrow[Nat, Complex],
					c *Expr[Complex],
					ρ *Expr[Real],
					positive, vanishes Fact,
				) {
					sums := arg.Have(
						"the series sums at every z of the disc to H(z), which is x(0) at c and 0 elsewhere",
						Statement{
							Binders: "∀z:complex.",
							Hypotheses: []string{
								"|z - c| < ρ",
							},
							Conclusion: "complex_sums(λn:num. x(n) * (z - c) ^ n, COND(z = c, x(0), complex_of_real(&0)))",
						},
						Derive(func(d *Argument) {
							z := d.FixAs[Complex]("z")
							inside := d.Assume()
							d.Cases(d.TermAs[Bool]("z = c"))
							d.When(
								"at the centre the series sums to its constant coefficient",
								func(b *Argument, centre Fact) {
									b.Show(
										"which is H(c) = x(0)",
										By(Normalized, centre, PowerSeriesAtCentre.At(x, c)))
								})
							d.Otherwise(
								"off the centre it sums to 0 by hypothesis",
								func(b *Argument, apart Fact) {
									b.Show(
										"which is H(z)",
										ByArith(apart, inside, vanishes.At(z), complex_abs.AbsPosIffNonzero.At(b.TermAs[Complex]("z - c"))))
								})
						}))
					H := arg.TermAs[Fun[Complex, Complex]]("λz:complex. COND(z = c, x(0), complex_of_real(&0))")
					disc := arg.TermAs[Set[Complex]]("{z:complex | |z - c| < ρ}")
					centre := arg.Have(
						"the centre lies in the disc",
						"c ∈ {z:complex | |z - c| < ρ}",
						ByArith(positive, complex_abs.AbsEqZero.At(arg.TermAs[Complex]("c - c"))))
					continuous := arg.Have(
						"H, the sum of a power series on the disc, is holomorphic there, so continuous at c",
						"complex_continuous_at(λz:complex. COND(z = c, x(0), complex_of_real(&0)), c)",
						By(
							sums,
							PowerSeriesHolomorphicDisc.At(x, H, c, ρ),
							centre,
							complex_derivative.HolomorphicOnContinuousAt.At(disc, H, c)))
					nonzero := arg.SupposeNot()
					x0 := x.Apply(arg.TermAs[Nat]("0"))
					size := arg.Have(
						"were x(0) not 0, |x(0)| would be a positive ε",
						"&0 < |x(0)|",
						By(nonzero, complex_abs.AbsPosIffNonzero.At(x0)))
					near := arg.Unfolded(continuous, complex_topology.ComplexContinuousAtDef)
					δ, radius := arg.UnpackAs[Real](GroupPremises(size, near.At(arg.TermAs[Real]("|x(0)|"))), "δ")
					parts := arg.Conjuncts(
						radius,
						"δ is positive",
						"within δ of c, H is within |x(0)| of H(c)")
					point := arg.Have(
						"the point c + δ/2 lies within δ of c and is not c",
						"c + &(δ / &2) ≠ c ∧ |c + &(δ / &2) - c| < δ",
						ByArith(
							parts[0],
							complex_topology.PuncturedDiscPoint.At(c, δ),
							complex_abs.AbsPosIffNonzero.At(arg.TermAs[Complex]("c + &(δ / &2) - c"))))
					negate := arg.Have(
						"there H is 0 and H(c) is x(0), so H differs from H(c) by 0 − x(0) = −x(0)",
						"&0 - x(0) = -x(0)",
						ByArith())
					arg.Show(
						"whose modulus |x(0)| is not below |x(0)|",
						ByArith(
							negate,
							point,
							parts[1].At(arg.TermAs[Complex]("c + &(δ / &2)")),
							complex_abs.AbsNeg.At(x0)))
				})
			return ctx.Theorem(headline,
				func(
					arg *Argument,
					a *Arrow[Nat, Complex],
					c *Expr[Complex],
					ρ *Expr[Real],
					n *Expr[Nat],
					positive, vanishes Fact,
				) {
					every := arg.Have(
						"for every m, each sequence whose series vanishes off c has m-th coefficient 0",
						Statement{
							Binders: "∀m:num. ∀x:num → complex.",
							Hypotheses: []string{
								"∀z:complex. &0 < |z - c| ∧ |z - c| < ρ ⇒ complex_sums(λk:num. x(k) * (z - c) ^ k, &0)",
							},
							Conclusion: "x(m) = &0",
						},
						Derive(func(d *Argument) {
							d.Induct("m")
							d.Base(
								"the constant coefficient is 0",
								By(positive, constant))
							d.Step(
								"x(m + 1) is the m-th coefficient of the series of x(k + 1), which vanishes off c too",
								func(b *Argument, ih Fact) {
									b.FixAs[Fun[Nat, Complex]]("x")
									hx := b.Assume()
									first := b.Have(
										"the constant coefficient x(0) is 0",
										"x(0) = &0",
										By(positive, hx, constant))
									shifted := b.Have(
										"the series of x(k + 1) also sums to 0 off c",
										"∀z:complex. &0 < |z - c| ∧ |z - c| < ρ ⇒ complex_sums(λk:num. x(k + 1) * (z - c) ^ k, &0)",
										Derive(func(e *Argument) {
											z := e.FixAs[Complex]("z")
											off := e.Assume()
											divide := e.Have(
												"dividing x(k + 1)(z − c)ᵏ⁺¹ by z − c leaves x(k + 1)(z − c)ᵏ",
												"∀k:num. complex_inv(z - c) * (x(k + 1) * (z - c) ^ (k + 1)) = x(k + 1) * (z - c) ^ k",
												Derive(func(g *Argument) {
													g.FixAs[Nat]("k")
													g.Show(
														"(z − c)ᵏ⁺¹ is (z − c)ᵏ·(z − c), and (z − c)/(z − c) is 1",
														Simp(
															Fwd(comm_monoid.PowAdd.Read(complex_field.MulMonoid)),
															Fwd(comm_monoid.PowOne.Read(complex_field.MulMonoid))),
														ByArith(off, complex_abs.AbsPosIffNonzero.At(g.TermAs[Complex]("z - c"))))
												}))
											rest := e.Have(
												"the series less its first term x(0) = 0 still sums to 0, and so does its quotient by z − c",
												"complex_inv(z - c) * (&0 - x(0) * (z - c) ^ 0) = &0",
												first.Rw(),
												ByArith())
											e.Show(
												"drop the first term of the series and divide the rest by z − c",
												By(
													hx.At(z),
													off,
													divide,
													rest,
													complex_series.SumsShift.At(
														e.TermAs[Fun[Nat, Complex]]("λk:num. x(k) * (z - c) ^ k"),
														e.TermAs[Complex]("complex_of_real(&0)")),
													complex_series.SumsScale.At(
														e.TermAs[Fun[Nat, Complex]]("λk:num. x(k + 1) * (z - c) ^ (k + 1)"),
														e.TermAs[Complex]("&0 - x(0) * (z - c) ^ 0"),
														e.TermAs[Complex]("complex_inv(z - c)"))))
										}))
									index := b.Have(
										"suc(m) is m + 1",
										"suc(m) = m + 1",
										ByArith())
									b.Show(
										"so x(m + 1) = 0 by the induction hypothesis at k ↦ x(k + 1)",
										By(index, shifted, ih.At(b.TermAs[Fun[Nat, Complex]]("λk:num. x(k + 1)"))))
								})
						}))
					arg.Show(
						"in particular a(n) = 0",
						By(vanishes, every.At(n, a)))
				})
		}),
})}

// CoefficientsUnique — two power series about c with the same sum at every
// point of a disc about c have the same coefficients: off c the series of the
// differences a(n) − b(n) sums to g(z) − g(z) = 0, so each difference is 0.
var CoefficientsUnique = coefficientsUniqueThm{family.Add(registry.ProofEntry{
	Name: "CoefficientsUnique",
	Key:  "prop_d6dad600f0ab3561",
	Build: family.Theorem(Statement{
		Binders: "∀a b:num → complex. ∀g:(complex → complex). ∀c:complex. ∀ρ:real.",
		Hypotheses: []string{
			"&0 < ρ",
			"∀z:complex. |z - c| < ρ ⇒ complex_sums(λn:num. a(n) * (z - c) ^ n, g(z))",
			"∀z:complex. |z - c| < ρ ⇒ complex_sums(λn:num. b(n) * (z - c) ^ n, g(z))",
		},
		Conclusion: "a = b",
	},
		func(
			arg *Argument,
			a, b *Arrow[Nat, Complex],
			g *Arrow[Complex, Complex],
			c *Expr[Complex],
			ρ *Expr[Real],
			positive, sumsA, sumsB Fact,
		) {
			difference := arg.Have(
				"off c the series of the differences a(n) − b(n) sums to g(z) − g(z) = 0",
				"∀z:complex. &0 < |z - c| ∧ |z - c| < ρ ⇒ complex_sums(λn:num. (a(n) - b(n)) * (z - c) ^ n, &0)",
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					off := d.Assume()
					termwise := d.Have(
						"termwise, a(n)(z − c)ⁿ − b(n)(z − c)ⁿ is (a(n) − b(n))(z − c)ⁿ",
						"∀n:num. a(n) * (z - c) ^ n - b(n) * (z - c) ^ n = (a(n) - b(n)) * (z - c) ^ n",
						d.ForEach(func(n *Expr[Nat]) Action { return ByArith() }))
					cancel := d.Have(
						"g(z) − g(z) is 0",
						"g(z) - g(z) = &0",
						ByArith())
					gz := g.Apply(z)
					d.Show(
						"the difference of two series sums to the difference of their sums",
						By(
							sumsA.At(z),
							sumsB.At(z),
							off,
							termwise,
							cancel,
							complex_series.SumsSub.At(
								d.TermAs[Fun[Nat, Complex]]("λn:num. a(n) * (z - c) ^ n"),
								d.TermAs[Fun[Nat, Complex]]("λn:num. b(n) * (z - c) ^ n"),
								gz,
								gz)))
				}))
			equal := arg.Have(
				"so every coefficient of the differences vanishes",
				"∀n:num. a(n) = b(n)",
				arg.ForEach(func(n *Expr[Nat]) Action {
					return ByArith(
						positive,
						difference,
						CoefficientsVanish.At(arg.TermAs[Fun[Nat, Complex]]("λk:num. a(k) - b(k)"), c, ρ, n))
				}))
			arg.Show(
				"so a and b agree at every index",
				By(Normalized, equal))
		}),
})}

// PowerSeriesFactor — a power series about c whose first m coefficients vanish
// is (z − c)ᵐ times the power series of the remaining coefficients, which
// converges wherever the first does. Dropping m leading zero terms leaves the
// sum of a series unchanged. Off c the remaining series is the tail of the
// first divided by (z − c)ᵐ, and at c every power series converges; (z − c)ᵐ
// times its sum is the sum of the tail, f(z).
var PowerSeriesFactor = powerSeriesFactorThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesFactor",
	Key:  "prop_e1695b02c315b31",
	Build: family.Sections(Statement{
		Binders: "∀a:num → complex. ∀f:(complex → complex). ∀c:complex. ∀R:real. ∀m:num.",
		Hypotheses: []string{
			"∀z:complex. |z - c| < R ⇒ complex_sums(λn:num. a(n) * (z - c) ^ n, f(z))",
			"∀k:num. k < m ⇒ a(k) = &0",
		},
		Conclusion: "∃h:(complex → complex). " +
			"    (∀z:complex. |z - c| < R ⇒ complex_sums(λn:num. a(n + m) * (z - c) ^ n, h(z))) ∧ " +
			"    (∀z:complex. |z - c| < R ⇒ f(z) = (z - c) ^ m * h(z))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			offset := ctx.Lemma(Statement{
				Binders: "∀m:num. ∀x:num → complex. ∀s:complex.",
				Hypotheses: []string{
					"∀k:num. k < m ⇒ x(k) = &0",
					"complex_sums(x, s)",
				},
				Conclusion: "complex_sums(λn:num. x(n + m), s)",
			},
				func(arg *Argument) {
					arg.Induct("m")
					arg.Base(
						"dropping no terms leaves the series as it was",
						func(b *Argument) {
							b.FixAs[Fun[Nat, Complex]]("x")
							b.FixAs[Complex]("s")
							given := b.Assume()
							b.Show(
								"x(n + 0) is x(n)",
								Simp(Fwd(nat_arith.AddZero)),
								By(given))
						})
					arg.Step(
						"dropping m + 1 zeros is dropping the first, then m more from x(n + 1)",
						func(b *Argument, ih Fact) {
							x := b.FixAs[Fun[Nat, Complex]]("x")
							s := b.FixAs[Complex]("s")
							given := b.Assume()
							parts := b.Conjuncts(
								given,
								"the first m + 1 terms of x are 0",
								"x sums to s")
							first := b.Have(
								"in particular x(0) is 0",
								"x(0) = &0",
								ByArith(parts[0].At(b.TermAs[Nat]("0"))))
							unchanged := b.Have(
								"so dropping it leaves the sum s",
								"s - x(0) = s",
								first.Rw(),
								ByArith())
							later := b.Have(
								"and the first m terms of x(n + 1) are 0",
								"∀k:num. k < m ⇒ x(k + 1) = &0",
								ByArith(parts[0]))
							b.Show(
								"x(n + m + 1) is x(n + 1) with its first m terms dropped",
								Simp(Fwd(nat_arith.Add1), Fwd(nat_arith.AddAssoc)),
								By(
									ih.At(b.TermAs[Fun[Nat, Complex]]("λn:num. x(n + 1)"), s),
									later,
									parts[1],
									unchanged,
									complex_series.SumsShift.At(x, s)))
						})
				})
			return ctx.Theorem(headline,
				func(
					arg *Argument,
					a *Arrow[Nat, Complex],
					f *Arrow[Complex, Complex],
					c *Expr[Complex],
					R *Expr[Real],
					m *Expr[Nat],
					sums, early Fact,
				) {
					tail := arg.Have(
						"dropping the first m terms, all 0, leaves the sum f(z)",
						"∀z:complex. |z - c| < R ⇒ complex_sums(λn:num. a(n + m) * (z - c) ^ (n + m), f(z))",
						Derive(func(d *Argument) {
							z := d.FixAs[Complex]("z")
							inside := d.Assume()
							zeros := d.Have(
								"the first m terms a(k)·(z − c)ᵏ are 0",
								"∀k:num. k < m ⇒ a(k) * (z - c) ^ k = &0",
								Derive(func(e *Argument) {
									k := e.FixAs[Nat]("k")
									below := e.Assume()
									e.Show(
										"a(k) is 0",
										ByArith(early.At(k), below))
								}))
							d.Show(
								"drop them from the series at z",
								By(
									sums.At(z),
									inside,
									zeros,
									At(offset, m, d.TermAs[Fun[Nat, Complex]]("λn:num. a(n) * (z - c) ^ n"), f.Apply(z))))
						}))
					converges := arg.Have(
						"the series of the remaining coefficients converges at every point of the disc",
						"∀z:complex. |z - c| < R ⇒ ∃t:complex. complex_sums(λn:num. a(n + m) * (z - c) ^ n, t)",
						Derive(func(d *Argument) {
							z := d.FixAs[Complex]("z")
							inside := d.Assume()
							apart := d.Unless(
								d.TermAs[Bool]("z = c"),
								"at the centre a power series converges, to its constant coefficient",
								Given(func(b *Argument, centre Fact) {
									b.Do(centre.Rw())
									b.Show(
										"here a(0 + m)",
										By(PowerSeriesAtCentre.At(b.TermAs[Fun[Nat, Complex]]("λn:num. a(n + m)"), c)))
								}))
							nonzero := d.Have(
								"(z − c)ᵐ is not 0, z − c not being 0",
								"(z - c) ^ m ≠ &0",
								ByArith(apart, field.PowEqZero.Read(complex_field.Field).At(d.TermAs[Complex]("z - c"), m)))
							termwise := d.Have(
								"termwise, a(n + m)(z − c)ⁿ⁺ᵐ divided by (z − c)ᵐ is a(n + m)(z − c)ⁿ",
								"∀n:num. complex_inv((z - c) ^ m) * (a(n + m) * (z - c) ^ (n + m)) = a(n + m) * (z - c) ^ n",
								Derive(func(e *Argument) {
									e.FixAs[Nat]("n")
									e.Show(
										"(z − c)ⁿ⁺ᵐ is (z − c)ⁿ·(z − c)ᵐ, and (z − c)ᵐ cancels its inverse",
										Simp(Fwd(comm_monoid.PowAdd.Read(complex_field.MulMonoid))),
										ByArith(nonzero))
								}))
							d.Take(d.TermAs[Complex]("complex_inv((z - c) ^ m) * f(z)"))
							d.Show(
								"off the centre it is the tail divided by (z − c)ᵐ, summing to f(z)/(z − c)ᵐ",
								Simp(Rev(termwise)),
								By(
									tail.At(z),
									inside,
									complex_series.SumsScale.At(
										d.TermAs[Fun[Nat, Complex]]("λn:num. a(n + m) * (z - c) ^ (n + m)"),
										f.Apply(z),
										d.TermAs[Complex]("complex_inv((z - c) ^ m)"))))
						}))
					h, sumsH := arg.ObtainAs[Fun[Complex, Complex]](
						"choose at each point of the disc a sum h(z) of the remaining series",
						"∃h:(complex → complex). ∀z:complex. "+
							"    |z - c| < R ⇒ complex_sums(λn:num. a(n + m) * (z - c) ^ n, h(z))",
						By(converges))
					factor := arg.Have(
						"(z − c)ᵐ·h(z) is the sum of the tail, which is f(z)",
						"∀z:complex. |z - c| < R ⇒ f(z) = (z - c) ^ m * h(z)",
						Derive(func(d *Argument) {
							z := d.FixAs[Complex]("z")
							inside := d.Assume()
							termwise := d.Have(
								"termwise, (z − c)ᵐ·a(n + m)(z − c)ⁿ is a(n + m)(z − c)ⁿ⁺ᵐ",
								"∀n:num. (z - c) ^ m * (a(n + m) * (z - c) ^ n) = a(n + m) * (z - c) ^ (n + m)",
								Derive(func(e *Argument) {
									e.FixAs[Nat]("n")
									e.Show(
										"(z − c)ⁿ⁺ᵐ is (z − c)ⁿ·(z − c)ᵐ",
										Simp(Fwd(comm_monoid.PowAdd.Read(complex_field.MulMonoid))),
										ByArith())
								}))
							scaled := d.Have(
								"so the tail also sums to (z − c)ᵐ·h(z)",
								"complex_sums(λn:num. a(n + m) * (z - c) ^ (n + m), (z - c) ^ m * h(z))",
								Simp(Rev(termwise)),
								By(
									sumsH.At(z),
									inside,
									complex_series.SumsScale.At(
										d.TermAs[Fun[Nat, Complex]]("λn:num. a(n + m) * (z - c) ^ n"),
										d.TermAs[Complex]("h(z)"),
										d.TermAs[Complex]("(z - c) ^ m"))))
							d.Show(
								"a series has one sum",
								By(
									tail.At(z),
									inside,
									scaled,
									complex_series.SumsUnique.At(
										d.TermAs[Fun[Nat, Complex]]("λn:num. a(n + m) * (z - c) ^ (n + m)"),
										f.Apply(z),
										d.TermAs[Complex]("(z - c) ^ m * h(z)"))))
						}))
					arg.Take(h)
					arg.Show(
						"h sums the remaining series and (z − c)ᵐ·h is f",
						By(sumsH, factor))
				})
		}),
})}
