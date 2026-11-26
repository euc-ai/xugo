// poles.go — poles and zeros: the residue and the principal part read off the
// regular part's power series (ResidueAtPole, PrincipalPart,
// PrincipalPartAtPole) and a principal part's holomorphy off its pole
// (PrincipalPartHolomorphic); the orders of a pole and of a zero, each the
// one exponent a factorization can have (VanishesAtCentre, PoleFactorUnique,
// PoleOrderUnique, ZeroOrderUnique); the residue of G(z)/(z − c)
// (SimplePoleResidue); the residues of a logarithmic derivative
// (LogDerivativeResidue, LogDerivativeAtZero, LogDerivativeAtPole); a
// function near a proper pole, unbounded and holomorphic off it, and near a
// point of continuity, with no pole (PoleUnbounded, PolePuncturedHolomorphic,
// NoPoleNearContinuity); and in a smaller closed disc, finitely many poles
// and finitely many zeros off them (PolesFiniteInClosedDisc,
// ZerosFiniteOffPoles).

package residue

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/cauchy_integral"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_power_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ResidueAtPole — at a pole of order at most m + 1, where f(z) is
// g(z)/(z − c)ᵐ⁺¹ off c and g is the sum of Σ b(n)(z − c)ⁿ on a disc about c,
// the residue of f at c is b(m). The residue is the w that some radius ρ
// gives, f holomorphic on the punctured disc of radius ρ and the integral of
// f round the circle of radius ρ/2 being 2πi·w; r is one such radius. For
// any, the function G equal to g(c) at c and to f(z)(z − c)ᵐ⁺¹ elsewhere is
// holomorphic on the disc of radius ρ: near c it is g, near any other point
// it is the product f(z)(z − c)ᵐ⁺¹. Its power series about c, its
// coefficients read off the circle of radius ρ/2, sums to G = g near c, so
// they are b's; round that circle f is G/(z − c)ᵐ⁺¹, whose integral is 2πi
// times G's m-th coefficient. So every such radius gives 2πi·b(m), and the
// residue is b(m).
var ResidueAtPole = residueAtPoleThm{family.Add(registry.ProofEntry{
	Name: "ResidueAtPole",
	Key:  "prop_3a069159b155243c",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀b:num → complex. ∀c:complex. ∀r:real. ∀m:num.",
		Hypotheses: []string{
			"&0 < r",
			"∀z:complex. |z - c| < r ⇒ complex_sums(λn:num. b(n) * (z - c) ^ n, g(z))",
			"∀z:complex. z ∈ «punctured»(c, r) ⇒ f(z) = g(z) / (z - c) ^ (m + 1)",
		},
		Conclusion: "complex_residue(f, c) = b(m)",
		Abbrev: Abbrev{
			{Name: "G", Text: "λz:complex. COND(z = c, g(c), f(z) * (z - c) ^ (m + 1))"},
		},
	},
		func(
			a *Argument,
			f, g *Arrow[Complex, Complex],
			b *Arrow[Nat, Complex],
			c *Expr[Complex],
			r *Expr[Real],
			m *Expr[Nat],
			positive, sums, pole Fact,
		) {
			order := a.TermAs[Nat]("m + 1")
			G := a.TermAs[Fun[Complex, Complex]]("«G»")
			product := a.TermAs[Fun[Complex, Complex]]("λu:complex. f(u) * (u - c) ^ (m + 1)")
			power := a.TermAs[Fun[Complex, Complex]]("λu:complex. (u - c) ^ (m + 1)")
			shift := a.TermAs[Fun[Complex, Complex]]("λu:complex. u - c")
			disc := a.TermAs[Set[Complex]]("«disc»(c, r)")
			holomorphic := a.Have(
				"g, the sum of a power series on the disc of radius r, is holomorphic there",
				"holomorphic_on(«disc»(c, r), g)",
				By(sums, complex_power_series.PowerSeriesHolomorphicDisc.At(b, g, c, r)))
			centre := a.Have(
				"c lies in that disc",
				"|c - c| < r",
				ByArith(positive, complex_abs.AbsEqZero.At(a.TermAs[Complex]("c - c"))))
			powers := a.Have(
				"off c, z − c is not 0, and so neither is (z − c)ᵐ⁺¹",
				"∀z:complex. &0 < |z - c| ⇒ (z - c) ^ (m + 1) ≠ &0",
				Derive(func(d *Argument) {
					d.FixAs[Complex]("z")
					off := d.Assume()
					difference := d.TermAs[Complex]("z - c")
					d.Show(
						"a power of a nonzero number is not 0",
						ByArith(
							off,
							complex_abs.AbsPosIffNonzero.At(difference),
							field.PowEqZero.Read(complex_field.Field).At(difference, order)))
				}))
			translation := a.Have(
				"z − c, a difference of the identity and a constant, is holomorphic on every set",
				"∀s:set(complex). holomorphic_on(s, λz:complex. z - c)",
				a.ForEach(func(s *Expr[Set[Complex]]) Action {
					return By(
						complex_derivative.HolomorphicOnId.At(s),
						complex_derivative.HolomorphicOnConst.At(s, c),
						complex_derivative.HolomorphicOnSub.At(
							s,
							a.TermAs[Fun[Complex, Complex]]("λz:complex. z"),
							a.TermAs[Fun[Complex, Complex]]("λz:complex. c")))
				}))
			agree := a.Have(
				"on the disc of radius r, G is g: at c by its definition, elsewhere since f(z)·(z − c)ᵐ⁺¹ = g(z)",
				"∀z:complex. |z - c| < r ⇒ «G»(z) = g(z)",
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					inside := d.Assume()
					d.Cases(d.TermAs[Bool]("z = c"))
					d.When(
						"at c, G is g(c)",
						func(e *Argument, atCentre Fact) {
							e.Show(
								"which is g(z)",
								By(Normalized, atCentre))
						})
					d.Otherwise(
						"off c, f(z) is g(z)/(z − c)ᵐ⁺¹, and (z − c)ᵐ⁺¹ cancels",
						func(e *Argument, apart Fact) {
							off := e.Have(
								"z is at positive distance from c",
								"&0 < |z - c|",
								ByArith(apart, complex_abs.AbsPosIffNonzero.At(e.TermAs[Complex]("z - c"))))
							e.Do(GroupPremises(off, inside, pole.At(z)).Rw())
							e.Show(
								"g(z)/(z − c)ᵐ⁺¹·(z − c)ᵐ⁺¹ is g(z)",
								ByArith(apart, off, powers.At(z)))
						})
				}))
			every := a.Have(
				"every radius ρ on whose punctured disc f is holomorphic "+
					"gives the circle of radius ρ/2 the integral 2πi·b(m)",
				Statement{
					Binders: "∀ρ:real.",
					Hypotheses: []string{
						"&0 < ρ",
						"holomorphic_on(«punctured»(c, ρ), f)",
					},
					Conclusion: "«circleInt»(f, c, ρ / &2) = &(&2 * pi) * complex_i * b(m)",
				},
				Derive(func(d *Argument) {
					ρ := d.FixAs[Real]("ρ")
					given := d.Assume()
					parts := d.Conjuncts(
						given,
						"ρ is positive",
						"f is holomorphic on the punctured disc of radius ρ")
					punctured := d.TermAs[Set[Complex]]("«punctured»(c, ρ)")
					half := d.TermAs[Real]("ρ / &2")
					factor := d.Have(
						"so is F(u) = f(u)·(u − c)ᵐ⁺¹",
						"holomorphic_on(«punctured»(c, ρ), λu:complex. f(u) * (u - c) ^ (m + 1))",
						By(
							translation.At(punctured),
							parts[1],
							complex_derivative.HolomorphicOnPow.At(punctured, shift, order),
							complex_derivative.HolomorphicOnMul.At(punctured, f, power)))
					holomorphicG := d.Have(
						"G is holomorphic on the disc of radius ρ: near c it is g, and near any other point it is F",
						"holomorphic_on(«disc»(c, ρ), «G»)",
						Derive(func(e *Argument) {
							e.Do(Simp(Fwd(complex_derivative.HolomorphicOnDef)))
							z := e.FixAs[Complex]("z")
							within := e.Assume()
							e.Cases(e.TermAs[Bool]("z = c"))
							e.When(
								"at c, G agrees with g on the disc of radius r, and g has a derivative there",
								func(h *Argument, atCentre Fact) {
									h.Do(atCentre.Rw())
									l, slope := h.ObtainAs[Complex](
										"g has a derivative l at c",
										"∃l:complex. complex_derivative_at(g, c, l)",
										By(centre, holomorphic, complex_derivative.HolomorphicOnDef))
									h.Take(l)
									h.Show(
										"so G has the derivative l at c",
										By(positive, agree, slope, complex_derivative.DerivativeLocal.At(G, g, c, l, r)))
								})
							e.Otherwise(
								"off c, G agrees with F on the disc about z of radius |z − c|, which misses c",
								func(h *Argument, apart Fact) {
									distance := h.TermAs[Real]("|z - c|")
									off := h.Have(
										"z is at positive distance from c",
										"&0 < |z - c|",
										ByArith(apart, complex_abs.AbsPosIffNonzero.At(h.TermAs[Complex]("z - c"))))
									l, slope := h.ObtainAs[Complex](
										"F has a derivative l at z, a point of the punctured disc",
										"∃l:complex. complex_derivative_at(λu:complex. f(u) * (u - c) ^ (m + 1), z, l)",
										By(off, within, factor, complex_derivative.HolomorphicOnDef))
									near := h.Have(
										"no point within |z − c| of z is c, since |c − z| = |z − c|; there G is F",
										"∀u:complex. |u - z| < |z - c| ⇒ «G»(u) = f(u) * (u - c) ^ (m + 1)",
										Derive(func(k *Argument) {
											k.FixAs[Complex]("u")
											nearby := k.Assume()
											k.Show(
												"were u = c, |z − c| would be below itself",
												By(nearby, complex_abs.AbsSubComm.At(c, z), real_order_ring.LessThanIrrefl.At(distance)))
										}))
									h.Take(l)
									h.Show(
										"so G has the derivative l at z",
										By(off, near, slope, complex_derivative.DerivativeLocal.At(G, product, z, l, distance)))
								})
						}))
					expansion := d.Have(
						"so G is the sum of its power series inside the circle "+
							"of radius ρ/2, the coefficients read off that circle",
						Statement{
							Binders: "∀z:complex.",
							Hypotheses: []string{
								"|z - c| < ρ / &2",
							},
							Conclusion: "complex_sums(λn:num. «coef»(«G», c, ρ / &2, n) * (z - c) ^ n, «G»(z))",
						},
						Derive(func(e *Argument) {
							z := e.FixAs[Complex]("z")
							inside := e.Assume()
							e.Show(
								"G is holomorphic on the disc of radius ρ, and ρ/2 < ρ",
								ByArith(
									holomorphicG,
									inside,
									parts[0],
									cauchy_integral.PowerSeriesExpansionCircle.At(
										G,
										c,
										z,
										ρ,
										half)))
						}))
					small := d.TermAs[Real]("min(r, ρ / &2)")
					smallPositive := d.Have(
						"the smaller of r and ρ/2 is positive",
						"&0 < min(r, ρ / &2)",
						ByArith(positive, parts[0], real_sup_inf.LessThanMin.At(r, half, d.TermAs[Real]("&0"))))
					series := d.Have(
						"within that smaller radius b's series sums to g(z), which is G(z)",
						"∀z:complex. |z - c| < min(r, ρ / &2) ⇒ complex_sums(λn:num. b(n) * (z - c) ^ n, «G»(z))",
						Derive(func(e *Argument) {
							z := e.FixAs[Complex]("z")
							within := e.Assume()
							e.Show(
								"z lies within r of c",
								By(
									within,
									real_sup_inf.LessThanMin.At(r, half, e.TermAs[Real]("|z - c|")),
									agree.At(z),
									sums.At(z)))
						}))
					coefficients := d.TermAs[Fun[Nat, Complex]]("«coef»(«G», c, ρ / &2)")
					same := d.Have(
						"two power series with one sum near c have one set "+
							"of coefficients, so those read off the circle are b's",
						"«coef»(«G», c, ρ / &2) = b",
						By(
							smallPositive,
							series,
							expansion,
							real_sup_inf.LessThanMin,
							complex_power_series.CoefficientsUnique.At(
								coefficients,
								b,
								G,
								c,
								small)))
					atM := d.Have(
						"in particular the m-th is b(m)",
						"«coef»(«G», c, ρ / &2, m) = b(m)",
						By(same))
					onCircle := d.Have(
						"the circle of radius ρ/2 stays at that distance from c",
						"∀t:real. &0 < |circle_path(c, ρ / &2, t) - c|",
						d.ForEach(func(t *Expr[Real]) Action {
							return ByArith(parts[0], path_integral.CirclePathRadius.At(c, half, t))
						}))
					quotient := d.Have(
						"off c, f is G over (u − c)ᵐ⁺¹",
						"∀u:complex. &0 < |u - c| ⇒ f(u) = «G»(u) / (u - c) ^ (m + 1)",
						Derive(func(e *Argument) {
							u := e.FixAs[Complex]("u")
							off := e.Assume()
							apart := e.Have(
								"u is not c",
								"u ≠ c",
								ByArith(off, complex_abs.AbsPosIffNonzero.At(e.TermAs[Complex]("u - c"))))
							e.Show(
								"G(u) is f(u)·(u − c)ᵐ⁺¹, and (u − c)ᵐ⁺¹ is not 0",
								ByArith(apart, off, powers.At(u)))
						}))
					integrand := d.TermAs[Fun[Complex, Complex]]("λu:complex. «G»(u) / (u - c) ^ (m + 1)")
					circle := d.Have(
						"so round the circle f has the integral of G/(u − c)ᵐ⁺¹",
						"«circleInt»(f, c, ρ / &2) = «circleInt»(λu:complex. «G»(u) / (u - c) ^ (m + 1), c, ρ / &2)",
						By(
							onCircle,
							quotient,
							path_integral.PathIntegralCongruence.At(
								f,
								integrand,
								d.TermAs[Fun[Real, Complex]]("circle_path(c, ρ / &2)"),
								d.TermAs[Fun[Real, Complex]]("λt:real. complex_i * &(ρ / &2) * exp(complex_i * &t)"),
								d.TermAs[Real]("&0"),
								d.TermAs[Real]("&2 * pi"))))
					d.Show(
						"which is 2πi times G's m-th coefficient b(m)",
						ByArith(
							circle,
							Scaled(d.TermAs[Complex]("&(&2 * pi) * complex_i"), atM),
							path_integral.TwoPiINonzero))
				}))
			punctured := a.TermAs[Set[Complex]]("«punctured»(c, r)")
			quotient := a.TermAs[Fun[Complex, Complex]]("λu:complex. g(u) / (u - c) ^ (m + 1)")
			holomorphicF := a.Have(
				"f is holomorphic on the punctured disc of radius r, an open set where it is g(z)/(z − c)ᵐ⁺¹",
				"holomorphic_on(«punctured»(c, r), f)",
				Derive(func(d *Argument) {
					inDisc := d.Have(
						"the punctured disc lies in the disc",
						"«punctured»(c, r) ⊆ «disc»(c, r)",
						BySets())
					restricted := d.Have(
						"g is holomorphic on the punctured disc",
						"holomorphic_on(«punctured»(c, r), g)",
						By(holomorphic, inDisc, complex_derivative.HolomorphicOnSubset.At(disc, punctured, g)))
					nonzero := d.Have(
						"(u − c)ᵐ⁺¹ is not 0 there",
						"∀u:complex. u ∈ «punctured»(c, r) ⇒ (u - c) ^ (m + 1) ≠ &0",
						Derive(func(e *Argument) {
							u := e.FixAs[Complex]("u")
							inside := e.Assume()
							e.Show(
								"u is off c",
								By(inside, powers.At(u)))
						}))
					holomorphicQuotient := d.Have(
						"so the quotient g(u)/(u − c)ᵐ⁺¹ is holomorphic there",
						"holomorphic_on(«punctured»(c, r), λu:complex. g(u) / (u - c) ^ (m + 1))",
						By(
							translation.At(punctured),
							restricted,
							nonzero,
							complex_derivative.HolomorphicOnPow.At(punctured, shift, order),
							complex_derivative.HolomorphicOnDiv.At(punctured, g, power)))
					d.Show(
						"and f is that quotient on the open punctured disc",
						By(
							holomorphicQuotient,
							pole,
							complex_topology.PuncturedDiscOpen.At(c, r),
							complex_derivative.HolomorphicOnAgree.At(punctured, f, quotient)))
				}))
			a.Do(Unfold(ComplexResidueDef))
			_, chooses := a.LetAs[Fun[Complex, Bool]](
				"P",
				"λw:complex. ∃ρ:real. "+
					"    &0 < ρ ∧ "+
					"    holomorphic_on(«punctured»(c, ρ), f) ∧ "+
					"    «circleInt»(f, c, ρ / &2) = &(&2 * pi) * complex_i * w")
			holds := a.Have(
				"r is such a radius, and it gives b(m)",
				"P(b(m))",
				Derive(func(d *Argument) {
					d.Do(chooses.Rw())
					d.Take(r)
					d.Show(
						"r is positive, f is holomorphic on its punctured "+
							"disc, and its circle of radius r/2 gives 2πi·b(m)",
						By(positive, holomorphicF, every.At(r)))
				}))
			only := a.Have(
				"and every radius gives b(m), so b(m) is the only w that P holds of",
				"∀w:complex. P(w) ⇒ w = b(m)",
				Derive(func(d *Argument) {
					d.FixAs[Complex]("w")
					chosen := d.Assume()
					d.Do(chooses.Rw())
					ρ, radius := d.UnpackAs[Real](chosen, "ρ")
					parts := d.Conjuncts(
						radius,
						"ρ is positive",
						"f is holomorphic on the punctured disc of radius ρ",
						"the circle of radius ρ/2 gives 2πi·w")
					same := d.Have(
						"that circle also gives 2πi·b(m)",
						"&(&2 * pi) * complex_i * w = &(&2 * pi) * complex_i * b(m)",
						By(parts[2], parts[0], parts[1], every.At(ρ)))
					d.Show(
						"so w = b(m), 2πi being nonzero",
						ByArith(
							Scaled(d.TermAs[Complex]("complex_inv(&(&2 * pi) * complex_i)"), same),
							path_integral.TwoPiINonzero))
				}))
			a.Show(
				"so the residue, the w that P chooses, is b(m)",
				By(holds, only))
		}),
})}

// PrincipalPart — at a pole of order at most m + 1, f is its principal part
// Σ_{k ≤ m} b(k)/(z − c)ᵐ⁺¹⁻ᵏ plus a function holomorphic on the whole disc.
// The sum of the tail Σ b(n + m + 1)(z − c)ⁿ of g's series is that function:
// off c the tail is g's series with its first m + 1 terms dropped, divided by
// (z − c)ᵐ⁺¹, so it sums to (g(z) − Σ_{k ≤ m} b(k)(z − c)ᵏ)/(z − c)ᵐ⁺¹, and at
// c to b(m + 1); the sum of a power series on the disc, it is holomorphic
// there. Off c, dividing the partial sum by (z − c)ᵐ⁺¹ term by
// term gives the principal part.
var PrincipalPart = principalPartThm{family.Add(registry.ProofEntry{
	Name: "PrincipalPart",
	Key:  "prop_836d50f4801341e3",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀b:num → complex. ∀c:complex. ∀r:real. ∀m:num.",
		Hypotheses: []string{
			"&0 < r",
			"∀z:complex. |z - c| < r ⇒ complex_sums(λn:num. b(n) * (z - c) ^ n, g(z))",
			"∀z:complex. z ∈ «punctured»(c, r) ⇒ f(z) = g(z) / (z - c) ^ (m + 1)",
		},
		Conclusion: "∃h:(complex → complex). " +
			"    holomorphic_on(«disc»(c, r), h) ∧ " +
			"    ∀z:complex. " +
			"        z ∈ «punctured»(c, r) ⇒ " +
			"        f(z) = Σ_{k∈0 .. m} b(k) * complex_inv((z - c) ^ (m + 1 - k)) + h(z)",
		Abbrev: Abbrev{
			{Name: "tail", Text: "λz:complex. " +
				"    COND(z = c, b(m + 1), (g(z) - Σ_{k∈0 .. m} b(k) * (z - c) ^ k) / (z - c) ^ (m + 1))"},
		},
	},
		func(
			a *Argument,
			f, g *Arrow[Complex, Complex],
			b *Arrow[Nat, Complex],
			c *Expr[Complex],
			r *Expr[Real],
			m *Expr[Nat],
			positive, sums, pole Fact,
		) {
			order := a.TermAs[Nat]("m + 1")
			tail := a.TermAs[Fun[Complex, Complex]]("«tail»")
			shifted := a.TermAs[Fun[Nat, Complex]]("λn:num. b(n + m + 1)")
			series := a.Have(
				"on the disc of radius r the series of b(n + m + 1) sums to the tail",
				"∀z:complex. |z - c| < r ⇒ complex_sums(λn:num. b(n + m + 1) * (z - c) ^ n, «tail»(z))",
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					inside := d.Assume()
					difference := d.TermAs[Complex]("z - c")
					d.Cases(d.TermAs[Bool]("z = c"))
					d.When(
						"at c it sums to its constant coefficient b(m + 1), the tail's value there",
						func(e *Argument, atCentre Fact) {
							e.Do(atCentre.Rw())
							index := e.Have(
								"0 + m + 1 is m + 1",
								"0 + m + 1 = m + 1",
								ByArith())
							e.Show(
								"a power series sums at its centre to its constant coefficient",
								By(index, complex_power_series.PowerSeriesAtCentre.At(shifted, c)))
						})
					d.Otherwise(
						"off c it is g's series without its first m + 1 terms, divided by (z − c)ᵐ⁺¹",
						func(e *Argument, apart Fact) {
							off := e.Have(
								"z is at positive distance from c",
								"&0 < |z - c|",
								ByArith(apart, complex_abs.AbsPosIffNonzero.At(difference)))
							power := e.Have(
								"so (z − c)ᵐ⁺¹ is not 0",
								"(z - c) ^ (m + 1) ≠ &0",
								ByArith(
									off,
									complex_abs.AbsPosIffNonzero.At(difference),
									field.PowEqZero.Read(complex_field.Field).At(
										difference,
										order)))
							divide := e.Have(
								"dividing b(n + m + 1)(z − c)ⁿ⁺ᵐ⁺¹ by (z − c)ᵐ⁺¹ leaves b(n + m + 1)(z − c)ⁿ",
								"∀n:num. "+
									"    complex_inv((z - c) ^ (m + 1)) * (b(n + m + 1) * (z - c) ^ (n + m + 1)) = "+
									"    b(n + m + 1) * (z - c) ^ n",
								Derive(func(h *Argument) {
									n := h.FixAs[Nat]("n")
									exponent := h.Have(
										"n + m + 1 is n + (m + 1)",
										"n + m + 1 = n + (m + 1)",
										ByArith())
									h.Do(exponent.Rw())
									h.Show(
										"(z − c)ⁿ⁺⁽ᵐ⁺¹⁾ is (z − c)ⁿ·(z − c)ᵐ⁺¹, and (z − c)ᵐ⁺¹ cancels",
										ByArith(
											power,
											Scaled(
												h.TermAs[Complex]("complex_inv((z - c) ^ (m + 1)) * b(n + (m + 1))"),
												comm_monoid.PowAdd.Read(complex_field.MulMonoid).At(
													difference,
													n,
													order))))
								}))
							rest := e.Have(
								"the terms dropped leave (g(z) − Σ_{k ≤ m} b(k)(z − c)ᵏ)/(z − c)ᵐ⁺¹, the tail at z",
								"complex_inv((z - c) ^ (m + 1)) * (g(z) - Σ_{k∈0 .. m} b(k) * (z - c) ^ k) = «tail»(z)",
								ByArith(apart))
							e.Show(
								"g's series less its first m + 1 terms, scaled by 1/(z − c)ᵐ⁺¹",
								By(
									inside,
									sums.At(z),
									divide,
									rest,
									complex_series.SumsOffset.At(
										e.TermAs[Fun[Nat, Complex]]("λn:num. b(n) * (z - c) ^ n"),
										g.Apply(z),
										m),
									complex_series.SumsScale.At(
										e.TermAs[Fun[Nat, Complex]]("λn:num. b(n + m + 1) * (z - c) ^ (n + m + 1)"),
										e.TermAs[Complex]("g(z) - Σ_{k∈0 .. m} b(k) * (z - c) ^ k"),
										e.TermAs[Complex]("complex_inv((z - c) ^ (m + 1))"))))
						})
				}))
			holomorphic := a.Have(
				"the tail, the sum of a power series on the disc, is holomorphic there",
				"holomorphic_on(«disc»(c, r), «tail»)",
				By(series, complex_power_series.PowerSeriesHolomorphicDisc.At(shifted, tail, c, r)))
			representation := a.Have(
				"off c, f is the principal part plus the tail",
				Statement{
					Binders: "∀z:complex.",
					Hypotheses: []string{
						"z ∈ «punctured»(c, r)",
					},
					Conclusion: "f(z) = Σ_{k∈0 .. m} b(k) * complex_inv((z - c) ^ (m + 1 - k)) + «tail»(z)",
				},
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					given := d.Assume()
					parts := d.Conjuncts(
						given,
						"z is off c",
						"z is inside r")
					difference := d.TermAs[Complex]("z - c")
					powers := d.Have(
						"z − c is not 0, so no power of it is",
						"∀k:num. (z - c) ^ k ≠ &0",
						d.ForEach(func(k *Expr[Nat]) Action {
							return ByArith(
								parts[0],
								complex_abs.AbsPosIffNonzero.At(difference),
								field.PowEqZero.Read(complex_field.Field).At(difference, k))
						}))
					termwise := d.Have(
						"for k ≤ m, (z − c)ᵏ over (z − c)ᵐ⁺¹ is 1/(z − c)ᵐ⁺¹⁻ᵏ",
						Statement{
							Binders: "∀k:num.",
							Hypotheses: []string{
								"k ≤ m",
							},
							Conclusion: "complex_inv((z - c) ^ (m + 1)) * (b(k) * (z - c) ^ k) = " +
								"b(k) * complex_inv((z - c) ^ (m + 1 - k))",
						},
						Derive(func(e *Argument) {
							k := e.FixAs[Nat]("k")
							below := e.Assume()
							remaining := e.TermAs[Nat]("m + 1 - k")
							exponents := e.Have(
								"k and m + 1 − k add up to m + 1",
								"k + (m + 1 - k) = m + 1",
								ByArith(below))
							split := e.Have(
								"so (z − c)ᵏ·(z − c)ᵐ⁺¹⁻ᵏ is (z − c)ᵐ⁺¹",
								"(z - c) ^ k * (z - c) ^ (m + 1 - k) = (z - c) ^ (m + 1)",
								By(exponents, comm_monoid.PowAdd.Read(complex_field.MulMonoid).At(difference, k, remaining)))
							e.Show(
								"and (z − c)ᵏ cancels",
								ByArith(
									Scaled(
										e.TermAs[Complex]("b(k) * complex_inv((z - c) ^ (m + 1)) * complex_inv((z - c) ^ (m + 1 - k))"),
										split),
									powers.At(order),
									powers.At(remaining)))
						}))
					addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
					keepsZero := d.Have(
						"multiplying by 1/(z − c)ᵐ⁺¹ keeps 0",
						"complex_inv((z - c) ^ (m + 1)) * neutral_elem(complex_add) = neutral_elem(complex_add)",
						ByArith(comm_ring.NeutralAdd.Read(complex_field.CommRing)))
					keepsAddition := d.Have(
						"and distributes over addition",
						"∀u v:complex. "+
							"    complex_inv((z - c) ^ (m + 1)) * (u + v) = "+
							"    complex_inv((z - c) ^ (m + 1)) * u + complex_inv((z - c) ^ (m + 1)) * v",
						Derive(func(e *Argument) {
							e.FixAs[Complex]("u")
							e.FixAs[Complex]("v")
							e.Show(
								"by distributivity",
								ByArith())
						}))
					scaled := d.Have(
						"so it passes through the finite sum",
						"complex_inv((z - c) ^ (m + 1)) * Σ_{k∈0 .. m} b(k) * (z - c) ^ k = "+
							"Σ_{k∈0 .. m} complex_inv((z - c) ^ (m + 1)) * (b(k) * (z - c) ^ k)",
						By(
							keepsZero,
							keepsAddition,
							addition,
							num_segment.Finite.At(d.TermAs[Nat]("0"), m),
							Where(
								monoidal.Homomorphic,
								"h",
								d.TermAs[Fun[Complex, Complex]]("λu:complex. complex_inv((z - c) ^ (m + 1)) * u"))))
					principal := d.Have(
						"which, term by term, is the principal part",
						"Σ_{k∈0 .. m} complex_inv((z - c) ^ (m + 1)) * (b(k) * (z - c) ^ k) = "+
							"Σ_{k∈0 .. m} b(k) * complex_inv((z - c) ^ (m + 1 - k))",
						By(termwise, addition, monoidal.IntervalCongruence))
					apart := d.Have(
						"z is not c",
						"z ≠ c",
						ByArith(parts[0], complex_abs.AbsPosIffNonzero.At(difference)))
					d.Show(
						"g(z)/(z − c)ᵐ⁺¹ is the partial sum over (z − c)ᵐ⁺¹ plus the rest over (z − c)ᵐ⁺¹, the tail",
						ByArith(apart, powers.At(order), scaled, principal, parts[0], parts[1], pole.At(z)))
				}))
			a.Take(tail)
			a.Show(
				"the tail is the holomorphic function",
				By(holomorphic, representation))
		}),
})}

// PrincipalPartAtPole — at a pole, f is a principal part plus a function
// holomorphic on a disc about the pole, and the residue is the coefficient of
// 1/(z − p) in the principal part. Near p, off p, f is g/(z − p)ᵐ⁺¹ with g
// holomorphic on a disc, so g is the sum of its power series there; dividing
// that series by (z − p)ᵐ⁺¹ gives the principal part (PrincipalPart), and the
// residue is its m-th coefficient (ResidueAtPole).
var PrincipalPartAtPole = principalPartAtPoleThm{family.Add(registry.ProofEntry{
	Name: "PrincipalPartAtPole",
	Key:  "prop_802e17d1720b722f",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀p:complex.",
		Hypotheses: []string{
			"«meromorphicAt»(f, p)",
		},
		Conclusion: "∃r:real. ∃m:num. ∃c:(num → complex). ∃h:(complex → complex). " +
			"    &0 < r ∧ " +
			"    holomorphic_on(«disc»(p, r), h) ∧ " +
			"    (∀z:complex. " +
			"        z ∈ «punctured»(p, r) ⇒ " +
			"        f(z) = Σ_{k∈0 .. m} c(k) * complex_inv((z - p) ^ (m + 1 - k)) + h(z)) ∧ " +
			"    complex_residue(f, p) = c(m)",
	},
		func(a *Argument, f *Arrow[Complex, Complex], p *Expr[Complex], pole Fact) {
			r, g, m, near := a.Unpack3As[Real, Fun[Complex, Complex], Nat](pole, "r", "g", "m")
			parts := a.Conjuncts(
				near,
				"r is positive",
				"g is holomorphic on the disc of radius r about p",
				"off p, f is g/(z − p)ᵐ⁺¹ on that disc")
			c, series := a.ObtainAs[Fun[Nat, Complex]](
				"g is the sum of its power series about p on the disc",
				"∃c:(num → complex). ∀z:complex. |z - p| < r ⇒ complex_sums(λn:num. c(n) * (z - p) ^ n, g(z))",
				By(parts[1], cauchy_integral.PowerSeriesExpansion.At(g, p, r)),
				Named("c"))
			h, split := a.UnpackAs[Fun[Complex, Complex]](
				GroupPremises(parts[0], series, parts[2], PrincipalPart.At(f, g, c, p, r, m)),
				"h")
			residue := a.Have(
				"and the residue of f at p is the m-th coefficient",
				"complex_residue(f, p) = c(m)",
				By(parts[0], series, parts[2], ResidueAtPole.At(f, g, c, p, r, m)))
			a.Take(r)
			a.Take(m)
			a.Take(c)
			a.Take(h)
			a.Show(
				"so r, m, the coefficients and the regular part h serve",
				By(parts[0], split, residue))
		}),
})}

// PrincipalPartHolomorphic — a principal part about p is holomorphic on any
// set that misses p: each of its terms c(k)/(z − p)ᵐ⁺¹⁻ᵏ is a constant times an
// inverse power of z − p, and a finite sum of holomorphic functions is
// holomorphic.
var PrincipalPartHolomorphic = principalPartHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "PrincipalPartHolomorphic",
	Key:  "prop_82e3d6fa8c3d30fc",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀p:complex. ∀c:(num → complex). ∀m:num.",
		Hypotheses: []string{
			"p ∉ s",
		},
		Conclusion: "holomorphic_on(s, λz:complex. Σ_{k∈0 .. m} c(k) * complex_inv((z - p) ^ (m + 1 - k)))",
	},
		func(
			a *Argument,
			s *Expr[Set[Complex]],
			p *Expr[Complex],
			c *Arrow[Nat, Complex],
			m *Expr[Nat],
			outside Fact,
		) {
			terms := a.Have(
				"each term is the constant c(k) times an inverse power of z − p, holomorphic on s",
				"∀k:num. holomorphic_on(s, λz:complex. c(k) * complex_inv((z - p) ^ (m + 1 - k)))",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					b.Show(
						"a product of holomorphic functions is holomorphic",
						By(
							outside,
							complex_derivative.HolomorphicOnConst.At(s, c.Apply(k)),
							InversePowerHolomorphic.At(s, p, b.TermAs[Nat]("m + 1 - k")),
							complex_derivative.HolomorphicOnMul.At(
								s,
								b.TermAs[Fun[Complex, Complex]]("λz:complex. c(k)"),
								b.TermAs[Fun[Complex, Complex]]("λz:complex. complex_inv((z - p) ^ (m + 1 - k))"))))
				}))
			a.Show(
				"so is their finite sum",
				By(
					terms,
					num_segment.Finite.At(a.TermAs[Nat]("0"), m),
					At(
						complex_derivative.HolomorphicOnSum,
						s,
						a.TermAs[Set[Nat]]("0 .. m"),
						a.TermAs[Fun[Nat, Fun[Complex, Complex]]](
							"λk:num. λz:complex. c(k) * complex_inv((z - p) ^ (m + 1 - k))"))))
		}),
})}

// VanishesAtCentre — a function continuous at c that agrees off c, near c,
// with (z − c)ᵏ⁺¹·g(z) for some g continuous at c vanishes at c: the
// difference h(z) − (z − c)ᵏ⁺¹g(z) is continuous at c and 0 on a punctured
// disc about it, so its limit at c is both its value h(c) − 0·g(c) and 0.
var VanishesAtCentre = vanishesAtCentreThm{family.Add(registry.ProofEntry{
	Name: "VanishesAtCentre",
	Key:  "prop_2dcb7c1316b17ffd",
	Build: family.Theorem(Statement{
		Binders: "∀g h:(complex → complex). ∀c:complex. ∀ρ:real. ∀k:num.",
		Hypotheses: []string{
			"&0 < ρ",
			"complex_continuous_at(g, c)",
			"complex_continuous_at(h, c)",
			"∀z:complex. z ∈ «punctured»(c, ρ) ⇒ h(z) = (z - c) ^ (k + 1) * g(z)",
		},
		Conclusion: "h(c) = &0",
		Abbrev: Abbrev{
			{Name: "gap", Text: "λz:complex. h(z) - (z - c) ^ (k + 1) * g(z)"},
		},
	},
		func(
			a *Argument,
			g, h *Arrow[Complex, Complex],
			c *Expr[Complex],
			ρ *Expr[Real],
			k *Expr[Nat],
			positive, gContinuous, hContinuous, near Fact,
		) {
			order := a.TermAs[Nat]("k + 1")
			centre := a.TermAs[Complex]("c - c")
			shift := a.TermAs[Fun[Complex, Complex]]("λz:complex. z - c")
			power := a.TermAs[Fun[Complex, Complex]]("λy:complex. y ^ (k + 1)")
			gap := a.TermAs[Fun[Complex, Complex]]("«gap»")
			zero := a.TermAs[Complex]("complex_of_real(&0)")
			powerContinuous := a.Have(
				"(z − c)ᵏ⁺¹ is continuous at c: z − c is, and the power has a derivative at c − c",
				"complex_continuous_at(λz:complex. (z - c) ^ (k + 1), c)",
				By(
					complex_topology.ContinuousAtSub.At(
						a.TermAs[Fun[Complex, Complex]]("λz:complex. z"),
						a.TermAs[Fun[Complex, Complex]]("λz:complex. c"),
						c),
					complex_topology.ContinuousAtId,
					complex_topology.ContinuousAtConst,
					complex_derivative.DerivativePow.At(order, centre),
					complex_derivative.DerivativeContinuous.At(
						power,
						centre,
						a.TermAs[Complex]("&(&(k + 1)) * (c - c) ^ (k + 1 - 1)")),
					complex_topology.ContinuousAtCompose.At(power, shift, c),
					functions.ComposeApply))
			gapContinuous := a.Have(
				"so the gap h(z) − (z − c)ᵏ⁺¹g(z) is continuous at c",
				"complex_continuous_at(«gap», c)",
				By(
					powerContinuous,
					gContinuous,
					hContinuous,
					complex_topology.ContinuousAtMul.At(
						a.TermAs[Fun[Complex, Complex]]("λz:complex. (z - c) ^ (k + 1)"),
						g,
						c),
					complex_topology.ContinuousAtSub.At(
						h,
						a.TermAs[Fun[Complex, Complex]]("λz:complex. (z - c) ^ (k + 1) * g(z)"),
						c)))
			vanishes := a.Have(
				"off c, near c, the gap is 0",
				"∀z:complex. &0 < |z - c| ∧ |z - c| < ρ ⇒ «gap»(z) = &0",
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					within := d.Assume()
					d.Show(
						"h(z) is (z − c)ᵏ⁺¹g(z) there",
						ByArith(within, near.At(z)))
				}))
			limit := a.Have(
				"so the gap tends to 0 at c, as the constant 0 does",
				"«gap» ⟶ complex_of_real(&0) (at c)",
				By(
					positive,
					vanishes,
					complex_topology.LimitAtLocal.At(
						gap,
						a.TermAs[Fun[Complex, Complex]]("λz:complex. complex_of_real(&0)"),
						c,
						ρ),
					complex_topology.LimitAtConst.At(c, zero)))
			value := a.Have(
				"and to its value h(c) − (c − c)ᵏ⁺¹g(c), being continuous there, so that value is 0",
				"h(c) - (c - c) ^ (k + 1) * g(c) = &0",
				By(
					gapContinuous,
					limit,
					complex_topology.ContinuousAtIffLimit.At(gap, c),
					complex_topology.LimitAtUnique.At(gap, c, a.TermAs[Complex]("«gap»(c)"), zero)))
			atCentre := a.Have(
				"(c − c)ᵏ⁺¹ is (c − c)ᵏ·(c − c), a multiple of 0",
				"(c - c) ^ (k + 1) = &0",
				Simp(
					Fwd(comm_monoid.PowAdd.Read(complex_field.MulMonoid)),
					Fwd(comm_monoid.PowOne.Read(complex_field.MulMonoid))),
				ByArith())
			a.Show(
				"so h(c) = 0",
				ByArith(value, atCentre))
		}),
})}

// PoleFactorUnique — near c a function is g/(z − c)ᵐ with g(c) ≠ 0 for at
// most one m: were it also h/(z − c)ⁿ with h(c) ≠ 0 and m < n, then off c
// h(z) = (z − c)ⁿ⁻ᵐ·g(z), so h would vanish at c by continuity; and n < m
// fails the same way with the two sides exchanged.
var PoleFactorUnique = poleFactorUniqueThm{family.Add(registry.ProofEntry{
	Name: "PoleFactorUnique",
	Key:  "prop_bf844cf95c8b6ef3",
	Build: family.Theorem(Statement{
		Binders: "∀g h:(complex → complex). ∀c:complex. ∀ρ:real. ∀m n:num.",
		Hypotheses: []string{
			"&0 < ρ",
			"complex_continuous_at(g, c)",
			"complex_continuous_at(h, c)",
			"g(c) ≠ &0",
			"h(c) ≠ &0",
			"∀z:complex. z ∈ «punctured»(c, ρ) ⇒ g(z) / (z - c) ^ m = h(z) / (z - c) ^ n",
		},
		Conclusion: "m = n",
	},
		func(
			a *Argument,
			g, h *Arrow[Complex, Complex],
			c *Expr[Complex],
			ρ *Expr[Real],
			m, n *Expr[Nat],
			positive, gContinuous, hContinuous, gNonzero, hNonzero, agree Fact,
		) {
			powers := a.Have(
				"off c, z − c is not 0, so no power of it is",
				"∀z:complex. ∀k:num. &0 < |z - c| ⇒ (z - c) ^ k ≠ &0",
				Derive(func(d *Argument) {
					d.FixAs[Complex]("z")
					k := d.FixAs[Nat]("k")
					off := d.Assume()
					difference := d.TermAs[Complex]("z - c")
					d.Show(
						"a power of a nonzero number is not 0",
						ByArith(
							off,
							complex_abs.AbsPosIffNonzero.At(difference),
							field.PowEqZero.Read(complex_field.Field).At(difference, k)))
				}))
			larger := a.Have(
				"of two such representations, the one with the larger exponent has its numerator vanish at c",
				Statement{
					Binders: "∀u v:(complex → complex). ∀p q:num.",
					Hypotheses: []string{
						"complex_continuous_at(u, c)",
						"complex_continuous_at(v, c)",
						"p < q",
						"∀z:complex. z ∈ «punctured»(c, ρ) ⇒ u(z) / (z - c) ^ p = v(z) / (z - c) ^ q",
					},
					Conclusion: "v(c) = &0",
				},
				Derive(func(d *Argument) {
					u := d.FixAs[Fun[Complex, Complex]]("u")
					v := d.FixAs[Fun[Complex, Complex]]("v")
					p := d.FixAs[Nat]("p")
					d.FixAs[Nat]("q")
					given := d.Assume()
					parts := d.Conjuncts(
						given,
						"u is continuous at c",
						"v is continuous at c",
						"p is less than q",
						"off c, u/(z − c)ᵖ is v/(z − c)^q")
					k, gap := d.ObtainAs[Nat](
						"q exceeds p by some k + 1",
						"∃k:num. q = p + (k + 1)",
						Derive(func(e *Argument) {
							e.Take(e.TermAs[Nat]("q - (p + 1)"))
							e.Show(
								"p < q",
								ByArith(parts[2]))
						}))
					d.Do(gap.Rw())
					product := d.Have(
						"so off c, v(z) is (z − c)ᵏ⁺¹u(z), since (z − c)^q = (z − c)ᵖ(z − c)ᵏ⁺¹",
						"∀z:complex. z ∈ «punctured»(c, ρ) ⇒ v(z) = (z - c) ^ (k + 1) * u(z)",
						Derive(func(e *Argument) {
							z := e.FixAs[Complex]("z")
							within := e.Assume()
							off := e.Have(
								"z is off c",
								"&0 < |z - c|",
								By(within))
							equal := e.Have(
								"at z, u/(z − c)ᵖ is v/(z − c)ᵖ⁺⁽ᵏ⁺¹⁾",
								"u(z) / (z - c) ^ p = v(z) / (z - c) ^ (p + (k + 1))",
								By(within, parts[3].At(z)))
							nonzero := e.Have(
								"neither (z − c)ᵖ nor (z − c)ᵖ⁺⁽ᵏ⁺¹⁾ is 0",
								"(z - c) ^ p ≠ &0 ∧ (z - c) ^ (p + (k + 1)) ≠ &0",
								By(off, powers.At(z, p), powers.At(z, e.TermAs[Nat]("p + (k + 1)"))))
							e.Show(
								"multiplying through by (z − c)ᵖ⁺⁽ᵏ⁺¹⁾",
								ByArith(
									nonzero,
									Scaled(
										e.TermAs[Complex]("u(z) * complex_inv((z - c) ^ p)"),
										comm_monoid.PowAdd.Read(complex_field.MulMonoid).At(
											e.TermAs[Complex]("z - c"),
											p,
											e.TermAs[Nat]("k + 1"))),
									Scaled(e.TermAs[Complex]("(z - c) ^ (p + (k + 1))"), equal)))
						}))
					d.Show(
						"so v vanishes at c",
						By(positive, parts[0], parts[1], product, VanishesAtCentre.At(u, v, c, ρ, k)))
				}))
			below := a.Unless(
				a.TermAs[Bool]("m < n"),
				"were m < n, h would vanish at c",
				Given(func(b *Argument, less Fact) {
					b.Show(
						"but h(c) is not 0",
						By(less, gContinuous, hContinuous, agree, hNonzero, larger.At(g, h, m, n)))
				}))
			flipped := a.Have(
				"read the other way round, h/(z − c)ⁿ is g/(z − c)ᵐ off c",
				"∀z:complex. z ∈ «punctured»(c, ρ) ⇒ h(z) / (z - c) ^ n = g(z) / (z - c) ^ m",
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					within := d.Assume()
					d.Show(
						"g(z)/(z − c)ᵐ = h(z)/(z − c)ⁿ at z, read right to left",
						By(within, agree.At(z)))
				}))
			above := a.Unless(
				a.TermAs[Bool]("n < m"),
				"were n < m, g would vanish at c",
				Given(func(b *Argument, less Fact) {
					b.Show(
						"but g(c) is not 0",
						By(less, hContinuous, gContinuous, flipped, gNonzero, larger.At(h, g, n, m)))
				}))
			a.Show(
				"so m = n",
				ByArith(below, above))
		}),
})}

// PoleOrderUnique — the pole order of f at c is m when f has a pole factor of
// order m at c: off c near c, f(z) is g(z)/(z − c)ᵐ with g holomorphic on a
// disc about c and g(c) ≠ 0. The order is the exponent of such a factor,
// chosen; any other one, j with q on the disc of radius δ, agrees with the
// given one, r with g, on the smaller disc, where PoleFactorUnique makes
// j = m.
var PoleOrderUnique = poleOrderUniqueThm{family.Add(registry.ProofEntry{
	Name: "PoleOrderUnique",
	Key:  "prop_3cb6f1c957a765af",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀m:num.",
		Hypotheses: []string{
			"«poleFactor»(f, c, m)",
		},
		Conclusion: "complex_pole_order(f, c) = m",
	},
		func(a *Argument, f *Arrow[Complex, Complex], c *Expr[Complex], m *Expr[Nat], factor Fact) {
			centre := a.TermAs[Complex]("c - c")
			a.Do(Unfold(ComplexPoleOrderDef))
			_, chooses := a.LetAs[Fun[Nat, Bool]]("P", "λj:num. «poleFactor»(f, c, j)")
			only := a.Have(
				"any exponent j of a pole factor is m",
				"∀j:num. P(j) ⇒ j = m",
				Derive(func(d *Argument) {
					j := d.FixAs[Nat]("j")
					chosen := d.Assume()
					d.Do(chooses.Rw())
					r, g, given := d.Unpack2As[Real, Fun[Complex, Complex]](factor, "r", "g")
					pole := d.Conjuncts(
						given,
						"r is positive",
						"g is holomorphic on the disc of radius r",
						"g(c) is not 0",
						"off c on that disc, f is g(z)/(z − c)ᵐ")
					inside := d.Have(
						"c lies in the disc of radius r",
						"c ∈ «disc»(c, r)",
						ByArith(pole[0], complex_abs.AbsEqZero.At(centre)))
					continuous := d.Have(
						"g, holomorphic on that disc, is continuous at c",
						"complex_continuous_at(g, c)",
						By(
							inside,
							pole[1],
							complex_derivative.HolomorphicOnContinuousAt.At(
								d.TermAs[Set[Complex]]("«disc»(c, r)"),
								g,
								c)))
					δ, q, other := d.Unpack2As[Real, Fun[Complex, Complex]](chosen, "δ", "q")
					parts := d.Conjuncts(
						other,
						"δ is positive",
						"q is holomorphic on the disc of radius δ",
						"q(c) is not 0",
						"off c near c, f is q(z)/(z − c)ʲ")
					insideQ := d.Have(
						"c lies in the disc of radius δ",
						"c ∈ «disc»(c, δ)",
						ByArith(parts[0], complex_abs.AbsEqZero.At(centre)))
					continuousQ := d.Have(
						"so q is continuous at c",
						"complex_continuous_at(q, c)",
						By(
							insideQ,
							parts[1],
							complex_derivative.HolomorphicOnContinuousAt.At(
								d.TermAs[Set[Complex]]("«disc»(c, δ)"),
								q,
								c)))
					small := d.TermAs[Real]("min(r, δ)")
					smallPositive := d.Have(
						"the smaller radius is positive",
						"&0 < min(r, δ)",
						ByArith(pole[0], parts[0], real_sup_inf.LessThanMin.At(r, δ, d.TermAs[Real]("&0"))))
					agree := d.Have(
						"within it, off c, g(z)/(z − c)ᵐ and q(z)/(z − c)ʲ are both f(z)",
						"∀z:complex. z ∈ «punctured»(c, min(r, δ)) ⇒ g(z) / (z - c) ^ m = q(z) / (z - c) ^ j",
						Derive(func(e *Argument) {
							z := e.FixAs[Complex]("z")
							within := e.Assume()
							e.Show(
								"z lies within both radii",
								By(
									within,
									real_sup_inf.LessThanMin.At(r, δ, e.TermAs[Real]("|z - c|")),
									pole[3].At(z),
									parts[3].At(z)))
						}))
					d.Show(
						"so the two exponents agree",
						By(
							smallPositive,
							continuous,
							continuousQ,
							pole[2],
							parts[2],
							agree,
							PoleFactorUnique.At(g, q, c, small, m, j)))
				}))
			a.Show(
				"so the pole order, the exponent P chooses, is m, the exponent of the given factor",
				By(factor, only))
		}),
})}

// ZeroOrderUnique — the zero order of f at c is m when f has a zero factor of
// order m at c: near c, f(z) is (z − c)ᵐg(z) with g holomorphic on a disc
// about c and g(c) ≠ 0. The order is the exponent of such a factor, chosen.
// Dividing by (z − c)ⁱ⁺ʲ turns a zero factor of order i into a pole factor of
// order j, so for any other exponent j the function f/(z − c)ᵐ⁺ʲ has pole
// factors of orders j and m, and its pole order is both (PoleOrderUnique).
var ZeroOrderUnique = zeroOrderUniqueThm{family.Add(registry.ProofEntry{
	Name: "ZeroOrderUnique",
	Key:  "prop_fe82623489335f3f",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀m:num.",
		Hypotheses: []string{
			"«zeroFactor»(f, c, m)",
		},
		Conclusion: "complex_zero_order(f, c) = m",
	},
		func(a *Argument, f *Arrow[Complex, Complex], c *Expr[Complex], m *Expr[Nat], factor Fact) {
			a.Do(Unfold(ComplexZeroOrderDef))
			_, chooses := a.LetAs[Fun[Nat, Bool]]("P", "λj:num. «zeroFactor»(f, c, j)")
			divided := a.Have(
				"a zero factor of f of order i is a pole factor of f/(z − c)ⁱ⁺ʲ of order j",
				"∀i j:num. «zeroFactor»(f, c, i) ⇒ «poleFactor»(λz:complex. f(z) / (z - c) ^ (i + j), c, j)",
				Derive(func(d *Argument) {
					i := d.FixAs[Nat]("i")
					d.FixAs[Nat]("j")
					r, g, given := d.Unpack2As[Real, Fun[Complex, Complex]](d.Assume(), "r", "g")
					zero := d.Conjuncts(
						given,
						"r is positive",
						"g is holomorphic on the disc of radius r",
						"g(c) is not 0",
						"on that disc, f is (z − c)ⁱg(z)")
					quotient := d.Have(
						"off c on that disc, f(z)/(z − c)ⁱ⁺ʲ is (z − c)ⁱg(z)/((z − c)ⁱ(z − c)ʲ), which is g(z)/(z − c)ʲ",
						"∀z:complex. z ∈ «punctured»(c, r) ⇒ f(z) / (z - c) ^ (i + j) = g(z) / (z - c) ^ j",
						Derive(func(e *Argument) {
							z := e.FixAs[Complex]("z")
							near := e.Assume()
							difference := e.TermAs[Complex]("z - c")
							nonzero := e.Have(
								"z − c is not 0, so neither is any power of it",
								"∀k:num. (z - c) ^ k ≠ &0",
								e.ForEach(func(k *Expr[Nat]) Action {
									return ByArith(
										near,
										complex_abs.AbsPosIffNonzero.At(difference),
										field.PowEqZero.Read(complex_field.Field).At(difference, k))
								}))
							atZ := e.Have(
								"f(z) is (z − c)ⁱg(z)",
								"f(z) = (z - c) ^ i * g(z)",
								By(near, zero[3].At(z)))
							e.Show(
								"(z − c)ⁱ⁺ʲ is (z − c)ⁱ(z − c)ʲ, and (z − c)ⁱ cancels",
								Simp(
									Fwd(comm_monoid.PowAdd.Read(complex_field.MulMonoid)),
									Fwd(field.DivMulInv.Read(complex_field.Field)),
									Fwd(field.InvMul.Read(complex_field.Field))),
								ByArith(
									nonzero.At(i),
									Scaled(
										e.TermAs[Complex]("complex_inv((z - c) ^ i) * complex_inv((z - c) ^ j)"),
										atZ)))
						}))
					d.Take(r)
					d.Take(g)
					d.Show(
						"r and g serve",
						By(zero[0], zero[1], zero[2], quotient))
				}))
			only := a.Have(
				"any exponent j of a zero factor is m, both being the pole order of f/(z − c)ᵐ⁺ʲ",
				"∀j:num. P(j) ⇒ j = m",
				Derive(func(d *Argument) {
					j := d.FixAs[Nat]("j")
					chosen := d.Assume()
					d.Do(chooses.Rw())
					quotient := d.TermAs[Fun[Complex, Complex]]("λz:complex. f(z) / (z - c) ^ (m + j)")
					orderJ := d.Have(
						"the given zero factor, of order m, makes the pole order of f/(z − c)ᵐ⁺ʲ j",
						"complex_pole_order(λz:complex. f(z) / (z - c) ^ (m + j), c) = j",
						By(factor, divided.At(m, j), PoleOrderUnique.At(quotient, c, j)))
					swapped := d.Have(
						"m + j is j + m",
						"m + j = j + m",
						ByArith())
					orderM := d.Have(
						"and the one of order j makes it m",
						"complex_pole_order(λz:complex. f(z) / (z - c) ^ (m + j), c) = m",
						swapped.Rw(),
						By(
							chosen,
							divided.At(j, m),
							PoleOrderUnique.At(
								d.TermAs[Fun[Complex, Complex]]("λz:complex. f(z) / (z - c) ^ (j + m)"),
								c,
								m)))
					d.Show(
						"so j = m",
						ByArith(orderJ, orderM))
				}))
			a.Show(
				"so the zero order, the exponent P chooses, is m, the exponent of the given factor",
				By(factor, only))
		}),
})}

// SimplePoleResidue — a function that is G(z)/(z − c) off c near c, G
// holomorphic on a disc about c, has at most a pole at c, and its residue
// there is G(c). G is the sum of its power series b on the disc, so the
// residue is b(0), and b(0) is the series' value at its centre, G(c).
var SimplePoleResidue = simplePoleResidueThm{family.Add(registry.ProofEntry{
	Name: "SimplePoleResidue",
	Key:  "prop_579d1b55e6e50b82",
	Build: family.Theorem(Statement{
		Binders: "∀F G:(complex → complex). ∀c:complex. ∀r:real.",
		Hypotheses: []string{
			"&0 < r",
			"holomorphic_on(«disc»(c, r), G)",
			"∀z:complex. z ∈ «punctured»(c, r) ⇒ F(z) = G(z) / (z - c)",
		},
		Conclusion: "«meromorphicAt»(F, c) ∧ complex_residue(F, c) = G(c)",
	},
		func(
			a *Argument,
			F, G *Arrow[Complex, Complex],
			c *Expr[Complex],
			r *Expr[Real],
			positive, holomorphic, quotient Fact,
		) {
			b, series := a.ObtainAs[Fun[Nat, Complex]](
				"G is the sum of its power series b on the disc",
				"∃b:(num → complex). ∀z:complex. |z - c| < r ⇒ complex_sums(λn:num. b(n) * (z - c) ^ n, G(z))",
				By(holomorphic, cauchy_integral.PowerSeriesExpansion),
				Named("b"))
			simple := a.Have(
				"off c, F is G over the first power of z − c",
				"∀z:complex. z ∈ «punctured»(c, r) ⇒ F(z) = G(z) / (z - c) ^ (0 + 1)",
				Simp(Fwd(nat_arith.AddLeftZeroClause), Fwd(comm_monoid.PowOne.Read(complex_field.MulMonoid))),
				By(quotient))
			pole := a.Have(
				"so F has at most a pole at c",
				"«meromorphicAt»(F, c)",
				Derive(func(d *Argument) {
					d.Take(r)
					d.Take(G)
					d.Take(d.TermAs[Nat]("0"))
					d.Show(
						"G being holomorphic on the disc of radius r",
						By(simple, holomorphic, positive))
				}))
			centre := a.Have(
				"the series at its centre sums to b(0), so G(c) = b(0)",
				"G(c) = b(0)",
				ByArith(
					series.At(c),
					positive,
					complex_power_series.PowerSeriesAtCentre.At(b, c),
					complex_series.SumsUnique,
					complex_abs.AbsEqZero.At(a.TermAs[Complex]("c - c"))))
			a.Show(
				"and its residue is the coefficient b(0) of the series of G, which is G(c)",
				By(pole, series, simple, centre, positive, ResidueAtPole.At(F, G, b, c, r, a.TermAs[Nat]("0"))))
		}),
})}

// LogDerivativeResidue — where f is φ·h off c near c, with h holomorphic and
// nowhere 0 on the disc, and φ not 0 with φ′ = k·φ/(z − c) there — φ behaves
// as (z − c)ᵏ — the logarithmic derivative f′/f has at most a pole at c, and
// its residue there is k. By the product rule f′/f = k/(z − c) + h′/h off c,
// which is G/(z − c) with G = k + (z − c)·h′/h holomorphic on the disc, and
// G(c) = k (SimplePoleResidue).
var LogDerivativeResidue = logDerivativeResidueThm{family.Add(registry.ProofEntry{
	Name: "LogDerivativeResidue",
	Key:  "prop_16167cbc427f1dd",
	Build: family.Theorem(Statement{
		Binders: "∀f f' φ h:(complex → complex). ∀c k:complex. ∀r:real.",
		Hypotheses: []string{
			"&0 < r",
			"holomorphic_on(«disc»(c, r), h)",
			"∀z:complex. z ∈ «disc»(c, r) ⇒ h(z) ≠ &0",
			"∀z:complex. z ∈ «punctured»(c, r) ⇒ φ(z) ≠ &0 ∧ complex_derivative_at(φ, z, k * φ(z) / (z - c))",
			"∀z:complex. z ∈ «punctured»(c, r) ⇒ f(z) = φ(z) * h(z)",
			"∀z:complex. z ∈ «punctured»(c, r) ⇒ complex_derivative_at(f, z, f'(z))",
		},
		Conclusion: "«meromorphicAt»(λz:complex. f'(z) / f(z), c) ∧ " +
			"complex_residue(λz:complex. f'(z) / f(z), c) = k",
		Abbrev: Abbrev{
			{Name: "G", Text: "λz:complex. k + (z - c) * h'(z) / h(z)"},
		},
	},
		func(
			a *Argument,
			f, fPrime, φ, h *Arrow[Complex, Complex],
			c, k *Expr[Complex],
			r *Expr[Real],
			positive, holomorphic, hNonzero, φSlope, product, slope Fact,
		) {
			disc := a.TermAs[Set[Complex]]("«disc»(c, r)")
			shift := a.TermAs[Fun[Complex, Complex]]("λz:complex. z - c")
			hPrime, hSlope := a.ObtainAs[Fun[Complex, Complex]](
				"h has a derivative h′ on the disc, itself holomorphic there",
				"∃h':(complex → complex). "+
					"    (∀z:complex. z ∈ «disc»(c, r) ⇒ complex_derivative_at(h, z, h'(z))) ∧ "+
					"    holomorphic_on(«disc»(c, r), h')",
				By(holomorphic, complex_topology.DiscOpen.At(c, r), cauchy_integral.HolomorphicDerivative),
				Named("h'"))
			hDerivative := a.Conjuncts(
				hSlope,
				"h′(z) is the derivative of h at each point z of the disc",
				"h′ is holomorphic on the disc")
			translate := a.Have(
				"z − c, a difference of the identity and a constant, is holomorphic on the disc",
				"holomorphic_on(«disc»(c, r), λz:complex. z - c)",
				By(
					complex_derivative.HolomorphicOnId.At(disc),
					complex_derivative.HolomorphicOnConst.At(disc, c),
					complex_derivative.HolomorphicOnSub.At(
						disc,
						a.TermAs[Fun[Complex, Complex]]("λz:complex. z"),
						a.TermAs[Fun[Complex, Complex]]("λz:complex. c"))))
			regular := a.Have(
				"so G = k + (z − c)·h′/h is holomorphic on the disc, h having no zero there",
				"holomorphic_on(«disc»(c, r), «G»)",
				By(
					hNonzero,
					hDerivative[1],
					holomorphic,
					translate,
					complex_derivative.HolomorphicOnConst.At(disc, k),
					complex_derivative.HolomorphicOnMul.At(disc, shift, hPrime),
					complex_derivative.HolomorphicOnDiv.At(
						disc,
						a.TermAs[Fun[Complex, Complex]]("λz:complex. (z - c) * h'(z)"),
						h),
					complex_derivative.HolomorphicOnAdd.At(
						disc,
						a.TermAs[Fun[Complex, Complex]]("λz:complex. k"),
						a.TermAs[Fun[Complex, Complex]]("λz:complex. (z - c) * h'(z) / h(z)"))))
			shape := a.Have(
				"off c, f′/f is k/(z − c) + h′/h, which is G/(z − c)",
				"∀z:complex. z ∈ «punctured»(c, r) ⇒ f'(z) / f(z) = «G»(z) / (z - c)",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					near := b.Assume()
					δ, ball := b.ObtainAs[Real](
						"the punctured disc is open, so some disc about z lies in it",
						"∃δ:real. &0 < δ ∧ ∀w:complex. |w - z| < δ ⇒ w ∈ «punctured»(c, r)",
						By(
							near,
							complex_topology.PuncturedDiscOpen.At(c, r),
							complex_topology.ComplexOpenIff.At(
								b.TermAs[Set[Complex]]("«punctured»(c, r)"))),
						Named("δ"))
					around := b.Conjuncts(
						ball,
						"δ is positive",
						"within δ of z the points lie in the punctured disc")
					local := b.Have(
						"so within δ of z, f is φ·h",
						"∀w:complex. |w - z| < δ ⇒ f(w) = φ(w) * h(w)",
						By(around[1], product))
					φAt := b.Conjuncts(
						GroupPremises(near, φSlope.At(z)),
						"φ(z) is not 0",
						"φ has the derivative k·φ(z)/(z − c) at z")
					value := b.TermAs[Complex]("k * φ(z) / (z - c) * h(z) + φ(z) * h'(z)")
					productRule := b.Have(
						"by the product rule φ·h has the derivative k·φ(z)/(z − c)·h(z) + φ(z)·h′(z) at z",
						"complex_derivative_at(λw:complex. φ(w) * h(w), z, k * φ(z) / (z - c) * h(z) + φ(z) * h'(z))",
						By(
							φAt[1],
							near,
							hDerivative[0].At(z),
							complex_derivative.DerivativeMul.At(
								φ,
								h,
								z,
								b.TermAs[Complex]("k * φ(z) / (z - c)"),
								b.TermAs[Complex]("h'(z)"))))
					derivative := b.Have(
						"f agrees with φ·h near z, so f′(z) is that derivative, a derivative being unique",
						"f'(z) = k * φ(z) / (z - c) * h(z) + φ(z) * h'(z)",
						By(
							around[0],
							local,
							productRule,
							near,
							slope.At(z),
							complex_derivative.DerivativeUnique,
							complex_derivative.DerivativeLocal.At(
								f,
								b.TermAs[Fun[Complex, Complex]]("λw:complex. φ(w) * h(w)"),
								z,
								value,
								δ)))
					atZ := b.Have(
						"f(z) is φ(z)·h(z)",
						"f(z) = φ(z) * h(z)",
						By(near, product.At(z)))
					hAtZ := b.Have(
						"h(z) is not 0",
						"h(z) ≠ &0",
						By(near, hNonzero.At(z)))
					apart := b.Have(
						"z − c is not 0",
						"z - c ≠ &0",
						ByArith(near, complex_abs.AbsPosIffNonzero.At(b.TermAs[Complex]("z - c"))))
					cross := b.Have(
						"so (z − c)·f′(z) = f(z)·G(z), z − c and h(z) cancelling",
						"(z - c) * f'(z) = f(z) * «G»(z)",
						ByArith(
							apart,
							hAtZ,
							Scaled(b.TermAs[Complex]("z - c"), derivative),
							Scaled(b.TermAs[Complex]("«G»(z)"), atZ)))
					fAtZ := b.Have(
						"f(z) is not 0, neither φ(z) nor h(z) being 0",
						"f(z) ≠ &0",
						By(
							Normalized,
							atZ,
							φAt[0],
							hAtZ,
							field.MulEqZero.Read(complex_field.Field).At(φ.Apply(z), h.Apply(z))))
					b.Show(
						"dividing by f(z)·(z − c)",
						ByArith(Scaled(b.TermAs[Complex]("complex_inv(f(z)) * complex_inv(z - c)"), cross), fAtZ, apart))
				}))
			simple := a.Have(
				"so f′/f has at most a pole at c, with residue G(c)",
				"«meromorphicAt»(λz:complex. f'(z) / f(z), c) ∧ "+
					"complex_residue(λz:complex. f'(z) / f(z), c) = «G»(c)",
				By(
					shape,
					regular,
					positive,
					SimplePoleResidue.At(
						a.TermAs[Fun[Complex, Complex]]("λz:complex. f'(z) / f(z)"),
						a.TermAs[Fun[Complex, Complex]]("«G»"),
						c,
						r)))
			a.Show(
				"and G(c) = k, the second term vanishing at c",
				ByArith(simple))
		}),
})}

// LogDerivativeAtZero — where f is holomorphic on a disc about c and not 0
// off c on it, the logarithmic derivative f′/f has at most a pole at c, and
// its residue there is the order of the zero of f at c. f is not 0 everywhere
// on the disc, so it is (z − c)ᵐ·h with h holomorphic and h(c) ≠ 0, m being
// the zero order; h is not 0 on the disc, f not being 0 off c. Off c,
// (z − c)ᵐ has derivative m(z − c)ᵐ⁻¹ = m·(z − c)ᵐ/(z − c), so the residue is
// m (LogDerivativeResidue).
var LogDerivativeAtZero = logDerivativeAtZeroThm{family.Add(registry.ProofEntry{
	Name: "LogDerivativeAtZero",
	Key:  "prop_5d5d67b690d7c961",
	Build: family.Theorem(Statement{
		Binders: "∀f f':(complex → complex). ∀c:complex. ∀r:real.",
		Hypotheses: []string{
			"&0 < r",
			"holomorphic_on(«disc»(c, r), f)",
			"∀z:complex. z ∈ «punctured»(c, r) ⇒ f(z) ≠ &0",
			"∀z:complex. z ∈ «punctured»(c, r) ⇒ complex_derivative_at(f, z, f'(z))",
		},
		Conclusion: "«meromorphicAt»(λz:complex. f'(z) / f(z), c) ∧ " +
			"complex_residue(λz:complex. f'(z) / f(z), c) = &(&(complex_zero_order(f, c)))",
	},
		func(
			a *Argument,
			f, fPrime *Arrow[Complex, Complex],
			c *Expr[Complex],
			r *Expr[Real],
			positive, holomorphic, nonzero, slope Fact,
		) {
			somewhere := a.Have(
				"f is not 0 at c + r/2, a point of the disc other than c",
				"¬(∀z:complex. |z - c| < r ⇒ f(z) = &0)",
				By(
					positive,
					nonzero.At(a.TermAs[Complex]("c + &(r / &2)")),
					complex_topology.PuncturedDiscPoint.At(c, r)))
			m, h, factored := a.Obtain2As[Nat, Fun[Complex, Complex]](
				"so f is (z − c)ᵐ times a function h holomorphic on the disc and not 0 at c",
				"∃m:num. ∃h:(complex → complex). "+
					"    holomorphic_on(«disc»(c, r), h) ∧ "+
					"    h(c) ≠ &0 ∧ "+
					"    (∀z:complex. |z - c| < r ⇒ f(z) = (z - c) ^ m * h(z))",
				By(holomorphic, somewhere, cauchy_integral.ZeroFactor),
				Named("m", "h"))
			factor := a.Conjuncts(
				factored,
				"h is holomorphic on the disc",
				"h(c) is not 0",
				"on the disc f is (z − c)ᵐ·h")
			zero := a.Have(
				"so (z − c)ᵐ·h, on the disc of radius r, is a zero factor of f of order m at c",
				"«zeroFactor»(f, c, m)",
				Derive(func(b *Argument) {
					b.Take(r)
					b.Take(h)
					b.Show(
						"r is positive, and h is holomorphic on the disc, not 0 at c, and f is (z − c)ᵐ·h there",
						By(positive, factor[0], factor[1], factor[2]))
				}))
			order := a.Have(
				"so m is the order of the zero of f at c",
				"complex_zero_order(f, c) = m",
				By(zero, ZeroOrderUnique.At(f, c, m)))
			hNonzero := a.Have(
				"h is not 0 on the disc: not at c, and not off c, where f is not",
				"∀z:complex. z ∈ «disc»(c, r) ⇒ h(z) ≠ &0",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					inside := b.Assume()
					b.Cases(b.TermAs[Bool]("z = c"))
					b.When(
						"at c, h(c) is not 0",
						func(d *Argument, same Fact) {
							d.Show(
								"h was chosen not 0 at c",
								By(Normalized, same, factor[1]))
						})
					b.Otherwise(
						"off c, f(z) = (z − c)ᵐ·h(z) is not 0, so neither is h(z)",
						func(d *Argument, apart Fact) {
							away := d.Have(
								"z is at positive distance from c",
								"&0 < |z - c|",
								ByArith(apart, complex_abs.AbsPosIffNonzero.At(d.TermAs[Complex]("z - c"))))
							d.Show(
								"a product with a zero factor is 0",
								By(
									Normalized,
									away,
									inside,
									factor[2].At(z),
									nonzero.At(z),
									comm_ring.MulRightZero.Read(complex_field.CommRing)))
						})
				}))
			power := a.Have(
				"w·(n·wⁿ⁻¹) = n·wⁿ for every w and n",
				"∀w:complex. ∀n:num. w * (&(&n) * w ^ (n - 1)) = &(&n) * w ^ n",
				Derive(func(b *Argument) {
					b.FixAs[Complex]("w")
					// The induction is ℕ's case split: the step never reads its
					// hypothesis.
					b.Induct("n")
					b.Base(
						"at 0 both sides are 0",
						ByArith())
					b.Step(
						"at n + 1, (n + 1) − 1 = n and wⁿ⁺¹ = w·wⁿ",
						func(d *Argument, _ Fact) {
							n := d.TermAs[Nat]("n")
							successor := d.Have(
								"wⁿ⁺¹ is w·wⁿ, by the power's step clause",
								"w ^ suc(n) = w * w ^ n",
								By(comm_monoid.MonoidPowDef))
							d.Show(
								"so both sides are (n + 1)·w·wⁿ",
								ByArith(Scaled(d.TermAs[Complex]("&(&suc(n))"), successor), nat_monus.SucSubOne.At(n)))
						})
				}))
			unit := a.Have(
				"1 − 0 is 1",
				"&(&1) - &(&0) = &(&1)",
				ByArith())
			shift := a.TermAs[Fun[Complex, Complex]]("λu:complex. u - c")
			powerSlope := a.Have(
				"off c, (z − c)ᵐ is not 0, and its derivative m(z − c)ᵐ⁻¹ is m·(z − c)ᵐ/(z − c)",
				Statement{
					Binders: "∀z:complex.",
					Hypotheses: []string{
						"z ∈ «punctured»(c, r)",
					},
					Conclusion: "(z - c) ^ m ≠ &0 ∧ " +
						"complex_derivative_at(λu:complex. (u - c) ^ m, z, &(&m) * (z - c) ^ m / (z - c))",
				},
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					near := b.Assume()
					difference := b.TermAs[Complex]("z - c")
					slopeAt := b.TermAs[Complex]("&(&m) * (z - c) ^ (m - 1)")
					apart := b.Have(
						"z − c is not 0",
						"z - c ≠ &0",
						ByArith(near, complex_abs.AbsPosIffNonzero.At(difference)))
					nonzeroPower := b.Have(
						"so neither is (z − c)ᵐ",
						"(z - c) ^ m ≠ &0",
						ByArith(apart, field.PowEqZero.Read(complex_field.Field).At(difference, m)))
					shifted := b.Have(
						"u − c has derivative 1 − 0 = 1 at z",
						"complex_derivative_at(λu:complex. u - c, z, &1)",
						By(
							unit,
							complex_derivative.DerivativeId.At(z),
							complex_derivative.DerivativeConst.At(z, c),
							complex_derivative.DerivativeSub.At(
								b.TermAs[Fun[Complex, Complex]]("λu:complex. u"),
								b.TermAs[Fun[Complex, Complex]]("λu:complex. c"),
								z,
								b.TermAs[Complex]("&1"),
								b.TermAs[Complex]("&0"))))
					raised := b.Unfolded(
						b.Have(
							"so (u − c)ᵐ has derivative m(z − c)ᵐ⁻¹, by the chain rule through the power rule",
							"complex_derivative_at((λy:complex. y ^ m) ∘ (λu:complex. u - c), z, &(&m) * (z - c) ^ (m - 1))",
							By(
								shifted,
								comm_monoid.RightIdentity.Read(complex_field.MulMonoid).At(slopeAt),
								complex_derivative.DerivativePow.At(m, difference),
								complex_derivative.DerivativeChain.At(
									b.TermAs[Fun[Complex, Complex]]("λy:complex. y ^ m"),
									shift,
									z,
									slopeAt,
									b.TermAs[Complex]("&1")))),
						functions.ComposeApply)
					value := b.Have(
						"m(z − c)ᵐ⁻¹ is m·(z − c)ᵐ/(z − c), as (z − c)·m(z − c)ᵐ⁻¹ = m(z − c)ᵐ",
						"&(&m) * (z - c) ^ (m - 1) = &(&m) * (z - c) ^ m / (z - c)",
						ByArith(apart, Scaled(b.TermAs[Complex]("complex_inv(z - c)"), power.At(difference, m))))
					b.Show(
						"so (z − c)ᵐ is not 0 and has derivative m·(z − c)ᵐ/(z − c)",
						By(nonzeroPower, value, raised))
				}))
			residue := a.Have(
				"so f′/f has at most a pole at c with residue m, f "+
					"being (z − c)ᵐ·h with h holomorphic and nowhere 0",
				"«meromorphicAt»(λz:complex. f'(z) / f(z), c) ∧ "+
					"complex_residue(λz:complex. f'(z) / f(z), c) = &(&m)",
				By(
					positive,
					factor[0],
					factor[2],
					hNonzero,
					powerSlope,
					slope,
					LogDerivativeResidue.At(
						f,
						fPrime,
						a.TermAs[Fun[Complex, Complex]]("λz:complex. (z - c) ^ m"),
						h,
						c,
						a.TermAs[Complex]("&(&m)"),
						r)))
			a.Show(
				"and m is the order of the zero",
				By(order, residue))
		}),
})}

// LogDerivativeAtPole — where f has a pole at c and a derivative f′ off c
// near c, the logarithmic derivative f′/f has at most a pole at c, and its
// residue there is minus the order of the pole. Near c, off c, f is
// g/(z − c)ᵐ⁺¹ with g holomorphic, g(c) ≠ 0, m + 1 being the pole order; g
// is continuous at c, so it has no zero near c. Off c, 1/(z − c)ᵐ⁺¹ has
// derivative −(m + 1)/(z − c)ᵐ⁺², which is −(m + 1)·(1/(z − c)ᵐ⁺¹)/(z − c),
// so the residue is −(m + 1) (LogDerivativeResidue).
var LogDerivativeAtPole = logDerivativeAtPoleThm{family.Add(registry.ProofEntry{
	Name: "LogDerivativeAtPole",
	Key:  "prop_2a05d28f670e37fd",
	Build: family.Theorem(Statement{
		Binders: "∀f f':(complex → complex). ∀c:complex. ∀r:real.",
		Hypotheses: []string{
			"«properPole»(f, c)",
			"&0 < r",
			"∀z:complex. z ∈ «punctured»(c, r) ⇒ complex_derivative_at(f, z, f'(z))",
		},
		Conclusion: "«meromorphicAt»(λz:complex. f'(z) / f(z), c) ∧ " +
			"complex_residue(λz:complex. f'(z) / f(z), c) = -&(&(complex_pole_order(f, c)))",
	},
		func(
			a *Argument,
			f, fPrime *Arrow[Complex, Complex],
			c *Expr[Complex],
			r *Expr[Real],
			proper, positive, slope Fact,
		) {
			m, ρ, g, data := a.Unpack3As[Nat, Real, Fun[Complex, Complex]](proper, "m", "ρ", "g")
			pole := a.Conjuncts(
				data,
				"ρ is positive",
				"g is holomorphic on the disc of radius ρ about c",
				"g(c) is not 0",
				"off c on that disc, f is g/(z − c)ᵐ⁺¹")
			factor := a.Have(
				"so g/(z − c)ᵐ⁺¹, on the disc of radius ρ, is a pole factor of f of order m + 1 at c",
				"«poleFactor»(f, c, m + 1)",
				Derive(func(b *Argument) {
					b.Take(ρ)
					b.Take(g)
					b.Show(
						"ρ is positive, g is holomorphic on the disc and not 0 at c, and f is g/(z − c)ᵐ⁺¹ off c on it",
						By(pole[0], pole[1], pole[2], pole[3]))
				}))
			order := a.Have(
				"so m + 1 is the order of the pole of f at c",
				"complex_pole_order(f, c) = m + 1",
				By(factor, PoleOrderUnique.At(f, c, a.TermAs[Nat]("m + 1"))))
			outer := a.TermAs[Set[Complex]]("«disc»(c, ρ)")
			centre := a.Have(
				"c lies in its own disc",
				"c ∈ «disc»(c, ρ)",
				ByArith(pole[0], complex_abs.AbsEqZero.At(a.TermAs[Complex]("c - c"))))
			continuous := a.Have(
				"g, holomorphic on that disc, is continuous at c",
				"complex_continuous_at(g, c)",
				By(centre, pole[1], complex_derivative.HolomorphicOnContinuousAt.At(outer, g, c)))
			size := a.Have(
				"|g(c)| is positive, g(c) not being 0",
				"&0 < |g(c)|",
				By(pole[2], complex_abs.AbsPosIffNonzero.At(a.TermAs[Complex]("g(c)"))))
			δ, radius := a.UnpackAs[Real](
				GroupPremises(
					size,
					a.Unfolded(continuous, complex_topology.ComplexContinuousAtDef).At(a.TermAs[Real]("|g(c)|"))),
				"δ")
			near := a.Conjuncts(
				radius,
				"δ is positive",
				"within δ of c, g(z) lies within |g(c)| of g(c)")
			s, sDef := a.LetAs[Real]("s", "min(ρ, min(r, δ))")
			rδ := a.TermAs[Real]("min(r, δ)")
			sPositive := a.Have(
				"s is positive",
				"&0 < s",
				By(
					Normalized,
					sDef,
					pole[0],
					positive,
					near[0],
					real_sup_inf.LessThanMin.At(ρ, rδ, a.TermAs[Real]("&0")),
					real_sup_inf.LessThanMin.At(r, δ, a.TermAs[Real]("&0"))))
			inner := a.Have(
				"within s of c a point is within ρ, r and δ of c",
				"∀z:complex. |z - c| < s ⇒ |z - c| < ρ ∧ |z - c| < r ∧ |z - c| < δ",
				Derive(func(b *Argument) {
					b.FixAs[Complex]("z")
					within := b.Assume()
					distance := b.TermAs[Real]("|z - c|")
					b.Show(
						"a number below the least of three is below each",
						By(
							sDef,
							within,
							real_sup_inf.LessThanMin.At(ρ, rδ, distance),
							real_sup_inf.LessThanMin.At(r, δ, distance)))
				}))
			disc := a.TermAs[Set[Complex]]("«disc»(c, s)")
			smaller := a.Have(
				"the disc of radius s about c lies in the one of radius ρ",
				"«disc»(c, s) ⊆ «disc»(c, ρ)",
				BySets(inner))
			gHolomorphic := a.Have(
				"so g is holomorphic on the disc of radius s",
				"holomorphic_on(«disc»(c, s), g)",
				By(pole[1], smaller, complex_derivative.HolomorphicOnSubset.At(outer, disc, g)))
			gNonzero := a.Have(
				"and not 0 there: within δ of c, |g(z)| ≥ |g(c)| − |g(z) − g(c)| > 0",
				"∀z:complex. z ∈ «disc»(c, s) ⇒ g(z) ≠ &0",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					inside := b.Assume()
					withinδ := b.Have(
						"z is within δ of c",
						"|z - c| < δ",
						By(inside, inner.At(z)))
					b.Show(
						"so |g(z) − g(c)| < |g(c)|, which bounds |g(z)| away from 0",
						ByArith(
							near[1].At(z),
							withinδ,
							complex_abs.AbsTriangleReverse.At(
								b.TermAs[Complex]("g(z)"),
								b.TermAs[Complex]("g(c)")),
							complex_abs.AbsPosIffNonzero.At(b.TermAs[Complex]("g(z)"))))
				}))
			inverse := a.Have(
				"off c, 1/(z − c)ᵐ⁺¹ is not 0, and its derivative −(m "+
					"+ 1)/(z − c)ᵐ⁺² is −(m + 1)·(1/(z − c)ᵐ⁺¹)/(z − c)",
				Statement{
					Binders: "∀z:complex.",
					Hypotheses: []string{
						"z ∈ «punctured»(c, s)",
					},
					Conclusion: "complex_inv((z - c) ^ (m + 1)) ≠ &0 ∧ " +
						"complex_derivative_at(λu:complex. complex_inv((u - c) ^ (m + 1)), " +
						"    z, " +
						"    -&(&(m + 1)) * complex_inv((z - c) ^ (m + 1)) / (z - c))",
				},
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					within := b.Assume()
					difference := b.TermAs[Complex]("z - c")
					apart := b.Have(
						"z is not c",
						"z ≠ c",
						ByArith(within, complex_abs.AbsPosIffNonzero.At(difference)))
					nonzero := b.Have(
						"so no power of z − c is 0",
						"∀k:num. (z - c) ^ k ≠ &0",
						b.ForEach(func(k *Expr[Nat]) Action {
							return ByArith(apart, field.PowEqZero.Read(complex_field.Field).At(difference, k))
						}))
					value := b.Have(
						"−(m + 1)/(z − c)ᵐ⁺² is −(m + 1)·(1/(z − c)ᵐ⁺¹)/(z − c), as (z − c)ᵐ⁺² = (z − c)ᵐ⁺¹·(z − c)",
						"-(complex_of_real(&(m + 1)) * complex_inv((z - c) ^ (m + 2))) = "+
							"-&(&(m + 1)) * complex_inv((z - c) ^ (m + 1)) / (z - c)",
						Simp(
							Fwd(comm_monoid.PowAdd.Read(complex_field.MulMonoid)),
							Fwd(comm_monoid.PowOne.Read(complex_field.MulMonoid)),
							Fwd(comm_monoid.PowTwo.Read(complex_field.MulMonoid)),
							Fwd(field.DivMulInv.Read(complex_field.Field)),
							Fwd(field.InvMul.Read(complex_field.Field))),
						ByArith())
					b.Show(
						"by the derivative of an inverse power, 1/(z − c)ᵐ⁺¹ not being 0",
						By(
							apart,
							value,
							nonzero.At(b.TermAs[Nat]("m + 1")),
							field.InvEqZero.Read(complex_field.Field).At(
								b.TermAs[Complex]("(z - c) ^ (m + 1)")),
							InversePowerDerivative.At(c, z, m)))
				}))
			quotient := a.Have(
				"off c on the disc of radius s, f is (1/(z − c)ᵐ⁺¹)·g",
				"∀z:complex. z ∈ «punctured»(c, s) ⇒ f(z) = complex_inv((z - c) ^ (m + 1)) * g(z)",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					within := b.Assume()
					b.Show(
						"z lies within ρ of c, where f is g/(z − c)ᵐ⁺¹",
						ByArith(within, inner.At(z), pole[3].At(z)))
				}))
			differentiable := a.Have(
				"and has the derivative f′ there, z lying within r of c",
				"∀z:complex. z ∈ «punctured»(c, s) ⇒ complex_derivative_at(f, z, f'(z))",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					within := b.Assume()
					b.Show(
						"z lies within r of c",
						By(within, inner.At(z), slope.At(z)))
				}))
			residue := a.Have(
				"so f′/f has at most a pole at c with residue −(m + 1), "+
					"g being holomorphic and nowhere 0 on the disc of radius s",
				"«meromorphicAt»(λz:complex. f'(z) / f(z), c) ∧ "+
					"complex_residue(λz:complex. f'(z) / f(z), c) = -&(&(m + 1))",
				By(
					sPositive,
					gHolomorphic,
					gNonzero,
					inverse,
					quotient,
					differentiable,
					LogDerivativeResidue.At(
						f,
						fPrime,
						a.TermAs[Fun[Complex, Complex]]("λz:complex. complex_inv((z - c) ^ (m + 1))"),
						g,
						c,
						a.TermAs[Complex]("-&(&(m + 1))"),
						s)))
			a.Show(
				"and m + 1 is the order of the pole",
				By(order, residue))
		}),
})}

// PoleUnbounded — a function grows without bound at a proper pole: for any M,
// at each point off p but near it, |f| exceeds M. Off p near p, f is
// g/(z − p)ᵐ⁺¹ with g(p) ≠ 0; g is continuous at p, so |g| stays above
// |g(p)|/2 near p, while |z − p|ᵐ⁺¹ ≤ |z − p| falls below |g(p)|/2 over
// |M| + 1, so |f| = |g|/|z − p|ᵐ⁺¹ exceeds |M| + 1.
var PoleUnbounded = poleUnboundedThm{family.Add(registry.ProofEntry{
	Name: "PoleUnbounded",
	Key:  "prop_61a1983436fde552",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀p:complex. ∀M:real.",
		Hypotheses: []string{
			"«properPole»(f, p)",
		},
		Conclusion: "∃δ:real. &0 < δ ∧ ∀z:complex. z ∈ «punctured»(p, δ) ⇒ M < |f(z)|",
	},
		func(a *Argument, f *Arrow[Complex, Complex], p *Expr[Complex], M *Expr[Real], proper Fact) {
			_, ρ, g, data := a.Unpack3As[Nat, Real, Fun[Complex, Complex]](proper, "m", "ρ", "g")
			pole := a.Conjuncts(
				data,
				"ρ is positive",
				"g is holomorphic on the disc of radius ρ about p",
				"g(p) is not 0",
				"off p on that disc, f is g/(z − p)ᵐ⁺¹")
			gp := a.TermAs[Complex]("g(p)")
			centre := a.Have(
				"p lies in its own disc",
				"p ∈ «disc»(p, ρ)",
				ByArith(pole[0], complex_abs.AbsEqZero.At(a.TermAs[Complex]("p - p"))))
			continuous := a.Have(
				"g, holomorphic on that disc, is continuous at p",
				"complex_continuous_at(g, p)",
				By(
					centre,
					pole[1],
					complex_derivative.HolomorphicOnContinuousAt.At(a.TermAs[Set[Complex]]("«disc»(p, ρ)"), g, p)))
			half := a.Have(
				"half of |g(p)| is positive",
				"&0 < |g(p)| / &2",
				ByArith(pole[2], complex_abs.AbsPosIffNonzero.At(gp)))
			η, radius := a.UnpackAs[Real](
				GroupPremises(
					half,
					a.Unfolded(continuous, complex_topology.ComplexContinuousAtDef).At(a.TermAs[Real]("|g(p)| / &2"))),
				"η")
			near := a.Conjuncts(
				radius,
				"η is positive",
				"within η of p, g(z) lies within |g(p)|/2 of g(p)")
			κ, κDef := a.LetAs[Real]("κ", "|g(p)| / &2 / (|M| + &1)")
			sizes := a.Have(
				"|M| + 1 is positive, and so is κ, |g(p)|/2 over it",
				"&0 < |M| + &1 ∧ &0 < κ",
				ByArith(
					half,
					κDef,
					real_sgn_abs.AbsNonneg.At(M),
					real_order_field.DivPos.At(a.TermAs[Real]("|g(p)| / &2"), a.TermAs[Real]("|M| + &1"))))
			δ, δDef := a.LetAs[Real]("δ", "min(min(ρ, η), min(&1, κ))")
			inner := a.TermAs[Real]("min(ρ, η)")
			outer := a.TermAs[Real]("min(&1, κ)")
			positive := a.Have(
				"δ is positive, the smallest of four positive numbers",
				"&0 < δ",
				ByArith(
					δDef,
					pole[0],
					near[0],
					sizes,
					real_sup_inf.LessThanMin.At(inner, outer, a.TermAs[Real]("&0")),
					real_sup_inf.LessThanMin.At(ρ, η, a.TermAs[Real]("&0")),
					real_sup_inf.LessThanMin.At(a.TermAs[Real]("&1"), κ, a.TermAs[Real]("&0"))))
			large := a.Have(
				"off p within δ of it, |f| exceeds M",
				"∀z:complex. z ∈ «punctured»(p, δ) ⇒ M < |f(z)|",
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					within := d.Assume()
					distance := d.TermAs[Real]("|z - p|")
					small := d.Have(
						"z lies off p, within ρ, η, 1 and κ of it",
						"&0 < |z - p| ∧ |z - p| < ρ ∧ |z - p| < η ∧ |z - p| < &1 ∧ |z - p| < κ",
						ByArith(
							within,
							δDef,
							real_sup_inf.LessThanMin.At(inner, outer, distance),
							real_sup_inf.LessThanMin.At(ρ, η, distance),
							real_sup_inf.LessThanMin.At(a.TermAs[Real]("&1"), κ, distance)))
					value := d.Have(
						"f(z) is g(z)/(z − p)ᵐ⁺¹, z lying off p within ρ of it",
						"f(z) = g(z) / (z - p) ^ (m + 1)",
						By(small, pole[3].At(z)))
					gz := d.TermAs[Complex]("g(z)")
					bigNumerator := d.Have(
						"|g(z)| exceeds |g(p)|/2, g(z) lying within |g(p)|/2 of g(p)",
						"|g(p)| / &2 < |g(z)|",
						ByArith(small, near[1].At(z), complex_abs.AbsTriangleReverse.At(gz, gp)))
					order := d.TermAs[Nat]("m + 1")
					smallDenominator := d.Have(
						"|z − p|ᵐ⁺¹ is positive and at most |z − p|, which is below 1",
						"&0 < real_pow(|z - p|, m + 1) ∧ real_pow(|z - p|, m + 1) ≤ |z - p|",
						ByArith(
							small,
							real_pow.PowPos.At(distance, order),
							real_pow.PowMonoExpBelowOne.At(distance, d.TermAs[Nat]("1"), order),
							real_pow.PowOne.At(distance)))
					modulus := d.Have(
						"so |f(z)| is |g(z)| over |z − p|ᵐ⁺¹",
						"|f(z)| = |g(z)| / real_pow(|z - p|, m + 1)",
						value.Rw(),
						ByArith(
							complex_abs.AbsDiv.At(gz, d.TermAs[Complex]("(z - p) ^ (m + 1)")),
							complex_abs.AbsPow.At(d.TermAs[Complex]("z - p"), order)))
					denominator := d.TermAs[Real]("real_pow(|z - p|, m + 1)")
					bound := d.TermAs[Real]("|M| + &1")
					d.Show(
						"so |f(z)| exceeds M: M·|z − p|ᵐ⁺¹ ≤ (|M| + 1)·|z − p| < |g(p)|/2 < |g(z)|",
						ByArith(
							modulus,
							bigNumerator,
							smallDenominator,
							small,
							sizes,
							κDef,
							real_sgn_abs.AbsDominates.At(M),
							real_order_ring.LessEqMulRight.At(M, bound, denominator),
							real_order_ring.LessEqMulLeft.At(bound, denominator, distance),
							real_order_field.LessThanDivMulLeft.At(distance, d.TermAs[Real]("|g(p)| / &2"), bound),
							real_order_field.LessThanDivMulLeft.At(M, d.TermAs[Real]("|g(z)|"), denominator)))
				}))
			a.Take(δ)
			a.Show(
				"δ is positive, and |f| exceeds M off p within it",
				By(positive, large))
		}),
})}

// NoPoleNearContinuity — a function has no proper pole near a point where it
// is continuous: its proper poles all lie at least some δ > 0 from q. Within
// δ of q it stays within 1 of f(q), so below |f(q)| + 1, while near a proper
// pole it exceeds every bound (PoleUnbounded).
var NoPoleNearContinuity = noPoleNearContinuityThm{family.Add(registry.ProofEntry{
	Name: "NoPoleNearContinuity",
	Key:  "prop_62af828644870be2",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀q:complex.",
		Hypotheses: []string{
			"complex_continuous_at(f, q)",
		},
		Conclusion: "∃δ:real. &0 < δ ∧ ∀p:complex. «properPole»(f, p) ⇒ δ ≤ |p - q|",
	},
		func(a *Argument, f *Arrow[Complex, Complex], q *Expr[Complex], continuous Fact) {
			one := a.Have(
				"1 is positive",
				"&0 < &1",
				ByArith())
			δ, radius := a.UnpackAs[Real](
				GroupPremises(
					one, a.Unfolded(continuous, complex_topology.ComplexContinuousAtDef).At(a.TermAs[Real]("&1"))),
				"δ")
			near := a.Conjuncts(
				radius,
				"δ is positive",
				"within δ of q, f(z) lies within 1 of f(q)")
			fq := a.TermAs[Complex]("f(q)")
			none := a.Have(
				"every proper pole of f lies at least δ from q",
				"∀p:complex. «properPole»(f, p) ⇒ δ ≤ |p - q|",
				Derive(func(d *Argument) {
					p := d.FixAs[Complex]("p")
					proper := d.Assume()
					close := d.SupposeNot()
					η, unbounded := d.UnpackAs[Real](
						GroupPremises(proper, PoleUnbounded.At(f, p, d.TermAs[Real]("|f(q)| + &1"))),
						"η")
					far := d.Conjuncts(
						unbounded,
						"η is positive",
						"off p within η of it, |f| exceeds |f(q)| + 1")
					ε := d.TermAs[Real]("min(η, δ - |p - q|)")
					room := d.TermAs[Real]("δ - |p - q|")
					z := d.TermAs[Complex]("p + &(min(η, δ - |p - q|) / &2)")
					positive := d.Have(
						"ε = min(η, δ − |p − q|) is positive",
						"&0 < min(η, δ - |p - q|)",
						ByArith(far[0], close, real_sup_inf.LessThanMin.At(η, room, d.TermAs[Real]("&0"))))
					point := d.Have(
						"z = p + ε/2 lies off p, within ε of it",
						"&0 < |p + &(min(η, δ - |p - q|) / &2) - p| ∧ "+
							"|p + &(min(η, δ - |p - q|) / &2) - p| < min(η, δ - |p - q|)",
						By(positive, complex_topology.PuncturedDiscPoint.At(p, ε)))
					offPole := d.Have(
						"so z lies off p within η of it, and within δ of q",
						"p + &(min(η, δ - |p - q|) / &2) ∈ «punctured»(p, η) ∧ |p + &(min(η, δ - |p - q|) / &2) - q| < δ",
						ByArith(point, real_sup_inf.MinLowerBound.At(η, room), complex_abs.AbsSubTriangle.At(z, p, q)))
					fz := d.TermAs[Complex]("f(p + &(min(η, δ - |p - q|) / &2))")
					d.Show(
						"there |f(z)| exceeds |f(q)| + 1, yet f(z) lies within 1 of f(q)",
						ByArith(offPole, far[1].At(z), near[1].At(z), complex_abs.AbsTriangleReverse.At(fz, fq)))
				}))
			a.Take(δ)
			a.Show(
				"δ is positive, and no proper pole lies within it of q",
				By(near[0], none))
		}),
})}

// PolePuncturedHolomorphic — a function is holomorphic on a punctured disc
// about each of its proper poles: off p near p it is g(z)/(z − p)ᵐ⁺¹, a
// quotient of functions holomorphic there whose denominator is not 0 off p,
// and the punctured disc is open.
var PolePuncturedHolomorphic = polePuncturedHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "PolePuncturedHolomorphic",
	Key:  "prop_e57bb2c0e1f81c9c",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀p:complex.",
		Hypotheses: []string{
			"«properPole»(f, p)",
		},
		Conclusion: "∃ρ:real. &0 < ρ ∧ holomorphic_on(«punctured»(p, ρ), f)",
	},
		func(a *Argument, f *Arrow[Complex, Complex], p *Expr[Complex], proper Fact) {
			_, ρ, g, data := a.Unpack3As[Nat, Real, Fun[Complex, Complex]](proper, "m", "ρ", "g")
			pole := a.Conjuncts(
				data,
				"ρ is positive",
				"g is holomorphic on the disc of radius ρ about p",
				"g(p) is not 0",
				"off p on that disc, f is g/(z − p)ᵐ⁺¹")
			punctured := a.TermAs[Set[Complex]]("«punctured»(p, ρ)")
			order := a.TermAs[Nat]("m + 1")
			shift := a.TermAs[Fun[Complex, Complex]]("λu:complex. u - p")
			inDisc := a.Have(
				"the punctured disc lies in the disc",
				"«punctured»(p, ρ) ⊆ «disc»(p, ρ)",
				BySets())
			translation := a.Have(
				"u − p, a difference of the identity and a constant, is holomorphic on the punctured disc",
				"holomorphic_on(«punctured»(p, ρ), λu:complex. u - p)",
				By(
					complex_derivative.HolomorphicOnId.At(punctured),
					complex_derivative.HolomorphicOnConst.At(punctured, p),
					complex_derivative.HolomorphicOnSub.At(
						punctured,
						a.TermAs[Fun[Complex, Complex]]("λu:complex. u"),
						a.TermAs[Fun[Complex, Complex]]("λu:complex. p"))))
			nonzero := a.Have(
				"(u − p)ᵐ⁺¹ is not 0 there, u − p not being 0",
				"∀u:complex. u ∈ «punctured»(p, ρ) ⇒ (u - p) ^ (m + 1) ≠ &0",
				Derive(func(d *Argument) {
					d.FixAs[Complex]("u")
					inside := d.Assume()
					difference := d.TermAs[Complex]("u - p")
					d.Show(
						"a power of a nonzero number is not 0",
						ByArith(
							inside,
							complex_abs.AbsPosIffNonzero.At(difference),
							field.PowEqZero.Read(complex_field.Field).At(difference, order)))
				}))
			quotient := a.Have(
				"so the quotient g(u)/(u − p)ᵐ⁺¹ is holomorphic there",
				"holomorphic_on(«punctured»(p, ρ), λu:complex. g(u) / (u - p) ^ (m + 1))",
				By(
					pole[1],
					inDisc,
					translation,
					nonzero,
					complex_derivative.HolomorphicOnSubset.At(a.TermAs[Set[Complex]]("«disc»(p, ρ)"), punctured, g),
					complex_derivative.HolomorphicOnPow.At(punctured, shift, order),
					complex_derivative.HolomorphicOnDiv.At(
						punctured,
						g,
						a.TermAs[Fun[Complex, Complex]]("λu:complex. (u - p) ^ (m + 1)"))))
			a.Take(ρ)
			a.Show(
				"and f is that quotient on the open punctured disc",
				By(
					pole[0],
					pole[3],
					quotient,
					complex_topology.PuncturedDiscOpen.At(p, ρ),
					complex_derivative.HolomorphicOnAgree.At(
						punctured,
						f,
						a.TermAs[Fun[Complex, Complex]]("λu:complex. g(u) / (u - p) ^ (m + 1)"))))
		}),
})}

// PolesFiniteInClosedDisc — the proper poles of a function holomorphic on a
// disc off them are finitely many in each smaller closed disc. About each
// point q of the disc lies a disc in which no pole but q lies: if q is a
// pole, f is holomorphic, so continuous, on a punctured disc about it
// (PolePuncturedHolomorphic), and no pole lies near a point of continuity
// (NoPoleNearContinuity), a pole there included; if not, f is continuous at q
// itself. Were the poles in the closed disc infinitely many, they would have
// a limit point q in it, which is compact, and some pole other than q would
// lie in each disc about q.
var PolesFiniteInClosedDisc = polesFiniteInClosedDiscThm{family.Add(registry.ProofEntry{
	Name: "PolesFiniteInClosedDisc",
	Key:  "prop_67c8369e5e59e7df",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀R r:real. ∀P:set(complex).",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R) ∖ P, f)",
			"∀p:complex. p ∈ P ⇒ «properPole»(f, p)",
			"r < R",
		},
		Conclusion: "finite({p:complex | p ∈ P ∧ |p - c| ≤ r})",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c *Expr[Complex],
			R, r *Expr[Real],
			P *Expr[Set[Complex]],
			holomorphic, poles, smaller Fact,
		) {
			isolated := arg.Have(
				"about each point q of the disc lies a disc in which no pole but q lies",
				"∀q:complex. |q - c| < R ⇒ ∃δ:real. &0 < δ ∧ (∀p:complex. p ∈ P ∧ |p - q| < δ ⇒ p = q)",
				Derive(func(d *Argument) {
					q := d.FixAs[Complex]("q")
					inside := d.Assume()
					d.Cases(d.TermAs[Bool]("q ∈ P"))
					d.When(
						"if q is a pole, f is continuous on a punctured disc about it, near whose points no pole lies",
						func(b *Argument, atPole Fact) {
							proper := b.Have(
								"q is a proper pole of f",
								"«properPole»(f, q)",
								By(atPole, poles.At(q)))
							ρ, near := b.UnpackAs[Real](GroupPremises(proper, PolePuncturedHolomorphic.At(f, q)), "ρ")
							parts := b.Conjuncts(
								near,
								"ρ is positive",
								"f is holomorphic on the punctured disc of radius ρ about q")
							apart := b.Have(
								"no pole other than q lies within ρ of q",
								"∀p:complex. p ∈ P ∧ |p - q| < ρ ⇒ p = q",
								Derive(func(e *Argument) {
									p := e.FixAs[Complex]("p")
									given := e.Assume()
									other := e.SupposeNot()
									offCentre := e.Have(
										"p lies off q within ρ of it",
										"p ∈ «punctured»(q, ρ)",
										ByArith(given, other, complex_abs.AbsPosIffNonzero.At(e.TermAs[Complex]("p - q"))))
									continuous := e.Have(
										"so f, holomorphic there, is continuous at p",
										"complex_continuous_at(f, p)",
										By(
											offCentre,
											parts[1],
											complex_derivative.HolomorphicOnContinuousAt.At(e.TermAs[Set[Complex]]("«punctured»(q, ρ)"), f, p)))
									_, away := e.UnpackAs[Real](GroupPremises(continuous, NoPoleNearContinuity.At(f, p)), "δ")
									far := e.Conjuncts(
										away,
										"δ is positive",
										"every proper pole of f lies at least δ from p")
									e.Show(
										"yet p is itself a proper pole, at distance 0 from p",
										ByArith(
											far[0],
											given,
											poles.At(p),
											far[1].At(p),
											complex_abs.AbsEqZero.At(e.TermAs[Complex]("p - p"))))
								}))
							b.Take(ρ)
							b.Show(
								"ρ is positive, and no other pole lies within it of q",
								By(parts[0], apart))
						})
					d.Otherwise(
						"if q is not a pole, f is continuous at q, and no pole lies near it",
						func(b *Argument, regular Fact) {
							offPoles := b.TermAs[Set[Complex]]("«disc»(c, R) ∖ P")
							member := b.Have(
								"q lies in the disc off the poles",
								"q ∈ «disc»(c, R) ∖ P",
								BySets(inside, regular))
							continuous := b.Have(
								"so f, holomorphic there, is continuous at q",
								"complex_continuous_at(f, q)",
								By(member, holomorphic, complex_derivative.HolomorphicOnContinuousAt.At(offPoles, f, q)))
							δ, away := b.UnpackAs[Real](GroupPremises(continuous, NoPoleNearContinuity.At(f, q)), "δ")
							far := b.Conjuncts(
								away,
								"δ is positive",
								"every proper pole of f lies at least δ from q")
							none := b.Have(
								"no pole lies within δ of q",
								"∀p:complex. p ∈ P ∧ |p - q| < δ ⇒ p = q",
								Derive(func(e *Argument) {
									p := e.FixAs[Complex]("p")
									given := e.Assume()
									e.Show(
										"a pole p is proper, so at least δ from q",
										ByArith(given, poles.At(p), far[1].At(p)))
								}))
							b.Take(δ)
							b.Show(
								"δ is positive, and no pole lies within it of q",
								By(far[0], none))
						})
				}))
			poleSet := arg.TermAs[Set[Complex]]("{p:complex | p ∈ P ∧ |p - c| ≤ r}")
			closed := arg.TermAs[Set[Complex]]("{z:complex | |z - c| ≤ r}")
			many := arg.SupposeNot()
			infinite := arg.Have(
				"suppose the poles in the closed disc of radius r are not finitely many: they form an infinite set",
				"infinite({p:complex | p ∈ P ∧ |p - c| ≤ r})",
				By(many, finite_set.InfiniteDef))
			within := arg.Have(
				"they lie in the closed disc",
				"{p:complex | p ∈ P ∧ |p - c| ≤ r} ⊆ {z:complex | |z - c| ≤ r}",
				BySets())
			q, limit := arg.ObtainAs[Complex](
				"the closed disc is compact, so the poles in it have a limit point q in it",
				"∃q:complex. "+
					"    q ∈ {z:complex | |z - c| ≤ r} ∧ "+
					"    q ∈ derived_set(complex_topology, {p:complex | p ∈ P ∧ |p - c| ≤ r})",
				By(
					infinite,
					within,
					complex_topology.ClosedDiscCompact.At(c, r),
					compact.CompactLimitPoint.At(arg.TermAs[Set[Set[Complex]]]("complex_topology"), closed, poleSet)),
				Named("q"))
			parts := arg.Conjuncts(
				limit,
				"q lies in the closed disc",
				"q is a limit point of the poles there")
			neighbourhoods := arg.Conjuncts(
				arg.Unfolded(parts[1], topological_space.DerivedSetDef),
				"q lies in the plane",
				"each open set holding q holds a pole other than q")
			inDisc := arg.Have(
				"q lies in the disc, r being below R",
				"|q - c| < R",
				ByArith(parts[0], smaller))
			δ, apart := arg.UnpackAs[Real](GroupPremises(inDisc, isolated.At(q)), "δ")
			around := arg.Conjuncts(
				apart,
				"δ is positive",
				"no pole but q lies within δ of q")
			ball := arg.TermAs[Set[Complex]]("{w:complex | |w - q| < δ}")
			centre := arg.Have(
				"the open disc of radius δ about q holds q",
				"q ∈ {w:complex | |w - q| < δ}",
				ByArith(around[0], complex_abs.AbsEqZero.At(arg.TermAs[Complex]("q - q"))))
			p, found := arg.UnpackAs[Complex](
				GroupPremises(complex_topology.DiscOpen.At(q, δ), centre, neighbourhoods[1].At(ball)),
				"p")
			point := arg.Conjuncts(
				found,
				"p is not q",
				"p is a pole in the closed disc",
				"p lies within δ of q")
			arg.Show(
				"yet no pole but q lies within δ of q",
				By(point[0], point[1], point[2], around[1].At(p)))
		}),
})}

// ZerosFiniteOffPoles — a function holomorphic on a disc off its proper
// poles, and not 0 throughout the disc off them, has finitely many zeros off
// the poles in each smaller closed disc. Where its zeros accumulate at a
// point q of the disc, f vanishes on a disc about q: q is no pole, near
// which f has no zero (PoleUnbounded), so f is continuous at q, no pole lies
// near it (NoPoleNearContinuity), and the identity theorem applies on a disc
// about q. So the points about which f vanishes on a disc form a set open in
// the plane holding each point of the disc it comes near; the disc being
// connected (DiscConnected), it holds no point of it, as f is not 0 at some
// point of the disc off the poles. Were the zeros in the closed disc
// infinitely many, they would accumulate at a point of it, which is compact.
var ZerosFiniteOffPoles = zerosFiniteOffPolesThm{family.Add(registry.ProofEntry{
	Name: "ZerosFiniteOffPoles",
	Key:  "prop_9c86e0bad6eeec5e",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀R r:real. ∀P:set(complex).",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R) ∖ P, f)",
			"∀p:complex. p ∈ P ⇒ «properPole»(f, p)",
			"r < R",
			"¬(∀z:complex. z ∈ «disc»(c, R) ∖ P ⇒ f(z) = &0)",
		},
		Conclusion: "finite({z:complex | |z - c| ≤ r ∧ z ∉ P ∧ f(z) = &0})",
		Abbrev: Abbrev{
			{Name: "vanishing", Text: "{z:complex | ∃ρ:real. &0 < ρ ∧ ∀x:complex. |x - z| < ρ ⇒ f(x) = &0}"},
		},
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c *Expr[Complex],
			R, r *Expr[Real],
			P *Expr[Set[Complex]],
			holomorphic, poles, smaller, notZero Fact,
		) {
			vanishes := arg.TermAs[Set[Complex]]("«vanishing»")
			spread := arg.Have(
				"where the zeros of f accumulate at a point q of the disc, f vanishes on a disc about q",
				Statement{
					Binders: "∀q:complex.",
					Hypotheses: []string{
						"|q - c| < R",
						"∀δ:real. &0 < δ ⇒ ∃x:complex. &0 < |x - q| ∧ |x - q| < δ ∧ f(x) = &0",
					},
					Conclusion: "∃ρ:real. &0 < ρ ∧ ∀x:complex. |x - q| < ρ ⇒ f(x) = &0",
				},
				Derive(func(d *Argument) {
					q := d.FixAs[Complex]("q")
					given := d.Conjuncts(
						d.Assume(),
						"q lies in the disc",
						"the zeros of f accumulate at q")
					regular := d.Have(
						"q is no pole: near a proper pole f has no zero, |f| exceeding 0",
						"q ∉ P",
						Derive(func(e *Argument) {
							atPole := e.SupposeNot()
							proper := e.Have(
								"q would be a proper pole",
								"«properPole»(f, q)",
								By(atPole, poles.At(q)))
							η, unbounded := e.UnpackAs[Real](
								GroupPremises(proper, PoleUnbounded.At(f, q, e.TermAs[Real]("&0"))),
								"η")
							far := e.Conjuncts(
								unbounded,
								"η is positive",
								"off q within η of it, |f| is positive")
							x, zero := e.UnpackAs[Complex](GroupPremises(far[0], given[1].At(η)), "x")
							e.Show(
								"yet some zero x of f lies off q within η of it",
								ByArith(zero, far[1].At(x), complex_abs.AbsEqZero.At(e.TermAs[Complex]("f(x)"))))
						}))
					offPoles := d.TermAs[Set[Complex]]("«disc»(c, R) ∖ P")
					member := d.Have(
						"q lies in the disc off the poles",
						"q ∈ «disc»(c, R) ∖ P",
						BySets(given[0], regular))
					continuous := d.Have(
						"so f, holomorphic there, is continuous at q",
						"complex_continuous_at(f, q)",
						By(member, holomorphic, complex_derivative.HolomorphicOnContinuousAt.At(offPoles, f, q)))
					δ, away := d.UnpackAs[Real](GroupPremises(continuous, NoPoleNearContinuity.At(f, q)), "δ")
					far := d.Conjuncts(
						away,
						"δ is positive",
						"every proper pole of f lies at least δ from q")
					ρ := d.TermAs[Real]("min(δ, R - |q - c|)")
					room := d.TermAs[Real]("R - |q - c|")
					positive := d.Have(
						"ρ = min(δ, R − |q − c|) is positive",
						"&0 < min(δ, R - |q - c|)",
						ByArith(far[0], given[0], real_sup_inf.LessThanMin.At(δ, room, d.TermAs[Real]("&0"))))
					inside := d.Have(
						"every point within ρ of q lies in the disc and is no pole",
						"∀x:complex. |x - q| < min(δ, R - |q - c|) ⇒ x ∈ «disc»(c, R) ∖ P",
						Derive(func(e *Argument) {
							x := e.FixAs[Complex]("x")
							near := e.Assume()
							bounds := e.Have(
								"x lies within δ of q, and within R of c",
								"|x - q| < δ ∧ |x - c| < R",
								ByArith(
									near,
									real_sup_inf.LessThanMin.At(δ, room, e.TermAs[Real]("|x - q|")),
									complex_abs.AbsSubTriangle.At(x, q, c)))
							notPole := e.Have(
								"so x is no pole, a pole lying at least δ from q",
								"x ∉ P",
								Derive(func(g *Argument) {
									atPole := g.SupposeNot()
									g.Show(
										"x would be a proper pole within δ of q",
										ByArith(bounds, atPole, poles.At(x), far[1].At(x)))
								}))
							e.Show(
								"x lies in the disc off the poles",
								BySets(bounds, notPole))
						}))
					small := d.TermAs[Set[Complex]]("«disc»(q, min(δ, R - |q - c|))")
					contained := d.Have(
						"so the disc of radius ρ about q lies in the disc off the poles",
						"«disc»(q, min(δ, R - |q - c|)) ⊆ «disc»(c, R) ∖ P",
						BySets(inside))
					holo := d.Have(
						"and f is holomorphic on it",
						"holomorphic_on(«disc»(q, min(δ, R - |q - c|)), f)",
						By(holomorphic, contained, complex_derivative.HolomorphicOnSubset.At(offPoles, small, f)))
					centre := d.Have(
						"q lies in that disc",
						"|q - q| < min(δ, R - |q - c|)",
						ByArith(positive, complex_abs.AbsEqZero.At(d.TermAs[Complex]("q - q"))))
					zeroDisc := d.Have(
						"by the identity theorem f vanishes on it, its zeros accumulating at q",
						"∀x:complex. |x - q| < min(δ, R - |q - c|) ⇒ f(x) = &0",
						d.ForEach(func(x *Expr[Complex]) Action {
							return By(holo, centre, given[1], cauchy_integral.IdentityTheorem.At(f, q, q, ρ, x))
						}))
					d.Take(ρ)
					d.Show(
						"so f vanishes on the disc of radius ρ about q",
						By(positive, zeroDisc))
				}))
			open := arg.Have(
				"the points about which f vanishes on a disc form an open set",
				"∀z:complex. z ∈ «vanishing» ⇒ ∃ρ:real. &0 < ρ ∧ (∀x:complex. |x - z| < ρ ⇒ x ∈ «vanishing»)",
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					in := d.Assume()
					ρ, ball := d.UnpackAs[Real](in, "ρ")
					around := d.Conjuncts(
						ball,
						"ρ is positive",
						"f vanishes within ρ of z")
					inner := d.Have(
						"about a point x within ρ of z, f vanishes within ρ − |x − z| of x",
						"∀x:complex. |x - z| < ρ ⇒ &0 < ρ - |x - z| ∧ (∀y:complex. |y - x| < ρ - |x - z| ⇒ f(y) = &0)",
						Derive(func(e *Argument) {
							x := e.FixAs[Complex]("x")
							near := e.Assume()
							within := e.Have(
								"a point y within ρ − |x − z| of x lies within ρ of z",
								"∀y:complex. |y - x| < ρ - |x - z| ⇒ |y - z| < ρ",
								e.ForEach(func(y *Expr[Complex]) Action {
									return ByArith(complex_abs.AbsSubTriangle.At(y, x, z))
								}))
							e.Show(
								"so f vanishes there",
								ByArith(near, within, around[1]))
						}))
					d.Take(ρ)
					d.Show(
						"the points within ρ of z lie in the set",
						BySets(around[0], inner))
				}))
			closedIn := arg.Have(
				"and a point of the disc the set comes arbitrarily near lies in it",
				Statement{
					Binders: "∀z:complex.",
					Hypotheses: []string{
						"|z - c| < R",
						"∀δ:real. &0 < δ ⇒ ∃x:complex. x ∈ «vanishing» ∧ |x - z| < δ",
					},
					Conclusion: "z ∈ «vanishing»",
				},
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					given := d.Conjuncts(
						d.Assume(),
						"z lies in the disc",
						"the set comes arbitrarily near z")
					outside := d.SupposeNot()
					accumulate := d.Have(
						"else the zeros of f accumulate at z: each point of the set near z is a zero other than z",
						"∀δ:real. &0 < δ ⇒ ∃x:complex. &0 < |x - z| ∧ |x - z| < δ ∧ f(x) = &0",
						Derive(func(e *Argument) {
							δ := e.FixAs[Real]("δ")
							positive := e.Assume()
							x, found := e.UnpackAs[Complex](GroupPremises(positive, given[1].At(δ)), "x")
							point := e.Conjuncts(
								found,
								"x lies in the set",
								"x lies within δ of z")
							zero := e.Have(
								"f vanishes at x, which lies in its own disc",
								"f(x) = &0",
								Derive(func(g *Argument) {
									_, ball := g.UnpackAs[Real](point[0], "ρ")
									around := g.Conjuncts(
										ball,
										"ρ is positive",
										"f vanishes within ρ of x")
									g.Show(
										"|x − x| = 0 < ρ",
										ByArith(around[0], around[1].At(x), complex_abs.AbsEqZero.At(g.TermAs[Complex]("x - x"))))
								}))
							apart := e.Have(
								"x is not z, x lying in the set and z not",
								"&0 < |x - z|",
								Derive(func(g *Argument) {
									same := g.SupposeNot()
									equal := g.Have(
										"x would be z",
										"x = z",
										ByArith(
											same,
											complex_abs.AbsNonneg.At(g.TermAs[Complex]("x - z")),
											complex_abs.AbsEqZero.At(g.TermAs[Complex]("x - z"))))
									g.Show(
										"and z would lie in the set",
										By(equal, point[0], outside))
								}))
							e.Take(x)
							e.Show(
								"x is a zero of f off z within δ of it",
								By(apart, point[1], zero))
						}))
					d.Show(
						"so f vanishes on a disc about z",
						BySets(given[0], accumulate, outside, spread.At(z)))
				}))
			zeros := arg.TermAs[Set[Complex]]("{z:complex | |z - c| ≤ r ∧ z ∉ P ∧ f(z) = &0}")
			closed := arg.TermAs[Set[Complex]]("{z:complex | |z - c| ≤ r}")
			many := arg.SupposeNot()
			infinite := arg.Have(
				"suppose the zeros in the closed disc of radius r are not finitely many: they form an infinite set",
				"infinite({z:complex | |z - c| ≤ r ∧ z ∉ P ∧ f(z) = &0})",
				By(many, finite_set.InfiniteDef))
			within := arg.Have(
				"they lie in the closed disc",
				"{z:complex | |z - c| ≤ r ∧ z ∉ P ∧ f(z) = &0} ⊆ {z:complex | |z - c| ≤ r}",
				BySets())
			q, limit := arg.ObtainAs[Complex](
				"the closed disc is compact, so the zeros have a limit point q in it",
				"∃q:complex. "+
					"    q ∈ {z:complex | |z - c| ≤ r} ∧ "+
					"    q ∈ derived_set(complex_topology, {z:complex | |z - c| ≤ r ∧ z ∉ P ∧ f(z) = &0})",
				By(
					infinite,
					within,
					complex_topology.ClosedDiscCompact.At(c, r),
					compact.CompactLimitPoint.At(arg.TermAs[Set[Set[Complex]]]("complex_topology"), closed, zeros)),
				Named("q"))
			parts := arg.Conjuncts(
				limit,
				"q lies in the closed disc",
				"q is a limit point of the zeros")
			neighbourhoods := arg.Conjuncts(
				arg.Unfolded(parts[1], topological_space.DerivedSetDef),
				"q lies in the plane",
				"each open set holding q holds a zero other than q")
			accumulate := arg.Have(
				"so the zeros of f accumulate at q",
				"∀δ:real. &0 < δ ⇒ ∃x:complex. &0 < |x - q| ∧ |x - q| < δ ∧ f(x) = &0",
				Derive(func(d *Argument) {
					δ := d.FixAs[Real]("δ")
					positive := d.Assume()
					ball := d.TermAs[Set[Complex]]("{w:complex | |w - q| < δ}")
					centre := d.Have(
						"the open disc of radius δ about q holds q",
						"q ∈ {w:complex | |w - q| < δ}",
						ByArith(positive, complex_abs.AbsEqZero.At(d.TermAs[Complex]("q - q"))))
					x, found := d.UnpackAs[Complex](
						GroupPremises(complex_topology.DiscOpen.At(q, δ), centre, neighbourhoods[1].At(ball)),
						"x")
					point := d.Conjuncts(
						found,
						"x is not q",
						"x is a zero in the closed disc",
						"x lies within δ of q")
					distance := d.Have(
						"x is not q, so it lies at positive distance from q",
						"&0 < |x - q|",
						ByArith(point[0], complex_abs.AbsPosIffNonzero.At(d.TermAs[Complex]("x - q"))))
					d.Take(x)
					d.Show(
						"x lies within δ of q, and f vanishes there",
						By(distance, point[1], point[2]))
				}))
			inDisc := arg.Have(
				"q lies in the disc, r being below R",
				"|q - c| < R",
				ByArith(parts[0], smaller))
			start := arg.Have(
				"so f vanishes on a disc about q",
				"q ∈ «vanishing»",
				BySets(inDisc, accumulate, spread.At(q)))
			w, witness := arg.ObtainAs[Complex](
				"f is not 0 at some point w of the disc off the poles",
				"∃w:complex. w ∈ «disc»(c, R) ∖ P ∧ f(w) ≠ &0",
				By(notZero),
				Named("w"))
			wPoint := arg.Conjuncts(
				witness,
				"w lies in the disc off the poles",
				"f(w) is not 0")
			wInside := arg.Have(
				"w lies in the disc",
				"|w - c| < R",
				BySets(wPoint[0]))
			reached := arg.Have(
				"the disc being connected, the set holds w",
				"w ∈ «vanishing»",
				By(open, closedIn, inDisc, start, wInside, cauchy_integral.DiscConnected.At(c, R, vanishes, q, w)))
			_, ball := arg.UnpackAs[Real](reached, "ρ")
			around := arg.Conjuncts(
				ball,
				"ρ is positive",
				"f vanishes within ρ of w")
			arg.Show(
				"so f(w) is 0, against the choice of w",
				ByArith(
					around[0],
					around[1].At(w),
					wPoint[1],
					complex_abs.AbsEqZero.At(arg.TermAs[Complex]("w - w"))))
		}),
})}
