// consequences.go — what the power series expansion gives. Cauchy's estimate
// bounds the coefficients by the function's size on a circle, and by its size
// on the open disc through the circles inside it; so a bounded entire
// function is constant (Liouville). The derived series sums to the
// derivative, so the derivative of a holomorphic function is holomorphic, and
// so is its logarithmic derivative on the open part where it does not vanish. A
// function not identically 0 near c has a first coefficient that is not 0, at
// m; its series is (z − c)ᵐ times the series of the coefficients from m on, so
// the function is (z − c)ᵐ times a function not 0 at c, and its zeros are
// isolated. Zeros accumulating at a point of a disc then spread along a
// segment, which makes the function vanish on the whole disc (the identity
// theorem); so a function not identically 0 has finitely many zeros in each
// smaller closed disc, the closed disc being compact. A function bounded near
// an isolated point, multiplied by (z − c)², is flat there and so expands
// about it, the first two coefficients 0: dividing by (z − c)² extends the
// function across the point.

package cauchy_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_power_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// CauchyEstimate — Cauchy's estimate: if a power series about c sums to f on
// the disc of radius R and |f| ≤ M on the circle of radius r < R, its n-th
// coefficient satisfies |a(n)|·rⁿ ≤ M. The sum is holomorphic on the disc, so
// the coefficients are those read off the circle, 2πi·a(n) being the integral
// of f(u)/(u − c)ⁿ⁺¹ round it; on the circle that integrand is at most M/rⁿ⁺¹
// in modulus, and the ML estimate bounds the integral by M/rⁿ⁺¹ times the
// length 2πr.
var CauchyEstimate = cauchyEstimateThm{family.Add(registry.ProofEntry{
	Name: "CauchyEstimate",
	Key:  "prop_3be4eb32d7a428c1",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀a:num → complex. ∀c:complex. ∀R r M:real. ∀n:num.",
		Hypotheses: []string{
			"∀z:complex. |z - c| < R ⇒ complex_sums(λk:num. a(k) * (z - c) ^ k, f(z))",
			"&0 < r",
			"r < R",
			"∀z:complex. |z - c| = r ⇒ |f(z)| ≤ M",
		},
		Conclusion: "|a(n)| * real_pow(r, n) ≤ M",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			a *Arrow[Nat, Complex],
			c *Expr[Complex],
			R, r, M *Expr[Real],
			n *Expr[Nat],
			sums, positive, smaller, bounded Fact,
		) {
			disc := arg.TermAs[Set[Complex]]("«disc»(c, R)")
			holomorphic := arg.Have(
				"the sum of the series is holomorphic on the disc",
				"holomorphic_on(«disc»(c, R), f)",
				By(sums, complex_power_series.PowerSeriesHolomorphicDisc.At(a, f, c, R)))
			inner := arg.Have(
				"inside the circle the series sums to f",
				"∀z:complex. |z - c| < r ⇒ complex_sums(λk:num. a(k) * (z - c) ^ k, f(z))",
				arg.ForEach(func(z *Expr[Complex]) Action {
					return ByArith(sums.At(z), smaller)
				}))
			circle := arg.Have(
				"and so does the series with the coefficients read off the circle",
				"∀z:complex. |z - c| < r ⇒ complex_sums(λk:num. «coef»(f, c, r, k) * (z - c) ^ k, f(z))",
				arg.ForEach(func(z *Expr[Complex]) Action {
					return ByArith(holomorphic, smaller, PowerSeriesExpansionCircle.At(f, c, z, R, r))
				}))
			coefficient := arg.Have(
				"so a(n) is the n-th coefficient read off the circle",
				"a(n) = «coef»(f, c, r, n)",
				By(
					inner,
					circle,
					positive,
					complex_power_series.CoefficientsUnique.At(
						a, arg.TermAs[Fun[Nat, Complex]]("λk:num. «coef»(f, c, r, k)"), f, c, r)))
			turn := arg.TermAs[Complex]("&(&2 * pi) * complex_i")
			modulus := arg.Have(
				"2πi has modulus 2π·|i| = 2π",
				"|&(&2 * pi) * complex_i| = &2 * pi",
				ByArith(
					real_trigonometry.PiBounds,
					complex_abs.AbsMul.At(arg.TermAs[Complex]("&(&2 * pi)"), arg.TermAs[Complex]("complex_i")),
					complex_abs.AbsOfReal.At(arg.TermAs[Real]("&2 * pi")),
					complex_abs.AbsI))
			an := a.Apply(n)
			times := arg.Have(
				"so 2πi·a(n) is the integral of f(u)/(u − c)ⁿ⁺¹ round the circle",
				"a(n) * (&(&2 * pi) * complex_i) = «circleInt»(λu:complex. f(u) / (u - c) ^ (n + 1), c, r)",
				ByArith(Scaled(turn, coefficient), path_integral.TwoPiINonzero))
			size := arg.Have(
				"and 2π|a(n)| is the modulus of that integral",
				"|a(n)| * (&2 * pi) = |«circleInt»(λu:complex. f(u) / (u - c) ^ (n + 1), c, r)|",
				By(times, modulus, complex_abs.AbsMul.At(an, turn)))
			next := arg.TermAs[Nat]("n + 1")
			estimate := arg.Have(
				"on the circle the integrand f(u)/(u − c)ⁿ⁺¹ is continuous, of modulus at most M/rⁿ⁺¹",
				Statement{
					Binders: "∀u:complex.",
					Hypotheses: []string{
						"|u - c| = r",
					},
					Conclusion: "complex_continuous_at(λv:complex. f(v) / (v - c) ^ (n + 1), u) ∧ " +
						"|f(u) / (u - c) ^ (n + 1)| ≤ M / real_pow(r, n + 1)",
				},
				Derive(func(d *Argument) {
					u := d.FixAs[Complex]("u")
					on := d.Assume()
					offset := d.TermAs[Complex]("u - c")
					apart := d.Have(
						"u lies in the disc and is not c, its distance r from c being positive and below R",
						"u ∈ «disc»(c, R) ∧ u ≠ c",
						ByArith(on, positive, smaller, complex_abs.AbsPosIffNonzero.At(offset)))
					continuous := d.Have(
						"f, holomorphic on the disc, is continuous at u, and so is the integrand, u not being c",
						"complex_continuous_at(λv:complex. f(v) / (v - c) ^ (n + 1), u)",
						By(
							apart,
							holomorphic,
							complex_derivative.HolomorphicOnContinuousAt.At(disc, f, u),
							CoefficientIntegrandContinuous.At(f, c, u, next)))
					d.Show(
						"|f(u)| ≤ M, and (u − c)ⁿ⁺¹ has modulus rⁿ⁺¹ > 0",
						ByArith(
							continuous,
							on,
							positive,
							bounded.At(u),
							complex_abs.AbsDiv.At(f.Apply(u), d.TermAs[Complex]("(u - c) ^ (n + 1)")),
							complex_abs.AbsPow.At(offset, next),
							real_pow.PowPos.At(r, next)))
				}))
			scaled := arg.Have(
				"so by the ML estimate 2π|a(n)| is at most M/rⁿ⁺¹ times the circle's length 2πr",
				"|a(n)| * (&2 * pi) ≤ M / real_pow(r, n + 1) * (&2 * pi * r)",
				ByArith(
					size,
					estimate,
					positive,
					path_integral.CircleIntegralBound.At(
						arg.TermAs[Fun[Complex, Complex]]("λu:complex. f(u) / (u - c) ^ (n + 1)"),
						c,
						r,
						arg.TermAs[Real]("M / real_pow(r, n + 1)"))))
			power := arg.Have(
				"rⁿ⁺¹ is r·rⁿ, so M/rⁿ⁺¹ times r·rⁿ is M",
				"M / real_pow(r, n + 1) * r * real_pow(r, n) = M",
				ByArith(
					positive,
					Scaled(arg.TermAs[Real]("M / real_pow(r, n + 1)"), real_pow.PowAddOne.At(r, n)),
					real_pow.PowPos.At(r, next)))
			arg.Show(
				"dividing by 2π, |a(n)| ≤ M·r/rⁿ⁺¹, and multiplying by rⁿ gives the estimate",
				ByArith(scaled, real_trigonometry.PiBounds, power, positive, real_pow.PowPos.At(r, n)))
		}),
})}

// CauchyEstimateDisc — Cauchy's estimate at the radius of the disc itself: if
// a power series about c sums to f on the open disc of radius r and |f| ≤ M
// there, its n-th coefficient satisfies |a(n)|·rⁿ ≤ M. Each circle of radius
// ρₖ = r(1 − 1/(k + 2)) lies inside the disc, so CauchyEstimate gives
// |a(n)|·ρₖⁿ ≤ M; the radii tend to r, so their n-th powers tend to rⁿ, xⁿ
// being continuous, and the bound passes to the limit.
var CauchyEstimateDisc = cauchyEstimateDiscThm{family.Add(registry.ProofEntry{
	Name: "CauchyEstimateDisc",
	Key:  "prop_63c8696520cc5e86",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀a:num → complex. ∀c:complex. ∀r M:real. ∀n:num.",
		Hypotheses: []string{
			"∀z:complex. |z - c| < r ⇒ complex_sums(λk:num. a(k) * (z - c) ^ k, f(z))",
			"&0 < r",
			"∀z:complex. |z - c| < r ⇒ |f(z)| ≤ M",
		},
		Conclusion: "|a(n)| * real_pow(r, n) ≤ M",
		Abbrev: Abbrev{
			{Name: "ρ", Text: "λk:num. r * (&1 - real_inv(&k + &2))"},
		},
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			a *Arrow[Nat, Complex],
			c *Expr[Complex],
			r, M *Expr[Real],
			n *Expr[Nat],
			sums, positive, bounded Fact,
		) {
			one := arg.TermAs[Real]("&1")
			ratio := arg.TermAs[Fun[Nat, Real]]("λk:num. &1 - real_inv(&k + &2)")
			reciprocals := arg.Have(
				"1/(k + 2) lies strictly between 0 and 1, so 1 − 1/(k + 2) is within 1/(k + 1) of 1",
				"∀k:num. "+
					"    &0 < real_inv(&k + &2) ∧ "+
					"    real_inv(&k + &2) < &1 ∧ "+
					"    |&1 - real_inv(&k + &2) - &1| < real_inv(&k + &1)",
				Derive(func(d *Argument) {
					d.FixAs[Nat]("k")
					next := d.TermAs[Real]("&k + &2")
					d.Show(
						"k + 2 is positive and exceeds both 1 and k + 1, and inversion reverses the order of positives",
						ByArith(
							real_order_field.InvPos.At(next),
							real_order_field.InvAntitone.At(one, next),
							real_order_field.InvAntitone.At(d.TermAs[Real]("&k + &1"), next)))
				}))
			radii := arg.Have(
				"so the ratios 1 − 1/(k + 2) tend to 1, and the radii ρₖ to r·1 = r",
				"«ρ» ⟶ r",
				By(
					reciprocals,
					real_sequences.WithinReciprocalConverges.At(ratio, one),
					real_sequences.LimitScale.At(ratio, one, r),
					real_ring.MulRightId.At(r)))
			power := arg.TermAs[Fun[Real, Real]]("λx:real. real_pow(x, n)")
			rho := arg.TermAs[Fun[Nat, Real]]("«ρ»")
			powers := arg.Have(
				"xⁿ, differentiable, is continuous at r, so ρₖⁿ tends to rⁿ",
				"(λk:num. real_pow(«ρ»(k), n)) ⟶ real_pow(r, n)",
				By(
					radii,
					real_derivative.DerivativePow.At(n, r),
					real_derivative.DerivativeContinuous.At(power, r, arg.TermAs[Real]("&n * real_pow(r, n - 1)")),
					real_continuous.ContinuousAtSequential.At(power, rho, r),
					functions.ComposeApply.At(power, rho)))
			estimates := arg.Have(
				"Cauchy's estimate on each circle of radius ρₖ inside the disc: |a(n)|·ρₖⁿ ≤ M",
				"∀k:num. |a(n)| * real_pow(«ρ»(k), n) ≤ M",
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]("k")
					inside := d.Have(
						"ρₖ lies strictly between 0 and r",
						"&0 < «ρ»(k) ∧ «ρ»(k) < r",
						ByArith(reciprocals.At(k), positive))
					circle := d.Have(
						"the circle of radius ρₖ lies in the disc, so |f| ≤ M on it",
						"∀z:complex. |z - c| = «ρ»(k) ⇒ |f(z)| ≤ M",
						Derive(func(e *Argument) {
							z := e.FixAs[Complex]("z")
							on := e.Assume()
							e.Show(
								"z is at distance ρₖ < r from c",
								By(bounded.At(z), on, inside))
						}))
					d.Show(
						"Cauchy's estimate on the circle of radius ρₖ < r",
						By(sums, inside, circle, CauchyEstimate.At(f, a, c, r, d.TermAs[Real]("«ρ»(k)"), M, n)))
				}))
			arg.Show(
				"|a(n)|·ρₖⁿ tends to |a(n)|·rⁿ and never exceeds M, so neither does its limit",
				By(
					estimates,
					powers,
					real_sequences.LimitScale.At(
						arg.TermAs[Fun[Nat, Real]]("λk:num. real_pow(«ρ»(k), n)"),
						arg.TermAs[Real]("real_pow(r, n)"),
						arg.TermAs[Real]("|a(n)|")),
					real_sequences.LimitLessEqBound.At(
						arg.TermAs[Fun[Nat, Real]]("λk:num. |a(n)| * real_pow(«ρ»(k), n)"),
						arg.TermAs[Real]("|a(n)| * real_pow(r, n)"),
						M)))
		}),
})}

// Liouville — a bounded entire function is constant. Expand f about w on the
// disc of radius |z − w| + 1. On any larger disc f has an expansion too, with
// the same coefficients, so Cauchy's estimate on every circle about w gives
// |a(m)|·ρᵐ ≤ M for every radius ρ; for m ≥ 1 a nonzero a(m) fails this once
// ρ exceeds (M + 1)/|a(m)| + 1, so every coefficient after the first is 0, and
// the series sums to a(0) at every point of the disc, z and w included.
var Liouville = liouvilleThm{family.Add(registry.ProofEntry{
	Name: "Liouville",
	Key:  "prop_bebd7d08bf615a4f",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀M:real. ∀z w:complex.",
		Hypotheses: []string{
			"holomorphic_on(𝕌, f)",
			"∀u:complex. |f(u)| ≤ M",
		},
		Conclusion: "f(z) = f(w)",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			M *Expr[Real],
			z, w *Expr[Complex],
			entire, bounded Fact,
		) {
			discs := arg.Have(
				"f is holomorphic on every disc about w",
				"∀ρ:real. holomorphic_on(«disc»(w, ρ), f)",
				Derive(func(d *Argument) {
					d.FixAs[Real]("ρ")
					disc := d.TermAs[Set[Complex]]("«disc»(w, ρ)")
					d.Show(
						"every disc lies in the plane",
						By(
							entire,
							complex_derivative.HolomorphicOnSubset.At(d.TermAs[Set[Complex]]("𝕌"), disc, f),
							set_order.SubsetUniv.At(disc)))
				}))
			R := arg.TermAs[Real]("|z - w| + &1")
			a, expansion := arg.ObtainAs[Fun[Nat, Complex]](
				"f is the sum of a power series about w on the disc of radius |z − w| + 1",
				"∃a:num → complex. ∀u:complex. "+
					"    |u - w| < |z - w| + &1 ⇒ complex_sums(λn:num. a(n) * (u - w) ^ n, f(u))",
				By(discs, PowerSeriesExpansion.At(f, w, R)),
				Named("a"))
			radius := arg.Have(
				"the radius |z − w| + 1 is positive",
				"&0 < |z - w| + &1",
				ByArith(complex_abs.AbsNonneg.At(arg.TermAs[Complex]("z - w"))))
			bounds := arg.Have(
				"Cauchy's estimate holds on every circle about w: |a(m)|·ρᵐ ≤ M for every ρ > 0",
				"∀m:num. ∀ρ:real. &0 < ρ ⇒ |a(m)| * real_pow(ρ, m) ≤ M",
				Derive(func(d *Argument) {
					m := d.FixAs[Nat]("m")
					ρ := d.FixAs[Real]("ρ")
					positive := d.Assume()
					wider := d.TermAs[Real]("ρ + (|z - w| + &1)")
					b, larger := d.ObtainAs[Fun[Nat, Complex]](
						"f is also the sum of a power series about w on the disc of radius ρ + |z − w| + 1",
						"∃b:num → complex. ∀u:complex. "+
							"    |u - w| < ρ + (|z - w| + &1) ⇒ complex_sums(λk:num. b(k) * (u - w) ^ k, f(u))",
						By(discs, PowerSeriesExpansion.At(f, w, wider)),
						Named("b"))
					inner := d.Have(
						"that series sums to f on the smaller disc as well",
						"∀u:complex. |u - w| < |z - w| + &1 ⇒ complex_sums(λk:num. b(k) * (u - w) ^ k, f(u))",
						d.ForEach(func(u *Expr[Complex]) Action {
							return ByArith(positive, larger.At(u))
						}))
					same := d.Have(
						"so its coefficients are those of a",
						"a(m) = b(m)",
						By(expansion, inner, radius, complex_power_series.CoefficientsUnique.At(a, b, f, w, R)))
					inside := d.Have(
						"the circle of radius ρ lies inside the larger disc",
						"ρ < ρ + (|z - w| + &1)",
						ByArith(radius))
					d.Show(
						"Cauchy's estimate for b on that circle bounds |b(m)|·ρᵐ = |a(m)|·ρᵐ by M",
						ByArith(same, CauchyEstimate.At(f, b, w, wider, ρ, M, m), larger, positive, inside, bounded))
				}))
			vanish := arg.Have(
				"so every coefficient after the first is 0",
				"∀m:num. a(m + 1) = &0",
				Derive(func(d *Argument) {
					d.FixAs[Nat]("m")
					next := d.TermAs[Nat]("m + 1")
					coefficient := d.TermAs[Complex]("a(m + 1)")
					nonzero := d.SupposeNot()
					size := d.Have(
						"were a(m + 1) not 0, its modulus would be positive",
						"&0 < |a(m + 1)|",
						By(nonzero, complex_abs.AbsPosIffNonzero.At(coefficient)))
					big := d.TermAs[Real]("(M + &1) / |a(m + 1)| + &1")
					large := d.Have(
						"the radius ρ = (M + 1)/|a(m + 1)| + 1, chosen so that |a(m + 1)|·ρ exceeds M, is at least 1",
						"&1 ≤ (M + &1) / |a(m + 1)| + &1",
						ByArith(
							bounded.At(w),
							complex_abs.AbsNonneg.At(f.Apply(w)),
							size,
							real_order_field.DivPos.At(d.TermAs[Real]("M + &1"), d.TermAs[Real]("|a(m + 1)|"))))
					grow := d.Have(
						"so ρ ≤ ρᵐ⁺¹",
						"(M + &1) / |a(m + 1)| + &1 ≤ real_pow((M + &1) / |a(m + 1)| + &1, m + 1)",
						ByArith(large, real_pow.PowMonoExp.At(big, d.TermAs[Nat]("1"), next), real_pow.PowOne.At(big)))
					times := d.Have(
						"|a(m + 1)|·ρ is M + 1 + |a(m + 1)|",
						"|a(m + 1)| * ((M + &1) / |a(m + 1)| + &1) = M + &1 + |a(m + 1)|",
						ByArith(size))
					d.Show(
						"then M + 1 + |a(m + 1)| = |a(m + 1)|·ρ ≤ |a(m + 1)|·ρᵐ⁺¹ ≤ M, which is absurd",
						ByArith(times, grow, size, large, bounds.At(next, big)))
				}))
			constant := arg.Have(
				"at every point of the disc only the first term of the series is not 0, so f is a(0) there",
				"∀u:complex. |u - w| < |z - w| + &1 ⇒ f(u) = a(0)",
				Derive(func(d *Argument) {
					u := d.FixAs[Complex]("u")
					inside := d.Assume()
					later := d.Have(
						"every term after the first is 0",
						"∀n:num. a(n + 1) * (u - w) ^ (n + 1) = &0",
						Derive(func(e *Argument) {
							n := e.FixAs[Nat]("n")
							e.Show(
								"its coefficient is 0",
								vanish.At(n).Rw(),
								ByArith())
						}))
					first := d.Have(
						"the first term is a(0)·(u − w)⁰ = a(0)",
						"a(0) - a(0) * (u - w) ^ 0 = &0",
						Simp(Fwd(comm_monoid.MonoidPowDef.Inst[Complex]())),
						ByArith())
					series := d.TermAs[Fun[Nat, Complex]]("λn:num. a(n) * (u - w) ^ n")
					zeroth := d.TermAs[Complex]("a(0)")
					d.Show(
						"so the series sums to a(0), and also to f(u)",
						By(
							later,
							first,
							complex_series.SumsShift.At(series, zeroth),
							complex_series.SumsOfReal,
							real_series.SumsZero,
							expansion.At(u),
							inside,
							complex_series.SumsUnique.At(series, f.Apply(u), zeroth)))
				}))
			arg.Show(
				"z and w both lie in the disc, so f(z) = a(0) = f(w)",
				ByArith(
					radius,
					complex_abs.AbsEqZero.At(arg.TermAs[Complex]("w - w")),
					constant.At(z),
					constant.At(w)))
		}),
})}

// HolomorphicDerivative — the derivative of a function holomorphic on an open
// set is holomorphic there. Choose a derivative g(z) of f at each point z of
// s. A disc about z lies in s, where f is the sum of its power series; at each
// point of the disc the derived series sums to a derivative of f, which is g
// there since a derivative is unique. So on the disc g is the sum of a power
// series, holomorphic, and in particular has a derivative at z.
var HolomorphicDerivative = holomorphicDerivativeThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicDerivative",
	Key:  "prop_e2bf1f9b59e5eb69",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f:(complex → complex).",
		Hypotheses: []string{
			"s ∈ complex_topology",
			"holomorphic_on(s, f)",
		},
		Conclusion: "∃g:(complex → complex). " +
			"    (∀z:complex. z ∈ s ⇒ complex_derivative_at(f, z, g(z))) ∧ holomorphic_on(s, g)",
	},
		func(arg *Argument, s *Expr[Set[Complex]], f *Arrow[Complex, Complex], open, holomorphic Fact) {
			pointwise := arg.Unfolded(holomorphic, complex_derivative.HolomorphicOnDef)
			g, derivative := arg.ObtainAs[Fun[Complex, Complex]](
				"choose a derivative g(z) of f at each point z of s",
				"∃g:(complex → complex). ∀z:complex. z ∈ s ⇒ complex_derivative_at(f, z, g(z))",
				By(pointwise))
			everywhere := arg.Have(
				"g has a derivative at every point of s",
				"∀z:complex. z ∈ s ⇒ ∃l:complex. complex_derivative_at(g, z, l)",
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					inS := d.Assume()
					r, ball := d.ObtainAs[Real](
						"s, being open, holds a disc of some radius r about z",
						"∃r:real. &0 < r ∧ (∀w:complex. |w - z| < r ⇒ w ∈ s)",
						By(open, inS, complex_topology.ComplexOpenIff.At(s)))
					radius := d.Conjuncts(
						ball,
						"r is positive",
						"every w within r of z lies in s")
					disc := d.TermAs[Set[Complex]]("«disc»(z, r)")
					within := d.Have(
						"the disc of radius r about z lies in s",
						"«disc»(z, r) ⊆ s",
						BySets(radius[1]))
					local := d.Have(
						"so f is holomorphic on that disc",
						"holomorphic_on(«disc»(z, r), f)",
						By(holomorphic, within, complex_derivative.HolomorphicOnSubset.At(s, disc, f)))
					a, expansion := d.UnpackAs[Fun[Nat, Complex]](
						GroupPremises(local, PowerSeriesExpansion.At(f, z, r)),
						"a")
					derived := d.Have(
						"at each point w of that disc the derived series sums to g(w)",
						"∀w:complex. |w - z| < r ⇒ complex_sums(λn:num. &(n + 1) * a(n + 1) * (w - z) ^ n, g(w))",
						Derive(func(e *Argument) {
							w := e.FixAs[Complex]("w")
							near := e.Assume()
							l, at := e.UnpackAs[Complex](
								GroupPremises(expansion, near, complex_power_series.PowerSeriesDerivativeDisc.At(a, f, z, r, w)),
								"l")
							e.Show(
								"it sums to a derivative l of f at w, which is g(w) since a derivative is unique",
								By(
									at,
									derivative.At(w),
									radius[1].At(w),
									near,
									complex_derivative.DerivativeUnique.At(f, w, l, e.TermAs[Complex]("g(w)"))))
						}))
					holoG := d.Have(
						"so g, the sum of a power series about z on that disc, is holomorphic there",
						"holomorphic_on(«disc»(z, r), g)",
						By(
							derived,
							complex_power_series.PowerSeriesHolomorphicDisc.At(
								d.TermAs[Fun[Nat, Complex]]("λn:num. &(n + 1) * a(n + 1)"), g, z, r)))
					centre := d.Have(
						"z lies in the disc",
						"z ∈ «disc»(z, r)",
						ByArith(radius[0], complex_abs.AbsEqZero.At(d.TermAs[Complex]("z - z"))))
					d.Show(
						"in particular g has a derivative at z",
						By(holoG, centre, complex_derivative.HolomorphicOnDef))
				}))
			arg.Take(g)
			arg.Show(
				"g is the derivative of f on s, and holomorphic there",
				By(derivative, everywhere, complex_derivative.HolomorphicOnDef))
		}),
})}

// LogDerivativeHolomorphic — the logarithmic derivative f′/f of a function
// holomorphic on an open set s is holomorphic where f does not vanish, and
// that part of s is open. The derivative g of f is holomorphic on s
// (HolomorphicDerivative); f is continuous at a point z where f(z) ≠ 0, so on
// a disc about z, inside s, f(w) is within |f(z)| of f(z) and is not 0; and a
// quotient of holomorphic functions is holomorphic where its denominator does
// not vanish.
var LogDerivativeHolomorphic = logDerivativeHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "LogDerivativeHolomorphic",
	Key:  "prop_6f4f87128919fbc2",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f:(complex → complex).",
		Hypotheses: []string{
			"s ∈ complex_topology",
			"holomorphic_on(s, f)",
		},
		Conclusion: "∃g:(complex → complex). " +
			"    (∀z:complex. z ∈ s ⇒ complex_derivative_at(f, z, g(z))) ∧ " +
			"    «nonvanishing» ∈ complex_topology ∧ " +
			"    holomorphic_on(«nonvanishing», λz:complex. g(z) / f(z))",
		Abbrev: Abbrev{
			{Name: "nonvanishing", Text: "{z:complex | z ∈ s ∧ f(z) ≠ &0}"},
		},
	},
		func(arg *Argument, s *Expr[Set[Complex]], f *Arrow[Complex, Complex], open, holomorphic Fact) {
			V := arg.TermAs[Set[Complex]]("«nonvanishing»")
			zero := arg.TermAs[Real]("&0")
			g, derivative := arg.UnpackAs[Fun[Complex, Complex]](
				GroupPremises(open, holomorphic, HolomorphicDerivative.At(s, f)),
				"g")
			parts := arg.Conjuncts(
				derivative,
				"g is the derivative of f on s",
				"g is holomorphic on s")
			openPart := arg.Have(
				"f stays away from 0 on a disc inside s about each point where it does not vanish",
				"«nonvanishing» ∈ complex_topology",
				Simp(Fwd(complex_topology.ComplexOpenIff)),
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					member := b.Assume()
					centre := b.Have(
						"z lies in s and f does not vanish at z",
						"z ∈ s ∧ f(z) ≠ &0",
						BySets(member))
					r, ball := b.ObtainAs[Real](
						"s, being open, holds a disc of some radius r about z",
						"∃r:real. &0 < r ∧ (∀w:complex. |w - z| < r ⇒ w ∈ s)",
						By(open, centre, complex_topology.ComplexOpenIff.At(s)))
					radius := b.Conjuncts(
						ball,
						"r is positive",
						"every w within r of z lies in s")
					modulus := b.TermAs[Real]("|f(z)|")
					positiveModulus := b.Have(
						"the modulus of f at z is positive",
						"&0 < |f(z)|",
						ByArith(centre))
					continuous := b.Have(
						"holomorphic f is continuous at z",
						"complex_continuous_at(f, z)",
						By(centre, holomorphic, complex_derivative.HolomorphicOnContinuousAt.At(s, f, z)))
					closeValues := b.Unfolded(continuous, complex_topology.ComplexContinuousAtDef)
					δ, close := b.ObtainAs[Real](
						"on a small disc the change in f is below its modulus at z",
						"∃δ:real. &0 < δ ∧ ∀w:complex. |w - z| < δ ⇒ |f(w) - f(z)| < |f(z)|",
						By(positiveModulus, closeValues.At(modulus)))
					change := b.Conjuncts(
						close,
						"the continuity radius is positive",
						"f varies by less than its modulus at z")
					b.Take(b.TermAs[Real]("min(δ, r)"))
					disc := b.Have(
						"on the disc of the smaller radius f does not vanish and stays in s",
						"∀w:complex. |w - z| < min(δ, r) ⇒ w ∈ «nonvanishing»",
						Derive(func(d *Argument) {
							w := d.FixAs[Complex]("w")
							near := d.Assume()
							both := d.Have(
								"the displacement lies below both radii",
								"|w - z| < δ ∧ |w - z| < r",
								By(near, real_sup_inf.LessThanMin.At(δ, r, d.TermAs[Real]("|w - z|"))))
							inS := d.Have(
								"w lies in s",
								"w ∈ s",
								By(both, radius[1].At(w)))
							value := d.TermAs[Complex]("f(w)")
							positive := d.Have(
								"f(w) is within |f(z)| of f(z), so its modulus is positive",
								"&0 < |f(w)|",
								ByArith(
									both,
									positiveModulus,
									change[1].At(w),
									complex_abs.AbsTriangleReverse.At(value, d.TermAs[Complex]("f(z)"))))
							d.Show(
								"the point belongs to the set where f does not vanish",
								BySets(inS, positive, complex_abs.AbsPosIffNonzero.At(value)))
						}))
					b.Show(
						"the smaller radius is positive and its disc lies in the set",
						By(change[0], radius[0], disc, real_sup_inf.LessThanMin.At(δ, r, zero)))
				}))
			within := arg.Have(
				"the set where f does not vanish lies in s",
				"«nonvanishing» ⊆ s",
				BySets())
			nonvanishing := arg.Have(
				"f does not vanish on that set",
				"∀z:complex. z ∈ «nonvanishing» ⇒ f(z) ≠ &0",
				Derive(func(b *Argument) {
					b.FixAs[Complex]("z")
					member := b.Assume()
					b.Show(
						"nonvanishing is a membership condition",
						BySets(member))
				}))
			arg.Take(g)
			arg.Show(
				"g is the derivative of f, and g / f is a quotient of holomorphic functions on the open set",
				By(
					parts[0],
					openPart,
					parts[1],
					holomorphic,
					within,
					nonvanishing,
					complex_derivative.HolomorphicOnSubset.At(s, V, g),
					complex_derivative.HolomorphicOnSubset.At(s, V, f),
					complex_derivative.HolomorphicOnDiv.At(V, g, f)))
		}),
})}

// ZeroFactor — a function holomorphic on a disc and not identically 0 there is
// (z − c)ᵐ times a function holomorphic on the disc and not 0 at its centre.
// Some coefficient of its expansion is not 0, else the series sums to 0
// everywhere; m is the least such index, and the series of the coefficients
// from m on sums to the factor h, whose value at c is a(m).
var ZeroFactor = zeroFactorThm{family.Add(registry.ProofEntry{
	Name: "ZeroFactor",
	Key:  "prop_250d5ce1e47e4529",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀R:real.",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R), f)",
			"¬(∀z:complex. |z - c| < R ⇒ f(z) = &0)",
		},
		Conclusion: "∃m:num. ∃h:(complex → complex). " +
			"    holomorphic_on(«disc»(c, R), h) ∧ " +
			"    h(c) ≠ &0 ∧ " +
			"    (∀z:complex. |z - c| < R ⇒ f(z) = (z - c) ^ m * h(z))",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c *Expr[Complex],
			R *Expr[Real],
			holomorphic, notZero Fact,
		) {
			a, expansion := arg.UnpackAs[Fun[Nat, Complex]](
				GroupPremises(holomorphic, PowerSeriesExpansion.At(f, c, R)),
				"a")
			w, witness := arg.ObtainAs[Complex](
				"some point w of the disc has f(w) ≠ 0",
				"∃w:complex. |w - c| < R ∧ f(w) ≠ &0",
				By(Normalized, notZero))
			somewhere := arg.Have(
				"some coefficient is not 0",
				"∃n:num. a(n) ≠ &0",
				Derive(func(d *Argument) {
					allZero := d.SupposeNot()
					terms := d.Have(
						"were every coefficient 0, so would every term be",
						"∀z:complex. ∀n:num. a(n) * (z - c) ^ n = &0",
						ByArith(allZero))
					zeroSum := d.Have(
						"and the series would sum to 0 everywhere",
						"∀z:complex. complex_sums(λn:num. a(n) * (z - c) ^ n, &0)",
						By(terms, complex_series.SumsOfReal, real_series.SumsZero))
					d.Show(
						"so f(w), its sum at w, would be 0",
						By(
							witness,
							expansion.At(w),
							zeroSum.At(w),
							complex_series.SumsUnique.At(
								d.TermAs[Fun[Nat, Complex]]("λn:num. a(n) * (w - c) ^ n"),
								f.Apply(w),
								d.TermAs[Complex]("complex_of_real(&0)"))))
				}))
			m, least := arg.ObtainAs[Nat](
				"let m be the least index whose coefficient is not 0",
				"∃m:num. a(m) ≠ &0 ∧ (∀k:num. k < m ⇒ a(k) = &0)",
				By(somewhere, nat_order.WellOrdering.At(arg.TermAs[Set[Nat]]("λn:num. a(n) ≠ &0"))))
			parts := arg.Conjuncts(
				least,
				"a(m) is not 0",
				"the coefficients below m are 0")
			h, factored := arg.UnpackAs[Fun[Complex, Complex]](
				GroupPremises(expansion, parts[1], complex_power_series.PowerSeriesFactor.At(a, f, c, R, m)),
				"h")
			pieces := arg.Conjuncts(
				factored,
				"the series of the a(n + m) sums to h on the disc",
				"f is (z − c)ᵐ·h on the disc")
			centre := arg.Have(
				"the disc holds w, so it is not empty and holds its centre",
				"|c - c| < R",
				ByArith(
					witness,
					complex_abs.AbsNonneg.At(arg.TermAs[Complex]("w - c")),
					complex_abs.AbsEqZero.At(arg.TermAs[Complex]("c - c"))))
			value := arg.Have(
				"h(c), the sum at the centre, is the constant coefficient a(0 + m) = a(m)",
				"h(c) = a(m)",
				By(
					pieces[0].At(c),
					centre,
					complex_power_series.PowerSeriesAtCentre.At(arg.TermAs[Fun[Nat, Complex]]("λn:num. a(n + m)"), c),
					complex_series.SumsUnique.At(
						arg.TermAs[Fun[Nat, Complex]]("λn:num. a(n + m) * (c - c) ^ n"),
						arg.TermAs[Complex]("h(c)"),
						arg.TermAs[Complex]("a(0 + m)")),
					nat_arith.AddLeftZeroClause.At(m)))
			holoH := arg.Have(
				"h, the sum of a power series on the disc, is holomorphic there",
				"holomorphic_on(«disc»(c, R), h)",
				By(
					pieces[0],
					complex_power_series.PowerSeriesHolomorphicDisc.At(
						arg.TermAs[Fun[Nat, Complex]]("λn:num. a(n + m)"), h, c, R)))
			arg.Take(m)
			arg.Take(h)
			arg.Show(
				"h is holomorphic, h(c) = a(m) ≠ 0, and f is (z − c)ᵐ·h",
				By(holoH, value, parts[0], pieces[1]))
		}),
})}

// IsolatedZeros — a function holomorphic on a disc and not identically 0 there
// has no zero at positive distance below some δ from the centre. Write f as
// (z − c)ᵐ·h with h(c) ≠ 0: h is continuous at c, so within some δ of c it
// stays within |h(c)| of h(c) and is not 0, and off c neither is (z − c)ᵐ.
var IsolatedZeros = isolatedZerosThm{family.Add(registry.ProofEntry{
	Name: "IsolatedZeros",
	Key:  "prop_dc73c796bc79d213",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀R:real.",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R), f)",
			"¬(∀z:complex. |z - c| < R ⇒ f(z) = &0)",
		},
		Conclusion: "∃δ:real. &0 < δ ∧ (∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ f(z) ≠ &0)",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c *Expr[Complex],
			R *Expr[Real],
			holomorphic, notZero Fact,
		) {
			m, h, factored := arg.Unpack2As[Nat, Fun[Complex, Complex]](
				GroupPremises(holomorphic, notZero, ZeroFactor.At(f, c, R)),
				"m",
				"h")
			parts := arg.Conjuncts(
				factored,
				"h is holomorphic on the disc",
				"h(c) is not 0",
				"f is (z − c)ᵐ·h on the disc")
			_, witness := arg.ObtainAs[Complex](
				"some point w of the disc has f(w) ≠ 0",
				"∃w:complex. |w - c| < R ∧ f(w) ≠ &0",
				By(Normalized, notZero))
			centre := arg.Have(
				"the disc holds w, so its radius is positive and it holds its centre",
				"&0 < R ∧ c ∈ «disc»(c, R)",
				ByArith(
					witness,
					complex_abs.AbsNonneg.At(arg.TermAs[Complex]("w - c")),
					complex_abs.AbsEqZero.At(arg.TermAs[Complex]("c - c"))))
			continuous := arg.Have(
				"h, holomorphic on the disc, is continuous at c",
				"complex_continuous_at(h, c)",
				By(
					parts[0],
					centre,
					complex_derivative.HolomorphicOnContinuousAt.At(arg.TermAs[Set[Complex]]("«disc»(c, R)"), h, c)))
			size := arg.Have(
				"|h(c)| is positive",
				"&0 < |h(c)|",
				By(parts[1], complex_abs.AbsPosIffNonzero.At(arg.TermAs[Complex]("h(c)"))))
			near := arg.Unfolded(continuous, complex_topology.ComplexContinuousAtDef)
			δ, radius := arg.UnpackAs[Real](GroupPremises(size, near.At(arg.TermAs[Real]("|h(c)|"))), "δ")
			bounds := arg.Conjuncts(
				radius,
				"δ is positive",
				"within δ of c, h is within |h(c)| of h(c)")
			apart := arg.Have(
				"f has no zero at positive distance below min(δ, R) from c",
				"∀z:complex. &0 < |z - c| ∧ |z - c| < min(δ, R) ⇒ f(z) ≠ &0",
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					point := d.Conjuncts(
						d.Assume(),
						"z is not c",
						"z lies within min(δ, R) of c")
					both := d.Have(
						"so z lies within δ and within R of c",
						"|z - c| < δ ∧ |z - c| < R",
						By(point[1], real_sup_inf.LessThanMin.At(δ, R, d.TermAs[Real]("|z - c|"))))
					negate := d.Have(
						"0 − h(c) is −h(c)",
						"&0 - h(c) = -h(c)",
						ByArith())
					hz := d.Have(
						"h(z) is not 0: else |0 − h(c)| = |h(c)| would be below |h(c)|",
						"h(z) ≠ &0",
						ByArith(negate, bounds[1].At(z), both, complex_abs.AbsNeg.At(d.TermAs[Complex]("h(c)"))))
					power := d.Have(
						"(z − c)ᵐ is not 0, z − c not being 0",
						"(z - c) ^ m ≠ &0",
						ByArith(
							point[0],
							complex_abs.AbsPosIffNonzero.At(d.TermAs[Complex]("z - c")),
							field.PowEqZero.Read(complex_field.Field).At(d.TermAs[Complex]("z - c"), m)))
					d.Show(
						"so f(z) = (z − c)ᵐ·h(z), a product of numbers not 0, is not 0",
						By(
							parts[2].At(z),
							both,
							hz,
							power,
							field.MulEqZero.Read(complex_field.Field).At(
								d.TermAs[Complex]("(z - c) ^ m"),
								d.TermAs[Complex]("h(z)"))))
				}))
			arg.Take(arg.TermAs[Real]("min(δ, R)"))
			arg.Show(
				"min(δ, R) is positive, both δ and R being so",
				ByArith(bounds[0], apart, centre, real_sup_inf.LessThanMin.At(δ, R, arg.TermAs[Real]("&0"))))
		}),
})}

// IdentityTheorem — a function holomorphic on a disc whose zeros accumulate
// at a point q of the disc vanishes on the whole disc. Where the zeros
// accumulate at a point p, f vanishes on each disc about p inside the disc,
// since otherwise they would be isolated at p; so where f vanishes on a disc
// about p, it vanishes on each disc inside the disc about any point w of that
// one, its zeros accumulating at w. Let ρ = R − |q − c| and run along the
// segment from c to q, at c + s·(q − c) at time s. The times in ⟦0, 1⟧ whose
// point has f vanishing on the disc of radius ρ about it form a set S, which
// holds 1 as the zeros accumulate at q; and an earlier time whose point lies
// less than ρ from that of a time of S lies in S, the disc of radius ρ about
// a point of the segment lying inside the disc. With k = ρ/(2R), a time s of
// S within k above the infimum of S is at most k, else s − k would lie in S
// below the infimum; so 0 lies in S, f vanishes on the disc of radius ρ about
// c, and so on the disc of radius R about c, the whole disc.
var IdentityTheorem = identityTheoremThm{family.Add(registry.ProofEntry{
	Name: "IdentityTheorem",
	Key:  "prop_3b7373092c71f6b2",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c q:complex. ∀R:real. ∀z:complex.",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R), f)",
			"|q - c| < R",
			"∀δ:real. &0 < δ ⇒ ∃w:complex. &0 < |w - q| ∧ |w - q| < δ ∧ f(w) = &0",
			"|z - c| < R",
		},
		Conclusion: "f(z) = &0",
		Abbrev: Abbrev{
			{Name: "ρ", Text: "R - |q - c|"},
			{Name: "S", Text: "{τ:real | " +
				"    &0 ≤ τ ∧ τ ≤ &1 ∧ ∀z:complex. |z - (c + &τ * (q - c))| " +
				"    < «ρ» ⇒ f(z) = &0}"},
		},
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c, q *Expr[Complex],
			R *Expr[Real],
			holomorphic, inside, accumulate Fact,
		) {
			local := arg.Have(
				"where the zeros of f accumulate at a point p, f vanishes on each disc about p inside the disc",
				Statement{
					Binders: "∀p:complex. ∀r:real.",
					Hypotheses: []string{
						"|p - c| + r ≤ R",
						"∀δ:real. &0 < δ ⇒ ∃z:complex. &0 < |z - p| ∧ |z - p| < δ ∧ f(z) = &0",
					},
					Conclusion: "∀z:complex. |z - p| < r ⇒ f(z) = &0",
				},
				Derive(func(d *Argument) {
					p := d.FixAs[Complex]("p")
					r := d.FixAs[Real]("r")
					given := d.Conjuncts(
						d.Assume(),
						"the disc of radius r about p lies inside the disc",
						"the zeros of f accumulate at p")
					within := d.Have(
						"every point within r of p lies within R of c",
						"∀z:complex. |z - p| < r ⇒ |z - c| < R",
						d.ForEach(func(z *Expr[Complex]) Action {
							return ByArith(given[0], complex_abs.AbsSubTriangle.At(z, p, c))
						}))
					contained := d.Have(
						"so the disc of radius r about p lies in the disc",
						"«disc»(p, r) ⊆ «disc»(c, R)",
						BySets(within))
					holo := d.Have(
						"and f is holomorphic on it",
						"holomorphic_on(«disc»(p, r), f)",
						By(
							holomorphic,
							contained,
							complex_derivative.HolomorphicOnSubset.At(
								d.TermAs[Set[Complex]]("«disc»(c, R)"),
								d.TermAs[Set[Complex]]("«disc»(p, r)"),
								f)))
					notZero := d.SupposeNot()
					δ, isolated := d.UnpackAs[Real](
						GroupPremises(holo, notZero, IsolatedZeros.At(f, p, r)),
						"δ")
					apart := d.Conjuncts(
						isolated,
						"δ is positive",
						"f has no zero at positive distance below δ from p")
					z, zero := d.UnpackAs[Complex](
						GroupPremises(apart[0], given[1].At(δ)),
						"z")
					d.Show(
						"else its zeros would be isolated at p, and yet one lies at positive distance below δ from p",
						By(zero, apart[1].At(z)))
				}))
			spread := arg.Have(
				"where f vanishes on a disc about p, it vanishes on "+
					"each disc inside the disc about a point w of that one",
				Statement{
					Binders: "∀p w:complex. ∀r₁ r₂:real.",
					Hypotheses: []string{
						"∀z:complex. |z - p| < r₁ ⇒ f(z) = &0",
						"|w - p| < r₁",
						"|w - c| + r₂ ≤ R",
					},
					Conclusion: "∀z:complex. |z - w| < r₂ ⇒ f(z) = &0",
				},
				Derive(func(d *Argument) {
					p := d.FixAs[Complex]("p")
					w := d.FixAs[Complex]("w")
					d.FixAs[Real]("r₁")
					r2 := d.FixAs[Real]("r₂")
					given := d.Conjuncts(
						d.Assume(),
						"f vanishes within r₁ of p",
						"w lies within r₁ of p",
						"the disc of radius r₂ about w lies inside the disc")
					accumulates := d.Have(
						"the zeros of f accumulate at w, the disc about p holding a disc about w",
						"∀δ:real. &0 < δ ⇒ ∃z:complex. &0 < |z - w| ∧ |z - w| < δ ∧ f(z) = &0",
						Derive(func(e *Argument) {
							δ := e.FixAs[Real]("δ")
							positive := e.Assume()
							room := e.TermAs[Real]("r₁ - |w - p|")
							ε := e.TermAs[Real]("min(δ, r₁ - |w - p|)")
							z := e.TermAs[Complex]("w + &(min(δ, r₁ - |w - p|) / &2)")
							small := e.Have(
								"ε = min(δ, r₁ − |w − p|) is positive and at most δ",
								"&0 < min(δ, r₁ - |w - p|) ∧ min(δ, r₁ - |w - p|) ≤ δ",
								ByArith(
									positive,
									given[1],
									real_sup_inf.LessThanMin.At(δ, room, e.TermAs[Real]("&0")),
									real_sup_inf.MinLowerBound.At(δ, room)))
							point := e.Have(
								"z = w + ε/2 lies at positive distance below ε from w",
								"&0 < |w + &(min(δ, r₁ - |w - p|) / &2) - w| ∧ "+
									"|w + &(min(δ, r₁ - |w - p|) / &2) - w| < min(δ, r₁ - |w - p|)",
								By(small, complex_topology.PuncturedDiscPoint.At(w, ε)))
							near := e.Have(
								"so z lies within r₁ of p",
								"|w + &(min(δ, r₁ - |w - p|) / &2) - p| < r₁",
								ByArith(point, real_sup_inf.MinLowerBound.At(δ, room), complex_abs.AbsSubTriangle.At(z, w, p)))
							e.Take(z)
							e.Show(
								"z lies at positive distance below δ from w, and f vanishes there",
								ByArith(small, point, near, given[0].At(z)))
						}))
					d.Show(
						"so f vanishes on the disc of radius r₂ about w",
						By(given[2], accumulates, local.At(w, r2)))
				}))
			ρ := arg.TermAs[Real]("«ρ»")
			S := arg.TermAs[Set[Real]]("«S»")
			gap := arg.TermAs[Complex]("q - c")
			positive := arg.Have(
				"ρ is positive, and so is R",
				"&0 < «ρ» ∧ &0 < R",
				ByArith(inside, complex_abs.AbsNonneg.At(gap)))
			fits := arg.Have(
				"the disc of radius ρ about q lies inside the disc",
				"|q - c| + «ρ» ≤ R",
				ByArith())
			start := arg.Have(
				"the zeros accumulate at q, so f vanishes on the disc of radius ρ about q",
				"∀z:complex. |z - q| < «ρ» ⇒ f(z) = &0",
				By(fits, accumulate, local.At(q, ρ)))
			step := arg.Have(
				"a time t ≥ 0 before a time s of S, whose point lies less than ρ from that at time s, lies in S",
				"∀s t:real. s ∈ «S» ∧ &0 ≤ t ∧ t ≤ s ∧ (s - t) * |q - c| < «ρ» ⇒ t ∈ «S»",
				Derive(func(d *Argument) {
					s := d.FixAs[Real]("s")
					t := d.FixAs[Real]("t")
					given := d.Conjuncts(
						d.Assume(),
						"s lies in S",
						"t is at least 0",
						"t is at most s",
						"the point at time t lies less than ρ from that at time s")
					atS := d.Conjuncts(
						given[0],
						"s is at least 0",
						"s is at most 1",
						"f vanishes on the disc of radius ρ about the point at time s")
					offset := d.TermAs[Complex]("q - c")
					difference := d.Have(
						"the point at time t less that at time s is (t − s)·(q − c)",
						"c + &t * (q - c) - (c + &s * (q - c)) = (&t - &s) * (q - c)",
						ByArith())
					back := d.Have(
						"t is at most s, so |t − s| is s − t",
						"|t - s| = s - t",
						ByArith(given[2], real_sgn_abs.AbsNegatedIffNonpos.At(d.TermAs[Real]("t - s"))))
					apart := d.Have(
						"so the two points lie (s − t)·|q − c| < ρ apart",
						"|c + &t * (q - c) - (c + &s * (q - c))| < «ρ»",
						difference.Rw(),
						ByArith(
							given[3],
							back,
							complex_abs.AbsMul.At(d.TermAs[Complex]("&t - &s"), offset),
							complex_abs.AbsOfRealSub.At(t, s)))
					shift := d.Have(
						"the point at time t less c is t·(q − c)",
						"c + &t * (q - c) - c = &t * (q - c)",
						ByArith())
					reach := d.Have(
						"so it lies t·|q − c| ≤ |q − c| from c, and the disc of radius ρ about it lies inside the disc",
						"|c + &t * (q - c) - c| + «ρ» ≤ R",
						shift.Rw(),
						ByArith(
							given[1],
							given[2],
							atS[1],
							complex_abs.AbsMul.At(d.TermAs[Complex]("&t"), offset),
							complex_abs.AbsOfNonnegReal.At(t),
							complex_abs.AbsNonneg.At(offset)))
					vanish := d.Have(
						"so f vanishes on the disc of radius ρ about the point at time t",
						"∀z:complex. |z - (c + &t * (q - c))| < «ρ» ⇒ f(z) = &0",
						By(
							atS[2],
							apart,
							reach,
							spread.At(d.TermAs[Complex]("c + &s * (q - c)"), d.TermAs[Complex]("c + &t * (q - c)"), ρ, ρ)))
					below := d.Have(
						"t is at most s, so at most 1",
						"t ≤ &1",
						ByArith(given[2], atS[1]))
					d.Show(
						"t lies in S",
						By(given[1], below, vanish))
				}))
			atOne := arg.Have(
				"the point at time 1 is q",
				"c + &(&1) * (q - c) = q",
				ByArith())
			ends := arg.Have(
				"1 lies in ⟦0, 1⟧",
				"&0 ≤ &1 ∧ &1 ≤ &1",
				ByArith())
			one := arg.Have(
				"so 1 lies in S",
				"&1 ∈ «S»",
				By(Normalized, ends, atOne, start))
			nonempty := arg.Have(
				"S is not empty",
				"«S» ≠ ∅",
				BySets(one))
			bounded := arg.Have(
				"S is bounded below by 0",
				"∃b:real. ∀s:real. s ∈ «S» ⇒ b ≤ s",
				Derive(func(d *Argument) {
					d.Take(d.TermAs[Real]("&0"))
					d.Show(
						"its times lie in ⟦0, 1⟧",
						BySets())
				}))
			k := arg.TermAs[Real]("«ρ» / R / &2")
			size := arg.Have(
				"a step of k = ρ/(2R) in time is positive, and k·R is below ρ",
				"&0 < «ρ» / R / &2 ∧ «ρ» / R / &2 * R < «ρ»",
				ByArith(positive, real_order_field.DivPos.At(ρ, R)))
			s, near := arg.ObtainAs[Real](
				"some time s of S lies within k above the infimum of S",
				"∃s:real. s ∈ «S» ∧ inf(«S») ≤ s ∧ s < inf(«S») + «ρ» / R / &2",
				By(nonempty, bounded, size, real_sup_inf.InfApproachWithin.At(S, k)),
				Named("s"))
			parts := arg.Conjuncts(
				near,
				"s lies in S",
				"s is at least the infimum of S",
				"s lies within k above it")
			atS := arg.Conjuncts(
				parts[0],
				"s is at least 0",
				"s is at most 1",
				"f vanishes on the disc of radius ρ about the point at time s")
			short := arg.Have(
				"s is at most k: else s − k would lie in S, below the infimum",
				"s ≤ «ρ» / R / &2",
				Derive(func(d *Argument) {
					beyond := d.SupposeNot()
					earlier := d.TermAs[Real]("s - «ρ» / R / &2")
					backStep := d.Have(
						"s − k lies in ⟦0, s⟧, a step of k back from s",
						"&0 ≤ s - «ρ» / R / &2 ∧ s - «ρ» / R / &2 ≤ s ∧ (s - (s - «ρ» / R / &2)) * |q - c| < «ρ»",
						ByArith(beyond, size, inside, complex_abs.AbsNonneg.At(gap)))
					inS := d.Have(
						"so s − k lies in S",
						"s - «ρ» / R / &2 ∈ «S»",
						By(parts[0], backStep, step.At(s, earlier)))
					d.Show(
						"and the infimum of S is at most s − k, against s < inf S + k",
						ByArith(parts[2], bounded, inS, real_sup_inf.InfLessEqMember.At(S, earlier)))
				}))
			zero := arg.TermAs[Real]("&0")
			toZero := arg.Have(
				"0 lies in ⟦0, s⟧, its point less than ρ from that at time s",
				"&0 ≤ &0 ∧ &0 ≤ s ∧ (s - &0) * |q - c| < «ρ»",
				ByArith(short, atS[0], size, positive, inside, complex_abs.AbsNonneg.At(gap)))
			zeroIn := arg.Have(
				"so 0 lies in S",
				"&0 ∈ «S»",
				By(parts[0], toZero, step.At(s, zero)))
			origin := arg.TermAs[Complex]("c + &(&0) * (q - c)")
			itself := arg.Have(
				"c lies within ρ of the point at time 0, which is c, "+
					"and the disc of radius R about c is the whole disc",
				"|c - (c + &(&0) * (q - c))| < «ρ» ∧ |c - c| + R ≤ R",
				ByArith(
					positive,
					complex_abs.AbsEqZero.At(arg.TermAs[Complex]("c - (c + &(&0) * (q - c))")),
					complex_abs.AbsEqZero.At(arg.TermAs[Complex]("c - c"))))
			arg.Show(
				"so f vanishes on the whole disc",
				By(zeroIn, itself, spread.At(origin, c, ρ, R)))
		}),
})}

// ZerosFiniteInClosedDisc — a function holomorphic on a disc and not
// identically 0 there has finitely many zeros in each smaller closed disc.
// Were they infinitely many, they would have a limit point q in the closed
// disc, which is compact; q lies in the disc, the zeros accumulate at it,
// and by the identity theorem f would vanish on the disc.
var ZerosFiniteInClosedDisc = zerosFiniteInClosedDiscThm{family.Add(registry.ProofEntry{
	Name: "ZerosFiniteInClosedDisc",
	Key:  "prop_7e7445c88347f108",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀R r:real.",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R), f)",
			"r < R",
			"¬(∀z:complex. |z - c| < R ⇒ f(z) = &0)",
		},
		Conclusion: "finite({z:complex | |z - c| ≤ r ∧ f(z) = &0})",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c *Expr[Complex],
			R, r *Expr[Real],
			holomorphic, smaller, notZero Fact,
		) {
			zeros := arg.TermAs[Set[Complex]]("{z:complex | |z - c| ≤ r ∧ f(z) = &0}")
			closed := arg.TermAs[Set[Complex]]("{z:complex | |z - c| ≤ r}")
			many := arg.SupposeNot()
			infinite := arg.Have(
				"suppose the zeros in the closed disc of radius r are not finitely many: they form an infinite set",
				"infinite({z:complex | |z - c| ≤ r ∧ f(z) = &0})",
				By(many, finite_set.InfiniteDef))
			within := arg.Have(
				"they lie in the closed disc",
				"{z:complex | |z - c| ≤ r ∧ f(z) = &0} ⊆ {z:complex | |z - c| ≤ r}",
				BySets())
			q, limit := arg.ObtainAs[Complex](
				"the closed disc is compact, so the zeros have a limit point q in it",
				"∃q:complex. "+
					"    q ∈ {z:complex | |z - c| ≤ r} ∧ "+
					"    q ∈ derived_set(complex_topology, {z:complex | |z - c| ≤ r ∧ f(z) = &0})",
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
				"∀δ:real. &0 < δ ⇒ ∃z:complex. &0 < |z - q| ∧ |z - q| < δ ∧ f(z) = &0",
				Derive(func(d *Argument) {
					δ := d.FixAs[Real]("δ")
					positive := d.Assume()
					ball := d.TermAs[Set[Complex]]("{w:complex | |w - q| < δ}")
					centre := d.Have(
						"the open disc of radius δ about q holds q",
						"q ∈ {w:complex | |w - q| < δ}",
						ByArith(positive, complex_abs.AbsEqZero.At(d.TermAs[Complex]("q - q"))))
					z, found := d.UnpackAs[Complex](
						GroupPremises(complex_topology.DiscOpen.At(q, δ), centre, neighbourhoods[1].At(ball)),
						"z")
					point := d.Conjuncts(
						found,
						"z is not q",
						"z is a zero in the closed disc",
						"z lies within δ of q")
					distance := d.Have(
						"z is not q, so it lies at positive distance from q",
						"&0 < |z - q|",
						ByArith(point[0], complex_abs.AbsPosIffNonzero.At(d.TermAs[Complex]("z - q"))))
					d.Take(z)
					d.Show(
						"z lies within δ of q, and f vanishes there",
						By(distance, point[1], point[2]))
				}))
			inDisc := arg.Have(
				"q lies in the disc, r being below R",
				"|q - c| < R",
				ByArith(parts[0], smaller))
			w, witness := arg.ObtainAs[Complex](
				"f is not 0 at some point w of the disc",
				"∃w:complex. |w - c| < R ∧ f(w) ≠ &0",
				By(Normalized, notZero),
				Named("w"))
			arg.Show(
				"yet by the identity theorem f vanishes on the disc, at w too",
				By(witness, holomorphic, inDisc, accumulate, IdentityTheorem.At(f, c, q, R, w)))
		}),
})}

// RemovableSingularity — Riemann's theorem: a function holomorphic on a disc
// less its centre and bounded there extends to a function holomorphic on the
// whole disc. (z − c)²·f(z) is holomorphic off c, and at c its increment is at
// most M·|h|², so its derivative there is 0: it is holomorphic on the disc,
// its expansion about c has its first two coefficients 0, and so it is
// (z − c)² times the sum g of a power series, which agrees with f off c.
var RemovableSingularity = removableSingularityThm{family.Add(registry.ProofEntry{
	Name: "RemovableSingularity",
	Key:  "prop_3c1f0ff5e68abb28",
	Build: family.Sections(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀R M:real.",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R) ∖ {c}, f)",
			"∀z:complex. &0 < |z - c| ∧ |z - c| < R ⇒ |f(z)| ≤ M",
		},
		Conclusion: "∃g:(complex → complex). " +
			"    holomorphic_on(«disc»(c, R), g) ∧ (∀z:complex. &0 < |z - c| ∧ |z - c| < R ⇒ g(z) = f(z))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			flat := ctx.Lemma(Statement{
				Binders: "∀f:(complex → complex). ∀c:complex. ∀R M:real.",
				Hypotheses: []string{
					"&0 < R",
					"∀z:complex. &0 < |z - c| ∧ |z - c| < R ⇒ |f(z)| ≤ M",
				},
				Conclusion: "complex_derivative_at(λz:complex. (z - c) ^ 2 * f(z), c, &0)",
			},
				func(
					arg *Argument,
					f *Arrow[Complex, Complex],
					c *Expr[Complex],
					R, M *Expr[Real],
					positive, bounded Fact,
				) {
					remainder := arg.Have(
						"within R of c the increment of (z − c)²·f(z) is at most M·|h|²",
						"∀h:complex. |h| < R ⇒ |(c + h - c) ^ 2 * f(c + h) - (c - c) ^ 2 * f(c) - &0 * h| ≤ M * |h| ^ 2",
						Derive(func(d *Argument) {
							h := d.FixAs[Complex]("h")
							small := d.Assume()
							identity := d.Have(
								"the increment is h²·f(c + h), the value at c being 0",
								"(c + h - c) ^ 2 * f(c + h) - (c - c) ^ 2 * f(c) - &0 * h = h ^ 2 * f(c + h)",
								Simp(Fwd(comm_monoid.PowTwo.Read(complex_field.MulMonoid))),
								ByArith())
							d.Do(identity.Rw())
							apart := d.Unless(
								d.TermAs[Bool]("h = &0"),
								"at h = 0 both sides are 0",
								Given(func(b *Argument, zero Fact) {
									b.Show(
										"|0²·f(c)| = 0 = M·|0|²",
										ByArith(
											zero,
											complex_abs.AbsMul.At(b.TermAs[Complex]("h ^ 2"), b.TermAs[Complex]("f(c + h)")),
											complex_abs.AbsPow.At(h, b.TermAs[Nat]("2")),
											complex_abs.AbsEqZero.At(h)))
								}))
							shift := d.Have(
								"c + h lies at h from c",
								"c + h - c = h",
								ByArith())
							d.Show(
								"off 0, |h²·f(c + h)| = |h|²·|f(c + h)| ≤ |h|²·M",
								ByArith(
									apart,
									bounded.At(d.TermAs[Complex]("c + h")),
									shift,
									small,
									complex_abs.AbsMul.At(d.TermAs[Complex]("h ^ 2"), d.TermAs[Complex]("f(c + h)")),
									complex_abs.AbsPow.At(h, d.TermAs[Nat]("2")),
									complex_abs.AbsPosIffNonzero.At(h),
									real_order_ring.LessEqMulRight.At(
										d.TermAs[Real]("|f(c + h)|"),
										M,
										d.TermAs[Real]("|h| ^ 2"))))
						}))
					arg.Show(
						"an increment quadratic in h makes the derivative 0",
						By(
							remainder,
							positive,
							complex_derivative.DerivativeFromQuadraticRemainder.At(
								arg.TermAs[Fun[Complex, Complex]]("λz:complex. (z - c) ^ 2 * f(z)"),
								c,
								arg.TermAs[Complex]("&0"),
								M,
								R)))
				})
			return ctx.Theorem(headline,
				func(
					arg *Argument,
					f *Arrow[Complex, Complex],
					c *Expr[Complex],
					R, M *Expr[Real],
					holomorphic, bounded Fact,
				) {
					positive := arg.Assuming(
						arg.TermAs[Bool]("&0 < R"),
						"a disc of radius at most 0 is empty, so the zero function extends f",
						Given(func(b *Argument, empty Fact) {
							b.Take(b.TermAs[Fun[Complex, Complex]]("λz:complex. &0"))
							b.Show(
								"it is holomorphic everywhere, and there is no z with 0 < |z − c| < R",
								ByArith(empty, complex_derivative.HolomorphicOnConst))
						}))
					extension := arg.TermAs[Fun[Complex, Complex]]("λz:complex. (z - c) ^ 2 * f(z)")
					punctured := arg.TermAs[Set[Complex]]("«disc»(c, R) ∖ {c}")
					atCentre := arg.Have(
						"(z − c)²·f(z) has derivative 0 at c",
						"complex_derivative_at(λz:complex. (z - c) ^ 2 * f(z), c, &0)",
						By(positive, bounded, At(flat, f, c, R, M)))
					translation := arg.Have(
						"z ↦ z − c is holomorphic off c",
						"holomorphic_on(«disc»(c, R) ∖ {c}, λu:complex. u - c)",
						By(
							complex_derivative.HolomorphicOnDef,
							complex_derivative.DerivativeSub,
							complex_derivative.DerivativeId,
							complex_derivative.DerivativeConst))
					offCentre := arg.Have(
						"so is (z − c)²·f(z), by the product rule",
						"holomorphic_on(«disc»(c, R) ∖ {c}, λu:complex. (u - c) ^ 2 * f(u))",
						By(
							holomorphic,
							translation,
							complex_derivative.HolomorphicOnPow.At(
								punctured,
								arg.TermAs[Fun[Complex, Complex]]("λu:complex. u - c"),
								arg.TermAs[Nat]("2")),
							complex_derivative.HolomorphicOnMul.At(
								punctured,
								arg.TermAs[Fun[Complex, Complex]]("λu:complex. (u - c) ^ 2"),
								f)))
					everywhere := arg.Have(
						"(z − c)²·f(z) has a derivative at every point of the disc",
						Statement{
							Binders: "∀z:complex.",
							Hypotheses: []string{
								"z ∈ «disc»(c, R)",
							},
							Conclusion: "∃l:complex. complex_derivative_at(λu:complex. (u - c) ^ 2 * f(u), z, l)",
						},
						Derive(func(d *Argument) {
							d.FixAs[Complex]("z")
							inDisc := d.Assume()
							d.Cases(d.TermAs[Bool]("z = c"))
							d.When(
								"at c, the derivative 0",
								func(b *Argument, centre Fact) {
									b.Do(centre.Rw())
									b.Show(
										"which is a derivative",
										By(atCentre))
								})
							d.Otherwise(
								"off c, a derivative on the punctured disc",
								func(b *Argument, other Fact) {
									member := b.Have(
										"z lies in the punctured disc",
										"z ∈ «disc»(c, R) ∖ {c}",
										BySets(inDisc, other))
									b.Show(
										"where (z − c)²·f(z) is holomorphic",
										By(
											offCentre,
											member,
											complex_derivative.HolomorphicOnDef.At(
												punctured,
												b.TermAs[Fun[Complex, Complex]]("λu:complex. (u - c) ^ 2 * f(u)"))))
								})
						}))
					holoExtension := arg.Have(
						"so (z − c)²·f(z) is holomorphic on the disc",
						"holomorphic_on(«disc»(c, R), λz:complex. (z - c) ^ 2 * f(z))",
						By(everywhere, complex_derivative.HolomorphicOnDef))
					a, expansion := arg.UnpackAs[Fun[Nat, Complex]](
						GroupPremises(holoExtension, PowerSeriesExpansion.At(extension, c, R)),
						"a")
					centre := arg.Have(
						"the centre lies in the disc",
						"|c - c| < R",
						ByArith(positive, complex_abs.AbsEqZero.At(arg.TermAs[Complex]("c - c"))))
					difference := arg.Have(
						"c − c is 0",
						"c - c = &0",
						ByArith())
					valueAtCentre := arg.Have(
						"so (z − c)²·f(z) is 0 at c",
						"(c - c) ^ 2 * f(c) = &0",
						ByArith(difference))
					first := arg.Have(
						"the constant coefficient is the value at c, 0",
						"a(0) = &0",
						By(
							expansion.At(c),
							centre,
							valueAtCentre,
							complex_power_series.PowerSeriesAtCentre.At(a, c),
							complex_series.SumsUnique.At(
								arg.TermAs[Fun[Nat, Complex]]("λn:num. a(n) * (c - c) ^ n"),
								arg.TermAs[Complex]("a(0)"),
								arg.TermAs[Complex]("(c - c) ^ 2 * f(c)"))))
					d, derived := arg.UnpackAs[Complex](
						GroupPremises(
							expansion, centre, complex_power_series.PowerSeriesDerivativeDisc.At(a, extension, c, R, c)),
						"d")
					second := arg.Have(
						"the next is the derivative at c, the derived series' constant coefficient, also 0",
						"a(1) = &0",
						ByArith(
							derived,
							atCentre,
							complex_derivative.DerivativeUnique.At(extension, c, d, arg.TermAs[Complex]("&0")),
							complex_power_series.PowerSeriesAtCentre.At(
								arg.TermAs[Fun[Nat, Complex]]("λn:num. &(n + 1) * a(n + 1)"), c),
							complex_series.SumsUnique.At(
								arg.TermAs[Fun[Nat, Complex]]("λn:num. &(n + 1) * a(n + 1) * (c - c) ^ n"),
								d,
								arg.TermAs[Complex]("&(0 + 1) * a(0 + 1)")),
							nat_arith.AddLeftZeroClause.At(arg.TermAs[Nat]("1"))))
					early := arg.Have(
						"so both coefficients below 2 are 0",
						"∀k:num. k < 2 ⇒ a(k) = &0",
						Derive(func(e *Argument) {
							e.FixAs[Nat]("k")
							below := e.Assume()
							either := e.Have(
								"k is 0 or 1",
								"k = 0 ∨ k = 1",
								ByArith(below))
							e.Show(
								"and a(0) = a(1) = 0",
								By(Normalized, either, first, second))
						}))
					g, factored := arg.UnpackAs[Fun[Complex, Complex]](
						GroupPremises(
							expansion,
							early,
							complex_power_series.PowerSeriesFactor.At(a, extension, c, R, arg.TermAs[Nat]("2"))),
						"g")
					pieces := arg.Conjuncts(
						factored,
						"the series of the a(n + 2) sums to g on the disc",
						"(z − c)²·f(z) is (z − c)²·g(z) on the disc")
					agree := arg.Have(
						"off c, g(z) = f(z): the factor (z − c)² is not 0 and cancels",
						"∀z:complex. &0 < |z - c| ∧ |z - c| < R ⇒ g(z) = f(z)",
						Derive(func(e *Argument) {
							z := e.FixAs[Complex]("z")
							point := e.Conjuncts(
								e.Assume(),
								"z is not c",
								"z lies in the disc")
							square := e.Have(
								"(z − c)² is not 0, z − c not being 0",
								"(z - c) ^ 2 ≠ &0",
								ByArith(
									point[0],
									complex_abs.AbsPosIffNonzero.At(e.TermAs[Complex]("z - c")),
									field.PowEqZero.Read(complex_field.Field).At(e.TermAs[Complex]("z - c"), e.TermAs[Nat]("2"))))
							e.Show(
								"(z − c)²·(f(z) − g(z)) is 0 with the first factor not 0",
								ByArith(
									pieces[1].At(z),
									point[1],
									square,
									field.MulEqZero.Read(complex_field.Field).At(
										e.TermAs[Complex]("(z - c) ^ 2"),
										e.TermAs[Complex]("f(z) - g(z)"))))
						}))
					arg.Take(g)
					arg.Show(
						"g, the sum of a power series on the disc, is holomorphic there and agrees with f off c",
						By(
							pieces[0],
							agree,
							complex_power_series.PowerSeriesHolomorphicDisc.At(
								arg.TermAs[Fun[Nat, Complex]]("λn:num. a(n + 2)"), g, c, R)))
				})
		}),
})}
