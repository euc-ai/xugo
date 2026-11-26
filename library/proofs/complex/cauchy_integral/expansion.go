// expansion.go — Taylor's formula with Cauchy's remainder, the power series
// of a holomorphic function inside a circle, and its expansion on its whole
// disc.

package cauchy_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_power_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// CoefficientIntegrandContinuous — the integrand f(u)/(u − c)ⁿ of a Cauchy
// coefficient is continuous wherever f is, away from c: the power (u − c)ⁿ is
// holomorphic on the whole plane, so continuous, and off c it is not 0, so its
// inverse is continuous there, and so is the product with f.
var CoefficientIntegrandContinuous = coefficientIntegrandContinuousThm{family.Add(registry.ProofEntry{
	Name: "CoefficientIntegrandContinuous",
	Key:  "prop_9df2b36afd47a4f6",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c p:complex. ∀n:num.",
		Hypotheses: []string{
			"complex_continuous_at(f, p)",
			"p ≠ c",
		},
		Conclusion: "complex_continuous_at(λu:complex. f(u) / (u - c) ^ n, p)",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c, p *Expr[Complex],
			n *Expr[Nat],
			continuous, apart Fact,
		) {
			translate := arg.Have(
				"u − c has derivative 1 everywhere, so is holomorphic on the whole plane",
				"holomorphic_on(𝕌, λu:complex. u - c)",
				By(
					complex_derivative.HolomorphicOnDef,
					complex_derivative.DerivativeSub,
					complex_derivative.DerivativeId,
					complex_derivative.DerivativeConst))
			powerContinuous := arg.Have(
				"so is its n-th power, which therefore is continuous at p",
				"complex_continuous_at(λu:complex. (u - c) ^ n, p)",
				By(
					translate,
					complex_derivative.HolomorphicOnPow.At(
						arg.TermAs[Set[Complex]]("𝕌"),
						arg.TermAs[Fun[Complex, Complex]]("λu:complex. u - c"),
						n),
					set_basic.InUniv,
					complex_derivative.HolomorphicOnContinuousAt.At(
						arg.TermAs[Set[Complex]]("𝕌"),
						arg.TermAs[Fun[Complex, Complex]]("λu:complex. (u - c) ^ n"),
						p)))
			nonzero := arg.Have(
				"(p − c)ⁿ is not 0, p − c not being 0",
				"(p - c) ^ n ≠ &0",
				ByArith(apart, field.PowEqZero.Read(complex_field.Field).At(arg.TermAs[Complex]("p - c"), n)))
			arg.Show(
				"so f times the inverse of (u − c)ⁿ is continuous at p",
				Simp(Fwd(field.DivMulInv.Read(complex_field.Field))),
				By(
					continuous,
					powerContinuous,
					nonzero,
					complex_topology.ContinuousAtInv.At(
						arg.TermAs[Fun[Complex, Complex]]("λu:complex. (u - c) ^ n"), p),
					complex_topology.ContinuousAtMul.At(
						f,
						arg.TermAs[Fun[Complex, Complex]]("λu:complex. complex_inv((u - c) ^ n)"),
						p)))
		}),
})}

// TaylorRemainderBound — weighted by a function continuous and bounded by M
// on the circle, the remainder of the geometric series in
// q(u) = (z − c)/(u − c) cut after N terms has an integral round the circle
// that shrinks like (|z − c|/r)ᴺ: on the circle |q| = |z − c|/r and the
// distance to z is at least r − |z − c| > 0, so the weighted remainder has
// modulus at most M·(|z − c|/r)ᴺ/(r − |z − c|), and the ML estimate multiplies
// this by the circle's length 2πr.
var TaylorRemainderBound = taylorRemainderBoundThm{family.Add(registry.ProofEntry{
	Name: "TaylorRemainderBound",
	Key:  "prop_ec58e657d1babf80",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c z:complex. ∀r M:real. ∀N:num.",
		Hypotheses: []string{
			"∀u:complex. |u - c| = r ⇒ complex_continuous_at(f, u) ∧ |f(u)| ≤ M",
			"|z - c| < r",
		},
		Conclusion: "|«circleInt»(λu:complex. f(u) * («q»(u) ^ N / (u - z)), c, r)| ≤ " +
			"&2 * pi * r * M * real_pow(|z - c| / r, N) / (r - |z - c|)",
		Abbrev: Abbrev{
			{Name: "q", Text: "λu:complex. (z - c) / (u - c)"},
		},
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c, z *Expr[Complex],
			r, M *Expr[Real],
			N *Expr[Nat],
			onCircle, inside Fact,
		) {
			sizes := arg.Have(
				"the radius r and the gap r − |z − c| are positive, the "+
					"ratio |z − c|/r is not negative, and z is not on the circle",
				"&0 < r ∧ &0 < r - |z - c| ∧ &0 ≤ |z - c| / r ∧ |z - c| ≠ r",
				ByArith(inside, complex_abs.AbsNonneg.At(arg.TermAs[Complex]("z - c"))))
			estimate := arg.Have(
				"at each point of the circle the weighted remainder is "+
					"continuous, of modulus at most M·(|z − c|/r)ᴺ/(r − |z − c|)",
				Statement{
					Binders: "∀u:complex.",
					Hypotheses: []string{
						"|u - c| = r",
					},
					Conclusion: "complex_continuous_at(λv:complex. f(v) * («q»(v) ^ N / (v - z)), u) ∧ " +
						"|f(u) * («q»(u) ^ N / (u - z))| ≤ M * real_pow(|z - c| / r, N) / (r - |z - c|)",
				},
				Derive(func(d *Argument) {
					u := d.FixAs[Complex]("u")
					on := d.Assume()
					remainder := d.TermAs[Complex]("«q»(u) ^ N / (u - z)")
					gap := d.TermAs[Real]("r - |z - c|")
					distance := d.TermAs[Real]("|u - z|")
					offC := d.Have(
						"u is not c, lying at distance r > 0 from it",
						"u ≠ c",
						ByArith(on, sizes, complex_abs.AbsPosIffNonzero.At(d.TermAs[Complex]("u - c"))))
					apart := d.Have(
						"nor z, which is not on the circle",
						"u ≠ c ∧ u ≠ z",
						By(Normalized, on, sizes, offC))
					far := d.Have(
						"so by the triangle inequality u lies at distance at least r − |z − c| from z",
						"r - |z - c| ≤ |u - z|",
						ByArith(on, complex_abs.AbsSubTriangle.At(u, z, c)))
					modulus := d.Have(
						"the remainder at u has modulus (|z − c|/r)ᴺ over |u − z|",
						"|«q»(u) ^ N / (u - z)| = real_pow(|z - c| / r, N) / |u - z|",
						ByArith(
							on,
							complex_abs.AbsDiv.At(d.TermAs[Complex]("«q»(u) ^ N"), d.TermAs[Complex]("u - z")),
							complex_abs.AbsPow.At(d.TermAs[Complex]("«q»(u)"), N),
							complex_abs.AbsDiv.At(d.TermAs[Complex]("z - c"), d.TermAs[Complex]("u - c"))))
					shrink := d.Have(
						"(|z − c|/r)ᴺ is not negative, and 1/|u − z| is at most 1/(r − |z − c|)",
						"&0 ≤ real_pow(|z - c| / r, N) ∧ real_inv(|u - z|) ≤ real_inv(r - |z - c|)",
						By(
							sizes,
							far,
							real_order_field.InvAntitoneWeak.At(gap, distance),
							real_pow.PowNonneg.At(d.TermAs[Real]("|z - c| / r"), N)))
					bound := d.Have(
						"so the remainder has modulus at most (|z − c|/r)ᴺ/(r − |z − c|)",
						"|«q»(u) ^ N / (u - z)| ≤ real_pow(|z - c| / r, N) / (r - |z - c|)",
						ByArith(modulus, shrink))
					continuous := d.Have(
						"f is continuous at u, and so is the remainder qᴺ/(v − z) off c and z",
						"complex_continuous_at(λv:complex. f(v) * («q»(v) ^ N / (v - z)), u)",
						By(
							onCircle.At(u),
							on,
							apart,
							CutSeriesContinuous.At(c, z, z, u, N),
							complex_topology.ContinuousAtMul.At(
								f,
								d.TermAs[Fun[Complex, Complex]]("λv:complex. «q»(v) ^ N / (v - z)"),
								u)))
					value := f.Apply(u)
					d.Show(
						"and f(u), at most M in modulus, multiplies that bound by at most M",
						ByArith(
							continuous,
							onCircle.At(u),
							on,
							bound,
							complex_abs.AbsMul.At(value, remainder),
							complex_abs.AbsNonneg.At(value),
							complex_abs.AbsNonneg.At(remainder),
							real_order_ring.LessEqMul2.At(
								d.TermAs[Real]("|f(u)|"),
								M,
								d.TermAs[Real]("|«q»(u) ^ N / (u - z)|"),
								d.TermAs[Real]("real_pow(|z - c| / r, N) / (r - |z - c|)"))))
				}))
			arg.Show(
				"so by the ML estimate the integral is at most that bound times the circle's length 2πr",
				ByArith(
					sizes,
					estimate,
					path_integral.CircleIntegralBound.At(
						arg.TermAs[Fun[Complex, Complex]]("λu:complex. f(u) * («q»(u) ^ N / (u - z))"),
						c,
						r,
						arg.TermAs[Real]("M * real_pow(|z - c| / r, N) / (r - |z - c|)"))))
		}),
})}

// TaylorRemainder — Taylor's formula with Cauchy's remainder: inside a circle
// lying in a disc where f is holomorphic, f(z) is the partial sum up to N of
// its power series about the centre, each coefficient the integral of f
// against a power of 1/(u − c) round the circle divided by 2πi, plus the
// integral of f times the remainder of the geometric series in
// q(u) = (z − c)/(u − c) cut after N + 1 terms, divided by 2πi. Off c and z the
// cut identity, weighted by f(u), splits each remainder into the next term and
// the next remainder, and every piece is continuous on the circle, so round it
// the remainder after k terms integrates to (z − c)ᵏ times the k-th coefficient
// integral plus the integral of the remainder after k + 1. The remainder after
// no terms integrates to 2πi·f(z) by the integral formula, and induction on N
// cuts off one term at a time.
var TaylorRemainder = taylorRemainderThm{family.Add(registry.ProofEntry{
	Name: "TaylorRemainder",
	Key:  "prop_bacc4bc5944625d9",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c z:complex. ∀R r:real. ∀N:num.",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R), f)",
			"r < R",
			"|z - c| < r",
		},
		Conclusion: "f(z) = " +
			"Σ_{k∈0 .. N} «coef»(f, c, r, k) * (z - c) ^ k + " +
			"«circleInt»(λu:complex. f(u) * («q»(u) ^ (N + 1) / (u - z)), c, r) / (&(&2 * pi) * complex_i)",
		Abbrev: Abbrev{
			{Name: "q", Text: "λu:complex. (z - c) / (u - c)"},
		},
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c, z *Expr[Complex],
			R, r *Expr[Real],
			holomorphic, smaller, inside Fact,
		) {
			disc := arg.TermAs[Set[Complex]]("«disc»(c, R)")
			inverseTurn := arg.TermAs[Complex]("complex_inv(&(&2 * pi) * complex_i)")
			positive := arg.Have(
				"the radius r exceeds |z − c| ≥ 0, so is positive, and z is not on the circle",
				"&0 < r ∧ |z - c| ≠ r",
				ByArith(inside, complex_abs.AbsNonneg.At(arg.TermAs[Complex]("z - c"))))
			points := arg.Have(
				"a point of the circle lies in the disc and is neither c nor z",
				"∀u:complex. |u - c| = r ⇒ u ∈ «disc»(c, R) ∧ u ≠ c ∧ u ≠ z",
				Derive(func(d *Argument) {
					d.FixAs[Complex]("u")
					on := d.Assume()
					near := d.Have(
						"u lies in the disc, r being less than R, and is not c, r being positive",
						"u ∈ «disc»(c, R) ∧ u ≠ c",
						ByArith(on, smaller, positive, complex_abs.AbsPosIffNonzero.At(d.TermAs[Complex]("u - c"))))
					d.Show(
						"nor is it z, which is not on the circle",
						By(Normalized, on, positive, near))
				}))
			coefficients := arg.Have(
				"so on the circle every coefficient integrand f(u)/(u − c)ᵏ⁺¹ is continuous",
				"∀k:num. ∀u:complex. |u - c| = r ⇒ complex_continuous_at(λv:complex. f(v) / (v - c) ^ (k + 1), u)",
				Derive(func(d *Argument) {
					d.FixAs[Nat]("k")
					u := d.FixAs[Complex]("u")
					on := d.Assume()
					d.Show(
						"f, holomorphic on the disc, is continuous at u, which is not c",
						By(
							on,
							points.At(u),
							holomorphic,
							complex_derivative.HolomorphicOnContinuousAt.At(disc, f, u),
							CoefficientIntegrandContinuous.At(f, c, u, d.TermAs[Nat]("k + 1"))))
				}))
			terms := arg.Have(
				"and so is its multiple by (z − c)ᵏ",
				Statement{
					Binders: "∀k:num. ∀u:complex.",
					Hypotheses: []string{
						"|u - c| = r",
					},
					Conclusion: "complex_continuous_at(λv:complex. (z - c) ^ k * (f(v) / (v - c) ^ (k + 1)), u)",
				},
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]("k")
					u := d.FixAs[Complex]("u")
					on := d.Assume()
					d.Show(
						"a constant times a continuous function is continuous",
						By(
							on,
							coefficients.At(k, u),
							complex_topology.ContinuousAtConst.At(u, d.TermAs[Complex]("(z - c) ^ k")),
							complex_topology.ContinuousAtMul.At(
								d.TermAs[Fun[Complex, Complex]]("λv:complex. (z - c) ^ k"),
								d.TermAs[Fun[Complex, Complex]]("λv:complex. f(v) / (v - c) ^ (k + 1)"),
								u)))
				}))
			remainders := arg.Have(
				"as is every weighted remainder f(u)·qᵏ/(u − z)",
				Statement{
					Binders: "∀k:num. ∀u:complex.",
					Hypotheses: []string{
						"|u - c| = r",
					},
					Conclusion: "complex_continuous_at(λv:complex. f(v) * («q»(v) ^ k / (v - z)), u)",
				},
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]("k")
					u := d.FixAs[Complex]("u")
					on := d.Assume()
					d.Show(
						"f is continuous at u, and so is qᵏ/(v − z) off c and z",
						By(
							on,
							points.At(u),
							holomorphic,
							complex_derivative.HolomorphicOnContinuousAt.At(disc, f, u),
							CutSeriesContinuous.At(c, z, z, u, k),
							complex_topology.ContinuousAtMul.At(
								f,
								d.TermAs[Fun[Complex, Complex]]("λv:complex. «q»(v) ^ k / (v - z)"),
								u)))
				}))
			cut := arg.Have(
				"off c and z one more term is cut off: weighted by f(u), "+
					"qᵏ/(u − z) is (z − c)ᵏ/(u − c)ᵏ⁺¹ plus qᵏ⁺¹/(u − z)",
				Statement{
					Binders: "∀k:num. ∀u:complex.",
					Hypotheses: []string{
						"u ≠ c",
						"u ≠ z",
					},
					Conclusion: "f(u) * («q»(u) ^ k / (u - z)) = " +
						"(z - c) ^ k * (f(u) / (u - c) ^ (k + 1)) + f(u) * («q»(u) ^ (k + 1) / (u - z))",
				},
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]("k")
					d.FixAs[Complex]("u")
					off := d.Assume()
					away := d.Have(
						"u − c and u − z are not 0",
						"u - c ≠ &0 ∧ u - z ≠ &0",
						ByArith(off))
					step := d.TermAs[Complex]("u - c")
					inverse := d.TermAs[Complex]("complex_inv(u - c)")
					inversePower := d.Have(
						"the inverse of (u − c)ᵏ is the k-th power of the inverse of u − c",
						"complex_inv((u - c) ^ k) = complex_inv(u - c) ^ k",
						By(
							away,
							field.MulRightInverse.Read(complex_field.Field).At(step),
							comm_monoid.PowInverse.Read(complex_field.MulMonoid).At(step, inverse, k),
							field.InvRightUnique.Read(complex_field.Field).At(
								d.TermAs[Complex]("(u - c) ^ k"),
								d.TermAs[Complex]("complex_inv(u - c) ^ k"))))
					d.Show(
						"with q = (z − c)·1/(u − c), the two sides differ by "+
							"multiples of (u − c)·1/(u − c) − 1 and (u − z)·1/(u − z) − 1",
						Simp(
							Fwd(comm_monoid.PowAdd.Read(complex_field.MulMonoid)),
							Fwd(comm_monoid.PowOne.Read(complex_field.MulMonoid)),
							Fwd(comm_monoid.MulPow.Read(complex_field.MulMonoid)),
							Fwd(field.DivMulInv.Read(complex_field.Field)),
							Fwd(field.InvMul.Read(complex_field.Field))),
						inversePower.Rw(),
						ByArith(away))
				}))
			shift := arg.Have(
				"so round the circle the remainder after k terms is (z − c)ᵏ "+
					"times the k-th coefficient integral plus the remainder after k + 1",
				"∀k:num. "+
					"    «circleInt»(λu:complex. f(u) * («q»(u) ^ k / (u - z)), c, r) = "+
					"    (z - c) ^ k * «circleInt»(λu:complex. f(u) / (u - c) ^ (k + 1), c, r) + "+
					"    «circleInt»(λu:complex. f(u) * («q»(u) ^ (k + 1) / (u - z)), c, r)",
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]("k")
					agree := d.Have(
						"on the circle, which misses c and z, the weighted "+
							"remainder is the term plus the next weighted remainder",
						Statement{
							Binders: "∀u:complex.",
							Hypotheses: []string{
								"|u - c| = r",
							},
							Conclusion: "f(u) * («q»(u) ^ k / (u - z)) = " +
								"(z - c) ^ k * (f(u) / (u - c) ^ (k + 1)) + f(u) * («q»(u) ^ (k + 1) / (u - z))",
						},
						By(points, cut))
					term := d.TermAs[Fun[Complex, Complex]]("λu:complex. (z - c) ^ k * (f(u) / (u - c) ^ (k + 1))")
					next := d.TermAs[Fun[Complex, Complex]]("λu:complex. f(u) * («q»(u) ^ (k + 1) / (u - z))")
					d.Show(
						"and the integral round the circle sees the integrand "+
							"only there and is linear in functions continuous there",
						ByArith(
							positive,
							agree,
							terms.At(k),
							remainders.At(d.TermAs[Nat]("k + 1")),
							coefficients.At(k),
							path_integral.CircleIntegralCongruence.At(
								d.TermAs[Fun[Complex, Complex]]("λu:complex. f(u) * («q»(u) ^ k / (u - z))"),
								d.TermAs[Fun[Complex, Complex]](
									"λu:complex. (z - c) ^ k * (f(u) / (u - c) ^ (k + 1)) + f(u) * («q»(u) ^ (k + 1) / (u - z))"),
								c,
								r),
							path_integral.CircleIntegralAdd.At(term, next, c, r),
							path_integral.CircleIntegralScale.At(
								d.TermAs[Fun[Complex, Complex]]("λu:complex. f(u) / (u - c) ^ (k + 1)"),
								c,
								r,
								d.TermAs[Complex]("(z - c) ^ k"))))
				}))
			formula := arg.Have(
				"by the integral formula, f(u)/(u − z) integrates to 2πi·f(z)",
				"«circleInt»(λu:complex. f(u) / (u - z), c, r) = &(&2 * pi) * complex_i * f(z)",
				By(holomorphic, smaller, inside, CauchyIntegralFormula.At(f, c, z, R, r)))
			start := arg.Have(
				"and the remainder after no terms, f(u)·q⁰/(u − z), is that integrand",
				"«circleInt»(λu:complex. f(u) / (u - z), c, r) = "+
					"«circleInt»(λu:complex. f(u) * («q»(u) ^ 0 / (u - z)), c, r)",
				Simp(
					Fwd(comm_monoid.MonoidPowDef.Inst[Complex]()),
					Fwd(field.DivMulInv.Read(complex_field.Field)),
					Fwd(comm_monoid.LeftIdentity.Read(complex_field.MulMonoid))),
				Refl())
			summand := arg.TermAs[Fun[Nat, Complex]]("λk:num. «coef»(f, c, r, k) * (z - c) ^ k")
			add := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
			arg.Induct("N")
			arg.Base(
				"the sum up to 0 is its first term, and 2πi·f(z), the remainder "+
					"after no terms, is that term's integral plus the remainder after it",
				ByArith(
					path_integral.TwoPiINonzero,
					Scaled(inverseTurn, shift.At(arg.TermAs[Nat]("0"))),
					Scaled(inverseTurn, formula),
					Scaled(inverseTurn, start),
					monoidal.IntervalPoint.Read(add).At(arg.TermAs[Nat]("0"), summand)))
			arg.Step(
				"each further term peeled off the sum is cut off from the remainder",
				func(b *Argument, ih Fact) {
					index := b.Have(
						"suc(N) is N + 1",
						"suc(N) = N + 1",
						ByArith())
					next := b.TermAs[Nat]("N + 1")
					peel := b.Have(
						"the sum up to N + 1 is the sum up to N plus its last term",
						"Σ_{k∈0 .. N + 1} «coef»(f, c, r, k) * (z - c) ^ k = "+
							"Σ_{k∈0 .. N} «coef»(f, c, r, k) * (z - c) ^ k + «coef»(f, c, r, N + 1) * (z - c) ^ (N + 1)",
						By(
							b.Have(
								"N + 1 is positive, and the sum starts at 0 ≤ N + 1",
								"0 < N + 1 ∧ 0 ≤ N + 1",
								ByArith()),
							monoidal.PeelRight.Read(add).At(next, b.TermAs[Nat]("0"), summand),
							nat_monus.AddSubCancel.At(b.TermAs[Nat]("N"), b.TermAs[Nat]("1"))))
					b.Show(
						"the remainder after N + 1 terms is the (N + 1)-th term plus the remainder after N + 2",
						index.Rw(),
						ByArith(ih, peel, Scaled(inverseTurn, shift.At(next))))
				})
		}),
})}

// PowerSeriesExpansionCircle — a function holomorphic on a disc about c is, at
// each point inside a smaller circle about c, the sum of its power series about
// c, whose n-th coefficient is the integral of f against the (n + 1)-th power
// of 1/(u − c) round that circle divided by 2πi. f is continuous on the
// compact circle, so bounded there by some M. By Taylor's formula, 2πi times
// the partial sum up to n less f(z) is minus the integral of the remainder
// after n + 1 terms, at most 2πrM·(|z − c|/r)ⁿ⁺¹/(r − |z − c|) in modulus;
// these bounds tend to 0, so the partial sums tend to f(z).
var PowerSeriesExpansionCircle = powerSeriesExpansionCircleThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesExpansionCircle",
	Key:  "prop_cf258d335154d2d0",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c z:complex. ∀R r:real.",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R), f)",
			"r < R",
			"|z - c| < r",
		},
		Conclusion: "complex_sums(λn:num. «coef»(f, c, r, n) * (z - c) ^ n, f(z))",
		Abbrev: Abbrev{
			{Name: "q", Text: "λu:complex. (z - c) / (u - c)"},
		},
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c, z *Expr[Complex],
			R, r *Expr[Real],
			holomorphic, smaller, inside Fact,
		) {
			disc := arg.TermAs[Set[Complex]]("«disc»(c, R)")
			continuous := arg.Have(
				"f is continuous at each point of the circle, which lies in the disc where f is holomorphic",
				"∀u:complex. |u - c| = r ⇒ complex_continuous_at(f, u)",
				Derive(func(d *Argument) {
					u := d.FixAs[Complex]("u")
					on := d.Assume()
					within := d.Have(
						"u lies in the disc, r being less than R",
						"u ∈ «disc»(c, R)",
						ByArith(on, smaller))
					d.Show(
						"where f is holomorphic, so continuous",
						By(holomorphic, within, complex_derivative.HolomorphicOnContinuousAt.At(disc, f, u)))
				}))
			circleSet := arg.TermAs[Set[Complex]]("{u:complex | |u - c| = r}")
			M, bounded := arg.ObtainAs[Real](
				"f is continuous on the compact circle, so bounded there by some M",
				"∃M:real. ∀u:complex. |u - c| = r ⇒ |f(u)| ≤ M",
				By(
					continuous,
					complex_topology.CircleCompact.At(c, r),
					complex_topology.ContinuousAtOn.At(circleSet, f),
					complex_topology.ContinuousOnCompactBounded.At(circleSet, f)))
			turn := arg.TermAs[Complex]("&(&2 * pi) * complex_i")
			modulus := arg.Have(
				"2πi has modulus 2π·|i| = 2π",
				"|&(&2 * pi) * complex_i| = &2 * pi",
				ByArith(
					real_trigonometry.PiBounds,
					complex_abs.AbsMul.At(arg.TermAs[Complex]("&(&2 * pi)"), arg.TermAs[Complex]("complex_i")),
					complex_abs.AbsOfReal.At(arg.TermAs[Real]("&2 * pi")),
					complex_abs.AbsI))
			estimate := arg.Have(
				"for every n, 2π times the distance of the partial sum up "+
					"to n from f(z) is at most 2πrM·(|z − c|/r)ⁿ⁺¹/(r − |z − c|)",
				"∀n:num. "+
					"    |Σ_{k∈0 .. n} «coef»(f, c, r, k) * (z - c) ^ k - f(z)| * (&2 * pi) ≤ "+
					"    &2 * pi * r * M * real_pow(|z - c| / r, n + 1) / (r - |z - c|)",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]("n")
					remainder := d.TermAs[Complex]("«circleInt»(λu:complex. f(u) * («q»(u) ^ (n + 1) / (u - z)), c, r)")
					next := d.TermAs[Nat]("n + 1")
					difference := d.Have(
						"by Taylor's formula, 2πi times the partial sum less f(z) is minus the remainder after n + 1 terms",
						"(Σ_{k∈0 .. n} «coef»(f, c, r, k) * (z - c) ^ k - f(z)) * (&(&2 * pi) * complex_i) = "+
							"-«circleInt»(λu:complex. f(u) * («q»(u) ^ (n + 1) / (u - z)), c, r)",
						ByArith(
							holomorphic,
							smaller,
							inside,
							path_integral.TwoPiINonzero,
							Scaled(turn, TaylorRemainder.At(f, c, z, R, r, n))))
					d.Show(
						"and the remainder's integral is at most 2πrM·(|z − c|/r)ⁿ⁺¹/(r − |z − c|) in modulus",
						ByArith(
							continuous,
							bounded,
							inside,
							modulus,
							difference,
							TaylorRemainderBound.At(f, c, z, r, M, next),
							complex_abs.AbsMul.At(
								d.TermAs[Complex]("Σ_{k∈0 .. n} «coef»(f, c, r, k) * (z - c) ^ k - f(z)"), turn),
							complex_abs.AbsNeg.At(remainder)))
				}))
			ratio := arg.TermAs[Real]("|z - c| / r")
			scale := arg.TermAs[Real]("&2 * pi * r * M / (r - |z - c|)")
			zero := arg.TermAs[Real]("&0")
			fraction := arg.Have(
				"the ratio |z − c|/r lies in [0, 1), r exceeding |z − c| ≥ 0",
				"&0 ≤ |z - c| / r ∧ |z - c| / r < &1",
				ByArith(inside, complex_abs.AbsNonneg.At(arg.TermAs[Complex]("z - c"))))
			powers := arg.Have(
				"so its powers tend to 0",
				"real_converges_to(λn:num. real_pow(|z - c| / r, n), &0)",
				ByArith(fraction, real_sequences.PowerTendsToZero.At(ratio)))
			bounds := arg.Have(
				"so do the bounds 2πrM/(r − |z − c|)·(|z − c|/r)ⁿ⁺¹",
				"real_converges_to(λn:num. &2 * pi * r * M / (r - |z - c|) * real_pow(|z - c| / r, n + 1), "+
					"    &2 * pi * r * M / (r - |z - c|) * &0)",
				By(
					powers,
					real_sequences.LimitShift.At(arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(|z - c| / r, n)"), zero),
					real_sequences.LimitScale.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(|z - c| / r, n + 1)"), zero, scale)))
			near := arg.Unfolded(bounds, real_sequences.RealConvergesToDef)
			partial := arg.Have(
				"so the partial sums tend to f(z)",
				"(λn:num. Σ_{k∈0 .. n} «coef»(f, c, r, k) * (z - c) ^ k) ⟶ f(z)",
				Derive(func(d *Argument) {
					d.Do(Unfold(complex_topology.ComplexConvergesToDef))
					d.FixAs[Real]("ε")
					pos := d.Assume()
					tolerance := d.TermAs[Real]("&2 * pi * ε")
					scaled := d.Have(
						"2πε is positive",
						"&0 < &2 * pi * ε",
						ByArith(pos, real_trigonometry.PiBounds))
					N, tail := d.ObtainAs[Nat](
						"past some index N the bounds are below 2πε",
						"∃N:num. ∀n:num. "+
							"    N ≤ n ⇒ "+
							"    |&2 * pi * r * M / (r - |z - c|) * real_pow(|z - c| / r, n + 1) - "+
							"    &2 * pi * r * M / (r - |z - c|) * &0| < "+
							"    &2 * pi * ε",
						By(near.At(tolerance), scaled))
					d.Take(N)
					n := d.FixAs[Nat]("n")
					past := d.Assume()
					below := d.Have(
						"2π times the distance of the partial sum from f(z) is below 2πε",
						"|Σ_{k∈0 .. n} «coef»(f, c, r, k) * (z - c) ^ k - f(z)| * (&2 * pi) < &2 * pi * ε",
						ByArith(estimate.At(n), tail.At(n), past))
					d.Show(
						"so the distance itself is below ε",
						ByArith(below, real_trigonometry.PiBounds))
				}))
			arg.Show(
				"a series sums to the limit of its partial sums",
				By(
					partial,
					complex_series.SumsIffPartialSums.At(
						arg.TermAs[Fun[Nat, Complex]]("λn:num. «coef»(f, c, r, n) * (z - c) ^ n"), f.Apply(z))))
		}),
})}

// PowerSeriesExpansion — a function holomorphic on a disc is the sum of one
// power series about the centre on the whole disc. The coefficients read off
// a circle do not depend on its radius: the series of two circles both sum to
// f inside the smaller one, so they have the same coefficients. Take those of
// the circle of radius R/2; a point z of the disc lies inside the circle of
// radius (|z − c| + R)/2 < R, whose series sums to f(z) and has the same
// coefficients.
var PowerSeriesExpansion = powerSeriesExpansionThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesExpansion",
	Key:  "prop_e0c041ca8f243e7d",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀R:real.",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R), f)",
		},
		Conclusion: "∃a:num → complex. ∀z:complex. " +
			"    |z - c| < R ⇒ complex_sums(λn:num. a(n) * (z - c) ^ n, f(z))",
	},
		func(arg *Argument, f *Arrow[Complex, Complex], c *Expr[Complex], R *Expr[Real], holomorphic Fact) {
			half := arg.TermAs[Real]("R / &2")
			atHalfCircle := arg.TermAs[Fun[Nat, Complex]]("λk:num. «coef»(f, c, R / &2, k)")
			arg.Take(atHalfCircle)
			z := arg.FixAs[Complex]("z")
			inside := arg.Assume()
			r, rDef := arg.LetAs[Real]("r", "(|z - c| + R) / &2")
			radii := arg.Have(
				"r, halfway between |z − c| and R, puts z inside the circle of radius "+
					"r and that circle inside the disc; and R/2 is positive and at most r",
				"|z - c| < r ∧ r < R ∧ R / &2 ≤ r ∧ &0 < R / &2",
				ByArith(rDef, inside, complex_abs.AbsNonneg.At(arg.TermAs[Complex]("z - c"))))
			small := arg.Have(
				"inside the circle of radius R/2, f is the sum of the series with that circle's coefficients",
				"∀w:complex. |w - c| < R / &2 ⇒ complex_sums(λn:num. «coef»(f, c, R / &2, n) * (w - c) ^ n, f(w))",
				arg.ForEach(func(w *Expr[Complex]) Action {
					return ByArith(holomorphic, radii, PowerSeriesExpansionCircle.At(f, c, w, R, half))
				}))
			large := arg.Have(
				"and so is the series with the coefficients of the circle of radius r, which encloses that circle",
				"∀w:complex. |w - c| < R / &2 ⇒ complex_sums(λn:num. «coef»(f, c, r, n) * (w - c) ^ n, f(w))",
				arg.ForEach(func(w *Expr[Complex]) Action {
					return ByArith(holomorphic, radii, PowerSeriesExpansionCircle.At(f, c, w, R, r))
				}))
			agree := arg.Have(
				"so the two circles have the same coefficients",
				"(λk:num. «coef»(f, c, R / &2, k)) = (λk:num. «coef»(f, c, r, k))",
				By(
					small,
					large,
					radii,
					complex_power_series.CoefficientsUnique.At(
						atHalfCircle, arg.TermAs[Fun[Nat, Complex]]("λk:num. «coef»(f, c, r, k)"), f, c, half)))
			arg.Show(
				"and z lies inside the circle of radius r, where the series sums to f(z)",
				By(agree, holomorphic, radii, PowerSeriesExpansionCircle.At(f, c, z, R, r)))
		}),
})}
