// holder.go — Young's inequality for conjugate exponents, read from the
// convexity of exp; Hölder's inequality for finite sums, read from
// Young's term by term, with the fact it needs about a vanishing sum of
// powers; and Minkowski's inequality, read from Hölder's.

package real_convex

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// Young — Young's inequality: for conjugate exponents p, q > 1, with
// 1/p + 1/q = 1, the product of two nonnegative reals a and b is at most
// a^p/p + b^q/q. When a·b ≤ 0 the right side, a sum of two nonnegative
// terms, bounds it. Otherwise a and b are positive and exp is convex: at
// the weights 1/p and 1/q between p·log a and q·log b its value at the
// combination log a + log b = log(a·b) is at most the combination
// (1/p)·exp(p·log a) + (1/q)·exp(q·log b) of its values, which is
// a^p/p + b^q/q.
var Young = youngThm{family.Add(registry.ProofEntry{
	Name: "Young",
	Key:  "prop_9a777e56d4ee2891",
	Build: family.Theorem(Statement{
		Binders: "∀a b p q:real.",
		Hypotheses: []string{
			"&0 ≤ a",
			"&0 ≤ b",
			"&1 < p",
			"&1 < q",
			"real_inv(p) + real_inv(q) = &1",
		},
		Conclusion: "a * b ≤ real_rpow(a, p) / p + real_rpow(b, q) / q",
	}, func(arg *Argument, a, b, p, q *Expr[Real], aNonneg, bNonneg, pAbove, qAbove, conjugate Fact) {
		positiveProduct := arg.Assuming(
			arg.Term("&0 < a * b"),
			"if a·b ≤ 0, the right side, a sum of two nonnegative terms, bounds it",
			Given(func(c *Argument, notPositive Fact) {
				terms := c.Have(
					"a^p/p and b^q/q are nonnegative",
					"&0 ≤ real_rpow(a, p) / p ∧ &0 ≤ real_rpow(b, q) / q",
					ByArith(pAbove, qAbove, real_rpow.RpowNonneg.At(a, p), real_rpow.RpowNonneg.At(b, q)),
				)
				c.Show(
					"a·b ≤ 0 ≤ a^p/p + b^q/q",
					ByArith(notPositive, terms))
			}))
		positive := arg.Have(
			"a and b are positive",
			"&0 < a ∧ &0 < b",
			ByArith(aNonneg, bNonneg, positiveProduct))
		weights := arg.Have(
			"1/p is a weight between 0 and 1, being at most 1/1, and 1/q is the complementary weight",
			"&0 ≤ real_inv(p) ∧ real_inv(p) ≤ &1 ∧ &1 - real_inv(p) = real_inv(q)",
			ByArith(conjugate, pAbove, real_order_field.InvAntitoneWeak.At(arg.TermAs[Real]("&1"), p)),
		)
		convex := arg.Unfolded(ExpConvex, RealConvexOnDef)
		chord := arg.Have(
			"exp is convex: at the weights 1/p and 1/q between p·log a and q·log b",
			"exp(real_inv(p) * (p * log(a)) + real_inv(q) * (q * log(b))) ≤ "+
				"real_inv(p) * exp(p * log(a)) + real_inv(q) * exp(q * log(b))",
			By(
				convex.At(
					arg.TermAs[Real]("p * log(a)"), arg.TermAs[Real]("q * log(b)"), arg.TermAs[Real]("real_inv(p)")),
				weights,
				set_basic.InUniv),
		)
		exponent := arg.Have(
			"the combination of the exponents is log a + log b = log(a·b)",
			"real_inv(p) * (p * log(a)) + real_inv(q) * (q * log(b)) = log(a * b)",
			ByArith(pAbove, qAbove, positive, real_exp_log.LogMul.At(a, b)),
		)
		arg.Show(
			"so a·b = exp(log(a·b)) is at most (1/p)·exp(p·log a) + (1/q)·exp(q·log b) = a^p/p + b^q/q",
			ByArith(
				exponent,
				chord,
				positiveProduct,
				positive,
				real_exp_log.ExpLog.At(arg.TermAs[Real]("a * b")),
				real_rpow.RpowExp.At(a, p),
				real_rpow.RpowExp.At(b, q)),
		)
	}),
})}

// PowerSumZero — a finite sum of powers |a(i)|^p vanishes only where each
// a(i) does: the powers are nonnegative, so each of them is 0, and a power
// of a positive real is positive, so each |a(j)| is 0.
var PowerSumZero = powerSumZeroThm{family.Add(registry.ProofEntry{
	Name: "PowerSumZero",
	Key:  "prop_4a6bfe36402c0b37",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(A). ∀a:A → real. ∀p:real. ∀j:A.",
		Hypotheses: []string{
			"finite(k)",
			"Σ_{i∈k} real_rpow(|a(i)|, p) = &0",
			"j ∈ k",
		},
		Conclusion: "a(j) = &0",
	}, func(
		arg *Argument,
		k *Expr[Set[A]],
		a *Arrow[A, Real],
		p *Expr[Real],
		j *Expr[A],
		finiteK, zero, jIn Fact,
	) {
		term := arg.Have(
			"the terms of a vanishing sum of nonnegative terms vanish, |a(j)|^p among them",
			"real_rpow(|a(j)|, p) = &0",
			By(
				real_sum.NonnegEqZero.At(k, arg.TermAs[Fun[A, Real]]("λi:A. real_rpow(|a(i)|, p)"), j),
				real_rpow.RpowNonneg,
				finiteK,
				zero,
				jIn),
		)
		arg.Show(
			"a power of a positive |a(j)| would be positive",
			ByArith(term, real_rpow.RpowPositive.At(arg.TermAs[Real]("|a(j)|"), p)))
	}),
})}

// Holder — Hölder's inequality: for conjugate exponents p, q > 1 the sum
// of |a(i)·b(i)| over a finite index set is at most μ·ν, where μ and ν
// are the p-th root of α = Σ |a(i)|^p and the q-th root of β = Σ |b(i)|^q.
// If α = 0 every a(i) is 0 and the left side vanishes, and likewise if
// β = 0. Otherwise μ and ν are positive, μ^p = α and ν^q = β, and Young's
// inequality at |a(i)|/μ and |b(i)|/ν bounds |a(i)·b(i)|/(μ·ν) by
// (1/μ)^p·|a(i)|^p/p + (1/ν)^q·|b(i)|^q/q; summed over k the right side
// is 1/p + 1/q = 1.
var Holder = holderThm{family.Add(registry.ProofEntry{
	Name: "Holder",
	Key:  "prop_d464920b67a65dd3",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(A). ∀a b:A → real. ∀p q:real.",
		Hypotheses: []string{
			"finite(k)",
			"&1 < p",
			"&1 < q",
			"real_inv(p) + real_inv(q) = &1",
		},
		Conclusion: "Σ_{i∈k} |a(i) * b(i)| ≤ " +
			"real_rpow(Σ_{i∈k} real_rpow(|a(i)|, p), real_inv(p)) * " +
			"real_rpow(Σ_{i∈k} real_rpow(|b(i)|, q), real_inv(q))",
	}, func(
		arg *Argument,
		k *Expr[Set[A]],
		a, b *Arrow[A, Real],
		p, q *Expr[Real],
		finiteK, pAbove, qAbove, conjugate Fact,
	) {
		powerA := arg.TermAs[Fun[A, Real]]("λi:A. real_rpow(|a(i)|, p)")
		powerB := arg.TermAs[Fun[A, Real]]("λi:A. real_rpow(|b(i)|, q)")
		sumsNonneg := arg.Have(
			"sums of nonnegative powers are nonnegative",
			"&0 ≤ Σ_{i∈k} real_rpow(|a(i)|, p) ∧ &0 ≤ Σ_{i∈k} real_rpow(|b(i)|, q)",
			By(real_sum.Nonneg.At(k, powerA), real_sum.Nonneg.At(k, powerB), real_rpow.RpowNonneg),
		)
		α, αDef := arg.LetAs[Real]("α", "Σ_{i∈k} real_rpow(|a(i)|, p)")
		β, βDef := arg.LetAs[Real]("β", "Σ_{i∈k} real_rpow(|b(i)|, q)")
		μ, μDef := arg.LetAs[Real]("μ", "real_rpow(α, real_inv(p))")
		ν, νDef := arg.LetAs[Real]("ν", "real_rpow(β, real_inv(q))")
		inverseP := arg.TermAs[Real]("real_inv(p)")
		inverseQ := arg.TermAs[Real]("real_inv(q)")
		rootsNonneg := arg.Have(
			"μ and ν, powers of nonnegative reals, are nonnegative",
			"&0 ≤ μ ∧ &0 ≤ ν",
			ByArith(μDef, νDef, real_rpow.RpowNonneg.At(α, inverseP), real_rpow.RpowNonneg.At(β, inverseQ)),
		)
		positiveAlpha := arg.Assuming(
			arg.Term("&0 < α"),
			"if α = 0, every a(i) is 0 and the left side vanishes",
			Given(func(c *Argument, notPositive Fact) {
				zero := c.Have(
					"the powers |a(i)|^p sum to 0",
					"Σ_{i∈k} real_rpow(|a(i)|, p) = &0",
					ByArith(notPositive, sumsNonneg, αDef))
				vanish := c.Have(
					"so every a(i) is 0, and with it every term |a(i)·b(i)|",
					"∀i:A. i ∈ k ⇒ |a(i) * b(i)| = &0",
					c.ForEach(func(i *Expr[A]) Action {
						return ByArith(PowerSumZero.At(k, a, p, i), finiteK, zero)
					}),
				)
				c.Show(
					"a sum of zero terms is 0, and μ·ν is nonnegative",
					ByArith(real_sum.EqZero.At(k, c.TermAs[Fun[A, Real]]("λi:A. |a(i) * b(i)|")), vanish, rootsNonneg))
			}))
		positiveBeta := arg.Assuming(
			arg.Term("&0 < β"),
			"if β = 0, every b(i) is 0 and the left side vanishes",
			Given(func(c *Argument, notPositive Fact) {
				zero := c.Have(
					"the powers |b(i)|^q sum to 0",
					"Σ_{i∈k} real_rpow(|b(i)|, q) = &0",
					ByArith(notPositive, sumsNonneg, βDef))
				vanish := c.Have(
					"so every b(i) is 0, and with it every term |a(i)·b(i)|",
					"∀i:A. i ∈ k ⇒ |a(i) * b(i)| = &0",
					c.ForEach(func(i *Expr[A]) Action {
						return ByArith(PowerSumZero.At(k, b, q, i), finiteK, zero)
					}),
				)
				c.Show(
					"a sum of zero terms is 0, and μ·ν is nonnegative",
					ByArith(real_sum.EqZero.At(k, c.TermAs[Fun[A, Real]]("λi:A. |a(i) * b(i)|")), vanish, rootsNonneg))
			}))
		rootsPositive := arg.Have(
			"μ and ν, powers of positive reals, are positive",
			"&0 < μ ∧ &0 < ν",
			ByArith(
				μDef,
				νDef,
				positiveAlpha,
				positiveBeta,
				real_rpow.RpowPositive.At(α, inverseP),
				real_rpow.RpowPositive.At(β, inverseQ)),
		)
		reciprocals := arg.Have(
			"p·(1/p) = q·(1/q) = 1, the reciprocals of the positive "+
				"μ and ν are nonnegative, and that of μ·ν is their product",
			"real_inv(p) * p = &1 ∧ "+
				"real_inv(q) * q = &1 ∧ "+
				"&0 ≤ real_inv(μ) ∧ "+
				"&0 ≤ real_inv(ν) ∧ "+
				"real_inv(μ * ν) = real_inv(μ) * real_inv(ν)",
			ByArith(pAbove, qAbove, rootsPositive),
		)
		powers := arg.Have(
			"μ is the p-th root of α and ν the q-th root of β: μ^p = α^((1/p)·p) = α, and ν^q = β",
			"real_rpow(μ, p) = α ∧ real_rpow(ν, q) = β",
			ByArith(
				μDef,
				νDef,
				sumsNonneg,
				reciprocals,
				real_rpow.RpowRpow.At(α, inverseP, p),
				real_rpow.RpowRpow.At(β, inverseQ, q),
				real_rpow.RpowOneExponent.At(α),
				real_rpow.RpowOneExponent.At(β)),
		)
		inverseMu := arg.TermAs[Real]("real_inv(μ)")
		inverseNu := arg.TermAs[Real]("real_inv(ν)")
		scales := arg.Conjuncts(
			arg.Have(
				"(1/μ)^p = 1/μ^p = 1/α, so (1/μ)^p·α = 1, and likewise (1/ν)^q·β = 1",
				"real_rpow(real_inv(μ), p) * α = &1 ∧ real_rpow(real_inv(ν), q) * β = &1",
				ByArith(
					Normalized,
					powers,
					rootsNonneg,
					positiveAlpha,
					positiveBeta,
					real_rpow.RpowInvBase.At(μ, p),
					real_rpow.RpowInvBase.At(ν, q)),
			),
			"(1/μ)^p·α = 1",
			"(1/ν)^q·β = 1")
		termwise := arg.Have(
			"Young's inequality at |a(i)|/μ and |b(i)|/ν, a power of a product being the product of the powers",
			"∀i:A. "+
				"    |a(i) * b(i)| * real_inv(μ * ν) ≤ "+
				"    real_rpow(real_inv(μ), p) / p * real_rpow(|a(i)|, p) + "+
				"    real_rpow(real_inv(ν), q) / q * real_rpow(|b(i)|, q)",
			Derive(func(c *Argument) {
				i := c.FixAs[A]("i")
				absA := c.TermAs[Real]("|a(i)|")
				absB := c.TermAs[Real]("|b(i)|")
				c.Show(
					"(|a(i)|/μ)·(|b(i)|/ν) ≤ (|a(i)|/μ)^p/p + (|b(i)|/ν)^q/q",
					ByArith(
						reciprocals,
						pAbove,
						qAbove,
						conjugate,
						real_sgn_abs.AbsNonneg.At(a.Apply(i)),
						real_sgn_abs.AbsNonneg.At(b.Apply(i)),
						Scaled(inverseP, real_rpow.RpowMulBase.At(inverseMu, absA, p)),
						Scaled(inverseQ, real_rpow.RpowMulBase.At(inverseNu, absB, q)),
						Young.At(c.TermAs[Real]("real_inv(μ) * |a(i)|"), c.TermAs[Real]("real_inv(ν) * |b(i)|"), p, q)),
				)
			}),
		)
		summed := arg.Have(
			"summed over k, the right side is (1/μ)^p·α/p + (1/ν)^q·β/q",
			"(Σ_{i∈k} |a(i) * b(i)|) * real_inv(μ * ν) ≤ "+
				"real_rpow(real_inv(μ), p) / p * α + real_rpow(real_inv(ν), q) / q * β",
			By(
				real_sum.Monotone.At(
					k,
					arg.TermAs[Fun[A, Real]]("λi:A. |a(i) * b(i)| * real_inv(μ * ν)"),
					arg.TermAs[Fun[A, Real]](
						"λi:A. "+
							"    real_rpow(real_inv(μ), p) / p * real_rpow(|a(i)|, p) + "+
							"    real_rpow(real_inv(ν), q) / q * real_rpow(|b(i)|, q)")),
				real_sum.ScalarRight.At(
					arg.TermAs[Real]("real_inv(μ * ν)"),
					arg.TermAs[Fun[A, Real]]("λi:A. |a(i) * b(i)|"),
					k),
				real_sum.Add.At(
					arg.TermAs[Fun[A, Real]]("λi:A. real_rpow(real_inv(μ), p) / p * real_rpow(|a(i)|, p)"),
					arg.TermAs[Fun[A, Real]]("λi:A. real_rpow(real_inv(ν), q) / q * real_rpow(|b(i)|, q)"),
					k),
				real_sum.ScalarLeft.At(arg.TermAs[Real]("real_rpow(real_inv(μ), p) / p"), powerA, k),
				real_sum.ScalarLeft.At(arg.TermAs[Real]("real_rpow(real_inv(ν), q) / q"), powerB, k),
				finiteK,
				termwise,
				αDef,
				βDef),
		)
		normalized := arg.Have(
			"which is 1/p + 1/q = 1",
			"(Σ_{i∈k} |a(i) * b(i)|) * real_inv(μ * ν) ≤ &1",
			ByArith(summed, Scaled(inverseP, scales[0]), Scaled(inverseQ, scales[1]), conjugate),
		)
		sum := arg.TermAs[Real]("Σ_{i∈k} |a(i) * b(i)|")
		product := arg.TermAs[Real]("μ * ν")
		arg.Show(
			"clear the positive divisor μ·ν",
			ByArith(
				normalized,
				rootsPositive,
				real_order_ring.MulPos.At(μ, ν),
				real_order_field.LessEqDivMulRight.At(sum, arg.TermAs[Real]("&1"), product),
				real_field.RealDivDef.At(sum, product)),
		)
	}),
})}

// Minkowski — Minkowski's inequality, the triangle inequality of the
// p-norm for p ≥ 1: the p-th root ρ of σ = Σ |a(i) + b(i)|^p is at most
// the sum of the p-th roots μ and ν of α = Σ |a(i)|^p and β = Σ |b(i)|^p.
// At p = 1 the roots are the sums, and the claim is the triangle
// inequality summed over k. For p > 1, and σ > 0, let q = p/(p − 1) be the
// conjugate exponent and τ = σ^(1/q). Each |a(i) + b(i)|^p is at most
// (|a(i)| + |b(i)|)·|a(i) + b(i)|^(p−1); the q-th powers of the
// |a(i) + b(i)|^(p−1) are the |a(i) + b(i)|^p, so Hölder's inequality
// bounds the two sums that result by μ·τ and ν·τ. Hence
// ρ·τ = σ^(1/p + 1/q) = σ ≤ (μ + ν)·τ, and τ > 0.
var Minkowski = minkowskiThm{family.Add(registry.ProofEntry{
	Name: "Minkowski",
	Key:  "prop_3102484559191e9c",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(A). ∀a b:A → real. ∀p:real.",
		Hypotheses: []string{
			"finite(k)",
			"&1 ≤ p",
		},
		Conclusion: "real_rpow(Σ_{i∈k} real_rpow(|a(i) + b(i)|, p), real_inv(p)) ≤ " +
			"real_rpow(Σ_{i∈k} real_rpow(|a(i)|, p), real_inv(p)) + " +
			"real_rpow(Σ_{i∈k} real_rpow(|b(i)|, p), real_inv(p))",
	}, func(
		arg *Argument,
		k *Expr[Set[A]],
		a, b *Arrow[A, Real],
		p *Expr[Real],
		finiteK, pAtLeastOne Fact,
	) {
		powerSum := arg.TermAs[Fun[A, Real]]("λi:A. real_rpow(|a(i) + b(i)|, p)")
		powerA := arg.TermAs[Fun[A, Real]]("λi:A. real_rpow(|a(i)|, p)")
		powerB := arg.TermAs[Fun[A, Real]]("λi:A. real_rpow(|b(i)|, p)")
		sumsNonneg := arg.Have(
			"sums of nonnegative powers are nonnegative",
			"&0 ≤ Σ_{i∈k} real_rpow(|a(i) + b(i)|, p) ∧ "+
				"&0 ≤ Σ_{i∈k} real_rpow(|a(i)|, p) ∧ "+
				"&0 ≤ Σ_{i∈k} real_rpow(|b(i)|, p)",
			By(
				real_sum.Nonneg.At(k, powerSum),
				real_sum.Nonneg.At(k, powerA),
				real_sum.Nonneg.At(k, powerB),
				real_rpow.RpowNonneg),
		)
		σ, σDef := arg.LetAs[Real]("σ", "Σ_{i∈k} real_rpow(|a(i) + b(i)|, p)")
		α, αDef := arg.LetAs[Real]("α", "Σ_{i∈k} real_rpow(|a(i)|, p)")
		β, βDef := arg.LetAs[Real]("β", "Σ_{i∈k} real_rpow(|b(i)|, p)")
		_, ρDef := arg.LetAs[Real]("ρ", "real_rpow(σ, real_inv(p))")
		_, μDef := arg.LetAs[Real]("μ", "real_rpow(α, real_inv(p))")
		_, νDef := arg.LetAs[Real]("ν", "real_rpow(β, real_inv(p))")
		inverseP := arg.TermAs[Real]("real_inv(p)")
		pNotOne := arg.Unless(
			arg.Term("p = &1"),
			"at p = 1 each root is its sum, and the claim is the triangle inequality summed over k",
			Given(func(c *Argument, one Fact) {
				termwise := c.Have(
					"at p = 1 each power is its base, and |a(i) + b(i)| ≤ |a(i)| + |b(i)|",
					"∀i:A. real_rpow(|a(i) + b(i)|, p) ≤ real_rpow(|a(i)|, p) + real_rpow(|b(i)|, p)",
					Derive(func(d *Argument) {
						i := d.FixAs[A]("i")
						d.Show(
							"the triangle inequality",
							ByArith(
								one,
								real_sgn_abs.AbsNonneg.At(d.TermAs[Real]("a(i) + b(i)")),
								real_sgn_abs.AbsNonneg.At(a.Apply(i)),
								real_sgn_abs.AbsNonneg.At(b.Apply(i)),
								real_rpow.RpowOneExponent.At(d.TermAs[Real]("|a(i) + b(i)|")),
								real_rpow.RpowOneExponent.At(d.TermAs[Real]("|a(i)|")),
								real_rpow.RpowOneExponent.At(d.TermAs[Real]("|b(i)|"))),
						)
					}),
				)
				summed := c.Have(
					"summed over k",
					"σ ≤ α + β",
					By(
						real_sum.Monotone.At(
							k, powerSum, c.TermAs[Fun[A, Real]]("λi:A. real_rpow(|a(i)|, p) + real_rpow(|b(i)|, p)")),
						real_sum.Add.At(powerA, powerB, k),
						finiteK,
						termwise,
						σDef,
						αDef,
						βDef),
				)
				reciprocal := c.Have(
					"1 is its own reciprocal",
					"real_inv(p) = &1",
					By(one, field.InvOne.Read(real_field.Field)))
				c.Show(
					"each root is its sum, the exponent 1/p being 1",
					ByArith(
						summed,
						reciprocal,
						ρDef,
						μDef,
						νDef,
						sumsNonneg,
						real_rpow.RpowOneExponent.At(σ),
						real_rpow.RpowOneExponent.At(α),
						real_rpow.RpowOneExponent.At(β)),
				)
			}))
		positiveSigma := arg.Assuming(
			arg.Term("&0 < σ"),
			"if σ = 0, its root is 0 and the right side is nonnegative",
			Given(func(c *Argument, notPositive Fact) {
				zero := c.Have(
					"σ is 0",
					"σ = &0",
					ByArith(notPositive, sumsNonneg))
				c.Show(
					"0 to the power 1/p ≠ 0 is 0, and μ and ν are nonnegative",
					ByArith(
						zero,
						ρDef,
						μDef,
						νDef,
						pAtLeastOne,
						real_rpow.RpowZeroBase.At(inverseP),
						real_rpow.RpowNonneg.At(α, inverseP),
						real_rpow.RpowNonneg.At(β, inverseP)),
				)
			}))
		q, qDef := arg.LetAs[Real]("q", "p / (p - &1)")
		conjugate := arg.Conjuncts(
			arg.Have(
				"p exceeds 1, and q = p/(p − 1) is its conjugate exponent",
				"&1 < p ∧ &1 < q ∧ (p - &1) * q = p ∧ real_inv(p) + real_inv(q) = &1",
				qDef.Rw(),
				ByArith(pNotOne, pAtLeastOne),
			),
			"p exceeds 1",
			"so does q",
			"(p − 1)·q = p",
			"1/p + 1/q = 1")
		_, τDef := arg.LetAs[Real]("τ", "real_rpow(σ, real_inv(q))")
		inverseQ := arg.TermAs[Real]("real_inv(q)")
		fixed := arg.Have(
			"each |a(i) + b(i)|^(p − 1), a power, is nonnegative and so its own absolute value",
			"∀i:A. |real_rpow(|a(i) + b(i)|, p - &1)| = real_rpow(|a(i) + b(i)|, p - &1)",
			Derive(func(c *Argument) {
				c.FixAs[A]("i")
				c.Show(
					"a power is nonnegative",
					ByArith(real_rpow.RpowNonneg.At(c.TermAs[Real]("|a(i) + b(i)|"), c.TermAs[Real]("p - &1"))))
			}),
		)
		lowered := arg.TermAs[Real]("p - &1")
		exponent := arg.Have(
			"the exponents p − 1 and 1 add to p",
			"p - &1 + &1 = p",
			ByArith())
		termwise := arg.Have(
			"|a(i) + b(i)|^p = |a(i) + b(i)|·|a(i) + b(i)|^(p − 1) ≤ (|a(i)| + |b(i)|)·|a(i) + b(i)|^(p − 1)",
			"∀i:A. "+
				"    real_rpow(|a(i) + b(i)|, p) ≤ "+
				"    |a(i) * real_rpow(|a(i) + b(i)|, p - &1)| + |b(i) * real_rpow(|a(i) + b(i)|, p - &1)|",
			Derive(func(c *Argument) {
				i := c.FixAs[A]("i")
				base := c.TermAs[Real]("|a(i) + b(i)|")
				c.Show(
					"raising the exponent p − 1 ≥ 0 by 1 multiplies the power by the base, and the triangle inequality",
					ByArith(
						conjugate[0],
						exponent,
						fixed.At(i),
						real_sgn_abs.AbsNonneg.At(c.TermAs[Real]("a(i) + b(i)")),
						real_rpow.RpowAddOne.At(base, lowered),
						real_rpow.RpowNonneg.At(base, lowered),
						real_sgn_abs.AbsTriangle.At(a.Apply(i), b.Apply(i))),
				)
			}),
		)
		power := arg.TermAs[Fun[A, Real]]("λi:A. real_rpow(|a(i) + b(i)|, p - &1)")
		summed := arg.Have(
			"summed over k",
			"σ ≤ "+
				"Σ_{i∈k} |a(i) * real_rpow(|a(i) + b(i)|, p - &1)| + "+
				"Σ_{i∈k} |b(i) * real_rpow(|a(i) + b(i)|, p - &1)|",
			By(
				real_sum.Monotone.At(
					k,
					powerSum,
					arg.TermAs[Fun[A, Real]](
						"λi:A. |a(i) * real_rpow(|a(i) + b(i)|, p - &1)| + |b(i) * real_rpow(|a(i) + b(i)|, p - &1)|")),
				real_sum.Add.At(
					arg.TermAs[Fun[A, Real]]("λi:A. |a(i) * real_rpow(|a(i) + b(i)|, p - &1)|"),
					arg.TermAs[Fun[A, Real]]("λi:A. |b(i) * real_rpow(|a(i) + b(i)|, p - &1)|"),
					k),
				finiteK,
				termwise,
				σDef),
		)
		powered := arg.Have(
			"the q-th power of |a(i) + b(i)|^(p − 1) is |a(i) + b(i)|^((p − 1)·q) = |a(i) + b(i)|^p",
			"∀i:A. real_rpow(|real_rpow(|a(i) + b(i)|, p - &1)|, q) = real_rpow(|a(i) + b(i)|, p)",
			Derive(func(c *Argument) {
				i := c.FixAs[A]("i")
				c.Show(
					"a power of a power is the power at the product of the exponents",
					By(
						conjugate[2],
						fixed.At(i),
						real_sgn_abs.AbsNonneg.At(c.TermAs[Real]("a(i) + b(i)")),
						real_rpow.RpowRpow.At(c.TermAs[Real]("|a(i) + b(i)|"), c.TermAs[Real]("p - &1"), q)),
				)
			}),
		)
		dual := arg.Have(
			"so those q-th powers sum to σ",
			"Σ_{i∈k} real_rpow(|real_rpow(|a(i) + b(i)|, p - &1)|, q) = σ",
			By(
				real_sum.Congruence.At(
					k,
					arg.TermAs[Fun[A, Real]]("λi:A. real_rpow(|real_rpow(|a(i) + b(i)|, p - &1)|, q)"),
					powerSum),
				powered,
				σDef),
		)
		bound := arg.Have(
			"Hölder's inequality bounds the two sums by μ·τ and ν·τ",
			"σ ≤ (μ + ν) * τ",
			ByArith(
				summed,
				Holder.At(k, a, power, p, q),
				Holder.At(k, b, power, p, q),
				finiteK,
				conjugate[0],
				conjugate[1],
				conjugate[3],
				dual,
				αDef,
				βDef,
				μDef,
				νDef,
				τDef),
		)
		split := arg.Have(
			"σ = σ^(1/p + 1/q) = ρ·τ, and τ is positive",
			"σ = ρ * τ ∧ &0 < τ",
			ByArith(
				conjugate[3],
				ρDef,
				τDef,
				positiveSigma,
				sumsNonneg,
				real_rpow.RpowAdd.At(σ, inverseP, inverseQ),
				real_rpow.RpowOneExponent.At(σ),
				real_rpow.RpowPositive.At(σ, inverseQ)),
		)
		arg.Show(
			"cancel the positive factor τ from ρ·τ ≤ (μ + ν)·τ",
			ByArith(bound, split))
	}),
})}
