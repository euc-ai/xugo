// multiplicative.go — the modulus of a product is the product of the moduli, and what follows from it.

package complex_abs

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// AbsMul — the modulus is multiplicative. The radicand of z·w is the
// product of the radicands of z and w (the two-squares identity), which
// is the square of |z|·|w|; a nonnegative number squaring to the
// radicand is its root.
var AbsMul = absMulThm{family.Add(registry.ProofEntry{
	Name: "AbsMul",
	Key:  "prop_9a90f3c903a56257",
	Build: family.Theorem("∀z w:complex. |z * w| = |z| * |w|",
		func(a *Argument, z, w *Expr[Complex]) {
			product := a.TermAs[Complex]("z * w")
			// The radicand of z·w, written on the parts of the product.
			radicand := a.TermAs[Real](
				"(re(z) * re(w) - im(z) * im(w)) * (re(z) * re(w) - im(z) * im(w)) + " +
					"(re(z) * im(w) + im(z) * re(w)) * (re(z) * im(w) + im(z) * re(w))")
			root := a.TermAs[Real]("|z| * |w|")

			// A chain of equations alone needs no order certificates: the
			// empty kit, where ℝ's OrderCalc would claim transitivity.
			squared := a.CalcLeibniz(CalcOrder{}, radicand,
				EqLeg(
					a.Term("(re(z) * re(z) + im(z) * im(z)) * (re(w) * re(w) + im(w) * im(w))"),
					"the two-squares identity: multiply out",
					ByArith()),
				EqLeg(
					a.Term("|z| * |z| * (|w| * |w|)"),
					"each radicand is the square of its modulus",
					By(AbsSquare.At(z), AbsSquare.At(w))),
				EqLeg(
					a.Term("real_pow(|z| * |w|, 2)"),
					"which is the square of |z|·|w|",
					ByArith()))
			sign := a.Have(
				"a product of two moduli is nonnegative",
				"&0 ≤ |z| * |w|",
				ByArith(AbsNonneg.At(z), AbsNonneg.At(w)))

			a.Show(
				"so |z|·|w| is the root of the radicand of z·w, which is |z·w|",
				By(
					ComplexAbsDef.At(product),
					complex_field.PartsMul.At(z, w),
					squared,
					sign,
					real_sqrt.SqrtUnique.At(radicand, root)))
		}),
})}

// AbsInv — the modulus of an inverse is the inverse of the modulus. The
// modulus is a map from ℂ to ℝ that sends zero to zero, one to one and
// products to products (AbsMul) — it is not additive, and does not need
// to be — so it carries inverses to inverses (field.MapInv).
var AbsInv = absInvThm{family.Add(registry.ProofEntry{
	Name: "AbsInv",
	Key:  "prop_6f384aef51a5930a",
	Build: family.Theorem("∀z:complex. |complex_inv(z)| = real_inv(|z|)",
		func(a *Argument, z *Expr[Complex]) {
			complexes := a.TermAs[field.FieldOps[Complex]]("restrict_field(complex_field_ops, 𝕌)")
			reals := a.TermAs[field.FieldOps[Real]]("restrict_field(real_field_ops, 𝕌)")
			complexesWhole := a.Have(
				"ℂ is a field on the whole of ℂ",
				"field_on(restrict_field(complex_field_ops, 𝕌))",
				By(complex_field.Field, field.FieldOnUniverse))
			realsWhole := a.Have(
				"ℝ is a field on the whole of ℝ",
				"field_on(restrict_field(real_field_ops, 𝕌))",
				By(real_field.Field, field.FieldOnUniverse))
			zeroMap := a.Have(
				"the modulus of zero is zero",
				"|complex_of_real(&0)| = &0",
				Simp(Fwd(AbsOfReal), Fwd(real_sgn_abs.AbsOfZero)),
				Refl())
			oneMap := a.Have(
				"and the modulus of one is one",
				"|complex_of_real(&1)| = &1",
				Simp(Fwd(AbsOfReal), Fwd(real_sgn_abs.AbsOfOne)),
				Refl())
			a.Show(
				"so the modulus, respecting products, carries inverses to inverses",
				By(
					field.MapInv.At(complexes, reals, a.TermAs[Fun[Complex, Real]]("complex_abs"), z),
					complexesWhole,
					realsWhole,
					AbsMul,
					zeroMap,
					oneMap,
					set_basic.InUniv))
		}),
})}

// AbsDiv — the modulus of a quotient is the quotient of the moduli: a
// quotient is a product with an inverse, and the modulus carries both.
var AbsDiv = absDivThm{family.Add(registry.ProofEntry{
	Name: "AbsDiv",
	Key:  "prop_56bab775e14e6b49",
	Build: family.Theorem("∀w v:complex. |w / v| = |w| / |v|",
		func(a *Argument, w, v *Expr[Complex]) {
			a.Show(
				"each quotient is a product with an inverse, and the modulus carries both",
				Simp(Fwd(complex_field.ComplexDivDef), Fwd(AbsMul), Fwd(AbsInv), Fwd(real_field.RealDivDef)),
				Refl())
		}),
})}

// AbsPow — the modulus of a power is the power of the modulus. The
// modulus keeps 1 and carries products to products (AbsMul), so
// comm_monoid.MapPow carries ℂ's power to the monoid power of ℝ's
// product, which is real_pow (real_pow.MonoidPow).
var AbsPow = absPowThm{family.Add(registry.ProofEntry{
	Name: "AbsPow",
	Key:  "prop_a544895c20cbbb88",
	Build: family.Theorem("∀z:complex. ∀n:num. |z ^ n| = real_pow(|z|, n)",
		func(a *Argument, z *Expr[Complex], n *Expr[Nat]) {
			one := a.Have(
				"the modulus of 1 is 1",
				"|complex_of_real(&1)| = &1",
				Simp(Fwd(AbsOfReal)),
				ByArith())
			a.Show(
				"ℝ's power is its product's monoid power, and the modulus keeps 1 and products",
				Simp(Fwd(real_pow.MonoidPow)),
				By(Where(comm_monoid.MapPow, "h", a.Term("complex_abs")), one, AbsMul))
		}),
})}

// AbsRootOfUnity — a root of unity has modulus 1. Taking moduli, |z|ⁿ is
// 1; at a nonzero exponent the power is strictly increasing on the
// nonnegative reals (real_pow.PowMonoBaseStrict), so |z| is neither below
// 1 nor above it.
var AbsRootOfUnity = absRootOfUnityThm{family.Add(registry.ProofEntry{
	Name: "AbsRootOfUnity",
	Key:  "prop_ebd4ebb84e12f132",
	Build: family.Theorem(Statement{
		Binders: "∀z:complex. ∀n:num.",
		Hypotheses: []string{
			"z ^ n = &1",
			"n ≠ 0",
		},
		Conclusion: "|z| = &1",
	}, func(a *Argument, z *Expr[Complex], n *Expr[Nat], root, nonzero Fact) {
		one := a.TermAs[Real]("&1")
		modulus := a.TermAs[Real]("|z|")
		modulusPower := a.Have(
			"taking moduli, |z|ⁿ is 1",
			"|z| ^ n = &1",
			By(root, AbsPow.At(z, n), AbsOfReal.At(one), real_sgn_abs.AbsOfOne))
		a.Show(
			"the nonzero power is strictly increasing on the nonnegative reals, so |z| is 1",
			ByArith(
				nonzero,
				modulusPower,
				AbsNonneg.At(z),
				real_pow.OnePow.At(n),
				real_pow.PowMonoBaseStrict.At(modulus, one, n),
				real_pow.PowMonoBaseStrict.At(one, modulus, n)))
	}),
})}
