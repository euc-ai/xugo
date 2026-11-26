// euler.go — Euler's formula: the exponential series at i·z, split by
// the parity of its index, is the cosine series plus i times the sine
// series; on the real line, and at π.

package complex_exp

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/registry"
)

// IPowEven — i to an even power is a real sign: i²ⁿ = (i²)ⁿ = (−1)ⁿ.
var IPowEven = iPowEvenThm{family.Add(registry.ProofEntry{
	Name: "IPowEven",
	Key:  "prop_998a2e9fac517efd",
	Build: family.Theorem("∀n:num. complex_i ^ (2 * n) = complex_of_real(real_pow(-&1, n))",
		func(arg *Argument, n *Expr[Nat]) {
			twice := arg.Have(
				"i² is i·i",
				"complex_i ^ 2 = complex_i * complex_i",
				By(comm_monoid.PowTwo, complex_field.MulMonoid))
			square := arg.Have(
				"which is −1",
				"complex_i ^ 2 = complex_of_real(-&1)",
				twice.Rw(),
				Simp(Fwd(complex_field.OfRealNeg)),
				By(complex_field.ISquared))
			even := arg.Have(
				"i²ⁿ is (i²)ⁿ",
				"complex_i ^ (2 * n) = (complex_i ^ 2) ^ n",
				By(comm_monoid.PowPow, complex_field.MulMonoid))
			arg.Show(
				"so it is (−1)ⁿ, the embedding carrying ℝ's power to ℂ's",
				even.Rw(),
				square.Rw(),
				By(complex_field.OfRealPow))
		}),
})}

// EulerTerm — Euler's formula term by term: the n-th pair of the
// exponential series at i·z is the cosine series' n-th term plus i times
// the sine series' n-th term. (i·z)²ⁿ = i²ⁿ·z²ⁿ = (−1)ⁿ·z²ⁿ, and
// (i·z)²ⁿ⁺¹ is one more factor i·z; what is left is one polynomial in i,
// z, (−1)ⁿ and z²ⁿ on both sides, compared part by part.
var EulerTerm = eulerTermThm{family.Add(registry.ProofEntry{
	Name: "EulerTerm",
	Key:  "prop_bae2356a7c321c97",
	Build: family.Theorem(Statement{
		Binders:    "∀z:complex. ∀n:num.",
		Conclusion: "«evenExpTerm» + «oddExpTerm» = «cosTerm» + complex_i * «sinTerm»",
		Abbrev: Abbrev{
			{Name: "evenExpTerm", Text: "(complex_i * z) ^ (2 * n) / complex_of_real(&factorial(2 * n))"},
			{Name: "oddExpTerm", Text: "(complex_i * z) ^ (2 * n + 1) / " +
				"complex_of_real(&factorial(2 * n + 1))"},
		},
	},
		func(arg *Argument, z *Expr[Complex], n *Expr[Nat]) {
			product := arg.Have(
				"(i·z)²ⁿ is i²ⁿ·z²ⁿ",
				"(complex_i * z) ^ (2 * n) = complex_i ^ (2 * n) * z ^ (2 * n)",
				By(comm_monoid.MulPow, complex_field.MulMonoid))
			even := arg.Have(
				"which is (−1)ⁿ·z²ⁿ",
				"(complex_i * z) ^ (2 * n) = complex_of_real(real_pow(-&1, n)) * z ^ (2 * n)",
				product.Rw(),
				Simp(Fwd(IPowEven)),
				Refl())
			odd := arg.Have(
				"(i·z)²ⁿ⁺¹ is one more factor i·z",
				"(complex_i * z) ^ (2 * n + 1) = complex_i * z * (complex_i * z) ^ (2 * n)",
				Simp(Rev(nat_arith.Add1)),
				Simp(Fwd(comm_monoid.MonoidPowDef.Inst[Complex]())),
				Refl())
			oddZ := arg.Have(
				"and z²ⁿ⁺¹ one more factor z",
				"z ^ (2 * n + 1) = z * z ^ (2 * n)",
				Simp(Rev(nat_arith.Add1)),
				Simp(Fwd(comm_monoid.MonoidPowDef.Inst[Complex]())),
				Refl())
			// One regrouping of a product of six factors — associativity and
			// commutativity, stated once over variables (a, w, c, y, u, v
			// for i, z, (−1)ⁿ, z²ⁿ, 1/(2n)!, 1/(2n+1)!) and proved by
			// comparing parts, which at the site would also unfold the
			// operation inside ℂ's power.
			regroup := arg.Have(
				"multiplication in ℂ regroups freely, as the parts compare",
				"∀a w c y u v:complex. c * y * u + a * w * (c * y) * v = c * y * u + a * (c * (w * y) * v)",
				Derive(func(d *Argument) {
					d.FixAs[Complex]()
					d.FixAs[Complex]()
					d.FixAs[Complex]()
					d.FixAs[Complex]()
					d.FixAs[Complex]()
					d.FixAs[Complex]()
					d.Show(
						"both sides have the same parts",
						Simp(complex_field.Parts, Fwd(complex_field.ComplexAddDef), Fwd(complex_field.ComplexMulDef)),
						ByArith())
				}))
			arg.Show(
				"both sides are one product of i, z, (−1)ⁿ and z²ⁿ over the factorials, grouped differently",
				odd.Rw(),
				even.Rw(),
				oddZ.Rw(),
				Simp(Fwd(complex_field.ComplexDivDef)),
				By(regroup))
		}),
})}

// Euler — Euler's formula: exp(i·z) = cos z + i·sin z. The exponential
// series at i·z, taken two terms at a time, still sums to exp(i·z), and
// by EulerTerm it is then the cosine series plus i times the sine
// series, which sums to cos z + i·sin z; a series has one sum.
var Euler = eulerThm{family.Add(registry.ProofEntry{
	Name: "Euler",
	Key:  "prop_e38643464c83b1b0",
	Build: family.Theorem("∀z:complex. exp(complex_i * z) = cos(z) + complex_i * sin(z)",
		func(arg *Argument, z *Expr[Complex]) {
			pairs := arg.Have(
				"the exponential series at i·z, two terms at a time, sums to exp(i·z)",
				"complex_sums(λn:num. "+
					"        (complex_i * z) ^ (2 * n) / complex_of_real(&factorial(2 * n)) + "+
					"        (complex_i * z) ^ (2 * n + 1) / complex_of_real(&factorial(2 * n + 1)), "+
					"    exp(complex_i * z))",
				By(ExpSums.At(arg.TermAs[Complex]("complex_i * z")), complex_series.SumsPair))
			termwise := arg.Have(
				"its n-th pair is the cosine's n-th term plus i times the sine's",
				"(λn:num. "+
					"    (complex_i * z) ^ (2 * n) / complex_of_real(&factorial(2 * n)) + "+
					"    (complex_i * z) ^ (2 * n + 1) / complex_of_real(&factorial(2 * n + 1))) = "+
					"λn:num. "+
					"    complex_of_real(real_pow(-&1, n)) * z ^ (2 * n) / complex_of_real(&factorial(2 * n)) + "+
					"    complex_i * "+
					"    (complex_of_real(real_pow(-&1, n)) * "+
					"        z ^ (2 * n + 1) / "+
					"        complex_of_real(&factorial(2 * n + 1)))",
				Funext(),
				arg.ForEach(func(n *Expr[Nat]) Action { return By(EulerTerm.At(z, n)) }))
			atI := arg.Have(
				"so the cosine series plus i times the sine series sums to exp(i·z)",
				"complex_sums(λn:num. "+
					"        complex_of_real(real_pow(-&1, n)) * z ^ (2 * n) / complex_of_real(&factorial(2 * n)) + "+
					"        complex_i * "+
					"        (complex_of_real(real_pow(-&1, n)) * "+
					"            z ^ (2 * n + 1) / "+
					"            complex_of_real(&factorial(2 * n + 1))), "+
					"    exp(complex_i * z))",
				termwise.RwRev(),
				By(pairs))
			scaled := arg.Have(
				"i times the sine series sums to i·sin z",
				"complex_sums(λn:num. "+
					"        complex_i * "+
					"        (complex_of_real(real_pow(-&1, n)) * "+
					"            z ^ (2 * n + 1) / "+
					"            complex_of_real(&factorial(2 * n + 1))), "+
					"    complex_i * sin(z))",
				By(SinSums.At(z), complex_series.SumsScale))
			both := arg.Have(
				"and with the cosine series added, to cos z + i·sin z",
				"complex_sums(λn:num. "+
					"        complex_of_real(real_pow(-&1, n)) * z ^ (2 * n) / complex_of_real(&factorial(2 * n)) + "+
					"        complex_i * "+
					"        (complex_of_real(real_pow(-&1, n)) * "+
					"            z ^ (2 * n + 1) / "+
					"            complex_of_real(&factorial(2 * n + 1))), "+
					"    cos(z) + complex_i * sin(z))",
				By(CosSums.At(z), scaled, complex_series.SumsAdd))
			arg.Show(
				"a series has one sum",
				By(atI, both, complex_series.SumsUnique))
		}),
})}

// EulerOfReal — Euler's formula on the real line: exp(i·x) is the point
// (cos x, sin x), with ℝ's cosine and sine.
var EulerOfReal = eulerOfRealThm{family.Add(registry.ProofEntry{
	Name: "EulerOfReal",
	Key:  "prop_944ebb0d7115dd2e",
	Build: family.Theorem("∀x:real. "+
		"    exp(complex_i * complex_of_real(x)) = "+
		"    complex_of_real(cos(x)) + complex_i * complex_of_real(sin(x))",
		func(arg *Argument, x *Expr[Real]) {
			arg.Show(
				"Euler's formula at the embedded x, where the cosine and the sine are ℝ's",
				Simp(Fwd(Euler)),
				Simp(Fwd(CosOfReal), Fwd(SinOfReal)),
				Refl())
		}),
})}

// AbsExpIOfReal — exp(i·x) lies on the unit circle: it is the point
// (cos x, sin x), whose distance from 0 is √(cos²x + sin²x), and
// cos²x + sin²x = 1.
var AbsExpIOfReal = absExpIOfRealThm{family.Add(registry.ProofEntry{
	Name: "AbsExpIOfReal",
	Key:  "prop_8577fa400f82d316",
	Build: family.Theorem("∀x:real. |exp(complex_i * complex_of_real(x))| = &1",
		func(arg *Argument, x *Expr[Real]) {
			circle := arg.Have(
				"cos²x + sin²x = 1",
				"cos(x) * cos(x) + sin(x) * sin(x) = &1",
				ByArith(
					real_trigonometry.SinSquareAddCosSquare.At(x),
					real_pow.PowTwo.At(arg.TermAs[Real]("cos(x)")),
					real_pow.PowTwo.At(arg.TermAs[Real]("sin(x)"))))
			one := arg.TermAs[Real]("&1")
			square := arg.Have(
				"1 is the square of 1",
				"&1 = real_pow(&1, 2)",
				By(real_pow.OnePow.At(arg.TermAs[Nat]("2"))))
			root := arg.Have(
				"so 1 is the root of 1",
				"&1 = real_sqrt(&1)",
				By(square, real_sqrt.SqrtUnique.At(one, one)))
			arg.Show(
				"exp(i·x) is the point (cos x, sin x), at distance √(cos²x + sin²x) from 0",
				Simp(Fwd(EulerOfReal), Rev(complex_field.StandardForm)),
				Simp(Fwd(complex_abs.ComplexAbsDef), complex_field.Parts),
				circle.Rw(),
				By(root))
		}),
})}

// EulerIdentity — e^{iπ} + 1 = 0: at π the cosine is −1 and the sine 0.
var EulerIdentity = eulerIdentityThm{family.Add(registry.ProofEntry{
	Name: "EulerIdentity",
	Key:  "prop_d9d3e5c7cba66055",
	Build: family.Theorem("exp(complex_i * complex_of_real(pi)) + complex_of_real(&1) = "+
		"complex_of_real(&0)",
		func(arg *Argument) {
			arg.Show(
				"exp(iπ) = cos π + i·sin π = −1 + i·0, and −1 + 1 = 0",
				Simp(Fwd(EulerOfReal), Fwd(real_trigonometry.CosPi), Fwd(real_trigonometry.SinPi)),
				Simp(
					complex_field.Parts,
					Fwd(complex_field.ComplexAddDef),
					Fwd(complex_field.ComplexMulDef),
					Fwd(complex_field.ComplexOfRealDef),
					Fwd(complex_field.ComplexIDef)),
				ByArith())
		}),
})}
