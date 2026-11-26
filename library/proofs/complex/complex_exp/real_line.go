// real_line.go — on the real line the three functions are ℝ's: each
// series at an embedded real is ℝ's series carried into ℂ term by term;
// and their values at 0.

package complex_exp

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/registry"
)

// ExpOfReal — on the reals the exponential is ℝ's. The embedding
// carries quotients and powers, so ℝ's exponential series at x, carried
// into ℂ, is ℂ's at the embedded x; a real series and its image converge
// together, and a series has one sum.
var ExpOfReal = expOfRealThm{family.Add(registry.ProofEntry{
	Name: "ExpOfReal",
	Key:  "prop_242420dc8b4d7a8c",
	Build: family.Theorem("∀x:real. exp(complex_of_real(x)) = complex_of_real(exp(x))",
		func(arg *Argument, x *Expr[Real]) {
			terms := arg.Have(
				"ℝ's series at x, carried into ℂ, is ℂ's at the embedded x",
				"(λn:num. complex_of_real(real_pow(x, n) / &factorial(n))) = "+
					"(λn:num. complex_of_real(x) ^ n / complex_of_real(&factorial(n)))",
				Funext(),
				arg.ForEach(func(*Expr[Nat]) Action {
					return Chain(Simp(Fwd(complex_field.OfRealDiv), Fwd(complex_field.OfRealPow)), Refl())
				}))
			embedded := arg.Have(
				"so ℂ's series at the embedded x sums to the embedded exp(x)",
				"complex_sums(λn:num. complex_of_real(x) ^ n / complex_of_real(&factorial(n)), "+
					"    complex_of_real(exp(x)))",
				terms.RwRev(),
				By(real_exp_log.ExpSums.At(x), complex_series.SumsOfReal))
			arg.Show(
				"it sums to exp of the embedded x as well, and a series has one sum",
				By(embedded, ExpSums.At(arg.TermAs[Complex]("complex_of_real(x)")), complex_series.SumsUnique))
		}),
})}

// CosOfReal — on the reals the cosine is ℝ's, as the exponential is.
var CosOfReal = cosOfRealThm{family.Add(registry.ProofEntry{
	Name: "CosOfReal",
	Key:  "prop_3ce9564fd0c89f3",
	Build: family.Theorem("∀x:real. cos(complex_of_real(x)) = complex_of_real(cos(x))",
		func(arg *Argument, x *Expr[Real]) {
			terms := arg.Have(
				"ℝ's series at x, carried into ℂ, is ℂ's at the embedded x",
				"(λn:num. complex_of_real(real_pow(-&1, n) * real_pow(x, 2 * n) / &factorial(2 * n))) = "+
					"(λn:num. "+
					"    complex_of_real(real_pow(-&1, n)) * "+
					"    complex_of_real(x) ^ (2 * n) / "+
					"    complex_of_real(&factorial(2 * n)))",
				Funext(),
				arg.ForEach(func(*Expr[Nat]) Action {
					return Chain(Simp(
						Fwd(complex_field.OfRealDiv),
						Fwd(complex_field.OfRealMul),
						Fwd(complex_field.OfRealPow)), Refl())
				}))
			embedded := arg.Have(
				"so ℂ's series at the embedded x sums to the embedded cos(x)",
				"complex_sums(λn:num. "+
					"        complex_of_real(real_pow(-&1, n)) * "+
					"        complex_of_real(x) ^ (2 * n) / "+
					"        complex_of_real(&factorial(2 * n)), "+
					"    complex_of_real(cos(x)))",
				terms.RwRev(),
				By(real_trigonometry.CosSums.At(x), complex_series.SumsOfReal))
			arg.Show(
				"it sums to cos of the embedded x as well, and a series has one sum",
				By(embedded, CosSums.At(arg.TermAs[Complex]("complex_of_real(x)")), complex_series.SumsUnique))
		}),
})}

// SinOfReal — on the reals the sine is ℝ's, as the cosine is.
var SinOfReal = sinOfRealThm{family.Add(registry.ProofEntry{
	Name: "SinOfReal",
	Key:  "prop_abdaf5d592837435",
	Build: family.Theorem("∀x:real. sin(complex_of_real(x)) = complex_of_real(sin(x))",
		func(arg *Argument, x *Expr[Real]) {
			terms := arg.Have(
				"ℝ's series at x, carried into ℂ, is ℂ's at the embedded x",
				"(λn:num. complex_of_real(real_pow(-&1, n) * real_pow(x, 2 * n + 1) / &factorial(2 * n + 1))) = "+
					"(λn:num. "+
					"    complex_of_real(real_pow(-&1, n)) * "+
					"    complex_of_real(x) ^ (2 * n + 1) / "+
					"    complex_of_real(&factorial(2 * n + 1)))",
				Funext(),
				arg.ForEach(func(*Expr[Nat]) Action {
					return Chain(Simp(
						Fwd(complex_field.OfRealDiv),
						Fwd(complex_field.OfRealMul),
						Fwd(complex_field.OfRealPow)), Refl())
				}))
			embedded := arg.Have(
				"so ℂ's series at the embedded x sums to the embedded sin(x)",
				"complex_sums(λn:num. "+
					"        complex_of_real(real_pow(-&1, n)) * "+
					"        complex_of_real(x) ^ (2 * n + 1) / "+
					"        complex_of_real(&factorial(2 * n + 1)), "+
					"    complex_of_real(sin(x)))",
				terms.RwRev(),
				By(real_trigonometry.SinSums.At(x), complex_series.SumsOfReal))
			arg.Show(
				"it sums to sin of the embedded x as well, and a series has one sum",
				By(embedded, SinSums.At(arg.TermAs[Complex]("complex_of_real(x)")), complex_series.SumsUnique))
		}),
})}

// ExpZero — the exponential is 1 at 0, as ℝ's is.
var ExpZero = expZeroThm{family.Add(registry.ProofEntry{
	Name: "ExpZero",
	Key:  "prop_2f06a4f97cf59c14",
	Build: family.Theorem("exp(complex_of_real(&0)) = complex_of_real(&1)",
		func(arg *Argument) {
			arg.Show(
				"0 is real, and ℝ's exponential is 1 there",
				Simp(Fwd(ExpOfReal), Fwd(real_exp_log.ExpZero)),
				Refl())
		}),
})}

// CosZero — the cosine is 1 at 0, as ℝ's is.
var CosZero = cosZeroThm{family.Add(registry.ProofEntry{
	Name: "CosZero",
	Key:  "prop_371ce941ab341fe6",
	Build: family.Theorem("cos(complex_of_real(&0)) = complex_of_real(&1)",
		func(arg *Argument) {
			arg.Show(
				"0 is real, and ℝ's cosine is 1 there",
				Simp(Fwd(CosOfReal), Fwd(real_trigonometry.CosZero)),
				Refl())
		}),
})}

// SinZero — the sine is 0 at 0, as ℝ's is.
var SinZero = sinZeroThm{family.Add(registry.ProofEntry{
	Name: "SinZero",
	Key:  "prop_c829791c1916725c",
	Build: family.Theorem("sin(complex_of_real(&0)) = complex_of_real(&0)",
		func(arg *Argument) {
			arg.Show(
				"0 is real, and ℝ's sine is 0 there",
				Simp(Fwd(SinOfReal), Fwd(real_trigonometry.SinZero)),
				Refl())
		}),
})}
