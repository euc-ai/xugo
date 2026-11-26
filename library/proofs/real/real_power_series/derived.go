// derived.go — the derived and the integrated series: inside the
// interval where a power series converges, so do the series of its
// termwise derivatives and of its termwise antiderivatives.

package real_power_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/registry"
)

// PowerSeriesDerivedConverges — inside the interval where a power series
// converges, its derived series Σ (n + 1)·a(n + 1)·xⁿ converges
// absolutely. Take a point ρ between |x| and R at which the series
// without its first term converges absolutely. The tangent line of tⁿ⁺¹
// at |x| gives (n + 1)·|x|ⁿ·(ρ − |x|) ≤ ρⁿ⁺¹, so each term is at most
// |a(n + 1)·ρⁿ⁺¹|/(ρ − |x|) in size; those bounds are the convergent
// series of sizes at ρ, scaled by 1/(ρ − |x|).
var PowerSeriesDerivedConverges = powerSeriesDerivedConvergesThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesDerivedConverges",
	Key:  "prop_ee543324985b4c49",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀R x:real.",
		Hypotheses: []string{
			"∀y:real. |y| < R ⇒ ∃s:real. real_sums(λn:num. a(n) * real_pow(y, n), s)",
			"|x| < R",
		},
		Conclusion: "∃s:real. real_sums(λn:num. |&(n + 1) * a(n + 1) * real_pow(x, n)|, s)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], R, x *Expr[Real], converges, inside Fact) {
			ρ, _, beyond := arg.Obtain2As[Real, Real](
				"between |x| and R lies a point ρ where the series "+
					"without its first term converges absolutely, to t",
				"∃ρ t:real. |x| < ρ ∧ ρ < R ∧ real_sums(λn:num. |a(n + 1) * real_pow(ρ, n + 1)|, t)",
				By(converges, inside, PowerSeriesAbsoluteBeyond.At(a, R, x)))
			between := arg.Have(
				"ρ lies beyond |x| ≥ 0, so being nonnegative it is its own size",
				"|x| < ρ ∧ &0 ≤ ρ ∧ |ρ| = ρ",
				ByArith(beyond))
			dominating := arg.Have(
				"scaled by 1/(ρ − |x|), that series sums to the same multiple of t",
				"real_sums(λn:num. real_inv(ρ - |x|) * |a(n + 1) * real_pow(ρ, n + 1)|, real_inv(ρ - |x|) * t)",
				By(beyond, real_series.SumsScale))
			termwise := arg.Have(
				"each term of the derived series is at most |a(n + 1)·ρⁿ⁺¹|/(ρ − |x|) in size",
				"∀n:num. "+
					"    |&(n + 1) * a(n + 1) * real_pow(x, n)| ≤ real_inv(ρ - |x|) * |a(n + 1) * real_pow(ρ, n + 1)|",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					absX := d.TermAs[Real]("|x|")
					next := d.TermAs[Nat]("n + 1")
					tangent := d.Have(
						"the tangent line of tⁿ⁺¹ at |x|, read at ρ: (n + 1)·|x|ⁿ·(ρ − |x|) ≤ ρⁿ⁺¹",
						"&(n + 1) * real_pow(|x|, n) * (ρ - |x|) ≤ real_pow(ρ, n + 1)",
						ByArith(
							between,
							real_sgn_abs.AbsNonneg.At(x),
							real_pow.PowNonneg.At(absX, next),
							real_pow.PowAboveTangentLine.At(absX, ρ, n)))
					weighted := d.Have(
						"times |a(n + 1)|: the term at x, times ρ − |x|, is at most |a(n + 1)·ρⁿ⁺¹|",
						"|&(n + 1) * a(n + 1) * real_pow(x, n)| * (ρ - |x|) ≤ |a(n + 1) * real_pow(ρ, n + 1)|",
						ByArith(
							between,
							tangent,
							real_pow.AbsPow.At(x, n),
							real_pow.AbsPow.At(ρ, next),
							real_sgn_abs.AbsNonneg.At(a.Apply(next)),
							real_order_ring.LessEqMulLeft.At(
								d.TermAs[Real]("|a(n + 1)|"),
								d.TermAs[Real]("&(n + 1) * real_pow(|x|, n) * (ρ - |x|)"),
								d.TermAs[Real]("real_pow(ρ, n + 1)"))))
					quotient := d.Have(
						"ρ − |x| is positive, so it divides out",
						"|&(n + 1) * a(n + 1) * real_pow(x, n)| ≤ |a(n + 1) * real_pow(ρ, n + 1)| / (ρ - |x|)",
						ByArith(weighted, between))
					d.Show(
						"a quotient is a product with the inverse",
						ByArith(quotient))
				}))
			arg.Show(
				"the derived series of sizes is dominated termwise "+
					"by a series with a sum, so it has one by comparison",
				By(
					termwise,
					dominating,
					real_sgn_abs.AbsIdempotent,
					real_series.Comparison.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. |&(n + 1) * a(n + 1) * real_pow(x, n)|"),
						arg.TermAs[Fun[Nat, Real]]("λn:num. real_inv(ρ - |x|) * |a(n + 1) * real_pow(ρ, n + 1)|"),
						arg.TermAs[Real]("real_inv(ρ - |x|) * t"),
						arg.TermAs[Nat]("0"))))
		}),
})}

// PowerSeriesIntegratedConverges — inside the interval where a power
// series converges, its integrated series Σ a(n)·xⁿ⁺¹/(n + 1) converges.
// The series converges absolutely at x, and each term of the integrated
// series is at most |x| times the size |a(n)·xⁿ|, dividing by n + 1 ≥ 1
// only shrinking it; |x| times a convergent series converges, and the
// comparison test applies.
var PowerSeriesIntegratedConverges = powerSeriesIntegratedConvergesThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesIntegratedConverges",
	Key:  "prop_5397be40c6217907",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀R x:real.",
		Hypotheses: []string{
			"∀y:real. |y| < R ⇒ ∃s:real. real_sums(λn:num. a(n) * real_pow(y, n), s)",
			"|x| < R",
		},
		Conclusion: "∃s:real. real_sums(λn:num. a(n) * real_pow(x, n + 1) / &(n + 1), s)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], R, x *Expr[Real], converges, inside Fact) {
			_, sizes := arg.ObtainAs[Real](
				"the series converges absolutely at x",
				"∃t:real. real_sums(λn:num. |a(n) * real_pow(x, n)|, t)",
				By(converges, inside, PowerSeriesAbsoluteInside.At(a, R, x)))
			scaled := arg.Have(
				"|x| times the series of sizes sums to |x|·t",
				"real_sums(λn:num. |x| * |a(n) * real_pow(x, n)|, |x| * t)",
				By(sizes, real_series.SumsScale))
			termwise := arg.Have(
				"each term of the integrated series is at most |x|·|a(n)·xⁿ| in size",
				"∀n:num. |a(n) * real_pow(x, n + 1) / &(n + 1)| ≤ |x| * |a(n) * real_pow(x, n)|",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					bound := d.TermAs[Real]("|x| * |a(n) * real_pow(x, n)|")
					index := d.TermAs[Real]("&(n + 1)")
					shift := d.Have(
						"|a(n)·xⁿ⁺¹| is |x|·|a(n)·xⁿ|",
						"|a(n) * real_pow(x, n + 1)| = |x| * |a(n) * real_pow(x, n)|",
						ByArith(real_pow.PowAddOne.At(x, n)))
					sign := d.Have(
						"which is nonnegative",
						"&0 ≤ |x| * |a(n) * real_pow(x, n)|",
						ByArith())
					atLeastOne := d.Have(
						"n + 1 is at least 1",
						"&1 ≤ &(n + 1)",
						ByArith())
					grown := d.Have(
						"so |a(n)·xⁿ⁺¹| is at most (n + 1)·|x|·|a(n)·xⁿ|",
						"|a(n) * real_pow(x, n + 1)| ≤ |x| * |a(n) * real_pow(x, n)| * &(n + 1)",
						ByArith(
							shift,
							sign,
							atLeastOne,
							real_order_ring.LessEqMulLeft.At(bound, d.TermAs[Real]("&1"), index)))
					d.Show(
						"dividing by n + 1 brings it below |x|·|a(n)·xⁿ|",
						Simp(Fwd(real_sgn_abs.AbsDiv), Fwd(real_sgn_abs.AbsOfNum)),
						ByArith(grown, atLeastOne))
				}))
			arg.Show(
				"the integrated series is dominated termwise by a series with a sum, so it has one by comparison",
				By(
					termwise,
					scaled,
					real_series.Comparison.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. a(n) * real_pow(x, n + 1) / &(n + 1)"),
						arg.TermAs[Fun[Nat, Real]]("λn:num. |x| * |a(n) * real_pow(x, n)|"),
						arg.TermAs[Real]("|x| * t"),
						arg.TermAs[Nat]("0"))))
		}),
})}
