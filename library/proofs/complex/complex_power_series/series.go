// series.go — Abel's lemma in the plane: a power series whose terms stay
// bounded at r converges absolutely at every point of smaller modulus,
// and so a power series converging on the disc |z| < R converges
// absolutely there.

package complex_power_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/registry"
)

// PowerSeriesAbelBounded — Abel's lemma: when the terms a(n)·rⁿ stay
// bounded by B, the series converges absolutely at every z of smaller
// modulus than r. With q = |z|/|r|, which lies in ⟦0, 1⟭, each
// |a(n)·zⁿ| is |a(n)·rⁿ|·qⁿ ≤ B·qⁿ, and B times the geometric series of q
// has a sum.
var PowerSeriesAbelBounded = powerSeriesAbelBoundedThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesAbelBounded",
	Key:  "prop_7471ec3a92a7ac2c",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀r:complex. ∀B:real. ∀z:complex.",
		Hypotheses: []string{
			"∀n:num. |a(n) * r ^ n| ≤ B",
			"|z| < |r|",
		},
		Conclusion: "∃s:real. real_sums(λn:num. |a(n) * z ^ n|, s)",
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Complex],
			r *Expr[Complex],
			B *Expr[Real],
			z *Expr[Complex],
			bounded, inside Fact,
		) {
			positive := arg.Have(
				"r is not 0: |r| exceeds |z| ≥ 0",
				"&0 < |r|",
				ByArith(inside, complex_abs.AbsNonneg.At(z)))
			q, qDef := arg.LetAs[Real]("q", "|z| / |r|")
			scaled := arg.Have(
				"|z| is q times |r|",
				"|z| = q * |r|",
				By(
					qDef,
					positive,
					real_order_field.EqDivMulLeft.At(q, arg.TermAs[Real]("|z|"), arg.TermAs[Real]("|r|"))))
			ratio := arg.Have(
				"so q lies in ⟦0, 1⟭, as |z| < |r|",
				"&0 ≤ q ∧ q < &1",
				ByArith(scaled, inside, positive, complex_abs.AbsNonneg.At(z)))
			termwise := arg.Have(
				"each |a(n)·zⁿ| is at most B·qⁿ",
				"∀n:num. |a(n) * z ^ n| ≤ B * real_pow(q, n)",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					split := d.Have(
						"|zⁿ| = qⁿ·|r|ⁿ, so the size of the term at z is its size at r times qⁿ",
						"|a(n) * z ^ n| = |a(n) * r ^ n| * real_pow(q, n)",
						Simp(Fwd(complex_abs.AbsMul), Fwd(complex_abs.AbsPow)),
						scaled.Rw(),
						Simp(Fwd(real_pow.MulPowDistrib)),
						ByArith())
					d.Show(
						"the size at r is at most B, and qⁿ ≥ 0",
						ByArith(bounded.At(n), split, ratio, real_pow.PowNonneg.At(q, n)))
				}))
			small := arg.Have(
				"q is below 1 in size",
				"|q| < &1",
				ByArith(ratio))
			geometric := arg.Have(
				"B times the geometric series of q sums to B·(1 − q)⁻¹",
				"real_sums(λn:num. B * real_pow(q, n), B * real_inv(&1 - q))",
				By(small, real_series.Geometric.At(q), real_series.SumsScale))
			arg.Show(
				"the sizes, being nonnegative, are dominated termwise by it "+
					"from the first index on, so they have a sum by comparison",
				By(
					termwise,
					geometric,
					complex_abs.AbsNonneg,
					real_sgn_abs.AbsFixedIffNonneg,
					real_series.Comparison.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. |a(n) * z ^ n|"),
						arg.TermAs[Fun[Nat, Real]]("λn:num. B * real_pow(q, n)"),
						arg.TermAs[Real]("B * real_inv(&1 - q)"),
						arg.TermAs[Nat]("0"))))
		}),
})}

// PowerSeriesAbel — Abel's lemma for a series that converges at r: it
// converges absolutely at every z of smaller modulus than r. The real
// parts and the imaginary parts of the terms a(n)·rⁿ are convergent real
// series, so each is bounded; a complex number is at most the sum of the
// sizes of its parts, so the terms are bounded, and the bounded form
// applies.
var PowerSeriesAbel = powerSeriesAbelThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesAbel",
	Key:  "prop_250a91f9983d5e7d",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀r z:complex.",
		Hypotheses: []string{
			"∃s:complex. complex_sums(λn:num. a(n) * r ^ n, s)",
			"|z| < |r|",
		},
		Conclusion: "∃s:real. real_sums(λn:num. |a(n) * z ^ n|, s)",
	},
		func(arg *Argument, a *Arrow[Nat, Complex], r, z *Expr[Complex], converges, inside Fact) {
			_, sum := arg.UnpackAs[Complex](converges)
			parts := arg.Have(
				"the real parts of the terms sum to re(s), and the imaginary parts to im(s)",
				"real_sums(λn:num. re(a(n) * r ^ n), re(s)) ∧ real_sums(λn:num. im(a(n) * r ^ n), im(s))",
				By(sum, complex_series.ComplexSumsDef))
			_, reBounded := arg.ObtainAs[Real](
				"the real parts converge, so they are bounded",
				"∃B₁:real. ∀n:num. |re(a(n) * r ^ n)| ≤ B₁",
				By(parts, real_series.SumsTermsBounded))
			_, imBounded := arg.ObtainAs[Real](
				"the imaginary parts converge too, so they are bounded",
				"∃B₂:real. ∀n:num. |im(a(n) * r ^ n)| ≤ B₂",
				By(parts, real_series.SumsTermsBounded))
			bounded := arg.Have(
				"a term is at most the sum of the sizes of its parts, so B₁ + B₂ bounds the terms",
				"∀n:num. |a(n) * r ^ n| ≤ B₁ + B₂",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					d.Show(
						"the size of a(n)·rⁿ is at most the sum of its parts' sizes, each within its bound",
						ByArith(
							reBounded.At(n),
							imBounded.At(n),
							complex_abs.AbsLeParts.At(d.TermAs[Complex]("a(n) * r ^ n"))))
				}))
			arg.Show(
				"so the bounded form of Abel's lemma applies at r",
				By(bounded, inside, PowerSeriesAbelBounded.At(a, r, arg.TermAs[Real]("B₁ + B₂"), z)))
		}),
})}

// PowerSeriesAbsoluteInside — a power series that converges at every
// point of the disc |w| < R converges absolutely there: for |z| < R the
// real number r = (|z| + R)/2, read as a complex number, has modulus
// strictly between |z| and R, the series converges at r, and Abel's
// lemma at r applies.
var PowerSeriesAbsoluteInside = powerSeriesAbsoluteInsideThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesAbsoluteInside",
	Key:  "prop_d2cfbb55a163ee1d",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀R:real. ∀z:complex.",
		Hypotheses: []string{
			"∀w:complex. |w| < R ⇒ ∃s:complex. complex_sums(λn:num. a(n) * w ^ n, s)",
			"|z| < R",
		},
		Conclusion: "∃s:real. real_sums(λn:num. |a(n) * z ^ n|, s)",
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Complex],
			R *Expr[Real],
			z *Expr[Complex],
			converges, inside Fact,
		) {
			r, rDef := arg.LetAs[Complex]("r", "&((|z| + R) / &2)")
			between := arg.Have(
				"r is real and halfway between |z| and R, so its modulus lies strictly between them",
				"|z| < |r| ∧ |r| < R",
				ByArith(
					rDef,
					inside,
					complex_abs.AbsOfReal.At(arg.TermAs[Real]("(|z| + R) / &2")),
					complex_abs.AbsNonneg.At(z)))
			arg.Show(
				"the series converges at r, and Abel's lemma at r applies",
				By(between, converges.At(r), PowerSeriesAbel.At(a, r, z)))
		}),
})}

// PowerSeriesAbsoluteBeyond — inside the disc where a power series
// converges, between each |z| < R and R lies a radius ρ at which the
// series without its first term converges absolutely: ρ = (|z| + R)/2
// lies strictly between |z| and R, the series converges absolutely at the
// real point ρ, and dropping the first term |a(0)| of the series of sizes
// drops it from the sum.
var PowerSeriesAbsoluteBeyond = powerSeriesAbsoluteBeyondThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesAbsoluteBeyond",
	Key:  "prop_9f859cfd9b765510",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀R:real. ∀z:complex.",
		Hypotheses: []string{
			"∀w:complex. |w| < R ⇒ ∃s:complex. complex_sums(λn:num. a(n) * w ^ n, s)",
			"|z| < R",
		},
		Conclusion: "∃ρ t:real. |z| < ρ ∧ ρ < R ∧ real_sums(λn:num. |a(n + 1) * &ρ ^ (n + 1)|, t)",
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Complex],
			R *Expr[Real],
			z *Expr[Complex],
			converges, inside Fact,
		) {
			ρ, ρDef := arg.LetAs[Real]("ρ", "(|z| + R) / &2")
			between := arg.Have(
				"ρ lies strictly between |z| and R, and is the modulus of ρ read in ℂ",
				"|z| < ρ ∧ ρ < R ∧ |&ρ| < R",
				ByArith(ρDef, inside, complex_abs.AbsOfReal.At(ρ), complex_abs.AbsNonneg.At(z)))
			_, sizes := arg.ObtainAs[Real](
				"the series converges absolutely at ρ",
				"∃t:real. real_sums(λn:num. |a(n) * &ρ ^ n|, t)",
				By(converges, between, PowerSeriesAbsoluteInside.At(a, R, arg.TermAs[Complex]("&ρ"))))
			first := arg.Have(
				"the first size is |a(0)·1| = |a(0)|",
				"|a(0) * &ρ ^ 0| = |a(0)|",
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				ByArith(
					complex_abs.AbsMul.At(a.Apply(arg.TermAs[Nat]("0")), arg.TermAs[Complex]("&1")),
					complex_abs.AbsOfReal.At(arg.TermAs[Real]("&1"))))
			arg.Take(ρ)
			arg.Take(arg.TermAs[Real]("t - |a(0)|"))
			arg.Show(
				"dropping the first term |a(0)| from the series of sizes drops it from the sum",
				ByArith(sizes, between, first, real_series.SumsShift))
		}),
})}

// PowerSeriesDerivedConverges — inside the disc where a power series
// converges, its derived series Σ (n + 1)·a(n + 1)·zⁿ converges
// absolutely. Take a radius ρ between |z| and R at which the series
// without its first term converges absolutely. The tangent line of tⁿ⁺¹
// at |z| gives (n + 1)·|z|ⁿ·(ρ − |z|) ≤ ρⁿ⁺¹, so each term is at most
// |a(n + 1)·ρⁿ⁺¹|/(ρ − |z|) in size; those bounds are the convergent
// series of sizes at ρ, scaled by 1/(ρ − |z|).
var PowerSeriesDerivedConverges = powerSeriesDerivedConvergesThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesDerivedConverges",
	Key:  "prop_638d4103b3cca67f",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀R:real. ∀z:complex.",
		Hypotheses: []string{
			"∀w:complex. |w| < R ⇒ ∃s:complex. complex_sums(λn:num. a(n) * w ^ n, s)",
			"|z| < R",
		},
		Conclusion: "∃s:real. real_sums(λn:num. |complex_of_real(&(n + 1)) * a(n + 1) * z ^ n|, s)",
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Complex],
			R *Expr[Real],
			z *Expr[Complex],
			converges, inside Fact,
		) {
			ρ, _, beyond := arg.Obtain2As[Real, Real](
				"between |z| and R lies a radius ρ where the series "+
					"without its first term converges absolutely, to t",
				"∃ρ t:real. |z| < ρ ∧ ρ < R ∧ real_sums(λn:num. |a(n + 1) * &ρ ^ (n + 1)|, t)",
				By(converges, inside, PowerSeriesAbsoluteBeyond.At(a, R, z)))
			between := arg.Have(
				"ρ lies beyond |z| ≥ 0, so being nonnegative it is its own size",
				"|z| < ρ ∧ &0 ≤ ρ ∧ |ρ| = ρ",
				ByArith(beyond, complex_abs.AbsNonneg.At(z)))
			dominating := arg.Have(
				"scaled by 1/(ρ − |z|), that series sums to the same multiple of t",
				"real_sums(λn:num. real_inv(ρ - |z|) * |a(n + 1) * &ρ ^ (n + 1)|, real_inv(ρ - |z|) * t)",
				By(beyond, real_series.SumsScale))
			termwise := arg.Have(
				"each term of the derived series is at most |a(n + 1)·ρⁿ⁺¹|/(ρ − |z|) in size",
				"∀n:num. "+
					"    |complex_of_real(&(n + 1)) * a(n + 1) * z ^ n| ≤ "+
					"    real_inv(ρ - |z|) * |a(n + 1) * &ρ ^ (n + 1)|",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					absZ := d.TermAs[Real]("|z|")
					next := d.TermAs[Nat]("n + 1")
					tangent := d.Have(
						"the tangent line of tⁿ⁺¹ at |z|, read at ρ: (n + 1)·|z|ⁿ·(ρ − |z|) ≤ ρⁿ⁺¹",
						"&(n + 1) * real_pow(|z|, n) * (ρ - |z|) ≤ real_pow(ρ, n + 1)",
						ByArith(
							between,
							complex_abs.AbsNonneg.At(z),
							real_pow.PowNonneg.At(absZ, next),
							real_pow.PowAboveTangentLine.At(absZ, ρ, n)))
					sizeAtZ := d.Have(
						"the term at z has size (n + 1)·|a(n + 1)|·|z|ⁿ",
						"|complex_of_real(&(n + 1)) * a(n + 1) * z ^ n| = &(n + 1) * |a(n + 1)| * real_pow(|z|, n)",
						Simp(
							Fwd(complex_abs.AbsMul),
							Fwd(complex_abs.AbsPow),
							Fwd(complex_abs.AbsOfReal),
							Fwd(real_sgn_abs.AbsOfNum)),
						ByArith())
					sizeAtRho := d.Have(
						"and the term at ρ has size |a(n + 1)|·ρⁿ⁺¹",
						"|a(n + 1) * &ρ ^ (n + 1)| = |a(n + 1)| * real_pow(ρ, n + 1)",
						Simp(Fwd(complex_abs.AbsMul), Fwd(complex_abs.AbsPow), Fwd(complex_abs.AbsOfReal)),
						ByArith(between))
					weighted := d.Have(
						"times |a(n + 1)|: the term at z, times ρ − |z|, is at most the term at ρ in size",
						"|complex_of_real(&(n + 1)) * a(n + 1) * z ^ n| * (ρ - |z|) ≤ |a(n + 1) * &ρ ^ (n + 1)|",
						ByArith(
							tangent,
							sizeAtZ,
							sizeAtRho,
							complex_abs.AbsNonneg.At(a.Apply(next)),
							real_order_ring.LessEqMulLeft.At(
								d.TermAs[Real]("|a(n + 1)|"),
								d.TermAs[Real]("&(n + 1) * real_pow(|z|, n) * (ρ - |z|)"),
								d.TermAs[Real]("real_pow(ρ, n + 1)"))))
					quotient := d.Have(
						"ρ − |z| is positive, so it divides out",
						"|complex_of_real(&(n + 1)) * a(n + 1) * z ^ n| ≤ |a(n + 1) * &ρ ^ (n + 1)| / (ρ - |z|)",
						ByArith(weighted, between))
					d.Show(
						"a quotient is a product with the inverse",
						ByArith(quotient))
				}))
			arg.Show(
				"the derived series of sizes is dominated termwise, from the first "+
					"index on, by a series with a sum, so it has one by comparison",
				By(
					termwise,
					dominating,
					complex_abs.AbsNonneg,
					real_sgn_abs.AbsFixedIffNonneg,
					real_series.Comparison.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. |complex_of_real(&(n + 1)) * a(n + 1) * z ^ n|"),
						arg.TermAs[Fun[Nat, Real]]("λn:num. real_inv(ρ - |z|) * |a(n + 1) * &ρ ^ (n + 1)|"),
						arg.TermAs[Real]("real_inv(ρ - |z|) * t"),
						arg.TermAs[Nat]("0"))))
		}),
})}
