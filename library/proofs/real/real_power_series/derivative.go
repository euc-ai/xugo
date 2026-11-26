// derivative.go — term-by-term differentiation: inside the interval
// where a power series converges, its sum has a derivative, the sum of
// the derived series.

package real_power_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// PowRemainderBound — the first-order expansion of (c + h)ⁿ⁺¹ at c has a
// quadratic remainder: for |h| ≤ δ the remainder
// Gₙ = (c + h)ⁿ⁺¹ − cⁿ⁺¹ − (n + 1)·cⁿ·h is at most (h/δ)²·(|c| + δ)ⁿ⁺¹ in
// size. It obeys Gₙ₊₁ = (c + h)·Gₙ + (n + 1)·cⁿ·h², and the same
// remainder Fₙ of (|c| + δ)ⁿ⁺¹ at |c| obeys Fₙ₊₁ = (|c| + δ)·Fₙ +
// (n + 1)·|c|ⁿ·δ². As |c + h| ≤ |c| + δ, induction on n gives
// δ²·|Gₙ| ≤ h²·Fₙ, and Fₙ is at most (|c| + δ)ⁿ⁺¹.
var PowRemainderBound = powRemainderBoundThm{family.Add(registry.ProofEntry{
	Name: "PowRemainderBound",
	Key:  "prop_44400d48b20278e5",
	Build: family.Theorem(Statement{
		Binders: "∀c h δ:real. ∀n:num.",
		Hypotheses: []string{
			"|h| ≤ δ",
		},
		Conclusion: "real_pow(δ, 2) * |«powRemainder»(c, h, n)| ≤ " +
			"real_pow(h, 2) * real_pow(|c| + δ, n + 1)",
		Abbrev: Abbrev{
			{Name: "powRemainder", Text: "λx:real. λy:real. λk:num. " +
				"    real_pow(x + y, k + 1) - real_pow(x, k + 1) - &(k + 1) * real_pow(x, k) * y"},
		},
	},
		func(arg *Argument, c, h, δ *Expr[Real], small Fact) {
			nonneg := arg.Have(
				"δ is at least |h| ≥ 0",
				"&0 ≤ δ",
				ByArith(small))
			dominated := arg.Have(
				"δ² times the remainder of (c + h)ⁿ⁺¹ is at most h² times that of (|c| + δ)ⁿ⁺¹, by induction on n",
				"∀n:num. real_pow(δ, 2) * |«powRemainder»(c, h, n)| ≤ real_pow(h, 2) * «powRemainder»(|c|, δ, n)",
				Derive(func(d *Argument) {
					d.Induct("n")
					d.Base(
						"at n = 0 both remainders vanish",
						func(b *Argument) {
							vanishes := b.Have(
								"(c + h) − c − h = 0",
								"«powRemainder»(c, h, 0) = &0",
								ByArith())
							b.Show(
								"and so does the comparison remainder",
								vanishes.Rw(),
								ByArith())
						})
					d.Step(
						"each remainder at n + 1 is the next base times "+
							"the one at n, plus (n + 1)·cⁿ·h² or (n + 1)·|c|ⁿ·δ²",
						func(b *Argument, ih Fact) {
							n := b.TermAs[Nat]("n")
							recurrence := b.Have(
								"the remainder of (c + h)ⁿ⁺² is (c + h) times that of (c + h)ⁿ⁺¹, plus (n + 1)·cⁿ·h²",
								"«powRemainder»(c, h, suc(n)) = "+
									"(c + h) * «powRemainder»(c, h, n) + &(n + 1) * real_pow(c, n) * real_pow(h, 2)",
								Simp(Fwd(nat_arith.Add1), Fwd(real_pow.PowAddOne), Fwd(real_construction.OfNumAdd)),
								ByArith())
							comparison := b.Have(
								"the remainder of (|c| + δ)ⁿ⁺² is (|c| + δ) times that of (|c| + δ)ⁿ⁺¹, plus (n + 1)·|c|ⁿ·δ²",
								"«powRemainder»(|c|, δ, suc(n)) = "+
									"(|c| + δ) * «powRemainder»(|c|, δ, n) + &(n + 1) * real_pow(|c|, n) * real_pow(δ, 2)",
								Simp(Fwd(nat_arith.Add1), Fwd(real_pow.PowAddOne), Fwd(real_construction.OfNumAdd)),
								ByArith())
							G, _ := b.LetAs[Real]("G", "«powRemainder»(c, h, n)")
							b.LetAs[Real]("F", "«powRemainder»(|c|, δ, n)")
							widened := b.Have(
								"|c + h| ≤ |c| + δ",
								"|c + h| ≤ |c| + δ",
								ByArith(small))
							triangle := b.Have(
								"by the triangle inequality the next remainder is at most |c + h|·|G| + (n + 1)·|c|ⁿ·h² in size",
								"|(c + h) * G + &(n + 1) * real_pow(c, n) * real_pow(h, 2)| ≤ "+
									"|c + h| * |G| + &(n + 1) * real_pow(|c|, n) * real_pow(h, 2)",
								ByArith(
									real_sgn_abs.AbsTriangle.At(
										b.TermAs[Real]("(c + h) * G"),
										b.TermAs[Real]("&(n + 1) * real_pow(c, n) * real_pow(h, 2)")),
									real_pow.AbsPow.At(c, n)))
							size := b.Have(
								"so at most (|c| + δ)·|G| + (n + 1)·|c|ⁿ·h²",
								"|(c + h) * G + &(n + 1) * real_pow(c, n) * real_pow(h, 2)| ≤ "+
									"(|c| + δ) * |G| + &(n + 1) * real_pow(|c|, n) * real_pow(h, 2)",
								ByArith(widened, triangle, real_sgn_abs.AbsNonneg.At(G)))
							b.Show(
								"scaled by δ², that is at most (|c| + δ)·h²·F + (n + 1)·|c|ⁿ·h²·δ², by the induction hypothesis",
								recurrence.Rw(),
								comparison.Rw(),
								ByArith(
									size,
									nonneg,
									ih,
									real_sgn_abs.AbsNonneg.At(c),
									real_pow.PowTwoNonneg.At(δ),
									real_order_ring.LessEqMulLeft.At(
										b.TermAs[Real]("real_pow(δ, 2)"),
										b.TermAs[Real]("|(c + h) * G + &(n + 1) * real_pow(c, n) * real_pow(h, 2)|"),
										b.TermAs[Real]("(|c| + δ) * |G| + &(n + 1) * real_pow(|c|, n) * real_pow(h, 2)")),
									real_order_ring.LessEqMulLeft.At(
										b.TermAs[Real]("|c| + δ"),
										b.TermAs[Real]("real_pow(δ, 2) * |G|"),
										b.TermAs[Real]("real_pow(h, 2) * F"))))
						})
				}))
			n := arg.FixAs[Nat]()
			coefficient := arg.Have(
				"(n + 1)·|c|ⁿ is nonnegative",
				"&0 ≤ &(n + 1) * real_pow(|c|, n)",
				ByArith(real_sgn_abs.AbsNonneg.At(c), real_pow.PowNonneg.At(arg.TermAs[Real]("|c|"), n)))
			dropped := arg.Have(
				"the terms the comparison remainder subtracts are nonnegative",
				"&0 ≤ real_pow(|c|, n + 1) + &(n + 1) * real_pow(|c|, n) * δ",
				ByArith(
					nonneg,
					coefficient,
					real_sgn_abs.AbsNonneg.At(c),
					real_pow.PowNonneg.At(arg.TermAs[Real]("|c|"), arg.TermAs[Nat]("n + 1"))))
			arg.Show(
				"so the comparison remainder is at most (|c| + δ)ⁿ⁺¹, and h² ≥ 0",
				ByArith(dominated.At(n), dropped, real_pow.PowTwoNonneg.At(h)))
		}),
})}

// PowerSeriesDerivative — term-by-term differentiation: inside the
// interval where a power series converges, its sum f has a derivative at
// c, the sum d of the derived series Σ (n + 1)·a(n + 1)·cⁿ. Take a point
// ρ between |c| and R at which the series without its first term
// converges absolutely, to M, and δ = ρ − |c|. For |h| < δ, dropping the
// vanishing first term of f(c + h) − f(c) and subtracting h times the
// derived series leaves f(c + h) − f(c) − h·d as the sum of the series
// a(n + 1)·Gₙ, Gₙ the remainder of the first-order expansion of
// (c + h)ⁿ⁺¹ at c. The remainder bound makes each term at most
// (h/δ)²·|a(n + 1)·ρⁿ⁺¹| in size, and those bounds sum to (h/δ)²·M: the
// increment is d·h to within a constant times h², which is a derivative.
var PowerSeriesDerivative = powerSeriesDerivativeThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesDerivative",
	Key:  "prop_9e8b5d56af7a3f5d",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀f:(real → real). ∀R c:real.",
		Hypotheses: []string{
			"∀x:real. |x| < R ⇒ real_sums(λn:num. a(n) * real_pow(x, n), f(x))",
			"|c| < R",
		},
		Conclusion: "∃d:real. " +
			"    real_sums(λn:num. &(n + 1) * a(n + 1) * real_pow(c, n), d) ∧ real_derivative_at(f, c, d)",
		Abbrev: Abbrev{
			{Name: "powRemainder", Text: "λx:real. λy:real. λk:num. " +
				"    real_pow(x + y, k + 1) - real_pow(x, k + 1) - &(k + 1) * real_pow(x, k) * y"},
			{Name: "remainderTerm", Text: "λh:real. λn:num. " +
				"    (a(n + 1) * real_pow(c + h, n + 1) - a(n + 1) * real_pow(c, n + 1)) - " +
				"    h * (&(n + 1) * a(n + 1) * real_pow(c, n))"},
		},
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Real],
			f *Arrow[Real, Real],
			R, c *Expr[Real],
			sums, inside Fact,
		) {
			zero := arg.TermAs[Nat]("0")
			converges := arg.Have(
				"the series converges at every point of ⟬−R, R⟭, to the value of f there",
				"∀y:real. |y| < R ⇒ ∃s:real. real_sums(λn:num. a(n) * real_pow(y, n), s)",
				By(Normalized, sums))
			t, derivedSizes := arg.ObtainAs[Real](
				"the derived series converges absolutely at c",
				"∃t:real. real_sums(λn:num. |&(n + 1) * a(n + 1) * real_pow(c, n)|, t)",
				By(converges, inside, PowerSeriesDerivedConverges.At(a, R, c)))
			d, derivedSum := arg.ObtainAs[Real](
				"so it converges, to d: each term is at most its own size",
				"∃d:real. real_sums(λn:num. &(n + 1) * a(n + 1) * real_pow(c, n), d)",
				By(
					derivedSizes,
					real_order_ring.LessEqRefl,
					real_series.Comparison.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. &(n + 1) * a(n + 1) * real_pow(c, n)"),
						arg.TermAs[Fun[Nat, Real]]("λn:num. |&(n + 1) * a(n + 1) * real_pow(c, n)|"),
						t,
						zero)))

			ρ, _, beyond := arg.Obtain2As[Real, Real](
				"between |c| and R lies a point ρ where the series "+
					"without its first term converges absolutely, to M",
				"∃ρ M:real. |c| < ρ ∧ ρ < R ∧ real_sums(λn:num. |a(n + 1) * real_pow(ρ, n + 1)|, M)",
				By(converges, inside, PowerSeriesAbsoluteBeyond.At(a, R, c)))
			δ, δDef := arg.LetAs[Real]("δ", "ρ - |c|")
			radius := arg.Have(
				"δ is positive, and ρ = |c| + δ is nonnegative, so its own size",
				"&0 < δ ∧ ρ = |c| + δ ∧ &0 ≤ ρ ∧ |ρ| = ρ",
				ByArith(δDef, beyond))

			quadratic := arg.Have(
				"for |h| < δ the increment f(c + h) − f(c) is d·h to within M/δ²·h²",
				"∀h:real. |h| < δ ⇒ |f(c + h) - f(c) - d * h| ≤ M / real_pow(δ, 2) * real_pow(h, 2)",
				Derive(func(e *Argument) {
					h := e.FixAs[Real]()
					small := e.Assume()
					shiftedPoint := e.TermAs[Real]("c + h")
					fShifted := e.TermAs[Real]("f(c + h)")
					fc := e.TermAs[Real]("f(c)")
					increment := e.TermAs[Real]("f(c + h) - f(c)")
					near := e.Have(
						"c + h lies in ⟬−R, R⟭, as |c + h| ≤ |c| + |h| < ρ",
						"|c + h| < R",
						ByArith(radius, beyond, small))
					difference := e.Have(
						"the series at c + h less the series at c sums to f(c + h) − f(c)",
						"real_sums(λn:num. a(n) * real_pow(c + h, n) - a(n) * real_pow(c, n), f(c + h) - f(c))",
						By(
							near,
							inside,
							sums.At(shiftedPoint),
							sums.At(c),
							real_series.SumsSub.At(
								e.TermAs[Fun[Nat, Real]]("λn:num. a(n) * real_pow(c + h, n)"),
								e.TermAs[Fun[Nat, Real]]("λn:num. a(n) * real_pow(c, n)"),
								fShifted,
								fc)))
					vanishing := e.Have(
						"its first term is a(0) − a(0) = 0",
						"f(c + h) - f(c) - (a(0) * real_pow(c + h, 0) - a(0) * real_pow(c, 0)) = f(c + h) - f(c)",
						ByArith())
					differenceShifted := e.Have(
						"so dropping that term leaves the sum unchanged",
						"real_sums(λn:num. a(n + 1) * real_pow(c + h, n + 1) - a(n + 1) * real_pow(c, n + 1), "+
							"    f(c + h) - f(c))",
						By(
							vanishing,
							difference,
							real_series.SumsShift.At(
								e.TermAs[Fun[Nat, Real]]("λn:num. a(n) * real_pow(c + h, n) - a(n) * real_pow(c, n)"),
								increment)))
					scaledDerived := e.Have(
						"h times the derived series sums to h·d",
						"real_sums(λn:num. h * (&(n + 1) * a(n + 1) * real_pow(c, n)), h * d)",
						By(derivedSum, real_series.SumsScale))
					remainder := e.Have(
						"the difference less h times the derived series sums to f(c + h) − f(c) − h·d",
						"real_sums(«remainderTerm»(h), f(c + h) - f(c) - h * d)",
						By(differenceShifted, scaledDerived, real_series.SumsSub))
					dominating := e.Have(
						"(h/δ)² times the series of sizes at ρ sums to (h/δ)²·M",
						"real_sums(λn:num. real_pow(h, 2) / real_pow(δ, 2) * |a(n + 1) * real_pow(ρ, n + 1)|, "+
							"    real_pow(h, 2) / real_pow(δ, 2) * M)",
						By(beyond, real_series.SumsScale))
					within := e.Have(
						"|h| is at most δ",
						"|h| ≤ δ",
						ByArith(small))
					termwise := e.Have(
						"each term is a(n + 1) times the remainder of (c + "+
							"h)ⁿ⁺¹ at c, at most (h/δ)²·|a(n + 1)·ρⁿ⁺¹| in size",
						"∀n:num. "+
							"    |«remainderTerm»(h, n)| ≤ real_pow(h, 2) / real_pow(δ, 2) * |a(n + 1) * real_pow(ρ, n + 1)|",
						Derive(func(k *Argument) {
							n := k.FixAs[Nat]()
							next := k.TermAs[Nat]("n + 1")
							factored := k.Have(
								"the term is a(n + 1) times the remainder Gₙ = (c + h)ⁿ⁺¹ − cⁿ⁺¹ − (n + 1)·cⁿ·h",
								"«remainderTerm»(h, n) = a(n + 1) * «powRemainder»(c, h, n)",
								ByArith())
							remainderBound := k.Have(
								"the remainder bound, δ² divided out: |Gₙ| ≤ h²·ρⁿ⁺¹/δ²",
								"|«powRemainder»(c, h, n)| ≤ real_pow(h, 2) * real_pow(ρ, n + 1) / real_pow(δ, 2)",
								ByArith(within, radius, PowRemainderBound.At(c, h, δ, n)))
							k.Show(
								"times |a(n + 1)|, with ρ its own size",
								factored.Rw(),
								ByArith(
									remainderBound,
									radius,
									real_sgn_abs.AbsNonneg.At(a.Apply(next)),
									real_pow.AbsPow.At(ρ, next),
									real_order_ring.LessEqMulLeft.At(
										k.TermAs[Real]("|a(n + 1)|"),
										k.TermAs[Real]("|«powRemainder»(c, h, n)|"),
										k.TermAs[Real]("real_pow(h, 2) * real_pow(ρ, n + 1) / real_pow(δ, 2)"))))
						}))
					total := e.Have(
						"so the increment less h·d is at most (h/δ)²·M in size",
						"|f(c + h) - f(c) - h * d| ≤ real_pow(h, 2) / real_pow(δ, 2) * M",
						By(
							termwise,
							remainder,
							dominating,
							real_series.ComparisonBound.At(
								e.TermAs[Fun[Nat, Real]]("«remainderTerm»(h)"),
								e.TermAs[Fun[Nat, Real]](
									"λn:num. real_pow(h, 2) / real_pow(δ, 2) * |a(n + 1) * real_pow(ρ, n + 1)|"),
								e.TermAs[Real]("f(c + h) - f(c) - h * d"),
								e.TermAs[Real]("real_pow(h, 2) / real_pow(δ, 2) * M"))))
					e.Show(
						"which is M/δ²·h²",
						ByArith(total))
				}))
			arg.Take(d)
			arg.Show(
				"a quadratic error on a ball makes d the derivative: "+
					"DerivativeFromQuadraticRemainder at the slope d, radius δ",
				By(
					derivedSum,
					radius,
					quadratic,
					real_derivative.DerivativeFromQuadraticRemainder.At(
						f,
						c,
						d,
						arg.TermAs[Real]("M / real_pow(δ, 2)"),
						δ)))
		}),
})}
