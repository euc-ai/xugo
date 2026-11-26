// derivative.go — term-by-term differentiation: inside the disc where a
// power series converges, its sum has a complex derivative, the sum of
// the derived series.

package complex_power_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// PowRemainderBound — the first-order expansion of (c + h)ⁿ⁺¹ at c has a
// quadratic remainder: for |h| ≤ δ the remainder
// Gₙ = (c + h)ⁿ⁺¹ − cⁿ⁺¹ − (n + 1)·cⁿ·h is at most (|h|/δ)²·(|c| + δ)ⁿ⁺¹
// in size. It obeys Gₙ₊₁ = (c + h)·Gₙ + (n + 1)·cⁿ·h², and the same
// remainder Fₙ of the real power (|c| + δ)ⁿ⁺¹ at |c| obeys
// Fₙ₊₁ = (|c| + δ)·Fₙ + (n + 1)·|c|ⁿ·δ². As |c + h| ≤ |c| + δ, induction
// on n gives δ²·|Gₙ| ≤ |h|²·Fₙ, and Fₙ is at most (|c| + δ)ⁿ⁺¹.
var PowRemainderBound = powRemainderBoundThm{family.Add(registry.ProofEntry{
	Name: "PowRemainderBound",
	Key:  "prop_eade96ff45b7ecf7",
	Build: family.Theorem(Statement{
		Binders: "∀c h:complex. ∀δ:real. ∀n:num.",
		Hypotheses: []string{
			"|h| ≤ δ",
		},
		Conclusion: "real_pow(δ, 2) * |«powRemainder»(c, h, n)| ≤ " +
			"real_pow(|h|, 2) * real_pow(|c| + δ, n + 1)",
		Abbrev: Abbrev{
			{Name: "powRemainder", Text: "λx:complex. λy:complex. λk:num. " +
				"    (x + y) ^ (k + 1) - x ^ (k + 1) - complex_of_real(&(k + 1)) * x ^ k * y"},
			{Name: "realRemainder", Text: "λx:real. λy:real. λk:num. " +
				"    real_pow(x + y, k + 1) - real_pow(x, k + 1) - &(k + 1) * real_pow(x, k) * y"},
		},
	},
		func(arg *Argument, c, h *Expr[Complex], δ *Expr[Real], small Fact) {
			nonneg := arg.Have(
				"δ is at least |h| ≥ 0",
				"&0 ≤ δ",
				ByArith(small, complex_abs.AbsNonneg.At(h)))
			dominated := arg.Have(
				"δ² times the remainder of (c + h)ⁿ⁺¹ is at most "+
					"|h|² times that of (|c| + δ)ⁿ⁺¹, by induction on n",
				"∀n:num. "+
					"    real_pow(δ, 2) * |«powRemainder»(c, h, n)| ≤ real_pow(|h|, 2) * «realRemainder»(|c|, δ, n)",
				Derive(func(d *Argument) {
					d.Induct("n")
					d.Base(
						"at n = 0 both remainders vanish",
						func(b *Argument) {
							vanishes := b.Have(
								"(c + h) − c − h = 0",
								"«powRemainder»(c, h, 0) = &0",
								Simp(
									Rev(nat_arith.Add1),
									Fwd(comm_monoid.MonoidPowDef),
									Fwd(real_ring.OfNumSuc),
									Fwd(complex_field.OfRealAdd)),
								ByArith())
							b.Show(
								"and so does the comparison remainder, and |0| = 0",
								vanishes.Rw(),
								ByArith(complex_abs.AbsOfReal.At(b.TermAs[Real]("&0"))))
						})
					d.Step(
						"each remainder at n + 1 is the next base times "+
							"the one at n, plus (n + 1)·cⁿ·h² or (n + 1)·|c|ⁿ·δ²",
						func(b *Argument, ih Fact) {
							// ℂ's power unfolds by its definition at a successor, so n + 1 is read
							// as suc(n) there; ℝ's power has its law at n + 1, so there suc(n) is
							// read as n + 1.
							recurrence := b.Have(
								"the remainder of (c + h)ⁿ⁺² is (c + h) times that of (c + h)ⁿ⁺¹, plus (n + 1)·cⁿ·h²",
								"«powRemainder»(c, h, suc(n)) = "+
									"(c + h) * «powRemainder»(c, h, n) + complex_of_real(&(n + 1)) * c ^ n * (h * h)",
								Simp(
									Rev(nat_arith.Add1),
									Fwd(comm_monoid.MonoidPowDef),
									Fwd(real_ring.OfNumSuc),
									Fwd(complex_field.OfRealAdd)),
								ByArith())
							comparison := b.Have(
								"the remainder of (|c| + δ)ⁿ⁺² is (|c| + δ) times that of (|c| + δ)ⁿ⁺¹, plus (n + 1)·|c|ⁿ·δ²",
								"«realRemainder»(|c|, δ, suc(n)) = "+
									"(|c| + δ) * «realRemainder»(|c|, δ, n) + &(n + 1) * real_pow(|c|, n) * real_pow(δ, 2)",
								Simp(Fwd(nat_arith.Add1), Fwd(real_pow.PowAddOne), Fwd(real_construction.OfNumAdd)),
								ByArith())
							G, _ := b.LetAs[Complex]("G", "«powRemainder»(c, h, n)")
							b.LetAs[Real]("F", "«realRemainder»(|c|, δ, n)")
							widened := b.Have(
								"|c + h| ≤ |c| + δ",
								"|c + h| ≤ |c| + δ",
								ByArith(small, complex_abs.AbsTriangle.At(c, h)))
							second := b.Have(
								"the added term (n + 1)·cⁿ·h² has size (n + 1)·|c|ⁿ·|h|²",
								"|complex_of_real(&(n + 1)) * c ^ n * (h * h)| = &(n + 1) * real_pow(|c|, n) * real_pow(|h|, 2)",
								Simp(
									Fwd(complex_abs.AbsMul),
									Fwd(complex_abs.AbsPow),
									Fwd(complex_abs.AbsOfReal),
									Fwd(real_sgn_abs.AbsOfNum)),
								ByArith())
							triangle := b.Have(
								"by the triangle inequality the next remainder is at most |c + h|·|G| + (n + 1)·|c|ⁿ·|h|² in size",
								"|(c + h) * G + complex_of_real(&(n + 1)) * c ^ n * (h * h)| ≤ "+
									"|c + h| * |G| + &(n + 1) * real_pow(|c|, n) * real_pow(|h|, 2)",
								ByArith(
									second,
									complex_abs.AbsTriangle.At(
										b.TermAs[Complex]("(c + h) * G"),
										b.TermAs[Complex]("complex_of_real(&(n + 1)) * c ^ n * (h * h)")),
									complex_abs.AbsMul.At(b.TermAs[Complex]("c + h"), G)))
							size := b.Have(
								"so at most (|c| + δ)·|G| + (n + 1)·|c|ⁿ·|h|²",
								"|(c + h) * G + complex_of_real(&(n + 1)) * c ^ n * (h * h)| ≤ "+
									"(|c| + δ) * |G| + &(n + 1) * real_pow(|c|, n) * real_pow(|h|, 2)",
								ByArith(widened, triangle, complex_abs.AbsNonneg.At(G)))
							scaledSize := b.Have(
								"scaled by δ² ≥ 0, the size bound stays a bound",
								"real_pow(δ, 2) * |(c + h) * G + complex_of_real(&(n + 1)) * c ^ n * (h * h)| ≤ "+
									"real_pow(δ, 2) * ((|c| + δ) * |G| + &(n + 1) * real_pow(|c|, n) * real_pow(|h|, 2))",
								By(
									size,
									real_pow.PowTwoNonneg.At(δ),
									real_order_ring.LessEqMulLeft.At(
										b.TermAs[Real]("real_pow(δ, 2)"),
										b.TermAs[Real]("|(c + h) * G + complex_of_real(&(n + 1)) * c ^ n * (h * h)|"),
										b.TermAs[Real]("(|c| + δ) * |G| + &(n + 1) * real_pow(|c|, n) * real_pow(|h|, 2)"))))
							scaledHypothesis := b.Have(
								"and scaled by |c| + δ ≥ 0, so does the induction hypothesis",
								"(|c| + δ) * (real_pow(δ, 2) * |G|) ≤ (|c| + δ) * (real_pow(|h|, 2) * F)",
								ByArith(
									ih,
									nonneg,
									complex_abs.AbsNonneg.At(c),
									real_order_ring.LessEqMulLeft.At(
										b.TermAs[Real]("|c| + δ"),
										b.TermAs[Real]("real_pow(δ, 2) * |G|"),
										b.TermAs[Real]("real_pow(|h|, 2) * F"))))
							b.Show(
								"scaled by δ², that is at most (|c| + δ)·|h|²·F + "+
									"(n + 1)·|c|ⁿ·|h|²·δ², by the induction hypothesis",
								recurrence.Rw(),
								comparison.Rw(),
								ByArith(scaledSize, scaledHypothesis))
						})
				}))
			n := arg.FixAs[Nat]()
			size := arg.TermAs[Real]("|c|")
			coefficient := arg.Have(
				"(n + 1)·|c|ⁿ is nonnegative",
				"&0 ≤ &(n + 1) * real_pow(|c|, n)",
				ByArith(complex_abs.AbsNonneg.At(c), real_pow.PowNonneg.At(size, n)))
			dropped := arg.Have(
				"the terms the comparison remainder subtracts are nonnegative",
				"&0 ≤ real_pow(|c|, n + 1) + &(n + 1) * real_pow(|c|, n) * δ",
				ByArith(
					nonneg,
					coefficient,
					complex_abs.AbsNonneg.At(c),
					real_pow.PowNonneg.At(size, arg.TermAs[Nat]("n + 1"))))
			arg.Show(
				"so the comparison remainder is at most (|c| + δ)ⁿ⁺¹, and |h|² ≥ 0",
				ByArith(dominated.At(n), dropped, real_pow.PowTwoNonneg.At(arg.TermAs[Real]("|h|"))))
		}),
})}

// PowerSeriesDerivative — term-by-term differentiation: inside the disc
// where a power series converges, its sum f has a complex derivative at
// c, the sum d of the derived series Σ (n + 1)·a(n + 1)·cⁿ. Take a radius
// ρ between |c| and R at which the series without its first term
// converges absolutely, to M, and δ = ρ − |c|. For |h| < δ, dropping the
// vanishing first term of f(c + h) − f(c) and subtracting h times the
// derived series leaves f(c + h) − f(c) − h·d as the sum of the series
// a(n + 1)·Gₙ, Gₙ the remainder of the first-order expansion of
// (c + h)ⁿ⁺¹ at c. The remainder bound makes each term at most
// (|h|/δ)²·|a(n + 1)·ρⁿ⁺¹| in size, and those bounds sum to (|h|/δ)²·M:
// the increment is d·h to within a constant times |h|², which is a
// derivative.
var PowerSeriesDerivative = powerSeriesDerivativeThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesDerivative",
	Key:  "prop_d57f0e2e23ea645d",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀f:(complex → complex). ∀R:real. ∀c:complex.",
		Hypotheses: []string{
			"∀z:complex. |z| < R ⇒ complex_sums(λn:num. a(n) * z ^ n, f(z))",
			"|c| < R",
		},
		Conclusion: "∃d:complex. " +
			"    complex_sums(λn:num. complex_of_real(&(n + 1)) * a(n + 1) * c ^ n, d) ∧ " +
			"    complex_derivative_at(f, c, d)",
		Abbrev: Abbrev{
			{Name: "powRemainder", Text: "λx:complex. λy:complex. λk:num. " +
				"    (x + y) ^ (k + 1) - x ^ (k + 1) - complex_of_real(&(k + 1)) * x ^ k * y"},
			{Name: "remainderTerm", Text: "λh:complex. λn:num. " +
				"    (a(n + 1) * (c + h) ^ (n + 1) - a(n + 1) * c ^ (n + 1)) - " +
				"    h * (complex_of_real(&(n + 1)) * a(n + 1) * c ^ n)"},
		},
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Complex],
			f *Arrow[Complex, Complex],
			R *Expr[Real],
			c *Expr[Complex],
			sums, inside Fact,
		) {
			converges := arg.Have(
				"the series converges at every point of the disc, to the value of f there",
				"∀w:complex. |w| < R ⇒ ∃s:complex. complex_sums(λn:num. a(n) * w ^ n, s)",
				By(Normalized, sums))
			_, derivedSizes := arg.ObtainAs[Real](
				"the derived series converges absolutely at c",
				"∃t:real. real_sums(λn:num. |complex_of_real(&(n + 1)) * a(n + 1) * c ^ n|, t)",
				By(converges, inside, PowerSeriesDerivedConverges.At(a, R, c)))
			d, derivedSum := arg.ObtainAs[Complex](
				"so it converges, to d",
				"∃d:complex. complex_sums(λn:num. complex_of_real(&(n + 1)) * a(n + 1) * c ^ n, d)",
				By(derivedSizes, complex_series.AbsoluteConvergence))

			_, _, beyond := arg.Obtain2As[Real, Real](
				"between |c| and R lies a radius ρ where the series "+
					"without its first term converges absolutely, to M",
				"∃ρ M:real. |c| < ρ ∧ ρ < R ∧ real_sums(λn:num. |a(n + 1) * &ρ ^ (n + 1)|, M)",
				By(converges, inside, PowerSeriesAbsoluteBeyond.At(a, R, c)))
			δ, δDef := arg.LetAs[Real]("δ", "ρ - |c|")
			radius := arg.Have(
				"δ is positive, and ρ = |c| + δ is nonnegative, so its own size",
				"&0 < δ ∧ ρ = |c| + δ ∧ &0 ≤ ρ ∧ |ρ| = ρ",
				ByArith(δDef, beyond, complex_abs.AbsNonneg.At(c)))

			quadratic := arg.Have(
				"for |h| < δ the increment f(c + h) − f(c) is d·h to within M/δ²·|h|²",
				"∀h:complex. |h| < δ ⇒ |f(c + h) - f(c) - d * h| ≤ M / real_pow(δ, 2) * real_pow(|h|, 2)",
				Derive(func(e *Argument) {
					h := e.FixAs[Complex]()
					small := e.Assume()
					shiftedPoint := e.TermAs[Complex]("c + h")
					fShifted := e.TermAs[Complex]("f(c + h)")
					fc := e.TermAs[Complex]("f(c)")
					increment := e.TermAs[Complex]("f(c + h) - f(c)")
					near := e.Have(
						"c + h lies in the disc, as |c + h| ≤ |c| + |h| < ρ",
						"|c + h| < R",
						ByArith(radius, beyond, small, complex_abs.AbsTriangle.At(c, h)))
					difference := e.Have(
						"the series at c + h less the series at c sums to f(c + h) − f(c)",
						"complex_sums(λn:num. a(n) * (c + h) ^ n - a(n) * c ^ n, f(c + h) - f(c))",
						By(
							near,
							inside,
							sums.At(shiftedPoint),
							sums.At(c),
							At(complex_series.SumsSub,
								e.TermAs[Fun[Nat, Complex]]("λn:num. a(n) * (c + h) ^ n"),
								e.TermAs[Fun[Nat, Complex]]("λn:num. a(n) * c ^ n"),
								fShifted,
								fc)))
					vanishing := e.Have(
						"its first term is a(0) − a(0) = 0",
						"f(c + h) - f(c) - (a(0) * (c + h) ^ 0 - a(0) * c ^ 0) = f(c + h) - f(c)",
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						ByArith())
					differenceShifted := e.Have(
						"so dropping that term leaves the sum unchanged",
						"complex_sums(λn:num. a(n + 1) * (c + h) ^ (n + 1) - a(n + 1) * c ^ (n + 1), f(c + h) - f(c))",
						By(
							vanishing,
							difference,
							At(complex_series.SumsShift,
								e.TermAs[Fun[Nat, Complex]]("λn:num. a(n) * (c + h) ^ n - a(n) * c ^ n"),
								increment)))
					scaledDerived := e.Have(
						"h times the derived series sums to h·d",
						"complex_sums(λn:num. h * (complex_of_real(&(n + 1)) * a(n + 1) * c ^ n), h * d)",
						By(derivedSum, complex_series.SumsScale))
					remainder := e.Have(
						"the difference less h times the derived series sums to f(c + h) − f(c) − h·d",
						"complex_sums(«remainderTerm»(h), f(c + h) - f(c) - h * d)",
						By(differenceShifted, scaledDerived, complex_series.SumsSub))
					dominating := e.Have(
						"(|h|/δ)² times the series of sizes at ρ sums to (|h|/δ)²·M",
						"real_sums(λn:num. real_pow(|h|, 2) / real_pow(δ, 2) * |a(n + 1) * &ρ ^ (n + 1)|, "+
							"    real_pow(|h|, 2) / real_pow(δ, 2) * M)",
						By(beyond, real_series.SumsScale))
					within := e.Have(
						"|h| is at most δ",
						"|h| ≤ δ",
						ByArith(small))
					termwise := e.Have(
						"each term is a(n + 1) times the remainder of (c + "+
							"h)ⁿ⁺¹ at c, at most (|h|/δ)²·|a(n + 1)·ρⁿ⁺¹| in size",
						"∀n:num. |«remainderTerm»(h, n)| ≤ real_pow(|h|, 2) / real_pow(δ, 2) * |a(n + 1) * &ρ ^ (n + 1)|",
						Derive(func(k *Argument) {
							n := k.FixAs[Nat]()
							next := k.TermAs[Nat]("n + 1")
							coefficient := a.Apply(next)
							remainderAt := k.TermAs[Complex]("«powRemainder»(c, h, n)")
							factored := k.Have(
								"the term is a(n + 1) times the remainder Gₙ = (c + h)ⁿ⁺¹ − cⁿ⁺¹ − (n + 1)·cⁿ·h",
								"«remainderTerm»(h, n) = a(n + 1) * «powRemainder»(c, h, n)",
								ByArith())
							remainderBound := k.Have(
								"the remainder bound, δ² divided out: |Gₙ| ≤ |h|²·ρⁿ⁺¹/δ²",
								"|«powRemainder»(c, h, n)| ≤ real_pow(|h|, 2) * real_pow(ρ, n + 1) / real_pow(δ, 2)",
								ByArith(within, radius, PowRemainderBound.At(c, h, δ, n)))
							sizeAtRho := k.Have(
								"the term at ρ has size |a(n + 1)|·ρⁿ⁺¹",
								"|a(n + 1) * &ρ ^ (n + 1)| = |a(n + 1)| * real_pow(ρ, n + 1)",
								Simp(Fwd(complex_abs.AbsMul), Fwd(complex_abs.AbsPow), Fwd(complex_abs.AbsOfReal)),
								ByArith(radius))
							k.Show(
								"times |a(n + 1)|",
								factored.Rw(),
								ByArith(
									remainderBound,
									sizeAtRho,
									complex_abs.AbsMul.At(coefficient, remainderAt),
									complex_abs.AbsNonneg.At(coefficient),
									real_order_ring.LessEqMulLeft.At(
										k.TermAs[Real]("|a(n + 1)|"),
										k.TermAs[Real]("|«powRemainder»(c, h, n)|"),
										k.TermAs[Real]("real_pow(|h|, 2) * real_pow(ρ, n + 1) / real_pow(δ, 2)"))))
						}))
					total := e.Have(
						"so the increment less h·d is at most (|h|/δ)²·M in size",
						"|f(c + h) - f(c) - h * d| ≤ real_pow(|h|, 2) / real_pow(δ, 2) * M",
						By(
							termwise,
							remainder,
							dominating,
							At(complex_series.ComparisonBound,
								e.TermAs[Fun[Nat, Complex]]("«remainderTerm»(h)"),
								e.TermAs[Fun[Nat, Real]]("λn:num. real_pow(|h|, 2) / real_pow(δ, 2) * |a(n + 1) * &ρ ^ (n + 1)|"),
								e.TermAs[Complex]("f(c + h) - f(c) - h * d"),
								e.TermAs[Real]("real_pow(|h|, 2) / real_pow(δ, 2) * M"))))
					commuted := e.Have(
						"h·d is d·h",
						"f(c + h) - f(c) - h * d = f(c + h) - f(c) - d * h",
						ByArith())
					e.Show(
						"which is M/δ²·|h|²",
						commuted.RwRev(),
						ByArith(total))
				}))
			arg.Take(d)
			arg.Show(
				"a quadratic error on a disc makes d the derivative",
				By(
					derivedSum,
					radius,
					quadratic,
					At(
						complex_derivative.DerivativeFromQuadraticRemainder,
						f,
						c,
						d,
						arg.TermAs[Real]("M / real_pow(δ, 2)"),
						δ)))
		}),
})}

// PowerSeriesHolomorphic — the sum of a power series is holomorphic on
// the open disc where the series converges: at each point of the disc
// term-by-term differentiation gives it a derivative.
var PowerSeriesHolomorphic = powerSeriesHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesHolomorphic",
	Key:  "prop_b08b445aefcf32be",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀f:(complex → complex). ∀R:real.",
		Hypotheses: []string{
			"∀z:complex. |z| < R ⇒ complex_sums(λn:num. a(n) * z ^ n, f(z))",
		},
		Conclusion: "holomorphic_on({z:complex | |z| < R}, f)",
	},
		func(arg *Argument, a *Arrow[Nat, Complex], f *Arrow[Complex, Complex], R *Expr[Real], sums Fact) {
			arg.Do(Unfold(complex_derivative.HolomorphicOnDef))
			c := arg.FixAs[Complex]("c")
			inside := arg.Assume()
			arg.Show(
				"term-by-term differentiation gives f a derivative at c",
				By(sums, inside, PowerSeriesDerivative.At(a, f, R, c)))
		}),
})}
