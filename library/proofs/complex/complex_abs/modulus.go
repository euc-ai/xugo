// modulus.go — the modulus: its definition, its square, its sign, where
// it vanishes, its value on the reals, and the two symmetries that leave
// it alone.

package complex_abs

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/registry"
)

// ComplexAbsDef — the modulus |z|: the length of the point (x, y) of
// the plane, the square root of the sum of the squares of the parts.
var ComplexAbsDef = complexAbsDefThm{family.Define(registry.DefEntry{
	Name:      "ComplexAbsDef",
	Key:       "prop_a93243dd3e7a1106",
	Const:     "complex_abs",
	Type:      "complex → real",
	Notation:  "|z|",
	Overload:  "abs",
	Equations: []string{"∀z:complex. complex_abs(z) = real_sqrt(re(z) * re(z) + im(z) * im(z))"},
})}

// SumSquaresNonneg — the radicand is never negative: each part's square
// is not.
var SumSquaresNonneg = sumSquaresNonnegThm{family.Add(registry.ProofEntry{
	Name: "SumSquaresNonneg",
	Key:  "prop_d21945b52bb5092a",
	Build: family.Theorem("∀z:complex. &0 ≤ re(z) * re(z) + im(z) * im(z)",
		func(a *Argument, z *Expr[Complex]) {
			a.Show(
				"each square is nonnegative",
				ByArith(
					real_order_ring.SquareNonneg.At(a.TermAs[Real]("re(z)")),
					real_order_ring.SquareNonneg.At(a.TermAs[Real]("im(z)"))))
		}),
})}

// AbsSquare — the square of the modulus is the sum of the squares of
// the parts: the root of a nonnegative number squares back to it.
var AbsSquare = absSquareThm{family.Add(registry.ProofEntry{
	Name: "AbsSquare",
	Key:  "prop_f90b1aed697d3f67",
	Build: family.Theorem("∀z:complex. |z| * |z| = re(z) * re(z) + im(z) * im(z)",
		func(a *Argument, z *Expr[Complex]) {
			sum := a.TermAs[Real]("re(z) * re(z) + im(z) * im(z)")
			a.Show(
				"the root of the nonnegative sum of squares, squared",
				Simp(Fwd(ComplexAbsDef)),
				ByArith(SumSquaresNonneg.At(z), real_sqrt.SqrtPowTwo.At(sum)))
		}),
})}

// AbsNonneg — the modulus is never negative.
var AbsNonneg = absNonnegThm{family.Add(registry.ProofEntry{
	Name: "AbsNonneg",
	Key:  "prop_642aa9a17dd3b23c",
	Build: family.Theorem("∀z:complex. &0 ≤ |z|",
		func(a *Argument, z *Expr[Complex]) {
			a.Show(
				"a root of a nonnegative number is nonnegative",
				Simp(Fwd(ComplexAbsDef)),
				By(SumSquaresNonneg.At(z), real_sqrt.SqrtNonneg))
		}),
})}

// AbsEqZero — only zero has modulus zero: a zero modulus makes the sum
// of the squares of the parts zero, and a sum of two squares vanishes
// only when both parts do.
var AbsEqZero = absEqZeroThm{family.Add(registry.ProofEntry{
	Name: "AbsEqZero",
	Key:  "prop_134fa38aac781b54",
	Build: family.Theorem("∀z:complex. |z| = &0 ⇔ z = complex_of_real(&0)",
		func(a *Argument, z *Expr[Complex]) {
			a.Iff()
			a.Forward(
				"a zero modulus leaves both parts zero",
				func(b *Argument, absZero Fact) {
					sum := b.Have(
						"the sum of the squares of the parts is the square of the modulus, which is zero",
						"re(z) * re(z) + im(z) * im(z) = &0",
						Simp(Rev(AbsSquare)),
						absZero.Rw(),
						ByArith())
					parts := b.Have(
						"so both parts are zero",
						"re(z) = &0 ∧ im(z) = &0",
						By(sum, real_order_ring.SumSquaresEqZero))
					b.Show(
						"and a number whose parts are zero is zero",
						Simp(complex_field.Parts, Fwd(complex_field.ComplexOfRealDef)),
						By(parts))
				})
			a.Backward(
				"zero's parts are zero, and so is the root of zero",
				func(b *Argument, isZero Fact) {
					b.Show(
						"the modulus of zero",
						isZero.Rw(),
						Simp(complex_field.Parts, Fwd(ComplexAbsDef), Fwd(complex_field.ComplexOfRealDef)),
						By(real_sqrt.SqrtZero))
				})
		}),
})}

// AbsPosIffNonzero — away from zero the modulus is strictly positive:
// AbsNonneg places |z| at or above &0, so ruling out equality is the
// whole of strictness, and AbsEqZero says when equality holds.
var AbsPosIffNonzero = absPosIffNonzeroThm{family.Add(registry.ProofEntry{
	Name: "AbsPosIffNonzero",
	Key:  "prop_b5ee898647487175",
	Build: family.Theorem("∀z:complex. &0 < |z| ⇔ z ≠ complex_of_real(&0)",
		func(a *Argument, z *Expr[Complex]) {
			a.Iff()
			a.Forward(
				"a positive modulus is not zero, so z is not zero",
				func(b *Argument, positive Fact) {
					b.Show(
						"zero alone has modulus zero",
						ByArith(positive, AbsEqZero.At(z)))
				})
			a.Backward(
				"a nonzero z has a nonzero modulus, and the modulus is never negative",
				func(b *Argument, nonzero Fact) {
					b.Show(
						"at or above zero and not zero is above zero",
						ByArith(nonzero, AbsEqZero.At(z), AbsNonneg.At(z)))
				})
		}),
})}

// AbsOfReal — on the reals the modulus is the absolute value: the root
// of x² is |x|, the nonnegative number that squares to it.
var AbsOfReal = absOfRealThm{family.Add(registry.ProofEntry{
	Name: "AbsOfReal",
	Key:  "prop_e3cc3b1a70a5cf",
	Build: family.Theorem("∀x:real. |complex_of_real(x)| = |x|",
		func(a *Argument, x *Expr[Real]) {
			square := a.Have(
				"|x| squares to x · x + 0 · 0",
				"x * x + &0 * &0 = real_pow(|x|, 2)",
				ByArith(real_pow.SquareOfAbs.At(x), real_pow.PowTwo.At(x)))
			a.Show(
				"|x| is the nonnegative number whose square is the radicand, so it is the root",
				Simp(complex_field.Parts, Fwd(ComplexAbsDef), Fwd(complex_field.ComplexOfRealDef)),
				By(
					square,
					real_sgn_abs.AbsNonneg.At(x),
					real_sqrt.SqrtUnique.At(a.TermAs[Real]("x * x + &0 * &0"), a.TermAs[Real]("|x|"))))
		}),
})}

// AbsOfNonnegReal — a nonnegative real is its own modulus: the modulus of
// a real is its absolute value, which leaves a nonnegative number alone.
var AbsOfNonnegReal = absOfNonnegRealThm{family.Add(registry.ProofEntry{
	Name: "AbsOfNonnegReal",
	Key:  "prop_ecc1d78fd4ef7141",
	Build: family.Theorem(Statement{
		Binders:    "∀x:real.",
		Hypotheses: []string{"&0 ≤ x"},
		Conclusion: "|complex_of_real(x)| = x",
	}, func(a *Argument, x *Expr[Real], nonneg Fact) {
		a.Show(
			"|&x| is |x|, and |x| is x where x is nonnegative",
			By(Normalized, nonneg, AbsOfReal.At(x), real_sgn_abs.AbsFixedIffNonneg.At(x)))
	}),
})}

// AbsOfRealSub — two reals are as far apart in ℂ as in ℝ: the difference
// of x and y seen in ℂ is x − y seen in ℂ, whose modulus is |x − y|.
var AbsOfRealSub = absOfRealSubThm{family.Add(registry.ProofEntry{
	Name: "AbsOfRealSub",
	Key:  "prop_20a41e7c0eb1552c",
	Build: family.Theorem("∀x y:real. |complex_of_real(x) - complex_of_real(y)| = |x - y|",
		func(a *Argument, x, y *Expr[Real]) {
			a.Show(
				"&x − &y is &(x − y), and the modulus of a real is its absolute value",
				Simp(Rev(complex_field.OfRealSub), Fwd(AbsOfReal)),
				Refl())
		}),
})}

// AbsI — the imaginary unit has modulus 1: its parts are 0 and 1, and 1 is
// the nonnegative root of 0·0 + 1·1.
var AbsI = absIThm{family.Add(registry.ProofEntry{
	Name: "AbsI",
	Key:  "prop_6000f8b1acb70045",
	Build: family.Theorem("|complex_i| = &1",
		func(a *Argument) {
			a.Show(
				"1 is the nonnegative number whose square is the radicand 0·0 + 1·1, so it is the root",
				Simp(Fwd(ComplexAbsDef), Fwd(complex_field.ComplexIDef)),
				ByArith(real_sqrt.SqrtUnique.At(a.TermAs[Real]("&0 * &0 + &1 * &1"), a.TermAs[Real]("&1"))))
		}),
})}

// AbsNeg — negation leaves the modulus alone: it negates both parts,
// and their squares do not see the sign.
var AbsNeg = absNegThm{family.Add(registry.ProofEntry{
	Name: "AbsNeg",
	Key:  "prop_f008dd2a6c84f04",
	Build: family.Theorem("∀z:complex. |-z| = |z|",
		func(a *Argument, z *Expr[Complex]) {
			same := a.Have(
				"the negated parts square to the parts' squares",
				"-re(z) * -re(z) + -im(z) * -im(z) = re(z) * re(z) + im(z) * im(z)",
				ByArith())
			a.Show(
				"so the two roots are of one radicand",
				Simp(complex_field.Parts, Fwd(ComplexAbsDef), Fwd(complex_field.ComplexNegDef)),
				same.Rw(),
				Basic())
		}),
})}

// AbsConj — so does conjugation, which negates the imaginary part
// alone.
var AbsConj = absConjThm{family.Add(registry.ProofEntry{
	Name: "AbsConj",
	Key:  "prop_66b46883ba622a7f",
	Build: family.Theorem("∀z:complex. |conj(z)| = |z|",
		func(a *Argument, z *Expr[Complex]) {
			same := a.Have(
				"the negated imaginary part squares to its square",
				"re(z) * re(z) + -im(z) * -im(z) = re(z) * re(z) + im(z) * im(z)",
				ByArith())
			a.Show(
				"so the two roots are of one radicand",
				Simp(complex_field.Parts, Fwd(ComplexAbsDef), Fwd(complex_field.ComplexConjDef)),
				same.Rw(),
				Basic())
		}),
})}
