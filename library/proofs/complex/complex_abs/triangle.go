// triangle.go — the modulus bounds each part and is bounded by the sum of
// their sizes, and the triangle inequality, for two terms and for a finite
// sum.

package complex_abs

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ReLessEqAbs — the real part is no bigger than the modulus: its square
// is one of the two nonnegative squares the modulus is the root of.
var ReLessEqAbs = reLessEqAbsThm{family.Add(registry.ProofEntry{
	Name: "ReLessEqAbs",
	Key:  "prop_d2a9d22f276cca34",
	Build: family.Theorem("∀z:complex. |re(z)| ≤ |z|",
		func(a *Argument, z *Expr[Complex]) {
			x, y := a.TermAs[Real]("re(z)"), a.TermAs[Real]("im(z)")
			bound := a.Have(
				"the square of |re(z)| is re(z) · re(z), at most the sum of the two squares",
				"real_pow(|re(z)|, 2) ≤ re(z) * re(z) + im(z) * im(z)",
				ByArith(real_pow.SquareOfAbs.At(x), real_pow.PowTwo.At(x), real_order_ring.SquareNonneg.At(y)))
			a.Show(
				"so |re(z)| is at most the root of that sum",
				Simp(Fwd(ComplexAbsDef)),
				By(
					bound,
					real_sqrt.SqrtLowerBound.At(
						a.TermAs[Real]("|re(z)|"), a.TermAs[Real]("re(z) * re(z) + im(z) * im(z)"))))
		}),
})}

// ImLessEqAbs — and so is the imaginary part.
var ImLessEqAbs = imLessEqAbsThm{family.Add(registry.ProofEntry{
	Name: "ImLessEqAbs",
	Key:  "prop_ab56eee0f2f6f931",
	Build: family.Theorem("∀z:complex. |im(z)| ≤ |z|",
		func(a *Argument, z *Expr[Complex]) {
			x, y := a.TermAs[Real]("re(z)"), a.TermAs[Real]("im(z)")
			bound := a.Have(
				"the square of |im(z)| is im(z) · im(z), at most the sum of the two squares",
				"real_pow(|im(z)|, 2) ≤ re(z) * re(z) + im(z) * im(z)",
				ByArith(real_pow.SquareOfAbs.At(y), real_pow.PowTwo.At(y), real_order_ring.SquareNonneg.At(x)))
			a.Show(
				"so |im(z)| is at most the root of that sum",
				Simp(Fwd(ComplexAbsDef)),
				By(
					bound,
					real_sqrt.SqrtLowerBound.At(
						a.TermAs[Real]("|im(z)|"), a.TermAs[Real]("re(z) * re(z) + im(z) * im(z)"))))
		}),
})}

// PartsNonexpanding — neither part moves a point further than the point
// moves: the parts of z − w are the differences of the parts, and each is
// at most the modulus of z − w.
var PartsNonexpanding = partsNonexpandingThm{family.Add(registry.ProofEntry{
	Name: "PartsNonexpanding",
	Key:  "prop_61d8896b29fbdcf8",
	Build: family.Theorem("∀z w:complex. |re(z) - re(w)| ≤ |z - w| ∧ |im(z) - im(w)| ≤ |z - w|",
		func(a *Argument, z, w *Expr[Complex]) {
			difference := a.TermAs[Complex]("z - w")
			a.Show(
				"the parts of z − w are the differences of the parts, each at most |z − w|",
				ByArith(complex_field.PartsSub.At(z, w), ReLessEqAbs.At(difference), ImLessEqAbs.At(difference)))
		}),
})}

// AbsLeParts — the modulus is at most the sum of the sizes of the two
// parts: z is its real part plus i times its imaginary part, and the
// triangle inequality bounds |z| by |re(z)| + |i|·|im(z)|, where |i| = 1.
var AbsLeParts = absLePartsThm{family.Add(registry.ProofEntry{
	Name: "AbsLeParts",
	Key:  "prop_17770cfe55a78b41",
	Build: family.Theorem("∀z:complex. |z| ≤ |re(z)| + |im(z)|",
		func(a *Argument, z *Expr[Complex]) {
			x, y := a.TermAs[Real]("re(z)"), a.TermAs[Real]("im(z)")
			i := a.TermAs[Complex]("complex_i")
			decomposed := a.Have(
				"z is its real part plus i times its imaginary part",
				"z = &(re(z)) + complex_i * &(im(z))",
				Simp(
					complex_field.Parts,
					Fwd(complex_field.ComplexAddDef),
					Fwd(complex_field.ComplexMulDef),
					Fwd(complex_field.ComplexOfRealDef),
					Fwd(complex_field.ComplexIDef)),
				ByArith())
			imaginary := a.TermAs[Complex]("&(im(z))")
			a.Show(
				"so the triangle inequality bounds |z| by |re(z)| + "+
					"|i|·|im(z)|, which is |re(z)| + |im(z)|, i having modulus 1",
				ByArith(
					decomposed,
					AbsI,
					AbsTriangle.At(a.TermAs[Complex]("&(re(z))"), a.TermAs[Complex]("complex_i * &(im(z))")),
					AbsMul.At(i, imaginary),
					AbsOfReal.At(x),
					AbsOfReal.At(y)))
		}),
})}

// AbsTriangle — the modulus of a sum is at most the sum of the moduli.
// Squared, |z + w|² is |z|² + |w|² plus twice re(z·conj(w)), the cross
// term of the two sums of squares. A real part is at most the modulus,
// and the modulus of z·conj(w) is |z|·|w|, so |z + w|² ≤ (|z| + |w|)².
// The moduli follow the squares: were |z| + |w| below |z + w|, the
// square of the smaller nonnegative number would be below the other's.
var AbsTriangle = absTriangleThm{family.Add(registry.ProofEntry{
	Name: "AbsTriangle",
	Key:  "prop_c38d5bc4c39a3afc",
	Build: family.Theorem("∀z w:complex. |z + w| ≤ |z| + |w|",
		func(a *Argument, z, w *Expr[Complex]) {
			product := a.TermAs[Complex]("z * conj(w)")
			cross := a.TermAs[Real]("re(z * conj(w))")
			absSum := a.TermAs[Real]("|z + w|")
			sumAbs := a.TermAs[Real]("|z| + |w|")

			expansion := a.Have(
				"|z + w|² is |z|² + |w|² and twice re(z·conj(w)), each squared modulus written out in parts",
				"|z + w| * |z + w| = |z| * |z| + &2 * re(z * conj(w)) + |w| * |w|",
				Simp(
					complex_field.Parts,
					Fwd(AbsSquare),
					Fwd(complex_field.ComplexAddDef),
					Fwd(complex_field.ComplexMulDef),
					Fwd(complex_field.ComplexConjDef)),
				ByArith())
			bound := a.CalcLeibniz(real_order_ring.OrderCalc(a.Ctx()), cross,
				LeLeg(
					a.Term("|re(z * conj(w))|"),
					"a real number is at most its absolute value",
					By(real_sgn_abs.AbsDominates.At(cross))),
				LeLeg(
					a.Term("|z * conj(w)|"),
					"a real part is at most the modulus",
					By(ReLessEqAbs.At(product))),
				EqLeg(
					a.Term("|z| * |conj(w)|"),
					"the modulus is multiplicative",
					Cite(AbsMul)),
				EqLeg(
					a.Term("|z| * |w|"),
					"and blind to conjugation",
					Cite(AbsConj)))
			squaresCompare := a.Have(
				"so |z + w|² is at most (|z| + |w|)²",
				"|z + w| * |z + w| ≤ (|z| + |w|) * (|z| + |w|)",
				ByArith(expansion, bound))

			larger := a.SupposeNot()
			a.Show(
				"then |z| + |w| < |z + w|, and squaring two nonnegative numbers "+
					"keeps their order — against the bound between the squares",
				ByArith(
					larger,
					squaresCompare,
					AbsNonneg.At(z),
					AbsNonneg.At(w),
					real_order_ring.LessThanMul2.At(sumAbs, absSum, sumAbs, absSum)))
		}),
})}

// AbsSubTriangle — the triangle inequality between three points: the
// distance from x to u is at most the distance from x to y plus that from y
// to u, x − u being (x − y) + (y − u).
var AbsSubTriangle = absSubTriangleThm{family.Add(registry.ProofEntry{
	Name: "AbsSubTriangle",
	Key:  "prop_86e4a303335c38dd",
	Build: family.Theorem("∀x y u:complex. |x - u| ≤ |x - y| + |y - u|",
		func(a *Argument, x, y, u *Expr[Complex]) {
			regrouped := a.Have(
				"x − u is (x − y) + (y − u)",
				"x - u = x - y + (y - u)",
				ByArith())
			a.Show(
				"so the triangle inequality bounds its modulus",
				regrouped.Rw(),
				Cite(AbsTriangle))
		}),
})}

// AbsSubComm — the distance between two points reads the same both ways:
// z − w is the negative of w − z, and negation leaves the modulus alone.
var AbsSubComm = absSubCommThm{family.Add(registry.ProofEntry{
	Name: "AbsSubComm",
	Key:  "prop_543e73d38b5d5c1",
	Build: family.Theorem("∀z w:complex. |z - w| = |w - z|",
		func(a *Argument, z, w *Expr[Complex]) {
			negated := a.Have(
				"z − w is the negative of w − z",
				"z - w = -(w - z)",
				ByArith())
			a.Show(
				"and negation leaves the modulus alone",
				negated.Rw(),
				Cite(AbsNeg))
		}),
})}

// AbsTriangleReverse — the moduli of two complex numbers differ by at
// most the modulus of their difference. z is (z − w) + w, so the
// triangle inequality bounds |z| by |z − w| + |w|; w is −(z − w) + z,
// and negation leaves the modulus alone, so it bounds |w| by
// |z − w| + |z|. The two bounds put |z| − |w| between −|z − w| and
// |z − w|.
var AbsTriangleReverse = absTriangleReverseThm{family.Add(registry.ProofEntry{
	Name: "AbsTriangleReverse",
	Key:  "prop_9b6d929faa035c1f",
	Build: family.Theorem("∀z w:complex. ||z| - |w|| ≤ |z - w|",
		func(a *Argument, z, w *Expr[Complex]) {
			addition := abelian_group.Group.Read(complex_field.AddGroup)
			difference := a.TermAs[Complex]("z - w")

			addBack := a.Have(
				"z is z − w with w added back: unfold the difference, regroup, and −w + w is zero",
				"(z - w) + w = z",
				Simp(
					Fwd(complex_field.ComplexSubDef),
					Rev(group.Assoc.Read(addition)),
					Fwd(group.LeftInverse.Read(addition)),
					Fwd(group.RightIdentity.Read(addition))),
				Refl())
			negBack := a.Have(
				"w is the negation of z − w with z added: −(z + −w) is w + −z, and regrouping cancels −z",
				"-(z - w) + z = w",
				Simp(
					Fwd(complex_field.ComplexSubDef),
					Fwd(group.InvMul.Read(addition)),
					Fwd(group.InvInv.Read(addition)),
					Rev(group.Assoc.Read(addition)),
					Fwd(group.LeftInverse.Read(addition)),
					Fwd(group.RightIdentity.Read(addition))),
				Refl())

			upper := a.Have(
				"so the triangle inequality bounds |z| by |z − w| + |w|",
				"|z| ≤ |z - w| + |w|",
				By(Normalized, addBack, AbsTriangle.At(difference, w)))
			lower := a.Have(
				"and |w| by |−(z − w)| + |z|, which is |z − w| + |z|",
				"|w| ≤ |z - w| + |z|",
				By(Normalized, negBack, AbsTriangle.At(a.TermAs[Complex]("-(z - w)"), z), AbsNeg.At(difference)))

			a.Show(
				"so |z| − |w| lies between −|z − w| and |z − w|",
				ByArith(upper, lower))
		}),
})}

// AbsSumTriangle — the modulus of a finite sum is at most the sum of the
// moduli of its terms: adjoining a term applies the two-term triangle
// inequality to it and the sum before it.
var AbsSumTriangle = absSumTriangleThm{family.Add(registry.ProofEntry{
	Name: "AbsSumTriangle",
	Key:  "prop_b12fa8742b993b7c",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(A). ∀F:(A → complex).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "|module_sum(complex_add, &0, s, F)| ≤ sum(s, λi:A. |F(i)|)",
	}, func(a *Argument, s *Expr[Set[A]], F *Arrow[A, Complex], finite Fact) {
		additive := comm_ring.AddMonoidOn.Read(complex_field.CommRingOn)
		a.Show(
			"the bound holds of every finite index set, s among them",
			ByInduction(finite_set.FiniteInductFresh, finite,
				Case(
					"the empty sums and their moduli vanish",
					ByArith(
						module.ModuleSumEmpty.At(
							a.TermAs[Op[Complex]]("complex_add"), a.TermAs[Complex]("complex_of_real(&0)"), F),
						real_sum.Clauses,
						AbsOfReal.At(a.TermAs[Real]("&0")))),
				Case(
					"one more term is bounded by its modulus and the previous bound",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						u := b.FixAs[Set[A]]("u")
						induction := b.Assume()
						complexInsert := b.Have(
							"the new complex sum splits off its new term",
							"module_sum(complex_add, &0, insert(x, u), F) = F(x) + module_sum(complex_add, &0, u, F)",
							By(
								induction,
								module.ModuleSumInsertMonoid.Read(additive).At(u, x, F),
								set_basic.InUniv.Inst[Complex]()))
						realInsert := b.Have(
							"the sum of moduli splits off the new modulus",
							"sum(insert(x, u), λi:A. |F(i)|) = |F(x)| + sum(u, λi:A. |F(i)|)",
							By(induction, real_sum.Clauses))
						b.Show(
							"the triangle inequality and induction bound the enlarged sum",
							ByArith(
								complexInsert,
								realInsert,
								induction,
								AbsTriangle.At(F.Apply(x), b.TermAs[Complex]("module_sum(complex_add, &0, u, F)"))))
					}))))
	}),
})}

// AbsSumDominated — anything that dominates the moduli of the terms
// bounds the modulus of the sum: the triangle inequality prices the sum
// by its sum of moduli, and the dominator prices that.
var AbsSumDominated = absSumDominatedThm{family.Add(registry.ProofEntry{
	Name: "AbsSumDominated",
	Key:  "prop_8ff7ead130a023df",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀F:(A → complex). ∀g:(A → real).",
		Hypotheses: []string{
			"finite(s)",
			"∀x:A. x ∈ s ⇒ |F(x)| ≤ g(x)",
		},
		Conclusion: "|module_sum(complex_add, &0, s, F)| ≤ sum(s, g)",
	}, func(
		a *Argument,
		s *Expr[Set[A]],
		F *Arrow[A, Complex],
		g *Arrow[A, Real],
		finite, dominates Fact,
	) {
		moduli := a.TermAs[Fun[A, Real]]("λx:A. |F(x)|")
		a.Show(
			"so the sum's modulus is within g's sum",
			real_order_ring.OrderCalc(a.Ctx()).Calc(a.TermAs[Real]("|module_sum(complex_add, &0, s, F)|"),
				LeLeg(
					a.TermAs[Real]("sum(s, λx:A. |F(x)|)"),
					"the sum is within its own sum of moduli",
					By(finite, AbsSumTriangle)),
				LeLeg(
					a.TermAs[Real]("sum(s, g)"),
					"whose terms g dominates pointwise",
					By(finite, dominates, real_sum.Monotone.At(s, moduli, g)))))
	}),
})}
