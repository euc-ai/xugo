// sqrt.go — the square root: that the choice can be made, what it
// gives, and that on the nonnegative half it is the only choice.
//
// `real_sqrt(x)` is named by a Hilbert choice, so the chapter's first duty
// is to show the choice is not vacuous: `Works` exhibits a y with the
// sign of x whose square is |x|, built from the existence theorem as
// sgn(x)·|r|. Two laws read straight off it — the root of a nonnegative
// real squares back to that real, and is itself nonnegative — and
// together those two say the root is a nonnegative value with a known
// square.
//
// `SqrtUnique` is the converse and the chapter's working tool: on the
// nonnegative half there is only ONE such value, so anything known to
// be nonnegative and to square to x IS real_sqrt(x). Every later law that
// identifies a root reads off it — `SqrtZero` immediately, and
// `SqrtLowerBound` through the same fact that carries it, that squares
// compare exactly as the sizes of their bases do. Monotonicity of the
// root is never stated: that equivalence already carries it.

package real_sqrt

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// Works — the signed square root has the sign of its argument and
// squares to its absolute value. The definition of `real_sqrt` is a choice
// of a y meeting exactly those two conditions, so the theorem is that
// the choice is not vacuous: such a y exists for every x, and the
// chosen one therefore satisfies the pair. Every later law of the
// chapter is a consequence of this one.
//
// The argument produces the required y. When x is &0 the root is &0.
// When x is nonzero, |x| is positive, so a root r of |x| exists
// (`SquareRootExists`); its absolute value |r| is a
// NONNEGATIVE root of |x|, and reflecting it through x's own sign,
// sgn(x)·|r|, gives a y whose sign is sgn(x) (a nonnegative factor
// contributes sign &1) and whose square is sgn(x)²·|r|² = &1·|x| = |x|.
var Works = worksThm{family.Add(registry.ProofEntry{
	Name: "Works",
	Key:  "prop_7b626ae4b1c1343a",
	Build: family.Theorem("∀x:real. sgn(real_sqrt(x)) = sgn(x) ∧ real_pow(real_sqrt(x), 2) = |x|", func(
		a *Argument,
		x Term,
	) {
		zero, one, two := a.Term("&0"), a.Term("&1"), a.Term("2")

		// real_sqrt(x) is the choice term εy. sgn(y) = sgn(x) ∧ y² = |x|; a
		// property of it follows from that same property holding of SOME
		// y, so the whole theorem reduces to the existence of a signed
		// root.
		a.Do(Unfold(RealSqrtDef))

		a.Have(
			"a signed square root of x exists — a y with x's own sign whose square is |x|",
			"∃y:real. sgn(y) = sgn(x) ∧ real_pow(y, 2) = |x|",
			Derive(func(a *Argument) {
				a.Cases(a.Term("x = &0"))
				a.When(
					"x is &0: the root is &0, whose sign is &0 and whose square is &0 = |&0|",
					func(a *Argument, xZero Fact) {
						a.Take(zero)
						a.Show(
							"&0² = &0·&0 = &0 = |&0|, and both signs are &0",
							By(xZero, At(real_pow.PowTwo, zero), At(real_ring.MulLeftZero, zero), real_sgn_abs.AbsOfZero))
					})
				a.Otherwise(
					"x is nonzero: reflect a nonnegative root of the positive |x| back through x's sign",
					func(a *Argument, xNonzero Fact) {
						// |x| is positive, so it has a root; take one.
						r, rootEq := a.Obtain(
							"|x| is positive and so has a square root r",
							"∃r:real. real_pow(r, 2) = |x|",
							By(Normalized, xNonzero, At(SquareRootExists, a.Term("|x|")), At(real_sgn_abs.AbsPosIffNonzero, x)))

						// |r| is a NONNEGATIVE root of |x|: it is positive
						// (r² = |x| ≠ &0 forces r ≠ &0) and squares to |x|
						// (a square is unchanged by |·|).
						posAbsR := a.Have(
							"|r| is positive, since r² = |x| and x ≠ &0",
							"&0 < |r|",
							By(
								Normalized,
								xNonzero,
								rootEq,
								At(real_sgn_abs.AbsPosIffNonzero, x),
								At(real_pow.PowTwo, r),
								At(real_order_ring.SquarePos, r),
								At(real_sgn_abs.AbsPosIffNonzero, r)))
						sqAbsR := a.Have(
							"|r| squares to |x| as r does, |·| leaving a square alone",
							"real_pow(|r|, 2) = |x|",
							By(Normalized, rootEq, At(real_pow.SquareOfAbs, r)))

						// The two sign facts the reflection needs: a
						// positive real has sign &1, so the sign is
						// idempotent (each of &1, &0, -&1 is its own sign)
						// and x's sign squares to &1 (x² is positive).
						posSign := a.Have(
							"a positive real has sign &1",
							"∀y:real. &0 < y ⇒ sgn(y) = &1",
							Derive(func(a *Argument) {
								a.Do(Unfold(real_sgn_abs.RealSgnDef))
								a.Fix()
								pos := a.Assume()
								a.Show(
									"the outer guard &0 < y holds, so the sign is its first branch, &1",
									By(pos))
							}))
						sgnIdem := a.Have(
							"the sign of a sign is itself, &1, &0 and -&1 each being their own sign",
							"sgn(sgn(x)) = sgn(x)",
							By(
								posSign.At(one),
								At(real_sgn_abs.SgnTrichotomy, x),
								real_order_ring.ZeroLessThanOne,
								At(real_sgn_abs.SgnOdd, one),
								real_sgn_abs.SgnOfZero))
						sgnSq := a.Have(
							"x's sign squares to &1, being ±&1 on the nonzero x",
							"real_pow(sgn(x), 2) = &1",
							By(
								Normalized,
								xNonzero,
								posSign.At(a.Term("x * x")),
								At(real_pow.SgnPow, x, two),
								At(real_pow.PowTwo, x),
								At(real_order_ring.SquarePos, x)))

						a.Show(
							"sgn(x)·|r| is the signed root: its sign is x's and its square is |x|",
							Witness(a.Term("sgn(x) * |r|")),
							SplitConj(
								Case(
									"its sign is x's: sgn(sgn(x)·|r|) = sgn(x)·&1 = sgn(x)",
									By(
										posSign.At(a.Term("|r|")),
										sgnIdem,
										posAbsR,
										At(real_sgn_abs.SgnMul, a.Term("sgn(x)"), a.Term("|r|")),
										At(real_ring.MulRightId, a.Term("sgn(x)")))),
								Case(
									"its square is |x|: (sgn(x)·|r|)² = sgn(x)²·|r|² = &1·|x| = |x|",
									By(
										sqAbsR,
										sgnSq,
										At(real_pow.MulPowDistrib, a.Term("sgn(x)"), a.Term("|r|"), two),
										At(real_construction.MulLeftId, a.Term("|x|")))),
							))
					})
			}))

		a.Show(
			"real_sqrt(x) is Hilbert's choice of such a y, so it has that sign and that square",
			TrivialNormalized())
	}),
})}

// SqrtPowTwo — the square of the root of a nonnegative real is that
// real. It reads off Works: the root squares to |x|,
// and |x| is x exactly on the nonnegative half (AbsFixedIffNonneg).
var SqrtPowTwo = sqrtPowTwoThm{family.Add(registry.ProofEntry{
	Name: "SqrtPowTwo",
	Key:  "prop_dcecde461b8e38e6",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 ≤ x",
		},
		Conclusion: "real_pow(real_sqrt(x), 2) = x",
	},
		func(a *Argument, x Term, nonneg Fact) {
			a.Show(
				"real_sqrt(x) squares to |x|, which is x on the nonnegative half",
				By(Normalized, nonneg, At(Works, x), At(real_sgn_abs.AbsFixedIffNonneg, x)))
		}),
})}

// SqrtNonneg — the root of a nonnegative real is nonnegative. It reads
// off Works — real_sqrt(x) has the sign of x.
// A nonnegative x has sign &1 or &0,
// and sgn(real_sqrt(x))·real_sqrt(x) = |real_sqrt(x)| decides both: with sign &1,
// real_sqrt(x) is its own absolute value, hence nonnegative; with sign &0,
// its absolute value vanishes, so real_sqrt(x) is &0.
var SqrtNonneg = sqrtNonnegThm{family.Add(registry.ProofEntry{
	Name: "SqrtNonneg",
	Key:  "prop_747f0bcf944ae610",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 ≤ x",
		},
		Conclusion: "&0 ≤ real_sqrt(x)",
	},
		func(a *Argument, x Term, nonneg Fact) {
			zero, root := a.Term("&0"), a.Term("real_sqrt(x)")

			sameSign := a.Have(
				"real_sqrt(x) has the sign of x",
				"sgn(real_sqrt(x)) = sgn(x)",
				By(At(Works, x)))

			// The definition's negative guard x < &0 fails on a
			// nonnegative x, leaving the sign its other two values.
			signOfNonneg := a.Have(
				"a nonnegative x has sign &1 or &0",
				"sgn(x) = &1 ∨ sgn(x) = &0",
				By(nonneg, At(real_order_ring.NotLessThan, x, zero), At(real_sgn_abs.RealSgnDef, x)))

			// Either sign is read through sgn(real_sqrt(x))·real_sqrt(x) = |real_sqrt(x)|,
			// with sgn(real_sqrt(x)) = sgn(x).
			a.Do(signOfNonneg.SplitDisj(
				LeftHolds(
					"sign &1: real_sqrt(x) = &1·real_sqrt(x) = |real_sqrt(x)|, which is nonnegative",
					Given(func(a *Argument, signOne Fact) {
						a.Show(
							"real_sqrt(x) is its own absolute value",
							By(
								Normalized,
								signOne,
								sameSign,
								At(real_sgn_abs.SgnMulSelfIsAbs, root),
								At(real_construction.MulLeftId, root),
								At(real_sgn_abs.AbsNonneg, root)))
					})),
				RightHolds(
					"sign &0: |real_sqrt(x)| = &0·real_sqrt(x) = &0, so real_sqrt(x) is &0",
					Given(func(a *Argument, signZero Fact) {
						a.Show(
							"an absolute value that vanishes has a vanishing argument, and &0 ≤ &0",
							By(
								signZero,
								sameSign,
								At(real_sgn_abs.SgnMulSelfIsAbs, root),
								At(real_ring.MulLeftZero, root),
								At(real_sgn_abs.AbsVanishes, root),
								At(real_order_ring.LessEqRefl, zero)))
					})),
			))
		}),
})}

// SqrtUnique — on the nonnegative half nothing else competes for the
// name: a nonnegative y whose square is x is real_sqrt(x) itself. This is the
// other half of the characterization Works begins, and the argument is
// that squaring, restricted to the nonnegative reals, forgets nothing.
//
// x is a square, hence nonnegative, and there the chapter's two laws
// apply: real_sqrt(x) is nonnegative, and it squares back to x. So real_sqrt(x)
// and y have one square between them. Squares compare exactly as the
// sizes of their bases do (real_pow.AbsLessEqIffPowTwoLessEq), so that
// one equation, read as an inequality each way round, bounds each size
// by the other, and antisymmetry makes the two sizes equal. A
// nonnegative real is its own size, and both of these are nonnegative.
var SqrtUnique = sqrtUniqueThm{family.Add(registry.ProofEntry{
	Name: "SqrtUnique",
	Key:  "prop_66a48f686cc12b1f",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"x = real_pow(y, 2)",
			"&0 ≤ y",
		},
		Conclusion: "y = real_sqrt(x)",
	},
		func(a *Argument, x, y Term, isSquare, nonnegY Fact) {
			root, sqY := a.Term("real_sqrt(x)"), a.Term("real_pow(y, 2)")
			absRoot, absY := a.Term("|real_sqrt(x)|"), a.Term("|y|")

			nonnegX := a.Have(
				"x is a square, so it is nonnegative",
				"&0 ≤ x",
				By(Normalized, isSquare, At(real_pow.PowTwoNonneg, y)))
			rootNonneg := a.Have(
				"and on the nonnegative half the root is nonnegative too",
				"&0 ≤ real_sqrt(x)",
				By(nonnegX, At(SqrtNonneg, x)))
			squares := a.Have(
				"there the root squares back to x, which is y²: one square between them",
				"real_pow(real_sqrt(x), 2) = real_pow(y, 2)",
				By(Normalized, isSquare, nonnegX, At(SqrtPowTwo, x)))

			rootBelow := a.Have(
				"that equation gives real_sqrt(x)² ≤ y², and squares compare as the sizes of their bases do",
				"|real_sqrt(x)| ≤ |y|",
				By(
					Normalized,
					squares,
					At(real_pow.AbsLessEqIffPowTwoLessEq, root, y),
					At(real_order_ring.LessEqRefl, sqY)))
			rootAbove := a.Have(
				"and it gives y² ≤ real_sqrt(x)² as well, the same law read the other way",
				"|y| ≤ |real_sqrt(x)|",
				By(
					Normalized,
					squares,
					At(real_pow.AbsLessEqIffPowTwoLessEq, y, root),
					At(real_order_ring.LessEqRefl, sqY)))
			sizesAgree := a.Have(
				"so each size is at most the other",
				"|real_sqrt(x)| = |y|",
				By(rootBelow, rootAbove, At(real_construction.LessEqAntisym, absRoot, absY)))

			a.Show(
				"and both are nonnegative, so each is its own size",
				By(
					Normalized,
					sizesAgree,
					nonnegY,
					rootNonneg,
					At(real_sgn_abs.AbsFixedIffNonneg, root),
					At(real_sgn_abs.AbsFixedIffNonneg, y)))
		}),
})}

// SqrtZero — the characterization settles this, not the definition. &0
// squares to &0 and is nonnegative, so it meets the condition SqrtUnique
// shows only one value meets; what the choice term actually picked at &0
// never comes up.
var SqrtZero = sqrtZeroThm{family.Add(registry.ProofEntry{
	Name: "SqrtZero",
	Key:  "prop_a0833569fe39ac4b",
	Build: family.Theorem("&0 = real_sqrt(&0)",
		func(a *Argument) {
			zero := a.Term("&0")

			a.Show(
				"&0 is a nonnegative square root of &0: &0² = &0·&0 = &0, and &0 ≤ &0",
				By(
					Normalized,
					At(real_pow.PowTwo, zero),
					At(real_ring.MulLeftZero, zero),
					At(real_order_ring.LessEqRefl, zero),
					At(SqrtUnique, zero, zero)))
		}),
})}

// SqrtLowerBound — a value whose square is under y is under the
// root of y: x is a lower bound for the root exactly when x² is one
// for the radicand.
//
// The value is not assumed nonnegative and need not be: the hypothesis
// already puts y above a square, so y is nonnegative and its root is
// too, which settles a negative value outright. The argument therefore
// never splits on the sign of x. It passes through the size |x|
// instead, where the comparison of squares lives, and comes back down
// to the root at the far end, a nonnegative root being its own size.
//
// Its one piece of content is that squares compare exactly as the sizes
// of their bases do (real_pow.AbsLessEqIffPowTwoLessEq): x² ≤ y is
// x² ≤ (√y)² once the root is known to square back to y, so
// monotonicity of the root is never needed — only the equivalence that
// carries it.
var SqrtLowerBound = sqrtLowerBoundThm{family.Add(registry.ProofEntry{
	Name: "SqrtLowerBound",
	Key:  "prop_53dcc95766b87342",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"real_pow(x, 2) ≤ y",
		},
		Conclusion: "x ≤ real_sqrt(y)",
	},
		func(a *Argument, x, y *Expr[Real], squareBound Fact) {
			zero := a.TermAs[Real]("&0")
			square := a.TermAs[Real]("real_pow(x, 2)")
			root := a.TermAs[Real]("real_sqrt(y)")
			size := a.TermAs[Real]("|x|")
			rootSize := a.TermAs[Real]("|real_sqrt(y)|")

			nonnegY := a.Have(
				"y is nonnegative, standing above a square",
				"&0 ≤ y",
				By(squareBound, real_pow.PowTwoNonneg.At(x), real_construction.LessEqTrans.At(zero, square, y)))
			squaresBack := a.Have(
				"so the root of y squares back to y",
				"real_pow(real_sqrt(y), 2) = y",
				By(nonnegY, SqrtPowTwo.At(y)))
			rootNonneg := a.Have(
				"and the root is itself nonnegative",
				"&0 ≤ real_sqrt(y)",
				By(nonnegY, SqrtNonneg.At(y)))

			a.Show(
				"x ≤ |x| ≤ |√y| = √y",
				real_order_ring.OrderCalc(a.Ctx()).CalcLeibniz(x,
					LeLeg(
						size,
						"nothing exceeds its own size",
						Cite(real_sgn_abs.AbsDominates)),
					LeLeg(
						rootSize,
						"and x is no larger than the root in size, its square being no larger than the root's",
						By(Normalized, squaresBack, squareBound, real_pow.AbsLessEqIffPowTwoLessEq.At(x, root))),
					EqLeg(
						root,
						"and the root, being nonnegative, is its own size",
						By(rootNonneg, real_sgn_abs.AbsFixedIffNonneg.At(root)))))
		}),
})}

// SqrtOfPow — the root of a power of a nonnegative real is that power of the
// root: the power of the root is nonnegative and squares back to the power of
// x, and on the nonnegative half SqrtUnique names such a value.
var SqrtOfPow = sqrtOfPowThm{family.Add(registry.ProofEntry{
	Name: "SqrtOfPow",
	Key:  "prop_222209c3b8e3e4d2",
	Build: family.Theorem(Statement{
		Binders: "∀x:real. ∀m:num.",
		Hypotheses: []string{
			"&0 ≤ x",
		},
		Conclusion: "real_pow(real_sqrt(x), m) = real_sqrt(real_pow(x, m))",
	},
		func(a *Argument, x, m Term, nonneg Fact) {
			root, two := a.Term("real_sqrt(x)"), a.Term("2")
			rootNonneg := a.Have(
				"the root is nonnegative, and so is its power",
				"&0 ≤ real_sqrt(x) ∧ &0 ≤ real_pow(real_sqrt(x), m)",
				By(nonneg, At(SqrtNonneg, x), At(real_pow.PowNonneg, root, m)))
			exponents := a.Have(
				"the two exponents commute",
				"2 * m = m * 2",
				ByArith())
			squares := a.Have(
				"x is the square of the root, so its power is the square of the root's power",
				"real_pow(x, m) = real_pow(real_pow(real_sqrt(x), m), 2)",
				By(
					Normalized,
					nonneg,
					exponents,
					At(SqrtPowTwo, x),
					At(real_pow.PowPow, root, two, m),
					At(real_pow.PowPow, root, m, two)))
			a.Show(
				"so that power of the root is the root of the power",
				By(
					squares,
					rootNonneg,
					At(SqrtUnique, a.Term("real_pow(x, m)"), a.Term("real_pow(real_sqrt(x), m)"))))
		}),
})}

// SqrtPos — the root of a positive real is positive: it is nonnegative, and it
// is not zero, its square being the real itself.
var SqrtPos = sqrtPosThm{family.Add(registry.ProofEntry{
	Name: "SqrtPos",
	Key:  "prop_a627eafa9f997566",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 < x",
		},
		Conclusion: "&0 < real_sqrt(x)",
	},
		func(a *Argument, x *Expr[Real], positive Fact) {
			a.Show(
				"the root is nonnegative and squares to x, which is not zero",
				ByArith(positive, SqrtNonneg.At(x), SqrtPowTwo.At(x)))
		}),
})}

// SqrtMul — the signed root is multiplicative, for every x and y. The
// product real_sqrt(x)·real_sqrt(y) has the sign sgn(x)·sgn(y) = sgn(x·y)
// and the square |x|·|y| = |x·y|, which are the sign and the square of
// real_sqrt(x·y) (Works). Two reals with one sign and one square are
// equal: their sum times their difference is the difference of their
// squares, 0, so either the difference vanishes, or the sum does — and
// then each is the other's negative, their common sign is its own
// negative, 0, and both are 0.
var SqrtMul = sqrtMulThm{family.Add(registry.ProofEntry{
	Name: "SqrtMul",
	Key:  "prop_a1aee9f38b7a5482",
	Build: family.Theorem("∀x y:real. real_sqrt(x) * real_sqrt(y) = real_sqrt(x * y)",
		func(a *Argument, x, y *Expr[Real]) {
			xy := a.TermAs[Real]("x * y")
			rootX, rootY := a.TermAs[Real]("real_sqrt(x)"), a.TermAs[Real]("real_sqrt(y)")
			root := a.TermAs[Real]("real_sqrt(x * y)")
			square := a.Have(
				"the product squares to |x|·|y| = |x·y|",
				"real_pow(real_sqrt(x) * real_sqrt(y), 2) = |x * y|",
				By(
					real_pow.MulPowDistrib.At(rootX, rootY, a.TermAs[Nat]("2")),
					Works.At(x),
					Works.At(y),
					real_sgn_abs.AbsMul.At(x, y)))
			sign := a.Have(
				"and has the sign sgn(x)·sgn(y) = sgn(x·y)",
				"sgn(real_sqrt(x) * real_sqrt(y)) = sgn(x * y)",
				By(
					Normalized,
					real_sgn_abs.SgnMul.At(rootX, rootY),
					Works.At(x),
					Works.At(y),
					real_sgn_abs.SgnMul.At(x, y)))
			a.Cases(a.Term("real_sqrt(x) * real_sqrt(y) + real_sqrt(x * y) = &0"))
			a.When(
				"if the two sum to 0, each is the other's negative, and both are 0",
				func(b *Argument, opposite Fact) {
					negated := b.Have(
						"the product is the negative of the root",
						"real_sqrt(x) * real_sqrt(y) = -real_sqrt(x * y)",
						ByArith(opposite))
					flipped := b.Have(
						"so the negative of the root has the sign of x·y",
						"sgn(-real_sqrt(x * y)) = sgn(x * y)",
						By(Normalized, negated, sign))
					signZero := b.Have(
						"as the root has, and the sign of a negative is the negative sign: the root's sign is 0",
						"sgn(real_sqrt(x * y)) = &0",
						ByArith(flipped, Works.At(xy), real_sgn_abs.SgnOdd.At(root)))
					rootZero := b.Have(
						"so the root's size, its sign times itself, is 0, and the root is 0",
						"real_sqrt(x * y) = &0",
						By(
							Normalized,
							signZero,
							real_sgn_abs.SgnMulSelfIsAbs.At(root),
							real_ring.MulLeftZero.At(root),
							real_sgn_abs.AbsVanishes.At(root)))
					b.Show(
						"and so is the product, its negative",
						ByArith(negated, rootZero))
				})
			a.Otherwise(
				"otherwise the sum is not 0, and it times the difference is the difference of the squares, 0",
				func(b *Argument, apart Fact) {
					factored := b.Have(
						"the sum times the difference is the difference of the squares, both |x·y|",
						"(real_sqrt(x) * real_sqrt(y) + real_sqrt(x * y)) * "+
							"(real_sqrt(x) * real_sqrt(y) - real_sqrt(x * y)) = "+
							"&0",
						ByArith(square, Works.At(xy)))
					difference := b.TermAs[Real]("real_sqrt(x) * real_sqrt(y) - real_sqrt(x * y)")
					vanishing := b.Have(
						"a product vanishes only where a factor does, and the sum does not",
						"real_sqrt(x) * real_sqrt(y) - real_sqrt(x * y) = &0",
						By(
							apart,
							factored,
							real_ring.MulEqZero.At(
								b.TermAs[Real]("real_sqrt(x) * real_sqrt(y) + real_sqrt(x * y)"), difference)))
					b.Show(
						"so the difference vanishes",
						ByArith(vanishing))
				})
		}),
})}
