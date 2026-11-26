// norm.go — the norm: what it is made of, and the elementary
// inequalities every later estimate is assembled from.
//
// `‖u‖_n` is the root of the form at (u, u), so every fact here
// is one law of the square root (real/real_sqrt) applied at the
// nonnegative real `dot(u, u)`. Two of them are read by everything
// after: the norm's square is the form back (NormPow2), and the norm
// is nonnegative (NormNonneg).
//
// The rest are the norm's arithmetic. NormVecZero and NormBasisVector
// evaluate: the form vanishes at the zero vector, and the root of zero
// is zero; a basis vector inside the range pairs with itself to its
// coordinate at its own index, 1, and 1 is its own root. The others read
// the root from the identifying side rather than the evaluating one —
// the law that names a nonnegative real by its square
// (real_sqrt.SqrtUnique), or the law that reads a bound on a square
// back as a bound on a root (real_sqrt.SqrtLowerBound). NormSmul: ‖c·u‖
// is |c|·‖u‖, with no case on the sign of c, because |c|·‖u‖ is
// nonnegative and squares to the scaled form; read at c = 1/‖u‖ it gives
// NormNormalize, a vector of nonzero norm so scaled has norm 1.
// ComponentLeNorm: a coordinate inside the active range is no larger in
// size than the norm, one square being at most the sum of the squares it
// belongs to. CoordinateNormBound runs the other way: coordinates below n
// at most b in size give a norm at most n·b.
//
// Cauchy–Schwarz, `⟨u,v⟩ ≤ ‖u‖·‖v‖`: the form is nonnegative at
// w = ‖v‖·u − ‖u‖·v, and by bilinearity ⟨w,w⟩ is
// 2(‖u‖‖v‖)² − 2‖u‖‖v‖⟨u,v⟩ once ⟨u,u⟩ and ⟨v,v⟩ are read as the
// squared norms; when both norms are positive the factor ‖u‖‖v‖
// cancels. When a norm vanishes so does the form at that vector, hence
// its form with anything, and both sides are zero. It reads the two
// norm laws above and NullVectorOrthogonal.

package euclidean

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// NormPow2 — unfold the norm to the root of the form; the form is
// nonnegative (DotPosLe), so the root squares back to it by the sqrt
// chapter's law.
var NormPow2 = normPow2Thm{family.Add(registry.ProofEntry{
	Name: "NormPow2",
	Key:  "prop_88ec75ec1749ba84",
	Build: family.Theorem("∀n:num. ∀u:(num → real). real_pow(‖u‖_n, 2) = ⟪u, u⟫_n",
		func(a *Argument, n *Expr[Nat], u *Vec[Real, DimN]) {
			a.Do(Unfold(VecNormDef), By(DotPosLe.At(u), real_sqrt.SqrtPowTwo))
		}),
})}

// NormNonneg — the norm is nonnegative: the form under the root is
// nonnegative, and the root of a nonnegative real is nonnegative — the
// sqrt chapter's law (real_sqrt.SqrtNonneg).
var NormNonneg = normNonnegThm{family.Add(registry.ProofEntry{
	Name: "NormNonneg",
	Key:  "prop_e0ae567ab56b0d35",
	Build: family.Theorem("∀n:num. ∀u:(num → real). &0 ≤ ‖u‖_n",
		func(a *Argument, n *Expr[Nat], u *Vec[Real, DimN]) {
			a.Show(
				"the form is nonnegative, and so is its root",
				Unfold(VecNormDef),
				By(DotPosLe.At(u), real_sqrt.SqrtNonneg))
		}),
})}

// NormVecZero — the norm of the zero vector is zero: under the root, the
// form annihilates the zero vector (the dot chapter's law, read at ℝ),
// and the root of zero is zero.
var NormVecZero = normVecZeroThm{family.Add(registry.ProofEntry{
	Name: "NormVecZero",
	Key:  "prop_f35a279746f6f395",
	Build: family.Theorem("∀n:num. ‖vec_zero‖_n = real_of_num(0)",
		func(a *Argument, n Term) {
			// The sqrt chapter states its zero law as `&0 = real_sqrt(&0)`, so
			// reading it as an evaluation is its reverse.
			a.Show(
				"the form at the zero vector is zero, and the root of zero is zero",
				Unfold(VecNormDef),
				Simp(Fwd(dot.ZeroLeft.Read(real_ring.CommRing)), Rev(real_sqrt.SqrtZero)),
				TrivialNormalized())
		}),
})}

// NormBasisVector — a basis vector whose index lies in the range has norm
// 1: the form pairs it with itself to its own coordinate at that index
// (dot.BasisVectorLeft), which is 1, and 1 is its own root.
var NormBasisVector = normBasisVectorThm{family.Add(registry.ProofEntry{
	Name: "NormBasisVector",
	Key:  "prop_642f2543d2d63983",
	Build: family.Theorem(Statement{
		Binders: "∀n j:num.",
		Hypotheses: []string{
			"j < n",
		},
		Conclusion: "‖basis_vector(j)‖_n = &1",
	},
		func(a *Argument, n, j *Expr[Nat], below Fact) {
			zero, one := a.TermAs[Real]("&0"), a.TermAs[Real]("&1")
			basis := a.VecAs[Real, DimN]("basis_vector(j)")
			form := a.Have(
				"the basis vector pairs with itself to its coordinate at j, which is 1",
				"⟪basis_vector(j), basis_vector(j)⟫_n = &1",
				ByArith(
					below,
					dot.BasisVectorLeft.Read(real_ring.CommRing).At(j, basis),
					vec_space.BasisVectorDef.At(zero, one, j, j)))
			a.Show(
				"so its norm is the root of 1, which is 1",
				ByArith(form, VecNormDef.At(basis), real_sqrt.SqrtUnique.At(one, one)))
		}),
})}

// NormSmul — scaling a vector scales its norm by the size of the
// scalar. One application of the square root's characterization does
// it, with no case on the sign of c: |c|·‖u‖ is a nonnegative real
// whose square is the form at c·u, and the norm at c·u is the root of
// that form, so the two are the same number.
var NormSmul = normSmulThm{family.Add(registry.ProofEntry{
	Name: "NormSmul",
	Key:  "prop_49bd1e97c95d4782",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num. ∀c:real. ∀u:(num → real).",
		Conclusion: "‖c • u‖_n = |c| * ‖u‖_n",
		Abbrev: Abbrev{
			{Name: "smulForm", Text: "c * (c * ⟪u, u⟫_n)"},
			{Name: "smulNorm", Text: "|c| * ‖u‖_n"},
		},
	},
		func(a *Argument, n *Expr[Nat], c *Expr[Real], u *Vec[Real, DimN]) {
			absC, normU := a.Term("|c|"), a.Term("‖u‖_n")
			formU := a.Term("⟪u, u⟫_n")
			two := a.Ctx().Numeral(2)

			form := a.Have(
				"the scalar comes out of each argument of the form",
				"⟪c • u, c • u⟫_n = «smulForm»",
				By(dot.SmulLeft.Read(real_ring.CommRing), dot.SmulRight.Read(real_ring.CommRing)))
			square := a.Have(
				"c·(c·⟨u,u⟩) is the square of |c|·‖u‖: squaring forgets the sign of c, and ‖u‖² is the form at u",
				"«smulForm» = real_pow(«smulNorm», 2)",
				By(
					At(real_pow.MulPowDistrib, absC, normU, two),
					At(real_pow.SquareOfAbs, c),
					NormPow2.At(u),
					At(real_pow.PowTwo, c),
					At(real_construction.MulAssoc, c, c, formU)))
			nonneg := a.Have(
				"|c|·‖u‖ is nonnegative, being a product of nonnegatives",
				"&0 ≤ «smulNorm»",
				By(At(real_sgn_abs.AbsNonneg, c), NormNonneg.At(u), At(real_construction.LessEqMul, absC, normU)))

			a.Show(
				"so |c|·‖u‖ is the root the norm at c·u unfolds to",
				By(
					form,
					square,
					nonneg,
					VecNormDef,
					At(real_sqrt.SqrtUnique, a.Term("«smulForm»"), a.Term("«smulNorm»"))))
		}),
})}

// NormNormalize — a vector of nonzero norm, scaled by the inverse of its
// norm, has norm 1: by NormSmul the scaled vector's norm is the size of
// 1/‖u‖ times ‖u‖; the norm is nonnegative, so that size is 1/‖u‖
// itself, and a nonzero real times its inverse is 1.
var NormNormalize = normNormalizeThm{family.Add(registry.ProofEntry{
	Name: "NormNormalize",
	Key:  "prop_61846cc956eeae81",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀u:(num → real).",
		Hypotheses: []string{
			"‖u‖_n ≠ &0",
		},
		Conclusion: "‖real_inv(‖u‖_n) • u‖_n = &1",
	},
		func(a *Argument, n *Expr[Nat], u *Vec[Real, DimN], nonzero Fact) {
			size := a.TermAs[Real]("‖u‖_n")
			a.Show(
				"the norm of the multiple is |1/‖u‖|·‖u‖ = 1/‖u‖·‖u‖, ‖u‖ being nonnegative, and that is 1",
				ByArith(
					nonzero,
					NormSmul.At(a.TermAs[Real]("real_inv(‖u‖_n)"), u),
					real_sgn_abs.AbsInv.At(size),
					real_sgn_abs.AbsFixedIffNonneg.At(size),
					NormNonneg.At(u)))
		}),
})}

// CauchySchwarz — ⟨u,v⟩ ≤ ‖u‖·‖v‖, from the positivity of the form at
// ‖v‖·u − ‖u‖·v, through the three norm laws it reads.
var CauchySchwarz = cauchySchwarzThm{family.Add(registry.ProofEntry{
	Name: "CauchySchwarz",
	Key:  "prop_73794f0005dea048",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num. ∀u v:(num → real).",
		Conclusion: "⟪u, v⟫_n ≤ ‖u‖_n * ‖v‖_n",
		Abbrev: Abbrev{
			{Name: "cauchyExpansion", Text: "&2 * (‖u‖_n * ‖v‖_n * (‖u‖_n * ‖v‖_n)) - " +
				"&2 * (‖u‖_n * ‖v‖_n * ⟪u, v⟫_n)"},
		},
	},
		func(a *Argument, n *Expr[Nat], u, v *Vec[Real, DimN]) {
			zero := a.Term("&0")
			normU, normV := a.Term("‖u‖_n"), a.Term("‖v‖_n")
			normProduct := a.Term("‖u‖_n * ‖v‖_n")
			form := a.Term("⟪u, v⟫_n")

			// A vanishing norm settles the inequality: the form at that vector
			// is its squared norm, zero, so the vector is null and its form
			// with the other is zero, while the right side is a product with 0.
			uNonzero := a.Unless(
				a.Term("‖u‖_n = &0"),
				"‖u‖ = 0: ⟨u,u⟩ = ‖u‖² = 0 makes ⟨u,v⟩ = 0, and the right side is 0·‖v‖",
				Given(func(z *Argument, uZero Fact) {
					z.Show(
						"both sides are zero",
						By(
							NullVectorOrthogonal.At(u, v),
							NormPow2.At(u),
							uZero,
							At(real_pow.PowTwo, normU),
							real_ring.MulLeftZero,
							real_order_ring.LessEqRefl))
				}))
			vNonzero := a.Unless(
				a.Term("‖v‖_n = &0"),
				"‖v‖ = 0: ⟨v,v⟩ = ‖v‖² = 0 makes ⟨v,u⟩ = 0, which "+
					"is ⟨u,v⟩ by symmetry, and the right side is ‖u‖·0",
				Given(func(z *Argument, vZero Fact) {
					z.Show(
						"both sides are zero",
						By(
							Normalized,
							NullVectorOrthogonal.At(v, u),
							NormPow2.At(v),
							vZero,
							dot.Sym.Read(real_ring.CommRing),
							At(real_pow.PowTwo, normV),
							real_ring.MulLeftZero,
							real_ring.MulRightZero,
							real_order_ring.LessEqRefl))
				}))

			// Both norms are positive: nonnegative and nonzero.
			uPos := a.Have(
				"‖u‖ is positive",
				"&0 < ‖u‖_n",
				By(uNonzero, NormNonneg.At(u), At(real_order_ring.LessThanSplit, zero, normU)))
			vPos := a.Have(
				"and so is ‖v‖",
				"&0 < ‖v‖_n",
				By(vNonzero, NormNonneg.At(v), At(real_order_ring.LessThanSplit, zero, normV)))

			// Take w = ‖v‖·u − ‖u‖·v. The form at w: expand it bilinearly,
			// read ⟨u,u⟩ and ⟨v,v⟩ as the squared norms and ⟨v,u⟩ as ⟨u,v⟩,
			// and collect.
			w := a.Let("w", a.Term("‖v‖_n • u - ‖u‖_n • v"))
			uu := a.Have(
				"⟨u,u⟩ is ‖u‖·‖u‖",
				"⟪u, u⟫_n = ‖u‖_n * ‖u‖_n",
				By(Normalized, NormPow2.At(u), At(real_pow.PowTwo, normU)))
			vv := a.Have(
				"⟨v,v⟩ is ‖v‖·‖v‖",
				"⟪v, v⟫_n = ‖v‖_n * ‖v‖_n",
				By(Normalized, NormPow2.At(v), At(real_pow.PowTwo, normV)))
			sym := a.Have(
				"the form is symmetric",
				"⟪v, u⟫_n = ⟪u, v⟫_n",
				By(dot.Sym.Read(real_ring.CommRing)))
			expand := a.Have(
				"the form at w is 2(‖u‖‖v‖)² − 2‖u‖‖v‖⟨u,v⟩",
				"⟪w, w⟫_n = «cauchyExpansion»",
				w.Rw(),
				Simp(
					Fwd(dot.SubLeft.Read(real_ring.CommRing)),
					Fwd(dot.SubRight.Read(real_ring.CommRing)),
					Fwd(dot.SmulLeft.Read(real_ring.CommRing)),
					Fwd(dot.SmulRight.Read(real_ring.CommRing))),
				uu.Rw(),
				sym.Rw(),
				vv.Rw(),
				ByArith(real_ring.RealSubDef))
			nonneg := a.Have(
				"and the form at w is nonnegative",
				"&0 ≤ «cauchyExpansion»",
				expand.RwRev(),
				By(DotPosLe.At(a.VecAs[Real, DimN]("w"))))

			// Halve — linear over the two products — then cancel the
			// positive factor ‖u‖‖v‖.
			bound := a.Have(
				"so ‖u‖‖v‖·⟨u,v⟩ ≤ ‖u‖‖v‖·(‖u‖‖v‖)",
				"‖u‖_n * ‖v‖_n * ⟪u, v⟫_n ≤ ‖u‖_n * ‖v‖_n * (‖u‖_n * ‖v‖_n)",
				ByArith(nonneg))
			prodPos := a.Have(
				"‖u‖‖v‖ is positive",
				"&0 < ‖u‖_n * ‖v‖_n",
				By(uPos, vPos, At(real_order_ring.MulPos, normU, normV)))
			a.Show(
				"cancel the positive factor ‖u‖‖v‖",
				By(prodPos, bound, At(real_order_ring.LessEqCancelMulLeft, normProduct, form, normProduct)))
		}),
})}

// ComponentLeNorm — squaring reduces the claim to one about the form:
// the coordinate's square is a single summand of ⟨u,u⟩, and a summand
// of a sum of nonnegative terms is within the sum.
//
// The sum chapter's term bound is what supplies that, and it is read at
// the sum ITSELF, which is what makes it usable here with no auxiliary
// bound to find: its hypothesis then says the form stands within the
// form, and what comes back is the summand bound. Coming back down
// needs no sign anywhere — the root law asks only that the square be
// under the radicand, and a coordinate and its size have one square
// between them.
var ComponentLeNorm = componentLeNormThm{family.Add(registry.ProofEntry{
	Name: "ComponentLeNorm",
	Key:  "prop_7721ea6fe447b8f7",
	Build: family.Theorem(Statement{
		Binders: "∀n i:num. ∀u:(num → real).",
		Hypotheses: []string{
			"i < n",
		},
		Conclusion: "|u(i)| ≤ ‖u‖_n",
	},
		func(a *Argument, n, i *Expr[Nat], u *Vec[Real, DimN], below Fact) {
			coord := a.Term("u(i)")
			summand := a.Term("λk:num. u(k) * u(k)")

			inRange := a.Have(
				"the coordinate's index is a point of the active range",
				"i ∈ {k:num | k < n}",
				BySets(below))
			squares := a.Have(
				"every summand of the form at (u, u) is a square, hence nonnegative",
				"∀j:num. j ∈ {k:num | k < n} ⇒ &0 ≤ u(j) * u(j)",
				By(real_order_ring.SquareNonneg))
			asSum := a.Have(
				"the form is the sum of those squares, so the sum is within the form",
				"Σ_{k<n} u(k) * u(k) ≤ ⟪u, u⟫_n",
				By(DotIsSum.At(u, u), real_order_ring.LessEqRefl))
			// The bound the term law is read at is the form itself; what it
			// asks for is the three facts above and the range's finiteness.
			// Only the summand has to be named — the rest it reads off the
			// goal and the context.
			termLe := a.Have(
				"so the summand at i is within the form",
				"u(i) * u(i) ≤ ⟪u, u⟫_n",
				By(
					squares,
					inRange,
					asSum,
					At(num_segment.FiniteBelowStrict, n),
					Where(real_sum.TermBound, "f", summand)))
			squareBound := a.Have(
				"and the square of the coordinate's size is that same summand",
				"real_pow(|u(i)|, 2) ≤ ⟪u, u⟫_n",
				By(Normalized, termLe, At(real_pow.PowTwo, coord), At(real_pow.SquareOfAbs, coord)))

			a.Show(
				"a size whose square is under the form is under the form's root, and that root is the norm",
				Unfold(VecNormDef),
				By(squareBound, real_sqrt.SqrtLowerBound))
		}),
})}

// CoordinateNormBound — a vector whose coordinates below n are at most b in
// size has norm at most n·b: the square of the norm is the sum of the n
// squares of the coordinates, each at most b², and n·b² is at most (n·b)².
var CoordinateNormBound = coordinateNormBoundThm{family.Add(registry.ProofEntry{
	Name: "CoordinateNormBound",
	Key:  "prop_cac9c559ff0c0475",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀u:(num → real). ∀b:real.",
		Hypotheses: []string{
			"∀i:num. i < n ⇒ |u(i)| ≤ b",
		},
		Conclusion: "‖u‖_n ≤ &n * b",
	}, func(a *Argument, n *Expr[Nat], u *Arrow[Nat, Real], b *Expr[Real], bounded Fact) {
		indices := a.TermAs[Set[Nat]]("{j:num | j < n}")
		vector := a.VecAt[Real](n, "u")
		scaled := a.TermAs[Real]("&n * b")
		norm := a.TermAs[Real]("‖u‖_n")
		squares := a.Have(
			"each coordinate below n squares to at most b²",
			"∀i:num. i ∈ {j:num | j < n} ⇒ u(i) * u(i) ≤ b * b",
			Derive(func(c *Argument) {
				i := c.FixAs[Nat]("i")
				below := c.Assume()
				c.Show(
					"-b ≤ u(i) ≤ b",
					ByArith(bounded.At(i), below, real_sgn_abs.AbsBounds.At(u.Apply(i), b)))
			}))
		squareSum := a.Have(
			"so the squared norm, the sum of these n squares, is at most n·b²",
			"‖u‖_n ^ 2 ≤ &n * (b * b)",
			By(
				squares,
				NormPow2.At(vector),
				DotIsSum.At(vector, vector),
				real_sum.Bound.At(
					indices, a.TermAs[Fun[Nat, Real]]("λi:num. u(i) * u(i)"), a.TermAs[Real]("b * b")),
				num_segment.HasSizeBelowStrict.At(n),
				cardinality.HasSizeDef.At(indices, n)))
		a.Cases(a.Term("0 < n"))
		a.When(
			"in positive dimension the bound is (n·b)²",
			func(c *Argument, positive Fact) {
				nonneg := c.Have(
					"b is at least |u(0)|, which is nonnegative",
					"&0 ≤ b",
					ByArith(
						bounded.At(c.TermAs[Nat]("0")),
						positive,
						real_sgn_abs.AbsNonneg.At(c.TermAs[Real]("u(0)"))))
				factors := c.Have(
					"n is at least 1 and n·b² is nonnegative",
					"&1 ≤ &n ∧ &0 ≤ &n * (b * b)",
					ByArith(positive))
				widen := c.Have(
					"n·b² is at most (n·b)²",
					"&n * (b * b) ≤ (&n * b) * (&n * b)",
					ByArith(factors))
				squared := c.Have(
					"so the squared norm is at most (n·b)²",
					"‖u‖_n ^ 2 ≤ (&n * b) ^ 2",
					By(
						widen,
						squareSum,
						real_pow.PowTwo.At(scaled),
						real_construction.LessEqTrans.At(
							c.TermAs[Real]("‖u‖_n ^ 2"),
							c.TermAs[Real]("&n * (b * b)"),
							c.TermAs[Real]("(&n * b) * (&n * b)"))))
				c.Show(
					"and the norm and n·b are nonnegative, so the norm is at most n·b",
					ByArith(
						positive,
						nonneg,
						squared,
						NormNonneg.At(vector),
						real_sgn_abs.AbsFixedIffNonneg.At(norm),
						real_sgn_abs.AbsFixedIffNonneg.At(scaled),
						real_pow.AbsLessEqIffPowTwoLessEq.At(norm, scaled)))
			})
		a.Otherwise(
			"in dimension 0 the squared norm is at most 0",
			func(c *Argument, empty Fact) {
				zero := c.Have(
					"n is 0",
					"n = 0",
					ByArith(empty))
				c.Show(
					"so the norm is 0",
					ByArith(zero, squareSum, NormNonneg.At(vector)))
			})
	}),
})}
