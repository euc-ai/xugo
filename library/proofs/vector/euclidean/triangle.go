// triangle.go — the triangle inequality, for two vectors and along a
// fold, and the convexity of a ball.
//
// ‖u + v‖ ≤ ‖u‖ + ‖v‖. Both sides are nonnegative, so the
// inequality is equivalent to the one between their squares. The left
// square is the form on the diagonal of the sum, which bilinearity opens
// to ‖u‖² + 2·dot(u, v) + ‖v‖²; Cauchy–Schwarz bounds the cross
// term dot(u, v) by ‖u‖·‖v‖, and the right side is exactly the
// perfect square (‖u‖ + ‖v‖)². The square root, monotone on the
// nonnegative reals, carries the bound between squares back to the norms.
// The argument rests on three lemmas of the chapter: Cauchy–Schwarz, the
// norm's nonnegativity, and the identity that the square of the norm is
// the form on the diagonal.
//
// The same inequality along a finite fold. A finite family of vectors has
// a sum, `iterated_op(vec_add, s, F)` (vector/vec_space's README says why
// that is the fold mechanism itself and not a constant of the chapter's
// own), and its norm is never more than the sum of the norms of its terms.
// That is the chapter's one induction — over the index set, in the strong
// form, because the recursion's insert clause asks for exactly what that
// form grants: the index laid in is new, and the set it is laid into is
// finite. The two folds step together, the vectors' on the left and ℝ's on
// the right: over ∅ each is the element it starts from, and one point
// further each has given up one term, where the two-vector inequality
// prices the new vector and the bound carried prices the rest.
//
// An open ball is convex: a point of the segment between two points of
// the ball is offset from the centre by a weighted average of their
// offsets, which the triangle inequality and the norm's homogeneity keep
// below the radius.

package euclidean

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// NormTriangle — the triangle inequality for the Euclidean norm, through
// Cauchy–Schwarz and the two norm laws. The estimate between the squares
// is one chain: the form on the diagonal of the sum opens by bilinearity
// and symmetry into the squared norms and twice the cross term,
// Cauchy–Schwarz prices the cross term, and what remains is the perfect
// square. The arithmetic closer reads a squared norm and a product of
// norms as monomials, so each leg is the laws it names and nothing is
// spelled for the closer's sake; the root then carries the bound
// back to the norms, both sides being nonnegative.
var NormTriangle = normTriangleThm{family.Add(registry.ProofEntry{
	Name: "NormTriangle",
	Key:  "prop_ebedc0792f6aebf2",
	Build: family.Theorem(
		"∀n:num. ∀u v:(num → real). ‖u + v‖_n ≤ ‖u‖_n + ‖v‖_n",
		func(a *Argument, n *Expr[Nat], u, v *Vec[Real, DimN]) {
			sum := a.VecAs[Real, DimN]("u + v")
			nu := a.Term("‖u‖_n")
			nv := a.Term("‖v‖_n")
			natSum := a.Term("‖u + v‖_n")
			sumNorms := a.Term("‖u‖_n + ‖v‖_n")

			// ‖u + v‖² = ‖u‖² + 2⟨u,v⟩ + ‖v‖² ≤ ‖u‖² + 2‖u‖‖v‖ + ‖v‖² = (‖u‖ + ‖v‖)².
			squaredBound := a.CalcLeibniz(real_order_ring.OrderCalc(a.Ctx()),
				a.Term("real_pow(‖u + v‖_n, 2)"),
				EqLeg(
					a.Term("real_pow(‖u‖_n, 2) + &2 * ⟪u, v⟫_n + real_pow(‖v‖_n, 2)"),
					"the form on the diagonal opens by bilinearity, its diagonal values "+
						"are the squared norms, and the two cross terms are one by symmetry",
					ByArith(
						dot.AddLeft.Read(real_ring.CommRing),
						dot.AddRight.Read(real_ring.CommRing),
						dot.Sym.Read(real_ring.CommRing),
						NormPow2.At(sum),
						NormPow2.At(u),
						NormPow2.At(v))),
				LeLeg(
					a.Term("real_pow(‖u‖_n, 2) + &2 * (‖u‖_n * ‖v‖_n) + real_pow(‖v‖_n, 2)"),
					"Cauchy–Schwarz bounds the cross term",
					ByArith(CauchySchwarz.At(u, v))),
				EqLeg(
					a.Term("real_pow(‖u‖_n + ‖v‖_n, 2)"),
					"which is the perfect square",
					ByArith()))

			// Both sides are nonnegative, so the square root is monotone.
			nnSum := a.Have(
				"each norm is nonnegative, and so is their sum",
				"&0 ≤ ‖u‖_n + ‖v‖_n",
				By(NormNonneg.At(u), NormNonneg.At(v), At(real_order_ring.AddNonneg, nu, nv)))
			a.Show(
				"both sides being nonnegative, the bound between squares carries back to the norms",
				By(
					squaredBound,
					NormNonneg.At(sum),
					nnSum,
					At(real_pow.AbsLessEqIffPowTwoLessEq, natSum, sumNorms),
					At(real_sgn_abs.AbsFixedIffNonneg, natSum),
					At(real_sgn_abs.AbsFixedIffNonneg, sumNorms)))
		}),
})}

// NormIterateLe — the two-term triangle inequality, applied once per
// point of the index set as it grows. The ∅ case is the zero vector's
// vanishing norm; the insert case is one turn of each recursion, the new
// vector priced by the inequality and the rest by the bound carried.
var NormIterateLe = normIterateLeThm{family.Add(registry.ProofEntry{
	Name: "NormIterateLe",
	Key:  "prop_9877b1e314a11a72",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num. ∀s:set(num). ∀F:(num → num → real).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "‖Σ_{i∈s} F(i)‖_n ≤ Σ_{i∈s} ‖F(i)‖_n",
		},
		func(a *Argument, n *Expr[Nat], s *Expr[Set[Nat]], F *Arrow[Nat, Fun[Nat, Real]],
			finite Fact) {
			// The one thing the fold mechanism asks of the vectors, read at
			// the real ring once here. Below this point the ring is read
			// once more — in the ∅ case, where the element the fold starts
			// from is the zero vector.
			vectors := a.Have(
				"pointwise addition folds",
				"monoidal_op(vec_add)",
				By(vec_space.MonoidalVecAdd.Read(real_ring.CommRing)))

			a.Show(
				"so the bound holds over every finite index set, s among them",
				ByInduction(finite_set.FiniteInductFresh, finite,

					// The two clause packs are polymorphic in their index and
					// carrier types; a rewrite installs them at the chapter's.
					Case(
						"∅: the fold is the element it starts from, the zero "+
							"vector, whose norm is zero; and the empty sum is zero",
						Simp(
							Fwd(monoidal.Clauses.Inst(
								TypeBinder.BindB[Fun[Nat, Real]](), TypeBinder.BindA[Nat](), TypeBinder.BindC[Nat]())),
							Fwd(vec_space.NeutralVecAdd.Read(real_ring.CommRing)),
							Fwd(NormVecZero),
							Fwd(real_sum.Clauses.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindC[Nat]()))),
						By(real_order_ring.LessEqRefl)),

					Case(
						"insert: the new vector's norm splits off by the two-term "+
							"inequality, and the bound carried prices the rest",
						Derive(func(b *Argument) {
							b.Fix()               // x — the index laid in
							b.Fix("t")            // the set it enlarges
							carried := b.Assume() // the bound at t, x ∉ t, finite(t)

							estimate := b.CalcOrder(real_order_ring.OrderCalc(b.Ctx()),
								b.Term("‖Σ_{i∈insert(x, t)} F(i)‖_n"),
								LeLeg(
									b.Term("‖F(x)‖_n + ‖Σ_{i∈t} F(i)‖_n"),
									"the enlarged fold gives up the new vector, whose norm the two-term inequality splits off",
									By(vectors, carried, monoidal.OneTurn, NormTriangle)),
								LeLeg(
									b.Term("‖F(x)‖_n + Σ_{i∈t} ‖F(i)‖_n"),
									"and the bound carried over t prices the rest, the new norm riding along on both sides",
									By(carried, real_order_ring.LessEqAddLeft)))

							b.Show(
								"which is the enlarged sum of norms, grown by exactly the new term's norm",
								By(carried, real_sum.Clauses, estimate))
						}))))
		}),
})}

// SegmentInBall — an open ball is convex: the segment between two points
// of the ball stays in it. The offset of the point u + t•(w − u) from the
// centre is the weighted average (1 − t)•(u − c) + t•(w − c), so its norm
// is at most (1 − t)·‖u − c‖ + t·‖w − c‖, the weights totalling one. Both
// norms are below r; the average is strictly below r because at t = 0
// the point is u itself, and for t > 0 the second weight carries the
// strict inequality.
var SegmentInBall = segmentInBallThm{family.Add(registry.ProofEntry{
	Name: "SegmentInBall",
	Key:  "prop_91b3e1a345b6b0a6",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀c u w:(num → real). ∀r t:real.",
		Hypotheses: []string{
			"‖u - c‖_n < r",
			"‖w - c‖_n < r",
			"&0 ≤ t",
			"t ≤ &1",
		},
		Conclusion: "‖u + t • (w - u) - c‖_n < r",
	},
		func(
			a *Argument,
			n *Expr[Nat],
			c, u, w *Vec[Real, DimN],
			r, t *Expr[Real],
			nearU, nearW, above, below Fact,
		) {
			fromU := a.VecAs[Real, DimN]("u - c")
			fromW := a.VecAs[Real, DimN]("w - c")
			distanceU := a.TermAs[Real]("‖u - c‖_n")
			distanceW := a.TermAs[Real]("‖w - c‖_n")
			rest := a.TermAs[Real]("&1 - t")
			offset := a.Have(
				"the point's offset from the centre is the weighted average of u − c and w − c",
				"u + t • (w - u) - c = (&1 - t) • (u - c) + t • (w - c)",
				Funext(),
				Unfold(vec_space.VecAddDef),
				Unfold(vec_space.VecSubDef),
				Unfold(vec_space.VecScalarMulDef),
				ByArith())
			weights := a.Have(
				"both weights are nonnegative, so each is its own size",
				"|&1 - t| = &1 - t ∧ |t| = t",
				ByArith(above, below))
			average := a.Have(
				"so the offset is at most the weighted average of ‖u − c‖ and ‖w − c‖",
				"‖u + t • (w - u) - c‖_n ≤ (&1 - t) * ‖u - c‖_n + t * ‖w - c‖_n",
				offset.Rw(),
				ByArith(
					weights,
					NormTriangle.At(a.VecAs[Real, DimN]("(&1 - t) • (u - c)"), a.VecAs[Real, DimN]("t • (w - c)")),
					NormSmul.At(rest, fromU),
					NormSmul.At(t, fromW)))
			first := a.Have(
				"the first weight scales the bound on ‖u − c‖",
				"(&1 - t) * ‖u - c‖_n ≤ (&1 - t) * r",
				ByArith(nearU, below, real_order_ring.LessEqMulLeft.At(rest, distanceU, r)))
			a.Cases(a.Term("t = &0"))
			a.When(
				"at t = 0 the point is u itself, inside the ball",
				func(b *Argument, zero Fact) {
					b.Show(
						"the average is ‖u − c‖ alone",
						ByArith(average, nearU, Scaled(distanceU, zero), Scaled(distanceW, zero)))
				})
			a.Otherwise(
				"for t > 0 the second weight carries the strict inequality",
				func(b *Argument, positive Fact) {
					b.Show(
						"t·‖w − c‖ is strictly below t·r, and (1 − t)·‖u − c‖ at most (1 − t)·r",
						ByArith(
							average,
							first,
							positive,
							above,
							nearW,
							real_order_ring.LessThanMulLeft.At(t, distanceW, r)))
				})
		}),
})}
