// face_iterate.go — the iterated faces of a simplex: face_iterate_top
// removes the top k vertices (the last face taken k times),
// face_iterate_bottom the bottom k (the 0-th face taken k times), and
// removing k + 1 is one more last (0-th) face after removing k. An
// iterate of an n-simplex is an (n − k)-simplex, and a single face of
// x passes an iterate as the face identity says, the vertices counted
// in x: at a vertex below the top k + 1 (outside the bottom k) it
// commutes with the removal, its index unchanged (lowered by k), and at
// one of the top (bottom) k + 1 it is absorbed by one more removal. A
// degeneracy of x passes as the mixed identities say: at a vertex
// outside the bottom k it commutes with their removal, its dimension
// and index lowered by k, and at one of the top k + 1 it is absorbed
// when the top k + 1 vertices of the degenerate simplex are removed.

package simplicial_set

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/registry"
)

// FaceIterateTopDef — `face_iterate_top(d, n, k, x)`: the n-simplex x
// with its top k vertices removed, the last face taken k times. Under
// a structure the text writes `face_iterate_top(n, k, x)`.
var FaceIterateTopDef = faceIterateTopDefThm{family.Define(registry.DefEntry{
	Name:     "FaceIterateTopDef",
	Key:      "prop_975217044e13bd6c",
	Const:    "face_iterate_top",
	Type:     "(num → num → A → A) → num → num → A → A",
	Implicit: []string{"d"},
	Equations: []string{
		"∀d:(num → num → A → A). ∀n:num. ∀x:A. face_iterate_top(d, n, 0, x) = x",
		"∀d:(num → num → A → A). ∀n k:num. ∀x:A. " +
			"    face_iterate_top(d, n, suc(k), x) = d(n - k, n - k, face_iterate_top(d, n, k, x))",
	},
})}

// FaceIterateBottomDef — `face_iterate_bottom(d, n, k, x)`: the
// n-simplex x with its bottom k vertices removed, the 0-th face taken
// k times. Under a structure the text writes
// `face_iterate_bottom(n, k, x)`.
var FaceIterateBottomDef = faceIterateBottomDefThm{family.Define(registry.DefEntry{
	Name:     "FaceIterateBottomDef",
	Key:      "prop_16726b3c0947ba36",
	Const:    "face_iterate_bottom",
	Type:     "(num → num → A → A) → num → num → A → A",
	Implicit: []string{"d"},
	Equations: []string{
		"∀d:(num → num → A → A). ∀n:num. ∀x:A. face_iterate_bottom(d, n, 0, x) = x",
		"∀d:(num → num → A → A). ∀n k:num. ∀x:A. " +
			"    face_iterate_bottom(d, n, suc(k), x) = d(n - k, 0, face_iterate_bottom(d, n, k, x))",
	},
})}

// FaceIterateTopSucc — removing the top k + 1 vertices of x is the last
// face of x with its top k removed: the definition's recursion clause,
// with suc(k) written k + 1.
var FaceIterateTopSucc = faceIterateTopSuccThm{family.Add(registry.ProofEntry{
	Name: "FaceIterateTopSucc",
	Key:  "prop_45df9b92433b96c7",
	Build: family.Theorem("∀d:(num → num → A → A). ∀n k:num. ∀x:A. "+
		"    face_iterate_top(d, n, k + 1, x) = d(n - k, n - k, face_iterate_top(d, n, k, x))",
		func(a *Argument) {
			a.Show(
				"with k + 1 read as suc(k), the recursion clause makes the two sides one term",
				Simp(Rev(nat_arith.Add1), Fwd(FaceIterateTopDef)),
				Basic())
		}),
})}

// FaceIterateBottomSucc — removing the bottom k + 1 vertices of x is the
// 0-th face of x with its bottom k removed: the definition's recursion
// clause, with suc(k) written k + 1.
var FaceIterateBottomSucc = faceIterateBottomSuccThm{family.Add(registry.ProofEntry{
	Name: "FaceIterateBottomSucc",
	Key:  "prop_cfcad22cbe82783b",
	Build: family.Theorem("∀d:(num → num → A → A). ∀n k:num. ∀x:A. "+
		"    face_iterate_bottom(d, n, k + 1, x) = d(n - k, 0, face_iterate_bottom(d, n, k, x))",
		func(a *Argument) {
			a.Show(
				"with k + 1 read as suc(k), the recursion clause makes the two sides one term",
				Simp(Rev(nat_arith.Add1), Fwd(FaceIterateBottomDef)),
				Basic())
		}),
})}

// FaceIterateTopIn — removing k ≤ n top vertices leaves an
// (n−k)-simplex: induction on k takes one more last face at each step.
var FaceIterateTopIn = faceIterateTopInThm{family.Add(registry.ProofEntry{
	Name: "FaceIterateTopIn",
	Key:  "prop_9ba2a1ba981f5825",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀n k:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n)",
			"k ≤ n",
		},
		Conclusion: "face_iterate_top(n, k, x) ∈ X.simplices(n - k)",
	},
		func(a *Argument, simplicial Fact) {
			a.Induct("k")
			a.Base(
				"removing no top vertex leaves x itself",
				Simp(Fwd(FaceIterateTopDef)),
				ByArith())
			a.Step(
				"one more last face lowers the dimension by one",
				func(b *Argument, ih Fact) {
					n := b.FixAs[Nat]()
					x := b.FixAs[A]()
					given := b.Conjuncts(
						b.Assume(),
						"x is an n-simplex",
						"and suc(k) ≤ n")
					simplex, bound := given[0], given[1]
					rangeK := b.Have(
						"k vertices can already be removed",
						"k ≤ n",
						ByArith(bound))
					dimension := b.Have(
						"x with its top k vertices removed has the successor dimension n − suc(k) + 1",
						"n - k = n - suc(k) + 1",
						ByArith(bound))
					iterated := b.Have(
						"the hypothesis places x with its top k vertices removed in dimension n − k",
						"face_iterate_top(n, k, x) ∈ X.simplices(n - k)",
						By(ih.At(n, x), simplex, rangeK))
					successorIn := b.Have(
						"the same simplex has the successor dimension read by the face law",
						"face_iterate_top(n, k, x) ∈ X.simplices(n - suc(k) + 1)",
						By(Normalized, iterated, dimension))
					y := b.TermAs[A]("face_iterate_top(n, k, x)")
					faceIn := b.Have(
						"its last face lies in dimension n − suc(k)",
						"X.d(n - suc(k) + 1, n - k, face_iterate_top(n, k, x)) ∈ X.simplices(n - suc(k))",
						ByArith(
							successorIn,
							FaceIn.Read(simplicial).At(b.TermAs[Nat]("n - suc(k)"), b.TermAs[Nat]("n - k"), y)))
					b.Show(
						"this last face is the next top iterate",
						Simp(Fwd(FaceIterateTopDef)),
						By(Normalized, faceIn, dimension))
				})
		}),
})}

// FaceIterateBottomIn — removing k ≤ n bottom vertices leaves an
// (n−k)-simplex: induction on k takes one more 0-th face at each step.
var FaceIterateBottomIn = faceIterateBottomInThm{family.Add(registry.ProofEntry{
	Name: "FaceIterateBottomIn",
	Key:  "prop_7d0f12c697b7b3d1",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀n k:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n)",
			"k ≤ n",
		},
		Conclusion: "face_iterate_bottom(n, k, x) ∈ X.simplices(n - k)",
	},
		func(a *Argument, simplicial Fact) {
			a.Induct("k")
			a.Base(
				"removing no bottom vertex leaves x itself",
				Simp(Fwd(FaceIterateBottomDef)),
				ByArith())
			a.Step(
				"one more 0-th face lowers the dimension by one",
				func(b *Argument, ih Fact) {
					n := b.FixAs[Nat]()
					x := b.FixAs[A]()
					given := b.Conjuncts(
						b.Assume(),
						"x is an n-simplex",
						"and suc(k) ≤ n")
					simplex, bound := given[0], given[1]
					rangeK := b.Have(
						"k vertices can already be removed",
						"k ≤ n",
						ByArith(bound))
					dimension := b.Have(
						"x with its bottom k vertices removed has the successor dimension n − suc(k) + 1",
						"n - k = n - suc(k) + 1",
						ByArith(bound))
					iterated := b.Have(
						"the hypothesis places x with its bottom k vertices removed in dimension n − k",
						"face_iterate_bottom(n, k, x) ∈ X.simplices(n - k)",
						By(ih.At(n, x), simplex, rangeK))
					successorIn := b.Have(
						"the same simplex has the successor dimension read by the face law",
						"face_iterate_bottom(n, k, x) ∈ X.simplices(n - suc(k) + 1)",
						By(Normalized, iterated, dimension))
					y := b.TermAs[A]("face_iterate_bottom(n, k, x)")
					faceIn := b.Have(
						"its 0-th face lies in dimension n − suc(k)",
						"X.d(n - suc(k) + 1, 0, face_iterate_bottom(n, k, x)) ∈ X.simplices(n - suc(k))",
						ByArith(
							successorIn,
							FaceIn.Read(simplicial).At(b.TermAs[Nat]("n - suc(k)"), b.TermAs[Nat]("0"), y)))
					b.Show(
						"this 0-th face is the next bottom iterate",
						Simp(Fwd(FaceIterateBottomDef)),
						By(Normalized, faceIn, dimension))
				})
		}),
})}

// FaceIterateTopFace — a face of x at a vertex below its top k + 1
// vertices commutes with the removal of the top k. By induction on k:
// the last face that removes one more vertex passes the i-th face by
// the face identity, i lying below it.
var FaceIterateTopFace = faceIterateTopFaceThm{family.Add(registry.ProofEntry{
	Name: "FaceIterateTopFace",
	Key:  "prop_60c112cd48219242",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀n k i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n + 1)",
			"i + k ≤ n",
		},
		Conclusion: "face_iterate_top(n, k, X.d(n + 1, i, x)) = " +
			"X.d(n + 1 - k, i, face_iterate_top(n + 1, k, x))",
	},
		func(a *Argument, simplicial Fact) {
			a.Induct("k")
			a.Base(
				"with no vertex removed both sides are the i-th face of x",
				Simp(Fwd(FaceIterateTopDef)),
				ByArith())
			a.Step(
				"removing one more vertex is one more last face, which passes the i-th",
				func(b *Argument, ih Fact) {
					n, i := b.FixAs[Nat](), b.FixAs[Nat]()
					x := b.FixAs[A]()
					given := b.Conjuncts(
						b.Assume(),
						"x is an (n + 1)-simplex",
						"and i + suc(k) ≤ n")
					simplex, bound := given[0], given[1]
					m, mIs := b.ObtainAs[Nat](
						"n − k, which exceeds i, is the successor of some m",
						"∃m:num. n - k = m + 1",
						ByArith(bound, nat_arith.NonzeroIsSucc.At(b.TermAs[Nat]("n - k"))))
					dimension := b.Have(
						"x with its top k vertices removed has dimension m + 2",
						"n + 1 - k = m + 2",
						ByArith(mIs, bound))
					lower := b.Have(
						"and with k + 1 removed, dimension m + 1",
						"n + 1 - suc(k) = m + 1",
						ByArith(mIs, bound))
					ranges := b.Have(
						"k is at most n + 1, and i lies below m + 2",
						"k ≤ n + 1 ∧ i < m + 2",
						ByArith(mIs, bound))
					k, top := b.TermAs[Nat]("k"), b.TermAs[Nat]("m + 2")
					y := b.TermAs[A]("face_iterate_top(n + 1, k, x)")
					yIn := b.Have(
						"x with its top k vertices removed is an (m + 2)-simplex",
						"face_iterate_top(n + 1, k, x) ∈ X.simplices(m + 2)",
						By(FaceIterateTopIn.Read(simplicial).At(b.TermAs[Nat]("n + 1"), k, x), simplex, ranges, dimension))
					hypothesis := b.Have(
						"the hypothesis at n, i and x",
						"face_iterate_top(n, k, X.d(n + 1, i, x)) = X.d(n + 1 - k, i, face_iterate_top(n + 1, k, x))",
						ByArith(ih.At(n, i, x), simplex, bound))
					b.Show(
						"the last face of the (m + 2)-simplex passes its i-th face",
						Simp(Fwd(FaceIterateTopDef)),
						CalcEq(
							Leg(
								b.TermAs[A]("X.d(m + 1, m + 1, X.d(m + 2, i, face_iterate_top(n + 1, k, x)))"),
								"the hypothesis, the dimensions written m + 1 and m + 2",
								By(hypothesis, mIs, dimension)),
							Leg(
								b.TermAs[A]("X.d(m + 1, i, X.d(m + 2, m + 2, face_iterate_top(n + 1, k, x)))"),
								"the face identity, i lying below m + 2",
								ByArith(FaceFace.Read(simplicial).At(m, i, top, y), yIn, ranges)),
							FinalLeg(
								"which is the right side, its dimensions written m + 1 and m + 2",
								By(dimension, lower)),
						))
				})
		}),
})}

// FaceIterateBottomFace — a face of x at a vertex not among its bottom
// k vertices commutes with their removal, its index lowered by k. By
// induction on k: the 0-th face that removes one more vertex passes the
// face, now at the positive index i − k, by the face identity.
var FaceIterateBottomFace = faceIterateBottomFaceThm{family.Add(registry.ProofEntry{
	Name: "FaceIterateBottomFace",
	Key:  "prop_7b3f016b93ced424",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀n k i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n + 1)",
			"k ≤ i",
			"i ≤ n + 1",
			"k ≤ n",
		},
		Conclusion: "face_iterate_bottom(n, k, X.d(n + 1, i, x)) = " +
			"X.d(n + 1 - k, i - k, face_iterate_bottom(n + 1, k, x))",
	},
		func(a *Argument, simplicial Fact) {
			a.Induct("k")
			a.Base(
				"with no vertex removed both sides are the i-th face of x",
				Simp(Fwd(FaceIterateBottomDef)),
				ByArith())
			a.Step(
				"removing one more vertex is one more 0-th face, which passes the face at i − k",
				func(b *Argument, ih Fact) {
					n, i := b.FixAs[Nat](), b.FixAs[Nat]()
					x := b.FixAs[A]()
					given := b.Conjuncts(
						b.Assume(),
						"x is an (n + 1)-simplex",
						"suc(k) ≤ i",
						"i ≤ n + 1",
						"and suc(k) ≤ n")
					simplex, above, upTo, short := given[0], given[1], given[2], given[3]
					m, mIs := b.ObtainAs[Nat](
						"n − k, which is positive, is the successor of some m",
						"∃m:num. n - k = m + 1",
						ByArith(short, nat_arith.NonzeroIsSucc.At(b.TermAs[Nat]("n - k"))))
					_, pIs := b.ObtainAs[Nat](
						"and i − k, positive too, the successor of some p",
						"∃p:num. i - k = p + 1",
						ByArith(above, nat_arith.NonzeroIsSucc.At(b.TermAs[Nat]("i - k"))))
					dimension := b.Have(
						"x with its bottom k vertices removed has dimension m + 2",
						"n + 1 - k = m + 2",
						ByArith(mIs, short))
					lower := b.Have(
						"and with k + 1 removed, dimension m + 1",
						"n + 1 - suc(k) = m + 1",
						ByArith(mIs, short))
					index := b.Have(
						"and its face index is p",
						"i - suc(k) = p",
						ByArith(pIs, above))
					ranges := b.Have(
						"k is at most n + 1, and 0 < p + 1 ≤ m + 2",
						"k ≤ n + 1 ∧ 0 < p + 1 ∧ p + 1 ≤ m + 2",
						ByArith(mIs, pIs, above, upTo, short))
					k, zero, face := b.TermAs[Nat]("k"), b.TermAs[Nat]("0"), b.TermAs[Nat]("p + 1")
					y := b.TermAs[A]("face_iterate_bottom(n + 1, k, x)")
					yIn := b.Have(
						"x with its bottom k vertices removed is an (m + 2)-simplex",
						"face_iterate_bottom(n + 1, k, x) ∈ X.simplices(m + 2)",
						By(
							FaceIterateBottomIn.Read(simplicial).At(b.TermAs[Nat]("n + 1"), k, x),
							simplex,
							ranges,
							dimension))
					shifted := b.Have(
						"the hypothesis at n, i and x",
						"face_iterate_bottom(n, k, X.d(n + 1, i, x)) = "+
							"X.d(n + 1 - k, i - k, face_iterate_bottom(n + 1, k, x))",
						ByArith(ih.At(n, i, x), simplex, above, upTo, short))
					b.Show(
						"the 0-th face of the (m + 2)-simplex passes its face p + 1",
						Simp(Fwd(FaceIterateBottomDef)),
						CalcEq(
							Leg(
								b.TermAs[A]("X.d(m + 1, 0, X.d(m + 2, p + 1, face_iterate_bottom(n + 1, k, x)))"),
								"the hypothesis, the dimensions written m + 1 and m + 2 and the index p + 1",
								By(shifted, mIs, pIs, dimension)),
							Leg(
								b.TermAs[A]("X.d(m + 1, p, X.d(m + 2, 0, face_iterate_bottom(n + 1, k, x)))"),
								"the face identity, 0 lying below p + 1",
								ByArith(FaceFace.Read(simplicial).At(m, zero, face, y), yIn, ranges)),
							FinalLeg(
								"which is the right side, its dimensions written m + 1 and m + 2 and its index p",
								By(dimension, lower, index)),
						))
				})
		}),
})}

// FaceIterateBottomDegeneracy — removing bottom vertices below a
// repeated vertex commutes with that degeneracy, lowering its dimension
// and index by the number removed. Induction takes one more 0-th face,
// which passes the remaining positive degeneracy index.
var FaceIterateBottomDegeneracy = faceIterateBottomDegeneracyThm{family.Add(registry.ProofEntry{
	Name: "FaceIterateBottomDegeneracy",
	Key:  "prop_56afd23ba2e4ced5",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀n k i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n)",
			"k ≤ i",
			"i ≤ n",
		},
		Conclusion: "face_iterate_bottom(n + 1, k, X.s(n, i, x)) = " +
			"X.s(n - k, i - k, face_iterate_bottom(n, k, x))",
	},
		func(a *Argument, simplicial Fact) {
			a.Induct("k")
			a.Base(
				"with no vertex removed both sides are the i-th degeneracy of x",
				Simp(Fwd(FaceIterateBottomDef)),
				ByArith())
			a.Step(
				"one more 0-th face passes the remaining positive degeneracy index",
				func(b *Argument, ih Fact) {
					n, i := b.FixAs[Nat](), b.FixAs[Nat]()
					x := b.FixAs[A]()
					given := b.Conjuncts(
						b.Assume(),
						"x is an n-simplex",
						"suc(k) ≤ i",
						"and i ≤ n")
					simplex, above, upTo := given[0], given[1], given[2]
					m, mIs := b.ObtainAs[Nat](
						"n − k, which is positive, is the successor of some m",
						"∃m:num. n - k = m + 1",
						ByArith(above, upTo, nat_arith.NonzeroIsSucc.At(b.TermAs[Nat]("n - k"))))
					dimension := b.Have(
						"the degenerate simplex after k removals has dimension m + 2",
						"n + 1 - k = m + 2",
						ByArith(mIs, above, upTo))
					lower := b.Have(
						"x after k + 1 removals has dimension m",
						"n - suc(k) = m",
						ByArith(mIs, above, upTo))
					index := b.Have(
						"the next removal lowers the remaining degeneracy index by one",
						"i - k - 1 = i - suc(k)",
						ByArith(above))
					ranges := b.Have(
						"k can be removed, and the remaining degeneracy index is positive and in range",
						"k ≤ n ∧ 0 < i - k ∧ i - k ≤ m + 1",
						ByArith(mIs, above, upTo))
					k, zero, repeated := b.TermAs[Nat]("k"), b.TermAs[Nat]("0"), b.TermAs[Nat]("i - k")
					y := b.TermAs[A]("face_iterate_bottom(n, k, x)")
					yIn := b.Have(
						"x with its bottom k vertices removed is an (m + 1)-simplex",
						"face_iterate_bottom(n, k, x) ∈ X.simplices(m + 1)",
						By(Normalized, simplex, ranges, mIs, FaceIterateBottomIn.Read(simplicial).At(n, k, x)))
					commutes := b.Have(
						"the hypothesis at n, i and x",
						"face_iterate_bottom(n + 1, k, X.s(n, i, x)) = X.s(n - k, i - k, face_iterate_bottom(n, k, x))",
						ByArith(ih.At(n, i, x), simplex, above, upTo))
					b.Show(
						"the mixed face-degeneracy identity moves the next 0-th face past the degeneracy",
						Simp(Fwd(FaceIterateBottomDef)),
						CalcEq(
							Leg(
								b.TermAs[A]("X.d(m + 2, 0, X.s(m + 1, i - k, face_iterate_bottom(n, k, x)))"),
								"the hypothesis, with the dimensions written m + 1 and m + 2",
								By(commutes, mIs, dimension)),
							Leg(
								b.TermAs[A]("X.s(m, i - k - 1, X.d(m + 1, 0, face_iterate_bottom(n, k, x)))"),
								"the mixed identity, 0 lying below i − k",
								ByArith(yIn, ranges, FaceDegeneracyBelow.Read(simplicial).At(m, zero, repeated, y))),
							FinalLeg(
								"which is the right side, with its dimension and index lowered once more",
								By(Normalized, mIs, lower, index)),
						))
				})
		}),
})}

// FaceIterateTopDegeneracyAbove — a degeneracy of x at one of its top
// k + 1 vertices is absorbed when the top k + 1 vertices of the
// degenerate simplex are removed: what is left is x with its top k
// vertices removed. The repeated copy of the vertex sits at i + 1, among
// the vertices removed, so the removal absorbs the face there, and that
// face cancels the degeneracy, d_{i+1} s_i = id.
var FaceIterateTopDegeneracyAbove = faceIterateTopDegeneracyAboveThm{family.Add(registry.ProofEntry{
	Name: "FaceIterateTopDegeneracyAbove",
	Key:  "prop_e421343635ceb908",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀n k i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n)",
			"i ≤ n",
			"n ≤ i + k",
			"k ≤ n",
		},
		Conclusion: "face_iterate_top(n + 1, k + 1, X.s(n, i, x)) = face_iterate_top(n, k, x)",
	},
		func(a *Argument, simplicial Fact, n, k, i *Expr[Nat], x *Expr[A], given Fact) {
			parts := a.Conjuncts(
				given,
				"x is an n-simplex",
				"i ≤ n",
				"n ≤ i + k",
				"and k ≤ n")
			simplex, upTo := parts[0], parts[1]
			y := a.TermAs[A]("X.s(n, i, x)")
			yIn := a.Have(
				"the degeneracy of x at i is an (n + 1)-simplex",
				"X.s(n, i, x) ∈ X.simplices(n + 1)",
				By(DegeneracyIn.Read(simplicial).At(n, i, x), simplex, upTo))
			a.Show(
				"the face at the repeated copy is absorbed by the removal, and cancels the degeneracy",
				CalcEq(
					Leg(
						a.TermAs[A]("face_iterate_top(n, k, X.d(n + 1, i + 1, X.s(n, i, x)))"),
						"the face at i + 1, one of the top k + 1 vertices, is absorbed by the removal of the top k",
						ByArith(FaceIterateTopAbove.Read(simplicial).At(n, k, a.TermAs[Nat]("i + 1"), y), yIn, given)),
					FinalLeg(
						"d_{i+1} s_i returns x",
						By(Normalized, FaceDegeneracyNext.Read(simplicial).At(n, i, x), simplex, upTo)),
				))
		}),
})}

// FaceIterateTopAbove — a face of x at one of its top k + 1 vertices is
// absorbed by the removal of the top k: what is left is x with its top
// k + 1 vertices removed. By induction on k. At k = 0 the face is the
// last one. Past it, while the face stays among the vertices removed,
// the next last face is taken on both sides; at the step where the face
// is the one just below the top of what is left, i + k = n, it commutes
// with the removal of the top k, and on the (m + 2)-simplex left the
// face identity d_{m+1} d_{m+1} = d_{m+1} d_{m+2} trades it for the
// last face.
var FaceIterateTopAbove = faceIterateTopAboveThm{family.Add(registry.ProofEntry{
	Name: "FaceIterateTopAbove",
	Key:  "prop_1babbbb18ba48205",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀n k i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n + 1)",
			"n < i + k",
			"i ≤ n + 1",
			"k ≤ n",
		},
		Conclusion: "face_iterate_top(n, k, X.d(n + 1, i, x)) = face_iterate_top(n + 1, k + 1, x)",
	},
		func(a *Argument, simplicial Fact) {
			d := a.TermAs[Fun3[Nat, Nat, A, A]]("X.d")
			a.Induct("k")
			a.Base(
				"at k = 0 the face is the last one, which removes the top vertex",
				func(b *Argument) {
					b.FixAs[Nat]()
					b.FixAs[Nat]()
					x := b.FixAs[A]()
					given := b.Assume()
					last := b.Have(
						"n < i ≤ n + 1 makes i the last index",
						"i = n + 1",
						ByArith(given))
					top := b.Have(
						"removing the top vertex of x is its last face",
						"face_iterate_top(n + 1, 0 + 1, x) = X.d(n + 1 - 0, n + 1 - 0, face_iterate_top(n + 1, 0, x))",
						Cite(FaceIterateTopSucc, d, b.TermAs[Nat]("n + 1"), b.TermAs[Nat]("0"), x))
					b.Show(
						"both sides are the last face of x",
						top.Rw(),
						Simp(Fwd(FaceIterateTopDef)),
						ByArith(last))
				})
			a.Step(
				"removing one more top vertex is one more last face on both sides",
				func(b *Argument, ih Fact) {
					n, i := b.FixAs[Nat](), b.FixAs[Nat]()
					x := b.FixAs[A]()
					given := b.Conjuncts(
						b.Assume(),
						"x is an (n + 1)-simplex",
						"n < i + suc(k)",
						"i ≤ n + 1",
						"and suc(k) ≤ n")
					simplex, above, upTo, short := given[0], given[1], given[2], given[3]
					m, mIs := b.ObtainAs[Nat](
						"n − k, which is positive, is the successor of some m",
						"∃m:num. n - k = m + 1",
						ByArith(short, nat_arith.NonzeroIsSucc.At(b.TermAs[Nat]("n - k"))))
					dimension := b.Have(
						"x with its top k vertices removed has dimension m + 2",
						"n + 1 - k = m + 2",
						ByArith(mIs, short))
					lower := b.Have(
						"and with k + 1 removed, dimension m + 1",
						"n + 1 - suc(k) = m + 1",
						ByArith(mIs, short))
					topNext := b.Have(
						"removing the top k + 2 vertices of x is the last face after removing the top k + 1",
						"face_iterate_top(n + 1, suc(k) + 1, x) = "+
							"X.d(n + 1 - suc(k), n + 1 - suc(k), face_iterate_top(n + 1, suc(k), x))",
						Cite(FaceIterateTopSucc, d, b.TermAs[Nat]("n + 1"), b.TermAs[Nat]("suc(k)"), x))
					b.Cases(b.Term("n < i + k"))
					b.When(
						"while the face stays among the top k + 1 vertices, the hypothesis takes it",
						func(c *Argument, still Fact) {
							absorbed := c.Have(
								"the hypothesis at n, i and x",
								"face_iterate_top(n, k, X.d(n + 1, i, x)) = face_iterate_top(n + 1, k + 1, x)",
								ByArith(ih.At(n, i, x), simplex, still, upTo, short))
							topStep := c.Have(
								"removing the top k + 1 vertices of x is the last face after removing the top k",
								"face_iterate_top(n + 1, k + 1, x) = X.d(n + 1 - k, n + 1 - k, face_iterate_top(n + 1, k, x))",
								Cite(FaceIterateTopSucc, d, c.TermAs[Nat]("n + 1"), c.TermAs[Nat]("k"), x))
							c.Show(
								"both sides are x with its top k + 1 vertices removed, and one more last face",
								topNext.Rw(),
								Simp(Fwd(FaceIterateTopDef)),
								By(absorbed, topStep, mIs, lower))
						})
					b.Otherwise(
						"at i + k = n the face is the one just below the top of the (m + 2)-simplex left",
						func(c *Argument, notStill Fact) {
							k, belowTop, top := c.TermAs[Nat]("k"), c.TermAs[Nat]("m + 1"), c.TermAs[Nat]("m + 2")
							y := c.TermAs[A]("face_iterate_top(n + 1, k, x)")
							at := c.Have(
								"i is m + 1",
								"i = m + 1",
								ByArith(notStill, above, mIs))
							ranges := c.Have(
								"k is at most n + 1, and m + 1 < m + 2",
								"k ≤ n + 1 ∧ m + 1 < m + 2",
								ByArith(short))
							yIn := c.Have(
								"x with its top k vertices removed is an (m + 2)-simplex",
								"face_iterate_top(n + 1, k, x) ∈ X.simplices(m + 2)",
								By(FaceIterateTopIn.Read(simplicial).At(c.TermAs[Nat]("n + 1"), k, x), simplex, ranges, dimension))
							commuted := c.Have(
								"the face at i, below the top k + 1 vertices of x, commutes with the removal of the top k",
								"face_iterate_top(n, k, X.d(n + 1, i, x)) = X.d(n + 1 - k, i, face_iterate_top(n + 1, k, x))",
								ByArith(FaceIterateTopFace.Read(simplicial).At(n, k, i, x), simplex, notStill, above))
							c.Show(
								"the last face taken twice, by the face identity",
								topNext.Rw(),
								Simp(Fwd(FaceIterateTopDef)),
								CalcEq(
									Leg(
										c.TermAs[A]("X.d(m + 1, m + 1, X.d(m + 2, m + 1, face_iterate_top(n + 1, k, x)))"),
										"the face at i = m + 1 passes the removal",
										By(commuted, at, mIs, dimension)),
									Leg(
										c.TermAs[A]("X.d(m + 1, m + 1, X.d(m + 2, m + 2, face_iterate_top(n + 1, k, x)))"),
										"the face identity, m + 1 lying below m + 2",
										ByArith(FaceFace.Read(simplicial).At(m, belowTop, top, y), yIn, ranges)),
									FinalLeg(
										"which is x with its top k + 2 vertices removed",
										By(dimension, lower)),
								))
						})
				})
		}),
})}

// FaceIterateBottomBelow — a face of x at one of its bottom k + 1
// vertices is absorbed by the removal of the bottom k: what is left is
// x with its bottom k + 1 vertices removed. By induction on k. At k = 0
// the face is the 0-th. Past it, while the face stays among the
// vertices removed, the next 0-th face is taken on both sides; at the
// step where it becomes the face 1 of what is left, i = k + 1, it
// commutes with the removal of the bottom k and the face identity
// d_{0} d_{1} = d_{0} d_{0} trades it for the 0-th face.
var FaceIterateBottomBelow = faceIterateBottomBelowThm{family.Add(registry.ProofEntry{
	Name: "FaceIterateBottomBelow",
	Key:  "prop_5f687bd1ae2c1e69",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀n k i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n + 1)",
			"i ≤ k",
			"k ≤ n",
		},
		Conclusion: "face_iterate_bottom(n, k, X.d(n + 1, i, x)) = face_iterate_bottom(n + 1, k + 1, x)",
	},
		func(a *Argument, simplicial Fact) {
			d := a.TermAs[Fun3[Nat, Nat, A, A]]("X.d")
			a.Induct("k")
			a.Base(
				"at k = 0 the face is the 0-th, which removes the bottom vertex",
				func(b *Argument) {
					b.FixAs[Nat]()
					b.FixAs[Nat]()
					x := b.FixAs[A]()
					given := b.Assume()
					first := b.Have(
						"i ≤ 0 makes i the 0-th index",
						"i = 0",
						ByArith(given))
					bottom := b.Have(
						"removing the bottom vertex of x is its 0-th face",
						"face_iterate_bottom(n + 1, 0 + 1, x) = X.d(n + 1 - 0, 0, face_iterate_bottom(n + 1, 0, x))",
						Cite(FaceIterateBottomSucc, d, b.TermAs[Nat]("n + 1"), b.TermAs[Nat]("0"), x))
					b.Show(
						"both sides are the 0-th face of x",
						bottom.Rw(),
						Simp(Fwd(FaceIterateBottomDef)),
						ByArith(first))
				})
			a.Step(
				"removing one more bottom vertex is one more 0-th face on both sides",
				func(b *Argument, ih Fact) {
					n, i := b.FixAs[Nat](), b.FixAs[Nat]()
					x := b.FixAs[A]()
					given := b.Conjuncts(
						b.Assume(),
						"x is an (n + 1)-simplex",
						"i ≤ suc(k)",
						"and suc(k) ≤ n")
					simplex, below, short := given[0], given[1], given[2]
					m, mIs := b.ObtainAs[Nat](
						"n − k, which is positive, is the successor of some m",
						"∃m:num. n - k = m + 1",
						ByArith(short, nat_arith.NonzeroIsSucc.At(b.TermAs[Nat]("n - k"))))
					dimension := b.Have(
						"x with its bottom k vertices removed has dimension m + 2",
						"n + 1 - k = m + 2",
						ByArith(mIs, short))
					lower := b.Have(
						"and with k + 1 removed, dimension m + 1",
						"n + 1 - suc(k) = m + 1",
						ByArith(mIs, short))
					bottomNext := b.Have(
						"removing the bottom k + 2 vertices of x is the 0-th face after removing the bottom k + 1",
						"face_iterate_bottom(n + 1, suc(k) + 1, x) = "+
							"X.d(n + 1 - suc(k), 0, face_iterate_bottom(n + 1, suc(k), x))",
						Cite(FaceIterateBottomSucc, d, b.TermAs[Nat]("n + 1"), b.TermAs[Nat]("suc(k)"), x))
					b.Cases(b.Term("i ≤ k"))
					b.When(
						"while the face stays among the bottom k + 1 vertices, the hypothesis takes it",
						func(c *Argument, still Fact) {
							absorbed := c.Have(
								"the hypothesis at n, i and x",
								"face_iterate_bottom(n, k, X.d(n + 1, i, x)) = face_iterate_bottom(n + 1, k + 1, x)",
								ByArith(ih.At(n, i, x), simplex, still, short))
							bottomStep := c.Have(
								"removing the bottom k + 1 vertices of x is the 0-th face after removing the bottom k",
								"face_iterate_bottom(n + 1, k + 1, x) = X.d(n + 1 - k, 0, face_iterate_bottom(n + 1, k, x))",
								Cite(FaceIterateBottomSucc, d, c.TermAs[Nat]("n + 1"), c.TermAs[Nat]("k"), x))
							c.Show(
								"both sides are x with its bottom k + 1 vertices removed, and one more 0-th face",
								bottomNext.Rw(),
								Simp(Fwd(FaceIterateBottomDef)),
								By(absorbed, bottomStep, mIs, lower))
						})
					b.Otherwise(
						"at i = k + 1 the face is the face 1 of the (m + 2)-simplex left",
						func(c *Argument, notStill Fact) {
							k, zero, one := c.TermAs[Nat]("k"), c.TermAs[Nat]("0"), c.TermAs[Nat]("1")
							y := c.TermAs[A]("face_iterate_bottom(n + 1, k, x)")
							index := c.Have(
								"i − k is 1",
								"i - k = 1",
								ByArith(notStill, below))
							ranges := c.Have(
								"k is at most n + 1, and 0 < 1 ≤ m + 2",
								"k ≤ n + 1 ∧ 0 < 1 ∧ 1 ≤ m + 2",
								ByArith(short))
							yIn := c.Have(
								"x with its bottom k vertices removed is an (m + 2)-simplex",
								"face_iterate_bottom(n + 1, k, x) ∈ X.simplices(m + 2)",
								By(
									FaceIterateBottomIn.Read(simplicial).At(c.TermAs[Nat]("n + 1"), k, x),
									simplex,
									ranges,
									dimension))
							shifted := c.Have(
								"the face at i commutes with the removal of the bottom k, its index lowered by k",
								"face_iterate_bottom(n, k, X.d(n + 1, i, x)) = "+
									"X.d(n + 1 - k, i - k, face_iterate_bottom(n + 1, k, x))",
								ByArith(FaceIterateBottomFace.Read(simplicial).At(n, k, i, x), simplex, notStill, below, short))
							c.Show(
								"the 0-th face taken twice, by the face identity",
								bottomNext.Rw(),
								Simp(Fwd(FaceIterateBottomDef)),
								CalcEq(
									Leg(
										c.TermAs[A]("X.d(m + 1, 0, X.d(m + 2, 1, face_iterate_bottom(n + 1, k, x)))"),
										"the face at i passes the removal, now the face 1",
										By(shifted, index, mIs, dimension)),
									Leg(
										c.TermAs[A]("X.d(m + 1, 0, X.d(m + 2, 0, face_iterate_bottom(n + 1, k, x)))"),
										"the face identity, 0 lying below 1",
										By(FaceFace.Read(simplicial).At(m, zero, one, y), yIn, ranges)),
									FinalLeg(
										"which is x with its bottom k + 2 vertices removed",
										By(dimension, lower)),
								))
						})
				})
		}),
})}
