// opposite.go — the opposite of a simplicial set, the same simplices
// with the order of the vertices reversed: the i-th face of an
// n-simplex is its (n − i)-th face in X, and likewise the degeneracies.
// The simplicial identities hold of the reversed maps, so the opposite
// is a simplicial set, and reversal exchanges the two iterated faces:
// removing the bottom k vertices in the opposite removes the top k in
// X, and removing the top k removes the bottom k. Beside it, the set of
// simplicial maps from X to Y, normalized with junk off each X(n), so
// that two maps agreeing on the simplices are one element.

package simplicial_set

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/registry"
)

// OppositeFaceDef — `opposite_face(d)`: the i-th face of an n-simplex
// read as its (n − i)-th.
var OppositeFaceDef = oppositeFaceDefThm{family.Define(registry.DefEntry{
	Name:  "OppositeFaceDef",
	Key:   "prop_b6e378ad40ffaae6",
	Const: "opposite_face",
	Type:  "(num → num → A → A) → num → num → A → A",
	Equations: []string{
		"∀d:(num → num → A → A). opposite_face(d) = λn:num. λi:num. λx:A. d(n, n - i, x)",
	},
})}

// OppositeDegeneracyDef — `opposite_degeneracy(s)`: the i-th degeneracy
// of an n-simplex read as its (n − i)-th.
var OppositeDegeneracyDef = oppositeDegeneracyDefThm{family.Define(registry.DefEntry{
	Name:  "OppositeDegeneracyDef",
	Key:   "prop_b362e8b9d8a75b9d",
	Const: "opposite_degeneracy",
	Type:  "(num → num → A → A) → num → num → A → A",
	Equations: []string{
		"∀s:(num → num → A → A). opposite_degeneracy(s) = λn:num. λi:num. λx:A. s(n, n - i, x)",
	},
})}

// OppositeSimplicialSet — a simplicial set read in the opposite order
// is a simplicial set: each axiom of the opposite is an axiom of X read
// at the reversed indices, with FaceDegeneracyBelow and
// FaceDegeneracyAbove exchanged, and FaceDegeneracyEqual and
// FaceDegeneracyNext exchanged.
var OppositeSimplicialSet = oppositeSimplicialSetThm{family.Add(registry.ProofEntry{
	Name: "OppositeSimplicialSet",
	Key:  "prop_6b006a71e414400d",
	Build: SimplicialSet.Law("simplicial_set(opposite_simplicial_set(X))",
		func(a *Argument, simplicial Fact) {
			a.Do(Simp(Fwd(SimplicialSet)), SplitConjAll(
				Case(
					"reversing a face index preserves face closure",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.FixAs[Nat]("i")
						x := b.FixAs[A]("x")
						datum := b.Assume()
						b.Do(Simp(Fwd(OppositeFaceDef)))
						bound := b.Have(
							"the reversed face index is in range",
							"n + 1 - i ≤ n + 1",
							ByArith())
						b.Show(
							"the ambient face remains in the preceding degree",
							By(datum, bound, FaceIn.Read(simplicial).At(n, b.TermAs[Nat]("n + 1 - i"), x)))
					})),
				Case(
					"reversing a degeneracy index preserves degeneracy closure",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.FixAs[Nat]("i")
						x := b.FixAs[A]("x")
						datum := b.Assume()
						b.Do(Simp(Fwd(OppositeDegeneracyDef)))
						bound := b.Have(
							"the reversed degeneracy index is in range",
							"n - i ≤ n",
							ByArith())
						b.Show(
							"the ambient degeneracy remains in the following degree",
							By(datum, bound, DegeneracyIn.Read(simplicial).At(n, b.TermAs[Nat]("n - i"), x)))
					})),
				Case(
					"reversed faces satisfy the ambient face identity in the opposite orientation",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.FixAs[Nat]("i")
						b.FixAs[Nat]("j")
						x := b.FixAs[A]("x")
						datum := b.Assume()
						b.Do(Simp(Fwd(OppositeFaceDef)))
						bounds := b.Have(
							"reversal exchanges the order of the face indices",
							"n + 2 - j < n + 2 - i ∧ n + 2 - i ≤ n + 2",
							ByArith(datum))
						indices := b.Have(
							"reversing the shifted indices gives the ambient indices",
							"n + 1 - i = n + 2 - i - 1 ∧ n + 1 - (j - 1) = n + 2 - j",
							ByArith(datum))
						b.Show(
							"the face identity applies at the reversed pair",
							Simp(Fwd(indices)),
							By(
								datum,
								bounds,
								FaceFace.Read(simplicial).At(n, b.TermAs[Nat]("n + 2 - j"), b.TermAs[Nat]("n + 2 - i"), x)))
					})),
				Case(
					"reversed degeneracies satisfy the ambient identity in the opposite orientation",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.FixAs[Nat]("i")
						b.FixAs[Nat]("j")
						x := b.FixAs[A]("x")
						datum := b.Assume()
						b.Do(Simp(Fwd(OppositeDegeneracyDef)))
						bounds := b.Have(
							"reversal exchanges the order of the degeneracy indices",
							"n - j ≤ n - i ∧ n - i ≤ n",
							ByArith(datum))
						indices := b.Have(
							"the shifted reversed indices agree",
							"n + 1 - i = n - i + 1 ∧ n + 1 - (j + 1) = n - j",
							ByArith(datum))
						b.Show(
							"the degeneracy identity applies at the reversed pair",
							Simp(Fwd(indices)),
							By(
								datum,
								bounds,
								DegeneracyDegeneracy.Read(simplicial).At(n, b.TermAs[Nat]("n - j"), b.TermAs[Nat]("n - i"), x)))
					})),
				Case(
					"a face below the degeneracy becomes a face above it after reversal",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.FixAs[Nat]("i")
						b.FixAs[Nat]("j")
						x := b.FixAs[A]("x")
						datum := b.Assume()
						b.Do(Simp(Fwd(OppositeFaceDef), Fwd(OppositeDegeneracyDef)))
						bounds := b.Have(
							"the reversed face lies above the reversed degeneracy",
							"n + 1 - j + 1 < n + 2 - i ∧ n + 2 - i ≤ n + 2",
							ByArith(datum))
						indices := b.Have(
							"the reversed shifts match the upper mixed identity",
							"n - (j - 1) = n + 1 - j ∧ n + 1 - i = n + 2 - i - 1",
							ByArith(datum))
						b.Show(
							"the upper mixed identity gives the lower identity of the opposite",
							Simp(Fwd(indices)),
							By(
								datum,
								bounds,
								FaceDegeneracyAbove.Read(simplicial).At(
									n, b.TermAs[Nat]("n + 2 - i"), b.TermAs[Nat]("n + 1 - j"), x)))
					})),
				Case(
					"the face at the degeneracy index becomes the following face after reversal",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.FixAs[Nat]("i")
						x := b.FixAs[A]("x")
						datum := b.Assume()
						b.Do(Simp(Fwd(OppositeFaceDef), Fwd(OppositeDegeneracyDef)))
						bound := b.Have(
							"the reversed degeneracy index is in range",
							"n - i ≤ n",
							ByArith(datum))
						index := b.Have(
							"the reversed face is one past the reversed degeneracy",
							"n + 1 - i = n - i + 1",
							ByArith(datum))
						b.Show(
							"the following face cancels the ambient degeneracy",
							Simp(Fwd(index)),
							By(datum, bound, FaceDegeneracyNext.Read(simplicial).At(n, b.TermAs[Nat]("n - i"), x)))
					})),
				Case(
					"the following face becomes the face at the degeneracy index after reversal",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.FixAs[Nat]("i")
						x := b.FixAs[A]("x")
						datum := b.Assume()
						b.Do(Simp(Fwd(OppositeFaceDef), Fwd(OppositeDegeneracyDef)))
						bound := b.Have(
							"the reversed degeneracy index is in range",
							"n - i ≤ n",
							ByArith(datum))
						index := b.Have(
							"the reversed face and degeneracy have the same index",
							"n + 1 - (i + 1) = n - i",
							ByArith(datum))
						b.Show(
							"the face at the index cancels the ambient degeneracy",
							Simp(Fwd(index)),
							By(datum, bound, FaceDegeneracyEqual.Read(simplicial).At(n, b.TermAs[Nat]("n - i"), x)))
					})),
				Case(
					"a face above the degeneracy becomes a face below it after reversal",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.FixAs[Nat]("i")
						b.FixAs[Nat]("j")
						x := b.FixAs[A]("x")
						datum := b.Assume()
						b.Do(Simp(Fwd(OppositeFaceDef), Fwd(OppositeDegeneracyDef)))
						bounds := b.Have(
							"the reversed face lies below the reversed degeneracy",
							"n + 2 - i < n + 1 - j ∧ n + 1 - j ≤ n + 1",
							ByArith(datum))
						indices := b.Have(
							"the reversed shifts match the lower mixed identity",
							"n - j = n + 1 - j - 1 ∧ n + 1 - (i - 1) = n + 2 - i",
							ByArith(datum))
						b.Show(
							"the lower mixed identity gives the upper identity of the opposite",
							Simp(Fwd(indices)),
							By(
								datum,
								bounds,
								FaceDegeneracyBelow.Read(simplicial).At(
									n, b.TermAs[Nat]("n + 2 - i"), b.TermAs[Nat]("n + 1 - j"), x)))
					})),
			))
		}),
})}

// FaceIterateBottomOpposite — removing the bottom k vertices of x in the
// opposite removes its top k in X: by induction on k, the opposite's
// 0-th face of an (m − k)-simplex being its last face in X.
var FaceIterateBottomOpposite = faceIterateBottomOppositeThm{family.Add(registry.ProofEntry{
	Name: "FaceIterateBottomOpposite",
	Key:  "prop_ee9849ef5e9151dc",
	Build: family.Theorem("∀d:(num → num → A → A). ∀m k:num. ∀x:A. "+
		"    face_iterate_bottom(opposite_face(d), m, k, x) = face_iterate_top(d, m, k, x)",
		func(a *Argument, d *Expr[Fun3[Nat, Nat, A, A]], m, k *Expr[Nat], x *Expr[A]) {
			a.Induct(k)
			a.Base(
				"with no vertex removed both sides are x",
				Simp(Fwd(FaceIterateBottomDef), Fwd(FaceIterateTopDef)),
				Basic())
			a.Step(
				"one more 0-th face in the opposite is one more last face in X",
				func(b *Argument, ih Fact) {
					b.Show(
						"the hypothesis makes the two iterates one simplex, "+
							"whose face 0 in the opposite is d(m − k, m − k, ·)",
						Simp(Fwd(FaceIterateBottomDef), Fwd(FaceIterateTopDef)),
						Simp(Fwd(ih)),
						Simp(Fwd(OppositeFaceDef), Fwd(nat_monus.Sub)),
						Basic())
				})
		}),
})}

// FaceIterateTopOpposite — removing the top k vertices of x in the
// opposite removes its bottom k in X: by induction on k, the opposite's
// last face of an (m − k)-simplex being its 0-th face in X.
var FaceIterateTopOpposite = faceIterateTopOppositeThm{family.Add(registry.ProofEntry{
	Name: "FaceIterateTopOpposite",
	Key:  "prop_2e8dde1dc29cda94",
	Build: family.Theorem("∀d:(num → num → A → A). ∀m k:num. ∀x:A. "+
		"    face_iterate_top(opposite_face(d), m, k, x) = face_iterate_bottom(d, m, k, x)",
		func(a *Argument, d *Expr[Fun3[Nat, Nat, A, A]], m, k *Expr[Nat], x *Expr[A]) {
			a.Induct(k)
			a.Base(
				"with no vertex removed both sides are x",
				Simp(Fwd(FaceIterateTopDef), Fwd(FaceIterateBottomDef)),
				Basic())
			a.Step(
				"one more last face in the opposite is one more 0-th face in X",
				func(b *Argument, ih Fact) {
					b.Show(
						"the hypothesis makes the two iterates one simplex, "+
							"whose face m − k in the opposite is d(m − k, 0, ·)",
						Simp(Fwd(FaceIterateTopDef), Fwd(FaceIterateBottomDef)),
						Simp(Fwd(ih)),
						Simp(Fwd(OppositeFaceDef), Fwd(nat_monus.SubRefl)),
						Basic())
				})
		}),
})}

// SimplicialMapSetDef — `simplicial_map_set(X, Y)`: the
// simplicial maps from X to Y, normalized with junk off each X(n).
var SimplicialMapSetDef = simplicialMapSetDefThm{family.Define(registry.DefEntry{
	Name:  "SimplicialMapSetDef",
	Key:   "prop_cd1f913bbc72432a",
	Const: "simplicial_map_set",
	Type:  "simplicial_ops(A) → simplicial_ops(B) → set(num → A → B)",
	Equations: []string{
		"∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). " +
			"    simplicial_map_set(X, Y) = " +
			"    {F:(num → A → B) | " +
			"        simplicial_map(X, Y, F) ∧ (∀n:num. F(n) = normalize_on(X.simplices(n), junk, F(n)))}",
	},
	Deps: []registry.EntryLike{SimplicialMap},
})}
