// kan_complex.go — the Kan condition in its combinatorial form: the
// faces of the horn Λⁿ⁺¹ₖ are horn_faces(n, k), the indices i ≤ n + 1
// of the faces of an (n+1)-simplex other than k; a horn of X is a face
// family of X on them, n-simplices pairwise compatible under the face
// identity, and a filler is an (n+1)-simplex with those faces there. A
// Kan complex is a simplicial set in which every horn has a filler. The
// faces of a simplex are a compatible family on the faces of every horn
// with k ≤ n + 1, with the simplex as a filler; the point is a Kan
// complex, and no standard simplex of positive dimension is one.
//
// The horn's index k ranges over 0 .. n + 1 and the compatibility
// quantifies over the pairs i < j of its faces; at n = 0 the two
// indices are 0 and 1, one of them k, so a one-dimensional horn is one
// vertex and is filled by an edge with the vertex as its face other
// than k.

package kan_complex

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// HornFacesDef — `horn_faces(n, k)`: the faces of the horn Λⁿ⁺¹ₖ, the
// indices i ≤ n + 1 of the faces of an (n+1)-simplex other than k. A
// horn of X is a face family on them, `face_family(n, horn_faces(n, k), y)`,
// and its filler fills that family, `faces_filler(n, horn_faces(n, k), y, x)`.
var HornFacesDef = hornFacesDefThm{family.Define(registry.DefEntry{
	Name:      "HornFacesDef",
	Key:       "prop_2d2a4537a6a201ae",
	Const:     "horn_faces",
	Type:      "num → num → set(num)",
	Equations: []string{"∀n k:num. horn_faces(n, k) = {i:num | i ≤ n + 1 ∧ ¬(i = k)}"},
})}

// HornFacesMember — a face of an (n+1)-simplex is a face of the horn
// Λⁿ⁺¹ₖ exactly when it is not the k-th.
var HornFacesMember = hornFacesMemberThm{family.Add(registry.ProofEntry{
	Name: "HornFacesMember",
	Key:  "prop_be128fd0ce7143f6",
	Build: family.Theorem("∀n k i:num. i ∈ horn_faces(n, k) ⇔ i ≤ n + 1 ∧ ¬(i = k)",
		func(a *Argument, n, k, i *Expr[Nat]) {
			a.Do(Unfold(HornFacesDef))
			a.Show(
				"membership in a comprehension is its condition",
				BySets())
		}),
})}

// KanComplex — `kan_complex(X)`: a simplicial set in which every
// compatible family of n-simplices indexed by the faces other than k,
// for every k ≤ n + 1, is the family of faces of some (n+1)-simplex.
var KanComplex = kanComplexThm{family.DefineStructure(registry.DefEntry{
	Name:    "KanComplex",
	Key:     "prop_db1a6708b31fb307",
	Const:   "kan_complex",
	Type:    "simplicial_ops(A) → bool",
	Subject: "X",
	Equations: []string{
		"∀X:simplicial_ops(A). " +
			"    kan_complex(X) ⇔ " +
			"    simplicial_set(X) ∧ " +
			"    (∀n k:num. ∀y:(num → A). " +
			"        k ≤ n + 1 ∧ face_family(X, n, horn_faces(n, k), y) ⇒ " +
			"        ∃x:A. x ∈ X.simplices(n + 1) ∧ faces_filler(X.d, n, horn_faces(n, k), y, x))",
	},
	Reading: "The horns are those of dimension n + 1 ≥ 1 with k ≤ n + 1, every horn there " +
		"is; a one-dimensional horn is a vertex and its filler an edge with that vertex as its " +
		"face other than k, which the degeneracy of the vertex supplies in any simplicial set.",
	Deps: []registry.EntryLike{HornFacesDef},
})}

// KanSimplicialSet — a Kan complex is a simplicial set.
var KanSimplicialSet = kanSimplicialSetThm{family.Add(registry.ProofEntry{
	Name:  "KanSimplicialSet",
	Key:   "prop_fd1d2b31ed941ca1",
	Build: KanComplex.Axiom("simplicial_set(X)"),
})}

// KanFill — every horn has a filler.
var KanFill = kanFillThm{family.Add(registry.ProofEntry{
	Name: "KanFill",
	Key:  "prop_7a97b0de8ced5b75",
	Build: KanComplex.Axiom(Statement{
		Binders: "∀n k:num. ∀y:(num → A).",
		Hypotheses: []string{
			"k ≤ n + 1",
			"face_family(X, n, horn_faces(n, k), y)",
		},
		Conclusion: "∃x:A. x ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, k), y, x)",
	}),
})}

// CommonSourceTriangle — two edges out of one vertex are the faces 1 and
// 2 of a triangle, the horn Λ²₀ filling: the family y with h at 2 and g
// elsewhere is a face family on the faces 1 and 2 of the horn missing
// the face 0, its one pair of faces (1, 2) meeting at the common source,
// and KanFill fills it.
var CommonSourceTriangle = commonSourceTriangleThm{family.Add(registry.ProofEntry{
	Name: "CommonSourceTriangle",
	Key:  "prop_d91a48f3a21ebdc6",
	Build: KanComplex.Law(Statement{
		Binders: "∀g h:A.",
		Hypotheses: []string{
			"g ∈ X.simplices(1)",
			"h ∈ X.simplices(1)",
			"X.d(1, 1, g) = X.d(1, 1, h)",
		},
		Conclusion: "∃w:A. w ∈ X.simplices(2) ∧ X.d(2, 1, w) = g ∧ X.d(2, 2, w) = h",
	},
		func(a *Argument, kan Fact, _, _ *Expr[A], commonSource Fact) {
			zero, one, two := a.TermAs[Nat]("0"), a.TermAs[Nat]("1"), a.TermAs[Nat]("2")
			// The horn: h at 2, g everywhere else, its value at 0 never read.
			y, yDef := a.LetAs[Fun[Nat, A]]("y", "λi:num. COND(i = 2, h, g)")
			values := a.Have(
				"the family read at 1 and at 2",
				"y(1) = g ∧ y(2) = h",
				yDef.Rw(),
				ByArith())
			edges := a.Have(
				"each member of y is g or h, an edge",
				"∀i:num. y(i) ∈ X.simplices(1)",
				By(yDef, commonSource))
			compatible := a.Have(
				"and compatible on the faces of the horn missing 0: its one pair of faces is (1, 2)",
				"faces_compatible(1, horn_faces(1, 0), y)",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(simplicial_set.FacesCompatibleDef)))
					i, j := b.FixAs[Nat](), b.FixAs[Nat]()
					pair := b.Assume()
					ends := b.Have(
						"the faces i < j of the horn, at most 2 and neither 0, are the pair (1, 2)",
						"i = 1 ∧ j = 2",
						ByArith(pair, HornFacesMember.At(one, zero, i), HornFacesMember.At(one, zero, j)))
					b.Show(
						"where the condition is d(1, 1, y(2)) = d(1, 1, y(1)): h and g have one source",
						ByArith(values, ends, commonSource))
				}))
			horn := a.Have(
				"so y is a horn of X, edges at the faces of the horn compatible there",
				"face_family(1, horn_faces(1, 0), y)",
				Simp(Fwd(simplicial_set.FaceFamilyDef)),
				By(edges, compatible))
			w, filler := a.ObtainAs[A](
				"so the horn y has a filler, a 2-simplex",
				"∃w:A. w ∈ X.simplices(2) ∧ faces_filler(1, horn_faces(1, 0), y, w)",
				By(KanFill.Read(kan).At(one, zero, y), horn))
			parts := a.Conjuncts(
				filler,
				"w is a 2-simplex",
				"whose faces at the faces of the horn are the members of y")
			simplex, faceOf := parts[0], a.Unfolded(parts[1], simplicial_set.FacesFillerDef)
			known := a.Have(
				"1 and 2 are faces of the horn, at most 2 and not 0",
				"1 ∈ horn_faces(1, 0) ∧ 2 ∈ horn_faces(1, 0)",
				By(HornFacesMember.At(one, zero, one), HornFacesMember.At(one, zero, two)))
			faceOne := a.Have(
				"its face 1 is y(1) = g",
				"X.d(2, 1, w) = g",
				ByArith(faceOf.At(one), known, values))
			faceTwo := a.Have(
				"and its face 2 is y(2) = h",
				"X.d(2, 2, w) = h",
				ByArith(faceOf.At(two), known, values))
			a.Take(w)
			a.Show(
				"so w is a triangle with g and h as its faces 1 and 2",
				By(simplex, faceOne, faceTwo))
		}),
})}

// CommonTargetTriangle — two edges into one vertex are the faces 0 and 1
// of a triangle, the horn Λ²₂ filling: the family y with f at 0 and g
// elsewhere is a face family on the faces 0 and 1 of the horn missing
// the face 2, its one pair of faces (0, 1) meeting at the common target,
// and KanFill fills it.
var CommonTargetTriangle = commonTargetTriangleThm{family.Add(registry.ProofEntry{
	Name: "CommonTargetTriangle",
	Key:  "prop_a38056db15e9b2b",
	Build: KanComplex.Law(Statement{
		Binders: "∀f g:A.",
		Hypotheses: []string{
			"f ∈ X.simplices(1)",
			"g ∈ X.simplices(1)",
			"X.d(1, 0, f) = X.d(1, 0, g)",
		},
		Conclusion: "∃w:A. w ∈ X.simplices(2) ∧ X.d(2, 0, w) = f ∧ X.d(2, 1, w) = g",
	},
		func(a *Argument, kan Fact, _, _ *Expr[A], commonTarget Fact) {
			zero, one, two := a.TermAs[Nat]("0"), a.TermAs[Nat]("1"), a.TermAs[Nat]("2")
			// The horn: f at 0, g everywhere else, its value at 2 never read.
			y, yDef := a.LetAs[Fun[Nat, A]]("y", "λi:num. COND(i = 0, f, g)")
			values := a.Have(
				"the family read at 0 and at 1",
				"y(0) = f ∧ y(1) = g",
				yDef.Rw(),
				ByArith())
			edges := a.Have(
				"each member of y is f or g, an edge",
				"∀i:num. y(i) ∈ X.simplices(1)",
				By(yDef, commonTarget))
			compatible := a.Have(
				"and compatible on the faces of the horn missing 2: its one pair of faces is (0, 1)",
				"faces_compatible(1, horn_faces(1, 2), y)",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(simplicial_set.FacesCompatibleDef)))
					i, j := b.FixAs[Nat](), b.FixAs[Nat]()
					pair := b.Assume()
					ends := b.Have(
						"the faces i < j of the horn are below 2, so they are the pair (0, 1)",
						"i = 0 ∧ j = 1",
						ByArith(pair, HornFacesMember.At(one, two, i), HornFacesMember.At(one, two, j)))
					b.Show(
						"where the condition is d(1, 0, y(1)) = d(1, 0, y(0)): g and f have one target",
						ByArith(values, ends, commonTarget))
				}))
			horn := a.Have(
				"so y is a horn of X, edges at the faces of the horn compatible there",
				"face_family(1, horn_faces(1, 2), y)",
				Simp(Fwd(simplicial_set.FaceFamilyDef)),
				By(edges, compatible))
			w, filler := a.ObtainAs[A](
				"so the horn y has a filler, a 2-simplex",
				"∃w:A. w ∈ X.simplices(2) ∧ faces_filler(1, horn_faces(1, 2), y, w)",
				By(KanFill.Read(kan).At(one, two, y), horn))
			parts := a.Conjuncts(
				filler,
				"w is a 2-simplex",
				"whose faces at the faces of the horn are the members of y")
			simplex, faceOf := parts[0], a.Unfolded(parts[1], simplicial_set.FacesFillerDef)
			known := a.Have(
				"0 and 1, both below 2, are faces of the horn",
				"0 ∈ horn_faces(1, 2) ∧ 1 ∈ horn_faces(1, 2)",
				By(HornFacesMember.At(one, two, zero), HornFacesMember.At(one, two, one)))
			faceZero := a.Have(
				"its face 0 is y(0) = f",
				"X.d(2, 0, w) = f",
				ByArith(faceOf.At(zero), known, values))
			faceOne := a.Have(
				"and its face 1 is y(1) = g",
				"X.d(2, 1, w) = g",
				ByArith(faceOf.At(one), known, values))
			a.Take(w)
			a.Show(
				"so w is a triangle with f and g as its faces 0 and 1",
				By(simplex, faceZero, faceOne))
		}),
})}

// FacesCompatible — the faces of an (n+1)-simplex are a compatible
// family on the faces of every horn Λⁿ⁺¹ₖ: a pair i < j of those faces
// is a pair of indices at most n + 1, neither k, where the condition is
// the face identity d_i d_j = d_{j−1} d_i on x, which the axiom states
// for x read as a simplex of dimension (n − 1) + 2 once n is positive;
// at n = 0 the only pair is (0, 1), and k ≤ 1 is one of its two indices.
var FacesCompatible = facesCompatibleThm{family.Add(registry.ProofEntry{
	Name: "FacesCompatible",
	Key:  "prop_b5491d1cdd919d0a",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀n k:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n + 1)",
			"k ≤ n + 1",
		},
		Conclusion: "faces_compatible(n, horn_faces(n, k), λi:num. X.d(n + 1, i, x))",
	},
		func(a *Argument, simplicial Fact, n, k *Expr[Nat], x *Expr[A], guards Fact) {
			a.Do(Simp(Fwd(simplicial_set.FacesCompatibleDef)))
			i, j := a.FixAs[Nat](), a.FixAs[Nat]()
			pair := a.Assume()
			faces := a.Have(
				"i and j are faces of the horn: indices at most n + 1, neither of them k",
				"i ≤ n + 1 ∧ ¬(i = k) ∧ j ≤ n + 1 ∧ ¬(j = k)",
				By(pair, HornFacesMember.At(n, k, i), HornFacesMember.At(n, k, j)))
			a.Cases(a.Term("n = 0"))
			a.When(
				"a horn of dimension one has no pair of faces both other than k",
				func(b *Argument, zero Fact) {
					b.Show(
						"i < j ≤ 1 is the pair (0, 1), and k ≤ 1 is one of them",
						ByArith(guards, zero, faces, pair))
				})
			a.Otherwise(
				"above dimension one the faces of x satisfy the face identity",
				func(b *Argument, positive Fact) {
					previous := b.TermAs[Nat]("n - 1")
					below := b.Have(
						"n, being positive, is (n − 1) + 1",
						"n - 1 + 1 = n",
						ByArith(positive))
					top := b.Have(
						"and the dimension n + 1 of x is (n − 1) + 2",
						"n - 1 + 2 = n + 1",
						ByArith(positive))
					b.Show(
						"so the face identity on x at the dimension (n − 1) + 2 is the condition at the pair (i, j)",
						By(simplicial_set.FaceFace.Read(simplicial).At(previous, i, j, x), below, top, guards, faces, pair))
				})
		}),
	Reading: "k ≤ n + 1 is load-bearing at n = 0: for k ≥ 2 the pair (0, 1) is not " +
		"excluded and the condition would read the faces of vertices, which no axiom constrains.",
})}

// MapHorn — a simplicial map carries a horn of X to a horn of Y: the
// images of a face family of X on the faces of Λⁿ⁺¹ₖ are a face family
// of Y there. F(n) places the members in Y(n), and at a pair i < j of
// faces of the horn the face i of F(n, y(j)) is F(n − 1) of the face i
// of y(j), which the horn matches with the face j − 1 of y(i), whose
// image is the face j − 1 of F(n, y(i)) — F commuting with the faces of
// n-simplices, read at the dimension (n − 1) + 1 once n is positive; at
// n = 0 there is no pair.
var MapHorn = mapHornThm{family.Add(registry.ProofEntry{
	Name: "MapHorn",
	Key:  "prop_2ef78b016c3c8c7",
	Build: simplicial_set.SimplicialMap.Law(Statement{
		Binders: "∀n k:num. ∀y:(num → A).",
		Hypotheses: []string{
			"k ≤ n + 1",
			"face_family(n, horn_faces(n, k), y)",
		},
		Conclusion: "face_family(Y, n, horn_faces(n, k), λi:num. F(n, y(i)))",
	},
		func(a *Argument, simplicialMap Fact, n, k *Expr[Nat], _ *Expr[Fun[Nat, A]], horn Fact) {
			given := a.Conjuncts(
				horn,
				"the missing face k is at most n + 1",
				"y is a face family of X on the faces of the horn")
			bound := given[0]
			family := a.Conjuncts(
				a.Unfolded(given[1], simplicial_set.FaceFamilyDef),
				"the members of y are n-simplices of X",
				"and they are compatible")
			members, compatible := family[0], family[1]
			imageIn := a.Have(
				"F(n) carries the members of y into Y(n)",
				"∀i:num. i ∈ horn_faces(n, k) ⇒ F(n, y(i)) ∈ Y.simplices(n)",
				By(simplicial_set.MapIn.Read(simplicialMap), members))
			imageCompatible := a.Have(
				"and F carries matching faces of y to matching faces of the images",
				"faces_compatible(n, horn_faces(n, k), λi:num. F(n, y(i)))",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(simplicial_set.FacesCompatibleDef)))
					i, j := b.FixAs[Nat](), b.FixAs[Nat]()
					pair := b.Assume()
					faces := b.Have(
						"i and j are faces of the horn: indices at most n + 1, neither of them k",
						"i ≤ n + 1 ∧ ¬(i = k) ∧ j ≤ n + 1 ∧ ¬(j = k)",
						By(pair, HornFacesMember.At(n, k, i), HornFacesMember.At(n, k, j)))
					b.Cases(b.Term("n = 0"))
					b.When(
						"a horn of dimension one has no pair of faces both other than k",
						func(c *Argument, zero Fact) {
							c.Show(
								"i < j ≤ 1 is the pair (0, 1), and k ≤ 1 is one of them",
								ByArith(bound, zero, faces, pair))
						})
					b.Otherwise(
						"above dimension one F commutes with the faces of the n-simplices y(i) and y(j)",
						func(c *Argument, positive Fact) {
							previous := c.TermAs[Nat]("n - 1")
							below := c.Have(
								"n, being positive, is (n − 1) + 1",
								"n - 1 + 1 = n",
								ByArith(positive))
							indices := c.Have(
								"i and j − 1 index faces of an n-simplex",
								"i ≤ n ∧ j - 1 ≤ n",
								ByArith(faces, pair))
							simplices := c.Have(
								"y(i) and y(j) are n-simplices",
								"y(i) ∈ X.simplices(n) ∧ y(j) ∈ X.simplices(n)",
								By(members, pair))
							matching := c.Unfolded(compatible, simplicial_set.FacesCompatibleDef)
							face := simplicial_set.MapFace.Read(simplicialMap)
							c.Show(
								"so the face i of F(n, y(j)) is the face j − 1 of F(n, y(i))",
								CalcEq(
									Leg(
										c.TermAs[B]("F(n - 1, X.d(n, i, y(j)))"),
										"the face i of F(n, y(j)) is F(n − 1) of the face i of y(j), F commuting with the faces",
										By(Normalized, face.At(previous, i, c.TermAs[A]("y(j)")), below, indices, simplices)),
									Leg(
										c.TermAs[B]("F(n - 1, X.d(n, j - 1, y(i)))"),
										"y is compatible: the face i of y(j) is the face j − 1 of y(i)",
										By(matching.At(i, j), pair)),
									FinalLeg(
										"and F(n − 1) of the face j − 1 of y(i) is the face j − 1 of F(n, y(i))",
										By(
											Normalized,
											face.At(previous, c.TermAs[Nat]("j - 1"), c.TermAs[A]("y(i)")),
											below,
											indices,
											simplices)),
								))
						})
				}))
			a.Show(
				"so the images of the members of y are a face family of Y on the faces of the horn",
				Simp(Fwd(simplicial_set.FaceFamilyDef)),
				By(imageIn, imageCompatible))
		}),
})}

// SimplexFillsOwnHorn — a simplex fills the horn of its own faces:
// read at the family i ↦ d(n + 1, i, x), the filler condition asks
// d(n + 1, i, x) = d(n + 1, i, x) at every face of the horn, for any k.
var SimplexFillsOwnHorn = simplexFillsOwnHornThm{family.Add(registry.ProofEntry{
	Name: "SimplexFillsOwnHorn",
	Key:  "prop_7ffe1785d0849e29",
	Build: family.Theorem("∀d:(num → num → A → A). ∀n k:num. ∀x:A. "+
		"    faces_filler(d, n, horn_faces(n, k), λi:num. d(n + 1, i, x), x)",
		func(a *Argument, d *Expr[Fun3[Nat, Nat, A, A]], n, k *Expr[Nat], x *Expr[A]) {
			a.Show(
				"each face of x is itself",
				Unfold(simplicial_set.FacesFillerDef))
		}),
})}

// OneDimensionalHornFill — in any simplicial set a one-dimensional
// horn, which is one vertex, is filled by the degeneracy of the vertex:
// the one face of the horn is 1 − k, and both faces of the degenerate
// edge at y(1 − k) are y(1 − k). The horn's compatibility is not read:
// at n = 0 it has one face and no pair.
var OneDimensionalHornFill = oneDimensionalHornFillThm{family.Add(registry.ProofEntry{
	Name: "OneDimensionalHornFill",
	Key:  "prop_e64ad8eda6a187f6",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀k:num. ∀y:(num → A).",
		Hypotheses: []string{
			"k ≤ 1",
			"face_family(0, horn_faces(0, k), y)",
		},
		Conclusion: "∃x:A. x ∈ X.simplices(1) ∧ faces_filler(0, horn_faces(0, k), y, x)",
	},
		func(a *Argument, simplicial Fact, k *Expr[Nat], _ *Expr[Fun[Nat, A]], horn Fact) {
			zero, other := a.TermAs[Nat]("0"), a.TermAs[Nat]("1 - k")
			given := a.Conjuncts(
				horn,
				"the missing face k is at most 1",
				"y is a face family of X on the faces of the horn")
			bound := given[0]
			family := a.Conjuncts(
				a.Unfolded(given[1], simplicial_set.FaceFamilyDef),
				"the horn has a vertex at each of its faces",
				"compatible, with no pair of faces to match")
			vertices := family[0]
			ends := a.Have(
				"so k is 0 or 1",
				"k = 0 ∨ k = 1",
				ByArith(bound))
			face := a.Have(
				"and 1 − k, at most 1 and not k, is the face of the horn",
				"1 - k ∈ horn_faces(0, k)",
				ByArith(ends, HornFacesMember.At(zero, k, other)))
			vertex := a.Have(
				"the horn's one vertex is y(1 − k)",
				"y(1 - k) ∈ X.simplices(0)",
				By(vertices.At(other), face))
			degenerateEdgeEnds := simplicial_set.VertexDegeneracyFaces.Read(simplicial).At(
				a.TermAs[A]("y(1 - k)"))
			a.Take(a.TermAs[A]("X.s(0, 0, y(1 - k))"))
			fills := a.Have(
				"the degenerate edge at y(1 − k) has y(i) for its face at each face i of the horn",
				"faces_filler(0, horn_faces(0, k), y, X.s(0, 0, y(1 - k)))",
				Derive(func(b *Argument) {
					// The condition at n = 0 reads the faces d(0 + 1, i, ·); fold the numerals.
					b.Do(Simp(Fwd(simplicial_set.FacesFillerDef)), RingNf())
					i := b.FixAs[Nat]()
					member := b.Assume()
					index := b.Have(
						"a face i of the horn is at most 1 and not k",
						"i ≤ 1 ∧ ¬(i = k)",
						By(member, HornFacesMember.At(zero, k, i)))
					b.Cases(b.Term("i = 0"))
					b.When(
						"at i = 0 the face is face 0",
						func(c *Argument, atZero Fact) {
							vertexAt := c.Have(
								"k ≤ 1 is not i = 0, so 1 − k is 0",
								"1 - k = 0",
								ByArith(atZero, index, bound))
							c.Show(
								"face 0 of the degenerate edge is the vertex y(1 − k), which is y(0)",
								atZero.Rw(),
								By(degenerateEdgeEnds, vertex, vertexAt))
						})
					b.Otherwise(
						"otherwise i = 1 and the face is face 1",
						func(c *Argument, notZero Fact) {
							atOne := c.Have(
								"i ≤ 1 and i ≠ 0 leave i = 1",
								"i = 1",
								ByArith(notZero, index))
							vertexAt := c.Have(
								"k is not i = 1, so 1 − k is 1",
								"1 - k = 1",
								ByArith(atOne, index, bound))
							c.Show(
								"face 1 of the degenerate edge is the vertex y(1 − k), which is y(1)",
								atOne.Rw(),
								By(degenerateEdgeEnds, vertex, vertexAt))
						})
				}))
			a.Show(
				"so the degenerate edge, an edge, fills the horn",
				By(degenerateEdgeEnds, vertex, fills))
		}),
})}

// KanPoint — the point is a Kan complex: it is a simplicial set, and its
// one simplex a fills every horn, since a member of a face family of the
// point is a simplex of the point and so is a, and every face of a is a.
var KanPoint = kanPointThm{family.Add(registry.ProofEntry{
	Name: "KanPoint",
	Key:  "prop_1ab2c49c67e44863",
	Build: family.Instance(KanComplex, "∀a:A. kan_complex(simplicial_point(a))",
		Case(
			"the point is a simplicial set",
			By(simplicial_set.SimplicialPoint)),
		Case(
			"a fills every horn, since every member of a horn is a",
			Derive(func(b *Argument) {
				b.FixAs[Nat]()
				b.FixAs[Nat]()
				b.FixAs[Fun[Nat, A]]()
				horn := b.Assume()
				members := b.Have(
					"each member of the horn is a simplex of the point, so it is a",
					"∀i:num. i ∈ horn_faces(n, k) ⇒ y(i) = a",
					horn.Simp(
						Fwd(simplicial_set.FaceFamilyDef),
						Fwd(simplicial_set.SimplicialPointSimplicesDef),
						Fwd(set_basic.InSing)),
					By(horn))
				b.Take(b.TermAs[A]("a"))
				b.Show(
					"a is the (n + 1)-simplex of the point, and its "+
						"face at each face of the horn is a, the member there",
					Simp(
						Fwd(simplicial_set.SimplicialPointSimplicesDef),
						Fwd(set_basic.InSing),
						Fwd(simplicial_set.FacesFillerDef)),
					By(members))
			})),
	),
})}

// StandardSimplexNotKan — no standard simplex of positive dimension is
// a Kan complex: the horn Λ²₀ with the edge from 0 to 1 at index 2 and
// the degenerate edge at 0 at index 1 is compatible, the two edges
// meeting at the vertex 0; a filler w would read 1 at index 1 through
// its face 2 and 0 at index 2 through its face 1, against the
// monotonicity of a 2-simplex of Δⁿ.
var StandardSimplexNotKan = standardSimplexNotKanThm{family.Add(registry.ProofEntry{
	Name: "StandardSimplexNotKan",
	Key:  "prop_f20c4b9aba083e8",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"1 ≤ n",
		},
		Conclusion: "¬kan_complex(standard_simplex(n))",
	},
		func(a *Argument, n *Expr[Nat], positive Fact) {
			zero, one, two := a.TermAs[Nat]("0"), a.TermAs[Nat]("1"), a.TermAs[Nat]("2")
			// The horn Λ²₀: y(2) is the edge from 0 to 1, every other member the degenerate edge at 0.
			y, yDef := a.LetAs[Fun2[Nat, Nat, Nat]]("y", "λi:num. λk:num. COND(i = 2 ∧ k = 1, 1, 0)")
			members := a.Have(
				"each member of y is an edge of Δⁿ",
				"∀i:num. y(i) ∈ standard_simplex_simplices(n, 1)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					monotone := b.Have(
						"y(i) is monotone on 0 .. 1: it reads 1 at most at index 1, and a = 1 forces b = 1",
						"∀a b:num. a ≤ b ∧ b ≤ 1 ⇒ y(i, a) ≤ y(i, b)",
						yDef.Rw(),
						Derive(func(c *Argument) {
							c.FixAs[Nat]("a")
							c.FixAs[Nat]("b")
							c.Show(
								"each side is 1 or 0 by its condition, and the left is 1 only when a = b = 1",
								CondRewrite(),
								ByArith())
						}))
					bounded := b.Have(
						"its values are 0 and 1, at most n",
						"∀a:num. a ≤ 1 ⇒ y(i, a) ≤ n",
						yDef.Rw(),
						b.ForEach(func(_ *Expr[Nat]) Action { return Chain(CondRewrite(), ByArith(positive)) }))
					padded := b.Have(
						"and it is zero past 1",
						"∀a:num. 1 < a ⇒ y(i, a) = 0",
						yDef.Rw(),
						ByArith())
					b.Show(
						"these are the three clauses of an edge of Δⁿ",
						By(
							monotone,
							bounded,
							padded,
							simplicial_set.InStandardSimplex.At(n, one, b.TermAs[Fun[Nat, Nat]]("y(i)"))))
				}))
			compatible := a.Have(
				"and y is compatible on the faces of the horn missing 0: at "+
					"its one pair of faces (1, 2) both faces 1 are the vertex 0",
				"faces_compatible(λm:num. simplex_face, 1, horn_faces(1, 0), y)",
				Unfold(simplicial_set.FacesCompatibleDef),
				Derive(func(b *Argument) {
					i, j := b.FixAs[Nat](), b.FixAs[Nat]()
					pair := b.Assume()
					pairIs := b.Have(
						"the faces i < j of the horn, at most 2 and neither 0, are the pair (1, 2)",
						"i = 1 ∧ j = 2",
						ByArith(pair, HornFacesMember.At(one, zero, i), HornFacesMember.At(one, zero, j)))
					b.Show(
						"face 1 of y(2) reads y(2) at 0 and from 2 on, where it is 0, as y(1) is everywhere",
						Funext(),
						Simp(Fwd(simplicial_set.SimplexFaceDef)),
						yDef.Rw(),
						ByArith(pairIs))
				}))
			horn := a.Have(
				"so y is a horn of Δⁿ, edges at the faces of the horn compatible there",
				"face_family(standard_simplex(n), 1, horn_faces(1, 0), y)",
				Simp(Fwd(simplicial_set.FaceFamilyDef)),
				By(members, compatible))
			values := a.Have(
				"y(2) reads 1 at index 1, and y(1) reads 0 there",
				"y(2, 1) = 1 ∧ y(1, 1) = 0",
				yDef.Rw(),
				ByArith())

			contrary := a.SupposeNot()
			kan := a.Have(
				"suppose, for a contradiction, that Δⁿ is a Kan complex",
				"kan_complex(standard_simplex(n))",
				By(contrary))
			w, filler := a.ObtainAs[Fun[Nat, Nat]](
				"the horn y has a filler w, a 2-simplex of Δⁿ",
				"∃w:(num → num). "+
					"    w ∈ standard_simplex_simplices(n, 2) ∧ "+
					"    faces_filler(λm:num. simplex_face, 1, horn_faces(1, 0), y, w)",
				By(KanFill.Read(kan).At(one, zero, y), horn))
			parts := a.Conjuncts(
				filler,
				"w is a 2-simplex of Δⁿ",
				"whose faces at the faces of the horn are the members of y")
			simplex, prescribed := parts[0], parts[1]
			monotone := a.Have(
				"so w is monotone on 0 .. 2",
				"∀a b:num. a ≤ b ∧ b ≤ 2 ⇒ w(a) ≤ w(b)",
				By(simplex, simplicial_set.InStandardSimplex.At(n, two, w)))
			faceOf := a.Unfolded(prescribed, simplicial_set.FacesFillerDef)
			faces := a.Have(
				"and its face i, read at an index k, is y(i) read at k",
				"∀i k:num. i ∈ horn_faces(1, 0) ⇒ simplex_face(i, w, k) = y(i, k)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.FixAs[Nat]("k")
					index := b.Assume()
					b.Show(
						"two sequences that are equal agree at k",
						By(Normalized, faceOf.At(i), index))
				}))
			known := a.Have(
				"1 and 2 are faces of the horn, at most 2 and not 0",
				"1 ∈ horn_faces(1, 0) ∧ 2 ∈ horn_faces(1, 0)",
				By(HornFacesMember.At(one, zero, one), HornFacesMember.At(one, zero, two)))
			atOne := a.Have(
				"face 2 of w reads w(1) at index 1, where y(2) reads 1",
				"w(1) = 1",
				ByArith(faces.At(two, one), known, simplicial_set.SimplexFaceDef.At(two, w, one), values))
			atTwo := a.Have(
				"face 1 of w skips index 1 and reads w(2) there, where y(1) reads 0",
				"w(2) = 0",
				ByArith(faces.At(one, one), known, simplicial_set.SimplexFaceDef.At(one, w, one), values))
			a.Show(
				"so w(1) = 1 exceeds w(2) = 0, against the monotonicity of w",
				ByArith(monotone.At(one, two), atOne, atTwo))
		}),
})}
