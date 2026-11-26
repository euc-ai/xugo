// left_fibration.go — left fibrations: simplicial maps lifting every
// horn except the last outer horn. The one-dimensional condition lifts
// an edge from a prescribed source; the two-dimensional horn Λ²₀ lifts
// a triangle from two edges out of one vertex.

package kan_fibration

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// LeftFibration — left_fibration(p) requires lifts of Λ^(n+1)_k for
// k ≤ n, including k = 0; the last outer horn k = n+1 is excluded.
var LeftFibration = leftFibrationThm{family.DefineStructure(registry.DefEntry{
	Name:     "LeftFibration",
	Key:      "prop_e1fecb5ad6868998",
	Const:    "left_fibration",
	Type:     "simplicial_ops(A) → simplicial_ops(B) → (num → A → B) → bool",
	Implicit: []string{"X", "Y"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). ∀p:(num → A → B). " +
			"    left_fibration(X, Y, p) ⇔ " +
			"    simplicial_map(X, Y, p) ∧ " +
			"    (∀n k:num. ∀y:(num → A). ∀z:B. " +
			"        k ≤ n ∧ " +
			"        face_family(X, n, horn_faces(n, k), y) ∧ " +
			"        z ∈ Y.simplices(n + 1) ∧ " +
			"        faces_filler(Y.d, n, horn_faces(n, k), λi:num. p(n, y(i)), z) ⇒ " +
			"        ∃x:A. " +
			"            x ∈ X.simplices(n + 1) ∧ " +
			"            faces_filler(X.d, n, horn_faces(n, k), y, x) ∧ " +
			"            p(n + 1, x) = z)",
	},
	Reading: "The convention is 0 ≤ k < q in dimension q = n + 1. Neither source nor target " +
		"is assumed to be a quasi-category; simplicial_map includes both simplicial-set structures.",
})}

// LeftFibrationMap — a left fibration is a simplicial map.
var LeftFibrationMap = leftFibrationMapThm{family.Add(registry.ProofEntry{
	Name:  "LeftFibrationMap",
	Key:   "prop_8905a258c0f2f886",
	Build: LeftFibration.Axiom("simplicial_map(X, Y, p)"),
})}

// LeftFibrationLift — every non-last horn over a simplex lifts.
var LeftFibrationLift = leftFibrationLiftThm{family.Add(registry.ProofEntry{
	Name: "LeftFibrationLift",
	Key:  "prop_58e5fa7979d109ba",
	Build: LeftFibration.Axiom(Statement{
		Binders: "∀n k:num. ∀y:(num → A). ∀z:B.",
		Hypotheses: []string{
			"k ≤ n",
			"face_family(X, n, horn_faces(n, k), y)",
			"z ∈ Y.simplices(n + 1)",
			"faces_filler(n, horn_faces(n, k), λi:num. p(n, y(i)), z)",
		},
		Conclusion: "∃x:A. " +
			"    x ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, k), y, x) ∧ p(n + 1, x) = z",
	}),
})}

// LeftFibrationTriangleLift — a left fibration lifts the horn Λ²₀: two
// edges g and h of X out of one vertex, over a triangle t of Y whose
// faces 1 and 2 are their images, are the faces 1 and 2 of a triangle
// of X over t. The family with g at 1 and h at 2 is a face family on
// the faces of the horn missing face 0 at n = 1, compatible because its
// one pair of faces (1, 2) meets at the common source; t fills its
// image, and LeftFibrationLift lifts it over t.
var LeftFibrationTriangleLift = leftFibrationTriangleLiftThm{family.Add(registry.ProofEntry{
	Name: "LeftFibrationTriangleLift",
	Key:  "prop_ca97f2eec89ab665",
	Build: LeftFibration.Law(Statement{
		Binders: "∀g h:A. ∀t:B.",
		Hypotheses: []string{
			"g ∈ X.simplices(1)",
			"h ∈ X.simplices(1)",
			"X.d(1, 1, g) = X.d(1, 1, h)",
			"t ∈ Y.simplices(2)",
			"Y.d(2, 1, t) = p(1, g)",
			"Y.d(2, 2, t) = p(1, h)",
		},
		Conclusion: "∃w:A. w ∈ X.simplices(2) ∧ X.d(2, 1, w) = g ∧ X.d(2, 2, w) = h ∧ p(2, w) = t",
	},
		func(a *Argument, left Fact, g, h *Expr[A], t *Expr[B], given Fact) {
			parts := a.Conjuncts(
				given,
				"g is an edge",
				"h is an edge",
				"g and h have a common source",
				"t is a triangle",
				"its face 1 is the image of g",
				"its face 2 is the image of h")
			gEdge, hEdge, source, tIn, overG, overH :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
			zero, one, two := a.TermAs[Nat]("0"), a.TermAs[Nat]("1"), a.TermAs[Nat]("2")

			// The horn: h at 2, g everywhere else, its value at 0 never read.
			y, yDef := a.LetAs[Fun[Nat, A]]("y", "λi:num. COND(i = 2, h, g)")
			yValues := a.Have(
				"the known faces are g at 1 and h at 2",
				"y(1) = g ∧ y(2) = h",
				Simp(Fwd(yDef)),
				ByArith())
			edges := a.Have(
				"each member of y is g or h, an edge",
				"∀i:num. y(i) ∈ X.simplices(1)",
				Simp(Fwd(yDef)),
				By(gEdge, hEdge))
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
						ByArith(
							pair,
							kan_complex.HornFacesMember.At(one, zero, i),
							kan_complex.HornFacesMember.At(one, zero, j)))
					b.Show(
						"where the condition is d(1, 1, y(2)) = d(1, 1, y(1)): h and g have one source",
						ByArith(ends, yValues, source))
				}))
			horn := a.Have(
				"so y is a horn of X, edges at the faces of the horn compatible there",
				"face_family(X, 1, horn_faces(1, 0), y)",
				Simp(Fwd(simplicial_set.FaceFamilyDef)),
				By(edges, compatible))
			images := a.Have(
				"and t fills its image: each known face lies over the corresponding face of t",
				"faces_filler(1, horn_faces(1, 0), λi:num. p(1, y(i)), t)",
				Derive(func(b *Argument) {
					// The condition at n = 1 reads the faces d'(1 + 1, i, t); fold the numerals.
					b.Do(Simp(Fwd(simplicial_set.FacesFillerDef)), RingNf())
					i := b.FixAs[Nat]()
					face := b.Assume()
					indices := b.Have(
						"a face of the horn, at most 2 and not 0, is 1 or 2",
						"i = 1 ∨ i = 2",
						ByArith(face, kan_complex.HornFacesMember.At(one, zero, i)))
					b.Show(
						"the two image equations cover the known faces",
						indices.SplitDisj(
							LeftHolds(
								"g lies over face 1 of t",
								Given(func(c *Argument, atOne Fact) {
									c.Show(
										"the face 1 images agree",
										Simp(Fwd(atOne), Fwd(yValues)),
										By(overG))
								})),
							RightHolds(
								"h lies over face 2 of t",
								Given(func(c *Argument, atTwo Fact) {
									c.Show(
										"the face 2 images agree",
										Simp(Fwd(atTwo), Fwd(yValues)),
										By(overH))
								})),
						))
				}))
			w, lift := a.ObtainAs[A](
				"lift t with g and h as its known faces",
				"∃w:A. w ∈ X.simplices(2) ∧ faces_filler(1, horn_faces(1, 0), y, w) ∧ p(2, w) = t",
				By(horn, tIn, images, LeftFibrationLift.Read(left).At(one, zero, y, t)))
			liftData := a.Conjuncts(
				lift,
				"w is a 2-simplex",
				"whose faces at the faces of the horn are the members of y",
				"w lies over t")
			wIn, wFaces, wImage :=
				liftData[0], a.Unfolded(liftData[1], simplicial_set.FacesFillerDef), liftData[2]
			known := a.Have(
				"1 and 2 are faces of the horn, at most 2 and not 0",
				"1 ∈ horn_faces(1, 0) ∧ 2 ∈ horn_faces(1, 0)",
				By(kan_complex.HornFacesMember.At(one, zero, one), kan_complex.HornFacesMember.At(one, zero, two)))
			faceOne := a.Have(
				"its face 1 is y(1) = g",
				"X.d(2, 1, w) = g",
				ByArith(wFaces.At(one), known, yValues))
			faceTwo := a.Have(
				"and its face 2 is y(2) = h",
				"X.d(2, 2, w) = h",
				ByArith(wFaces.At(two), known, yValues))
			a.Take(w)
			a.Show(
				"w is a triangle over t with faces g and h",
				By(wIn, faceOne, faceTwo, wImage))
		}),
})}
