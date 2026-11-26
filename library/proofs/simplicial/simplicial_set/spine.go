// spine.go — the spine of a simplex: its chain of edges between
// consecutive vertices, read by iterated faces, and the spine map, the
// chain of spine edges padded with the degenerate edge at the last
// vertex. Consecutive spine edges share a vertex, and the spine edges
// of a face of x are spine edges of x away from the deleted vertex.
// Nothing here reads a filler condition: the spines are the simplicial
// set's own, and the nerve, the Segal characterization and the maps
// into a nerve read them.

package simplicial_set

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// SimplexSpineDef — `simplex_spine(d, n, x, i)`: the i-th edge of the
// spine of the n-simplex x, between its vertices i and i + 1: the top
// n − 1 − i vertices removed, then the bottom i. Under a structure the
// text writes `simplex_spine(n, x, i)`.
var SimplexSpineDef = simplexSpineDefThm{family.Define(registry.DefEntry{
	Name:     "SimplexSpineDef",
	Key:      "prop_659943af55c09280",
	Const:    "simplex_spine",
	Type:     "(num → num → A → A) → num → A → num → A",
	Implicit: []string{"d"},
	Equations: []string{
		"∀d:(num → num → A → A). ∀n:num. ∀x:A. ∀i:num. " +
			"    simplex_spine(d, n, x, i) = " +
			"    face_iterate_bottom(d, i + 1, i, face_iterate_top(d, n, n - 1 - i, x))",
	},
	Deps: []registry.EntryLike{FaceIterateTopDef, FaceIterateBottomDef},
})}

// SpineIn — a spine edge is an edge: removing the top n − 1 − i vertices
// of the n-simplex x leaves an (i + 1)-simplex, and removing the bottom i
// vertices of that leaves a 1-simplex.
var SpineIn = spineInThm{family.Add(registry.ProofEntry{
	Name: "SpineIn",
	Key:  "prop_eed91a30bbf74fb0",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀n i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n)",
			"i < n",
		},
		Conclusion: "simplex_spine(n, x, i) ∈ X.simplices(1)",
	},
		func(a *Argument, simplicial Fact, n, i *Expr[Nat], x *Expr[A], given Fact) {
			parts := a.Conjuncts(
				given,
				"x is an n-simplex",
				"and i is a spine index of x")
			simplex, inside := parts[0], parts[1]
			counts := a.Have(
				"the top n − 1 − i ≤ n vertices removed leave dimension i + 1, the bottom i ≤ i + 1 then leave 1",
				"n - 1 - i ≤ n ∧ n - (n - 1 - i) = i + 1 ∧ i ≤ i + 1 ∧ i + 1 - i = 1",
				ByArith(inside))
			top := a.Have(
				"x with its top n − 1 − i vertices removed is an (i + 1)-simplex",
				"face_iterate_top(n, n - 1 - i, x) ∈ X.simplices(i + 1)",
				By(FaceIterateTopIn.Read(simplicial).At(n, a.TermAs[Nat]("n - 1 - i"), x), simplex, counts))
			y := a.TermAs[A]("face_iterate_top(n, n - 1 - i, x)")
			a.Show(
				"and with its bottom i vertices removed as well it is an edge",
				Simp(Fwd(SimplexSpineDef)),
				By(FaceIterateBottomIn.Read(simplicial).At(a.TermAs[Nat]("i + 1"), i, y), top, counts))
		}),
})}

// SpineEnds — consecutive spine edges share a vertex: the target of the
// i-th is the source of the (i+1)-th. Both are the vertex i + 1 of x. Let
// y be x with its top q = n − 2 − i vertices removed, an (i + 2)-simplex:
// the edge i + 1 is y with its bottom i + 1 vertices removed. The edge i
// removes one more top vertex, the last face of y, and its target one
// more bottom vertex; that last face passes the removal of the bottom
// i + 1 vertices of y as its face 1, the source of the edge i + 1.
var SpineEnds = spineEndsThm{family.Add(registry.ProofEntry{
	Name: "SpineEnds",
	Key:  "prop_4c7975d863dad67c",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀n i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n)",
			"i + 1 < n",
		},
		Conclusion: "X.d(1, 0, simplex_spine(n, x, i)) = X.d(1, 1, simplex_spine(n, x, i + 1))",
	},
		func(a *Argument, simplicial Fact, n, i *Expr[Nat], x *Expr[A], given Fact) {
			parts := a.Conjuncts(
				given,
				"x is an n-simplex",
				"and i + 1 is a spine index of x")
			simplex, inside := parts[0], parts[1]
			d := a.TermAs[Fun3[Nat, Nat, A, A]]("X.d")
			// q: the number of vertices of x past the vertex i + 2 — the top
			// count of the edge i + 1, spelled as SimplexSpineDef spells it there.
			q, qDef := a.LetAs[Nat]("q", "n - 1 - (i + 1)")
			next := a.TermAs[Nat]("i + 1")
			last := a.TermAs[Nat]("i + 1 + 1")
			y := a.TermAs[A]("face_iterate_top(n, q, x)")
			yIn := a.Have(
				"so y, x with its top q vertices removed, is an (i + 2)-simplex",
				"face_iterate_top(n, q, x) ∈ X.simplices(i + 1 + 1)",
				ByArith(FaceIterateTopIn.Read(simplicial).At(n, q, x), simplex, qDef, inside))
			edge := a.TermAs[A]("face_iterate_top(n, n - 1 - i, x)")
			a.Show(
				"both ends are the vertex i + 1 of x, the source of y with its bottom i + 1 vertices removed",
				Simp(Fwd(SimplexSpineDef)),
				qDef.RwRev(),
				CalcEq(
					Leg(
						a.TermAs[A]("face_iterate_bottom(i + 1, i + 1, face_iterate_top(n, n - 1 - i, x))"),
						"the 0-th face of the edge i removes one more bottom vertex",
						ByArith(FaceIterateBottomSucc.At(d, next, i, edge))),
					Leg(
						a.TermAs[A](
							"face_iterate_bottom(i + 1, i + 1, X.d(i + 1 + 1, i + 1 + 1, face_iterate_top(n, q, x)))"),
						"removing the top q + 1 vertices of x is the last face of y",
						ByArith(FaceIterateTopSucc.At(d, n, q, x), qDef, inside)),
					FinalLeg(
						"the last face of y, at its vertex i + 2, passes the removal "+
							"of its bottom i + 1 vertices as the face (i + 2) − (i + 1) = 1",
						ByArith(FaceIterateBottomFace.Read(simplicial).At(next, next, last, y), yIn)),
				))
		}),
})}

// SpineMapDef — `spine_map(d, s, n, x)`: the chain of the spine edges of
// x, padded with the degenerate edge at its last vertex. Under the
// structure the text writes `spine_map(n, x)`.
var SpineMapDef = spineMapDefThm{family.Define(registry.DefEntry{
	Name:     "SpineMapDef",
	Key:      "prop_b86fd79e8ac4bf4a",
	Const:    "spine_map",
	Type:     "(num → num → A → A) → (num → num → A → A) → num → A → num → A",
	Implicit: []string{"d", "s"},
	Equations: []string{
		"∀d s:(num → num → A → A). ∀n:num. ∀x:A. ∀j:num. " +
			"    spine_map(d, s, n, x, j) = " +
			"    COND(j < n, simplex_spine(d, n, x, j), s(0, 0, face_iterate_bottom(d, n, n, x)))",
	},
	Deps: []registry.EntryLike{SimplexSpineDef, FaceIterateBottomDef},
})}

// FaceSpineBelow — below the vertex a face deletes, the spine edges of
// the face are those of x: the edge j of the face of x at i > j + 1 keeps
// the vertices 0, …, j + 1 of x, the face being absorbed by the removal
// of the top vertices.
var FaceSpineBelow = faceSpineBelowThm{family.Add(registry.ProofEntry{
	Name: "FaceSpineBelow",
	Key:  "prop_27427167a7111724",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀n i j:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n + 1)",
			"j + 1 < i",
			"i ≤ n + 1",
		},
		Conclusion: "simplex_spine(n, X.d(n + 1, i, x), j) = simplex_spine(n + 1, x, j)",
	},
		func(a *Argument, simplicial Fact, n, i, j *Expr[Nat], x *Expr[A], given Fact) {
			parts := a.Conjuncts(
				given,
				"x is an (n + 1)-simplex",
				"the face lies past the vertex j + 1",
				"and is one of the faces of x")
			simplex, past, face := parts[0], parts[1], parts[2]
			absorbed := a.Have(
				"the face lies among the top n − j vertices of x, which the spine edge j removes",
				"face_iterate_top(n, n - 1 - j, X.d(n + 1, i, x)) = face_iterate_top(n + 1, n - 1 - j + 1, x)",
				ByArith(
					FaceIterateTopAbove.Read(simplicial).At(n, a.TermAs[Nat]("n - 1 - j"), i, x),
					simplex,
					past,
					face))
			count := a.Have(
				"and the spine edge j of x removes as many",
				"n - 1 - j + 1 = n + 1 - 1 - j",
				ByArith(past, face))
			a.Show(
				"so both edges are x with those vertices and its bottom j removed",
				Simp(Fwd(SimplexSpineDef)),
				absorbed.Rw(),
				count.Rw(),
				Basic())
		}),
})}

// FaceSpineAbove — above the vertex a face deletes, the spine edges of
// the face are those of x one index up: the face at i ≤ j commutes with
// the removal of the top vertices and is then absorbed by the removal of
// the bottom j.
var FaceSpineAbove = faceSpineAboveThm{family.Add(registry.ProofEntry{
	Name: "FaceSpineAbove",
	Key:  "prop_80490bcdeec36cc8",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀n i j:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n + 1)",
			"i ≤ j",
			"j < n",
		},
		Conclusion: "simplex_spine(n, X.d(n + 1, i, x), j) = simplex_spine(n + 1, x, j + 1)",
	},
		func(a *Argument, simplicial Fact, n, i, j *Expr[Nat], x *Expr[A], given Fact) {
			parts := a.Conjuncts(
				given,
				"x is an (n + 1)-simplex",
				"the face lies at or below the vertex j",
				"and j is a spine index of the face")
			simplex, before, inside := parts[0], parts[1], parts[2]
			// q: the number of vertices of x past the vertex j + 2.
			q, qDef := a.LetAs[Nat]("q", "n - 1 - j")
			next := a.TermAs[Nat]("j + 1")
			y := a.TermAs[A]("face_iterate_top(n + 1, q, x)")
			dimension := a.Have(
				"x with its top q vertices removed has dimension j + 2",
				"n + 1 - q = j + 1 + 1",
				ByArith(qDef, inside))
			ranges := a.Have(
				"q is at most n + 1, and i + q at most n",
				"q ≤ n + 1 ∧ i + q ≤ n",
				ByArith(qDef, before, inside))
			yIn := a.Have(
				"x with its top q vertices removed is a (j + 2)-simplex",
				"face_iterate_top(n + 1, q, x) ∈ X.simplices(j + 1 + 1)",
				By(FaceIterateTopIn.Read(simplicial).At(a.TermAs[Nat]("n + 1"), q, x), simplex, ranges, dimension))
			commuted := a.Have(
				"the face at i ≤ j, below the top q + 1 vertices, commutes with the removal of the top q",
				"face_iterate_top(n, q, X.d(n + 1, i, x)) = X.d(n + 1 - q, i, face_iterate_top(n + 1, q, x))",
				ByArith(FaceIterateTopFace.Read(simplicial).At(n, q, i, x), simplex, ranges))
			count := a.Have(
				"the spine edge j + 1 of x removes its top q vertices",
				"n + 1 - 1 - (j + 1) = q",
				ByArith(qDef, inside))
			a.Show(
				"the face is then absorbed by the removal of the bottom j",
				Simp(Fwd(SimplexSpineDef)),
				qDef.RwRev(),
				count.Rw(),
				CalcEq(
					Leg(
						a.TermAs[A]("face_iterate_bottom(j + 1, j, X.d(j + 1 + 1, i, face_iterate_top(n + 1, q, x)))"),
						"the face passes the removal of the top vertices",
						By(commuted, dimension)),
					FinalLeg(
						"and the face at i ≤ j is absorbed by the removal of the bottom j",
						ByArith(FaceIterateBottomBelow.Read(simplicial).At(next, j, i, y), yIn, before)),
				))
		}),
})}
