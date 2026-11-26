// simplicial_set.go — the structure: a family of sets indexed by the
// dimension with total face and degeneracy maps that read the
// dimension of their argument, and the eight simplicial identities as
// its axioms; edges and 2-simplices: the degenerate edge at a vertex,
// the two ends of an edge with the identity edge at each, the three
// edges of a 2-simplex meeting at its vertices, and the degenerate
// 2-simplices on an edge with their faces; sub-simplicial
// sets, which are simplicial sets with the restricted maps; simplicial
// maps between simplicial sets on two types, their identity,
// composition, restriction, image and preimage; isomorphisms;
// the base simplex at a vertex, the totally degenerate simplex every
// homotopy group is measured against; and the one-point simplicial set.

package simplicial_set

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structure and its axioms
// ---------------------------------------------------------------------------

// SimplicialSet — `simplicial_set(X)`: X(n) is the set of
// n-simplices of a type A, `d(n, i, x)` the i-th face of the n-simplex
// x, an (n−1)-simplex, and `s(n, i, x)` its i-th degeneracy, an
// (n+1)-simplex. The eight conjuncts are the two closures and the
// simplicial identities d_i d_j = d_{j−1} d_i (i < j),
// s_i s_j = s_{j+1} s_i (i ≤ j),
// d_i s_j = s_{j−1} d_i (i < j), d_j s_j = id = d_{j+1} s_j, and
// d_i s_j = s_j d_{i−1} (i > j + 1).
var SimplicialSet = simplicialSetThm{family.DefineStructure(registry.DefEntry{
	Name:    "SimplicialSet",
	Key:     "prop_66be3663f227a0f9",
	Const:   "simplicial_set",
	Type:    "simplicial_ops(A) → bool",
	Subject: "X",
	Equations: []string{
		"∀X:simplicial_ops(A). " +
			"    simplicial_set(X) ⇔ " +
			"    (∀n i:num. ∀x:A. x ∈ X.simplices(n + 1) ∧ i ≤ n + 1 ⇒ X.d(n + 1, i, x) ∈ X.simplices(n)) ∧ " +
			"    (∀n i:num. ∀x:A. x ∈ X.simplices(n) ∧ i ≤ n ⇒ X.s(n, i, x) ∈ X.simplices(n + 1)) ∧ " +
			"    (∀n i j:num. ∀x:A. " +
			"        x ∈ X.simplices(n + 2) ∧ i < j ∧ j ≤ n + 2 ⇒ " +
			"        X.d(n + 1, i, X.d(n + 2, j, x)) = X.d(n + 1, j - 1, X.d(n + 2, i, x))) ∧ " +
			"    (∀n i j:num. ∀x:A. " +
			"        x ∈ X.simplices(n) ∧ i ≤ j ∧ j ≤ n ⇒ " +
			"        X.s(n + 1, i, X.s(n, j, x)) = X.s(n + 1, j + 1, X.s(n, i, x))) ∧ " +
			"    (∀n i j:num. ∀x:A. " +
			"        x ∈ X.simplices(n + 1) ∧ i < j ∧ j ≤ n + 1 ⇒ " +
			"        X.d(n + 2, i, X.s(n + 1, j, x)) = X.s(n, j - 1, X.d(n + 1, i, x))) ∧ " +
			"    (∀n i:num. ∀x:A. x ∈ X.simplices(n) ∧ i ≤ n ⇒ X.d(n + 1, i, X.s(n, i, x)) = x) ∧ " +
			"    (∀n i:num. ∀x:A. x ∈ X.simplices(n) ∧ i ≤ n ⇒ X.d(n + 1, i + 1, X.s(n, i, x)) = x) ∧ " +
			"    (∀n i j:num. ∀x:A. " +
			"        x ∈ X.simplices(n + 1) ∧ j + 1 < i ∧ i ≤ n + 2 ⇒ " +
			"        X.d(n + 2, i, X.s(n + 1, j, x)) = X.s(n, j, X.d(n + 1, i - 1, x)))",
	},
	Reading: "The maps are total: a face of a 0-simplex and a face past the dimension " +
		"are values the axioms never read. The face identity is stated on X(n + 2), where both " +
		"composites land in X(n); stated on X(n + 1) it would constrain the faces of vertices.",
	Deps: recordFields,
})}

// FaceIn — a face of an (n+1)-simplex is an n-simplex.
var FaceIn = faceInThm{family.Add(registry.ProofEntry{
	Name: "FaceIn",
	Key:  "prop_42587c507ffd88ce",
	Build: SimplicialSet.Axiom(Statement{
		Binders: "∀n i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n + 1)",
			"i ≤ n + 1",
		},
		Conclusion: "X.d(n + 1, i, x) ∈ X.simplices(n)",
	}),
})}

// DegeneracyIn — a degeneracy of an n-simplex is an (n+1)-simplex.
var DegeneracyIn = degeneracyInThm{family.Add(registry.ProofEntry{
	Name: "DegeneracyIn",
	Key:  "prop_f0b11108746567df",
	Build: SimplicialSet.Axiom(Statement{
		Binders: "∀n i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n)",
			"i ≤ n",
		},
		Conclusion: "X.s(n, i, x) ∈ X.simplices(n + 1)",
	}),
})}

// FaceFace — d_i d_j = d_{j−1} d_i for i < j.
var FaceFace = faceFaceThm{family.Add(registry.ProofEntry{
	Name: "FaceFace",
	Key:  "prop_4e3d62065f15603d",
	Build: SimplicialSet.Axiom(Statement{
		Binders: "∀n i j:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n + 2)",
			"i < j",
			"j ≤ n + 2",
		},
		Conclusion: "X.d(n + 1, i, X.d(n + 2, j, x)) = X.d(n + 1, j - 1, X.d(n + 2, i, x))",
	}),
})}

// DegeneracyDegeneracy — s_i s_j = s_{j+1} s_i for i ≤ j.
var DegeneracyDegeneracy = degeneracyDegeneracyThm{family.Add(registry.ProofEntry{
	Name: "DegeneracyDegeneracy",
	Key:  "prop_aa1857f12e4f3f4d",
	Build: SimplicialSet.Axiom(Statement{
		Binders: "∀n i j:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n)",
			"i ≤ j",
			"j ≤ n",
		},
		Conclusion: "X.s(n + 1, i, X.s(n, j, x)) = X.s(n + 1, j + 1, X.s(n, i, x))",
	}),
})}

// FaceDegeneracyBelow — d_i s_j = s_{j−1} d_i for i < j.
var FaceDegeneracyBelow = faceDegeneracyBelowThm{family.Add(registry.ProofEntry{
	Name: "FaceDegeneracyBelow",
	Key:  "prop_1a8c95e1c45894bc",
	Build: SimplicialSet.Axiom(Statement{
		Binders: "∀n i j:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n + 1)",
			"i < j",
			"j ≤ n + 1",
		},
		Conclusion: "X.d(n + 2, i, X.s(n + 1, j, x)) = X.s(n, j - 1, X.d(n + 1, i, x))",
	}),
})}

// FaceDegeneracyEqual — d_i s_i is the identity.
var FaceDegeneracyEqual = faceDegeneracyEqualThm{family.Add(registry.ProofEntry{
	Name: "FaceDegeneracyEqual",
	Key:  "prop_f1be386c6d22292d",
	Build: SimplicialSet.Axiom(Statement{
		Binders: "∀n i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n)",
			"i ≤ n",
		},
		Conclusion: "X.d(n + 1, i, X.s(n, i, x)) = x",
	}),
})}

// FaceDegeneracyNext — d_{i+1} s_i is the identity.
var FaceDegeneracyNext = faceDegeneracyNextThm{family.Add(registry.ProofEntry{
	Name: "FaceDegeneracyNext",
	Key:  "prop_19869ed41c79dd36",
	Build: SimplicialSet.Axiom(Statement{
		Binders: "∀n i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n)",
			"i ≤ n",
		},
		Conclusion: "X.d(n + 1, i + 1, X.s(n, i, x)) = x",
	}),
})}

// FaceDegeneracyAbove — d_i s_j = s_j d_{i−1} for i > j + 1.
var FaceDegeneracyAbove = faceDegeneracyAboveThm{family.Add(registry.ProofEntry{
	Name: "FaceDegeneracyAbove",
	Key:  "prop_4c573268171cb896",
	Build: SimplicialSet.Axiom(Statement{
		Binders: "∀n i j:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n + 1)",
			"j + 1 < i",
			"i ≤ n + 2",
		},
		Conclusion: "X.d(n + 2, i, X.s(n + 1, j, x)) = X.s(n, j, X.d(n + 1, i - 1, x))",
	}),
})}

// ---------------------------------------------------------------------------
// Edges and 2-simplices
// ---------------------------------------------------------------------------

// VertexDegeneracyFaces — the degeneracy s(0, 0, v) of a vertex v is an
// edge from v to v: both its faces cancel the degeneracy.
var VertexDegeneracyFaces = vertexDegeneracyFacesThm{family.Add(registry.ProofEntry{
	Name: "VertexDegeneracyFaces",
	Key:  "prop_12800fb580a0dd5a",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀v:A.",
		Hypotheses: []string{
			"v ∈ X.simplices(0)",
		},
		Conclusion: "X.s(0, 0, v) ∈ X.simplices(1) ∧ " +
			"X.d(1, 0, X.s(0, 0, v)) = v ∧ " +
			"X.d(1, 1, X.s(0, 0, v)) = v",
	},
		func(a *Argument, simplicial Fact, v *Expr[A], vertex Fact) {
			zero := a.TermAs[Nat]("0")
			a.Show(
				"each clause is one axiom read at the degeneracy index 0 of the vertex v",
				SplitConjAll(
					Case(
						"a degeneracy of the vertex v is an edge",
						By(DegeneracyIn.Read(simplicial).At(zero, zero, v), vertex)),
					Case(
						"its face 0, the one at the degeneracy's index, is v",
						By(FaceDegeneracyEqual.Read(simplicial).At(zero, zero, v), vertex)),
					Case(
						"its face 1, the one just past the degeneracy's index, is v",
						By(FaceDegeneracyNext.Read(simplicial).At(zero, zero, v), vertex)),
				))
		}),
})}

// EdgeEndIdentities — the two ends of an edge are vertices, and the
// identity edge at each end starts and ends there: the ends are the two
// faces of the edge, and VertexDegeneracyFaces is read at each.
var EdgeEndIdentities = edgeEndIdentitiesThm{family.Add(registry.ProofEntry{
	Name: "EdgeEndIdentities",
	Key:  "prop_5142945730be0335",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀f:A.",
		Hypotheses: []string{
			"f ∈ X.simplices(1)",
		},
		Conclusion: "X.d(1, 1, f) ∈ X.simplices(0) ∧ " +
			"X.d(1, 0, f) ∈ X.simplices(0) ∧ " +
			"X.s(0, 0, X.d(1, 1, f)) ∈ X.simplices(1) ∧ " +
			"X.d(1, 0, X.s(0, 0, X.d(1, 1, f))) = X.d(1, 1, f) ∧ " +
			"X.d(1, 1, X.s(0, 0, X.d(1, 1, f))) = X.d(1, 1, f) ∧ " +
			"X.s(0, 0, X.d(1, 0, f)) ∈ X.simplices(1) ∧ " +
			"X.d(1, 0, X.s(0, 0, X.d(1, 0, f))) = X.d(1, 0, f) ∧ " +
			"X.d(1, 1, X.s(0, 0, X.d(1, 0, f))) = X.d(1, 0, f)",
	},
		func(a *Argument, simplicial Fact, f *Expr[A], edge Fact) {
			zero, one := a.TermAs[Nat]("0"), a.TermAs[Nat]("1")
			source, target := a.TermAs[A]("X.d(1, 1, f)"), a.TermAs[A]("X.d(1, 0, f)")
			vertices := a.Have(
				"the two ends of f, its faces 1 and 0, are vertices",
				"X.d(1, 1, f) ∈ X.simplices(0) ∧ X.d(1, 0, f) ∈ X.simplices(0)",
				By(edge, FaceIn.Read(simplicial).At(zero, one, f), FaceIn.Read(simplicial).At(zero, zero, f)))
			a.Show(
				"so the identity edge at each end starts and ends there",
				By(
					vertices,
					VertexDegeneracyFaces.Read(simplicial).At(source),
					VertexDegeneracyFaces.Read(simplicial).At(target)))
		}),
})}

// TwoSimplexFaceEnds — the three edges of a 2-simplex w meet at its
// three vertices. Its three faces are edges, an edge running from its
// face 1 to its face 0, and each shared vertex is one face identity
// d_i d_j = d_{j−1} d_i: faces 1 and 2 start at the vertex 0, face 2
// ends at the vertex 1 where face 0 starts, and faces 1 and 0 end at
// the vertex 2.
var TwoSimplexFaceEnds = twoSimplexFaceEndsThm{family.Add(registry.ProofEntry{
	Name: "TwoSimplexFaceEnds",
	Key:  "prop_d957ab4bf01b7ed2",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀w:A.",
		Hypotheses: []string{
			"w ∈ X.simplices(2)",
		},
		Conclusion: "X.d(2, 0, w) ∈ X.simplices(1) ∧ " +
			"X.d(2, 1, w) ∈ X.simplices(1) ∧ " +
			"X.d(2, 2, w) ∈ X.simplices(1) ∧ " +
			"X.d(1, 1, X.d(2, 1, w)) = X.d(1, 1, X.d(2, 2, w)) ∧ " +
			"X.d(1, 0, X.d(2, 2, w)) = X.d(1, 1, X.d(2, 0, w)) ∧ " +
			"X.d(1, 0, X.d(2, 1, w)) = X.d(1, 0, X.d(2, 0, w))",
	},
		func(a *Argument, simplicial Fact, w *Expr[A], triangle Fact) {
			zero, one, two := a.TermAs[Nat]("0"), a.TermAs[Nat]("1"), a.TermAs[Nat]("2")
			a.Show(
				"each clause is one axiom read at the 2-simplex w",
				SplitConjAll(
					Case(
						"the face 0 of the 2-simplex w is an edge",
						By(FaceIn.Read(simplicial).At(one, zero, w), triangle)),
					Case(
						"so is its face 1",
						By(FaceIn.Read(simplicial).At(one, one, w), triangle)),
					Case(
						"and its face 2",
						By(FaceIn.Read(simplicial).At(one, two, w), triangle)),
					Case(
						"the faces 1 and 2 start at the vertex 0: d_1 d_1 = d_1 d_2",
						ByArith(FaceFace.Read(simplicial).At(zero, one, two, w), triangle)),
					Case(
						"the face 2 ends at the vertex 1, where the face 0 starts: d_0 d_2 = d_1 d_0",
						By(FaceFace.Read(simplicial).At(zero, zero, two, w), triangle)),
					Case(
						"the faces 1 and 0 end at the vertex 2: d_0 d_1 = d_0 d_0",
						By(FaceFace.Read(simplicial).At(zero, zero, one, w), triangle)),
				))
		}),
})}

// EdgeLastDegeneracyFaces — the last degeneracy s(1, 1, f) of an edge f
// is a 2-simplex whose face 0 is the degenerate edge at the target of f
// and whose faces 1 and 2 are f itself.
var EdgeLastDegeneracyFaces = edgeLastDegeneracyFacesThm{family.Add(registry.ProofEntry{
	Name: "EdgeLastDegeneracyFaces",
	Key:  "prop_a71fd5fb4d2e56e5",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀f:A.",
		Hypotheses: []string{
			"f ∈ X.simplices(1)",
		},
		Conclusion: "X.s(1, 1, f) ∈ X.simplices(2) ∧ " +
			"X.d(2, 0, X.s(1, 1, f)) = X.s(0, 0, X.d(1, 0, f)) ∧ " +
			"X.d(2, 1, X.s(1, 1, f)) = f ∧ " +
			"X.d(2, 2, X.s(1, 1, f)) = f",
	},
		func(a *Argument, simplicial Fact, f *Expr[A], edge Fact) {
			zero, one := a.TermAs[Nat]("0"), a.TermAs[Nat]("1")
			a.Show(
				"each clause is one axiom read at the degeneracy index 1 of the edge f",
				SplitConjAll(
					Case(
						"a degeneracy of the edge f is a 2-simplex",
						By(DegeneracyIn.Read(simplicial).At(one, one, f), edge)),
					Case(
						"its face 0 passes below the degeneracy: the degenerate edge at the target of f",
						By(FaceDegeneracyBelow.Read(simplicial).At(zero, zero, one, f), edge)),
					Case(
						"its face 1, the one at the degeneracy's index, is f",
						By(FaceDegeneracyEqual.Read(simplicial).At(one, one, f), edge)),
					Case(
						"its face 2, the one just past the degeneracy's index, is f",
						By(FaceDegeneracyNext.Read(simplicial).At(one, one, f), edge)),
				))
		}),
})}

// EdgeFirstDegeneracyFaces — the first degeneracy s(1, 0, g) of an edge g
// is a 2-simplex whose faces 0 and 1 are g itself and whose face 2 is the
// degenerate edge at the source of g.
var EdgeFirstDegeneracyFaces = edgeFirstDegeneracyFacesThm{family.Add(registry.ProofEntry{
	Name: "EdgeFirstDegeneracyFaces",
	Key:  "prop_97295642548517c5",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀g:A.",
		Hypotheses: []string{
			"g ∈ X.simplices(1)",
		},
		Conclusion: "X.s(1, 0, g) ∈ X.simplices(2) ∧ " +
			"X.d(2, 0, X.s(1, 0, g)) = g ∧ " +
			"X.d(2, 1, X.s(1, 0, g)) = g ∧ " +
			"X.d(2, 2, X.s(1, 0, g)) = X.s(0, 0, X.d(1, 1, g))",
	},
		func(a *Argument, simplicial Fact, g *Expr[A], edge Fact) {
			zero, one, two := a.TermAs[Nat]("0"), a.TermAs[Nat]("1"), a.TermAs[Nat]("2")
			a.Show(
				"each clause is one axiom read at the degeneracy index 0 of the edge g",
				SplitConjAll(
					Case(
						"a degeneracy of the edge g is a 2-simplex",
						By(DegeneracyIn.Read(simplicial).At(one, zero, g), edge)),
					Case(
						"its face 0, the one at the degeneracy's index, is g",
						By(FaceDegeneracyEqual.Read(simplicial).At(one, zero, g), edge)),
					Case(
						"its face 1, the one just past the degeneracy's index, is g",
						By(FaceDegeneracyNext.Read(simplicial).At(one, zero, g), edge)),
					Case(
						"its face 2 passes above the degeneracy: the degenerate edge at the source of g",
						By(FaceDegeneracyAbove.Read(simplicial).At(zero, two, zero, g), edge)),
				))
		}),
})}

// ---------------------------------------------------------------------------
// Sub-simplicial sets
// ---------------------------------------------------------------------------

// SubSimplicialSetDef — `sub_simplicial_set(X, Y)`: a family of
// subsets of the X(n) closed under the faces and the degeneracies of
// X. Defined for any family and any maps; under the structure the text
// writes `sub_simplicial_set(Y)`.
var SubSimplicialSetDef = subSimplicialSetDefThm{family.Define(registry.DefEntry{
	Name:     "SubSimplicialSetDef",
	Key:      "prop_227d8fab00a7de8d",
	Const:    "sub_simplicial_set",
	Type:     "simplicial_ops(A) → (num → set(A)) → bool",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀Y:(num → set(A)). " +
			"    sub_simplicial_set(X, Y) ⇔ " +
			"    (∀n:num. Y(n) ⊆ X.simplices(n)) ∧ " +
			"    (∀n i:num. ∀x:A. x ∈ Y(n + 1) ∧ i ≤ n + 1 ⇒ X.d(n + 1, i, x) ∈ Y(n)) ∧ " +
			"    (∀n i:num. ∀x:A. x ∈ Y(n) ∧ i ≤ n ⇒ X.s(n, i, x) ∈ Y(n + 1))",
	},
	Deps: recordFields,
})}

// SubSimplicialSet — a sub-simplicial set is a simplicial set under the
// restricted maps. The target's predicate is unfolded into its eight
// conjuncts: the two closures are the hypothesis's own, and each
// identity holds at a simplex of Y because that simplex lies in X,
// where the axiom of X states it with the same d and s.
var SubSimplicialSet = subSimplicialSetThm{family.Add(registry.ProofEntry{
	Name: "SubSimplicialSet",
	Key:  "prop_cb9cebcfd3f9e8e6",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀Y:(num → set(A)).",
		Hypotheses: []string{
			"sub_simplicial_set(Y)",
		},
		Conclusion: "simplicial_set(restrict_simplicial_set(X, Y))",
	},
		func(a *Argument, simplicial Fact, _ *Arrow[Nat, Set[A]], sub Fact) {
			given := a.Conjuncts(
				a.Unfolded(sub, SubSimplicialSetDef),
				"Y lies in X dimension by dimension",
				"Y is closed under the faces",
				"and under the degeneracies")
			contained, faces, degeneracies := given[0], given[1], given[2]
			inX := a.Have(
				"so a simplex of Y is a simplex of X",
				"∀n:num. ∀x:A. x ∈ Y(n) ⇒ x ∈ X.simplices(n)",
				By(contained, set_basic.SubsetDef))
			a.Show(
				"Y with the restricted maps satisfies the eight axioms, each checked at a simplex of Y",
				Simp(Fwd(SimplicialSet)),
				SplitConjAll(
					Case(
						"a face of an (n + 1)-simplex of Y is an n-simplex of Y",
						By(faces)),
					Case(
						"a degeneracy of an n-simplex of Y is an (n + 1)-simplex of Y",
						By(degeneracies)),
					Case(
						"d_i d_j = d_{j−1} d_i for i < j",
						By(FaceFace.Read(simplicial), inX)),
					Case(
						"s_i s_j = s_{j+1} s_i for i ≤ j",
						By(DegeneracyDegeneracy.Read(simplicial), inX)),
					Case(
						"d_i s_j = s_{j−1} d_i for i < j",
						By(FaceDegeneracyBelow.Read(simplicial), inX)),
					Case(
						"d_i s_i is the identity",
						By(FaceDegeneracyEqual.Read(simplicial), inX)),
					Case(
						"so is d_{i+1} s_i",
						By(FaceDegeneracyNext.Read(simplicial), inX)),
					Case(
						"d_i s_j = s_j d_{i−1} for i > j + 1",
						By(FaceDegeneracyAbove.Read(simplicial), inX)),
				))
		}),
})}

// SubSimplicialSetRefl — every simplicial set is a sub-simplicial set
// of itself: each X(n) is contained in itself, and the two closures
// asked of X are the two closure axioms X satisfies.
var SubSimplicialSetRefl = subSimplicialSetReflThm{family.Add(registry.ProofEntry{
	Name: "SubSimplicialSetRefl",
	Key:  "prop_299df596bb28f485",
	Build: SimplicialSet.Law("sub_simplicial_set(X, X.simplices)",
		func(a *Argument, simplicial Fact) {
			a.Show(
				"X(n) ⊆ X(n), and a face or a degeneracy of a simplex of X is a simplex of X",
				Simp(Fwd(SubSimplicialSetDef)),
				SplitConjAll(
					Case(
						"each X(n) lies in itself",
						By(set_order.SubsetRefl)),
					Case(
						"a face of an (n + 1)-simplex of X is an n-simplex of X",
						By(FaceIn.Read(simplicial))),
					Case(
						"a degeneracy of an n-simplex of X is an (n + 1)-simplex of X",
						By(DegeneracyIn.Read(simplicial))),
				))
		}),
})}

// SubSimplicialSetInter — two sub-simplicial sets meet in one: Y(n) ∩ Z(n)
// lies in Y(n) and so in X(n), and a face or a degeneracy of a simplex
// of both lies in Y by Y's closure and in Z by Z's.
var SubSimplicialSetInter = subSimplicialSetInterThm{family.Add(registry.ProofEntry{
	Name: "SubSimplicialSetInter",
	Key:  "prop_c8cff28969236a06",
	Build: family.Theorem(Statement{
		Binders: "∀X:simplicial_ops(A). ∀Y Z:(num → set(A)).",
		Hypotheses: []string{
			"sub_simplicial_set(X, Y)",
			"sub_simplicial_set(X, Z)",
		},
		Conclusion: "sub_simplicial_set(X, λn:num. Y(n) ∩ Z(n))",
	},
		func(
			a *Argument,
			X *Expr[SimplicialOps[A]],
			Y *Arrow[Nat, Set[A]],
			Z *Arrow[Nat, Set[A]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"Y is a sub-simplicial set",
				"and so is Z")
			ofY := a.Conjuncts(
				a.Unfolded(given[0], SubSimplicialSetDef),
				"Y lies in X dimension by dimension",
				"Y is closed under the faces",
				"and under the degeneracies")
			ofZ := a.Conjuncts(
				a.Unfolded(given[1], SubSimplicialSetDef),
				"Z lies in X dimension by dimension",
				"Z is closed under the faces",
				"and under the degeneracies")
			yContained, yFaces, yDegeneracies := ofY[0], ofY[1], ofY[2]
			zFaces, zDegeneracies := ofZ[1], ofZ[2]
			a.Show(
				"the intersection is checked clause by clause, a simplex of it being a simplex of both",
				Simp(Fwd(SubSimplicialSetDef)),
				SplitConjAll(
					Case(
						"Y(n) ∩ Z(n) lies in Y(n), hence in X(n)",
						BySets(yContained)),
					Case(
						"a face of a simplex of both is a simplex of both",
						BySets(yFaces, zFaces)),
					Case(
						"so is a degeneracy",
						BySets(yDegeneracies, zDegeneracies)),
				))
		}),
})}

// ---------------------------------------------------------------------------
// Simplicial maps
// ---------------------------------------------------------------------------

// SimplicialMap — `simplicial_map(X, Y, F)`: a map
// `F : num → A → B` of simplicial sets on two types, F(n) carrying X(n)
// into Y(n) and commuting with every face and every degeneracy. The two
// structures are its first conjuncts, as the groups are a group
// homomorphism's; the components are implicit, so under a law here the
// text writes `simplicial_map(X, Y, F)`.
var SimplicialMap = simplicialMapThm{family.DefineStructure(registry.DefEntry{
	Name:     "SimplicialMap",
	Key:      "prop_f88aa943ddacabd5",
	Const:    "simplicial_map",
	Type:     "simplicial_ops(A) → simplicial_ops(B) → (num → A → B) → bool",
	Implicit: []string{"X", "Y"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). ∀F:(num → A → B). " +
			"    simplicial_map(X, Y, F) ⇔ " +
			"    simplicial_set(X) ∧ " +
			"    simplicial_set(Y) ∧ " +
			"    (∀n:num. ∀x:A. x ∈ X.simplices(n) ⇒ F(n, x) ∈ Y.simplices(n)) ∧ " +
			"    (∀n i:num. ∀x:A. " +
			"        x ∈ X.simplices(n + 1) ∧ i ≤ n + 1 ⇒ " +
			"        F(n, X.d(n + 1, i, x)) = Y.d(n + 1, i, F(n + 1, x))) ∧ " +
			"    (∀n i:num. ∀x:A. x ∈ X.simplices(n) ∧ i ≤ n ⇒ F(n + 1, X.s(n, i, x)) = Y.s(n, i, F(n, x)))",
	},
	Deps: []registry.EntryLike{SimplicialSet},
})}

// MapSource — the source of a simplicial map is a simplicial set.
var MapSource = mapSourceThm{family.Add(registry.ProofEntry{
	Name:  "MapSource",
	Key:   "prop_9816e7a379004275",
	Build: SimplicialMap.Axiom("simplicial_set(X)"),
})}

// MapTarget — and so is its target.
var MapTarget = mapTargetThm{family.Add(registry.ProofEntry{
	Name:  "MapTarget",
	Key:   "prop_b60b6290d1141f37",
	Build: SimplicialMap.Axiom("simplicial_set(Y)"),
})}

// MapIn — F(n) carries X(n) into Y(n).
var MapIn = mapInThm{family.Add(registry.ProofEntry{
	Name: "MapIn",
	Key:  "prop_fc0a36168adde114",
	Build: SimplicialMap.Axiom(Statement{
		Binders: "∀n:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n)",
		},
		Conclusion: "F(n, x) ∈ Y.simplices(n)",
	}),
})}

// MapFace — F commutes with the faces.
var MapFace = mapFaceThm{family.Add(registry.ProofEntry{
	Name: "MapFace",
	Key:  "prop_27bba45a422e7ce3",
	Build: SimplicialMap.Axiom(Statement{
		Binders: "∀n i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n + 1)",
			"i ≤ n + 1",
		},
		Conclusion: "F(n, X.d(n + 1, i, x)) = Y.d(n + 1, i, F(n + 1, x))",
	}),
})}

// MapDegeneracy — and with the degeneracies.
var MapDegeneracy = mapDegeneracyThm{family.Add(registry.ProofEntry{
	Name: "MapDegeneracy",
	Key:  "prop_c92389a4757f12da",
	Build: SimplicialMap.Axiom(Statement{
		Binders: "∀n i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n)",
			"i ≤ n",
		},
		Conclusion: "F(n + 1, X.s(n, i, x)) = Y.s(n, i, F(n, x))",
	}),
})}

// MapIdentity — the identity is a simplicial map: its source and its
// target are the one simplicial set in hand, a simplex maps to itself,
// and the map commutes with every face and every degeneracy because
// applying it changes nothing.
var MapIdentity = mapIdentityThm{family.Add(registry.ProofEntry{
	Name: "MapIdentity",
	Key:  "prop_c8885148fc475843",
	Build: SimplicialSet.Law("simplicial_map(X, X, λn:num. λx:A. x)",
		func(a *Argument, simplicial Fact) {
			// The simplicial set in hand, by its components.
			X := a.TermAs[SimplicialOps[A]]("X")
			carries := a.Have(
				"a simplex maps to itself, so it stays in X(n)",
				"∀n:num. ∀x:A. x ∈ X.simplices(n) ⇒ x ∈ X.simplices(n)",
				Basic())
			faces := a.Have(
				"the identity commutes with every face",
				"∀n i:num. ∀x:A. x ∈ X.simplices(n + 1) ∧ i ≤ n + 1 ⇒ X.d(n + 1, i, x) = X.d(n + 1, i, x)",
				Basic())
			degeneracies := a.Have(
				"and with every degeneracy",
				"∀n i:num. ∀x:A. x ∈ X.simplices(n) ∧ i ≤ n ⇒ X.s(n, i, x) = X.s(n, i, x)",
				Basic())
			a.Show(
				"both structures of the map are the hypothesis, and its three clauses are in hand",
				By(simplicial, carries, faces, degeneracies, At(SimplicialMap, X, X, a.Term("λn:num. λx:A. x"))))
		}),
})}

// MapCompose — simplicial maps compose. The composite's source is the
// source of F and its target the target of G; a simplex of X goes into Y
// under F and on into Z under G; and the composite commutes with a face,
// or a degeneracy, because F does and then G does at the image simplex,
// which F places in Y.
var MapCompose = mapComposeThm{family.Add(registry.ProofEntry{
	Name: "MapCompose",
	Key:  "prop_265e819eb925f484",
	Build: family.Theorem(Statement{
		Binders: "∀X:simplicial_ops(A). " +
			"∀Y:simplicial_ops(B). " +
			"∀Z:simplicial_ops(C). " +
			"∀F:(num → A → B). " +
			"∀G:(num → B → C).",
		Hypotheses: []string{
			"simplicial_map(X, Y, F)",
			"simplicial_map(Y, Z, G)",
		},
		Conclusion: "simplicial_map(X, Z, λn:num. λx:A. G(n, F(n, x)))",
	},
		func(
			a *Argument,
			X *Expr[SimplicialOps[A]],
			Y *Expr[SimplicialOps[B]],
			Z *Expr[SimplicialOps[C]],
			F *Arrow2[Nat, A, B],
			G *Arrow2[Nat, B, C],
			maps Fact,
		) {
			given := a.Conjuncts(
				maps,
				"F is a simplicial map from X to Y",
				"G is a simplicial map from Y to Z")
			first, second := given[0], given[1]
			source := a.Have(
				"the composite's source is the source of F",
				"simplicial_set(X)",
				By(MapSource.Read(first)))
			target := a.Have(
				"and its target is the target of G",
				"simplicial_set(Z)",
				By(MapTarget.Read(second)))
			carries := a.Have(
				"a simplex of X goes into Y under F and on into Z under G",
				"∀n:num. ∀x:A. x ∈ X.simplices(n) ⇒ G(n, F(n, x)) ∈ Z.simplices(n)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					b.FixAs[A]()
					member := b.Assume()
					b.Show(
						"F(n, x) lies in Y(n), and G carries it into Z(n)",
						By(MapIn.Read(second), MapIn.Read(first), member))
				}))
			faces := a.Have(
				"the composite commutes with the faces: F does, then G does at F(n + 1, x), a simplex of Y",
				Statement{
					Binders: "∀n i:num. ∀x:A.",
					Hypotheses: []string{
						"x ∈ X.simplices(n + 1)",
						"i ≤ n + 1",
					},
					Conclusion: "G(n, F(n, X.d(n + 1, i, x))) = Z.d(n + 1, i, G(n + 1, F(n + 1, x)))",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					i := b.FixAs[Nat]()
					x := b.FixAs[A]()
					bounds := b.Assume()
					above := b.TermAs[Nat]("n + 1")
					b.Show(
						"the face passes F, then G",
						CalcEq(
							Leg(
								b.TermAs[C]("G(n, Y.d(n + 1, i, F(n + 1, x)))"),
								"F commutes with the i-th face of x",
								By(MapFace.Read(first).At(n, i, x), bounds)),
							FinalLeg(
								"G commutes with the i-th face of F(n + 1, x), which lies in Y(n + 1)",
								By(MapFace.Read(second).At(n, i, F.Apply(above, x)), MapIn.Read(first).At(above, x), bounds)),
						))
				}))
			degeneracies := a.Have(
				"and with the degeneracies: F does, then G does at F(n, x), a simplex of Y",
				Statement{
					Binders: "∀n i:num. ∀x:A.",
					Hypotheses: []string{
						"x ∈ X.simplices(n)",
						"i ≤ n",
					},
					Conclusion: "G(n + 1, F(n + 1, X.s(n, i, x))) = Z.s(n, i, G(n, F(n, x)))",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					i := b.FixAs[Nat]()
					x := b.FixAs[A]()
					bounds := b.Assume()
					b.Show(
						"the degeneracy passes F, then G",
						CalcEq(
							Leg(
								b.TermAs[C]("G(n + 1, Y.s(n, i, F(n, x)))"),
								"F commutes with the i-th degeneracy of x",
								By(MapDegeneracy.Read(first).At(n, i, x), bounds)),
							FinalLeg(
								"G commutes with the i-th degeneracy of F(n, x), which lies in Y(n)",
								By(MapDegeneracy.Read(second).At(n, i, F.Apply(n, x)), MapIn.Read(first).At(n, x), bounds)),
						))
				}))
			a.Show(
				"the five clauses of a simplicial map are in hand",
				By(
					source,
					target,
					carries,
					faces,
					degeneracies,
					At(SimplicialMap, X, Z, a.Term("λn:num. λx:A. G(n, F(n, x))"))))
		}),
})}

// MapRestrict — compose F with the inclusion of Z into its source.
var MapRestrict = mapRestrictThm{family.Add(registry.ProofEntry{
	Name: "MapRestrict",
	Key:  "prop_eb649ee6ad6c9e41",
	Build: family.Theorem(Statement{
		Binders: "∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). ∀F:(num → A → B). ∀Z:(num → set(A)).",
		Hypotheses: []string{
			"simplicial_map(X, Y, F)",
			"sub_simplicial_set(X, Z)",
		},
		Conclusion: "simplicial_map(restrict_simplicial_set(X, Z), Y, F)",
	},
		func(
			a *Argument,
			X *Expr[SimplicialOps[A]],
			Y *Expr[SimplicialOps[B]],
			F *Arrow2[Nat, A, B],
			Z *Arrow[Nat, Set[A]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"F is a simplicial map from X to Y",
				"Z is a sub-simplicial set of X")
			mapping, sub := given[0], given[1]
			source := MapSource.Read(mapping)
			inclusion := a.Have(
				"Z includes into the source of F",
				"simplicial_map(restrict_simplicial_set(X, Z), X, λn:num. λx:A. x)",
				By(sub, MapInclusion.Read(source).At(Z)))
			identity := a.TermAs[Fun2[Nat, A, A]]("λn:num. λx:A. x")
			a.Show(
				"compose F with the inclusion of Z",
				By(inclusion, mapping, At(MapCompose, a.Term("restrict_simplicial_set(X, Z)"), X, Y, identity, F)))
		}),
})}

// MapInclusion — the inclusion of a sub-simplicial set is a simplicial
// map: its source is a simplicial set because a sub-simplicial set is
// one, its target is the simplicial set in hand, a simplex of Y is a
// simplex of X because Y(n) ⊆ X(n), and the inclusion commutes with
// every face and every degeneracy because applying it changes nothing.
var MapInclusion = mapInclusionThm{family.Add(registry.ProofEntry{
	Name: "MapInclusion",
	Key:  "prop_e129be35325ea1ce",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀Y:(num → set(A)).",
		Hypotheses: []string{
			"sub_simplicial_set(Y)",
		},
		Conclusion: "simplicial_map(restrict_simplicial_set(X, Y), X, λn:num. λx:A. x)",
	},
		func(a *Argument, simplicial Fact, Y *Arrow[Nat, Set[A]], sub Fact) {
			// The simplicial set in hand, by its components.
			X := a.TermAs[SimplicialOps[A]]("X")
			source := a.Have(
				"Y with the restricted maps is a simplicial set",
				"simplicial_set(restrict_simplicial_set(X, Y))",
				By(SubSimplicialSet.Read(simplicial).At(Y), sub))
			carries := a.Have(
				"a simplex of Y is a simplex of X, since Y(n) ⊆ X(n)",
				"∀n:num. ∀x:A. x ∈ Y(n) ⇒ x ∈ X.simplices(n)",
				By(sub, At(SubSimplicialSetDef, X, Y), set_basic.SubsetDef))
			faces := a.Have(
				"the inclusion commutes with every face",
				"∀n i:num. ∀x:A. x ∈ Y(n + 1) ∧ i ≤ n + 1 ⇒ X.d(n + 1, i, x) = X.d(n + 1, i, x)",
				Basic())
			degeneracies := a.Have(
				"and with every degeneracy",
				"∀n i:num. ∀x:A. x ∈ Y(n) ∧ i ≤ n ⇒ X.s(n, i, x) = X.s(n, i, x)",
				Basic())
			a.Show(
				"the source is Y, the target is the hypothesis, and the three clauses are in hand",
				By(
					source,
					simplicial,
					carries,
					faces,
					degeneracies,
					At(SimplicialMap, a.Term("restrict_simplicial_set(X, Y)"), X, a.Term("λn:num. λx:A. x"))))
		}),
})}

// MapPreimage — a simplex of the preimage is a simplex of X that F
// carries into Z. Its faces and degeneracies stay in X, and F carries
// each to the same face or degeneracy of its image, which Z's closure
// keeps in Z.
var MapPreimage = mapPreimageThm{family.Add(registry.ProofEntry{
	Name: "MapPreimage",
	Key:  "prop_d5bc42f349497fac",
	Build: SimplicialMap.Law(Statement{
		Binders: "∀Z:(num → set(B)).",
		Hypotheses: []string{
			"sub_simplicial_set(Y, Z)",
		},
		Conclusion: "sub_simplicial_set(X, λn:num. preimage_on(X.simplices(n), F(n), Z(n)))",
	},
		func(a *Argument, simplicialMap Fact, _ *Arrow[Nat, Set[B]], sub Fact) {
			source := MapSource.Read(simplicialMap)
			ofZ := a.Conjuncts(
				a.Unfolded(sub, SubSimplicialSetDef),
				"Z lies in Y dimension by dimension",
				"Z is closed under the faces of Y",
				"and under its degeneracies")
			zFaces, zDegeneracies := ofZ[1], ofZ[2]
			a.Show(
				"the preimage is checked clause by clause",
				Simp(Fwd(SubSimplicialSetDef)),
				SplitConjAll(
					Case(
						"a simplex of the preimage is a simplex of X",
						BySets()),
					Case(
						"a face of a simplex of the preimage lies in the preimage",
						Derive(func(b *Argument) {
							n, i := b.FixAs[Nat](), b.FixAs[Nat]()
							x := b.FixAs[A]()
							given := b.Assume()
							image := b.TermAs[B]("F(n + 1, x)")
							faceIn := b.Have(
								"the i-th face of x is an n-simplex of X",
								"X.d(n + 1, i, x) ∈ X.simplices(n)",
								BySets(FaceIn.Read(source).At(n, i, x), given))
							faceInZ := b.Have(
								"F carries it to the i-th face of F(n + 1, x), which Z's closure keeps in Z(n)",
								"F(n, X.d(n + 1, i, x)) ∈ Z(n)",
								BySets(MapFace.Read(simplicialMap).At(n, i, x), zFaces.At(n, i, image), given))
							b.Show(
								"so the face lies in the preimage",
								BySets(faceIn, faceInZ))
						})),
					Case(
						"a degeneracy of a simplex of the preimage lies in the preimage",
						Derive(func(b *Argument) {
							n, i := b.FixAs[Nat](), b.FixAs[Nat]()
							x := b.FixAs[A]()
							given := b.Assume()
							image := b.TermAs[B]("F(n, x)")
							degeneracyIn := b.Have(
								"the i-th degeneracy of x is an (n + 1)-simplex of X",
								"X.s(n, i, x) ∈ X.simplices(n + 1)",
								BySets(DegeneracyIn.Read(source).At(n, i, x), given))
							degeneracyInZ := b.Have(
								"F carries it to the i-th degeneracy of F(n, x), which Z's closure keeps in Z(n + 1)",
								"F(n + 1, X.s(n, i, x)) ∈ Z(n + 1)",
								BySets(MapDegeneracy.Read(simplicialMap).At(n, i, x), zDegeneracies.At(n, i, image), given))
							b.Show(
								"so the degeneracy lies in the preimage",
								BySets(degeneracyIn, degeneracyInZ))
						})),
				))
		}),
})}

// SimplicialIsomorphismDef — `simplicial_isomorphism(X, Y, F)`:
// a simplicial map that is a bijection in every dimension, between the
// sets: injective on X(n), and X(n) onto Y(n).
var SimplicialIsomorphismDef = simplicialIsomorphismDefThm{family.Define(registry.DefEntry{
	Name:     "SimplicialIsomorphismDef",
	Key:      "prop_de1fc549e05f6802",
	Const:    "simplicial_isomorphism",
	Type:     "simplicial_ops(A) → simplicial_ops(B) → (num → A → B) → bool",
	Implicit: []string{"X", "Y"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). ∀F:(num → A → B). " +
			"    simplicial_isomorphism(X, Y, F) ⇔ " +
			"    simplicial_map(X, Y, F) ∧ " +
			"    (∀n:num. injective_on(X.simplices(n), F(n))) ∧ " +
			"    (∀n:num. image(F(n), X.simplices(n)) = Y.simplices(n))",
	},
	Deps: []registry.EntryLike{SimplicialMap},
})}

// IsomorphismInverse — the degreewise inverse commutes with faces and
// degeneracies by the two inverse identities.
var IsomorphismInverse = isomorphismInverseThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismInverse",
	Key:  "prop_685449d3ea52c5c0",
	Build: family.Theorem(Statement{
		Binders: "∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). ∀F:(num → A → B).",
		Hypotheses: []string{
			"simplicial_isomorphism(F)",
		},
		Conclusion: "simplicial_map(Y, X, λn:num. inverse_on(X.simplices(n), F(n))) ∧ " +
			"(∀n:num. ∀x:A. x ∈ X.simplices(n) ⇒ inverse_on(X.simplices(n), F(n), F(n, x)) = x) ∧ " +
			"(∀n:num. ∀y:B. y ∈ Y.simplices(n) ⇒ F(n, inverse_on(X.simplices(n), F(n), y)) = y)",
	},
		func(
			a *Argument,
			X *Expr[SimplicialOps[A]],
			Y *Expr[SimplicialOps[B]],
			F *Arrow[Nat, Fun[A, B]],
			iso Fact,
		) {
			// The definition of a simplicial isomorphism, read at F and its two simplicial sets.
			isomorphism := At(SimplicialIsomorphismDef, X, Y, F)
			morphism := a.Have(
				"the isomorphism is a simplicial map",
				"simplicial_map(X, Y, F)",
				By(iso, isomorphism))
			bijective := a.Have(
				"each degree map is a bijection",
				"∀n:num. injective_on(X.simplices(n), F(n)) ∧ image(F(n), X.simplices(n)) = Y.simplices(n)",
				By(iso, isomorphism))
			structures := a.Have(
				"source and target are simplicial sets",
				"simplicial_set(X) ∧ simplicial_set(Y)",
				By(MapSource.Read(morphism), MapTarget.Read(morphism)))
			rightInverse := a.Have(
				"the inverse takes target simplices to their preimages",
				Statement{
					Binders: "∀n:num. ∀y:B.",
					Hypotheses: []string{
						"y ∈ Y.simplices(n)",
					},
					Conclusion: "inverse_on(X.simplices(n), F(n), y) ∈ X.simplices(n) ∧ " +
						"F(n, inverse_on(X.simplices(n), F(n), y)) = y",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					y := b.FixAs[B]("y")
					member := b.Assume()
					b.Show(
						"the chosen preimage lies in its degree and maps to y",
						By(
							member,
							bijective.At(n),
							functions.InverseOnIn.At(b.TermAs[Set[A]]("X.simplices(n)"), F.Apply(n), y),
							functions.InverseOnRight.At(b.TermAs[Set[A]]("X.simplices(n)"), F.Apply(n), y)))
				}))
			leftInverse := a.Have(
				"the inverse recovers every source simplex",
				"∀n:num. ∀x:A. x ∈ X.simplices(n) ⇒ inverse_on(X.simplices(n), F(n), F(n, x)) = x",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					x := b.FixAs[A]("x")
					member := b.Assume()
					b.Show(
						"injectivity identifies the preimage",
						By(
							member,
							bijective.At(n),
							functions.InverseOnLeft.At(b.TermAs[Set[A]]("X.simplices(n)"), F.Apply(n), x)))
				}))
			faces := a.Have(
				"the inverse commutes with faces",
				Statement{
					Binders: "∀n i:num. ∀y:B.",
					Hypotheses: []string{
						"y ∈ Y.simplices(n + 1)",
						"i ≤ n + 1",
					},
					Conclusion: "inverse_on(X.simplices(n), F(n), Y.d(n + 1, i, y)) = " +
						"X.d(n + 1, i, inverse_on(X.simplices(n + 1), F(n + 1), y))",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					i := b.FixAs[Nat]("i")
					y := b.FixAs[B]("y")
					faceDomain := b.Assume()
					next := b.TermAs[Nat]("n + 1")
					preimage := b.TermAs[A]("inverse_on(X.simplices(n + 1), F(n + 1), y)")
					face := b.TermAs[A]("X.d(n + 1, i, inverse_on(X.simplices(n + 1), F(n + 1), y))")
					lift := b.Have(
						"lift the target simplex to its source degree",
						"inverse_on(X.simplices(n + 1), F(n + 1), y) ∈ X.simplices(n + 1) ∧ "+
							"F(n + 1, inverse_on(X.simplices(n + 1), F(n + 1), y)) = y",
						By(faceDomain, rightInverse.At(next, y)))
					faceIn := b.Have(
						"the lifted face belongs to the source",
						"X.d(n + 1, i, inverse_on(X.simplices(n + 1), F(n + 1), y)) ∈ X.simplices(n)",
						By(lift, faceDomain, FaceIn.Read(MapSource.Read(morphism)).At(n, i, preimage)))
					faceImage := b.Have(
						"the original map sends the lifted face to the target face",
						"F(n, X.d(n + 1, i, inverse_on(X.simplices(n + 1), F(n + 1), y))) = Y.d(n + 1, i, y)",
						By(lift, faceDomain, MapFace.Read(morphism).At(n, i, preimage)))
					b.Show(
						"the left inverse identifies the lifted face",
						By(faceImage, faceIn, leftInverse.At(n, face)))
				}))
			degeneracies := a.Have(
				"the inverse commutes with degeneracies",
				Statement{
					Binders: "∀n i:num. ∀y:B.",
					Hypotheses: []string{
						"y ∈ Y.simplices(n)",
						"i ≤ n",
					},
					Conclusion: "inverse_on(X.simplices(n + 1), F(n + 1), Y.s(n, i, y)) = " +
						"X.s(n, i, inverse_on(X.simplices(n), F(n), y))",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					i := b.FixAs[Nat]("i")
					y := b.FixAs[B]("y")
					degeneracyDomain := b.Assume()
					next := b.TermAs[Nat]("n + 1")
					preimage := b.TermAs[A]("inverse_on(X.simplices(n), F(n), y)")
					degeneracy := b.TermAs[A]("X.s(n, i, inverse_on(X.simplices(n), F(n), y))")
					lift := b.Have(
						"lift the target simplex to its source degree",
						"inverse_on(X.simplices(n), F(n), y) ∈ X.simplices(n) ∧ "+
							"F(n, inverse_on(X.simplices(n), F(n), y)) = y",
						By(degeneracyDomain, rightInverse.At(n, y)))
					degeneracyIn := b.Have(
						"the lifted degeneracy belongs to the source",
						"X.s(n, i, inverse_on(X.simplices(n), F(n), y)) ∈ X.simplices(n + 1)",
						By(lift, degeneracyDomain, DegeneracyIn.Read(MapSource.Read(morphism)).At(n, i, preimage)))
					degeneracyImage := b.Have(
						"the original map sends the lifted degeneracy to the target degeneracy",
						"F(n + 1, X.s(n, i, inverse_on(X.simplices(n), F(n), y))) = Y.s(n, i, y)",
						By(lift, degeneracyDomain, MapDegeneracy.Read(morphism).At(n, i, preimage)))
					b.Show(
						"the left inverse identifies the lifted degeneracy",
						By(degeneracyImage, degeneracyIn, leftInverse.At(next, degeneracy)))
				}))
			inverseMap := a.Have(
				"the degreewise inverse is a simplicial map",
				"simplicial_map(Y, X, λn:num. inverse_on(X.simplices(n), F(n)))",
				By(
					rightInverse,
					degeneracies,
					faces,
					structures,
					At(SimplicialMap, Y, X, a.Term("λn:num. inverse_on(X.simplices(n), F(n))"))))
			a.Show(
				"the inverse map satisfies both inverse identities",
				By(leftInverse, rightInverse, inverseMap))
		}),
})}

// ---------------------------------------------------------------------------
// The base simplex at a vertex, and the one-point simplicial set
// ---------------------------------------------------------------------------

// BaseSimplexDef — `base_simplex(s, x₀, n)`: the totally degenerate
// n-simplex at the vertex x₀, the vertex itself at n = 0 and the 0-th
// degeneracy of the one below at n + 1. Under the structure the text
// writes `base_simplex(x₀, n)`.
var BaseSimplexDef = baseSimplexDefThm{family.Define(registry.DefEntry{
	Name:     "BaseSimplexDef",
	Key:      "prop_2aa17e9338ceff0a",
	Const:    "base_simplex",
	Type:     "(num → num → A → A) → A → num → A",
	Implicit: []string{"s"},
	Equations: []string{
		"∀s:(num → num → A → A). ∀x₀:A. base_simplex(s, x₀, 0) = x₀",
		"∀s:(num → num → A → A). ∀x₀:A. ∀n:num. " +
			"    base_simplex(s, x₀, suc(n)) = s(n, 0, base_simplex(s, x₀, n))",
	},
})}

// BaseSimplexIn — the base simplex at a vertex of X is a simplex of X:
// by induction on the dimension, it is the vertex at 0, and at n + 1 the
// 0-th degeneracy of the n-simplex below, which the degeneracy closure
// places one dimension up.
var BaseSimplexIn = baseSimplexInThm{family.Add(registry.ProofEntry{
	Name: "BaseSimplexIn",
	Key:  "prop_dc94c95bb280838d",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀x₀:A. ∀n:num.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
		},
		Conclusion: "base_simplex(x₀, n) ∈ X.simplices(n)",
	},
		func(a *Argument, simplicial Fact, _ *Expr[A], n *Expr[Nat], vertex Fact) {
			a.Induct(n)
			a.Base(
				"the base simplex at 0 is the vertex",
				Simp(Fwd(BaseSimplexDef)),
				By(vertex))
			a.Step(
				"the next one is the 0-th degeneracy of an n-simplex",
				func(b *Argument, below Fact) {
					simplex := b.TermAs[A]("base_simplex(x₀, n)")
					b.Show(
						"which the degeneracy closure places in X(n + 1)",
						Simp(Fwd(BaseSimplexDef), Fwd(nat_arith.Add1)),
						By(
							DegeneracyIn.Read(simplicial).At(n, b.TermAs[Nat]("0"), simplex),
							below,
							nat_order.ZeroLessEq.At(n)))
				})
		}),
})}

// BaseSimplexSucc — the definition's recursion clause at suc(n), with
// suc(n) written n + 1.
var BaseSimplexSucc = baseSimplexSuccThm{family.Add(registry.ProofEntry{
	Name: "BaseSimplexSucc",
	Key:  "prop_bc897b302d525a69",
	Build: family.Theorem("∀s:(num → num → A → A). ∀x₀:A. ∀n:num. "+
		"    base_simplex(s, x₀, n + 1) = s(n, 0, base_simplex(s, x₀, n))",
		func(a *Argument) {
			a.Show(
				"with n + 1 read as suc(n), the recursion clause makes the two sides one term",
				Simp(Rev(nat_arith.Add1), Fwd(BaseSimplexDef)),
				Basic())
		}),
})}

// BaseSimplexFixedPoint — the base simplex at a point every 0-th degeneracy
// fixes is that point, in every dimension.
var BaseSimplexFixedPoint = baseSimplexFixedPointThm{family.Add(registry.ProofEntry{
	Name: "BaseSimplexFixedPoint",
	Key:  "prop_c7f05c564b41801e",
	Reading: "Only the 0-th degeneracies at the point are read: the base simplex is " +
		"built by them alone, and no face, no closure and no simplicial identity enters.",
	Deps: []registry.EntryLike{BaseSimplexDef, BaseSimplexSucc},
	Build: family.Card(Statement{
		Binders: "∀s:(num → num → A → A). ∀x₀:A. ∀n:num.",
		Hypotheses: []string{
			"∀m:num. s(m, 0, x₀) = x₀",
		},
		Conclusion: "base_simplex(s, x₀, n) = x₀",
	},
		"induction on n: base_simplex(s, x₀, 0) is x₀ (BaseSimplexDef), and base_simplex(s, "+
			"x₀, n + 1) = s(n, 0, base_simplex(s, x₀, n)) (BaseSimplexSucc) = s(n, 0, x₀) = x₀"),
})}

// BaseSimplexFace — express the base simplex as the i-th degeneracy
// when i ≤ n, and cancel it with d_i s_i. The remaining face has index
// n + 1: express the same simplex as the last degeneracy and cancel
// with d_{n+1} s_n.
var BaseSimplexFace = baseSimplexFaceThm{family.Add(registry.ProofEntry{
	Name: "BaseSimplexFace",
	Key:  "prop_b30bbf93919c8d80",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀x₀:A. ∀n i:num.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"i ≤ n + 1",
		},
		Conclusion: "X.d(n + 1, i, base_simplex(x₀, n + 1)) = base_simplex(x₀, n)",
	},
		func(a *Argument, simplicial Fact, x0 *Expr[A], n, i *Expr[Nat], given Fact) {
			below := a.TermAs[A]("base_simplex(x₀, n)")
			inX := a.Have(
				"the simplex below lies in X(n)",
				"base_simplex(x₀, n) ∈ X.simplices(n)",
				By(given, BaseSimplexIn.Read(simplicial).At(x0, n)))
			a.Cases(a.Term("i ≤ n"))
			a.When(
				"face i cancels the i-th degeneracy when i ≤ n",
				func(b *Argument, within Fact) {
					degenerate := b.Have(
						"the base simplex is the i-th degeneracy of the one below",
						"base_simplex(x₀, n + 1) = X.s(n, i, base_simplex(x₀, n))",
						By(within, given, BaseSimplexDegeneracy.Read(simplicial).At(x0, n, i)))
					b.Show(
						"d_i s_i returns the simplex below",
						degenerate.Rw(),
						By(within, inX, FaceDegeneracyEqual.Read(simplicial).At(n, i, below)))
				})
			a.Otherwise(
				"the last face cancels the last degeneracy",
				func(b *Argument, past Fact) {
					last := b.Have(
						"i ≤ n + 1 and i > n force the last face",
						"i = n + 1",
						ByArith(past, given))
					degenerate := b.Have(
						"the base simplex is the last degeneracy of the one below",
						"base_simplex(x₀, n + 1) = X.s(n, n, base_simplex(x₀, n))",
						ByArith(given, BaseSimplexDegeneracy.Read(simplicial).At(x0, n, n)))
					b.Show(
						"d_{n+1} s_n returns the simplex below",
						last.Rw(),
						degenerate.Rw(),
						ByArith(inX, FaceDegeneracyNext.Read(simplicial).At(n, n, below)))
				})
		}),
})}

// BaseSimplexDegeneracy — every degeneracy of the base simplex is the
// base simplex one dimension up. The 0-th is the definition, in every
// dimension. The higher ones go by induction on the dimension: writing
// i = j + 1, the degeneracy passes the 0-th one, s_{j+1} s_0 = s_0 s_j,
// the hypothesis at j turns s_j of the base simplex into the one above
// it, and s_0 of that is the base simplex again.
var BaseSimplexDegeneracy = baseSimplexDegeneracyThm{family.Add(registry.ProofEntry{
	Name: "BaseSimplexDegeneracy",
	Key:  "prop_ab46b50aac20a893",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀x₀:A. ∀n i:num.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"i ≤ n",
		},
		Conclusion: "X.s(n, i, base_simplex(x₀, n)) = base_simplex(x₀, n + 1)",
	},
		func(a *Argument, simplicial Fact, x0 *Expr[A]) {
			zero, s := a.TermAs[Nat]("0"), a.TermAs[Fun3[Nat, Nat, A, A]]("X.s")
			// The induction is on n with i still bound: the step reads the
			// hypothesis at j, where i = j + 1.
			a.Induct("n")
			a.Base(
				"at dimension 0 the only degeneracy is the 0-th",
				func(b *Argument) {
					b.FixAs[Nat]()
					given := b.Assume()
					atZero := b.Have(
						"i ≤ 0 leaves i = 0",
						"i = 0",
						ByArith(given))
					b.Show(
						"s_0 of the vertex is the base simplex at 1",
						atZero.Rw(),
						By(BaseSimplexSucc.At(s, x0, zero)))
				})
			a.Step(
				"a degeneracy of the base simplex at n + 1 is the 0-th or passes it",
				func(b *Argument, ih Fact) {
					b.FixAs[Nat]()
					given := b.Conjuncts(
						b.Assume(),
						"x₀ is a vertex",
						"i is at most n + 1")
					vertex, within := given[0], given[1]
					b.Cases(b.Term("i = 0"))
					b.When(
						"the 0-th degeneracy is the definition",
						func(c *Argument, atZero Fact) {
							c.Show(
								"read at the dimension suc(n)",
								atZero.Rw(),
								By(BaseSimplexSucc.At(s, x0, c.TermAs[Nat]("suc(n)"))))
						})
					b.Otherwise(
						"a higher degeneracy passes the 0-th and meets the hypothesis one index down",
						func(c *Argument, nonzero Fact) {
							j, next := c.ObtainAs[Nat](
								"i is j + 1 for some j",
								"∃j:num. i = j + 1",
								Derive(func(d *Argument) {
									d.Take(d.TermAs[Nat]("i - 1"))
									d.Show(
										"i is at least 1",
										ByArith(nonzero))
								}))
							bound := c.Have(
								"j + 1 ≤ n + 1 leaves j ≤ n",
								"j ≤ n",
								ByArith(within, next))
							n, below := c.TermAs[Nat]("n"), c.TermAs[A]("base_simplex(x₀, n)")
							c.Show(
								"with i = j + 1 and suc(n) written n + 1, the degeneracy runs through s_0 and the hypothesis at j",
								next.Rw(),
								Simp(Fwd(nat_arith.Add1)),
								CalcEq(
									Leg(
										c.TermAs[A]("X.s(n + 1, j + 1, X.s(n, 0, base_simplex(x₀, n)))"),
										"the base simplex at n + 1 is s_0 of the one at n",
										By(Normalized, BaseSimplexSucc.At(s, x0, n))),
									Leg(
										c.TermAs[A]("X.s(n + 1, 0, X.s(n, j, base_simplex(x₀, n)))"),
										"s_{j+1} s_0 = s_0 s_j, as 0 ≤ j ≤ n",
										By(
											DegeneracyDegeneracy.Read(simplicial).At(n, zero, j, below),
											BaseSimplexIn.Read(simplicial).At(x0, n),
											vertex,
											nat_order.ZeroLessEq.At(j),
											bound)),
									Leg(
										c.TermAs[A]("X.s(n + 1, 0, base_simplex(x₀, n + 1))"),
										"the hypothesis at j ≤ n",
										By(Normalized, ih.At(j), vertex, bound)),
									FinalLeg(
										"which is the base simplex at n + 2",
										By(BaseSimplexSucc.At(s, x0, c.TermAs[Nat]("n + 1")))),
								))
						})
				})
		}),
})}

// BaseSimplexFaceInherited — where the face i of an (n+2)-simplex v is the
// base simplex, so is the face i of every face of v above i: by the face
// identity d_i d_k = d_{k−1} d_i it is a face of the base simplex at n + 1,
// which is the base simplex one dimension down (BaseSimplexFace).
var BaseSimplexFaceInherited = baseSimplexFaceInheritedThm{family.Add(registry.ProofEntry{
	Name: "BaseSimplexFaceInherited",
	Key:  "prop_5661a1adfdc1e72c",
	Build: SimplicialSet.Law(Statement{
		Binders: "∀x₀:A. ∀n i k:num. ∀v:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"v ∈ X.simplices(n + 2)",
			"i < k",
			"k ≤ n + 2",
			"X.d(n + 2, i, v) = base_simplex(x₀, n + 1)",
		},
		Conclusion: "X.d(n + 1, i, X.d(n + 2, k, v)) = base_simplex(x₀, n)",
	},
		func(a *Argument, simplicial Fact, x0 *Expr[A], n, i, k *Expr[Nat], v *Expr[A], given Fact) {
			a.Show(
				"the face i of the face k of v is a face of the face i of v, the base simplex",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, k - 1, X.d(n + 2, i, v))"),
						"d_i d_k = d_{k−1} d_i, as i < k ≤ n + 2",
						By(FaceFace.Read(simplicial).At(n, i, k, v), given)),
					FinalLeg(
						"the face i of v is the base simplex at n + 1, and its face k − 1 ≤ n + 1 is the base simplex at n",
						ByArith(BaseSimplexFace.Read(simplicial).At(x0, n, a.TermAs[Nat]("k - 1")), given)),
				))
		}),
})}

// MapBaseSimplex — a simplicial map carries the base simplex at a
// vertex to the base simplex at the image vertex. By induction on the
// dimension: at 0 both sides are F(0, x₀); at n + 1 the base simplex is
// the 0-th degeneracy of the one at n, an n-simplex of X, so the map
// passes the degeneracy, the hypothesis turns the image of the simplex
// below into the base simplex of Y at F(0, x₀), and its 0-th degeneracy
// is the base simplex of Y one dimension up.
var MapBaseSimplex = mapBaseSimplexThm{family.Add(registry.ProofEntry{
	Name: "MapBaseSimplex",
	Key:  "prop_730d9264ffa34a53",
	Build: SimplicialMap.Law(Statement{
		Binders: "∀x₀:A. ∀n:num.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
		},
		Conclusion: "F(n, base_simplex(x₀, n)) = base_simplex(F(0, x₀), n)",
	},
		func(a *Argument, mapping Fact, x0 *Expr[A], n *Expr[Nat], vertex Fact) {
			s, sPrime := a.TermAs[Fun3[Nat, Nat, A, A]]("X.s"), a.TermAs[Fun3[Nat, Nat, B, B]]("Y.s")
			imageVertex := a.TermAs[B]("F(0, x₀)")
			a.Induct(n)
			a.Base(
				"at 0 the base simplex is the vertex, on both sides",
				Simp(Fwd(BaseSimplexDef), Fwd(BaseSimplexDef.Inst[B]())),
				Refl())
			a.Step(
				"the map passes the 0-th degeneracy that builds the next base simplex",
				func(b *Argument, ih Fact) {
					zero, below := b.TermAs[Nat]("0"), b.TermAs[A]("base_simplex(x₀, n)")
					b.Show(
						"with suc(n) written n + 1, the base simplex runs through s_0, the map and the hypothesis",
						Simp(Fwd(nat_arith.Add1)),
						CalcEq(
							Leg(
								b.TermAs[B]("F(n + 1, X.s(n, 0, base_simplex(x₀, n)))"),
								"the base simplex of X at n + 1 is s_0 of the one at n",
								By(Normalized, BaseSimplexSucc.At(s, x0, n))),
							Leg(
								b.TermAs[B]("Y.s(n, 0, F(n, base_simplex(x₀, n)))"),
								"F commutes with s_0 at the base simplex at n, an n-simplex of X",
								By(
									MapDegeneracy.Read(mapping).At(n, zero, below),
									BaseSimplexIn.Read(MapSource.Read(mapping)).At(x0, n),
									vertex,
									nat_order.ZeroLessEq.At(n))),
							Leg(
								b.TermAs[B]("Y.s(n, 0, base_simplex(F(0, x₀), n))"),
								"the hypothesis at n",
								By(Normalized, ih)),
							FinalLeg(
								"which is the base simplex of Y at n + 1",
								By(BaseSimplexSucc.At(sPrime, imageVertex, n))),
						))
				})
		}),
})}

// SimplicialPointSimplicesDef — `simplicial_point(a)`: the simplicial set with
// one simplex in every dimension, the point a; its faces and
// degeneracies are the constant maps at a.
var SimplicialPointSimplicesDef = simplicialPointSimplicesDefThm{family.Define(registry.DefEntry{
	Name:      "SimplicialPointSimplicesDef",
	Key:       "prop_af7af1ad968a697a",
	Const:     "simplicial_point_simplices",
	Type:      "A → num → set(A)",
	Equations: []string{"∀a:A. ∀n:num. simplicial_point_simplices(a, n) = {a}"},
})}

// SimplicialPoint — the one-point simplicial set is a simplicial set.
// Every face and every degeneracy returns a, so of the eight axioms the
// unfolded predicate leaves three: the four identities equating two
// composites read a = a, and d_i s_i = id and d_{i+1} s_i = id both read
// a = x, one obligation.
var SimplicialPoint = simplicialPointThm{family.Add(registry.ProofEntry{
	Name: "SimplicialPoint",
	Key:  "prop_7f58f2efef811dd7",
	Build: family.Instance(SimplicialSet, "∀a:A. simplicial_set(simplicial_point(a))",
		Case(
			"a face of an (n + 1)-simplex is a, a simplex in every dimension",
			BySets(SimplicialPointSimplicesDef)),
		Case(
			"so is a degeneracy of an n-simplex",
			BySets(SimplicialPointSimplicesDef)),
		Case(
			"d_i s_i and d_{i+1} s_i return a, and the simplex they start from is a, the only one",
			BySets(SimplicialPointSimplicesDef)),
	),
})}

// ConstantSimplicialSet — the constant simplicial set on S is a
// simplicial set. Every face and every degeneracy is the identity, so
// the six simplicial identities read x = x and the unfolded predicate
// leaves the two closures, each x ∈ S ⇒ x ∈ S.
var ConstantSimplicialSet = constantSimplicialSetThm{family.Add(registry.ProofEntry{
	Name: "ConstantSimplicialSet",
	Key:  "prop_84d847fc557f0f08",
	Build: family.Instance(SimplicialSet, "∀S:set(A). simplicial_set(constant_simplicial_set(S))",
		Case(
			"a face of a simplex is the simplex itself, in S",
			BySets()),
		Case(
			"so is a degeneracy",
			BySets()),
	),
})}

// MapToPoint — every simplicial set maps to the point by the constant
// map: its source is the simplicial set in hand, its target is the
// point, each value a is the one simplex of the point in its
// dimension, and with every face and every degeneracy of the point
// returning a, each commutation reads a = a.
var MapToPoint = mapToPointThm{family.Add(registry.ProofEntry{
	Name: "MapToPoint",
	Key:  "prop_9632f5d2fac92fd5",
	Build: SimplicialSet.Law("∀a:B. simplicial_map(X, simplicial_point(a), λn:num. λx:A. a)",
		func(arg *Argument, simplicial Fact, a *Expr[B]) {
			// The simplicial set in hand, by its components, and the point's constant face and degeneracy.
			X := arg.TermAs[SimplicialOps[A]]("X")
			target := arg.Have(
				"the point is a simplicial set",
				"simplicial_set(simplicial_point(a))",
				By(SimplicialPoint.At(a)))
			value := arg.Have(
				"a is a simplex of the point in every dimension",
				"∀n:num. a ∈ simplicial_point_simplices(a, n)",
				BySets(SimplicialPointSimplicesDef))
			arg.Show(
				"the source is the hypothesis, every value lies in the point, and every commutation is a = a",
				By(
					simplicial,
					target,
					value,
					At(SimplicialMap, X, arg.Term("simplicial_point(a)"), arg.Term("λn:num. λx:A. a"))))
		}),
})}
