package sensitivity

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/hypercube"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/simple_graph"
	"github.com/euc-ai/xugo/library/proofs/sets/boolean_function/boolean_degree"
	"github.com/euc-ai/xugo/library/proofs/sets/boolean_function/boolean_function"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// DegreeLeLocalSensitivity counts neighbours using the coordinates that
// change f at X. It applies in any face S of the ambient cube U.
var DegreeLeLocalSensitivity = degreeLeLocalSensitivityThm{family.Add(registry.ProofEntry{
	Name: "DegreeLeLocalSensitivity",
	Key:  "prop_3027092469e7c9ca",
	Build: family.Theorem(Statement{
		Binders: "∀U S:set(A). ∀H:set(set(A)). ∀f:set(A) → bool. ∀X:set(A).",
		Hypotheses: []string{
			"finite(U)", "S ⊆ U",
			"∀i:A. i ∈ S ∧ set_toggle(i, X) ∈ H ⇒ f(X) ≠ f(set_toggle(i, X))",
		},
		Conclusion: "graph_degree(H, cube_adjacent(S), X) ≤ local_sensitivity(U, f, X)",
		Abbrev: Abbrev{
			{Name: "changes", Text: "{i:A | i ∈ U ∧ f(X) ≠ f(set_toggle(i, X))}"},
			{Name: "flip", Text: "λi:A. set_toggle(i, X)"},
			{Name: "flipped", Text: "image(«flip», «changes»)"},
			{Name: "neighbours", Text: "graph_neighbours(H, cube_adjacent(S), X)"},
		},
	}, func(
		a *Argument,
		U, S *Expr[Set[A]],
		H *Expr[Set[Set[A]]],
		f *Arrow[Set[A], Bool],
		X *Expr[Set[A]],
		finiteU, face, internal Fact,
	) {
		changes := a.TermAs[Set[A]]("«changes»")
		flip := a.TermAs[Fun[A, Set[A]]]("«flip»")
		flipped := a.TermAs[Set[Set[A]]]("«flipped»")
		adjacent := a.TermAs[Fun2[Set[A], Set[A], Bool]]("cube_adjacent(S)")
		inU := a.Have(
			"changing coordinates lie in U",
			"«changes» ⊆ U",
			BySets())
		finiteChanges := a.Have(
			"finitely many coordinates change f",
			"finite(«changes»)",
			By(finiteU, inU, finite_set.FiniteSubset.At(changes, U)))
		finiteFlips := a.Have(
			"their flips give a finite set of vertices",
			"finite(«flipped»)",
			By(finiteChanges, finite_set.FiniteImage.At(flip, changes)))
		covered := a.Have(
			"every neighbour in H is a flip of a changing coordinate",
			"«neighbours» ⊆ «flipped»",
			Derive(func(b *Argument) {
				b.Do(Simp(Fwd(set_basic.SubsetDef)))
				Y := b.FixAs[Set[A]]("Y")
				member := b.Assume()
				edge := b.Have(
					"Y is an adjacent vertex of H",
					"Y ∈ H ∧ cube_adjacent(S, X, Y)",
					BySets(member, simple_graph.NeighboursDef.At(H, adjacent, X)))
				_, coord := b.ObtainAs[A](
					"choose the coordinate joining X to Y",
					"∃i:A. i ∈ S ∧ Y = set_toggle(i, X)",
					By(edge, hypercube.CubeAdjacentDef.At(S, X, Y)))
				changesHere := b.Have(
					"that coordinate changes f at X",
					"i ∈ «changes»",
					BySets(face, internal, coord, edge))
				b.Show(
					"Y is in the image of the changing coordinates",
					By(changesHere, coord, set_basic.InImage.At(flip, changes, Y)))
			}))
		a.Show(
			"count the neighbours inside the image, then bound the image by its source",
			ByArith(
				finiteChanges,
				finiteFlips,
				covered,
				cardinality.CardSubset.At(a.TermAs[Set[Set[A]]]("«neighbours»"), flipped),
				cardinality.CardImageLe.At(flip, changes),
				simple_graph.DegreeDef.At(H, adjacent, X),
				boolean_function.LocalSensitivityDef.At(U, f, X)))
	}),
})}

// ParityClassDegreeBound bounds every internal degree of a face parity class by the sensitivity
// on the ambient cube. Each internal edge flips a sensitive coordinate at its initial vertex.
var ParityClassDegreeBound = parityClassDegreeBoundThm{family.Add(registry.ProofEntry{
	Name: "ParityClassDegreeBound",
	Key:  "prop_a3b6fb29b5580d5a",
	Build: family.Theorem(Statement{
		Binders:    "∀U S:set(A). ∀f:(set(A) → bool). ∀b:bool. ∀X:set(A).",
		Hypotheses: []string{"finite(U)", "S ⊆ U", "X ∈ boolean_parity_class(S, f, b)"},
		Conclusion: "graph_degree(boolean_parity_class(S, f, b), cube_adjacent(S), X) ≤ sensitivity(U, f)",
	}, func(
		a *Argument,
		U, S *Expr[Set[A]],
		f *Arrow[Set[A], Bool],
		b *Expr[Bool],
		X *Expr[Set[A]],
		finite, face, inside Fact,
	) {
		H := a.TermAs[Set[Set[A]]]("boolean_parity_class(S, f, b)")
		input := a.Have(
			"a vertex of the face is an input of the ambient cube",
			"X ⊆ U",
			By(face, inside, boolean_degree.InParityClass.At(S, f, b, X), set_order.SubsetTrans.At(X, S, U)))
		finiteX := a.Have(
			"the input uses finitely many coordinates",
			"finite(X)",
			By(finite, input, finite_set.FiniteSubset.At(X, U)))
		changes := a.Have(
			"internal flips change the Boolean value",
			"∀i:A. i ∈ S ∧ set_toggle(i, X) ∈ boolean_parity_class(S, f, b) ⇒ f(X) ≠ f(set_toggle(i, X))",
			By(finiteX, inside, At(boolean_degree.ParityClassEdge, S, f, b, X)))
		a.Show(
			"the neighbour count is bounded first locally and then globally",
			By(
				finite,
				face,
				input,
				changes,
				DegreeLeLocalSensitivity.At(U, S, H, f, X),
				boolean_function.SensitivityBounds.At(U, f, X),
				nat_order.LessEqTrans.At(
					a.TermAs[Nat]("graph_degree(boolean_parity_class(S, f, b), cube_adjacent(S), X)"),
					a.TermAs[Nat]("local_sensitivity(U, f, X)"),
					a.TermAs[Nat]("sensitivity(U, f)"))))
	}),
})}

// SensitivityTheorem bounds the multilinear degree of a Boolean function by the
// square of its sensitivity on any finite set of coordinates.
var SensitivityTheorem = sensitivityTheoremThm{family.Add(registry.ProofEntry{
	Name: "SensitivityTheorem",
	Key:  "prop_4e68449819c599ca",
	Build: family.Theorem(Statement{
		Binders:    "∀U:set(A). ∀f:(set(A) → bool).",
		Hypotheses: []string{"finite(U)"},
		Conclusion: "boolean_degree(U, f) ≤ sensitivity(U, f) * sensitivity(U, f)",
		Abbrev: Abbrev{
			{Name: "Face", Text: "λS:set(A). {Y:set(A) | Y ⊆ S}"},
			{Name: "Degree", Text: "λS:set(A). λH:set(set(A)). λX:set(A). " +
				"    graph_degree(H, cube_adjacent(S), X)"},
		},
	}, func(a *Argument, U *Expr[Set[A]], f *Arrow[Set[A], Bool], finite Fact) {
		a.Cases(a.TermAs[Bool]("0 < boolean_degree(U, f)"))
		a.When(
			"positive degree selects a face with a strict parity majority",
			func(b *Argument, positive Fact) {
				S, face := b.ObtainAs[Set[A]](
					"choose a face of full degree",
					"∃S:set(A). "+
						"    S ⊆ U ∧ "+
						"    card(S) = boolean_degree(U, f) ∧ "+
						"    (∃b:bool. card(«Face»(S)) < 2 * card(boolean_parity_class(S, f, b)))",
					By(finite, positive, boolean_degree.MajorityFace.At(U, f)))
				larger, majority := b.ObtainAs[Bool](
					"choose its larger parity class",
					"∃b:bool. card(«Face»(S)) < 2 * card(boolean_parity_class(S, f, b))",
					By(face))
				class := b.TermAs[Set[Set[A]]]("boolean_parity_class(S, f, b)")
				finiteS := b.Have(
					"only finitely many coordinates remain",
					"finite(S)",
					By(finite, face, finite_set.FiniteSubset.At(S, U)))
				contained := b.Have(
					"the chosen parity class consists of vertices of the face",
					"boolean_parity_class(S, f, b) ⊆ «Face»(S)",
					Simp(Fwd(boolean_degree.ParityClassDef)),
					BySets())
				X, large := b.ObtainAs[Set[A]](
					"apply the graph bound to find a vertex with large internal degree",
					"∃X:set(A). "+
						"    X ∈ boolean_parity_class(S, f, b) ∧ "+
						"    card(S) ≤ "+
						"    «Degree»(S, boolean_parity_class(S, f, b), X) * «Degree»(S, boolean_parity_class(S, f, b), X)",
					By(finiteS, majority, contained, hypercube.Huang.At(S, class)))
				bounded := b.Have(
					"every edge counted there is detected by the Boolean function",
					"«Degree»(S, boolean_parity_class(S, f, b), X) ≤ sensitivity(U, f)",
					By(finite, large, face, ParityClassDegreeBound.At(U, S, f, larger, X)))
				d := b.TermAs[Nat]("«Degree»(S, boolean_parity_class(S, f, b), X)")
				s := b.TermAs[Nat]("sensitivity(U, f)")
				b.Show(
					"the square of sensitivity therefore bounds the dimension of the chosen face",
					By(
						bounded,
						large,
						face,
						nat_order.LessEqMul2.At(d, s, d, s),
						nat_order.LessEqTrans.At(b.TermAs[Nat]("card(S)"),
							b.TermAs[Nat](
								"«Degree»(S, boolean_parity_class(S, f, b), X) * «Degree»(S, boolean_parity_class(S, f, b), X)"),
							b.TermAs[Nat]("sensitivity(U, f) * sensitivity(U, f)"))))
			})
		a.Otherwise(
			"degree zero already satisfies the bound",
			func(b *Argument, zero Fact) {
				b.Show(
					"squares of natural numbers are nonnegative",
					ByArith(zero))
			})
	}),
})}
