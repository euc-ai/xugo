// alexander_whitney.go — the Alexander–Whitney map of a bisimplicial
// module and its laws. At an (n, n)-simplex x the map's coordinate p, in
// bidegree (p, n − p), is the front p-face of the back (n − p)-face of x.
// The front face is horizontal and the back face vertical: in
// simplicial_set's iterates the front face is face_iterate_top along the
// row, which removes the last horizontal face (here n − p times), and the
// back face is face_iterate_bottom along the column, which removes the
// 0-th vertical face (here p times).
//
// The map is a chain map from the face complex of the diagonal to the
// total complex, with no sign of its own. Out of an (n + 1, n + 1)-simplex,
// the diagonal's faces i ≤ p land at the coordinate p as the horizontal
// faces i of the coordinate p + 1, and its faces i > p as the vertical
// faces i − p of the coordinate p: two disjoint ranges. The horizontal
// boundary has one term more, the face i = p + 1, and the vertical
// boundary one more, the face j = 0; the two are one simplex with
// opposite signs, and cancel. The map is natural in maps of bisimplicial
// modules, and it reads the coordinate n as the simplex itself when the
// vertical faces are identities, the coordinate 0 when the horizontal
// ones are.

package simplicial_module

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_homotopy"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// AlexanderWhitneyDef — `alexander_whitney(V, dh, dv, n, x, p)`: the
// Alexander–Whitney map at an (n, n)-simplex x, a diagonal of degree n
// whose coordinate p ≤ n is the horizontal front face
// dh_{p+1} ∘ ⋯ ∘ dh_n of the vertical back face (dv_0)^p x, a member of
// D(p, n − p), and V.zero past n.
var AlexanderWhitneyDef = alexanderWhitneyDefThm{family.Define(registry.DefEntry{
	Name:  "AlexanderWhitneyDef",
	Key:   "prop_647aaf2ac6066e2",
	Const: "alexander_whitney",
	Type: "module_ops(A, B) → " +
		"(num → num → num → B → B) → " +
		"(num → num → num → B → B) → " +
		"num → " +
		"B → " +
		"num → " +
		"B",
	Equations: []string{
		"∀V:module_ops(A, B). ∀dh dv:(num → num → num → B → B). ∀n:num. ∀x:B. ∀p:num. " +
			"    alexander_whitney(V, dh, dv, n, x, p) = " +
			"    COND(p ≤ n, " +
			"        face_iterate_top(λa:num. λi:num. dh(a, n - p, i), " +
			"            n, " +
			"            n - p, " +
			"            face_iterate_bottom(λb:num. λj:num. dv(n, b, j), n, p, x)), " +
			"        V.zero)",
	},
	Reading: "Coordinate p keeps the horizontal vertices 0, …, p and the vertical " +
		"vertices p, …, n of x: on a tensor product of simplicial modules it is x ⊗ y ↦ " +
		"Σ_p (front p-face of x) ⊗ (back (n − p)-face of y), the half of Eilenberg–Zilber " +
		"that runs from the diagonal to the total complex. The degeneracies are not read.",
})}

// AlexanderWhitneyChainMap — the Alexander–Whitney map is a chain map from
// the face complex of the diagonal of a bisimplicial module to the total
// complex of its alternating face sums.
var AlexanderWhitneyChainMap = alexanderWhitneyChainMapThm{family.Add(registry.ProofEntry{
	Name: "AlexanderWhitneyChainMap",
	Key:  "prop_21e41484003fa4f5",
	Reading: "In degree 0 the map is x ↦ (x, 0, 0, …). Out of degree 1 it takes x to dh_1 x at the " +
		"coordinate 0 and dv_0 x at the coordinate 1, and the check is the one coordinate 0: h of the " +
		"coordinate 1 plus v of the coordinate 0 is dh_0 dv_0 x − dh_1 dv_0 x + dv_0 dh_1 x − dv_1 " +
		"dh_1 x, which the commuting faces reduce to the diagonal's boundary dh_0 dv_0 x − dh_1 dv_1 x.",
	Build: family.Sections(BisimplicialModule.Statement(Statement{
		Conclusion: "chain_map(R, " +
			"    face_complex(R, V, bisimplicial_diagonal(D)), " +
			"    double_total(V, " +
			"        D.simplices, " +
			"        «horizontalBoundaryFamily», " +
			"        «verticalBoundaryFamily», " +
			"        alternating_sign), " +
			"    alexander_whitney(V, D.dh, D.dv))",
		Abbrev: Abbrev{
			{Name: "horizontalBoundaryFamily", Text: "λp:num. λq:num. " +
				"    face_boundary(R, V, λm:num. λi:num. D.dh(m, q, i), p)"},
			{Name: "verticalBoundaryFamily", Text: "λp:num. λq:num. " +
				"    face_boundary(R, V, λm:num. λj:num. D.dv(p, m, j), q)"},
		},
	}), func(ctx *Script, headline string) *GoalStackNode {
		// Past its degree the map is zero.
		coordinatePast := ctx.Lemma(Statement{
			Binders:    "∀V:module_ops(A, B). ∀D:bisimplicial_ops(B). ∀n p:num. ∀x:B.",
			Hypotheses: []string{"n < p"},
			Conclusion: "alexander_whitney(V, D.dh, D.dv, n, x, p) = V.zero",
		}, func(
			a *Argument,
			V *Expr[ModuleOps[A, B]],
			D *Expr[BisimplicialOps[B]],
			n, p *Expr[Nat],
			x *Expr[B],
			past Fact,
		) {
			beyond := a.Simplified(past, Rev(nat_order.NotLessEq))
			a.Show(
				"the definition's tail is zero",
				Simp(Fwd(AlexanderWhitneyDef), Fwd(beyond)),
				Basic())
		})

		coordinateHom := ctx.Lemma(Statement{
			Binders:    "∀R:ring_ops(A). ∀V:module_ops(A, B). ∀D:bisimplicial_ops(B). ∀n p:num.",
			Hypotheses: []string{"bisimplicial_module(R, V, D)", "p ≤ n"},
			Conclusion: "module_homomorphism(R, " +
				"    restrict_module(V, D.simplices(n, n)), " +
				"    restrict_module(V, D.simplices(p, n - p)), " +
				"    λx:B. alexander_whitney(V, D.dh, D.dv, n, x, p))",
		}, func(
			a *Argument,
			R *Expr[RingOps[A]],
			V *Expr[ModuleOps[A, B]],
			D *Expr[BisimplicialOps[B]],
			n, p *Expr[Nat],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the bisimplicial module",
				"the coordinate is in range")
			columnBack := a.Have(
				"the vertical back iterate is linear",
				"module_homomorphism(R, "+
					"    restrict_module(V, bisimplicial_column(D, n).simplices(n)), "+
					"    restrict_module(V, bisimplicial_column(D, n).simplices(n - p)), "+
					"    λx:B. face_iterate_bottom(bisimplicial_column(D, n).d, n, p, x))",
				By(
					parts[1],
					BisimplicialColumns.Read(parts[0]).At(n),
					FaceIterateBottomHom.At(R, V, a.TermAs[SimplicialOps[B]]("bisimplicial_column(D, n)"), n, p)))
			back := a.Simplified(
				columnBack,
				Fwd(simplicial_homotopy.BisimplicialColumnDef),
				Fwd(simplicial_set.SimplicialSimplicesDef),
				Fwd(simplicial_set.SimplicialFaceDef))
			rowFront := a.Have(
				"the horizontal front iterate is linear",
				"module_homomorphism(R, "+
					"    restrict_module(V, bisimplicial_row(D, n - p).simplices(n)), "+
					"    restrict_module(V, bisimplicial_row(D, n - p).simplices(n - (n - p))), "+
					"    λx:B. face_iterate_top(bisimplicial_row(D, n - p).d, n, n - p, x))",
				ByArith(
					BisimplicialRows.Read(parts[0]).At(a.TermAs[Nat]("n - p")),
					FaceIterateTopHom.At(
						R, V, a.TermAs[SimplicialOps[B]]("bisimplicial_row(D, n - p)"), n, a.TermAs[Nat]("n - p"))))
			frontOnRow := a.Simplified(
				rowFront,
				Fwd(simplicial_homotopy.BisimplicialRowDef),
				Fwd(simplicial_set.SimplicialSimplicesDef),
				Fwd(simplicial_set.SimplicialFaceDef))
			dimension := a.Have(
				"the front iterate finishes in horizontal degree p",
				"n - (n - p) = p",
				ByArith(parts[1]))
			front := a.Simplified(frontOnRow, Fwd(dimension))
			a.Show(
				"the Alexander–Whitney coordinate is the composite",
				Simp(Fwd(AlexanderWhitneyDef)),
				By(
					back,
					front,
					module_homomorphism.HomCompose.At(
						R,
						a.TermAs[ModuleOps[A, B]]("restrict_module(V, D.simplices(n, n))"),
						a.TermAs[ModuleOps[A, B]]("restrict_module(V, D.simplices(n, n - p))"),
						a.TermAs[ModuleOps[A, B]]("restrict_module(V, D.simplices(p, n - p))"),
						a.TermAs[Fun[B, B]]("λx:B. «columnZerothFaces»(n, n, p, x)"),
						a.TermAs[Fun[B, B]]("λx:B. «rowLastFaces»(n - p, n, n - p, x)")),
					functions.ComposeApply))
		})

		// The coordinate p of the diagonal face i of x: the horizontal face i
		// passes the back iterate of the vertical face i.
		faceCoordinate := ctx.Lemma(Statement{
			Binders:    "∀V:module_ops(A, B). ∀D:bisimplicial_ops(B). ∀n p i:num. ∀x:B.",
			Hypotheses: []string{"bisimplicial_set(D)", "x ∈ D.simplices(n + 1, n + 1)", "p ≤ n", "i ≤ n + 1"},
			Conclusion: "«columnZerothFaces»(n + 1, n, p, D.dv(n + 1, n + 1, i, x)) ∈ " +
				"D.simplices(n + 1, n - p) ∧ " +
				"alexander_whitney(V, D.dh, D.dv, n, D.dh(n + 1, n, i, D.dv(n + 1, n + 1, i, x)), p) = " +
				"«rowLastFaces»(n - p, " +
				"    n, " +
				"    n - p, " +
				"    D.dh(n + 1, n - p, i, «columnZerothFaces»(n + 1, n, p, D.dv(n + 1, n + 1, i, x))))",
		}, func(
			a *Argument,
			V *Expr[ModuleOps[A, B]],
			D *Expr[BisimplicialOps[B]],
			n, p, i *Expr[Nat],
			x *Expr[B],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the bisimplicial identities",
				"the diagonal simplex",
				"the coordinate is in range",
				"the face is in range")
			verticalFaceIn := a.Have(
				"the diagonal vertical face lies in bidegree (n + 1, n)",
				"D.dv(n + 1, n + 1, i, x) ∈ D.simplices(n + 1, n)",
				By(
					parts[0],
					parts[1],
					parts[3],
					simplicial_homotopy.BisimplicialSet.At(D),
					simplicial_set.FaceIn.At(a.TermAs[SimplicialOps[B]]("bisimplicial_column(D, n + 1)"), n, i, x),
					simplicial_homotopy.BisimplicialColumnDef,
					simplicial_set.SimplicialSimplicesDef,
					simplicial_set.SimplicialFaceDef))
			passHorizontal := a.Have(
				"the horizontal face passes the vertical back iterate",
				"«columnZerothFaces»(n, n, p, D.dh(n + 1, n, i, D.dv(n + 1, n + 1, i, x))) = "+
					"D.dh(n + 1, n - p, i, «columnZerothFaces»(n + 1, n, p, D.dv(n + 1, n + 1, i, x)))",
				By(
					parts[2],
					parts[3],
					verticalFaceIn,
					simplicial_homotopy.ColumnFaceIterateBottomHorizontalFace.Read(parts[0]).At(
						n, n, p, i, a.TermAs[B]("D.dv(n + 1, n + 1, i, x)"))))
			a.Show(
				"the back iterate of the vertical face stays in its column, and the horizontal face passes it",
				SplitConj(
					Case(
						"the back iterate of the vertical face lies in bidegree (n + 1, n − p)",
						By(
							parts[2],
							verticalFaceIn,
							simplicial_homotopy.ColumnFaceIterateBottomIn.Read(parts[0]).At(
								a.TermAs[Nat]("n + 1"), n, p, a.TermAs[B]("D.dv(n + 1, n + 1, i, x)")))),
					Case(
						"the coordinate p of the face is the front iterate of the passed face",
						Simp(Fwd(AlexanderWhitneyDef)),
						By(parts[2], passHorizontal))))
		})

		// At the coordinate p the diagonal's faces split into two disjoint
		// ranges: a face i ≤ p is the horizontal face i of the coordinate
		// p + 1, a face i > p the vertical face i − p of the coordinate p.
		lowerFaces := ctx.Lemma(Statement{
			Binders:    "∀V:module_ops(A, B). ∀D:bisimplicial_ops(B). ∀n p i:num. ∀x:B.",
			Hypotheses: []string{"bisimplicial_set(D)", "x ∈ D.simplices(n + 1, n + 1)", "p ≤ n", "i ≤ p"},
			Conclusion: "alexander_whitney(V, " +
				"    D.dh, " +
				"    D.dv, " +
				"    n, " +
				"    D.dh(n + 1, n, i, D.dv(n + 1, n + 1, i, x)), " +
				"    p) = " +
				"D.dh(p + 1, n - p, i, alexander_whitney(V, D.dh, D.dv, n + 1, x, p + 1))",
		}, func(
			a *Argument,
			V *Expr[ModuleOps[A, B]],
			D *Expr[BisimplicialOps[B]],
			n, p, i *Expr[Nat],
			x *Expr[B],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the bisimplicial identities",
				"the diagonal simplex",
				"the coordinate is in range",
				"the face is in the lower range")
			dimensions := a.Have(
				"the lower face and the iterates of both coordinates have matching degrees",
				"i ≤ n + 1 ∧ "+
					"p + 1 ≤ n + 1 ∧ "+
					"n + 1 - (p + 1) = n - p ∧ "+
					"n + 1 - (n - p) = p + 1 ∧ "+
					"i + (n - p) ≤ n ∧ "+
					"n - p ≤ n",
				ByArith(parts[3], parts[2]))
			absorbFace := a.Have(
				"a face at or below p is absorbed into one further back iterate",
				"«columnZerothFaces»(n + 1, n, p, D.dv(n + 1, n + 1, i, x)) = "+
					"«columnZerothFaces»(n + 1, n + 1, p + 1, x)",
				By(
					parts[0],
					parts[3],
					parts[2],
					parts[1],
					simplicial_homotopy.BisimplicialSet.At(D),
					simplicial_set.FaceIterateBottomBelow.At(
						a.TermAs[SimplicialOps[B]]("bisimplicial_column(D, n + 1)"), n, p, i, x),
					simplicial_homotopy.BisimplicialColumnDef,
					simplicial_set.SimplicialSimplicesDef,
					simplicial_set.SimplicialFaceDef))
			backCarrier := a.Have(
				"the next back iterate has bidegree (n + 1, n − p)",
				"«columnZerothFaces»(n + 1, n + 1, p + 1, x) ∈ D.simplices(n + 1, n - p)",
				By(
					parts[1],
					dimensions,
					simplicial_homotopy.ColumnFaceIterateBottomIn.Read(parts[0]).At(
						a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("p + 1"), x)))
			passFront := a.Have(
				"the lower horizontal face passes the front iterate",
				"«rowLastFaces»(n - p, "+
					"    n, "+
					"    n - p, "+
					"    D.dh(n + 1, n - p, i, «columnZerothFaces»(n + 1, n + 1, p + 1, x))) = "+
					"D.dh(p + 1, "+
					"    n - p, "+
					"    i, "+
					"    «rowLastFaces»(n - p, n + 1, n - p, «columnZerothFaces»(n + 1, n + 1, p + 1, x)))",
				By(
					parts[0],
					backCarrier,
					dimensions,
					simplicial_homotopy.BisimplicialSet.At(D),
					simplicial_set.FaceIterateTopFace.At(
						a.TermAs[SimplicialOps[B]]("bisimplicial_row(D, n - p)"),
						n,
						a.TermAs[Nat]("n - p"),
						i,
						a.TermAs[B]("«columnZerothFaces»(n + 1, n + 1, p + 1, x)")),
					simplicial_homotopy.BisimplicialRowDef,
					simplicial_set.SimplicialSimplicesDef,
					simplicial_set.SimplicialFaceDef))
			a.Show(
				"the remaining lower face is the horizontal boundary face of the next coordinate",
				CalcEq(
					Leg(
						a.TermAs[B](
							"«rowLastFaces»(n - p, "+
								"    n, "+
								"    n - p, "+
								"    D.dh(n + 1, n - p, i, «columnZerothFaces»(n + 1, n, p, D.dv(n + 1, n + 1, i, x))))"),
						"the coordinate p of the face i is read through the back iterate of its vertical face",
						By(parts[0], parts[1], parts[2], dimensions, At(faceCoordinate, V, D, n, p, i, x))),
					FinalLeg(
						"the face is absorbed into the next back iterate and passes the front iterate",
						Simp(Fwd(AlexanderWhitneyDef), Fwd(dimensions)),
						By(absorbFace, passFront))))
		})

		upperFaces := ctx.Lemma(Statement{
			Binders: "∀V:module_ops(A, B). ∀D:bisimplicial_ops(B). ∀n p i:num. ∀x:B.",
			Hypotheses: []string{
				"bisimplicial_set(D)",
				"x ∈ D.simplices(n + 1, n + 1)",
				"p ≤ n",
				"p < i",
				"i ≤ n + 1",
			},
			Conclusion: "alexander_whitney(V, " +
				"    D.dh, " +
				"    D.dv, " +
				"    n, " +
				"    D.dh(n + 1, n, i, D.dv(n + 1, n + 1, i, x)), " +
				"    p) = " +
				"D.dv(p, n + 1 - p, i - p, alexander_whitney(V, D.dh, D.dv, n + 1, x, p))",
		},
			func(
				a *Argument,
				V *Expr[ModuleOps[A, B]],
				D *Expr[BisimplicialOps[B]],
				n, p, i *Expr[Nat],
				x *Expr[B],
				given Fact,
			) {
				parts := a.Conjuncts(
					given,
					"the bisimplicial identities",
					"the diagonal simplex",
					"the coordinate is in range",
					"the face is above p",
					"the face is in range")
				dimensions := a.Have(
					"the upper face and the iterates of the coordinate have matching degrees",
					"p ≤ i ∧ "+
						"n < i + (n - p) ∧ "+
						"n - p ≤ n ∧ "+
						"p ≤ n + 1 ∧ "+
						"n + 1 - p = n - p + 1 ∧ "+
						"n + 1 - (n - p + 1) = p ∧ "+
						"n - p + 1 ≤ n + 1 ∧ "+
						"i - p ≤ n - p + 1",
					ByArith(parts[3], parts[4], parts[2]))
				face := At(faceCoordinate, V, D, n, p, i, x)
				backCarrier := a.Have(
					"the back iterate of x has bidegree (n + 1, n + 1 − p)",
					"«columnZerothFaces»(n + 1, n + 1, p, x) ∈ D.simplices(n + 1, n + 1 - p)",
					By(
						parts[1],
						dimensions,
						simplicial_homotopy.ColumnFaceIterateBottomIn.Read(parts[0]).At(
							a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 1"), p, x)))
				passVertical := a.Have(
					"the upper vertical face passes the back iterate with shifted index",
					"«columnZerothFaces»(n + 1, n, p, D.dv(n + 1, n + 1, i, x)) = "+
						"D.dv(n + 1, n + 1 - p, i - p, «columnZerothFaces»(n + 1, n + 1, p, x))",
					By(
						parts[0],
						parts[4],
						parts[2],
						parts[1],
						dimensions,
						simplicial_homotopy.BisimplicialSet.At(D),
						simplicial_set.FaceIterateBottomFace.At(
							a.TermAs[SimplicialOps[B]]("bisimplicial_column(D, n + 1)"), n, p, i, x),
						simplicial_homotopy.BisimplicialColumnDef,
						simplicial_set.SimplicialSimplicesDef,
						simplicial_set.SimplicialFaceDef))
				passFront := a.Have(
					"the vertical face passes the horizontal front iterate",
					"«rowLastFaces»(n - p, "+
						"    n + 1, "+
						"    n - p + 1, "+
						"    D.dv(n + 1, n - p + 1, i - p, «columnZerothFaces»(n + 1, n + 1, p, x))) = "+
						"D.dv(p, "+
						"    n - p + 1, "+
						"    i - p, "+
						"    «rowLastFaces»(n - p + 1, n + 1, n - p + 1, «columnZerothFaces»(n + 1, n + 1, p, x)))",
					By(
						backCarrier,
						dimensions,
						simplicial_homotopy.RowFaceIterateTopVerticalFace.Read(parts[0]).At(
							a.TermAs[Nat]("n + 1"),
							a.TermAs[Nat]("n - p"),
							a.TermAs[Nat]("n - p + 1"),
							a.TermAs[Nat]("i - p"),
							a.TermAs[B]("«columnZerothFaces»(n + 1, n + 1, p, x)"))))
				a.Show(
					"the remaining upper face is the vertical boundary face of the coordinate",
					CalcEq(
						Leg(
							a.TermAs[B](
								"«rowLastFaces»(n - p, "+
									"    n, "+
									"    n - p, "+
									"    D.dh(n + 1, n - p, i, «columnZerothFaces»(n + 1, n, p, D.dv(n + 1, n + 1, i, x))))"),
							"the coordinate p of the face i is read through the back iterate of its vertical face",
							By(parts[0], parts[1], parts[2], parts[4], face)),
						Leg(
							a.TermAs[B](
								"«rowLastFaces»(n - p, "+
									"    n + 1, "+
									"    n - p + 1, "+
									"    «columnZerothFaces»(n + 1, n, p, D.dv(n + 1, n + 1, i, x)))"),
							"the front iterate ignores a horizontal face above p",
							By(
								parts[0],
								parts[1],
								parts[2],
								parts[4],
								face,
								dimensions,
								simplicial_homotopy.BisimplicialSet.At(D),
								simplicial_set.FaceIterateTopAbove.At(
									a.TermAs[SimplicialOps[B]]("bisimplicial_row(D, n - p)"),
									n,
									a.TermAs[Nat]("n - p"),
									i,
									a.TermAs[B]("«columnZerothFaces»(n + 1, n, p, D.dv(n + 1, n + 1, i, x))")),
								simplicial_homotopy.BisimplicialRowDef,
								simplicial_set.SimplicialSimplicesDef,
								simplicial_set.SimplicialFaceDef)),
						FinalLeg(
							"the vertical face i − p passes the front iterate",
							Simp(Fwd(AlexanderWhitneyDef), Fwd(dimensions)),
							By(passVertical, passFront, dimensions))))
			})

		commonCorner := ctx.Lemma(Statement{
			Binders: "∀V:module_ops(A, B). ∀D:bisimplicial_ops(B). ∀n p:num. ∀x:B.",
			Hypotheses: []string{
				"bisimplicial_set(D)",
				"x ∈ D.simplices(n + 1, n + 1)",
				"p ≤ n",
			},
			Conclusion: "D.dh(p + 1, n - p, p + 1, alexander_whitney(V, D.dh, D.dv, n + 1, x, p + 1)) = " +
				"D.dv(p, n + 1 - p, 0, alexander_whitney(V, D.dh, D.dv, n + 1, x, p))",
		},
			func(
				a *Argument,
				V *Expr[ModuleOps[A, B]],
				D *Expr[BisimplicialOps[B]],
				n, p *Expr[Nat],
				x *Expr[B],
				given Fact,
			) {
				parts := a.Conjuncts(
					given,
					"the bisimplicial identities",
					"the diagonal simplex",
					"the coordinate is in range")
				dimensions := a.Have(
					"the two neighboring coordinates have matching degrees",
					"p ≤ n + 1 ∧ "+
						"p + 1 ≤ n + 1 ∧ "+
						"n + 1 - (p + 1) = n - p ∧ "+
						"n + 1 - p = n - p + 1 ∧ "+
						"n + 1 - (n - p + 1) = p ∧ "+
						"n + 1 - (n - p) = p + 1 ∧ "+
						"n - p + 1 ≤ n + 1 ∧ "+
						"0 ≤ n - p + 1",
					ByArith(parts[2]))
				backCarrier := a.Have(
					"the back iterate has its expected bidegree",
					"«columnZerothFaces»(n + 1, n + 1, p, x) ∈ D.simplices(n + 1, n + 1 - p)",
					By(
						parts[1],
						dimensions,
						simplicial_homotopy.ColumnFaceIterateBottomIn.Read(parts[0]).At(
							a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 1"), p, x)))
				passFront := a.Have(
					"the vertical face 0 passes the horizontal front iterate",
					"«rowLastFaces»(n - p, "+
						"    n + 1, "+
						"    n - p + 1, "+
						"    D.dv(n + 1, n - p + 1, 0, «columnZerothFaces»(n + 1, n + 1, p, x))) = "+
						"D.dv(p, "+
						"    n - p + 1, "+
						"    0, "+
						"    «rowLastFaces»(n - p + 1, n + 1, n - p + 1, «columnZerothFaces»(n + 1, n + 1, p, x)))",
					By(
						backCarrier,
						dimensions,
						simplicial_homotopy.RowFaceIterateTopVerticalFace.Read(parts[0]).At(
							a.TermAs[Nat]("n + 1"),
							a.TermAs[Nat]("n - p"),
							a.TermAs[Nat]("n - p + 1"),
							a.TermAs[Nat]("0"),
							a.TermAs[B]("«columnZerothFaces»(n + 1, n + 1, p, x)"))))
				successorCorners := a.Have(
					"one more step of each iterate reaches the shared corner",
					"«rowLastFaces»(n - p, n + 1, n - p + 1, «columnZerothFaces»(n + 1, n + 1, p + 1, x)) = "+
						"D.dh(p + 1, "+
						"    n - p, "+
						"    p + 1, "+
						"    «rowLastFaces»(n - p, n + 1, n - p, «columnZerothFaces»(n + 1, n + 1, p + 1, x))) ∧ "+
						"«columnZerothFaces»(n + 1, n + 1, p + 1, x) = "+
						"D.dv(n + 1, n - p + 1, 0, «columnZerothFaces»(n + 1, n + 1, p, x))",
					SplitConj(
						Case(
							"one more front face is the horizontal face p + 1",
							Simp(Fwd(dimensions), Fwd(simplicial_set.FaceIterateTopSucc)),
							Basic()),
						Case(
							"one more back face is the vertical face 0",
							Simp(Fwd(dimensions), Fwd(simplicial_set.FaceIterateBottomSucc)),
							Basic())))
				a.Show(
					"the horizontal face p + 1 of the coordinate p + 1 is the vertical face 0 of the coordinate p",
					Simp(Fwd(AlexanderWhitneyDef), Fwd(dimensions)),
					By(passFront, successorCorners))
			})

		// Two finite sums spliced at a pair of endpoints that cancel.
		spliceSums := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀V:module_ops(A, B). ∀p q:num. ∀F H G:(num → B).",
			Hypotheses: []string{
				"module_on(R, V)",
				"∀i:num. i ≤ p + 1 ⇒ H(i) ∈ V.carrier",
				"∀j:num. j ≤ q + 1 ⇒ G(j) ∈ V.carrier",
				"∀i:num. i ≤ p ⇒ F(i) = H(i)",
				"∀j:num. 1 ≤ j ∧ j ≤ q + 1 ⇒ F(j + p) = G(j)",
				"H(p + 1) + G(0) = V.zero",
			},
			Conclusion: "«spliceAll» = «spliceHorizontal» + «spliceVertical»",
			Abbrev: Abbrev{
				{Name: "spliceAll", Text: "module_sum(V.add, V.zero, 0 .. p + q + 1, F)"},
				{Name: "spliceHorizontal", Text: "module_sum(V.add, V.zero, 0 .. p + 1, H)"},
				{Name: "spliceVertical", Text: "module_sum(V.add, V.zero, 0 .. q + 1, G)"},
				{Name: "spliceLower", Text: "module_sum(V.add, V.zero, 0 .. p, H)"},
				{Name: "spliceTail", Text: "module_sum(V.add, V.zero, 1 .. q + 1, G)"},
			},
		},
			func(
				a *Argument,
				R *Expr[RingOps[A]],
				V *Expr[ModuleOps[A, B]],
				p, q *Expr[Nat],
				F, H, G *Arrow[Nat, B],
				moduleV module.ModuleFact[on.R, on.V],
				hypotheses Fact,
			) {
				given := a.Conjuncts(
					hypotheses,
					"the horizontal summands lie in the module",
					"the vertical summands lie in the module",
					"the lower ranges agree",
					"the translated upper ranges agree",
					"the shared endpoints cancel")
				dimensions := a.Have(
					"the two interval descriptions have the same endpoints",
					"p + (q + 1) = p + q + 1 ∧ 1 + p = p + 1 ∧ q + 1 + p = p + q + 1 ∧ 0 ≤ p + 1",
					ByArith())
				partition := a.Have(
					"the diagonal interval splits at p",
					"0 .. p + q + 1 = (0 .. p) ∪ (p + 1 .. p + q + 1)",
					By(Normalized, dimensions, num_segment.AddSplit.At(a.TermAs[Nat]("0"), p, a.TermAs[Nat]("q + 1"))))
				shiftedTail := a.Have(
					"the upper interval is the vertical tail shifted by p",
					"p + 1 .. p + q + 1 = image(λj:num. j + p, 1 .. q + 1)",
					By(dimensions, num_segment.OffsetImage.At(a.TermAs[Nat]("1"), a.TermAs[Nat]("q + 1"), p)))
				disjointRanges := a.Have(
					"the two pieces of the diagonal interval do not overlap",
					"disjoint(0 .. p, p + 1 .. p + q + 1)",
					Simp(Fwd(num_segment.Disjoint)),
					ByArith())
				shiftInjective := a.Have(
					"the shift by p is injective",
					"injective_on(1 .. q + 1, λj:num. j + p)",
					Unfold(functions.InjectiveOnDef),
					ByArith())
				horizontalInsert := a.Have(
					"the horizontal interval is the lower one with the endpoint p + 1 inserted",
					"0 .. p + 1 = insert(p + 1, 0 .. p)",
					Simp(Rev(nat_arith.Add1)),
					ByArith(num_segment.Rec.At(a.TermAs[Nat]("0"), p)))
				verticalInsert := a.Have(
					"the vertical interval is the tail with the endpoint 0 inserted",
					"0 .. q + 1 = insert(0, 1 .. q + 1)",
					ByArith(num_segment.RecLeft.At(a.TermAs[Nat]("0"), a.TermAs[Nat]("q + 1"))))
				horizontalNew := a.Have(
					"the horizontal endpoint p + 1 is new",
					"p + 1 ∉ 0 .. p",
					Simp(Fwd(num_segment.Membership)),
					ByArith())
				verticalNew := a.Have(
					"the vertical endpoint 0 is new",
					"0 ∉ 1 .. q + 1",
					Simp(Fwd(num_segment.Membership)),
					ByArith())
				lowerIn := a.Have(
					"the lower horizontal range lies in the module",
					"∀i:num. i ∈ 0 .. p ⇒ H(i) ∈ V.carrier",
					Simp(Fwd(num_segment.Membership)),
					ByArith(given[0]))
				tailIn := a.Have(
					"the vertical tail lies in the module",
					"∀j:num. j ∈ 1 .. q + 1 ⇒ G(j) ∈ V.carrier",
					Simp(Fwd(num_segment.Membership)),
					By(given[1]))
				splitIn := a.Have(
					"both pieces of the diagonal range lie in the module",
					"∀i:num. i ∈ 0 .. p ∨ i ∈ p + 1 .. p + q + 1 ⇒ F(i) ∈ V.carrier",
					Simp(Fwd(num_segment.Membership)),
					Derive(func(b *Argument) {
						b.FixAs[Nat]("i")
						piece := b.Assume()
						b.Cases(b.TermAs[Bool]("i ≤ p"))
						b.When(
							"up to p the diagonal summand is the horizontal one",
							func(c *Argument, low Fact) {
								c.Show(
									"a horizontal summand lies in the module",
									ByArith(low, given[0], given[2]))
							})
						b.Otherwise(
							"above p it is the vertical summand at i − p",
							func(c *Argument, high Fact) {
								shift := c.Have(
									"i − p is a vertical index, shifted back to i by p",
									"1 ≤ i - p ∧ i - p ≤ q + 1 ∧ i - p + p = i",
									ByArith(piece, high))
								j := c.TermAs[Nat]("i - p")
								c.Show(
									"a vertical summand lies in the module",
									By(shift, given[1].At(j), given[3].At(j)))
							})
					}))
				shiftedIn := a.Have(
					"the shifted diagonal tail lies in the module",
					"∀j:num. j ∈ 1 .. q + 1 ⇒ F(j + p) ∈ V.carrier",
					Simp(Fwd(num_segment.Membership)),
					By(Normalized, given[1], given[3]))
				horizontalEndIn := a.Have(
					"the horizontal endpoint p + 1 lies in the module",
					"H(p + 1) ∈ V.carrier",
					ByArith(given[0]))
				verticalEndIn := a.Have(
					"the vertical endpoint 0 lies in the module",
					"G(0) ∈ V.carrier",
					ByArith(given[1]))
				endpointSums := a.Have(
					"the horizontal and vertical sums split off their shared endpoints",
					"«spliceHorizontal» = H(p + 1) + «spliceLower» ∧ «spliceVertical» = G(0) + «spliceTail»",
					SplitConj(
						Case(
							"extract the horizontal term p + 1",
							Simp(Fwd(horizontalInsert)),
							By(
								moduleV,
								lowerIn,
								horizontalEndIn,
								horizontalNew,
								num_segment.Finite.At(a.TermAs[Nat]("0"), p),
								module.ModuleSumInsert.At(R, V, a.TermAs[Set[Nat]]("0 .. p"), a.TermAs[Nat]("p + 1"), H))),
						Case(
							"extract the vertical term 0",
							Simp(Fwd(verticalInsert)),
							By(
								moduleV,
								tailIn,
								verticalEndIn,
								verticalNew,
								num_segment.Finite.At(a.TermAs[Nat]("1"), a.TermAs[Nat]("q + 1")),
								module.ModuleSumInsert.At(R, V, a.TermAs[Set[Nat]]("1 .. q + 1"), a.TermAs[Nat]("0"), G)))))
				reindexedSums := a.Have(
					"the two diagonal pieces are the lower horizontal sum and the vertical tail",
					"module_sum(V.add, V.zero, 0 .. p, F) = «spliceLower» ∧ "+
						"module_sum(V.add, V.zero, p + 1 .. p + q + 1, F) = «spliceTail»",
					SplitConj(
						Case(
							"identify the lower range term by term",
							By(
								given[2],
								num_segment.MembershipFromZero,
								module.ModuleSumCongruence.At(
									a.TermAs[Op[B]]("V.add"), a.TermAs[B]("V.zero"), a.TermAs[Set[Nat]]("0 .. p"), F, H))),
						Case(
							"translate and identify the upper range",
							CalcEq(
								Leg(
									a.TermAs[B]("module_sum(V.add, V.zero, 1 .. q + 1, λj:num. F(j + p))"),
									"translate the tail indices",
									Simp(Fwd(shiftedTail)),
									By(
										shiftedIn,
										shiftInjective,
										moduleV,
										num_segment.Finite.At(a.TermAs[Nat]("1"), a.TermAs[Nat]("q + 1")),
										module.ModuleSumImage.At(
											R, V, a.TermAs[Set[Nat]]("1 .. q + 1"), a.TermAs[Fun[Nat, Nat]]("λj:num. j + p"), F))),
								FinalLeg(
									"the translated upper summands agree",
									By(
										given[3],
										num_segment.Membership,
										module.ModuleSumCongruence.At(
											a.TermAs[Op[B]]("V.add"),
											a.TermAs[B]("V.zero"),
											a.TermAs[Set[Nat]]("1 .. q + 1"),
											a.TermAs[Fun[Nat, B]]("λj:num. F(j + p)"),
											G)))))))
				splitSum := a.Have(
					"the diagonal sum is the sum of the two nonshared ranges",
					"«spliceAll» = «spliceLower» + «spliceTail»",
					Simp(Fwd(partition)),
					By(
						splitIn,
						disjointRanges,
						moduleV,
						reindexedSums,
						num_segment.Finite.At(a.TermAs[Nat]("0"), p),
						num_segment.Finite.At(a.TermAs[Nat]("p + 1"), a.TermAs[Nat]("p + q + 1")),
						module.ModuleSumDisjointUnion.At(
							R, V, a.TermAs[Set[Nat]]("0 .. p"), a.TermAs[Set[Nat]]("p + 1 .. p + q + 1"), F)))
				partialSumsIn := a.Have(
					"both nonshared partial sums lie in the module",
					"«spliceLower» ∈ V.carrier ∧ «spliceTail» ∈ V.carrier",
					SplitConj(
						Case(
							"the lower sum lies in the module",
							By(
								moduleV,
								lowerIn,
								num_segment.Finite.At(a.TermAs[Nat]("0"), p),
								module.ModuleSumIn.At(R, V, a.TermAs[Set[Nat]]("0 .. p"), H))),
						Case(
							"the tail sum lies in the module",
							By(
								moduleV,
								tailIn,
								num_segment.Finite.At(a.TermAs[Nat]("1"), a.TermAs[Nat]("q + 1")),
								module.ModuleSumIn.At(R, V, a.TermAs[Set[Nat]]("1 .. q + 1"), G)))))
				a.Show(
					"the shared endpoints cancel and leave the two ranges",
					Simp(Fwd(splitSum), Fwd(endpointSums)),
					ByChase(Depth(0), moduleV, verticalEndIn, horizontalEndIn, partialSumsIn, given[4]))
			})

		// The weighted face ranges give the coordinate boundary identity.
		coordinateBoundary := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀V:module_ops(A, B). ∀D:bisimplicial_ops(B). ∀p q:num. ∀x:B.",
			Hypotheses: []string{
				"bisimplicial_module(R, V, D)",
				"x ∈ D.simplices(p + q + 1, p + q + 1)",
			},
			Conclusion: "«awCurrent»(«diagonalBoundary», p) = " +
				"«horizontalBoundary» + alternating_sign(p) • «verticalBoundary»",
			Abbrev: Abbrev{
				{Name: "awNext", Text: "alexander_whitney(V, D.dh, D.dv, p + q + 1, x)"},
				{Name: "awCurrent", Text: "alexander_whitney(V, D.dh, D.dv, p + q)"},
				{Name: "diagonalFaces", Text: "λi:num. " +
					"    D.dh(p + q + 1, p + q, i, D.dv(p + q + 1, p + q + 1, i, x))"},
				{Name: "horizontalFaces", Text: "λi:num. D.dh(p + 1, q, i, «awNext»(p + 1))"},
				{Name: "verticalFaces", Text: "λj:num. D.dv(p, q + 1, j, «awNext»(p))"},
				{Name: "weightedDiagonal", Text: "λi:num. " +
					"    alternating_sign(i) • «awCurrent»(«diagonalFaces»(i), p)"},
				{Name: "weightedHorizontal", Text: "λi:num. alternating_sign(i) • «horizontalFaces»(i)"},
				{Name: "weightedVertical", Text: "λj:num. " +
					"    alternating_sign(p) • (alternating_sign(j) • «verticalFaces»(j))"},
				{Name: "diagonalBoundary", Text: "face_boundary(R, " +
					"    V, " +
					"    bisimplicial_diagonal_face(D.dh, D.dv), " +
					"    p + q + 1, " +
					"    x)"},
				{Name: "horizontalBoundary", Text: "face_boundary(R, " +
					"    V, " +
					"    λm:num. λi:num. D.dh(m, q, i), " +
					"    p + 1, " +
					"    «awNext»(p + 1))"},
				{Name: "verticalBoundary", Text: "face_boundary(R, " +
					"    V, " +
					"    λm:num. λj:num. D.dv(p, m, j), " +
					"    q + 1, " +
					"    «awNext»(p))"},
			},
		},
			func(
				a *Argument,
				R *Expr[RingOps[A]],
				V *Expr[ModuleOps[A, B]],
				D *Expr[BisimplicialOps[B]],
				p, q *Expr[Nat],
				x *Expr[B],
				hypotheses Fact,
			) {
				given := a.Conjuncts(
					hypotheses,
					"the bisimplicial module",
					"the diagonal simplex")
				bisimplicialSet := BisimplicialUnderlyingSet.Read(given[0])
				ring := module.RingOn.Read(BisimplicialAmbientModule.Read(given[0]))
				dimensions := a.Have(
					"the neighboring bidegrees and the diagonal total degree align",
					"p ≤ p + q ∧ "+
						"p ≤ p + q + 1 ∧ "+
						"p + 1 ≤ p + q + 1 ∧ "+
						"p + q - p = q ∧ "+
						"p + q + 1 - p = q + 1 ∧ "+
						"p + q + 1 - (p + 1) = q ∧ "+
						"p + q + 1 - 1 = p + q ∧ "+
						"p + (q + 1) = p + q + 1 ∧ "+
						"q + 1 + p = p + q + 1",
					ByArith())
				signs := a.Have(
					"the signs lie in the coefficient ring and adjacent signs cancel",
					"∀k:num. alternating_sign(k) ∈ R.carrier ∧ alternating_sign(k + 1) + alternating_sign(k) = R.zero",
					By(comm_ring.AlternatingSignIn.Read(ring), comm_ring.AlternatingSignSuc.Read(ring)))
				coordinateMap := a.Have(
					"the coordinate map at p is linear into bidegree (p, q)",
					"module_homomorphism(R, "+
						"    restrict_module(V, D.simplices(p + q, p + q)), "+
						"    restrict_module(V, D.simplices(p, q)), "+
						"    λy:B. «awCurrent»(y, p))",
					By(dimensions, given[0], At(coordinateHom, R, V, D, a.TermAs[Nat]("p + q"), p)))
				neighborCarriers := a.Have(
					"the neighboring coordinates lie in their bidegrees",
					"«awNext»(p + 1) ∈ D.simplices(p + 1, q) ∧ «awNext»(p) ∈ D.simplices(p, q + 1)",
					SplitConj(
						Case(
							"the coordinate p + 1 lies in bidegree (p + 1, q)",
							By(
								given[1],
								dimensions,
								given[0],
								At(coordinateHom, R, V, D, a.TermAs[Nat]("p + q + 1"), a.TermAs[Nat]("p + 1")),
								module_homomorphism.HomIn)),
						Case(
							"the coordinate p lies in bidegree (p, q + 1)",
							By(
								given[1],
								dimensions,
								given[0],
								At(coordinateHom, R, V, D, a.TermAs[Nat]("p + q + 1"), p),
								module_homomorphism.HomIn))))
				// A face linear between two bidegrees under its index bound
				// carries each simplex of the first into the second.
				placed := func(b *Argument, linear Fact, y *Expr[B], member Fact) {
					face := b.Simplified(GroupPremises(b.Assume(), linear))
					b.Show(
						"linearity places the face in its target carrier",
						By(member, module_homomorphism.HomIn.Read(face).AsFact().At(y)))
				}
				diagonalIn := a.Have(
					"each diagonal face lies in the previous diagonal degree",
					"∀i:num. i ≤ p + q + 1 ⇒ «diagonalFaces»(i) ∈ D.simplices(p + q, p + q)",
					Derive(func(b *Argument) {
						i := b.FixAs[Nat]("i")
						placed(b, DiagonalFaceHom.Read(given[0]).At(b.TermAs[Nat]("p + q"), i), x, given[1])
					}))
				horizontalIn := a.Have(
					"each horizontal face of the coordinate p + 1 lies in bidegree (p, q)",
					"∀i:num. i ≤ p + 1 ⇒ «horizontalFaces»(i) ∈ D.simplices(p, q)",
					Derive(func(b *Argument) {
						i := b.FixAs[Nat]("i")
						placed(
							b,
							BisimplicialHorizontalHom.Read(given[0]).At(p, q, i),
							b.TermAs[B]("«awNext»(p + 1)"),
							neighborCarriers)
					}))
				verticalIn := a.Have(
					"each vertical face of the coordinate p lies in bidegree (p, q)",
					"∀j:num. j ≤ q + 1 ⇒ «verticalFaces»(j) ∈ D.simplices(p, q)",
					Derive(func(b *Argument) {
						j := b.FixAs[Nat]("j")
						placed(
							b, BisimplicialVerticalHom.Read(given[0]).At(p, q, j), b.TermAs[B]("«awNext»(p)"), neighborCarriers)
					}))
				commonModule := module_homomorphism.HomTarget.Read(coordinateMap)
				weightedCarriers := a.Have(
					"the weighted horizontal and vertical face families lie in the common module",
					"(∀i:num. i ≤ p + 1 ⇒ «weightedHorizontal»(i) ∈ D.simplices(p, q)) ∧ "+
						"(∀j:num. j ≤ q + 1 ⇒ «weightedVertical»(j) ∈ D.simplices(p, q))",
					SplitConj(
						Case(
							"the weighted horizontal faces lie in the common module",
							By(module.SmulIn.Read(commonModule), signs, horizontalIn)),
						Case(
							"the weighted vertical faces lie in the common module",
							By(module.SmulIn.Read(commonModule), signs, verticalIn))))
				lowerRange := a.Have(
					"the lower weighted diagonal range is the horizontal range",
					"∀i:num. i ≤ p ⇒ «weightedDiagonal»(i) = «weightedHorizontal»(i)",
					Derive(func(b *Argument) {
						i := b.FixAs[Nat]("i")
						bound := b.Assume()
						b.Show(
							"the lower face identity preserves its sign",
							By(
								bound,
								bisimplicialSet,
								given[1],
								dimensions,
								At(lowerFaces, V, D, b.TermAs[Nat]("p + q"), p, i, x)))
					}))
				upperRange := a.Have(
					"the translated upper weighted diagonal range is the signed vertical tail",
					"∀j:num. 1 ≤ j ∧ j ≤ q + 1 ⇒ «weightedDiagonal»(j + p) = «weightedVertical»(j)",
					Derive(func(b *Argument) {
						j := b.FixAs[Nat]("j")
						bound := b.Assume()
						indices := b.Have(
							"the translated face lies above p with the required shifted index",
							"p < j + p ∧ j + p ≤ p + q + 1 ∧ j + p - p = j ∧ j + p = p + j",
							ByArith(bound))
						face := b.Have(
							"the upper diagonal face is the corresponding vertical face of the coordinate",
							"«awCurrent»(«diagonalFaces»(j + p), p) = «verticalFaces»(j)",
							By(
								bisimplicialSet,
								given[1],
								dimensions,
								indices,
								At(upperFaces, V, D, b.TermAs[Nat]("p + q"), p, b.TermAs[Nat]("j + p"), x)))
						coefficient := b.Have(
							"the translated sign is the product of the two signs",
							"alternating_sign(j + p) = alternating_sign(p) * alternating_sign(j)",
							By(indices, comm_ring.AlternatingSignAdd.Read(ring).At(p, j)))
						b.Show(
							"scalar associativity supplies the sign on the vertical tail",
							By(
								bound,
								signs.At(p),
								signs.At(j),
								verticalIn.At(j),
								face,
								coefficient,
								module.SmulMul.Read(commonModule).AsFact().At(
									b.TermAs[A]("alternating_sign(p)"),
									b.TermAs[A]("alternating_sign(j)"),
									b.TermAs[B]("«verticalFaces»(j)"))))
					}))
				cornerCancels := a.Have(
					"the horizontal term p + 1 cancels the signed vertical term 0",
					"«weightedHorizontal»(p + 1) + «weightedVertical»(0) = V.zero",
					Derive(func(b *Argument) {
						corner := b.Have(
							"the two boundary endpoints are one simplex",
							"«horizontalFaces»(p + 1) = «verticalFaces»(0)",
							By(bisimplicialSet, given[1], dimensions, At(commonCorner, V, D, b.TermAs[Nat]("p + q"), p, x)))
						cornerIn := b.Have(
							"the shared corner lies in the common bidegree",
							"«verticalFaces»(0) ∈ D.simplices(p, q)",
							ByArith(verticalIn))
						cornerSign := b.Have(
							"the vertical corner carries alternating_sign(p) alone",
							"«weightedVertical»(0) = alternating_sign(p) • «verticalFaces»(0)",
							Simp(Fwd(comm_ring.AlternatingSignDef), Fwd(module.SmulOne.Read(commonModule))),
							Basic())
						b.Show(
							"adjacent coefficients on the shared corner sum to zero",
							Simp(Fwd(corner), Fwd(cornerSign)),
							CalcEq(
								Leg(
									b.TermAs[B]("(alternating_sign(p + 1) + alternating_sign(p)) • «verticalFaces»(0)"),
									"combine the coefficients on the common corner",
									By(
										signs.At(p),
										signs.At(b.TermAs[Nat]("p + 1")),
										cornerIn,
										module.SmulAddRight.Read(commonModule).AsFact().At(
											b.TermAs[A]("alternating_sign(p + 1)"),
											b.TermAs[A]("alternating_sign(p)"),
											b.TermAs[B]("«verticalFaces»(0)")))),
								FinalLeg(
									"adjacent signs cancel",
									Simp(Fwd(signs), Fwd(module.ZeroSmul.Read(commonModule))),
									Basic())))
					}))
				spliced := a.Have(
					"the diagonal weighted sum splices into the boundary sums of the two coordinates",
					"module_sum(V.add, V.zero, 0 .. p + q + 1, «weightedDiagonal») = "+
						"module_sum(V.add, V.zero, 0 .. p + 1, «weightedHorizontal») + "+
						"module_sum(V.add, V.zero, 0 .. q + 1, «weightedVertical»)",
					By(
						lowerRange,
						upperRange,
						cornerCancels,
						commonModule,
						weightedCarriers,
						At(
							spliceSums,
							R,
							a.TermAs[ModuleOps[A, B]]("restrict_module(V, D.simplices(p, q))"),
							p,
							q,
							a.TermAs[Fun[Nat, B]]("«weightedDiagonal»"),
							a.TermAs[Fun[Nat, B]]("«weightedHorizontal»"),
							a.TermAs[Fun[Nat, B]]("«weightedVertical»"))))
				diagonalGuards := a.Have(
					"the diagonal sum's coefficients and faces meet their guards",
					Statement{
						Binders:    "∀i:num.",
						Hypotheses: []string{"i ∈ 0 .. p + q + 1"},
						Conclusion: "alternating_sign(i) ∈ R.carrier ∧ «diagonalFaces»(i) ∈ D.simplices(p + q, p + q)",
					},
					Simp(Fwd(num_segment.MembershipFromZero)),
					By(diagonalIn, signs))
				verticalGuards := a.Have(
					"the weighted vertical summands lie in the common bidegree",
					"∀j:num. j ∈ 0 .. q + 1 ⇒ alternating_sign(j) • «verticalFaces»(j) ∈ D.simplices(p, q)",
					Simp(Fwd(num_segment.MembershipFromZero)),
					By(module.SmulIn.Read(commonModule), verticalIn, signs))
				linearity := a.Have(
					"the coordinate map carries the diagonal face sum to its weighted image sum",
					"«awCurrent»(module_sum(V.add, "+
						"        V.zero, "+
						"        0 .. p + q + 1, "+
						"        λi:num. alternating_sign(i) • «diagonalFaces»(i)), "+
						"    p) = "+
						"module_sum(V.add, V.zero, 0 .. p + q + 1, «weightedDiagonal»)",
					By(
						diagonalGuards,
						num_segment.Finite.At(a.TermAs[Nat]("0"), a.TermAs[Nat]("p + q + 1")),
						module_homomorphism.HomCombination.Read(coordinateMap).At(
							a.TermAs[Set[Nat]]("0 .. p + q + 1"),
							a.TermAs[Fun[Nat, A]]("alternating_sign"),
							a.TermAs[Fun[Nat, B]]("«diagonalFaces»"))))
				boundarySums := a.Have(
					"the three face boundaries are exactly the corresponding weighted sums",
					"(«diagonalBoundary» = "+
						"    module_sum(V.add, "+
						"        V.zero, "+
						"        0 .. p + q + 1, "+
						"        λi:num. alternating_sign(i) • «diagonalFaces»(i))) ∧ "+
						"(«horizontalBoundary» = module_sum(V.add, V.zero, 0 .. p + 1, «weightedHorizontal»)) ∧ "+
						"(alternating_sign(p) • «verticalBoundary» = "+
						"    module_sum(V.add, V.zero, 0 .. q + 1, «weightedVertical»))",
					SplitConjAll(
						Case(
							"recognize the diagonal face sum",
							Simp(Fwd(FaceBoundaryDef), Fwd(dimensions), Fwd(simplicial_homotopy.BisimplicialDiagonalFaceDef)),
							Basic()),
						Case(
							"recognize the horizontal face sum",
							Simp(Fwd(FaceBoundaryDef)),
							Basic()),
						Case(
							"recognize the signed vertical face sum",
							Simp(Fwd(FaceBoundaryDef)),
							By(
								commonModule,
								verticalGuards,
								signs.At(p),
								num_segment.Finite.At(a.TermAs[Nat]("0"), a.TermAs[Nat]("q + 1")),
								module.ModuleSumSmul.At(
									R,
									a.TermAs[ModuleOps[A, B]]("restrict_module(V, D.simplices(p, q))"),
									a.TermAs[Set[Nat]]("0 .. q + 1"),
									a.TermAs[A]("alternating_sign(p)"),
									a.TermAs[Fun[Nat, B]]("λj:num. alternating_sign(j) • «verticalFaces»(j)"))))))
				a.Show(
					"linearity and the splice of the weighted sums give the coordinate boundary identity",
					By(spliced, linearity, boundarySums))
			})

		// The degree map at n is a homomorphism into the total degree n.
		degreeHom := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀V:module_ops(A, B). " +
				"∀D:bisimplicial_ops(B). " +
				"∀h v:(num → num → B → B). " +
				"∀n:num.",
			Hypotheses: []string{
				"bisimplicial_module(R, V, D)",
			},
			Conclusion: "module_homomorphism(R, «awSourceModule», «awTargetModule», «awDegree»)",
			Abbrev: Abbrev{
				{Name: "awTotalComplex", Text: "double_total(V, D.simplices, h, v, alternating_sign)"},
				{Name: "awSourceModule", Text: "restrict_module(V, D.simplices(n, n))"},
				{Name: "awTargetModule", Text: "complex_module(«awTotalComplex», n)"},
				{Name: "awDegree", Text: "alexander_whitney(V, D.dh, D.dv, n)"},
			},
		},
			func(
				a *Argument,
				R *Expr[RingOps[A]],
				V *Expr[ModuleOps[A, B]],
				D *Expr[BisimplicialOps[B]],
				h, v *Expr[Fun3[Nat, Nat, B, B]],
				n *Expr[Nat],
				bisimplicial BisimplicialModuleFact[on.R, on.V],
			) {
				moduleV := BisimplicialAmbientModule.Read(bisimplicial)
				submodules := BisimplicialSubmodules.Read(bisimplicial)
				// The coordinate map at p ≤ n, linear into its bidegree: each
				// branch below reads it at its own p.
				coordinate := func(b *Argument, p *Expr[Nat], bound Fact) Fact {
					return b.Have(
						"the coordinate map at p is linear into its bidegree",
						"module_homomorphism(R, "+
							"    «awSourceModule», "+
							"    restrict_module(V, D.simplices(p, n - p)), "+
							"    λx:B. «awDegree»(x, p))",
						By(bound, bisimplicial, At(coordinateHom, R, V, D, n, p)))
				}
				a.Show(
					"the coordinate maps assemble to a homomorphism into the total degree",
					Simp(Fwd(module_homomorphism.ModuleHomomorphismDef)),
					SplitConjAll(
						Case(
							"the diagonal source is a module",
							By(
								moduleV,
								submodules.At(n, n),
								submodule.SubmoduleModuleOn.At(R, V, a.TermAs[Set[B]]("D.simplices(n, n)")))),
						Case(
							"the total-degree target is a module",
							By(
								submodules,
								moduleV,
								chain_complex.DoubleTotalModule.At(
									R,
									V,
									a.TermAs[Fun3[Nat, Nat, B, Bool]]("D.simplices"),
									h,
									v,
									a.TermAs[Fun[Nat, A]]("alternating_sign"),
									n))),
						Case(
							"the image has the required bidegrees and finite support",
							Derive(func(b *Argument) {
								u := b.FixAs[B]("u")
								inSource := b.Assume()
								b.Show(
									"each coordinate has its bidegree and the tail is zero",
									Simp(Fwd(chain_complex.DoubleTotalTermsMember)),
									SplitConj(
										Case(
											"coordinates in range land in their bidegrees",
											Derive(func(c *Argument) {
												p := c.FixAs[Nat]("p")
												bound := c.Assume()
												c.Show(
													"the source simplex maps into the carrier of the coordinate",
													By(inSource, module_homomorphism.HomIn.Read(coordinate(c, p, bound)).AsFact().At(u)))
											})),
										Case(
											"coordinates past n vanish",
											By(At(coordinatePast, V, D, n)))))
							})),
						Case(
							"the degree map preserves addition coordinate by coordinate",
							Derive(func(b *Argument) {
								u := b.FixAs[B]("u")
								w := b.FixAs[B]("w")
								inSource := b.Assume()
								b.Do(Funext())
								p := b.FixAs[Nat]("p")
								b.Cases(b.TermAs[Bool]("p ≤ n"))
								b.When(
									"coordinates in range preserve addition by their linearity",
									func(c *Argument, bound Fact) {
										c.Show(
											"this coordinate carries the sum to the sum of the coordinates",
											By(inSource, module_homomorphism.HomAdd.Read(coordinate(c, p, bound)).AsFact().At(u, w)))
									})
								b.Otherwise(
									"the zero tail preserves addition",
									func(c *Argument, beyond Fact) {
										past := c.Simplified(beyond, Fwd(nat_order.NotLessEq))
										c.Show(
											"two zero coordinates add to zero",
											By(
												past,
												At(coordinatePast, V, D, n, p),
												group.OneIn.Read(module.AddGroupOn.Read(moduleV)),
												group.LeftIdentityOn.Read(module.AddGroupOn.Read(moduleV))))
									})
							})),
						Case(
							"the degree map preserves scalar multiplication coordinate by coordinate",
							Derive(func(b *Argument) {
								c := b.FixAs[A]("c")
								u := b.FixAs[B]("u")
								inSource := b.Assume()
								b.Do(Funext())
								p := b.FixAs[Nat]("p")
								b.Cases(b.TermAs[Bool]("p ≤ n"))
								b.When(
									"coordinates in range preserve scaling by their linearity",
									func(d *Argument, bound Fact) {
										d.Show(
											"this coordinate carries a scalar multiple to the scalar multiple of the coordinate",
											By(inSource, module_homomorphism.HomSmul.Read(coordinate(d, p, bound)).AsFact().At(c, u)))
									})
								b.Otherwise(
									"the zero tail preserves scaling",
									func(d *Argument, beyond Fact) {
										past := d.Simplified(beyond, Fwd(nat_order.NotLessEq))
										d.Show(
											"a scalar multiple of a zero coordinate is zero",
											By(past, At(coordinatePast, V, D, n, p), module.SmulZero.Read(moduleV), inSource))
									})
							}))))
			})

		return ctx.Theorem(headline, func(
			a *Argument,
			R *Expr[RingOps[A]],
			V *Expr[ModuleOps[A, B]],
			D *Expr[BisimplicialOps[B]],
			bisimplicial BisimplicialModuleFact[on.R, on.V],
		) {
			commutes := a.Have(
				"the degree maps commute with the differentials, the "+
					"diagonal's being the face boundary of its faces dh_i ∘ dv_i",
				Statement{
					Binders:    "∀n:num. ∀u:B.",
					Hypotheses: []string{"u ∈ bisimplicial_diagonal_simplices(D, n + 1)"},
					Conclusion: "alexander_whitney(V, " +
						"    D.dh, " +
						"    D.dv, " +
						"    n, " +
						"    face_boundary(R, V, bisimplicial_diagonal_face(D.dh, D.dv), n + 1, u)) = " +
						"double_boundary(V, " +
						"    «horizontalBoundaryFamily», " +
						"    «verticalBoundaryFamily», " +
						"    alternating_sign, " +
						"    n + 1, " +
						"    alexander_whitney(V, D.dh, D.dv, n + 1, u))",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					u := b.FixAs[B]("u")
					horizontal := b.TermAs[Fun3[Nat, Nat, B, B]]("«horizontalBoundaryFamily»")
					vertical := b.TermAs[Fun3[Nat, Nat, B, B]]("«verticalBoundaryFamily»")
					sign := b.TermAs[Fun[Nat, A]]("alternating_sign")
					image := b.TermAs[Fun[Nat, B]]("alexander_whitney(V, D.dh, D.dv, n + 1, u)")
					inDiagonal := b.Simplified(b.Assume(), Fwd(simplicial_homotopy.BisimplicialDiagonalSimplicesDef))
					b.Do(Funext())
					p := b.FixAs[Nat]("p")
					b.Cases(b.TermAs[Bool]("p ≤ n"))
					b.When(
						"coordinates in range satisfy the signed boundary identity",
						func(c *Argument, bound Fact) {
							dimensions := c.Have(
								"the coordinate and complementary degree sum to n",
								"p + (n - p) = n",
								ByArith(bound))
							c.Show(
								"the two boundary coordinates agree",
								By(
									inDiagonal,
									dimensions,
									bisimplicial,
									chain_complex.DoubleBoundaryCoordinate.At(
										V, horizontal, vertical, sign, p, c.TermAs[Nat]("n - p"), image),
									At(coordinateBoundary, R, V, D, p, c.TermAs[Nat]("n - p"), u)))
						})
					b.Otherwise(
						"coordinates past the diagonal degree vanish on both sides",
						func(c *Argument, beyond Fact) {
							past := c.Simplified(beyond, Fwd(nat_order.NotLessEq))
							c.Show(
								"both sides are zero past n",
								By(
									past,
									At(coordinatePast, V, D, n, p),
									chain_complex.DoubleBoundaryPast.At(V, horizontal, vertical, sign, n, p, image)))
						})
				}))
			a.Show(
				"the degreewise homomorphisms commute with the two boundaries",
				Simp(Fwd(chain_complex.ChainMapDef)),
				SplitConj(
					Case(
						"every degree map is a homomorphism",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]("n")
							b.Show(
								"the face complex's module in degree n is cut out by the (n, "+
									"n)-simplices, which the degree map carries into the total degree n",
								Simp(Fwd(FaceComplexModule), Fwd(simplicial_homotopy.BisimplicialDiagonalSimplicesDef)),
								By(
									bisimplicial,
									At(
										degreeHom,
										R,
										V,
										D,
										b.TermAs[Fun3[Nat, Nat, B, B]]("«horizontalBoundaryFamily»"),
										b.TermAs[Fun3[Nat, Nat, B, B]]("«verticalBoundaryFamily»"),
										n)))
						})),
					Case(
						"the degree maps commute with the differentials",
						By(commutes))))
		})
	}),
})}

// AlexanderWhitneyNatural — the Alexander–Whitney map is natural in maps
// of bisimplicial sets that keep zero on the bottom row: on an
// (n, n)-simplex, the map after F is F, coordinate by coordinate, after
// the map.
var AlexanderWhitneyNatural = alexanderWhitneyNaturalThm{family.Add(registry.ProofEntry{
	Name: "AlexanderWhitneyNatural",
	Key:  "prop_b7e06ef31cfe9131",
	Reading: "On the coordinates p ≤ n only bisimplicial_map is read: F's commuting with " +
		"the horizontal and vertical faces, and bisimplicial_set(D), its first conjunct, for " +
		"the memberships each commuting step asks. The zero hypothesis is load-bearing past " +
		"n and nowhere else: there the left side is V'.zero, the definition's tail, and the " +
		"right side is F(p, 0, V.zero), n − p truncating to 0, so without it the two sides " +
		"differ at every p > n. A linear F, each F(p, 0) a homomorphism of the restricted " +
		"modules, keeps zero there (HomZero). At n = 0 the coordinate 0 is F(0, 0, x) on " +
		"both sides. No module axiom of V or V' is read: they enter through their zeros alone.",
	Deps: []registry.EntryLike{
		AlexanderWhitneyDef,
		simplicial_homotopy.BisimplicialMap,
		chain_complex.DoubleTotalMapDef,
		simplicial_set.FaceIterateBottomDef,
		simplicial_set.FaceIterateTopDef,
		simplicial_homotopy.ColumnFaceIterateBottomIn,
		simplicial_homotopy.RowFaceIterateTopIn,
		set_basic.Extension,
	},
	Build: family.Card(Statement{
		Binders: "∀V:module_ops(A, B). " +
			"∀D:bisimplicial_ops(B). " +
			"∀V':module_ops(A, C). " +
			"∀D':bisimplicial_ops(C). " +
			"∀F:(num → num → B → C). " +
			"∀n:num. " +
			"∀x:B.",
		Hypotheses: []string{
			"bisimplicial_map(D, D', F)",
			"∀p:num. F(p, 0, V.zero) = V'.zero",
			"x ∈ D.simplices(n, n)",
		},
		Conclusion: "alexander_whitney(V', D'.dh, D'.dv, n, F(n, n, x)) = " +
			"double_total_map(F, n, alexander_whitney(V, D.dh, D.dv, n, x))",
	},
		"extensionality at each coordinate p (Extension), the right side F(p, n − p) of the "+
			"coordinate p (DoubleTotalMapDef). For p ≤ n both sides are F(p, n − p) of the front face "+
			"of the back face of x (AlexanderWhitneyDef): by induction along each iterate "+
			"(FaceIterateBottomDef, FaceIterateTopDef), F passes one face at a time, commuting with "+
			"every horizontal and vertical face on the simplices (BisimplicialMap), each intermediate "+
			"face of x lying in its D(p', q') (ColumnFaceIterateBottomIn, RowFaceIterateTopIn, at the "+
			"bisimplicial_set(D) that BisimplicialMap carries). Past n the left side is V'.zero and "+
			"the right side F(p, 0, V.zero), n − p truncating to 0, which the hypothesis makes V'.zero"),
})}

// AlexanderWhitneyConstantVertical — when the 0-th vertical face of the
// column n of a bisimplicial set fixes its simplices, the
// Alexander–Whitney map reads the coordinate n of an (n, n)-simplex z, in
// bidegree (n, 0), as z itself.
var AlexanderWhitneyConstantVertical = alexanderWhitneyConstantVerticalThm{family.Add(registry.ProofEntry{
	Name: "AlexanderWhitneyConstantVertical",
	Key:  "prop_407a67792763291a",
	Reading: "The coordinate n is (dv_0)^n z, no horizontal face being taken, so the edge of " +
		"chain_complex's AugmentedAssembly, double_edge(a), which reads the coordinate n, reads a(n, z) " +
		"after the map: on a bisimplicial module with identity vertical faces the Alexander–Whitney map " +
		"is a section of the edge. The face hypothesis is load-bearing: each of the n steps of (dv_0)^n " +
		"z applies it, at the column n in a vertical degree q + 1 ≤ n, and without it the coordinate n " +
		"is an arbitrary iterated face of z. It is asked on the simplices of the column n in every " +
		"vertical degree, though the route reads it at q + 1 ≤ n alone. bisimplicial_set(D) is read only " +
		"for the closure of the column n, which keeps z, once fixed, in the next lower vertical degree, " +
		"where the hypothesis applies again. At n = 0 no face is taken and the coordinate 0 is z by the " +
		"definition alone; V enters only through V.zero past n, which the coordinate n never reaches.",
	Deps: []registry.EntryLike{
		AlexanderWhitneyDef,
		simplicial_set.FaceIterateTopDef,
		simplicial_set.FaceIterateBottomDef,
		simplicial_homotopy.BisimplicialSet,
		simplicial_homotopy.ColumnFaceIterateBottomIn,
	},
	Build: family.Card(Statement{
		Binders: "∀V:module_ops(A, B). ∀D:bisimplicial_ops(B). ∀n:num. ∀z:B.",
		Hypotheses: []string{
			"bisimplicial_set(D)",
			"∀q:num. ∀x:B. x ∈ D.simplices(n, q + 1) ⇒ D.dv(n, q + 1, 0, x) = x",
			"z ∈ D.simplices(n, n)",
		},
		Conclusion: "alexander_whitney(V, D.dh, D.dv, n, z, n) = z",
	},
		"at p = n the horizontal front face is taken zero times, n − n = 0 (AlexanderWhitneyDef, "+
			"FaceIterateTopDef), leaving (dv_0)^n z (FaceIterateBottomDef); by induction on k ≤ n, (dv_0)^k "+
			"z = z: the iterate lies in D(n, n − k) (ColumnFaceIterateBottomIn), so it is z in D(n, n − k), "+
			"and for n − k = q + 1 ≥ 1 the next 0-th face, D.dv(n, q + 1, 0), fixes it by the hypothesis"),
})}

// AlexanderWhitneyConstantHorizontal — when the last horizontal face of
// the row n of a bisimplicial set fixes its simplices, the
// Alexander–Whitney map reads the coordinate 0 of an (n, n)-simplex y, in
// bidegree (0, n), as y itself.
var AlexanderWhitneyConstantHorizontal = alexanderWhitneyConstantHorizontalThm{family.Add(registry.ProofEntry{
	Name: "AlexanderWhitneyConstantHorizontal",
	Key:  "prop_c63095307af2e75d",
	Reading: "The coordinate 0, in bidegree (0, n), is the horizontal front 0-face dh_1 ∘ ⋯ " +
		"∘ dh_n y, no vertical face being taken, so reading the coordinate 0 of the total, as " +
		"chain_complex's AugmentedAssemblyRows does, gives y back. The face hypothesis is " +
		"load-bearing: each of the n steps applies it, at the row n in a horizontal degree p + " +
		"1 ≤ n, and without it the coordinate 0 is an arbitrary iterated face of y. It is asked " +
		"on the simplices of the row n in every horizontal degree, though the route reads it at " +
		"p + 1 ≤ n alone. bisimplicial_set(D) is read only for the closure of the row n, which " +
		"keeps y, once fixed, in the next lower horizontal degree, where the hypothesis applies " +
		"again. At n = 0 no face is taken and the coordinate 0 is y by the definition alone; V " +
		"enters only through V.zero past n, which the coordinate 0 never reaches.",
	Deps: []registry.EntryLike{
		AlexanderWhitneyDef,
		simplicial_set.FaceIterateTopDef,
		simplicial_set.FaceIterateBottomDef,
		simplicial_homotopy.BisimplicialSet,
		simplicial_homotopy.RowFaceIterateTopIn,
	},
	Build: family.Card(Statement{
		Binders: "∀V:module_ops(A, B). ∀D:bisimplicial_ops(B). ∀n:num. ∀y:B.",
		Hypotheses: []string{
			"bisimplicial_set(D)",
			"∀p:num. ∀x:B. x ∈ D.simplices(p + 1, n) ⇒ D.dh(p + 1, n, p + 1, x) = x",
			"y ∈ D.simplices(n, n)",
		},
		Conclusion: "alexander_whitney(V, D.dh, D.dv, n, y, 0) = y",
	},
		"at p = 0 the vertical back face is taken zero times (AlexanderWhitneyDef, "+
			"FaceIterateBottomDef), leaving the last horizontal face taken n times on the row n "+
			"(FaceIterateTopDef); by induction on k ≤ n, removing k top vertices leaves y: the "+
			"iterate lies in D(n − k, n) (RowFaceIterateTopIn), so it is y in D(n − k, n), and for "+
			"n − k = p + 1 ≥ 1 the next last face, D.dh(p + 1, n, p + 1), fixes it by the hypothesis"),
})}
