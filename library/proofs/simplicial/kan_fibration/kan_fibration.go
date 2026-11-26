// kan_fibration.go — Kan fibrations and the long exact sequence of
// homotopy groups. A fibration is a simplicial map along which every
// horn of the source whose image is filled in the target has a filler
// over that filling. Over a Kan complex a fibration's source is Kan;
// the fibre over a vertex is a sub-simplicial set and, over any base,
// a Kan complex; and a Kan complex is exactly a fibration to the point. The
// connecting map sends the class of an (n+1)-sphere of the base to the
// class, in the fibre, of the n-th face of a lift of it whose other
// faces are the base simplex; it is well defined, a homomorphism for
// 0 < n, and the sequence of the fibre, the total space and the base
// is exact at each of the three homotopy groups.
//
// The lifts the connecting map reads miss the n-th face, so that the
// lift of a product filler of the base, read along two more horns,
// gives the product in the fibre. Exactness lifts one new horn at the
// total space, one at the base, and none at the fibre, whose lifts are
// the connecting map's own.

package kan_fibration

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/simplicial/homotopy_group"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structure, the fibre, and the Kan complexes it gives
// ---------------------------------------------------------------------------

// KanFibration — `kan_fibration(X, Y, p)`: a simplicial
// map p such that every compatible family of n-simplices of X, missing
// the index k, whose images are the faces of an (n+1)-simplex z of Y
// other than the k-th, is the family of faces of an (n+1)-simplex of X
// over z. The components are implicit: under a law here the text
// writes `kan_fibration(X, Y, p)`.
var KanFibration = kanFibrationThm{family.DefineStructure(registry.DefEntry{
	Name:     "KanFibration",
	Key:      "prop_be45e6ca615d1592",
	Const:    "kan_fibration",
	Type:     "simplicial_ops(A) → simplicial_ops(B) → (num → A → B) → bool",
	Implicit: []string{"X", "Y"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). ∀p:(num → A → B). " +
			"    kan_fibration(X, Y, p) ⇔ " +
			"    simplicial_map(X, Y, p) ∧ " +
			"    (∀n k:num. ∀y:(num → A). ∀z:B. " +
			"        k ≤ n + 1 ∧ " +
			"        face_family(X, n, horn_faces(n, k), y) ∧ " +
			"        z ∈ Y.simplices(n + 1) ∧ " +
			"        faces_filler(Y.d, n, horn_faces(n, k), λi:num. p(n, y(i)), z) ⇒ " +
			"        ∃x:A. " +
			"            x ∈ X.simplices(n + 1) ∧ " +
			"            faces_filler(X.d, n, horn_faces(n, k), y, x) ∧ " +
			"            p(n + 1, x) = z)",
	},
	Reading: "The lifting condition quantifies over every horn of X and every " +
		"simplex of Y filling its image; with Y the point it is the Kan condition on X.",
})}

// FibrationMap — a fibration is a simplicial map.
var FibrationMap = fibrationMapThm{family.Add(registry.ProofEntry{
	Name:  "FibrationMap",
	Key:   "prop_f4fffc34b69e712c",
	Build: KanFibration.Axiom("simplicial_map(X, Y, p)"),
})}

// FibrationLift — every horn whose image is filled lifts.
var FibrationLift = fibrationLiftThm{family.Add(registry.ProofEntry{
	Name: "FibrationLift",
	Key:  "prop_9db427017635a2d6",
	Build: KanFibration.Axiom(Statement{
		Binders: "∀n k:num. ∀y:(num → A). ∀z:B.",
		Hypotheses: []string{
			"k ≤ n + 1",
			"face_family(X, n, horn_faces(n, k), y)",
			"z ∈ Y.simplices(n + 1)",
			"faces_filler(n, horn_faces(n, k), λi:num. p(n, y(i)), z)",
		},
		Conclusion: "∃x:A. " +
			"    x ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, k), y, x) ∧ p(n + 1, x) = z",
	}),
})}

// simplicialFiberSimplicesDef — `simplicial_fiber(…, p, y₀, n)`: the n-simplices
// of X over the base simplex at the vertex y₀ of Y. Under the two
// structures the text writes `simplicial_fiber(p, y₀, n)`, and
// `simplicial_fiber(p, y₀)` is the family.
var simplicialFiberSimplicesDef = simplicialFiberSimplicesDefThm{family.Define(registry.DefEntry{
	Name:     "simplicialFiberSimplicesDef",
	Key:      "prop_b6a20cf2778c9d63",
	Const:    "simplicial_fiber_simplices",
	Type:     "simplicial_ops(A) → simplicial_ops(B) → (num → A → B) → B → num → set(A)",
	Implicit: []string{"X", "Y"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). ∀p:(num → A → B). ∀y₀:B. ∀n:num. " +
			"    simplicial_fiber_simplices(X, Y, p, y₀, n) = " +
			"    {x:A | x ∈ X.simplices(n) ∧ p(n, x) = base_simplex(Y.s, y₀, n)}",
	},
})}

// FiberSub — the fibre is a sub-simplicial set of X: a simplex of the
// fibre is a simplex of X, and F (the map's binder under simplicial_map,
// the fibration's p below) carries a face or a degeneracy of it
// to the same face or degeneracy of the base simplex, which is the base
// simplex again.
var FiberSub = fiberSubThm{family.Add(registry.ProofEntry{
	Name: "FiberSub",
	Key:  "prop_7b4ad42f24a874f1",
	Build: simplicial_set.SimplicialMap.Law(Statement{
		Binders: "∀y₀:B.",
		Hypotheses: []string{
			"y₀ ∈ Y.simplices(0)",
		},
		Conclusion: "sub_simplicial_set(X, simplicial_fiber_simplices(X, Y, F, y₀))",
	},
		func(a *Argument, simplicialMap Fact, y0 *Expr[B], vertex Fact) {
			source := simplicial_set.MapSource.Read(simplicialMap)
			target := simplicial_set.MapTarget.Read(simplicialMap)
			// The sub-simplicial-set condition is opened in the goal alone, so
			// the map hypothesis stays whole.
			a.Do(Simp(Fwd(simplicial_set.SubSimplicialSetDef)), SplitConjAll(
				Case(
					"every simplex of the fibre is a simplex of X",
					a.ForEach(
						func(_ *Expr[Nat]) Action { return Chain(Simp(Fwd(simplicialFiberSimplicesDef)), BySets()) })),
				Case(
					"a face of a simplex of the fibre lies in the fibre",
					Derive(func(b *Argument) {
						n, i := b.FixAs[Nat](), b.FixAs[Nat]()
						x := b.FixAs[A]()
						given := b.Conjuncts(
							b.Assume(),
							"x is an (n+1)-simplex of the fibre",
							"and i indexes one of its faces")
						member, bound := given[0], given[1]
						over := b.Conjuncts(
							b.Have(
								"so x is an (n+1)-simplex of X lying over the base simplex",
								"x ∈ X.simplices(n + 1) ∧ F(n + 1, x) = base_simplex(y₀, n + 1)",
								BySets(b.Unfolded(member, simplicialFiberSimplicesDef))),
							"x is an (n+1)-simplex of X",
							"and F carries it to the base simplex")
						xIn, xOver := over[0], over[1]
						faceIn := b.Have(
							"its i-th face is an n-simplex of X",
							"X.d(n + 1, i, x) ∈ X.simplices(n)",
							By(simplicial_set.FaceIn.Read(source).At(n, i, x), xIn, bound))
						faceOver := b.Have(
							"which F carries to the base simplex",
							"F(n, X.d(n + 1, i, x)) = base_simplex(y₀, n)",
							CalcEq(
								Leg(
									b.TermAs[B]("Y.d(n + 1, i, F(n + 1, x))"),
									"F commutes with the face",
									By(simplicial_set.MapFace.Read(simplicialMap).At(n, i, x), xIn, bound)),
								FinalLeg(
									"and the i-th face of the base simplex at n + 1 is the base simplex at n",
									By(Normalized, xOver, simplicial_set.BaseSimplexFace.Read(target).At(y0, n, i), vertex, bound)),
							))
						b.Show(
							"so the face lies in the fibre",
							BySets(faceIn, faceOver, simplicialFiberSimplicesDef))
					})),
				Case(
					"a degeneracy of a simplex of the fibre lies in the fibre",
					Derive(func(b *Argument) {
						n, i := b.FixAs[Nat](), b.FixAs[Nat]()
						x := b.FixAs[A]()
						given := b.Conjuncts(
							b.Assume(),
							"x is an n-simplex of the fibre",
							"and i indexes one of its degeneracies")
						member, bound := given[0], given[1]
						over := b.Conjuncts(
							b.Have(
								"so x is an n-simplex of X lying over the base simplex",
								"x ∈ X.simplices(n) ∧ F(n, x) = base_simplex(y₀, n)",
								BySets(b.Unfolded(member, simplicialFiberSimplicesDef))),
							"x is an n-simplex of X",
							"and F carries it to the base simplex")
						xIn, xOver := over[0], over[1]
						degeneracyIn := b.Have(
							"its i-th degeneracy is an (n+1)-simplex of X",
							"X.s(n, i, x) ∈ X.simplices(n + 1)",
							By(simplicial_set.DegeneracyIn.Read(source).At(n, i, x), xIn, bound))
						degeneracyOver := b.Have(
							"which F carries to the base simplex",
							"F(n + 1, X.s(n, i, x)) = base_simplex(y₀, n + 1)",
							CalcEq(
								Leg(
									b.TermAs[B]("Y.s(n, i, F(n, x))"),
									"F commutes with the degeneracy",
									By(simplicial_set.MapDegeneracy.Read(simplicialMap).At(n, i, x), xIn, bound)),
								FinalLeg(
									"and the i-th degeneracy of the base simplex at n is the base simplex at n + 1",
									By(
										Normalized,
										xOver,
										simplicial_set.BaseSimplexDegeneracy.Read(target).At(y0, n, i),
										vertex,
										bound)),
							))
						b.Show(
							"so the degeneracy lies in the fibre",
							BySets(degeneracyIn, degeneracyOver, simplicialFiberSimplicesDef))
					})),
			))
		}),
})}

// FiberSimplicialSet — the fibre is a simplicial set: it is a
// sub-simplicial set of X, and X is a simplicial set.
var FiberSimplicialSet = fiberSimplicialSetThm{family.Add(registry.ProofEntry{
	Name: "FiberSimplicialSet",
	Key:  "prop_c1c5c739d4d141e5",
	Build: simplicial_set.SimplicialMap.Law(Statement{
		Binders: "∀y₀:B.",
		Hypotheses: []string{
			"y₀ ∈ Y.simplices(0)",
		},
		Conclusion: "simplicial_set(simplicial_fiber(X, Y, F, y₀))",
	},
		func(a *Argument, simplicialMap Fact, y0 *Expr[B], vertex Fact) {
			source := simplicial_set.MapSource.Read(simplicialMap)
			a.Do(Simp(Fwd(SimplicialFiberDef)), By(
				simplicial_set.SubSimplicialSet.Read(source),
				FiberSub.Read(simplicialMap).At(y0),
				vertex))
		}),
})}

// FiberSphere — a sphere of the fibre is a sphere of X over the base
// simplex: the fibre carries the faces and degeneracies of X, so with
// both spheres and the fibre unfolded the two sides state the same three
// conditions, grouped differently.
var FiberSphere = fiberSphereThm{family.Add(registry.ProofEntry{
	Name: "FiberSphere",
	Key:  "prop_6a432c524b27b71",
	Build: family.Theorem("∀X:simplicial_ops(A). "+
		"∀Y:simplicial_ops(B). "+
		"∀F:(num → A → B). "+
		"∀x₀:A. "+
		"∀n:num. "+
		"∀x:A. "+
		"    x ∈ simplicial_sphere(simplicial_fiber(X, Y, F, F(0, x₀)), x₀, n) ⇔ "+
		"    x ∈ simplicial_sphere(X, x₀, n) ∧ F(n, x) = base_simplex(Y.s, F(0, x₀), n)",
		func(a *Argument, _, _, _, _, _, _ Term) {
			a.Do(Simp(Fwd(homotopy_group.SimplicialSphereDef), Fwd(simplicialFiberSimplicesDef)), BySets())
		}),
})}

// FiberBasePoint — a vertex lies in the fibre over its image: the base
// simplex at 0 is the vertex itself.
var FiberBasePoint = fiberBasePointThm{family.Add(registry.ProofEntry{
	Name: "FiberBasePoint",
	Key:  "prop_f3bb335817c7820d",
	Reading: "The fibre is defined for any F, and x₀ lies " +
		"over F(0, x₀) by the definition of the base simplex at 0.",
	Build: family.Theorem(Statement{
		Binders: "∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). ∀F:(num → A → B). ∀x₀:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
		},
		Conclusion: "x₀ ∈ simplicial_fiber_simplices(X, Y, F, F(0, x₀), 0)",
	},
		func(a *Argument, _, _, _, _ Term, vertex Fact) {
			a.Show(
				"x₀ is a vertex of X, and the base simplex at 0 over F(0, x₀) is F(0, x₀) itself",
				Simp(Fwd(simplicialFiberSimplicesDef), Fwd(simplicial_set.BaseSimplexDef)),
				BySets(vertex))
		}),
})}

// TotalKan — over a Kan complex the source of a fibration is a Kan
// complex: a horn of X maps to a horn of Y, which fills there, and the
// filling lifts.
var TotalKan = totalKanThm{family.Add(registry.ProofEntry{
	Name: "TotalKan",
	Key:  "prop_14ea04d6dbd36b30",
	Build: KanFibration.Law(Statement{
		Hypotheses: []string{
			"kan_complex(Y)",
		},
		Conclusion: "kan_complex(X)",
	},
		func(a *Argument, fibration, base Fact) {
			simplicialMap := FibrationMap.Read(fibration)
			// The Kan condition is opened in the goal alone, so the hypothesis
			// that Y is a Kan complex stays whole.
			a.Do(Simp(Fwd(kan_complex.KanComplex)), SplitConjAll(
				Case(
					"X is a simplicial set, the source of the simplicial map p",
					By(simplicial_set.MapSource.Read(simplicialMap))),
				Case(
					"every horn of X fills",
					Derive(func(b *Argument) {
						n, k := b.FixAs[Nat](), b.FixAs[Nat]()
						y := b.FixAs[Fun[Nat, A]]()
						horn := b.Assume()
						bound := b.Conjuncts(
							horn,
							"the missing face k is at most n + 1",
							"and y is a face family of X on the faces of the horn")[0]

						image := b.TermAs[Fun[Nat, B]]("λi:num. p(n, y(i))")
						imageHorn := b.Have(
							"p carries the horn to a horn of Y",
							"face_family(Y, n, horn_faces(n, k), λi:num. p(n, y(i)))",
							By(kan_complex.MapHorn.Read(simplicialMap).At(n, k, y), horn))

						z, fills := b.ObtainAs[B](
							"Y is a Kan complex, so the horn fills there: an (n+1)-simplex z of Y "+
								"whose faces at the faces of the horn are the images of the members of y",
							"∃z:B. z ∈ Y.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, k), λi:num. p(n, y(i)), z)",
							By(kan_complex.KanFill.Read(base).At(n, k, image), bound, imageHorn))
						b.Show(
							"and the filling lifts along the fibration to a filler of y over z",
							By(FibrationLift.Read(fibration).At(n, k, y, z), horn, fills))
					})),
			))
		}),
})}

// FiberKan — the fibre of a fibration is a Kan complex: a horn of the
// fibre is a horn of X lying over the base simplex, so its images are
// the faces of the base simplex one dimension up; the horn lifts over
// that simplex, and the lift lies in the fibre.
var FiberKan = fiberKanThm{family.Add(registry.ProofEntry{
	Name: "FiberKan",
	Reading: "kan_complex(Y) is not needed: the simplex of Y a horn of the " +
		"fibre lifts over is base_simplex(y₀, n + 1), which every simplicial set has.",
	Key: "prop_89d8cc1c32f61048",
	Build: KanFibration.Law(Statement{
		Binders: "∀y₀:B.",
		Hypotheses: []string{
			"y₀ ∈ Y.simplices(0)",
		},
		Conclusion: "kan_complex(simplicial_fiber(p, y₀))",
	},
		func(a *Argument, fibration Fact, y0 *Expr[B], vertex Fact) {
			simplicialMap := FibrationMap.Read(fibration)
			target := simplicial_set.MapTarget.Read(simplicialMap)
			// The Kan condition is opened in the goal alone, so the fibration
			// hypothesis stays whole.
			a.Do(Simp(Fwd(kan_complex.KanComplex)), SplitConjAll(
				Case(
					"the fibre is a simplicial set",
					By(FiberSimplicialSet.Read(simplicialMap).At(y0), vertex)),
				Case(
					"every horn of the fibre fills in the fibre",
					Derive(func(b *Argument) {
						n, k := b.FixAs[Nat](), b.FixAs[Nat]()
						y := b.FixAs[Fun[Nat, A]]()
						given := b.Conjuncts(
							b.Assume(),
							"the missing face k is at most n + 1",
							"and y is a face family of the fibre on the faces of the horn")
						bound := given[0]
						family := b.Conjuncts(
							b.Unfolded(given[1], simplicial_set.FaceFamilyDef),
							"the members of y are n-simplices of the fibre",
							"and they are compatible")
						members, compatible := family[0], family[1]

						comprehension := b.Unfolded(members, simplicialFiberSimplicesDef)
						inX := b.Have(
							"the members of y are n-simplices of X",
							"∀i:num. i ∈ horn_faces(n, k) ⇒ y(i) ∈ X.simplices(n)",
							BySets(comprehension))
						over := b.Have(
							"and p carries them to the base simplex",
							"∀i:num. i ∈ horn_faces(n, k) ⇒ p(n, y(i)) = base_simplex(y₀, n)",
							BySets(comprehension))
						horn := b.Have(
							"so y is a horn of X",
							"face_family(X, n, horn_faces(n, k), y)",
							Simp(Fwd(simplicial_set.FaceFamilyDef)),
							By(inX, compatible))
						z := b.TermAs[B]("base_simplex(y₀, n + 1)")
						zIn := b.Have(
							"the base simplex one dimension up is an (n+1)-simplex of Y",
							"base_simplex(y₀, n + 1) ∈ Y.simplices(n + 1)",
							By(simplicial_set.BaseSimplexIn.Read(target).At(y0, b.TermAs[Nat]("n + 1")), vertex))
						faces := b.Have(
							"whose faces at the faces of the horn are the images of the members of y",
							"faces_filler(n, horn_faces(n, k), λi:num. p(n, y(i)), base_simplex(y₀, n + 1))",
							Derive(func(c *Argument) {
								c.Do(Simp(Fwd(simplicial_set.FacesFillerDef)))
								i := c.FixAs[Nat]()
								face := c.Assume()
								index := c.Have(
									"a face of the horn is at most n + 1",
									"i ≤ n + 1",
									By(face, kan_complex.HornFacesMember.At(n, k, i)))
								c.Show(
									"the i-th face of the base simplex at n + 1 is the image of y(i)",
									CalcEq(
										Leg(
											c.TermAs[B]("base_simplex(y₀, n)"),
											"the i-th face of the base simplex at n + 1 is the base simplex at n",
											By(simplicial_set.BaseSimplexFace.Read(target).At(y0, n, i), vertex, index)),
										FinalLeg(
											"which is the image of y(i), y(i) lying over the base simplex",
											By(over.At(i), face)),
									))
							}))
						x, lifted := b.ObtainAs[A](
							"so y lifts along the fibration to an (n+1)-simplex x of X over the base simplex",
							"∃x:A. "+
								"    x ∈ X.simplices(n + 1) ∧ "+
								"    faces_filler(n, horn_faces(n, k), y, x) ∧ "+
								"    p(n + 1, x) = base_simplex(y₀, n + 1)",
							By(FibrationLift.Read(fibration).At(n, k, y, z), bound, horn, zIn, faces))
						b.Take(x)
						b.Show(
							"x lies over the base simplex, so in the fibre, and it fills y",
							BySets(lifted, simplicialFiberSimplicesDef))
					})),
			))
		}),
})}

// KanIffFibrationToPoint — the point has the one simplex a in every
// dimension, and its faces and the map to it are constant at a: every
// lift of a horn of X is a lift over a, and its image condition reads
// a = a. So a filler of a horn is a lift of it, and a lift is a filler.
var KanIffFibrationToPoint = kanIffFibrationToPointThm{family.Add(registry.ProofEntry{
	Name: "KanIffFibrationToPoint",
	Key:  "prop_fda03fd281f98c45",
	Build: simplicial_set.SimplicialSet.Law("∀a:B. "+
		"    kan_complex(X) ⇔ kan_fibration(X, simplicial_point(a), λn:num. λx:A. a)",
		func(arg *Argument, simplicial Fact, a *Expr[B]) {
			arg.Iff()
			arg.Forward(
				"a filler of a horn of X lies over a, the one simplex of the point, so it is a lift",
				func(b *Argument, kan Fact) {
					// The fibration condition is opened in the goal alone, so the
					// Kan hypothesis stays whole.
					b.Do(Simp(Fwd(KanFibration)), SplitConjAll(
						Case(
							"the map to the point is simplicial",
							By(simplicial_set.MapToPoint.Read(simplicial))),
						Case(
							"every horn of X whose image is filled in the point lifts",
							Derive(func(c *Argument) {
								n, k := c.FixAs[Nat](), c.FixAs[Nat]()
								y := c.FixAs[Fun[Nat, A]]()
								c.FixAs[B]("z")
								given := c.Conjuncts(
									c.Assume(),
									"the missing face k is at most n + 1",
									"y is a face family of X on the faces of the horn",
									"z is an (n+1)-simplex of the point",
									"and its faces at the faces of the horn, each a, are the images of the members of y, each a")
								bound, horn, zIn := given[0], given[1], given[2]

								x, fills := c.ObtainAs[A](
									"X is a Kan complex, so the horn fills: an (n+1)-simplex x of X",
									"∃x:A. x ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, k), y, x)",
									By(kan_complex.KanFill.Read(kan).At(n, k, y), bound, horn))
								zIsA := c.Have(
									"z is a simplex of the point, so it is a",
									"z = a",
									zIn.Simp(
										Fwd(simplicial_set.SimplicialPointSimplicesDef.Inst[B]()),
										Fwd(set_basic.InSing.Inst[B]())),
									By(zIn))
								c.Take(x)
								c.Show(
									"x fills the horn, and the map sends it to a, which is z",
									By(fills, zIsA))
							})),
					))
				})
			arg.Backward(
				"a horn of X lifts over a, the one simplex of the point, and the lift fills it",
				func(b *Argument, fibration Fact) {
					// The Kan condition is opened in the goal alone, so the fibration
					// hypothesis stays whole.
					b.Do(Simp(Fwd(kan_complex.KanComplex)), SplitConjAll(
						Case(
							"X is a simplicial set",
							By(simplicial)),
						Case(
							"every horn of X fills",
							Derive(func(c *Argument) {
								n, k := c.FixAs[Nat](), c.FixAs[Nat]()
								y := c.FixAs[Fun[Nat, A]]()
								horn := c.Assume()

								aIn := c.Have(
									"a is the (n+1)-simplex of the point",
									"a ∈ simplicial_point_simplices(a, n + 1)",
									By(
										Normalized,
										simplicial_set.SimplicialPointSimplicesDef.At(a, c.TermAs[Nat]("n + 1")),
										set_basic.InSing.At(a, a)))
								image := c.Have(
									"and a fills the image of the horn: each face of a is a, the image of the member there",
									"faces_filler(λn:num. λi:num. λx:B. a, n, horn_faces(n, k), λi:num. a, a)",
									Unfold(simplicial_set.FacesFillerDef))
								c.Show(
									"so the horn lifts over a, and the lift is a filler",
									By(FibrationLift.Read(fibration).At(n, k, y, a), horn, aIn, image))
							})),
					))
				})
		}),
})}

// FibrationCompose — fibrations compose: a horn of X whose image under
// q ∘ p is filled in Z maps under p to a horn of Y filled by the same
// simplex, which lifts along q; the horn of X then lifts along p over
// that lift.
var FibrationCompose = fibrationComposeThm{family.Add(registry.ProofEntry{
	Name: "FibrationCompose",
	Key:  "prop_343a448b7a712cef",
	Build: family.Theorem(Statement{
		Binders: "∀X:simplicial_ops(A). " +
			"∀Y:simplicial_ops(B). " +
			"∀Z:simplicial_ops(C). " +
			"∀p:(num → A → B). " +
			"∀q:(num → B → C).",
		Hypotheses: []string{
			"kan_fibration(X, Y, p)",
			"kan_fibration(Y, Z, q)",
		},
		Conclusion: "kan_fibration(X, Z, λn:num. λx:A. q(n, p(n, x)))",
	},
		func(
			a *Argument,
			X *Expr[simplicial_set.SimplicialOps[A]],
			Y *Expr[simplicial_set.SimplicialOps[B]],
			Z *Expr[simplicial_set.SimplicialOps[C]],
			p *Expr[Fun2[Nat, A, B]],
			q *Expr[Fun2[Nat, B, C]],
			fibrations Fact,
		) {
			both := a.Conjuncts(
				fibrations,
				"p is a fibration",
				"and so is q")
			first, second := both[0], both[1]
			simplicialMap := FibrationMap.Read(first)
			// The fibration condition is opened in the goal alone, so the two
			// hypotheses stay whole; the structure's B is bound to C, where the
			// composite's target Z lives.
			a.Do(Simp(Fwd(Inst(KanFibration, TypeBinder.BindA[A](), TypeBinder.BindB[C]()))), SplitConjAll(
				Case(
					"the composite of the simplicial maps p and q is simplicial",
					By(simplicial_set.MapCompose, simplicialMap, FibrationMap.Read(second))),
				Case(
					"every horn of X whose image under q ∘ p is filled in Z lifts",
					Derive(func(b *Argument) {
						n, k := b.FixAs[Nat](), b.FixAs[Nat]()
						y := b.FixAs[Fun[Nat, A]]()
						w := b.FixAs[C]("w")
						horn := b.Assume()
						given := b.Conjuncts(
							horn,
							"the missing face k is at most n + 1",
							"y is a face family of X on the faces of the horn",
							"w is an (n+1)-simplex of Z",
							"whose faces at the faces of the horn are the images of the members of y under q ∘ p")
						bound, family, filled, imageFaces := given[0], given[1], given[2], given[3]

						image := b.TermAs[Fun[Nat, B]]("λi:num. p(n, y(i))")
						imageHorn := b.Have(
							"p carries the horn to a horn of Y",
							"face_family(Y, n, horn_faces(n, k), λi:num. p(n, y(i)))",
							By(kan_complex.MapHorn.Read(simplicialMap).At(n, k, y), bound, family))

						z, lifted := b.ObtainAs[B](
							"q is a fibration, so the image horn, filled by w in Z, lifts to an (n+1)-simplex z of Y over w",
							"∃z:B. "+
								"    z ∈ Y.simplices(n + 1) ∧ "+
								"    faces_filler(n, horn_faces(n, k), λi:num. p(n, y(i)), z) ∧ "+
								"    q(n + 1, z) = w",
							By(FibrationLift.Read(second).At(n, k, image, w), bound, imageHorn, filled, imageFaces))
						lift := b.Conjuncts(
							lifted,
							"z is an (n+1)-simplex of Y",
							"whose faces at the faces of the horn are the images of the members of y under p",
							"and q(n + 1, z) = w")
						zIn, faces, zOverW := lift[0], lift[1], lift[2]
						x, over := b.ObtainAs[A](
							"and p is a fibration, so y lifts to an (n+1)-simplex x of X over z",
							"∃x:A. x ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, k), y, x) ∧ p(n + 1, x) = z",
							By(FibrationLift.Read(first).At(n, k, y, z), bound, family, zIn, faces))
						b.Take(x)
						b.Show(
							"x fills y, and q ∘ p sends it to q(n + 1, z), which is w",
							By(Normalized, over, zOverW))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// The connecting map
// ---------------------------------------------------------------------------

// SimplicialConnectingMapDef — `simplicial_connecting_map(…, p, x₀, n, L)`:
// the class in the fibre of the n-th face of a lift, with the base
// simplex for its other faces, of a representative of the class L of
// (n+1)-spheres of Y. Under the two structures the text writes
// `simplicial_connecting_map(p, x₀, n, L)`.
var SimplicialConnectingMapDef = simplicialConnectingMapDefThm{family.Define(registry.DefEntry{
	Name:     "SimplicialConnectingMapDef",
	Key:      "prop_1e1d50901c11b410",
	Const:    "simplicial_connecting_map",
	Type:     "simplicial_ops(A) → simplicial_ops(B) → (num → A → B) → A → num → set(B) → set(A)",
	Implicit: []string{"X", "Y"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). ∀p:(num → A → B). ∀x₀:A. ∀n:num. ∀L:set(B). " +
			"    simplicial_connecting_map(X, Y, p, x₀, n, L) = " +
			"    equivalence_class(simplicial_homotopic(simplicial_fiber(X, Y, p, p(0, x₀)), x₀, n), " +
			"        X.d(n + 1, " +
			"            n, " +
			"            εw:A. " +
			"                w ∈ X.simplices(n + 1) ∧ " +
			"                (∀i:num. i ≤ n + 1 ∧ ¬(i = n) ⇒ X.d(n + 1, i, w) = base_simplex(X.s, x₀, n)) ∧ " +
			"                p(n + 1, w) = (εz:B. z ∈ L)))",
	},
	Reading: "The lift misses the n-th face, not the last: the n-th face of a " +
		"lift of a product filler of Y is then read by two more horns as a product " +
		"in the fibre. The class is taken in the fibre, where it is finer than in X.",
	Deps: []registry.EntryLike{simplicialFiberSimplicesDef, SimplicialFiberDef},
})}

// ConnectingLiftExists — a sphere of Y lifts with the base simplex for
// its faces other than the n-th: the base simplex of X is a sphere, so the
// constant family at it, a family of spheres missing the face n, is a
// horn; its member maps to the base simplex of Y, which is every face of
// the sphere, so the horn lifts over the sphere.
var ConnectingLiftExists = connectingLiftExistsThm{family.Add(registry.ProofEntry{
	Name:    "ConnectingLiftExists",
	Reading: "The sphere is itself the simplex of Y the horn lifts over, so no horn of Y has to fill.",
	Key:     "prop_213dcfcd7efbe4ee",
	Build: KanFibration.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀z:B.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"z ∈ simplicial_sphere(Y, p(0, x₀), n + 1)",
		},
		Conclusion: "∃w:A. " +
			"    w ∈ X.simplices(n + 1) ∧ " +
			"    (∀i:num. i ≤ n + 1 ∧ ¬(i = n) ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ " +
			"    p(n + 1, w) = z",
	},
		func(a *Argument, fibration Fact, x0 *Expr[A], n *Expr[Nat], vertex Fact, z *Expr[B], sphere Fact) {
			simplicialMap := FibrationMap.Read(fibration)
			source := simplicial_set.MapSource.Read(simplicialMap)
			X := a.TermAs[simplicial_set.SimplicialOps[A]]("X")

			index := a.Have(
				"n + 1 is positive, and one less is n",
				"0 < n + 1 ∧ n + 1 - 1 = n",
				ByArith())
			sphereFacts := a.Conjuncts(
				a.Have(
					"z is an (n+1)-simplex of Y whose every face is the base simplex at p(0, x₀)",
					"z ∈ Y.simplices(n + 1) ∧ (∀i:num. i ≤ n + 1 ⇒ Y.d(n + 1, i, z) = base_simplex(p(0, x₀), n))",
					BySets(a.Unfolded(sphere, homotopy_group.SimplicialSphereDef), index)),
				"z is an (n+1)-simplex of Y",
				"and each of its faces is the base simplex at p(0, x₀)")
			zIn, faces := sphereFacts[0], sphereFacts[1]

			constant := a.TermAs[Fun[Nat, A]]("λi:num. base_simplex(x₀, n)")
			bound := a.Have(
				"the missing face n is at most n + 1",
				"n ≤ n + 1",
				ByArith())
			baseSphere := a.Have(
				"the base simplex of X is a sphere",
				"base_simplex(x₀, n) ∈ simplicial_sphere(X, x₀, n)",
				By(homotopy_group.BaseSphere.Read(source).At(x0, n), vertex))
			horn := a.Have(
				"so the constant family at it, a family of spheres missing the "+
					"face n, is a horn: a face family of X on the faces of the horn",
				"face_family(X, n, horn_faces(n, n), λi:num. base_simplex(x₀, n))",
				By(At(homotopy_group.SphereHornCompatible, X, x0, n, n, constant), bound, baseSphere))
			images := a.Have(
				"the faces of z at the faces of the horn are the image of the "+
					"member: p carries the base simplex of X to the base simplex of Y",
				"faces_filler(n, horn_faces(n, n), λi:num. p(n, base_simplex(x₀, n)), z)",
				Simp(Fwd(simplicial_set.FacesFillerDef)),
				a.ForEach(func(i *Expr[Nat]) Action {
					return By(
						Normalized,
						faces.At(i),
						kan_complex.HornFacesMember.At(n, n, i),
						simplicial_set.MapBaseSimplex.Read(simplicialMap).At(x0, n),
						vertex)
				}))

			w, lifted := a.ObtainAs[A](
				"so the horn lifts along the fibration to an (n+1)-simplex w of X over z",
				"∃w:A. "+
					"    w ∈ X.simplices(n + 1) ∧ "+
					"    faces_filler(n, horn_faces(n, n), λi:num. base_simplex(x₀, n), w) ∧ "+
					"    p(n + 1, w) = z",
				By(FibrationLift.Read(fibration).At(n, n, constant, z), bound, horn, zIn, images))
			filler := a.Unfolded(lifted, simplicial_set.FacesFillerDef)
			a.Take(w)
			a.Show(
				"w fills the horn, so its faces other than the n-th are the member of the family, the base simplex",
				By(filler, kan_complex.HornFacesMember))
		}),
})}

// ConnectingLiftFace — the n-th face of such a lift is a sphere of the
// fibre: the lift is a homotopy in X from its n-th face to the base
// simplex, a sphere, so the face is a sphere of X; and p carries it to
// the n-th face of z, the base simplex of Y, so it lies in the fibre.
var ConnectingLiftFace = connectingLiftFaceThm{family.Add(registry.ProofEntry{
	Name: "ConnectingLiftFace",
	Reading: "The lift's face n + 1, not only its faces below n, must be the " +
		"base simplex: only then is w a homotopy from its face n to the base simplex.",
	Key: "prop_86c64bca6820c2e1",
	Build: KanFibration.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀z:B. ∀w:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"z ∈ simplicial_sphere(Y, p(0, x₀), n + 1)",
			"w ∈ X.simplices(n + 1)",
			"∀i:num. i ≤ n + 1 ∧ ¬(i = n) ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)",
			"p(n + 1, w) = z",
		},
		Conclusion: "X.d(n + 1, n, w) ∈ simplicial_sphere(simplicial_fiber(p, p(0, x₀)), x₀, n)",
	},
		func(
			a *Argument,
			fibration Fact,
			x0 *Expr[A],
			vertex Fact,
			n *Expr[Nat],
			z *Expr[B],
			sphere Fact,
			w *Expr[A],
			wIn, wFaces, wOver Fact,
		) {
			simplicialMap := FibrationMap.Read(fibration)
			source := simplicial_set.MapSource.Read(simplicialMap)

			face, base := a.TermAs[A]("X.d(n + 1, n, w)"), a.TermAs[A]("base_simplex(x₀, n)")
			homotopic := a.Have(
				"w is a homotopy from its n-th face to the base simplex: "+
					"its faces below n and its face n + 1 are the base simplex",
				"simplicial_homotopic(X, x₀, n, X.d(n + 1, n, w), base_simplex(x₀, n))",
				Simp(Fwd(homotopy_group.SimplicialHomotopicDef)),
				Witness(w),
				ByArith(wIn, wFaces))
			inX := a.Have(
				"so the n-th face, homotopic to the base simplex, which is a sphere, is a sphere of X",
				"X.d(n + 1, n, w) ∈ simplicial_sphere(X, x₀, n)",
				By(
					homotopy_group.HomotopicSphere.Read(source).At(x0, n, face, base),
					homotopy_group.BaseSphere.Read(source).At(x0, n),
					vertex,
					homotopic))

			zFaces := a.Have(
				"z is a sphere: its faces are the base simplex at p(0, x₀) one dimension down",
				"∀i:num. i ≤ n + 1 ⇒ Y.d(n + 1, i, z) = base_simplex(p(0, x₀), n)",
				ByArith(a.Unfolded(sphere, homotopy_group.SimplicialSphereDef)))
			over := a.Have(
				"p carries the n-th face to the n-th face of z, the base simplex of Y",
				"p(n, X.d(n + 1, n, w)) = base_simplex(p(0, x₀), n)",
				CalcEq(
					Leg(
						a.TermAs[B]("Y.d(n + 1, n, p(n + 1, w))"),
						"p commutes with the face n",
						ByArith(simplicial_set.MapFace.Read(simplicialMap).At(n, n, w), wIn)),
					Leg(
						a.TermAs[B]("Y.d(n + 1, n, z)"),
						"w lies over z",
						By(Normalized, wOver)),
					FinalLeg(
						"z is a sphere, so its face n is the base simplex one dimension down",
						ByArith(zFaces.At(n))),
				))
			a.Show(
				"so the n-th face is a sphere of X over the base simplex of Y: a sphere of the fibre",
				By(inX, over, FiberSphere))
		}),
})}

// ConnectingHomotopic — lifts of homotopic simplices of Y, with the base
// simplex at every face but the n-th, have homotopic n-th faces in the
// fibre: the horn missing the face n, with the base simplex below n and
// the two lifts at n + 1 and n + 2, lifts over the homotopy H; the n-th
// face of the lift lies over the face n of H, the base simplex, and is a
// homotopy in the fibre from the one n-th face to the other.
var ConnectingHomotopic = connectingHomotopicThm{family.Add(registry.ProofEntry{
	Name: "ConnectingHomotopic",
	Reading: "The homotopy H is itself the simplex of " +
		"Y the horn lifts over, so no horn of Y has to fill.",
	Key: "prop_86bdf9387ddf867e",
	Build: KanFibration.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀z z':B. ∀w w':A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"simplicial_homotopic(Y, p(0, x₀), n + 1, z, z') ∧ " +
				"(w ∈ X.simplices(n + 1) ∧ " +
				"    (∀i:num. i ≤ n + 1 ∧ ¬(i = n) ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ " +
				"    p(n + 1, w) = z) ∧ " +
				"(w' ∈ X.simplices(n + 1) ∧ " +
				"    (∀i:num. i ≤ n + 1 ∧ ¬(i = n) ⇒ X.d(n + 1, i, w') = base_simplex(x₀, n)) ∧ " +
				"    p(n + 1, w') = z')",
		},
		Conclusion: "simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), " +
			"    x₀, " +
			"    n, " +
			"    X.d(n + 1, n, w), " +
			"    X.d(n + 1, n, w'))",
	},
		func(
			a *Argument,
			fibration Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			vertex Fact,
			_, _ *Expr[B],
			_, _ *Expr[A],
			given Fact,
		) {
			simplicialMap := FibrationMap.Read(fibration)
			source := simplicial_set.MapSource.Read(simplicialMap)
			faceFace, baseFace :=
				simplicial_set.FaceFace.Read(source), simplicial_set.BaseSimplexFace.Read(source)
			next, top := a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 2")

			parts := a.Conjuncts(
				given,
				"z is homotopic to z' in Y",
				"w is an (n+1)-simplex of X",
				"whose faces other than the n-th are the base simplex",
				"and p carries it to z",
				"w' is an (n+1)-simplex of X",
				"whose faces other than the n-th are the base simplex",
				"and p carries it to z'")
			wIn, wFaces, wOver := parts[1], parts[2], parts[3]
			wPrimeIn, wPrimeFaces, wPrimeOver := parts[4], parts[5], parts[6]
			H, homotopy := a.UnpackAs[B](a.Unfolded(parts[0], homotopy_group.SimplicialHomotopicDef), "H")
			HParts := a.Conjuncts(
				homotopy,
				"H is an (n+2)-simplex of Y",
				"whose faces below n + 1 are the base simplex of Y",
				"z is its face n + 1",
				"and z' its face n + 2")
			HIn, HBelow, HStart, HEnd := HParts[0], HParts[1], HParts[2], HParts[3]
			dims := a.Have(
				"the lift has dimension (n + 1) + 1 = n + 2, and the missing face n is one of its faces",
				"n + 1 + 1 = n + 2 ∧ n ≤ n + 1 + 1",
				ByArith())

			// The horn: the base simplex below n, w at n + 1 and w' at n + 2;
			// its value at the missing face n is never read.
			f, fDef := a.LetAs[Fun[Nat, A]](
				"f", "λi:num. COND(i = n + 1, w, COND(i = n + 2, w', base_simplex(x₀, n + 1)))")
			values := a.Have(
				"f is w at n + 1 and w' at n + 2",
				"f(n + 1) = w ∧ f(n + 2) = w'",
				fDef.Rw(),
				ByArith())
			baseValues := a.Have(
				"and the base simplex below n",
				"∀i:num. i < n ⇒ f(i) = base_simplex(x₀, n + 1)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
			members := a.Have(
				"every member of f is an (n+1)-simplex of X: w, w' or the base simplex",
				"∀i:num. f(i) ∈ X.simplices(n + 1)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action {
					return Chain(CondRewrite(), ByArith(
						wIn,
						wPrimeIn,
						simplicial_set.BaseSimplexIn.Read(source).At(x0, next),
						vertex))
				}))
			lowerFaces := a.Have(
				"every member of f has the base simplex for its faces below n",
				"∀j i:num. i < n ⇒ X.d(n + 1, i, f(j)) = base_simplex(x₀, n)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					i := b.FixAs[Nat]()
					below := b.Assume()
					b.Show(
						"f(j) is w, w' or the base simplex at n + 1, and the face i of each is the base simplex",
						fDef.Rw(),
						CondRewrite(),
						ByArith(wFaces.At(i), wPrimeFaces.At(i), baseFace.At(x0, n, i), below, vertex))
				}))
			lastFaces := a.Have(
				"and the base simplex for its face n + 1",
				"∀j:num. X.d(n + 1, n + 1, f(j)) = base_simplex(x₀, n)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action {
					return Chain(CondRewrite(), ByArith(
						wFaces.At(next),
						wPrimeFaces.At(next),
						baseFace.At(x0, n, next),
						vertex))
				}))
			compatible := a.Have(
				"so f is compatible on the faces of the horn missing the face n",
				"faces_compatible(n + 1, horn_faces(n + 1, n), f)",
				Simp(Fwd(simplicial_set.FacesCompatibleDef)),
				Derive(func(b *Argument) {
					i, j := b.FixAs[Nat](), b.FixAs[Nat]()
					faces := b.Assume()
					pair := b.Have(
						"i < j are faces of the horn: both at most n + 2, and neither is n",
						"i < j ∧ j ≤ n + 1 + 1 ∧ ¬(i = n) ∧ ¬(j = n)",
						By(faces, kan_complex.HornFacesMember.At(next, n, i), kan_complex.HornFacesMember.At(next, n, j)))
					jPrevious := b.TermAs[Nat]("j - 1")
					notBelow := b.Unless(
						b.Term("i < n"),
						"below n the member f(i) is the base simplex, and both faces are the base simplex at n",
						Given(func(c *Argument, below Fact) {
							c.Show(
								"the face i of f(j) and the face j − 1 of the base simplex f(i) are the base simplex at n",
								ByArith(lowerFaces.At(j, i), baseValues.At(i), baseFace.At(x0, n, jPrevious), below, pair, vertex))
						}))
					atNext := b.Have(
						"i, neither n nor below it, is n + 1",
						"i = n + 1",
						ByArith(notBelow, pair))
					atTop := b.Have(
						"and j, above i, is n + 2",
						"j = n + 2",
						ByArith(notBelow, pair))
					b.Show(
						"so the pair is (n + 1, n + 2), and the faces n + 1 of "+
							"f(n + 2) and of f(n + 1) are both the base simplex at n",
						atNext.Rw(),
						atTop.Rw(),
						ByArith(lastFaces.At(top), lastFaces.At(next)))
				}))
			horn := a.Have(
				"so f is a horn of X: a face family of (n+1)-simplices on the faces of the horn missing the face n",
				"face_family(X, n + 1, horn_faces(n + 1, n), f)",
				Simp(Fwd(simplicial_set.FaceFamilyDef)),
				By(members, compatible))

			// The simplex of Y the horn lifts over is the homotopy H.
			memberImages := a.Have(
				"p carries the members of f below n to the base simplex of Y",
				"∀i:num. i < n ⇒ p(n + 1, f(i)) = base_simplex(p(0, x₀), n + 1)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action {
					return Chain(CondRewrite(), ByArith(
						simplicial_set.MapBaseSimplex.Read(simplicialMap).At(x0, next),
						vertex))
				}))
			images := a.Have(
				"the faces of H at the faces of the horn are the images of the members of f",
				"faces_filler(n + 1, horn_faces(n + 1, n), λi:num. p(n + 1, f(i)), H)",
				Simp(Fwd(simplicial_set.FacesFillerDef)),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					face := b.Assume()
					within := b.Have(
						"a face of the horn is at most n + 2, and not n",
						"i ≤ n + 1 + 1 ∧ ¬(i = n)",
						By(face, kan_complex.HornFacesMember.At(next, n, i)))
					b.Cases(b.Term("i < n"))
					b.When(
						"below n both are the base simplex of Y",
						func(c *Argument, below Fact) {
							c.Show(
								"the face i of H and the image of f(i) are the base simplex of Y",
								ByArith(HBelow.At(i), memberImages.At(i), below, dims))
						})
					b.Otherwise(
						"above n the face is n + 1 or n + 2, and H has z and z' there",
						func(c *Argument, notBelow Fact) {
							c.Cases(c.Term("i = n + 1"))
							c.When(
								"the face n + 1 of H is z, the image of w = f(n + 1)",
								func(e *Argument, atNext Fact) {
									e.Show(
										"so the face n + 1 of H is the image of f(n + 1)",
										atNext.Rw(),
										CalcEq(
											Leg(
												e.TermAs[B]("z"),
												"z is the face n + 1 of H",
												ByArith(HStart, dims)),
											Leg(
												e.TermAs[B]("p(n + 1, w)"),
												"w lies over z",
												By(wOver)),
											FinalLeg(
												"and w is f(n + 1)",
												By(Normalized, values)),
										))
								})
							c.Otherwise(
								"the face n + 2 of H is z', the image of w' = f(n + 2)",
								func(e *Argument, notNext Fact) {
									atTop := e.Have(
										"i is then n + 2",
										"i = n + 2",
										ByArith(notBelow, notNext, within))
									e.Show(
										"so the face n + 2 of H is the image of f(n + 2)",
										atTop.Rw(),
										CalcEq(
											Leg(
												e.TermAs[B]("z'"),
												"z' is the face n + 2 of H",
												ByArith(HEnd, dims)),
											Leg(
												e.TermAs[B]("p(n + 1, w')"),
												"w' lies over z'",
												By(wPrimeOver)),
											FinalLeg(
												"and w' is f(n + 2)",
												By(Normalized, values)),
										))
								})
						})
				}))

			v, lifted := a.ObtainAs[A](
				"so the horn lifts along the fibration to an (n+2)-simplex v of X over H",
				"∃v:A. v ∈ X.simplices(n + 2) ∧ faces_filler(n + 1, horn_faces(n + 1, n), f, v) ∧ p(n + 2, v) = H",
				By(FibrationLift.Read(fibration).At(next, n, f, H), dims, horn, HIn, images))
			lift := a.Conjuncts(
				lifted,
				"v is an (n+2)-simplex of X",
				"whose faces other than n are the members of f",
				"over H")
			vIn, vOver := lift[0], lift[2]
			faceOfV := a.Unfolded(lift[1], simplicial_set.FacesFillerDef)

			// The n-th face of v is the homotopy in the fibre.
			inFiber := a.Have(
				"the n-th face of v is an (n+1)-simplex of the fibre: "+
					"p carries it to the face n of H, the base simplex of Y",
				"X.d(n + 2, n, v) ∈ simplicial_fiber_simplices(p, p(0, x₀), n + 1)",
				Derive(func(b *Argument) {
					faceIn := b.Have(
						"the n-th face of v is an (n+1)-simplex of X",
						"X.d(n + 2, n, v) ∈ X.simplices(n + 1)",
						ByArith(simplicial_set.FaceIn.Read(source).At(next, n, v), vIn, dims))
					over := b.Have(
						"which p carries to the base simplex of Y",
						"p(n + 1, X.d(n + 2, n, v)) = base_simplex(p(0, x₀), n + 1)",
						CalcEq(
							Leg(
								b.TermAs[B]("Y.d(n + 2, n, p(n + 2, v))"),
								"p commutes with the face n",
								ByArith(simplicial_set.MapFace.Read(simplicialMap).At(next, n, v), vIn, dims)),
							Leg(
								b.TermAs[B]("Y.d(n + 2, n, H)"),
								"v lies over H",
								By(Normalized, vOver)),
							FinalLeg(
								"the face n of H, below n + 1, is the base simplex of Y",
								ByArith(HBelow.At(n), dims)),
						))
					b.Show(
						"so it lies in the fibre",
						BySets(faceIn, over, simplicialFiberSimplicesDef))
				}))
			lower := a.Have(
				"its faces below n are the base simplex",
				"∀i:num. i < n ⇒ X.d(n + 1, i, X.d(n + 2, n, v)) = base_simplex(x₀, n)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					below := b.Assume()
					b.Show(
						"its face i is the face n − 1 of the face i of v, the base simplex",
						CalcEq(
							Leg(
								b.TermAs[A]("X.d(n + 1, n - 1, X.d(n + 2, i, v))"),
								"the face identity of v at the pair (i, n)",
								ByArith(faceFace.At(n, i, n, v), vIn, below)),
							Leg(
								b.TermAs[A]("X.d(n + 1, n - 1, base_simplex(x₀, n + 1))"),
								"the face i of v is f(i), the base simplex",
								ByArith(faceOfV.At(i), kan_complex.HornFacesMember.At(next, n, i), baseValues.At(i), dims, below)),
							FinalLeg(
								"whose face n − 1 is the base simplex at n",
								ByArith(baseFace.At(x0, n, b.TermAs[Nat]("n - 1")), vertex)),
						))
				}))
			start := a.Have(
				"its face n is the n-th face of w",
				"X.d(n + 1, n, X.d(n + 2, n, v)) = X.d(n + 1, n, w)",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.d(n + 2, n + 1, v))"),
						"the face identity of v at the pair (n, n + 1)",
						ByArith(faceFace.At(n, n, next, v), vIn)),
					FinalLeg(
						"the face n + 1 of v is f(n + 1), which is w",
						ByArith(faceOfV.At(next), kan_complex.HornFacesMember.At(next, n, next), values, dims)),
				))
			end := a.Have(
				"and its face n + 1 is the n-th face of w'",
				"X.d(n + 1, n + 1, X.d(n + 2, n, v)) = X.d(n + 1, n, w')",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.d(n + 2, n + 2, v))"),
						"the face identity of v at the pair (n, n + 2)",
						ByArith(faceFace.At(n, n, top, v), vIn)),
					FinalLeg(
						"the face n + 2 of v is f(n + 2), which is w'",
						ByArith(faceOfV.At(top), kan_complex.HornFacesMember.At(next, n, top), values, dims)),
				))
			a.Do(Simp(Fwd(homotopy_group.SimplicialHomotopicDef)))
			a.Take(a.TermAs[A]("X.d(n + 2, n, v)"))
			a.Show(
				"so the n-th face of v is a homotopy in the fibre from the n-th face of w to that of w'",
				By(inFiber, lower, start, end))
		}),
})}

// ConnectingMapClass — the connecting map sends the class of a sphere
// to the class of the n-th face of any of its lifts: well defined. The
// map reads the class of z through the representative z' it chooses and
// the lift w' it chooses for z'; z is homotopic to z', so the n-th faces
// of w and w' are homotopic in the fibre, and homotopic spheres of the
// fibre share a class.
var ConnectingMapClass = connectingMapClassThm{family.Add(registry.ProofEntry{
	Name:    "ConnectingMapClass",
	Reading: "The classes are compared in the fibre, a Kan complex over any base (FiberKan).",
	Key:     "prop_b81e44ebe8fb0601",
	Build: KanFibration.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀z:B. ∀w:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"z ∈ simplicial_sphere(Y, p(0, x₀), n + 1)",
			"w ∈ X.simplices(n + 1)",
			"∀i:num. i ≤ n + 1 ∧ ¬(i = n) ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)",
			"p(n + 1, w) = z",
		},
		Conclusion: "simplicial_connecting_map(p, " +
			"    x₀, " +
			"    n, " +
			"    equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), z)) = " +
			"equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), X.d(n + 1, n, w))",
	},
		func(
			a *Argument,
			fibration Fact,
			x0 *Expr[A],
			vertex Fact,
			n *Expr[Nat],
			z *Expr[B],
			zSphere Fact,
			w *Expr[A],
			wIn, wFaces, wOver Fact,
		) {
			simplicialMap := FibrationMap.Read(fibration)
			target := simplicial_set.MapTarget.Read(simplicialMap)
			X := a.TermAs[simplicial_set.SimplicialOps[A]]("X")
			Y := a.TermAs[simplicial_set.SimplicialOps[B]]("Y")
			p := a.TermAs[Fun2[Nat, A, B]]("p")
			y0, next := a.TermAs[B]("p(0, x₀)"), a.TermAs[Nat]("n + 1")
			class := a.TermAs[Set[B]]("equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), z)")

			baseVertex := a.Have(
				"p(0, x₀) is a vertex of Y",
				"p(0, x₀) ∈ Y.simplices(0)",
				By(simplicial_set.MapIn.Read(simplicialMap).At(a.TermAs[Nat]("0"), x0), vertex))

			homotopicInY := a.TermAs[Fun2[B, B, Bool]]("simplicial_homotopic(Y, p(0, x₀), n + 1)")
			zPrime, zPrimeDef := a.LetAs[B](
				"z'", "εy:B. y ∈ equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), z)")
			toZPrime := a.Have(
				"z is homotopic to itself, so to the representative z' the connecting map chooses in its class",
				"simplicial_homotopic(Y, p(0, x₀), n + 1, z, z')",
				zPrimeDef.Rw(),
				By(
					homotopy_group.HomotopicRefl.Read(target).At(y0, next, z),
					baseVertex,
					zSphere,
					equivalence.ChosenRepresentative.At(homotopicInY, z)))
			zPrimeSphere := a.Have(
				"so z', homotopic to the sphere z, is a sphere",
				"z' ∈ simplicial_sphere(Y, p(0, x₀), n + 1)",
				By(
					homotopy_group.HomotopicSphere.Read(target).At(y0, next, z, zPrime),
					baseVertex,
					toZPrime,
					zSphere))

			wPrime, wPrimeDef := a.LetAs[A](
				"w'",
				"εv:A. "+
					"    v ∈ X.simplices(n + 1) ∧ "+
					"    (∀i:num. i ≤ n + 1 ∧ ¬(i = n) ⇒ X.d(n + 1, i, v) = base_simplex(x₀, n)) ∧ "+
					"    p(n + 1, v) = z'")
			_, liftChosen := a.ObtainChosen(
				"z' lifts with the base simplex at every face but the "+
					"n-th, and the connecting map chooses such a lift w'",
				"∃v:A. "+
					"    v ∈ X.simplices(n + 1) ∧ "+
					"    (∀i:num. i ≤ n + 1 ∧ ¬(i = n) ⇒ X.d(n + 1, i, v) = base_simplex(x₀, n)) ∧ "+
					"    p(n + 1, v) = z'",
				ConnectingLiftExists.Read(fibration).At(x0, n, zPrime),
				vertex,
				zPrimeSphere)
			lifted := a.Have(
				"so w' is such a lift of z'",
				"w' ∈ X.simplices(n + 1) ∧ "+
					"(∀i:num. i ≤ n + 1 ∧ ¬(i = n) ⇒ X.d(n + 1, i, w') = base_simplex(x₀, n)) ∧ "+
					"p(n + 1, w') = z'",
				By(Normalized, wPrimeDef, liftChosen))
			homotopic := a.Have(
				"w and w' lift the homotopic z and z', so their n-th faces are homotopic in the fibre",
				"simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n, X.d(n + 1, n, w), X.d(n + 1, n, w'))",
				By(
					ConnectingHomotopic.Read(fibration).At(x0, n, z, zPrime, w, wPrime),
					vertex,
					toZPrime,
					wIn,
					wFaces,
					wOver,
					lifted))

			fiberKan := a.Have(
				"the fibre over p(0, x₀) is a Kan complex",
				"kan_complex(simplicial_fiber(p, p(0, x₀)))",
				By(FiberKan.Read(fibration).At(y0), baseVertex))
			face, facePrime := a.TermAs[A]("X.d(n + 1, n, w)"), a.TermAs[A]("X.d(n + 1, n, w')")
			faceSphere := a.Have(
				"the n-th face of the lift w is a sphere of the fibre",
				"X.d(n + 1, n, w) ∈ simplicial_sphere(simplicial_fiber(p, p(0, x₀)), x₀, n)",
				By(ConnectingLiftFace.Read(fibration).At(x0, n, z, w), vertex, zSphere, wIn, wFaces, wOver))
			facePrimeSphere := a.Have(
				"and so is that of the lift w'",
				"X.d(n + 1, n, w') ∈ simplicial_sphere(simplicial_fiber(p, p(0, x₀)), x₀, n)",
				By(ConnectingLiftFace.Read(fibration).At(x0, n, zPrime, wPrime), vertex, zPrimeSphere, lifted))

			a.Show(
				"the connecting map gives the class of the n-th face of w', which is that of w",
				CalcEq(
					Leg(
						a.TermAs[Set[A]](
							"equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), X.d(n + 1, n, w'))"),
						"the connecting map reads the class of z through the representative z' and its lift w'",
						By(SimplicialConnectingMapDef.At(X, Y, p, x0, n, class), wPrimeDef, zPrimeDef)),
					FinalLeg(
						"the two n-th faces are homotopic spheres of the fibre at its vertex x₀, so they share a class",
						By(
							homotopy_group.ClassEqIff.Read(fiberKan).At(x0, n, face, facePrime),
							FiberBasePoint.At(X, Y, p, x0),
							vertex,
							faceSphere,
							facePrimeSphere,
							homotopic)),
				))
		}),
})}

// ConnectingMapIn — the connecting map carries πₙ₊₁(Y, p(0, x₀)) into
// πₙ(F, x₀): represent a class by a sphere, lift it, and take the class
// of its n-th face, a sphere of the fibre.
var ConnectingMapIn = connectingMapInThm{family.Add(registry.ProofEntry{
	Name: "ConnectingMapIn",
	Key:  "prop_ce18c8afcf51c2bf",
	Build: KanFibration.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀L:set(B).",
		Hypotheses: []string{
			"kan_complex(Y)",
			"x₀ ∈ X.simplices(0)",
			"L ∈ simplicial_homotopy_group(Y, p(0, x₀), n + 1)",
		},
		Conclusion: "simplicial_connecting_map(p, x₀, n, L) ∈ " +
			"simplicial_homotopy_group(simplicial_fiber(p, p(0, x₀)), x₀, n)",
	},
		func(
			a *Argument,
			fibration Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			hypotheses Fact,
			L *Expr[Set[B]],
			inGroup Fact,
		) {
			simplicialMap := FibrationMap.Read(fibration)
			target := simplicial_set.MapTarget.Read(simplicialMap)
			X := a.TermAs[simplicial_set.SimplicialOps[A]]("X")
			Y := a.TermAs[simplicial_set.SimplicialOps[B]]("Y")
			p := a.TermAs[Fun2[Nat, A, B]]("p")
			y0, next := a.TermAs[B]("p(0, x₀)"), a.TermAs[Nat]("n + 1")

			baseVertex := a.Have(
				"p(0, x₀) is a vertex of Y",
				"p(0, x₀) ∈ Y.simplices(0)",
				By(simplicial_set.MapIn.Read(simplicialMap).At(a.TermAs[Nat]("0"), x0), hypotheses))
			z, represented := a.ObtainAs[B](
				"L is the class of a sphere z of Y",
				"∃z:B. "+
					"    z ∈ simplicial_sphere(Y, p(0, x₀), n + 1) ∧ "+
					"    L = equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), z)",
				By(homotopy_group.InHomotopyGroup.Read(target).At(y0, next, L), baseVertex, inGroup))
			w, lifted := a.ObtainAs[A](
				"z lifts with the base simplex at every face but the n-th",
				"∃w:A. "+
					"    w ∈ X.simplices(n + 1) ∧ "+
					"    (∀i:num. i ≤ n + 1 ∧ ¬(i = n) ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ "+
					"    p(n + 1, w) = z",
				By(ConnectingLiftExists.Read(fibration).At(x0, n, z), hypotheses, represented))
			fiberKan := a.Have(
				"the fibre over p(0, x₀) is a Kan complex",
				"kan_complex(simplicial_fiber(p, p(0, x₀)))",
				By(FiberKan.Read(fibration).At(y0), baseVertex))
			faceSphere := a.Have(
				"the n-th face of w is a sphere of the fibre",
				"X.d(n + 1, n, w) ∈ simplicial_sphere(simplicial_fiber(p, p(0, x₀)), x₀, n)",
				By(ConnectingLiftFace.Read(fibration).At(x0, n, z, w), hypotheses, represented, lifted))
			a.Show(
				"the connecting image of L is the class of this sphere of the fibre",
				By(
					hypotheses,
					faceSphere,
					represented,
					lifted,
					ConnectingMapClass.Read(fibration).At(x0, n, z, w),
					FiberBasePoint.At(X, Y, p, x0),
					homotopy_group.ClassInHomotopyGroup.Read(kan_complex.KanSimplicialSet.Read(fiberKan)).At(
						x0, n, a.TermAs[A]("X.d(n + 1, n, w)"))))
		}),
})}

// ConnectingProductLift — lifts of the last two faces of a product
// filler determine a lift of its n-th face whose last faces are their
// n-th faces: fill the horn with those two lifts and the base simplices,
// then read the n-th face of its filler.
var ConnectingProductLift = connectingProductLiftThm{family.Add(registry.ProofEntry{
	Name: "ConnectingProductLift",
	Key:  "prop_fa204bfb6964a21d",
	Build: KanFibration.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀W:B. ∀u v:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"W ∈ Y.simplices(n + 2)",
			"∀i:num. i < n ⇒ Y.d(n + 2, i, W) = base_simplex(p(0, x₀), n + 1)",
			"u ∈ X.simplices(n + 1)",
			"v ∈ X.simplices(n + 1)",
			"∀i:num. " +
				"    i ≤ n + 1 ∧ ¬(i = n) ⇒ " +
				"    X.d(n + 1, i, u) = base_simplex(x₀, n) ∧ X.d(n + 1, i, v) = base_simplex(x₀, n)",
			"p(n + 1, u) = Y.d(n + 2, n + 2, W)",
			"p(n + 1, v) = Y.d(n + 2, n + 1, W)",
		},
		Conclusion: "∃t:A. " +
			"    t ∈ X.simplices(n + 1) ∧ " +
			"    p(n + 1, t) = Y.d(n + 2, n, W) ∧ " +
			"    (∀i:num. i < n ⇒ X.d(n + 1, i, t) = base_simplex(x₀, n)) ∧ " +
			"    X.d(n + 1, n, t) = X.d(n + 1, n, v) ∧ " +
			"    X.d(n + 1, n + 1, t) = X.d(n + 1, n, u)",
	},
		func(
			a *Argument,
			fibration Fact,
			x0 *Expr[A],
			vertex Fact,
			n *Expr[Nat],
			W *Expr[B],
			WIn, WBelow Fact,
			u, v *Expr[A],
			given Fact,
		) {
			simplicialMap := FibrationMap.Read(fibration)
			source := simplicial_set.MapSource.Read(simplicialMap)
			faceFace, baseFace :=
				simplicial_set.FaceFace.Read(source), simplicial_set.BaseSimplexFace.Read(source)
			next, top := a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 2")
			parts := a.Conjuncts(
				given,
				"u is an (n+1)-simplex of X",
				"and so is v",
				"their faces other than n are the base simplex",
				"u lies over the last face of W",
				"and v lies over the penultimate face")
			uIn, vIn, liftFaces, uOver, vOver := parts[0], parts[1], parts[2], parts[3], parts[4]

			f, fDef := a.LetAs[Fun[Nat, A]](
				"f", "λi:num. COND(i = n + 1, v, COND(i = n + 2, u, base_simplex(x₀, n + 1)))")
			values := a.Have(
				"the last two members of the horn are v and u",
				"f(n + 1) = v ∧ f(n + 2) = u",
				fDef.Rw(),
				ByArith())
			baseValues := a.Have(
				"its members below n are the base simplex",
				"∀i:num. i < n ⇒ f(i) = base_simplex(x₀, n + 1)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
			members := a.Have(
				"each member is an (n+1)-simplex of X",
				"∀i:num. f(i) ∈ X.simplices(n + 1)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action {
					return Chain(CondRewrite(), ByArith(
						uIn,
						vIn,
						simplicial_set.BaseSimplexIn.Read(source).At(x0, next),
						vertex))
				}))
			lowerFaces := a.Have(
				"every member has the base simplex for its faces below n",
				"∀j i:num. i < n ⇒ X.d(n + 1, i, f(j)) = base_simplex(x₀, n)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					i := b.FixAs[Nat]()
					below := b.Assume()
					b.Show(
						"u, v and the base simplex all have that face",
						fDef.Rw(),
						CondRewrite(),
						ByArith(liftFaces.At(i), baseFace.At(x0, n, i), below, vertex))
				}))
			lastFaces := a.Have(
				"and its face n + 1 is the base simplex",
				"∀j:num. X.d(n + 1, n + 1, f(j)) = base_simplex(x₀, n)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action {
					return Chain(CondRewrite(), ByArith(liftFaces.At(next), baseFace.At(x0, n, next), vertex))
				}))
			compatible := a.Have(
				"the lower faces and the last pair agree on their intersections",
				"faces_compatible(n + 1, horn_faces(n + 1, n), f)",
				Simp(Fwd(simplicial_set.FacesCompatibleDef)),
				Derive(func(b *Argument) {
					i, j := b.FixAs[Nat](), b.FixAs[Nat]()
					faces := b.Assume()
					pair := b.Have(
						"the two horn indices are ordered, at most n + 2, and neither is n",
						"i < j ∧ j ≤ n + 1 + 1 ∧ ¬(i = n) ∧ ¬(j = n)",
						By(faces, kan_complex.HornFacesMember.At(next, n, i), kan_complex.HornFacesMember.At(next, n, j)))
					notBelow := b.Unless(
						b.Term("i < n"),
						"below n both intersections are the base simplex",
						Given(func(c *Argument, below Fact) {
							c.Show(
								"the face i of f(j) and the face j − 1 of f(i) are the base simplex",
								ByArith(
									lowerFaces.At(j, i),
									baseValues.At(i),
									baseFace.At(x0, n, c.TermAs[Nat]("j - 1")),
									below,
									pair,
									vertex))
						}))
					atNext := b.Have(
						"otherwise i is n + 1",
						"i = n + 1",
						ByArith(notBelow, pair))
					atTop := b.Have(
						"and j is n + 2",
						"j = n + 2",
						ByArith(notBelow, pair))
					b.Show(
						"the faces n + 1 of these last two members are both the base simplex",
						atNext.Rw(),
						atTop.Rw(),
						ByArith(lastFaces.At(next), lastFaces.At(top)))
				}))
			horn := a.Have(
				"so f is a horn of X missing face n",
				"face_family(X, n + 1, horn_faces(n + 1, n), f)",
				Simp(Fwd(simplicial_set.FaceFamilyDef)),
				By(members, compatible))
			dims := a.Have(
				"the horn lifts in dimension n + 2 and n is a face index",
				"n + 1 + 1 = n + 2 ∧ n ≤ n + 1 + 1",
				ByArith())
			images := a.Have(
				"the horn maps to the corresponding faces of W",
				"faces_filler(n + 1, horn_faces(n + 1, n), λi:num. p(n + 1, f(i)), W)",
				Simp(Fwd(simplicial_set.FacesFillerDef)),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					face := b.Assume()
					b.Show(
						"the last two members lie over their faces of W, and the lower members map to its base faces",
						fDef.Rw(),
						CondRewrite(),
						ByArith(
							WBelow.At(i),
							uOver,
							vOver,
							face,
							dims,
							vertex,
							kan_complex.HornFacesMember.At(next, n, i),
							simplicial_set.MapBaseSimplex.Read(simplicialMap).At(x0, next)))
				}))
			T, lifted := a.ObtainAs[A](
				"the horn lifts to an (n+2)-simplex T over W",
				"∃T:A. T ∈ X.simplices(n + 2) ∧ faces_filler(n + 1, horn_faces(n + 1, n), f, T) ∧ p(n + 2, T) = W",
				By(FibrationLift.Read(fibration).At(next, n, f, W), dims, horn, WIn, images))
			lift := a.Conjuncts(
				lifted,
				"T is an (n+2)-simplex",
				"whose prescribed faces are f",
				"and whose image is W")
			TIn, TOver := lift[0], lift[2]
			faceOfT := a.Unfolded(lift[1], simplicial_set.FacesFillerDef)

			a.Take(a.TermAs[A]("X.d(n + 2, n, T)"))
			a.Do(SplitConjAll(
				Case(
					"the n-th face of T is an (n+1)-simplex",
					ByArith(simplicial_set.FaceIn.Read(source).At(next, n, T), TIn, dims)),
				Case(
					"p carries it to the n-th face of W",
					ByArith(simplicial_set.MapFace.Read(simplicialMap).At(next, n, T), TIn, TOver, dims)),
				Case(
					"its faces below n are the base simplex",
					Derive(func(b *Argument) {
						i := b.FixAs[Nat]()
						below := b.Assume()
						b.Show(
							"its face i is the face n − 1 of the base simplex at face i of T",
							ByArith(
								faceFace.At(n, i, n, T),
								TIn,
								below,
								dims,
								faceOfT.At(i),
								kan_complex.HornFacesMember.At(next, n, i),
								baseValues.At(i),
								baseFace.At(x0, n, b.TermAs[Nat]("n - 1")),
								vertex))
					})),
				Case(
					"its face n is the n-th face of v, the face n + 1 of T",
					ByArith(
						faceFace.At(n, n, next, T),
						TIn,
						dims,
						faceOfT.At(next),
						kan_complex.HornFacesMember.At(next, n, next),
						values)),
				Case(
					"its face n + 1 is the n-th face of u, the face n + 2 of T",
					ByArith(
						faceFace.At(n, n, top, T),
						TIn,
						dims,
						faceOfT.At(top),
						kan_complex.HornFacesMember.At(next, n, top),
						values))))
		}),
})}

// ConnectingProductClass — the boundary classes of standard lifts preserve
// a product filler: two lifted horns and an inverse filler reduce the
// boundary equation to left cancellation in the homotopy group of the fibre.
var ConnectingProductClass = connectingProductClassThm{family.Add(registry.ProofEntry{
	Name: "ConnectingProductClass",
	Key:  "prop_b46bc1c861b2258",
	Build: KanFibration.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀z zprime W:B. ∀u v w:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"0 < n",
			"z ∈ simplicial_sphere(Y, p(0, x₀), n + 1)",
			"zprime ∈ simplicial_sphere(Y, p(0, x₀), n + 1)",
			"W ∈ Y.simplices(n + 2)",
			"∀i:num. i < n ⇒ Y.d(n + 2, i, W) = base_simplex(p(0, x₀), n + 1)",
			"Y.d(n + 2, n + 2, W) = z",
			"Y.d(n + 2, n, W) = zprime",
			"u ∈ X.simplices(n + 1)",
			"v ∈ X.simplices(n + 1)",
			"w ∈ X.simplices(n + 1)",
			"∀i:num. " +
				"    i ≤ n + 1 ∧ i ≠ n ⇒ " +
				"    X.d(n + 1, i, u) = base_simplex(x₀, n) ∧ " +
				"    X.d(n + 1, i, v) = base_simplex(x₀, n) ∧ " +
				"    X.d(n + 1, i, w) = base_simplex(x₀, n)",
			"p(n + 1, u) = z",
			"p(n + 1, v) = Y.d(n + 2, n + 1, W)",
			"p(n + 1, w) = zprime",
		},
		Conclusion: "«C» = simplicial_homotopy_mul(«F», x₀, n, «A», «B»)",
		Abbrev: Abbrev{
			{Name: "F", Text: "simplicial_fiber(p, p(0, x₀))"},
			{Name: "A", Text: "equivalence_class(simplicial_homotopic(«F», x₀, n), X.d(n + 1, n, u))"},
			{Name: "C", Text: "equivalence_class(simplicial_homotopic(«F», x₀, n), X.d(n + 1, n, v))"},
			{Name: "B", Text: "equivalence_class(simplicial_homotopic(«F», x₀, n), X.d(n + 1, n, w))"},
		},
	}, func(
		a *Argument,
		fibration Fact,
		x0 *Expr[A],
		vertex Fact,
		n *Expr[Nat],
		positive Fact,
		z, zprime, W *Expr[B],
		u, v, w *Expr[A],
		given Fact,
	) {
		X, Y, p :=
			a.TermAs[simplicial_set.SimplicialOps[A]]("X"),
			a.TermAs[simplicial_set.SimplicialOps[B]]("Y"),
			a.TermAs[Fun2[Nat, A, B]]("p")
		simplicialMap := FibrationMap.Read(fibration)
		source, target :=
			simplicial_set.MapSource.Read(simplicialMap), simplicial_set.MapTarget.Read(simplicialMap)
		baseFace, faceFace :=
			simplicial_set.BaseSimplexFace.Read(source), simplicial_set.FaceFace.Read(source)
		next, top, previous := a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 2"), a.TermAs[Nat]("n - 1")
		y0 := a.TermAs[B]("p(0, x₀)")
		parts := a.Conjuncts(
			given,
			"z is a sphere of Y",
			"zprime is a sphere of Y",
			"W is the product simplex",
			"the lower faces of W are base simplices",
			"its last face is z",
			"its n-th face is zprime",
			"u is a simplex of X",
			"v is a simplex of X",
			"w is a simplex of X",
			"the three lifts have base faces away from n",
			"u lies over z",
			"v lies over the middle face",
			"w lies over zprime")
		zSphere, zprimeSphere, WIn, WBelow, WLast, WAtN :=
			parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
		uIn, vIn, wIn, liftFaces, uOver, vOver, wOver :=
			parts[6], parts[7], parts[8], parts[9], parts[10], parts[11], parts[12]
		baseVertex := a.Have(
			"the image of the base vertex is a vertex",
			"p(0, x₀) ∈ Y.simplices(0)",
			By(vertex, simplicial_set.MapIn.Read(simplicialMap).At(a.TermAs[Nat]("0"), x0)))
		fiberKan := a.Have(
			"the fibre is Kan",
			"kan_complex(«F»)",
			By(baseVertex, FiberKan.Read(fibration).At(y0)))
		fiberVertex := a.Have(
			"x₀ is a vertex of the fibre",
			"x₀ ∈ simplicial_fiber_simplices(p, p(0, x₀), 0)",
			By(vertex, FiberBasePoint.At(X, Y, p, x0)))
		fiberSimplicial := kan_complex.KanSimplicialSet.Read(fiberKan)
		dims := a.Have(
			"the successor and predecessor dimensions agree",
			"n + 1 + 1 = n + 2 ∧ n + 1 - 1 = n ∧ 0 < n + 1 ∧ n - 1 + 1 = n",
			ByArith(positive))
		WProductLower := a.Have(
			"the lower faces satisfy the product filler convention",
			"∀i:num. i + 1 < n + 1 ⇒ Y.d(n + 2, i, W) = base_simplex(p(0, x₀), n + 1)",
			a.ForEach(func(i *Expr[Nat]) Action { return ByArith(WBelow.At(i)) }))
		middleSphere := a.Have(
			"the middle face of W is a sphere",
			"Y.d(n + 2, n + 1, W) ∈ simplicial_sphere(Y, p(0, x₀), n + 1)",
			ByArith(
				baseVertex,
				zSphere,
				zprimeSphere,
				WIn,
				WProductLower,
				WLast,
				WAtN,
				dims,
				homotopy_group.ProductSphere.Read(target).At(y0, next, z, zprime, W)))
		aFace, bFace, cFace :=
			a.TermAs[A]("X.d(n + 1, n, u)"), a.TermAs[A]("X.d(n + 1, n, w)"), a.TermAs[A]("X.d(n + 1, n, v)")
		aSphere := a.Have(
			"the boundary of u is a fibre sphere",
			"X.d(n + 1, n, u) ∈ simplicial_sphere(«F», x₀, n)",
			By(vertex, uIn, uOver, liftFaces, zSphere, ConnectingLiftFace.Read(fibration).At(x0, n, z, u)))
		cSphere := a.Have(
			"the boundary of v is a fibre sphere",
			"X.d(n + 1, n, v) ∈ simplicial_sphere(«F», x₀, n)",
			By(
				vertex,
				vIn,
				vOver,
				liftFaces,
				middleSphere,
				ConnectingLiftFace.Read(fibration).At(x0, n, a.TermAs[B]("Y.d(n + 2, n + 1, W)"), v)))
		bSphere := a.Have(
			"the boundary of w is a fibre sphere",
			"X.d(n + 1, n, w) ∈ simplicial_sphere(«F», x₀, n)",
			By(
				vertex,
				wIn,
				wOver,
				liftFaces,
				zprimeSphere,
				ConnectingLiftFace.Read(fibration).At(x0, n, zprime, w)))
		pairLiftFaces := a.Have(
			"u and v have the standard connecting faces",
			Statement{
				Binders:    "∀i:num.",
				Hypotheses: []string{"i ≤ n + 1", "i ≠ n"},
				Conclusion: "X.d(n + 1, i, u) = base_simplex(x₀, n) ∧ X.d(n + 1, i, v) = base_simplex(x₀, n)",
			},
			By(liftFaces))
		_, lifted := a.ObtainAs[A](
			"lift the product horn to obtain t over zprime",
			"∃t:A. "+
				"    t ∈ X.simplices(n + 1) ∧ "+
				"    p(n + 1, t) = Y.d(n + 2, n, W) ∧ "+
				"    (∀i:num. i < n ⇒ X.d(n + 1, i, t) = base_simplex(x₀, n)) ∧ "+
				"    X.d(n + 1, n, t) = X.d(n + 1, n, v) ∧ "+
				"    X.d(n + 1, n + 1, t) = X.d(n + 1, n, u)",
			By(
				vertex,
				WIn,
				WBelow,
				WLast,
				uIn,
				vIn,
				pairLiftFaces,
				uOver,
				vOver,
				ConnectingProductLift.Read(fibration).At(x0, n, W, u, v)))
		tParts := a.Conjuncts(
			lifted,
			"t is a simplex of X",
			"t lies over the n-th face of W",
			"its lower faces are base simplices",
			"its n-th face is the boundary of v",
			"its last face is the boundary of u")
		tIn, tOver, tBelow, tN, tLast := tParts[0], tParts[1], tParts[2], tParts[3], tParts[4]
		r, inverseFilled := a.ObtainAs[A](
			"choose an inverse filler for the boundary of u in the fibre",
			"∃r:A. "+
				"    r ∈ simplicial_fiber_simplices(p, p(0, x₀), n + 1) ∧ "+
				"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, r) = base_simplex(x₀, n)) ∧ "+
				"    X.d(n + 1, n - 1, r) = X.d(n + 1, n, u) ∧ "+
				"    X.d(n + 1, n, r) = base_simplex(x₀, n)",
			By(
				fiberVertex,
				positive,
				aSphere,
				homotopy_group.InverseFillerExists.Read(fiberKan).At(x0, n, aFace)))
		rParts := a.Conjuncts(
			inverseFilled,
			"r is a simplex of the fibre",
			"its lower faces are base simplices",
			"its preceding face is the boundary of u",
			"its n-th face is the base simplex")
		rFiberIn, rBelow, rPrevious, rN := rParts[0], rParts[1], rParts[2], rParts[3]
		rInAndOver := a.Have(
			"r is a simplex of X lying over the base simplex",
			"r ∈ X.simplices(n + 1) ∧ p(n + 1, r) = base_simplex(p(0, x₀), n + 1)",
			BySets(rFiberIn, simplicialFiberSimplicesDef))
		aPrime := a.TermAs[A]("X.d(n + 1, n + 1, r)")
		aPrimeSphere := a.Have(
			"the last face of the inverse filler is a fibre sphere",
			"X.d(n + 1, n + 1, r) ∈ simplicial_sphere(«F», x₀, n)",
			By(
				fiberVertex,
				positive,
				aSphere,
				inverseFilled,
				homotopy_group.InverseSphere.Read(fiberSimplicial).At(x0, n, aFace, r)))
		D, DDef := a.LetAs[B]("D", "Y.s(n + 1, n - 1, zprime)")
		DShape := a.Have(
			"the degeneracy repeats zprime at n − 1 and n and has base faces elsewhere",
			"D ∈ Y.simplices(n + 2) ∧ "+
				"Y.d(n + 2, n - 1, D) = zprime ∧ "+
				"Y.d(n + 2, n, D) = zprime ∧ "+
				"(∀i:num. i ≤ n + 2 ∧ i ≠ n - 1 ∧ i ≠ n ⇒ Y.d(n + 2, i, D) = base_simplex(p(0, x₀), n + 1))",
			DDef.Rw(),
			ByArith(
				baseVertex,
				zprimeSphere,
				dims,
				positive,
				homotopy_group.SphereDegeneracyFaces.Read(target).At(y0, next, zprime, previous)))
		DParts := a.Conjuncts(
			DShape,
			"D is a simplex of Y",
			"its preceding face is zprime",
			"its n-th face is zprime",
			"its other faces are base simplices")
		DIn, DPrevious, DN, DOther := DParts[0], DParts[1], DParts[2], DParts[3]
		f, fDef := a.LetAs[Fun[Nat, A]](
			"f", "λi:num. COND(i = n - 1, t, COND(i = n, w, COND(i = n + 2, r, base_simplex(x₀, n + 1))))")
		values := a.Have(
			"the three nonconstant members of the horn are t, w and r",
			"f(n - 1) = t ∧ f(n) = w ∧ f(n + 2) = r",
			fDef.Rw(),
			ByArith(positive))
		baseValues := a.Have(
			"the earlier members are base simplices",
			"∀i:num. i + 1 < n ⇒ f(i) = base_simplex(x₀, n + 1)",
			fDef.Rw(),
			a.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
		members := a.Have(
			"every member is an (n+1)-simplex of X",
			"∀i:num. f(i) ∈ X.simplices(n + 1)",
			fDef.Rw(),
			a.ForEach(func(_ *Expr[Nat]) Action {
				return Chain(CondRewrite(), ByArith(
					vertex,
					tIn,
					wIn,
					rInAndOver,
					simplicial_set.BaseSimplexIn.Read(source).At(x0, next)))
			}))
		lowerFaces := a.Have(
			"all members have base faces below n − 1",
			"∀j i:num. i + 1 < n ⇒ X.d(n + 1, i, f(j)) = base_simplex(x₀, n)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]()
				i := b.FixAs[Nat]()
				below := b.Assume()
				b.Show(
					"each of t, w, r and the base simplex has the required face",
					fDef.Rw(),
					CondRewrite(),
					ByArith(vertex, below, tBelow.At(i), rBelow.At(i), liftFaces.At(i), baseFace.At(x0, n, i)))
			}))
		compatible := a.Have(
			"the members form a compatible horn missing n + 1",
			"faces_compatible(n + 1, horn_faces(n + 1, n + 1), f)",
			Simp(Fwd(simplicial_set.FacesCompatibleDef)),
			Derive(func(b *Argument) {
				i, j := b.FixAs[Nat](), b.FixAs[Nat]()
				indices := b.Assume()
				pair := b.Have(
					"the ordered indices avoid the missing face",
					"i < j ∧ j ≤ n + 1 + 1 ∧ i ≠ n + 1 ∧ j ≠ n + 1",
					By(
						indices,
						kan_complex.HornFacesMember.At(next, next, i),
						kan_complex.HornFacesMember.At(next, next, j)))
				notBelow := b.Unless(
					b.Term("i + 1 < n"),
					"below n − 1 both faces are base simplices",
					Given(func(c *Argument, below Fact) {
						c.Show(
							"use the lower face table and the face of a base simplex",
							ByArith(
								lowerFaces.At(j, i),
								baseValues.At(i),
								pair,
								vertex,
								below,
								baseFace.At(x0, n, c.TermAs[Nat]("j - 1"))))
					}))
				jNotN := b.Unless(
					b.Term("j = n"),
					"the pair (n − 1, n) has two base faces",
					Given(func(c *Argument, jAtN Fact) {
						iAtPrevious := c.Have(
							"the first index is n − 1",
							"i = n - 1",
							ByArith(pair, notBelow, jAtN))
						c.Show(
							"the faces of w and t agree",
							iAtPrevious.Rw(),
							jAtN.Rw(),
							ByArith(values, positive, tBelow.At(previous), liftFaces.At(previous)))
					}))
				jAtTop := b.Have(
					"the remaining second index is n + 2",
					"j = n + 2",
					ByArith(pair, notBelow, jNotN))
				b.Show(
					"compare r with t or w",
					jAtTop.Rw(),
					Derive(func(c *Argument) {
						iNotPrevious := c.Unless(
							c.Term("i = n - 1"),
							"the pair (n − 1, n + 2) shares the boundary of u",
							Given(func(e *Argument, iAtPrevious Fact) {
								e.Show(
									"the preceding face of r equals the last face of t",
									iAtPrevious.Rw(),
									ByArith(values, positive, rPrevious, tLast))
							}))
						iAtN := c.Have(
							"the final pair starts at n",
							"i = n",
							ByArith(pair, notBelow, iNotPrevious, jAtTop))
						c.Show(
							"the n-th face of r and last face of w are base simplices",
							iAtN.Rw(),
							ByArith(values, rN, liftFaces.At(next)))
					}))
			}))
		horn := a.Have(
			"the compatible members are a horn of X",
			"face_family(X, n + 1, horn_faces(n + 1, n + 1), f)",
			Simp(Fwd(simplicial_set.FaceFamilyDef)),
			By(members, compatible))
		images := a.Have(
			"D fills the images of the horn",
			"faces_filler(Y.d, n + 1, horn_faces(n + 1, n + 1), λi:num. p(n + 1, f(i)), D)",
			Simp(Fwd(simplicial_set.FacesFillerDef)),
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]()
				face := b.Assume()
				b.Show(
					"the two repeated faces lie over zprime and the others over the base simplex",
					fDef.Rw(),
					CondRewrite(),
					ByArith(
						DPrevious,
						DN,
						tOver,
						WAtN,
						wOver,
						rInAndOver,
						vertex,
						positive,
						dims,
						face,
						DOther.At(i),
						kan_complex.HornFacesMember.At(next, next, i),
						simplicial_set.MapBaseSimplex.Read(simplicialMap).At(x0, next)))
			}))
		S, secondLifted := a.ObtainAs[A](
			"lift this horn over D",
			"∃S:A. "+
				"    S ∈ X.simplices(n + 2) ∧ "+
				"    faces_filler(n + 1, horn_faces(n + 1, n + 1), f, S) ∧ "+
				"    p(n + 2, S) = D",
			ByArith(FibrationLift.Read(fibration).At(next, next, f, D), dims, horn, DIn, images))
		SParts := a.Conjuncts(
			secondLifted,
			"S is a simplex of X",
			"S fills the horn",
			"S lies over D")
		SIn, SFills, SOver := SParts[0], SParts[1], SParts[2]
		SFace := a.Unfolded(SFills, simplicial_set.FacesFillerDef)
		q, qDef := a.LetAs[A]("q", "X.d(n + 2, n + 1, S)")
		qIn := a.Have(
			"the missing face is an (n+1)-simplex",
			"q ∈ X.simplices(n + 1)",
			qDef.Rw(),
			ByArith(simplicial_set.FaceIn.Read(source).At(next, next, S), SIn, dims))
		qOver := a.Have(
			"the missing face lies over the base simplex",
			"p(n + 1, q) = base_simplex(p(0, x₀), n + 1)",
			qDef.Rw(),
			ByArith(
				simplicial_set.MapFace.Read(simplicialMap).At(next, next, S),
				SIn,
				dims,
				SOver,
				positive,
				DOther.At(next)))
		qFiberIn := a.Have(
			"q is therefore a simplex of the fibre",
			"q ∈ simplicial_fiber_simplices(p, p(0, x₀), n + 1)",
			BySets(qIn, qOver, simplicialFiberSimplicesDef))
		qBelow := a.Have(
			"the lower faces of q are base simplices",
			"∀i:num. i + 1 < n ⇒ X.d(n + 1, i, q) = base_simplex(x₀, n)",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]()
				below := b.Assume()
				b.Show(
					"commute the two faces and use the base members of the horn",
					qDef.Rw(),
					ByArith(
						SIn,
						dims,
						vertex,
						below,
						SFace.At(i),
						baseValues.At(i),
						faceFace.At(n, i, next, S),
						kan_complex.HornFacesMember.At(next, next, i),
						baseFace.At(x0, n, n)))
			}))
		qLast := a.Have(
			"the last face of q is the last face of r",
			"X.d(n + 1, n + 1, q) = X.d(n + 1, n + 1, r)",
			qDef.Rw(),
			ByArith(
				SIn,
				dims,
				positive,
				values,
				SFace.At(top),
				faceFace.At(n, next, top, S),
				kan_complex.HornFacesMember.At(next, next, top)))
		qPrevious := a.Have(
			"the preceding face of q is the boundary of v",
			"X.d(n + 1, n - 1, q) = X.d(n + 1, n, v)",
			qDef.Rw(),
			ByArith(
				SIn,
				dims,
				positive,
				values,
				tN,
				SFace.At(previous),
				faceFace.At(n, previous, next, S),
				kan_complex.HornFacesMember.At(next, next, previous)))
		qN := a.Have(
			"the n-th face of q is the boundary of w",
			"X.d(n + 1, n, q) = X.d(n + 1, n, w)",
			qDef.Rw(),
			ByArith(
				SIn,
				dims,
				positive,
				values,
				SFace.At(n),
				faceFace.At(n, n, next, S),
				kan_complex.HornFacesMember.At(next, next, n)))
		aClass, bClass, cClass := a.TermAs[Set[A]]("«A»"), a.TermAs[Set[A]]("«B»"), a.TermAs[Set[A]]("«C»")
		aPrimeClass := a.TermAs[Set[A]](
			"equivalence_class(simplicial_homotopic(«F», x₀, n), X.d(n + 1, n + 1, r))")
		productEquation := a.Have(
			"q multiplies the inverse boundary class by the boundary of v to give the boundary of w",
			"simplicial_homotopy_mul(«F», "+
				"    x₀, "+
				"    n, "+
				"    equivalence_class(simplicial_homotopic(«F», x₀, n), X.d(n + 1, n + 1, r)), "+
				"    «C») = "+
				"«B»",
			By(
				fiberVertex,
				positive,
				aPrimeSphere,
				cSphere,
				qFiberIn,
				qBelow,
				qLast,
				qPrevious,
				qN,
				homotopy_group.MulClass.Read(fiberKan).At(x0, n, aPrime, cFace, q)))
		inverseEquation := a.Have(
			"r multiplies the inverse boundary class by the boundary of u to give the unit",
			"simplicial_homotopy_mul(«F», "+
				"    x₀, "+
				"    n, "+
				"    equivalence_class(simplicial_homotopic(«F», x₀, n), X.d(n + 1, n + 1, r)), "+
				"    «A») = "+
				"simplicial_homotopy_unit(«F», x₀, n)",
			CalcEq(
				Leg(
					a.TermAs[Set[A]]("equivalence_class(simplicial_homotopic(«F», x₀, n), base_simplex(x₀, n))"),
					"the n-th face of r is the base simplex",
					By(
						fiberVertex,
						positive,
						aPrimeSphere,
						aSphere,
						inverseFilled,
						homotopy_group.MulClass.Read(fiberKan).At(x0, n, aPrime, aFace, r))),
				FinalLeg(
					"the base class is the unit",
					Simp(Fwd(homotopy_group.SimplicialHomotopyUnitDef), Fwd(SimplicialFiberDef)),
					Refl()),
			))
		classes := a.Have(
			"all four sphere classes belong to the homotopy group of the fibre",
			"equivalence_class(simplicial_homotopic(«F», x₀, n), X.d(n + 1, n + 1, r)) ∈ "+
				"simplicial_homotopy_group(«F», x₀, n) ∧ "+
				"«A» ∈ simplicial_homotopy_group(«F», x₀, n) ∧ "+
				"«B» ∈ simplicial_homotopy_group(«F», x₀, n) ∧ "+
				"«C» ∈ simplicial_homotopy_group(«F», x₀, n)",
			By(
				fiberVertex,
				aPrimeSphere,
				aSphere,
				bSphere,
				cSphere,
				homotopy_group.ClassInHomotopyGroup.Read(fiberSimplicial).At(x0, n, aPrime),
				homotopy_group.ClassInHomotopyGroup.Read(fiberSimplicial).At(x0, n, aFace),
				homotopy_group.ClassInHomotopyGroup.Read(fiberSimplicial).At(x0, n, bFace),
				homotopy_group.ClassInHomotopyGroup.Read(fiberSimplicial).At(x0, n, cFace)))
		fiberGroup := a.Have(
			"in positive dimension the homotopy classes form a group",
			"group_on(mk_group(simplicial_homotopy_mul(«F», x₀, n), "+
				"        simplicial_homotopy_unit(«F», x₀, n), "+
				"        simplicial_homotopy_inv(«F», x₀, n), "+
				"        simplicial_homotopy_group(«F», x₀, n)))",
			By(fiberVertex, positive, homotopy_group.GroupOn.Read(fiberKan).At(x0, n)))
		product := a.TermAs[Set[A]]("simplicial_homotopy_mul(«F», x₀, n, «A», «B»)")
		productIn := a.Have(
			"the product of the endpoint boundary classes belongs to the group",
			"simplicial_homotopy_mul(«F», x₀, n, «A», «B») ∈ simplicial_homotopy_group(«F», x₀, n)",
			By(classes, fiberVertex, positive, homotopy_group.MulIn.Read(fiberKan).At(x0, n, aClass, bClass)))
		sameProduct := a.Have(
			"left multiplication by the inverse boundary class "+
				"also sends the endpoint product to the boundary of w",
			"simplicial_homotopy_mul(«F», "+
				"    x₀, "+
				"    n, "+
				"    equivalence_class(simplicial_homotopic(«F», x₀, n), X.d(n + 1, n + 1, r)), "+
				"    simplicial_homotopy_mul(«F», x₀, n, «A», «B»)) = "+
				"«B»",
			By(
				classes,
				fiberVertex,
				positive,
				inverseEquation,
				homotopy_group.Assoc.Read(fiberKan).At(x0, n, aPrimeClass, aClass, bClass),
				homotopy_group.LeftIdentity.Read(fiberKan).At(x0, n, bClass)))
		a.Show(
			"left cancellation gives the product formula for the middle boundary class",
			By(
				classes,
				productIn,
				sameProduct,
				productEquation,
				group.LeftCancelOn.Read(fiberGroup).AsFact().At(aPrimeClass, cClass, product)))
	}),
})}

// ConnectingMapHom — the connecting map is a homomorphism in positive
// dimension: represent two classes by spheres, lift their product filler,
// and read its boundary product through the connecting map.
var ConnectingMapHom = connectingMapHomThm{family.Add(registry.ProofEntry{
	Name: "ConnectingMapHom",
	Key:  "prop_c7775def63565bbe",
	Build: KanFibration.Law(Statement{
		Binders: "∀x₀:A. ∀n:num.",
		Hypotheses: []string{
			"kan_complex(Y)",
			"x₀ ∈ X.simplices(0)",
			"0 < n",
		},
		Conclusion: "group_homomorphism(mk_group(simplicial_homotopy_mul(Y, p(0, x₀), n + 1), " +
			"        simplicial_homotopy_unit(Y, p(0, x₀), n + 1), " +
			"        simplicial_homotopy_inv(Y, p(0, x₀), n + 1), " +
			"        simplicial_homotopy_group(Y, p(0, x₀), n + 1)), " +
			"    mk_group(simplicial_homotopy_mul(simplicial_fiber(p, p(0, x₀)), x₀, n), " +
			"        simplicial_homotopy_unit(simplicial_fiber(p, p(0, x₀)), x₀, n), " +
			"        simplicial_homotopy_inv(simplicial_fiber(p, p(0, x₀)), x₀, n), " +
			"        simplicial_homotopy_group(simplicial_fiber(p, p(0, x₀)), x₀, n)), " +
			"    simplicial_connecting_map(p, x₀, n))",
	},
		func(a *Argument, fibration Fact, x0 *Expr[A], n *Expr[Nat], targetKan, vertex, positive Fact) {
			simplicialMap := FibrationMap.Read(fibration)
			target := simplicial_set.MapTarget.Read(simplicialMap)
			X, Y, p :=
				a.TermAs[simplicial_set.SimplicialOps[A]]("X"),
				a.TermAs[simplicial_set.SimplicialOps[B]]("Y"),
				a.TermAs[Fun2[Nat, A, B]]("p")
			y0, next := a.TermAs[B]("p(0, x₀)"), a.TermAs[Nat]("n + 1")
			baseVertex := a.Have(
				"the image of x₀ is a vertex of Y",
				"p(0, x₀) ∈ Y.simplices(0)",
				By(vertex, simplicial_set.MapIn.Read(simplicialMap).At(a.TermAs[Nat]("0"), x0)))
			fiberKan := a.Have(
				"the fibre over that vertex is Kan",
				"kan_complex(simplicial_fiber(p, p(0, x₀)))",
				By(baseVertex, FiberKan.Read(fibration).At(y0)))
			fiberVertex := a.Have(
				"x₀ is a vertex of the fibre",
				"x₀ ∈ simplicial_fiber_simplices(p, p(0, x₀), 0)",
				By(vertex, FiberBasePoint.At(X, Y, p, x0)))
			dims := a.Have(
				"the source dimension is positive and its adjacent dimensions simplify",
				"n + 1 + 1 = n + 2 ∧ n + 1 - 1 = n ∧ 0 < n + 1",
				ByArith())

			preservesProduct := a.Have(
				"the connecting map preserves products of homotopy classes",
				Statement{
					Binders: "∀L M:set(B).",
					Hypotheses: []string{
						"L ∈ simplicial_homotopy_group(Y, p(0, x₀), n + 1)",
						"M ∈ simplicial_homotopy_group(Y, p(0, x₀), n + 1)",
					},
					Conclusion: "simplicial_connecting_map(p, " +
						"    x₀, " +
						"    n, " +
						"    simplicial_homotopy_mul(Y, p(0, x₀), n + 1, L, M)) = " +
						"simplicial_homotopy_mul(simplicial_fiber(p, p(0, x₀)), " +
						"    x₀, " +
						"    n, " +
						"    simplicial_connecting_map(p, x₀, n, L), " +
						"    simplicial_connecting_map(p, x₀, n, M))",
				},
				Derive(func(b *Argument) {
					L, M := b.FixAs[Set[B]](), b.FixAs[Set[B]]()
					classesIn := b.Assume()
					z, representedL := b.ObtainAs[B](
						"choose a sphere representing L",
						"∃z:B. "+
							"    z ∈ simplicial_sphere(Y, p(0, x₀), n + 1) ∧ "+
							"    L = equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), z)",
						By(baseVertex, classesIn, homotopy_group.InHomotopyGroup.Read(target).At(y0, next, L)))
					zParts := b.Conjuncts(
						representedL,
						"z is a sphere",
						"L is its class")
					zSphere, classL := zParts[0], zParts[1]
					zprime, representedM := b.ObtainAs[B](
						"choose a sphere representing M",
						"∃zprime:B. "+
							"    zprime ∈ simplicial_sphere(Y, p(0, x₀), n + 1) ∧ "+
							"    M = equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), zprime)",
						By(baseVertex, classesIn, homotopy_group.InHomotopyGroup.Read(target).At(y0, next, M)))
					zprimeParts := b.Conjuncts(
						representedM,
						"zprime is a sphere",
						"M is its class")
					zprimeSphere, classM := zprimeParts[0], zprimeParts[1]
					W, filled := b.ObtainAs[B](
						"choose a product filler for the two spheres",
						"∃W:B. "+
							"    W ∈ Y.simplices(n + 2) ∧ "+
							"    (∀i:num. i + 1 < n + 1 ⇒ Y.d(n + 2, i, W) = base_simplex(p(0, x₀), n + 1)) ∧ "+
							"    Y.d(n + 2, n + 2, W) = z ∧ "+
							"    Y.d(n + 2, n, W) = zprime",
						ByArith(
							baseVertex,
							dims,
							zSphere,
							zprimeSphere,
							homotopy_group.ProductFillerExists.Read(targetKan).At(y0, next, z, zprime)))
					WParts := b.Conjuncts(
						filled,
						"W is an (n+2)-simplex of Y",
						"its lower faces are base simplices",
						"its last face is z",
						"its n-th face is zprime")
					WIn, WLower, WLast, WAtN := WParts[0], WParts[1], WParts[2], WParts[3]
					middle := b.TermAs[B]("Y.d(n + 2, n + 1, W)")
					middleSphere := b.Have(
						"the middle face of W is a sphere",
						"Y.d(n + 2, n + 1, W) ∈ simplicial_sphere(Y, p(0, x₀), n + 1)",
						ByArith(
							baseVertex,
							dims,
							zSphere,
							zprimeSphere,
							filled,
							homotopy_group.ProductSphere.Read(target).At(y0, next, z, zprime, W)))

					u, uLifted := b.ObtainAs[A](
						"choose a standard connecting lift of z",
						"∃u:A. "+
							"    u ∈ X.simplices(n + 1) ∧ "+
							"    (∀i:num. i ≤ n + 1 ∧ i ≠ n ⇒ X.d(n + 1, i, u) = base_simplex(x₀, n)) ∧ "+
							"    p(n + 1, u) = z",
						By(vertex, zSphere, ConnectingLiftExists.Read(fibration).At(x0, n, z)))
					v, vLifted := b.ObtainAs[A](
						"choose a standard connecting lift of the middle sphere",
						"∃v:A. "+
							"    v ∈ X.simplices(n + 1) ∧ "+
							"    (∀i:num. i ≤ n + 1 ∧ i ≠ n ⇒ X.d(n + 1, i, v) = base_simplex(x₀, n)) ∧ "+
							"    p(n + 1, v) = Y.d(n + 2, n + 1, W)",
						By(vertex, middleSphere, ConnectingLiftExists.Read(fibration).At(x0, n, middle)))
					w, wLifted := b.ObtainAs[A](
						"choose a standard connecting lift of zprime",
						"∃w:A. "+
							"    w ∈ X.simplices(n + 1) ∧ "+
							"    (∀i:num. i ≤ n + 1 ∧ i ≠ n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ "+
							"    p(n + 1, w) = zprime",
						By(vertex, zprimeSphere, ConnectingLiftExists.Read(fibration).At(x0, n, zprime)))
					WBelow := b.Have(
						"the faces below n satisfy the connecting product convention",
						"∀i:num. i < n ⇒ Y.d(n + 2, i, W) = base_simplex(p(0, x₀), n + 1)",
						b.ForEach(func(i *Expr[Nat]) Action { return ByArith(WLower.At(i)) }))
					liftFaces := b.Have(
						"all three lifts have the standard base faces away from n",
						Statement{
							Binders: "∀i:num.", Hypotheses: []string{"i ≤ n + 1", "i ≠ n"},
							Conclusion: "X.d(n + 1, i, u) = base_simplex(x₀, n) ∧ " +
								"X.d(n + 1, i, v) = base_simplex(x₀, n) ∧ " +
								"X.d(n + 1, i, w) = base_simplex(x₀, n)",
						},
						By(uLifted, vLifted, wLifted))
					b.Show(
						"read the connecting map on the three spheres and use the boundary product formula",
						CalcEq(
							Leg(
								b.TermAs[Set[A]](
									"simplicial_connecting_map(p, "+
										"    x₀, "+
										"    n, "+
										"    equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), Y.d(n + 2, n + 1, W)))"),
								"the middle face of W represents the product of L and M",
								ByArith(
									baseVertex,
									dims,
									zSphere,
									zprimeSphere,
									filled,
									classL,
									classM,
									homotopy_group.MulClass.Read(targetKan).At(y0, next, z, zprime, W))),
							Leg(
								b.TermAs[Set[A]](
									"equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), X.d(n + 1, n, v))"),
								"the connecting map takes the middle sphere to the boundary class of v",
								By(
									vertex,
									targetKan,
									middleSphere,
									vLifted,
									ConnectingMapClass.Read(fibration).At(x0, n, middle, v))),
							Leg(
								b.TermAs[Set[A]](
									"simplicial_homotopy_mul(simplicial_fiber(p, p(0, x₀)), "+
										"    x₀, "+
										"    n, "+
										"    equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), "+
										"        X.d(n + 1, n, u)), "+
										"    equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), "+
										"        X.d(n + 1, n, w)))"),
								"the boundary class of v is the product of the endpoint boundary classes",
								By(
									vertex,
									positive,
									zSphere,
									zprimeSphere,
									WIn,
									WBelow,
									WLast,
									WAtN,
									uLifted,
									vLifted,
									wLifted,
									liftFaces,
									ConnectingProductClass.Read(fibration).At(x0, n, z, zprime, W, u, v, w))),
							FinalLeg(
								"the endpoint boundary classes are the connecting images of L and M",
								By(
									vertex,
									targetKan,
									zSphere,
									zprimeSphere,
									uLifted,
									wLifted,
									classL,
									classM,
									ConnectingMapClass.Read(fibration).At(x0, n, z, u),
									ConnectingMapClass.Read(fibration).At(x0, n, zprime, w))),
						))
				}))
			mapsCarrier := a.Have(
				"the connecting map carries the source homotopy group into the fibre homotopy group",
				Statement{
					Binders: "∀L:set(B).", Hypotheses: []string{"L ∈ simplicial_homotopy_group(Y, p(0, x₀), n + 1)"},
					Conclusion: "simplicial_connecting_map(p, x₀, n, L) ∈ " +
						"simplicial_homotopy_group(simplicial_fiber(p, p(0, x₀)), x₀, n)",
				},
				Derive(func(b *Argument) {
					L := b.FixAs[Set[B]]()
					inGroup := b.Assume()
					b.Show(
						"the connecting image lies in the fibre homotopy group",
						By(targetKan, vertex, inGroup, ConnectingMapIn.Read(fibration).At(x0, n, L)))
				}))
			sourceGroup := a.TermAs[group.GroupOps[Set[B]]](
				"mk_group(simplicial_homotopy_mul(Y, p(0, x₀), n + 1), " +
					"    simplicial_homotopy_unit(Y, p(0, x₀), n + 1), " +
					"    simplicial_homotopy_inv(Y, p(0, x₀), n + 1), " +
					"    simplicial_homotopy_group(Y, p(0, x₀), n + 1))")
			targetGroup := a.TermAs[group.GroupOps[Set[A]]](
				"mk_group(simplicial_homotopy_mul(simplicial_fiber(p, p(0, x₀)), x₀, n), " +
					"    simplicial_homotopy_unit(simplicial_fiber(p, p(0, x₀)), x₀, n), " +
					"    simplicial_homotopy_inv(simplicial_fiber(p, p(0, x₀)), x₀, n), " +
					"    simplicial_homotopy_group(simplicial_fiber(p, p(0, x₀)), x₀, n))")
			connecting := a.TermAs[Fun[Set[B], Set[A]]]("simplicial_connecting_map(p, x₀, n)")
			a.Show(
				"the two groups, carrier map and product preservation give a homomorphism",
				ByArith(
					baseVertex,
					fiberVertex,
					positive,
					dims,
					mapsCarrier,
					preservesProduct,
					group_homomorphism.GroupHomomorphism.At(sourceGroup, targetGroup, connecting),
					homotopy_group.GroupOn.Read(targetKan).At(y0, next),
					homotopy_group.GroupOn.Read(fiberKan).At(x0, n)))
		}),
})}

// ---------------------------------------------------------------------------
// Exactness
// ---------------------------------------------------------------------------

// FiberInclusionClass — the inclusion of the fibre carries the class of
// a sphere of the fibre to its class in X: the fibre is a sub-simplicial
// set of X, so its inclusion is a simplicial map, x₀ is a vertex of the
// fibre (FiberBasePoint), and its target X is a Kan complex, so
// HomotopyMapClass reads it on classes.
var FiberInclusionClass = fiberInclusionClassThm{family.Add(registry.ProofEntry{
	Name: "FiberInclusionClass",
	Key:  "prop_284cdf8222d84a9b",
	Reading: "kan_complex(X) is the one Kan hypothesis: HomotopyMapClass asks only the target of " +
		"a map to be Kan, and X is the target of the inclusion. Neither Y nor the fibre need be Kan.",
	Build: simplicial_set.SimplicialMap.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀a:A.",
		Hypotheses: []string{
			"kan_complex(X)",
			"x₀ ∈ X.simplices(0)",
			"a ∈ simplicial_sphere(simplicial_fiber(X, Y, F, F(0, x₀)), x₀, n)",
		},
		Conclusion: "simplicial_homotopy_map(simplicial_fiber(X, Y, F, F(0, x₀)), " +
			"    X, " +
			"    λm:num. λx:A. x, " +
			"    x₀, " +
			"    n, " +
			"    equivalence_class(simplicial_homotopic(simplicial_fiber(X, Y, F, F(0, x₀)), x₀, n), a)) = " +
			"equivalence_class(simplicial_homotopic(X, x₀, n), a)",
	},
		func(arg *Argument, simplicialMap Fact, x0 *Expr[A], n *Expr[Nat], a *Expr[A], hypotheses Fact) {
			source := simplicial_set.MapSource.Read(simplicialMap)
			given := arg.Conjuncts(
				hypotheses,
				"X is a Kan complex",
				"x₀ is a vertex of X",
				"and a is a sphere of the fibre over F(0, x₀)")
			kan, vertex, aSphereFiber := given[0], given[1], given[2]
			y0 := arg.TermAs[B]("F(0, x₀)")
			fiber := arg.TermAs[Fun[Nat, Set[A]]]("simplicial_fiber_simplices(F, F(0, x₀))")

			baseVertex := arg.Have(
				"F(0, x₀) is a vertex of Y",
				"F(0, x₀) ∈ Y.simplices(0)",
				By(simplicial_set.MapIn.Read(simplicialMap).At(arg.TermAs[Nat]("0"), x0), vertex))
			inclusion := arg.Have(
				"the fibre over it is a sub-simplicial set of X, so its inclusion in X is a simplicial map",
				"simplicial_map(simplicial_fiber(F, F(0, x₀)), X, λm:num. λx:A. x)",
				By(
					simplicial_set.MapInclusion.Read(source).At(fiber),
					FiberSub.Read(simplicialMap).At(y0),
					baseVertex,
					SimplicialFiberDef))
			fiberVertex := arg.Have(
				"x₀ is a vertex of the fibre",
				"x₀ ∈ simplicial_fiber_simplices(F, F(0, x₀), 0)",
				By(Where(FiberBasePoint, "x_0", x0), vertex))
			arg.Show(
				"the inclusion, a simplicial map into the Kan complex X, sends "+
					"the class of the sphere a of the fibre to the class of its image a",
				By(homotopy_group.HomotopyMapClass.Read(inclusion).At(x0, n, a), kan, fiberVertex, aSphereFiber))
		}),
})}

// ExactAtTotal — at πₙ(X): a class maps to the unit of Y exactly when
// it comes from the fibre. The inclusion carries the class of a sphere a
// of the fibre to its class in X (FiberInclusionClass), and a, a sphere
// of X over the base simplex, is carried by p to the base simplex, whose
// class is the unit. Conversely, with x a sphere of X whose image is
// homotopic in Y to the base simplex by some h, the horn of dimension
// n + 1 with x at n and the base simplex below lifts over h. The lift is
// a homotopy in X from x to its last face c, which, the other end of a
// homotopy from a sphere, is a sphere, and lies over the last face of h,
// so it is a sphere of the fibre.
var ExactAtTotal = exactAtTotalThm{family.Add(registry.ProofEntry{
	Name: "ExactAtTotal",
	Reading: "kan_complex(Y) is read in Y itself, by HomotopyMapClass, which reads p on " +
		"classes, and by ClassEqIff for the image of a sphere of X; and through TotalKan, " +
		"which makes X a Kan complex: there a sphere of X and a sphere of the fibre homotopic " +
		"to it share a class, and the inclusion into X is read on classes (FiberInclusionClass).",
	Key: "prop_a6be4c57cb46b182",
	Build: KanFibration.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀C:set(A).",
		Hypotheses: []string{
			"kan_complex(Y)",
			"x₀ ∈ X.simplices(0)",
			"C ∈ simplicial_homotopy_group(X, x₀, n)",
		},
		Conclusion: "simplicial_homotopy_map(X, Y, p, x₀, n, C) = " +
			"simplicial_homotopy_unit(Y, p(0, x₀), n) ⇔ " +
			"∃K:set(A). " +
			"    K ∈ simplicial_homotopy_group(simplicial_fiber(p, p(0, x₀)), x₀, n) ∧ " +
			"    simplicial_homotopy_map(simplicial_fiber(p, p(0, x₀)), X, λm:num. λx:A. x, x₀, n, K) = C",
	},
		func(
			arg *Argument,
			fibration Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			hypotheses Fact,
			C *Expr[Set[A]],
			inGroup Fact,
		) {
			simplicialMap := FibrationMap.Read(fibration)
			source := simplicial_set.MapSource.Read(simplicialMap)
			target := simplicial_set.MapTarget.Read(simplicialMap)
			given := arg.Conjuncts(
				hypotheses,
				"Y is a Kan complex",
				"and x₀ is a vertex of X")
			base, vertex := given[0], given[1]
			X := arg.TermAs[simplicial_set.SimplicialOps[A]]("X")
			y0, next := arg.TermAs[B]("p(0, x₀)"), arg.TermAs[Nat]("n + 1")

			total := arg.Have(
				"X is a Kan complex, the source of a fibration over one",
				"kan_complex(X)",
				By(TotalKan.Read(fibration), base))
			baseVertex := arg.Have(
				"p(0, x₀) is a vertex of Y",
				"p(0, x₀) ∈ Y.simplices(0)",
				By(simplicial_set.MapIn.Read(simplicialMap).At(arg.TermAs[Nat]("0"), x0), vertex))
			fiberSimplicial := arg.Have(
				"the fibre over p(0, x₀) is a simplicial set",
				"simplicial_set(simplicial_fiber(p, p(0, x₀)))",
				By(FiberSimplicialSet.Read(simplicialMap).At(y0), baseVertex))
			fiberVertex := arg.Have(
				"x₀ is a vertex of the fibre",
				"x₀ ∈ simplicial_fiber_simplices(p, p(0, x₀), 0)",
				By(Where(FiberBasePoint, "x_0", x0), vertex))

			arg.Iff()
			arg.Backward(
				"a class of the fibre is the class of a sphere a there, a sphere of X over the base simplex",
				func(b *Argument, comes Fact) {
					K, from := b.UnpackAs[Set[A]](comes, "K")
					parts := b.Conjuncts(
						from,
						"K is a class of πₙ of the fibre",
						"which the inclusion carries to C")
					inFiber, image := parts[0], parts[1]
					a, represented := b.ObtainAs[A](
						"K is the class of a sphere a of the fibre",
						"∃a:A. "+
							"    a ∈ simplicial_sphere(simplicial_fiber(p, p(0, x₀)), x₀, n) ∧ "+
							"    K = equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), a)",
						By(inFiber, homotopy_group.InHomotopyGroup.Read(fiberSimplicial).At(x0, n, K), fiberVertex))
					aParts := b.Conjuncts(
						represented,
						"a is a sphere of the fibre",
						"whose class there is K")
					aSphereFiber, kClass := aParts[0], aParts[1]
					aFacts := b.Conjuncts(
						b.Have(
							"so a is a sphere of X lying over the base simplex",
							"a ∈ simplicial_sphere(X, x₀, n) ∧ p(n, a) = base_simplex(p(0, x₀), n)",
							By(Where(FiberSphere, "x_0", x0).Where("n", n).Where("x", a), aSphereFiber)),
						"a is a sphere of X",
						"and p carries it to the base simplex")
					aSphereX, aOver := aFacts[0], aFacts[1]
					cClass := b.Have(
						"C is the class of a in X",
						"C = equivalence_class(simplicial_homotopic(X, x₀, n), a)",
						CalcEq(
							Leg(
								b.TermAs[Set[A]](
									"simplicial_homotopy_map(simplicial_fiber(p, p(0, x₀)), X, λm:num. λx:A. x, x₀, n, K)"),
								"C is the image of K",
								By(Normalized, image)),
							Leg(
								b.TermAs[Set[A]](
									"simplicial_homotopy_map(simplicial_fiber(p, p(0, x₀)), "+
										"    X, "+
										"    λm:num. λx:A. x, "+
										"    x₀, "+
										"    n, "+
										"    equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), a))"),
								"K is the class of a in the fibre",
								By(kClass)),
							FinalLeg(
								"which the inclusion sends to the class of a in X",
								By(FiberInclusionClass.Read(simplicialMap).At(x0, n, a), total, vertex, aSphereFiber)),
						))
					b.Show(
						"so p carries C to the class of p(n, a), the base simplex, whose class is the unit",
						CalcEq(
							Leg(
								b.TermAs[Set[B]](
									"simplicial_homotopy_map(X, Y, p, x₀, n, equivalence_class(simplicial_homotopic(X, x₀, n), a))"),
								"C is the class of a",
								By(Normalized, cClass)),
							Leg(
								b.TermAs[Set[B]]("equivalence_class(simplicial_homotopic(Y, p(0, x₀), n), p(n, a))"),
								"the induced map sends the class of a sphere to the class of its image",
								By(homotopy_group.HomotopyMapClass.Read(simplicialMap).At(x0, n, a), base, vertex, aSphereX)),
							Leg(
								b.TermAs[Set[B]](
									"equivalence_class(simplicial_homotopic(Y, p(0, x₀), n), base_simplex(p(0, x₀), n))"),
								"a lies over the base simplex",
								By(aOver)),
							FinalLeg(
								"the class of the base simplex is the unit of Y",
								By(homotopy_group.SimplicialHomotopyUnitDef)),
						))
				})
			arg.Forward(
				"the horn of x and the base simplex lifts over a homotopy in Y from "+
					"p(n, x) to the base simplex, to one in X from x to a sphere of the fibre",
				func(b *Argument, unit Fact) {
					x, represented := b.ObtainAs[A](
						"C is the class of a sphere x of X",
						"∃x:A. x ∈ simplicial_sphere(X, x₀, n) ∧ C = equivalence_class(simplicial_homotopic(X, x₀, n), x)",
						By(inGroup, homotopy_group.InHomotopyGroup.Read(source).At(x0, n, C), vertex))
					xParts := b.Conjuncts(
						represented,
						"x is a sphere of X",
						"whose class is C")
					xSphere, cClass := xParts[0], xParts[1]

					px := b.TermAs[B]("p(n, x)")
					baseY := b.TermAs[B]("base_simplex(p(0, x₀), n)")
					imageSphere := b.Have(
						"its image p(n, x) is a sphere of Y",
						"p(n, x) ∈ simplicial_sphere(Y, p(0, x₀), n)",
						By(homotopy_group.MapSphere.Read(simplicialMap).At(x0, n, x), vertex, xSphere))
					baseSphereY := b.Have(
						"and so is the base simplex of Y",
						"base_simplex(p(0, x₀), n) ∈ simplicial_sphere(Y, p(0, x₀), n)",
						By(homotopy_group.BaseSphere.Read(target).At(y0, n), baseVertex))
					sameClassY := b.Have(
						"the class of p(n, x) is the unit, the class of the base simplex",
						"equivalence_class(simplicial_homotopic(Y, p(0, x₀), n), p(n, x)) = "+
							"equivalence_class(simplicial_homotopic(Y, p(0, x₀), n), base_simplex(p(0, x₀), n))",
						CalcEq(
							Leg(
								b.TermAs[Set[B]](
									"simplicial_homotopy_map(X, Y, p, x₀, n, equivalence_class(simplicial_homotopic(X, x₀, n), x))"),
								"the induced map sends the class of x to the class of its image",
								By(homotopy_group.HomotopyMapClass.Read(simplicialMap).At(x0, n, x), base, vertex, xSphere)),
							Leg(
								b.TermAs[Set[B]]("simplicial_homotopy_map(X, Y, p, x₀, n, C)"),
								"the class of x is C",
								By(Normalized, cClass)),
							Leg(
								b.TermAs[Set[B]]("simplicial_homotopy_unit(Y, p(0, x₀), n)"),
								"which p carries to the unit",
								By(unit)),
							FinalLeg(
								"the class of the base simplex",
								By(homotopy_group.SimplicialHomotopyUnitDef)),
						))
					homotopicY := b.Have(
						"so p(n, x) is homotopic in Y to the base simplex",
						"simplicial_homotopic(Y, p(0, x₀), n, p(n, x), base_simplex(p(0, x₀), n))",
						By(
							homotopy_group.ClassEqIff.Read(base).At(y0, n, px, baseY),
							baseVertex,
							imageSphere,
							baseSphereY,
							sameClassY))
					h, homotopy := b.UnpackAs[B](b.Unfolded(homotopicY, homotopy_group.SimplicialHomotopicDef), "h")
					hParts := b.Conjuncts(
						homotopy,
						"h is an (n+1)-simplex of Y",
						"whose faces below n are the base simplex",
						"its face n is p(n, x)",
						"and its face n + 1 the base simplex")
					hIn, hBelow, hStart, hEnd := hParts[0], hParts[1], hParts[2], hParts[3]

					// The horn: x at n, the base simplex at every other index; its
					// value at the missing face n + 1 is never read.
					baseSphereX := b.Have(
						"the base simplex of X is a sphere",
						"base_simplex(x₀, n) ∈ simplicial_sphere(X, x₀, n)",
						By(homotopy_group.BaseSphere.Read(source).At(x0, n), vertex))
					f, fDef := b.LetAs[Fun[Nat, A]]("f", "λi:num. COND(i = n, x, base_simplex(x₀, n))")
					values := b.Conjuncts(
						b.Have(
							"f is x at n and the base simplex below n",
							"f(n) = x ∧ (∀i:num. i < n ⇒ f(i) = base_simplex(x₀, n))",
							fDef.Rw(),
							ByArith()),
						"f is x at n",
						"and the base simplex below n")
					atN, baseValues := values[0], values[1]
					memberSpheres := b.Have(
						"every member of f is a sphere of X: x or the base simplex",
						"∀i:num. f(i) ∈ simplicial_sphere(X, x₀, n)",
						fDef.Rw(),
						b.ForEach(func(_ *Expr[Nat]) Action {
							return Chain(CondRewrite(), By(xSphere, baseSphereX))
						}))
					bound := b.Have(
						"the missing face n + 1 is a face of an (n+1)-simplex",
						"n + 1 ≤ n + 1",
						ByArith())
					horn := b.Have(
						"so f, a family of spheres missing the face n + 1, is "+
							"a horn: a face family of X on the faces of the horn",
						"face_family(X, n, horn_faces(n, n + 1), f)",
						By(At(homotopy_group.SphereHornCompatible, X, x0, n, next, f), bound, memberSpheres))
					images := b.Have(
						"the faces of h at the faces of the horn are the images of the "+
							"members: p(n, x) at n, below n the image of the base simplex",
						"faces_filler(n, horn_faces(n, n + 1), λi:num. p(n, f(i)), h)",
						Simp(Fwd(simplicial_set.FacesFillerDef)),
						Derive(func(e *Argument) {
							i := e.FixAs[Nat]()
							face := e.Assume()
							within := e.Have(
								"a face of the horn is at most n + 1, and not n + 1",
								"i ≤ n + 1 ∧ ¬(i = n + 1)",
								By(face, kan_complex.HornFacesMember.At(n, next, i)))
							e.Show(
								"the face i of h is p(n, x) at n and the image of "+
									"the base simplex below n, the image of f(i) at each",
								fDef.Rw(),
								CondRewrite(),
								ByArith(
									hBelow.At(i),
									hStart,
									within,
									simplicial_set.MapBaseSimplex.Read(simplicialMap).At(x0, n),
									vertex))
						}))

					w, lifted := b.ObtainAs[A](
						"so the horn lifts along the fibration to an (n+1)-simplex w of X over h",
						"∃w:A. w ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, n + 1), f, w) ∧ p(n + 1, w) = h",
						By(FibrationLift.Read(fibration).At(n, next, f, h), bound, horn, hIn, images))
					wParts := b.Conjuncts(
						lifted,
						"w is an (n+1)-simplex of X",
						"whose faces at the faces of the horn are the members of f",
						"over h")
					wIn, wOver := wParts[0], wParts[2]
					faceOfW := b.Unfolded(wParts[1], simplicial_set.FacesFillerDef)
					wBelow := b.Have(
						"so w has the base simplex below n",
						"∀i:num. i < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)",
						b.ForEach(func(i *Expr[Nat]) Action {
							return ByArith(faceOfW.At(i), kan_complex.HornFacesMember.At(n, next, i), baseValues.At(i))
						}))
					wAtN := b.Have(
						"and x at n",
						"X.d(n + 1, n, w) = x",
						ByArith(faceOfW.At(n), kan_complex.HornFacesMember.At(n, next, n), atN))

					c := b.TermAs[A]("X.d(n + 1, n + 1, w)")
					homotopic := b.Have(
						"w is a homotopy in X from x to its last face c",
						"simplicial_homotopic(X, x₀, n, x, X.d(n + 1, n + 1, w))",
						Simp(Fwd(homotopy_group.SimplicialHomotopicDef)),
						Derive(func(e *Argument) {
							e.Take(w)
							e.Show(
								"w is an (n+1)-simplex of X with the base simplex below n, x at n and c at n + 1",
								By(wIn, wBelow, wAtN))
						}))
					cSphereX := b.Have(
						"so c, the other end of a homotopy from the sphere x, is a sphere of X",
						"X.d(n + 1, n + 1, w) ∈ simplicial_sphere(X, x₀, n)",
						By(homotopy_group.HomotopicSphere.Read(source).At(x0, n, x, c), vertex, homotopic, xSphere))
					cOver := b.Have(
						"p carries c to the last face of h, the base simplex",
						"p(n, X.d(n + 1, n + 1, w)) = base_simplex(p(0, x₀), n)",
						CalcEq(
							Leg(
								b.TermAs[B]("Y.d(n + 1, n + 1, p(n + 1, w))"),
								"p commutes with the last face",
								By(simplicial_set.MapFace.Read(simplicialMap).At(n, next, w), wIn, bound)),
							Leg(
								b.TermAs[B]("Y.d(n + 1, n + 1, h)"),
								"w lies over h",
								By(Normalized, wOver)),
							FinalLeg(
								"whose last face is the base simplex",
								By(hEnd)),
						))
					cSphereFiber := b.Have(
						"so, lying over the base simplex, c is a sphere of the fibre",
						"X.d(n + 1, n + 1, w) ∈ simplicial_sphere(simplicial_fiber(p, p(0, x₀)), x₀, n)",
						By(Where(FiberSphere, "x_0", x0).Where("n", n).Where("x", c), cSphereX, cOver))
					sameClassX := b.Have(
						"so x and c have one class in X",
						"equivalence_class(simplicial_homotopic(X, x₀, n), x) = "+
							"equivalence_class(simplicial_homotopic(X, x₀, n), X.d(n + 1, n + 1, w))",
						By(homotopy_group.ClassEqIff.Read(total).At(x0, n, x, c), vertex, xSphere, cSphereX, homotopic))

					classC := b.TermAs[Set[A]](
						"equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), " +
							"    X.d(n + 1, n + 1, w))")
					inPi := b.Have(
						"so its class is a class of πₙ(F, x₀)",
						"equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), "+
							"    X.d(n + 1, n + 1, w)) ∈ "+
							"simplicial_homotopy_group(simplicial_fiber(p, p(0, x₀)), x₀, n)",
						By(
							cSphereFiber,
							homotopy_group.ClassInHomotopyGroup.Read(fiberSimplicial).At(x0, n, c),
							fiberVertex))
					mapped := b.Have(
						"which the inclusion carries to C",
						"simplicial_homotopy_map(simplicial_fiber(p, p(0, x₀)), "+
							"    X, "+
							"    λm:num. λx:A. x, "+
							"    x₀, "+
							"    n, "+
							"    equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), "+
							"        X.d(n + 1, n + 1, w))) = "+
							"C",
						CalcEq(
							Leg(
								b.TermAs[Set[A]]("equivalence_class(simplicial_homotopic(X, x₀, n), X.d(n + 1, n + 1, w))"),
								"the inclusion sends the class of a sphere of the fibre to its class in X",
								By(FiberInclusionClass.Read(simplicialMap).At(x0, n, c), total, vertex, cSphereFiber)),
							Leg(
								b.TermAs[Set[A]]("equivalence_class(simplicial_homotopic(X, x₀, n), x)"),
								"c and x have one class in X",
								By(sameClassX)),
							FinalLeg(
								"the class of x is C",
								By(Normalized, cClass)),
						))
					b.Take(classC)
					b.Show(
						"so the class of c in the fibre is a class of πₙ(F, x₀) that the inclusion carries to C",
						By(inPi, mapped))
				})
		}),
})}

// ExactAtBase — at πₙ₊₁(Y): a class is sent to the unit of the fibre
// by the connecting map exactly when it comes from X. A sphere x of X is
// itself a lift of its image with the base simplex at every face, so the
// connecting map sends the class of p(n + 1, x) to the class of the base
// simplex. Conversely, with z a sphere of Y and w a lift of it, the n-th
// face of w has the unit for its class in the fibre, so it is homotopic
// there to the base simplex by some h; the horn of dimension n + 2 with h
// at n, w at n + 1 and the base simplex below lifts over the degeneracy
// s'(n + 1, n + 1, z), and the last face of the lift is a sphere of X over
// z, whose class p carries to the class of z.
var ExactAtBase = exactAtBaseThm{family.Add(registry.ProofEntry{
	Name: "ExactAtBase",
	Reading: "kan_complex(Y) is read by HomotopyMapClass, which reads p on classes. No " +
		"two classes of X are compared, so X is never shown Kan; the classes compared are " +
		"the fibre's, a Kan complex over any base (FiberKan). The homotopy must lie in the " +
		"fibre, over the base simplex, to fill the face n of a horn over s'(n + 1, n + 1, z).",
	Key: "prop_713a0687d3740987",
	Build: KanFibration.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀L:set(B).",
		Hypotheses: []string{
			"kan_complex(Y)",
			"x₀ ∈ X.simplices(0)",
			"L ∈ simplicial_homotopy_group(Y, p(0, x₀), n + 1)",
		},
		Conclusion: "simplicial_connecting_map(p, x₀, n, L) = " +
			"simplicial_homotopy_unit(simplicial_fiber(p, p(0, x₀)), x₀, n) ⇔ " +
			"∃C:set(A). " +
			"    C ∈ simplicial_homotopy_group(X, x₀, n + 1) ∧ " +
			"    simplicial_homotopy_map(X, Y, p, x₀, n + 1, C) = L",
	},
		func(
			a *Argument,
			fibration Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			hypotheses Fact,
			L *Expr[Set[B]],
			inGroup Fact,
		) {
			simplicialMap := FibrationMap.Read(fibration)
			source := simplicial_set.MapSource.Read(simplicialMap)
			target := simplicial_set.MapTarget.Read(simplicialMap)
			faceFace, baseFace :=
				simplicial_set.FaceFace.Read(source), simplicial_set.BaseSimplexFace.Read(source)
			given := a.Conjuncts(
				hypotheses,
				"Y is a Kan complex",
				"and x₀ is a vertex of X")
			base, vertex := given[0], given[1]
			X := a.TermAs[simplicial_set.SimplicialOps[A]]("X")
			y0, next, top := a.TermAs[B]("p(0, x₀)"), a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 2")

			baseVertex := a.Have(
				"p(0, x₀) is a vertex of Y",
				"p(0, x₀) ∈ Y.simplices(0)",
				By(simplicial_set.MapIn.Read(simplicialMap).At(a.TermAs[Nat]("0"), x0), vertex))
			index := a.Have(
				"n + 1 is positive, and one less is n",
				"0 < n + 1 ∧ n + 1 - 1 = n",
				ByArith())

			a.Iff()
			a.Backward(
				"a class of X is the class of a sphere x, which is "+
					"its own lift, and its n-th face is the base simplex",
				func(b *Argument, comes Fact) {
					C, from := b.UnpackAs[Set[A]](comes, "C")
					parts := b.Conjuncts(
						from,
						"C is a class of πₙ₊₁(X, x₀)",
						"which p carries to L")
					inX, image := parts[0], parts[1]
					x, represented := b.ObtainAs[A](
						"C is the class of a sphere x of X",
						"∃x:A. "+
							"    x ∈ simplicial_sphere(X, x₀, n + 1) ∧ "+
							"    C = equivalence_class(simplicial_homotopic(X, x₀, n + 1), x)",
						By(inX, homotopy_group.InHomotopyGroup.Read(source).At(x0, next, C), vertex))
					classOf := b.Conjuncts(
						represented,
						"x is a sphere of X",
						"whose class is C")
					xSphere, cClass := classOf[0], classOf[1]
					xParts := b.Conjuncts(
						b.Have(
							"x is an (n+1)-simplex of X whose every face is the base simplex",
							"x ∈ X.simplices(n + 1) ∧ (∀i:num. i ≤ n + 1 ⇒ X.d(n + 1, i, x) = base_simplex(x₀, n))",
							BySets(b.Unfolded(xSphere, homotopy_group.SimplicialSphereDef), index)),
						"x is an (n+1)-simplex of X",
						"and each of its faces is the base simplex")
					xIn, xFaces := xParts[0], xParts[1]

					z := b.TermAs[B]("p(n + 1, x)")
					zSphere := b.Have(
						"its image p(n + 1, x) is a sphere of Y",
						"p(n + 1, x) ∈ simplicial_sphere(Y, p(0, x₀), n + 1)",
						By(homotopy_group.MapSphere.Read(simplicialMap).At(x0, next, x), vertex, xSphere))
					lClass := b.Have(
						"L is the class of p(n + 1, x)",
						"L = equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), p(n + 1, x))",
						CalcEq(
							Leg(
								b.TermAs[Set[B]]("simplicial_homotopy_map(X, Y, p, x₀, n + 1, C)"),
								"L is the image of C",
								By(Normalized, image)),
							Leg(
								b.TermAs[Set[B]](
									"simplicial_homotopy_map(X, "+
										"    Y, "+
										"    p, "+
										"    x₀, "+
										"    n + 1, "+
										"    equivalence_class(simplicial_homotopic(X, x₀, n + 1), x))"),
								"C is the class of x",
								By(Normalized, cClass)),
							FinalLeg(
								"and the induced map sends the class of x to the class of its image",
								By(homotopy_group.HomotopyMapClass.Read(simplicialMap).At(x0, next, x), base, vertex, xSphere)),
						))
					b.Show(
						"so the connecting map reads L through the lift x: the class of its n-th face, the base simplex",
						CalcEq(
							Leg(
								b.TermAs[Set[A]](
									"simplicial_connecting_map(p, "+
										"    x₀, "+
										"    n, "+
										"    equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), p(n + 1, x)))"),
								"L is the class of p(n + 1, x)",
								By(Normalized, lClass)),
							Leg(
								b.TermAs[Set[A]](
									"equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), X.d(n + 1, n, x))"),
								"x is a lift of p(n + 1, x) with the base simplex at every face but the n-th",
								By(ConnectingMapClass.Read(fibration).At(x0, n, z, x), hypotheses, zSphere, xIn, xFaces)),
							Leg(
								b.TermAs[Set[A]](
									"equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), "+
										"    base_simplex(x₀, n))"),
								"and the n-th face of x is the base simplex",
								ByArith(xFaces.At(n))),
							FinalLeg(
								"whose class is the unit of the fibre",
								By(homotopy_group.SimplicialHomotopyUnitDef)),
						))
				})
			a.Forward(
				"with z a sphere of class L, w its lift and h a homotopy in the fibre, "+
					"the horn of h, w and the base simplex lifts to a sphere of X over z",
				func(b *Argument, unit Fact) {
					z, represented := b.ObtainAs[B](
						"L is the class of a sphere z of Y",
						"∃z:B. "+
							"    z ∈ simplicial_sphere(Y, p(0, x₀), n + 1) ∧ "+
							"    L = equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), z)",
						By(inGroup, homotopy_group.InHomotopyGroup.Read(target).At(y0, next, L), baseVertex))
					zParts := b.Conjuncts(
						represented,
						"z is a sphere of Y",
						"whose class is L")
					zSphere, lClass := zParts[0], zParts[1]

					w, lifted := b.ObtainAs[A](
						"z lifts to an (n+1)-simplex w of X with the base simplex at every face but the n-th",
						"∃w:A. "+
							"    w ∈ X.simplices(n + 1) ∧ "+
							"    (∀i:num. i ≤ n + 1 ∧ ¬(i = n) ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ "+
							"    p(n + 1, w) = z",
						By(ConnectingLiftExists.Read(fibration).At(x0, n, z), hypotheses, zSphere))
					lift := b.Conjuncts(
						lifted,
						"w is an (n+1)-simplex of X",
						"whose faces other than the n-th are the base simplex",
						"and p carries it to z")
					wIn, wFaces, wOver := lift[0], lift[1], lift[2]

					fiberKan := b.Have(
						"the fibre over p(0, x₀) is a Kan complex",
						"kan_complex(simplicial_fiber(p, p(0, x₀)))",
						By(FiberKan.Read(fibration).At(y0), baseVertex))
					fiberVertex := b.Have(
						"x₀ is a vertex of the fibre",
						"x₀ ∈ simplicial_fiber_simplices(p, p(0, x₀), 0)",
						By(Where(FiberBasePoint, "x_0", x0), vertex))
					nthFace := b.TermAs[A]("X.d(n + 1, n, w)")
					baseSimplex := b.TermAs[A]("base_simplex(x₀, n)")
					faceSphere := b.Have(
						"the n-th face of w is a sphere of the fibre",
						"X.d(n + 1, n, w) ∈ simplicial_sphere(simplicial_fiber(p, p(0, x₀)), x₀, n)",
						By(ConnectingLiftFace.Read(fibration).At(x0, n, z, w), hypotheses, zSphere, lifted))
					baseSphere := b.Have(
						"and so is the base simplex",
						"base_simplex(x₀, n) ∈ simplicial_sphere(simplicial_fiber(p, p(0, x₀)), x₀, n)",
						By(
							homotopy_group.BaseSphere.Read(kan_complex.KanSimplicialSet.Read(fiberKan)).At(x0, n),
							fiberVertex))
					sameClass := b.Have(
						"its class in the fibre is the unit, the class of the base simplex",
						"equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), "+
							"    X.d(n + 1, n, w)) = "+
							"equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), "+
							"    base_simplex(x₀, n))",
						CalcEq(
							Leg(
								b.TermAs[Set[A]](
									"simplicial_connecting_map(p, "+
										"    x₀, "+
										"    n, "+
										"    equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), z))"),
								"the connecting map reads the class of z through its lift w",
								By(ConnectingMapClass.Read(fibration).At(x0, n, z, w), hypotheses, zSphere, lifted)),
							Leg(
								b.TermAs[Set[A]]("simplicial_connecting_map(p, x₀, n, L)"),
								"the class of z is L",
								By(Normalized, lClass)),
							Leg(
								b.TermAs[Set[A]]("simplicial_homotopy_unit(simplicial_fiber(p, p(0, x₀)), x₀, n)"),
								"which the connecting map sends to the unit",
								By(unit)),
							FinalLeg(
								"the class of the base simplex",
								By(homotopy_group.SimplicialHomotopyUnitDef)),
						))
					homotopic := b.Have(
						"so the n-th face of w is homotopic in the fibre to the base simplex",
						"simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n, X.d(n + 1, n, w), base_simplex(x₀, n))",
						By(
							homotopy_group.ClassEqIff.Read(fiberKan).At(x0, n, nthFace, baseSimplex),
							fiberVertex,
							faceSphere,
							baseSphere,
							sameClass))
					_, homotopy := b.UnpackAs[A](b.Unfolded(homotopic, homotopy_group.SimplicialHomotopicDef), "h")
					hParts := b.Conjuncts(
						homotopy,
						"h is an (n+1)-simplex of the fibre",
						"whose faces below n are the base simplex",
						"its face n is the n-th face of w",
						"and its face n + 1 the base simplex")
					hInFiber, hBelow, hStart, hEnd := hParts[0], hParts[1], hParts[2], hParts[3]
					hFacts := b.Conjuncts(
						b.Have(
							"h is an (n+1)-simplex of X over the base simplex of Y",
							"h ∈ X.simplices(n + 1) ∧ p(n + 1, h) = base_simplex(p(0, x₀), n + 1)",
							BySets(b.Unfolded(hInFiber, simplicialFiberSimplicesDef))),
						"h is an (n+1)-simplex of X",
						"over the base simplex of Y")
					hIn, hOver := hFacts[0], hFacts[1]

					// The horn: h at n, w at n + 1, the base simplex at every
					// other index; its value at the missing face n + 2 is never read.
					f, fDef := b.LetAs[Fun[Nat, A]](
						"f", "λi:num. COND(i = n, h, COND(i = n + 1, w, base_simplex(x₀, n + 1)))")
					values := b.Have(
						"f is h at n and w at n + 1",
						"f(n) = h ∧ f(n + 1) = w",
						fDef.Rw(),
						ByArith())
					baseValues := b.Have(
						"and the base simplex below n",
						"∀i:num. i < n ⇒ f(i) = base_simplex(x₀, n + 1)",
						fDef.Rw(),
						b.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
					members := b.Have(
						"every member of f is an (n+1)-simplex of X: h, w or the base simplex",
						"∀i:num. f(i) ∈ X.simplices(n + 1)",
						fDef.Rw(),
						b.ForEach(func(_ *Expr[Nat]) Action {
							return Chain(CondRewrite(), ByArith(
								hIn,
								wIn,
								simplicial_set.BaseSimplexIn.Read(source).At(x0, next),
								vertex))
						}))
					lowerFaces := b.Have(
						"every member of f has the base simplex for its faces below n",
						"∀j i:num. i < n ⇒ X.d(n + 1, i, f(j)) = base_simplex(x₀, n)",
						Derive(func(e *Argument) {
							e.FixAs[Nat]()
							i := e.FixAs[Nat]()
							below := e.Assume()
							e.Show(
								"f(j) is h, w or the base simplex at n + 1, and the face i of each is the base simplex",
								fDef.Rw(),
								CondRewrite(),
								ByArith(hBelow.At(i), wFaces.At(i), baseFace.At(x0, n, i), below, vertex))
						}))
					lastFaces := b.Have(
						"and the base simplex for its face n + 1",
						"∀j:num. X.d(n + 1, n + 1, f(j)) = base_simplex(x₀, n)",
						fDef.Rw(),
						b.ForEach(func(_ *Expr[Nat]) Action {
							return Chain(CondRewrite(), ByArith(hEnd, wFaces.At(next), baseFace.At(x0, n, next), vertex))
						}))
					dims := b.Have(
						"the lift has dimension (n + 1) + 1 = n + 2, and the missing face n + 2 is one of its faces",
						"n + 1 + 1 = n + 2 ∧ n + 2 ≤ n + 1 + 1",
						ByArith())
					compatible := b.Have(
						"so f is compatible on the faces of the horn missing the face n + 2",
						"faces_compatible(n + 1, horn_faces(n + 1, n + 2), f)",
						Simp(Fwd(simplicial_set.FacesCompatibleDef)),
						Derive(func(e *Argument) {
							i, j := e.FixAs[Nat](), e.FixAs[Nat]()
							faces := e.Assume()
							pair := e.Have(
								"i < j are faces of the horn: both at most n + 2, and neither is n + 2",
								"i < j ∧ j ≤ n + 1 + 1 ∧ ¬(i = n + 2) ∧ ¬(j = n + 2)",
								By(
									faces,
									kan_complex.HornFacesMember.At(next, top, i),
									kan_complex.HornFacesMember.At(next, top, j)))
							jPrevious := e.TermAs[Nat]("j - 1")
							notBelow := e.Unless(
								e.Term("i < n"),
								"below n the member f(i) is the base simplex, and both faces are the base simplex at n",
								Given(func(c *Argument, below Fact) {
									c.Show(
										"the face i of f(j) and the face j − 1 of the base simplex f(i) are the base simplex at n",
										ByArith(lowerFaces.At(j, i), baseValues.At(i), baseFace.At(x0, n, jPrevious), below, pair, vertex))
								}))
							at := e.Have(
								"i < j ≤ n + 1 with i not below n leave the pair (n, n + 1)",
								"i = n ∧ j = n + 1 ∧ j - 1 = n",
								ByArith(notBelow, pair))
							e.Show(
								"so at the pair (n, n + 1) the face n of f(n + 1) = w and the face n of f(n) = h agree",
								CalcEq(
									Leg(
										nthFace,
										"f(j) is w",
										ByArith(at, values)),
									Leg(
										e.TermAs[A]("X.d(n + 1, n, h)"),
										"the n-th face of w is the face n of h",
										By(hStart)),
									FinalLeg(
										"and h is f(i)",
										ByArith(at, values)),
								))
						}))
					horn := b.Have(
						"so f is a horn of X: a face family of (n+1)-simplices "+
							"on the faces of the horn missing the face n + 2",
						"face_family(X, n + 1, horn_faces(n + 1, n + 2), f)",
						Simp(Fwd(simplicial_set.FaceFamilyDef)),
						By(members, compatible))

					// The simplex of Y the horn lifts over: the last degeneracy of z.
					degenerate := b.TermAs[B]("Y.s(n + 1, n + 1, z)")
					table := b.Conjuncts(
						b.Have(
							"the face table of the degeneracy s'(n + 1, n + 1, z) of the sphere z",
							"Y.s(n + 1, n + 1, z) ∈ Y.simplices(n + 2) ∧ "+
								"Y.d(n + 2, n + 1, Y.s(n + 1, n + 1, z)) = z ∧ "+
								"Y.d(n + 2, n + 2, Y.s(n + 1, n + 1, z)) = z ∧ "+
								"(∀i:num. "+
								"    i ≤ n + 2 ∧ ¬(i = n + 1) ∧ ¬(i = n + 2) ⇒ "+
								"    Y.d(n + 2, i, Y.s(n + 1, n + 1, z)) = base_simplex(p(0, x₀), n + 1))",
							ByArith(
								homotopy_group.SphereDegeneracyFaces.Read(target).At(y0, next, z, next),
								baseVertex,
								zSphere,
								dims)),
						"the degeneracy is an (n+2)-simplex of Y",
						"whose face n + 1 is z",
						"as is its face n + 2",
						"and whose other faces are the base simplex of Y")
					degenerateIn, degenerateAtNext, degenerateAtTop, degenerateAway :=
						table[0], table[1], table[2], table[3]
					memberImages := b.Have(
						"p carries the members of f below n + 1 to the base simplex of Y: h lies in the fibre",
						"∀i:num. i ≤ n ⇒ p(n + 1, f(i)) = base_simplex(p(0, x₀), n + 1)",
						fDef.Rw(),
						b.ForEach(func(_ *Expr[Nat]) Action {
							return Chain(CondRewrite(), ByArith(
								hOver,
								simplicial_set.MapBaseSimplex.Read(simplicialMap).At(x0, next),
								vertex))
						}))
					images := b.Have(
						"the faces of the degeneracy at the faces of the horn are the images of the members of f",
						"faces_filler(n + 1, horn_faces(n + 1, n + 2), λi:num. p(n + 1, f(i)), Y.s(n + 1, n + 1, z))",
						Simp(Fwd(simplicial_set.FacesFillerDef)),
						Derive(func(e *Argument) {
							i := e.FixAs[Nat]()
							face := e.Assume()
							within := e.Have(
								"a face of the horn is at most n + 2, and not n + 2",
								"i ≤ n + 1 + 1 ∧ ¬(i = n + 2)",
								By(face, kan_complex.HornFacesMember.At(next, top, i)))
							e.Cases(e.Term("i ≤ n"))
							e.When(
								"below n + 1 both are the base simplex of Y",
								func(e *Argument, below Fact) {
									e.Show(
										"the face i of the degeneracy and the image of f(i) are the base simplex",
										ByArith(degenerateAway.At(i), memberImages.At(i), below, dims))
								})
							e.Otherwise(
								"at n + 1 both are z",
								func(e *Argument, above Fact) {
									at := e.Have(
										"i is n + 1",
										"i = n + 1",
										ByArith(above, within))
									e.Show(
										"the face n + 1 of the degeneracy is z, the image of w = f(n + 1)",
										CalcEq(
											Leg(
												z,
												"its face n + 1 is z",
												ByArith(degenerateAtNext, at, dims)),
											Leg(
												e.TermAs[B]("p(n + 1, w)"),
												"w lies over z",
												By(wOver)),
											FinalLeg(
												"and w is f(n + 1)",
												By(Normalized, at, values)),
										))
								})
						}))

					v, filled := b.ObtainAs[A](
						"so the horn lifts along the fibration to an (n+2)-simplex v of X over the degeneracy",
						"∃v:A. "+
							"    v ∈ X.simplices(n + 2) ∧ "+
							"    faces_filler(n + 1, horn_faces(n + 1, n + 2), f, v) ∧ "+
							"    p(n + 2, v) = Y.s(n + 1, n + 1, z)",
						By(FibrationLift.Read(fibration).At(next, top, f, degenerate), dims, horn, degenerateIn, images))
					vParts := b.Conjuncts(
						filled,
						"v is an (n+2)-simplex of X",
						"whose faces other than the last are the members of f",
						"over the degeneracy")
					vIn, vOver := vParts[0], vParts[2]
					faceOfV := b.Unfolded(vParts[1], simplicial_set.FacesFillerDef)

					c := b.TermAs[A]("X.d(n + 2, n + 2, v)")
					cIn := b.Have(
						"the last face c of v is an (n+1)-simplex of X",
						"X.d(n + 2, n + 2, v) ∈ X.simplices(n + 1)",
						ByArith(simplicial_set.FaceIn.Read(source).At(next, top, v), vIn, dims))
					cOver := b.Have(
						"which p carries to z",
						"p(n + 1, X.d(n + 2, n + 2, v)) = z",
						CalcEq(
							Leg(
								b.TermAs[B]("Y.d(n + 2, n + 2, p(n + 2, v))"),
								"p commutes with the last face",
								ByArith(simplicial_set.MapFace.Read(simplicialMap).At(next, top, v), vIn, dims)),
							Leg(
								b.TermAs[B]("Y.d(n + 2, n + 2, Y.s(n + 1, n + 1, z))"),
								"v lies over the degeneracy",
								By(vOver)),
							FinalLeg(
								"whose last face is z",
								By(degenerateAtTop)),
						))
					cFaces := b.Have(
						"and every face of c is the base simplex",
						"∀i:num. i ≤ n + 1 ⇒ X.d(n + 1, i, X.d(n + 2, n + 2, v)) = base_simplex(x₀, n)",
						Derive(func(e *Argument) {
							i := e.FixAs[Nat]()
							within := e.Assume()
							e.Show(
								"the face i of c is the last face of the member f(i)",
								CalcEq(
									Leg(
										e.TermAs[A]("X.d(n + 1, n + 1, X.d(n + 2, i, v))"),
										"the face identity of v at the pair (i, n + 2)",
										ByArith(faceFace.At(n, i, top, v), vIn, within)),
									Leg(
										e.TermAs[A]("X.d(n + 1, n + 1, f(i))"),
										"the face i of v is f(i)",
										ByArith(faceOfV.At(i), kan_complex.HornFacesMember.At(next, top, i), dims, within)),
									FinalLeg(
										"whose last face is the base simplex",
										By(lastFaces.At(i))),
								))
						}))
					cSphere := b.Have(
						"so c is a sphere of X",
						"X.d(n + 2, n + 2, v) ∈ simplicial_sphere(X, x₀, n + 1)",
						BySets(At(homotopy_group.SimplicialSphereDef, X, x0, next), cIn, cFaces, index))
					classC := b.TermAs[Set[A]](
						"equivalence_class(simplicial_homotopic(X, x₀, n + 1), X.d(n + 2, n + 2, v))")
					inPi := b.Have(
						"so its class is a class of πₙ₊₁(X, x₀)",
						"equivalence_class(simplicial_homotopic(X, x₀, n + 1), X.d(n + 2, n + 2, v)) ∈ "+
							"simplicial_homotopy_group(X, x₀, n + 1)",
						By(cSphere, homotopy_group.ClassInHomotopyGroup.Read(source).At(x0, next, c), vertex))
					mapped := b.Have(
						"which p carries to L",
						"simplicial_homotopy_map(X, "+
							"    Y, "+
							"    p, "+
							"    x₀, "+
							"    n + 1, "+
							"    equivalence_class(simplicial_homotopic(X, x₀, n + 1), X.d(n + 2, n + 2, v))) = "+
							"L",
						CalcEq(
							Leg(
								b.TermAs[Set[B]](
									"equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), p(n + 1, X.d(n + 2, n + 2, v)))"),
								"the induced map sends the class of a sphere to the class of its image",
								By(homotopy_group.HomotopyMapClass.Read(simplicialMap).At(x0, next, c), base, vertex, cSphere)),
							Leg(
								b.TermAs[Set[B]]("equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), z)"),
								"c lies over z",
								By(Normalized, cOver)),
							FinalLeg(
								"whose class is L",
								By(Normalized, lClass)),
						))
					b.Take(classC)
					b.Show(
						"so the class of c comes from X and maps to L",
						By(inPi, mapped))
				})
		}),
})}

// ExactAtFiber — at πₙ(F): a class of the fibre is sent to the unit of
// X by the inclusion exactly when it is a connecting image. A lift w
// of a sphere of Y, with the base simplex at every face but the n-th,
// is a homotopy in X from its n-th face to the base simplex; and a
// homotopy h in X from a sphere a of the fibre to the base simplex is
// such a lift of p(n + 1, h), whose faces are all the base simplex of
// Y because a lies in the fibre.
var ExactAtFiber = exactAtFiberThm{family.Add(registry.ProofEntry{
	Name: "ExactAtFiber",
	Reading: "kan_complex(Y) is read through TotalKan, which makes X the Kan " +
		"complex where, in both directions, the class of a sphere of the fibre " +
		"is compared with the unit (FiberInclusionClass, then ClassEqIff in X).",
	Key: "prop_f7c79fda209a7b1b",
	Build: KanFibration.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀K:set(A).",
		Hypotheses: []string{
			"kan_complex(Y)",
			"x₀ ∈ X.simplices(0)",
			"K ∈ simplicial_homotopy_group(simplicial_fiber(p, p(0, x₀)), x₀, n)",
		},
		Conclusion: "simplicial_homotopy_map(simplicial_fiber(p, p(0, x₀)), " +
			"    X, " +
			"    λm:num. λx:A. x, " +
			"    x₀, " +
			"    n, " +
			"    K) = " +
			"simplicial_homotopy_unit(X, x₀, n) ⇔ " +
			"∃L:set(B). " +
			"    L ∈ simplicial_homotopy_group(Y, p(0, x₀), n + 1) ∧ " +
			"    simplicial_connecting_map(p, x₀, n, L) = K",
	},
		func(
			arg *Argument,
			fibration Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			hypotheses Fact,
			K *Expr[Set[A]],
			inGroup Fact,
		) {
			simplicialMap := FibrationMap.Read(fibration)
			source := simplicial_set.MapSource.Read(simplicialMap)
			target := simplicial_set.MapTarget.Read(simplicialMap)
			given := arg.Conjuncts(
				hypotheses,
				"Y is a Kan complex",
				"and x₀ is a vertex of X")
			base, vertex := given[0], given[1]
			Y := arg.TermAs[simplicial_set.SimplicialOps[B]]("Y")
			y0, next := arg.TermAs[B]("p(0, x₀)"), arg.TermAs[Nat]("n + 1")
			baseSimplex := arg.TermAs[A]("base_simplex(x₀, n)")

			total := arg.Have(
				"X is a Kan complex, the source of a fibration over one",
				"kan_complex(X)",
				By(TotalKan.Read(fibration), base))
			baseSphere := arg.Have(
				"the base simplex is a sphere of X",
				"base_simplex(x₀, n) ∈ simplicial_sphere(X, x₀, n)",
				By(homotopy_group.BaseSphere.Read(source).At(x0, n), vertex))
			baseVertex := arg.Have(
				"p(0, x₀) is a vertex of Y",
				"p(0, x₀) ∈ Y.simplices(0)",
				By(simplicial_set.MapIn.Read(simplicialMap).At(arg.TermAs[Nat]("0"), x0), vertex))

			arg.Iff()
			arg.Backward(
				"L is the class of a sphere z of Y; a lift w of z is a homotopy "+
					"in X from its n-th face, whose class is K, to the base simplex",
				func(b *Argument, comes Fact) {
					L, from := b.UnpackAs[Set[B]](comes, "L")
					parts := b.Conjuncts(
						from,
						"L is a class of πₙ₊₁(Y, p(0, x₀))",
						"which the connecting map sends to K")
					inY, image := parts[0], parts[1]
					z, represented := b.ObtainAs[B](
						"L is the class of a sphere z of Y",
						"∃z:B. "+
							"    z ∈ simplicial_sphere(Y, p(0, x₀), n + 1) ∧ "+
							"    L = equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), z)",
						By(inY, homotopy_group.InHomotopyGroup.Read(target).At(y0, next, L), baseVertex))
					zParts := b.Conjuncts(
						represented,
						"z is a sphere of Y",
						"whose class is L")
					zSphere, lClass := zParts[0], zParts[1]

					w, lifted := b.ObtainAs[A](
						"z lifts to an (n+1)-simplex w of X with the base simplex at every face but the n-th",
						"∃w:A. "+
							"    w ∈ X.simplices(n + 1) ∧ "+
							"    (∀i:num. i ≤ n + 1 ∧ ¬(i = n) ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ "+
							"    p(n + 1, w) = z",
						By(ConnectingLiftExists.Read(fibration).At(x0, n, z), hypotheses, zSphere))
					lift := b.Conjuncts(
						lifted,
						"w is an (n+1)-simplex of X",
						"whose faces other than the n-th are the base simplex",
						"and p carries it to z")
					wIn, wFaces := lift[0], lift[1]
					nthFace := b.TermAs[A]("X.d(n + 1, n, w)")
					faceSphereFiber := b.Have(
						"the n-th face of w is a sphere of the fibre",
						"X.d(n + 1, n, w) ∈ simplicial_sphere(simplicial_fiber(p, p(0, x₀)), x₀, n)",
						By(ConnectingLiftFace.Read(fibration).At(x0, n, z, w), hypotheses, zSphere, lifted))
					kClass := b.Have(
						"K is the class of the n-th face of w in the fibre",
						"K = "+
							"equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), X.d(n + 1, n, w))",
						CalcEq(
							Leg(
								b.TermAs[Set[A]]("simplicial_connecting_map(p, x₀, n, L)"),
								"K is the connecting image of L",
								By(Normalized, image)),
							Leg(
								b.TermAs[Set[A]](
									"simplicial_connecting_map(p, "+
										"    x₀, "+
										"    n, "+
										"    equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), z))"),
								"L is the class of z",
								By(Normalized, lClass)),
							FinalLeg(
								"the connecting map reads the class of z through its lift w",
								By(ConnectingMapClass.Read(fibration).At(x0, n, z, w), hypotheses, zSphere, lifted)),
						))

					below := b.Have(
						"below n the faces of w are the base simplex",
						"∀i:num. i < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)",
						b.ForEach(func(i *Expr[Nat]) Action { return ByArith(wFaces.At(i)) }))
					last := b.Have(
						"and so is its face n + 1",
						"X.d(n + 1, n + 1, w) = base_simplex(x₀, n)",
						ByArith(wFaces.At(next)))
					homotopic := b.Have(
						"so w is a homotopy in X from its n-th face to the base simplex",
						"simplicial_homotopic(X, x₀, n, X.d(n + 1, n, w), base_simplex(x₀, n))",
						Simp(Fwd(homotopy_group.SimplicialHomotopicDef)),
						Derive(func(c *Argument) {
							c.Take(w)
							c.Show(
								"w is an (n+1)-simplex of X with the base simplex below n and at n + 1",
								By(wIn, below, last))
						}))
					faceSphereX := b.Have(
						"the n-th face of w is a sphere of X",
						"X.d(n + 1, n, w) ∈ simplicial_sphere(X, x₀, n)",
						By(Where(FiberSphere, "x_0", x0).Where("n", n).Where("x", nthFace), faceSphereFiber))

					b.Show(
						"so the inclusion sends K to the class in X of the n-th face of w, the class of the base simplex",
						CalcEq(
							Leg(
								b.TermAs[Set[A]](
									"simplicial_homotopy_map(simplicial_fiber(p, p(0, x₀)), "+
										"    X, "+
										"    λm:num. λx:A. x, "+
										"    x₀, "+
										"    n, "+
										"    equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), "+
										"        X.d(n + 1, n, w)))"),
								"K is the class of the n-th face of w in the fibre",
								By(Normalized, kClass)),
							Leg(
								b.TermAs[Set[A]]("equivalence_class(simplicial_homotopic(X, x₀, n), X.d(n + 1, n, w))"),
								"the inclusion sends the class of a sphere of the fibre to its class in X",
								By(FiberInclusionClass.Read(simplicialMap).At(x0, n, nthFace), total, vertex, faceSphereFiber)),
							Leg(
								b.TermAs[Set[A]]("equivalence_class(simplicial_homotopic(X, x₀, n), base_simplex(x₀, n))"),
								"w is a homotopy in X from the n-th face to the base simplex",
								By(
									homotopy_group.ClassEqIff.Read(total).At(x0, n, nthFace, baseSimplex),
									vertex,
									faceSphereX,
									baseSphere,
									homotopic)),
							FinalLeg(
								"the class of the base simplex is the unit",
								By(homotopy_group.SimplicialHomotopyUnitDef)),
						))
				})
			arg.Forward(
				"with a a sphere of class K, a homotopy h in X from a to the "+
					"base simplex is a lift of the sphere p(n + 1, h) of Y, sent to K",
				func(b *Argument, unit Fact) {
					fiberSimplicial := b.Have(
						"the fibre over p(0, x₀) is a simplicial set",
						"simplicial_set(simplicial_fiber(p, p(0, x₀)))",
						By(FiberSimplicialSet.Read(simplicialMap).At(y0), baseVertex))
					fiberVertex := b.Have(
						"x₀ is a vertex of the fibre",
						"x₀ ∈ simplicial_fiber_simplices(p, p(0, x₀), 0)",
						By(Where(FiberBasePoint, "x_0", x0), vertex))
					a, represented := b.ObtainAs[A](
						"K is the class of a sphere a of the fibre",
						"∃a:A. "+
							"    a ∈ simplicial_sphere(simplicial_fiber(p, p(0, x₀)), x₀, n) ∧ "+
							"    K = equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), a)",
						By(inGroup, homotopy_group.InHomotopyGroup.Read(fiberSimplicial).At(x0, n, K), fiberVertex))
					aParts := b.Conjuncts(
						represented,
						"a is a sphere of the fibre",
						"whose class there is K")
					aSphereFiber, kClass := aParts[0], aParts[1]
					over := b.Conjuncts(
						b.Have(
							"a is a sphere of X over the base simplex of Y",
							"a ∈ simplicial_sphere(X, x₀, n) ∧ p(n, a) = base_simplex(p(0, x₀), n)",
							By(Where(FiberSphere, "x_0", x0).Where("n", n).Where("x", a), aSphereFiber)),
						"a is a sphere of X",
						"lying over the base simplex of Y")
					aSphereX, aOver := over[0], over[1]

					sameClass := b.Have(
						"the class of a in X is the class of the base simplex",
						"equivalence_class(simplicial_homotopic(X, x₀, n), a) = "+
							"equivalence_class(simplicial_homotopic(X, x₀, n), base_simplex(x₀, n))",
						CalcEq(
							Leg(
								b.TermAs[Set[A]](
									"simplicial_homotopy_map(simplicial_fiber(p, p(0, x₀)), "+
										"    X, "+
										"    λm:num. λx:A. x, "+
										"    x₀, "+
										"    n, "+
										"    equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), a))"),
								"the inclusion sends the class of a in the fibre to its class in X",
								By(FiberInclusionClass.Read(simplicialMap).At(x0, n, a), total, vertex, aSphereFiber)),
							Leg(
								b.TermAs[Set[A]](
									"simplicial_homotopy_map(simplicial_fiber(p, p(0, x₀)), X, λm:num. λx:A. x, x₀, n, K)"),
								"the class of a in the fibre is K",
								By(kClass)),
							Leg(
								b.TermAs[Set[A]]("simplicial_homotopy_unit(X, x₀, n)"),
								"which the inclusion sends to the unit",
								By(unit)),
							FinalLeg(
								"the class of the base simplex",
								By(homotopy_group.SimplicialHomotopyUnitDef)),
						))
					homotopic := b.Have(
						"so a is homotopic in X to the base simplex",
						"simplicial_homotopic(X, x₀, n, a, base_simplex(x₀, n))",
						By(
							homotopy_group.ClassEqIff.Read(total).At(x0, n, a, baseSimplex),
							vertex,
							aSphereX,
							baseSphere,
							sameClass))
					h, homotopy := b.UnpackAs[A](b.Unfolded(homotopic, homotopy_group.SimplicialHomotopicDef), "h")
					hParts := b.Conjuncts(
						homotopy,
						"h is an (n+1)-simplex of X",
						"whose faces below n are the base simplex",
						"its face n is a",
						"and its face n + 1 the base simplex")
					hIn, hBelow, hStart, hEnd := hParts[0], hParts[1], hParts[2], hParts[3]

					hFaces := b.Have(
						"every face of h but the n-th is the base simplex",
						"∀i:num. i ≤ n + 1 ∧ ¬(i = n) ⇒ X.d(n + 1, i, h) = base_simplex(x₀, n)",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]()
							within := c.Assume()
							c.Cases(c.Term("i < n"))
							c.When(
								"below n it is a face of the homotopy below n",
								func(e *Argument, lower Fact) {
									e.Show(
										"the face i of h is the base simplex",
										By(hBelow.At(i), lower))
								})
							c.Otherwise(
								"otherwise it is the last face",
								func(e *Argument, upper Fact) {
									at := e.Have(
										"i is n + 1",
										"i = n + 1",
										ByArith(upper, within))
									e.Show(
										"the face n + 1 of h is the base simplex",
										By(Normalized, at, hEnd))
								})
						}))
					images := b.Have(
						"p carries every face of h to the base simplex of Y",
						"∀i:num. i ≤ n + 1 ⇒ p(n, X.d(n + 1, i, h)) = base_simplex(p(0, x₀), n)",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]()
							within := c.Assume()
							c.Cases(c.Term("i = n"))
							c.When(
								"the n-th face of h is a, which lies in the fibre",
								func(e *Argument, at Fact) {
									e.Show(
										"p carries a to the base simplex of Y",
										at.Rw(),
										By(Normalized, hStart, aOver))
								})
							c.Otherwise(
								"any other face of h is the base simplex of X, which p carries to the base simplex of Y",
								func(e *Argument, other Fact) {
									e.Show(
										"the face i of h maps to the base simplex of Y",
										By(
											Normalized,
											hFaces.At(i),
											within,
											other,
											simplicial_set.MapBaseSimplex.Read(simplicialMap).At(x0, n),
											vertex))
								})
						}))
					z := b.TermAs[B]("p(n + 1, h)")
					zIn := b.Have(
						"z = p(n + 1, h) is an (n+1)-simplex of Y",
						"p(n + 1, h) ∈ Y.simplices(n + 1)",
						By(simplicial_set.MapIn.Read(simplicialMap).At(next, h), hIn))
					zFaces := b.Have(
						"and each of its faces, the image of a face of h, is the base simplex of Y",
						"∀i:num. i ≤ n + 1 ⇒ Y.d(n + 1, i, p(n + 1, h)) = base_simplex(p(0, x₀), n)",
						b.ForEach(func(i *Expr[Nat]) Action {
							return By(simplicial_set.MapFace.Read(simplicialMap).At(n, i, h), hIn, images.At(i))
						}))
					index := b.Have(
						"n + 1 is positive, and one less is n",
						"0 < n + 1 ∧ n + 1 - 1 = n",
						ByArith())
					zSphere := b.Have(
						"so z is a sphere of Y",
						"p(n + 1, h) ∈ simplicial_sphere(Y, p(0, x₀), n + 1)",
						BySets(At(homotopy_group.SimplicialSphereDef, Y, y0, next), zIn, zFaces, index))

					connects := b.Have(
						"the connecting map sends the class of z to K",
						"simplicial_connecting_map(p, "+
							"    x₀, "+
							"    n, "+
							"    equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), p(n + 1, h))) = "+
							"K",
						CalcEq(
							Leg(
								b.TermAs[Set[A]](
									"equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), X.d(n + 1, n, h))"),
								"h is a lift of z with the base simplex at every face but the n-th",
								By(ConnectingMapClass.Read(fibration).At(x0, n, z, h), hypotheses, zSphere, hIn, hFaces)),
							Leg(
								b.TermAs[Set[A]](
									"equivalence_class(simplicial_homotopic(simplicial_fiber(p, p(0, x₀)), x₀, n), a)"),
								"the n-th face of h is a",
								By(hStart)),
							FinalLeg(
								"whose class in the fibre is K",
								By(Normalized, kClass)),
						))
					zClass := b.TermAs[Set[B]](
						"equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), p(n + 1, h))")
					inPi := b.Have(
						"so its class is a class of πₙ₊₁(Y, p(0, x₀))",
						"equivalence_class(simplicial_homotopic(Y, p(0, x₀), n + 1), p(n + 1, h)) ∈ "+
							"simplicial_homotopy_group(Y, p(0, x₀), n + 1)",
						By(zSphere, homotopy_group.ClassInHomotopyGroup.Read(target).At(y0, next, z), baseVertex))
					b.Take(zClass)
					b.Show(
						"so the class of z is in πₙ₊₁(Y, p(0, x₀)) and the connecting map sends it to K",
						By(inPi, connects))
				})
		}),
})}
