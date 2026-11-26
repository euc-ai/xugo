// homotopy_group.go — the homotopy groups of a Kan complex at a vertex:
// the n-spheres are the n-simplices all of whose faces are the base
// simplex, two spheres are homotopic when an (n+1)-simplex has them as
// its last two faces and the base simplex for the others, and the
// n-th homotopy group is the set of classes of spheres under that
// relation. For 0 < n the classes multiply by filling a horn, the
// product of two spheres being the n-th face of a filler whose last
// face is the first sphere and whose (n−1)-th face is the second; the
// unit is the class of the base simplex, and the inverse the last
// face of a filler whose n-th face is the base simplex. That the
// product does not depend on the filler nor on the representatives
// takes three horn fillings of dimension n + 2, and associativity one;
// the unit is a left identity through a degeneracy, with no filling,
// and the inverse a left inverse through the filler that defines it;
// for 2 ≤ n three more fillings make the group abelian. A simplicial
// map sends spheres to spheres and homotopies to homotopies, so it
// induces a map of the classes, a homomorphism for 0 < n.
//
// The index n is the dimension of the spheres throughout: the group
// laws are stated under `0 < n`, where `n - 1` is exact, and π₀ is the
// set of classes of vertices under the edges. The representatives the
// operations read are chosen by ε, and are read through Representative
// or, where the source need not be Kan, through
// equivalence.ChosenRepresentative: x is homotopic to itself, so to the
// point chosen in its class.

package homotopy_group

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Spheres, homotopy and the classes
// ---------------------------------------------------------------------------

// SimplicialSphereDef — `simplicial_sphere(X, x₀, n)`: the
// n-simplices every face of which is the base simplex at x₀; at n = 0
// every vertex. Under the structure the text writes
// `simplicial_sphere(x₀, n)`.
var SimplicialSphereDef = simplicialSphereDefThm{family.Define(registry.DefEntry{
	Name:     "SimplicialSphereDef",
	Key:      "prop_bd46e8958ede8956",
	Const:    "simplicial_sphere",
	Type:     "simplicial_ops(A) → A → num → set(A)",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀x₀:A. ∀n:num. " +
			"    simplicial_sphere(X, x₀, n) = " +
			"    {x:A | " +
			"        x ∈ X.simplices(n) ∧ " +
			"        (∀i:num. i ≤ n ∧ 0 < n ⇒ X.d(n, i, x) = base_simplex(X.s, x₀, n - 1))}",
	},
	Reading: "The guard 0 < n keeps the faces of a vertex, which no " +
		"axiom reads, out of the condition: the 0-spheres are all of X(0).",
})}

// SimplicialHomotopicDef — `simplicial_homotopic(X, x₀, n, x, y)`:
// an (n+1)-simplex has x as its n-th face, y as its (n+1)-th, and the
// base simplex for every face below n. At n = 0 it is an edge from y
// to x, its source being its face 1. Under the structure the text writes
// `simplicial_homotopic(x₀, n, x, y)`.
var SimplicialHomotopicDef = simplicialHomotopicDefThm{family.Define(registry.DefEntry{
	Name:     "SimplicialHomotopicDef",
	Key:      "prop_4dd0d137f46e38eb",
	Const:    "simplicial_homotopic",
	Type:     "simplicial_ops(A) → A → num → A → A → bool",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀x₀:A. ∀n:num. ∀x y:A. " +
			"    simplicial_homotopic(X, x₀, n, x, y) ⇔ " +
			"    (∃h:A. " +
			"        h ∈ X.simplices(n + 1) ∧ " +
			"        (∀i:num. i < n ⇒ X.d(n + 1, i, h) = base_simplex(X.s, x₀, n)) ∧ " +
			"        X.d(n + 1, n, h) = x ∧ " +
			"        X.d(n + 1, n + 1, h) = y)",
	},
	Reading: "The relation is between simplices of the type, not of the sphere; a " +
		"simplex homotopic to a sphere is a sphere (HomotopicSphere), so it is an equivalence " +
		"on the spheres, where the classes are taken, and its two ends share their n-th face.",
})}

// SimplicialHomotopyGroupDef — `simplicial_homotopy_group(X, x₀, n)`:
// πₙ(X, x₀) as a set, the quotient of the n-spheres by homotopy — the
// relations chapter's `quotient_on` at the spheres and the homotopy
// relation. Its members are the classes of spheres (InHomotopyGroup).
// Under the structure the text writes `simplicial_homotopy_group(x₀, n)`.
var SimplicialHomotopyGroupDef = simplicialHomotopyGroupDefThm{family.Define(registry.DefEntry{
	Name:     "SimplicialHomotopyGroupDef",
	Key:      "prop_8d3ae595dc09805a",
	Const:    "simplicial_homotopy_group",
	Type:     "simplicial_ops(A) → A → num → set(set(A))",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀x₀:A. ∀n:num. " +
			"    simplicial_homotopy_group(X, x₀, n) = " +
			"    quotient_on(simplicial_sphere(X, x₀, n), simplicial_homotopic(X, x₀, n))",
	},
	Deps: []registry.EntryLike{SimplicialSphereDef, SimplicialHomotopicDef},
})}

// SimplicialHomotopyUnitDef — the class of the base simplex, the unit
// of πₙ.
var SimplicialHomotopyUnitDef = simplicialHomotopyUnitDefThm{family.Define(registry.DefEntry{
	Name:     "SimplicialHomotopyUnitDef",
	Key:      "prop_db99ee710ba3fcc9",
	Const:    "simplicial_homotopy_unit",
	Type:     "simplicial_ops(A) → A → num → set(A)",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀x₀:A. ∀n:num. " +
			"    simplicial_homotopy_unit(X, x₀, n) = " +
			"    equivalence_class(simplicial_homotopic(X, x₀, n), base_simplex(X.s, x₀, n))",
	},
	Deps: []registry.EntryLike{SimplicialHomotopicDef},
})}

// SimplicialHomotopyMulDef — `simplicial_homotopy_mul(…, x₀, n, C, C')`:
// the product of two classes, for 0 < n: a representative x of C and
// y of C' are chosen, then an (n+1)-simplex w with d(n + 1, n + 1, w) = x,
// d(n + 1, n - 1, w) = y and the base simplex for the faces below n − 1
// — a filler of the horn with the n-th face missing — and the product
// is the class of that n-th face. In π₁ the product of the classes of
// two edges x then y is the class of the edge the 2-simplex x, y
// closes, the composite in the order the edges are traversed.
var SimplicialHomotopyMulDef = simplicialHomotopyMulDefThm{family.Define(registry.DefEntry{
	Name:     "SimplicialHomotopyMulDef",
	Key:      "prop_beb57a5e45f62a84",
	Const:    "simplicial_homotopy_mul",
	Type:     "simplicial_ops(A) → A → num → set(A) → set(A) → set(A)",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀x₀:A. ∀n:num. ∀C C':set(A). " +
			"    simplicial_homotopy_mul(X, x₀, n, C, C') = " +
			"    equivalence_class(simplicial_homotopic(X, x₀, n), " +
			"        X.d(n + 1, " +
			"            n, " +
			"            εw:A. " +
			"                w ∈ X.simplices(n + 1) ∧ " +
			"                (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(X.s, x₀, n)) ∧ " +
			"                X.d(n + 1, n + 1, w) = (εx:A. x ∈ C) ∧ " +
			"                X.d(n + 1, n - 1, w) = (εy:A. y ∈ C')))",
	},
	Reading: "The filler and the two representatives are chosen by ε; MulClass says " +
		"the class of the n-th face is the same for every choice, and that is the only way " +
		"the operation is read. At n = 0 the value is unconstrained and no law is stated.",
	Deps: []registry.EntryLike{SimplicialHomotopicDef},
})}

// SimplicialHomotopyInvDef — `simplicial_homotopy_inv(…, x₀, n, C)`:
// the inverse of a class, for 0 < n: the class of the last face of an
// (n+1)-simplex whose (n−1)-th face is a representative of C, whose
// n-th face is the base simplex, and whose lower faces are the base
// simplex — a filler of the horn with the last face missing, so that
// the product of the inverse with the representative is the unit.
var SimplicialHomotopyInvDef = simplicialHomotopyInvDefThm{family.Define(registry.DefEntry{
	Name:     "SimplicialHomotopyInvDef",
	Key:      "prop_dc7a0d37be4a6a21",
	Const:    "simplicial_homotopy_inv",
	Type:     "simplicial_ops(A) → A → num → set(A) → set(A)",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀x₀:A. ∀n:num. ∀C:set(A). " +
			"    simplicial_homotopy_inv(X, x₀, n, C) = " +
			"    equivalence_class(simplicial_homotopic(X, x₀, n), " +
			"        X.d(n + 1, " +
			"            n + 1, " +
			"            εw:A. " +
			"                w ∈ X.simplices(n + 1) ∧ " +
			"                (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(X.s, x₀, n)) ∧ " +
			"                X.d(n + 1, n - 1, w) = (εx:A. x ∈ C) ∧ " +
			"                X.d(n + 1, n, w) = base_simplex(X.s, x₀, n)))",
	},
	Deps: []registry.EntryLike{SimplicialHomotopicDef},
})}

// SimplicialHomotopyMapDef — `simplicial_homotopy_map(…, F, x₀, n, C)`:
// the class a simplicial map induces, the class in the target of the
// image of a representative. Under the two structures the text writes
// `simplicial_homotopy_map(F, x₀, n, C)`.
var SimplicialHomotopyMapDef = simplicialHomotopyMapDefThm{family.Define(registry.DefEntry{
	Name:     "SimplicialHomotopyMapDef",
	Key:      "prop_d0c89656a2d6e30f",
	Const:    "simplicial_homotopy_map",
	Type:     "simplicial_ops(A) → simplicial_ops(B) → (num → A → B) → A → num → set(A) → set(B)",
	Implicit: []string{"X", "Y"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). ∀F:(num → A → B). ∀x₀:A. ∀n:num. ∀C:set(A). " +
			"    simplicial_homotopy_map(X, Y, F, x₀, n, C) = " +
			"    equivalence_class(simplicial_homotopic(Y, F(0, x₀), n), F(n, εx:A. x ∈ C))",
	},
	Deps: []registry.EntryLike{SimplicialHomotopicDef},
})}

// BaseSphere — the base simplex is a sphere: it is an n-simplex, and
// for 0 < n its face i, read at the dimension (n − 1) + 1, is the base
// simplex one dimension down.
var BaseSphere = baseSphereThm{family.Add(registry.ProofEntry{
	Name: "BaseSphere",
	Key:  "prop_2eaa7a7476be509f",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀x₀:A. ∀n:num.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
		},
		Conclusion: "base_simplex(x₀, n) ∈ simplicial_sphere(x₀, n)",
	},
		func(a *Argument, simplicial Fact, x0 *Expr[A], n *Expr[Nat], vertex Fact) {
			faces := a.Have(
				"for 0 < n every face of the base simplex is the base simplex one dimension down",
				"∀i:num. i ≤ n ∧ 0 < n ⇒ X.d(n, i, base_simplex(x₀, n)) = base_simplex(x₀, n - 1)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					position := b.Assume()
					shift := b.Have(
						"n, being positive, is (n − 1) + 1",
						"n - 1 + 1 = n",
						ByArith(position))
					b.Show(
						"so the face i of the base simplex at (n − 1) + 1 is the base simplex at n − 1",
						By(
							simplicial_set.BaseSimplexFace.Read(simplicial).At(x0, b.TermAs[Nat]("n - 1"), i),
							vertex,
							shift,
							position))
				}))
			a.Show(
				"the base simplex is an n-simplex, and with its faces it is an n-sphere",
				Unfold(SimplicialSphereDef),
				BySets(simplicial_set.BaseSimplexIn.Read(simplicial).At(x0, n), vertex, faces))
		}),
})}

// HomotopicSphere — a simplex homotopic to a sphere is a sphere: the
// homotopy fixes the faces below n of both ends as the base simplex
// and makes their n-th faces equal.
var HomotopicSphere = homotopicSphereThm{family.Add(registry.ProofEntry{
	Name: "HomotopicSphere",
	Key:  "prop_6f3d39f742757b5a",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x y:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"simplicial_homotopic(x₀, n, x, y)",
		},
		Conclusion: "x ∈ simplicial_sphere(x₀, n) ⇔ y ∈ simplicial_sphere(x₀, n)",
	},
		func(
			a *Argument,
			simplicial Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			x, y *Expr[A],
			vertex, homotopic Fact,
		) {
			faceIn := simplicial_set.FaceIn.Read(simplicial)
			baseInherited := simplicial_set.BaseSimplexFaceInherited.Read(simplicial)
			previous, next := a.TermAs[Nat]("n - 1"), a.TermAs[Nat]("n + 1")

			h, byH := a.UnpackAs[A](a.Unfolded(homotopic, SimplicialHomotopicDef), "h")
			hParts := a.Conjuncts(
				byH,
				"h is an (n+1)-simplex",
				"whose faces below n are the base simplex",
				"whose face n is x",
				"and whose face n + 1 is y")
			hIn, hBelow, hAtN, hAtNext := hParts[0], hParts[1], hParts[2], hParts[3]

			ends := a.Have(
				"x and y, the faces n and n + 1 of h, are n-simplices",
				"x ∈ X.simplices(n) ∧ y ∈ X.simplices(n)",
				ByArith(faceIn.At(n, n, h), faceIn.At(n, next, h), hIn, hAtN, hAtNext))
			sameFaces := a.Have(
				"and for positive n they have the same faces",
				"∀i:num. i ≤ n ∧ 0 < n ⇒ X.d(n, i, x) = X.d(n, i, y)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					position := b.Assume()
					shift := b.Have(
						"n is positive, so it is (n − 1) + 1",
						"n - 1 + 1 = n ∧ n - 1 + 2 = n + 1",
						ByArith(position))

					b.Cases(b.Term("i < n"))
					b.When(
						"below n both faces are the base simplex, the face i of h being one",
						func(c *Argument, below Fact) {
							c.Show(
								"so the face i of x and the face i of y agree",
								CalcEq(
									Leg(
										c.TermAs[A]("base_simplex(x₀, n - 1)"),
										"x is the face n of h, so its face i is the base simplex at n − 1",
										ByArith(baseInherited.At(x0, previous, i, n, h), vertex, hIn, hBelow.At(i), hAtN, shift, below)),
									FinalLeg(
										"and so is the face i of y, the face n + 1 of h",
										ByArith(
											baseInherited.At(x0, previous, i, next, h),
											vertex,
											hIn,
											hBelow.At(i),
											hAtNext,
											shift,
											below)),
								))
						})
					b.Otherwise(
						"the face n is shared, by the simplicial identity d_n d_{n+1} = d_n d_n on h",
						func(c *Argument, notBelow Fact) {
							top := c.Have(
								"i, at most n and not below it, is n",
								"i = n",
								ByArith(notBelow, position))
							c.Show(
								"so x and y, the faces n and n + 1 of h, share their face n",
								ByArith(
									simplicial_set.FaceFace.Read(simplicial).At(previous, n, next, h),
									hIn,
									hAtN,
									hAtNext,
									shift,
									top))
						})
				}))
			a.Show(
				"a sphere is an n-simplex whose faces are the base "+
					"simplex, so either end is one exactly when the other is",
				// Simp, not Unfold: Unfold's tidy would split the resident ends, which the close names whole.
				Simp(Fwd(SimplicialSphereDef)),
				BySets(ends, sameFaces))
		}),
	Reading: "The two ends of a homotopy need not be spheres: their common n-th face " +
		"is free. Only the transfer holds, and it is what the classes of spheres need.",
})}

// SphereDegeneracyFaces — the face table of a degeneracy s(n, k, x) of a
// sphere: it is an (n+1)-simplex whose faces k and k + 1 are x and whose
// every other face is the base simplex. It lies in X(n + 1) by
// DegeneracyIn, and its faces k and k + 1 are x by the two simplicial
// identities d_k s_k = d_{k+1} s_k = id. Below k the face i is the
// degeneracy s(n − 1, k − 1, ·) of the face i of x, above k + 1 the
// degeneracy s(n − 1, k, ·) of its face i − 1; every face of x is the
// base simplex one dimension down, and a degeneracy of the base simplex
// is the base simplex.
var SphereDegeneracyFaces = sphereDegeneracyFacesThm{family.Add(registry.ProofEntry{
	Name: "SphereDegeneracyFaces",
	Key:  "prop_628346d77f33ccd1",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x:A. ∀k:num.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"x ∈ simplicial_sphere(x₀, n)",
			"k ≤ n",
		},
		Conclusion: "X.s(n, k, x) ∈ X.simplices(n + 1) ∧ " +
			"X.d(n + 1, k, X.s(n, k, x)) = x ∧ " +
			"X.d(n + 1, k + 1, X.s(n, k, x)) = x ∧ " +
			"(∀i:num. i ≤ n + 1 ∧ ¬(i = k) ∧ ¬(i = k + 1) ⇒ X.d(n + 1, i, X.s(n, k, x)) = base_simplex(x₀, n))",
	},
		func(
			a *Argument,
			simplicial Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			x *Expr[A],
			k *Expr[Nat],
			vertex, xSphere, bound Fact,
		) {
			previous := a.TermAs[Nat]("n - 1")
			xUnfolded := a.Unfolded(xSphere, SimplicialSphereDef)
			xIn := a.Have(
				"x is an n-simplex",
				"x ∈ X.simplices(n)",
				BySets(xUnfolded))
			degenerateIn := a.Have(
				"so its degeneracy s(n, k, x) is an (n+1)-simplex",
				"X.s(n, k, x) ∈ X.simplices(n + 1)",
				By(simplicial_set.DegeneracyIn.Read(simplicial).At(n, k, x), xIn, bound))
			atK := a.Have(
				"whose face k is x",
				"X.d(n + 1, k, X.s(n, k, x)) = x",
				By(simplicial_set.FaceDegeneracyEqual.Read(simplicial).At(n, k, x), xIn, bound))
			atKNext := a.Have(
				"as is its face k + 1",
				"X.d(n + 1, k + 1, X.s(n, k, x)) = x",
				By(simplicial_set.FaceDegeneracyNext.Read(simplicial).At(n, k, x), xIn, bound))
			away := a.Have(
				"and whose every other face is the base simplex",
				"∀i:num. i ≤ n + 1 ∧ ¬(i = k) ∧ ¬(i = k + 1) ⇒ X.d(n + 1, i, X.s(n, k, x)) = base_simplex(x₀, n)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					position := b.Assume()
					shift := b.Have(
						"a face other than k and k + 1 exists only for positive n, so n is (n − 1) + 1",
						"0 < n ∧ n - 1 + 1 = n ∧ n - 1 + 2 = n + 1",
						ByArith(bound, position))
					xFaces := b.Have(
						"every face of x is the base simplex one dimension down",
						"∀j:num. j ≤ n ⇒ X.d(n, j, x) = base_simplex(x₀, n - 1)",
						BySets(xUnfolded, shift))

					b.Cases(b.Term("i < k"))
					b.When(
						"below k the face of the degeneracy is a degeneracy of the face i of x",
						func(c *Argument, below Fact) {
							bounds := c.Have(
								"i is a face of x, and k − 1 a degeneracy index one dimension down",
								"i ≤ n ∧ k ≤ n - 1 + 1 ∧ k - 1 ≤ n - 1",
								ByArith(below, bound, position, shift))
							c.Show(
								"so the face i of s(n, k, x) is the base simplex",
								CalcEq(
									Leg(
										c.TermAs[A]("X.s(n - 1, k - 1, X.d(n, i, x))"),
										"d_i s_k = s_{k−1} d_i, i being below k",
										By(
											simplicial_set.FaceDegeneracyBelow.Read(simplicial).At(previous, i, k, x),
											xIn,
											shift,
											below,
											bounds)),
									Leg(
										c.TermAs[A]("X.s(n - 1, k - 1, base_simplex(x₀, n - 1))"),
										"the face i of x is the base simplex",
										By(Normalized, xFaces.At(i), bounds)),
									FinalLeg(
										"and a degeneracy of the base simplex is the base simplex",
										By(
											simplicial_set.BaseSimplexDegeneracy.Read(simplicial).At(x0, previous, c.TermAs[Nat]("k - 1")),
											vertex,
											shift,
											bounds)),
								))
						})
					b.Otherwise(
						"above k + 1 the face of the degeneracy is a degeneracy of the face i − 1 of x",
						func(c *Argument, notBelow Fact) {
							bounds := c.Have(
								"i lies above k + 1, i − 1 is a face of x, and k a degeneracy index one dimension down",
								"k + 1 < i ∧ i ≤ n - 1 + 2 ∧ i - 1 ≤ n ∧ k ≤ n - 1",
								ByArith(notBelow, bound, position, shift))
							c.Show(
								"so the face i of s(n, k, x) is the base simplex",
								CalcEq(
									Leg(
										c.TermAs[A]("X.s(n - 1, k, X.d(n, i - 1, x))"),
										"d_i s_k = s_k d_{i−1}, i being above k + 1",
										By(simplicial_set.FaceDegeneracyAbove.Read(simplicial).At(previous, i, k, x), xIn, shift, bounds)),
									Leg(
										c.TermAs[A]("X.s(n - 1, k, base_simplex(x₀, n - 1))"),
										"the face i − 1 of x is the base simplex",
										By(Normalized, xFaces.At(c.TermAs[Nat]("i - 1")), bounds)),
									FinalLeg(
										"and a degeneracy of the base simplex is the base simplex",
										By(
											simplicial_set.BaseSimplexDegeneracy.Read(simplicial).At(x0, previous, k),
											vertex,
											shift,
											bounds)),
								))
						})
				}))
			a.Show(
				"so the whole face table of s(n, k, x) holds",
				By(degenerateIn, atK, atKNext, away))
		}),
})}

// SphereHornCompatible — a horn of n-spheres is a horn: its members are
// n-simplices, and for 0 < n every face of every member is the base
// simplex one dimension down, so any two faces the horn condition
// compares agree; at n = 0 the condition compares nothing.
var SphereHornCompatible = sphereHornCompatibleThm{family.Add(registry.ProofEntry{
	Name: "SphereHornCompatible",
	Key:  "prop_396b61efbc5f0e03",
	Build: family.Theorem(Statement{
		Binders: "∀X:simplicial_ops(A). ∀x₀:A. ∀n k:num. ∀y:(num → A).",
		Hypotheses: []string{
			"k ≤ n + 1",
			"∀i:num. i ≤ n + 1 ∧ ¬(i = k) ⇒ y(i) ∈ simplicial_sphere(X, x₀, n)",
		},
		Conclusion: "face_family(X, n, horn_faces(n, k), y)",
	},
		func(
			a *Argument,
			X *Expr[simplicial_set.SimplicialOps[A]],
			x0 *Expr[A],
			n *Expr[Nat],
			k *Expr[Nat],
			y *Expr[Fun[Nat, A]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the missing face k is a face of an (n+1)-simplex",
				"and every other member of y is a sphere")
			missing, spheres := parts[0], parts[1]
			hornFace := kan_complex.HornFacesMember
			members := a.Have(
				"every member of y on the faces of the horn is an n-simplex",
				"∀i:num. i ∈ horn_faces(n, k) ⇒ y(i) ∈ X.simplices(n)",
				Unfold(kan_complex.HornFacesDef),
				BySets(a.Unfolded(spheres, SimplicialSphereDef)))
			compatible := a.Have(
				"and y is compatible there: the faces the condition compares are faces of spheres",
				"faces_compatible(n, horn_faces(n, k), y)",
				Simp(Fwd(simplicial_set.FacesCompatibleDef)),
				Derive(func(b *Argument) {
					i, j := b.FixAs[Nat](), b.FixAs[Nat]()
					pair := b.Assume()
					faces := b.Have(
						"i < j are faces of the horn: both at most n + 1, and neither is k",
						"i < j ∧ i ≤ n + 1 ∧ ¬(i = k) ∧ j ≤ n + 1 ∧ ¬(j = k)",
						By(hornFace.At(n, k, i), hornFace.At(n, k, j), pair))
					positive := b.Assuming(
						b.Term("0 < n"),
						"at n = 0 the only pair is (0, 1), and k, at most 1, is one of its indices",
						Given(func(c *Argument, zero Fact) {
							c.Show(
								"so no pair is compared",
								ByArith(zero, faces, missing))
						}))
					indices := b.Have(
						"i and j − 1 index faces of the n-simplices y(j) and y(i)",
						"i ≤ n ∧ j - 1 ≤ n",
						ByArith(faces))
					jSphere := b.Have(
						"y(j) is a sphere",
						"y(j) ∈ simplicial_sphere(X, x₀, n)",
						By(spheres.At(j), faces))
					iSphere := b.Have(
						"and so is y(i)",
						"y(i) ∈ simplicial_sphere(X, x₀, n)",
						By(spheres.At(i), faces))
					b.Show(
						"so the face i of y(j) and the face j − 1 of y(i) are both the base simplex at n − 1",
						CalcEq(
							Leg(
								b.TermAs[A]("base_simplex(x₀, n - 1)"),
								"the face i of the sphere y(j) is the base simplex",
								BySets(b.Unfolded(jSphere, SimplicialSphereDef), indices, positive)),
							FinalLeg(
								"and so is the face j − 1 of the sphere y(i)",
								BySets(b.Unfolded(iSphere, SimplicialSphereDef), indices, positive)),
						))
				}))
			a.Show(
				"so y is a face family of X on the faces of the horn",
				Unfold(simplicial_set.FaceFamilyDef),
				By(members, compatible))
		}),
})}

// SphereHornFill — in a Kan complex a horn of n-spheres has a filler:
// it is a horn (SphereHornCompatible), and KanFill fills it.
var SphereHornFill = sphereHornFillThm{family.Add(registry.ProofEntry{
	Name: "SphereHornFill",
	Key:  "prop_a7b51589f1e38be3",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n k:num. ∀y:(num → A).",
		Hypotheses: []string{
			"k ≤ n + 1",
			"∀i:num. i ≤ n + 1 ∧ ¬(i = k) ⇒ y(i) ∈ simplicial_sphere(x₀, n)",
		},
		Conclusion: "∃x:A. x ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, k), y, x)",
	},
		func(a *Argument, kan Fact, x0 *Expr[A], n, k *Expr[Nat], y *Expr[Fun[Nat, A]], given Fact) {
			X := a.TermAs[simplicial_set.SimplicialOps[A]]("X")
			horn := a.Have(
				"y is a horn: its members are n-simplices, compatible on the faces of the horn",
				"face_family(n, horn_faces(n, k), y)",
				By(At(SphereHornCompatible, X, x0, n, k, y), given))
			a.Show(
				"so KanFill fills the horn",
				By(kan_complex.KanFill.Read(kan).At(n, k, y), given, horn))
		}),
})}

// HomotopicRefl — a sphere is homotopic to itself, by its n-th
// degeneracy; no filling is needed.
var HomotopicRefl = homotopicReflThm{family.Add(registry.ProofEntry{
	Name: "HomotopicRefl",
	Key:  "prop_805b65000d24c6e7",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"x ∈ simplicial_sphere(x₀, n)",
		},
		Conclusion: "simplicial_homotopic(x₀, n, x, x)",
	},
		func(a *Argument, simplicial Fact, x0 *Expr[A], n *Expr[Nat], x *Expr[A], vertex, xSphere Fact) {
			a.Do(Simp(Fwd(SimplicialHomotopicDef)))
			a.Take(a.TermAs[A]("X.s(n, n, x)"))
			a.Show(
				"s(n, n, x) is an (n+1)-simplex with x for its faces n and n + 1 and "+
					"the base simplex for every other face, each face below n among them",
				ByArith(SphereDegeneracyFaces.Read(simplicial).At(x0, n, x, n), vertex, xSphere))
		}),
})}

// HomotopicSym — in a Kan complex the homotopy relation is symmetric.
// With h a homotopy from x to y, the horn of dimension n + 2 missing the
// last face, with the base simplex below n, h at n and the degeneracy
// s(n, n, x) at n + 1, is compatible: below n every face is the base
// simplex, and at the pair (n, n + 1) both faces are x. The last face of
// a filler has y as its n-th face, x as its (n+1)-th and the base simplex
// below n, so it is a homotopy from y to x. SphereDegeneracyFaces does
// not apply to s(n, n, x): x need not be a sphere, its n-th face being
// free, so the faces of the degeneracy below n are read off h.
var HomotopicSym = homotopicSymThm{family.Add(registry.ProofEntry{
	Name: "HomotopicSym",
	Key:  "prop_d56a63cae73ca20f",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x y:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"simplicial_homotopic(x₀, n, x, y)",
		},
		Conclusion: "simplicial_homotopic(x₀, n, y, x)",
	},
		func(a *Argument, kan Fact, x0 *Expr[A], n *Expr[Nat], x, _ *Expr[A], vertex, homotopic Fact) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			face := simplicial_set.FaceFace.Read(simplicial)
			baseFace := simplicial_set.BaseSimplexFace.Read(simplicial)
			baseInherited := simplicial_set.BaseSimplexFaceInherited.Read(simplicial)
			previous, next, top := a.TermAs[Nat]("n - 1"), a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 2")

			h, byH := a.UnpackAs[A](a.Unfolded(homotopic, SimplicialHomotopicDef), "h")
			hParts := a.Conjuncts(
				byH,
				"h is an (n+1)-simplex",
				"whose faces below n are the base simplex",
				"whose face n is x",
				"and whose face n + 1 is y")
			hIn, hBelow, hAtN, hAtNext := hParts[0], hParts[1], hParts[2], hParts[3]

			xIn := a.Have(
				"x, a face of h, is an n-simplex",
				"x ∈ X.simplices(n)",
				ByArith(simplicial_set.FaceIn.Read(simplicial).At(n, n, h), hIn, hAtN))
			degenerateIn := a.Have(
				"so its degeneracy s(n, n, x) is an (n+1)-simplex",
				"X.s(n, n, x) ∈ X.simplices(n + 1)",
				ByArith(simplicial_set.DegeneracyIn.Read(simplicial).At(n, n, x), xIn))
			degenerateBelow := a.Have(
				"the faces of the degeneracy s(n, n, x) below n are the base simplex",
				"∀i:num. i < n ⇒ X.d(n + 1, i, X.s(n, n, x)) = base_simplex(x₀, n)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					below := b.Assume()
					shift := b.Have(
						"n, being above i, is (n − 1) + 1",
						"n - 1 + 1 = n ∧ n - 1 + 2 = n + 1",
						ByArith(below))
					b.Show(
						"the face i of s(n, n, x) is the base simplex",
						CalcEq(
							Leg(
								b.TermAs[A]("X.s(n - 1, n - 1, X.d(n, i, x))"),
								"d_i s_n = s_{n−1} d_i, as i < n",
								ByArith(
									simplicial_set.FaceDegeneracyBelow.Read(simplicial).At(previous, i, n, x),
									xIn,
									shift,
									below)),
							Leg(
								b.TermAs[A]("X.s(n - 1, n - 1, base_simplex(x₀, n - 1))"),
								"x is the face n of h, whose face i is the base "+
									"simplex, so the face i of x is the base simplex at n − 1",
								ByArith(baseInherited.At(x0, previous, i, n, h), vertex, hIn, hBelow.At(i), hAtN, shift, below)),
							FinalLeg(
								"and a degeneracy of the base simplex is the base simplex",
								ByArith(
									simplicial_set.BaseSimplexDegeneracy.Read(simplicial).At(x0, previous, previous),
									shift,
									vertex)),
						))
				}))

			f, fDef := a.LetAs[Fun[Nat, A]](
				"f", "λi:num. COND(i = n, h, COND(i = n + 1, X.s(n, n, x), base_simplex(x₀, n + 1)))")
			values := a.Have(
				"f is h at n and s(n, n, x) at n + 1",
				"f(n) = h ∧ f(n + 1) = X.s(n, n, x)",
				fDef.Rw(),
				ByArith())
			baseValues := a.Have(
				"and the base simplex below n",
				"∀i:num. i < n ⇒ f(i) = base_simplex(x₀, n + 1)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
			members := a.Have(
				"every member of f is an (n+1)-simplex: h, the degeneracy or the base simplex",
				"∀i:num. f(i) ∈ X.simplices(n + 1)",
				fDef.Rw(),
				By(hIn, degenerateIn, simplicial_set.BaseSimplexIn.Read(simplicial).At(x0, next), vertex))
			membersBelow := a.Have(
				"and every member of f has the base simplex for its faces below n",
				"∀j i:num. i < n ⇒ X.d(n + 1, i, f(j)) = base_simplex(x₀, n)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					i := b.FixAs[Nat]()
					below := b.Assume()
					b.Show(
						"f(j) is h, s(n, n, x) or the base simplex at n + 1, and the face i of each is the base simplex",
						fDef.Rw(),
						CondRewrite(),
						ByArith(hBelow.At(i), degenerateBelow.At(i), baseFace.At(x0, n, i), below, vertex))
				}))
			hornFace := kan_complex.HornFacesMember
			compatible := a.Have(
				"so f is compatible on the faces of the horn missing the face n + 2",
				"faces_compatible(n + 1, horn_faces(n + 1, n + 2), f)",
				Simp(Fwd(simplicial_set.FacesCompatibleDef)),
				Derive(func(b *Argument) {
					i, j := b.FixAs[Nat](), b.FixAs[Nat]()
					faces := b.Assume()
					pair := b.Have(
						"i < j are faces of the horn, so j is at most n + 1",
						"i < j ∧ j ≤ n + 1",
						ByArith(hornFace.At(next, top, j), faces))
					jPrevious := b.TermAs[Nat]("j - 1")
					notBelow := b.Unless(
						b.Term("i < n"),
						"below n the member f(i) is the base simplex, and both faces are the base simplex at n",
						Given(func(c *Argument, below Fact) {
							c.Show(
								"the face i of f(j) and the face j − 1 of the base simplex f(i) are the base simplex at n",
								ByArith(
									membersBelow.At(j, i),
									baseValues.At(i),
									baseFace.At(x0, n, jPrevious),
									below,
									pair,
									vertex))
						}))
					at := b.Have(
						"i < j ≤ n + 1 with i not below n leave the pair (n, n + 1)",
						"i = n ∧ j = n + 1 ∧ j - 1 = n",
						ByArith(notBelow, pair))
					b.Show(
						"where the face n of f(n + 1) and the face n of f(n) are both x",
						CalcEq(
							Leg(
								x,
								"the face n of the degeneracy s(n, n, x) is x",
								ByArith(simplicial_set.FaceDegeneracyEqual.Read(simplicial).At(n, n, x), at, values, xIn)),
							Leg(
								b.TermAs[A]("X.d(n + 1, n, h)"),
								"x is the face n of h",
								By(hAtN)),
							FinalLeg(
								"and h is f(n), at n = i = j − 1",
								ByArith(at, values)),
						))
				}))
			horn := a.Have(
				"so f is a horn of X missing the face n + 2",
				"face_family(n + 1, horn_faces(n + 1, n + 2), f)",
				Unfold(simplicial_set.FaceFamilyDef),
				By(members, compatible))
			dimension := a.Have(
				"the horn has dimension (n + 1) + 1 = n + 2, and the missing face n + 2 is one of its faces",
				"n + 1 + 1 = n + 2 ∧ n + 2 ≤ n + 1 + 1",
				ByArith())

			v, filled := a.ObtainAs[A](
				"so the horn f has a filler v, an (n+2)-simplex of X",
				"∃v:A. v ∈ X.simplices(n + 2) ∧ faces_filler(n + 1, horn_faces(n + 1, n + 2), f, v)",
				By(kan_complex.KanFill.Read(kan).At(next, top, f), dimension, horn))
			filling := a.Conjuncts(
				filled,
				"v is an (n+2)-simplex",
				"whose faces other than the last are the members of f")
			vIn, faceOf := filling[0], a.Unfolded(filling[1], simplicial_set.FacesFillerDef)

			homotopy := a.TermAs[A]("X.d(n + 2, n + 2, v)")
			homotopyIn := a.Have(
				"the last face of v is an (n+1)-simplex",
				"X.d(n + 2, n + 2, v) ∈ X.simplices(n + 1)",
				By(simplicial_set.FaceIn.Read(simplicial).At(next, top, v), vIn, dimension))
			vBelow := a.Have(
				"the faces of v below n are the members of f there, the base simplex",
				"∀i:num. i < n ⇒ X.d(n + 2, i, v) = base_simplex(x₀, n + 1)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(faceOf.At(i), hornFace.At(next, top, i), baseValues.At(i), dimension)
				}))
			homotopyBelow := a.Have(
				"so the faces of its last face below n are the base simplex",
				"∀i:num. i < n ⇒ X.d(n + 1, i, X.d(n + 2, n + 2, v)) = base_simplex(x₀, n)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(baseInherited.At(x0, n, i, top, v), vertex, vIn, vBelow.At(i))
				}))
			homotopyAtN := a.Have(
				"its face n is the last face of h, which is y",
				"X.d(n + 1, n, X.d(n + 2, n + 2, v)) = y",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, X.d(n + 2, n, v))"),
						"the face identity of v at the pair (n, n + 2)",
						ByArith(face.At(n, n, top, v), vIn, dimension)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, h)"),
						"the face n of v is f(n), which is h",
						ByArith(faceOf.At(n), hornFace.At(next, top, n), values, dimension)),
					FinalLeg(
						"and the last face of h is y",
						By(hAtNext)),
				))
			homotopyAtNext := a.Have(
				"its face n + 1 is the last face of s(n, n, x), which is x",
				"X.d(n + 1, n + 1, X.d(n + 2, n + 2, v)) = x",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, X.d(n + 2, n + 1, v))"),
						"the face identity of v at the pair (n + 1, n + 2)",
						ByArith(face.At(n, next, top, v), vIn, dimension)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, X.s(n, n, x))"),
						"the face n + 1 of v is f(n + 1), which is s(n, n, x)",
						ByArith(faceOf.At(next), hornFace.At(next, top, next), values, dimension)),
					FinalLeg(
						"and the last face of s(n, n, x) is x",
						ByArith(simplicial_set.FaceDegeneracyNext.Read(simplicial).At(n, n, x), xIn)),
				))
			a.Do(Simp(Fwd(SimplicialHomotopicDef)))
			a.Take(homotopy)
			a.Show(
				"so the last face of v is a homotopy from y to x",
				By(homotopyIn, homotopyBelow, homotopyAtN, homotopyAtNext))
		}),
})}

// HomotopicTrans — and transitive: with h a homotopy from x to y and h'
// one from y to z, the horn of dimension n + 2 missing the face n + 1,
// with h at n, h' at n + 2 and the base simplex elsewhere, fills; the two
// homotopies meet along y, and the face identities carry the filler's
// faces n and n + 2 to the faces n and n + 1 of its face n + 1, which is
// a homotopy from x to z.
var HomotopicTrans = homotopicTransThm{family.Add(registry.ProofEntry{
	Name: "HomotopicTrans",
	Key:  "prop_7b3924c803ead8ef",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x y z:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"simplicial_homotopic(x₀, n, x, y) ∧ simplicial_homotopic(x₀, n, y, z)",
		},
		Conclusion: "simplicial_homotopic(x₀, n, x, z)",
	},
		func(a *Argument, kan Fact, x0 *Expr[A], n *Expr[Nat], _, y, _ *Expr[A], vertex, homotopies Fact) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			face := simplicial_set.FaceFace.Read(simplicial)
			baseFace := simplicial_set.BaseSimplexFace.Read(simplicial)
			baseInherited := simplicial_set.BaseSimplexFaceInherited.Read(simplicial)
			next, top := a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 2")

			both := a.Conjuncts(
				homotopies,
				"x is homotopic to y",
				"and y to z")
			_, byH := a.UnpackAs[A](a.Unfolded(both[0], SimplicialHomotopicDef), "h")
			hParts := a.Conjuncts(
				byH,
				"h is an (n+1)-simplex",
				"whose faces below n are the base simplex",
				"whose face n is x",
				"and whose face n + 1 is y")
			hIn, hBelow, hAtN, hAtNext := hParts[0], hParts[1], hParts[2], hParts[3]
			_, byHPrime := a.UnpackAs[A](a.Unfolded(both[1], SimplicialHomotopicDef), "h'")
			hPrimeParts := a.Conjuncts(
				byHPrime,
				"h' is an (n+1)-simplex",
				"whose faces below n are the base simplex",
				"whose face n is y",
				"and whose face n + 1 is z")
			hPrimeIn, hPrimeBelow, hPrimeAtN, hPrimeAtNext :=
				hPrimeParts[0], hPrimeParts[1], hPrimeParts[2], hPrimeParts[3]

			f, fDef := a.LetAs[Fun[Nat, A]](
				"f", "λi:num. COND(i = n, h, COND(i = n + 2, h', base_simplex(x₀, n + 1)))")
			values := a.Have(
				"f is h at n and h' at n + 2",
				"f(n) = h ∧ f(n + 2) = h'",
				fDef.Rw(),
				ByArith())
			baseValues := a.Have(
				"and the base simplex below n",
				"∀i:num. i < n ⇒ f(i) = base_simplex(x₀, n + 1)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
			members := a.Have(
				"every member of f is an (n+1)-simplex: h, h' or the base simplex",
				"∀i:num. f(i) ∈ X.simplices(n + 1)",
				fDef.Rw(),
				By(hIn, hPrimeIn, simplicial_set.BaseSimplexIn.Read(simplicial).At(x0, next), vertex))
			hornFace := kan_complex.HornFacesMember
			compatible := a.Have(
				"and f is compatible on the faces of the horn missing the face n + 1",
				"faces_compatible(n + 1, horn_faces(n + 1, n + 1), f)",
				fDef.Rw(),
				Simp(Fwd(simplicial_set.FacesCompatibleDef)),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					j := b.FixAs[Nat]()
					faces := b.Assume()
					pair := b.Have(
						"i < j are faces of the horn: j is at most n + 2, and neither is n + 1",
						"i < j ∧ j ≤ n + 1 + 1 ∧ ¬(i = n + 1) ∧ ¬(j = n + 1)",
						By(hornFace.At(next, next, i), hornFace.At(next, next, j), faces))
					jPrevious := b.TermAs[Nat]("j - 1")
					b.Cases(b.Term("i = n"))
					b.When(
						"at the pair (n, n + 2) the face n of h' and the face n + 1 of h are both y",
						func(c *Argument, atN Fact) {
							positions := c.Have(
								"j is then n + 2, not n, and j − 1 is n + 1",
								"j = n + 2 ∧ j - 1 = n + 1 ∧ ¬(j = n)",
								ByArith(pair, atN))
							c.Show(
								"so the face i of the member at j is the face j − 1 of the member at i",
								CalcEq(
									Leg(
										c.TermAs[A]("X.d(n + 1, n, h')"),
										"the member at j = n + 2 is h', read at its face i = n",
										By(Normalized, atN, positions)),
									Leg(
										y,
										"h' starts at y",
										By(hPrimeAtN)),
									Leg(
										c.TermAs[A]("X.d(n + 1, n + 1, h)"),
										"where h ends",
										By(hAtNext)),
									FinalLeg(
										"which is the face j − 1 = n + 1 of the member h at i = n",
										By(Normalized, atN, positions)),
								))
						})
					b.Otherwise(
						"below n both faces are the base simplex one dimension down",
						func(c *Argument, notN Fact) {
							positions := c.Have(
								"i is then below n, so neither n nor n + 2, and j − 1 indexes a face of an (n+1)-simplex",
								"i < n ∧ i ≤ n + 1 ∧ ¬(i = n + 2) ∧ j - 1 ≤ n + 1",
								ByArith(pair, notN))
							c.Show(
								"so the face i of the member at j and the face j − 1 of the member at i agree",
								CalcEq(
									Leg(
										c.TermAs[A]("base_simplex(x₀, n)"),
										"every member, h, h' or the base simplex, has the base simplex as its face i below n",
										By(hBelow.At(i), hPrimeBelow.At(i), baseFace.At(x0, n, i), vertex, positions)),
									FinalLeg(
										"and the member at i is the base simplex, whose face j − 1 is the base simplex too",
										By(notN, positions, baseFace.At(x0, n, jPrevious), vertex)),
								))
						})
				}))
			horn := a.Have(
				"so f is a horn of X missing the face n + 1",
				"face_family(n + 1, horn_faces(n + 1, n + 1), f)",
				Unfold(simplicial_set.FaceFamilyDef),
				By(members, compatible))
			dimension := a.Have(
				"the horn has dimension (n + 1) + 1 = n + 2, and the missing face n + 1 is one of its faces",
				"n + 1 + 1 = n + 2 ∧ n + 1 ≤ n + 1 + 1",
				ByArith())

			v, filled := a.ObtainAs[A](
				"so the horn f has a filler v, an (n+2)-simplex of X",
				"∃v:A. v ∈ X.simplices(n + 2) ∧ faces_filler(n + 1, horn_faces(n + 1, n + 1), f, v)",
				By(kan_complex.KanFill.Read(kan).At(next, next, f), horn, dimension))
			filling := a.Conjuncts(
				filled,
				"v is an (n+2)-simplex",
				"whose faces other than n + 1 are the members of f")
			vIn, faceOf := filling[0], a.Unfolded(filling[1], simplicial_set.FacesFillerDef)
			vAtN := a.Have(
				"v has h as its face n",
				"X.d(n + 2, n, v) = h",
				ByArith(faceOf.At(n), hornFace.At(next, next, n), values, dimension))
			vAtTop := a.Have(
				"and h' as its face n + 2",
				"X.d(n + 2, n + 2, v) = h'",
				ByArith(faceOf.At(top), hornFace.At(next, next, top), values, dimension))
			vBelow := a.Have(
				"and the base simplex as its faces below n",
				"∀i:num. i < n ⇒ X.d(n + 2, i, v) = base_simplex(x₀, n + 1)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(faceOf.At(i), hornFace.At(next, next, i), baseValues.At(i), dimension)
				}))

			homotopy := a.TermAs[A]("X.d(n + 2, n + 1, v)")
			homotopyIn := a.Have(
				"the face n + 1 of v is an (n+1)-simplex",
				"X.d(n + 2, n + 1, v) ∈ X.simplices(n + 1)",
				ByArith(simplicial_set.FaceIn.Read(simplicial).At(next, next, v), vIn, dimension))
			homotopyBelow := a.Have(
				"whose faces below n are the base simplex, as those of v are",
				"∀i:num. i < n ⇒ X.d(n + 1, i, X.d(n + 2, n + 1, v)) = base_simplex(x₀, n)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(baseInherited.At(x0, n, i, next, v), vertex, vIn, vBelow.At(i))
				}))
			homotopyAtN := a.Have(
				"its face n is x",
				"X.d(n + 1, n, X.d(n + 2, n + 1, v)) = x",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.d(n + 2, n, v))"),
						"the face identity at the pair (n, n + 1)",
						ByArith(face.At(n, n, next, v), vIn)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n, h)"),
						"the face n of v is h",
						By(Normalized, vAtN)),
					FinalLeg(
						"which starts at x",
						By(hAtN)),
				))
			homotopyAtNext := a.Have(
				"and its face n + 1 is z",
				"X.d(n + 1, n + 1, X.d(n + 2, n + 1, v)) = z",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, X.d(n + 2, n + 2, v))"),
						"the face identity at the pair (n + 1, n + 2)",
						ByArith(face.At(n, next, top, v), vIn)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, h')"),
						"the face n + 2 of v is h'",
						By(Normalized, vAtTop)),
					FinalLeg(
						"which ends at z",
						By(hPrimeAtNext)),
				))
			a.Do(Simp(Fwd(SimplicialHomotopicDef)))
			a.Take(homotopy)
			a.Show(
				"so the face n + 1 of v is a homotopy from x to z",
				By(homotopyIn, homotopyBelow, homotopyAtN, homotopyAtNext))
		}),
})}

// HomotopicEquivalenceOn — in a Kan complex homotopy is an equivalence
// on the n-spheres: reflexive there (HomotopicRefl), symmetric and
// transitive on any simplices (HomotopicSym, HomotopicTrans). πₙ is its
// quotient.
var HomotopicEquivalenceOn = homotopicEquivalenceOnThm{family.Add(registry.ProofEntry{
	Name: "HomotopicEquivalenceOn",
	Key:  "prop_5401ebb6b0cb1ebd",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders:    "∀x₀:A. ∀n:num.",
		Hypotheses: []string{"x₀ ∈ X.simplices(0)"},
		Conclusion: "equivalence_on(simplicial_sphere(x₀, n), simplicial_homotopic(x₀, n))",
	},
		func(a *Argument, kan Fact, x0 *Expr[A], n *Expr[Nat], vertex Fact) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			a.Do(Unfold(equivalence.EquivalenceOn), SplitConjAll(
				Case(
					"reflexive on the spheres: a sphere is homotopic to itself",
					By(HomotopicRefl.Read(simplicial).AsFact().At(x0, n), vertex)),
				Case(
					"symmetric, as on any two simplices",
					By(HomotopicSym.Read(kan).AsFact().At(x0, n), vertex)),
				Case(
					"and transitive, as on any three",
					By(HomotopicTrans.Read(kan).AsFact().At(x0, n), vertex)),
			))
		}),
})}

// InHomotopyGroup — a member of πₙ is the class of a sphere. A simplex
// homotopic to a sphere is a sphere (HomotopicSphere), so the spheres
// are closed under homotopy, and the quotient of a set closed under a
// relation is its image under the class map
// (equivalence.QuotientOnClosed).
var InHomotopyGroup = inHomotopyGroupThm{family.Add(registry.ProofEntry{
	Name: "InHomotopyGroup",
	Key:  "prop_71de7f4fd2def00f",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀C:set(A).",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
		},
		Conclusion: "C ∈ simplicial_homotopy_group(x₀, n) ⇔ " +
			"∃x:A. x ∈ simplicial_sphere(x₀, n) ∧ C = equivalence_class(simplicial_homotopic(x₀, n), x)",
	},
		func(a *Argument, simplicial Fact, x0 *Expr[A], n *Expr[Nat], _ *Expr[Set[A]], vertex Fact) {
			closed := a.Have(
				"a simplex homotopic to a sphere is a sphere",
				Statement{
					Binders: "∀x y:A.",
					Hypotheses: []string{
						"x ∈ simplicial_sphere(x₀, n)",
						"simplicial_homotopic(x₀, n, x, y)",
					},
					Conclusion: "y ∈ simplicial_sphere(x₀, n)",
				},
				By(HomotopicSphere.Read(simplicial).AsFact().At(x0, n), vertex))
			asImage := a.Have(
				"so πₙ, the quotient of the spheres, is their image under the class map",
				"simplicial_homotopy_group(x₀, n) = "+
					"image(equivalence_class(simplicial_homotopic(x₀, n)), simplicial_sphere(x₀, n))",
				Unfold(SimplicialHomotopyGroupDef),
				By(closed, equivalence.QuotientOnClosed))
			a.Show(
				"and a member of that image is the class of some sphere",
				asImage.Rw(),
				BySets())
		}),
})}

// ClassInHomotopyGroup — the class of a sphere is a member of πₙ. The
// spheres are closed under homotopy (HomotopicSphere), and the class of
// a point of a set closed under a relation is a member of its quotient
// (equivalence.ClassInQuotientOnClosed).
var ClassInHomotopyGroup = classInHomotopyGroupThm{family.Add(registry.ProofEntry{
	Name: "ClassInHomotopyGroup",
	Key:  "prop_13780e6a5727f2e2",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"x ∈ simplicial_sphere(x₀, n)",
		},
		Conclusion: "equivalence_class(simplicial_homotopic(x₀, n), x) ∈ simplicial_homotopy_group(x₀, n)",
	},
		func(a *Argument, simplicial Fact, x0 *Expr[A], n *Expr[Nat], x *Expr[A], vertex, sphere Fact) {
			spheres := a.TermAs[Set[A]]("simplicial_sphere(x₀, n)")
			homotopic := a.TermAs[Fun2[A, A, Bool]]("simplicial_homotopic(x₀, n)")
			closed := a.Have(
				"a simplex homotopic to a sphere is a sphere",
				Statement{
					Binders: "∀u v:A.",
					Hypotheses: []string{
						"u ∈ simplicial_sphere(x₀, n)",
						"simplicial_homotopic(x₀, n, u, v)",
					},
					Conclusion: "v ∈ simplicial_sphere(x₀, n)",
				},
				By(HomotopicSphere.Read(simplicial).AsFact().At(x0, n), vertex))
			a.Show(
				"so the class of the sphere x is a member of πₙ, the quotient of the spheres",
				Unfold(SimplicialHomotopyGroupDef),
				By(closed, sphere, equivalence.ClassInQuotientOnClosed.At(spheres, homotopic, x)))
		}),
})}

// ClassEqIff — two spheres have the same class exactly when they are
// homotopic. Homotopy is an equivalence on the spheres
// (HomotopicEquivalenceOn), and a simplex homotopic to a sphere is a
// sphere (HomotopicSphere): on a set closed under an equivalence two
// points have one class exactly when they are related
// (equivalence.ClassEqIffClosed).
var ClassEqIff = classEqIffThm{family.Add(registry.ProofEntry{
	Name: "ClassEqIff",
	Key:  "prop_a7fa146de6129833",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x y:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"x ∈ simplicial_sphere(x₀, n) ∧ y ∈ simplicial_sphere(x₀, n)",
		},
		Conclusion: "equivalence_class(simplicial_homotopic(x₀, n), x) = " +
			"equivalence_class(simplicial_homotopic(x₀, n), y) ⇔ " +
			"simplicial_homotopic(x₀, n, x, y)",
	},
		func(a *Argument, kan Fact, x0 *Expr[A], n *Expr[Nat], x, y *Expr[A], vertex, spheres Fact) {
			equiv := a.Have(
				"homotopy is an equivalence on the spheres",
				"equivalence_on(simplicial_sphere(x₀, n), simplicial_homotopic(x₀, n))",
				By(HomotopicEquivalenceOn, kan, vertex))
			closed := a.Have(
				"a simplex homotopic to a sphere is a sphere",
				Statement{
					Binders: "∀u v:A.",
					Hypotheses: []string{
						"u ∈ simplicial_sphere(x₀, n)",
						"simplicial_homotopic(x₀, n, u, v)",
					},
					Conclusion: "v ∈ simplicial_sphere(x₀, n)",
				},
				By(HomotopicSphere.Read(kan_complex.KanSimplicialSet.Read(kan)).AsFact().At(x0, n), vertex))
			a.Show(
				"the spheres being closed under homotopy, two of "+
					"them have one class exactly when they are homotopic",
				By(equivalence.ClassEqIffClosed.Read(equiv).AsFact().At(x, y), closed, spheres))
		}),
})}

// Representative — a class of πₙ has a chosen member, a sphere, whose
// class it is. The class C is the class of a sphere x
// (InHomotopyGroup), and x is homotopic to itself (HomotopicRefl), so
// to the point c chosen in C (equivalence.ChosenRepresentative), which
// therefore lies in C; c is then a sphere (HomotopicSphere) with the
// class of x (ClassEqIff).
var Representative = representativeThm{family.Add(registry.ProofEntry{
	Name: "Representative",
	Key:  "prop_286b724267faad53",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀C:set(A).",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"C ∈ simplicial_homotopy_group(x₀, n)",
		},
		Conclusion: "(εx:A. x ∈ C) ∈ C ∧ " +
			"(εx:A. x ∈ C) ∈ simplicial_sphere(x₀, n) ∧ " +
			"C = equivalence_class(simplicial_homotopic(x₀, n), εx:A. x ∈ C)",
	},
		func(a *Argument, kan Fact, x0 *Expr[A], n *Expr[Nat], C *Expr[Set[A]], vertex, inGroup Fact) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			homotopic := a.TermAs[Fun2[A, A, Bool]]("simplicial_homotopic(x₀, n)")
			c, chosen := a.LetAs[A]("c", "εx:A. x ∈ C")
			x, represented := a.ObtainAs[A](
				"C is a class of πₙ: the class of a sphere x",
				"∃x:A. x ∈ simplicial_sphere(x₀, n) ∧ C = equivalence_class(simplicial_homotopic(x₀, n), x)",
				By(InHomotopyGroup.Read(simplicial).At(x0, n, C), vertex, inGroup))
			parts := a.Conjuncts(
				represented,
				"x is a sphere",
				"and C is its class")
			xSphere, class := parts[0], parts[1]
			toC := a.Have(
				"x is homotopic to itself, so to the point c chosen in C, its class",
				"simplicial_homotopic(x₀, n, x, c)",
				chosen.Rw(),
				class.Rw(),
				By(
					HomotopicRefl.Read(simplicial).At(x0, n, x),
					vertex,
					xSphere,
					equivalence.ChosenRepresentative.At(homotopic, x)))
			cIn := a.Have(
				"so c lies in C, the class of x",
				"c ∈ C",
				class.Rw(),
				By(equivalence.InClass, toC))
			cSphere := a.Have(
				"a simplex homotopic to a sphere is a sphere: c is one",
				"c ∈ simplicial_sphere(x₀, n)",
				By(HomotopicSphere.Read(simplicial).At(x0, n, x, c), vertex, toC, xSphere))
			sameClass := a.Have(
				"and homotopic spheres have one class",
				"equivalence_class(simplicial_homotopic(x₀, n), x) = "+
					"equivalence_class(simplicial_homotopic(x₀, n), c)",
				By(ClassEqIff.Read(kan).At(x0, n, x, c), vertex, xSphere, cSphere, toC))
			a.Show(
				"so c lies in C, is a sphere, and C, the class of x, is its class",
				By(Normalized, cIn, cSphere, class, sameClass))
		}),
})}

// ---------------------------------------------------------------------------
// The product: fillers, their independence, and the group
// ---------------------------------------------------------------------------

// ProductFillerExists — for 0 < n two spheres have a product filler: the
// horn of dimension n + 1 missing the face n, with x at n + 1, y at n − 1
// and the base simplex elsewhere, is a horn of spheres, which
// SphereHornFill fills; a filler of it is a product filler.
var ProductFillerExists = productFillerExistsThm{family.Add(registry.ProofEntry{
	Name: "ProductFillerExists",
	Key:  "prop_1aed0bbce7655cb1",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x y:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"0 < n",
			"x ∈ simplicial_sphere(x₀, n) ∧ y ∈ simplicial_sphere(x₀, n)",
		},
		Conclusion: "∃w:A. " +
			"    w ∈ X.simplices(n + 1) ∧ " +
			"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ " +
			"    X.d(n + 1, n + 1, w) = x ∧ " +
			"    X.d(n + 1, n - 1, w) = y",
	},
		func(a *Argument, kan Fact, x0 *Expr[A], n *Expr[Nat], standing Fact, _, _ *Expr[A], given Fact) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is positive")
			vertex, positive := hypotheses[0], hypotheses[1]
			previous, next := a.TermAs[Nat]("n - 1"), a.TermAs[Nat]("n + 1")

			f, fDef := a.LetAs[Fun[Nat, A]](
				"f", "λi:num. COND(i = n + 1, x, COND(i = n - 1, y, base_simplex(x₀, n)))")
			values := a.Have(
				"f is x at n + 1 and y at n − 1, two distinct indices",
				"f(n + 1) = x ∧ f(n - 1) = y",
				fDef.Rw(),
				ByArith())
			baseValues := a.Have(
				"and the base simplex below n − 1",
				"∀i:num. i + 1 < n ⇒ f(i) = base_simplex(x₀, n)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
			members := a.Have(
				"every member of f is a sphere: x and y by hypothesis, the base simplex by BaseSphere",
				"∀i:num. f(i) ∈ simplicial_sphere(x₀, n)",
				fDef.Rw(),
				By(BaseSphere.Read(simplicial).At(x0, n), vertex, given))
			dimension := a.Have(
				"the horn has dimension n + 1, and the missing face n is one of its faces",
				"n ≤ n + 1",
				ByArith())

			w, filled := a.ObtainAs[A](
				"so the horn f of spheres has a filler w, an (n+1)-simplex of X",
				"∃w:A. w ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, n), f, w)",
				By(SphereHornFill.Read(kan).At(x0, n, n, f), dimension, members))
			filling := a.Conjuncts(
				filled,
				"w is an (n+1)-simplex",
				"whose faces other than n are the members of f")
			wIn, faceOf := filling[0], a.Unfolded(filling[1], simplicial_set.FacesFillerDef)
			hornFace := kan_complex.HornFacesMember
			wBelow := a.Have(
				"the faces of w below n − 1 are the base simplex",
				"∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(faceOf.At(i), hornFace.At(n, n, i), baseValues.At(i))
				}))
			a.Take(w)
			a.Show(
				"w is a product filler: its faces n + 1 and n − 1 are the members of f there, x and y",
				ByArith(
					wIn,
					wBelow,
					faceOf.At(next),
					hornFace.At(n, n, next),
					faceOf.At(previous),
					hornFace.At(n, n, previous),
					values,
					positive))
		}),
})}

// ProductSphere — the n-th face of a product filler is a sphere: it is
// an n-simplex (FaceIn), and each of its faces is read through the face
// identity. Below n − 1 the face of the filler is the base simplex and
// the n-th face inherits it (BaseSimplexFaceInherited); at n − 1 the
// identity at the pair (n − 1, n) makes it the face n − 1 of the sphere
// y, and at n the identity at the pair (n, n + 1) the face n of the
// sphere x, the base simplex either way.
var ProductSphere = productSphereThm{family.Add(registry.ProofEntry{
	Name: "ProductSphere",
	Key:  "prop_8f4e7a6d8519630f",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x y w:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"0 < n",
			"x ∈ simplicial_sphere(x₀, n)",
			"y ∈ simplicial_sphere(x₀, n)",
			"w ∈ X.simplices(n + 1)",
			"∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)",
			"X.d(n + 1, n + 1, w) = x",
			"X.d(n + 1, n - 1, w) = y",
		},
		Conclusion: "X.d(n + 1, n, w) ∈ simplicial_sphere(x₀, n)",
	},
		func(a *Argument, simplicial Fact, x0 *Expr[A], n *Expr[Nat], _, _, w *Expr[A],
			vertex, positive, xSphere, ySphere, wIn, wBelow, wLast, wPrevious Fact) {
			previous, next := a.TermAs[Nat]("n - 1"), a.TermAs[Nat]("n + 1")
			shift := a.Have(
				"n, being positive, is (n − 1) + 1",
				"n - 1 + 1 = n ∧ n - 1 + 2 = n + 1",
				ByArith(positive))

			middleIn := a.Have(
				"the n-th face of w is an n-simplex",
				"X.d(n + 1, n, w) ∈ X.simplices(n)",
				ByArith(simplicial_set.FaceIn.Read(simplicial).At(n, n, w), wIn))
			faces := a.Have(
				"every face of it is the base simplex at n − 1",
				"∀i:num. i ≤ n ⇒ X.d(n, i, X.d(n + 1, n, w)) = base_simplex(x₀, n - 1)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					index := b.Assume()
					notBelow := b.Unless(
						b.Term("i + 1 < n"),
						"below n − 1 the face i of w is the base simplex, and the n-th face inherits it",
						Given(func(c *Argument, below Fact) {
							c.Show(
								"so the face i of the n-th face of w is the base simplex at n − 1",
								ByArith(
									simplicial_set.BaseSimplexFaceInherited.Read(simplicial).At(x0, previous, i, n, w),
									vertex,
									wIn,
									wBelow.At(i),
									below,
									shift))
						}))
					b.Cases(b.Term("i = n - 1"))
					b.When(
						"at n − 1 the face identity reads the face off the face n − 1 of w, the sphere y",
						func(c *Argument, atPrevious Fact) {
							c.Show(
								"so the face n − 1 of the n-th face of w is the base simplex at n − 1",
								CalcEq(
									Leg(
										c.TermAs[A]("X.d(n, i, X.d(n + 1, i, w))"),
										"the face identity at the pair (n − 1, n)",
										ByArith(simplicial_set.FaceFace.Read(simplicial).At(previous, i, n, w), wIn, shift, atPrevious)),
									Leg(
										c.TermAs[A]("X.d(n, i, y)"),
										"the face n − 1 of w is y",
										By(Normalized, atPrevious, wPrevious)),
									FinalLeg(
										"and every face of the sphere y is the base simplex at n − 1",
										BySets(c.Unfolded(ySphere, SimplicialSphereDef), index, positive)),
								))
						})
					b.Otherwise(
						"at n the face identity reads the face off the last face of w, the sphere x",
						func(c *Argument, notPrevious Fact) {
							atN := c.Have(
								"i, at most n and neither below n − 1 nor n − 1 itself, is n",
								"i = n",
								ByArith(index, notBelow, notPrevious))
							c.Show(
								"so the face n of the n-th face of w is the base simplex at n − 1",
								CalcEq(
									Leg(
										c.TermAs[A]("X.d(n, i, X.d(n + 1, n + 1, w))"),
										"the face identity at the pair (n, n + 1)",
										ByArith(simplicial_set.FaceFace.Read(simplicial).At(previous, n, next, w), wIn, shift, atN)),
									Leg(
										c.TermAs[A]("X.d(n, i, x)"),
										"the last face of w is x",
										By(Normalized, wLast)),
									FinalLeg(
										"and every face of the sphere x is the base simplex at n − 1",
										BySets(c.Unfolded(xSphere, SimplicialSphereDef), index, positive)),
								))
						})
				}))
			a.Show(
				"so the n-th face of w is a sphere",
				Unfold(SimplicialSphereDef),
				BySets(middleIn, faces))
		}),
})}

// inverseFiller is the shape of a filler for the inverse of x: the base
// simplex below n − 1 and at n, x at n − 1.
const inverseFiller = "w ∈ X.simplices(n + 1) ∧ (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = " +
	"base_simplex(x₀, n)) ∧ X.d(n + 1, n - 1, w) = x ∧ X.d(n + 1, n, w) = base_simplex(x₀, n)"

// InverseFillerExists — for 0 < n a sphere has an inverse filler: the
// horn of dimension n + 1 missing the last face, with x at n − 1 and the
// base simplex elsewhere, is a horn of spheres, and a filler of it is an
// inverse filler.
var InverseFillerExists = inverseFillerExistsThm{family.Add(registry.ProofEntry{
	Name: "InverseFillerExists",
	Key:  "prop_51e27795398292a1",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"0 < n",
			"x ∈ simplicial_sphere(x₀, n)",
		},
		Conclusion: "∃w:A. " +
			"    w ∈ X.simplices(n + 1) ∧ " +
			"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ " +
			"    X.d(n + 1, n - 1, w) = x ∧ " +
			"    X.d(n + 1, n, w) = base_simplex(x₀, n)",
	},
		func(a *Argument, kan Fact, x0 *Expr[A], n *Expr[Nat], standing Fact, x *Expr[A], xSphere Fact) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is positive")
			vertex, positive := hypotheses[0], hypotheses[1]
			previous, next := a.TermAs[Nat]("n - 1"), a.TermAs[Nat]("n + 1")

			f, fDef := a.LetAs[Fun[Nat, A]]("f", "λi:num. COND(i = n - 1, x, base_simplex(x₀, n))")
			values := a.Have(
				"f is x at n − 1 and the base simplex at n",
				"f(n - 1) = x ∧ f(n) = base_simplex(x₀, n)",
				fDef.Rw(),
				ByArith(positive))
			baseValues := a.Have(
				"and the base simplex below n − 1",
				"∀i:num. i + 1 < n ⇒ f(i) = base_simplex(x₀, n)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
			members := a.Have(
				"every member of f is a sphere: x by hypothesis, the base simplex by BaseSphere",
				"∀i:num. f(i) ∈ simplicial_sphere(x₀, n)",
				fDef.Rw(),
				By(BaseSphere.Read(simplicial).At(x0, n), vertex, xSphere))
			dimension := a.Have(
				"the horn has dimension n + 1, and the missing face n + 1 is one of its faces",
				"n + 1 ≤ n + 1",
				ByArith())

			w, filled := a.ObtainAs[A](
				"so the horn f of spheres has a filler w, an (n+1)-simplex of X",
				"∃w:A. w ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, n + 1), f, w)",
				By(SphereHornFill.Read(kan).At(x0, n, next, f), dimension, members))
			filling := a.Conjuncts(
				filled,
				"w is an (n+1)-simplex",
				"whose faces other than the last are the members of f")
			wIn, faceOf := filling[0], a.Unfolded(filling[1], simplicial_set.FacesFillerDef)
			hornFace := kan_complex.HornFacesMember
			wBelow := a.Have(
				"the faces of w below n − 1 are the base simplex",
				"∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(faceOf.At(i), hornFace.At(n, next, i), baseValues.At(i))
				}))
			a.Take(w)
			a.Show(
				"w is an inverse filler: its faces n − 1 and n are the members of f there, x and the base simplex",
				ByArith(
					wIn,
					wBelow,
					faceOf.At(previous),
					hornFace.At(n, next, previous),
					faceOf.At(n),
					hornFace.At(n, next, n),
					values,
					positive))
		}),
})}

// InverseSphere — the last face of an inverse filler is a sphere: by the
// face identity at the pair (i, n + 1) its face i is the face n of the
// face i of the filler. At n − 1 that is the sphere x, whose face n is
// the base simplex at n − 1; at every other i ≤ n the face i of the filler
// is the base simplex, and the last face inherits it (BaseSimplexFaceInherited).
var InverseSphere = inverseSphereThm{family.Add(registry.ProofEntry{
	Name: "InverseSphere",
	Key:  "prop_e292d9cbe8d32c5c",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x w:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"0 < n",
			"x ∈ simplicial_sphere(x₀, n) ∧ " +
				"w ∈ X.simplices(n + 1) ∧ " +
				"(∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ " +
				"X.d(n + 1, n - 1, w) = x ∧ " +
				"X.d(n + 1, n, w) = base_simplex(x₀, n)",
		},
		Conclusion: "X.d(n + 1, n + 1, w) ∈ simplicial_sphere(x₀, n)",
	},
		func(
			a *Argument,
			simplicial Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			standing Fact,
			_, w *Expr[A],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is positive")
			vertex, positive := hypotheses[0], hypotheses[1]
			previous, next := a.TermAs[Nat]("n - 1"), a.TermAs[Nat]("n + 1")
			parts := a.Conjuncts(
				given,
				"x is a sphere",
				"w is an (n+1)-simplex",
				"whose faces below n − 1 are the base simplex",
				"whose face n − 1 is x",
				"and whose face n is the base simplex")
			xSphere, wIn, wBelow, wAtPrevious, wAtN := parts[0], parts[1], parts[2], parts[3], parts[4]
			shift := a.Have(
				"n, being positive, is (n − 1) + 1",
				"n - 1 + 1 = n ∧ n - 1 + 2 = n + 1",
				ByArith(positive))

			lastIn := a.Have(
				"the last face of w is an n-simplex",
				"X.d(n + 1, n + 1, w) ∈ X.simplices(n)",
				ByArith(simplicial_set.FaceIn.Read(simplicial).At(n, next, w), wIn))
			lastFaces := a.Have(
				"every face of it is the base simplex at n − 1",
				"∀i:num. i ≤ n ⇒ X.d(n, i, X.d(n + 1, n + 1, w)) = base_simplex(x₀, n - 1)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					index := b.Assume()
					b.Cases(b.Term("i = n - 1"))
					b.When(
						"at n − 1 the face of w is the sphere x, whose face n is the base simplex",
						func(c *Argument, atPrevious Fact) {
							xAtN := c.Have(
								"the face n of the sphere x is the base simplex at n − 1",
								"X.d(n, n, x) = base_simplex(x₀, n - 1)",
								BySets(c.Unfolded(xSphere, SimplicialSphereDef), positive, nat_order.LessEqRefl.At(n)))
							identity := c.Have(
								"the face i of the last face of w is the face n of its "+
									"face i, by the face identity at the pair (i, n + 1)",
								"X.d(n, i, X.d(n + 1, n + 1, w)) = X.d(n, n, X.d(n + 1, i, w))",
								ByArith(simplicial_set.FaceFace.Read(simplicial).At(previous, i, next, w), wIn, shift, index))
							c.Show(
								"so the face i of the last face is the base simplex at n − 1",
								By(identity, atPrevious, wAtPrevious, xAtN))
						})
					b.Otherwise(
						"at every other i ≤ n the face of w is the base simplex, and the last face inherits it",
						func(c *Argument, notPrevious Fact) {
							onBase := c.Have(
								"the face i of w is the base simplex: below n − 1, and at n",
								"X.d(n + 1, i, w) = base_simplex(x₀, n)",
								Derive(func(e *Argument) {
									notBelow := e.Unless(
										e.Term("i + 1 < n"),
										"below n − 1 it is, w being an inverse filler",
										Given(func(g *Argument, below Fact) {
											g.Show(
												"so the face i of w is the base simplex",
												By(wBelow.At(i), below))
										}))
									atN := e.Have(
										"otherwise i, at most n and neither n − 1 nor below it, is n",
										"i = n",
										ByArith(index, notPrevious, notBelow))
									e.Show(
										"where the face of w is the base simplex too",
										ByArith(atN, wAtN))
								}))
							c.Show(
								"so the face i of the last face of w is the base simplex at n − 1",
								ByArith(
									simplicial_set.BaseSimplexFaceInherited.Read(simplicial).At(x0, previous, i, next, w),
									vertex,
									wIn,
									onBase,
									index,
									shift))
						})
				}))
			a.Show(
				"so the last face of w is a sphere",
				Unfold(SimplicialSphereDef),
				BySets(lastIn, lastFaces))
		}),
})}

// ProductIndependent — two product fillers of the same spheres have
// homotopic n-th faces. With w and w' the two fillers, the horn of
// dimension n + 2 missing the face n, with the degeneracy s(n, n, y) at
// n − 1, w' at n + 1, w at n + 2 and the base simplex below n − 1, is
// compatible: the degeneracy has y as its faces n and n + 1, where it
// meets w' and w, w' meets w along x, and every other face in play is the
// base simplex. The face n of a filler has the face n of w' as its face
// n, the face n of w as its face n + 1 and the base simplex below n: a
// homotopy from the one to the other.
var ProductIndependent = productIndependentThm{family.Add(registry.ProofEntry{
	Name: "ProductIndependent",
	Key:  "prop_ee3146d9372f1ecf",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x y w w':A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"0 < n",
			"y ∈ simplicial_sphere(x₀, n) ∧ " +
				"(w ∈ X.simplices(n + 1) ∧ " +
				"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ " +
				"    X.d(n + 1, n + 1, w) = x ∧ " +
				"    X.d(n + 1, n - 1, w) = y) ∧ " +
				"(w' ∈ X.simplices(n + 1) ∧ " +
				"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w') = base_simplex(x₀, n)) ∧ " +
				"    X.d(n + 1, n + 1, w') = x ∧ " +
				"    X.d(n + 1, n - 1, w') = y)",
		},
		Conclusion: "simplicial_homotopic(x₀, n, X.d(n + 1, n, w'), X.d(n + 1, n, w))",
	},
		func(
			a *Argument,
			kan Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			standing Fact,
			_, y, _, _ *Expr[A],
			given Fact,
		) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			face := simplicial_set.FaceFace.Read(simplicial)
			baseFace := simplicial_set.BaseSimplexFace.Read(simplicial)
			baseInherited := simplicial_set.BaseSimplexFaceInherited.Read(simplicial)
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is positive")
			vertex, positive := hypotheses[0], hypotheses[1]
			previous, next, top := a.TermAs[Nat]("n - 1"), a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 2")

			parts := a.Conjuncts(
				given,
				"y is a sphere",
				"w is an (n+1)-simplex",
				"whose faces below n − 1 are the base simplex",
				"x is its face n + 1",
				"and y its face n − 1",
				"w' is an (n+1)-simplex",
				"whose faces below n − 1 are the base simplex",
				"x is its face n + 1",
				"and y its face n − 1")
			ySphere := parts[0]
			wIn, wBelow, wAtNext, wAtPrevious := parts[1], parts[2], parts[3], parts[4]
			wPrimeIn, wPrimeBelow, wPrimeAtNext, wPrimeAtPrevious := parts[5], parts[6], parts[7], parts[8]

			degenerate := a.Conjuncts(
				a.Have(
					"the face table of the degeneracy s(n, n, y) of the sphere y",
					"X.s(n, n, y) ∈ X.simplices(n + 1) ∧ "+
						"X.d(n + 1, n, X.s(n, n, y)) = y ∧ "+
						"X.d(n + 1, n + 1, X.s(n, n, y)) = y ∧ "+
						"(∀i:num. i ≤ n + 1 ∧ ¬(i = n) ∧ ¬(i = n + 1) ⇒ X.d(n + 1, i, X.s(n, n, y)) = base_simplex(x₀, n))",
					ByArith(SphereDegeneracyFaces.Read(simplicial).At(x0, n, y, n), vertex, ySphere)),
				"s(n, n, y) is an (n+1)-simplex",
				"whose face n is y",
				"as is its face n + 1",
				"and whose other faces are the base simplex")
			degenerateIn, degenerateAtN, degenerateAtNext, degenerateAway :=
				degenerate[0], degenerate[1], degenerate[2], degenerate[3]

			f, fDef := a.LetAs[Fun[Nat, A]](
				"f",
				"λi:num. "+
					"    COND(i = n - 1, "+
					"        X.s(n, n, y), "+
					"        COND(i = n + 1, w', COND(i = n + 2, w, base_simplex(x₀, n + 1))))")
			values := a.Have(
				"f is the degeneracy at n − 1, w' at n + 1 and w at n + 2",
				"f(n - 1) = X.s(n, n, y) ∧ f(n + 1) = w' ∧ f(n + 2) = w",
				fDef.Rw(),
				ByArith())
			baseValues := a.Have(
				"and the base simplex below n − 1",
				"∀i:num. i + 1 < n ⇒ f(i) = base_simplex(x₀, n + 1)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
			members := a.Have(
				"every member of f is an (n+1)-simplex: the degeneracy, w', w or the base simplex",
				"∀i:num. f(i) ∈ X.simplices(n + 1)",
				fDef.Rw(),
				By(degenerateIn, wPrimeIn, wIn, simplicial_set.BaseSimplexIn.Read(simplicial).At(x0, next), vertex))
			membersBelow := a.Have(
				"and every member of f has the base simplex for its faces below n − 1",
				"∀j i:num. i + 1 < n ⇒ X.d(n + 1, i, f(j)) = base_simplex(x₀, n)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					i := b.FixAs[Nat]()
					below := b.Assume()
					b.Show(
						"f(j) is the degeneracy, w', w or the base simplex "+
							"at n + 1, and the face i of each is the base simplex",
						fDef.Rw(),
						CondRewrite(),
						ByArith(
							degenerateAway.At(i),
							wPrimeBelow.At(i),
							wBelow.At(i),
							baseFace.At(x0, n, i),
							below,
							vertex))
				}))
			hornFace := kan_complex.HornFacesMember
			compatible := a.Have(
				"so f is compatible on the faces of the horn missing the face n",
				"faces_compatible(n + 1, horn_faces(n + 1, n), f)",
				Simp(Fwd(simplicial_set.FacesCompatibleDef)),
				Derive(func(b *Argument) {
					i, j := b.FixAs[Nat](), b.FixAs[Nat]()
					faces := b.Assume()
					pair := b.Have(
						"i < j are faces of the horn: j is at most n + 2, and neither is n",
						"i < j ∧ j ≤ n + 1 + 1 ∧ ¬(i = n) ∧ ¬(j = n)",
						By(hornFace.At(next, n, i), hornFace.At(next, n, j), faces))
					jPrevious := b.TermAs[Nat]("j - 1")
					notBelow := b.Unless(
						b.Term("i + 1 < n"),
						"below n − 1 the member f(i) is the base simplex, and both faces are the base simplex at n",
						Given(func(c *Argument, below Fact) {
							c.Show(
								"the face i of f(j) and the face j − 1 of the base simplex f(i) are the base simplex at n",
								ByArith(
									membersBelow.At(j, i),
									baseValues.At(i),
									baseFace.At(x0, n, jPrevious),
									below,
									pair,
									vertex))
						}))
					notPrevious := b.Unless(
						b.Term("i = n - 1"),
						"with i = n − 1 the member there is the degeneracy, and j is n + 1 or n + 2",
						Given(func(c *Argument, atPrevious Fact) {
							jNotNext := c.Unless(
								c.Term("j = n + 1"),
								"at the pair (n − 1, n + 1) the face n − 1 of w' and the face n of the degeneracy are y",
								Given(func(e *Argument, jAtNext Fact) {
									e.Show(
										"so both faces are y",
										atPrevious.Rw(),
										jAtNext.Rw(),
										ByArith(values, wPrimeAtPrevious, degenerateAtN))
								}))
							jAtTop := c.Have(
								"so j is n + 2",
								"j = n + 2",
								ByArith(pair, atPrevious, jNotNext))
							c.Show(
								"at the pair (n − 1, n + 2) the face n − 1 of w and the face n + 1 of the degeneracy are y",
								atPrevious.Rw(),
								jAtTop.Rw(),
								ByArith(values, wAtPrevious, degenerateAtNext))
						}))
					remaining := b.Conjuncts(
						b.Have(
							"the one pair left is (n + 1, n + 2)",
							"i = n + 1 ∧ j = n + 2",
							ByArith(notBelow, notPrevious, pair)),
						"i is n + 1",
						"j is n + 2")
					b.Show(
						"where the face n + 1 of w and the face n + 1 of w' are x",
						remaining[0].Rw(),
						remaining[1].Rw(),
						ByArith(values, wAtNext, wPrimeAtNext))
				}))
			horn := a.Have(
				"so f is a horn of X missing the face n",
				"face_family(n + 1, horn_faces(n + 1, n), f)",
				Unfold(simplicial_set.FaceFamilyDef),
				By(members, compatible))
			dimension := a.Have(
				"the horn has dimension (n + 1) + 1 = n + 2, and the missing face n is one of its faces",
				"n + 1 + 1 = n + 2 ∧ n ≤ n + 1 + 1",
				ByArith())

			v, filled := a.ObtainAs[A](
				"so the horn f has a filler v, an (n+2)-simplex of X",
				"∃v:A. v ∈ X.simplices(n + 2) ∧ faces_filler(n + 1, horn_faces(n + 1, n), f, v)",
				By(kan_complex.KanFill.Read(kan).At(next, n, f), dimension, horn))
			filling := a.Conjuncts(
				filled,
				"v is an (n+2)-simplex",
				"whose faces other than n are the members of f")
			vIn, faceOf := filling[0], a.Unfolded(filling[1], simplicial_set.FacesFillerDef)
			vBelow := a.Have(
				"the faces of v below n − 1 are the base simplex",
				"∀i:num. i + 1 < n ⇒ X.d(n + 2, i, v) = base_simplex(x₀, n + 1)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(faceOf.At(i), hornFace.At(next, n, i), baseValues.At(i), dimension)
				}))

			homotopy := a.TermAs[A]("X.d(n + 2, n, v)")
			homotopyIn := a.Have(
				"the face n of v is an (n+1)-simplex",
				"X.d(n + 2, n, v) ∈ X.simplices(n + 1)",
				ByArith(simplicial_set.FaceIn.Read(simplicial).At(next, n, v), vIn, dimension))
			homotopyBelow := a.Have(
				"whose faces below n are the base simplex",
				"∀i:num. i < n ⇒ X.d(n + 1, i, X.d(n + 2, n, v)) = base_simplex(x₀, n)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					below := b.Assume()
					notBelowPrevious := b.Unless(
						b.Term("i + 1 < n"),
						"below n − 1 the face i of v is the base simplex, and the face n of v inherits it",
						Given(func(c *Argument, belowPrevious Fact) {
							c.Show(
								"so the face i of the face n of v is the base simplex",
								ByArith(baseInherited.At(x0, n, i, n, v), vertex, vIn, vBelow.At(i), belowPrevious))
						}))
					at := b.Have(
						"otherwise i is n − 1",
						"i = n - 1",
						ByArith(below, notBelowPrevious))
					identity := b.Have(
						"the face i of the face n of v is the face n − 1 of "+
							"its face i, by the face identity at the pair (i, n)",
						"X.d(n + 1, i, X.d(n + 2, n, v)) = X.d(n + 1, n - 1, X.d(n + 2, i, v))",
						ByArith(face.At(n, i, n, v), vIn, below))
					vAtPrevious := b.Have(
						"where the face of v is the degeneracy s(n, n, y)",
						"X.d(n + 2, n - 1, v) = X.s(n, n, y)",
						ByArith(faceOf.At(previous), hornFace.At(next, n, previous), values, dimension, positive))
					b.Show(
						"whose face n − 1 is the base simplex, so the face i of the face n of v is the base simplex",
						ByArith(identity, at, vAtPrevious, degenerateAway.At(previous), positive))
				}))
			homotopyAtN := a.Have(
				"its face n is the face n of w'",
				"X.d(n + 1, n, X.d(n + 2, n, v)) = X.d(n + 1, n, w')",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.d(n + 2, n + 1, v))"),
						"the face identity of v at the pair (n, n + 1)",
						ByArith(face.At(n, n, next, v), vIn)),
					FinalLeg(
						"the face n + 1 of v is f(n + 1), which is w'",
						ByArith(faceOf.At(next), hornFace.At(next, n, next), values, dimension)),
				))
			homotopyAtNext := a.Have(
				"and its face n + 1 is the face n of w",
				"X.d(n + 1, n + 1, X.d(n + 2, n, v)) = X.d(n + 1, n, w)",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.d(n + 2, n + 2, v))"),
						"the face identity of v at the pair (n, n + 2)",
						ByArith(face.At(n, n, top, v), vIn)),
					FinalLeg(
						"the face n + 2 of v is f(n + 2), which is w",
						ByArith(faceOf.At(top), hornFace.At(next, n, top), values, dimension)),
				))
			a.Do(Simp(Fwd(SimplicialHomotopicDef)))
			a.Take(homotopy)
			a.Show(
				"so the face n of v is a homotopy from the face n of w' to the face n of w",
				By(homotopyIn, homotopyBelow, homotopyAtN, homotopyAtNext))
		}),
	Reading: "The first sphere x is not needed: the horn reads only that the two fillers share their " +
		"last face. y is load-bearing at the face n − 1 of s(n, n, y), which must be the base simplex.",
})}

// ProductLeftHomotopic — replacing the first sphere by a homotopic one
// changes the product by a homotopy. With h a homotopy from x to x', the
// horn of dimension n + 2 missing the face n + 1, with the degeneracy
// s(n, n − 1, y) at n − 1, w at n, h at n + 2 and the base simplex below
// n − 1, is compatible: the degeneracy has y as its faces n − 1 and n and
// the base simplex for the others, so it meets w along y and h in the base
// simplex, and w meets h along x. The face n + 1 of a filler has y as its
// face n − 1, the face n of w as its face n and x' as its last face: a
// product filler for x' and y, which ProductIndependent compares with w'.
var ProductLeftHomotopic = productLeftHomotopicThm{family.Add(registry.ProofEntry{
	Name: "ProductLeftHomotopic",
	Key:  "prop_b54ba9e244507608",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x x' y w w':A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"0 < n",
			"simplicial_homotopic(x₀, n, x, x') ∧ " +
				"y ∈ simplicial_sphere(x₀, n) ∧ " +
				"(w ∈ X.simplices(n + 1) ∧ " +
				"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ " +
				"    X.d(n + 1, n + 1, w) = x ∧ " +
				"    X.d(n + 1, n - 1, w) = y) ∧ " +
				"(w' ∈ X.simplices(n + 1) ∧ " +
				"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w') = base_simplex(x₀, n)) ∧ " +
				"    X.d(n + 1, n + 1, w') = x' ∧ " +
				"    X.d(n + 1, n - 1, w') = y)",
		},
		Conclusion: "simplicial_homotopic(x₀, n, X.d(n + 1, n, w), X.d(n + 1, n, w'))",
	},
		func(
			a *Argument,
			kan Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			standing Fact,
			_, xPrime, y, _, wPrime *Expr[A],
			given Fact,
		) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			face := simplicial_set.FaceFace.Read(simplicial)
			baseFace := simplicial_set.BaseSimplexFace.Read(simplicial)
			baseInherited := simplicial_set.BaseSimplexFaceInherited.Read(simplicial)
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is positive")
			vertex, positive := hypotheses[0], hypotheses[1]
			previous, next, top := a.TermAs[Nat]("n - 1"), a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 2")

			parts := a.Conjuncts(
				given,
				"x is homotopic to x'",
				"y is a sphere",
				"w is an (n+1)-simplex",
				"whose faces below n − 1 are the base simplex",
				"x is its face n + 1",
				"and y its face n − 1",
				"w' is an (n+1)-simplex",
				"whose faces below n − 1 are the base simplex",
				"x' is its face n + 1",
				"and y its face n − 1")
			ySphere := parts[1]
			wIn, wBelow, wAtNext, wAtPrevious := parts[2], parts[3], parts[4], parts[5]
			wPrimeIn, wPrimeBelow, wPrimeAtNext, wPrimeAtPrevious := parts[6], parts[7], parts[8], parts[9]
			_, byH := a.UnpackAs[A](a.Unfolded(parts[0], SimplicialHomotopicDef), "h")
			hParts := a.Conjuncts(
				byH,
				"h is an (n+1)-simplex",
				"whose faces below n are the base simplex",
				"whose face n is x",
				"and whose face n + 1 is x'")
			hIn, hBelow, hAtN, hAtNext := hParts[0], hParts[1], hParts[2], hParts[3]

			shift := a.Have(
				"n, being positive, is (n − 1) + 1",
				"n - 1 + 1 = n",
				ByArith(positive))
			degenerate := a.Conjuncts(
				a.Have(
					"the face table of the degeneracy s(n, n − 1, y) of the sphere y",
					"X.s(n, n - 1, y) ∈ X.simplices(n + 1) ∧ "+
						"X.d(n + 1, n - 1, X.s(n, n - 1, y)) = y ∧ "+
						"X.d(n + 1, n, X.s(n, n - 1, y)) = y ∧ "+
						"(∀i:num. "+
						"    i ≤ n + 1 ∧ ¬(i = n - 1) ∧ ¬(i = n) ⇒ X.d(n + 1, i, X.s(n, n - 1, y)) = base_simplex(x₀, n))",
					ByArith(SphereDegeneracyFaces.Read(simplicial).At(x0, n, y, previous), vertex, ySphere, shift)),
				"s(n, n − 1, y) is an (n+1)-simplex",
				"whose face n − 1 is y",
				"as is its face n",
				"and whose other faces are the base simplex")
			degenerateIn, degenerateAtPrevious, degenerateAtN, degenerateAway :=
				degenerate[0], degenerate[1], degenerate[2], degenerate[3]

			f, fDef := a.LetAs[Fun[Nat, A]](
				"f",
				"λi:num. "+
					"    COND(i = n - 1, "+
					"        X.s(n, n - 1, y), "+
					"        COND(i = n, w, COND(i = n + 2, h, base_simplex(x₀, n + 1))))")
			values := a.Have(
				"f is the degeneracy at n − 1, w at n and h at n + 2",
				"f(n - 1) = X.s(n, n - 1, y) ∧ f(n) = w ∧ f(n + 2) = h",
				fDef.Rw(),
				ByArith(positive))
			baseValues := a.Have(
				"and the base simplex below n − 1",
				"∀i:num. i + 1 < n ⇒ f(i) = base_simplex(x₀, n + 1)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
			members := a.Have(
				"every member of f is an (n+1)-simplex: the degeneracy, w, h or the base simplex",
				"∀i:num. f(i) ∈ X.simplices(n + 1)",
				fDef.Rw(),
				By(degenerateIn, wIn, hIn, simplicial_set.BaseSimplexIn.Read(simplicial).At(x0, next), vertex))
			membersBelow := a.Have(
				"and every member of f has the base simplex for its faces below n − 1",
				"∀j i:num. i + 1 < n ⇒ X.d(n + 1, i, f(j)) = base_simplex(x₀, n)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					i := b.FixAs[Nat]()
					below := b.Assume()
					b.Show(
						"f(j) is the degeneracy, w, h or the base simplex "+
							"at n + 1, and the face i of each is the base simplex",
						fDef.Rw(),
						CondRewrite(),
						ByArith(degenerateAway.At(i), wBelow.At(i), hBelow.At(i), baseFace.At(x0, n, i), below, vertex))
				}))
			hornFace := kan_complex.HornFacesMember
			compatible := a.Have(
				"so f is compatible on the faces of the horn missing the face n + 1",
				"faces_compatible(n + 1, horn_faces(n + 1, n + 1), f)",
				Simp(Fwd(simplicial_set.FacesCompatibleDef)),
				Derive(func(b *Argument) {
					i, j := b.FixAs[Nat](), b.FixAs[Nat]()
					faces := b.Assume()
					pair := b.Have(
						"i < j are faces of the horn: j is at most n + 2, and neither is n + 1",
						"i < j ∧ j ≤ n + 1 + 1 ∧ ¬(i = n + 1) ∧ ¬(j = n + 1)",
						By(hornFace.At(next, next, i), hornFace.At(next, next, j), faces))
					jPrevious := b.TermAs[Nat]("j - 1")
					notBelow := b.Unless(
						b.Term("i + 1 < n"),
						"below n − 1 the member f(i) is the base simplex, and both faces are the base simplex at n",
						Given(func(c *Argument, below Fact) {
							c.Show(
								"the face i of f(j) and the face j − 1 of the base simplex f(i) are the base simplex at n",
								ByArith(
									membersBelow.At(j, i),
									baseValues.At(i),
									baseFace.At(x0, n, jPrevious),
									below,
									pair,
									vertex))
						}))
					b.Cases(b.Term("i = n"))
					b.When(
						"at the pair (n, n + 2) h starts and w ends at x",
						func(e *Argument, atN Fact) {
							jAtTop := e.Have(
								"j is then n + 2",
								"j = n + 2",
								ByArith(atN, pair))
							e.Show(
								"the face n of h and the face n + 1 of w are x",
								atN.Rw(),
								jAtTop.Rw(),
								CalcEq(
									Leg(
										e.TermAs[A]("X.d(n + 1, n, h)"),
										"the member at n + 2 is h",
										By(Normalized, values)),
									Leg(
										e.TermAs[A]("X.d(n + 1, n + 1, w)"),
										"h starts at x, where w ends",
										By(Normalized, hAtN, wAtNext)),
									FinalLeg(
										"and w is the member at n, at the face n + 1 = (n + 2) − 1",
										ByArith(values)),
								))
						})
					b.Otherwise(
						"at i = n − 1 the pair is (n − 1, n) or (n − 1, n + 2)",
						func(e *Argument, notN Fact) {
							atPrevious := e.Have(
								"i is then n − 1",
								"i = n - 1",
								ByArith(notBelow, notN, pair))
							e.Cases(e.Term("j = n"))
							e.When(
								"at the pair (n − 1, n) w and the degeneracy share the face y",
								func(g *Argument, jAtN Fact) {
									g.Show(
										"the face n − 1 of w and of the degeneracy is y",
										atPrevious.Rw(),
										jAtN.Rw(),
										CalcEq(
											Leg(
												g.TermAs[A]("X.d(n + 1, n - 1, w)"),
												"the member at n is w",
												By(Normalized, values)),
											Leg(
												y,
												"w has y as its face n − 1",
												By(wAtPrevious)),
											Leg(
												g.TermAs[A]("X.d(n + 1, n - 1, X.s(n, n - 1, y))"),
												"as does the degeneracy",
												By(degenerateAtPrevious)),
											FinalLeg(
												"which is the member at n − 1",
												By(Normalized, values)),
										))
								})
							e.Otherwise(
								"at the pair (n − 1, n + 2) h and the degeneracy meet in the base simplex",
								func(g *Argument, jNotN Fact) {
									jAtTop := g.Have(
										"j is then n + 2",
										"j = n + 2",
										ByArith(atPrevious, jNotN, pair))
									g.Show(
										"the face n − 1 of h and the last face of the degeneracy are the base simplex",
										atPrevious.Rw(),
										jAtTop.Rw(),
										CalcEq(
											Leg(
												g.TermAs[A]("X.d(n + 1, n - 1, h)"),
												"the member at n + 2 is h",
												By(Normalized, values)),
											Leg(
												g.TermAs[A]("base_simplex(x₀, n)"),
												"h has the base simplex as its face n − 1, below n",
												ByArith(hBelow.At(previous), positive)),
											Leg(
												g.TermAs[A]("X.d(n + 1, n + 1, X.s(n, n - 1, y))"),
												"as the degeneracy has as its last face",
												ByArith(degenerateAway.At(next))),
											FinalLeg(
												"which is the member at n − 1, at the face n + 1 = (n + 2) − 1",
												ByArith(values)),
										))
								})
						})
				}))
			horn := a.Have(
				"so f is a horn of X missing the face n + 1",
				"face_family(n + 1, horn_faces(n + 1, n + 1), f)",
				Unfold(simplicial_set.FaceFamilyDef),
				By(members, compatible))
			dimension := a.Have(
				"the horn has dimension (n + 1) + 1 = n + 2, and the missing face n + 1 is one of its faces",
				"n + 1 + 1 = n + 2 ∧ n + 1 ≤ n + 1 + 1",
				ByArith())

			v, filled := a.ObtainAs[A](
				"so the horn f has a filler v, an (n+2)-simplex of X",
				"∃v:A. v ∈ X.simplices(n + 2) ∧ faces_filler(n + 1, horn_faces(n + 1, n + 1), f, v)",
				By(kan_complex.KanFill.Read(kan).At(next, next, f), dimension, horn))
			filling := a.Conjuncts(
				filled,
				"v is an (n+2)-simplex",
				"whose faces other than n + 1 are the members of f")
			vIn, faceOf := filling[0], a.Unfolded(filling[1], simplicial_set.FacesFillerDef)

			product := a.TermAs[A]("X.d(n + 2, n + 1, v)")
			productIn := a.Have(
				"the face n + 1 of v is an (n+1)-simplex",
				"X.d(n + 2, n + 1, v) ∈ X.simplices(n + 1)",
				ByArith(simplicial_set.FaceIn.Read(simplicial).At(next, next, v), vIn, dimension))
			vBelow := a.Have(
				"the faces of v below n − 1 are the members of f there, the base simplex",
				"∀i:num. i + 1 < n ⇒ X.d(n + 2, i, v) = base_simplex(x₀, n + 1)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(faceOf.At(i), hornFace.At(next, next, i), baseValues.At(i), dimension)
				}))
			productBelow := a.Have(
				"so the faces of its face n + 1 below n − 1 are the base simplex",
				"∀i:num. i + 1 < n ⇒ X.d(n + 1, i, X.d(n + 2, n + 1, v)) = base_simplex(x₀, n)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(baseInherited.At(x0, n, i, next, v), vertex, vIn, vBelow.At(i))
				}))
			productAtPrevious := a.Have(
				"its face n − 1 is y",
				"X.d(n + 1, n - 1, X.d(n + 2, n + 1, v)) = y",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.d(n + 2, n - 1, v))"),
						"the face identity of v at the pair (n − 1, n + 1)",
						ByArith(face.At(n, previous, next, v), vIn)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.s(n, n - 1, y))"),
						"the face n − 1 of v is f(n − 1), the degeneracy",
						ByArith(faceOf.At(previous), hornFace.At(next, next, previous), values, dimension)),
					FinalLeg(
						"whose face n is y",
						By(degenerateAtN)),
				))
			productAtN := a.Have(
				"its face n is the face n of w",
				"X.d(n + 1, n, X.d(n + 2, n + 1, v)) = X.d(n + 1, n, w)",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.d(n + 2, n, v))"),
						"the face identity of v at the pair (n, n + 1)",
						ByArith(face.At(n, n, next, v), vIn)),
					FinalLeg(
						"the face n of v is f(n), which is w",
						ByArith(faceOf.At(n), hornFace.At(next, next, n), values, dimension)),
				))
			productAtNext := a.Have(
				"and its last face is x'",
				"X.d(n + 1, n + 1, X.d(n + 2, n + 1, v)) = x'",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, X.d(n + 2, n + 2, v))"),
						"the face identity of v at the pair (n + 1, n + 2)",
						ByArith(face.At(n, next, top, v), vIn)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, h)"),
						"the face n + 2 of v is f(n + 2), which is h",
						ByArith(faceOf.At(top), hornFace.At(next, next, top), values, dimension)),
					FinalLeg(
						"which ends at x'",
						By(hAtNext)),
				))
			a.Show(
				"so the face n + 1 of v and w' are two product fillers for x' and "+
					"y, and their faces n, the first being that of w, are homotopic",
				productAtN.RwRev(),
				By(
					ProductIndependent.Read(kan).At(x0, n, xPrime, y, wPrime, product),
					vertex,
					positive,
					ySphere,
					wPrimeIn,
					wPrimeBelow,
					wPrimeAtNext,
					wPrimeAtPrevious,
					productIn,
					productBelow,
					productAtNext,
					productAtPrevious))
		}),
})}

// ProductRightHomotopic — and so does replacing the second sphere. With g
// a homotopy from y to y' and p the face n of w, the horn of dimension
// n + 2 missing the last face, with g at n − 1, the degeneracy s(n, n, p)
// at n, w at n + 1 and the base simplex below n − 1, is compatible: g
// meets w along y, the degeneracy meets g in the base simplex, p being a
// sphere (ProductSphere), and meets w along p. The last face of a filler
// has y' as its face n − 1, p as its face n and x as its last face: a
// product filler for x and y', which ProductIndependent compares with w'.
var ProductRightHomotopic = productRightHomotopicThm{family.Add(registry.ProofEntry{
	Name: "ProductRightHomotopic",
	Reading: "That y is a sphere is not forced: its faces below n follow from g, and its " +
		"face n from w with x a sphere. The hypothesis gives p its sphere through ProductSphere " +
		"at once, and y′ its sphere through HomotopicSphere, which ProductIndependent reads.",
	Key: "prop_38874b5c47f8284a",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x y y' w w':A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"0 < n",
			"x ∈ simplicial_sphere(x₀, n) ∧ " +
				"y ∈ simplicial_sphere(x₀, n) ∧ " +
				"simplicial_homotopic(x₀, n, y, y') ∧ " +
				"(w ∈ X.simplices(n + 1) ∧ " +
				"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ " +
				"    X.d(n + 1, n + 1, w) = x ∧ " +
				"    X.d(n + 1, n - 1, w) = y) ∧ " +
				"(w' ∈ X.simplices(n + 1) ∧ " +
				"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w') = base_simplex(x₀, n)) ∧ " +
				"    X.d(n + 1, n + 1, w') = x ∧ " +
				"    X.d(n + 1, n - 1, w') = y')",
		},
		Conclusion: "simplicial_homotopic(x₀, n, X.d(n + 1, n, w), X.d(n + 1, n, w'))",
	},
		func(
			a *Argument,
			kan Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			standing Fact,
			x, y, yPrime, w, wPrime *Expr[A],
			given Fact,
		) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			face := simplicial_set.FaceFace.Read(simplicial)
			baseFace := simplicial_set.BaseSimplexFace.Read(simplicial)
			baseInherited := simplicial_set.BaseSimplexFaceInherited.Read(simplicial)
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is positive")
			vertex, positive := hypotheses[0], hypotheses[1]
			previous, next, top := a.TermAs[Nat]("n - 1"), a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 2")

			parts := a.Conjuncts(
				given,
				"x is a sphere",
				"and so is y",
				"y is homotopic to y'",
				"w is an (n+1)-simplex",
				"whose faces below n − 1 are the base simplex",
				"x is its face n + 1",
				"and y its face n − 1",
				"w' is an (n+1)-simplex",
				"whose faces below n − 1 are the base simplex",
				"x is its face n + 1",
				"and y' its face n − 1")
			xSphere, ySphere, homotopic := parts[0], parts[1], parts[2]
			wIn, wBelow, wAtNext, wAtPrevious := parts[3], parts[4], parts[5], parts[6]
			wPrimeIn, wPrimeBelow, wPrimeAtNext, wPrimeAtPrevious := parts[7], parts[8], parts[9], parts[10]
			_, byG := a.UnpackAs[A](a.Unfolded(homotopic, SimplicialHomotopicDef), "g")
			gParts := a.Conjuncts(
				byG,
				"g is an (n+1)-simplex",
				"whose faces below n are the base simplex",
				"whose face n is y",
				"and whose face n + 1 is y'")
			gIn, gBelow, gAtN, gAtNext := gParts[0], gParts[1], gParts[2], gParts[3]

			yPrimeSphere := a.Have(
				"y', homotopic to the sphere y, is a sphere",
				"y' ∈ simplicial_sphere(x₀, n)",
				By(HomotopicSphere.Read(simplicial).At(x0, n, y, yPrime), vertex, homotopic, ySphere))

			p, pDef := a.LetAs[A]("p", "X.d(n + 1, n, w)")
			pSphere := a.Have(
				"p is a sphere, w being a product filler for the spheres x and y",
				"p ∈ simplicial_sphere(x₀, n)",
				pDef.Rw(),
				By(
					ProductSphere.Read(simplicial).At(x0, n, x, y, w),
					vertex,
					positive,
					xSphere,
					ySphere,
					wIn,
					wBelow,
					wAtNext,
					wAtPrevious))
			degenerate := a.Conjuncts(
				a.Have(
					"the face table of the degeneracy s(n, n, p) of the sphere p",
					"X.s(n, n, p) ∈ X.simplices(n + 1) ∧ "+
						"X.d(n + 1, n, X.s(n, n, p)) = p ∧ "+
						"X.d(n + 1, n + 1, X.s(n, n, p)) = p ∧ "+
						"(∀i:num. i ≤ n + 1 ∧ ¬(i = n) ∧ ¬(i = n + 1) ⇒ X.d(n + 1, i, X.s(n, n, p)) = base_simplex(x₀, n))",
					ByArith(SphereDegeneracyFaces.Read(simplicial).At(x0, n, p, n), vertex, pSphere)),
				"s(n, n, p) is an (n+1)-simplex",
				"whose face n is p",
				"as is its face n + 1",
				"and whose other faces are the base simplex")
			degenerateIn, degenerateAtN, degenerateAtNext, degenerateAway :=
				degenerate[0], degenerate[1], degenerate[2], degenerate[3]

			f, fDef := a.LetAs[Fun[Nat, A]](
				"f",
				"λi:num. "+
					"    COND(i = n - 1, g, COND(i = n, X.s(n, n, p), COND(i = n + 1, w, base_simplex(x₀, n + 1))))")
			values := a.Have(
				"f is g at n − 1, the degeneracy at n and w at n + 1",
				"f(n - 1) = g ∧ f(n) = X.s(n, n, p) ∧ f(n + 1) = w",
				fDef.Rw(),
				ByArith(positive))
			baseValues := a.Have(
				"and the base simplex below n − 1",
				"∀i:num. i + 1 < n ⇒ f(i) = base_simplex(x₀, n + 1)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
			members := a.Have(
				"every member of f is an (n+1)-simplex: g, the degeneracy, w or the base simplex",
				"∀i:num. f(i) ∈ X.simplices(n + 1)",
				fDef.Rw(),
				By(gIn, degenerateIn, wIn, simplicial_set.BaseSimplexIn.Read(simplicial).At(x0, next), vertex))
			membersBelow := a.Have(
				"and every member of f has the base simplex for its faces below n − 1",
				"∀j i:num. i + 1 < n ⇒ X.d(n + 1, i, f(j)) = base_simplex(x₀, n)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					i := b.FixAs[Nat]()
					below := b.Assume()
					b.Show(
						"f(j) is g, the degeneracy, w or the base simplex "+
							"at n + 1, and the face i of each is the base simplex",
						fDef.Rw(),
						CondRewrite(),
						ByArith(gBelow.At(i), degenerateAway.At(i), wBelow.At(i), baseFace.At(x0, n, i), below, vertex))
				}))
			hornFace := kan_complex.HornFacesMember
			compatible := a.Have(
				"so f is compatible on the faces of the horn missing the face n + 2",
				"faces_compatible(n + 1, horn_faces(n + 1, n + 2), f)",
				Simp(Fwd(simplicial_set.FacesCompatibleDef)),
				Derive(func(b *Argument) {
					i, j := b.FixAs[Nat](), b.FixAs[Nat]()
					faces := b.Assume()
					pair := b.Have(
						"i < j are faces of the horn, so j is at most n + 1",
						"i < j ∧ j ≤ n + 1",
						ByArith(hornFace.At(next, top, j), faces))
					jPrevious := b.TermAs[Nat]("j - 1")
					notBelow := b.Unless(
						b.Term("i + 1 < n"),
						"below n − 1 the member f(i) is the base simplex, and both faces are the base simplex at n",
						Given(func(c *Argument, below Fact) {
							c.Show(
								"the face i of f(j) and the face j − 1 of the base simplex f(i) are the base simplex at n",
								ByArith(
									membersBelow.At(j, i),
									baseValues.At(i),
									baseFace.At(x0, n, jPrevious),
									below,
									pair,
									vertex))
						}))
					b.Cases(b.Term("i = n"))
					b.When(
						"at the pair (n, n + 1) w and the degeneracy share the face p",
						func(e *Argument, atN Fact) {
							jAtNext := e.Have(
								"j is then n + 1",
								"j = n + 1",
								ByArith(atN, pair))
							e.Show(
								"the face n of w and of the degeneracy are p",
								atN.Rw(),
								jAtNext.Rw(),
								CalcEq(
									Leg(
										p,
										"the member at n + 1 is w, whose face n is p",
										By(Normalized, values, pDef)),
									Leg(
										e.TermAs[A]("X.d(n + 1, n, X.s(n, n, p))"),
										"which is the face n of its degeneracy",
										By(degenerateAtN)),
									FinalLeg(
										"and the degeneracy is the member at n, at the face n = (n + 1) − 1",
										ByArith(values)),
								))
						})
					b.Otherwise(
						"at i = n − 1 the pair is (n − 1, n) or (n − 1, n + 1)",
						func(e *Argument, notN Fact) {
							atPrevious := e.Have(
								"i is then n − 1",
								"i = n - 1",
								ByArith(notBelow, notN, pair))
							e.Cases(e.Term("j = n"))
							e.When(
								"at the pair (n − 1, n) g and the degeneracy meet in the base simplex",
								func(h *Argument, jAtN Fact) {
									h.Show(
										"the face n − 1 of the degeneracy and of g are the base simplex",
										atPrevious.Rw(),
										jAtN.Rw(),
										CalcEq(
											Leg(
												h.TermAs[A]("X.d(n + 1, n - 1, X.s(n, n, p))"),
												"the member at n is the degeneracy",
												By(Normalized, values)),
											Leg(
												h.TermAs[A]("base_simplex(x₀, n)"),
												"whose face n − 1 is the base simplex, below n",
												ByArith(degenerateAway.At(previous), positive)),
											Leg(
												h.TermAs[A]("X.d(n + 1, n - 1, g)"),
												"as is the face n − 1 of g",
												ByArith(gBelow.At(previous), positive)),
											FinalLeg(
												"which is the member at n − 1",
												By(Normalized, values)),
										))
								})
							e.Otherwise(
								"at the pair (n − 1, n + 1) w and g share the face y",
								func(h *Argument, jNotN Fact) {
									jAtNext := h.Have(
										"j is then n + 1",
										"j = n + 1",
										ByArith(atPrevious, jNotN, pair))
									h.Show(
										"the face n − 1 of w and the face n of g are y",
										atPrevious.Rw(),
										jAtNext.Rw(),
										CalcEq(
											Leg(
												h.TermAs[A]("X.d(n + 1, n - 1, w)"),
												"the member at n + 1 is w",
												By(Normalized, values)),
											Leg(
												y,
												"w has y as its face n − 1",
												By(wAtPrevious)),
											Leg(
												h.TermAs[A]("X.d(n + 1, n, g)"),
												"where g starts",
												By(gAtN)),
											FinalLeg(
												"which is the member g at n − 1, at the face n = (n + 1) − 1",
												ByArith(values)),
										))
								})
						})
				}))
			horn := a.Have(
				"so f is a horn of X missing the face n + 2",
				"face_family(n + 1, horn_faces(n + 1, n + 2), f)",
				Unfold(simplicial_set.FaceFamilyDef),
				By(members, compatible))
			dimension := a.Have(
				"the horn has dimension (n + 1) + 1 = n + 2, and the missing face n + 2 is one of its faces",
				"n + 1 + 1 = n + 2 ∧ n + 2 ≤ n + 1 + 1",
				ByArith())

			v, filled := a.ObtainAs[A](
				"so the horn f has a filler v, an (n+2)-simplex of X",
				"∃v:A. v ∈ X.simplices(n + 2) ∧ faces_filler(n + 1, horn_faces(n + 1, n + 2), f, v)",
				By(kan_complex.KanFill.Read(kan).At(next, top, f), dimension, horn))
			filling := a.Conjuncts(
				filled,
				"v is an (n+2)-simplex",
				"whose faces other than the last are the members of f")
			vIn, faceOf := filling[0], a.Unfolded(filling[1], simplicial_set.FacesFillerDef)

			product := a.TermAs[A]("X.d(n + 2, n + 2, v)")
			productIn := a.Have(
				"the last face of v is an (n+1)-simplex",
				"X.d(n + 2, n + 2, v) ∈ X.simplices(n + 1)",
				By(simplicial_set.FaceIn.Read(simplicial).At(next, top, v), vIn, dimension))
			vBelow := a.Have(
				"the faces of v below n − 1 are the members of f there, the base simplex",
				"∀i:num. i + 1 < n ⇒ X.d(n + 2, i, v) = base_simplex(x₀, n + 1)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(faceOf.At(i), hornFace.At(next, top, i), baseValues.At(i), dimension)
				}))
			productBelow := a.Have(
				"so the faces of its last face below n − 1 are the base simplex",
				"∀i:num. i + 1 < n ⇒ X.d(n + 1, i, X.d(n + 2, n + 2, v)) = base_simplex(x₀, n)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(baseInherited.At(x0, n, i, top, v), vertex, vIn, vBelow.At(i))
				}))
			productAtPrevious := a.Have(
				"its face n − 1 is y'",
				"X.d(n + 1, n - 1, X.d(n + 2, n + 2, v)) = y'",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, X.d(n + 2, n - 1, v))"),
						"the face identity of v at the pair (n − 1, n + 2)",
						ByArith(face.At(n, previous, top, v), vIn, dimension)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, g)"),
						"the face n − 1 of v is f(n − 1), which is g",
						ByArith(faceOf.At(previous), hornFace.At(next, top, previous), values, dimension)),
					FinalLeg(
						"which ends at y'",
						By(gAtNext)),
				))
			productAtN := a.Have(
				"its face n is p",
				"X.d(n + 1, n, X.d(n + 2, n + 2, v)) = p",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, X.d(n + 2, n, v))"),
						"the face identity of v at the pair (n, n + 2)",
						ByArith(face.At(n, n, top, v), vIn, dimension)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, X.s(n, n, p))"),
						"the face n of v is f(n), the degeneracy",
						ByArith(faceOf.At(n), hornFace.At(next, top, n), values, dimension)),
					FinalLeg(
						"whose last face is p",
						By(degenerateAtNext)),
				))
			productAtNext := a.Have(
				"and its last face is x",
				"X.d(n + 1, n + 1, X.d(n + 2, n + 2, v)) = x",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, X.d(n + 2, n + 1, v))"),
						"the face identity of v at the pair (n + 1, n + 2)",
						ByArith(face.At(n, next, top, v), vIn, dimension)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, w)"),
						"the face n + 1 of v is f(n + 1), which is w",
						ByArith(faceOf.At(next), hornFace.At(next, top, next), values, dimension)),
					FinalLeg(
						"which is x",
						By(wAtNext)),
				))
			a.Show(
				"so the last face of v and w' are two product fillers for x "+
					"and y', and their faces n, the first being p, are homotopic",
				productAtN.RwRev(),
				By(
					ProductIndependent.Read(kan).At(x0, n, x, yPrime, wPrime, product),
					vertex,
					positive,
					yPrimeSphere,
					wPrimeIn,
					wPrimeBelow,
					wPrimeAtNext,
					wPrimeAtPrevious,
					productIn,
					productBelow,
					productAtNext,
					productAtPrevious))
		}),
})}

// MulClass — the product of the classes of two spheres is the class of
// the n-th face of any product filler: the operation is well defined.
// The product reads the chosen representatives x' and y' of the two
// classes, spheres homotopic to x and y, and the chosen product filler w'
// for them, which exists. A product filler u for x' and y compares w with
// w' one sphere at a time: the face n of w is homotopic to that of u
// (ProductLeftHomotopic, x against x'), and the face n of u to that of w'
// (ProductRightHomotopic, y against y'). The two faces are spheres, so
// homotopic they have one class.
var MulClass = mulClassThm{family.Add(registry.ProofEntry{
	Name: "MulClass",
	Key:  "prop_a4610f67ea113fb6",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x y w:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"0 < n",
			"x ∈ simplicial_sphere(x₀, n) ∧ " +
				"y ∈ simplicial_sphere(x₀, n) ∧ " +
				"w ∈ X.simplices(n + 1) ∧ " +
				"(∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ " +
				"X.d(n + 1, n + 1, w) = x ∧ " +
				"X.d(n + 1, n - 1, w) = y",
		},
		Conclusion: "simplicial_homotopy_mul(x₀, " +
			"    n, " +
			"    equivalence_class(simplicial_homotopic(x₀, n), x), " +
			"    equivalence_class(simplicial_homotopic(x₀, n), y)) = " +
			"equivalence_class(simplicial_homotopic(x₀, n), X.d(n + 1, n, w))",
	},
		func(
			a *Argument,
			kan Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			standing Fact,
			x, y, w *Expr[A],
			given Fact,
		) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			X := a.TermAs[simplicial_set.SimplicialOps[A]]("X")
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is positive")
			vertex, positive := hypotheses[0], hypotheses[1]

			parts := a.Conjuncts(
				given,
				"x is a sphere",
				"and so is y",
				"w is an (n+1)-simplex",
				"whose faces below n − 1 are the base simplex",
				"x is its face n + 1",
				"and y its face n − 1")
			xSphere, ySphere := parts[0], parts[1]
			classX := a.TermAs[Set[A]]("equivalence_class(simplicial_homotopic(x₀, n), x)")
			classY := a.TermAs[Set[A]]("equivalence_class(simplicial_homotopic(x₀, n), y)")
			xInPi := a.Have(
				"the class of the sphere x is a class of πₙ",
				"equivalence_class(simplicial_homotopic(x₀, n), x) ∈ simplicial_homotopy_group(x₀, n)",
				By(xSphere, ClassInHomotopyGroup.Read(simplicial).At(x0, n, x), vertex))
			yInPi := a.Have(
				"and so is the class of y",
				"equivalence_class(simplicial_homotopic(x₀, n), y) ∈ simplicial_homotopy_group(x₀, n)",
				By(ySphere, ClassInHomotopyGroup.Read(simplicial).At(x0, n, y), vertex))

			xPrime, xPrimeDef := a.LetAs[A]("x'", "εz:A. z ∈ equivalence_class(simplicial_homotopic(x₀, n), x)")
			yPrime, yPrimeDef := a.LetAs[A]("y'", "εz:A. z ∈ equivalence_class(simplicial_homotopic(x₀, n), y)")
			xPrimeClass := a.Have(
				"the chosen point x' of the class of x is a sphere with that class",
				"x' ∈ simplicial_sphere(x₀, n) ∧ "+
					"equivalence_class(simplicial_homotopic(x₀, n), x) = "+
					"equivalence_class(simplicial_homotopic(x₀, n), x')",
				By(Representative.Read(kan).At(x0, n, classX), vertex, xInPi, xPrimeDef))
			yPrimeClass := a.Have(
				"and the chosen point y' of the class of y likewise",
				"y' ∈ simplicial_sphere(x₀, n) ∧ "+
					"equivalence_class(simplicial_homotopic(x₀, n), y) = "+
					"equivalence_class(simplicial_homotopic(x₀, n), y')",
				By(Representative.Read(kan).At(x0, n, classY), vertex, yInPi, yPrimeDef))
			toXPrime := a.Have(
				"two spheres with one class are homotopic: x to x'",
				"simplicial_homotopic(x₀, n, x, x')",
				By(ClassEqIff.Read(kan).At(x0, n, x, xPrime), vertex, given, xPrimeClass))
			toYPrime := a.Have(
				"and y to y'",
				"simplicial_homotopic(x₀, n, y, y')",
				By(ClassEqIff.Read(kan).At(x0, n, y, yPrime), vertex, given, yPrimeClass))

			wPrime, wPrimeDef := a.LetAs[A](
				"w'",
				"εw:A. "+
					"    w ∈ X.simplices(n + 1) ∧ "+
					"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ "+
					"    X.d(n + 1, n + 1, w) = x' ∧ "+
					"    X.d(n + 1, n - 1, w) = y'")
			_, chosen := a.ObtainChosen(
				"the spheres x' and y' have a product filler, so the chosen one is a product filler",
				"∃w:A. "+
					"    w ∈ X.simplices(n + 1) ∧ "+
					"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ "+
					"    X.d(n + 1, n + 1, w) = x' ∧ "+
					"    X.d(n + 1, n - 1, w) = y'",
				ProductFillerExists.Read(kan).At(x0, n, xPrime, yPrime),
				vertex,
				positive,
				xPrimeClass,
				yPrimeClass)
			wPrimeFills := a.Have(
				"so w' is a product filler for x' and y'",
				"w' ∈ X.simplices(n + 1) ∧ "+
					"(∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w') = base_simplex(x₀, n)) ∧ "+
					"X.d(n + 1, n + 1, w') = x' ∧ "+
					"X.d(n + 1, n - 1, w') = y'",
				By(Normalized, wPrimeDef, chosen))

			u, uFills := a.ObtainAs[A](
				"the spheres x' and y have a product filler u",
				"∃u:A. "+
					"    u ∈ X.simplices(n + 1) ∧ "+
					"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, u) = base_simplex(x₀, n)) ∧ "+
					"    X.d(n + 1, n + 1, u) = x' ∧ "+
					"    X.d(n + 1, n - 1, u) = y",
				By(ProductFillerExists.Read(kan).At(x0, n, xPrime, y), vertex, positive, xPrimeClass, given))
			wFace, uFace, wPrimeFace :=
				a.TermAs[A]("X.d(n + 1, n, w)"), a.TermAs[A]("X.d(n + 1, n, u)"), a.TermAs[A]("X.d(n + 1, n, w')")
			wToU := a.Have(
				"w fills for x and y, u for x' and y, and x is homotopic to x': their faces n are homotopic",
				"simplicial_homotopic(x₀, n, X.d(n + 1, n, w), X.d(n + 1, n, u))",
				By(
					ProductLeftHomotopic.Read(kan).At(x0, n, x, xPrime, y, w, u),
					vertex,
					positive,
					toXPrime,
					given,
					uFills))
			uToWPrime := a.Have(
				"u fills for x' and y, w' for x' and y', and y is homotopic to y': their faces n are homotopic",
				"simplicial_homotopic(x₀, n, X.d(n + 1, n, u), X.d(n + 1, n, w'))",
				By(
					ProductRightHomotopic.Read(kan).At(x0, n, xPrime, y, yPrime, u, wPrime),
					vertex,
					positive,
					xPrimeClass,
					given,
					toYPrime,
					uFills,
					wPrimeFills))
			homotopic := a.Have(
				"by transitivity the faces n of w and w' are homotopic",
				"simplicial_homotopic(x₀, n, X.d(n + 1, n, w), X.d(n + 1, n, w'))",
				By(HomotopicTrans.Read(kan).At(x0, n, wFace, uFace, wPrimeFace), vertex, wToU, uToWPrime))
			wFaceSphere := a.Have(
				"the face n of a product filler is a sphere: of w",
				"X.d(n + 1, n, w) ∈ simplicial_sphere(x₀, n)",
				By(ProductSphere.Read(simplicial).At(x0, n, x, y, w), vertex, positive, given))
			wPrimeFaceSphere := a.Have(
				"and of w'",
				"X.d(n + 1, n, w') ∈ simplicial_sphere(x₀, n)",
				By(
					ProductSphere.Read(simplicial).At(x0, n, xPrime, yPrime, wPrime),
					vertex,
					positive,
					xPrimeClass,
					yPrimeClass,
					wPrimeFills))

			a.Show(
				"the product is the class of the face n of w', which is that of w",
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("equivalence_class(simplicial_homotopic(x₀, n), X.d(n + 1, n, w'))"),
						"the product of the classes is the class of the face "+
							"n of the filler w' chosen for the chosen x' and y'",
						By(At(SimplicialHomotopyMulDef, X, x0, n, classX, classY), wPrimeDef, xPrimeDef, yPrimeDef)),
					FinalLeg(
						"homotopic spheres have one class",
						By(
							ClassEqIff.Read(kan).At(x0, n, wFace, wPrimeFace),
							vertex,
							wFaceSphere,
							wPrimeFaceSphere,
							homotopic)),
				))
		}),
})}

// MulIn — πₙ is closed under the product. C and C' are the classes of
// spheres x and y (InHomotopyGroup), so x and y have a product filler w
// (ProductFillerExists). The product of the classes of x and y is the
// class of the face n of w (MulClass), and that face is a sphere
// (ProductSphere): the product is the class of a sphere.
var MulIn = mulInThm{family.Add(registry.ProofEntry{
	Name: "MulIn",
	Key:  "prop_51cd79b80dd86aa",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀C C':set(A).",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"0 < n",
			"C ∈ simplicial_homotopy_group(x₀, n)",
			"C' ∈ simplicial_homotopy_group(x₀, n)",
		},
		Conclusion: "simplicial_homotopy_mul(x₀, n, C, C') ∈ simplicial_homotopy_group(x₀, n)",
	},
		func(
			a *Argument,
			kan Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			standing Fact,
			C, CPrime *Expr[Set[A]],
			inGroup, inGroupPrime Fact,
		) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is positive")
			vertex, positive := hypotheses[0], hypotheses[1]

			x, xClass := a.ObtainAs[A](
				"C is the class of a sphere x",
				"∃x:A. x ∈ simplicial_sphere(x₀, n) ∧ C = equivalence_class(simplicial_homotopic(x₀, n), x)",
				By(inGroup, InHomotopyGroup.Read(simplicial).At(x0, n, C), vertex))
			y, yClass := a.ObtainAs[A](
				"and C' the class of a sphere y",
				"∃y:A. y ∈ simplicial_sphere(x₀, n) ∧ C' = equivalence_class(simplicial_homotopic(x₀, n), y)",
				By(inGroupPrime, InHomotopyGroup.Read(simplicial).At(x0, n, CPrime), vertex))
			xParts := a.Conjuncts(
				xClass,
				"x is a sphere",
				"whose class is C")
			yParts := a.Conjuncts(
				yClass,
				"y is a sphere",
				"whose class is C'")
			xSphere, ofC := xParts[0], xParts[1]
			ySphere, ofCPrime := yParts[0], yParts[1]

			w, filler := a.ObtainAs[A](
				"the spheres x and y have a product filler w",
				"∃w:A. "+
					"    w ∈ X.simplices(n + 1) ∧ "+
					"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ "+
					"    X.d(n + 1, n + 1, w) = x ∧ "+
					"    X.d(n + 1, n - 1, w) = y",
				By(ProductFillerExists.Read(kan).At(x0, n, x, y), vertex, positive, xSphere, ySphere))
			face := a.TermAs[A]("X.d(n + 1, n, w)")
			faceSphere := a.Have(
				"its face n is a sphere",
				"X.d(n + 1, n, w) ∈ simplicial_sphere(x₀, n)",
				By(ProductSphere.Read(simplicial).At(x0, n, x, y, w), vertex, positive, xSphere, ySphere, filler))
			product := a.Have(
				"the product of C and C', the classes of x and y, is the class of that face",
				"simplicial_homotopy_mul(x₀, n, C, C') = "+
					"equivalence_class(simplicial_homotopic(x₀, n), X.d(n + 1, n, w))",
				By(
					MulClass.Read(kan).At(x0, n, x, y, w),
					vertex,
					positive,
					xSphere,
					ySphere,
					filler,
					ofC,
					ofCPrime))
			a.Show(
				"so it is the class of a sphere, a class of πₙ",
				By(product, faceSphere, ClassInHomotopyGroup.Read(simplicial).At(x0, n, face), vertex))
		}),
})}

// UnitIn — the unit is a member of πₙ. Unfolded, the unit is the class
// of the base simplex; the base simplex is a sphere (BaseSphere), and the
// class of a sphere is a member of πₙ (ClassInHomotopyGroup).
var UnitIn = unitInThm{family.Add(registry.ProofEntry{
	Name: "UnitIn",
	Key:  "prop_6a4a2d4b0904509a",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀x₀:A. ∀n:num.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
		},
		Conclusion: "simplicial_homotopy_unit(x₀, n) ∈ simplicial_homotopy_group(x₀, n)",
	},
		func(a *Argument, simplicial Fact, x0 *Expr[A], n *Expr[Nat], vertex Fact) {
			base := a.TermAs[A]("base_simplex(x₀, n)")
			a.Show(
				"the unit is the class of the base simplex, a sphere, so it is a class of πₙ",
				Unfold(SimplicialHomotopyUnitDef),
				By(
					vertex,
					BaseSphere.Read(simplicial).At(x0, n),
					ClassInHomotopyGroup.Read(simplicial).At(x0, n, base)))
		}),
})}

// LeftIdentity — the unit is a left identity. C is the class of a sphere
// y (InHomotopyGroup), and the degeneracy w = s(n, n − 1, y) has y as its
// faces n − 1 and n and the base simplex as every other face
// (SphereDegeneracyFaces at k = n − 1). So w is a product filler for the
// base simplex and y whose face n is y, and the product of the unit, the
// class of the base simplex, with C is the class of y (MulClass), which
// is C.
var LeftIdentity = leftIdentityThm{family.Add(registry.ProofEntry{
	Name: "LeftIdentity",
	Key:  "prop_859b3b16671ffd48",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀C:set(A).",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"0 < n",
			"C ∈ simplicial_homotopy_group(x₀, n)",
		},
		Conclusion: "simplicial_homotopy_mul(x₀, n, simplicial_homotopy_unit(x₀, n), C) = C",
	},
		func(
			a *Argument,
			kan Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			standing Fact,
			C *Expr[Set[A]],
			inGroup Fact,
		) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is positive")
			vertex, positive := hypotheses[0], hypotheses[1]
			previous := a.TermAs[Nat]("n - 1")

			y, yClass := a.ObtainAs[A](
				"C is the class of a sphere y",
				"∃y:A. y ∈ simplicial_sphere(x₀, n) ∧ C = equivalence_class(simplicial_homotopic(x₀, n), y)",
				By(inGroup, InHomotopyGroup.Read(simplicial).At(x0, n, C), vertex))
			yParts := a.Conjuncts(
				yClass,
				"y is a sphere",
				"whose class is C")
			ySphere, ofC := yParts[0], yParts[1]

			w, wDef := a.LetAs[A]("w", "X.s(n, n - 1, y)")
			fills := a.Have(
				"by its face table at k = n − 1, the degeneracy w is a product filler for the base simplex and y",
				"w ∈ X.simplices(n + 1) ∧ "+
					"(∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ "+
					"X.d(n + 1, n + 1, w) = base_simplex(x₀, n) ∧ "+
					"X.d(n + 1, n - 1, w) = y",
				ByArith(
					SphereDegeneracyFaces.Read(simplicial).At(x0, n, y, previous),
					wDef,
					vertex,
					ySphere,
					positive))
			wAtN := a.Have(
				"and its face (n − 1) + 1 = n is y",
				"X.d(n + 1, n, w) = y",
				ByArith(
					SphereDegeneracyFaces.Read(simplicial).At(x0, n, y, previous),
					wDef,
					vertex,
					ySphere,
					positive))
			base := a.TermAs[A]("base_simplex(x₀, n)")

			a.Show(
				"so the product of the unit with C is the class of y, which is C",
				CalcEq(
					Leg(
						a.TermAs[Set[A]](
							"simplicial_homotopy_mul(x₀, "+
								"    n, "+
								"    equivalence_class(simplicial_homotopic(x₀, n), base_simplex(x₀, n)), "+
								"    equivalence_class(simplicial_homotopic(x₀, n), y))"),
						"the unit is the class of the base simplex, and C is the class of y",
						Unfold(SimplicialHomotopyUnitDef),
						By(ofC)),
					Leg(
						a.TermAs[Set[A]]("equivalence_class(simplicial_homotopic(x₀, n), X.d(n + 1, n, w))"),
						"w is a product filler for the base simplex, a sphere, and y",
						By(
							MulClass.Read(kan).At(x0, n, base, y, w),
							vertex,
							positive,
							BaseSphere.Read(simplicial).At(x0, n),
							ySphere,
							fills)),
					Leg(
						a.TermAs[Set[A]]("equivalence_class(simplicial_homotopic(x₀, n), y)"),
						"whose face n is y",
						By(Normalized, wAtN)),
					FinalLeg(
						"and the class of y is C",
						By(Normalized, ofC)),
				))
		}),
})}

// InvIn — πₙ is closed under the inverse. With x the point the inverse
// chooses in C, a sphere, x has an inverse filler (InverseFillerExists),
// so the filler w the inverse chooses for x is one; its last face z is a
// sphere (InverseSphere), and the inverse is the class of z.
var InvIn = invInThm{family.Add(registry.ProofEntry{
	Name: "InvIn",
	Key:  "prop_8cd32154b4a1edae",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀C:set(A).",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"0 < n",
			"C ∈ simplicial_homotopy_group(x₀, n)",
		},
		Conclusion: "simplicial_homotopy_inv(x₀, n, C) ∈ simplicial_homotopy_group(x₀, n)",
	},
		func(
			a *Argument,
			kan Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			standing Fact,
			C *Expr[Set[A]],
			inGroup Fact,
		) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			X := a.TermAs[simplicial_set.SimplicialOps[A]]("X")
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is positive")
			vertex, positive := hypotheses[0], hypotheses[1]

			x, xDef := a.LetAs[A]("x", "εx:A. x ∈ C")
			xSphere := a.Have(
				"x, the chosen point of C, is a sphere",
				"x ∈ simplicial_sphere(x₀, n)",
				By(Normalized, Representative.Read(kan).At(x0, n, C), vertex, inGroup, xDef))

			w, wDef := a.LetAs[A]("w", "εw:A. "+inverseFiller)
			_, chosen := a.ObtainChosen(
				"the sphere x has an inverse filler, so the chosen one is an inverse filler",
				"∃w:A. "+
					"    w ∈ X.simplices(n + 1) ∧ "+
					"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ "+
					"    X.d(n + 1, n - 1, w) = x ∧ "+
					"    X.d(n + 1, n, w) = base_simplex(x₀, n)",
				InverseFillerExists.Read(kan).At(x0, n, x),
				vertex,
				positive,
				xSphere)
			fills := a.Have(
				"so w is an inverse filler for x",
				"«inverseFiller»",
				By(Normalized, wDef, chosen))
			z, zDef := a.LetAs[A]("z", "X.d(n + 1, n + 1, w)")
			zSphere := a.Have(
				"so its last face z is a sphere",
				"z ∈ simplicial_sphere(x₀, n)",
				zDef.Rw(),
				By(InverseSphere.Read(simplicial).At(x0, n, x, w), vertex, positive, xSphere, fills))

			inverse := a.Have(
				"the inverse of C is the class of z",
				"simplicial_homotopy_inv(x₀, n, C) = equivalence_class(simplicial_homotopic(x₀, n), z)",
				By(At(SimplicialHomotopyInvDef, X, x0, n, C), zDef, wDef, xDef))
			a.Show(
				"so it is the class of a sphere, a class of πₙ",
				inverse.Rw(),
				By(zSphere, ClassInHomotopyGroup.Read(simplicial).At(x0, n, z), vertex))
		}),
})}

// LeftInverse — the inverse is a left inverse. Unfolded, the inverse of
// C is the class of the last face z of the inverse filler w chosen for x,
// the point chosen in C: an (n+1)-simplex with x as its face n − 1 and the
// base simplex as its face n and below n − 1. Such a filler exists
// (InverseFillerExists), so w is one, and z is a sphere (InverseSphere);
// then w is a product filler for z and x whose face n is the base
// simplex, so [z]·C is the unit.
var LeftInverse = leftInverseThm{family.Add(registry.ProofEntry{
	Name: "LeftInverse",
	Key:  "prop_3b9c3750eaacbf02",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀C:set(A).",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"0 < n",
			"C ∈ simplicial_homotopy_group(x₀, n)",
		},
		Conclusion: "simplicial_homotopy_mul(x₀, n, simplicial_homotopy_inv(x₀, n, C), C) = " +
			"simplicial_homotopy_unit(x₀, n)",
	},
		func(
			a *Argument,
			kan Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			standing Fact,
			C *Expr[Set[A]],
			inGroup Fact,
		) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is positive")
			vertex, positive := hypotheses[0], hypotheses[1]

			x, xDef := a.LetAs[A]("x", "εx:A. x ∈ C")
			xParts := a.Conjuncts(
				a.Have(
					"x, the chosen point of C, is a sphere whose class is C",
					"x ∈ simplicial_sphere(x₀, n) ∧ C = equivalence_class(simplicial_homotopic(x₀, n), x)",
					By(Normalized, Representative.Read(kan).At(x0, n, C), xDef, vertex, inGroup)),
				"x is a sphere",
				"whose class is C")
			xSphere, ofC := xParts[0], xParts[1]

			w, wDef := a.LetAs[A]("w", "εw:A. "+inverseFiller)
			_, chosen := a.ObtainChosen(
				"the sphere x has an inverse filler, so the chosen one is an inverse filler",
				"∃w:A. "+
					"    w ∈ X.simplices(n + 1) ∧ "+
					"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ "+
					"    X.d(n + 1, n - 1, w) = x ∧ "+
					"    X.d(n + 1, n, w) = base_simplex(x₀, n)",
				InverseFillerExists.Read(kan).At(x0, n, x),
				vertex,
				positive,
				xSphere)
			fills := a.Have(
				"so w is an inverse filler for x",
				"«inverseFiller»",
				By(Normalized, wDef, chosen))
			wParts := a.Conjuncts(
				fills,
				"w is an (n+1)-simplex",
				"whose faces below n − 1 are the base simplex",
				"whose face n − 1 is x",
				"and whose face n is the base simplex")
			wIn, wBelow, wAtPrevious, wAtN := wParts[0], wParts[1], wParts[2], wParts[3]
			z := a.TermAs[A]("X.d(n + 1, n + 1, w)")
			zSphere := a.Have(
				"its last face z is a sphere",
				"X.d(n + 1, n + 1, w) ∈ simplicial_sphere(x₀, n)",
				By(InverseSphere.Read(simplicial).At(x0, n, x, w), vertex, positive, xSphere, fills))

			a.Show(
				"so the product of the inverse with C is the class of the base simplex, the unit",
				CalcEq(
					Leg(
						a.TermAs[Set[A]](
							"simplicial_homotopy_mul(x₀, "+
								"    n, "+
								"    equivalence_class(simplicial_homotopic(x₀, n), X.d(n + 1, n + 1, w)), "+
								"    equivalence_class(simplicial_homotopic(x₀, n), x))"),
						"unfolded, the inverse of C is the class of z, and C is the class of x",
						Simp(Fwd(SimplicialHomotopyInvDef)),
						By(ofC, wDef, xDef)),
					Leg(
						a.TermAs[Set[A]]("equivalence_class(simplicial_homotopic(x₀, n), X.d(n + 1, n, w))"),
						"w is a product filler for the spheres z and x",
						By(
							MulClass.Read(kan).At(x0, n, z, x, w),
							vertex,
							positive,
							zSphere,
							xSphere,
							wIn,
							wBelow,
							wAtPrevious)),
					Leg(
						a.TermAs[Set[A]]("equivalence_class(simplicial_homotopic(x₀, n), base_simplex(x₀, n))"),
						"whose face n is the base simplex",
						By(Normalized, wAtN)),
					FinalLeg(
						"the class of the base simplex is the unit",
						Unfold(SimplicialHomotopyUnitDef)),
				))
		}),
})}

// Assoc — the product associates. With x, y, z spheres representing the
// three classes, take product fillers w₁ for x and y, w₂ for p and z, w₃
// for y and z, where p, q, r are the n-th faces of w₁, w₂, w₃. The horn
// of dimension n + 2 missing the face n + 1, with w₃ at n − 1, w₂ at n,
// w₁ at n + 2 and the base simplex below n − 1, is compatible: w₂ and w₃
// share the face z, w₃ and w₁ the face y, w₂ and w₁ the face p. The face
// n + 1 of a filler is a product filler for x and r whose n-th face is q,
// so the two products, [x]·[r] and [p]·[z], are both the class of q.
var Assoc = assocThm{family.Add(registry.ProofEntry{
	Name: "Assoc",
	Key:  "prop_f8c886135b7faf63",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀C C' C'':set(A).",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"0 < n",
			"C ∈ simplicial_homotopy_group(x₀, n) ∧ " +
				"C' ∈ simplicial_homotopy_group(x₀, n) ∧ " +
				"C'' ∈ simplicial_homotopy_group(x₀, n)",
		},
		Conclusion: "simplicial_homotopy_mul(x₀, n, C, simplicial_homotopy_mul(x₀, n, C', C'')) = " +
			"simplicial_homotopy_mul(x₀, n, simplicial_homotopy_mul(x₀, n, C, C'), C'')",
	},
		func(
			a *Argument,
			kan Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			standing Fact,
			C, CPrime, CPrimePrime *Expr[Set[A]],
			classes Fact,
		) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			face := simplicial_set.FaceFace.Read(simplicial)
			baseFace := simplicial_set.BaseSimplexFace.Read(simplicial)
			baseInherited := simplicial_set.BaseSimplexFaceInherited.Read(simplicial)
			fillerExists, mulClass := ProductFillerExists.Read(kan), MulClass.Read(kan)
			productSphere := ProductSphere.Read(simplicial)
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is positive")
			vertex, positive := hypotheses[0], hypotheses[1]
			previous, next, top := a.TermAs[Nat]("n - 1"), a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 2")

			inGroup := a.Conjuncts(
				classes,
				"C is a class of πₙ",
				"so is C'",
				"and so is C''")
			x, xClass := a.ObtainAs[A](
				"C is the class of a sphere x",
				"∃x:A. x ∈ simplicial_sphere(x₀, n) ∧ C = equivalence_class(simplicial_homotopic(x₀, n), x)",
				By(inGroup[0], InHomotopyGroup.Read(simplicial).At(x0, n, C), vertex))
			y, yClass := a.ObtainAs[A](
				"C' the class of a sphere y",
				"∃y:A. y ∈ simplicial_sphere(x₀, n) ∧ C' = equivalence_class(simplicial_homotopic(x₀, n), y)",
				By(inGroup[1], InHomotopyGroup.Read(simplicial).At(x0, n, CPrime), vertex))
			z, zClass := a.ObtainAs[A](
				"and C'' the class of a sphere z",
				"∃z:A. z ∈ simplicial_sphere(x₀, n) ∧ C'' = equivalence_class(simplicial_homotopic(x₀, n), z)",
				By(inGroup[2], InHomotopyGroup.Read(simplicial).At(x0, n, CPrimePrime), vertex))
			xParts := a.Conjuncts(
				xClass,
				"x is a sphere",
				"whose class is C")
			yParts := a.Conjuncts(
				yClass,
				"y is a sphere",
				"whose class is C'")
			zParts := a.Conjuncts(
				zClass,
				"z is a sphere",
				"whose class is C''")
			xSphere, ofC := xParts[0], xParts[1]
			ySphere, ofCPrime := yParts[0], yParts[1]
			zSphere, ofCPrimePrime := zParts[0], zParts[1]

			w1, w1Fills := a.ObtainAs[A](
				"x and y have a product filler w₁",
				"∃w₁:A. "+
					"    w₁ ∈ X.simplices(n + 1) ∧ "+
					"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w₁) = base_simplex(x₀, n)) ∧ "+
					"    X.d(n + 1, n + 1, w₁) = x ∧ "+
					"    X.d(n + 1, n - 1, w₁) = y",
				By(fillerExists.At(x0, n, x, y), vertex, positive, xSphere, ySphere))
			w1Parts := a.Conjuncts(
				w1Fills,
				"w₁ is an (n+1)-simplex",
				"whose faces below n − 1 are the base simplex",
				"whose face n + 1 is x",
				"and whose face n − 1 is y")
			w1In, w1Below, w1AtNext, w1AtPrevious := w1Parts[0], w1Parts[1], w1Parts[2], w1Parts[3]
			p, pDef := a.LetAs[A]("p", "X.d(n + 1, n, w₁)")
			pSphere := a.Have(
				"p, the face n of a product filler, is a sphere",
				"p ∈ simplicial_sphere(x₀, n)",
				pDef.Rw(),
				By(productSphere.At(x0, n, x, y, w1), vertex, positive, xSphere, ySphere, w1Fills))

			w2, w2Fills := a.ObtainAs[A](
				"p and z have a product filler w₂",
				"∃w₂:A. "+
					"    w₂ ∈ X.simplices(n + 1) ∧ "+
					"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w₂) = base_simplex(x₀, n)) ∧ "+
					"    X.d(n + 1, n + 1, w₂) = p ∧ "+
					"    X.d(n + 1, n - 1, w₂) = z",
				By(fillerExists.At(x0, n, p, z), vertex, positive, pSphere, zSphere))
			w2Parts := a.Conjuncts(
				w2Fills,
				"w₂ is an (n+1)-simplex",
				"whose faces below n − 1 are the base simplex",
				"whose face n + 1 is p",
				"and whose face n − 1 is z")
			w2In, w2Below, w2AtNext, w2AtPrevious := w2Parts[0], w2Parts[1], w2Parts[2], w2Parts[3]
			qDef := a.Let("q", a.Term("X.d(n + 1, n, w₂)"))

			w3, w3Fills := a.ObtainAs[A](
				"y and z have a product filler w₃",
				"∃w₃:A. "+
					"    w₃ ∈ X.simplices(n + 1) ∧ "+
					"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w₃) = base_simplex(x₀, n)) ∧ "+
					"    X.d(n + 1, n + 1, w₃) = y ∧ "+
					"    X.d(n + 1, n - 1, w₃) = z",
				By(fillerExists.At(x0, n, y, z), vertex, positive, ySphere, zSphere))
			w3Parts := a.Conjuncts(
				w3Fills,
				"w₃ is an (n+1)-simplex",
				"whose faces below n − 1 are the base simplex",
				"whose face n + 1 is y",
				"and whose face n − 1 is z")
			w3In, w3Below, w3AtNext, w3AtPrevious := w3Parts[0], w3Parts[1], w3Parts[2], w3Parts[3]
			r, rDef := a.LetAs[A]("r", "X.d(n + 1, n, w₃)")
			rSphere := a.Have(
				"r, the face n of a product filler, is a sphere",
				"r ∈ simplicial_sphere(x₀, n)",
				rDef.Rw(),
				By(productSphere.At(x0, n, y, z, w3), vertex, positive, ySphere, zSphere, w3Fills))

			f, fDef := a.LetAs[Fun[Nat, A]](
				"f", "λi:num. COND(i = n - 1, w₃, COND(i = n, w₂, COND(i = n + 2, w₁, base_simplex(x₀, n + 1))))")
			values := a.Have(
				"f is w₃ at n − 1, w₂ at n and w₁ at n + 2, three distinct indices as n is positive",
				"f(n - 1) = w₃ ∧ f(n) = w₂ ∧ f(n + 2) = w₁",
				fDef.Rw(),
				ByArith(positive))
			baseValues := a.Have(
				"and the base simplex below n − 1",
				"∀i:num. i + 1 < n ⇒ f(i) = base_simplex(x₀, n + 1)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
			members := a.Have(
				"every member of f is an (n+1)-simplex: a product filler or the base simplex",
				"∀i:num. f(i) ∈ X.simplices(n + 1)",
				fDef.Rw(),
				By(w1In, w2In, w3In, simplicial_set.BaseSimplexIn.Read(simplicial).At(x0, next), vertex))
			membersBelow := a.Have(
				"and has the base simplex for its faces below n − 1",
				"∀j i:num. i + 1 < n ⇒ X.d(n + 1, i, f(j)) = base_simplex(x₀, n)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					i := b.FixAs[Nat]()
					below := b.Assume()
					b.Show(
						"f(j) is a product filler or the base simplex at n + 1, and its face i is the base simplex",
						fDef.Rw(),
						CondRewrite(),
						ByArith(w1Below.At(i), w2Below.At(i), w3Below.At(i), baseFace.At(x0, n, i), below, vertex))
				}))
			hornFace := kan_complex.HornFacesMember
			compatible := a.Have(
				"so f is compatible on the faces of the horn missing the face n + 1",
				"faces_compatible(n + 1, horn_faces(n + 1, n + 1), f)",
				Simp(Fwd(simplicial_set.FacesCompatibleDef)),
				Derive(func(b *Argument) {
					i, j := b.FixAs[Nat](), b.FixAs[Nat]()
					faces := b.Assume()
					pair := b.Have(
						"i < j are faces of the horn: j is at most n + 2, and neither is n + 1",
						"i < j ∧ j ≤ n + 1 + 1 ∧ ¬(i = n + 1) ∧ ¬(j = n + 1)",
						By(hornFace.At(next, next, i), hornFace.At(next, next, j), faces))
					jPrevious := b.TermAs[Nat]("j - 1")
					notBelow := b.Unless(
						b.Term("i + 1 < n"),
						"below n − 1 the member f(i) is the base simplex, and both faces are the base simplex at n",
						Given(func(c *Argument, below Fact) {
							c.Show(
								"the face i of f(j) and the face j − 1 of the base simplex f(i) are the base simplex at n",
								ByArith(
									membersBelow.At(j, i),
									baseValues.At(i),
									baseFace.At(x0, n, jPrevious),
									below,
									pair,
									vertex))
						}))
					b.Cases(b.Term("j = n"))
					b.When(
						"at the pair (n − 1, n) the faces n − 1 of w₂ and of w₃ are both z",
						func(e *Argument, jAtN Fact) {
							atPrevious := e.Have(
								"i is then n − 1",
								"i = n - 1",
								ByArith(notBelow, jAtN, pair))
							e.Show(
								"so the face n − 1 of f(n) is the face n − 1 of f(n − 1)",
								jAtN.Rw(),
								atPrevious.Rw(),
								CalcEq(
									Leg(
										e.TermAs[A]("X.d(n + 1, n - 1, w₂)"),
										"f(n) is w₂",
										By(Normalized, values)),
									Leg(
										z,
										"whose face n − 1 is z",
										By(w2AtPrevious)),
									Leg(
										e.TermAs[A]("X.d(n + 1, n - 1, w₃)"),
										"as is the face n − 1 of w₃",
										By(w3AtPrevious)),
									FinalLeg(
										"and w₃ is f(n − 1)",
										By(Normalized, values)),
								))
						})
					b.Otherwise(
						"otherwise j is n + 2",
						func(e *Argument, jNotN Fact) {
							jAt := e.Conjuncts(
								e.Have(
									"j − 1 is then n + 1, and j is n + 2",
									"j - 1 = n + 1 ∧ j = n + 2",
									ByArith(notBelow, jNotN, pair)),
								"j − 1 is n + 1",
								"j is n + 2")
							jPreviousAtNext, jAtTop := jAt[0], jAt[1]
							e.Cases(e.Term("i = n - 1"))
							e.When(
								"at the pair (n − 1, n + 2) the face n − 1 of w₁ and the face n + 1 of w₃ are both y",
								func(g *Argument, atPrevious Fact) {
									g.Show(
										"so the face n − 1 of f(n + 2) is the face n + 1 of f(n − 1)",
										atPrevious.Rw(),
										jPreviousAtNext.Rw(),
										jAtTop.Rw(),
										CalcEq(
											Leg(
												g.TermAs[A]("X.d(n + 1, n - 1, w₁)"),
												"f(n + 2) is w₁",
												By(Normalized, values)),
											Leg(
												y,
												"whose face n − 1 is y",
												By(w1AtPrevious)),
											Leg(
												g.TermAs[A]("X.d(n + 1, n + 1, w₃)"),
												"the face n + 1 of w₃",
												By(w3AtNext)),
											FinalLeg(
												"and w₃ is f(n − 1)",
												By(Normalized, values)),
										))
								})
							e.Otherwise(
								"at the pair (n, n + 2) the face n of w₁ and the face n + 1 of w₂ are both p",
								func(g *Argument, notPrevious Fact) {
									atN := g.Have(
										"i is then n",
										"i = n",
										ByArith(notBelow, notPrevious, pair))
									g.Show(
										"so the face n of f(n + 2) is the face n + 1 of f(n)",
										atN.Rw(),
										jPreviousAtNext.Rw(),
										jAtTop.Rw(),
										CalcEq(
											Leg(
												g.TermAs[A]("X.d(n + 1, n, w₁)"),
												"f(n + 2) is w₁",
												By(Normalized, values)),
											Leg(
												p,
												"whose face n is p",
												By(pDef)),
											Leg(
												g.TermAs[A]("X.d(n + 1, n + 1, w₂)"),
												"the face n + 1 of w₂",
												By(w2AtNext)),
											FinalLeg(
												"and w₂ is f(n)",
												By(Normalized, values)),
										))
								})
						})
				}))
			horn := a.Have(
				"so f is a horn of X missing the face n + 1",
				"face_family(n + 1, horn_faces(n + 1, n + 1), f)",
				Unfold(simplicial_set.FaceFamilyDef),
				By(members, compatible))
			dimension := a.Have(
				"the horn has dimension (n + 1) + 1 = n + 2, and the missing face n + 1 is one of its faces",
				"n + 1 + 1 = n + 2 ∧ n + 1 ≤ n + 1 + 1",
				ByArith())

			v, filled := a.ObtainAs[A](
				"so the horn f has a filler v, an (n+2)-simplex of X",
				"∃v:A. v ∈ X.simplices(n + 2) ∧ faces_filler(n + 1, horn_faces(n + 1, n + 1), f, v)",
				By(kan_complex.KanFill.Read(kan).At(next, next, f), dimension, horn))
			filling := a.Conjuncts(
				filled,
				"v is an (n+2)-simplex",
				"whose faces other than n + 1 are the members of f")
			vIn, faceOf := filling[0], a.Unfolded(filling[1], simplicial_set.FacesFillerDef)
			vAtPrevious := a.Have(
				"so v has w₃ as its face n − 1",
				"X.d(n + 2, n - 1, v) = w₃",
				ByArith(faceOf.At(previous), hornFace.At(next, next, previous), values, dimension))
			vAtN := a.Have(
				"w₂ as its face n",
				"X.d(n + 2, n, v) = w₂",
				ByArith(faceOf.At(n), hornFace.At(next, next, n), values, dimension))
			vAtTop := a.Have(
				"and w₁ as its face n + 2",
				"X.d(n + 2, n + 2, v) = w₁",
				ByArith(faceOf.At(top), hornFace.At(next, next, top), values, dimension))
			vBelow := a.Have(
				"and the base simplex as its faces below n − 1",
				"∀i:num. i + 1 < n ⇒ X.d(n + 2, i, v) = base_simplex(x₀, n + 1)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(faceOf.At(i), hornFace.At(next, next, i), baseValues.At(i), dimension)
				}))

			product := a.TermAs[A]("X.d(n + 2, n + 1, v)")
			productIn := a.Have(
				"the face n + 1 of v is an (n+1)-simplex",
				"X.d(n + 2, n + 1, v) ∈ X.simplices(n + 1)",
				ByArith(simplicial_set.FaceIn.Read(simplicial).At(next, next, v), vIn, dimension))
			productBelow := a.Have(
				"whose faces below n − 1 are the base simplex, as those of v are",
				"∀i:num. i + 1 < n ⇒ X.d(n + 1, i, X.d(n + 2, n + 1, v)) = base_simplex(x₀, n)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(baseInherited.At(x0, n, i, next, v), vertex, vIn, vBelow.At(i))
				}))
			productAtNext := a.Have(
				"its face n + 1 is x",
				"X.d(n + 1, n + 1, X.d(n + 2, n + 1, v)) = x",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, X.d(n + 2, n + 2, v))"),
						"the face identity at the pair (n + 1, n + 2)",
						ByArith(face.At(n, next, top, v), vIn)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, w₁)"),
						"the face n + 2 of v is w₁",
						By(Normalized, vAtTop)),
					FinalLeg(
						"whose face n + 1 is x",
						By(w1AtNext)),
				))
			productAtPrevious := a.Have(
				"its face n − 1 is r",
				"X.d(n + 1, n - 1, X.d(n + 2, n + 1, v)) = r",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.d(n + 2, n - 1, v))"),
						"the face identity at the pair (n − 1, n + 1)",
						ByArith(face.At(n, previous, next, v), vIn)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n, w₃)"),
						"the face n − 1 of v is w₃",
						By(Normalized, vAtPrevious)),
					FinalLeg(
						"whose face n is r",
						By(rDef)),
				))
			productAtN := a.Have(
				"and its face n is q",
				"X.d(n + 1, n, X.d(n + 2, n + 1, v)) = q",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.d(n + 2, n, v))"),
						"the face identity at the pair (n, n + 1)",
						ByArith(face.At(n, n, next, v), vIn)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n, w₂)"),
						"the face n of v is w₂",
						By(Normalized, vAtN)),
					FinalLeg(
						"whose face n is q",
						By(qDef)),
				))

			a.Show(
				"so both products are the class of q",
				CalcEq(
					Leg(
						a.TermAs[Set[A]](
							"simplicial_homotopy_mul(x₀, n, C, equivalence_class(simplicial_homotopic(x₀, n), r))"),
						"C'·C'' is the class of r, w₃ being a product filler for y and z",
						By(
							Normalized,
							mulClass.At(x0, n, y, z, w3),
							rDef,
							vertex,
							positive,
							ySphere,
							ofCPrime,
							zSphere,
							ofCPrimePrime,
							w3Fills)),
					Leg(
						a.TermAs[Set[A]]("equivalence_class(simplicial_homotopic(x₀, n), q)"),
						"and C·[r] is the class of q, the face n + 1 of v being a product filler for x and r",
						By(
							mulClass.At(x0, n, x, r, product),
							vertex,
							positive,
							xSphere,
							ofC,
							rSphere,
							productIn,
							productBelow,
							productAtNext,
							productAtPrevious,
							productAtN)),
					Leg(
						a.TermAs[Set[A]](
							"simplicial_homotopy_mul(x₀, n, equivalence_class(simplicial_homotopic(x₀, n), p), C'')"),
						"[p]·C'' is the class of q as well, w₂ being a product filler for p and z",
						By(mulClass.At(x0, n, p, z, w2), qDef, vertex, positive, pSphere, zSphere, ofCPrimePrime, w2Fills)),
					FinalLeg(
						"and [p] is C·C', w₁ being a product filler for x and y",
						By(
							Normalized,
							mulClass.At(x0, n, x, y, w1),
							pDef,
							vertex,
							positive,
							xSphere,
							ofC,
							ySphere,
							ofCPrime,
							w1Fills)),
				))
		}),
})}

// GroupOn — for 0 < n the classes form a group on a set, under the
// filler product, with the class of the base simplex as its unit and the
// filler inverse. Unfolded, a group on πₙ asks six things of the classes,
// and each is a law of the chapter at the vertex and the positive
// dimension: the unit is a class (UnitIn), products and inverses of
// classes are classes (MulIn, InvIn), the product associates (Assoc), and
// the unit and the inverse are a left identity and a left inverse
// (LeftIdentity, LeftInverse).
var GroupOn = groupOnThm{family.Add(registry.ProofEntry{
	Name: "GroupOn",
	Key:  "prop_2de763719ddfd2b6",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"0 < n",
		},
		Conclusion: "group_on(mk_group(simplicial_homotopy_mul(x₀, n), " +
			"        simplicial_homotopy_unit(x₀, n), " +
			"        simplicial_homotopy_inv(x₀, n), " +
			"        simplicial_homotopy_group(x₀, n)))",
	},
		func(a *Argument, kan Fact, x0 *Expr[A], n *Expr[Nat], standing Fact) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is positive")
			vertex, positive := hypotheses[0], hypotheses[1]

			a.Show(
				"unfolded, the six conditions of a group on πₙ are the six laws of the classes",
				Unfold(group.GroupOn),
				By(
					UnitIn.Read(simplicial),
					MulIn.Read(kan),
					InvIn.Read(kan),
					Assoc.Read(kan),
					LeftIdentity.Read(kan),
					LeftInverse.Read(kan),
					vertex,
					positive))
		}),
})}

// JuxtapositionExists — for 2 ≤ n two spheres lie side by side in one
// (n+1)-simplex u: x at its faces n − 2 and n − 1, y at n and n + 1, the
// base simplex below. The horn of dimension n + 2 missing the face n,
// with s(n, n − 2, x) at n − 2 and n − 1, s(n, n, y) at n + 1 and n + 2
// and the base simplex below, is compatible: two members in one block
// are one degeneracy read at the same face, and every other pair of
// faces is the base simplex. The face n of a filler is u, its faces
// read off the members through the face identities.
var JuxtapositionExists = juxtapositionExistsThm{family.Add(registry.ProofEntry{
	Name: "JuxtapositionExists",
	Key:  "prop_14334c88f7e36992",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x y:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"2 ≤ n",
			"x ∈ simplicial_sphere(x₀, n) ∧ y ∈ simplicial_sphere(x₀, n)",
		},
		Conclusion: "∃u:A. " +
			"    u ∈ X.simplices(n + 1) ∧ " +
			"    (∀i:num. i + 2 < n ⇒ X.d(n + 1, i, u) = base_simplex(x₀, n)) ∧ " +
			"    X.d(n + 1, n - 2, u) = x ∧ " +
			"    X.d(n + 1, n - 1, u) = x ∧ " +
			"    X.d(n + 1, n, u) = y ∧ " +
			"    X.d(n + 1, n + 1, u) = y",
	},
		func(a *Argument, kan Fact, x0 *Expr[A], n *Expr[Nat], standing Fact, x, y *Expr[A], given Fact) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			face := simplicial_set.FaceFace.Read(simplicial)
			baseFace := simplicial_set.BaseSimplexFace.Read(simplicial)
			baseInherited := simplicial_set.BaseSimplexFaceInherited.Read(simplicial)
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is at least 2")
			vertex, two := hypotheses[0], hypotheses[1]
			both := a.Conjuncts(
				given,
				"x is a sphere",
				"and so is y")
			xSphere, ySphere := both[0], both[1]
			twoDown, previous := a.TermAs[Nat]("n - 2"), a.TermAs[Nat]("n - 1")
			next, top := a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 2")
			shift := a.Have(
				"with 2 ≤ n, n − 2 is at most n and one below n − 1",
				"n - 2 ≤ n ∧ n - 2 + 1 = n - 1",
				ByArith(two))

			sTwoDown := a.Conjuncts(
				a.Have(
					"the face table of the degeneracy s(n, n − 2, x) of the sphere x",
					"X.s(n, n - 2, x) ∈ X.simplices(n + 1) ∧ "+
						"X.d(n + 1, n - 2, X.s(n, n - 2, x)) = x ∧ "+
						"X.d(n + 1, n - 1, X.s(n, n - 2, x)) = x ∧ "+
						"(∀i:num. "+
						"    i ≤ n + 1 ∧ ¬(i = n - 2) ∧ ¬(i = n - 1) ⇒ "+
						"    X.d(n + 1, i, X.s(n, n - 2, x)) = base_simplex(x₀, n))",
					ByArith(SphereDegeneracyFaces.Read(simplicial).At(x0, n, x, twoDown), vertex, xSphere, shift)),
				"s(n, n − 2, x) is an (n+1)-simplex",
				"whose face n − 2 is x",
				"as is its face n − 1",
				"and whose other faces are the base simplex")
			sN := a.Conjuncts(
				a.Have(
					"and the face table of the degeneracy s(n, n, y) of the sphere y",
					"X.s(n, n, y) ∈ X.simplices(n + 1) ∧ "+
						"X.d(n + 1, n, X.s(n, n, y)) = y ∧ "+
						"X.d(n + 1, n + 1, X.s(n, n, y)) = y ∧ "+
						"(∀i:num. i ≤ n + 1 ∧ ¬(i = n) ∧ ¬(i = n + 1) ⇒ X.d(n + 1, i, X.s(n, n, y)) = base_simplex(x₀, n))",
					ByArith(SphereDegeneracyFaces.Read(simplicial).At(x0, n, y, n), vertex, ySphere)),
				"s(n, n, y) is an (n+1)-simplex",
				"whose face n is y",
				"as is its face n + 1",
				"and whose other faces are the base simplex")
			sTwoDownIn, sTwoDownAtPrevious, sTwoDownAway := sTwoDown[0], sTwoDown[2], sTwoDown[3]
			sNIn, sNAtN, sNAway := sN[0], sN[1], sN[3]

			f, fDef := a.LetAs[Fun[Nat, A]](
				"f",
				"λi:num. COND(i + 2 < n, base_simplex(x₀, n + 1), COND(i < n, X.s(n, n - 2, x), X.s(n, n, y)))")
			members := a.Have(
				"every member of f is an (n+1)-simplex",
				"∀i:num. f(i) ∈ X.simplices(n + 1)",
				fDef.Rw(),
				By(sTwoDownIn, sNIn, simplicial_set.BaseSimplexIn.Read(simplicial).At(x0, next), vertex))
			hornFace := kan_complex.HornFacesMember
			compatible := a.Have(
				"and f is compatible on the faces of the horn missing the face n",
				"faces_compatible(n + 1, horn_faces(n + 1, n), f)",
				Simp(Fwd(simplicial_set.FacesCompatibleDef)),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					j := b.FixAs[Nat]()
					faces := b.Assume()
					pair := b.Have(
						"i < j are faces of the horn: j is at most n + 2, and neither is n",
						"i < j ∧ j ≤ n + 1 + 1 ∧ ¬(i = n) ∧ ¬(j = n)",
						By(hornFace.At(next, n, i), hornFace.At(next, n, j), faces))
					jPrevious := b.TermAs[Nat]("j - 1")
					notBelow := b.Unless(
						b.Term("i + 2 < n"),
						"below n − 2 the member at i is the base simplex, and every member has the base simplex there",
						Given(func(c *Argument, below Fact) {
							indices := c.Have(
								"i and j − 1 index faces of an (n+1)-simplex",
								"i ≤ n + 1 ∧ j - 1 ≤ n + 1",
								ByArith(below, pair))
							c.Show(
								"so whichever member stands at j, both faces are the base simplex",
								fDef.Rw(),
								CondRewrite(),
								ByArith(
									below,
									indices,
									vertex,
									baseFace.At(x0, n, i),
									baseFace.At(x0, n, jPrevious),
									sTwoDownAway.At(i),
									sNAway.At(i)))
						}))
					jAbove := b.Unless(
						b.Term("j < n"),
						"with j below n too, i and j are n − 2 and n − 1, both members s(n, n − 2, x)",
						Given(func(c *Argument, jBelow Fact) {
							positions := c.Have(
								"both lie in the block n − 2, n − 1 of x: j is not below n − 2, and j − 1 = i",
								"¬(j + 2 < n) ∧ i < n ∧ j - 1 = i",
								ByArith(notBelow, jBelow, pair))
							c.Show(
								"so both faces are the face n − 2 of s(n, n − 2, x)",
								fDef.Rw(),
								By(notBelow, jBelow, positions))
						}))
					above := b.Unless(
						b.Term("i < n"),
						"with i below n and j above, the members are s(n, n − 2, x) at i and s(n, n, y) at j",
						Given(func(c *Argument, belowN Fact) {
							jNotBelow := c.Have(
								"j is not below n − 2",
								"¬(j + 2 < n)",
								ByArith(jAbove))
							sNAtI := c.Have(
								"the face i of s(n, n, y) misses its copies of y at n and n + 1",
								"X.d(n + 1, i, X.s(n, n, y)) = base_simplex(x₀, n)",
								ByArith(sNAway.At(i), belowN))
							sTwoDownAtJPrevious := c.Have(
								"and the face j − 1 of s(n, n − 2, x) its copies of x at n − 2 and n − 1",
								"X.d(n + 1, j - 1, X.s(n, n - 2, x)) = base_simplex(x₀, n)",
								ByArith(sTwoDownAway.At(jPrevious), two, jAbove, pair))
							c.Show(
								"so both faces are the base simplex",
								fDef.Rw(),
								By(notBelow, jAbove, belowN, jNotBelow, sNAtI, sTwoDownAtJPrevious))
						}))
					positions := b.Have(
						"otherwise both lie in the block n + 1, n + 2 of y: j is not below n, and j − 1 = i",
						"¬(j + 2 < n) ∧ ¬(j < n) ∧ j - 1 = i",
						ByArith(notBelow, jAbove, above, pair))
					b.Show(
						"so both members are s(n, n, y), read at the same face",
						fDef.Rw(),
						By(notBelow, above, positions))
				}))
			horn := a.Have(
				"so f is a horn of X missing the face n",
				"face_family(n + 1, horn_faces(n + 1, n), f)",
				Unfold(simplicial_set.FaceFamilyDef),
				By(members, compatible))
			dimension := a.Have(
				"the horn has dimension (n + 1) + 1 = n + 2, and the missing face n is one of its faces",
				"n + 1 + 1 = n + 2 ∧ n ≤ n + 1 + 1",
				ByArith())

			v, filled := a.ObtainAs[A](
				"so the horn f has a filler v, an (n+2)-simplex of X",
				"∃v:A. v ∈ X.simplices(n + 2) ∧ faces_filler(n + 1, horn_faces(n + 1, n), f, v)",
				By(kan_complex.KanFill.Read(kan).At(next, n, f), horn, dimension))
			filling := a.Conjuncts(
				filled,
				"v is an (n+2)-simplex",
				"whose faces other than n are the members of f")
			vIn, faceOf := filling[0], a.Unfolded(filling[1], simplicial_set.FacesFillerDef)
			values := a.Have(
				"f is s(n, n − 2, x) at n − 2 and n − 1, and s(n, n, y) at n + 1 and n + 2",
				"f(n - 2) = X.s(n, n - 2, x) ∧ "+
					"f(n - 1) = X.s(n, n - 2, x) ∧ "+
					"f(n + 1) = X.s(n, n, y) ∧ "+
					"f(n + 2) = X.s(n, n, y)",
				fDef.Rw(),
				ByArith(two))
			baseValues := a.Have(
				"and the base simplex below n − 2",
				"∀i:num. i + 2 < n ⇒ f(i) = base_simplex(x₀, n + 1)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
			vBelow := a.Have(
				"so the faces of v below n − 2 are the base simplex",
				"∀i:num. i + 2 < n ⇒ X.d(n + 2, i, v) = base_simplex(x₀, n + 1)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(faceOf.At(i), hornFace.At(next, n, i), baseValues.At(i), dimension)
				}))

			u := a.TermAs[A]("X.d(n + 2, n, v)")
			uIn := a.Have(
				"the face n of v is an (n+1)-simplex",
				"X.d(n + 2, n, v) ∈ X.simplices(n + 1)",
				ByArith(simplicial_set.FaceIn.Read(simplicial).At(next, n, v), vIn, dimension))
			uBelow := a.Have(
				"whose faces below n − 2 are the base simplex, as those of v are",
				"∀i:num. i + 2 < n ⇒ X.d(n + 1, i, X.d(n + 2, n, v)) = base_simplex(x₀, n)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(baseInherited.At(x0, n, i, n, v), vertex, vIn, vBelow.At(i))
				}))
			uAtTwoDown := a.Have(
				"its face n − 2 is x",
				"X.d(n + 1, n - 2, X.d(n + 2, n, v)) = x",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n - 1, X.d(n + 2, n - 2, v))"),
						"the face identity at the pair (n − 2, n)",
						ByArith(face.At(n, twoDown, n, v), vIn, two)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n - 1, X.s(n, n - 2, x))"),
						"the face n − 2 of v is s(n, n − 2, x)",
						ByArith(faceOf.At(twoDown), hornFace.At(next, n, twoDown), values, dimension, two)),
					FinalLeg(
						"whose face n − 1 is x",
						By(sTwoDownAtPrevious)),
				))
			uAtPrevious := a.Have(
				"so is its face n − 1",
				"X.d(n + 1, n - 1, X.d(n + 2, n, v)) = x",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n - 1, X.d(n + 2, n - 1, v))"),
						"the face identity at the pair (n − 1, n)",
						ByArith(face.At(n, previous, n, v), vIn, two)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n - 1, X.s(n, n - 2, x))"),
						"the face n − 1 of v is s(n, n − 2, x)",
						ByArith(faceOf.At(previous), hornFace.At(next, n, previous), values, dimension, two)),
					FinalLeg(
						"whose face n − 1 is x",
						By(sTwoDownAtPrevious)),
				))
			uAtN := a.Have(
				"its face n is y",
				"X.d(n + 1, n, X.d(n + 2, n, v)) = y",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.d(n + 2, n + 1, v))"),
						"the face identity at the pair (n, n + 1)",
						ByArith(face.At(n, n, next, v), vIn)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.s(n, n, y))"),
						"the face n + 1 of v is s(n, n, y)",
						ByArith(faceOf.At(next), hornFace.At(next, n, next), values, dimension)),
					FinalLeg(
						"whose face n is y",
						By(sNAtN)),
				))
			uAtNext := a.Have(
				"and so is its face n + 1",
				"X.d(n + 1, n + 1, X.d(n + 2, n, v)) = y",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.d(n + 2, n + 2, v))"),
						"the face identity at the pair (n, n + 2)",
						ByArith(face.At(n, n, top, v), vIn)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.s(n, n, y))"),
						"the face n + 2 of v is s(n, n, y)",
						ByArith(faceOf.At(top), hornFace.At(next, n, top), values, dimension)),
					FinalLeg(
						"whose face n is y",
						By(sNAtN)),
				))
			a.Take(u)
			a.Show(
				"so the face n of v holds x at n − 2 and n − 1, y at n and n + 1, and the base simplex below",
				By(uIn, uBelow, uAtTwoDown, uAtPrevious, uAtN, uAtNext))
		}),
})}

// MulClassLower — for 2 ≤ n the product is also read one position down:
// an (n+1)-simplex t with x at its face n − 2, y at n, the base simplex
// at n + 1 and below n − 2 has the product of the classes of x and y as
// the class of its face n − 1. The horn of dimension n + 2 missing the
// face n − 1, with s(n, n, x) at n − 2, s(n, n − 1, y) at n, t at n + 1,
// s(n, n − 2, x) at n + 2 and the base simplex below, is compatible, and
// the face n − 1 of a filler is a product filler for x and y whose face
// n is the face n − 1 of t: MulClass reads the product there.
var MulClassLower = mulClassLowerThm{family.Add(registry.ProofEntry{
	Name: "MulClassLower",
	Key:  "prop_c3992527a5ced953",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x y t:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"2 ≤ n",
			"x ∈ simplicial_sphere(x₀, n) ∧ " +
				"y ∈ simplicial_sphere(x₀, n) ∧ " +
				"t ∈ X.simplices(n + 1) ∧ " +
				"(∀i:num. i + 2 < n ⇒ X.d(n + 1, i, t) = base_simplex(x₀, n)) ∧ " +
				"X.d(n + 1, n - 2, t) = x ∧ " +
				"X.d(n + 1, n, t) = y ∧ " +
				"X.d(n + 1, n + 1, t) = base_simplex(x₀, n)",
		},
		Conclusion: "simplicial_homotopy_mul(x₀, " +
			"    n, " +
			"    equivalence_class(simplicial_homotopic(x₀, n), x), " +
			"    equivalence_class(simplicial_homotopic(x₀, n), y)) = " +
			"equivalence_class(simplicial_homotopic(x₀, n), X.d(n + 1, n - 1, t))",
	},
		func(
			a *Argument,
			kan Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			standing Fact,
			x, y, _ *Expr[A],
			given Fact,
		) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			face := simplicial_set.FaceFace.Read(simplicial)
			baseFace := simplicial_set.BaseSimplexFace.Read(simplicial)
			baseInherited := simplicial_set.BaseSimplexFaceInherited.Read(simplicial)
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is at least 2")
			vertex, two := hypotheses[0], hypotheses[1]
			parts := a.Conjuncts(
				given,
				"x is a sphere",
				"and so is y",
				"t is an (n+1)-simplex",
				"whose faces below n − 2 are the base simplex",
				"x is its face n − 2",
				"y its face n",
				"and the base simplex its face n + 1")
			xSphere, ySphere, tIn, tBelow, tAtTwoDown, tAtN, tAtNext :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5], parts[6]
			twoDown, previous := a.TermAs[Nat]("n - 2"), a.TermAs[Nat]("n - 1")
			next, top := a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 2")
			shift := a.Have(
				"2 ≤ n makes n positive and n − 2, n − 1, n consecutive, the first two at most n",
				"0 < n ∧ n - 2 ≤ n ∧ n - 1 ≤ n ∧ n - 2 + 1 = n - 1 ∧ n - 1 + 1 = n ∧ n - 1 - 1 = n - 2",
				ByArith(two))

			sN := a.Conjuncts(
				a.Have(
					"the face table of the degeneracy s(n, n, x) of the sphere x",
					"X.s(n, n, x) ∈ X.simplices(n + 1) ∧ "+
						"X.d(n + 1, n, X.s(n, n, x)) = x ∧ "+
						"X.d(n + 1, n + 1, X.s(n, n, x)) = x ∧ "+
						"(∀i:num. i ≤ n + 1 ∧ ¬(i = n) ∧ ¬(i = n + 1) ⇒ X.d(n + 1, i, X.s(n, n, x)) = base_simplex(x₀, n))",
					ByArith(SphereDegeneracyFaces.Read(simplicial).At(x0, n, x, n), vertex, xSphere)),
				"s(n, n, x) is an (n+1)-simplex",
				"whose face n is x",
				"as is its face n + 1",
				"and whose other faces are the base simplex")
			sPrevious := a.Conjuncts(
				a.Have(
					"that of the degeneracy s(n, n − 1, y) of the sphere y",
					"X.s(n, n - 1, y) ∈ X.simplices(n + 1) ∧ "+
						"X.d(n + 1, n - 1, X.s(n, n - 1, y)) = y ∧ "+
						"X.d(n + 1, n, X.s(n, n - 1, y)) = y ∧ "+
						"(∀i:num. "+
						"    i ≤ n + 1 ∧ ¬(i = n - 1) ∧ ¬(i = n) ⇒ X.d(n + 1, i, X.s(n, n - 1, y)) = base_simplex(x₀, n))",
					ByArith(SphereDegeneracyFaces.Read(simplicial).At(x0, n, y, previous), vertex, ySphere, shift)),
				"s(n, n − 1, y) is an (n+1)-simplex",
				"whose face n − 1 is y",
				"as is its face n",
				"and whose other faces are the base simplex")
			sTwoDown := a.Conjuncts(
				a.Have(
					"and that of the degeneracy s(n, n − 2, x) of the sphere x",
					"X.s(n, n - 2, x) ∈ X.simplices(n + 1) ∧ "+
						"X.d(n + 1, n - 2, X.s(n, n - 2, x)) = x ∧ "+
						"X.d(n + 1, n - 1, X.s(n, n - 2, x)) = x ∧ "+
						"(∀i:num. "+
						"    i ≤ n + 1 ∧ ¬(i = n - 2) ∧ ¬(i = n - 1) ⇒ "+
						"    X.d(n + 1, i, X.s(n, n - 2, x)) = base_simplex(x₀, n))",
					ByArith(SphereDegeneracyFaces.Read(simplicial).At(x0, n, x, twoDown), vertex, xSphere, shift)),
				"s(n, n − 2, x) is an (n+1)-simplex",
				"whose face n − 2 is x",
				"as is its face n − 1",
				"and whose other faces are the base simplex")
			sNIn, sNAtN, sNAtNext, sNAway := sN[0], sN[1], sN[2], sN[3]
			sPreviousIn, sPreviousAtPrevious, sPreviousAtN, sPreviousAway :=
				sPrevious[0], sPrevious[1], sPrevious[2], sPrevious[3]
			sTwoDownIn, sTwoDownAtTwoDown, sTwoDownAtPrevious, sTwoDownAway :=
				sTwoDown[0], sTwoDown[1], sTwoDown[2], sTwoDown[3]

			f, fDef := a.LetAs[Fun[Nat, A]](
				"f",
				"λi:num. "+
					"    COND(i + 2 < n, "+
					"        base_simplex(x₀, n + 1), "+
					"        COND(i = n - 2, "+
					"            X.s(n, n, x), "+
					"            COND(i = n, X.s(n, n - 1, y), COND(i = n + 1, t, X.s(n, n - 2, x)))))")
			members := a.Have(
				"every member of f is an (n+1)-simplex",
				"∀i:num. f(i) ∈ X.simplices(n + 1)",
				fDef.Rw(),
				By(
					sNIn,
					sPreviousIn,
					sTwoDownIn,
					tIn,
					simplicial_set.BaseSimplexIn.Read(simplicial).At(x0, next),
					vertex))
			values := a.Have(
				"f is s(n, n, x) at n − 2, s(n, n − 1, y) at n, t at n + 1 and s(n, n − 2, x) at n + 2",
				"f(n - 2) = X.s(n, n, x) ∧ f(n) = X.s(n, n - 1, y) ∧ f(n + 1) = t ∧ f(n + 2) = X.s(n, n - 2, x)",
				fDef.Rw(),
				ByArith(two))
			baseValues := a.Have(
				"and the base simplex below n − 2",
				"∀i:num. i + 2 < n ⇒ f(i) = base_simplex(x₀, n + 1)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
			hornFace := kan_complex.HornFacesMember
			compatible := a.Have(
				"and f is compatible on the faces of the horn missing the face n − 1",
				"faces_compatible(n + 1, horn_faces(n + 1, n - 1), f)",
				Simp(Fwd(simplicial_set.FacesCompatibleDef)),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					j := b.FixAs[Nat]()
					faces := b.Assume()
					pair := b.Have(
						"i < j are faces of the horn: j is at most n + 2, and neither is n − 1",
						"i < j ∧ j ≤ n + 1 + 1 ∧ ¬(i = n - 1) ∧ ¬(j = n - 1)",
						By(hornFace.At(next, previous, i), hornFace.At(next, previous, j), faces))
					jPrevious := b.TermAs[Nat]("j - 1")
					shifts := b.Have(
						"one below n + 1 is n, and one below n + 2 is n + 1",
						"n + 1 - 1 = n ∧ n + 2 - 1 = n + 1",
						ByArith())
					notBelow := b.Unless(
						b.Term("i + 2 < n"),
						"below n − 2 the member at i is the base simplex, and every member has the base simplex there",
						Given(func(c *Argument, below Fact) {
							indices := c.Have(
								"i and j − 1 index faces of an (n+1)-simplex",
								"i ≤ n + 1 ∧ j - 1 ≤ n + 1",
								ByArith(below, pair))
							c.Show(
								"so whichever member stands at j, both faces are the base simplex",
								fDef.Rw(),
								CondRewrite(),
								ByArith(
									below,
									indices,
									vertex,
									baseFace.At(x0, n, i),
									baseFace.At(x0, n, jPrevious),
									sNAway.At(i),
									sPreviousAway.At(i),
									tBelow.At(i),
									sTwoDownAway.At(i)))
						}))
					notTwoDown := b.Unless(
						b.Term("i = n - 2"),
						"with i = n − 2, the member there is s(n, n, x) and j is n, n + 1 or n + 2",
						Given(func(c *Argument, atTwoDown Fact) {
							jNotN := c.Unless(
								c.Term("j = n"),
								"at the pair (n − 2, n): the face n − 2 of s(n, n − 1, "+
									"y) and the face n − 1 of s(n, n, x) are the base simplex",
								Given(func(e *Argument, jAtN Fact) {
									e.Show(
										"so both faces are the base simplex",
										atTwoDown.Rw(),
										jAtN.Rw(),
										ByArith(values, sPreviousAway.At(twoDown), sNAway.At(previous), two))
								}))
							jNotNext := c.Unless(
								c.Term("j = n + 1"),
								"at the pair (n − 2, n + 1): the face n − 2 of t and the face n of s(n, n, x) are x",
								Given(func(e *Argument, jAtNext Fact) {
									e.Show(
										"so both faces are x",
										atTwoDown.Rw(),
										jAtNext.Rw(),
										By(Normalized, shifts, values, tAtTwoDown, sNAtN))
								}))
							jAtTop := c.Have(
								"so j is n + 2",
								"j = n + 2",
								ByArith(pair, atTwoDown, jNotN, jNotNext))
							c.Show(
								"at the pair (n − 2, n + 2) the face n − 2 of s(n, "+
									"n − 2, x) and the face n + 1 of s(n, n, x) are x",
								atTwoDown.Rw(),
								jAtTop.Rw(),
								By(shifts, values, sTwoDownAtTwoDown, sNAtNext))
						}))
					notN := b.Unless(
						b.Term("i = n"),
						"with i = n, the member there is s(n, n − 1, y) and j is n + 1 or n + 2",
						Given(func(c *Argument, atN Fact) {
							jNotNext := c.Unless(
								c.Term("j = n + 1"),
								"at the pair (n, n + 1): the face n of t and the face n of s(n, n − 1, y) are y",
								Given(func(e *Argument, jAtNext Fact) {
									e.Show(
										"so both faces are y",
										atN.Rw(),
										jAtNext.Rw(),
										By(Normalized, shifts, values, tAtN, sPreviousAtN))
								}))
							jAtTop := c.Have(
								"so j is n + 2",
								"j = n + 2",
								ByArith(pair, atN, jNotNext))
							c.Show(
								"at the pair (n, n + 2) the face n of s(n, n − 2, x) and "+
									"the face n + 1 of s(n, n − 1, y) are the base simplex",
								atN.Rw(),
								jAtTop.Rw(),
								ByArith(shifts, values, sTwoDownAway.At(n), sPreviousAway.At(next), two))
						}))
					remaining := b.Conjuncts(
						b.Have(
							"the one pair left is (n + 1, n + 2)",
							"i = n + 1 ∧ j = n + 2",
							ByArith(notBelow, notTwoDown, notN, pair)),
						"i is n + 1",
						"j is n + 2")
					b.Show(
						"where the face n + 1 of s(n, n − 2, x) and the face n + 1 of t are the base simplex",
						remaining[0].Rw(),
						remaining[1].Rw(),
						ByArith(shifts, values, sTwoDownAway.At(next), tAtNext, two))
				}))
			horn := a.Have(
				"so f is a horn of X missing the face n − 1",
				"face_family(n + 1, horn_faces(n + 1, n - 1), f)",
				Unfold(simplicial_set.FaceFamilyDef),
				By(members, compatible))
			dimension := a.Have(
				"the horn has dimension (n + 1) + 1 = n + 2, and the missing face n − 1 is one of its faces",
				"n + 1 + 1 = n + 2 ∧ n - 1 ≤ n + 1 + 1",
				ByArith())

			v, filled := a.ObtainAs[A](
				"so the horn f has a filler v, an (n+2)-simplex of X",
				"∃v:A. v ∈ X.simplices(n + 2) ∧ faces_filler(n + 1, horn_faces(n + 1, n - 1), f, v)",
				By(kan_complex.KanFill.Read(kan).At(next, previous, f), horn, dimension))
			filling := a.Conjuncts(
				filled,
				"v is an (n+2)-simplex",
				"whose faces other than n − 1 are the members of f")
			vIn, faceOf := filling[0], a.Unfolded(filling[1], simplicial_set.FacesFillerDef)
			vBelow := a.Have(
				"and the faces of v below n − 2 are the base simplex",
				"∀i:num. i + 2 < n ⇒ X.d(n + 2, i, v) = base_simplex(x₀, n + 1)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(faceOf.At(i), hornFace.At(next, previous, i), baseValues.At(i), dimension)
				}))

			product := a.TermAs[A]("X.d(n + 2, n - 1, v)")
			productIn := a.Have(
				"the face n − 1 of v is an (n+1)-simplex",
				"X.d(n + 2, n - 1, v) ∈ X.simplices(n + 1)",
				ByArith(simplicial_set.FaceIn.Read(simplicial).At(next, previous, v), vIn, dimension))
			productBelow := a.Have(
				"whose faces below n − 1 are the base simplex",
				"∀i:num. i + 1 < n ⇒ X.d(n + 1, i, X.d(n + 2, n - 1, v)) = base_simplex(x₀, n)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					below := b.Assume()
					notBelowTwoDown := b.Unless(
						b.Term("i + 2 < n"),
						"below n − 2 the face i of v is the base simplex, and the face n − 1 of v inherits it",
						Given(func(c *Argument, belowTwoDown Fact) {
							c.Show(
								"so the face i of the face n − 1 of v is the base simplex",
								ByArith(baseInherited.At(x0, n, i, previous, v), vertex, vIn, vBelow.At(i), belowTwoDown))
						}))
					at := b.Have(
						"otherwise i is n − 2",
						"i = n - 2",
						ByArith(below, notBelowTwoDown))
					identity := b.Have(
						"the face i of the face n − 1 of v is the face n − 2 of "+
							"its face i, by the face identity at the pair (i, n − 1)",
						"X.d(n + 1, i, X.d(n + 2, n - 1, v)) = X.d(n + 1, n - 2, X.d(n + 2, i, v))",
						ByArith(face.At(n, i, previous, v), vIn, below, shift))
					vAtTwoDown := b.Have(
						"where the face of v is s(n, n, x)",
						"X.d(n + 2, n - 2, v) = X.s(n, n, x)",
						ByArith(faceOf.At(twoDown), hornFace.At(next, previous, twoDown), values, dimension, two))
					b.Show(
						"whose face n − 2 is the base simplex, so the face i of the face n − 1 of v is the base simplex",
						ByArith(identity, at, vAtTwoDown, sNAway.At(twoDown), two))
				}))
			productAtPrevious := a.Have(
				"its face n − 1 is y",
				"X.d(n + 1, n - 1, X.d(n + 2, n - 1, v)) = y",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n - 1, X.d(n + 2, n, v))"),
						"the face identity at the pair (n − 1, n)",
						ByArith(face.At(n, previous, n, v), vIn, shift)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n - 1, X.s(n, n - 1, y))"),
						"the face n of v is s(n, n − 1, y)",
						ByArith(faceOf.At(n), hornFace.At(next, previous, n), values, dimension, two)),
					FinalLeg(
						"whose face n − 1 is y",
						By(sPreviousAtPrevious)),
				))
			productAtN := a.Have(
				"its face n is the face n − 1 of t",
				"X.d(n + 1, n, X.d(n + 2, n - 1, v)) = X.d(n + 1, n - 1, t)",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n - 1, X.d(n + 2, n + 1, v))"),
						"the face identity at the pair (n − 1, n + 1)",
						ByArith(face.At(n, previous, next, v), vIn, shift)),
					FinalLeg(
						"the face n + 1 of v is t",
						ByArith(faceOf.At(next), hornFace.At(next, previous, next), values, dimension)),
				))
			productAtNext := a.Have(
				"and its face n + 1 is x",
				"X.d(n + 1, n + 1, X.d(n + 2, n - 1, v)) = x",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n - 1, X.d(n + 2, n + 2, v))"),
						"the face identity at the pair (n − 1, n + 2)",
						ByArith(face.At(n, previous, top, v), vIn, shift)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n - 1, X.s(n, n - 2, x))"),
						"the face n + 2 of v is s(n, n − 2, x)",
						ByArith(faceOf.At(top), hornFace.At(next, previous, top), values, dimension)),
					FinalLeg(
						"whose face n − 1 is x",
						By(sTwoDownAtPrevious)),
				))
			a.Show(
				"so the face n − 1 of v is a product filler for x "+
					"and y, and MulClass reads the product at its face n",
				By(
					MulClass.Read(kan).At(x0, n, x, y, product),
					vertex,
					shift,
					xSphere,
					ySphere,
					productIn,
					productBelow,
					productAtNext,
					productAtPrevious,
					productAtN))
		}),
})}

// Commutative — for 2 ≤ n the product commutes. With C and C' the
// classes of spheres x and y, a product filler w for y and x has a face
// n whose class is the product of C' and C (MulClass), and an
// (n+1)-simplex u holds x at its faces n − 2 and n − 1 and y at n and
// n + 1 (JuxtapositionExists). The horn of dimension n + 2 missing the
// face n + 1, with s(n, n − 1, x) at n − 2, w at n − 1, u at n,
// s(n, n − 1, y) at n + 2 and the base simplex below, is compatible; the
// face n + 1 of a filler holds x at n − 2, the face n of w at n − 1, y at
// n and the base simplex at n + 1, so MulClassLower reads the face n of
// w as a representative of the product of C and C' too.
var Commutative = commutativeThm{family.Add(registry.ProofEntry{
	Name: "Commutative",
	Key:  "prop_7a7969052afeb458",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀C C':set(A).",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"2 ≤ n",
			"C ∈ simplicial_homotopy_group(x₀, n) ∧ C' ∈ simplicial_homotopy_group(x₀, n)",
		},
		Conclusion: "simplicial_homotopy_mul(x₀, n, C, C') = simplicial_homotopy_mul(x₀, n, C', C)",
	},
		func(
			a *Argument,
			kan Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			standing Fact,
			C, CPrime *Expr[Set[A]],
			classes Fact,
		) {
			simplicial := kan_complex.KanSimplicialSet.Read(kan)
			face := simplicial_set.FaceFace.Read(simplicial)
			baseFace := simplicial_set.BaseSimplexFace.Read(simplicial)
			baseInherited := simplicial_set.BaseSimplexFaceInherited.Read(simplicial)
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is at least 2")
			vertex, two := hypotheses[0], hypotheses[1]
			inGroup := a.Conjuncts(
				classes,
				"C is a class of πₙ",
				"and so is C'")
			x, xClass := a.ObtainAs[A](
				"C is the class of a sphere x",
				"∃x:A. x ∈ simplicial_sphere(x₀, n) ∧ C = equivalence_class(simplicial_homotopic(x₀, n), x)",
				By(inGroup[0], InHomotopyGroup.Read(simplicial).At(x0, n, C), vertex))
			y, yClass := a.ObtainAs[A](
				"and C' the class of a sphere y",
				"∃y:A. y ∈ simplicial_sphere(x₀, n) ∧ C' = equivalence_class(simplicial_homotopic(x₀, n), y)",
				By(inGroup[1], InHomotopyGroup.Read(simplicial).At(x0, n, CPrime), vertex))
			xParts := a.Conjuncts(
				xClass,
				"x is a sphere",
				"whose class is C")
			yParts := a.Conjuncts(
				yClass,
				"y is a sphere",
				"whose class is C'")
			xSphere, ofC := xParts[0], xParts[1]
			ySphere, ofCPrime := yParts[0], yParts[1]
			twoDown, previous := a.TermAs[Nat]("n - 2"), a.TermAs[Nat]("n - 1")
			next, top := a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("n + 2")
			shift := a.Have(
				"2 ≤ n makes n positive, n − 2 and n − 1 at most n, and (n − 1) + 1 = n",
				"0 < n ∧ n - 2 ≤ n ∧ n - 1 ≤ n ∧ n - 1 + 1 = n",
				ByArith(two))

			w, wFills := a.ObtainAs[A](
				"y and x have a product filler w",
				"∃w:A. "+
					"    w ∈ X.simplices(n + 1) ∧ "+
					"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ "+
					"    X.d(n + 1, n + 1, w) = y ∧ "+
					"    X.d(n + 1, n - 1, w) = x",
				By(ProductFillerExists.Read(kan).At(x0, n, y, x), vertex, shift, ySphere, xSphere))
			wParts := a.Conjuncts(
				wFills,
				"w is an (n+1)-simplex",
				"whose faces below n − 1 are the base simplex",
				"y is its face n + 1",
				"and x its face n − 1")
			wIn, wBelow, wAtNext, wAtPrevious := wParts[0], wParts[1], wParts[2], wParts[3]

			_, uFills := a.ObtainAs[A](
				"x and y lie side by side in an (n+1)-simplex u",
				"∃u:A. "+
					"    u ∈ X.simplices(n + 1) ∧ "+
					"    (∀i:num. i + 2 < n ⇒ X.d(n + 1, i, u) = base_simplex(x₀, n)) ∧ "+
					"    X.d(n + 1, n - 2, u) = x ∧ "+
					"    X.d(n + 1, n - 1, u) = x ∧ "+
					"    X.d(n + 1, n, u) = y ∧ "+
					"    X.d(n + 1, n + 1, u) = y",
				By(JuxtapositionExists.Read(kan).At(x0, n, x, y), vertex, two, xSphere, ySphere))
			uParts := a.Conjuncts(
				uFills,
				"u is an (n+1)-simplex",
				"whose faces below n − 2 are the base simplex",
				"x is its face n − 2",
				"and its face n − 1",
				"y is its face n",
				"and its face n + 1")
			uIn, uBelow, uAtTwoDown, uAtPrevious, uAtN, uAtNext :=
				uParts[0], uParts[1], uParts[2], uParts[3], uParts[4], uParts[5]

			sX := a.Conjuncts(
				a.Have(
					"the face table of the degeneracy s(n, n − 1, x) of the sphere x",
					"X.s(n, n - 1, x) ∈ X.simplices(n + 1) ∧ "+
						"X.d(n + 1, n - 1, X.s(n, n - 1, x)) = x ∧ "+
						"X.d(n + 1, n, X.s(n, n - 1, x)) = x ∧ "+
						"(∀i:num. "+
						"    i ≤ n + 1 ∧ ¬(i = n - 1) ∧ ¬(i = n) ⇒ X.d(n + 1, i, X.s(n, n - 1, x)) = base_simplex(x₀, n))",
					ByArith(SphereDegeneracyFaces.Read(simplicial).At(x0, n, x, previous), vertex, xSphere, shift)),
				"s(n, n − 1, x) is an (n+1)-simplex",
				"whose face n − 1 is x",
				"as is its face n",
				"and whose other faces are the base simplex")
			sY := a.Conjuncts(
				a.Have(
					"and that of the degeneracy s(n, n − 1, y) of the sphere y",
					"X.s(n, n - 1, y) ∈ X.simplices(n + 1) ∧ "+
						"X.d(n + 1, n - 1, X.s(n, n - 1, y)) = y ∧ "+
						"X.d(n + 1, n, X.s(n, n - 1, y)) = y ∧ "+
						"(∀i:num. "+
						"    i ≤ n + 1 ∧ ¬(i = n - 1) ∧ ¬(i = n) ⇒ X.d(n + 1, i, X.s(n, n - 1, y)) = base_simplex(x₀, n))",
					ByArith(SphereDegeneracyFaces.Read(simplicial).At(x0, n, y, previous), vertex, ySphere, shift)),
				"s(n, n − 1, y) is an (n+1)-simplex",
				"whose face n − 1 is y",
				"as is its face n",
				"and whose other faces are the base simplex")
			sXIn, sXAtPrevious, sXAtN, sXAway := sX[0], sX[1], sX[2], sX[3]
			sYIn, sYAtPrevious, sYAtN, sYAway := sY[0], sY[1], sY[2], sY[3]

			f, fDef := a.LetAs[Fun[Nat, A]](
				"f",
				"λi:num. "+
					"    COND(i + 2 < n, "+
					"        base_simplex(x₀, n + 1), "+
					"        COND(i = n - 2, X.s(n, n - 1, x), COND(i = n - 1, w, COND(i = n, u, X.s(n, n - 1, y)))))")
			members := a.Have(
				"every member of f is an (n+1)-simplex",
				"∀i:num. f(i) ∈ X.simplices(n + 1)",
				fDef.Rw(),
				By(sXIn, sYIn, wIn, uIn, simplicial_set.BaseSimplexIn.Read(simplicial).At(x0, next), vertex))
			values := a.Have(
				"f is s(n, n − 1, x) at n − 2, w at n − 1, u at n and s(n, n − 1, y) at n + 2",
				"f(n - 2) = X.s(n, n - 1, x) ∧ f(n - 1) = w ∧ f(n) = u ∧ f(n + 2) = X.s(n, n - 1, y)",
				fDef.Rw(),
				ByArith(two))
			baseValues := a.Have(
				"and the base simplex below n − 2",
				"∀i:num. i + 2 < n ⇒ f(i) = base_simplex(x₀, n + 1)",
				fDef.Rw(),
				a.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
			hornFace := kan_complex.HornFacesMember
			compatible := a.Have(
				"and f is compatible on the faces of the horn missing the face n + 1",
				"faces_compatible(n + 1, horn_faces(n + 1, n + 1), f)",
				Simp(Fwd(simplicial_set.FacesCompatibleDef)),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					j := b.FixAs[Nat]()
					faces := b.Assume()
					pair := b.Have(
						"i < j are faces of the horn: j is at most n + 2, and neither is n + 1",
						"i < j ∧ j ≤ n + 1 + 1 ∧ ¬(i = n + 1) ∧ ¬(j = n + 1)",
						By(hornFace.At(next, next, i), hornFace.At(next, next, j), faces))
					jPrevious := b.TermAs[Nat]("j - 1")
					shifts := b.Have(
						"one below n − 1 is n − 2, and one below n + 2 is n + 1",
						"n - 1 - 1 = n - 2 ∧ n + 2 - 1 = n + 1",
						ByArith())
					notBelow := b.Unless(
						b.Term("i + 2 < n"),
						"below n − 2 the member at i is the base simplex, and every member has the base simplex there",
						Given(func(c *Argument, below Fact) {
							indices := c.Have(
								"i and j − 1 index faces of an (n+1)-simplex",
								"i ≤ n + 1 ∧ j - 1 ≤ n + 1",
								ByArith(below, pair))
							c.Show(
								"so whichever member stands at j, both faces are the base simplex",
								fDef.Rw(),
								CondRewrite(),
								ByArith(
									below,
									indices,
									vertex,
									baseFace.At(x0, n, i),
									baseFace.At(x0, n, jPrevious),
									sXAway.At(i),
									wBelow.At(i),
									uBelow.At(i),
									sYAway.At(i)))
						}))
					notTwoDown := b.Unless(
						b.Term("i = n - 2"),
						"with i = n − 2, the member there is s(n, n − 1, x) and j is n − 1, n or n + 2",
						Given(func(c *Argument, atTwoDown Fact) {
							jNotPrevious := c.Unless(
								c.Term("j = n - 1"),
								"at the pair (n − 2, n − 1): the face n − 2 of w and "+
									"the face n − 2 of s(n, n − 1, x) are the base simplex",
								Given(func(e *Argument, jAtPrevious Fact) {
									e.Show(
										"so both faces are the base simplex",
										atTwoDown.Rw(),
										jAtPrevious.Rw(),
										ByArith(shifts, values, wBelow.At(twoDown), sXAway.At(twoDown), two))
								}))
							jNotN := c.Unless(
								c.Term("j = n"),
								"at the pair (n − 2, n): the face n − 2 of u and the face n − 1 of s(n, n − 1, x) are x",
								Given(func(e *Argument, jAtN Fact) {
									e.Show(
										"so both faces are x",
										atTwoDown.Rw(),
										jAtN.Rw(),
										By(Normalized, values, uAtTwoDown, sXAtPrevious))
								}))
							jAtTop := c.Have(
								"so j is n + 2",
								"j = n + 2",
								ByArith(pair, atTwoDown, jNotPrevious, jNotN))
							c.Show(
								"at the pair (n − 2, n + 2) the face n − 2 of s(n, n − 1, "+
									"y) and the face n + 1 of s(n, n − 1, x) are the base simplex",
								atTwoDown.Rw(),
								jAtTop.Rw(),
								ByArith(shifts, values, sYAway.At(twoDown), sXAway.At(next), two))
						}))
					notPrevious := b.Unless(
						b.Term("i = n - 1"),
						"with i = n − 1, the member there is w and j is n or n + 2",
						Given(func(c *Argument, atPrevious Fact) {
							jNotN := c.Unless(
								c.Term("j = n"),
								"at the pair (n − 1, n): the face n − 1 of u and the face n − 1 of w are x",
								Given(func(e *Argument, jAtN Fact) {
									e.Show(
										"so both faces are x",
										atPrevious.Rw(),
										jAtN.Rw(),
										By(Normalized, values, uAtPrevious, wAtPrevious))
								}))
							jAtTop := c.Have(
								"so j is n + 2",
								"j = n + 2",
								ByArith(pair, atPrevious, jNotN))
							c.Show(
								"at the pair (n − 1, n + 2) the face n − 1 of s(n, n − 1, y) and the face n + 1 of w are y",
								atPrevious.Rw(),
								jAtTop.Rw(),
								By(shifts, values, sYAtPrevious, wAtNext))
						}))
					remaining := b.Conjuncts(
						b.Have(
							"the one pair left is (n, n + 2)",
							"i = n ∧ j = n + 2",
							ByArith(notBelow, notTwoDown, notPrevious, pair)),
						"i is n",
						"j is n + 2")
					b.Show(
						"where the face n of s(n, n − 1, y) and the face n + 1 of u are y",
						remaining[0].Rw(),
						remaining[1].Rw(),
						By(shifts, values, sYAtN, uAtNext))
				}))
			horn := a.Have(
				"so f is a horn of X missing the face n + 1",
				"face_family(n + 1, horn_faces(n + 1, n + 1), f)",
				Unfold(simplicial_set.FaceFamilyDef),
				By(members, compatible))
			dimension := a.Have(
				"the horn has dimension (n + 1) + 1 = n + 2, and the missing face n + 1 is one of its faces",
				"n + 1 + 1 = n + 2 ∧ n + 1 ≤ n + 1 + 1",
				ByArith())

			v, filled := a.ObtainAs[A](
				"so the horn f has a filler v, an (n+2)-simplex of X",
				"∃v:A. v ∈ X.simplices(n + 2) ∧ faces_filler(n + 1, horn_faces(n + 1, n + 1), f, v)",
				By(kan_complex.KanFill.Read(kan).At(next, next, f), horn, dimension))
			filling := a.Conjuncts(
				filled,
				"v is an (n+2)-simplex",
				"whose faces other than n + 1 are the members of f")
			vIn, faceOf := filling[0], a.Unfolded(filling[1], simplicial_set.FacesFillerDef)
			vBelow := a.Have(
				"and the faces of v below n − 2 are the base simplex",
				"∀i:num. i + 2 < n ⇒ X.d(n + 2, i, v) = base_simplex(x₀, n + 1)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(faceOf.At(i), hornFace.At(next, next, i), baseValues.At(i), dimension)
				}))

			t := a.TermAs[A]("X.d(n + 2, n + 1, v)")
			tIn := a.Have(
				"the face n + 1 of v is an (n+1)-simplex",
				"X.d(n + 2, n + 1, v) ∈ X.simplices(n + 1)",
				ByArith(simplicial_set.FaceIn.Read(simplicial).At(next, next, v), vIn, dimension))
			tBelow := a.Have(
				"whose faces below n − 2 are the base simplex, as those of v are",
				"∀i:num. i + 2 < n ⇒ X.d(n + 1, i, X.d(n + 2, n + 1, v)) = base_simplex(x₀, n)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return ByArith(baseInherited.At(x0, n, i, next, v), vertex, vIn, vBelow.At(i))
				}))
			tAtTwoDown := a.Have(
				"its face n − 2 is x",
				"X.d(n + 1, n - 2, X.d(n + 2, n + 1, v)) = x",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.d(n + 2, n - 2, v))"),
						"the face identity at the pair (n − 2, n + 1)",
						ByArith(face.At(n, twoDown, next, v), vIn, shift)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.s(n, n - 1, x))"),
						"the face n − 2 of v is s(n, n − 1, x)",
						ByArith(faceOf.At(twoDown), hornFace.At(next, next, twoDown), values, dimension, two)),
					FinalLeg(
						"whose face n is x",
						By(sXAtN)),
				))
			tAtPrevious := a.Have(
				"its face n − 1 is the face n of w",
				"X.d(n + 1, n - 1, X.d(n + 2, n + 1, v)) = X.d(n + 1, n, w)",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.d(n + 2, n - 1, v))"),
						"the face identity at the pair (n − 1, n + 1)",
						ByArith(face.At(n, previous, next, v), vIn, shift)),
					FinalLeg(
						"the face n − 1 of v is w",
						ByArith(faceOf.At(previous), hornFace.At(next, next, previous), values, dimension, two)),
				))
			tAtN := a.Have(
				"its face n is y",
				"X.d(n + 1, n, X.d(n + 2, n + 1, v)) = y",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n, X.d(n + 2, n, v))"),
						"the face identity at the pair (n, n + 1)",
						ByArith(face.At(n, n, next, v), vIn)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n, u)"),
						"the face n of v is u",
						ByArith(faceOf.At(n), hornFace.At(next, next, n), values, dimension)),
					FinalLeg(
						"whose face n is y",
						By(uAtN)),
				))
			tAtNext := a.Have(
				"and its face n + 1 is the base simplex",
				"X.d(n + 1, n + 1, X.d(n + 2, n + 1, v)) = base_simplex(x₀, n)",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, X.d(n + 2, n + 2, v))"),
						"the face identity at the pair (n + 1, n + 2)",
						ByArith(face.At(n, next, top, v), vIn)),
					Leg(
						a.TermAs[A]("X.d(n + 1, n + 1, X.s(n, n - 1, y))"),
						"the face n + 2 of v is s(n, n − 1, y)",
						ByArith(faceOf.At(top), hornFace.At(next, next, top), values, dimension)),
					FinalLeg(
						"whose face n + 1 is the base simplex",
						ByArith(sYAway.At(next))),
				))

			a.Show(
				"so both products are the class of the face n of w",
				CalcEq(
					Leg(
						a.TermAs[Set[A]](
							"simplicial_homotopy_mul(x₀, "+
								"    n, "+
								"    equivalence_class(simplicial_homotopic(x₀, n), x), "+
								"    equivalence_class(simplicial_homotopic(x₀, n), y))"),
						"C and C' are the classes of x and y",
						By(Normalized, ofC, ofCPrime)),
					Leg(
						a.TermAs[Set[A]](
							"equivalence_class(simplicial_homotopic(x₀, n), X.d(n + 1, n - 1, X.d(n + 2, n + 1, v)))"),
						"MulClassLower reads the product of the classes of x and y at the face n − 1 of t",
						By(
							MulClassLower.Read(kan).At(x0, n, x, y, t),
							vertex,
							two,
							xSphere,
							ySphere,
							tIn,
							tBelow,
							tAtTwoDown,
							tAtN,
							tAtNext)),
					Leg(
						a.TermAs[Set[A]]("equivalence_class(simplicial_homotopic(x₀, n), X.d(n + 1, n, w))"),
						"which is the face n of w",
						By(tAtPrevious)),
					Leg(
						a.TermAs[Set[A]](
							"simplicial_homotopy_mul(x₀, "+
								"    n, "+
								"    equivalence_class(simplicial_homotopic(x₀, n), y), "+
								"    equivalence_class(simplicial_homotopic(x₀, n), x))"),
						"MulClass reads the product of the classes of y and x at w",
						By(
							MulClass.Read(kan).At(x0, n, y, x, w),
							vertex,
							shift,
							ySphere,
							xSphere,
							wIn,
							wBelow,
							wAtNext,
							wAtPrevious)),
					FinalLeg(
						"C' and C are the classes of y and x",
						By(Normalized, ofC, ofCPrime)),
				))
		}),
})}

// AbelianGroupOn — for 2 ≤ n the classes form an abelian group on a set.
// Unfolded, an abelian group is a group whose product commutes on its
// carrier: πₙ is a group by GroupOn, the dimension being positive as it
// is at least 2, and its product commutes by Commutative.
var AbelianGroupOn = abelianGroupOnThm{family.Add(registry.ProofEntry{
	Name: "AbelianGroupOn",
	Key:  "prop_952dbd57873c4fe9",
	Build: kan_complex.KanComplex.Law(Statement{
		Binders: "∀x₀:A. ∀n:num.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"2 ≤ n",
		},
		Conclusion: "abelian_group_on(mk_group(simplicial_homotopy_mul(x₀, n), " +
			"        simplicial_homotopy_unit(x₀, n), " +
			"        simplicial_homotopy_inv(x₀, n), " +
			"        simplicial_homotopy_group(x₀, n)))",
	},
		func(a *Argument, kan Fact, x0 *Expr[A], n *Expr[Nat], standing Fact) {
			hypotheses := a.Conjuncts(
				standing,
				"x₀ is a vertex of X",
				"and n is at least 2")
			vertex, two := hypotheses[0], hypotheses[1]

			a.Show(
				"unfolded, πₙ is a group, n being positive, and its product commutes",
				Unfold(abelian_group.AbelianGroupOn),
				ByArith(GroupOn.Read(kan), Commutative.Read(kan), vertex, two))
		}),
})}

// ---------------------------------------------------------------------------
// The map a simplicial map induces
// ---------------------------------------------------------------------------

// MapSphere — a simplicial map carries spheres to spheres at the image
// vertex. The image of the n-simplex x is an n-simplex of Y (MapIn); for
// 0 < n its face i is the image of the face i of x (MapFace at n − 1),
// which is the base simplex at x₀, and the map carries that to the base
// simplex at F(0, x₀) (MapBaseSimplex).
var MapSphere = mapSphereThm{family.Add(registry.ProofEntry{
	Name: "MapSphere",
	Key:  "prop_54d5ec644269ad31",
	Build: simplicial_set.SimplicialMap.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"x ∈ simplicial_sphere(X, x₀, n)",
		},
		Conclusion: "F(n, x) ∈ simplicial_sphere(Y, F(0, x₀), n)",
	},
		func(a *Argument, mapping Fact, x0 *Expr[A], n *Expr[Nat], x *Expr[A], vertex, xSphere Fact) {
			previous := a.TermAs[Nat]("n - 1")
			sphere := a.Conjuncts(
				a.Unfolded(xSphere, SimplicialSphereDef),
				"x is an n-simplex of X",
				"every face of which is the base simplex at x₀")
			xIn, xFaces := sphere[0], sphere[1]
			imageIn := a.Have(
				"so its image is an n-simplex of Y",
				"F(n, x) ∈ Y.simplices(n)",
				By(simplicial_set.MapIn.Read(mapping).At(n, x), xIn))
			imageFaces := a.Have(
				"and every face of the image is the base simplex at F(0, x₀)",
				"∀i:num. i ≤ n ∧ 0 < n ⇒ Y.d(n, i, F(n, x)) = base_simplex(F(0, x₀), n - 1)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					position := b.Assume()
					shift := b.Have(
						"n, being positive, is (n − 1) + 1",
						"n - 1 + 1 = n",
						ByArith(position))
					b.Show(
						"so the face i of F(n, x) is the base simplex at F(0, x₀)",
						CalcEq(
							Leg(
								b.TermAs[B]("F(n - 1, X.d(n, i, x))"),
								"F commutes with the face i",
								ByArith(simplicial_set.MapFace.Read(mapping).At(previous, i, x), xIn, shift, position)),
							Leg(
								b.TermAs[B]("F(n - 1, base_simplex(x₀, n - 1))"),
								"the face i of the sphere x is the base simplex at x₀",
								By(xFaces.At(i), position)),
							FinalLeg(
								"which F carries to the base simplex at F(0, x₀)",
								By(simplicial_set.MapBaseSimplex.Read(mapping).At(x0, previous), vertex)),
						))
				}))
			a.Show(
				"so F(n, x) is a sphere at F(0, x₀)",
				Unfold(SimplicialSphereDef),
				BySets(imageIn, imageFaces))
		}),
})}

// MapHomotopic — and homotopies to homotopies: the image F(n + 1, h) of a
// homotopy h from x to y is an (n+1)-simplex of Y whose faces are the
// images of the faces of h, so its faces n and n + 1 are F(n, x) and
// F(n, y), and below n the image of the base simplex at x₀, which is the
// base simplex at F(0, x₀).
var MapHomotopic = mapHomotopicThm{family.Add(registry.ProofEntry{
	Name: "MapHomotopic",
	Key:  "prop_4066a72e4caea40b",
	Build: simplicial_set.SimplicialMap.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x y:A.",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"simplicial_homotopic(X, x₀, n, x, y)",
		},
		Conclusion: "simplicial_homotopic(Y, F(0, x₀), n, F(n, x), F(n, y))",
	},
		func(a *Argument, mapping Fact, x0 *Expr[A], n *Expr[Nat], x, y *Expr[A], vertex, homotopic Fact) {
			face := simplicial_set.MapFace.Read(mapping)
			next := a.TermAs[Nat]("n + 1")

			h, byH := a.UnpackAs[A](a.Unfolded(homotopic, SimplicialHomotopicDef), "h")
			hParts := a.Conjuncts(
				byH,
				"h is an (n+1)-simplex of X",
				"whose faces below n are the base simplex",
				"whose face n is x",
				"and whose face n + 1 is y")
			hIn, hBelow, hAtN, hAtNext := hParts[0], hParts[1], hParts[2], hParts[3]
			image := a.TermAs[B]("F(n + 1, h)")

			imageIn := a.Have(
				"its image F(n + 1, h) is an (n+1)-simplex of Y",
				"F(n + 1, h) ∈ Y.simplices(n + 1)",
				By(simplicial_set.MapIn.Read(mapping).At(next, h), hIn))
			imageBelow := a.Have(
				"below n the faces of the image are the base simplex at F(0, x₀)",
				"∀i:num. i < n ⇒ Y.d(n + 1, i, F(n + 1, h)) = base_simplex(F(0, x₀), n)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					below := b.Assume()
					b.Show(
						"the face i of the image is the image of the base simplex at x₀",
						CalcEq(
							Leg(
								b.TermAs[B]("F(n, X.d(n + 1, i, h))"),
								"F commutes with the face i, as i < n ≤ n + 1",
								ByArith(face.At(n, i, h), hIn, below)),
							Leg(
								b.TermAs[B]("F(n, base_simplex(x₀, n))"),
								"the face i of h is the base simplex, i being below n",
								By(hBelow.At(i), below)),
							FinalLeg(
								"which F carries to the base simplex at F(0, x₀)",
								By(simplicial_set.MapBaseSimplex.Read(mapping).At(x0, n), vertex)),
						))
				}))
			imageAtN := a.Have(
				"its face n is the image of the face n of h, which is F(n, x)",
				"Y.d(n + 1, n, F(n + 1, h)) = F(n, x)",
				ByArith(face.At(n, n, h), hIn, hAtN))
			imageAtNext := a.Have(
				"and its face n + 1 the image of the face n + 1 of h, which is F(n, y)",
				"Y.d(n + 1, n + 1, F(n + 1, h)) = F(n, y)",
				ByArith(face.At(n, next, h), hIn, hAtNext))
			a.Do(Simp(Fwd(SimplicialHomotopicDef)))
			a.Take(image)
			a.Show(
				"so F(n + 1, h) is a homotopy in Y from F(n, x) to F(n, y)",
				By(imageIn, imageBelow, imageAtN, imageAtNext))
		}),
})}

// HomotopyMapClass — the induced map sends the class of a sphere to
// the class of its image: well defined. x is homotopic to the point the
// map chooses in its class, which is then a sphere, and the map carries
// that homotopy to one in Y, where homotopic spheres share a class.
var HomotopyMapClass = homotopyMapClassThm{family.Add(registry.ProofEntry{
	Name:    "HomotopyMapClass",
	Reading: "Only the target need be Kan: it is read by ClassEqIff in Y.",
	Key:     "prop_5bb7892f6fa4c5db",
	Build: simplicial_set.SimplicialMap.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀x:A.",
		Hypotheses: []string{
			"kan_complex(Y)",
			"x₀ ∈ X.simplices(0)",
			"x ∈ simplicial_sphere(X, x₀, n)",
		},
		Conclusion: "simplicial_homotopy_map(X, " +
			"    Y, " +
			"    F, " +
			"    x₀, " +
			"    n, " +
			"    equivalence_class(simplicial_homotopic(X, x₀, n), x)) = " +
			"equivalence_class(simplicial_homotopic(Y, F(0, x₀), n), F(n, x))",
	},
		func(a *Argument, mapping Fact, x0 *Expr[A], n *Expr[Nat], x *Expr[A], kan, vertex, xSphere Fact) {
			source := simplicial_set.MapSource.Read(mapping)
			X := a.TermAs[simplicial_set.SimplicialOps[A]]("X")
			Y := a.TermAs[simplicial_set.SimplicialOps[B]]("Y")
			F := a.TermAs[Fun2[Nat, A, B]]("F")
			classX := a.TermAs[Set[A]]("equivalence_class(simplicial_homotopic(X, x₀, n), x)")

			homotopic := a.TermAs[Fun2[A, A, Bool]]("simplicial_homotopic(X, x₀, n)")
			xPrime, xPrimeDef := a.LetAs[A](
				"x'", "εz:A. z ∈ equivalence_class(simplicial_homotopic(X, x₀, n), x)")
			toXPrime := a.Have(
				"x is homotopic to itself, so to the point x' chosen in its class",
				"simplicial_homotopic(X, x₀, n, x, x')",
				xPrimeDef.Rw(),
				By(
					HomotopicRefl.Read(source).At(x0, n, x),
					vertex,
					xSphere,
					equivalence.ChosenRepresentative.At(homotopic, x)))
			xPrimeSphere := a.Have(
				"a simplex homotopic to a sphere is a sphere: so is x'",
				"x' ∈ simplicial_sphere(X, x₀, n)",
				By(HomotopicSphere.Read(source).At(x0, n, x, xPrime), vertex, toXPrime, xSphere))

			y0 := a.TermAs[B]("F(0, x₀)")
			image, imagePrime := a.TermAs[B]("F(n, x)"), a.TermAs[B]("F(n, x')")
			baseVertex := a.Have(
				"F(0, x₀) is a vertex of Y",
				"F(0, x₀) ∈ Y.simplices(0)",
				By(simplicial_set.MapIn.Read(mapping).At(a.TermAs[Nat]("0"), x0), vertex))
			imageHomotopic := a.Have(
				"F carries the homotopy from x to x' to one from F(n, x) to F(n, x')",
				"simplicial_homotopic(Y, F(0, x₀), n, F(n, x), F(n, x'))",
				By(MapHomotopic.Read(mapping).At(x0, n, x, xPrime), vertex, toXPrime))
			imageSpheres := a.Have(
				"and the spheres x and x' to spheres of Y at the vertex F(0, x₀)",
				"F(n, x) ∈ simplicial_sphere(Y, F(0, x₀), n) ∧ F(n, x') ∈ simplicial_sphere(Y, F(0, x₀), n)",
				By(
					MapSphere.Read(mapping).At(x0, n, x),
					MapSphere.Read(mapping).At(x0, n, xPrime),
					vertex,
					xSphere,
					xPrimeSphere))

			a.Show(
				"the induced map gives the class of the image of x', which is that of the image of x",
				CalcEq(
					Leg(
						a.TermAs[Set[B]]("equivalence_class(simplicial_homotopic(Y, F(0, x₀), n), F(n, x'))"),
						"the induced map reads the class of x through the point x' chosen in it",
						By(SimplicialHomotopyMapDef.At(X, Y, F, x0, n, classX), xPrimeDef)),
					FinalLeg(
						"F(n, x') and F(n, x) are homotopic spheres of the Kan "+
							"complex Y at its vertex F(0, x₀), so they share a class",
						By(ClassEqIff.Read(kan).At(y0, n, image, imagePrime), baseVertex, imageSpheres, imageHomotopic)),
				))
		}),
})}

// HomotopyMapIn — the induced map carries πₙ(X, x₀) into πₙ(Y, F(0, x₀)):
// the point the map chooses in the class of a sphere x is one x is
// homotopic to, so a sphere, and its image is a sphere of Y.
var HomotopyMapIn = homotopyMapInThm{family.Add(registry.ProofEntry{
	Name: "HomotopyMapIn",
	Reading: "No Kan condition is read: the image is the class of the image " +
		"of the chosen point, a sphere of Y, and no two classes are compared.",
	Key: "prop_72f978df5a6c61cd",
	Build: simplicial_set.SimplicialMap.Law(Statement{
		Binders: "∀x₀:A. ∀n:num. ∀C:set(A).",
		Hypotheses: []string{
			"x₀ ∈ X.simplices(0)",
			"C ∈ simplicial_homotopy_group(X, x₀, n)",
		},
		Conclusion: "simplicial_homotopy_map(X, Y, F, x₀, n, C) ∈ " +
			"simplicial_homotopy_group(Y, F(0, x₀), n)",
	},
		func(a *Argument, mapping Fact, x0 *Expr[A], n *Expr[Nat], C *Expr[Set[A]], vertex, inGroup Fact) {
			source := simplicial_set.MapSource.Read(mapping)
			target := simplicial_set.MapTarget.Read(mapping)
			X := a.TermAs[simplicial_set.SimplicialOps[A]]("X")
			Y := a.TermAs[simplicial_set.SimplicialOps[B]]("Y")
			F := a.TermAs[Fun2[Nat, A, B]]("F")
			homotopic := a.TermAs[Fun2[A, A, Bool]]("simplicial_homotopic(X, x₀, n)")
			x, represented := a.ObtainAs[A](
				"C is the class of a sphere x",
				"∃x:A. x ∈ simplicial_sphere(X, x₀, n) ∧ C = equivalence_class(simplicial_homotopic(X, x₀, n), x)",
				By(vertex, inGroup, InHomotopyGroup.Read(source).At(x0, n, C)))
			parts := a.Conjuncts(
				represented,
				"x is a sphere",
				"C is its class")
			xSphere, class := parts[0], parts[1]
			c, chosen := a.LetAs[A]("c", "εz:A. z ∈ C")
			toC := a.Have(
				"x is homotopic to the point c chosen in its class",
				"simplicial_homotopic(X, x₀, n, x, c)",
				chosen.Rw(),
				class.Rw(),
				By(
					vertex,
					xSphere,
					HomotopicRefl.Read(source).At(x0, n, x),
					equivalence.ChosenRepresentative.At(homotopic, x)))
			cSphere := a.Have(
				"the chosen point is a sphere because it is homotopic to x",
				"c ∈ simplicial_sphere(X, x₀, n)",
				By(vertex, xSphere, toC, HomotopicSphere.Read(source).At(x0, n, x, c)))
			a.Show(
				"F carries c to a sphere at its image vertex, whose class is the induced image of C",
				By(
					chosen,
					cSphere,
					vertex,
					SimplicialHomotopyMapDef.At(X, Y, F, x0, n, C),
					ClassInHomotopyGroup.Read(target).At(a.TermAs[B]("F(0, x₀)"), n, a.TermAs[B]("F(n, c)")),
					MapSphere.Read(mapping).At(x0, n, c),
					simplicial_set.MapIn.Read(mapping).At(a.TermAs[Nat]("0"), x0)))
		}),
})}

// HomotopyMapHom — for 0 < n the induced map is a group homomorphism:
// the image of a product filler is a product filler.
var HomotopyMapHom = homotopyMapHomThm{family.Add(registry.ProofEntry{
	Name: "HomotopyMapHom",
	Key:  "prop_9f4b792583046307",
	Build: simplicial_set.SimplicialMap.Law(Statement{
		Binders: "∀x₀:A. ∀n:num.",
		Hypotheses: []string{
			"kan_complex(X)",
			"kan_complex(Y)",
			"x₀ ∈ X.simplices(0)",
			"0 < n",
		},
		Conclusion: "group_homomorphism(mk_group(simplicial_homotopy_mul(X, x₀, n), " +
			"        simplicial_homotopy_unit(X, x₀, n), " +
			"        simplicial_homotopy_inv(X, x₀, n), " +
			"        simplicial_homotopy_group(X, x₀, n)), " +
			"    mk_group(simplicial_homotopy_mul(Y, F(0, x₀), n), " +
			"        simplicial_homotopy_unit(Y, F(0, x₀), n), " +
			"        simplicial_homotopy_inv(Y, F(0, x₀), n), " +
			"        simplicial_homotopy_group(Y, F(0, x₀), n)), " +
			"    simplicial_homotopy_map(X, Y, F, x₀, n))",
	},
		func(
			a *Argument,
			mapping Fact,
			x0 *Expr[A],
			n *Expr[Nat],
			sourceKan, targetKan, vertex, positive Fact,
		) {
			source := simplicial_set.MapSource.Read(mapping)
			y0 := a.TermAs[B]("F(0, x₀)")
			imageVertex := a.Have(
				"the base vertex maps to a vertex of Y",
				"F(0, x₀) ∈ Y.simplices(0)",
				By(vertex, simplicial_set.MapIn.Read(mapping).At(a.TermAs[Nat]("0"), x0)))
			preservesProduct := a.Have(
				"the induced map preserves products of homotopy classes",
				Statement{
					Binders: "∀C D:set(A).",
					Hypotheses: []string{
						"C ∈ simplicial_homotopy_group(X, x₀, n)",
						"D ∈ simplicial_homotopy_group(X, x₀, n)",
					},
					Conclusion: "simplicial_homotopy_map(X, Y, F, x₀, n, simplicial_homotopy_mul(X, x₀, n, C, D)) = " +
						"simplicial_homotopy_mul(Y, " +
						"    F(0, x₀), " +
						"    n, " +
						"    simplicial_homotopy_map(X, Y, F, x₀, n, C), " +
						"    simplicial_homotopy_map(X, Y, F, x₀, n, D))",
				},
				Derive(func(b *Argument) {
					C, D := b.FixAs[Set[A]](), b.FixAs[Set[A]]()
					classes := b.Assume()
					x, representedC := b.ObtainAs[A](
						"choose a sphere x representing C",
						"∃x:A. x ∈ simplicial_sphere(X, x₀, n) ∧ C = equivalence_class(simplicial_homotopic(X, x₀, n), x)",
						By(vertex, classes, InHomotopyGroup.Read(source).At(x0, n, C)))
					y, representedD := b.ObtainAs[A](
						"choose a sphere y representing D",
						"∃y:A. y ∈ simplicial_sphere(X, x₀, n) ∧ D = equivalence_class(simplicial_homotopic(X, x₀, n), y)",
						By(vertex, classes, InHomotopyGroup.Read(source).At(x0, n, D)))
					xParts := b.Conjuncts(
						representedC,
						"x is a sphere",
						"C is its class")
					yParts := b.Conjuncts(
						representedD,
						"y is a sphere",
						"D is its class")
					xSphere, classC := xParts[0], xParts[1]
					ySphere, classD := yParts[0], yParts[1]
					w, filled := b.ObtainAs[A](
						"a product filler w for x and y exists in the Kan complex X",
						"∃w:A. "+
							"    w ∈ X.simplices(n + 1) ∧ "+
							"    (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(X.s, x₀, n)) ∧ "+
							"    X.d(n + 1, n + 1, w) = x ∧ "+
							"    X.d(n + 1, n - 1, w) = y",
						By(vertex, positive, xSphere, ySphere, ProductFillerExists.Read(sourceKan).At(x0, n, x, y)))
					faces := b.Conjuncts(
						filled,
						"w is an (n+1)-simplex",
						"its faces below n − 1 are the base simplex",
						"its last face is x",
						"its face n − 1 is y")
					wIn, wBelow, wLast, wPrevious := faces[0], faces[1], faces[2], faces[3]
					next, previous := b.TermAs[Nat]("n + 1"), b.TermAs[Nat]("n - 1")
					imageX, imageY := b.TermAs[B]("F(n, x)"), b.TermAs[B]("F(n, y)")
					imageW := b.TermAs[B]("F(n + 1, w)")
					imageFiller := b.Have(
						"F carries w to a product filler for the image spheres, and preserves its middle face",
						"F(n + 1, w) ∈ Y.simplices(n + 1) ∧ "+
							"(∀i:num. i + 1 < n ⇒ Y.d(n + 1, i, F(n + 1, w)) = base_simplex(Y.s, F(0, x₀), n)) ∧ "+
							"Y.d(n + 1, n + 1, F(n + 1, w)) = F(n, x) ∧ "+
							"Y.d(n + 1, n - 1, F(n + 1, w)) = F(n, y) ∧ "+
							"Y.d(n + 1, n, F(n + 1, w)) = F(n, X.d(n + 1, n, w))",
						SplitConjAll(
							Case(
								"the image is an (n+1)-simplex",
								By(wIn, simplicial_set.MapIn.Read(mapping).At(next, w))),
							Case(
								"the lower faces remain the base simplex",
								Derive(func(c *Argument) {
									i := c.FixAs[Nat]()
									below := c.Assume()
									c.Show(
										"F commutes with the face and carries the base simplex to the base simplex",
										ByArith(
											wBelow.At(i),
											below,
											wIn,
											vertex,
											simplicial_set.MapFace.Read(mapping).At(n, i, w),
											simplicial_set.MapBaseSimplex.Read(mapping).At(x0, n)))
								})),
							Case(
								"the last face is the image of x",
								ByArith(wIn, wLast, simplicial_set.MapFace.Read(mapping).At(n, next, w))),
							Case(
								"the face n − 1 is the image of y",
								ByArith(wIn, wPrevious, simplicial_set.MapFace.Read(mapping).At(n, previous, w))),
							Case(
								"the middle face is the image of the middle face of w",
								ByArith(wIn, simplicial_set.MapFace.Read(mapping).At(n, n, w)))))
					middle := b.TermAs[A]("X.d(n + 1, n, w)")
					middleSphere := b.Have(
						"the middle face of the product filler is a sphere",
						"X.d(n + 1, n, w) ∈ simplicial_sphere(X, x₀, n)",
						By(vertex, positive, xSphere, ySphere, filled, ProductSphere.Read(source).At(x0, n, x, y, w)))
					b.Show(
						"both products are the class of the image of the middle face of w",
						CalcEq(
							Leg(
								b.TermAs[Set[B]](
									"simplicial_homotopy_map(X, "+
										"    Y, "+
										"    F, "+
										"    x₀, "+
										"    n, "+
										"    equivalence_class(simplicial_homotopic(X, x₀, n), X.d(n + 1, n, w)))"),
								"the source product is the class of the middle face of w",
								By(
									vertex,
									positive,
									xSphere,
									ySphere,
									classC,
									classD,
									filled,
									MulClass.Read(sourceKan).At(x0, n, x, y, w))),
							Leg(
								b.TermAs[Set[B]]("equivalence_class(simplicial_homotopic(Y, F(0, x₀), n), F(n, X.d(n + 1, n, w)))"),
								"the induced map sends the class of that sphere to the class of its image",
								By(vertex, targetKan, middleSphere, HomotopyMapClass.Read(mapping).At(x0, n, middle))),
							FinalLeg(
								"the image filler computes the product of the two image classes",
								By(
									vertex,
									imageVertex,
									positive,
									targetKan,
									xSphere,
									ySphere,
									classC,
									classD,
									imageFiller,
									MulClass.Read(targetKan).At(y0, n, imageX, imageY, imageW),
									MapSphere.Read(mapping).At(x0, n, x),
									HomotopyMapClass.Read(mapping).At(x0, n, x),
									MapSphere.Read(mapping).At(x0, n, y),
									HomotopyMapClass.Read(mapping).At(x0, n, y)))))
				}))
			mapsCarrier := a.Have(
				"the induced map carries the source homotopy group into the target",
				Statement{
					Binders:    "∀C:set(A).",
					Hypotheses: []string{"C ∈ simplicial_homotopy_group(X, x₀, n)"},
					Conclusion: "simplicial_homotopy_map(X, Y, F, x₀, n, C) ∈ " +
						"simplicial_homotopy_group(Y, F(0, x₀), n)",
				},
				Derive(func(b *Argument) {
					C := b.FixAs[Set[A]]()
					inGroup := b.Assume()
					b.Show(
						"the induced image lies in the target group",
						By(vertex, inGroup, HomotopyMapIn.Read(mapping).At(x0, n, C)))
				}))
			sourceGroup := a.TermAs[group.GroupOps[Set[A]]](
				"mk_group(simplicial_homotopy_mul(X, x₀, n), " +
					"    simplicial_homotopy_unit(X, x₀, n), " +
					"    simplicial_homotopy_inv(X, x₀, n), " +
					"    simplicial_homotopy_group(X, x₀, n))")
			targetGroup := a.TermAs[group.GroupOps[Set[B]]](
				"mk_group(simplicial_homotopy_mul(Y, F(0, x₀), n), " +
					"    simplicial_homotopy_unit(Y, F(0, x₀), n), " +
					"    simplicial_homotopy_inv(Y, F(0, x₀), n), " +
					"    simplicial_homotopy_group(Y, F(0, x₀), n))")
			induced := a.TermAs[Fun[Set[A], Set[B]]]("simplicial_homotopy_map(X, Y, F, x₀, n)")
			a.Show(
				"the two homotopy groups, carrier map and product preservation give a homomorphism",
				By(
					vertex,
					imageVertex,
					positive,
					preservesProduct,
					mapsCarrier,
					group_homomorphism.GroupHomomorphism.At(sourceGroup, targetGroup, induced),
					GroupOn.Read(sourceKan).At(x0, n),
					GroupOn.Read(targetKan).At(y0, n)))
		}),
})}
