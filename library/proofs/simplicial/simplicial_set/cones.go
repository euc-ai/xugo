// cones.go — the cone of simplices under a fixed simplex k and the cone
// under its boundary: their carriers and tail operators, the membership
// law of the boundary cone, both cones as simplicial sets, the
// restriction from the cone to the boundary cone and the projection
// from the boundary cone to X as simplicial maps.

package simplicial_set

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// SimplexConeSimplicesDef — the q-simplices under k are the (r+q+1)-simplices
// whose first r+1 vertices form k.
var SimplexConeSimplicesDef = simplexConeSimplicesDefThm{family.Define(registry.DefEntry{
	Name:     "SimplexConeSimplicesDef",
	Key:      "prop_2f232d68d28bcafa",
	Const:    "simplex_cone_simplices",
	Type:     "simplicial_ops(A) → num → A → num → set(A)",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀r:num. ∀k:A. " +
			"    simplex_cone_simplices(X, r, k) = " +
			"    λq:num. {x:A | x ∈ X.simplices(r + q + 1) ∧ face_iterate_top(X.d, r + q + 1, q + 1, x) = k}",
	},
	Deps: append([]registry.EntryLike{FaceIterateTopDef}, recordFields...),
})}

// SimplexConeFaceDef — remove a tail vertex, past the fixed prefix.
var SimplexConeFaceDef = simplexConeFaceDefThm{family.Define(registry.DefEntry{
	Name:     "SimplexConeFaceDef",
	Key:      "prop_e65b64f4d21f6c46",
	Const:    "simplex_cone_face",
	Type:     "(num → num → A → A) → num → num → num → A → A",
	Implicit: []string{"d"},
	Equations: []string{
		"∀d:(num → num → A → A). ∀r:num. " +
			"    simplex_cone_face(d, r) = λq:num. λi:num. λx:A. d(r + q + 1, r + 1 + i, x)",
	},
})}

// simplexConeDegeneracyDef — repeat a tail vertex.
var simplexConeDegeneracyDef = simplexConeDegeneracyDefThm{family.Define(registry.DefEntry{
	Name:     "simplexConeDegeneracyDef",
	Key:      "prop_a31e6fc7f42b0cc5",
	Const:    "simplex_cone_degeneracy",
	Type:     "(num → num → A → A) → num → num → num → A → A",
	Implicit: []string{"s"},
	Equations: []string{
		"∀s:(num → num → A → A). ∀r:num. " +
			"    simplex_cone_degeneracy(s, r) = λq:num. λi:num. λx:A. s(r + q + 1, r + 1 + i, x)",
	},
})}

// SimplexBoundaryConeSimplicesDef — a cone under the boundary of k is a face
// family on its r+1 prefix faces, each with the matching face of k on
// top, and junk in every unused coordinate.
var SimplexBoundaryConeSimplicesDef = simplexBoundaryConeSimplicesDefThm{family.Define(registry.DefEntry{
	Name:     "SimplexBoundaryConeSimplicesDef",
	Key:      "prop_c92e710f047b628a",
	Const:    "simplex_boundary_cone_simplices",
	Type:     "simplicial_ops(A) → num → A → num → set(num → A)",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀r:num. ∀k:A. " +
			"    simplex_boundary_cone_simplices(X, r, k) = " +
			"    λq:num. " +
			"        {y:(num → A) | " +
			"            y = normalize_on(0 .. r, junk, y) ∧ " +
			"            face_family(X, r + q, 0 .. r, y) ∧ " +
			"            (∀j:num. 0 < r ∧ j ≤ r ⇒ face_iterate_top(X.d, r + q, q + 1, y(j)) = X.d(r, j, k))}",
	},
	Deps: []registry.EntryLike{FaceIterateTopDef, FaceFamilyDef},
	Reading: "At r = 0 there is no prefix restriction: y(0) is an arbitrary q-simplex of X and " +
		"every other coordinate is junk. Thus the boundary cone is canonically isomorphic to X, not " +
		"literally the same carrier type. For positive r all iterations stay within the simplex dimension.",
})}

// BoundaryConeMembership — the definition read at a normalized family:
// a family normalized on 0 .. r lies in the boundary cone exactly when
// its values there form a face family whose top faces are the faces of
// k. Unfolded, the cone admits it by three clauses; normalizing twice
// changes nothing, and the other two read the family only on 0 .. r,
// where the normalized family is f.
var BoundaryConeMembership = boundaryConeMembershipThm{family.Add(registry.ProofEntry{
	Name: "BoundaryConeMembership",
	Key:  "prop_8e34046b5fe63ea0",
	Build: family.Theorem("∀X:simplicial_ops(A). ∀r q:num. ∀k:A. ∀f:(num → A). "+
		"    normalize_on(0 .. r, junk, f) ∈ simplex_boundary_cone_simplices(X, r, k, q) ⇔ "+
		"    face_family(X, r + q, 0 .. r, f) ∧ "+
		"    (∀j:num. 0 < r ∧ j ≤ r ⇒ face_iterate_top(X.d, r + q, q + 1, f(j)) = X.d(r, j, k))",
		func(
			a *Argument,
			X *Expr[SimplicialOps[A]],
			r *Expr[Nat],
			q *Expr[Nat],
			k *Expr[A],
			f *Arrow[Nat, A],
		) {
			sameFamily := a.Have(
				"the face family is read only on 0 .. r, where the normalized family is f",
				"face_family(X, r + q, 0 .. r, normalize_on(0 .. r, junk, f)) ⇔ face_family(X, r + q, 0 .. r, f)",
				Simp(Fwd(FaceFamilyDef), Fwd(FacesCompatibleDef)),
				Derive(func(b *Argument) {
					b.Iff()
					b.Forward(
						"the normalized values on 0 .. r are f's",
						func(c *Argument, normalized Fact) {
							c.Show(
								"so f's values lie in X(r + q) and have compatible faces",
								By(normalized, functions.NormalizeOnIn))
						})
					b.Backward(
						"f's values on 0 .. r are the normalized ones",
						func(c *Argument, original Fact) {
							c.Show(
								"so the normalized values lie in X(r + q) and have compatible faces",
								By(Normalized, original, functions.NormalizeOnIn))
						})
				}))
			sameTops := a.Have(
				"so are the top faces, read at j ≤ r",
				"(∀j:num. "+
					"    0 < r ∧ j ≤ r ⇒ "+
					"    face_iterate_top(X.d, r + q, q + 1, normalize_on(0 .. r, junk, f, j)) = X.d(r, j, k)) ⇔ "+
					"(∀j:num. 0 < r ∧ j ≤ r ⇒ face_iterate_top(X.d, r + q, q + 1, f(j)) = X.d(r, j, k))",
				Derive(func(b *Argument) {
					b.Iff()
					b.Forward(
						"the normalized tops on 0 .. r are f's",
						func(c *Argument, normalized Fact) {
							c.Show(
								"so f's tops are the faces of k",
								By(normalized, num_segment.NormalizeOnSegmentIn))
						})
					b.Backward(
						"f's tops on 0 .. r are the normalized ones",
						func(c *Argument, original Fact) {
							c.Show(
								"so the normalized tops are the faces of k",
								By(Normalized, original, num_segment.NormalizeOnSegmentIn))
						})
				}))
			unfolded := a.Have(
				"unfolded, the cone admits the normalized family by its padding, its face family and its tops",
				"normalize_on(0 .. r, junk, f) ∈ simplex_boundary_cone_simplices(X, r, k, q) ⇔ "+
					"normalize_on(0 .. r, junk, f) = normalize_on(0 .. r, junk, normalize_on(0 .. r, junk, f)) ∧ "+
					"face_family(X, r + q, 0 .. r, normalize_on(0 .. r, junk, f)) ∧ "+
					"(∀j:num. "+
					"    0 < r ∧ j ≤ r ⇒ "+
					"    face_iterate_top(X.d, r + q, q + 1, normalize_on(0 .. r, junk, f, j)) = X.d(r, j, k))",
				Unfold(SimplexBoundaryConeSimplicesDef),
				BySets())
			a.Show(
				"the padding holds, as normalizing twice is normalizing once, and the other two clauses are f's",
				unfolded.Rw(),
				Simp(Fwd(functions.NormalizeOnIdempotent)),
				sameFamily.Rw(),
				sameTops.Rw(),
				Basic())
		}),
})}

// SimplexBoundaryConeFaceDef — take a tail face in each prefix face,
// retaining the fixed padding outside 0 .. r.
var SimplexBoundaryConeFaceDef = simplexBoundaryConeFaceDefThm{family.Define(registry.DefEntry{
	Name:     "SimplexBoundaryConeFaceDef",
	Key:      "prop_f24d52ba169a1aff",
	Const:    "simplex_boundary_cone_face",
	Type:     "(num → num → A → A) → num → num → num → (num → A) → num → A",
	Implicit: []string{"d"},
	Equations: []string{
		"∀d:(num → num → A → A). ∀r:num. " +
			"    simplex_boundary_cone_face(d, r) = " +
			"    λq:num. λi:num. λy:(num → A). normalize_on(0 .. r, junk, λj:num. d(r + q, r + i, y(j)))",
	},
})}

// simplexBoundaryConeDegeneracyDef — repeat a tail vertex in each
// prefix face and normalize the resulting family.
var simplexBoundaryConeDegeneracyDef = simplexBoundaryConeDegeneracyDefThm{family.Define(registry.DefEntry{
	Name:     "simplexBoundaryConeDegeneracyDef",
	Key:      "prop_80c129a795acc8a8",
	Const:    "simplex_boundary_cone_degeneracy",
	Type:     "(num → num → A → A) → num → num → num → (num → A) → num → A",
	Implicit: []string{"s"},
	Equations: []string{
		"∀s:(num → num → A → A). ∀r:num. " +
			"    simplex_boundary_cone_degeneracy(s, r) = " +
			"    λq:num. λi:num. λy:(num → A). normalize_on(0 .. r, junk, λj:num. s(r + q, r + i, y(j)))",
	},
})}

// SimplexConeRestrictionDef — restrict a cone to its prefix faces.
var SimplexConeRestrictionDef = simplexConeRestrictionDefThm{family.Define(registry.DefEntry{
	Name:     "SimplexConeRestrictionDef",
	Key:      "prop_15d31379aa0792c9",
	Const:    "simplex_cone_restriction",
	Type:     "(num → num → A → A) → num → num → A → num → A",
	Implicit: []string{"d"},
	Equations: []string{
		"∀d:(num → num → A → A). ∀r:num. " +
			"    simplex_cone_restriction(d, r) = " +
			"    λq:num. λx:A. normalize_on(0 .. r, junk, λj:num. d(r + q + 1, j, x))",
	},
})}

// SimplexBoundaryConeProjectionDef — remove the r prefix vertices of
// the zeroth face to recover the common tail simplex.
var SimplexBoundaryConeProjectionDef = simplexBoundaryConeProjectionDefThm{family.Define(registry.DefEntry{
	Name:     "SimplexBoundaryConeProjectionDef",
	Key:      "prop_b68620cfa11df88f",
	Const:    "simplex_boundary_cone_projection",
	Type:     "(num → num → A → A) → num → num → (num → A) → A",
	Implicit: []string{"d"},
	Equations: []string{
		"∀d:(num → num → A → A). ∀r:num. " +
			"    simplex_boundary_cone_projection(d, r) = " +
			"    λq:num. λy:(num → A). face_iterate_bottom(d, r + q, r, y(0))",
	},
	Deps: []registry.EntryLike{FaceIterateBottomDef},
})}

// SimplexConeSimplicialSet — the cone under any k is a simplicial set:
// a tail face or degeneracy keeps the prefix k, the top iteration
// absorbing it by FaceIterateTopAbove or FaceIterateTopDegeneracyAbove,
// and each identity of the cone is the identity of X at the indices
// shifted by r + 1.
var SimplexConeSimplicialSet = simplexConeSimplicialSetThm{family.Add(registry.ProofEntry{
	Name: "SimplexConeSimplicialSet",
	Key:  "prop_ac0c8a3060b84d1",
	Build: SimplicialSet.Law("∀r:num. ∀k:A. simplicial_set(simplex_cone(X, r, k))",
		func(a *Argument, simplicial Fact, r *Expr[Nat], k *Expr[A]) {
			a.Show(
				"the tail operators satisfy the eight simplicial-set axioms",
				Simp(Fwd(SimplicialSet)),
				SplitConjAll(
					Case(
						"a tail face preserves the carrier and the fixed prefix",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							x := b.FixAs[A]("x")
							given := b.Assume()
							data := b.Have(
								"read the ambient dimension and fixed prefix of x",
								"x ∈ X.simplices(r + (n + 1) + 1) ∧ face_iterate_top(r + (n + 1) + 1, n + 1 + 1, x) = k",
								BySets(b.Unfolded(given, SimplexConeSimplicesDef)))
							parts := b.Conjuncts(
								data,
								"x has the ambient input dimension",
								"its top iteration is the fixed prefix")
							membership, fixed := parts[0], parts[1]
							dimension := b.Have(
								"align the source degree with the ambient successor degree",
								"r + (n + 1) + 1 = r + n + 1 + 1",
								ByArith())
							b.Do(Simp(Fwd(SimplexConeFaceDef)), dimension.Rw())
							degree, tail, count :=
								b.TermAs[Nat]("r + n + 1"), b.TermAs[Nat]("r + 1 + i"), b.TermAs[Nat]("n + 1")
							inAmbient := b.Have(
								"the tail face has the required ambient dimension",
								"X.d(r + n + 1 + 1, r + 1 + i, x) ∈ X.simplices(r + n + 1)",
								ByArith(FaceIn.Read(simplicial).At(degree, tail, x), membership, given))
							retains := b.Have(
								"the tail face retains the fixed prefix",
								"face_iterate_top(r + n + 1, n + 1, X.d(r + n + 1 + 1, r + 1 + i, x)) = k",
								CalcEq(
									Leg(
										b.TermAs[A]("face_iterate_top(r + n + 1 + 1, n + 1 + 1, x)"),
										"absorb the tail face into the top iteration",
										ByArith(FaceIterateTopAbove.Read(simplicial).At(degree, count, tail, x), membership, given)),
									FinalLeg(
										"the input top iteration is the fixed prefix",
										By(fixed)),
								))
							b.Show(
								"both cone-carrier conditions hold for the tail face",
								Unfold(SimplexConeSimplicesDef),
								BySets(inAmbient, retains))
						})),
					Case(
						"a tail degeneracy preserves the carrier and the fixed prefix",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							x := b.FixAs[A]("x")
							given := b.Assume()
							data := b.Have(
								"read the ambient dimension and fixed prefix of x",
								"x ∈ X.simplices(r + n + 1) ∧ face_iterate_top(r + n + 1, n + 1, x) = k",
								BySets(b.Unfolded(given, SimplexConeSimplicesDef)))
							parts := b.Conjuncts(
								data,
								"x has the ambient input dimension",
								"its top iteration is the fixed prefix")
							membership, fixed := parts[0], parts[1]
							b.Do(Simp(Fwd(simplexConeDegeneracyDef)))
							degree, tail, count :=
								b.TermAs[Nat]("r + n + 1"), b.TermAs[Nat]("r + 1 + i"), b.TermAs[Nat]("n + 1")
							inAmbient := b.Have(
								"the tail degeneracy has the required ambient dimension",
								"X.s(r + n + 1, r + 1 + i, x) ∈ X.simplices(r + n + 1 + 1)",
								ByArith(DegeneracyIn.Read(simplicial).At(degree, tail, x), membership, given))
							cancels := b.Have(
								"the top iteration cancels the repeated tail vertex",
								"face_iterate_top(r + n + 1 + 1, n + 1 + 1, X.s(r + n + 1, r + 1 + i, x)) = "+
									"face_iterate_top(r + n + 1, n + 1, x)",
								ByArith(
									FaceIterateTopDegeneracyAbove.Read(simplicial).At(degree, count, tail, x),
									membership,
									given))
							retains := b.Have(
								"the tail degeneracy retains the fixed prefix",
								"face_iterate_top(r + n + 1 + 1, n + 1 + 1, X.s(r + n + 1, r + 1 + i, x)) = k",
								By(cancels, fixed))
							dimension := b.Have(
								"align the output degree with the ambient successor degree",
								"r + (n + 1) + 1 = r + n + 1 + 1",
								ByArith())
							b.Show(
								"both cone-carrier conditions hold for the tail degeneracy",
								Unfold(SimplexConeSimplicesDef),
								dimension.Rw(),
								BySets(inAmbient, retains))
						})),
					Case(
						"the face identity holds after shifting each tail index",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							b.FixAs[Nat]("j")
							x := b.FixAs[A]("x")
							given := b.Assume()
							membership := b.Have(
								"x has the ambient input dimension",
								"x ∈ X.simplices(r + (n + 2) + 1)",
								BySets(b.Unfolded(given, SimplexConeSimplicesDef)))
							b.Do(Simp(Fwd(SimplexConeFaceDef)))
							dimensions := b.Have(
								"align the shifted dimensions and indices",
								"r + (n + 1) + 1 = r + n + 1 + 1 ∧ "+
									"r + (n + 2) + 1 = r + n + 1 + 2 ∧ "+
									"r + 1 + (j - 1) = r + 1 + j - 1",
								ByArith(given))
							bridges := b.Conjuncts(
								dimensions,
								"degree n + 1 of the cone is degree (r + n + 1) + 1 of X",
								"degree n + 2 of the cone is degree (r + n + 1) + 2 of X",
								"the shift of j − 1 is the shift of j, less one")
							b.Show(
								"the corresponding ambient identity applies",
								bridges[0].Rw(),
								bridges[1].Rw(),
								bridges[2].Rw(),
								ByArith(
									FaceFace.Read(simplicial).At(
										b.TermAs[Nat]("r + n + 1"), b.TermAs[Nat]("r + 1 + i"), b.TermAs[Nat]("r + 1 + j"), x),
									membership,
									given))
						})),
					Case(
						"the degeneracy identity holds after shifting each tail index",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							b.FixAs[Nat]("j")
							x := b.FixAs[A]("x")
							given := b.Assume()
							membership := b.Have(
								"x has the ambient input dimension",
								"x ∈ X.simplices(r + n + 1)",
								BySets(b.Unfolded(given, SimplexConeSimplicesDef)))
							b.Do(Simp(Fwd(simplexConeDegeneracyDef)))
							dimensions := b.Have(
								"align the shifted dimensions and indices",
								"r + (n + 1) + 1 = r + n + 1 + 1 ∧ r + 1 + (j + 1) = r + 1 + j + 1",
								ByArith())
							bridges := b.Conjuncts(
								dimensions,
								"degree n + 1 of the cone is degree (r + n + 1) + 1 of X",
								"the shift of j + 1 is the shift of j, plus one")
							b.Show(
								"the corresponding ambient identity applies",
								bridges[0].Rw(),
								bridges[1].Rw(),
								ByArith(
									DegeneracyDegeneracy.Read(simplicial).At(
										b.TermAs[Nat]("r + n + 1"), b.TermAs[Nat]("r + 1 + i"), b.TermAs[Nat]("r + 1 + j"), x),
									membership,
									given))
						})),
					Case(
						"a lower tail face passes a tail degeneracy",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							b.FixAs[Nat]("j")
							x := b.FixAs[A]("x")
							given := b.Assume()
							membership := b.Have(
								"x has the ambient input dimension",
								"x ∈ X.simplices(r + (n + 1) + 1)",
								BySets(b.Unfolded(given, SimplexConeSimplicesDef)))
							b.Do(Simp(Fwd(SimplexConeFaceDef), Fwd(simplexConeDegeneracyDef)))
							dimensions := b.Have(
								"align the shifted dimensions and indices",
								"r + (n + 1) + 1 = r + n + 1 + 1 ∧ "+
									"r + (n + 2) + 1 = r + n + 1 + 2 ∧ "+
									"r + 1 + (j - 1) = r + 1 + j - 1",
								ByArith(given))
							bridges := b.Conjuncts(
								dimensions,
								"degree n + 1 of the cone is degree (r + n + 1) + 1 of X",
								"degree n + 2 of the cone is degree (r + n + 1) + 2 of X",
								"the shift of j − 1 is the shift of j, less one")
							b.Show(
								"the corresponding ambient identity applies",
								bridges[0].Rw(),
								bridges[1].Rw(),
								bridges[2].Rw(),
								ByArith(
									FaceDegeneracyBelow.Read(simplicial).At(
										b.TermAs[Nat]("r + n + 1"), b.TermAs[Nat]("r + 1 + i"), b.TermAs[Nat]("r + 1 + j"), x),
									membership,
									given))
						})),
					Case(
						"the repeated tail face cancels a tail degeneracy",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							x := b.FixAs[A]("x")
							given := b.Assume()
							membership := b.Have(
								"x has the ambient input dimension",
								"x ∈ X.simplices(r + n + 1)",
								BySets(b.Unfolded(given, SimplexConeSimplicesDef)))
							b.Do(Simp(Fwd(SimplexConeFaceDef), Fwd(simplexConeDegeneracyDef)))
							dimensions := b.Have(
								"align the shifted dimensions and indices",
								"r + (n + 1) + 1 = r + n + 1 + 1",
								ByArith())
							b.Show(
								"the corresponding ambient identity applies",
								dimensions.Rw(),
								ByArith(
									FaceDegeneracyEqual.Read(simplicial).At(b.TermAs[Nat]("r + n + 1"), b.TermAs[Nat]("r + 1 + i"), x),
									membership,
									given))
						})),
					Case(
						"the next tail face cancels a tail degeneracy",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							x := b.FixAs[A]("x")
							given := b.Assume()
							membership := b.Have(
								"x has the ambient input dimension",
								"x ∈ X.simplices(r + n + 1)",
								BySets(b.Unfolded(given, SimplexConeSimplicesDef)))
							b.Do(Simp(Fwd(SimplexConeFaceDef), Fwd(simplexConeDegeneracyDef)))
							dimensions := b.Have(
								"align the shifted dimensions and indices",
								"r + (n + 1) + 1 = r + n + 1 + 1 ∧ r + 1 + (i + 1) = r + 1 + i + 1",
								ByArith())
							bridges := b.Conjuncts(
								dimensions,
								"degree n + 1 of the cone is degree (r + n + 1) + 1 of X",
								"the shift of i + 1 is the shift of i, plus one")
							b.Show(
								"the corresponding ambient identity applies",
								bridges[0].Rw(),
								bridges[1].Rw(),
								ByArith(
									FaceDegeneracyNext.Read(simplicial).At(b.TermAs[Nat]("r + n + 1"), b.TermAs[Nat]("r + 1 + i"), x),
									membership,
									given))
						})),
					Case(
						"an upper tail face passes a tail degeneracy",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							b.FixAs[Nat]("j")
							x := b.FixAs[A]("x")
							given := b.Assume()
							membership := b.Have(
								"x has the ambient input dimension",
								"x ∈ X.simplices(r + (n + 1) + 1)",
								BySets(b.Unfolded(given, SimplexConeSimplicesDef)))
							b.Do(Simp(Fwd(SimplexConeFaceDef), Fwd(simplexConeDegeneracyDef)))
							dimensions := b.Have(
								"align the shifted dimensions and indices",
								"r + (n + 1) + 1 = r + n + 1 + 1 ∧ "+
									"r + (n + 2) + 1 = r + n + 1 + 2 ∧ "+
									"r + 1 + (i - 1) = r + 1 + i - 1",
								ByArith(given))
							bridges := b.Conjuncts(
								dimensions,
								"degree n + 1 of the cone is degree (r + n + 1) + 1 of X",
								"degree n + 2 of the cone is degree (r + n + 1) + 2 of X",
								"the shift of i − 1 is the shift of i, less one")
							b.Show(
								"the corresponding ambient identity applies",
								bridges[0].Rw(),
								bridges[1].Rw(),
								bridges[2].Rw(),
								ByArith(
									FaceDegeneracyAbove.Read(simplicial).At(
										b.TermAs[Nat]("r + n + 1"), b.TermAs[Nat]("r + 1 + i"), b.TermAs[Nat]("r + 1 + j"), x),
									membership,
									given))
						})),
				))
		}),
})}

// BoundaryConeSimplicialSet — the boundary cone under any k is a
// simplicial set: a tail face or degeneracy taken in each prefix face
// gives again a face family whose tops are the faces of k
// (BoundaryConeMembership), compatibility passing it by FaceFace or
// FaceDegeneracyBelow and the tops absorbing it by FaceIterateTopAbove
// or FaceIterateTopDegeneracyAbove; each identity is an equation between
// families normalized on 0 .. r, so it holds once it holds at every
// coordinate there (NormalizeOnEqIff), where it is the identity of X at
// the indices shifted by r.
var BoundaryConeSimplicialSet = boundaryConeSimplicialSetThm{family.Add(registry.ProofEntry{
	Name: "BoundaryConeSimplicialSet",
	Key:  "prop_ff72c98cccd439b4",
	Build: family.Sections(SimplicialSet.Statement(
		"∀r:num. ∀k:A. simplicial_set(simplex_boundary_cone(X, r, k))"),
		func(ctx *Script, headline string) *GoalStackNode {
			faceClosure := ctx.Lemma("∀X:simplicial_ops(A). "+
				"    simplicial_set(X) ⇒ "+
				"    ∀r q i:num. ∀k:A. ∀y:(num → A). "+
				"        y ∈ simplex_boundary_cone_simplices(r, k, q + 1) ∧ i ≤ q + 1 ⇒ "+
				"        simplex_boundary_cone_face(r, q + 1, i, y) ∈ simplex_boundary_cone_simplices(r, k, q)",
				func(
					arg *Argument,
					X *Expr[SimplicialOps[A]],
					simplicial Fact,
					r *Expr[Nat],
					q *Expr[Nat],
					i *Expr[Nat],
					k *Expr[A],
					y *Arrow[Nat, A],
					given Fact,
				) {
					assumptions := arg.Conjuncts(
						given,
						"y is a boundary-cone simplex",
						"the tail-face index is in range")
					inCone, index := assumptions[0], assumptions[1]
					data := arg.Have(
						"read the face family and the top faces of y",
						"face_family(r + (q + 1), 0 .. r, y) ∧ "+
							"(∀j:num. 0 < r ∧ j ≤ r ⇒ face_iterate_top(r + (q + 1), q + 1 + 1, y(j)) = X.d(r, j, k))",
						BySets(arg.Unfolded(inCone, SimplexBoundaryConeSimplicesDef)))
					parts := arg.Conjuncts(
						data,
						"the prefix faces of y form a face family",
						"its top faces give the boundary of k")
					faces := arg.Conjuncts(
						arg.Simplified(parts[0], Fwd(FaceFamilyDef), Fwd(FacesCompatibleDef)),
						"its coordinates have the prescribed dimension",
						"its prefix faces are compatible")
					coordinates, compatibility, fixedTop := faces[0], faces[1], parts[1]
					tails := arg.TermAs[Fun[Nat, A]]("λj:num. X.d(r + (q + 1), r + i, y(j))")
					carries := arg.Have(
						"each tail face of a live coordinate is an ambient face",
						"∀j:num. j ∈ 0 .. r ⇒ X.d(r + (q + 1), r + i, y(j)) ∈ X.simplices(r + q)",
						Derive(func(sub *Argument) {
							j := sub.FixAs[Nat]("j")
							live := sub.Assume()
							dimension := sub.Have(
								"write the input dimension as a successor",
								"r + (q + 1) = r + q + 1",
								ByArith())
							sub.Show(
								"ambient face closure lowers the coordinate dimension",
								dimension.Rw(),
								ByArith(
									coordinates.At(j),
									index,
									live,
									FaceIn.Read(simplicial).At(sub.TermAs[Nat]("r + q"), sub.TermAs[Nat]("r + i"), y.Apply(j))))
						}))
					compatible := arg.Have(
						"tail faces preserve prefix compatibility",
						Statement{
							Binders: "∀a b:num.",
							Hypotheses: []string{
								"a ∈ 0 .. r",
								"b ∈ 0 .. r",
								"a < b",
							},
							Conclusion: "X.d(r + q, a, X.d(r + (q + 1), r + i, y(b))) = " +
								"X.d(r + q, b - 1, X.d(r + (q + 1), r + i, y(a)))",
						},
						Derive(func(sub *Argument) {
							left, right := sub.FixAs[Nat]("a"), sub.FixAs[Nat]("b")
							rangeAB := sub.Assume()
							bounded := sub.Have(
								"both prefix indices are at most r",
								"a ≤ r ∧ b ≤ r",
								By(
									rangeAB,
									num_segment.MembershipFromZero.At(left, r),
									num_segment.MembershipFromZero.At(right, r)))
							m, lower := sub.ObtainAs[Nat](
								"the compatible faces have a positive ambient dimension",
								"∃m:num. r + q = m + 1",
								ByArith(rangeAB, bounded, nat_arith.NonzeroIsSucc.At(sub.TermAs[Nat]("r + q"))))
							upper := sub.Have(
								"the input coordinates are two dimensions above m",
								"r + (q + 1) = m + 2",
								ByArith(lower))
							sub.Do(lower.Rw(), upper.Rw())
							sub.Show(
								"pass both prefix faces through the tail face",
								CalcEq(
									Leg(
										sub.TermAs[A]("X.d(m + 1, r + i - 1, X.d(m + 2, a, y(b)))"),
										"pass the left prefix face",
										ByArith(
											coordinates.At(right),
											index,
											upper,
											rangeAB,
											bounded,
											FaceFace.Read(simplicial).At(m, left, sub.TermAs[Nat]("r + i"), y.Apply(right)))),
									Leg(
										sub.TermAs[A]("X.d(m + 1, r + i - 1, X.d(m + 2, b - 1, y(a)))"),
										"use the input prefix compatibility",
										By(compatibility.At(left, right), rangeAB)),
									FinalLeg(
										"pass the right prefix face back",
										ByArith(
											coordinates.At(left),
											index,
											upper,
											rangeAB,
											bounded,
											FaceFace.Read(simplicial).At(
												m, sub.TermAs[Nat]("b - 1"), sub.TermAs[Nat]("r + i"), y.Apply(left)))),
								))
						}))
					retains := arg.Have(
						"tail faces retain the prescribed boundary of k",
						Statement{
							Binders: "∀j:num.",
							Hypotheses: []string{
								"0 < r",
								"j ≤ r",
							},
							Conclusion: "face_iterate_top(r + q, q + 1, X.d(r + (q + 1), r + i, y(j))) = X.d(r, j, k)",
						},
						Derive(func(sub *Argument) {
							j := sub.FixAs[Nat]("j")
							positive := sub.Assume()
							live := sub.Have(
								"j lies in the live interval",
								"j ∈ 0 .. r",
								By(positive, num_segment.MembershipFromZero.At(j, r)))
							dimension := sub.Have(
								"write the input dimension as a successor",
								"r + (q + 1) = r + q + 1",
								ByArith())
							sub.Show(
								"the tail face is absorbed by one more top removal",
								dimension.Rw(),
								CalcEq(
									Leg(
										sub.TermAs[A]("face_iterate_top(r + q + 1, q + 1 + 1, y(j))"),
										"absorb the tail face",
										ByArith(
											coordinates.At(j),
											live,
											index,
											positive,
											FaceIterateTopAbove.Read(simplicial).At(
												sub.TermAs[Nat]("r + q"), sub.TermAs[Nat]("q + 1"), sub.TermAs[Nat]("r + i"), y.Apply(j)))),
									FinalLeg(
										"the input has the prescribed top face",
										By(fixedTop.At(j), positive)),
								))
						}))
					family := arg.Have(
						"the tail faces of the coordinates form a face family on 0 .. r",
						"face_family(r + q, 0 .. r, λj:num. X.d(r + (q + 1), r + i, y(j)))",
						Simp(Fwd(FaceFamilyDef), Fwd(FacesCompatibleDef)),
						By(carries, compatible))
					arg.Show(
						"so the normalized tail faces lie in the boundary cone",
						Simp(Fwd(SimplexBoundaryConeFaceDef)),
						By(At(BoundaryConeMembership, X, r, q, k, tails), family, retains))
				})
			degeneracyClosure := ctx.Lemma("∀X:simplicial_ops(A). "+
				"    simplicial_set(X) ⇒ "+
				"    ∀r q i:num. ∀k:A. ∀y:(num → A). "+
				"        y ∈ simplex_boundary_cone_simplices(r, k, q) ∧ i ≤ q ⇒ "+
				"        simplex_boundary_cone_degeneracy(r, q, i, y) ∈ "+
				"        simplex_boundary_cone_simplices(r, k, q + 1)",
				func(
					arg *Argument,
					X *Expr[SimplicialOps[A]],
					simplicial Fact,
					r *Expr[Nat],
					q *Expr[Nat],
					i *Expr[Nat],
					k *Expr[A],
					y *Arrow[Nat, A],
					given Fact,
				) {
					assumptions := arg.Conjuncts(
						given,
						"y is a boundary-cone simplex",
						"the tail-degeneracy index is in range")
					inCone, index := assumptions[0], assumptions[1]
					data := arg.Have(
						"read the face family and the top faces of y",
						"face_family(r + q, 0 .. r, y) ∧ "+
							"(∀j:num. 0 < r ∧ j ≤ r ⇒ face_iterate_top(r + q, q + 1, y(j)) = X.d(r, j, k))",
						BySets(arg.Unfolded(inCone, SimplexBoundaryConeSimplicesDef)))
					parts := arg.Conjuncts(
						data,
						"the prefix faces of y form a face family",
						"its top faces give the boundary of k")
					faces := arg.Conjuncts(
						arg.Simplified(parts[0], Fwd(FaceFamilyDef), Fwd(FacesCompatibleDef)),
						"its coordinates have the prescribed dimension",
						"its prefix faces are compatible")
					coordinates, compatibility, fixedTop := faces[0], faces[1], parts[1]
					tails := arg.TermAs[Fun[Nat, A]]("λj:num. X.s(r + q, r + i, y(j))")
					carries := arg.Have(
						"each tail degeneracy of a live coordinate is an ambient degeneracy",
						"∀j:num. j ∈ 0 .. r ⇒ X.s(r + q, r + i, y(j)) ∈ X.simplices(r + (q + 1))",
						Derive(func(sub *Argument) {
							j := sub.FixAs[Nat]("j")
							live := sub.Assume()
							dimension := sub.Have(
								"write the output dimension as a successor",
								"r + (q + 1) = r + q + 1",
								ByArith())
							sub.Show(
								"ambient degeneracy closure raises the coordinate dimension",
								dimension.Rw(),
								ByArith(
									coordinates.At(j),
									live,
									index,
									DegeneracyIn.Read(simplicial).At(sub.TermAs[Nat]("r + q"), sub.TermAs[Nat]("r + i"), y.Apply(j))))
						}))
					compatible := arg.Have(
						"tail degeneracies preserve prefix compatibility",
						Statement{
							Binders: "∀a b:num.",
							Hypotheses: []string{
								"a ∈ 0 .. r",
								"b ∈ 0 .. r",
								"a < b",
							},
							Conclusion: "X.d(r + (q + 1), a, X.s(r + q, r + i, y(b))) = " +
								"X.d(r + (q + 1), b - 1, X.s(r + q, r + i, y(a)))",
						},
						Derive(func(sub *Argument) {
							left, right := sub.FixAs[Nat]("a"), sub.FixAs[Nat]("b")
							rangeAB := sub.Assume()
							bounded := sub.Have(
								"both prefix indices are at most r",
								"a ≤ r ∧ b ≤ r",
								By(
									rangeAB,
									num_segment.MembershipFromZero.At(left, r),
									num_segment.MembershipFromZero.At(right, r)))
							m, lower := sub.ObtainAs[Nat](
								"the compatible faces have a positive ambient dimension",
								"∃m:num. r + q = m + 1",
								ByArith(rangeAB, bounded, nat_arith.NonzeroIsSucc.At(sub.TermAs[Nat]("r + q"))))
							upper := sub.Have(
								"the output coordinates are two dimensions above m",
								"r + (q + 1) = m + 2",
								ByArith(lower))
							sub.Do(lower.Rw(), upper.Rw())
							sub.Show(
								"pass both prefix faces through the tail degeneracy",
								CalcEq(
									Leg(
										sub.TermAs[A]("X.s(m, r + i - 1, X.d(m + 1, a, y(b)))"),
										"pass the left prefix face",
										ByArith(
											coordinates.At(right),
											rangeAB,
											bounded,
											index,
											lower,
											FaceDegeneracyBelow.Read(simplicial).At(m, left, sub.TermAs[Nat]("r + i"), y.Apply(right)))),
									Leg(
										sub.TermAs[A]("X.s(m, r + i - 1, X.d(m + 1, b - 1, y(a)))"),
										"use the input prefix compatibility",
										By(compatibility.At(left, right), rangeAB)),
									FinalLeg(
										"pass the right prefix face back",
										ByArith(
											coordinates.At(left),
											rangeAB,
											bounded,
											index,
											lower,
											FaceDegeneracyBelow.Read(simplicial).At(
												m, sub.TermAs[Nat]("b - 1"), sub.TermAs[Nat]("r + i"), y.Apply(left)))),
								))
						}))
					retains := arg.Have(
						"tail degeneracies retain the prescribed boundary of k",
						Statement{
							Binders: "∀j:num.",
							Hypotheses: []string{
								"0 < r",
								"j ≤ r",
							},
							Conclusion: "face_iterate_top(r + (q + 1), q + 1 + 1, X.s(r + q, r + i, y(j))) = X.d(r, j, k)",
						},
						Derive(func(sub *Argument) {
							j := sub.FixAs[Nat]("j")
							positive := sub.Assume()
							live := sub.Have(
								"j lies in the live interval",
								"j ∈ 0 .. r",
								By(positive, num_segment.MembershipFromZero.At(j, r)))
							dimension := sub.Have(
								"write the output dimension as a successor",
								"r + (q + 1) = r + q + 1",
								ByArith())
							sub.Do(dimension.Rw())
							n, count, repeated := sub.TermAs[Nat]("r + q"), sub.TermAs[Nat]("q + 1"), sub.TermAs[Nat]("r + i")
							cancels := sub.Have(
								"the top iteration cancels the repeated tail vertex",
								"face_iterate_top(r + q + 1, q + 1 + 1, X.s(r + q, r + i, y(j))) = "+
									"face_iterate_top(r + q, q + 1, y(j))",
								ByArith(
									coordinates.At(j),
									live,
									positive,
									index,
									FaceIterateTopDegeneracyAbove.Read(simplicial).At(n, count, repeated, y.Apply(j))))
							sub.Show(
								"the original top iteration gives the boundary of k",
								By(cancels, fixedTop.At(j), positive))
						}))
					family := arg.Have(
						"the tail degeneracies of the coordinates form a face family on 0 .. r",
						"face_family(r + (q + 1), 0 .. r, λj:num. X.s(r + q, r + i, y(j)))",
						Simp(Fwd(FaceFamilyDef), Fwd(FacesCompatibleDef)),
						By(carries, compatible))
					arg.Show(
						"so the normalized tail degeneracies lie in the boundary cone",
						Simp(Fwd(simplexBoundaryConeDegeneracyDef)),
						By(At(BoundaryConeMembership, X, r, arg.TermAs[Nat]("q + 1"), k, tails), family, retains))
				})
			return ctx.Theorem(headline, func(
				arg *Argument,
				X *Expr[SimplicialOps[A]],
				simplicial Fact,
				r *Expr[Nat],
				k *Expr[A],
			) {
				arg.Show(
					"the tail operators satisfy the eight simplicial-set axioms",
					Simp(Fwd(SimplicialSet)),
					SplitConjAll(
						Case(
							"tail faces preserve the carrier",
							By(simplicial, faceClosure)),
						Case(
							"tail degeneracies preserve the carrier",
							By(simplicial, degeneracyClosure)),
						Case(
							"the face identity holds in each coordinate",
							Derive(func(b *Argument) {
								b.FixAs[Nat]("n")
								b.FixAs[Nat]("i")
								b.FixAs[Nat]("j")
								b.FixAs[Fun[Nat, A]]("x")
								given := b.Assume()
								coordinates := b.Have(
									"read the input coordinate data",
									"∀a:num. a ∈ 0 .. r ⇒ x(a) ∈ X.simplices(r + (n + 2))",
									BySets(b.Unfolded(b.Unfolded(given, SimplexBoundaryConeSimplicesDef), FaceFamilyDef)))
								b.Do(Simp(Fwd(SimplexBoundaryConeFaceDef), Fwd(functions.NormalizeOnEqIff)))
								point := b.FixAs[Nat]("a")
								live := b.Assume()
								b.Do(Simp(Fwd(functions.NormalizeOnIn)))
								dimensions := b.Have(
									"align the shifted dimensions and indices",
									"r + (n + 1) = r + n + 1 ∧ r + (n + 2) = r + n + 2 ∧ r + (j - 1) = r + j - 1",
									ByArith(given))
								bridges := b.Conjuncts(
									dimensions,
									"degree n + 1 of a coordinate is degree (r + n) + 1 of X",
									"degree n + 2 of a coordinate is degree (r + n) + 2 of X",
									"the shift of j − 1 is the shift of j, less one")
								b.Show(
									"the ambient identity applies to this coordinate",
									bridges[0].Rw(),
									bridges[1].Rw(),
									bridges[2].Rw(),
									ByArith(
										FaceFace.Read(simplicial).At(
											b.TermAs[Nat]("r + n"), b.TermAs[Nat]("r + i"), b.TermAs[Nat]("r + j"), b.TermAs[A]("x(a)")),
										coordinates.At(point),
										live,
										given))
							})),
						Case(
							"the degeneracy identity holds in each coordinate",
							Derive(func(b *Argument) {
								b.FixAs[Nat]("n")
								b.FixAs[Nat]("i")
								b.FixAs[Nat]("j")
								b.FixAs[Fun[Nat, A]]("x")
								given := b.Assume()
								coordinates := b.Have(
									"read the input coordinate data",
									"∀a:num. a ∈ 0 .. r ⇒ x(a) ∈ X.simplices(r + n)",
									BySets(b.Unfolded(b.Unfolded(given, SimplexBoundaryConeSimplicesDef), FaceFamilyDef)))
								b.Do(Simp(Fwd(simplexBoundaryConeDegeneracyDef), Fwd(functions.NormalizeOnEqIff)))
								point := b.FixAs[Nat]("a")
								live := b.Assume()
								b.Do(Simp(Fwd(functions.NormalizeOnIn)))
								dimensions := b.Have(
									"align the shifted dimensions and indices",
									"r + (n + 1) = r + n + 1 ∧ r + (j + 1) = r + j + 1",
									ByArith())
								bridges := b.Conjuncts(
									dimensions,
									"degree n + 1 of a coordinate is degree (r + n) + 1 of X",
									"the shift of j + 1 is the shift of j, plus one")
								b.Show(
									"the ambient identity applies to this coordinate",
									bridges[0].Rw(),
									bridges[1].Rw(),
									ByArith(
										DegeneracyDegeneracy.Read(simplicial).At(
											b.TermAs[Nat]("r + n"), b.TermAs[Nat]("r + i"), b.TermAs[Nat]("r + j"), b.TermAs[A]("x(a)")),
										coordinates.At(point),
										live,
										given))
							})),
						Case(
							"a lower face passes a tail degeneracy in each coordinate",
							Derive(func(b *Argument) {
								b.FixAs[Nat]("n")
								b.FixAs[Nat]("i")
								b.FixAs[Nat]("j")
								b.FixAs[Fun[Nat, A]]("x")
								given := b.Assume()
								coordinates := b.Have(
									"read the input coordinate data",
									"∀a:num. a ∈ 0 .. r ⇒ x(a) ∈ X.simplices(r + (n + 1))",
									BySets(b.Unfolded(b.Unfolded(given, SimplexBoundaryConeSimplicesDef), FaceFamilyDef)))
								b.Do(Simp(
									Fwd(SimplexBoundaryConeFaceDef),
									Fwd(simplexBoundaryConeDegeneracyDef),
									Fwd(functions.NormalizeOnEqIff)))
								point := b.FixAs[Nat]("a")
								live := b.Assume()
								b.Do(Simp(Fwd(functions.NormalizeOnIn)))
								dimensions := b.Have(
									"align the shifted dimensions and indices",
									"r + (n + 1) = r + n + 1 ∧ r + (n + 2) = r + n + 2 ∧ r + (j - 1) = r + j - 1",
									ByArith(given))
								bridges := b.Conjuncts(
									dimensions,
									"degree n + 1 of a coordinate is degree (r + n) + 1 of X",
									"degree n + 2 of a coordinate is degree (r + n) + 2 of X",
									"the shift of j − 1 is the shift of j, less one")
								b.Show(
									"the ambient identity applies to this coordinate",
									bridges[0].Rw(),
									bridges[1].Rw(),
									bridges[2].Rw(),
									ByArith(
										FaceDegeneracyBelow.Read(simplicial).At(
											b.TermAs[Nat]("r + n"), b.TermAs[Nat]("r + i"), b.TermAs[Nat]("r + j"), b.TermAs[A]("x(a)")),
										coordinates.At(point),
										live,
										given))
							})),
						Case(
							"the repeated face cancels a tail degeneracy in each coordinate",
							Derive(func(b *Argument) {
								b.FixAs[Nat]("n")
								b.FixAs[Nat]("i")
								b.FixAs[Fun[Nat, A]]("x")
								given := b.Assume()
								data := b.Have(
									"read the input coordinate data",
									"x = normalize_on(0 .. r, junk, x) ∧ (∀a:num. a ∈ 0 .. r ⇒ x(a) ∈ X.simplices(r + n))",
									BySets(b.Unfolded(b.Unfolded(given, SimplexBoundaryConeSimplicesDef), FaceFamilyDef)))
								parts := b.Conjuncts(
									data,
									"x has normalized padding",
									"its live coordinates have the prescribed dimension")
								padding, coordinates := parts[0], parts[1]
								b.Do(Simp(Fwd(SimplexBoundaryConeFaceDef), Fwd(simplexBoundaryConeDegeneracyDef)))
								b.Show(
									"the two sides agree on 0 .. r, and x is normalized past r",
									CalcEq(
										Leg(
											b.TermAs[Fun[Nat, A]]("normalize_on(0 .. r, junk, x)"),
											"on 0 .. r each coordinate is the ambient identity",
											Simp(Fwd(functions.NormalizeOnEqIff)),
											Derive(func(c *Argument) {
												point := c.FixAs[Nat]("a")
												live := c.Assume()
												c.Do(Simp(Fwd(functions.NormalizeOnIn)))
												dimensions := c.Have(
													"align the shifted dimensions and indices",
													"r + (n + 1) = r + n + 1",
													ByArith())
												c.Show(
													"the ambient identity applies to this coordinate",
													dimensions.Rw(),
													ByArith(
														FaceDegeneracyEqual.Read(simplicial).At(
															c.TermAs[Nat]("r + n"), c.TermAs[Nat]("r + i"), c.TermAs[A]("x(a)")),
														coordinates.At(point),
														live,
														given))
											})),
										FinalLeg(
											"x is its own normalization, by its padding",
											By(Normalized, padding)),
									))
							})),
						Case(
							"the next face cancels a tail degeneracy in each coordinate",
							Derive(func(b *Argument) {
								b.FixAs[Nat]("n")
								b.FixAs[Nat]("i")
								b.FixAs[Fun[Nat, A]]("x")
								given := b.Assume()
								data := b.Have(
									"read the input coordinate data",
									"x = normalize_on(0 .. r, junk, x) ∧ (∀a:num. a ∈ 0 .. r ⇒ x(a) ∈ X.simplices(r + n))",
									BySets(b.Unfolded(b.Unfolded(given, SimplexBoundaryConeSimplicesDef), FaceFamilyDef)))
								parts := b.Conjuncts(
									data,
									"x has normalized padding",
									"its live coordinates have the prescribed dimension")
								padding, coordinates := parts[0], parts[1]
								b.Do(Simp(Fwd(SimplexBoundaryConeFaceDef), Fwd(simplexBoundaryConeDegeneracyDef)))
								b.Show(
									"the two sides agree on 0 .. r, and x is normalized past r",
									CalcEq(
										Leg(
											b.TermAs[Fun[Nat, A]]("normalize_on(0 .. r, junk, x)"),
											"on 0 .. r each coordinate is the ambient identity",
											Simp(Fwd(functions.NormalizeOnEqIff)),
											Derive(func(c *Argument) {
												point := c.FixAs[Nat]("a")
												live := c.Assume()
												c.Do(Simp(Fwd(functions.NormalizeOnIn)))
												dimensions := c.Have(
													"align the shifted dimensions and indices",
													"r + (n + 1) = r + n + 1 ∧ r + (i + 1) = r + i + 1",
													ByArith())
												bridges := c.Conjuncts(
													dimensions,
													"degree n + 1 of a coordinate is degree (r + n) + 1 of X",
													"the shift of i + 1 is the shift of i, plus one")
												c.Show(
													"the ambient identity applies to this coordinate",
													bridges[0].Rw(),
													bridges[1].Rw(),
													ByArith(
														FaceDegeneracyNext.Read(simplicial).At(
															c.TermAs[Nat]("r + n"), c.TermAs[Nat]("r + i"), c.TermAs[A]("x(a)")),
														coordinates.At(point),
														live,
														given))
											})),
										FinalLeg(
											"x is its own normalization, by its padding",
											By(Normalized, padding)),
									))
							})),
						Case(
							"an upper face passes a tail degeneracy in each coordinate",
							Derive(func(b *Argument) {
								b.FixAs[Nat]("n")
								b.FixAs[Nat]("i")
								b.FixAs[Nat]("j")
								b.FixAs[Fun[Nat, A]]("x")
								given := b.Assume()
								coordinates := b.Have(
									"read the input coordinate data",
									"∀a:num. a ∈ 0 .. r ⇒ x(a) ∈ X.simplices(r + (n + 1))",
									BySets(b.Unfolded(b.Unfolded(given, SimplexBoundaryConeSimplicesDef), FaceFamilyDef)))
								b.Do(Simp(
									Fwd(SimplexBoundaryConeFaceDef),
									Fwd(simplexBoundaryConeDegeneracyDef),
									Fwd(functions.NormalizeOnEqIff)))
								point := b.FixAs[Nat]("a")
								live := b.Assume()
								b.Do(Simp(Fwd(functions.NormalizeOnIn)))
								dimensions := b.Have(
									"align the shifted dimensions and indices",
									"r + (n + 1) = r + n + 1 ∧ r + (n + 2) = r + n + 2 ∧ r + (i - 1) = r + i - 1",
									ByArith(given))
								bridges := b.Conjuncts(
									dimensions,
									"degree n + 1 of a coordinate is degree (r + n) + 1 of X",
									"degree n + 2 of a coordinate is degree (r + n) + 2 of X",
									"the shift of i − 1 is the shift of i, less one")
								b.Show(
									"the ambient identity applies to this coordinate",
									bridges[0].Rw(),
									bridges[1].Rw(),
									bridges[2].Rw(),
									ByArith(
										FaceDegeneracyAbove.Read(simplicial).At(
											b.TermAs[Nat]("r + n"), b.TermAs[Nat]("r + i"), b.TermAs[Nat]("r + j"), b.TermAs[A]("x(a)")),
										coordinates.At(point),
										live,
										given))
							})),
					))
			})
		}),
})}

// ConeRestrictionMap — restriction from the cone to its boundary cone
// is simplicial: the r + 1 prefix faces of a cone simplex are compatible
// by FaceFace, and each, its tail removed, is the matching face of k, by
// FaceIterateTopFace below r and FaceIterateTopAbove at r; a prefix face
// passes a tail face by FaceFace and a tail degeneracy by
// FaceDegeneracyBelow.
var ConeRestrictionMap = coneRestrictionMapThm{family.Add(registry.ProofEntry{
	Name: "ConeRestrictionMap",
	Key:  "prop_9e949c43e387fa05",
	Build: SimplicialSet.Law("∀r:num. ∀k:A. "+
		"    simplicial_map(simplex_cone(X, r, k), "+
		"        simplex_boundary_cone(X, r, k), "+
		"        simplex_cone_restriction(r))",
		func(arg *Argument, simplicial Fact, r *Expr[Nat], k *Expr[A]) {
			arg.Show(
				"restriction carries cone simplices to boundary-cone "+
					"simplices and commutes with the tail operators",
				Simp(Fwd(SimplicialMap)),
				SplitConjAll(
					Case(
						"the simplex cone is the source simplicial set",
						By(SimplexConeSimplicialSet.Read(simplicial).At(r, k))),
					Case(
						"the boundary cone is the target simplicial set",
						By(BoundaryConeSimplicialSet.Read(simplicial).At(r, k))),
					Case(
						"the prefix faces form a boundary-cone simplex",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]("n")
							x := b.FixAs[A]("x")
							inCone := b.Assume()
							data := b.Have(
								"read the ambient dimension and fixed top face",
								"x ∈ X.simplices(r + n + 1) ∧ face_iterate_top(r + n + 1, n + 1, x) = k",
								BySets(b.Unfolded(inCone, SimplexConeSimplicesDef)))
							parts := b.Conjuncts(
								data,
								"x has the ambient input dimension",
								"its first r + 1 vertices form k")
							simplex, fixed := parts[0], parts[1]
							prefixFaces := b.TermAs[Fun[Nat, A]]("λj:num. X.d(r + n + 1, j, x)")
							coordinates := b.Have(
								"each live prefix face has the target dimension",
								"∀j:num. j ∈ 0 .. r ⇒ X.d(r + n + 1, j, x) ∈ X.simplices(r + n)",
								Derive(func(c *Argument) {
									j := c.FixAs[Nat]("j")
									live := c.Assume()
									bounded := c.Have(
										"j is at most r",
										"j ≤ r",
										By(live))
									c.Show(
										"ambient face closure gives the coordinate dimension",
										ByArith(bounded, simplex, FaceIn.Read(simplicial).At(c.TermAs[Nat]("r + n"), j, x)))
								}))
							compatible := b.Have(
								"the prefix faces satisfy boundary compatibility",
								Statement{
									Binders: "∀i j:num.",
									Hypotheses: []string{
										"i ∈ 0 .. r",
										"j ∈ 0 .. r",
										"i < j",
									},
									Conclusion: "X.d(r + n, i, X.d(r + n + 1, j, x)) = X.d(r + n, j - 1, X.d(r + n + 1, i, x))",
								},
								Derive(func(c *Argument) {
									i, j := c.FixAs[Nat]("i"), c.FixAs[Nat]("j")
									rangeIJ := c.Assume()
									bounded := c.Have(
										"both prefix indices are at most r",
										"i ≤ r ∧ j ≤ r",
										By(rangeIJ))
									m, lower := c.ObtainAs[Nat](
										"two distinct prefix vertices make r + n positive",
										"∃m:num. r + n = m + 1",
										ByArith(rangeIJ, bounded, nat_arith.NonzeroIsSucc.At(c.TermAs[Nat]("r + n"))))
									upper := c.Have(
										"x has dimension m + 2",
										"r + n + 1 = m + 2",
										ByArith(lower))
									c.Show(
										"the ambient face identity is the prefix compatibility equation",
										upper.Rw(),
										lower.Rw(),
										ByArith(rangeIJ, bounded, simplex, upper, lower, FaceFace.Read(simplicial).At(m, i, j, x)))
								}))
							retains := b.Have(
								"each prefix face has the prescribed boundary of k",
								"∀j:num. 0 < r ∧ j ≤ r ⇒ face_iterate_top(r + n, n + 1, X.d(r + n + 1, j, x)) = X.d(r, j, k)",
								Derive(func(c *Argument) {
									j := c.FixAs[Nat]("j")
									positive := c.Assume()
									dimension := c.Have(
										"removing the n + 1 tail vertices leaves dimension r",
										"r + n + 1 - (n + 1) = r",
										ByArith())
									c.Cases(c.TermAs[Bool]("j < r"))
									c.When(
										"below r the prefix face passes the top iteration",
										func(e *Argument, below Fact) {
											commutes := e.Have(
												"the prefix face commutes with removal of the tail",
												"face_iterate_top(r + n, n + 1, X.d(r + n + 1, j, x)) = "+
													"X.d(r + n + 1 - (n + 1), j, face_iterate_top(r + n + 1, n + 1, x))",
												ByArith(
													simplex,
													below,
													FaceIterateTopFace.Read(simplicial).At(e.TermAs[Nat]("r + n"), e.TermAs[Nat]("n + 1"), j, x)))
											e.Show(
												"the remaining top face is the j-th face of k",
												By(commutes, dimension, fixed))
										})
									c.Otherwise(
										"at r one more top removal is the last face of k",
										func(e *Argument, notBelow Fact) {
											last := e.Have(
												"the remaining prefix index is r",
												"j = r",
												ByArith(positive, notBelow))
											absorbed := e.Have(
												"the face at r is absorbed by one more top removal",
												"face_iterate_top(r + n, n + 1, X.d(r + n + 1, j, x)) = face_iterate_top(r + n + 1, n + 1 + 1, x)",
												ByArith(
													simplex,
													positive,
													last,
													FaceIterateTopAbove.Read(simplicial).At(e.TermAs[Nat]("r + n"), e.TermAs[Nat]("n + 1"), j, x)))
											oneMore := FaceIterateTopSucc.At(
												e.TermAs[Fun3[Nat, Nat, A, A]]("X.d"), e.TermAs[Nat]("r + n + 1"), e.TermAs[Nat]("n + 1"), x)
											e.Show(
												"that last face is the r-th face of k",
												By(Normalized, absorbed, oneMore, dimension, fixed, last))
										})
								}))
							family := b.Have(
								"the prefix faces form a face family on 0 .. r",
								"face_family(r + n, 0 .. r, λj:num. X.d(r + n + 1, j, x))",
								Simp(Fwd(FaceFamilyDef), Fwd(FacesCompatibleDef)),
								By(coordinates, compatible))
							b.Show(
								"so the normalized prefix faces lie in the boundary cone",
								Simp(Fwd(SimplexConeRestrictionDef)),
								By(
									At(BoundaryConeMembership, b.TermAs[SimplicialOps[A]]("X"), r, n, k, prefixFaces),
									family,
									retains))
						})),
					Case(
						"restriction commutes with each tail face",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							x := b.FixAs[A]("x")
							given := b.Assume()
							source := b.Have(
								"x has the ambient input dimension",
								"x ∈ X.simplices(r + (n + 1) + 1)",
								BySets(b.Unfolded(given, SimplexConeSimplicesDef)))
							b.Do(Simp(
								Fwd(SimplexConeRestrictionDef),
								Fwd(SimplexConeFaceDef),
								Fwd(SimplexBoundaryConeFaceDef),
								Fwd(functions.NormalizeOnEqIff)))
							point := b.FixAs[Nat]("a")
							live := b.Assume()
							bounded := b.Have(
								"the prefix index is at most r",
								"a ≤ r",
								By(live))
							b.Do(Simp(Fwd(functions.NormalizeOnIn)))
							dimensions := b.Have(
								"align both successor dimensions and the lowered tail index",
								"r + (n + 1) + 1 = r + n + 2 ∧ r + (n + 1) = r + n + 1 ∧ r + 1 + i - 1 = r + i",
								ByArith())
							bridges := b.Conjuncts(
								dimensions,
								"the input dimension is r + n + 2",
								"the output dimension is r + n + 1",
								"the tail index lowers to r + i")
							ambientIn := b.Have(
								"write x in the dimension read by the face identity",
								"x ∈ X.simplices(r + n + 2)",
								bridges[0].Rw(),
								By(source))
							commutes := b.Have(
								"the ambient face identity passes the prefix face",
								"X.d(r + n + 1, a, X.d(r + n + 2, r + 1 + i, x)) = "+
									"X.d(r + n + 1, r + 1 + i - 1, X.d(r + n + 2, a, x))",
								ByArith(
									ambientIn,
									given,
									bounded,
									FaceFace.Read(simplicial).At(b.TermAs[Nat]("r + n"), point, b.TermAs[Nat]("r + 1 + i"), x)))
							b.Show(
								"the coordinate equality follows after aligning the dimensions",
								By(commutes, bridges[0], bridges[1], bridges[2]))
						})),
					Case(
						"restriction commutes with each tail degeneracy",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							x := b.FixAs[A]("x")
							given := b.Assume()
							source := b.Have(
								"x has the ambient input dimension",
								"x ∈ X.simplices(r + n + 1)",
								BySets(b.Unfolded(given, SimplexConeSimplicesDef)))
							b.Do(Simp(
								Fwd(SimplexConeRestrictionDef),
								Fwd(simplexConeDegeneracyDef),
								Fwd(simplexBoundaryConeDegeneracyDef),
								Fwd(functions.NormalizeOnEqIff)))
							point := b.FixAs[Nat]("a")
							live := b.Assume()
							bounded := b.Have(
								"the prefix index is at most r",
								"a ≤ r",
								By(live))
							b.Do(Simp(Fwd(functions.NormalizeOnIn)))
							dimensions := b.Have(
								"align the successor dimension and the lowered tail index",
								"r + (n + 1) + 1 = r + n + 2 ∧ r + 1 + i - 1 = r + i",
								ByArith())
							bridges := b.Conjuncts(
								dimensions,
								"the output dimension is r + n + 2",
								"the tail index lowers to r + i")
							commutes := b.Have(
								"the mixed identity passes the prefix face",
								"X.d(r + n + 2, a, X.s(r + n + 1, r + 1 + i, x)) = X.s(r + n, r + 1 + i - 1, X.d(r + n + 1, a, x))",
								ByArith(
									source,
									given,
									bounded,
									FaceDegeneracyBelow.Read(simplicial).At(
										b.TermAs[Nat]("r + n"), point, b.TermAs[Nat]("r + 1 + i"), x)))
							b.Show(
								"the coordinate equality follows after aligning dimension and index",
								By(commutes, bridges[0], bridges[1]))
						})),
				))
		}),
})}

// ConeProjectionMap — projection from the boundary cone to X is
// simplicial: the projection keeps the tail of the zeroth prefix face,
// its bottom r vertices removed, which is a simplex of X by
// FaceIterateBottomIn and commutes with a tail face by
// FaceIterateBottomFace and with a tail degeneracy by
// FaceIterateBottomDegeneracy.
var ConeProjectionMap = coneProjectionMapThm{family.Add(registry.ProofEntry{
	Name: "ConeProjectionMap",
	Key:  "prop_9c9a8f0f0c986488",
	Build: SimplicialSet.Law("∀r:num. ∀k:A. "+
		"    simplicial_map(simplex_boundary_cone(X, r, k), X, simplex_boundary_cone_projection(r))",
		func(a *Argument, simplicial Fact, r *Expr[Nat], k *Expr[A]) {
			a.Show(
				"projection carries boundary-cone simplices to simplices of X and commutes with the tail operators",
				Simp(Fwd(SimplicialMap)),
				SplitConjAll(
					Case(
						"the boundary cone is the source simplicial set",
						By(BoundaryConeSimplicialSet.Read(simplicial).At(r, k))),
					Case(
						"the ambient simplicial set is the target",
						By(simplicial)),
					Case(
						"removing the prefix vertices gives a simplex of the target degree",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Fun[Nat, A]]("x")
							inCone := b.Assume()
							coordinates := b.Have(
								"read the live coordinate dimensions",
								"∀j:num. j ∈ 0 .. r ⇒ x(j) ∈ X.simplices(r + n)",
								BySets(b.Unfolded(b.Unfolded(inCone, SimplexBoundaryConeSimplicesDef), FaceFamilyDef)))
							zero := b.TermAs[Nat]("0")
							zeroLive := b.Have(
								"the zeroth coordinate is in the live interval",
								"0 ∈ 0 .. r",
								ByArith())
							zeroIn := b.Have(
								"the zeroth coordinate has the ambient input dimension",
								"x(0) ∈ X.simplices(r + n)",
								By(coordinates.At(zero), zeroLive))
							dimension := b.Have(
								"removing r prefix vertices leaves dimension n",
								"r + n - r = n",
								ByArith())
							b.Show(
								"bottom-iterate closure gives the projected simplex",
								Simp(Fwd(SimplexBoundaryConeProjectionDef)),
								ByArith(
									zeroIn,
									dimension,
									FaceIterateBottomIn.Read(simplicial).At(b.TermAs[Nat]("r + n"), r, b.TermAs[A]("x(0)"))))
						})),
					Case(
						"projection commutes with each tail face",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							b.FixAs[Fun[Nat, A]]("x")
							given := b.Assume()
							coordinates := b.Have(
								"read the live coordinate dimensions",
								"∀j:num. j ∈ 0 .. r ⇒ x(j) ∈ X.simplices(r + (n + 1))",
								BySets(b.Unfolded(b.Unfolded(given, SimplexBoundaryConeSimplicesDef), FaceFamilyDef)))
							zero := b.TermAs[Nat]("0")
							zeroLive := b.Have(
								"the zeroth coordinate is in the live interval",
								"0 ∈ 0 .. r",
								ByArith())
							zeroIn := b.Have(
								"the zeroth coordinate has the source dimension",
								"x(0) ∈ X.simplices(r + (n + 1))",
								By(coordinates.At(zero), zeroLive))
							dimensions := b.Have(
								"align the successor dimension and remove the prefix from dimension and index",
								"r + (n + 1) = r + n + 1 ∧ r + n + 1 - r = n + 1 ∧ r + i - r = i",
								ByArith())
							bridges := b.Conjuncts(
								dimensions,
								"the successor dimension is aligned",
								"the output dimension is n + 1",
								"the output face index is i")
							ambientIn := b.Have(
								"write the zeroth coordinate in the successor dimension read by the face law",
								"x(0) ∈ X.simplices(r + n + 1)",
								bridges[0].Rw(),
								By(zeroIn))
							commutes := b.Have(
								"the r-fold bottom iterate passes the face at r + i",
								"face_iterate_bottom(r + n, r, X.d(r + n + 1, r + i, x(0))) = "+
									"X.d(r + n + 1 - r, r + i - r, face_iterate_bottom(r + n + 1, r, x(0)))",
								ByArith(
									ambientIn,
									given,
									FaceIterateBottomFace.Read(simplicial).At(
										b.TermAs[Nat]("r + n"), r, b.TermAs[Nat]("r + i"), b.TermAs[A]("x(0)"))))
							b.Show(
								"read the normalized zeroth coordinate and align the face dimensions",
								Simp(
									Fwd(SimplexBoundaryConeProjectionDef),
									Fwd(SimplexBoundaryConeFaceDef),
									Fwd(functions.NormalizeOnIn)),
								By(commutes, bridges[0], bridges[1], bridges[2]))
						})),
					Case(
						"projection commutes with each tail degeneracy",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							b.FixAs[Fun[Nat, A]]("x")
							given := b.Assume()
							coordinates := b.Have(
								"read the live coordinate dimensions",
								"∀j:num. j ∈ 0 .. r ⇒ x(j) ∈ X.simplices(r + n)",
								BySets(b.Unfolded(b.Unfolded(given, SimplexBoundaryConeSimplicesDef), FaceFamilyDef)))
							zero := b.TermAs[Nat]("0")
							zeroLive := b.Have(
								"the zeroth coordinate is in the live interval",
								"0 ∈ 0 .. r",
								ByArith())
							zeroIn := b.Have(
								"the zeroth coordinate has the ambient input dimension",
								"x(0) ∈ X.simplices(r + n)",
								By(coordinates.At(zero), zeroLive))
							dimensions := b.Have(
								"align the successor dimension and remove the prefix from dimension and index",
								"r + (n + 1) = r + n + 1 ∧ r + n - r = n ∧ r + i - r = i",
								ByArith())
							bridges := b.Conjuncts(
								dimensions,
								"the successor dimension is aligned",
								"the input dimension is n",
								"the output degeneracy index is i")
							commutes := b.Have(
								"the r-fold bottom iterate passes the degeneracy at r + i",
								"face_iterate_bottom(r + n + 1, r, X.s(r + n, r + i, x(0))) = "+
									"X.s(r + n - r, r + i - r, face_iterate_bottom(r + n, r, x(0)))",
								ByArith(
									zeroIn,
									given,
									FaceIterateBottomDegeneracy.Read(simplicial).At(
										b.TermAs[Nat]("r + n"), r, b.TermAs[Nat]("r + i"), b.TermAs[A]("x(0)"))))
							b.Show(
								"read the normalized zeroth coordinate and align the degeneracy dimensions",
								Simp(
									Fwd(SimplexBoundaryConeProjectionDef),
									Fwd(simplexBoundaryConeDegeneracyDef),
									Fwd(functions.NormalizeOnIn)),
								By(commutes, bridges[0], bridges[1], bridges[2]))
						})),
				))
		}),
})}
