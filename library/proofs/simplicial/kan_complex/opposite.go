// opposite.go — the opposite of a Kan complex is a Kan complex. A horn
// of dimension n + 1 missing the face k is a face family on
// horn_faces(n, k); a face family of the opposite there is, its members
// reindexed by i ↦ n + 1 − i, a face family of X on
// horn_faces(n, n + 1 − k), and the two have the same fillers, the
// opposite's face i of an (n+1)-simplex being X's face n + 1 − i.

package kan_complex

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// HornFamilyOpposite — a family is a horn of the opposite missing the
// face k, a face family of the opposite on horn_faces(n, k), exactly
// when, reindexed by i ↦ n + 1 − i, it is a horn of X missing the face
// n + 1 − k, a face family of X on horn_faces(n, n + 1 − k). Reversal is
// an involution of the indices 0 .. n + 1 exchanging k and n + 1 − k, so
// it carries the faces of the one horn onto the faces of the other, and
// the members are the same n-simplices; it carries a pair i < j of faces
// of the one horn to the pair n + 1 − j < n + 1 − i of faces of the
// other, and the two compatibility conditions there are one equation,
// the opposite's face i of y(j) being X's face n − i = (n + 1 − i) − 1,
// and its face j − 1 of y(i) X's face n − (j − 1) = n + 1 − j.
var HornFamilyOpposite = hornFamilyOppositeThm{family.Add(registry.ProofEntry{
	Name: "HornFamilyOpposite",
	Key:  "prop_4ad15ed8cfa9057e",
	Build: family.Theorem(Statement{
		Binders: "∀X:simplicial_ops(A). ∀n k:num. ∀y:(num → A).",
		Hypotheses: []string{
			"k ≤ n + 1",
		},
		Conclusion: "face_family(opposite_simplicial_set(X), n, horn_faces(n, k), y) ⇔ " +
			"face_family(X, n, horn_faces(n, n + 1 - k), λi:num. y(n + 1 - i))",
	},
		func(
			a *Argument,
			X *Expr[simplicial_set.SimplicialOps[A]],
			n *Expr[Nat],
			k *Expr[Nat],
			y *Arrow[Nat, A],
			bound Fact,
		) {
			reversedFace := a.TermAs[Nat]("n + 1 - k")
			a.Iff()
			a.Forward(
				"a horn of the opposite, reversed, is a horn of X",
				func(b *Argument, opposite Fact) {
					given := b.Conjuncts(
						b.Unfolded(opposite, simplicial_set.FaceFamilyDef),
						"the members of y on the faces of the horn missing k are n-simplices of X",
						"and they are compatible in the opposite")
					members := given[0]
					matching := b.Simplified(
						given[1],
						Fwd(simplicial_set.FacesCompatibleDef),
						Fwd(simplicial_set.OppositeFaceDef))
					reversedMembers := b.Have(
						"the members of the reversal on the faces of the horn missing n + 1 − k are n-simplices of X",
						"∀i:num. i ∈ horn_faces(n, n + 1 - k) ⇒ y(n + 1 - i) ∈ X.simplices(n)",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							index := c.Have(
								"a face i of the horn missing n + 1 − k is at most n + 1 and not n + 1 − k",
								"i ≤ n + 1 ∧ ¬(i = n + 1 - k)",
								By(c.Assume(), HornFacesMember.At(n, reversedFace, i)))
							bounds := c.Have(
								"so the reversed index n + 1 − i is at most n + 1 and not k",
								"n + 1 - i ≤ n + 1 ∧ ¬(n + 1 - i = k)",
								ByArith(bound, index))
							c.Show(
								"and y(n + 1 − i), a member of y on a face of the horn missing k, is an n-simplex of X",
								By(
									members.At(c.TermAs[Nat]("n + 1 - i")),
									bounds,
									HornFacesMember.At(n, k, c.TermAs[Nat]("n + 1 - i"))))
						}))
					reversedCompatible := b.Have(
						"and X's faces of each pair of them are the opposite's faces of the reversed pair",
						"faces_compatible(n, horn_faces(n, n + 1 - k), λi:num. y(n + 1 - i))",
						Derive(func(c *Argument) {
							c.Do(Simp(Fwd(simplicial_set.FacesCompatibleDef)))
							i, j := c.FixAs[Nat]("i"), c.FixAs[Nat]("j")
							pair := c.Assume()
							faces := c.Have(
								"i and j are indices at most n + 1, neither of them n + 1 − k",
								"i ≤ n + 1 ∧ ¬(i = n + 1 - k) ∧ j ≤ n + 1 ∧ ¬(j = n + 1 - k)",
								By(pair, HornFacesMember.At(n, reversedFace, i), HornFacesMember.At(n, reversedFace, j)))
							bounds := c.Have(
								"the reversed pair n + 1 − j < n + 1 − i is a pair of indices at most n + 1, neither of them k",
								"n + 1 - j < n + 1 - i ∧ "+
									"n + 1 - j ≤ n + 1 ∧ "+
									"¬(n + 1 - j = k) ∧ "+
									"n + 1 - i ≤ n + 1 ∧ "+
									"¬(n + 1 - i = k)",
								ByArith(bound, faces, pair))
							reversed := c.Have(
								"so it is a pair of faces of the horn missing k",
								"n + 1 - j ∈ horn_faces(n, k) ∧ n + 1 - i ∈ horn_faces(n, k)",
								By(
									bounds,
									HornFacesMember.At(n, k, c.TermAs[Nat]("n + 1 - j")),
									HornFacesMember.At(n, k, c.TermAs[Nat]("n + 1 - i"))))
							indices := c.Have(
								"the opposite's faces at the reversed pair are X's faces j − 1 and i",
								"n - (n + 1 - j) = j - 1 ∧ n - (n + 1 - i - 1) = i",
								ByArith(faces, pair))
							c.Show(
								"so the opposite's compatibility at the reversed pair is X's at (i, j)",
								By(matching.At(c.TermAs[Nat]("n + 1 - j"), c.TermAs[Nat]("n + 1 - i")), reversed, bounds, indices))
						}))
					b.Show(
						"so the reversal is a face family of X on the faces of the horn missing n + 1 − k",
						Simp(Fwd(simplicial_set.FaceFamilyDef)),
						By(reversedMembers, reversedCompatible))
				})
			a.Backward(
				"a family whose reversal is a horn of X is a horn of the opposite",
				func(b *Argument, reversed Fact) {
					given := b.Conjuncts(
						b.Unfolded(reversed, simplicial_set.FaceFamilyDef),
						"the members of the reversal on the faces of the horn missing n + 1 − k are n-simplices of X",
						"and they are compatible in X")
					members := given[0]
					matching := b.Simplified(given[1], Fwd(simplicial_set.FacesCompatibleDef))
					originalMembers := b.Have(
						"the members of y on the faces of the horn missing k are n-simplices of X",
						"∀i:num. i ∈ horn_faces(n, k) ⇒ y(i) ∈ X.simplices(n)",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							index := c.Have(
								"a face i of the horn missing k is at most n + 1 and not k",
								"i ≤ n + 1 ∧ ¬(i = k)",
								By(c.Assume(), HornFacesMember.At(n, k, i)))
							bounds := c.Have(
								"so the reversed index n + 1 − i is at most n + 1 and not n + 1 − k",
								"n + 1 - i ≤ n + 1 ∧ ¬(n + 1 - i = n + 1 - k)",
								ByArith(bound, index))
							involution := c.Have(
								"and reversing it again returns i",
								"n + 1 - (n + 1 - i) = i",
								ByArith(index))
							c.Show(
								"so y(i), the reversal's member on the face n + 1 − "+
									"i of the horn missing n + 1 − k, is an n-simplex of X",
								By(
									members.At(c.TermAs[Nat]("n + 1 - i")),
									bounds,
									involution,
									HornFacesMember.At(n, reversedFace, c.TermAs[Nat]("n + 1 - i"))))
						}))
					originalCompatible := b.Have(
						"and the opposite's faces of each pair of them are X's faces of the reversed pair",
						"faces_compatible(opposite_face(X.d), n, horn_faces(n, k), y)",
						Derive(func(c *Argument) {
							c.Do(Simp(Fwd(simplicial_set.FacesCompatibleDef), Fwd(simplicial_set.OppositeFaceDef)))
							i, j := c.FixAs[Nat]("i"), c.FixAs[Nat]("j")
							pair := c.Assume()
							faces := c.Have(
								"i and j are indices at most n + 1, neither of them k",
								"i ≤ n + 1 ∧ ¬(i = k) ∧ j ≤ n + 1 ∧ ¬(j = k)",
								By(pair, HornFacesMember.At(n, k, i), HornFacesMember.At(n, k, j)))
							bounds := c.Have(
								"the reversed pair n + 1 − j < n + 1 − i is a pair "+
									"of indices at most n + 1, neither of them n + 1 − k",
								"n + 1 - j < n + 1 - i ∧ "+
									"n + 1 - j ≤ n + 1 ∧ "+
									"¬(n + 1 - j = n + 1 - k) ∧ "+
									"n + 1 - i ≤ n + 1 ∧ "+
									"¬(n + 1 - i = n + 1 - k)",
								ByArith(bound, faces, pair))
							reversedPair := c.Have(
								"so it is a pair of faces of the horn missing n + 1 − k",
								"n + 1 - j ∈ horn_faces(n, n + 1 - k) ∧ n + 1 - i ∈ horn_faces(n, n + 1 - k)",
								By(
									bounds,
									HornFacesMember.At(n, reversedFace, c.TermAs[Nat]("n + 1 - j")),
									HornFacesMember.At(n, reversedFace, c.TermAs[Nat]("n + 1 - i"))))
							involution := c.Have(
								"reversing the pair twice returns i and j",
								"n + 1 - (n + 1 - i) = i ∧ n + 1 - (n + 1 - j) = j",
								ByArith(faces))
							indices := c.Have(
								"the opposite's faces n − i and n − (j − 1) are X's faces n + 1 − i − 1 and n + 1 − j",
								"n - i = n + 1 - i - 1 ∧ n - (j - 1) = n + 1 - j",
								ByArith(faces, pair))
							c.Show(
								"so X's compatibility at the reversed pair is the opposite's at (i, j)",
								Simp(Fwd(indices)),
								By(
									matching.At(c.TermAs[Nat]("n + 1 - j"), c.TermAs[Nat]("n + 1 - i")),
									reversedPair,
									bounds,
									involution))
						}))
					b.Show(
						"so y is a face family of the opposite on the faces of the horn missing k",
						Simp(Fwd(simplicial_set.FaceFamilyDef)),
						By(originalMembers, originalCompatible))
				})
		}),
})}

// HornFillerOpposite — an (n+1)-simplex fills a horn of the opposite
// missing the face k, the family on horn_faces(n, k), exactly when it
// fills in X the family reindexed by i ↦ n + 1 − i on
// horn_faces(n, n + 1 − k): its face i in the opposite is its face
// n + 1 − i in X, and the reversal of the indices 0 .. n + 1 is an
// involution carrying the faces of the one horn onto the faces of the
// other.
var HornFillerOpposite = hornFillerOppositeThm{family.Add(registry.ProofEntry{
	Name: "HornFillerOpposite",
	Key:  "prop_ff6dad9311ec5a8d",
	Build: family.Theorem(Statement{
		Binders: "∀d:(num → num → A → A). ∀n k:num. ∀y:(num → A). ∀x:A.",
		Hypotheses: []string{
			"k ≤ n + 1",
		},
		Conclusion: "faces_filler(opposite_face(d), n, horn_faces(n, k), y, x) ⇔ " +
			"faces_filler(d, n, horn_faces(n, n + 1 - k), λi:num. y(n + 1 - i), x)",
	},
		func(
			a *Argument,
			d *Expr[Fun3[Nat, Nat, A, A]],
			n, k *Expr[Nat],
			y *Arrow[Nat, A],
			x *Expr[A],
			bound Fact,
		) {
			reversedFace := a.TermAs[Nat]("n + 1 - k")
			a.Iff()
			a.Forward(
				"a filler in the opposite fills the reversed horn in X",
				func(b *Argument, opposite Fact) {
					faces := b.Simplified(
						opposite,
						Fwd(simplicial_set.FacesFillerDef),
						Fwd(simplicial_set.OppositeFaceDef))
					b.Do(Simp(Fwd(simplicial_set.FacesFillerDef)))
					i := b.FixAs[Nat]("i")
					index := b.Have(
						"a face i of the horn missing n + 1 − k is at most n + 1 and not n + 1 − k",
						"i ≤ n + 1 ∧ ¬(i = n + 1 - k)",
						By(b.Assume(), HornFacesMember.At(n, reversedFace, i)))
					bounds := b.Have(
						"so the reversed index n + 1 − i is at most n + 1 and not k",
						"n + 1 - i ≤ n + 1 ∧ ¬(n + 1 - i = k)",
						ByArith(bound, index))
					involution := b.Have(
						"and reversing it again returns i",
						"n + 1 - (n + 1 - i) = i",
						ByArith(index))
					b.Show(
						"so the face i of x in X, its face n + 1 − i in the opposite, is y(n + 1 − i)",
						By(
							Normalized,
							faces.At(b.TermAs[Nat]("n + 1 - i")),
							bounds,
							involution,
							HornFacesMember.At(n, k, b.TermAs[Nat]("n + 1 - i"))))
				})
			a.Backward(
				"a filler of the reversed horn in X fills the horn of the opposite",
				func(b *Argument, reversed Fact) {
					faces := b.Simplified(reversed, Fwd(simplicial_set.FacesFillerDef))
					b.Do(Simp(Fwd(simplicial_set.FacesFillerDef), Fwd(simplicial_set.OppositeFaceDef)))
					i := b.FixAs[Nat]("i")
					index := b.Have(
						"a face i of the horn missing k is at most n + 1 and not k",
						"i ≤ n + 1 ∧ ¬(i = k)",
						By(b.Assume(), HornFacesMember.At(n, k, i)))
					bounds := b.Have(
						"so the reversed index n + 1 − i is at most n + 1 and not n + 1 − k",
						"n + 1 - i ≤ n + 1 ∧ ¬(n + 1 - i = n + 1 - k)",
						ByArith(bound, index))
					involution := b.Have(
						"and reversing it again returns i",
						"n + 1 - (n + 1 - i) = i",
						ByArith(index))
					b.Show(
						"so the face i of x in the opposite, its face n + 1 − i in X, is y(i)",
						By(
							faces.At(b.TermAs[Nat]("n + 1 - i")),
							bounds,
							involution,
							HornFacesMember.At(n, reversedFace, b.TermAs[Nat]("n + 1 - i"))))
				})
		}),
})}

// HornFamilyReversed — a family is a horn of X missing the face k, a
// face family of X on horn_faces(n, k), exactly when, reindexed by
// i ↦ n + 1 − i, it is a horn of the opposite missing the face n + 1 − k,
// a face family of the opposite on horn_faces(n, n + 1 − k):
// HornFamilyOpposite with X and the opposite exchanged, the family y
// standing as itself rather than reversed twice. Reversal carries the
// faces of the one horn onto the faces of the other, and a pair i < j of
// faces of the horn missing n + 1 − k to the pair n + 1 − j < n + 1 − i
// of faces of the horn missing k, where the two compatibility conditions
// are one equation, the opposite's face i of y(n + 1 − j) being X's face
// n − i = (n + 1 − i) − 1, and its face j − 1 of y(n + 1 − i) X's face
// n − (j − 1) = n + 1 − j.
var HornFamilyReversed = hornFamilyReversedThm{family.Add(registry.ProofEntry{
	Name: "HornFamilyReversed",
	Key:  "prop_63f6258c74103d56",
	Build: family.Theorem(Statement{
		Binders: "∀X:simplicial_ops(A). ∀n k:num. ∀y:(num → A).",
		Hypotheses: []string{
			"k ≤ n + 1",
		},
		Conclusion: "face_family(X, n, horn_faces(n, k), y) ⇔ " +
			"face_family(opposite_simplicial_set(X), n, horn_faces(n, n + 1 - k), λi:num. y(n + 1 - i))",
	},
		func(
			a *Argument,
			X *Expr[simplicial_set.SimplicialOps[A]],
			n *Expr[Nat],
			k *Expr[Nat],
			y *Arrow[Nat, A],
			bound Fact,
		) {
			reversedFace := a.TermAs[Nat]("n + 1 - k")
			a.Iff()
			a.Forward(
				"a horn of X, reversed, is a horn of the opposite",
				func(b *Argument, original Fact) {
					given := b.Conjuncts(
						b.Unfolded(original, simplicial_set.FaceFamilyDef),
						"the members of y on the faces of the horn missing k are n-simplices of X",
						"and they are compatible in X")
					members := given[0]
					matching := b.Simplified(given[1], Fwd(simplicial_set.FacesCompatibleDef))
					reversedMembers := b.Have(
						"the members of the reversal on the faces of the horn missing n + 1 − k are n-simplices of X",
						"∀i:num. i ∈ horn_faces(n, n + 1 - k) ⇒ y(n + 1 - i) ∈ X.simplices(n)",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							index := c.Have(
								"a face i of the horn missing n + 1 − k is at most n + 1 and not n + 1 − k",
								"i ≤ n + 1 ∧ ¬(i = n + 1 - k)",
								By(c.Assume(), HornFacesMember.At(n, reversedFace, i)))
							bounds := c.Have(
								"so the reversed index n + 1 − i is at most n + 1 and not k",
								"n + 1 - i ≤ n + 1 ∧ ¬(n + 1 - i = k)",
								ByArith(bound, index))
							c.Show(
								"and y(n + 1 − i), a member of y on a face of the horn missing k, is an n-simplex of X",
								By(
									members.At(c.TermAs[Nat]("n + 1 - i")),
									bounds,
									HornFacesMember.At(n, k, c.TermAs[Nat]("n + 1 - i"))))
						}))
					reversedCompatible := b.Have(
						"and the opposite's faces of each pair of them are X's faces of the reversed pair",
						"faces_compatible(opposite_face(X.d), n, horn_faces(n, n + 1 - k), λi:num. y(n + 1 - i))",
						Derive(func(c *Argument) {
							c.Do(Simp(Fwd(simplicial_set.FacesCompatibleDef), Fwd(simplicial_set.OppositeFaceDef)))
							i, j := c.FixAs[Nat]("i"), c.FixAs[Nat]("j")
							pair := c.Assume()
							faces := c.Have(
								"i and j are indices at most n + 1, neither of them n + 1 − k",
								"i ≤ n + 1 ∧ ¬(i = n + 1 - k) ∧ j ≤ n + 1 ∧ ¬(j = n + 1 - k)",
								By(pair, HornFacesMember.At(n, reversedFace, i), HornFacesMember.At(n, reversedFace, j)))
							bounds := c.Have(
								"the reversed pair n + 1 − j < n + 1 − i is a pair of indices at most n + 1, neither of them k",
								"n + 1 - j < n + 1 - i ∧ "+
									"n + 1 - j ≤ n + 1 ∧ "+
									"¬(n + 1 - j = k) ∧ "+
									"n + 1 - i ≤ n + 1 ∧ "+
									"¬(n + 1 - i = k)",
								ByArith(bound, faces, pair))
							reversed := c.Have(
								"so it is a pair of faces of the horn missing k",
								"n + 1 - j ∈ horn_faces(n, k) ∧ n + 1 - i ∈ horn_faces(n, k)",
								By(
									bounds,
									HornFacesMember.At(n, k, c.TermAs[Nat]("n + 1 - j")),
									HornFacesMember.At(n, k, c.TermAs[Nat]("n + 1 - i"))))
							indices := c.Have(
								"the opposite's faces n − i and n − (j − 1) are X's faces n + 1 − i − 1 and n + 1 − j",
								"n - i = n + 1 - i - 1 ∧ n - (j - 1) = n + 1 - j",
								ByArith(faces, pair))
							c.Show(
								"so the opposite's compatibility at (i, j) is X's at the reversed pair",
								Simp(Fwd(indices)),
								By(matching.At(c.TermAs[Nat]("n + 1 - j"), c.TermAs[Nat]("n + 1 - i")), reversed, bounds))
						}))
					b.Show(
						"so the reversal is a face family of the opposite on the faces of the horn missing n + 1 − k",
						Simp(Fwd(simplicial_set.FaceFamilyDef)),
						By(reversedMembers, reversedCompatible))
				})
			a.Backward(
				"a family whose reversal is a horn of the opposite is a horn of X",
				func(b *Argument, reversed Fact) {
					given := b.Conjuncts(
						b.Unfolded(reversed, simplicial_set.FaceFamilyDef),
						"the members of the reversal on the faces of the horn missing n + 1 − k are n-simplices of X",
						"and they are compatible in the opposite")
					members := given[0]
					matching := b.Simplified(
						given[1],
						Fwd(simplicial_set.FacesCompatibleDef),
						Fwd(simplicial_set.OppositeFaceDef))
					originalMembers := b.Have(
						"the members of y on the faces of the horn missing k are n-simplices of X",
						"∀i:num. i ∈ horn_faces(n, k) ⇒ y(i) ∈ X.simplices(n)",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							index := c.Have(
								"a face i of the horn missing k is at most n + 1 and not k",
								"i ≤ n + 1 ∧ ¬(i = k)",
								By(c.Assume(), HornFacesMember.At(n, k, i)))
							bounds := c.Have(
								"so the reversed index n + 1 − i is at most n + 1 and not n + 1 − k",
								"n + 1 - i ≤ n + 1 ∧ ¬(n + 1 - i = n + 1 - k)",
								ByArith(bound, index))
							involution := c.Have(
								"and reversing it again returns i",
								"n + 1 - (n + 1 - i) = i",
								ByArith(index))
							c.Show(
								"so y(i), the reversal's member on the face n + 1 − "+
									"i of the horn missing n + 1 − k, is an n-simplex of X",
								By(
									members.At(c.TermAs[Nat]("n + 1 - i")),
									bounds,
									involution,
									HornFacesMember.At(n, reversedFace, c.TermAs[Nat]("n + 1 - i"))))
						}))
					originalCompatible := b.Have(
						"and X's faces of each pair of them are the opposite's faces of the reversed pair",
						"faces_compatible(n, horn_faces(n, k), y)",
						Derive(func(c *Argument) {
							c.Do(Simp(Fwd(simplicial_set.FacesCompatibleDef)))
							i, j := c.FixAs[Nat]("i"), c.FixAs[Nat]("j")
							pair := c.Assume()
							faces := c.Have(
								"i and j are indices at most n + 1, neither of them k",
								"i ≤ n + 1 ∧ ¬(i = k) ∧ j ≤ n + 1 ∧ ¬(j = k)",
								By(pair, HornFacesMember.At(n, k, i), HornFacesMember.At(n, k, j)))
							bounds := c.Have(
								"the reversed pair n + 1 − j < n + 1 − i is a pair "+
									"of indices at most n + 1, neither of them n + 1 − k",
								"n + 1 - j < n + 1 - i ∧ "+
									"n + 1 - j ≤ n + 1 ∧ "+
									"¬(n + 1 - j = n + 1 - k) ∧ "+
									"n + 1 - i ≤ n + 1 ∧ "+
									"¬(n + 1 - i = n + 1 - k)",
								ByArith(bound, faces, pair))
							reversedPair := c.Have(
								"so it is a pair of faces of the horn missing n + 1 − k",
								"n + 1 - j ∈ horn_faces(n, n + 1 - k) ∧ n + 1 - i ∈ horn_faces(n, n + 1 - k)",
								By(
									bounds,
									HornFacesMember.At(n, reversedFace, c.TermAs[Nat]("n + 1 - j")),
									HornFacesMember.At(n, reversedFace, c.TermAs[Nat]("n + 1 - i"))))
							involution := c.Have(
								"reversing the pair twice returns i and j",
								"n + 1 - (n + 1 - i) = i ∧ n + 1 - (n + 1 - j) = j",
								ByArith(faces))
							indices := c.Have(
								"the opposite's faces at the reversed pair are X's faces j − 1 and i",
								"n - (n + 1 - j) = j - 1 ∧ n - (n + 1 - i - 1) = i",
								ByArith(faces, pair))
							c.Show(
								"so X's compatibility at (i, j) is the opposite's at the reversed pair",
								By(
									matching.At(c.TermAs[Nat]("n + 1 - j"), c.TermAs[Nat]("n + 1 - i")),
									reversedPair,
									bounds,
									involution,
									indices))
						}))
					b.Show(
						"so y is a face family of X on the faces of the horn missing k",
						Simp(Fwd(simplicial_set.FaceFamilyDef)),
						By(originalMembers, originalCompatible))
				})
		}),
})}

// HornFillerReversed — an (n+1)-simplex fills a horn of X missing the
// face k, the family on horn_faces(n, k), exactly when it fills in the
// opposite the family reindexed by i ↦ n + 1 − i on
// horn_faces(n, n + 1 − k): the reversal of HornFillerOpposite, its face
// i in the opposite being its face n + 1 − i in X, and the reversal of
// the indices 0 .. n + 1 an involution carrying the faces of the one
// horn onto the faces of the other.
var HornFillerReversed = hornFillerReversedThm{family.Add(registry.ProofEntry{
	Name: "HornFillerReversed",
	Key:  "prop_beb9d5a37f771d09",
	Build: family.Theorem(Statement{
		Binders: "∀d:(num → num → A → A). ∀n k:num. ∀y:(num → A). ∀x:A.",
		Hypotheses: []string{
			"k ≤ n + 1",
		},
		Conclusion: "faces_filler(d, n, horn_faces(n, k), y, x) ⇔ " +
			"faces_filler(opposite_face(d), n, horn_faces(n, n + 1 - k), λi:num. y(n + 1 - i), x)",
	},
		func(
			a *Argument,
			d *Expr[Fun3[Nat, Nat, A, A]],
			n, k *Expr[Nat],
			y *Arrow[Nat, A],
			x *Expr[A],
			bound Fact,
		) {
			reversedFace := a.TermAs[Nat]("n + 1 - k")
			a.Iff()
			a.Forward(
				"a filler in X fills the reversed horn in the opposite",
				func(b *Argument, original Fact) {
					faces := b.Simplified(original, Fwd(simplicial_set.FacesFillerDef))
					b.Do(Simp(Fwd(simplicial_set.FacesFillerDef), Fwd(simplicial_set.OppositeFaceDef)))
					i := b.FixAs[Nat]("i")
					index := b.Have(
						"a face i of the horn missing n + 1 − k is at most n + 1 and not n + 1 − k",
						"i ≤ n + 1 ∧ ¬(i = n + 1 - k)",
						By(b.Assume(), HornFacesMember.At(n, reversedFace, i)))
					bounds := b.Have(
						"so the reversed index n + 1 − i is at most n + 1 and not k",
						"n + 1 - i ≤ n + 1 ∧ ¬(n + 1 - i = k)",
						ByArith(bound, index))
					b.Show(
						"so the face i of x in the opposite, its face n + 1 − i in X, is y(n + 1 − i)",
						By(
							faces.At(b.TermAs[Nat]("n + 1 - i")),
							bounds,
							HornFacesMember.At(n, k, b.TermAs[Nat]("n + 1 - i"))))
				})
			a.Backward(
				"a filler of the reversed horn in the opposite fills the horn in X",
				func(b *Argument, reversed Fact) {
					faces := b.Simplified(
						reversed,
						Fwd(simplicial_set.FacesFillerDef),
						Fwd(simplicial_set.OppositeFaceDef))
					b.Do(Simp(Fwd(simplicial_set.FacesFillerDef)))
					i := b.FixAs[Nat]("i")
					index := b.Have(
						"a face i of the horn missing k is at most n + 1 and not k",
						"i ≤ n + 1 ∧ ¬(i = k)",
						By(b.Assume(), HornFacesMember.At(n, k, i)))
					bounds := b.Have(
						"so the reversed index n + 1 − i is at most n + 1 and not n + 1 − k",
						"n + 1 - i ≤ n + 1 ∧ ¬(n + 1 - i = n + 1 - k)",
						ByArith(bound, index))
					involution := b.Have(
						"and reversing it again returns i",
						"n + 1 - (n + 1 - i) = i",
						ByArith(index))
					b.Show(
						"so the face i of x in X, its face n + 1 − (n + 1 − i) in the opposite, is y(i)",
						By(
							Normalized,
							faces.At(b.TermAs[Nat]("n + 1 - i")),
							bounds,
							involution,
							HornFacesMember.At(n, reversedFace, b.TermAs[Nat]("n + 1 - i"))))
				})
		}),
})}

// OppositeKan — a Kan complex read in the opposite order is a Kan
// complex: the opposite is a simplicial set, and a horn of the opposite
// missing the face k, a face family on horn_faces(n, k), is, its members
// reindexed by i ↦ n + 1 − i, a horn of X missing the face n + 1 − k,
// whose filler in X fills the original horn in the opposite.
var OppositeKan = oppositeKanThm{family.Add(registry.ProofEntry{
	Name: "OppositeKan",
	Key:  "prop_f3cb14ef120dc493",
	Build: KanComplex.Law("kan_complex(opposite_simplicial_set(X))",
		func(a *Argument, kan Fact) {
			a.Show(
				"the opposite is a simplicial set in which every horn has a filler",
				Simp(Fwd(KanComplex)),
				SplitConj(
					Case(
						"the opposite is a simplicial set",
						By(simplicial_set.OppositeSimplicialSet.Read(KanSimplicialSet.Read(kan)))),
					Case(
						"a horn of the opposite is filled by reversing it, filling it in X, and reading the filler back",
						Derive(func(b *Argument) {
							n, k := b.FixAs[Nat]("n"), b.FixAs[Nat]("k")
							y := b.FixAs[Fun[Nat, A]]("y")
							horn := b.Conjuncts(
								b.Assume(),
								"the missing face k is at most n + 1",
								"y is a face family of the opposite on the faces of the horn missing k")
							bound, opposite := horn[0], horn[1]
							X, d := b.TermAs[simplicial_set.SimplicialOps[A]]("X"), b.TermAs[Fun3[Nat, Nat, A, A]]("X.d")
							reversedFace := b.TermAs[Nat]("n + 1 - k")
							reversed := b.TermAs[Fun[Nat, A]]("λi:num. y(n + 1 - i)")
							reversedBound := b.Have(
								"the reversed missing face n + 1 − k is at most n + 1",
								"n + 1 - k ≤ n + 1",
								ByArith())
							reversedHorn := b.Have(
								"reversed, y is a face family of X on the faces of the horn missing n + 1 − k",
								"face_family(X, n, horn_faces(n, n + 1 - k), λi:num. y(n + 1 - i))",
								By(At(HornFamilyOpposite, X, n, k, y), bound, opposite))
							x, filled := b.ObtainAs[A](
								"so the reversed horn has a filler x in X",
								"∃x:A. x ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, n + 1 - k), λi:num. y(n + 1 - i), x)",
								By(KanFill.Read(kan).At(n, reversedFace, reversed), reversedBound, reversedHorn))
							filler := b.Conjuncts(
								filled,
								"x is an (n+1)-simplex of X",
								"filling the reversed horn")
							fills := b.Have(
								"read back through the reversal, x fills the horn of the opposite",
								"faces_filler(opposite_face(X.d), n, horn_faces(n, k), y, x)",
								By(HornFillerOpposite.At(d, n, k, y, x), bound, filler[1]))
							b.Take(x)
							b.Show(
								"so x is a filler of the horn in the opposite",
								By(filler[0], fills))
						})),
				))
		}),
})}
