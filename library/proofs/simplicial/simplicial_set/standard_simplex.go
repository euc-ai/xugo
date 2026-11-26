// standard_simplex.go — the standard simplices: the m-simplices of Δⁿ
// are the monotone maps [m] → [n], encoded as sequences `num → num`
// that are monotone on 0 .. m, bounded by n there, and zero past m —
// the zero padding of the vector chapters. The face and degeneracy
// maps precompose with the coface and codegeneracy of the simplex
// category and are the same two constants at every n; they re-pad
// nothing, since the coface and the codegeneracy send an index past
// the range to an index past the range. The simplicial identities of
// the two constants hold of every sequence, with no membership: they
// are the identities of the cofaces and codegeneracies, each one case
// analysis on an index closed by arithmetic. The boundary and the horns
// are the sub-simplicial sets of the maps that miss a vertex, and the
// maps that miss a vertex other than k.

package simplicial_set

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// StandardSimplexSimplicesDef — `standard_simplex(n, m)`: the m-simplices of Δⁿ,
// the sequences monotone on 0 .. m, at most n there, and zero past m.
var StandardSimplexSimplicesDef = standardSimplexSimplicesDefThm{family.Define(registry.DefEntry{
	Name:  "StandardSimplexSimplicesDef",
	Key:   "prop_ecc7a994e5577612",
	Const: "standard_simplex_simplices",
	Type:  "num → num → set(num → num)",
	Equations: []string{
		"∀n m:num. " +
			"    standard_simplex_simplices(n, m) = " +
			"    {f:(num → num) | " +
			"        (∀a b:num. a ≤ b ∧ b ≤ m ⇒ f(a) ≤ f(b)) ∧ " +
			"        (∀a:num. a ≤ m ⇒ f(a) ≤ n) ∧ " +
			"        (∀a:num. m < a ⇒ f(a) = 0)}",
	},
	Reading: "A vertex of Δⁿ is a sequence constant at some v ≤ n on 0 .. 0 and zero after, so " +
		"Δⁿ(0) has n + 1 points; the padding makes two maps equal exactly when they agree on 0 .. m.",
})}

// InStandardSimplex — the definition read at a point: unfolded, Δⁿ in
// dimension m is a set builder, which admits f exactly by its three clauses.
var InStandardSimplex = inStandardSimplexThm{family.Add(registry.ProofEntry{
	Name: "InStandardSimplex",
	Key:  "prop_1090f9d3eef42719",
	Build: family.Theorem(
		"∀n m:num. ∀f:(num → num). "+
			"    f ∈ standard_simplex_simplices(n, m) ⇔ "+
			"    (∀a b:num. a ≤ b ∧ b ≤ m ⇒ f(a) ≤ f(b)) ∧ "+
			"    (∀a:num. a ≤ m ⇒ f(a) ≤ n) ∧ "+
			"    (∀a:num. m < a ⇒ f(a) = 0)",
		Chain(Unfold(StandardSimplexSimplicesDef), BySets())),
})}

// SimplexFaceDef — `simplex_face(i, f)`: f precomposed with the i-th
// coface, which skips i: the sequence reads f below i and f one step
// ahead from i on.
var SimplexFaceDef = simplexFaceDefThm{family.Define(registry.DefEntry{
	Name:  "SimplexFaceDef",
	Key:   "prop_816019ada17f27f3",
	Const: "simplex_face",
	Type:  "num → (num → num) → num → num",
	Equations: []string{
		"∀i:num. ∀f:(num → num). ∀k:num. simplex_face(i, f, k) = COND(k < i, f(k), f(k + 1))",
	},
})}

// SimplexDegeneracyDef — `simplex_degeneracy(i, f)`: f precomposed with
// the i-th codegeneracy, which repeats i: the sequence reads f up to i
// and f one step behind after i.
var SimplexDegeneracyDef = simplexDegeneracyDefThm{family.Define(registry.DefEntry{
	Name:  "SimplexDegeneracyDef",
	Key:   "prop_3e329c4a43be71ac",
	Const: "simplex_degeneracy",
	Type:  "num → (num → num) → num → num",
	Equations: []string{
		"∀i:num. ∀f:(num → num). ∀k:num. simplex_degeneracy(i, f, k) = COND(k ≤ i, f(k), f(k - 1))",
	},
})}

// SimplexFaceIn — a face of an (m+1)-simplex of Δⁿ is an m-simplex. The
// face reads f through the coface, at k below i and at k + 1 from i on:
// an order-preserving map that keeps 0 .. m inside 0 .. m + 1, so the face
// is monotone and at most n there; and an index past m is at least i, so
// there the face reads f past m + 1, where f is zero.
var SimplexFaceIn = simplexFaceInThm{family.Add(registry.ProofEntry{
	Name: "SimplexFaceIn",
	Key:  "prop_44f908de59c5b71b",
	Build: family.Theorem(Statement{
		Binders: "∀n m i:num. ∀f:(num → num).",
		Hypotheses: []string{
			"f ∈ standard_simplex_simplices(n, m + 1)",
			"i ≤ m + 1",
		},
		Conclusion: "simplex_face(i, f) ∈ standard_simplex_simplices(n, m)",
	},
		func(a *Argument, n, m, i *Expr[Nat], f *Arrow[Nat, Nat], given Fact) {
			parts := a.Conjuncts(
				given,
				"f is an (m + 1)-simplex of Δⁿ",
				"and i indexes one of its m + 2 faces")
			fIn, iUpTo := parts[0], parts[1]
			clauses := a.Conjuncts(
				a.Have(
					"f is monotone on 0 .. m + 1, at most n there, and zero past m + 1",
					"(∀j k:num. j ≤ k ∧ k ≤ m + 1 ⇒ f(j) ≤ f(k)) ∧ "+
						"(∀k:num. k ≤ m + 1 ⇒ f(k) ≤ n) ∧ "+
						"(∀k:num. m + 1 < k ⇒ f(k) = 0)",
					By(fIn, InStandardSimplex.At(n, a.TermAs[Nat]("m + 1"), f))),
				"f is monotone on 0 .. m + 1",
				"f is at most n there",
				"f is zero past m + 1")
			monotone, bounded, padded := clauses[0], clauses[1], clauses[2]

			faceMonotone := a.Have(
				"the face is monotone on 0 .. m",
				"∀j k:num. j ≤ k ∧ k ≤ m ⇒ simplex_face(i, f, j) ≤ simplex_face(i, f, k)",
				Unfold(SimplexFaceDef),
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]()
					k := b.FixAs[Nat]()
					ordered := b.Assume()
					b.Cases(b.Term("j < i"))
					b.When(
						"j below i, where the face reads f(j)",
						func(c *Argument, jBelow Fact) {
							c.Cases(c.Term("k < i"))
							c.When(
								"k below i as well, where it reads f(k): f(j) ≤ f(k)",
								func(d *Argument, kBelow Fact) {
									d.Show(
										"f is monotone at j ≤ k, inside 0 .. m + 1",
										ByArith(jBelow, kBelow, ordered, monotone.At(j, k)))
								})
							c.Otherwise(
								"k from i on, where it reads f(k + 1): f(j) ≤ f(k + 1)",
								func(d *Argument, kFrom Fact) {
									d.Show(
										"f is monotone at j ≤ k + 1, inside 0 .. m + 1",
										ByArith(jBelow, kFrom, ordered, monotone.At(j, d.TermAs[Nat]("k + 1"))))
								})
						})
					b.Otherwise(
						"j from i on, and so k: the face reads f one step ahead at both, f(j + 1) ≤ f(k + 1)",
						func(c *Argument, jFrom Fact) {
							c.Show(
								"f is monotone at j + 1 ≤ k + 1, inside 0 .. m + 1",
								ByArith(jFrom, ordered, monotone.At(c.TermAs[Nat]("j + 1"), c.TermAs[Nat]("k + 1"))))
						})
				}))
			faceBounded := a.Have(
				"bounded by n there",
				"∀k:num. k ≤ m ⇒ simplex_face(i, f, k) ≤ n",
				Unfold(SimplexFaceDef),
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					inRange := b.Assume()
					b.Show(
						"the face reads f at k or at k + 1, both within 0 .. m + 1",
						ByArith(inRange, bounded.At(k), bounded.At(b.TermAs[Nat]("k + 1"))))
				}))
			facePadded := a.Have(
				"zero past m",
				"∀k:num. m < k ⇒ simplex_face(i, f, k) = 0",
				Unfold(SimplexFaceDef),
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					pastM := b.Assume()
					b.Show(
						"i ≤ m + 1 ≤ k puts k from i on, where the face reads f(k + 1), past m + 1",
						ByArith(pastM, iUpTo, padded.At(b.TermAs[Nat]("k + 1"))))
				}))
			a.Show(
				"these are the three clauses of an m-simplex of Δⁿ",
				By(
					faceMonotone,
					faceBounded,
					facePadded,
					InStandardSimplex.At(n, m, a.TermAs[Fun[Nat, Nat]]("simplex_face(i, f)"))))
		}),
})}

// SimplexDegeneracyIn — a degeneracy of an m-simplex of Δⁿ is an
// (m+1)-simplex. The degeneracy reads f through the codegeneracy, at k up
// to i and at k − 1 past i: an order-preserving map that sends 0 .. m + 1
// into 0 .. m, the index m + 1 included since i ≤ m puts it past i, so the
// degeneracy is monotone and at most n there; and an index past m + 1 is
// past i, so there the degeneracy reads f one step behind, past m, where f
// is zero.
var SimplexDegeneracyIn = simplexDegeneracyInThm{family.Add(registry.ProofEntry{
	Name: "SimplexDegeneracyIn",
	Key:  "prop_2403d03623ff9fa6",
	Build: family.Theorem(Statement{
		Binders: "∀n m i:num. ∀f:(num → num).",
		Hypotheses: []string{
			"f ∈ standard_simplex_simplices(n, m)",
			"i ≤ m",
		},
		Conclusion: "simplex_degeneracy(i, f) ∈ standard_simplex_simplices(n, m + 1)",
	},
		func(a *Argument, n, m, i *Expr[Nat], f *Arrow[Nat, Nat], given Fact) {
			parts := a.Conjuncts(
				given,
				"f is an m-simplex of Δⁿ",
				"and i indexes one of its m + 1 degeneracies")
			fIn, iUpTo := parts[0], parts[1]
			clauses := a.Conjuncts(
				a.Have(
					"f is monotone on 0 .. m, at most n there, and zero past m",
					"(∀j k:num. j ≤ k ∧ k ≤ m ⇒ f(j) ≤ f(k)) ∧ (∀k:num. k ≤ m ⇒ f(k) ≤ n) ∧ (∀k:num. m < k ⇒ f(k) = 0)",
					By(fIn, InStandardSimplex.At(n, m, f))),
				"f is monotone on 0 .. m",
				"f is at most n there",
				"f is zero past m")
			monotone, bounded, padded := clauses[0], clauses[1], clauses[2]

			degeneracyMonotone := a.Have(
				"the degeneracy is monotone on 0 .. m + 1",
				"∀j k:num. j ≤ k ∧ k ≤ m + 1 ⇒ simplex_degeneracy(i, f, j) ≤ simplex_degeneracy(i, f, k)",
				Unfold(SimplexDegeneracyDef),
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]()
					k := b.FixAs[Nat]()
					ordered := b.Assume()
					b.Cases(b.Term("j ≤ i"))
					b.When(
						"j up to i, where the degeneracy reads f(j)",
						func(c *Argument, jUpTo Fact) {
							c.Cases(c.Term("k ≤ i"))
							c.When(
								"k up to i as well, where it reads f(k): f(j) ≤ f(k)",
								func(d *Argument, kUpTo Fact) {
									d.Show(
										"f is monotone at j ≤ k, inside 0 .. m since k ≤ i ≤ m",
										ByArith(jUpTo, kUpTo, ordered, iUpTo, monotone.At(j, k)))
								})
							c.Otherwise(
								"k past i, where it reads f(k − 1): f(j) ≤ f(k − 1)",
								func(d *Argument, kPast Fact) {
									d.Show(
										"f is monotone at j ≤ k − 1, inside 0 .. m since k ≤ m + 1",
										ByArith(jUpTo, kPast, ordered, monotone.At(j, d.TermAs[Nat]("k - 1"))))
								})
						})
					b.Otherwise(
						"j past i, and so k: the degeneracy reads f one step behind at both, f(j − 1) ≤ f(k − 1)",
						func(c *Argument, jPast Fact) {
							c.Show(
								"f is monotone at j − 1 ≤ k − 1, inside 0 .. m",
								ByArith(jPast, ordered, monotone.At(c.TermAs[Nat]("j - 1"), c.TermAs[Nat]("k - 1"))))
						})
				}))
			degeneracyBounded := a.Have(
				"bounded by n there",
				"∀k:num. k ≤ m + 1 ⇒ simplex_degeneracy(i, f, k) ≤ n",
				Unfold(SimplexDegeneracyDef),
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					inRange := b.Assume()
					b.Show(
						"the degeneracy reads f at k up to i ≤ m, or at k − 1 ≤ m",
						ByArith(inRange, iUpTo, bounded.At(k), bounded.At(b.TermAs[Nat]("k - 1"))))
				}))
			degeneracyPadded := a.Have(
				"zero past m + 1",
				"∀k:num. m + 1 < k ⇒ simplex_degeneracy(i, f, k) = 0",
				Unfold(SimplexDegeneracyDef),
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					pastM := b.Assume()
					b.Show(
						"i ≤ m < k puts k past i, where the degeneracy reads f(k − 1), past m",
						ByArith(pastM, iUpTo, padded.At(b.TermAs[Nat]("k - 1"))))
				}))
			a.Show(
				"these are the three clauses of an (m + 1)-simplex of Δⁿ",
				By(
					degeneracyMonotone,
					degeneracyBounded,
					degeneracyPadded,
					InStandardSimplex.At(
						n, a.TermAs[Nat]("m + 1"), a.TermAs[Fun[Nat, Nat]]("simplex_degeneracy(i, f)"))))
		}),
})}

// SimplexFaceFace — d_i d_j = d_{j−1} d_i for i < j, for every
// sequence. Read at an index k, each side steps one index ahead from i
// on and one more from j − 1 on, so the two read f at the same index on
// each of the three ranges.
var SimplexFaceFace = simplexFaceFaceThm{family.Add(registry.ProofEntry{
	Name: "SimplexFaceFace",
	Key:  "prop_265470a5f873804e",
	Build: family.Theorem(Statement{
		Binders: "∀i j:num. ∀f:(num → num).",
		Hypotheses: []string{
			"i < j",
		},
		Conclusion: "simplex_face(i, simplex_face(j, f)) = simplex_face(j - 1, simplex_face(i, f))",
	},
		func(a *Argument, i, j *Expr[Nat], f *Arrow[Nat, Nat], iBelowJ Fact) {
			a.Show(
				"index by index, read through the two faces on each side",
				Funext(),
				Unfold(SimplexFaceDef),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					b.Cases(b.Term("k < i"))
					b.When(
						"below i both sides read f(k)",
						func(c *Argument, belowI Fact) {
							c.Show(
								"k < i < j puts k below j and below j − 1",
								ByArith(belowI, iBelowJ))
						})
					b.Otherwise(
						"from i on the left side reads simplex_face(j, f) at k + 1",
						func(c *Argument, fromI Fact) {
							c.Cases(c.Term("k + 1 < j"))
							c.When(
								"between i and j − 1 both read f(k + 1)",
								func(d *Argument, beforeJ Fact) {
									d.Show(
										"k + 1 < j puts k below j − 1, where the right side reads simplex_face(i, f) at k",
										ByArith(fromI, beforeJ))
								})
							c.Otherwise(
								"from j − 1 on both read f(k + 2)",
								func(d *Argument, fromJ Fact) {
									d.Show(
										"j ≤ k + 1 puts k at j − 1 or past, where the right side reads simplex_face(i, f) at k + 1",
										ByArith(fromI, fromJ))
								})
						})
				}))
		}),
})}

// SimplexDegeneracyDegeneracy — s_i s_j = s_{j+1} s_i for i ≤ j, for
// every sequence. Read at an index k, each side reads f at k up to i, one
// step behind from i to j + 1, and two steps behind past j + 1.
var SimplexDegeneracyDegeneracy = simplexDegeneracyDegeneracyThm{family.Add(registry.ProofEntry{
	Name: "SimplexDegeneracyDegeneracy",
	Key:  "prop_3eecb177296fc991",
	Build: family.Theorem(Statement{
		Binders: "∀i j:num. ∀f:(num → num).",
		Hypotheses: []string{
			"i ≤ j",
		},
		Conclusion: "simplex_degeneracy(i, simplex_degeneracy(j, f)) = " +
			"simplex_degeneracy(j + 1, simplex_degeneracy(i, f))",
	},
		func(a *Argument, i, j *Expr[Nat], f *Arrow[Nat, Nat], iUpToJ Fact) {
			a.Show(
				"index by index, read through the two degeneracies on each side",
				Funext(),
				Unfold(SimplexDegeneracyDef),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					b.Cases(b.Term("k ≤ i"))
					b.When(
						"up to i both sides read f(k)",
						func(c *Argument, upToI Fact) {
							c.Show(
								"k ≤ i ≤ j puts k at most j, and at most j + 1",
								ByArith(upToI, iUpToJ))
						})
					b.Otherwise(
						"past i the left side reads simplex_degeneracy(j, f) at k − 1",
						func(c *Argument, pastI Fact) {
							c.Cases(c.Term("k ≤ j + 1"))
							c.When(
								"from i to j + 1 both read f(k − 1)",
								func(d *Argument, upToJ1 Fact) {
									d.Show(
										"k − 1 ≤ j on the left; on the right simplex_degeneracy(i, f) is read at k, past i",
										ByArith(pastI, upToJ1))
								})
							c.Otherwise(
								"past j + 1 both read f(k − 2)",
								func(d *Argument, pastJ1 Fact) {
									d.Show(
										"k − 1 is past j and so past i: each inner degeneracy is read at k − 1, one step behind again",
										ByArith(pastJ1, iUpToJ))
								})
						})
				}))
		}),
})}

// SimplexFaceDegeneracyBelow — d_i s_j = s_{j−1} d_i for i < j, for
// every sequence. Read at an index k, each side reads f at k below i, one
// step ahead from i to j − 1, and at k again from j on, where the step
// ahead and the step behind cancel.
var SimplexFaceDegeneracyBelow = simplexFaceDegeneracyBelowThm{family.Add(registry.ProofEntry{
	Name: "SimplexFaceDegeneracyBelow",
	Key:  "prop_5ea29cb6bf18d344",
	Build: family.Theorem(Statement{
		Binders: "∀i j:num. ∀f:(num → num).",
		Hypotheses: []string{
			"i < j",
		},
		Conclusion: "simplex_face(i, simplex_degeneracy(j, f)) = " +
			"simplex_degeneracy(j - 1, simplex_face(i, f))",
	},
		func(a *Argument, i, j *Expr[Nat], f *Arrow[Nat, Nat], iBelowJ Fact) {
			a.Show(
				"index by index, read through the face and the degeneracy on each side",
				Funext(),
				Unfold(SimplexFaceDef),
				Unfold(SimplexDegeneracyDef),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					b.Cases(b.Term("k < i"))
					b.When(
						"below i both sides read f(k)",
						func(c *Argument, belowI Fact) {
							c.Show(
								"k < i < j puts k at most j, and at most j − 1",
								ByArith(belowI, iBelowJ))
						})
					b.Otherwise(
						"from i on the left side reads simplex_degeneracy(j, f) at k + 1",
						func(c *Argument, fromI Fact) {
							c.Cases(c.Term("k < j"))
							c.When(
								"from i to j − 1 both read f(k + 1)",
								func(d *Argument, belowJ Fact) {
									d.Show(
										"k + 1 ≤ j on the left; on the right k ≤ j − 1, where simplex_face(i, f) is read at k, from i on",
										ByArith(fromI, belowJ))
								})
							c.Otherwise(
								"from j on both read f(k)",
								func(d *Argument, fromJ Fact) {
									back := d.Have(
										"k ≥ j > i puts k at 1 or past, so one step behind and one ahead is k",
										"k - 1 + 1 = k",
										ByArith(fromJ, iBelowJ))
									d.Show(
										"k + 1 is past j on the left, read one step behind; on the right "+
											"k is past j − 1 and k − 1 is not below i, read one step ahead",
										ByArith(fromJ, iBelowJ, back))
								})
						})
				}))
		}),
})}

// SimplexFaceDegeneracyEqual — d_i s_i is the identity on sequences:
// read at an index k, the face looks at the degeneracy at k below i and
// one step ahead from i on, where the degeneracy looks one step back.
var SimplexFaceDegeneracyEqual = simplexFaceDegeneracyEqualThm{family.Add(registry.ProofEntry{
	Name: "SimplexFaceDegeneracyEqual",
	Key:  "prop_bca39cf24517fb9c",
	Build: family.Theorem("∀i:num. ∀f:(num → num). simplex_face(i, simplex_degeneracy(i, f)) = f",
		func(a *Argument, i *Expr[Nat], f *Arrow[Nat, Nat]) {
			a.Show(
				"index by index, read through the face and the degeneracy",
				Funext(),
				Unfold(SimplexFaceDef),
				Unfold(SimplexDegeneracyDef),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					b.Cases(b.Term("k < i"))
					b.When(
						"below i the face and the degeneracy both read f(k)",
						func(c *Argument, below Fact) {
							c.Show(
								"k < i, so k ≤ i as well",
								ByArith(below))
						})
					b.Otherwise(
						"from i on the degeneracy reads one step behind the face",
						func(c *Argument, fromI Fact) {
							c.Show(
								"k + 1 is past i, and one step behind k + 1 is k",
								ByArith(fromI))
						})
				}))
		}),
})}

// SimplexFaceDegeneracyNext — d_{i+1} s_i is the identity on sequences:
// read at an index k, the face looks at the degeneracy at k up to i and
// one step ahead past i, where the degeneracy looks one step back.
var SimplexFaceDegeneracyNext = simplexFaceDegeneracyNextThm{family.Add(registry.ProofEntry{
	Name: "SimplexFaceDegeneracyNext",
	Key:  "prop_ec324db278e5ff31",
	Build: family.Theorem("∀i:num. ∀f:(num → num). simplex_face(i + 1, simplex_degeneracy(i, f)) = f",
		func(a *Argument, i *Expr[Nat], f *Arrow[Nat, Nat]) {
			a.Show(
				"index by index, read through the face and the degeneracy",
				Funext(),
				Unfold(SimplexFaceDef),
				Unfold(SimplexDegeneracyDef),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					b.Cases(b.Term("k < i + 1"))
					b.When(
						"up to i the face and the degeneracy both read f(k)",
						func(c *Argument, upToI Fact) {
							c.Show(
								"k < i + 1, so k ≤ i",
								ByArith(upToI))
						})
					b.Otherwise(
						"past i the degeneracy reads one step behind the face",
						func(c *Argument, pastI Fact) {
							c.Show(
								"k + 1 is past i, and one step behind k + 1 is k",
								ByArith(pastI))
						})
				}))
		}),
})}

// SimplexFaceDegeneracyAbove — d_i s_j = s_j d_{i−1} for i > j + 1,
// for every sequence. Read at an index k, each side reads f at k up to j,
// one step behind from j + 1 to i − 1, and at k again from i on, where the
// step behind and the step ahead cancel.
var SimplexFaceDegeneracyAbove = simplexFaceDegeneracyAboveThm{family.Add(registry.ProofEntry{
	Name: "SimplexFaceDegeneracyAbove",
	Key:  "prop_e6e5e01ca147a5c1",
	Build: family.Theorem(Statement{
		Binders: "∀i j:num. ∀f:(num → num).",
		Hypotheses: []string{
			"j + 1 < i",
		},
		Conclusion: "simplex_face(i, simplex_degeneracy(j, f)) = " +
			"simplex_degeneracy(j, simplex_face(i - 1, f))",
	},
		func(a *Argument, i, j *Expr[Nat], f *Arrow[Nat, Nat], jBelowI Fact) {
			a.Show(
				"index by index, read through the face and the degeneracy on each side",
				Funext(),
				Unfold(SimplexFaceDef),
				Unfold(SimplexDegeneracyDef),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					b.Cases(b.Term("k ≤ j"))
					b.When(
						"up to j both sides read f(k)",
						func(c *Argument, upToJ Fact) {
							c.Show(
								"k ≤ j < i − 1 puts k below i, and below i − 1",
								ByArith(upToJ, jBelowI))
						})
					b.Otherwise(
						"past j the right side reads simplex_face(i − 1, f) at k − 1",
						func(c *Argument, pastJ Fact) {
							c.Cases(c.Term("k < i"))
							c.When(
								"from j + 1 to i − 1 both read f(k − 1)",
								func(d *Argument, belowI Fact) {
									d.Show(
										"on the left simplex_degeneracy(j, f) is read at k, past j; on the right k − 1 is below i − 1",
										ByArith(pastJ, belowI))
								})
							c.Otherwise(
								"from i on both read f(k)",
								func(d *Argument, fromI Fact) {
									back := d.Have(
										"k is past j, so at 1 or past: one step behind and one ahead is k",
										"k - 1 + 1 = k",
										ByArith(pastJ))
									d.Show(
										"on the left k + 1 is past j, read one step behind; on "+
											"the right k − 1 is not below i − 1, read one step ahead",
										ByArith(fromI, pastJ, back))
								})
						})
				}))
		}),
})}

// StandardSimplex — Δⁿ is a simplicial set, at every n. The maps are
// the face and the degeneracy at every dimension, so the two closures
// are their membership laws, and each identity is theirs over every
// sequence, the membership the axiom carries unused.
var StandardSimplex = standardSimplexThm{family.Add(registry.ProofEntry{
	Name: "StandardSimplex",
	Key:  "prop_6982c210366bbf85",
	Build: family.Instance(SimplicialSet, "∀n:num. simplicial_set(standard_simplex(n))",
		Case(
			"a face of an (m + 1)-simplex is an m-simplex",
			By(SimplexFaceIn)),
		Case(
			"a degeneracy of an m-simplex is an (m + 1)-simplex",
			By(SimplexDegeneracyIn)),
		Case(
			"d_i d_j = d_{j−1} d_i for i < j",
			By(SimplexFaceFace)),
		Case(
			"s_i s_j = s_{j+1} s_i for i ≤ j",
			By(SimplexDegeneracyDegeneracy)),
		Case(
			"d_i s_j = s_{j−1} d_i for i < j",
			By(SimplexFaceDegeneracyBelow)),
		Case(
			"d_i s_i is the identity",
			By(SimplexFaceDegeneracyEqual)),
		Case(
			"so is d_{i+1} s_i",
			By(SimplexFaceDegeneracyNext)),
		Case(
			"d_i s_j = s_j d_{i−1} for i > j + 1",
			By(SimplexFaceDegeneracyAbove)),
	),
})}

// SimplexHornSimplicesDef — `simplex_horn(n, k, m)`: the m-simplices of Δⁿ that
// miss a vertex of [n] other than k, the k-th horn Λⁿₖ.
var SimplexHornSimplicesDef = simplexHornSimplicesDefThm{family.Define(registry.DefEntry{
	Name:  "SimplexHornSimplicesDef",
	Key:   "prop_c25f1442ccddcdf3",
	Const: "simplex_horn_simplices",
	Type:  "num → num → num → set(num → num)",
	Equations: []string{
		"∀n k m:num. " +
			"    simplex_horn_simplices(n, k, m) = " +
			"    {f:(num → num) | " +
			"        f ∈ standard_simplex_simplices(n, m) ∧ " +
			"        ∃v:num. v ≤ n ∧ ¬(v = k) ∧ ∀a:num. a ≤ m ⇒ ¬(f(a) = v)}",
	},
	Reading: "Λ⁰₀ is empty; Λ¹ₖ, the maps missing the vertex 1 − k, " +
		"is the vertex k in every dimension; the horn is defined for every k.",
	Deps: []registry.EntryLike{StandardSimplexSimplicesDef},
})}

// SimplexHornSub — every horn is a sub-simplicial set of Δⁿ.
var SimplexHornSub = simplexHornSubThm{family.Add(registry.ProofEntry{
	Name: "SimplexHornSub",
	Key:  "prop_fe202e5e4bdc720f",
	Deps: []registry.EntryLike{
		SubSimplicialSetDef,
		SimplexHornSimplicesDef,
		SimplexFaceIn,
		SimplexDegeneracyIn,
		SimplexFaceDef,
		SimplexDegeneracyDef,
		set_basic.SubsetDef,
	},
	Build: family.Card(
		"∀n k:num. sub_simplicial_set(standard_simplex(n), simplex_horn_simplices(n, k))",
		"a face or a degeneracy of f reads f inside f's own range, "+
			"so a vertex other than k that f misses is missed by them too"),
})}
