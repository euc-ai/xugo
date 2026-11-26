// nerve.go — the nerve of a category. An n-simplex of the nerve is
// a chain of n composable morphisms, a sequence `num → M` whose n-th
// term is the identity at the end of the chain and which is constant
// from there on — the padding of the standard simplices with the
// identity for its zero. The 0-th face drops the first morphism, the
// n-th drops the last and re-pads with the identity at its source,
// an inner face composes two neighbours; a degeneracy inserts the
// identity at the source of a morphism. The simplicial identities of
// the nerve come from the laws of the category: the face identity from
// associativity, d_i s_i and d_{i+1} s_i from the two unit laws, and the
// rest from the ends of identities and composites. A functor induces a
// simplicial map.
//
// A simplicial set has unique inner fillers when every inner horn has
// exactly one filler; the nerve of a category has them. Segal's
// characterization — unique inner fillers exactly when the set is
// isomorphic to the nerve of a category — is the segal family's.

package nerve

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The nerve of a category
// ---------------------------------------------------------------------------

// NerveSimplicesDef — `category_nerve(…, C.objects, C.morphisms, n)`: the chains of n
// composable morphisms, a sequence whose terms up to n are morphisms,
// each composable with the next, whose n-th term is the identity at an
// object, and which is constant from n on; at n = 0 the constant
// identity chains, one per object. Under the category the text writes
// `category_nerve(C, n)`, and `category_nerve(C)` is the
// family.
var NerveSimplicesDef = nerveSimplicesDefThm{family.Define(registry.DefEntry{
	Name:  "NerveSimplicesDef",
	Key:   "prop_36579a257ed64776",
	Const: "nerve_simplices",
	Type:  "category_ops(A, M) → num → set(num → M)",
	Equations: []string{
		"∀C:category_ops(A, M). ∀n:num. " +
			"    nerve_simplices(C, n) = " +
			"    {f:(num → M) | " +
			"        (∀i:num. i ≤ n ⇒ f(i) ∈ C.morphisms) ∧ " +
			"        (∀i:num. i < n ⇒ C.target(f(i)) = C.source(f(i + 1))) ∧ " +
			"        (∃x:A. x ∈ C.objects ∧ f(n) = C.identity(x)) ∧ " +
			"        (∀i:num. n < i ⇒ f(i) = f(n))}",
	},
	Reading: "The n-th term is the identity at the end of the chain, composable with the " +
		"(n−1)-th by the second clause, so the end object is read off the chain itself; at n = 0 " +
		"the chain is the constant identity at an object, which the identity axiom makes a morphism.",
})}

// NerveFaceDef — `nerve_face(C, …, n, i, f)`: the i-th face of the chain
// f of length n: for i = 0 the chain without its first morphism, for
// i = n the chain without its last, padded with the identity at the
// last source, and for 0 < i < n the chain with the (i−1)-th and i-th
// morphisms composed.
var NerveFaceDef = nerveFaceDefThm{family.Define(registry.DefEntry{
	Name:  "NerveFaceDef",
	Key:   "prop_6f0ee566a4ef2701",
	Const: "nerve_face",
	Type:  "category_ops(A, M) → num → num → (num → M) → num → M",
	Equations: []string{
		"∀C:category_ops(A, M). ∀n i:num. ∀f:(num → M). ∀j:num. " +
			"    nerve_face(C, n, i, f, j) = " +
			"    COND(i = 0, " +
			"        f(j + 1), " +
			"        COND(i = n, " +
			"            COND(j + 1 < n, f(j), C.identity(C.source(f(n - 1)))), " +
			"            COND(j + 1 < i, f(j), COND(j + 1 = i, C.compose(f(i), f(i - 1)), f(j + 1)))))",
	},
	Reading: "The dimension n is read: the last face re-pads from index " +
		"n − 1 with the identity at the source of the dropped morphism. The " +
		"face at i = n = 0 is the first branch, a value no axiom reads.",
})}

// NerveDegeneracyDef — `nerve_degeneracy(C, …, i, f)`: the chain with the
// identity at the source of its i-th morphism inserted before it; the
// dimension is not read, and at i = n the chain is unchanged as a
// sequence.
var NerveDegeneracyDef = nerveDegeneracyDefThm{family.Define(registry.DefEntry{
	Name:  "NerveDegeneracyDef",
	Key:   "prop_3340829d60db00db",
	Const: "nerve_degeneracy",
	Type:  "category_ops(A, M) → num → (num → M) → num → M",
	Equations: []string{
		"∀C:category_ops(A, M). ∀i:num. ∀f:(num → M). ∀j:num. " +
			"    nerve_degeneracy(C, i, f, j) = " +
			"    COND(j < i, f(j), COND(j = i, C.identity(C.source(f(i))), f(j - 1)))",
	},
})}

// NerveFaceIn — a face of a chain of length n + 1 is a chain of length
// n, by cases on the face. The 0-th face is f one index up. The last
// keeps f below n and pads with the identity at the source of f(n),
// which f(n − 1) composes with, its target being that source. An inner
// face at i = p + 1 composes f(p) and f(p + 1) into a morphism from the
// source of f(p) to the target of f(p + 1), which composes with f(p − 1)
// before it and with f(p + 2) after it. In each case the face is read
// index by index against the four clauses of a chain.
var NerveFaceIn = nerveFaceInThm{family.Add(registry.ProofEntry{
	Name: "NerveFaceIn",
	Key:  "prop_45a9624379451769",
	Build: category.Category.Law(Statement{
		Binders: "∀n i:num. ∀f:(num → M).",
		Hypotheses: []string{
			"f ∈ nerve_simplices(C, n + 1)",
			"i ≤ n + 1",
		},
		Conclusion: "nerve_face(C, n + 1, i, f) ∈ nerve_simplices(C, n)",
		Abbrev: Abbrev{
			{Name: "morphisms", Text: "∀k:num. k ≤ n ⇒ nerve_face(C, n + 1, i, f, k) ∈ C.morphisms"},
			{Name: "composing", Text: "∀k:num. " +
				"    k < n ⇒ " +
				"    C.target(nerve_face(C, n + 1, i, f, k)) = C.source(nerve_face(C, n + 1, i, f, k + 1))"},
			{Name: "ending", Text: "∃x:A. x ∈ C.objects ∧ nerve_face(C, n + 1, i, f, n) = C.identity(x)"},
			{Name: "padded", Text: "∀k:num. " +
				"    n < k ⇒ nerve_face(C, n + 1, i, f, k) = nerve_face(C, n + 1, i, f, n)"},
		},
	},
		func(a *Argument, cat Fact, n, i *Expr[Nat], f Term, given Fact) {
			parts := a.Conjuncts(
				given,
				"f is a chain of n + 1 morphisms",
				"and i indexes one of its faces")
			chain, iUpTo := parts[0], parts[1]
			clauses := a.Conjuncts(
				a.Have(
					"f read by the definition of the nerve",
					"(∀k:num. k ≤ n + 1 ⇒ f(k) ∈ C.morphisms) ∧ "+
						"(∀k:num. k < n + 1 ⇒ C.target(f(k)) = C.source(f(k + 1))) ∧ "+
						"(∃x:A. x ∈ C.objects ∧ f(n + 1) = C.identity(x)) ∧ "+
						"(∀k:num. n + 1 < k ⇒ f(k) = f(n + 1))",
					BySets(a.Simplified(chain, Fwd(NerveSimplicesDef)))),
				"its terms up to n + 1 are morphisms",
				"each composes with the next",
				"its (n + 1)-th term is the identity at an object",
				"and it is constant from n + 1 on")
			mor, next, end, stays := clauses[0], clauses[1], clauses[2], clauses[3]

			a.Cases(a.Term("i = 0"))
			a.When(
				"the 0-th face drops the first morphism: it is f one index up",
				func(b *Argument, _ Fact) {
					terms := b.Have(
						"its terms up to n are f(1), …, f(n + 1), morphisms",
						"«morphisms»",
						Simp(Fwd(NerveFaceDef)),
						ByArith(mor))
					composable := b.Have(
						"each composes with the next, as in f one index up",
						"«composing»",
						Simp(Fwd(NerveFaceDef)),
						ByArith(next))
					last := b.Have(
						"its n-th term is f(n + 1), the identity at an object",
						"«ending»",
						Simp(Fwd(NerveFaceDef)),
						By(end))
					constant := b.Have(
						"it is constant from n on, as f is from n + 1",
						"«padded»",
						Simp(Fwd(NerveFaceDef)),
						ByArith(stays))
					b.Show(
						"so it is a chain of n morphisms",
						Simp(Fwd(NerveSimplicesDef)),
						BySets(terms, composable, last, constant))
				})
			a.Otherwise(
				"a face past the 0-th drops the last morphism or composes two",
				func(b *Argument, notFirst Fact) {
					b.Cases(b.Term("i = n + 1"))
					b.When(
						"the last face keeps f below n and pads with the identity at the source of f(n)",
						func(c *Argument, _ Fact) {
							// The face read by its definition, n + 1 − 1 being n.
							read := Simp(Fwd(NerveFaceDef), Fwd(nat_monus.AddSubCancel))
							source := c.Have(
								"f(n) is a morphism, so its source is an object",
								"C.source(f(n)) ∈ C.objects",
								ByArith(mor.At(n), At(category.MorphismEnds.Read(cat), c.Term("f(n)"))))
							pad := c.Have(
								"the identity at the source of f(n) is a morphism from it",
								"C.identity(C.source(f(n))) ∈ C.morphisms ∧ C.source(C.identity(C.source(f(n)))) = C.source(f(n))",
								By(source, At(category.IdentityMorphism.Read(cat), c.Term("C.source(f(n))"))))
							joins := c.Have(
								"f(n − 1) composes with that identity, its target the source "+
									"of f(n): said of k with k + 1 = n, as n = 0 has no n − 1",
								"∀k:num. k + 1 = n ⇒ C.target(f(k)) = C.source(C.identity(C.source(f(n))))",
								Derive(func(d *Argument) {
									k := d.FixAs[Nat]()
									before := d.Assume()
									step := d.Have(
										"f(k) composes with f(k + 1)",
										"C.target(f(k)) = C.source(f(k + 1))",
										ByArith(before, next.At(k)))
									d.Show(
										"and f(k + 1) is f(n)",
										By(before, step, pad))
								}))
							terms := c.Have(
								"its terms are f(k) below n and the padding identity at n, all morphisms",
								"«morphisms»",
								Derive(func(d *Argument) {
									k := d.FixAs[Nat]()
									d.Assume()
									d.Cases(d.Term("k < n"))
									d.When(
										"below n it is f(k)",
										func(e *Argument, below Fact) {
											e.Show(
												"f(k) is a morphism",
												read,
												ByArith(below, mor.At(k)))
										})
									d.Otherwise(
										"at n it is the padding identity",
										func(e *Argument, at Fact) {
											e.Show(
												"the padding identity is a morphism",
												read,
												ByArith(at, pad))
										})
								}))
							composable := c.Have(
								"each composes with the next, the last with the padding identity",
								"«composing»",
								Derive(func(d *Argument) {
									k := d.FixAs[Nat]()
									below := d.Assume()
									d.Cases(d.Term("k + 1 < n"))
									d.When(
										"below n − 1 both are terms of f",
										func(e *Argument, inner Fact) {
											e.Show(
												"f(k) composes with f(k + 1)",
												read,
												ByArith(inner, next.At(k)))
										})
									d.Otherwise(
										"at n − 1 the next term is the padding identity",
										func(e *Argument, boundary Fact) {
											e.Show(
												"which f(n − 1) composes with",
												read,
												ByArith(below, boundary, joins.At(k)))
										})
								}))
							last := c.Have(
								"its n-th term is the identity at the source of f(n), an object",
								"«ending»",
								Derive(func(d *Argument) {
									d.Take(d.Term("C.source(f(n))"))
									d.Show(
										"the face at n is the identity at C.source(f(n))",
										read,
										ByArith(source))
								}))
							constant := c.Have(
								"it is the padding identity from n on",
								"«padded»",
								read,
								ByArith())
							c.Show(
								"so it is a chain of n morphisms",
								Simp(Fwd(NerveSimplicesDef)),
								BySets(terms, composable, last, constant))
						})
					b.Otherwise(
						"an inner face composes the two morphisms either side of its vertex",
						func(c *Argument, notLast Fact) {
							p, iIs := c.ObtainAs[Nat](
								"i is p + 1 for some p",
								"∃p:num. i = p + 1",
								By(notFirst, nat_arith.NonzeroIsSucc.At(i)))
							// The face read by its definition: the case settles the
							// choice of the inner branch, and then i is p + 1.
							read := Chain(Simp(Fwd(NerveFaceDef)), iIs.Rw(), Simp(Fwd(nat_monus.AddSubCancel)))
							pNext := c.TermAs[Nat]("p + 1")
							inner := c.Have(
								"i is neither 0 nor n + 1, so p < n",
								"p < n",
								ByArith(iIs, iUpTo, notLast))
							composite := c.Conjuncts(
								c.Have(
									"f(p) and f(p + 1) compose, from the source of f(p) to the target of f(p + 1)",
									"C.compose(f(p + 1), f(p)) ∈ C.morphisms ∧ "+
										"C.source(C.compose(f(p + 1), f(p))) = C.source(f(p)) ∧ "+
										"C.target(C.compose(f(p + 1), f(p))) = C.target(f(p + 1))",
									ByArith(
										inner,
										mor.At(p),
										mor.At(pNext),
										next.At(p),
										At(category.CompositeMorphism.Read(cat), c.Term("f(p)"), c.Term("f(p + 1)")))),
								"the composite is a morphism",
								"from the source of f(p)",
								"to the target of f(p + 1)")
							compIn, compSrc, compTgt := composite[0], composite[1], composite[2]
							enters := c.Have(
								"f(p − 1) composes with the composite, its target the source "+
									"of f(p): said of k with k + 1 = p, as p = 0 has no p − 1",
								"∀k:num. k + 1 = p ⇒ C.target(f(k)) = C.source(C.compose(f(p + 1), f(p)))",
								Derive(func(d *Argument) {
									k := d.FixAs[Nat]()
									before := d.Assume()
									// Resident for the grounding below, which reads the
									// chain condition at k under this guard.
									kBelowSuccessor := d.Have(
										"k is below n + 1, being below p",
										"k < n + 1",
										ByArith(before, inner))
									step := d.Have(
										"f(k) composes with f(k + 1)",
										"C.target(f(k)) = C.source(f(k + 1))",
										GroupPremises(kBelowSuccessor, next.At(k)),
										Assumption())
									d.Show(
										"and f(k + 1) is f(p)",
										By(before, step, compSrc))
								}))
							leaves := c.Have(
								"and f(p + 2) composes with it, its source being the target of f(p + 1)",
								"C.target(C.compose(f(p + 1), f(p))) = C.source(f(p + 1 + 1))",
								ByArith(inner, compTgt, next.At(pNext)))
							terms := c.Have(
								"its terms are f below p, the composite at p and f one index up past p, all morphisms",
								"«morphisms»",
								Derive(func(d *Argument) {
									k := d.FixAs[Nat]()
									upTo := d.Assume()
									d.Cases(d.Term("k < p"))
									d.When(
										"below p it is f(k)",
										func(e *Argument, below Fact) {
											e.Show(
												"f(k) is a morphism",
												read,
												ByArith(below, inner, mor.At(k)))
										})
									d.Otherwise(
										"from p on",
										func(e *Argument, from Fact) {
											e.Cases(e.Term("p < k"))
											e.When(
												"past p it is f(k + 1)",
												func(g *Argument, past Fact) {
													g.Show(
														"f(k + 1) is a morphism, k + 1 being at most n + 1",
														read,
														ByArith(past, upTo, mor.At(g.TermAs[Nat]("k + 1"))))
												})
											e.Otherwise(
												"at p it is the composite",
												func(g *Argument, notPast Fact) {
													g.Show(
														"the composite is a morphism",
														read,
														ByArith(from, notPast, compIn))
												})
										})
								}))
							composable := c.Have(
								"each composes with the next, across the composite as well",
								"«composing»",
								Derive(func(d *Argument) {
									k := d.FixAs[Nat]()
									below := d.Assume()
									notEarly := d.Unless(
										d.Term("k + 1 < p"),
										"below p − 1 both are terms of f",
										Given(func(e *Argument, early Fact) {
											e.Show(
												"f(k) composes with f(k + 1)",
												read,
												ByArith(early, inner, next.At(k)))
										}))
									notEntering := d.Unless(
										d.Term("k < p"),
										"at p − 1 the next term is the composite",
										Given(func(e *Argument, entering Fact) {
											e.Show(
												"which f(p − 1) composes with",
												read,
												ByArith(notEarly, entering, enters.At(k)))
										}))
									notPast := d.Unless(
										d.Term("p < k"),
										"past p both are terms of f one index up",
										Given(func(e *Argument, past Fact) {
											e.Show(
												"f(k + 1) composes with f(k + 2)",
												read,
												ByArith(past, below, next.At(e.TermAs[Nat]("k + 1"))))
										}))
									at := d.Have(
										"k is p",
										"k = p",
										ByArith(notEntering, notPast))
									d.Show(
										"the composite composes with f(p + 2)",
										at.Rw(),
										read,
										ByArith(inner, leaves))
								}))
							last := c.Have(
								"its n-th term is f(n + 1), the identity at an object",
								"«ending»",
								read,
								ByArith(inner, end))
							constant := c.Have(
								"it is constant from n on, as f is from n + 1",
								"«padded»",
								Derive(func(d *Argument) {
									d.FixAs[Nat]()
									past := d.Assume()
									d.Show(
										"past n it is f(k + 1), and f is f(n + 1) past n + 1",
										read,
										ByArith(past, inner, stays.At(d.TermAs[Nat]("k + 1"))))
								}))
							c.Show(
								"so it is a chain of n morphisms",
								Simp(Fwd(NerveSimplicesDef)),
								BySets(terms, composable, last, constant))
						})
				})
		}),
})}

// NerveDegeneracyIn — a degeneracy of a chain of length n is a chain
// of length n + 1. The inserted identity is a morphism from the source
// of f(i) to itself, so it composes with the terms on either side.
// The new final term is f(n), and the shifted padding is constant.
var NerveDegeneracyIn = nerveDegeneracyInThm{family.Add(registry.ProofEntry{
	Name: "NerveDegeneracyIn",
	Key:  "prop_33a1ca79a3bbdd56",
	Build: category.Category.Law(Statement{
		Binders: "∀n i:num. ∀f:(num → M).",
		Hypotheses: []string{
			"f ∈ nerve_simplices(C, n)",
			"i ≤ n",
		},
		Conclusion: "nerve_degeneracy(C, i, f) ∈ nerve_simplices(C, n + 1)",
		Abbrev: Abbrev{
			{Name: "morphisms", Text: "∀k:num. k ≤ n + 1 ⇒ nerve_degeneracy(C, i, f, k) ∈ C.morphisms"},
			{Name: "composing", Text: "∀k:num. " +
				"    k < n + 1 ⇒ " +
				"    C.target(nerve_degeneracy(C, i, f, k)) = C.source(nerve_degeneracy(C, i, f, k + 1))"},
			{Name: "ending", Text: "∃x:A. x ∈ C.objects ∧ nerve_degeneracy(C, i, f, n + 1) = C.identity(x)"},
			{Name: "padded", Text: "∀k:num. " +
				"    n + 1 < k ⇒ nerve_degeneracy(C, i, f, k) = nerve_degeneracy(C, i, f, n + 1)"},
		},
	},
		func(a *Argument, cat Fact, n, i *Expr[Nat], f Term, given Fact) {
			parts := a.Conjuncts(
				given,
				"f is a chain of n morphisms",
				"and i indexes one of its degeneracies")
			chain, iUpTo := parts[0], parts[1]
			clauses := a.Conjuncts(
				a.Have(
					"f read by the definition of the nerve",
					"(∀k:num. k ≤ n ⇒ f(k) ∈ C.morphisms) ∧ "+
						"(∀k:num. k < n ⇒ C.target(f(k)) = C.source(f(k + 1))) ∧ "+
						"(∃x:A. x ∈ C.objects ∧ f(n) = C.identity(x)) ∧ "+
						"(∀k:num. n < k ⇒ f(k) = f(n))",
					BySets(a.Unfolded(chain, NerveSimplicesDef))),
				"its terms up to n are morphisms",
				"each composes with the next",
				"its n-th term is the identity at an object",
				"and it is constant from n on")
			mor, next, end, stays := clauses[0], clauses[1], clauses[2], clauses[3]
			source := a.Have(
				"f(i) is a morphism, so its source is an object",
				"C.source(f(i)) ∈ C.objects",
				ByArith(iUpTo, mor.At(i), At(category.MorphismEnds.Read(cat), a.Term("f(i)"))))
			identity := a.Have(
				"the inserted identity is a morphism from that source to itself",
				"C.identity(C.source(f(i))) ∈ C.morphisms ∧ "+
					"C.source(C.identity(C.source(f(i)))) = C.source(f(i)) ∧ "+
					"C.target(C.identity(C.source(f(i)))) = C.source(f(i))",
				By(source, At(category.IdentityMorphism.Read(cat), a.TermAs[A]("C.source(f(i))"))))
			read := Simp(Fwd(NerveDegeneracyDef))
			terms := a.Have(
				"the terms are f below i, the identity at i and f one index back above i",
				"«morphisms»",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					upTo := b.Assume()
					b.Cases(b.Term("k < i"))
					b.When(
						"below i the term is f(k)",
						func(c *Argument, before Fact) {
							c.Show(
								"f(k) is a morphism",
								read,
								ByArith(before, iUpTo, mor.At(k)))
						})
					b.Otherwise(
						"from i on the term is inserted or shifted",
						func(c *Argument, notBefore Fact) {
							c.Cases(c.Term("k = i"))
							c.When(
								"at i the term is the inserted identity",
								func(d *Argument, _ Fact) {
									d.Show(
										"the identity is a morphism",
										read,
										ByArith(identity))
								})
							c.Otherwise(
								"past i the term is f(k − 1)",
								func(d *Argument, notAt Fact) {
									d.Show(
										"f(k − 1) is a morphism",
										read,
										ByArith(notBefore, notAt, upTo, mor.At(d.TermAs[Nat]("k - 1"))))
								})
						})
				}))
			composable := a.Have(
				"successive terms compose, including both sides of the inserted identity",
				"«composing»",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					below := b.Assume()
					b.Cases(b.Term("k + 1 < i"))
					b.When(
						"before i − 1 both terms are unchanged",
						func(c *Argument, early Fact) {
							c.Show(
								"f(k) composes with f(k + 1)",
								read,
								ByArith(early, iUpTo, next.At(k)))
						})
					b.Otherwise(
						"from i − 1 on a term is inserted or shifted",
						func(c *Argument, notEarly Fact) {
							c.Cases(c.Term("k < i"))
							c.When(
								"at i − 1 the next term is the inserted identity",
								func(d *Argument, entering Fact) {
									// Read the two terms before identifying the next index with i.
									d.Do(read)
									at := d.Have(
										"the next index is i",
										"k + 1 = i",
										ByArith(notEarly, entering))
									step := d.Have(
										"f(k) composes with f(k + 1)",
										"C.target(f(k)) = C.source(f(k + 1))",
										ByArith(entering, iUpTo, next.At(k)))
									d.Show(
										"its target is the source of the inserted identity",
										By(Normalized, at, step, identity))
								})
							c.Otherwise(
								"from i on the current term is inserted or shifted",
								func(d *Argument, notEntering Fact) {
									d.Cases(d.Term("i < k"))
									d.When(
										"past i both terms are shifted one index back",
										func(e *Argument, past Fact) {
											// The predecessor names the unchanged pair of terms in f.
											e.Do(read)
											p, kIs := e.ObtainAs[Nat](
												"k is p + 1",
												"∃p:num. k = p + 1",
												ByArith(past, nat_arith.NonzeroIsSucc.At(k)))
											e.Show(
												"f(p) composes with f(p + 1)",
												kIs.Rw(),
												Simp(Fwd(nat_monus.AddSubCancel)),
												ByArith(past, below, next.At(p)))
										})
									d.Otherwise(
										"at i the inserted identity is followed by f(i)",
										func(e *Argument, notPast Fact) {
											e.Do(read)
											at := e.Have(
												"the current index is i",
												"k = i",
												ByArith(notPast, notEntering))
											e.Show(
												"the identity has target the source of f(i)",
												at.Rw(),
												Simp(Fwd(nat_monus.AddSubCancel)),
												ByArith(identity))
										})
								})
						})
				}))
			lastValue := a.Have(
				"the new final term is f(n)",
				"nerve_degeneracy(C, i, f, n + 1) = f(n)",
				Simp(Fwd(NerveDegeneracyDef), Fwd(nat_monus.AddSubCancel)),
				ByArith(iUpTo))
			last := a.Have(
				"so it ends at the same object's identity",
				"«ending»",
				By(lastValue, end))
			constant := a.Have(
				"the shifted padding is constant from n + 1 on",
				"«padded»",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					past := b.Assume()
					b.Show(
						"past n + 1 the term is f(k − 1), equal to f(n)",
						Simp(Fwd(NerveDegeneracyDef), Fwd(nat_monus.AddSubCancel)),
						ByArith(past, iUpTo, stays.At(b.TermAs[Nat]("k - 1"))))
				}))
			a.Show(
				"the degeneracy is a chain of n + 1 morphisms",
				Simp(Fwd(NerveSimplicesDef)),
				BySets(terms, composable, last, constant))
		}),
})}

// NerveFaceFace — d_i d_j = d_{j−1} d_i on chains for i < j. Read at an
// index k, each side is f with two of its morphisms dropped or composed,
// and the two orders agree by arithmetic on the index — the drops and the
// compositions at a distance shift the chain in the same way — except
// where the two places meet. Two neighbouring compositions are the two
// bracketings of the triple f(i − 1), f(i), f(i + 1), equal by
// associativity; and where the last two morphisms are composed and the
// composite then dropped, the chain is re-padded with the identity at the
// source of the composite, which is the source of f(n), as when the two
// are dropped one at a time.
var NerveFaceFace = nerveFaceFaceThm{family.Add(registry.ProofEntry{
	Name: "NerveFaceFace",
	Key:  "prop_c0714def8b4b3cb6",
	Build: category.Category.Law(Statement{
		Binders: "∀n i j:num. ∀f:(num → M).",
		Hypotheses: []string{
			"f ∈ nerve_simplices(C, n + 2)",
			"i < j",
			"j ≤ n + 2",
		},
		Conclusion: "nerve_face(C, n + 1, i, nerve_face(C, n + 2, j, f)) = " +
			"nerve_face(C, n + 1, j - 1, nerve_face(C, n + 2, i, f))",
	},
		func(a *Argument, cat Fact, n, i, j *Expr[Nat], f Term, given Fact) {
			parts := a.Conjuncts(
				given,
				"f is a chain of n + 2 morphisms",
				"i is below j",
				"and j is at most n + 2")
			chain, iBelowJ, jUpTo := parts[0], parts[1], parts[2]
			links := a.Conjuncts(
				a.Have(
					"the terms of f up to n + 2 are morphisms, each composable with the next",
					"(∀m:num. m ≤ n + 2 ⇒ f(m) ∈ C.morphisms) ∧ "+
						"(∀m:num. m < n + 2 ⇒ C.target(f(m)) = C.source(f(m + 1)))",
					BySets(a.Simplified(chain, Fwd(NerveSimplicesDef)))),
				"the terms up to n + 2 are morphisms",
				"each composable with the next")
			morphisms, composable := links[0], links[1]

			a.Show(
				"index by index, each side read through its two faces",
				Funext(),
				Simp(Fwd(NerveFaceDef)),
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					b.Cases(b.Term("i = 0"))
					b.When(
						"d_0 drops the first morphism",
						func(c *Argument, first Fact) {
							c.Cases(c.Term("j = n + 2"))
							c.When(
								"and d_{n+2} the last",
								func(d *Argument, last Fact) {
									d.Cases(d.Term("k < n"))
									d.When(
										"below n",
										func(e *Argument, below Fact) {
											e.Show(
												"both sides read f(k + 1)",
												ByArith(first, last, below))
										})
									d.Otherwise(
										"from n on",
										func(e *Argument, past Fact) {
											e.Show(
												"both sides re-pad with the identity at the source of f(n + 1)",
												ByArith(first, last, past))
										})
								})
							c.Otherwise(
								"and d_j composes f(j − 1) and f(j)",
								func(d *Argument, inner Fact) {
									d.Cases(d.Term("k + 1 + 1 < j"))
									d.When(
										"below the composite",
										func(e *Argument, below Fact) {
											e.Show(
												"both sides read f(k + 1)",
												ByArith(first, inner, below))
										})
									d.Otherwise(
										"at or past the composite",
										func(e *Argument, notBelow Fact) {
											e.Cases(e.Term("j = k + 1 + 1"))
											e.When(
												"at k = j − 2",
												func(g *Argument, at Fact) {
													inside := g.Have(
														"the composite sits inside the chain, so d_{j−1} of the 0-th face is an inner face too",
														"k + 1 + 1 < n + 2",
														ByArith(inner, jUpTo, at))
													g.Show(
														"both sides read the composite of f(k + 1) and f(k + 2)",
														at.Rw(),
														ByArith(first, inside))
												})
											e.Otherwise(
												"past it",
												func(g *Argument, past Fact) {
													g.Show(
														"both sides read f(k + 2)",
														ByArith(first, inner, iBelowJ, notBelow, past))
												})
										})
								})
						})
					b.Otherwise(
						"d_i composes f(i − 1) and f(i)",
						func(c *Argument, notFirst Fact) {
							c.Cases(c.Term("j = n + 2"))
							c.When(
								"and d_{n+2} drops the last morphism",
								func(d *Argument, last Fact) {
									d.Cases(d.Term("i = n + 1"))
									d.When(
										"d_{n+1} composes the last two morphisms",
										func(e *Argument, lastPair Fact) {
											e.Cases(e.Term("k < n"))
											e.When(
												"below n",
												func(g *Argument, below Fact) {
													g.Show(
														"both sides read f(k)",
														ByArith(last, lastPair, below))
												})
											e.Otherwise(
												"from n on",
												func(g *Argument, past Fact) {
													pair := g.Have(
														"f(n) and f(n + 1) are composable morphisms",
														"f(n) ∈ C.morphisms ∧ f(n + 1) ∈ C.morphisms ∧ C.target(f(n)) = C.source(f(n + 1))",
														ByArith(morphisms.At(n), morphisms.At(g.TermAs[Nat]("n + 1")), composable.At(n)))
													composite := g.Have(
														"their composite has the source of f(n)",
														"C.source(C.compose(f(n + 1), f(n))) = C.source(f(n))",
														By(pair, At(category.CompositeMorphism.Read(cat), g.Term("f(n)"), g.Term("f(n + 1)"))))
													g.Show(
														"both sides re-pad with the identity at the source of f(n)",
														lastPair.Rw(),
														ByArith(composite, last, past))
												})
										})
									d.Otherwise(
										"d_i composes below the last morphism",
										func(e *Argument, innerPair Fact) {
											e.Cases(e.Term("k < n"))
											e.When(
												"below n",
												func(g *Argument, below Fact) {
													g.Show(
														"both sides read f with f(i − 1) and f(i) composed",
														ByArith(notFirst, last, innerPair, below, iBelowJ))
												})
											e.Otherwise(
												"from n on",
												func(g *Argument, past Fact) {
													g.Show(
														"both sides re-pad with the identity at the source of f(n + 1)",
														ByArith(notFirst, last, innerPair, past, iBelowJ))
												})
										})
								})
							c.Otherwise(
								"and d_j composes f(j − 1) and f(j)",
								func(d *Argument, inner Fact) {
									d.Cases(d.Term("j = i + 1"))
									d.When(
										"the two compositions are neighbours",
										func(e *Argument, neighbours Fact) {
											notBelow := e.Unless(
												e.Term("k + 1 < i"),
												"below them",
												Given(func(g *Argument, below Fact) {
													g.Show(
														"both sides read f(k)",
														ByArith(notFirst, inner, jUpTo, neighbours, below))
												}))
											e.Cases(e.Term("i = k + 1"))
											e.When(
												"at k = i − 1",
												func(g *Argument, at Fact) {
													inside := g.Have(
														"the triple sits inside the chain, so its terms are morphisms and d_i is an inner face",
														"k + 1 + 1 < n + 2",
														ByArith(inner, jUpTo, neighbours, at))
													triple := g.Have(
														"f(k), f(k + 1) and f(k + 2) are morphisms, each composable with the next",
														"f(k) ∈ C.morphisms ∧ "+
															"f(k + 1) ∈ C.morphisms ∧ "+
															"f(k + 1 + 1) ∈ C.morphisms ∧ "+
															"C.target(f(k)) = C.source(f(k + 1)) ∧ "+
															"C.target(f(k + 1)) = C.source(f(k + 1 + 1))",
														ByArith(
															morphisms.At(k),
															morphisms.At(g.TermAs[Nat]("k + 1")),
															morphisms.At(g.TermAs[Nat]("k + 1 + 1")),
															composable.At(k),
															composable.At(g.TermAs[Nat]("k + 1")),
															inside))
													associative := g.Have(
														"composition associates on the triple",
														"C.compose(f(k + 1 + 1), C.compose(f(k + 1), f(k))) = "+
															"C.compose(C.compose(f(k + 1 + 1), f(k + 1)), f(k))",
														By(
															triple,
															At(category.Assoc.Read(cat), g.Term("f(k)"), g.Term("f(k + 1)"), g.Term("f(k + 1 + 1)"))))
													g.Show(
														"the two sides are its two bracketings",
														neighbours.Rw(),
														at.Rw(),
														ByArith(associative, inside))
												})
											e.Otherwise(
												"past them",
												func(g *Argument, past Fact) {
													g.Show(
														"both sides read f(k + 2)",
														ByArith(notFirst, inner, jUpTo, neighbours, notBelow, past))
												})
										})
									d.Otherwise(
										"the two compositions are apart",
										func(e *Argument, apart Fact) {
											notBelow := e.Unless(
												e.Term("k + 1 + 1 < j"),
												"below the outer one",
												Given(func(g *Argument, below Fact) {
													g.Show(
														"both sides read f with f(i − 1) and f(i) composed",
														ByArith(notFirst, inner, iBelowJ, jUpTo, apart, below))
												}))
											e.Cases(e.Term("j = k + 1 + 1"))
											e.When(
												"at k = j − 2",
												func(g *Argument, at Fact) {
													placed := g.Have(
														"the outer composite lies past the inner one and "+
															"inside the chain, where d_{j−1} is an inner face too",
														"i < k + 1 ∧ k + 1 + 1 < n + 2",
														ByArith(inner, iBelowJ, jUpTo, apart, at))
													g.Show(
														"both sides read the composite of f(k + 1) and f(k + 2)",
														at.Rw(),
														ByArith(notFirst, placed))
												})
											e.Otherwise(
												"past it",
												func(g *Argument, past Fact) {
													g.Show(
														"both sides read f(k + 2)",
														ByArith(notFirst, inner, iBelowJ, jUpTo, apart, notBelow, past))
												})
										})
								})
						})
				}))
		}),
})}

// NerveDegeneracyDegeneracy — the degeneracies satisfy their simplicial identity.
// Both orders insert the identities at the sources of f(i) and f(j)
// at positions i and j + 1. When i = j the first insertion reads the
// source of an identity, which is the same object. The other positions
// are unchanged, shifted once between the insertions and twice after them.
var NerveDegeneracyDegeneracy = nerveDegeneracyDegeneracyThm{family.Add(registry.ProofEntry{
	Name: "NerveDegeneracyDegeneracy",
	Key:  "prop_c7da2ad5b12d1898",
	Build: category.Category.Law(Statement{
		Binders: "∀n i j:num. ∀f:(num → M).",
		Hypotheses: []string{
			"f ∈ nerve_simplices(C, n)",
			"i ≤ j",
			"j ≤ n",
		},
		Conclusion: "nerve_degeneracy(C, i, nerve_degeneracy(C, j, f)) = " +
			"nerve_degeneracy(C, j + 1, nerve_degeneracy(C, i, f))",
	},
		func(a *Argument, cat Fact, n, i, j *Expr[Nat], f Term, given Fact) {
			parts := a.Conjuncts(
				given,
				"f is a chain of n morphisms",
				"i is at most j",
				"and j is at most n")
			chain, iUpToJ, jUpTo := parts[0], parts[1], parts[2]
			morphisms := a.Have(
				"the terms of f up to n are morphisms",
				"∀k:num. k ≤ n ⇒ f(k) ∈ C.morphisms",
				BySets(a.Unfolded(chain, NerveSimplicesDef)))
			source := a.Have(
				"f(i) is a morphism, so its source is an object",
				"C.source(f(i)) ∈ C.objects",
				ByArith(iUpToJ, jUpTo, morphisms.At(i), At(category.MorphismEnds.Read(cat), a.Term("f(i)"))))
			identitySource := a.Have(
				"inserting an identity keeps the source object",
				"C.source(C.identity(C.source(f(i)))) = C.source(f(i))",
				By(source, At(category.IdentityMorphism.Read(cat), a.TermAs[A]("C.source(f(i))"))))
			read := Simp(Fwd(NerveDegeneracyDef))
			a.Show(
				"both orders of insertion agree at every index",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					notBefore := b.Unless(
						b.Term("k < i"),
						"below i neither insertion shifts f(k)",
						Given(func(c *Argument, before Fact) {
							c.Show(
								"both terms are f(k)",
								read,
								ByArith(before, iUpToJ))
						}))
					notFirst := b.Unless(
						b.Term("k = i"),
						"at i both orders insert the first identity",
						Given(func(c *Argument, at Fact) {
							c.Show(
								"the identities at the first insertion have the same source",
								at.Rw(),
								Derive(func(d *Argument) {
									d.Cases(d.Term("i = j"))
									d.When(
										"coincident insertions read the source of the first identity",
										func(e *Argument, same Fact) {
											e.Show(
												"that source is the original source object",
												read,
												ByArith(same, identitySource))
										})
									d.Otherwise(
										"separate insertions read the source of f(i)",
										func(e *Argument, different Fact) {
											e.Show(
												"the first identity is unchanged",
												read,
												ByArith(iUpToJ, different))
										})
								}))
						}))
					notBetween := b.Unless(
						b.Term("k < j + 1"),
						"between the inserted identities both orders shift once",
						Given(func(c *Argument, between Fact) {
							c.Show(
								"both terms are f(k − 1)",
								read,
								ByArith(notBefore, notFirst, between))
						}))
					notSecond := b.Unless(
						b.Term("k = j + 1"),
						"at j + 1 both orders insert the second identity",
						Given(func(c *Argument, at Fact) {
							c.Show(
								"both identities are at the source of f(j)",
								at.Rw(),
								Simp(Fwd(NerveDegeneracyDef), Fwd(nat_monus.AddSubCancel)),
								ByArith(iUpToJ))
						}))
					b.Show(
						"past j + 1 both orders shift twice",
						read,
						ByArith(iUpToJ, notBetween, notSecond))
				}))
		}),
})}

// NerveFaceDegeneracyBelow — a face below an insertion shifts that
// insertion down one place. Writing j = q + 1, the identity appears at
// q in either order, with the source of f(q + 1). A first face drops
// the first term; an inner face composes the same original pair below
// q. Above q the face's shift and the insertion's shift cancel.
var NerveFaceDegeneracyBelow = nerveFaceDegeneracyBelowThm{family.Add(registry.ProofEntry{
	Name: "NerveFaceDegeneracyBelow",
	Key:  "prop_c355127189b140ba",
	Reading: "No chain condition and no law of the category is read, only the " +
		"definitions of the face and the degeneracy, so the identity holds for every sequence.",
	Build: family.Theorem(Statement{
		Binders: "∀C:category_ops(A, M). ∀n i j:num. ∀f:(num → M).",
		Hypotheses: []string{
			"i < j",
			"j ≤ n + 1",
		},
		Conclusion: "nerve_face(C, n + 2, i, nerve_degeneracy(C, j, f)) = " +
			"nerve_degeneracy(C, j - 1, nerve_face(C, n + 1, i, f))",
	},
		func(a *Argument, C Term, n, i, j *Expr[Nat], f Term, given Fact) {
			parts := a.Conjuncts(
				given,
				"the face is below the insertion",
				"and the insertion is at most n + 1")
			iBelowJ, jUpTo := parts[0], parts[1]
			_, jIs := a.ObtainAs[Nat](
				"j is q + 1",
				"∃q:num. j = q + 1",
				ByArith(iBelowJ, nat_arith.NonzeroIsSucc.At(j)))
			bounds := a.Have(
				"the face is at most q and q is at most n",
				"i ≤ q ∧ q ≤ n",
				ByArith(iBelowJ, jUpTo, jIs))
			read := Simp(Fwd(NerveFaceDef), Fwd(NerveDegeneracyDef), Fwd(nat_monus.AddSubCancel))
			notFirst := a.Unless(
				a.Term("i = 0"),
				"the first face drops the first term",
				Given(func(b *Argument, first Fact) {
					firstRead := Chain(first.Rw(), jIs.Rw(), read)
					b.Show(
						"dropping the first term moves the insertion from q + 1 to q",
						Funext(),
						Derive(func(c *Argument) {
							c.FixAs[Nat]("k")
							notBefore := c.Unless(
								c.Term("k < q"),
								"below q both sides read f one index up",
								Given(func(d *Argument, before Fact) {
									d.Show(
										"both terms are f(k + 1)",
										firstRead,
										ByArith(before))
								}))
							notAt := c.Unless(
								c.Term("k = q"),
								"at q both sides insert the identity at the source of f(q + 1)",
								Given(func(d *Argument, at Fact) {
									d.Show(
										"the inserted identities agree",
										at.Rw(),
										firstRead,
										ByArith())
								}))
							c.Have(
								"past q the index has a predecessor",
								"1 ≤ k",
								ByArith(notBefore, notAt))
							c.Show(
								"above q the two shifts cancel",
								first.Rw(),
								jIs.Rw(),
								Simp(
									Fwd(NerveFaceDef),
									Fwd(NerveDegeneracyDef),
									Fwd(nat_monus.AddSubCancel),
									Fwd(nat_monus.SubAddCancel)),
								ByArith(notBefore, notAt))
						}))
				}))
			_, iIs := a.ObtainAs[Nat](
				"the positive face is p + 1",
				"∃p:num. i = p + 1",
				By(notFirst, nat_arith.NonzeroIsSucc.At(i)))
			inner := a.Have(
				"the composition coordinate p is below the insertion coordinate q",
				"p < q",
				ByArith(bounds, iIs))
			innerRead := Chain(iIs.Rw(), jIs.Rw(), read)
			a.Show(
				"the inner face and insertion agree at every index",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					notBefore := b.Unless(
						b.Term("k < p"),
						"below p both operations keep f(k)",
						Given(func(c *Argument, before Fact) {
							c.Show(
								"the term is unchanged",
								innerRead,
								ByArith(inner, bounds, before))
						}))
					notComposite := b.Unless(
						b.Term("k = p"),
						"at p both sides compose f(p) and f(p + 1)",
						Given(func(c *Argument, at Fact) {
							c.Show(
								"the composites agree",
								at.Rw(),
								innerRead,
								ByArith(inner, bounds))
						}))
					notBetween := b.Unless(
						b.Term("k < q"),
						"between p and q both sides read f one index up",
						Given(func(c *Argument, between Fact) {
							c.Show(
								"both terms are f(k + 1)",
								innerRead,
								ByArith(inner, bounds, notBefore, notComposite, between))
						}))
					notInserted := b.Unless(
						b.Term("k = q"),
						"at q both sides insert the identity at the source of f(q + 1)",
						Given(func(c *Argument, at Fact) {
							c.Show(
								"the inserted identities agree",
								at.Rw(),
								innerRead,
								ByArith(inner, bounds))
						}))
					b.Have(
						"past q the index has a predecessor",
						"1 ≤ k",
						ByArith(notBetween, notInserted))
					b.Show(
						"above q the two shifts cancel",
						innerRead,
						Simp(Fwd(nat_monus.SubAddCancel)),
						ByArith(inner, bounds, notBetween, notInserted))
				}))
		}),
})}

// NerveFaceDegeneracyEqual — d_i s_i is the identity on chains: the
// 0-th face drops the inserted identity. At i = p + 1 the face is
// inner and composes that identity with f(p); the chain identifies its
// source with the target of f(p), and the left unit law removes it.
// All other terms retain their index or have the two shifts cancelled.
var NerveFaceDegeneracyEqual = nerveFaceDegeneracyEqualThm{family.Add(registry.ProofEntry{
	Name: "NerveFaceDegeneracyEqual",
	Key:  "prop_5f2509a243364acf",
	Build: category.Category.Law(Statement{
		Binders: "∀n i:num. ∀f:(num → M).",
		Hypotheses: []string{
			"f ∈ nerve_simplices(C, n)",
			"i ≤ n",
		},
		Conclusion: "nerve_face(C, n + 1, i, nerve_degeneracy(C, i, f)) = f",
	},
		func(a *Argument, cat Fact, n, i *Expr[Nat], f Term, given Fact) {
			parts := a.Conjuncts(
				given,
				"f is a chain of n morphisms",
				"and i indexes one of its degeneracies")
			chain, iUpTo := parts[0], parts[1]
			notFirst := a.Unless(
				a.Term("i = 0"),
				"the 0-th face drops the inserted identity",
				Given(func(b *Argument, first Fact) {
					b.Show(
						"every term of f is recovered one index up",
						Funext(),
						Derive(func(c *Argument) {
							c.FixAs[Nat]("k")
							c.Show(
								"the two shifts cancel",
								Simp(Fwd(NerveFaceDef), Fwd(NerveDegeneracyDef), Fwd(nat_monus.AddSubCancel)),
								ByArith(first))
						}))
				}))
			p, iIs := a.ObtainAs[Nat](
				"i is p + 1",
				"∃p:num. i = p + 1",
				By(notFirst, nat_arith.NonzeroIsSucc.At(i)))
			inner := a.Have(
				"p is below n, so this face is inner",
				"p < n",
				ByArith(iUpTo, iIs))
			clauses := a.Conjuncts(
				a.Have(
					"the terms of f are morphisms with adjacent endpoints equal",
					"(∀k:num. k ≤ n ⇒ f(k) ∈ C.morphisms) ∧ (∀k:num. k < n ⇒ C.target(f(k)) = C.source(f(k + 1)))",
					BySets(a.Unfolded(chain, NerveSimplicesDef))),
				"the terms up to n are morphisms",
				"each composes with the next")
			mor, next := clauses[0], clauses[1]
			morphism := a.Have(
				"f(p) is a morphism",
				"f(p) ∈ C.morphisms",
				ByArith(inner, mor.At(p)))
			joins := a.Have(
				"the source of the inserted identity is the target of f(p)",
				"C.target(f(p)) = C.source(f(p + 1))",
				By(inner, next.At(p)))
			cancel := a.Have(
				"composing the inserted identity after f(p) gives f(p)",
				"C.compose(C.identity(C.source(f(p + 1))), f(p)) = f(p)",
				By(Normalized, joins, morphism, At(category.LeftUnit.Read(cat), a.Term("f(p)"))))
			read := Chain(iIs.Rw(), Simp(
				Fwd(NerveFaceDef),
				Fwd(NerveDegeneracyDef),
				Fwd(nat_monus.AddSubCancel)))
			a.Show(
				"the original chain is recovered at every index",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					b.Cases(b.Term("k < p"))
					b.When(
						"below p both operations keep the term f(k)",
						func(c *Argument, before Fact) {
							c.Show(
								"the term is unchanged",
								read,
								ByArith(before, inner))
						})
					b.Otherwise(
						"from p on the term is composed or shifted",
						func(c *Argument, notBefore Fact) {
							c.Cases(c.Term("k = p"))
							c.When(
								"at p the left unit law removes the inserted identity",
								func(d *Argument, at Fact) {
									d.Show(
										"the composite is f(p)",
										at.Rw(),
										read,
										ByArith(inner, cancel))
								})
							c.Otherwise(
								"above p the two shifts cancel",
								func(d *Argument, notAt Fact) {
									d.Show(
										"the term is again f(k)",
										read,
										ByArith(inner, notBefore, notAt))
								})
						})
				}))
		}),
})}

// NerveFaceDegeneracyNext — d_{i+1} s_i is the identity on chains: the
// inner face composes f(i) with the inserted identity at its source,
// which the right unit law removes. At i = n the last face re-pads
// with the same terminal identity; beyond n the original chain is
// already constant. The remaining coordinates cancel the two shifts.
var NerveFaceDegeneracyNext = nerveFaceDegeneracyNextThm{family.Add(registry.ProofEntry{
	Name: "NerveFaceDegeneracyNext",
	Key:  "prop_8599ac5eb05431c1",
	Build: category.Category.Law(Statement{
		Binders: "∀n i:num. ∀f:(num → M).",
		Hypotheses: []string{
			"f ∈ nerve_simplices(C, n)",
			"i ≤ n",
		},
		Conclusion: "nerve_face(C, n + 1, i + 1, nerve_degeneracy(C, i, f)) = f",
	},
		func(a *Argument, cat Fact, n, i *Expr[Nat], f Term, given Fact) {
			parts := a.Conjuncts(
				given,
				"f is a chain of n morphisms",
				"and i indexes one of its degeneracies")
			chain, iUpTo := parts[0], parts[1]
			clauses := a.Conjuncts(
				a.Have(
					"the terms of f are morphisms, ending at an identity and constant thereafter",
					"(∀k:num. k ≤ n ⇒ f(k) ∈ C.morphisms) ∧ "+
						"(∃x:A. x ∈ C.objects ∧ f(n) = C.identity(x)) ∧ "+
						"(∀k:num. n < k ⇒ f(k) = f(n))",
					BySets(a.Unfolded(chain, NerveSimplicesDef))),
				"the terms up to n are morphisms",
				"the n-th term is an object's identity",
				"the padding is constant")
			mor, end, stays := clauses[0], clauses[1], clauses[2]
			read := Simp(Fwd(NerveFaceDef), Fwd(NerveDegeneracyDef), Fwd(nat_monus.AddSubCancel))
			a.Cases(a.Term("i = n"))
			a.When(
				"at i = n the face is the last face",
				func(b *Argument, last Fact) {
					x, ends := b.UnpackAs[A](end)
					terminal := b.Conjuncts(
						ends,
						"the end object belongs to C",
						"f(n) is its identity")
					object, lastIs := terminal[0], terminal[1]
					source := b.Have(
						"the identity at the end object has that object as its source",
						"C.source(C.identity(x)) = x",
						By(object, At(category.IdentityMorphism.Read(cat), x)))
					repad := b.Have(
						"re-padding at the source of the inserted terminal identity recovers f(n)",
						"C.identity(C.source(C.identity(C.source(f(n))))) = f(n)",
						By(Normalized, lastIs, source))
					lastRead := Chain(last.Rw(), read)
					b.Show(
						"the last face recovers the original chain at every index",
						Funext(),
						Derive(func(c *Argument) {
							k := c.FixAs[Nat]("k")
							c.Cases(c.Term("k < n"))
							c.When(
								"below n both operations keep f(k)",
								func(d *Argument, below Fact) {
									d.Show(
										"the term is unchanged",
										lastRead,
										ByArith(below))
								})
							c.Otherwise(
								"from n on the face re-pads with the terminal identity",
								func(d *Argument, notBelow Fact) {
									d.Cases(d.Term("k = n"))
									d.When(
										"at n the new padding equals f(n)",
										func(e *Argument, at Fact) {
											e.Show(
												"the terminal term is recovered",
												at.Rw(),
												lastRead,
												ByArith(repad))
										})
									d.Otherwise(
										"past n the original chain is constant",
										func(e *Argument, notAt Fact) {
											e.Show(
												"its padding agrees with the new padding",
												lastRead,
												ByArith(notBelow, notAt, repad, stays.At(k)))
										})
								})
						}))
				})
			a.Otherwise(
				"below n the face composes away the inserted identity",
				func(b *Argument, notLast Fact) {
					inner := b.Have(
						"i is below n, so i + 1 is an inner face",
						"i < n",
						ByArith(notLast, iUpTo))
					cancel := b.Have(
						"composing the inserted identity before f(i) gives f(i)",
						"C.compose(f(i), C.identity(C.source(f(i)))) = f(i)",
						ByArith(iUpTo, mor.At(i), At(category.RightUnit.Read(cat), b.Term("f(i)"))))
					b.Show(
						"the inner face recovers the original chain at every index",
						Funext(),
						Derive(func(c *Argument) {
							c.FixAs[Nat]("k")
							c.Cases(c.Term("k < i"))
							c.When(
								"below i both operations keep f(k)",
								func(d *Argument, before Fact) {
									d.Show(
										"the term is unchanged",
										read,
										ByArith(inner, before))
								})
							c.Otherwise(
								"from i on the term is composed or shifted",
								func(d *Argument, notBefore Fact) {
									d.Cases(d.Term("k = i"))
									d.When(
										"at i the right unit law removes the inserted identity",
										func(e *Argument, at Fact) {
											e.Show(
												"the composite is f(i)",
												at.Rw(),
												read,
												ByArith(inner, cancel))
										})
									d.Otherwise(
										"above i the two shifts cancel",
										func(e *Argument, notAt Fact) {
											e.Show(
												"the term is again f(k)",
												read,
												ByArith(inner, notBefore, notAt))
										})
								})
						}))
				})
		}),
})}

// NerveFaceDegeneracyAbove — a face above an insertion leaves the
// insertion in place and shifts its own index down one. At the closest
// inner face, the composite has the source of its first morphism; at
// the last face, an identity at that source has the same source. These
// are the two ways the face can meet the insertion's source. The other
// coordinates agree by their shifts, composition or terminal padding.
var NerveFaceDegeneracyAbove = nerveFaceDegeneracyAboveThm{family.Add(registry.ProofEntry{
	Name: "NerveFaceDegeneracyAbove",
	Key:  "prop_f555e7b00bf45b93",
	Build: category.Category.Law(Statement{
		Binders: "∀n i j:num. ∀f:(num → M).",
		Hypotheses: []string{
			"f ∈ nerve_simplices(C, n + 1)",
			"j + 1 < i",
			"i ≤ n + 2",
		},
		Conclusion: "nerve_face(C, n + 2, i, nerve_degeneracy(C, j, f)) = " +
			"nerve_degeneracy(C, j, nerve_face(C, n + 1, i - 1, f))",
	},
		func(a *Argument, cat Fact, n, i, j *Expr[Nat], f Term, given Fact) {
			parts := a.Conjuncts(
				given,
				"f is a chain of n + 1 morphisms",
				"the face is above the insertion",
				"and the face is at most n + 2")
			chain, after, iUpTo := parts[0], parts[1], parts[2]
			clauses := a.Conjuncts(
				a.Have(
					"the terms of f are morphisms with adjacent endpoints equal",
					"(∀k:num. k ≤ n + 1 ⇒ f(k) ∈ C.morphisms) ∧ "+
						"(∀k:num. k < n + 1 ⇒ C.target(f(k)) = C.source(f(k + 1)))",
					BySets(a.Unfolded(chain, NerveSimplicesDef))),
				"the terms up to n + 1 are morphisms",
				"each composes with the next")
			mor, next := clauses[0], clauses[1]
			jUpTo := a.Have(
				"the insertion is at most n",
				"j ≤ n",
				ByArith(after, iUpTo))
			dimension := a.Have(
				"the new dimension is two successive increments",
				"n + 2 = n + 1 + 1",
				ByArith())
			read := Simp(Fwd(NerveFaceDef), Fwd(NerveDegeneracyDef), Fwd(nat_monus.AddSubCancel))
			a.Cases(a.Term("i = n + 2"))
			a.When(
				"the last face re-pads the chain",
				func(b *Argument, last Fact) {
					source := b.Have(
						"f(j) is a morphism, so its source is an object",
						"C.source(f(j)) ∈ C.objects",
						ByArith(jUpTo, mor.At(j), At(category.MorphismEnds.Read(cat), b.Term("f(j)"))))
					identitySource := b.Have(
						"the repadding identity has the original source",
						"C.source(C.identity(C.source(f(j)))) = C.source(f(j))",
						By(source, At(category.IdentityMorphism.Read(cat), b.TermAs[A]("C.source(f(j))"))))
					lastRead := Chain(last.Rw(), dimension.Rw(), read)
					b.Show(
						"the insertion and the two last faces agree at every index",
						Funext(),
						Derive(func(c *Argument) {
							c.FixAs[Nat]("k")
							notBefore := c.Unless(
								c.Term("k < j"),
								"below j neither operation changes f(k)",
								Given(func(d *Argument, before Fact) {
									d.Show(
										"both terms are f(k)",
										lastRead,
										ByArith(before, jUpTo))
								}))
							notInserted := c.Unless(
								c.Term("k = j"),
								"at j both sides insert an identity at the same source",
								Given(func(d *Argument, at Fact) {
									d.Show(
										"the face keeps the source used by the insertion",
										at.Rw(),
										Derive(func(e *Argument) {
											e.Cases(e.Term("j = n"))
											e.When(
												"at n the insertion reads the repadding identity's source",
												func(g *Argument, atEnd Fact) {
													g.Show(
														"that source is unchanged",
														lastRead,
														ByArith(atEnd, identitySource))
												})
											e.Otherwise(
												"below n the last face keeps f(j)",
												func(g *Argument, notEnd Fact) {
													g.Show(
														"the source is unchanged",
														lastRead,
														ByArith(notEnd, jUpTo))
												})
										}))
								}))
							notMiddle := c.Unless(
								c.Term("k < n + 1"),
								"between the insertion and padding both sides shift once",
								Given(func(d *Argument, middle Fact) {
									d.Show(
										"both terms are f(k − 1)",
										lastRead,
										ByArith(notBefore, notInserted, middle, jUpTo))
								}))
							c.Show(
								"from n + 1 on both sides have the same terminal padding",
								lastRead,
								ByArith(notMiddle, jUpTo))
						}))
				})
			a.Otherwise(
				"an inner face composes two original morphisms",
				func(b *Argument, notLast Fact) {
					p, iIs := b.ObtainAs[Nat](
						"i is p + 1 + 1",
						"∃p:num. i = p + 1 + 1",
						Derive(func(c *Argument) {
							c.Take(c.TermAs[Nat]("i - 2"))
							c.Show(
								"the face is at least two places up",
								ByArith(after))
						}))
					bounds := b.Have(
						"the insertion is at most p and p is below n",
						"j ≤ p ∧ p < n",
						ByArith(after, iUpTo, notLast, iIs))
					compositeSource := b.Have(
						"the composite of f(p) followed by f(p + 1) has the source of f(p)",
						"C.source(C.compose(f(p + 1), f(p))) = C.source(f(p))",
						ByArith(
							bounds,
							mor.At(p),
							mor.At(b.TermAs[Nat]("p + 1")),
							next.At(p),
							At(category.CompositeMorphism.Read(cat), b.Term("f(p)"), b.Term("f(p + 1)"))))
					innerRead := Chain(iIs.Rw(), read)
					b.Show(
						"the insertion and the two inner faces agree at every index",
						Funext(),
						Derive(func(c *Argument) {
							c.FixAs[Nat]("k")
							notBefore := c.Unless(
								c.Term("k < j"),
								"below j both sides keep f(k)",
								Given(func(d *Argument, before Fact) {
									d.Show(
										"the term is unchanged",
										innerRead,
										ByArith(before, bounds))
								}))
							notInserted := c.Unless(
								c.Term("k = j"),
								"at j both sides insert an identity at the same source",
								Given(func(d *Argument, at Fact) {
									d.Show(
										"the face keeps the source used by the insertion",
										at.Rw(),
										Derive(func(e *Argument) {
											e.Cases(e.Term("j = p"))
											e.When(
												"at p the source is read from the composite",
												func(g *Argument, atComposite Fact) {
													g.Show(
														"the composite keeps the source of f(p)",
														innerRead,
														ByArith(atComposite, bounds, compositeSource))
												})
											e.Otherwise(
												"below p the face keeps f(j)",
												func(g *Argument, notComposite Fact) {
													g.Show(
														"the source is unchanged",
														innerRead,
														ByArith(notComposite, bounds))
												})
										}))
								}))
							notMiddle := c.Unless(
								c.Term("k < p + 1"),
								"between j and p + 1 both sides shift once",
								Given(func(d *Argument, middle Fact) {
									d.Show(
										"both terms are f(k − 1)",
										innerRead,
										ByArith(notBefore, notInserted, middle, bounds))
								}))
							notComposite := c.Unless(
								c.Term("k = p + 1"),
								"at p + 1 both sides compose f(p) and f(p + 1)",
								Given(func(d *Argument, at Fact) {
									d.Show(
										"the composites agree",
										at.Rw(),
										innerRead,
										ByArith(bounds))
								}))
							c.Have(
								"past p + 1 the index has a predecessor",
								"1 ≤ k",
								ByArith(notMiddle, notComposite))
							c.Show(
								"past p + 1 the two shifts cancel",
								innerRead,
								Simp(Fwd(nat_monus.SubAddCancel)),
								ByArith(notMiddle, notComposite, bounds))
						}))
				})
		}),
})}

// NerveSimplicialSet — the nerve of a category is a simplicial set:
// the two closure laws and six simplicial identities give its eight axioms.
var NerveSimplicialSet = nerveSimplicialSetThm{family.Add(registry.ProofEntry{
	Name: "NerveSimplicialSet",
	Key:  "prop_dc3db9692b86eb89",
	Build: category.Category.Law("simplicial_set(nerve(C))",
		func(a *Argument, cat Fact) {
			a.Show(
				"the chains and their maps satisfy the eight simplicial axioms",
				Simp(Fwd(simplicial_set.SimplicialSet)),
				SplitConjAll(
					Case(
						"faces of chains have one lower dimension",
						Cite(NerveFaceIn.Read(cat))),
					Case(
						"degeneracies of chains have one higher dimension",
						Cite(NerveDegeneracyIn.Read(cat))),
					Case(
						"two faces satisfy the face identity",
						Cite(NerveFaceFace.Read(cat))),
					Case(
						"two degeneracies satisfy the shifted insertion identity",
						Cite(NerveDegeneracyDegeneracy.Read(cat))),
					Case(
						"a face below an insertion shifts the insertion down",
						By(NerveFaceDegeneracyBelow)),
					Case(
						"the face at an insertion cancels it",
						Cite(NerveFaceDegeneracyEqual.Read(cat))),
					Case(
						"the face just past an insertion cancels it",
						Cite(NerveFaceDegeneracyNext.Read(cat))),
					Case(
						"a face above an insertion shifts its own index down",
						Cite(NerveFaceDegeneracyAbove.Read(cat))),
				))
		}),
})}

// NerveVertex — the vertices of the nerve are the constant identity
// chains at the objects. The end clause supplies the object, and padding
// makes every term its identity; conversely an identity is a morphism,
// and the constant chain satisfies the four clauses at length zero.
var NerveVertex = nerveVertexThm{family.Add(registry.ProofEntry{
	Name: "NerveVertex",
	Key:  "prop_abbb6dc41473bafb",
	Build: category.Category.Law("∀f:(num → M). "+
		"    f ∈ nerve_simplices(C, 0) ⇔ ∃x:A. x ∈ C.objects ∧ f = (λj:num. C.identity(x))",
		func(a *Argument, cat Fact, f Term) {
			a.Iff()
			a.Forward(
				"a chain of length zero is the constant identity at its end object",
				func(b *Argument, chain Fact) {
					clauses := b.Conjuncts(
						b.Have(
							"the chain ends at an object and stays at its 0-th term",
							"(∃x:A. x ∈ C.objects ∧ f(0) = C.identity(x)) ∧ (∀j:num. 0 < j ⇒ f(j) = f(0))",
							BySets(b.Simplified(chain, Fwd(NerveSimplicesDef)))),
						"its 0-th term is the identity at an object",
						"every later term equals its 0-th term")
					x, atZero := b.UnpackAs[A](clauses[0])
					stays := clauses[1]
					pointwise := b.Have(
						"every term is the identity at x",
						"∀j:num. f(j) = C.identity(x)",
						Derive(func(c *Argument) {
							j := c.FixAs[Nat]()
							c.Cases(c.Term("j = 0"))
							c.When(
								"at index zero the end clause gives the identity",
								func(d *Argument, zero Fact) {
									d.Show(
										"the term is the identity at x",
										By(Normalized, zero, atZero))
								})
							c.Otherwise(
								"a later term is padded with the same identity",
								func(d *Argument, notZero Fact) {
									positive := d.Have(
										"a nonzero natural index is positive",
										"0 < j",
										ByArith(notZero))
									d.Show(
										"padding gives the identity at x",
										By(Normalized, positive, atZero, stays.At(j)))
								})
						}))
					b.Take(x)
					b.Show(
						"x is the object and f is its constant identity chain",
						SplitConj(
							Case(
								"x is an object",
								By(atZero)),
							Case(
								"the chains agree at every index",
								By(Normalized, pointwise)),
						))
				})
			a.Backward(
				"the constant identity at an object is a chain of length zero",
				func(b *Argument, constant Fact) {
					x, data := b.UnpackAs[A](constant)
					parts := b.Conjuncts(
						data,
						"x is an object",
						"f is the constant identity at x")
					object, asConstant := parts[0], parts[1]
					identity := b.Have(
						"the identity at x is a morphism",
						"C.identity(x) ∈ C.morphisms",
						By(category.IdentityMorphism.Read(cat).At(proof.MemberOf(x, object))))
					terms := b.Have(
						"the term up to index zero is a morphism",
						"∀j:num. j ≤ 0 ⇒ f(j) ∈ C.morphisms",
						asConstant.Rw(),
						By(identity))
					composable := b.Have(
						"there is no composability condition below index zero",
						"∀j:num. j < 0 ⇒ C.target(f(j)) = C.source(f(j + 1))",
						ByArith())
					ending := b.Have(
						"the chain ends at x",
						"∃y:A. y ∈ C.objects ∧ f(0) = C.identity(y)",
						Witness(x),
						asConstant.Rw(),
						By(object))
					padded := b.Have(
						"the chain is constant from zero on",
						"∀j:num. 0 < j ⇒ f(j) = f(0)",
						asConstant.Rw(),
						Basic())
					b.Show(
						"the four clauses make f a chain of length zero",
						Simp(Fwd(NerveSimplicesDef)),
						BySets(terms, composable, ending, padded))
				})
		}),
})}

// NerveEdge — the edges of the nerve are the morphisms, each followed
// by the identity at its target. Composability identifies the end object
// of a chain with the target of its first morphism, and padding determines
// every later term; conversely a morphism and that identity form a chain.
var NerveEdge = nerveEdgeThm{family.Add(registry.ProofEntry{
	Name: "NerveEdge",
	Key:  "prop_973723bae308de2a",
	Build: category.Category.Law("∀f:(num → M). "+
		"    f ∈ nerve_simplices(C, 1) ⇔ "+
		"    ∃g:M. g ∈ C.morphisms ∧ f = (λj:num. COND(j = 0, g, C.identity(C.target(g))))",
		func(a *Argument, cat Fact, f Term) {
			a.Iff()
			a.Forward(
				"a chain of length one is its first morphism followed by the identity at its target",
				func(b *Argument, chain Fact) {
					clauses := b.Conjuncts(
						b.Have(
							"f read by the four clauses of a chain of length one",
							"(∀j:num. j ≤ 1 ⇒ f(j) ∈ C.morphisms) ∧ "+
								"(∀j:num. j < 1 ⇒ C.target(f(j)) = C.source(f(j + 1))) ∧ "+
								"(∃x:A. x ∈ C.objects ∧ f(1) = C.identity(x)) ∧ "+
								"(∀j:num. 1 < j ⇒ f(j) = f(1))",
							BySets(b.Simplified(chain, Fwd(NerveSimplicesDef)))),
						"its first two terms are morphisms",
						"the first morphism composes with the second",
						"the second term is the identity at an object",
						"every later term equals the second")
					mor, next, end, stays := clauses[0], clauses[1], clauses[2], clauses[3]
					x, endData := b.UnpackAs[A](end)
					parts := b.Conjuncts(
						endData,
						"x is an object",
						"f(1) is the identity at x")
					object, atOne := parts[0], parts[1]
					source := b.Have(
						"the source of the identity at x is x",
						"C.source(C.identity(x)) = x",
						By(category.IdentityMorphism.Read(cat).At(proof.MemberOf(x, object))))
					zero := b.TermAs[Nat]("0")
					endpoint := b.Have(
						"the end object is the target of the first morphism",
						"C.target(f(0)) = x",
						CalcEq(
							Leg(
								b.TermAs[A]("C.source(f(1))"),
								"the first morphism composes with f(1)",
								By(next.At(zero))),
							FinalLeg(
								"f(1) is the identity at x",
								Simp(Fwd(atOne), Fwd(source)),
								Basic()),
						))
					firstIn := b.Have(
						"the first term is a morphism",
						"f(0) ∈ C.morphisms",
						By(mor.At(zero)))
					pointwise := b.Have(
						"the first morphism and its target determine every term",
						"∀j:num. f(j) = COND(j = 0, f(0), C.identity(C.target(f(0))))",
						Derive(func(c *Argument) {
							j := c.FixAs[Nat]()
							notZero := c.Unless(
								c.Term("j = 0"),
								"at zero the term is f(0)",
								Given(func(d *Argument, atZero Fact) {
									d.Show(
										"the first terms agree",
										ByArith(atZero))
								}))
							notOne := c.Unless(
								c.Term("j = 1"),
								"at one the term is the identity at the target",
								Given(func(d *Argument, one Fact) {
									d.Show(
										"the end identities agree",
										ByArith(Normalized, one, endpoint, atOne))
								}))
							later := c.Have(
								"an index past zero and one is beyond the endpoint",
								"1 < j",
								ByArith(notZero, notOne))
							c.Show(
								"padding gives the identity at the target",
								By(Normalized, notZero, later, endpoint, atOne, stays.At(j)))
						}))
					b.Take(b.Term("f(0)"))
					b.Show(
						"f is the edge of its first morphism",
						SplitConj(
							Case(
								"the first term is a morphism",
								By(firstIn)),
							Case(
								"the chains agree at every index",
								By(pointwise)),
						))
				})
			a.Backward(
				"a morphism followed by the identity at its target is a chain of length one",
				func(b *Argument, edge Fact) {
					g, data := b.Unpack(edge)
					parts := b.Conjuncts(
						data,
						"g is a morphism",
						"f is g followed by the identity at its target")
					gIn, asEdge := parts[0], parts[1]
					target := b.TermAs[A]("C.target(g)")
					targetObject := b.Have(
						"the target of g is an object",
						"C.target(g) ∈ C.objects",
						By(gIn, category.MorphismEnds.Read(cat).AsFact().At(g)))
					identity := b.Conjuncts(
						b.Have(
							"the identity at the target is a morphism with that source and target",
							"C.identity(C.target(g)) ∈ C.morphisms ∧ "+
								"C.source(C.identity(C.target(g))) = C.target(g) ∧ "+
								"C.target(C.identity(C.target(g))) = C.target(g)",
							By(category.IdentityMorphism.Read(cat).At(proof.MemberOf(target, targetObject)))),
						"the identity at the target is a morphism",
						"its source is the target of g",
						"its target is the target of g")
					idIn, idSource := identity[0], identity[1]
					terms := b.Have(
						"both g and its constant tail are morphisms",
						"∀j:num. j ≤ 1 ⇒ f(j) ∈ C.morphisms",
						asEdge.Rw(),
						Derive(func(c *Argument) {
							c.FixAs[Nat]()
							c.Assume()
							c.Cases(c.Term("j = 0"))
							c.When(
								"at zero the morphism is g",
								func(d *Argument, atZero Fact) {
									d.Show(
										"g is a morphism",
										By(atZero, gIn))
								})
							c.Otherwise(
								"every later term is the identity at its target",
								func(d *Argument, notZero Fact) {
									d.Show(
										"the identity is a morphism",
										By(notZero, idIn))
								})
						}))
					composable := b.Have(
						"g composes with the identity at its target",
						"∀j:num. j < 1 ⇒ C.target(f(j)) = C.source(f(j + 1))",
						asEdge.Rw(),
						ByArith(idSource))
					ending := b.Have(
						"the chain ends at the target of g",
						"∃x:A. x ∈ C.objects ∧ f(1) = C.identity(x)",
						Witness(target),
						asEdge.Rw(),
						ByArith(targetObject))
					padded := b.Have(
						"the chain stays at its endpoint identity",
						"∀j:num. 1 < j ⇒ f(j) = f(1)",
						asEdge.Rw(),
						ByArith())
					b.Show(
						"the four clauses make f a chain of length one",
						Simp(Fwd(NerveSimplicesDef)),
						BySets(terms, composable, ending, padded))
				})
		}),
})}

// NerveFunctor — a functor induces a simplicial map of the nerves, the
// map of morphisms applied termwise.
var NerveFunctor = nerveFunctorThm{family.Add(registry.ProofEntry{
	Name: "NerveFunctor",
	Key:  "prop_c8f36c09c62fd4f8",
	Deps: []registry.EntryLike{
		simplicial_set.SimplicialMap,
		NerveSimplicialSet,
		NerveSimplicesDef,
		NerveFaceDef,
		NerveDegeneracyDef,
		category.FunctorDef,
		set_basic.Extension,
	},
	Build: family.Card(Statement{
		Binders: "∀C:category_ops(A, M). ∀D:category_ops(B, N). ∀F:functor_ops(A, M, B, N).",
		Hypotheses: []string{
			"functor(C, D, F)",
		},
		Conclusion: "simplicial_map(nerve(C), nerve(D), λn:num. λf:(num → M). λj:num. F.map(f(j)))",
	},
		"both nerves are simplicial sets (NerveSimplicialSet); the image of a chain "+
			"is a chain since the functor preserves morphisms, ends and identities; the "+
			"faces and degeneracies commute with the termwise map since it preserves "+
			"identities at sources and composites, by extensionality at every index"),
})}

// NerveSpine — the spine of a chain is the chain: its i-th spine edge
// is the edge of its i-th morphism.
var NerveSpine = nerveSpineThm{family.Add(registry.ProofEntry{
	Name: "NerveSpine",
	Key:  "prop_de8e1f8d729c26b2",
	Deps: []registry.EntryLike{
		simplicial_set.SimplexSpineDef,
		simplicial_set.FaceIterateTopDef,
		simplicial_set.FaceIterateBottomDef,
		NerveSimplicesDef,
		NerveFaceDef,
		NerveSimplicialSet,
		set_basic.Extension,
	},
	Build: family.Card(category.Category.Statement(Statement{
		Binders: "∀n i:num. ∀f:(num → M).",
		Hypotheses: []string{
			"f ∈ nerve_simplices(C, n)",
			"i < n",
		},
		Conclusion: "simplex_spine(nerve_face(C), n, f, i) = " +
			"λj:num. COND(j = 0, f(i), C.identity(C.target(f(i))))",
	}),
		"the top removals drop the last morphisms one at a time, re-padding at the source of the "+
			"dropped one, which is the target of the one before; the bottom removals drop the first "+
			"morphisms; what is left is f(i) followed by the identity at its target, by extensionality at j"),
})}

// NerveOuterFacesDetermine — a sequence is determined, at a length
// m ≥ 2, by its 0-th and last nerve faces: the 0-th face is the
// sequence one index up, and the last face begins with its first term.
var NerveOuterFacesDetermine = nerveOuterFacesDetermineThm{family.Add(registry.ProofEntry{
	Name: "NerveOuterFacesDetermine",
	Key:  "prop_9caa714715167797",
	Reading: "No chain condition is read, only the definition of the two faces; at m = 1 the " +
		"last face keeps the source of the first term and not the term, so the bound is needed.",
	Build: family.Theorem(Statement{
		Binders: "∀C:category_ops(A, M). ∀m:num. ∀g h:(num → M).",
		Hypotheses: []string{
			"2 ≤ m",
			"nerve_face(C, m, 0, g) = nerve_face(C, m, 0, h)",
			"nerve_face(C, m, m, g) = nerve_face(C, m, m, h)",
		},
		Conclusion: "g = h",
	},
		func(a *Argument, C Term, m *Expr[Nat], g, h Term, faces Fact) {
			parts := a.Conjuncts(
				faces,
				"m is at least 2",
				"g and h have one 0-th face",
				"and one last face")
			long, first, last := parts[0], parts[1], parts[2]
			a.Do(Funext())
			j := a.FixAs[Nat]("j")
			a.Cases(a.Term("j = 0"))
			a.When(
				"at 0 both begin their last faces",
				func(b *Argument, atZero Fact) {
					b.Show(
						"g(0) and h(0) are the last faces at 0, which agree",
						atZero.Rw(),
						CalcEq(
							Leg(
								b.Term("nerve_face(C, m, m, g, 0)"),
								"below its last index, 0 + 1 < m, the last face of g is g",
								Simp(Fwd(NerveFaceDef)),
								ByArith(long)),
							Leg(
								b.Term("nerve_face(C, m, m, h, 0)"),
								"which is the last face of h",
								By(Normalized, last)),
							FinalLeg(
								"and so h(0)",
								Simp(Fwd(NerveFaceDef)),
								ByArith(long)),
						))
				})
			a.Otherwise(
				"past 0 both are their 0-th faces one index down",
				func(b *Argument, notZero Fact) {
					_, jIs := b.ObtainAs[Nat](
						"j is p + 1 for some p",
						"∃p:num. j = p + 1",
						By(notZero, nat_arith.NonzeroIsSucc.At(j)))
					b.Show(
						"g(p + 1) and h(p + 1) are the 0-th faces at p, which agree",
						jIs.Rw(),
						CalcEq(
							Leg(
								b.Term("nerve_face(C, m, 0, g, p)"),
								"the 0-th face of g is g one index up",
								Simp(Fwd(NerveFaceDef)),
								Basic()),
							Leg(
								b.Term("nerve_face(C, m, 0, h, p)"),
								"which is the 0-th face of h",
								By(Normalized, first)),
							FinalLeg(
								"and so h one index up",
								Simp(Fwd(NerveFaceDef)),
								Basic()),
						))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Unique inner fillers
// ---------------------------------------------------------------------------

// InnerHornUnique — `inner_horn_unique(X)`: a simplicial set in
// which every inner horn, 0 < k < n + 1, has exactly one filler.
var InnerHornUnique = innerHornUniqueThm{family.DefineStructure(registry.DefEntry{
	Name:    "InnerHornUnique",
	Key:     "prop_d2cbc8b13caf2fdf",
	Const:   "inner_horn_unique",
	Type:    "simplicial_ops(A) → bool",
	Subject: "X",
	Equations: []string{
		"∀X:simplicial_ops(A). " +
			"    inner_horn_unique(X) ⇔ " +
			"    simplicial_set(X) ∧ " +
			"    (∀n k:num. ∀y:(num → A). " +
			"        0 < k ∧ k ≤ n ∧ face_family(X, n, horn_faces(n, k), y) ⇒ " +
			"        ∃x:A. " +
			"            x ∈ X.simplices(n + 1) ∧ " +
			"            faces_filler(X.d, n, horn_faces(n, k), y, x) ∧ " +
			"            (∀x':A. " +
			"                x' ∈ X.simplices(n + 1) ∧ faces_filler(X.d, n, horn_faces(n, k), y, x') ⇒ " +
			"                x' = x))",
	},
	Reading: "The inner horns are those of dimension n + 1 ≥ 2 with 0 " +
		"< k ≤ n; the outer horns k = 0 and k = n + 1 are not asked, which " +
		"is what admits the nerves of categories that are not groupoids.",
})}

// UniqueInnerSimplicialSet — a simplicial set with unique inner fillers
// is a simplicial set.
var UniqueInnerSimplicialSet = uniqueInnerSimplicialSetThm{family.Add(registry.ProofEntry{
	Name:  "UniqueInnerSimplicialSet",
	Key:   "prop_6be96f6011eaf98a",
	Build: InnerHornUnique.Axiom("simplicial_set(X)"),
})}

// UniqueInnerFill — every inner horn has exactly one filler.
var UniqueInnerFill = uniqueInnerFillThm{family.Add(registry.ProofEntry{
	Name: "UniqueInnerFill",
	Key:  "prop_1d04c19439462568",
	Build: InnerHornUnique.Axiom(Statement{
		Binders: "∀n k:num. ∀y:(num → A).",
		Hypotheses: []string{
			"0 < k",
			"k ≤ n",
			"face_family(X, n, horn_faces(n, k), y)",
		},
		Conclusion: "∃x:A. " +
			"    x ∈ X.simplices(n + 1) ∧ " +
			"    faces_filler(n, horn_faces(n, k), y, x) ∧ " +
			"    (∀x':A. x' ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, k), y, x') ⇒ x' = x)",
	}),
})}

// NerveInnerHornUnique — the nerve of a category has unique inner
// fillers. A chain of length m ≥ 2 is determined by its 0-th and last
// faces (NerveOuterFacesDetermine), and an inner horn y in dimension
// n + 1 has both of those faces, so it has at most one filler. The chain
// w that begins with the first morphism of y(n + 1) and goes on as y(0)
// is one. Compatibility at the pair (0, n + 1) says that y(n + 1) one
// index up is the last face of y(0): so the first morphism of y(n + 1)
// composes with the first of y(0), which makes w a chain, and the last
// face of w is y(n + 1). At the pairs (0, i) and (i, n + 1) the face
// identities and compatibility give an inner face of w the two outer
// faces of y(i), so the two agree.
var NerveInnerHornUnique = nerveInnerHornUniqueThm{family.Add(registry.ProofEntry{
	Name: "NerveInnerHornUnique",
	Key:  "prop_70d6ac728e039ff2",
	Build: category.Category.Law("inner_horn_unique(nerve(C))",
		func(a *Argument, cat Fact) {
			a.Do(Simp(Fwd(InnerHornUnique)), SplitConj(
				Case(
					"the nerve is a simplicial set",
					By(cat, NerveSimplicialSet)),
				Case(
					"every inner horn has exactly one filler",
					Derive(func(b *Argument) {
						shift := b.Have(
							"the 0-th face of a chain is the chain one index up",
							"∀m:num. ∀g:(num → M). ∀q:num. nerve_face(C, m, 0, g, q) = g(q + 1)",
							Simp(Fwd(NerveFaceDef)),
							Basic())
						below := b.Have(
							"below its last index the last face of a chain is the chain",
							"∀m:num. ∀g:(num → M). ∀q:num. q + 1 < m ⇒ nerve_face(C, m, m, g, q) = g(q)",
							Derive(func(c *Argument) {
								c.FixAs[Nat]()
								c.Fix()
								c.FixAs[Nat]()
								inside := c.Assume()
								c.Show(
									"q + 1 being below m, the definition keeps g(q)",
									Simp(Fwd(NerveFaceDef)),
									ByArith(inside))
							}))
						padding := b.Have(
							"from the last index on, the last face of a chain of "+
								"m + 1 morphisms is the identity at the source of g(m)",
							Statement{
								Binders: "∀m:num. ∀g:(num → M). ∀q:num.",
								Hypotheses: []string{
									"m ≤ q",
								},
								Conclusion: "nerve_face(C, m + 1, m + 1, g, q) = C.identity(C.source(g(m)))",
							},
							Derive(func(c *Argument) {
								c.FixAs[Nat]()
								c.Fix()
								c.FixAs[Nat]()
								outside := c.Assume()
								c.Show(
									"from m on, the definition pads with the identity at the source of g(m)",
									Simp(Fwd(NerveFaceDef), Fwd(nat_monus.AddSubCancel)),
									ByArith(outside))
							}))
						n, k := b.FixAs[Nat](), b.FixAs[Nat]()
						y := b.Fix()
						given := b.Conjuncts(
							b.Assume(),
							"k is positive",
							"k is at most n",
							"and y is a family of chains of n morphisms on the faces of the horn")
						kPos, kUpTo, horn := given[0], given[1], given[2]
						faces := b.Conjuncts(
							b.Unfolded(horn, simplicial_set.FaceFamilyDef),
							"the members of y are chains of n morphisms",
							"and they are compatible")
						members, compat := faces[0], b.Simplified(faces[1], Fwd(simplicial_set.FacesCompatibleDef))
						zero, top := b.TermAs[Nat]("0"), b.TermAs[Nat]("n + 1")
						yZero, yTop := y.Apply(zero), y.Apply(top)
						zeroIndex := b.Have(
							"0 is a face of the horn, k being positive",
							"0 ∈ horn_faces(n, k)",
							ByArith(kan_complex.HornFacesMember.At(n, k, zero), kPos))
						topIndex := b.Have(
							"and so is n + 1, k being at most n",
							"n + 1 ∈ horn_faces(n, k)",
							ByArith(kan_complex.HornFacesMember.At(n, k, top), kUpTo))
						nonzero := b.Have(
							"n is not 0, as 0 < k ≤ n",
							"¬(n = 0)",
							ByArith(kPos, kUpTo))
						r, nIs := b.ObtainAs[Nat](
							"n is r + 1 for some r",
							"∃r:num. n = r + 1",
							By(nonzero, nat_arith.NonzeroIsSucc.At(n)))
						cancel := b.Have(
							"n + 1 − 1 is n",
							"n + 1 - 1 = n",
							ByArith())

						zeroIn := b.Have(
							"y(0) is a chain of n morphisms",
							"y(0) ∈ nerve_simplices(C, n)",
							By(members.At(zero), zeroIndex))
						topIn := b.Have(
							"and so is y(n + 1)",
							"y(n + 1) ∈ nerve_simplices(C, n)",
							By(members.At(top), topIndex))
						bottom := b.Conjuncts(
							b.Have(
								"y(0) read by the definition of the nerve",
								"(∀q:num. q ≤ n ⇒ y(0, q) ∈ C.morphisms) ∧ "+
									"(∀q:num. q < n ⇒ C.target(y(0, q)) = C.source(y(0, q + 1))) ∧ "+
									"(∃x:A. x ∈ C.objects ∧ y(0, n) = C.identity(x)) ∧ "+
									"(∀q:num. n < q ⇒ y(0, q) = y(0, n))",
								BySets(b.Simplified(zeroIn, Fwd(NerveSimplicesDef)))),
							"the terms of y(0) up to n are morphisms",
							"each composes with the next",
							"its n-th term is the identity at an object",
							"and it is constant from n on")
						mor, next, end, stays := bottom[0], bottom[1], bottom[2], bottom[3]
						upper := b.Conjuncts(
							b.Have(
								"y(n + 1) read by the definition of the nerve, in its first two clauses",
								"(∀q:num. q ≤ n ⇒ y(n + 1, q) ∈ C.morphisms) ∧ "+
									"(∀q:num. q < n ⇒ C.target(y(n + 1, q)) = C.source(y(n + 1, q + 1)))",
								BySets(b.Simplified(topIn, Fwd(NerveSimplicesDef)))),
							"the terms of y(n + 1) up to n are morphisms",
							"each composes with the next")
						morTop, nextTop := upper[0], upper[1]

						outer := b.Have(
							"compatibility at the pair (0, n + 1): the 0-th face of y(n + 1) is the last face of y(0)",
							"nerve_face(C, n, 0, y(n + 1)) = nerve_face(C, n, n, y(0))",
							ByArith(zeroIndex, topIndex, cancel, compat.At(zero, top)))
						down := b.Have(
							"so y(n + 1) one index up is the last face of y(0)",
							"∀q:num. y(n + 1, q + 1) = nerve_face(C, n, n, y(0), q)",
							Derive(func(c *Argument) {
								q := c.FixAs[Nat]()
								c.Show(
									"the 0-th face of y(n + 1) at q",
									By(outer, shift.At(n, yTop, q)))
							}))
						junction := b.Have(
							"the first morphism of y(n + 1) composes with the first of y(0)",
							"C.target(y(n + 1, 0)) = C.source(y(0, 0))",
							Derive(func(c *Argument) {
								step := c.Have(
									"the first morphism of y(n + 1) composes with its second term",
									"C.target(y(n + 1, 0)) = C.source(y(n + 1, 1))",
									ByArith(kPos, kUpTo, nextTop.At(zero)))
								second := c.Have(
									"which is the last face of y(0) at 0",
									"y(n + 1, 1) = nerve_face(C, n, n, y(0), 0)",
									By(down.At(zero)))
								c.Cases(c.Term("1 < n"))
								c.When(
									"for n ≥ 2 that is the first term of y(0)",
									func(d *Argument, long Fact) {
										d.Show(
											"the source of y(0, 0)",
											ByArith(long, step, second, below.At(n, yZero, zero)))
									})
								c.Otherwise(
									"for n = 1 it is the identity at the source of y(0, 0)",
									func(d *Argument, short Fact) {
										single := d.Have(
											"n is 1",
											"n = 1",
											ByArith(short, kPos, kUpTo))
										padded := d.Have(
											"the last face of a chain of one morphism is the identity at its source",
											"nerve_face(C, n, n, y(0), 0) = C.identity(C.source(y(0, 0)))",
											single.Rw(),
											By(padding.At(zero, yZero, zero)))
										object := d.Have(
											"the source of y(0, 0) is an object",
											"C.source(y(0, 0)) ∈ C.objects",
											ByArith(mor.At(zero), At(category.MorphismEnds.Read(cat), yZero.Apply(zero))))
										identity := d.Have(
											"the identity at it has it for its source",
											"C.source(C.identity(C.source(y(0, 0)))) = C.source(y(0, 0))",
											By(object, At(category.IdentityMorphism.Read(cat), d.Term("C.source(y(0, 0))"))))
										d.Show(
											"the source of the identity at C.source(y(0, 0))",
											By(step, second, padded, identity))
									})
							}))

						wDef := b.Let("w", b.Term("λj:num. COND(j = 0, y(n + 1, 0), y(0, j - 1))"))
						w := b.Term("w")
						starts := b.Have(
							"w begins with the first morphism of y(n + 1)",
							"w(0) = y(n + 1, 0)",
							wDef.Rw(),
							Basic())
						continues := b.Have(
							"and goes on as y(0)",
							"∀q:num. w(q + 1) = y(0, q)",
							Derive(func(c *Argument) {
								c.FixAs[Nat]()
								c.Show(
									"past 0 the term of w is the one before it in y(0)",
									wDef.Rw(),
									Simp(Fwd(nat_monus.AddSubCancel)),
									ByArith())
							}))
						wEnd := b.Have(
							"so w(n) is y(0, r), the last morphism of y(0)",
							"w(n) = y(0, r)",
							nIs.Rw(),
							By(continues.At(r)))

						terms := b.Have(
							"the terms of w up to n + 1 are morphisms",
							"∀i:num. i ≤ n + 1 ⇒ w(i) ∈ C.morphisms",
							Derive(func(c *Argument) {
								i := c.FixAs[Nat]()
								upTo := c.Assume()
								c.Cases(c.Term("i = 0"))
								c.When(
									"w(0) is the first morphism of y(n + 1)",
									func(d *Argument, atZero Fact) {
										d.Show(
											"a term of y(n + 1)",
											atZero.Rw(),
											ByArith(starts, morTop.At(zero)))
									})
								c.Otherwise(
									"past 0 it is a term of y(0)",
									func(d *Argument, notZero Fact) {
										p, iIs := d.ObtainAs[Nat](
											"i is p + 1 for some p",
											"∃p:num. i = p + 1",
											By(notZero, nat_arith.NonzeroIsSucc.At(i)))
										d.Show(
											"w(p + 1) is y(0, p), p being at most n",
											ByArith(upTo, iIs, continues.At(p), mor.At(p)))
									})
							}))
						composable := b.Have(
							"each term of w composes with the next",
							"∀i:num. i < n + 1 ⇒ C.target(w(i)) = C.source(w(i + 1))",
							Derive(func(c *Argument) {
								i := c.FixAs[Nat]()
								inside := c.Assume()
								c.Cases(c.Term("i = 0"))
								c.When(
									"at 0 the first morphism of y(n + 1) meets the first of y(0)",
									func(d *Argument, atZero Fact) {
										d.Show(
											"w(0) and w(1) are y(n + 1, 0) and y(0, 0)",
											atZero.Rw(),
											ByArith(starts, continues.At(zero), junction))
									})
								c.Otherwise(
									"past 0 two neighbours in y(0) meet",
									func(d *Argument, notZero Fact) {
										p, iIs := d.ObtainAs[Nat](
											"i is p + 1 for some p",
											"∃p:num. i = p + 1",
											By(notZero, nat_arith.NonzeroIsSucc.At(i)))
										d.Show(
											"w(p + 1) and w(p + 2) are y(0, p) and y(0, p + 1)",
											ByArith(inside, iIs, continues.At(p), continues.At(d.TermAs[Nat]("p + 1")), next.At(p)))
									})
							}))
						ending := b.Have(
							"the (n + 1)-th term of w is y(0, n), the identity at an object",
							"∃x:A. x ∈ C.objects ∧ w(n + 1) = C.identity(x)",
							By(Normalized, end, continues.At(n)))
						constant := b.Have(
							"w is constant from n + 1 on, as y(0) is from n",
							"∀i:num. n + 1 < i ⇒ w(i) = w(n + 1)",
							Derive(func(c *Argument) {
								i := c.FixAs[Nat]()
								past := c.Assume()
								notZero := c.Have(
									"i is not 0",
									"¬(i = 0)",
									ByArith(past))
								p, iIs := c.ObtainAs[Nat](
									"i is p + 1 for some p",
									"∃p:num. i = p + 1",
									By(notZero, nat_arith.NonzeroIsSucc.At(i)))
								c.Show(
									"w(p + 1) is y(0, p), which is y(0, n) past n",
									ByArith(past, iIs, continues.At(p), continues.At(n), stays.At(p)))
							}))
						inNerve := b.Have(
							"so w is a chain of n + 1 morphisms",
							"w ∈ nerve_simplices(C, n + 1)",
							Simp(Fwd(NerveSimplicesDef)),
							BySets(terms, composable, ending, constant))

						zeroFace := b.Have(
							"the 0-th face of w is y(0)",
							"nerve_face(C, n + 1, 0, w) = y(0)",
							Derive(func(c *Argument) {
								c.Do(Funext())
								q := c.FixAs[Nat]("q")
								c.Show(
									"w one index up is y(0)",
									By(shift.At(top, w, q), continues.At(q)))
							}))
						topFace := b.Have(
							"the last face of w is y(n + 1)",
							"nerve_face(C, n + 1, n + 1, w) = y(n + 1)",
							Derive(func(c *Argument) {
								c.Do(Funext())
								q := c.FixAs[Nat]("q")
								c.Cases(c.Term("q = 0"))
								c.When(
									"both begin with the first morphism of y(n + 1)",
									func(d *Argument, atZero Fact) {
										d.Show(
											"the last face of w begins with w(0)",
											atZero.Rw(),
											ByArith(kPos, kUpTo, starts, below.At(top, w, zero)))
									})
								c.Otherwise(
									"past 0, y(n + 1) is the last face of y(0) one index down",
									func(d *Argument, notZero Fact) {
										p, qIs := d.ObtainAs[Nat](
											"q is p + 1 for some p",
											"∃p:num. q = p + 1",
											By(notZero, nat_arith.NonzeroIsSucc.At(q)))
										d.Do(qIs.Rw())
										pNext := d.TermAs[Nat]("p + 1")
										d.Cases(d.Term("p + 1 < n"))
										d.When(
											"below n both are y(0, p)",
											func(e *Argument, inside Fact) {
												e.Show(
													"w(p + 1) is y(0, p), and so is the last face of y(0) at p",
													ByArith(inside, down.At(p), continues.At(p), below.At(top, w, pNext), below.At(n, yZero, p)))
											})
										d.Otherwise(
											"from n on both are the identity at the source of y(0, r)",
											func(e *Argument, outside Fact) {
												wPad := e.Have(
													"the last face of w pads there with the identity at the source of w(n)",
													"nerve_face(C, n + 1, n + 1, w, p + 1) = C.identity(C.source(w(n)))",
													ByArith(outside, padding.At(n, w, pNext)))
												yPad := e.Have(
													"and the last face of y(0) with the identity at the source of y(0, r)",
													"nerve_face(C, n, n, y(0), p) = C.identity(C.source(y(0, r)))",
													ByArith(outside, nIs, padding.At(r, yZero, p)))
												e.Show(
													"w(n) being y(0, r), the two agree",
													By(wPad, yPad, down.At(p), wEnd))
											})
									})
							}))

						fills := b.Have(
							"w fills the horn: its faces other than the k-th are the members of y",
							"faces_filler(nerve_face(C), n, horn_faces(n, k), y, w)",
							Simp(Fwd(simplicial_set.FacesFillerDef)),
							Derive(func(c *Argument) {
								i := c.FixAs[Nat]()
								index := c.Assume()
								face := c.Have(
									"a face of the horn is at most n + 1 and other than k",
									"i ≤ n + 1 ∧ ¬(i = k)",
									By(kan_complex.HornFacesMember.At(n, k, i), index))
								c.Cases(c.Term("i = 0"))
								c.When(
									"the 0-th face is y(0)",
									func(d *Argument, atZero Fact) {
										d.Show(
											"as w goes on as y(0)",
											atZero.Rw(),
											By(zeroFace))
									})
								c.Otherwise(
									"a face past the 0-th",
									func(d *Argument, notZero Fact) {
										d.Cases(d.Term("i = n + 1"))
										d.When(
											"the last face is y(n + 1)",
											func(e *Argument, atTop Fact) {
												e.Show(
													"by compatibility at (0, n + 1)",
													atTop.Rw(),
													By(topFace))
											})
										d.Otherwise(
											"an inner face of w has the two outer faces of y(i)",
											func(e *Argument, notTop Fact) {
												long := e.Have(
													"i and k are two inner indices, so n is at least 2",
													"2 ≤ n",
													ByArith(face, notZero, notTop, kPos, kUpTo))
												lift := e.Have(
													"the chains of n + 1 morphisms are those of r + 2",
													"r + 2 = n + 1",
													ByArith(nIs))
												bottomFaces := e.Have(
													"the 0-th faces agree, both the face i − 1 of y(0)",
													"nerve_face(C, n, 0, nerve_face(C, n + 1, i, w)) = nerve_face(C, n, 0, y(i))",
													CalcEq(
														Leg(
															e.Term("nerve_face(C, n, i - 1, nerve_face(C, n + 1, 0, w))"),
															"the face identity at the pair (0, i) on w",
															ByArith(face, notZero, nIs, lift, inNerve, At(NerveFaceFace.Read(cat), r, zero, i, w))),
														Leg(
															e.Term("nerve_face(C, n, i - 1, y(0))"),
															"the 0-th face of w is y(0)",
															zeroFace.Rw(),
															Basic()),
														FinalLeg(
															"compatibility at the pair (0, i)",
															ByArith(face, notZero, zeroIndex, index, compat.At(zero, i))),
													))
												topFaces := e.Have(
													"and so do the last faces, both the face i of y(n + 1)",
													"nerve_face(C, n, n, nerve_face(C, n + 1, i, w)) = nerve_face(C, n, n, y(i))",
													CalcEq(
														Leg(
															e.Term("nerve_face(C, n, i, nerve_face(C, n + 1, n + 1, w))"),
															"the face identity at the pair (i, n + 1) on w",
															ByArith(face, notTop, nIs, lift, cancel, inNerve, At(NerveFaceFace.Read(cat), r, i, top, w))),
														Leg(
															e.Term("nerve_face(C, n, i, y(n + 1))"),
															"the last face of w is y(n + 1)",
															topFace.Rw(),
															Basic()),
														FinalLeg(
															"compatibility at the pair (i, n + 1)",
															ByArith(face, notTop, index, topIndex, cancel, compat.At(i, top))),
													))
												e.Show(
													"so the face is y(i), two chains of length n ≥ 2 with the same outer faces",
													By(NerveOuterFacesDetermine, long, bottomFaces, topFaces))
											})
									})
							}))
						unique := b.Have(
							"a filler has the 0-th face y(0) and the last face y(n + 1), so it is w",
							Statement{
								Binders: "∀x':(num → M).",
								Hypotheses: []string{
									"x' ∈ nerve_simplices(C, n + 1)",
									"faces_filler(nerve_face(C), n, horn_faces(n, k), y, x')",
								},
								Conclusion: "x' = w",
							},
							Derive(func(c *Argument) {
								c.Fix()
								parts := c.Conjuncts(
									c.Assume(),
									"x' is a chain of n + 1 morphisms",
									"which fills the horn")
								filler := c.Simplified(parts[1], Fwd(simplicial_set.FacesFillerDef))
								otherZero := c.Have(
									"its 0-th face is y(0)",
									"nerve_face(C, n + 1, 0, x') = y(0)",
									By(filler.At(zero), zeroIndex))
								otherTop := c.Have(
									"its last face is y(n + 1)",
									"nerve_face(C, n + 1, n + 1, x') = y(n + 1)",
									By(filler.At(top), topIndex))
								sameZero := c.Have(
									"as is that of w",
									"nerve_face(C, n + 1, 0, x') = nerve_face(C, n + 1, 0, w)",
									zeroFace.Rw(),
									By(otherZero))
								sameTop := c.Have(
									"as is that of w",
									"nerve_face(C, n + 1, n + 1, x') = nerve_face(C, n + 1, n + 1, w)",
									topFace.Rw(),
									By(otherTop))
								longer := c.Have(
									"x' and w have length n + 1, at least 2",
									"2 ≤ n + 1",
									ByArith(kPos, kUpTo))
								c.Show(
									"so x' is w",
									By(NerveOuterFacesDetermine, longer, sameZero, sameTop))
							}))

						b.Take(w)
						b.Show(
							"w is a filler, and the only one",
							By(inNerve, fills, unique))
					})),
			))
		}),
})}
