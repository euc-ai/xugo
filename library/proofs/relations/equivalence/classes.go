// classes.go — what an equivalence does to the set it lives on: the
// class of a point, the class inside a set and what the axioms make of
// it — two classes are equal or disjoint, two points share one exactly
// when they are related — the same laws on the whole type, read off the
// set's at 𝕌, the correspondence with partitions in both directions, how
// the classes count a set they cover, and the value of a map that
// respects the relation on a class.

package equivalence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The class of a point
// ---------------------------------------------------------------------------

// InClass — the class of x is the set of points x is related to, so
// lying in it is being related to by x: the definition unfolded and
// membership in the comprehension read off. This is the interface every
// later law reads a class through; the relation is any relation, the
// axioms enter only downstream.
var InClass = inClassThm{family.Add(registry.ProofEntry{
	Name: "InClass",
	Key:  "prop_74e6fab8353702b8",
	Build: family.Theorem("∀R:(A → A → bool). ∀x y:A. y ∈ equivalence_class(R, x) ⇔ R(x, y)",
		func(a *Argument, R *Arrow2[A, A, Bool], x, y *Expr[A]) {
			a.Show(
				"a point of the comprehension is one x is related to, and conversely",
				Unfold(EquivalenceClassDef),
				BySets())
		}),
})}

// ChosenRepresentative — where x is related to itself, x is related to
// the point chosen in its class: x then lies in its class (InClass), so
// the class is inhabited and the point chosen in it lies in it, which
// InClass reads back. Only reflexivity at x is asked, so the relation is
// any relation.
var ChosenRepresentative = chosenRepresentativeThm{family.Add(registry.ProofEntry{
	Name: "ChosenRepresentative",
	Key:  "prop_733429ec5b9931cb",
	Build: family.Theorem(Statement{
		Binders: "∀R:(A → A → bool). ∀x:A.",
		Hypotheses: []string{
			"R(x, x)",
		},
		Conclusion: "R(x, εy:A. y ∈ equivalence_class(R, x))",
	},
		func(a *Argument, R *Arrow2[A, A, Bool], x *Expr[A], reflexive Fact) {
			_, chosen := a.ObtainChosen(
				"x is related to itself, so it lies in its class: the "+
					"class is inhabited, and the point chosen in it lies in it",
				"∃y:A. y ∈ equivalence_class(R, x)",
				InClass,
				reflexive)
			a.Show(
				"a point of the class of x is one x is related to",
				By(InClass, chosen))
		}),
})}

// ---------------------------------------------------------------------------
// The class inside a set
// ---------------------------------------------------------------------------
//
// The quotient of a set c is made of the classes of the relation
// restricted to c. Read through the restriction, a class inside c is the
// points of c its point is related to; it lies in c, and where c is
// closed under the relation it is the class itself. Under
// equivalence_on(c, R) the laws of the classes hold at the points of c,
// whatever R does elsewhere.

// InClassOn — a point lies in the class of x inside c exactly when both
// lie in c and x is related to it.
var InClassOn = inClassOnThm{family.Add(registry.ProofEntry{
	Name: "InClassOn",
	Key:  "prop_f46f2898d8351efa",
	Build: family.Theorem("∀c:set(A). ∀R:(A → A → bool). ∀x y:A. "+
		"    y ∈ equivalence_class(relation_on(c, R), x) ⇔ x ∈ c ∧ y ∈ c ∧ R(x, y)",
		func(a *Argument, c *Expr[Set[A]], R *Arrow2[A, A, Bool], x, y *Expr[A]) {
			a.Show(
				"lying in the class is being related to by x under the restriction, which asks both points in c",
				By(InClass, RelationOnDef))
		}),
})}

// ClassOnSubset — a class inside c lies in c.
var ClassOnSubset = classOnSubsetThm{family.Add(registry.ProofEntry{
	Name: "ClassOnSubset",
	Key:  "prop_e07739510a3aeda0",
	Build: family.Theorem("∀c:set(A). ∀R:(A → A → bool). ∀x:A. "+
		"    equivalence_class(relation_on(c, R), x) ⊆ c",
		func(a *Argument, c *Expr[Set[A]], R *Arrow2[A, A, Bool], x *Expr[A]) {
			a.Show(
				"a member of the class inside c is a point of c",
				Unfold(set_basic.SubsetDef),
				By(InClassOn))
		}),
})}

// ClassOnClosed — where every point x is related to lies in c, the
// class of x inside c is its class: the restriction asks nothing the
// relation does not already give.
var ClassOnClosed = classOnClosedThm{family.Add(registry.ProofEntry{
	Name: "ClassOnClosed",
	Key:  "prop_ba6f63dc9f36aed",
	Build: family.Theorem(Statement{
		Binders: "∀c:set(A). ∀R:(A → A → bool). ∀x:A.",
		Hypotheses: []string{
			"x ∈ c",
			"∀y:A. R(x, y) ⇒ y ∈ c",
		},
		Conclusion: "equivalence_class(relation_on(c, R), x) = equivalence_class(R, x)",
	},
		func(a *Argument, c *Expr[Set[A]], R *Arrow2[A, A, Bool], x *Expr[A], given Fact) {
			a.Show(
				"sets with the same members are equal: a point x is related to lies in c already",
				Simp(Fwd(set_basic.Extension), Fwd(InClassOn), Fwd(InClass)),
				By(given))
		}),
})}

// ClassOwnOn — a point of c lies in its own class inside c.
var ClassOwnOn = classOwnOnThm{family.Add(registry.ProofEntry{
	Name: "ClassOwnOn",
	Key:  "prop_71b37161330cc2a2",
	Build: EquivalenceOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ c",
		},
		Conclusion: "x ∈ equivalence_class(relation_on(c, R), x)",
	},
		func(
			a *Argument,
			c *Expr[Set[A]],
			R *Arrow2[A, A, Bool],
			equiv EquivalenceFact[on.C],
			x *Member[A, on.C],
		) {
			a.Show(
				"x lies in c and is related to itself",
				By(InClassOn, ReflexiveOn, equiv, x))
		}),
})}

// ClassOnEqIff — two points of c have one class inside c exactly when
// they are related. Forwards, y lies in its own class, which the equation
// makes the class of x; backwards, what x and y are related to in c
// agree, by symmetry and transitivity, and extensionality carries it.
var ClassOnEqIff = classOnEqIffThm{family.Add(registry.ProofEntry{
	Name: "ClassOnEqIff",
	Key:  "prop_3b9b7cffc790b637",
	Build: EquivalenceOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ c",
			"y ∈ c",
		},
		Conclusion: "equivalence_class(relation_on(c, R), x) = equivalence_class(relation_on(c, R), y) ⇔ " +
			"R(x, y)",
	},
		func(
			a *Argument,
			c *Expr[Set[A]],
			R *Arrow2[A, A, Bool],
			equiv EquivalenceFact[on.C],
			x, y *Member[A, on.C],
		) {
			a.Iff()
			a.Forward(
				"y lies in its own class, which the equation makes the class of x",
				func(b *Argument, eq Fact) {
					own := b.Have(
						"y lies in the class of x",
						"y ∈ equivalence_class(relation_on(c, R), x)",
						eq.Rw(),
						By(ClassOwnOn, equiv, y))
					b.Show(
						"lying in the class of x inside c is being related to by x",
						By(own, InClassOn))
				})
			a.Backward(
				"the two classes have the same members, since what x and y are related to in c agree",
				func(b *Argument, rel Fact) {
					back := b.Have(
						"y is related to x, by symmetry",
						"R(y, x)",
						By(rel, SymmetricOn.At(c, R, x, y), equiv, x, y))
					fromX := b.Have(
						"what x is related to in c, y is related to: y to x, then on by transitivity",
						"∀z:A. z ∈ c ∧ R(x, z) ⇒ R(y, z)",
						By(back, TransitiveOn, equiv, x, y))
					fromY := b.Have(
						"what y is related to in c, x is related to: x to y, then on by transitivity",
						"∀z:A. z ∈ c ∧ R(y, z) ⇒ R(x, z)",
						By(rel, TransitiveOn, equiv, x, y))
					b.Show(
						"sets with the same members are equal, and a member of "+
							"a class inside c is a point of c its point is related to",
						Simp(Fwd(set_basic.Extension), Fwd(InClassOn)),
						b.ForEach(func(z *Expr[A]) Action {
							return By(Normalized, x, y, fromX.At(z), fromY.At(z))
						}))
				})
		}),
})}

// ClassOnDisjointOrEqual — two classes inside c of points of c are
// equal or disjoint. Related points have equal classes (ClassOnEqIff);
// a point of both classes of unrelated ones would relate x to y through
// itself, by symmetry then transitivity.
var ClassOnDisjointOrEqual = classOnDisjointOrEqualThm{family.Add(registry.ProofEntry{
	Name: "ClassOnDisjointOrEqual",
	Key:  "prop_967780a9572652d4",
	Build: EquivalenceOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ c",
			"y ∈ c",
		},
		Conclusion: "equivalence_class(relation_on(c, R), x) = equivalence_class(relation_on(c, R), y) ∨ " +
			"disjoint(equivalence_class(relation_on(c, R), x), equivalence_class(relation_on(c, R), y))",
	},
		func(
			a *Argument,
			c *Expr[Set[A]],
			R *Arrow2[A, A, Bool],
			equiv EquivalenceFact[on.C],
			x, y *Member[A, on.C],
		) {
			apart := a.Have(
				"unrelated points have disjoint classes",
				Statement{
					Hypotheses: []string{
						"¬R(x, y)",
					},
					Conclusion: "disjoint(equivalence_class(relation_on(c, R), x), " +
						"    equivalence_class(relation_on(c, R), y))",
				},
				Derive(func(b *Argument) {
					unrelated := b.Assume()
					b.Show(
						"a point of both classes is a point of c related to by x "+
							"and by y, so symmetry and transitivity would relate x to y",
						Simp(Fwd(set_algebra.InDisjoint), Fwd(InClassOn)),
						b.ForEach(func(z *Expr[A]) Action {
							return By(unrelated, SymmetricOn.At(c, R, y, z), TransitiveOn.At(c, R, x, z, y), equiv, x, y)
						}))
				}))
			a.Show(
				"the classes are equal when x and y are related, and disjoint when they are not",
				By(Normalized, ClassOnEqIff.At(c, R, x, y), apart, equiv, x, y))
		}),
})}

// ClassEqIffClosed — when c is closed under the relation, two points of c
// have one class exactly when they are related: the class of a point of
// c is its class inside c (ClassOnClosed), and ClassOnEqIff compares
// those. This is the form a quotient built by a chapter reads, its
// classes being classes of the relation itself.
var ClassEqIffClosed = classEqIffClosedThm{family.Add(registry.ProofEntry{
	Name: "ClassEqIffClosed",
	Key:  "prop_f4c45e36d451df0d",
	Build: EquivalenceOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ c",
			"y ∈ c",
			"∀u v:A. u ∈ c ∧ R(u, v) ⇒ v ∈ c",
		},
		Conclusion: "equivalence_class(R, x) = equivalence_class(R, y) ⇔ R(x, y)",
	},
		func(
			a *Argument,
			c *Expr[Set[A]],
			R *Arrow2[A, A, Bool],
			equiv EquivalenceFact[on.C],
			x, y *Member[A, on.C],
			closed Fact,
		) {
			classX := a.Have(
				"the class of x inside c is its class, c being closed under R",
				"equivalence_class(relation_on(c, R), x) = equivalence_class(R, x)",
				By(closed, x, ClassOnClosed.At(c, R, x)))
			classY := a.Have(
				"and so is the class of y",
				"equivalence_class(relation_on(c, R), y) = equivalence_class(R, y)",
				By(closed, y, ClassOnClosed.At(c, R, y)))
			inside := a.Have(
				"the classes inside c are equal exactly when x and y are related",
				"equivalence_class(relation_on(c, R), x) = equivalence_class(relation_on(c, R), y) ⇔ R(x, y)",
				By(ClassOnEqIff.At(c, R, x, y), equiv, x, y))
			a.Show(
				"and they are the classes",
				By(classX, classY, inside))
		}),
})}

// ---------------------------------------------------------------------------
// On the whole type
// ---------------------------------------------------------------------------
//
// The class laws of an equivalence on the whole type are the laws on a
// set at c = 𝕌. The view door does not carry them: its argument reads a
// carrier law at 𝕌 as it stands, and these speak of the class of R
// where the set laws speak of the class of relation_on(𝕌, R), so each
// rewrites the one into the other (ClassOnUniverse) before citing the
// set law.

// ClassOnUniverse — the class inside 𝕌 is the class: every point lies
// in 𝕌, so ClassOnClosed applies at every point.
var ClassOnUniverse = classOnUniverseThm{family.Add(registry.ProofEntry{
	Name: "ClassOnUniverse",
	Key:  "prop_b802a32b9810f16b",
	Build: family.Theorem("∀R:(A → A → bool). ∀x:A. "+
		"    equivalence_class(relation_on(𝕌, R), x) = equivalence_class(R, x)",
		func(a *Argument, R *Arrow2[A, A, Bool], x *Expr[A]) {
			a.Show(
				"x and every point it is related to lie in 𝕌",
				By(ClassOnClosed, set_basic.InUniv))
		}),
})}

// ClassOwn — a point lies in its own class: ClassOwnOn at 𝕌, where the
// restriction asks nothing.
var ClassOwn = classOwnThm{family.Add(registry.ProofEntry{
	Name: "ClassOwn",
	Key:  "prop_70d74d2e5fa7880a",
	Build: Equivalence.Law("∀x:A. x ∈ equivalence_class(R, x)",
		func(a *Argument, R *Arrow2[A, A, Bool], equiv Fact, x *Expr[A]) {
			onUniverse := a.Have(
				"R is an equivalence on 𝕌",
				"equivalence_on(𝕌, R)",
				By(equiv, EquivalenceOnUniverse))
			same := a.Have(
				"the class of x is its class inside 𝕌",
				"equivalence_class(relation_on(𝕌, R), x) = equivalence_class(R, x)",
				By(ClassOnUniverse))
			a.Show(
				"which holds x",
				same.RwRev(),
				By(ClassOwnOn, onUniverse, set_basic.InUniv))
		}),
})}

// ClassEqIff — two classes are equal exactly when their points are
// related: ClassEqIffClosed at 𝕌, which every relation keeps closed.
var ClassEqIff = classEqIffThm{family.Add(registry.ProofEntry{
	Name: "ClassEqIff",
	Key:  "prop_4341d76e9cde3103",
	Build: Equivalence.Law("∀x y:A. equivalence_class(R, x) = equivalence_class(R, y) ⇔ R(x, y)",
		func(a *Argument, R *Arrow2[A, A, Bool], equiv Fact, x, y *Expr[A]) {
			onUniverse := a.Have(
				"R is an equivalence on 𝕌",
				"equivalence_on(𝕌, R)",
				By(equiv, EquivalenceOnUniverse))
			a.Show(
				"every point lies in 𝕌, so 𝕌 is closed under R and holds x and y",
				By(ClassEqIffClosed, onUniverse, set_basic.InUniv))
		}),
})}

// ClassesDisjointOrEqual — two classes are equal or disjoint:
// ClassOnDisjointOrEqual at 𝕌.
var ClassesDisjointOrEqual = classesDisjointOrEqualThm{family.Add(registry.ProofEntry{
	Name: "ClassesDisjointOrEqual",
	Key:  "prop_23608dacdcbc63bb",
	Build: Equivalence.Law("∀x y:A. "+
		"    equivalence_class(R, x) = equivalence_class(R, y) ∨ "+
		"    disjoint(equivalence_class(R, x), equivalence_class(R, y))",
		func(a *Argument, R *Arrow2[A, A, Bool], equiv Fact, x, y *Expr[A]) {
			onUniverse := a.Have(
				"R is an equivalence on 𝕌",
				"equivalence_on(𝕌, R)",
				By(equiv, EquivalenceOnUniverse))
			sameX := a.Have(
				"the class of x is its class inside 𝕌",
				"equivalence_class(relation_on(𝕌, R), x) = equivalence_class(R, x)",
				By(ClassOnUniverse))
			sameY := a.Have(
				"and so is the class of y",
				"equivalence_class(relation_on(𝕌, R), y) = equivalence_class(R, y)",
				By(ClassOnUniverse))
			a.Show(
				"the two classes are the classes inside 𝕌, which are equal or disjoint",
				sameX.RwRev(),
				sameY.RwRev(),
				By(ClassOnDisjointOrEqual, onUniverse, set_basic.InUniv))
		}),
})}

// ---------------------------------------------------------------------------
// The classes partition the type
// ---------------------------------------------------------------------------

// ClassesPartition — the classes of an equivalence partition the type.
// The partition predicate is unfolded and its three clauses closed in
// the definition's order, each read off a block's representative: a
// block is the class of some point, which lies in it; every point lies
// in its own class; and two blocks sharing a point are equal or
// disjoint (ClassesDisjointOrEqual), and the shared point rules out
// disjoint.
var ClassesPartition = classesPartitionThm{family.Add(registry.ProofEntry{
	Name: "ClassesPartition",
	Key:  "prop_7aadacc72dded02",
	Build: Equivalence.Law("set_partition(image(equivalence_class(R), 𝕌))",
		func(a *Argument, R *Arrow2[A, A, Bool], equiv Fact) {
			classOf := a.TermAs[Fun[A, Set[A]]]("equivalence_class(R)")
			a.Do(Unfold(SetPartition), SplitConjAll(
				Case(
					"no block is empty: a block is the class of some point, and that point lies in it",
					Derive(func(b *Argument) {
						c := b.FixAs[Set[A]]()
						block := b.Assume()
						x, isClass := b.ObtainAs[A](
							"c is the class of some point x",
							"∃x:A. c = equivalence_class(R, x)",
							By(block, set_image.InRange.At(classOf, c)))
						b.Show(
							"and x lies in its own class",
							By(Normalized, isClass, ClassOwn.At(R, x), set_basic.MemberNotEmpty.At(c), equiv))
					})),
				Case(
					"every point lies in a block: its own class",
					Derive(func(b *Argument) {
						x := b.FixAs[A]()
						b.Take(b.TermAs[Set[A]]("equivalence_class(R, x)"))
						b.Show(
							"the class of x is a value of the class map, and x lies in it",
							By(set_image.FunInRange.At(classOf, x), ClassOwn.At(R, x), equiv))
					})),
				Case(
					"two blocks sharing a point are one block: equal or "+
						"disjoint, and the shared point rules out disjoint",
					Derive(func(b *Argument) {
						c := b.FixAs[Set[A]]()
						d := b.FixAs[Set[A]]()
						x := b.FixAs[A]()
						shared := b.Assume()
						y, cIsClass := b.ObtainAs[A](
							"c is the class of some point y",
							"∃y:A. c = equivalence_class(R, y)",
							By(shared, set_image.InRange.At(classOf, c)))
						z, dIsClass := b.ObtainAs[A](
							"d is the class of some point z",
							"∃z:A. d = equivalence_class(R, z)",
							By(shared, set_image.InRange.At(classOf, d)))
						overlap := b.Have(
							"the two classes have a common point, x",
							"∃w:A. w ∈ equivalence_class(R, y) ∧ w ∈ equivalence_class(R, z)",
							Derive(func(e *Argument) {
								e.Take(x)
								e.Show(
									"x lies in c and in d, which are those classes",
									By(Normalized, shared, cIsClass, dIsClass))
							}))
						notApart := b.Have(
							"so the two classes are not disjoint",
							"¬disjoint(equivalence_class(R, y), equivalence_class(R, z))",
							Simp(Fwd(set_algebra.InDisjoint)),
							By(overlap))
						b.Show(
							"equal or disjoint, and not disjoint",
							cIsClass.Rw(),
							dIsClass.Rw(),
							By(Normalized, notApart, ClassesDisjointOrEqual.At(R, y, z), equiv))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// A partition's relation is an equivalence
// ---------------------------------------------------------------------------

// PartitionEquivalence — the relation a partition induces, "some block
// holds both points", is an equivalence. The equivalence predicate is
// unfolded and its three conjuncts closed in order, each unfolding its
// property and `same_block`: a point's block holds it twice; a block
// holding x and y holds y and x; and blocks holding x, y and y, z share
// y, so they are one block, which holds x and z.
var PartitionEquivalence = partitionEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "PartitionEquivalence",
	Key:  "prop_408527352903258c",
	Build: SetPartition.Law("equivalence(same_block(P))",
		func(a *Argument, P *Expr[Set[Set[A]]], part SetPartitionFact[on.P]) {
			a.Do(Unfold(Equivalence), SplitConjAll(
				Case(
					"reflexive: every point lies in some block, which holds it twice",
					Derive(func(b *Argument) {
						b.Do(Unfold(ReflexiveDef), Unfold(SameBlockDef))
						x := b.FixAs[A]()
						c, holds := b.Obtain(
							"some block holds x",
							"∃c:set(A). c ∈ P ∧ x ∈ c",
							By(BlocksCover.At(P, x), part))
						b.Take(c)
						b.Show(
							"that block holds x, twice over",
							By(holds))
					})),
				Case(
					"symmetric: the block holding x and y holds y and x",
					Derive(func(b *Argument) {
						b.Do(Unfold(SymmetricDef), Unfold(SameBlockDef))
						b.Fix("x")
						b.Fix("y")
						related := b.Assume()
						c, holds := b.Unpack(related)
						b.Take(c)
						b.Show(
							"the same block holds y and x",
							By(holds))
					})),
				Case(
					"transitive: the blocks holding x, y and y, z share y, so they are one block",
					Derive(func(b *Argument) {
						b.Do(Unfold(TransitiveDef), Unfold(SameBlockDef))
						b.Fix("x")
						y := b.FixAs[A]()
						b.Fix("z")
						both := b.Conjuncts(
							b.Assume(),
							"some block c holds x and y",
							"some block d holds y and z")
						// The definition calls both witnesses c; the second is named d.
						c, cHolds := b.UnpackAs[Set[A]](both[0], "c")
						d, dHolds := b.UnpackAs[Set[A]](both[1], "d")
						same := b.Have(
							"c and d share the point y, so they are one block",
							"c = d",
							By(cHolds, dHolds, BlocksOverlapEqual.At(P, c, d, y), part))
						inC := b.Have(
							"z lies in c, which is d",
							"z ∈ c",
							same.Rw(),
							By(dHolds))
						b.Take(c)
						b.Show(
							"c is a block holding x and z",
							By(cHolds, inC))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// The two constructions are inverse
// ---------------------------------------------------------------------------

// BlockIsClass — a point is related to x exactly when some block holds
// both, and the one block holding x is c, so the class of x is c.
var BlockIsClass = blockIsClassThm{family.Add(registry.ProofEntry{
	Name: "BlockIsClass",
	Key:  "prop_9f7d190a61d61c2f",
	Build: SetPartition.Law(Statement{
		Binders: "∀c:set(A). ∀x:A.",
		Hypotheses: []string{
			"c ∈ P",
			"x ∈ c",
		},
		Conclusion: "equivalence_class(same_block(P), x) = c",
	},
		func(
			a *Argument,
			P *Expr[Set[Set[A]]],
			part SetPartitionFact[on.P],
			c *Member[Set[A], on.P],
			x *Member[A, on.C],
		) {
			a.Show(
				"sets with the same members are equal, and y lies in the class of x when some block holds x and y",
				Simp(Fwd(set_basic.Extension), Fwd(InClass), Fwd(SameBlockDef)),
				Derive(func(b *Argument) {
					b.Fix("y")
					b.Iff()
					b.Forward(
						"a point of c shares a block with x: c itself",
						func(b *Argument, inC Fact) {
							b.Take(c)
							b.Show(
								"c is a block holding x and y",
								By(c, x, inC))
						})
					b.Backward(
						"a block holding x and y shares x with c, so it is c, and y lies in c",
						func(b *Argument, related Fact) {
							d, dHolds := b.UnpackAs[Set[A]](related)
							// d is the witness of the same-block relation's own ∃c, which the
							// section's c shadows in claim text, so the claim is built from
							// the two terms.
							same := b.Have(
								"d and c share the point x, so they are one block",
								MakeProp(Equal(d, c)),
								By(dHolds, c, x, BlocksOverlapEqual.At(P, d, c, x), part))
							b.Show(
								"y lies in d, which is c",
								same.RwRev(),
								By(dHolds))
						})
				}))
		}),
})}

// ClassesOfSameBlock — a set is a block exactly when it is a class: a
// block holds some point, whose class it is, and the class of a point is
// the block holding it.
var ClassesOfSameBlock = classesOfSameBlockThm{family.Add(registry.ProofEntry{
	Name: "ClassesOfSameBlock",
	Key:  "prop_2120be98043e4a17",
	Build: SetPartition.Law("image(equivalence_class(same_block(P)), 𝕌) = P",
		func(a *Argument, P *Expr[Set[Set[A]]], part SetPartitionFact[on.P]) {
			// Both laws are read at the class map's values, sets of A: a Simp
			// rule is not adapted to another type on its own, so each is
			// instantiated there.
			a.Show(
				"two families with the same members are equal, and a class is a value of the class map",
				Simp(
					Fwd(set_basic.Extension.Inst[Set[A]]()),
					Fwd(set_image.InRange.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[Set[A]]()))),
				Derive(func(b *Argument) {
					c := b.FixAs[Set[A]]("c")
					b.Iff()
					b.Forward(
						"a block is a class: it holds some point, whose class it is",
						func(b *Argument, block Fact) {
							x, inC := b.ObtainAs[A](
								"c holds some point x, since no block is empty",
								"∃x:A. x ∈ c",
								Simp(Fwd(set_basic.MemberNotEmpty)),
								By(BlockNonempty, block, part))
							b.Take(x)
							b.Show(
								"c is the class of the point x it holds",
								By(Normalized, BlockIsClass.At(P, c, x), block, inC, part))
						})
					b.Backward(
						"a class is a block: the class of z is the block holding z",
						func(b *Argument, isClass Fact) {
							z, classOfZ := b.UnpackAs[A](isClass)
							d, dHolds := b.ObtainAs[Set[A]](
								"some block d holds z",
								"∃d:set(A). d ∈ P ∧ z ∈ d",
								By(BlocksCover.At(P, z), part))
							b.Show(
								"c is the class of z, which is d, a block",
								classOfZ.Rw(),
								By(Normalized, BlockIsClass.At(P, d, z), dHolds, part))
						})
				}))
		}),
})}

// SameBlockOfClasses — two points share a class exactly when they are
// related: a class holding both is the class of some point, which is
// related to each of them, and the class of x holds x and every point x
// is related to.
var SameBlockOfClasses = sameBlockOfClassesThm{family.Add(registry.ProofEntry{
	Name: "SameBlockOfClasses",
	Key:  "prop_ff4a6049f93c6f2",
	Build: Equivalence.Law("same_block(image(equivalence_class(R), 𝕌)) = R",
		func(a *Argument, R *Arrow2[A, A, Bool], equiv Fact) {
			classOf := a.TermAs[Fun[A, Set[A]]]("equivalence_class(R)")
			a.Show(
				"equal relations relate the same pairs, and a block of the classes is a class",
				Funext(),
				Simp(Fwd(SameBlockDef)),
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					b.Iff()
					b.Forward(
						"a class holding x and y is the class of some point z, "+
							"which is related to both, so x is related to y through z",
						func(b *Argument, shared Fact) {
							c, holds := b.UnpackAs[Set[A]](shared)
							z, isClass := b.ObtainAs[A](
								"c is the class of some point z",
								"∃z:A. c = equivalence_class(R, z)",
								By(holds, set_image.InRange.At(classOf, c)))
							fromZ := b.Have(
								"z is related to x and to y, since its class holds both",
								"R(z, x) ∧ R(z, y)",
								By(Normalized, isClass, holds, InClass.At(R, z, x), InClass.At(R, z, y)))
							b.Show(
								"x is related to z by symmetry, and on to y by transitivity",
								By(fromZ, Symmetric.At(R, z, x), Transitive.At(R, x, z, y), equiv))
						})
					b.Backward(
						"the class of x holds x, and y, which x is related to",
						func(b *Argument, related Fact) {
							b.Take(b.TermAs[Set[A]]("equivalence_class(R, x)"))
							b.Show(
								"the class of x is a class; x lies in it, and so does y, since x is related to y",
								By(set_image.FunInRange.At(classOf, x), ClassOwn.At(R, x), InClass.At(R, x, y), related, equiv))
						})
				}))
		}),
})}

// ---------------------------------------------------------------------------
// Counting by classes
// ---------------------------------------------------------------------------

// CountByClassesOn — a finite set c with an equivalence on it, the class
// of each of whose points has m elements, has m elements for every
// class.
//
// The blocks are the members of the quotient. There are finitely many of
// them, c being finite (QuotientOnFinite); each has m elements, being the
// class of a point of c; and two different ones are disjoint
// (QuotientOnDisjointOrEqual). So `HasSizeUnions` gives their union m
// elements for every block, and that union is c (QuotientOnCovers).
var CountByClassesOn = countByClassesOnThm{family.Add(registry.ProofEntry{
	Name: "CountByClassesOn",
	Key:  "prop_f908267a66c07818",
	Build: EquivalenceOn.Law(Statement{
		Binders: "∀m:num.",
		Hypotheses: []string{
			"finite(c)",
			"∀x:A. x ∈ c ⇒ has_size(equivalence_class(relation_on(c, R), x), m)",
		},
		Conclusion: "card(c) = m * card(quotient_on(c, R))",
	},
		func(
			a *Argument,
			c *Expr[Set[A]],
			R *Arrow2[A, A, Bool],
			equiv EquivalenceFact[on.C],
			m *Expr[Nat],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"c is finite",
				"the class of each point of c has m elements")
			finiteC, sized := parts[0], parts[1]

			classes := a.TermAs[Set[Set[A]]]("quotient_on(c, R)")
			count := a.TermAs[Nat]("m * card(quotient_on(c, R))")

			eachSized := a.Have(
				"each class has m elements: it is the class of a point of c",
				"∀s:set(A). s ∈ quotient_on(c, R) ⇒ has_size(s, m)",
				Simp(Fwd(ForallInQuotientOn)),
				By(sized))

			equalOrApart := a.Have(
				"two classes are equal or disjoint",
				"∀s t:set(A). s ∈ quotient_on(c, R) ∧ t ∈ quotient_on(c, R) ⇒ s = t ∨ disjoint(s, t)",
				By(QuotientOnDisjointOrEqual, equiv))

			apart := a.Have(
				"so two different classes are disjoint",
				"∀s t:set(A). s ∈ quotient_on(c, R) ∧ t ∈ quotient_on(c, R) ∧ s ≠ t ⇒ disjoint(s, t)",
				a.ForEach(func(s *Expr[Set[A]]) Action {
					return a.ForEach(func(t *Expr[Set[A]]) Action {
						return By(Normalized, equalOrApart.At(s, t))
					})
				}))

			covers := a.Have(
				"the classes make up c",
				"⋃quotient_on(c, R) = c",
				By(QuotientOnCovers, equiv))

			unionSized := a.Have(
				"so the union of the finitely many classes has m elements for every class",
				"has_size(⋃quotient_on(c, R), m * card(quotient_on(c, R)))",
				By(cardinality.HasSizeUnions.At(classes, m), finiteC, QuotientOnFinite.At(c, R), eachSized, apart))

			a.Show(
				"that union is c, and a set of known size has that many elements",
				By(Normalized, unionSized, covers, cardinality.CardOfSized.At(c, count)))
		}),
})}

// CountByClasses — a finite set s closed under an equivalence, the class
// of each of whose points has m elements, has m elements for every class:
// CountByClassesOn at s. The equivalence is one on s (EquivalenceOnMono),
// and s being closed, the class of a point of s inside s is its class
// (ClassOnClosed) and the quotient of s is the image of s under the class
// map (QuotientOnClosed).
var CountByClasses = countByClassesThm{family.Add(registry.ProofEntry{
	Name: "CountByClasses",
	Key:  "prop_8a3da47ccf01895b",
	Build: Equivalence.Law(Statement{
		Binders: "∀s:set(A). ∀m:num.",
		Hypotheses: []string{
			"finite(s)",
			"∀x y:A. x ∈ s ∧ R(x, y) ⇒ y ∈ s",
			"∀x:A. x ∈ s ⇒ has_size(equivalence_class(R, x), m)",
		},
		Conclusion: "card(s) = m * card(image(equivalence_class(R), s))",
	},
		func(a *Argument, R *Arrow2[A, A, Bool], equiv Fact, s *Expr[Set[A]], m *Expr[Nat], given Fact) {
			parts := a.Conjuncts(
				given,
				"s is finite",
				"s is closed under R",
				"the class of each point of s has m elements")
			finiteS, closed, sized := parts[0], parts[1], parts[2]

			onUniverse := a.Have(
				"R is an equivalence on 𝕌",
				"equivalence_on(𝕌, R)",
				By(equiv, EquivalenceOnUniverse))
			onS := a.Have(
				"so on s",
				"equivalence_on(s, R)",
				By(EquivalenceOnMono, onUniverse, set_order.SubsetUniv))
			quotient := a.Have(
				"s being closed under R, its quotient is the image of s under the class map",
				"quotient_on(s, R) = image(equivalence_class(R), s)",
				By(closed, QuotientOnClosed))
			sizedOn := a.Have(
				"the class inside s of each point of s is its class, which has m elements",
				"∀x:A. x ∈ s ⇒ has_size(equivalence_class(relation_on(s, R), x), m)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					inS := b.Assume()
					same := b.Have(
						"the class of x inside s is its class, s being closed under R",
						"equivalence_class(relation_on(s, R), x) = equivalence_class(R, x)",
						By(inS, closed, ClassOnClosed.At(s, R, x)))
					b.Show(
						"and that class has m elements",
						same.Rw(),
						By(inS, sized.At(x)))
				}))
			a.Show(
				"count s by its quotient, which is the image of s under the class map",
				quotient.RwRev(),
				By(CountByClassesOn, onS, finiteS, sizedOn))
		}),
})}

// ---------------------------------------------------------------------------
// The value of a map on a class
// ---------------------------------------------------------------------------

// InducedMapClass — a map that respects the relation on c takes, on the
// class of a point x of c, the value f(x): the induced map reads f at
// the point chosen in the class, and f takes one value on related
// points. x is related to itself inside c, so to the chosen point
// (ChosenRepresentative), which is then a point of c related to x.
var InducedMapClass = inducedMapClassThm{family.Add(registry.ProofEntry{
	Name: "InducedMapClass",
	Key:  "prop_a546b8317eddcba1",
	Build: EquivalenceOn.Law(Statement{
		Binders: "∀f:(A → B). ∀x:A.",
		Hypotheses: []string{
			"respects_on(c, R, f)",
			"x ∈ c",
		},
		Conclusion: "induced_map(f, equivalence_class(relation_on(c, R), x)) = f(x)",
	},
		func(
			a *Argument,
			c *Expr[Set[A]],
			R *Arrow2[A, A, Bool],
			equiv EquivalenceFact[on.C],
			f *Arrow[A, B],
			x *Member[A, on.C],
			respects Fact,
		) {
			agrees := a.Unfolded(respects, RespectsOnDef)
			inside := a.TermAs[Fun2[A, A, Bool]]("relation_on(c, R)")
			related := a.Have(
				"x lies in c and is related to itself, so, inside c, to the point chosen in its class",
				"relation_on(c, R, x, εy:A. y ∈ equivalence_class(relation_on(c, R), x))",
				By(ReflexiveOn.Read(equiv).At(x), RelationOnDef.At(c, R, x, x), ChosenRepresentative.At(inside, x)))
			a.Show(
				"the induced map is f at the chosen point, a point of "+
					"c that x is related to, where f takes the value f(x)",
				Unfold(InducedMapDef),
				By(agrees, related, RelationOnDef))
		}),
})}
