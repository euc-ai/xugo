// category.go — a category on two carrier sets, held in the record
// `category_ops(A, M)`: a set of objects, a set of morphisms, the
// source and target of a morphism, the identity at an object and the
// composite of two morphisms, with the unit and associativity laws
// stated for the composable morphisms of the carrier; the hom sets;
// the isomorphisms and the groupoids, the categories whose every
// morphism is one; and the functors between two categories, with the
// set of normalized functors the functor category is built on.
//
// The composition is a total map and reads `C.compose(g, f)` for g
// after f; what it does off the carrier or on a non-composable pair is
// not constrained, so every law carries its memberships and the
// composability `C.target(f) = C.source(g)` as hypotheses.

package category

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structure and its axioms
// ---------------------------------------------------------------------------

// Category — `category(C)`: a morphism of C has its source and target
// among the objects; the identity at an object is a morphism from it to
// itself; two morphisms with the target of the first the source of the
// second compose to a morphism from the source of the first to the
// target of the second; the identities are units and composition
// associates.
var Category = categoryThm{family.DefineStructure(registry.DefEntry{
	Name:    "Category",
	Key:     "prop_dbf0a799778d4e57",
	Const:   "category",
	Type:    "category_ops(A, M) → bool",
	Subject: "C",
	Equations: []string{
		"∀C:category_ops(A, M). " +
			"    category(C) ⇔ " +
			"    (∀f:M. f ∈ C.morphisms ⇒ C.source(f) ∈ C.objects ∧ C.target(f) ∈ C.objects) ∧ " +
			"    (∀x:A. " +
			"        x ∈ C.objects ⇒ " +
			"        C.identity(x) ∈ C.morphisms ∧ " +
			"        C.source(C.identity(x)) = x ∧ " +
			"        C.target(C.identity(x)) = x) ∧ " +
			"    (∀f g:M. " +
			"        f ∈ C.morphisms ∧ g ∈ C.morphisms ∧ C.target(f) = C.source(g) ⇒ " +
			"        C.compose(g, f) ∈ C.morphisms ∧ " +
			"        C.source(C.compose(g, f)) = C.source(f) ∧ " +
			"        C.target(C.compose(g, f)) = C.target(g)) ∧ " +
			"    (∀f:M. f ∈ C.morphisms ⇒ C.compose(C.identity(C.target(f)), f) = f) ∧ " +
			"    (∀f:M. f ∈ C.morphisms ⇒ C.compose(f, C.identity(C.source(f))) = f) ∧ " +
			"    (∀f g h:M. " +
			"        f ∈ C.morphisms ∧ " +
			"        g ∈ C.morphisms ∧ " +
			"        h ∈ C.morphisms ∧ " +
			"        C.target(f) = C.source(g) ∧ " +
			"        C.target(g) = C.source(h) ⇒ " +
			"        C.compose(h, C.compose(g, f)) = C.compose(C.compose(h, g), f))",
	},
	Deps: []registry.EntryLike{
		CategoryObjectsDef,
		CategoryMorphismsDef,
		CategorySourceDef,
		CategoryTargetDef,
		CategoryIdentityDef,
		CategoryComposeDef,
	},
	Reading: "The composite is written C.compose(g, f) for g after f. An object or a morphism off " +
		"the carriers is unconstrained: the empty category is category(mk_category(∅, ∅, …)) for any maps.",
})}

// MorphismEnds — the ends of a morphism are objects.
var MorphismEnds = morphismEndsThm{family.Add(registry.ProofEntry{
	Name: "MorphismEnds",
	Key:  "prop_9ab2215a41c3685d",
	Build: Category.Axiom(Statement{
		Binders: "∀f:M.",
		Hypotheses: []string{
			"f ∈ C.morphisms",
		},
		Conclusion: "C.source(f) ∈ C.objects ∧ C.target(f) ∈ C.objects",
	}),
})}

// IdentityMorphism — the identity at an object is a morphism from it to
// itself.
var IdentityMorphism = identityMorphismThm{family.Add(registry.ProofEntry{
	Name: "IdentityMorphism",
	Key:  "prop_63798fb7f984139e",
	Build: Category.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ C.objects",
		},
		Conclusion: "C.identity(x) ∈ C.morphisms ∧ " +
			"C.source(C.identity(x)) = x ∧ " +
			"C.target(C.identity(x)) = x",
	}),
})}

// CompositeMorphism — composable morphisms compose to a morphism with
// the source of the first and the target of the second.
var CompositeMorphism = compositeMorphismThm{family.Add(registry.ProofEntry{
	Name: "CompositeMorphism",
	Key:  "prop_8a5d2cca1fc2ff47",
	Build: Category.Axiom(Statement{
		Binders: "∀f g:M.",
		Hypotheses: []string{
			"f ∈ C.morphisms",
			"g ∈ C.morphisms",
			"C.target(f) = C.source(g)",
		},
		Conclusion: "C.compose(g, f) ∈ C.morphisms ∧ " +
			"C.source(C.compose(g, f)) = C.source(f) ∧ " +
			"C.target(C.compose(g, f)) = C.target(g)",
	}),
})}

// LeftUnit — the identity at the target is a left unit.
var LeftUnit = leftUnitThm{family.Add(registry.ProofEntry{
	Name: "LeftUnit",
	Key:  "prop_d62e60a1d04e994b",
	Build: Category.Axiom(Statement{
		Binders: "∀f:M.",
		Hypotheses: []string{
			"f ∈ C.morphisms",
		},
		Conclusion: "C.compose(C.identity(C.target(f)), f) = f",
	}),
})}

// RightUnit — the identity at the source is a right unit.
var RightUnit = rightUnitThm{family.Add(registry.ProofEntry{
	Name: "RightUnit",
	Key:  "prop_77aba7999992e9c5",
	Build: Category.Axiom(Statement{
		Binders: "∀f:M.",
		Hypotheses: []string{
			"f ∈ C.morphisms",
		},
		Conclusion: "C.compose(f, C.identity(C.source(f))) = f",
	}),
})}

// Assoc — composition associates on composable triples.
var Assoc = assocThm{family.Add(registry.ProofEntry{
	Name: "Assoc",
	Key:  "prop_d90a8afa7d0a1074",
	Build: Category.Axiom(Statement{
		Binders: "∀f g h:M.",
		Hypotheses: []string{
			"f ∈ C.morphisms",
			"g ∈ C.morphisms",
			"h ∈ C.morphisms",
			"C.target(f) = C.source(g)",
			"C.target(g) = C.source(h)",
		},
		Conclusion: "C.compose(h, C.compose(g, f)) = C.compose(C.compose(h, g), f)",
	}),
})}

// IdentityComposeIdentity — the identity at an object composed with
// itself is itself: the left unit at C.identity(x), whose target is x.
var IdentityComposeIdentity = identityComposeIdentityThm{family.Add(registry.ProofEntry{
	Name: "IdentityComposeIdentity",
	Key:  "prop_5e971893bb437c30",
	Build: Category.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ C.objects",
		},
		Conclusion: "C.compose(C.identity(x), C.identity(x)) = C.identity(x)",
	},
		func(a *Argument, category Fact, x *Expr[A], object Fact) {
			identity := a.Have(
				"the identity at x is a morphism whose target is x",
				"C.identity(x) ∈ C.morphisms ∧ C.target(C.identity(x)) = x",
				By(object, At(IdentityMorphism.Read(category), x)))
			a.Show(
				"the left unit at C.identity(x), whose target is x",
				By(Normalized, identity, At(LeftUnit.Read(category), a.Term("C.identity(x)"))))
		}),
})}

// ---------------------------------------------------------------------------
// Hom sets, isomorphisms and groupoids
// ---------------------------------------------------------------------------

// CategoryHomDef — `category_hom(C, x, y)`: the morphisms of C from x
// to y.
var CategoryHomDef = categoryHomDefThm{family.Define(registry.DefEntry{
	Name:  "CategoryHomDef",
	Key:   "prop_4af00deb55a8bbf6",
	Const: "category_hom",
	Type:  "category_ops(A, M) → A → A → set(M)",
	Equations: []string{
		"∀C:category_ops(A, M). ∀x y:A. " +
			"    category_hom(C, x, y) = {f:M | f ∈ C.morphisms ∧ C.source(f) = x ∧ C.target(f) = y}",
	},
	Deps: []registry.EntryLike{CategoryMorphismsDef, CategorySourceDef, CategoryTargetDef},
	Reading: "The hom set is a set of the morphism type M; it is " +
		"empty when x or y is no object, since a morphism's ends are objects.",
})}

// IdentityHom — the identity at an object lies in its endomorphism hom
// set: IdentityMorphism read through the hom set.
var IdentityHom = identityHomThm{family.Add(registry.ProofEntry{
	Name: "IdentityHom",
	Key:  "prop_6270ad2cc16aa15f",
	Build: Category.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ C.objects",
		},
		Conclusion: "C.identity(x) ∈ category_hom(C, x, x)",
	},
		func(a *Argument, category Fact, x *Expr[A], object Fact) {
			a.Show(
				"the identity at x is a morphism from x to x",
				BySets(
					object,
					IdentityMorphism.Read(category).AsFact().At(x),
					CategoryHomDef.At(a.TermAs[CategoryOps[A, M]]("C"), x, x)))
		}),
})}

// ComposeHom — the composite of a morphism from x to y and a morphism
// from y to z lies in the hom set from x to z: CompositeMorphism read
// through the three hom sets.
var ComposeHom = composeHomThm{family.Add(registry.ProofEntry{
	Name: "ComposeHom",
	Key:  "prop_1b697bc111dd505a",
	Build: Category.Law(Statement{
		Binders: "∀x y z:A. ∀f g:M.",
		Hypotheses: []string{
			"f ∈ category_hom(C, x, y)",
			"g ∈ category_hom(C, y, z)",
		},
		Conclusion: "C.compose(g, f) ∈ category_hom(C, x, z)",
	},
		func(a *Argument, category Fact, x, y, z *Expr[A], f, g *Expr[M], homs Fact) {
			C := a.TermAs[CategoryOps[A, M]]("C")
			a.Show(
				"g follows f, and their composite runs from the source of f to the target of g",
				BySets(
					homs,
					CategoryHomDef.At(C, x, y),
					CategoryHomDef.At(C, y, z),
					CategoryHomDef.At(C, x, z),
					CompositeMorphism.Read(category).AsFact().At(f, g)))
		}),
})}

// MorphismInHom — a morphism lies in the hom set from its source to its
// target.
var MorphismInHom = morphismInHomThm{family.Add(registry.ProofEntry{
	Name: "MorphismInHom",
	Key:  "prop_198277a5c7ed5141",
	Build: family.Theorem(Statement{
		Binders: "∀C:category_ops(A, M). ∀f:M.",
		Hypotheses: []string{
			"f ∈ C.morphisms",
		},
		Conclusion: "f ∈ category_hom(C, C.source(f), C.target(f))",
	}, func(a *Argument, C *Expr[CategoryOps[A, M]], f *Expr[M], morphism Fact) {
		a.Show(
			"f is a morphism from its source to its target",
			BySets(morphism, CategoryHomDef.At(C, a.TermAs[A]("C.source(f)"), a.TermAs[A]("C.target(f)"))))
	}),
})}

// AssocHom — composition associates on three consecutive hom sets: Assoc
// read through the hom sets.
var AssocHom = assocHomThm{family.Add(registry.ProofEntry{
	Name: "AssocHom",
	Key:  "prop_69303700fd61c915",
	Build: Category.Law(Statement{
		Binders: "∀x y z w:A. ∀f g h:M.",
		Hypotheses: []string{
			"f ∈ category_hom(C, x, y)",
			"g ∈ category_hom(C, y, z)",
			"h ∈ category_hom(C, z, w)",
		},
		Conclusion: "C.compose(h, C.compose(g, f)) = C.compose(C.compose(h, g), f)",
	},
		func(a *Argument, category Fact, x, y, z, w *Expr[A], f, g, h *Expr[M], homs Fact) {
			C := a.TermAs[CategoryOps[A, M]]("C")
			a.Show(
				"the three consecutive arrows associate",
				BySets(
					homs,
					CategoryHomDef.At(C, x, y),
					CategoryHomDef.At(C, y, z),
					CategoryHomDef.At(C, z, w),
					Assoc.Read(category).AsFact().At(f, g, h)))
		}),
})}

// LeftUnitHom — the identity at y is a left unit on the hom set from x
// to y: LeftUnit read through the hom set.
var LeftUnitHom = leftUnitHomThm{family.Add(registry.ProofEntry{
	Name: "LeftUnitHom",
	Key:  "prop_f68c9fe17ece08f3",
	Build: Category.Law(Statement{
		Binders: "∀x y:A. ∀f:M.",
		Hypotheses: []string{
			"f ∈ category_hom(C, x, y)",
		},
		Conclusion: "C.compose(C.identity(y), f) = f",
	},
		func(a *Argument, category Fact, x, y *Expr[A], f *Expr[M], arrow Fact) {
			a.Show(
				"the identity at the target of f is a left unit",
				BySets(
					arrow,
					CategoryHomDef.At(a.TermAs[CategoryOps[A, M]]("C"), x, y),
					LeftUnit.Read(category).AsFact().At(f)))
		}),
})}

// RightUnitHom — the identity at x is a right unit on the hom set from x
// to y: RightUnit read through the hom set.
var RightUnitHom = rightUnitHomThm{family.Add(registry.ProofEntry{
	Name: "RightUnitHom",
	Key:  "prop_c3a612e2495e5e23",
	Build: Category.Law(Statement{
		Binders: "∀x y:A. ∀f:M.",
		Hypotheses: []string{
			"f ∈ category_hom(C, x, y)",
		},
		Conclusion: "C.compose(f, C.identity(x)) = f",
	},
		func(a *Argument, category Fact, x, y *Expr[A], f *Expr[M], arrow Fact) {
			a.Show(
				"the identity at the source of f is a right unit",
				BySets(
					arrow,
					CategoryHomDef.At(a.TermAs[CategoryOps[A, M]]("C"), x, y),
					RightUnit.Read(category).AsFact().At(f)))
		}),
})}

// CategoryIsomorphismDef — `category_isomorphism(C, f)`: a morphism
// with a two-sided inverse.
var CategoryIsomorphismDef = categoryIsomorphismDefThm{family.Define(registry.DefEntry{
	Name:  "CategoryIsomorphismDef",
	Key:   "prop_ecffed71f8254249",
	Const: "category_isomorphism",
	Type:  "category_ops(A, M) → M → bool",
	Equations: []string{
		"∀C:category_ops(A, M). ∀f:M. " +
			"    category_isomorphism(C, f) ⇔ " +
			"    f ∈ C.morphisms ∧ " +
			"    (∃g:M. " +
			"        g ∈ C.morphisms ∧ " +
			"        C.source(g) = C.target(f) ∧ " +
			"        C.target(g) = C.source(f) ∧ " +
			"        C.compose(g, f) = C.identity(C.source(f)) ∧ " +
			"        C.compose(f, g) = C.identity(C.target(f)))",
	},
	Deps: []registry.EntryLike{
		CategoryMorphismsDef,
		CategorySourceDef,
		CategoryTargetDef,
		CategoryIdentityDef,
		CategoryComposeDef,
	},
})}

// GroupoidDef — `groupoid(C)`: a category in which every morphism is an
// isomorphism.
var GroupoidDef = groupoidDefThm{family.Define(registry.DefEntry{
	Name:  "GroupoidDef",
	Key:   "prop_e821fadc6bc31f04",
	Const: "groupoid",
	Type:  "category_ops(A, M) → bool",
	Equations: []string{
		"∀C:category_ops(A, M). " +
			"    groupoid(C) ⇔ category(C) ∧ (∀f:M. f ∈ C.morphisms ⇒ category_isomorphism(C, f))",
	},
	Deps: []registry.EntryLike{Category, CategoryIsomorphismDef},
})}

// InverseUnique — a morphism has at most one inverse: a left inverse g
// and a right inverse g' of f are both the composite g ∘ f ∘ g', read
// through f ∘ g' = C.identity(C.target f) as g and through g ∘ f =
// C.identity(C.source f) as g', associativity on the composable triple
// (g', f, g) moving the brackets between the two readings.
var InverseUnique = inverseUniqueThm{family.Add(registry.ProofEntry{
	Name: "InverseUnique",
	Key:  "prop_14675f6670105651",
	Build: Category.Law(Statement{
		Binders: "∀f g g':M.",
		Hypotheses: []string{
			"f ∈ C.morphisms",
			"g ∈ C.morphisms",
			"g' ∈ C.morphisms",
			"C.source(g) = C.target(f)",
			"C.target(g') = C.source(f)",
			"C.compose(g, f) = C.identity(C.source(f))",
			"C.compose(f, g') = C.identity(C.target(f))",
		},
		Conclusion: "g = g'",
	},
		func(a *Argument, category Fact, f, g, gPrime Term, inverses Fact) {
			a.Show(
				"g and g' are the composite g ∘ f ∘ g' bracketed two ways",
				CalcEq(
					Leg(
						a.Term("C.compose(g, C.identity(C.source(g)))"),
						"the right unit at g",
						By(inverses, At(RightUnit.Read(category), g))),
					Leg(
						a.Term("C.compose(g, C.identity(C.target(f)))"),
						"g follows f",
						By(Normalized, inverses)),
					Leg(
						a.Term("C.compose(g, C.compose(f, g'))"),
						"f ∘ g' is the identity at C.target(f)",
						By(Normalized, inverses)),
					Leg(
						a.Term("C.compose(C.compose(g, f), g')"),
						"associativity on g', f, g, composable as C.target(g') = C.source(f) and C.target(f) = C.source(g)",
						By(inverses, At(Assoc.Read(category), gPrime, f, g))),
					Leg(
						a.Term("C.compose(C.identity(C.source(f)), g')"),
						"g ∘ f is the identity at C.source(f)",
						By(Normalized, inverses)),
					Leg(
						a.Term("C.compose(C.identity(C.target(g')), g')"),
						"f follows g'",
						By(Normalized, inverses)),
					FinalLeg(
						"the left unit at g'",
						By(inverses, At(LeftUnit.Read(category), gPrime))),
				))
		}),
	Reading: "C.target(g') = C.source(f) is load-bearing: without it " +
		"the pair (f, g') need not be composable and C.compose(f, g') is " +
		"an unconstrained value, so g' could be the identity at C.target(f).",
})}

// IsomorphismFromInverses — a morphism with a left inverse and a right
// inverse is an isomorphism: InverseUnique makes the two inverses one,
// so the left inverse takes on the target and the right-inverse
// equation of the right one and is a two-sided inverse.
var IsomorphismFromInverses = isomorphismFromInversesThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismFromInverses",
	Key:  "prop_69c3dcc5ffd5a95b",
	Build: Category.Law(Statement{
		Binders: "∀f g g':M.",
		Hypotheses: []string{
			"f ∈ C.morphisms",
			"g ∈ C.morphisms",
			"g' ∈ C.morphisms",
			"C.source(g) = C.target(f)",
			"C.target(g') = C.source(f)",
			"C.compose(g, f) = C.identity(C.source(f))",
			"C.compose(f, g') = C.identity(C.target(f))",
		},
		Conclusion: "category_isomorphism(C, f)",
	},
		func(a *Argument, category Fact, f, g, gPrime Term, inverses Fact) {
			same := a.Have(
				"the left inverse is the right inverse",
				"g = g'",
				By(inverses, At(InverseUnique.Read(category), f, g, gPrime)))
			right := a.Have(
				"so g ends at the source of f and is a right inverse of f",
				"C.target(g) = C.source(f) ∧ C.compose(f, g) = C.identity(C.target(f))",
				Simp(Fwd(same)),
				By(inverses))
			a.Do(Simp(Fwd(CategoryIsomorphismDef)), SplitConj(
				Case(
					"f is a morphism",
					By(inverses)),
				Case(
					"g is a two-sided inverse of f",
					Derive(func(b *Argument) {
						b.Take(g)
						b.Show(
							"g runs from the target of f back to its source and both composites are identities",
							By(inverses, right))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Functors
// ---------------------------------------------------------------------------

// FunctorDef — `functor(C, D, F)`: a map of objects and a map of
// morphisms between two categories, carrying objects to objects and
// morphisms to morphisms, preserving sources, targets, identities and
// composites. The two categories are its first conjuncts.
var FunctorDef = functorDefThm{family.Define(registry.DefEntry{
	Name:  "FunctorDef",
	Key:   "prop_f5be4415aed42666",
	Const: "functor",
	Type:  "category_ops(A, M) → category_ops(B, N) → functor_ops(A, M, B, N) → bool",
	Equations: []string{
		"∀C:category_ops(A, M). ∀D:category_ops(B, N). ∀F:functor_ops(A, M, B, N). " +
			"    functor(C, D, F) ⇔ " +
			"    category(C) ∧ " +
			"    category(D) ∧ " +
			"    (∀x:A. x ∈ C.objects ⇒ F.obj(x) ∈ D.objects) ∧ " +
			"    (∀f:M. " +
			"        f ∈ C.morphisms ⇒ " +
			"        F.map(f) ∈ D.morphisms ∧ " +
			"        D.source(F.map(f)) = F.obj(C.source(f)) ∧ " +
			"        D.target(F.map(f)) = F.obj(C.target(f))) ∧ " +
			"    (∀x:A. x ∈ C.objects ⇒ F.map(C.identity(x)) = D.identity(F.obj(x))) ∧ " +
			"    (∀f g:M. " +
			"        f ∈ C.morphisms ∧ g ∈ C.morphisms ∧ C.target(f) = C.source(g) ⇒ " +
			"        F.map(C.compose(g, f)) = D.compose(F.map(g), F.map(f)))",
	},
	Deps: []registry.EntryLike{Category, FunctorObjDef, FunctorMapDef},
})}

// FunctorSourceCategory — the source of a functor is a category.
var FunctorSourceCategory = functorSourceCategoryThm{family.Add(registry.ProofEntry{
	Name:  "FunctorSourceCategory",
	Key:   "prop_a3f1930e80f01591",
	Build: FunctorDef.Entry().Conjunct("category(C)"),
})}

// FunctorTargetCategory — the target of a functor is a category.
var FunctorTargetCategory = functorTargetCategoryThm{family.Add(registry.ProofEntry{
	Name:  "FunctorTargetCategory",
	Key:   "prop_2029ebc4929e33f2",
	Build: FunctorDef.Entry().Conjunct("category(D)"),
})}

// FunctorObjectImage — a functor carries an object to an object.
var FunctorObjectImage = functorObjectImageThm{family.Add(registry.ProofEntry{
	Name: "FunctorObjectImage",
	Key:  "prop_def6477bbbfcc980",
	Build: FunctorDef.Entry().Conjunct(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ C.objects",
		},
		Conclusion: "F.obj(x) ∈ D.objects",
	}),
})}

// FunctorMapEnds — a functor carries a morphism to a morphism from the
// image of its source to the image of its target.
var FunctorMapEnds = functorMapEndsThm{family.Add(registry.ProofEntry{
	Name: "FunctorMapEnds",
	Key:  "prop_89a5dd41b884184b",
	Build: FunctorDef.Entry().Conjunct(Statement{
		Binders: "∀f:M.",
		Hypotheses: []string{
			"f ∈ C.morphisms",
		},
		Conclusion: "F.map(f) ∈ D.morphisms ∧ " +
			"D.source(F.map(f)) = F.obj(C.source(f)) ∧ " +
			"D.target(F.map(f)) = F.obj(C.target(f))",
	}),
})}

// FunctorPreservesIdentity — a functor carries the identity at an
// object to the identity at its image.
var FunctorPreservesIdentity = functorPreservesIdentityThm{family.Add(registry.ProofEntry{
	Name: "FunctorPreservesIdentity",
	Key:  "prop_2e800cfec1ab",
	Build: FunctorDef.Entry().Conjunct(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ C.objects",
		},
		Conclusion: "F.map(C.identity(x)) = D.identity(F.obj(x))",
	}),
})}

// FunctorPreservesComposite — a functor carries the composite of two
// composable morphisms to the composite of their images.
var FunctorPreservesComposite = functorPreservesCompositeThm{family.Add(registry.ProofEntry{
	Name: "FunctorPreservesComposite",
	Key:  "prop_ecc516aa25202a44",
	Build: FunctorDef.Entry().Conjunct(Statement{
		Binders: "∀f g:M.",
		Hypotheses: []string{
			"f ∈ C.morphisms",
			"g ∈ C.morphisms",
			"C.target(f) = C.source(g)",
		},
		Conclusion: "F.map(C.compose(g, f)) = D.compose(F.map(g), F.map(f))",
	}),
})}

// FunctorMapHom — a functor carries the hom set from x to y into the hom
// set between the images of x and y: FunctorMapEnds read on the
// membership.
var FunctorMapHom = functorMapHomThm{family.Add(registry.ProofEntry{
	Name: "FunctorMapHom",
	Key:  "prop_5052fc6e8b9eda59",
	Build: FunctorDef.Entry().Law(Statement{
		Binders: "∀x y:A. ∀f:M.",
		Hypotheses: []string{
			"f ∈ category_hom(C, x, y)",
		},
		Conclusion: "F.map(f) ∈ category_hom(D, F.obj(x), F.obj(y))",
	}, func(a *Argument, functorial Fact, x, y *Expr[A], f *Expr[M], arrow Fact) {
		a.Show(
			"the image of f is a morphism between the images of its ends",
			BySets(
				arrow,
				FunctorMapEnds.Read(functorial).AsFact().At(f),
				CategoryHomDef.At(a.TermAs[CategoryOps[A, M]]("C"), x, y),
				CategoryHomDef.At(
					a.TermAs[CategoryOps[B, N]]("D"), a.TermAs[B]("F.obj(x)"), a.TermAs[B]("F.obj(y)"))))
	}),
})}

// FunctorMapInHom — a functor carries a morphism into the hom set
// between the images of its source and its target: MorphismInHom, then
// FunctorMapHom.
var FunctorMapInHom = functorMapInHomThm{family.Add(registry.ProofEntry{
	Name: "FunctorMapInHom",
	Key:  "prop_12ba3d998afc4e51",
	Build: FunctorDef.Entry().Law(Statement{
		Binders: "∀f:M.",
		Hypotheses: []string{
			"f ∈ C.morphisms",
		},
		Conclusion: "F.map(f) ∈ category_hom(D, F.obj(C.source(f)), F.obj(C.target(f)))",
	}, func(a *Argument, functorial Fact, f *Expr[M], morphism Fact) {
		C := a.TermAs[CategoryOps[A, M]]("C")
		a.Show(
			"f lies in the hom set between its ends, which F carries into the hom set between their images",
			By(
				functorial,
				morphism,
				MorphismInHom.At(C, f),
				FunctorMapHom.At(
					C,
					a.TermAs[CategoryOps[B, N]]("D"),
					a.TermAs[FunctorOps[A, M, B, N]]("F"),
					a.TermAs[A]("C.source(f)"),
					a.TermAs[A]("C.target(f)"),
					f)))
	}),
})}

// FunctorPreservesCompositeHom — a functor carries the composite of a
// morphism from x to y and one from y to z to the composite of their
// images: FunctorPreservesComposite read through the hom sets.
var FunctorPreservesCompositeHom = functorPreservesCompositeHomThm{family.Add(registry.ProofEntry{
	Name: "FunctorPreservesCompositeHom",
	Key:  "prop_a861baea5b746d56",
	Build: FunctorDef.Entry().Law(Statement{
		Binders: "∀x y z:A. ∀f g:M.",
		Hypotheses: []string{
			"f ∈ category_hom(C, x, y)",
			"g ∈ category_hom(C, y, z)",
		},
		Conclusion: "F.map(C.compose(g, f)) = D.compose(F.map(g), F.map(f))",
	}, func(a *Argument, functorial Fact, x, y, z *Expr[A], f, g *Expr[M], homs Fact) {
		C := a.TermAs[CategoryOps[A, M]]("C")
		a.Show(
			"g follows f, and F carries their composite",
			BySets(
				homs,
				CategoryHomDef.At(C, x, y),
				CategoryHomDef.At(C, y, z),
				FunctorPreservesComposite.Read(functorial).AsFact().At(f, g)))
	}),
})}

// FunctorIdentity — the identity maps form a functor from a category to
// itself: unfolded, its two categories are the hypothesis, and with the
// identity maps applied every other clause says that an object is an
// object, a morphism a morphism, or t = t.
var FunctorIdentity = functorIdentityThm{family.Add(registry.ProofEntry{
	Name:  "FunctorIdentity",
	Key:   "prop_36546b1702dc1d02",
	Build: Category.Law("functor(C, C, mk_functor(λx:A. x, λf:M. f))", Unfold(FunctorDef)),
})}

// FunctorCompose — functors compose: each clause of a functor holds of
// the composite maps because it holds of F and then of G, read at the
// image of an object or a morphism, which F places in the middle
// category. For composites, F.map(f) and F.map(g) compose there, the
// target of the one and the source of the other both being
// F.obj(C.target(f)) = F.obj(C.source(g)).
var FunctorCompose = functorComposeThm{family.Add(registry.ProofEntry{
	Name: "FunctorCompose",
	Key:  "prop_20a1f10e2e0650cf",
	Build: family.Theorem(Statement{
		Binders: "∀C₁:category_ops(A, M). " +
			"∀C₂:category_ops(B, N). " +
			"∀C₃:category_ops(C, D). " +
			"∀F:functor_ops(A, M, B, N). " +
			"∀G:functor_ops(B, N, C, D).",
		Hypotheses: []string{
			"functor(C₁, C₂, F)",
			"functor(C₂, C₃, G)",
		},
		Conclusion: "functor(C₁, C₃, mk_functor(λx:A. G.obj(F.obj(x)), λf:M. G.map(F.map(f))))",
	},
		func(a *Argument, C1, C2, C3, F, G Term, fFunctor, gFunctor Fact) {
			fObjects := FunctorObjectImage.Read(fFunctor).AsFact()
			fEnds := FunctorMapEnds.Read(fFunctor).AsFact()
			fIdentities := FunctorPreservesIdentity.Read(fFunctor).AsFact()
			fComposites := FunctorPreservesComposite.Read(fFunctor).AsFact()
			gObjects := FunctorObjectImage.Read(gFunctor).AsFact()
			gEnds := FunctorMapEnds.Read(gFunctor).AsFact()
			gIdentities := FunctorPreservesIdentity.Read(gFunctor).AsFact()
			gComposites := FunctorPreservesComposite.Read(gFunctor).AsFact()
			a.Do(Simp(Fwd(FunctorDef)), SplitConjAll(
				Case(
					"the source of F is a category",
					By(FunctorSourceCategory.Read(fFunctor))),
				Case(
					"the target of G is a category",
					By(FunctorTargetCategory.Read(gFunctor))),
				Case(
					"objects go to objects: F.obj(x) is an object of the middle category",
					By(fObjects, gObjects)),
				Case(
					"the goal opened alone keeps F and G whole for their clause readings, "+
						"and splits the ends clause in three: morphisms go to morphisms",
					Derive(func(b *Argument) {
						f := b.Fix("f")
						morphism := b.Assume()
						b.Show(
							"G carries the morphism F.map(f) of the middle category",
							By(morphism, fEnds.At(f), gEnds.At(b.Term("F.map(f)"))))
					})),
				Case(
					"the source of a morphism is carried: G carries the source F.obj(C₁.source(f)) of F.map(f)",
					Derive(func(b *Argument) {
						f := b.Fix("f")
						morphism := b.Assume()
						b.Show(
							"G carries the source of F.map(f), which F carries from the source of f",
							By(Normalized, morphism, fEnds.At(f), gEnds.At(b.Term("F.map(f)"))))
					})),
				Case(
					"the target of a morphism is carried: G carries the target F.obj(C₁.target(f)) of F.map(f)",
					Derive(func(b *Argument) {
						f := b.Fix("f")
						morphism := b.Assume()
						b.Show(
							"G carries the target of F.map(f), which F carries from the target of f",
							By(Normalized, morphism, fEnds.At(f), gEnds.At(b.Term("F.map(f)"))))
					})),
				Case(
					"identities are carried: F takes C₁.identity(x) to the identity at the object F.obj(x)",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						object := b.Assume()
						b.Show(
							"through the identity at F.obj(x) in the middle category",
							CalcEq(
								Leg(
									b.Term("G.map(C₂.identity(F.obj(x)))"),
									"F carries the identity at x",
									By(Normalized, object, fIdentities.At(x))),
								FinalLeg(
									"G carries the identity at the object F.obj(x)",
									By(object, fObjects.At(x), gIdentities.At(b.Term("F.obj(x)")))),
							))
					})),
				Case(
					"composites are carried: F.map(f) and F.map(g) compose in the middle category",
					Derive(func(b *Argument) {
						f := b.Fix("f")
						g := b.Fix("g")
						composable := b.Assume()
						images := b.Have(
							"F.map(f) and F.map(g) are morphisms of the middle category",
							"F.map(f) ∈ C₂.morphisms ∧ F.map(g) ∈ C₂.morphisms",
							By(composable, fEnds.At(f), fEnds.At(g)))
						follows := b.Have(
							"F.map(g) follows F.map(f) in the middle category",
							"C₂.target(F.map(f)) = C₂.source(F.map(g))",
							CalcEq(
								Leg(
									b.Term("F.obj(C₁.target(f))"),
									"F carries the target of f",
									By(composable, fEnds.At(f))),
								Leg(
									b.Term("F.obj(C₁.source(g))"),
									"g follows f",
									By(Normalized, composable)),
								FinalLeg(
									"F carries the source of g",
									By(composable, fEnds.At(g))),
							))
						b.Show(
							"through the composite of F.map(g) and F.map(f) in the middle category",
							CalcEq(
								Leg(
									b.Term("G.map(C₂.compose(F.map(g), F.map(f)))"),
									"F carries the composite of f and g",
									By(composable, fComposites.At(f, g))),
								FinalLeg(
									"G carries the composite of F.map(f) and F.map(g)",
									By(images, follows, gComposites.At(b.Term("F.map(f)"), b.Term("F.map(g)")))),
							))
					})),
			))
		}),
})}

// FunctorSetDef — `functor_set(C, D)`: the functors from C to D whose
// maps are normalized, junk off the objects and off the morphisms of C.
// Two functors that agree on C are then equal, which makes the functor
// set the object set of the functor category.
var FunctorSetDef = functorSetDefThm{family.Define(registry.DefEntry{
	Name:  "FunctorSetDef",
	Key:   "prop_100ca237b8a533d7",
	Const: "functor_set",
	Type:  "category_ops(A, M) → category_ops(B, N) → set(functor_ops(A, M, B, N))",
	Equations: []string{
		"∀C:category_ops(A, M). ∀D:category_ops(B, N). " +
			"    functor_set(C, D) = " +
			"    {F:functor_ops(A, M, B, N) | " +
			"        functor(C, D, F) ∧ " +
			"        F = " +
			"        mk_functor(normalize_on(C.objects, junk, F.obj), normalize_on(C.morphisms, junk, F.map))}",
	},
	Deps: []registry.EntryLike{
		FunctorDef,
		CategoryObjectsDef,
		CategoryMorphismsDef,
		FunctorObjDef,
		FunctorMapDef,
	},
	Reading: "The normalization is the second conjunct: a functor is in " +
		"the set exactly when both its maps take junk off C's carriers. Where C " +
		"is no category the set is empty, since functor(C, D, F) asks category(C).",
})}

// FunctorSetFunctor — a normalized functor is a functor.
var FunctorSetFunctor = functorSetFunctorThm{family.Add(registry.ProofEntry{
	Name: "FunctorSetFunctor",
	Key:  "prop_43354f86254c6705",
	Build: family.Theorem(Statement{
		Binders: "∀C:category_ops(A, M). ∀D:category_ops(B, N). ∀F:functor_ops(A, M, B, N).",
		Hypotheses: []string{
			"F ∈ functor_set(C, D)",
		},
		Conclusion: "functor(C, D, F)",
	}, func(
		a *Argument,
		C *Expr[CategoryOps[A, M]],
		D *Expr[CategoryOps[B, N]],
		F *Expr[FunctorOps[A, M, B, N]],
		member Fact,
	) {
		a.Show(
			"the functor set holds functors",
			BySets(member, FunctorSetDef.At(C, D)))
	}),
})}

// NormalizedFunctorSet — a functor normalized off the carriers of its
// source is a normalized functor: on the carriers the normalized maps
// take the values of the functor, so every clause of a functor is
// kept, and normalizing them again changes nothing.
var NormalizedFunctorSet = normalizedFunctorSetThm{family.Add(registry.ProofEntry{
	Name: "NormalizedFunctorSet",
	Key:  "prop_2c15b34c226372a3",
	Build: family.Theorem(Statement{
		Binders: "∀C:category_ops(A, M). ∀D:category_ops(B, N). ∀o:(A → B). ∀m:(M → N).",
		Hypotheses: []string{
			"functor(C, D, mk_functor(o, m))",
		},
		Conclusion: "mk_functor(normalize_on(C.objects, junk, o), normalize_on(C.morphisms, junk, m)) ∈ " +
			"functor_set(C, D)",
	}, func(
		a *Argument,
		C *Expr[CategoryOps[A, M]],
		D *Expr[CategoryOps[B, N]],
		o *Arrow[A, B],
		m *Arrow[M, N],
		raw Fact,
	) {
		catC := FunctorSourceCategory.Read(raw)
		catD := FunctorTargetCategory.Read(raw)
		objects := a.TermAs[Set[A]]("C.objects")
		morphisms := a.TermAs[Set[M]]("C.morphisms")
		junkObject := a.TermAs[B]("junk")
		junkMorphism := a.TermAs[N]("junk")
		isFunctor := a.Have(
			"the normalized maps keep every clause of a functor",
			"functor(C, D, mk_functor(normalize_on(C.objects, junk, o), normalize_on(C.morphisms, junk, m)))",
			Simp(Fwd(FunctorDef)),
			SplitConjAll(
				Case(
					"C is the source category",
					By(catC)),
				Case(
					"D is the target category",
					By(catD)),
				Case(
					"the normalized object map takes the value of o on an object",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						b.Show(
							"o carries the object to an object",
							By(
								Normalized,
								FunctorObjectImage.Read(raw).AsFact().At(x),
								functions.NormalizeOnIn.At(objects, junkObject, o, x)))
					})),
				Case(
					"the normalized morphism map takes the value of m on a morphism",
					Derive(func(b *Argument) {
						f := b.FixAs[M]("f")
						b.Show(
							"m carries the morphism to a morphism",
							By(
								Normalized,
								FunctorMapEnds.Read(raw).AsFact().At(f),
								functions.NormalizeOnIn.At(morphisms, junkMorphism, m, f)))
					})),
				Case(
					"the source of a morphism is carried",
					Derive(func(b *Argument) {
						f := b.FixAs[M]("f")
						b.Show(
							"the normalized maps take the values of m at f and of o at its source",
							By(
								FunctorMapEnds.Read(raw).AsFact().At(f),
								MorphismEnds.Read(catC).AsFact().At(f),
								functions.NormalizeOnIn.At(morphisms, junkMorphism, m, f),
								functions.NormalizeOnIn.At(objects, junkObject, o, b.TermAs[A]("C.source(f)"))))
					})),
				Case(
					"the target of a morphism is carried",
					Derive(func(b *Argument) {
						f := b.FixAs[M]("f")
						b.Show(
							"the normalized maps take the values of m at f and of o at its target",
							By(
								FunctorMapEnds.Read(raw).AsFact().At(f),
								MorphismEnds.Read(catC).AsFact().At(f),
								functions.NormalizeOnIn.At(morphisms, junkMorphism, m, f),
								functions.NormalizeOnIn.At(objects, junkObject, o, b.TermAs[A]("C.target(f)"))))
					})),
				Case(
					"identities are carried",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						b.Show(
							"the normalized maps take the values of m at the identity and of o at x",
							By(
								FunctorPreservesIdentity.Read(raw).AsFact().At(x),
								IdentityMorphism.Read(catC).AsFact().At(x),
								functions.NormalizeOnIn.At(morphisms, junkMorphism, m, b.TermAs[M]("C.identity(x)")),
								functions.NormalizeOnIn.At(objects, junkObject, o, x)))
					})),
				Case(
					"composites are carried",
					Derive(func(b *Argument) {
						f := b.FixAs[M]("f")
						g := b.FixAs[M]("g")
						b.Show(
							"the normalized morphism map takes the values of m at f, at g and at their composite",
							By(
								FunctorPreservesComposite.Read(raw).AsFact().At(f, g),
								CompositeMorphism.Read(catC).AsFact().At(f, g),
								functions.NormalizeOnIn.At(morphisms, junkMorphism, m, b.TermAs[M]("C.compose(g, f)")),
								functions.NormalizeOnIn.At(morphisms, junkMorphism, m, f),
								functions.NormalizeOnIn.At(morphisms, junkMorphism, m, g)))
					}))))
		a.Show(
			"normalizing either map again changes nothing, so the functor is in the functor set",
			Simp(Fwd(FunctorSetDef), Fwd(FunctorObjDef), Fwd(FunctorMapDef)),
			By(
				isFunctor,
				functions.NormalizeOnIdempotent.At(objects, junkObject, o),
				functions.NormalizeOnIdempotent.At(morphisms, junkMorphism, m)))
	}),
})}
