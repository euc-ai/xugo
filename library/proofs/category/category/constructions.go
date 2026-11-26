// constructions.go — the constructions on categories: the opposite, the
// same objects and morphisms with source and target exchanged and the
// composite read the other way, kept on the category's own record type;
// the inverse of an isomorphism and the relation of being isomorphic;
// and the identity functor and the composite of two functors,
// normalized off the carriers of their source so that they are elements
// of the functor sets.

package category

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The opposite category
// ---------------------------------------------------------------------------

// OppositeCategoryDef — `opposite_category(C)`: the objects and the
// morphisms of C, the source and target exchanged, and g after f read
// as f after g in C.
var OppositeCategoryDef = oppositeCategoryDefThm{family.Define(registry.DefEntry{
	Name:  "OppositeCategoryDef",
	Key:   "prop_e0511453e57ea210",
	Const: "opposite_category",
	Type:  "category_ops(A, M) → category_ops(A, M)",
	Equations: []string{
		"∀C:category_ops(A, M). " +
			"    opposite_category(C) = " +
			"    mk_category(C.objects, " +
			"        C.morphisms, " +
			"        C.target, " +
			"        C.source, " +
			"        C.identity, " +
			"        λg:M. λf:M. C.compose(f, g))",
	},
	Deps: []registry.EntryLike{
		CategoryObjectsDef,
		CategoryMorphismsDef,
		CategorySourceDef,
		CategoryTargetDef,
		CategoryIdentityDef,
		CategoryComposeDef,
	},
	Reading: "The opposite keeps the morphism type of C, so a functor C → D is the same record " +
		"as a functor between the opposites, and opposite_category(opposite_category(C)) = C as records.",
})}

// ---------------------------------------------------------------------------
// Isomorphisms and inverses
// ---------------------------------------------------------------------------

// CategoryIsomorphicDef — `category_isomorphic(C, x, y)`: there is an
// isomorphism of C from x to y.
var CategoryIsomorphicDef = categoryIsomorphicDefThm{family.Define(registry.DefEntry{
	Name:  "CategoryIsomorphicDef",
	Key:   "prop_aa12dc8c3d84cad8",
	Const: "category_isomorphic",
	Type:  "category_ops(A, M) → A → A → bool",
	Equations: []string{
		"∀C:category_ops(A, M). ∀x y:A. " +
			"    category_isomorphic(C, x, y) ⇔ ∃f:M. f ∈ category_hom(C, x, y) ∧ category_isomorphism(C, f)",
	},
	Deps: []registry.EntryLike{CategoryHomDef, CategoryIsomorphismDef},
})}

// CategoryInverseDef — `category_inverse(C, f)`: a two-sided inverse of
// f, chosen.
var CategoryInverseDef = categoryInverseDefThm{family.Define(registry.DefEntry{
	Name:  "CategoryInverseDef",
	Key:   "prop_cf39e12e568d49f7",
	Const: "category_inverse",
	Type:  "category_ops(A, M) → M → M",
	Equations: []string{
		"∀C:category_ops(A, M). ∀f:M. " +
			"    category_inverse(C, f) = " +
			"    εg:M. " +
			"        g ∈ C.morphisms ∧ " +
			"        C.source(g) = C.target(f) ∧ " +
			"        C.target(g) = C.source(f) ∧ " +
			"        C.compose(g, f) = C.identity(C.source(f)) ∧ " +
			"        C.compose(f, g) = C.identity(C.target(f))",
	},
	Deps: []registry.EntryLike{
		CategoryMorphismsDef,
		CategorySourceDef,
		CategoryTargetDef,
		CategoryIdentityDef,
		CategoryComposeDef,
	},
	Reading: "The choice is controlled only where f is an isomorphism; " +
		"there the inverse is unique (InverseUnique), so the choice is the inverse.",
})}

// InverseIsomorphism — the chosen inverse of an isomorphism is a
// two-sided inverse with the ends exchanged, and an isomorphism itself:
// inverse existence controls the choice, and f inverts the chosen inverse.
// It is stated under the structure beside the other laws of a category;
// the argument reads the choice alone and holds in any record.
var InverseIsomorphism = inverseIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "InverseIsomorphism",
	Key:  "prop_f0461beafcf7a6e6",
	Build: Category.Law(Statement{
		Binders: "∀f:M.",
		Hypotheses: []string{
			"category_isomorphism(C, f)",
		},
		Conclusion: "category_inverse(C, f) ∈ C.morphisms ∧ " +
			"C.source(category_inverse(C, f)) = C.target(f) ∧ " +
			"C.target(category_inverse(C, f)) = C.source(f) ∧ " +
			"C.compose(category_inverse(C, f), f) = C.identity(C.source(f)) ∧ " +
			"C.compose(f, category_inverse(C, f)) = C.identity(C.target(f)) ∧ " +
			"category_isomorphism(C, category_inverse(C, f))",
	}, func(a *Argument, _ Fact, f *Expr[M], iso Fact) {
		data := a.Conjuncts(
			a.Unfolded(iso, CategoryIsomorphismDef),
			"f is a morphism",
			"f has a two-sided inverse with exchanged endpoints")
		chosen := a.Have(
			"the choice satisfies the inverse condition",
			"category_inverse(C, f) ∈ C.morphisms ∧ "+
				"C.source(category_inverse(C, f)) = C.target(f) ∧ "+
				"C.target(category_inverse(C, f)) = C.source(f) ∧ "+
				"C.compose(category_inverse(C, f), f) = C.identity(C.source(f)) ∧ "+
				"C.compose(f, category_inverse(C, f)) = C.identity(C.target(f))",
			Unfold(CategoryInverseDef))
		inverseIso := a.Have(
			"f is an inverse of the chosen inverse",
			"category_isomorphism(C, category_inverse(C, f))",
			Simp(Fwd(CategoryIsomorphismDef)),
			SplitConj(
				Case(
					"the chosen inverse is a morphism",
					By(chosen)),
				Case(
					"f supplies the inverse with the endpoints exchanged",
					Witness(f),
					By(Normalized, data[0], chosen))))
		a.Show(
			"the chosen inverse has all the asserted properties",
			By(chosen, inverseIso))
	}),
})}

// InverseHom — the chosen inverse of an isomorphism from x to y lies in
// the hom set from y to x and inverts it on both sides:
// InverseIsomorphism read through the hom sets.
var InverseHom = inverseHomThm{family.Add(registry.ProofEntry{
	Name: "InverseHom",
	Key:  "prop_4aa99f86076ddded",
	Build: Category.Law(Statement{
		Binders: "∀x y:A. ∀f:M.",
		Hypotheses: []string{
			"f ∈ category_hom(C, x, y)",
			"category_isomorphism(C, f)",
		},
		Conclusion: "category_inverse(C, f) ∈ category_hom(C, y, x) ∧ " +
			"C.compose(category_inverse(C, f), f) = C.identity(x) ∧ " +
			"C.compose(f, category_inverse(C, f)) = C.identity(y)",
	},
		func(a *Argument, category Fact, x, y *Expr[A], f *Expr[M], premises Fact) {
			C := a.TermAs[CategoryOps[A, M]]("C")
			a.Show(
				"the inverse has the reversed ends and the two inverse equations",
				BySets(
					premises,
					CategoryHomDef.At(C, x, y),
					CategoryHomDef.At(C, y, x),
					InverseIsomorphism.Read(category).AsFact().At(f)))
		}),
})}

// CancelInverseLeft — the inverse of an isomorphism h undoes composition
// with h on the left: h⁻¹ ∘ (h ∘ f) = (h⁻¹ ∘ h) ∘ f = f.
var CancelInverseLeft = cancelInverseLeftThm{family.Add(registry.ProofEntry{
	Name: "CancelInverseLeft",
	Key:  "prop_2b070e88b7cc1c87",
	Build: Category.Law(Statement{
		Binders: "∀x y z:A. ∀f h:M.",
		Hypotheses: []string{
			"f ∈ category_hom(C, x, y)",
			"h ∈ category_hom(C, y, z)",
			"category_isomorphism(C, h)",
		},
		Conclusion: "C.compose(category_inverse(C, h), C.compose(h, f)) = f",
	},
		func(a *Argument, category Fact, x, y, z *Expr[A], f, h *Expr[M], premises Fact) {
			inverse := a.Conjuncts(
				GroupPremises(category, premises, InverseHom.At(a.TermAs[CategoryOps[A, M]]("C"), y, z, h)),
				"the inverse of h runs from z to y",
				"h⁻¹ ∘ h is the identity at y",
				"h ∘ h⁻¹ is the identity at z")
			a.Show(
				"reassociated, h⁻¹ ∘ h is the identity at y, a left unit on f",
				Simp(
					Fwd(category),
					Fwd(AssocHom),
					Fwd(inverse[0]),
					Fwd(inverse[1]),
					Fwd(premises),
					Fwd(LeftUnitHom)),
				Basic())
		}),
})}

// CancelInverseRight — the inverse of an isomorphism h undoes composition
// with h on the right: (f ∘ h) ∘ h⁻¹ = f ∘ (h ∘ h⁻¹) = f.
var CancelInverseRight = cancelInverseRightThm{family.Add(registry.ProofEntry{
	Name: "CancelInverseRight",
	Key:  "prop_cbfb3860e707f5a7",
	Build: Category.Law(Statement{
		Binders: "∀x y z:A. ∀f h:M.",
		Hypotheses: []string{
			"h ∈ category_hom(C, x, y)",
			"f ∈ category_hom(C, y, z)",
			"category_isomorphism(C, h)",
		},
		Conclusion: "C.compose(C.compose(f, h), category_inverse(C, h)) = f",
	},
		func(a *Argument, category Fact, x, y, z *Expr[A], f, h *Expr[M], premises Fact) {
			inverse := a.Conjuncts(
				GroupPremises(category, premises, InverseHom.At(a.TermAs[CategoryOps[A, M]]("C"), x, y, h)),
				"the inverse of h runs from y to x",
				"h⁻¹ ∘ h is the identity at x",
				"h ∘ h⁻¹ is the identity at y")
			a.Show(
				"reassociated, h ∘ h⁻¹ is the identity at y, a right unit on f",
				Simp(
					Fwd(category),
					Rev(AssocHom),
					Fwd(inverse[0]),
					Fwd(inverse[2]),
					Fwd(premises),
					Fwd(RightUnitHom)),
				Basic())
		}),
})}

// CancelIsomorphismLeft — an isomorphism h undoes composition with its
// inverse on the left: h ∘ (h⁻¹ ∘ f) = (h ∘ h⁻¹) ∘ f = f.
var CancelIsomorphismLeft = cancelIsomorphismLeftThm{family.Add(registry.ProofEntry{
	Name: "CancelIsomorphismLeft",
	Key:  "prop_3cca83b3d6465466",
	Build: Category.Law(Statement{
		Binders: "∀x y z:A. ∀f h:M.",
		Hypotheses: []string{
			"f ∈ category_hom(C, x, z)",
			"h ∈ category_hom(C, y, z)",
			"category_isomorphism(C, h)",
		},
		Conclusion: "C.compose(h, C.compose(category_inverse(C, h), f)) = f",
	},
		func(a *Argument, category Fact, x, y, z *Expr[A], f, h *Expr[M], premises Fact) {
			inverse := a.Conjuncts(
				GroupPremises(category, premises, InverseHom.At(a.TermAs[CategoryOps[A, M]]("C"), y, z, h)),
				"the inverse of h runs from z to y",
				"h⁻¹ ∘ h is the identity at y",
				"h ∘ h⁻¹ is the identity at z")
			a.Show(
				"reassociated, h ∘ h⁻¹ is the identity at z, a left unit on f",
				Simp(
					Fwd(category),
					Fwd(AssocHom),
					Fwd(inverse[0]),
					Fwd(inverse[2]),
					Fwd(premises),
					Fwd(LeftUnitHom)),
				Basic())
		}),
})}

// IsomorphismMonic — an isomorphism is monic: h ∘ f = h ∘ g gives f = g,
// both being h⁻¹ ∘ (h ∘ −) (CancelInverseLeft).
var IsomorphismMonic = isomorphismMonicThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismMonic",
	Key:  "prop_7fe29a69d9390553",
	Build: Category.Law(Statement{
		Binders: "∀x y z:A. ∀f g h:M.",
		Hypotheses: []string{
			"f ∈ category_hom(C, x, y)",
			"g ∈ category_hom(C, x, y)",
			"h ∈ category_hom(C, y, z)",
			"category_isomorphism(C, h)",
			"C.compose(h, f) = C.compose(h, g)",
		},
		Conclusion: "f = g",
	},
		func(a *Argument, category Fact, x, y, z *Expr[A], f, g, h *Expr[M], premises Fact) {
			C := a.TermAs[CategoryOps[A, M]]("C")
			a.Show(
				"h⁻¹ undoes h on both sides of the equation",
				By(
					category,
					premises,
					CancelInverseLeft.At(C, x, y, z, f, h),
					CancelInverseLeft.At(C, x, y, z, g, h)))
		}),
})}

// IsomorphismEpic — an isomorphism is epic: f ∘ h = g ∘ h gives f = g,
// both being (− ∘ h) ∘ h⁻¹ (CancelInverseRight).
var IsomorphismEpic = isomorphismEpicThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismEpic",
	Key:  "prop_e52438278d13d017",
	Build: Category.Law(Statement{
		Binders: "∀x y z:A. ∀f g h:M.",
		Hypotheses: []string{
			"h ∈ category_hom(C, x, y)",
			"f ∈ category_hom(C, y, z)",
			"g ∈ category_hom(C, y, z)",
			"category_isomorphism(C, h)",
			"C.compose(f, h) = C.compose(g, h)",
		},
		Conclusion: "f = g",
	},
		func(a *Argument, category Fact, x, y, z *Expr[A], f, g, h *Expr[M], premises Fact) {
			C := a.TermAs[CategoryOps[A, M]]("C")
			a.Show(
				"h⁻¹ undoes h on both sides of the equation",
				By(
					category,
					premises,
					CancelInverseRight.At(C, x, y, z, f, h),
					CancelInverseRight.At(C, x, y, z, g, h)))
		}),
})}

// ---------------------------------------------------------------------------
// Identity and composite functors
// ---------------------------------------------------------------------------

// IdentityFunctorDef — `identity_functor(C)`: the identity maps,
// normalized with junk off the carriers of C.
var IdentityFunctorDef = identityFunctorDefThm{family.Define(registry.DefEntry{
	Name:  "IdentityFunctorDef",
	Key:   "prop_69b1ba225a3fa34b",
	Const: "identity_functor",
	Type:  "category_ops(A, M) → functor_ops(A, M, A, M)",
	Equations: []string{
		"∀C:category_ops(A, M). " +
			"    identity_functor(C) = " +
			"    mk_functor(normalize_on(C.objects, junk, λx:A. x), normalize_on(C.morphisms, junk, λf:M. f))",
	},
	Deps: []registry.EntryLike{CategoryObjectsDef, CategoryMorphismsDef},
})}

// FunctorComposeDef — `functor_compose(C, G, F)`: G after F, normalized
// with junk off the carriers of C, the source of F. A composite of two
// normalized maps is normalized only on C, so the normalization is done
// again.
var FunctorComposeDef = functorComposeDefThm{family.Define(registry.DefEntry{
	Name:  "FunctorComposeDef",
	Key:   "prop_e4787c01c69f1577",
	Const: "functor_compose",
	Type: "category_ops(A, M) → " +
		"functor_ops(B, N, U, Z) → " +
		"functor_ops(A, M, B, N) → " +
		"functor_ops(A, M, U, Z)",
	Equations: []string{
		"∀C:category_ops(A, M). ∀G:functor_ops(B, N, U, Z). ∀F:functor_ops(A, M, B, N). " +
			"    functor_compose(C, G, F) = " +
			"    mk_functor(normalize_on(C.objects, junk, G.obj ∘ F.obj), " +
			"        normalize_on(C.morphisms, junk, G.map ∘ F.map))",
	},
	Deps: []registry.EntryLike{CategoryObjectsDef, CategoryMorphismsDef},
})}

// IdentityFunctorApply — on the objects and the morphisms of C the
// identity functor is the identity: the normalization keeps the values
// on the carriers.
var IdentityFunctorApply = identityFunctorApplyThm{family.Add(registry.ProofEntry{
	Name: "IdentityFunctorApply",
	Key:  "prop_7c1d45ec6114a83e",
	Build: family.Theorem(Statement{
		Binders: "∀C:category_ops(A, M).",
		Conclusion: "(∀x:A. x ∈ C.objects ⇒ identity_functor(C).obj(x) = x) ∧ " +
			"(∀f:M. f ∈ C.morphisms ⇒ identity_functor(C).map(f) = f)",
	}, func(a *Argument, C *Expr[CategoryOps[A, M]]) {
		a.Do(SplitConj(
			Case(
				"an object is its own image",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					object := b.Assume()
					b.Show(
						"the normalized identity keeps the value at an object",
						Simp(Fwd(object), Fwd(IdentityFunctorDef), Fwd(FunctorObjDef), Fwd(functions.NormalizeOnIn)),
						Basic())
				})),
			Case(
				"a morphism is its own image",
				Derive(func(b *Argument) {
					b.FixAs[M]("f")
					morphism := b.Assume()
					b.Show(
						"the normalized identity keeps the value at a morphism",
						Simp(Fwd(morphism), Fwd(IdentityFunctorDef), Fwd(FunctorMapDef), Fwd(functions.NormalizeOnIn)),
						Basic())
				}))))
	}),
})}

// FunctorComposeApply — on the objects and the morphisms of C the
// composite functor is G after F: the normalization keeps the values on
// the carriers.
var FunctorComposeApply = functorComposeApplyThm{family.Add(registry.ProofEntry{
	Name: "FunctorComposeApply",
	Key:  "prop_ab4d9b5e16d8ff79",
	Build: family.Theorem(Statement{
		Binders: "∀C:category_ops(A, M). ∀G:functor_ops(B, N, U, Z). ∀F:functor_ops(A, M, B, N).",
		Conclusion: "(∀x:A. x ∈ C.objects ⇒ functor_compose(C, G, F).obj(x) = G.obj(F.obj(x))) ∧ " +
			"(∀f:M. f ∈ C.morphisms ⇒ functor_compose(C, G, F).map(f) = G.map(F.map(f)))",
	}, func(
		a *Argument,
		C *Expr[CategoryOps[A, M]],
		G *Expr[FunctorOps[B, N, U, Z]],
		F *Expr[FunctorOps[A, M, B, N]],
	) {
		a.Do(SplitConj(
			Case(
				"an object goes to its image under F, then under G",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					object := b.Assume()
					b.Show(
						"the normalized composite keeps the value at an object",
						Simp(
							Fwd(object),
							Fwd(FunctorComposeDef),
							Fwd(FunctorObjDef),
							Fwd(functions.NormalizeOnIn),
							Fwd(functions.ComposeApply)),
						Basic())
				})),
			Case(
				"a morphism goes to its image under F, then under G",
				Derive(func(b *Argument) {
					b.FixAs[M]("f")
					morphism := b.Assume()
					b.Show(
						"the normalized composite keeps the value at a morphism",
						Simp(
							Fwd(morphism),
							Fwd(FunctorComposeDef),
							Fwd(FunctorMapDef),
							Fwd(functions.NormalizeOnIn),
							Fwd(functions.ComposeApply)),
						Basic())
				}))))
	}),
})}

// IdentityFunctorSet — the identity functor is a normalized functor:
// the identity maps form a functor (FunctorIdentity), normalized off the
// carriers of C (NormalizedFunctorSet).
var IdentityFunctorSet = identityFunctorSetThm{family.Add(registry.ProofEntry{
	Name: "IdentityFunctorSet",
	Key:  "prop_47ced71931961479",
	Build: Category.Law("identity_functor(C) ∈ functor_set(C, C)",
		func(a *Argument, cat Fact) {
			C := a.TermAs[CategoryOps[A, M]]("C")
			a.Show(
				"the identity functor is the identity maps normalized off the carriers of C",
				Simp(Fwd(IdentityFunctorDef)),
				By(
					FunctorIdentity.Read(cat),
					NormalizedFunctorSet.At(C, C, a.TermAs[Fun[A, A]]("λx:A. x"), a.TermAs[Fun[M, M]]("λf:M. f"))))
		}),
})}

// FunctorComposeSet — the normalized composite of two functors is a
// normalized functor: the pointwise composite maps form a functor
// (FunctorCompose), normalized off the carriers of C
// (NormalizedFunctorSet).
var FunctorComposeSet = functorComposeSetThm{family.Add(registry.ProofEntry{
	Name: "FunctorComposeSet",
	Key:  "prop_870f5ce6798022dd",
	Build: family.Theorem(Statement{
		Binders: "∀C:category_ops(A, M). " +
			"∀D:category_ops(B, N). " +
			"∀E:category_ops(U, Z). " +
			"∀F:functor_ops(A, M, B, N). " +
			"∀G:functor_ops(B, N, U, Z).",
		Hypotheses: []string{
			"functor(C, D, F)",
			"functor(D, E, G)",
		},
		Conclusion: "functor_compose(C, G, F) ∈ functor_set(C, E)",
	}, func(
		a *Argument,
		C *Expr[CategoryOps[A, M]],
		D *Expr[CategoryOps[B, N]],
		E *Expr[CategoryOps[U, Z]],
		F *Expr[FunctorOps[A, M, B, N]],
		G *Expr[FunctorOps[B, N, U, Z]],
		functors Fact,
	) {
		a.Show(
			"the composite is the pointwise composite maps normalized off the carriers of C",
			Simp(Fwd(FunctorComposeDef), Fwd(functions.ComposeApply)),
			By(
				functors,
				FunctorCompose.At(C, D, E, F, G),
				NormalizedFunctorSet.At(
					C, E, a.TermAs[Fun[A, U]]("λx:A. G.obj(F.obj(x))"), a.TermAs[Fun[M, Z]]("λf:M. G.map(F.map(f))"))))
	}),
})}

// IdentityFunctorFunctor — the identity functor of a category is a
// functor: it is a normalized functor (IdentityFunctorSet).
var IdentityFunctorFunctor = identityFunctorFunctorThm{family.Add(registry.ProofEntry{
	Name: "IdentityFunctorFunctor",
	Key:  "prop_5d2a6f5acb578493",
	Build: Category.Law("functor(C, C, identity_functor(C))",
		func(a *Argument, cat Fact) {
			C := a.TermAs[CategoryOps[A, M]]("C")
			a.Show(
				"the identity functor is in the functor set",
				By(
					IdentityFunctorSet.Read(cat),
					FunctorSetFunctor.At(C, C, a.TermAs[FunctorOps[A, M, A, M]]("identity_functor(C)"))))
		}),
})}

// FunctorComposeFunctor — the normalized composite of two functors is a
// functor: it is a normalized functor (FunctorComposeSet).
var FunctorComposeFunctor = functorComposeFunctorThm{family.Add(registry.ProofEntry{
	Name: "FunctorComposeFunctor",
	Key:  "prop_26f8f8d867903bff",
	Build: family.Theorem(Statement{
		Binders: "∀C:category_ops(A, M). " +
			"∀D:category_ops(B, N). " +
			"∀E:category_ops(U, Z). " +
			"∀F:functor_ops(A, M, B, N). " +
			"∀G:functor_ops(B, N, U, Z).",
		Hypotheses: []string{
			"functor(C, D, F)",
			"functor(D, E, G)",
		},
		Conclusion: "functor(C, E, functor_compose(C, G, F))",
	}, func(
		a *Argument,
		C *Expr[CategoryOps[A, M]],
		D *Expr[CategoryOps[B, N]],
		E *Expr[CategoryOps[U, Z]],
		F *Expr[FunctorOps[A, M, B, N]],
		G *Expr[FunctorOps[B, N, U, Z]],
		functors Fact,
	) {
		a.Show(
			"the normalized composite is in the functor set",
			By(
				functors,
				FunctorComposeSet.At(C, D, E, F, G),
				FunctorSetFunctor.At(C, E, a.TermAs[FunctorOps[A, M, U, Z]]("functor_compose(C, G, F)"))))
	}),
})}
