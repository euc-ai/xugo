// yoneda.go — the Yoneda lemma. A family α assigning to each object x
// of C and each morphism g: x → c an element α(x, g) of P(x), natural
// in x, is determined by the one element α(c, 1_c), and every element of
// P(c) arises: the inverse sends u to the family g ↦ P(g)(u). The
// presheaf P is valued in the subsets of any type.

package yoneda

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/category/set_category"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// A presheaf here is valued in the subsets of a type B, its maps framed
// maps of B, and a family assigns to an object x and a morphism into c an
// element of B.
type (
	setArrow  = MorphismTriple[Set[B], Fun[B, B]]
	presheaf  = FunctorOps[A, M, Set[B], setArrow]
	familyMap = Fun[A, Fun[M, B]]
)

// ---------------------------------------------------------------------------
// The lemma, in its element form
// ---------------------------------------------------------------------------

// yonedaFamilyDef — `yoneda_family(C, c, P, α)`: α(x, g) lies in P(x)
// for every morphism g: x → c, and α is natural in x: precomposing g
// with f: y → x is acting by P(f).
var yonedaFamilyDef = yonedaFamilyDefThm{family.Define(registry.DefEntry{
	Name:  "yonedaFamilyDef",
	Key:   "prop_c07ad16cc17ff7e6",
	Const: "yoneda_family",
	Type: "category_ops(A, M) → " +
		"A → " +
		"functor_ops(A, M, set(B), morphism_triple(set(B), B → B)) → " +
		"(A → M → B) → " +
		"bool",
	Equations: []string{
		"∀C:category_ops(A, M). " +
			"∀c:A. " +
			"∀P:functor_ops(A, M, set(B), morphism_triple(set(B), B → B)). " +
			"∀α:(A → M → B). " +
			"    yoneda_family(C, c, P, α) ⇔ " +
			"    (∀x:A. ∀g:M. x ∈ C.objects ∧ g ∈ category_hom(C, x, c) ⇒ α(x, g) ∈ P.obj(x)) ∧ " +
			"    (∀x y:A. ∀g f:M. " +
			"        g ∈ category_hom(C, x, c) ∧ f ∈ category_hom(C, y, x) ⇒ " +
			"        α(y, C.compose(g, f)) = P.map(f).map(α(x, g)))",
	},
	Reading: "P is read as a functor on the opposite of C: " +
		"P.map(f) for f: y → x is the map of sets from P(x) to P(y).",
})}

// yonedaFamilySetDef — `yoneda_family_set(C, c, P)`: the natural
// families, normalized with junk off the objects of C and off each hom
// set.
var yonedaFamilySetDef = yonedaFamilySetDefThm{family.Define(registry.DefEntry{
	Name:  "yonedaFamilySetDef",
	Key:   "prop_bd91c40cca57591b",
	Const: "yoneda_family_set",
	Type: "category_ops(A, M) → " +
		"A → " +
		"functor_ops(A, M, set(B), morphism_triple(set(B), B → B)) → " +
		"set(A → M → B)",
	Equations: []string{
		"∀C:category_ops(A, M). ∀c:A. ∀P:functor_ops(A, M, set(B), morphism_triple(set(B), B → B)). " +
			"    yoneda_family_set(C, c, P) = " +
			"    {α:(A → M → B) | " +
			"        yoneda_family(C, c, P, α) ∧ " +
			"        α = " +
			"        normalize_on(C.objects, " +
			"            λg:M. junk, " +
			"            λx:A. normalize_on(category_hom(C, x, c), junk, α(x)))}",
	},
	Deps: []registry.EntryLike{yonedaFamilyDef},
})}

// yonedaElementDef — `yoneda_element(C, c, α)`: the family at the
// identity of c.
var yonedaElementDef = yonedaElementDefThm{family.Define(registry.DefEntry{
	Name:  "yonedaElementDef",
	Key:   "prop_2b5b49f9ecf8a16",
	Const: "yoneda_element",
	Type:  "category_ops(A, M) → A → (A → M → B) → B",
	Equations: []string{
		"∀C:category_ops(A, M). ∀c:A. ∀α:(A → M → B). yoneda_element(C, c, α) = α(c, C.identity(c))",
	},
})}

// yonedaInverseDef — `yoneda_inverse(C, c, P, u)`: the family that sends
// g: x → c to P(g) applied to u, normalized.
var yonedaInverseDef = yonedaInverseDefThm{family.Define(registry.DefEntry{
	Name:  "yonedaInverseDef",
	Key:   "prop_ea460df51f47f407",
	Const: "yoneda_inverse",
	Type: "category_ops(A, M) → " +
		"A → " +
		"functor_ops(A, M, set(B), morphism_triple(set(B), B → B)) → " +
		"B → " +
		"A → " +
		"M → " +
		"B",
	Equations: []string{
		"∀C:category_ops(A, M). " +
			"∀c:A. " +
			"∀P:functor_ops(A, M, set(B), morphism_triple(set(B), B → B)). " +
			"∀u:B. " +
			"    yoneda_inverse(C, c, P, u) = " +
			"    normalize_on(C.objects, " +
			"        λg:M. junk, " +
			"        λx:A. normalize_on(category_hom(C, x, c), junk, λg:M. P.map(g).map(u)))",
	},
})}

// YonedaFamilyFromElement — a natural family is determined by its
// element: α(x, g) = P(g)(α(c, 1_c)), naturality read at the identity of
// c and the morphism g, since 1_c ∘ g = g.
var YonedaFamilyFromElement = yonedaFamilyFromElementThm{family.Add(registry.ProofEntry{
	Name: "YonedaFamilyFromElement",
	Key:  "prop_1c5a016ade0b7390",
	Build: family.Theorem(Statement{
		Binders: "∀C:category_ops(A, M). " +
			"∀c:A. " +
			"∀P:functor_ops(A, M, set(B), morphism_triple(set(B), B → B)). " +
			"∀α:(A → M → B). " +
			"∀x:A. " +
			"∀g:M.",
		Hypotheses: []string{
			"category(C)",
			"yoneda_family(C, c, P, α)",
			"g ∈ category_hom(C, x, c)",
		},
		Conclusion: "α(x, g) = P.map(g).map(yoneda_element(C, c, α))",
	}, func(
		a *Argument,
		C *Expr[CategoryOps[A, M]],
		c *Expr[A],
		P *Expr[presheaf],
		α *Expr[familyMap],
		x *Expr[A],
		g *Expr[M],
		cat, natural, gIn Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(natural, yonedaFamilyDef),
			"the values lie in P",
			"precomposition acts by P")
		object := a.Have(
			"c is an object, the target of the morphism g",
			"c ∈ C.objects",
			BySets(gIn, category.CategoryHomDef.At(C, x, c), category.MorphismEnds.Read(cat).AsFact().At(g)))
		leftUnit := a.Have(
			"the target identity fixes g",
			"C.compose(C.identity(c), g) = g",
			By(cat, gIn, category.LeftUnitHom.At(C, x, c, g)))
		a.Show(
			"naturality at the identity recovers the value",
			By(
				leftUnit,
				gIn,
				object,
				cat,
				category.IdentityHom.At(C, c),
				laws[1].At(c, x, a.TermAs[M]("C.identity(c)"), g),
				yonedaElementDef.At(C, c, α)))
	}),
})}

// YonedaLemma — natural families are determined by evaluation at the
// identity, and the presheaf action constructs the family of any element.
var YonedaLemma = yonedaLemmaThm{family.Add(registry.ProofEntry{
	Name: "YonedaLemma",
	Key:  "prop_130d33a7ddc85a73",
	Build: family.Sections(Statement{
		Binders: "∀C:category_ops(A, M). " +
			"∀c:A. " +
			"∀P:functor_ops(A, M, set(B), morphism_triple(set(B), B → B)).",
		Hypotheses: []string{
			"category(C)",
			"c ∈ C.objects",
			"functor(opposite_category(C), set_category, P)",
		},
		Conclusion: "injective_on(yoneda_family_set(C, c, P), yoneda_element(C, c)) ∧ " +
			"image(yoneda_element(C, c), yoneda_family_set(C, c, P)) = P.obj(c) ∧ " +
			"(∀u:B. " +
			"    u ∈ P.obj(c) ⇒ " +
			"    yoneda_inverse(C, c, P, u) ∈ yoneda_family_set(C, c, P) ∧ " +
			"    yoneda_element(C, c, yoneda_inverse(C, c, P, u)) = u)",
	}, func(ctx *Script, headline string) *GoalStackNode {

		inverseValue := ctx.Lemma(Statement{
			Binders: "∀C:category_ops(A, M). " +
				"∀c:A. " +
				"∀P:functor_ops(A, M, set(B), morphism_triple(set(B), B → B)). " +
				"∀u:B. " +
				"∀x:A. " +
				"∀g:M.",
			Hypotheses: []string{
				"x ∈ C.objects",
				"g ∈ category_hom(C, x, c)",
			},
			Conclusion: "yoneda_inverse(C, c, P, u, x, g) = P.map(g).map(u)",
		}, func(
			a *Argument,
			C *Expr[CategoryOps[A, M]],
			c *Expr[A],
			P *Expr[presheaf],
			u *Expr[B],
			x *Expr[A],
			g *Expr[M],
			xIn, gIn Fact,
		) {
			a.Show(
				"both normalizations preserve the value on the carriers",
				Simp(Fwd(xIn), Fwd(gIn), Fwd(yonedaInverseDef), Fwd(functions.NormalizeOnIn)),
				Basic())
		})
		inverseNatural := ctx.Lemma(Statement{
			Binders: "∀C:category_ops(A, M). " +
				"∀c:A. " +
				"∀P:functor_ops(A, M, set(B), morphism_triple(set(B), B → B)). " +
				"∀u:B.",
			Hypotheses: []string{
				"category(C)",
				"functor(opposite_category(C), set_category, P)",
				"u ∈ P.obj(c)",
			},
			Conclusion: "yoneda_family(C, c, P, yoneda_inverse(C, c, P, u))",
		}, func(
			a *Argument,
			C *Expr[CategoryOps[A, M]],
			c *Expr[A],
			P *Expr[presheaf],
			u *Expr[B],
			cat, isPresheaf, uIn Fact,
		) {
			a.Do(Unfold(yonedaFamilyDef))
			a.Do(SplitConj(
				Case(
					"the inverse values lie in P(x)",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						g := b.FixAs[M]("g")
						carriers := b.Assume()
						b.Show(
							"at opposite_category(C) source and target swap, so "+
								"P(g) runs from P(c) to P(x) and carries u into P(x)",
							Simp(Fwd(inverseValue)),
							BySets(
								uIn,
								isPresheaf,
								carriers,
								category.CategoryHomDef.At(C, x, c),
								set_category.SetFunctorMapsInto.At(b.TermAs[CategoryOps[A, M]]("opposite_category(C)"), P, g, u)))
					})),
				Case(
					"precomposition agrees with the presheaf action",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						y := b.FixAs[A]("y")
						g := b.FixAs[M]("g")
						f := b.FixAs[M]("f")
						homs := b.Assume()
						composable := b.Have(
							"the endpoints and composite belong to their carriers",
							"x ∈ C.objects ∧ y ∈ C.objects ∧ C.compose(g, f) ∈ category_hom(C, y, c)",
							BySets(
								homs,
								category.CategoryHomDef.At(C, x, c),
								category.CategoryHomDef.At(C, y, x),
								category.CategoryHomDef.At(C, y, c),
								category.MorphismEnds.Read(cat).AsFact().At(f),
								category.MorphismEnds.Read(cat).AsFact().At(g),
								category.CompositeMorphism.Read(cat).AsFact().At(f, g)))
						b.Show(
							"P turns the composite into successive actions",
							Simp(Fwd(inverseValue), Fwd(composable)),
							BySets(
								uIn,
								isPresheaf,
								homs,
								category.CategoryHomDef.At(C, x, c),
								category.CategoryHomDef.At(C, y, x),
								set_category.SetFunctorComposeValue.At(
									b.TermAs[CategoryOps[A, M]]("opposite_category(C)"), P, g, f, u)))
					}))))
		})
		inverseNormalized := ctx.Lemma(Statement{
			Binders: "∀C:category_ops(A, M). " +
				"∀c:A. " +
				"∀P:functor_ops(A, M, set(B), morphism_triple(set(B), B → B)). " +
				"∀u:B.",
			Conclusion: "yoneda_inverse(C, c, P, u) = " +
				"normalize_on(C.objects, " +
				"    λg:M. junk, " +
				"    λx:A. normalize_on(category_hom(C, x, c), junk, yoneda_inverse(C, c, P, u, x)))",
		}, func(a *Argument, C *Expr[CategoryOps[A, M]], c *Expr[A], P *Expr[presheaf], u *Expr[B]) {
			a.Do(Simp(Fwd(yonedaInverseDef), Fwd(functions.NormalizeOnEqIff)))
			a.FixAs[A]("x")
			a.Assume()
			a.FixAs[M]("g")
			a.Assume()
			a.Show(
				"the normalized inverse retains its carrier values",
				Simp(Fwd(functions.NormalizeOnIn)),
				Basic())
		})
		inverse := ctx.Lemma(Statement{
			Binders: "∀C:category_ops(A, M). " +
				"∀c:A. " +
				"∀P:functor_ops(A, M, set(B), morphism_triple(set(B), B → B)). " +
				"∀u:B.",
			Hypotheses: []string{
				"category(C)",
				"c ∈ C.objects",
				"functor(opposite_category(C), set_category, P)",
				"u ∈ P.obj(c)",
			},
			Conclusion: "yoneda_inverse(C, c, P, u) ∈ yoneda_family_set(C, c, P) ∧ " +
				"yoneda_element(C, c, yoneda_inverse(C, c, P, u)) = u",
		}, func(
			a *Argument,
			C *Expr[CategoryOps[A, M]],
			c *Expr[A],
			P *Expr[presheaf],
			u *Expr[B],
			cat, cIn, isPresheaf, uIn Fact,
		) {
			a.Do(SplitConj(
				Case(
					"the inverse is a normalized natural family",
					BySets(
						cat,
						isPresheaf,
						uIn,
						yonedaFamilySetDef.At(C, c, P),
						At(inverseNatural, C, c, P, u),
						At(inverseNormalized, C, c, P, u))),
				Case(
					"evaluation recovers u",
					Derive(func(b *Argument) {
						identity := b.Have(
							"the identity is an endomorphism of c",
							"C.identity(c) ∈ category_hom(C, c, c)",
							By(cat, cIn, category.IdentityHom.At(C, c)))
						b.Show(
							"P sends the identity to the identity map",
							Simp(Fwd(yonedaElementDef), Fwd(inverseValue), Fwd(identity)),
							By(
								cIn,
								uIn,
								isPresheaf,
								set_category.SetFunctorIdentityValue.At(
									b.TermAs[CategoryOps[A, M]]("opposite_category(C)"), P, c, u)))
					}))))
		})

		unique := ctx.Lemma(Statement{
			Binders: "∀C:category_ops(A, M). " +
				"∀c:A. " +
				"∀P:functor_ops(A, M, set(B), morphism_triple(set(B), B → B)). " +
				"∀α β:(A → M → B).",
			Hypotheses: []string{
				"category(C)",
				"c ∈ C.objects",
				"α ∈ yoneda_family_set(C, c, P)",
				"β ∈ yoneda_family_set(C, c, P)",
				"yoneda_element(C, c, α) = yoneda_element(C, c, β)",
			},
			Conclusion: "α = β",
		}, func(
			a *Argument,
			C *Expr[CategoryOps[A, M]],
			c *Expr[A],
			P *Expr[presheaf],
			α, β *Expr[familyMap],
			cat, cIn, αIn, βIn, equal Fact,
		) {
			alpha := a.Conjuncts(
				a.Unfolded(αIn, yonedaFamilySetDef),
				"α is natural",
				"α is normalized")
			beta := a.Conjuncts(
				a.Unfolded(βIn, yonedaFamilySetDef),
				"β is natural",
				"β is normalized")
			normalAlpha := a.TermAs[familyMap](
				"normalize_on(C.objects, λg:M. junk, λx:A. normalize_on(category_hom(C, x, c), junk, α(x)))")
			normalBeta := a.TermAs[familyMap](
				"normalize_on(C.objects, λg:M. junk, λx:A. normalize_on(category_hom(C, x, c), junk, β(x)))")
			a.Show(
				"normalized families agreeing at the identity are equal",
				CalcEq(
					Leg(
						normalAlpha,
						"α is normalized",
						By(alpha[1])),
					Leg(
						normalBeta,
						"the normalized values agree",
						Simp(Fwd(functions.NormalizeOnEqIff)),
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							b.Assume()
							g := b.FixAs[M]("g")
							gIn := b.Assume()
							b.Show(
								"both values are the action on the common identity value",
								By(
									cat,
									equal,
									cIn,
									gIn,
									alpha[0],
									beta[0],
									YonedaFamilyFromElement.At(C, c, P, α, x, g),
									YonedaFamilyFromElement.At(C, c, P, β, x, g)))
						})),
					FinalLeg(
						"β is normalized",
						By(Normalized, beta[1]))))
		})
		elementIn := ctx.Lemma(Statement{
			Binders: "∀C:category_ops(A, M). " +
				"∀c:A. " +
				"∀P:functor_ops(A, M, set(B), morphism_triple(set(B), B → B)). " +
				"∀α:(A → M → B).",
			Hypotheses: []string{
				"category(C)",
				"c ∈ C.objects",
				"α ∈ yoneda_family_set(C, c, P)",
			},
			Conclusion: "yoneda_element(C, c, α) ∈ P.obj(c)",
		}, func(
			a *Argument,
			C *Expr[CategoryOps[A, M]],
			c *Expr[A],
			P *Expr[presheaf],
			α *Expr[familyMap],
			cat, cIn, αIn Fact,
		) {
			values := a.Have(
				"the family values lie in the presheaf",
				"∀x:A. ∀g:M. x ∈ C.objects ∧ g ∈ category_hom(C, x, c) ⇒ α(x, g) ∈ P.obj(x)",
				BySets(αIn, yonedaFamilySetDef.At(C, c, P), yonedaFamilyDef.At(C, c, P, α)))
			a.Show(
				"the value of the family at the identity of c lies in P(c)",
				Unfold(yonedaElementDef),
				By(cat, cIn, category.IdentityHom.At(C, c), values.At(c, a.TermAs[M]("C.identity(c)"))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			C *Expr[CategoryOps[A, M]],
			c *Expr[A],
			P *Expr[presheaf],
			cat, cIn, isPresheaf Fact,
		) {
			a.Do(SplitConjAll(
				Case(
					"evaluation is injective",
					Unfold(functions.InjectiveOnDef),
					By(cat, cIn, At(unique, C, c, P))),
				Case(
					"the image is P(c)",
					BySets(cat, cIn, isPresheaf, At(inverse, C, c, P), At(elementIn, C, c, P))),
				Case(
					"the explicit inverse realizes every element",
					Cite(inverse))))
		})
	}),
	Reading: "The values of P lie in the subsets of any type B: the " +
		"lemma never compares an element of P(x) with a morphism of C.",
})}

// YonedaNatural — the correspondence is natural in c: a natural family
// read along h: c → c' has for its element P(h) applied to the element.
// Both are α(c, h): on the left since h ∘ 1_c = h, on the right since a
// natural family is read off its element.
var YonedaNatural = yonedaNaturalThm{family.Add(registry.ProofEntry{
	Name: "YonedaNatural",
	Key:  "prop_a36c0aacbfc89580",
	Build: family.Theorem(Statement{
		Binders: "∀C:category_ops(A, M). " +
			"∀c c':A. " +
			"∀h:M. " +
			"∀P:functor_ops(A, M, set(B), morphism_triple(set(B), B → B)). " +
			"∀α:(A → M → B).",
		Hypotheses: []string{
			"category(C)",
			"h ∈ category_hom(C, c, c')",
			"yoneda_family(C, c', P, α)",
		},
		Conclusion: "yoneda_element(C, c, λx:A. λg:M. α(x, C.compose(h, g))) = " +
			"P.map(h).map(yoneda_element(C, c', α))",
	}, func(
		a *Argument,
		C *Expr[CategoryOps[A, M]],
		c, cPrime *Expr[A],
		h *Expr[M],
		P *Expr[presheaf],
		α *Expr[familyMap],
		cat, hIn, natural Fact,
	) {
		a.Show(
			"both sides are the value of α at h",
			CalcEq(
				Leg(
					a.TermAs[B]("α(c, h)"),
					"the element is the value at h ∘ 1_c, and the identity at c is a right unit for h",
					By(hIn, yonedaElementDef, category.RightUnitHom.Read(cat).At(c, cPrime, h))),
				FinalLeg(
					"the natural family α is read off its element at h",
					By(cat, hIn, natural, YonedaFamilyFromElement.At(C, cPrime, P, α, c, h)))))
	}),
	Reading: "The naturality in P is definitional — a transformation θ: P → Q " +
		"acts on the element by its component at c — and has no member of its own.",
})}
