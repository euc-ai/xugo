// set_category.go — the category of the subsets of a type. Its objects
// are all the sets of a type M, its morphisms from S to T the maps
// M → M carrying S into T, normalized with junk off S so that two maps
// agreeing on S are one morphism; the identity at S is the identity
// map normalized, and the composite the composite of maps normalized
// again, since g ∘ f off S is g at junk. The category is assembled
// from this hom data, and an isomorphism in it is a map that is a
// bijection of S onto T. Its morphisms, and a functor into it, are
// read on elements: a morphism maps its source into its target, the
// identity fixes elements, and a composite is the composite of the
// maps there.

package set_category

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// SetCategoryDef — `set_category`: the category of the subsets of the
// type M, assembled from the normalized maps between them.
var SetCategoryDef = setCategoryDefThm{family.Define(registry.DefEntry{
	Name:  "SetCategoryDef",
	Key:   "prop_162c2ffbf3aa194",
	Const: "set_category",
	Type:  "category_ops(set(M), morphism_triple(set(M), M → M))",
	Equations: []string{
		"set_category = " +
			"category_from_hom(𝕌, " +
			"    λS:set(M). λT:set(M). " +
			"        {f:(M → M) | (∀x:M. x ∈ S ⇒ f(x) ∈ T) ∧ normalize_on(S, junk, f) = f}, " +
			"    λS:set(M). normalize_on(S, junk, λx:M. x), " +
			"    λS:set(M). λT:set(M). λV:set(M). λg:(M → M). λf:(M → M). normalize_on(S, junk, g ∘ f))",
	},
	Reading: "The category is one per type M, with every subset of M an object. A morphism is a " +
		"framed map, mk_morphism(S, T, f), whose map is normalized: a map into T on S and junk off it.",
})}

// SetCategory — the subsets of a type form a category: normalized
// maps are closed under identities and composition, and their equations
// are determined on the source set.
var SetCategory = setCategoryThm{family.Add(registry.ProofEntry{
	Name: "SetCategory",
	Key:  "prop_a72fc0301deea531",
	Build: family.Theorem("category(set_category⟨M:A⟩)",
		func(a *Argument) {
			a.Do(Unfold(SetCategoryDef))
			junk := a.TermAs[A]("junk")
			identity := a.TermAs[Fun[A, A]]("λx:A. x")
			onSource := functions.NormalizeOnIn.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]())
			inner := functions.NormalizeOnComposeInner.Inst(
				TypeBinder.BindA[A](), TypeBinder.BindB[A](), TypeBinder.BindC[A]())
			identities := a.Have(
				"normalized identities are endomorphisms",
				Statement{
					Binders: "∀S:set(A).",
					Hypotheses: []string{
						"S ∈ 𝕌",
					},
					Conclusion: "normalize_on(S, junk, λx:A. x) ∈ " +
						"{k:A → A | (∀u:A. u ∈ S ⇒ k(u) ∈ S) ∧ normalize_on(S, junk, k) = k}",
				},
				Derive(func(b *Argument) {
					S := b.FixAs[Set[A]]("S")
					b.Assume()
					b.Show(
						"the identity preserves S and normalization is idempotent",
						BySets(onSource.At(S, junk, identity), functions.NormalizeOnIdempotent.At(S, junk, identity)))
				}))
			composites := a.Have(
				"normalized composites are morphisms",
				Statement{
					Binders: "∀S T V:set(A). ∀f g:(A → A).",
					Hypotheses: []string{
						"S ∈ 𝕌",
						"T ∈ 𝕌",
						"V ∈ 𝕌",
						"f ∈ {k:A → A | (∀u:A. u ∈ S ⇒ k(u) ∈ T) ∧ normalize_on(S, junk, k) = k}",
						"g ∈ {k:A → A | (∀u:A. u ∈ T ⇒ k(u) ∈ V) ∧ normalize_on(T, junk, k) = k}",
					},
					Conclusion: "normalize_on(S, junk, g ∘ f) ∈ " +
						"{k:A → A | (∀u:A. u ∈ S ⇒ k(u) ∈ V) ∧ normalize_on(S, junk, k) = k}",
				},
				Derive(func(b *Argument) {
					S := b.FixAs[Set[A]]("S")
					b.FixAs[Set[A]]("T")
					b.FixAs[Set[A]]("V")
					f := b.FixAs[Fun[A, A]]("f")
					g := b.FixAs[Fun[A, A]]("g")
					morphisms := b.Assume()
					composite := b.TermAs[Fun[A, A]]("g ∘ f")
					mapsInto := b.Have(
						"the normalized composite carries S into V",
						"∀x:A. x ∈ S ⇒ normalize_on(S, junk, g ∘ f, x) ∈ V",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							inS := c.Assume()
							images := c.Have(
								"the two maps carry x through T into V",
								"f(x) ∈ T ∧ g(f(x)) ∈ V",
								BySets(inS, morphisms))
							c.Show(
								"normalization keeps the composite value on S",
								By(inS, images, functions.NormalizeOnIn.At(S, junk, composite, x), functions.ComposeApply.At(g, f)))
						}))
					b.Show(
						"the composite maps into V and is normalized",
						BySets(mapsInto, functions.NormalizeOnIdempotent.At(S, junk, composite)))
				}))
			leftUnit := a.Have(
				"the target identity is a left unit",
				Statement{
					Binders: "∀S T:set(A). ∀f:(A → A).",
					Hypotheses: []string{
						"S ∈ 𝕌",
						"T ∈ 𝕌",
						"f ∈ {k:A → A | (∀u:A. u ∈ S ⇒ k(u) ∈ T) ∧ normalize_on(S, junk, k) = k}",
					},
					Conclusion: "normalize_on(S, junk, normalize_on(T, junk, λx:A. x) ∘ f) = f",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("S")
					T := b.FixAs[Set[A]]("T")
					b.FixAs[Fun[A, A]]("f")
					morphism := b.Assume()
					normalized := b.TermAs[Fun[A, A]]("normalize_on(S, junk, f)")
					b.Show(
						"the composite agrees with f on S and f is normalized",
						CalcEq(
							Leg(
								normalized.Core(),
								"the normalized maps agree on S",
								Simp(Fwd(functions.NormalizeOnEqIff)),
								Derive(func(c *Argument) {
									c.FixAs[A]("x")
									inS := c.Assume()
									imageIn := c.Have(
										"f sends x into T",
										"f(x) ∈ T",
										BySets(inS, morphism))
									c.Show(
										"the normalized target identity fixes f(x)",
										Simp(Fwd(functions.ComposeApply)),
										By(imageIn, functions.NormalizeOnIn.At(T, junk, identity, c.TermAs[A]("f(x)"))))
								})),
							FinalLeg(
								"f already is normalized",
								BySets(morphism))))
				}))
			rightUnit := a.Have(
				"the source identity is a right unit",
				Statement{
					Binders: "∀S T:set(A). ∀f:(A → A).",
					Hypotheses: []string{
						"S ∈ 𝕌",
						"T ∈ 𝕌",
						"f ∈ {k:A → A | (∀u:A. u ∈ S ⇒ k(u) ∈ T) ∧ normalize_on(S, junk, k) = k}",
					},
					Conclusion: "normalize_on(S, junk, f ∘ normalize_on(S, junk, λx:A. x)) = f",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("S")
					b.FixAs[Set[A]]("T")
					b.FixAs[Fun[A, A]]("f")
					morphism := b.Assume()
					b.Show(
						"inner normalization leaves the normalized composite unchanged",
						Simp(Fwd(inner), Fwd(functions.ComposeApply)),
						BySets(morphism))
				}))
			associativity := a.Have(
				"normalized composition is associative",
				Statement{
					Binders: "∀S T V W:set(A). ∀f g h:(A → A).",
					Hypotheses: []string{
						"S ∈ 𝕌",
						"T ∈ 𝕌",
						"V ∈ 𝕌",
						"W ∈ 𝕌",
						"f ∈ {k:A → A | (∀u:A. u ∈ S ⇒ k(u) ∈ T) ∧ normalize_on(S, junk, k) = k}",
						"g ∈ {k:A → A | (∀u:A. u ∈ T ⇒ k(u) ∈ V) ∧ normalize_on(T, junk, k) = k}",
						"h ∈ {k:A → A | (∀u:A. u ∈ V ⇒ k(u) ∈ W) ∧ normalize_on(V, junk, k) = k}",
					},
					Conclusion: "normalize_on(S, junk, h ∘ normalize_on(S, junk, g ∘ f)) = " +
						"normalize_on(S, junk, normalize_on(T, junk, h ∘ g) ∘ f)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("S")
					T := b.FixAs[Set[A]]("T")
					b.FixAs[Set[A]]("V")
					b.FixAs[Set[A]]("W")
					b.FixAs[Fun[A, A]]("f")
					b.FixAs[Fun[A, A]]("g")
					b.FixAs[Fun[A, A]]("h")
					morphisms := b.Assume()
					b.Do(Simp(Fwd(inner), Fwd(functions.NormalizeOnEqIff), Fwd(functions.ComposeApply)))
					b.FixAs[A]("x")
					inS := b.Assume()
					imageIn := b.Have(
						"f sends x into T",
						"f(x) ∈ T",
						BySets(inS, morphisms))
					hg := b.TermAs[Fun[A, A]]("λu:A. h(g(u))")
					b.Show(
						"both parenthesizations have value h applied to g applied to f at x",
						By(imageIn, functions.NormalizeOnIn.At(T, junk, hg, b.TermAs[A]("f(x)"))))
				}))
			objects := a.TermAs[Set[Set[A]]]("𝕌")
			hom := a.TermAs[Fun3[Set[A], Set[A], Fun[A, A], Bool]](
				"λS:set(A). λT:set(A). {f:A → A | (∀x:A. x ∈ S ⇒ f(x) ∈ T) ∧ normalize_on(S, junk, f) = f}")
			units := a.TermAs[Fun[Set[A], Fun[A, A]]]("λS:set(A). normalize_on(S, junk, λx:A. x)")
			compose := a.TermAs[Fun[Set[A], Fun[Set[A], Fun3[Set[A], Fun[A, A], Fun[A, A], Fun[A, A]]]]](
				"λS:set(A). λT:set(A). λV:set(A). λg:(A → A). λf:(A → A). normalize_on(S, junk, g ∘ f)")
			a.Show(
				"the five hom-data laws give the category",
				By(
					identities,
					composites,
					leftUnit,
					rightUnit,
					associativity,
					category.CategoryFromHom.At(objects, hom, units, compose)))
		}),
})}

// SetIsomorphismIff — a normalized map is an isomorphism exactly when
// it bijects its source onto its target: inverse data give the two
// inverse laws on the carriers, and a bijection's inverse is normalized
// to give inverse data.
var SetIsomorphismIff = setIsomorphismIffThm{family.Add(registry.ProofEntry{
	Name: "SetIsomorphismIff",
	Key:  "prop_189589e32ff33e8",
	Build: family.Theorem("∀S T:set(M). ∀f:(M → M). "+
		"    category_isomorphism(set_category, mk_morphism(S, T, f)) ⇔ "+
		"    (∀x:M. x ∈ S ⇒ f(x) ∈ T) ∧ "+
		"    normalize_on(S, junk, f) = f ∧ "+
		"    injective_on(S, f) ∧ "+
		"    image(f, S) = T",
		func(a *Argument, S, T *Expr[Set[M]], f *Arrow[M, M]) {
			a.Do(Simp(Fwd(SetCategoryDef), Fwd(category.CategoryFromHomIsomorphismIff)))
			a.Iff()
			a.Forward(
				"inverse data give a bijection of the carriers",
				func(b *Argument, isomorphism Fact) {
					parts := b.Conjuncts(
						isomorphism,
						"the source is an object",
						"the target is an object",
						"f belongs to its hom set",
						"inverse data exist")
					g, inverse := b.UnpackAs[Fun[M, M]](parts[3], "g")
					inverseOnCarriers := b.Simplified(
						inverse,
						Fwd(functions.NormalizeOnEqIff),
						Fwd(functions.ComposeApply))
					b.Show(
						"the inverse maps between the carriers and undoes f on both sides",
						BySets(parts[2], inverseOnCarriers, functions.TwoSidedInverseBijection.At(S, T, f, g)))
				})
			a.Backward(
				"normalize the inverse of the bijection",
				func(b *Argument, bijection Fact) {
					b.Do(SplitConj(
						Case(
							"the ends are objects and f is a morphism",
							BySets(bijection)),
						Case(
							"the normalized inverse supplies inverse data",
							Derive(func(c *Argument) {
								junk := c.TermAs[M]("junk")
								inverse := c.TermAs[Fun[M, M]]("inverse_on(S, f)")
								c.Take(c.TermAs[Fun[M, M]]("normalize_on(T, junk, inverse_on(S, f))"))
								c.Do(SplitConjAll(
									Case(
										"the inverse is a normalized map from T into S",
										Derive(func(d *Argument) {
											mapsBack := d.Have(
												"the inverse sends T into S",
												"∀y:M. y ∈ T ⇒ normalize_on(T, junk, inverse_on(S, f), y) ∈ S",
												Derive(func(e *Argument) {
													y := e.FixAs[M]("y")
													inT := e.Assume()
													e.Show(
														"normalization preserves the chosen preimage on T",
														Simp(Fwd(functions.NormalizeOnIn)),
														By(Normalized, inT, bijection, functions.InverseOnIn.At(S, f, y)))
												}))
											d.Show(
												"the inverse maps back and normalization is idempotent",
												BySets(mapsBack, functions.NormalizeOnIdempotent.At(T, junk, inverse)))
										})),
									Case(
										"the inverse after f gives the source identity",
										Derive(func(d *Argument) {
											d.Do(Simp(Fwd(functions.NormalizeOnEqIff), Fwd(functions.ComposeApply)))
											x := d.FixAs[M]("x")
											inS := d.Assume()
											d.Have(
												"f sends x into T",
												"f(x) ∈ T",
												By(inS, bijection))
											d.Show(
												"normalization preserves the inverse at f of x",
												Simp(Fwd(functions.NormalizeOnIn)),
												By(inS, bijection, functions.InverseOnLeft.At(S, f, x)))
										})),
									Case(
										"f after the inverse gives the target identity",
										Derive(func(d *Argument) {
											d.Do(Simp(Fwd(functions.NormalizeOnEqIff), Fwd(functions.ComposeApply)))
											x := d.FixAs[M]("x")
											inT := d.Assume()
											d.Show(
												"the chosen preimage maps back to x",
												Simp(Fwd(functions.NormalizeOnIn)),
												By(Normalized, inT, bijection, functions.InverseOnRight.At(S, f, x)))
										})),
								))
							})),
					))
				})
		}),
	Reading: "The first two conjuncts say the triple is a morphism at all; a triple " +
		"whose map is not normalized or leaves T is no morphism, hence no isomorphism.",
})}

// ---------------------------------------------------------------------------
// Elements: morphisms and functors into the sets, evaluated
// ---------------------------------------------------------------------------

// SetMorphismMapsInto — a morphism of sets from S to T carries each
// element of S into T: its map is a map into T on S.
var SetMorphismMapsInto = setMorphismMapsIntoThm{family.Add(registry.ProofEntry{
	Name: "SetMorphismMapsInto",
	Key:  "prop_ff1133e1c7c3c731",
	Build: family.Theorem(Statement{
		Binders: "∀f:morphism_triple(set(M), M → M). ∀S T:set(M). ∀t:M.",
		Hypotheses: []string{
			"f ∈ category_hom(set_category, S, T)",
			"t ∈ S",
		},
		Conclusion: "f.map(t) ∈ T",
	}, func(a *Argument) {
		a.Show(
			"a framed map takes the elements of its source into its target",
			Simp(Fwd(category.CategoryHomDef), Fwd(SetCategoryDef), Fwd(category.CategoryFromHomDef)),
			BySets())
	}),
})}

// SetIdentityValue — the identity of sets at S fixes each element of S:
// the identity map, normalized, keeps its values on S.
var SetIdentityValue = setIdentityValueThm{family.Add(registry.ProofEntry{
	Name: "SetIdentityValue",
	Key:  "prop_e865a2ee2824387b",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(M). ∀t:M.",
		Hypotheses: []string{
			"t ∈ S",
		},
		Conclusion: "set_category.identity(S).map(t) = t",
	}, func(a *Argument) {
		a.Show(
			"normalizing the identity keeps its values on S",
			Simp(Fwd(SetCategoryDef), Fwd(category.CategoryFromHomDef), Fwd(category.CategoryIdentityDef)),
			By(functions.NormalizeOnIn))
	}),
})}

// SetComposeValue — the composite of sets g after f takes an element of
// the source of f to g of f of it: the composite map, normalized, keeps
// its values on the source.
var SetComposeValue = setComposeValueThm{family.Add(registry.ProofEntry{
	Name: "SetComposeValue",
	Key:  "prop_627457b79799c292",
	Build: family.Theorem(Statement{
		Binders: "∀f g:morphism_triple(set(M), M → M). ∀t:M.",
		Hypotheses: []string{
			"t ∈ f.source",
		},
		Conclusion: "set_category.compose(g, f).map(t) = g.map(f.map(t))",
	}, func(a *Argument) {
		a.Show(
			"normalizing the composite keeps its values on the source",
			Simp(
				Fwd(SetCategoryDef),
				Fwd(category.CategoryFromHomDef),
				Fwd(category.CategoryComposeDef),
				Fwd(functions.ComposeApply)),
			By(functions.NormalizeOnIn))
	}),
})}

// SetFunctorMapsInto — a functor into the sets carries an element of
// the image of the source of a morphism into the image of its target:
// F.map(f) is a morphism of sets between those images (FunctorMapInHom),
// and a morphism of sets maps into its target (SetMorphismMapsInto).
var SetFunctorMapsInto = setFunctorMapsIntoThm{family.Add(registry.ProofEntry{
	Name: "SetFunctorMapsInto",
	Key:  "prop_fb5f74c2df26392b",
	Build: family.Theorem(Statement{
		Binders: "∀C:category_ops(A, N). " +
			"∀F:functor_ops(A, N, set(M), morphism_triple(set(M), M → M)). " +
			"∀f:N. " +
			"∀t:M.",
		Hypotheses: []string{
			"functor(C, set_category, F)",
			"f ∈ C.morphisms",
			"t ∈ F.obj(C.source(f))",
		},
		Conclusion: "F.map(f).map(t) ∈ F.obj(C.target(f))",
	}, func(a *Argument, C, F, f, t Term, functorial, morphism, element Fact) {
		a.Show(
			"F.map(f) is a morphism of sets between the images of the ends of f, and carries t into its target",
			By(
				element,
				morphism,
				category.FunctorMapInHom.Read(functorial).AsFact().At(f),
				At(
					SetMorphismMapsInto,
					a.Term("F.map(f)"),
					a.Term("F.obj(C.source(f))"),
					a.Term("F.obj(C.target(f))"),
					t)))
	}),
})}

// SetFunctorIdentityValue — a functor into the sets fixes each element
// of an image under the image of an identity: F carries the identity at
// x to the identity of sets at F(x) (FunctorPreservesIdentity), which
// fixes the elements of F(x) (SetIdentityValue).
var SetFunctorIdentityValue = setFunctorIdentityValueThm{family.Add(registry.ProofEntry{
	Name: "SetFunctorIdentityValue",
	Key:  "prop_a21e4f3cd46dd838",
	Build: family.Theorem(Statement{
		Binders: "∀C:category_ops(A, N). " +
			"∀F:functor_ops(A, N, set(M), morphism_triple(set(M), M → M)). " +
			"∀x:A. " +
			"∀t:M.",
		Hypotheses: []string{
			"functor(C, set_category, F)",
			"x ∈ C.objects",
			"t ∈ F.obj(x)",
		},
		Conclusion: "F.map(C.identity(x)).map(t) = t",
	}, func(a *Argument, C, F, x, t Term, functorial, object, element Fact) {
		identity := a.Have(
			"F carries the identity at x to the identity of sets at F(x)",
			"F.map(C.identity(x)) = set_category.identity(F.obj(x))",
			By(object, category.FunctorPreservesIdentity.Read(functorial).AsFact().At(x)))
		a.Show(
			"the identity of sets fixes t",
			identity.Rw(),
			By(element, At(SetIdentityValue, a.Term("F.obj(x)"), t)))
	}),
})}

// SetFunctorComposeValue — a functor into the sets evaluates the image
// of a composite one image after the other: F carries g ∘ f to the
// composite of sets F(g) ∘ F(f) (FunctorPreservesComposite), whose value
// at an element of the source of F(f) is F(g) of F(f) of it
// (SetComposeValue).
var SetFunctorComposeValue = setFunctorComposeValueThm{family.Add(registry.ProofEntry{
	Name: "SetFunctorComposeValue",
	Key:  "prop_4e46dff60634f174",
	Build: family.Theorem(Statement{
		Binders: "∀C:category_ops(A, N). " +
			"∀F:functor_ops(A, N, set(M), morphism_triple(set(M), M → M)). " +
			"∀f g:N. " +
			"∀t:M.",
		Hypotheses: []string{
			"functor(C, set_category, F)",
			"f ∈ C.morphisms",
			"g ∈ C.morphisms",
			"C.target(f) = C.source(g)",
			"t ∈ F.obj(C.source(f))",
		},
		Conclusion: "F.map(C.compose(g, f)).map(t) = F.map(g).map(F.map(f).map(t))",
	}, func(a *Argument, C, F, f, g, t Term, functorial, fIn, gIn, follows, element Fact) {
		composite := a.Have(
			"F carries the composite of f and g to the composite of sets",
			"F.map(C.compose(g, f)) = set_category.compose(F.map(g), F.map(f))",
			By(fIn, gIn, follows, category.FunctorPreservesComposite.Read(functorial).AsFact().At(f, g)))
		inSource := a.Have(
			"t lies in the source of F.map(f), a morphism of sets from the image of the source of f",
			"t ∈ F.map(f).source",
			By(Normalized, element, fIn, category.FunctorMapEnds.Read(functorial).AsFact().At(f)))
		a.Show(
			"the composite of sets sends t through F(f), then F(g)",
			composite.Rw(),
			By(inSource, At(SetComposeValue, a.Term("F.map(f)"), a.Term("F.map(g)"), t)))
	}),
})}
