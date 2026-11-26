package presheaf

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/category/preorder_category"
	"github.com/euc-ai/xugo/library/proofs/category/set_category"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PresheafFunctorDef assigns sections to open sets and normalized
// restrictions to the morphisms of the reverse-inclusion category.
var PresheafFunctorDef = presheafFunctorDefThm{family.Define(registry.DefEntry{
	Name:  "PresheafFunctorDef",
	Key:   "prop_7eaba7bed43ce182",
	Const: "presheaf_functor",
	Type: "(set(A) → set(B)) → " +
		"(set(A) → set(A) → B → B) → " +
		"functor_ops(set(A), morphism_triple(set(A), bool), set(B), morphism_triple(set(B), B → B))",
	Equations: []string{
		"∀F:(set(A) → set(B)). ∀res:(set(A) → set(A) → B → B). " +
			"    presheaf_functor(F, res) = " +
			"    mk_functor(F, " +
			"        λt:morphism_triple(set(A), bool). " +
			"            mk_morphism(F(t.source), " +
			"                F(t.target), " +
			"                normalize_on(F(t.source), junk, res(t.source, t.target))))",
	},
})}

// PresheafIffFunctor identifies restriction laws with the functor laws
// for reverse inclusion: normalization records only values on sections.
var PresheafIffFunctor = presheafIffFunctorThm{family.Add(registry.ProofEntry{
	Name: "PresheafIffFunctor",
	Key:  "prop_c1a07c4edf18cbeb",
	Build: family.Theorem("∀T:set(set(A)). ∀F:(set(A) → set(B)). ∀res:(set(A) → set(A) → B → B). "+
		"    presheaf(T, F, res) ⇔ "+
		"    is_topology(T) ∧ "+
		"    functor(preorder_category(λU:set(A). λV:set(A). V ⊆ U, T), "+
		"        set_category⟨M:B⟩, "+
		"        presheaf_functor(F, res))",
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			F *Expr[Fun[Set[A], Set[B]]],
			res *Expr[Fun3[Set[A], Set[A], B, B]],
		) {
			reverseInclusion := a.Have(
				"reverse inclusion is a preorder",
				"preorder(λU:set(A). λV:set(A). V ⊆ U)",
				Unfold(order.Preorder),
				Unfold(equivalence.ReflexiveDef),
				Unfold(equivalence.TransitiveDef),
				By(set_order.SubsetRefl, set_order.SubsetTrans))
			a.Have(
				"the source and target are categories",
				"category(preorder_category(λU:set(A). λV:set(A). V ⊆ U, T)) ∧ category(set_category⟨M:B⟩)",
				By(
					reverseInclusion,
					preorder_category.PreorderCategory.At(
						a.TermAs[Fun2[Set[A], Set[A], Bool]]("λU:set(A). λV:set(A). V ⊆ U"), T),
					set_category.SetCategory.Inst[B]()))

			arrows := a.Have(
				"a normalized restriction is a map of section sets precisely when restriction is closed",
				"∀U V:set(A). "+
					"    mk_morphism(F(U), F(V), normalize_on(F(U), junk, res(U, V))) ∈ "+
					"    category_hom(set_category⟨M:B⟩, F(U), F(V)) ⇔ "+
					"    (∀s:B. s ∈ F(U) ⇒ res(U, V, s) ∈ F(V))",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("U")
					b.FixAs[Set[A]]("V")
					sections := b.TermAs[Set[B]]("F(U)")
					junk := b.TermAs[B]("junk")
					restriction := b.TermAs[Fun[B, B]]("res(U, V)")
					b.Do(Simp(Fwd(set_category.SetCategoryDef), Fwd(category.CategoryFromHomHomIff)))
					b.Iff()
					b.Backward(
						"the normalized restriction is a normalized map of section sets",
						func(c *Argument, closed Fact) {
							mapsInto := c.Have(
								"the normalized restriction maps F(U) into F(V)",
								"∀x:B. x ∈ F(U) ⇒ normalize_on(F(U), junk, res(U, V), x) ∈ F(V)",
								Derive(func(d *Argument) {
									x := d.FixAs[B]("x")
									inSource := d.Assume()
									d.Show(
										"the restriction lands in the target section set",
										BySets(inSource, closed.At(x), functions.NormalizeOnIn.At(sections, junk, restriction, x)))
								}))
							c.Show(
								"the section sets are objects, and the normalized "+
									"restriction maps F(U) into F(V) and is normalized",
								BySets(mapsInto, functions.NormalizeOnIdempotent.At(sections, junk, restriction)))
						})
					b.Forward(
						"a map of section sets preserves membership in its section sets",
						func(c *Argument, member Fact) {
							mapsInto := c.Have(
								"the normalized restriction maps F(U) into F(V)",
								"∀x:B. x ∈ F(U) ⇒ normalize_on(F(U), junk, res(U, V), x) ∈ F(V)",
								BySets(member))
							s := c.FixAs[B]("s")
							inSource := c.Assume()
							c.Show(
								"normalization can be removed at the section",
								By(inSource, mapsInto.At(s), functions.NormalizeOnIn.At(sections, junk, restriction, s)))
						})
				}))

			identities := a.Have(
				"preserving identities is restriction to the same open set",
				"∀U:set(A). "+
					"    mk_morphism(F(U), F(U), normalize_on(F(U), junk, res(U, U))) = "+
					"    set_category⟨M:B⟩.identity(F(U)) ⇔ "+
					"    (∀s:B. s ∈ F(U) ⇒ res(U, U, s) = s)",
				Simp(
					Fwd(set_category.SetCategoryDef),
					Fwd(category.CategoryFromHomDef),
					Fwd(category.CategoryIdentityDef),
					Fwd(category.MorphismTripleData.Inj),
					Fwd(functions.NormalizeOnEqIff)),
				Basic())
			composition := a.Have(
				"under restriction closure, preserving composition is restriction in two steps",
				Statement{
					Binders: "∀U V W:set(A).",
					Hypotheses: []string{
						"∀s:B. s ∈ F(U) ⇒ res(U, V, s) ∈ F(V)",
					},
					Conclusion: "mk_morphism(F(U), F(W), normalize_on(F(U), junk, res(U, W))) = " +
						"set_category⟨M:B⟩.compose(mk_morphism(F(V), F(W), normalize_on(F(V), junk, res(V, W))), " +
						"    mk_morphism(F(U), F(V), normalize_on(F(U), junk, res(U, V)))) ⇔ " +
						"∀s:B. s ∈ F(U) ⇒ res(V, W, res(U, V, s)) = res(U, W, s)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("U")
					b.FixAs[Set[A]]("V")
					b.FixAs[Set[A]]("W")
					closed := b.Assume()
					b.Do(Simp(
						Fwd(set_category.SetCategoryDef),
						Fwd(category.CategoryFromHomDef),
						Fwd(category.CategoryComposeDef),
						Fwd(category.TripleSourceDef),
						Fwd(category.TripleTargetDef),
						Fwd(category.TripleMapDef),
						Fwd(category.MorphismTripleData.Inj),
						Fwd(functions.NormalizeOnEqIff),
						Fwd(functions.ComposeApply)))
					evaluation := b.Have(
						"both normalizations agree with restriction at a section",
						Statement{
							Binders: "∀s:B.",
							Hypotheses: []string{
								"s ∈ F(U)",
							},
							Conclusion: "normalize_on(F(V), junk, res(V, W), normalize_on(F(U), junk, res(U, V), s)) = " +
								"res(V, W, res(U, V, s))",
						},
						Derive(func(c *Argument) {
							s := c.FixAs[B]("s")
							inSource := c.Assume()
							c.Show(
								"source and middle membership remove both normalizations",
								By(
									inSource,
									closed.At(s),
									functions.NormalizeOnIn.At(
										c.TermAs[Set[B]]("F(U)"), c.TermAs[B]("junk"), c.TermAs[Fun[B, B]]("res(U, V)"), s),
									functions.NormalizeOnIn.At(
										c.TermAs[Set[B]]("F(V)"),
										c.TermAs[B]("junk"),
										c.TermAs[Fun[B, B]]("res(V, W)"),
										c.TermAs[B]("res(U, V, s)"))))
						}))
					b.Show(
						"equality of normalized composites is equality on the source section set",
						Expect(Basic(),
							Case(
								"a preserved composite gives the restriction law",
								Derive(func(c *Argument) {
									s := c.FixAs[B]("s")
									preserved := c.Hyp(Statement{
										Binders: "∀x:B.",
										Hypotheses: []string{
											"x ∈ F(U)",
										},
										Conclusion: "res(U, W, x) = " +
											"normalize_on(F(V), junk, res(V, W), normalize_on(F(U), junk, res(U, V), x))",
									})
									c.Show(
										"evaluate the composite at the section",
										By(preserved.At(s), evaluation.At(s)))
								})),
							Case(
								"the restriction law gives a preserved composite",
								Derive(func(c *Argument) {
									x := c.FixAs[B]("x")
									inSource := c.Assume()
									twice := c.Hyp("∀s:B. s ∉ F(U) ∨ res(U, W, s) = res(V, W, res(U, V, s))")
									c.Show(
										"evaluate the two-step restriction at the section",
										By(inSource, twice.At(x), evaluation.At(x)))
								}))))
				}))

			functorLaws := a.Have(
				"the hom-data criterion specializes to reverse inclusion",
				"functor(preorder_category(λU:set(A). λV:set(A). V ⊆ U, T), "+
					"    set_category⟨M:B⟩, "+
					"    presheaf_functor(F, res)) ⇔ "+
					"(∀U V:set(A). "+
					"    U ∈ T ∧ V ∈ T ∧ V ⊆ U ⇒ "+
					"    mk_morphism(F(U), F(V), normalize_on(F(U), junk, res(U, V))) ∈ "+
					"    category_hom(set_category⟨M:B⟩, F(U), F(V))) ∧ "+
					"(∀U:set(A). "+
					"    U ∈ T ⇒ "+
					"    mk_morphism(F(U), F(U), normalize_on(F(U), junk, res(U, U))) = "+
					"    set_category⟨M:B⟩.identity(F(U))) ∧ "+
					"(∀U V W:set(A). "+
					"    U ∈ T ∧ V ∈ T ∧ W ∈ T ∧ W ⊆ V ∧ V ⊆ U ⇒ "+
					"    mk_morphism(F(U), F(W), normalize_on(F(U), junk, res(U, W))) = "+
					"    set_category⟨M:B⟩.compose(mk_morphism(F(V), F(W), normalize_on(F(V), junk, res(V, W))), "+
					"        mk_morphism(F(U), F(V), normalize_on(F(U), junk, res(U, V)))))",
				Derive(func(b *Argument) {
					b.Do(Unfold(PresheafFunctorDef), Unfold(preorder_category.PreorderCategoryDef))
					categories := b.Have(
						"the two categories satisfy the generic criterion's premise",
						"category(category_from_hom(T, "+
							"        λU:set(A). λV:set(A). {u:bool | u ∧ V ⊆ U}, "+
							"        λU:set(A). ⊤, "+
							"        λU:set(A). λV:set(A). λW:set(A). λv:bool. λu:bool. ⊤)) ∧ "+
							"category(set_category⟨M:B⟩)",
						By(
							b.Hyp(
								"category(category_from_hom(T, "+
									"        λU:set(A). λV:set(A). {u:bool | u ∧ V ⊆ U}, "+
									"        λU:set(A). ⊤, "+
									"        λU:set(A). λV:set(A). λW:set(A). λv:bool. λu:bool. ⊤))"),
							b.Hyp("category(set_category⟨M:B⟩)")))
					generic := b.Have(
						"a functor is exactly a map preserving objects, hom data, identities and composites",
						"functor(category_from_hom(T, "+
							"        λU:set(A). λV:set(A). {u:bool | u ∧ V ⊆ U}, "+
							"        λU:set(A). ⊤, "+
							"        λU:set(A). λV:set(A). λW:set(A). λv:bool. λu:bool. ⊤), "+
							"    set_category⟨M:B⟩, "+
							"    mk_functor(F, "+
							"        λt:morphism_triple(set(A), bool). "+
							"            mk_morphism(F(t.source), "+
							"                F(t.target), "+
							"                normalize_on(F(t.source), junk, res(t.source, t.target))))) ⇔ "+
							"(∀x:set(A). x ∈ T ⇒ F(x) ∈ 𝕌) ∧ "+
							"(∀x y:set(A). ∀f:bool. "+
							"    x ∈ T ∧ y ∈ T ∧ f ∈ {u:bool | u ∧ y ⊆ x} ⇒ "+
							"    mk_morphism(F(x), F(y), normalize_on(F(x), junk, res(x, y))) ∈ "+
							"    category_hom(set_category⟨M:B⟩, F(x), F(y))) ∧ "+
							"(∀x:set(A). "+
							"    x ∈ T ⇒ "+
							"    mk_morphism(F(x), F(x), normalize_on(F(x), junk, res(x, x))) = "+
							"    mk_morphism(F(x), F(x), normalize_on(F(x), junk, λx:B. x))) ∧ "+
							"(∀x y z:set(A). ∀f g:bool. "+
							"    x ∈ T ∧ y ∈ T ∧ z ∈ T ∧ f ∈ {u:bool | u ∧ y ⊆ x} ∧ g ∈ {u:bool | u ∧ z ⊆ y} ⇒ "+
							"    mk_morphism(F(x), F(z), normalize_on(F(x), junk, res(x, z))) = "+
							"    mk_morphism(F(x), "+
							"        F(z), "+
							"        normalize_on(F(x), "+
							"            junk, "+
							"            normalize_on(F(y), junk, res(y, z)) ∘ normalize_on(F(x), junk, res(x, y)))))",
						By(
							category.FunctorFromHomIff.At(T,
								b.TermAs[Fun3[Set[A], Set[A], Bool, Bool]]("λU:set(A). λV:set(A). {u:bool | u ∧ V ⊆ U}"),
								b.TermAs[Fun[Set[A], Bool]]("λU:set(A). ⊤"),
								b.TermAs[Fun[Set[A], Fun[Set[A], Fun3[Set[A], Bool, Bool, Bool]]]](
									"λU:set(A). λV:set(A). λW:set(A). λv:bool. λu:bool. ⊤"),
								b.TermAs[category.CategoryOps[Set[B], category.MorphismTriple[Set[B], Fun[B, B]]]](
									"set_category⟨M:B⟩"), F,
								b.TermAs[Fun3[Set[A], Set[A], Bool, category.MorphismTriple[Set[B], Fun[B, B]]]](
									"λU:set(A). λV:set(A). λu:bool. mk_morphism(F(U), F(V), normalize_on(F(U), junk, res(U, V)))")),
							categories))
					b.Do(Simp(Fwd(generic)),
						Simp(
							Fwd(set_basic.SetMemberDef),
							Fwd(set_basic.SetComprehensionDef),
							Fwd(set_basic.ComprehensionSpecDef),
							Fwd(set_basic.UniverseDef)))
					b.Iff()
					b.Backward(
						"the unique Boolean datum adds no condition",
						func(c *Argument, laws Fact) {
							c.Show(
								"every admissible datum carries the same framed restriction",
								By(Normalized, laws))
						})
					b.Forward(
						"choose the Boolean datum true for each inclusion",
						func(c *Argument, laws Fact) {
							parts := c.Conjuncts(
								laws,
								"all section sets are objects",
								"each Boolean hom datum preserves its ends",
								"identities are preserved",
								"composites are preserved")
							c.Show(
								"the inclusion laws follow by choosing true",
								SplitConj(
									Case(
										"arrows and identities are preserved",
										SplitConj(
											Case(
												"the arrow attached to an inclusion is preserved",
												Derive(func(d *Argument) {
													U := d.FixAs[Set[A]]("U")
													V := d.FixAs[Set[A]]("V")
													d.Show(
														"true belongs to the hom data of an inclusion",
														By(parts[1].At(U, V, d.TermAs[Bool]("⊤"))))
												})),
											Case(
												"the identity equation is unchanged",
												By(parts[2])))),
									Case(
										"two inclusions have their composite preserved",
										Derive(func(d *Argument) {
											U := d.FixAs[Set[A]]("U")
											V := d.FixAs[Set[A]]("V")
											W := d.FixAs[Set[A]]("W")
											d.Show(
												"choose true for both hom data",
												By(parts[3].At(U, V, W, d.TermAs[Bool]("⊤"), d.TermAs[Bool]("⊤"))))
										}))))
						})
				}))

			a.Do(Simp(Fwd(functorLaws), Fwd(arrows), Fwd(identities), Fwd(Presheaf)))
			a.Iff()
			a.Backward(
				"the functor laws recover all presheaf laws",
				func(b *Argument, laws Fact) {
					b.Show(
						"restriction is closed, is the identity on each open set, and composes",
						SplitConj(
							Case(
								"topology, closure and identity have already been identified",
								By(laws)),
							Case(
								"composition gives restriction in two steps",
								Derive(func(c *Argument) {
									parts := c.Conjuncts(
										laws,
										"the family is a topology",
										"restrictions land in section sets",
										"restrictions preserve identity",
										"restrictions preserve composition")
									c.Show(
										"the two-step equation holds at every section",
										Derive(func(d *Argument) {
											U := d.FixAs[Set[A]]("U")
											V := d.FixAs[Set[A]]("V")
											W := d.FixAs[Set[A]]("W")
											d.FixAs[B]("s")
											inside := d.Assume()
											closed := d.Have(
												"restriction to the middle open set is closed",
												"∀s:B. s ∈ F(U) ⇒ res(U, V, s) ∈ F(V)",
												By(inside, parts[1].At(U, V)))
											d.Show(
												"the composition comparison applies on the source section set",
												By(closed, composition.At(U, V, W), parts[3].At(U, V, W), inside))
										}))
								}))))
				})
			a.Forward(
				"the presheaf laws give the functor laws",
				func(b *Argument, laws Fact) {
					b.Show(
						"the topology and the three functor requirements hold",
						SplitConj(
							Case(
								"the family is a topology",
								By(laws)),
							Case(
								"the restrictions define a functor",
								SplitConj(
									Case(
										"closure and identity give the first two requirements",
										By(laws)),
									Case(
										"restriction in two steps preserves composition",
										Derive(func(c *Argument) {
											parts := c.Conjuncts(
												laws,
												"the family is a topology",
												"restriction is closed",
												"restriction to the same set fixes sections",
												"restriction in two steps equals restriction once")
											c.Show(
												"the composition equation holds for every chain of inclusions",
												Derive(func(d *Argument) {
													U := d.FixAs[Set[A]]("U")
													V := d.FixAs[Set[A]]("V")
													W := d.FixAs[Set[A]]("W")
													inside := d.Assume()
													closed := d.Have(
														"restriction to the middle open set is closed",
														"∀s:B. s ∈ F(U) ⇒ res(U, V, s) ∈ F(V)",
														By(inside, parts[1].At(U, V)))
													d.Show(
														"restriction in two steps is the normalized composite",
														By(closed, composition.At(U, V, W), parts[3].At(U, V, W), inside))
												}))
										}))))))
				})
		}),
})}
