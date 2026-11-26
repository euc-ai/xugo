package matching

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// Hall — a finite family admits distinct representatives exactly when
// every subfamily with a finite neighbourhood has at least as many
// neighbours as members. For sufficiency, descend on proper subsets: a
// tight subset reserves its whole neighbourhood, and otherwise one index
// reserves one neighbour; either way the rest is matched by descent
// outside what was reserved, and the two matchings join.
var Hall = hallThm{family.Add(registry.ProofEntry{
	Name: "Hall",
	Key:  "prop_ed6876efafa3247c",
	Build: family.Sections(
		Statement{
			Binders:    "∀s:set(A). ∀N:(A → set(B)).",
			Hypotheses: []string{"finite(s)"},
			Conclusion: "«HallCondition»(s, N) ⇔ «Representatives»(s, N)",
			Abbrev: Abbrev{
				{Name: "neighbourhood", Text: "λM:(A → set(B)). λv:set(A). ⋃image(M, v)"},
				{Name: "HallCondition", Text: "λu:set(A). λM:(A → set(B)). ∀v:set(A). " +
					"    v ⊆ u ∧ finite(«neighbourhood»(M, v)) ⇒ card(v) ≤ card(«neighbourhood»(M, v))"},
				{Name: "Representatives", Text: "λu:set(A). λM:(A → set(B)). ∃f:(A → B). " +
					"    injective_on(u, f) ∧ (∀x:A. x ∈ u ⇒ f(x) ∈ M(x))"},
				{Name: "TightSubset", Text: "λu:set(A). λM:(A → set(B)). ∃t:set(A). " +
					"    t ⊊ u ∧ t ≠ ∅ ∧ finite(«neighbourhood»(M, t)) ∧ card(t) = card(«neighbourhood»(M, t))"},
			},
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// Two matchings, one of t into d and one of the rest of u outside
			// d, have disjoint images and join into a matching of u.
			combine := ctx.Lemma(
				Statement{
					Binders: "∀u t:set(A). ∀M:(A → set(B)). ∀d:set(B). ∀f g:(A → B).",
					Hypotheses: []string{
						"injective_on(t, f)",
						"injective_on(u ∖ t, g)",
						"∀x:A. x ∈ t ⇒ f(x) ∈ M(x) ∩ d",
						"∀x:A. x ∈ u ∖ t ⇒ g(x) ∈ M(x) ∖ d",
					},
					Conclusion: "«Representatives»(u, M)",
				},
				func(a *Argument, u, t *Expr[Set[A]], M *Arrow2[A, B, Bool], d *Expr[Set[B]],
					f, g *Arrow[A, B], fInjective, gInjective, inside, outside Fact) {
					h, hDef := a.LetAs[Fun[A, B]]("h", "λx:A. COND(x ∈ t, f(x), g(x))")
					selection := a.Have(
						"the joined map selects a neighbour, in d exactly on t",
						"∀x:A. x ∈ u ⇒ h(x) ∈ M(x) ∧ (x ∈ t ⇔ h(x) ∈ d)",
						Derive(func(b *Argument) {
							x := b.FixAs[A]()
							inU := b.Assume()
							b.Cases(b.TermAs[Bool]("x ∈ t"))
							b.When(
								"on t the map follows f",
								func(c *Argument, inT Fact) {
									c.Show(
										"the selected neighbour belongs to d",
										BySets(inT, hDef, inside.At(x)))
								})
							b.Otherwise(
								"off t the map follows g",
								func(c *Argument, offT Fact) {
									c.Show(
										"the selected neighbour lies outside d",
										BySets(offT, inU, hDef, outside.At(x)))
								})
						}),
					)
					a.Take(h)
					a.Show(
						"the joined map is a system of distinct representatives",
						SplitConj(
							Case(
								"equal images can only come from the same side",
								Simp(Fwd(functions.InjectiveOnDef)),
								Derive(func(b *Argument) {
									x := b.FixAs[A]()
									y := b.FixAs[A]()
									collision := b.Assume()
									side := b.Have(
										"equal images agree on membership in d",
										"x ∈ t ⇔ y ∈ t",
										By(Normalized, collision, selection.At(x), selection.At(y)),
									)
									fSeparates := b.Unfolded(fInjective, functions.InjectiveOnDef)
									gSeparates := b.Unfolded(gInjective, functions.InjectiveOnDef)
									b.Cases(b.TermAs[Bool]("x ∈ t"))
									b.When(
										"both indices lie in t",
										func(c *Argument, inT Fact) {
											c.Show(
												"f separates them",
												By(inT, side, collision, hDef, fSeparates.At(x, y)))
										})
									b.Otherwise(
										"both indices lie outside t",
										func(c *Argument, offT Fact) {
											c.Show(
												"g separates them",
												BySets(offT, side, collision, hDef, gSeparates.At(x, y)))
										})
								}),
							),
							Case(
								"the map selects each index's neighbour",
								Derive(func(b *Argument) {
									x := b.FixAs[A]()
									inU := b.Assume()
									b.Show(
										"read the neighbourhood membership at x",
										By(inU, selection.At(x)))
								})),
						),
					)
				},
			)

			// A matching of t into d extends to u when the rest, with d taken out
			// of every neighbourhood, still satisfies Hall's condition: descent
			// matches the rest, and combine joins the two.
			extend := ctx.Lemma(
				Statement{
					Binders: "∀u t:set(A). ∀M:(A → set(B)). ∀d:set(B). ∀f:(A → B).",
					Hypotheses: []string{
						"u ∖ t ⊊ u",
						"∀v:set(A). v ⊊ u ⇒ ∀L:(A → set(B)). «HallCondition»(v, L) ⇒ «Representatives»(v, L)",
						"injective_on(t, f)",
						"∀x:A. x ∈ t ⇒ f(x) ∈ M(x) ∩ d",
						"«HallCondition»(u ∖ t, λx:A. M(x) ∖ d)",
					},
					Conclusion: "«Representatives»(u, M)",
				},
				func(a *Argument, u, t *Expr[Set[A]], M *Arrow2[A, B, Bool], d *Expr[Set[B]], f *Arrow[A, B],
					smaller, descent, fInjective, intoD, hallOnRest Fact) {
					rest := a.TermAs[Set[A]]("u ∖ t")
					outsideD := a.TermAs[Fun[A, Set[B]]]("λx:A. M(x) ∖ d")
					g, second := a.ObtainAs[Fun[A, B]](
						"the rest is a proper subfamily, so by descent it has representatives outside d",
						"«Representatives»(u ∖ t, λx:A. M(x) ∖ d)",
						By(smaller, hallOnRest, descent.At(rest, outsideD)),
						// «Representatives» binds f, which this section already fixes.
						Named("g"),
					)
					a.Show(
						"the two matchings have disjoint images and join into one on u",
						By(fInjective, intoD, second, At(combine, u, t, M, d, f, g)))
				},
			)

			// A tight subset t is matched by descent and keeps its whole
			// neighbourhood; the rest keeps Hall's condition without it, since a
			// subset w of the rest joined to t is bounded by the original
			// condition, and t's equal counts cancel.
			tightCase := ctx.Lemma(
				Statement{
					Binders: "∀u:set(A). ∀M:(A → set(B)).",
					Hypotheses: []string{
						"finite(u)",
						"«HallCondition»(u, M)",
						"∀v:set(A). v ⊊ u ⇒ ∀L:(A → set(B)). «HallCondition»(v, L) ⇒ «Representatives»(v, L)",
						"«TightSubset»(u, M)",
					},
					Conclusion: "«Representatives»(u, M)",
				},
				func(a *Argument, u *Expr[Set[A]], M *Arrow2[A, B, Bool], finiteU, condition, descent, tight Fact) {
					t, tightSet := a.UnpackAs[Set[A]](tight)
					parts := a.Conjuncts(
						tightSet,
						"the subset is proper",
						"the subset is nonempty",
						"its neighbourhood is finite",
						"the counts are equal")
					hallOnT := a.Have(
						"the tight subset inherits the original bounds",
						"«HallCondition»(t, M)",
						Derive(func(b *Argument) {
							w := b.FixAs[Set[A]]("w")
							given := b.Assume()
							b.Show(
								"a subset of t is a subset of u",
								BySets(given, parts[0], condition.At(w)))
						}),
					)
					f, first := a.ObtainAs[Fun[A, B]](
						"match the tight subset by descent",
						"«Representatives»(t, M)",
						By(parts[0], hallOnT, descent.At(t, M)),
					)
					_, kDef := a.LetAs[Fun[A, Set[B]]]("K", "λx:A. M(x) ∖ «neighbourhood»(M, t)")
					reserved := a.TermAs[Set[B]]("«neighbourhood»(M, t)")
					smaller := a.Have(
						"the remainder is a proper subfamily",
						"u ∖ t ⊊ u",
						BySets(parts[0], parts[1]),
					)
					hallOnRemainder := a.Have(
						"the remainder satisfies Hall's condition after reserving the tight neighbourhood",
						"«HallCondition»(u ∖ t, K)",
						Derive(func(b *Argument) {
							w := b.FixAs[Set[A]]("w")
							given := b.Assume()
							split := b.Conjuncts(
								given,
								"w is a subset of the remainder",
								"its remaining neighbourhood is finite")
							joined := b.TermAs[Set[A]]("w ∪ t")
							neighbours := b.TermAs[Set[B]]("«neighbourhood»(M, w ∪ t)")
							reduced := b.Have(
								"the neighbourhood left for w is the union's neighbourhood with the reserved part removed",
								"«neighbourhood»(K, w) = «neighbourhood»(M, w ∪ t) ∖ «neighbourhood»(M, t)",
								BySets(kDef),
							)
							restored := b.Have(
								"putting back the reserved part gives a finite neighbourhood and a bound on its size",
								"finite(«neighbourhood»(M, w ∪ t)) ∧ "+
									"card(«neighbourhood»(M, w ∪ t)) ≤ card(«neighbourhood»(K, w)) + card(«neighbourhood»(M, t))",
								By(split[1], parts[2], reduced, cardinality.CardLeDiffAdd.At(neighbours, reserved)),
							)
							sources := b.Have(
								"w and t are disjoint subsets of u",
								"w ⊆ u ∧ t ⊆ u ∧ w ∪ t ⊆ u ∧ w ∩ t = ∅",
								BySets(split[0], parts[0]),
							)
							countSources := b.Have(
								"the union counts both disjoint pieces",
								"card(w ∪ t) = card(w) + card(t)",
								By(
									sources,
									finiteU,
									finite_set.FiniteSubset.At(w, u),
									finite_set.FiniteSubset.At(t, u),
									cardinality.CardUnion.At(w, t)),
							)
							boundUnion := b.Have(
								"apply the original bound to the union",
								"card(w ∪ t) ≤ card(«neighbourhood»(M, w ∪ t))",
								By(sources, restored, condition.At(joined)),
							)
							b.Show(
								"cancel the equal counts of t and its neighbourhood",
								ByArith(restored, countSources, boundUnion, parts[3]))
						}),
					)
					firstRange := a.Have(
						"the representatives of t lie in the reserved neighbourhood",
						"∀x:A. x ∈ t ⇒ f(x) ∈ M(x) ∩ «neighbourhood»(M, t)",
						BySets(first),
					)
					a.Show(
						"reserve the tight neighbourhood for t and match the rest outside it",
						By(smaller, descent, first, firstRange, hallOnRemainder, kDef, At(extend, u, t, M, reserved, f)))
				},
			)

			// With no tight subset, one index x keeps one neighbour y: every
			// nonempty proper subfamily has strictly more neighbours than
			// members, so it can spare y.
			slackCase := ctx.Lemma(
				Statement{
					Binders: "∀u:set(A). ∀M:(A → set(B)).",
					Hypotheses: []string{
						"«HallCondition»(u, M)",
						"∀v:set(A). v ⊊ u ⇒ ∀L:(A → set(B)). «HallCondition»(v, L) ⇒ «Representatives»(v, L)",
						"u ≠ ∅",
						"¬«TightSubset»(u, M)",
					},
					Conclusion: "«Representatives»(u, M)",
				},
				func(
					a *Argument,
					u *Expr[Set[A]],
					M *Arrow2[A, B, Bool],
					condition, descent, nonempty, noTight Fact,
				) {
					x, inU := a.ObtainAs[A](
						"choose one index from the nonempty family",
						"∃x:A. x ∈ u",
						BySets(nonempty))
					oneSource := a.TermAs[Set[A]]("{x}")
					singleNeighbourhood := a.Have(
						"a singleton has its index's neighbourhood",
						"«neighbourhood»(M, {x}) = M(x)",
						BySets(),
					)
					y, neighbour := a.ObtainAs[B](
						"the singleton bound gives a neighbour to its index",
						"∃y:B. y ∈ M(x)",
						Derive(func(b *Argument) {
							b.Cases(b.TermAs[Bool]("M(x) = ∅"))
							b.When(
								"an empty neighbourhood would violate the singleton bound",
								func(c *Argument, empty Fact) {
									within := c.Have(
										"the singleton lies in u",
										"{x} ⊆ u",
										BySets(inU))
									finite := c.Have(
										"an empty neighbourhood is finite",
										"finite(«neighbourhood»(M, {x}))",
										By(empty, singleNeighbourhood, finite_set.FiniteRules.Inst[B]()),
									)
									bound := c.Have(
										"apply the cardinality bound to the singleton",
										"card({x}) ≤ card(«neighbourhood»(M, {x}))",
										By(within, finite, condition.At(oneSource)),
									)
									zero := c.Have(
										"the empty neighbourhood has size zero",
										"card(«neighbourhood»(M, {x})) = 0",
										By(Normalized, empty, singleNeighbourhood, cardinality.CardClauses.Inst[B]()),
									)
									c.Show(
										"one cannot be at most zero",
										ByArith(bound, zero, cardinality.CardSing.At(x)))
								})
							b.Otherwise(
								"a nonempty neighbourhood contains a neighbour",
								func(c *Argument, neighbourhoodNonempty Fact) {
									c.Show(
										"choose a point of M(x)",
										BySets(neighbourhoodNonempty))
								})
						}),
					)
					strict := a.Have(
						"no nonempty proper subset with finite neighbourhood has equal counts",
						"∀v:set(A). v ⊊ u ∧ v ≠ ∅ ∧ finite(«neighbourhood»(M, v)) ⇒ card(v) ≠ card(«neighbourhood»(M, v))",
						By(Normalized, noTight),
					)
					_, kDef := a.LetAs[Fun[A, Set[B]]]("K", "λz:A. M(z) ∖ {y}")
					reserved := a.TermAs[Set[B]]("{y}")
					smaller := a.Have(
						"deleting x gives a proper subfamily",
						"u ∖ {x} ⊊ u",
						BySets(inU),
					)
					hallOnRemainder := a.Have(
						"the remaining neighbourhoods satisfy Hall's condition after deleting y",
						"«HallCondition»(u ∖ {x}, K)",
						Derive(func(b *Argument) {
							w := b.FixAs[Set[A]]("w")
							given := b.Assume()
							b.Cases(b.TermAs[Bool]("w = ∅"))
							b.When(
								"the empty subfamily needs zero neighbours",
								func(c *Argument, empty Fact) {
									zero := c.Have(
										"the empty subfamily has size zero",
										"card(w) = 0",
										By(Normalized, empty, cardinality.CardClauses.Inst[A]()))
									c.Show(
										"the remaining count is nonnegative",
										ByArith(zero))
								})
							b.Otherwise(
								"a nonempty proper subfamily can spare one neighbour",
								func(c *Argument, subfamilyNonempty Fact) {
									neighbours := c.TermAs[Set[B]]("«neighbourhood»(M, w)")
									reduced := c.Have(
										"the neighbourhood of w loses only y",
										"«neighbourhood»(K, w) = «neighbourhood»(M, w) ∖ {y}",
										BySets(kDef),
									)
									restored := c.Have(
										"putting y back gives a finite neighbourhood and raises the count by at most one",
										"finite(«neighbourhood»(M, w)) ∧ "+
											"card(«neighbourhood»(M, w)) ≤ card(«neighbourhood»(K, w)) + card({y})",
										By(given, reduced, finite_set.FiniteSing.At(y), cardinality.CardLeDiffAdd.At(neighbours, reserved)),
									)
									proper := c.Have(
										"w lies in a proper subset of u",
										"w ⊊ u",
										BySets(given, smaller))
									within := c.Have(
										"w is among the subsets tested in Hall's condition",
										"w ⊆ u",
										BySets(proper))
									bound := c.Have(
										"the original condition bounds the size of w by its neighbourhood",
										"card(w) ≤ card(«neighbourhood»(M, w))",
										By(within, restored, condition.At(w)),
									)
									unequal := c.Have(
										"the two sizes cannot be equal",
										"card(w) ≠ card(«neighbourhood»(M, w))",
										By(proper, subfamilyNonempty, restored, strict.At(w)),
									)
									c.Show(
										"the strict bound pays for deleting y",
										ByArith(bound, unequal, restored, cardinality.CardSing.At(y)))
								})
						}),
					)
					first := a.Have(
						"the singleton representative is y",
						"injective_on({x}, λz:A. y) ∧ (∀z:A. z ∈ {x} ⇒ y ∈ M(z) ∩ {y})",
						Simp(Fwd(functions.InjectiveOnDef)),
						BySets(neighbour),
					)
					a.Show(
						"reserve y for x and match the remaining indices without it",
						By(
							smaller,
							descent,
							first,
							hallOnRemainder,
							kDef,
							At(extend, u, oneSource, M, reserved, a.TermAs[Fun[A, B]]("λz:A. y"))))
				},
			)

			return ctx.Theorem(headline, func(
				a *Argument,
				s *Expr[Set[A]],
				N *Arrow2[A, B, Bool],
				finiteS Fact,
			) {
				a.Iff()
				a.Forward(
					"construct distinct representatives by induction on proper subsets",
					func(b *Argument, hall Fact) {
						matched := b.TermAs[Fun[Set[A], Bool]](
							"λu:set(A). ∀M:(A → set(B)). «HallCondition»(u, M) ⇒ «Representatives»(u, M)")
						b.Show(
							"every finite family satisfying Hall's condition is matched, s and N among them",
							ByInduction(finite_set.FiniteInductProperSubset.At(matched, s), finiteS, hall,
								Case(
									"a finite family whose proper subfamilies are all "+
										"matched under Hall's condition is matched under it",
									Derive(func(c *Argument) {
										u := c.FixAs[Set[A]]("u")
										given := c.Assume()
										parts := c.Conjuncts(
											given,
											"u is finite",
											"every proper subfamily of u satisfying Hall's condition has representatives")
										M := c.FixAs[Fun[A, Set[B]]]()
										condition := c.Assume()
										c.Cases(c.TermAs[Bool]("u = ∅"))
										c.When(
											"any map represents the empty family",
											func(d *Argument, empty Fact) {
												d.Take(d.TermAs[Fun[A, B]]("λx:A. εy:B. ⊤"))
												d.Show(
													"there are no neighbourhood or injectivity conditions to check",
													Simp(Fwd(functions.InjectiveOnDef)),
													BySets(empty))
											})
										c.Otherwise(
											"for a nonempty family, test for a tight proper subset",
											func(d *Argument, nonempty Fact) {
												d.Cases(d.TermAs[Bool]("«TightSubset»(u, M)"))
												d.When(
													"a tight subset reserves its neighbourhood",
													func(e *Argument, tight Fact) {
														e.Show(
															"reserving the tight neighbourhood matches u",
															By(parts[0], condition, parts[1], tight, At(tightCase, u, M)))
													})
												d.Otherwise(
													"a strict bound pays for deleting one representative",
													func(e *Argument, noTight Fact) {
														e.Show(
															"reserving one neighbour for one index matches u",
															By(condition, parts[1], nonempty, noTight, At(slackCase, u, M)))
													})
											})
									}))))
					})
				a.Backward(
					"a matching supplies enough neighbours for each subfamily",
					func(b *Argument, match Fact) {
						f, selects := b.UnpackAs[Fun[A, B]](match)
						t := b.FixAs[Set[A]]("t")
						subfamily := b.Assume()
						pieces := b.Conjuncts(
							selects,
							"the representatives are distinct",
							"each representative is a neighbour")
						images := b.TermAs[Set[B]]("image(f, t)")
						neighbourhood := b.TermAs[Set[B]]("«neighbourhood»(N, t)")
						contained := b.Have(
							"the representatives lie inside the neighbourhood",
							"image(f, t) ⊆ «neighbourhood»(N, t)",
							BySets(subfamily, pieces[1]))
						count := b.Have(
							"they have the same count as the subfamily",
							"card(image(f, t)) = card(t)",
							By(
								subfamily,
								finiteS,
								pieces[0],
								finite_set.FiniteSubset.At(t, s),
								functions.InjectiveOnSubset.At(f, t, s),
								cardinality.CardImageInj.At(f, t)))
						b.Show(
							"compare with the finite neighbourhood",
							By(Normalized, subfamily, contained, count, cardinality.CardSubset.At(images, neighbourhood)))
					})
			})
		},
	),
})}
