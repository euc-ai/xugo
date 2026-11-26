// tower.go — the tower of an operation on sets, and the fixed point it
// reaches. An operation f on sets is INFLATIONARY when it only enlarges
// its argument, s ⊆ f(s). Its tower, `set_tower(f)`, is the least
// family of sets closed under f — the first rule — and under the union
// of any of its subfamilies — the second. Under an inflationary f the
// tower is a chain under inclusion, and its union is a set f fixes.
// The README carries the chapter story.

package order

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The tower
// ---------------------------------------------------------------------------

// setTower — the tower of an operation f on sets: the least family of
// sets closed under f and under the union of any of its subfamilies.
// The empty union puts the empty set in it; and where f only enlarges
// its argument, the tower is what f reaches from ∅ when it is iterated
// through every limit, which is how the chapter iterates without
// ordinals. The theorems the two rules come with are the faces below.
var setTower = family.DefineInductive(registry.InductiveEntry{
	Name: "setTower",
	Keys: registry.InductiveKeys{
		Rules:        "prop_6a736edc9673daa6",
		Induct:       "prop_405f9fbd7719dbf5",
		Cases:        "prop_b81e127c4b9dd707",
		InductStrong: "prop_629ce143c2f4ba3d",
	},
	Const:  "set_tower",
	Type:   "(set(A) → set(A)) → set(A) → bool",
	Params: []string{"f"},
	Rules: []string{
		"∀s:set(A). set_tower(f, s) ⇒ set_tower(f, f(s))",
		"∀F:set(set(A)). (∀s:set(A). s ∈ F ⇒ set_tower(f, s)) ⇒ set_tower(f, ⋃F)",
	},
	Deps: []registry.EntryLike{set_basic.SetMemberDef, set_basic.BigUnionDef},
})

// setTowerRules — f carries a set of the tower to a set of the tower,
// and the union of a family of sets of the tower is a set of the
// tower: the definition's rule set, registered verbatim.
var setTowerRules = setTowerRulesThm{setTower.Rules}

// setTowerInduct — rule induction along the tower: a property of sets
// that f preserves, and that the union of a family has when each of
// its members has it, holds of every set of the tower.
var setTowerInduct = setTowerInductThm{setTower.Induct}

// setTowerInductStrong — the same induction, with each step told that
// the sets it reasons from are themselves sets of the tower.
var setTowerInductStrong = setTowerInductStrongThm{setTower.InductStrong}

// setTowerCases — the two rules are exhaustive: a set of the tower is
// f of one, or the union of a family of them.
var setTowerCases = setTowerCasesThm{setTower.Cases}

// ---------------------------------------------------------------------------
// The tower of an inflationary operation is a chain
// ---------------------------------------------------------------------------

// towerStepComparable — rule induction along the tower, on the property
// of standing on one side of the step from d to f(d): lying in d, or
// containing f(d). Across f, a set that contains f(d) only grows, f
// being inflationary; and a set inside d is d itself, whose image is
// f(d), or another set, whose image the hypothesis on d keeps inside
// d. Across a union, a family whose members all lie in d has its union
// in d, and a member that does not lie in d contains f(d) and carries
// it into the union. The strengthened principle is what lets the first
// case spend the hypothesis on d: it hands over that the set the step
// starts from is itself a set of the tower.
var towerStepComparable = towerStepComparableThm{family.Add(registry.ProofEntry{
	Name: "towerStepComparable",
	Key:  "prop_d7fe929be439d61e",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(set(A) → set(A)). ∀d c:set(A).",
			Hypotheses: []string{
				"∀s:set(A). s ⊆ f(s)",
				"∀e:set(A). set_tower(f, e) ∧ e ⊆ d ⇒ d = e ∨ f(e) ⊆ d",
				"set_tower(f, c)",
			},
			Conclusion: "c ⊆ d ∨ f(d) ⊆ c",
		},
		func(
			a *Argument,
			f *Arrow[Set[A], Set[A]],
			d, c *Expr[Set[A]],
			inflationary, keepsInside, cInTower Fact,
		) {
			imageOfD := f.Apply(d)

			a.Show(
				"rule induction along the tower carries the property to c",
				ByInduction(setTowerInductStrong, cInTower,
					Case(
						"f preserves it: the image of a set that lies in d or contains f(d) does one of the two as well",
						Derive(func(b *Argument) {
							s := b.FixAs[Set[A]]("s")
							imageOfS := f.Apply(s)
							atS := b.Conjuncts(
								b.Assume(),
								"s is a set of the tower",
								"s lies in d, or contains f(d)")
							sInTower, sOnOneSide := atS[0], atS[1]

							b.Do(sOnOneSide.SplitDisj(
								LeftHolds(
									"s lies in d, so it is d itself or f keeps its image inside d",
									Given(func(g *Argument, below Fact) {
										g.Cases(g.Term("d = s"))
										g.When(
											"d is s itself, so f(d) is f(s) and lies in it",
											func(h *Argument, same Fact) {
												h.Show(
													"with s written for d, the second alternative is the inclusion of f(s) in itself",
													same.Rw(),
													By(set_order.SubsetRefl.At(imageOfS)))
											})
										g.Otherwise(
											"d is another set, and the hypothesis on d leaves f(s) inside d",
											func(h *Argument, differ Fact) {
												h.Show(
													"the first alternative, read off the hypothesis at s",
													By(Normalized, sInTower, below, differ, keepsInside.At(s)))
											})
									})),
								RightHolds(
									"s contains f(d), and f(s) contains s",
									Given(func(g *Argument, above Fact) {
										g.Show(
											"the second alternative: f(d) lies in s, which lies in f(s)",
											By(above, inflationary.At(s), set_order.SubsetTrans.At(imageOfD, s, imageOfS)))
									})),
							))
						})),
					Case(
						"unions preserve it: a family whose members each lie in "+
							"d or contain f(d) has a union that does one of the two",
						Derive(func(b *Argument) {
							F := b.FixAs[Set[Set[A]]]("F")
							union := b.TermAs[Set[A]]("⋃F")
							members := b.Assume()

							b.Cases(b.Term("∀m:set(A). m ∈ F ⇒ m ⊆ d"))
							b.When(
								"every member of F lies in d, and then so does their union",
								func(g *Argument, allBelow Fact) {
									g.Show(
										"the first alternative: a union of sets inside d is inside d",
										By(Normalized, allBelow, set_order.UnionsSubset.At(F, d)))
								})
							b.Otherwise(
								"some member of F does not lie in d, so it contains f(d), and the union contains it",
								func(g *Argument, notAll Fact) {
									m, mOutside := g.ObtainAs[Set[A]](
										"a member of F that does not lie in d",
										"∃m:set(A). m ∈ F ∧ ¬(m ⊆ d)",
										By(Normalized, notAll))
									g.Show(
										"the second alternative: f(d) lies in m, the alternative left to m, and m lies in the union",
										By(
											mOutside,
											members.At(m),
											set_order.MemberSubsetUnions.At(F, m),
											set_order.SubsetTrans.At(imageOfD, m, union)))
								})
						}))))
		}),
})}

// TowerSuccessor — f(c) is the next set of the tower after c: a set of
// the tower that contains c is c itself or already contains f(c). The
// proof is rule induction along the tower, on the hypothesis
// `towerStepComparable` asks at a single set: that f keeps inside the
// set every set of the tower lying strictly inside it. The comparison
// does not ask the set it is made at to be a set of the tower, and the
// property carries the tower membership of the lower sets itself, so the
// plain principle serves.
var TowerSuccessor = towerSuccessorThm{family.Add(registry.ProofEntry{
	Name: "TowerSuccessor",
	Key:  "prop_ffcbdb185527864b",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(set(A) → set(A)). ∀c d:set(A).",
			Hypotheses: []string{
				"∀s:set(A). s ⊆ f(s)",
				"set_tower(f, c) ∧ set_tower(f, d) ∧ c ⊆ d",
			},
			Conclusion: "d = c ∨ f(c) ⊆ d",
		},
		func(a *Argument, f *Arrow[Set[A], Set[A]], c, d *Expr[Set[A]], inflationary, nested Fact) {
			parts := a.Conjuncts(
				nested,
				"c is a set of the tower",
				"d is a set of the tower",
				"c lies in d")
			cInTower, dInTower, cBelowD := parts[0], parts[1], parts[2]

			atD := a.Have(
				"rule induction along the tower carries the property to d",
				"∀e:set(A). set_tower(f, e) ∧ e ⊆ d ⇒ d = e ∨ f(e) ⊆ d",
				ByInduction(setTowerInduct, dInTower,
					Case(
						"f preserves it: a set of the tower inside f(s) is f(s) "+
							"itself, or lies in s, and then is s or has its image inside s",
						Derive(func(b *Argument) {
							s := b.FixAs[Set[A]]("s")
							imageOfS := f.Apply(s)
							atS := b.Assume()
							e := b.FixAs[Set[A]]("e")
							imageOfE := f.Apply(e)
							aboutE := b.Conjuncts(
								b.Assume(),
								"e is a set of the tower",
								"e lies in f(s)")
							eInTower, eBelowImage := aboutE[0], aboutE[1]

							eBelowS := b.Have(
								"e lies in s or contains f(s): the comparison at s, whose hypothesis is the property at s",
								"e ⊆ s ∨ f(s) ⊆ e",
								By(inflationary, atS, eInTower, towerStepComparable.At(f, s, e)))
							b.Do(eBelowS.DismissRight(
								"e contains f(s) and lies in it, so f(s) is e",
								Given(func(g *Argument, above Fact) {
									g.Show(
										"the first alternative: f(s) and e lie in each other",
										By(Normalized, eBelowImage, above, set_order.SubsetAntisym.At(imageOfS, e)))
								})))

							readAtE := b.Have(
								"the property at s, read at e: s is e, or f(e) lies in s",
								"s = e ∨ f(e) ⊆ s",
								By(eInTower, eBelowS, atS.At(e)))
							b.Do(readAtE.SplitDisj(
								LeftHolds(
									"s is e itself, so f(e) is f(s) and lies in it",
									Given(func(g *Argument, same Fact) {
										g.Show(
											"with e written for s, the second alternative is the inclusion of f(e) in itself",
											same.Rw(),
											By(set_order.SubsetRefl.At(imageOfE)))
									})),
								RightHolds(
									"f(e) lies in s, and f(s) contains s",
									Given(func(g *Argument, inside Fact) {
										g.Show(
											"the second alternative: f(e) lies in s, which lies in f(s)",
											By(inside, inflationary.At(s), set_order.SubsetTrans.At(imageOfE, s, imageOfS)))
									})),
							))
						})),
					Case(
						"unions preserve it: a set of the tower inside ⋃F contains "+
							"every member of F, or lies in a member that has the property",
						Derive(func(b *Argument) {
							F := b.FixAs[Set[Set[A]]]("F")
							union := b.TermAs[Set[A]]("⋃F")
							atMembers := b.Assume()
							e := b.FixAs[Set[A]]("e")
							imageOfE := f.Apply(e)
							aboutE := b.Conjuncts(
								b.Assume(),
								"e is a set of the tower",
								"e lies in the union of F")
							eInTower, eBelowUnion := aboutE[0], aboutE[1]

							notAll := b.Unless(
								b.Term("∀m:set(A). m ∈ F ⇒ m ⊆ e"),
								"every member of F lies in e: then so does their union, which is therefore e",
								Given(func(g *Argument, allBelow Fact) {
									g.Show(
										"the first alternative: the union and e lie in each other",
										By(
											Normalized,
											allBelow,
											eBelowUnion,
											set_order.UnionsSubset.At(F, e),
											set_order.SubsetAntisym.At(union, e)))
								}))

							m, mOutside := b.ObtainAs[Set[A]](
								"a member of F that does not lie in e",
								"∃m:set(A). m ∈ F ∧ ¬(m ⊆ e)",
								By(Normalized, notAll))
							imageOfM := f.Apply(m)

							eBelowM := b.Have(
								"e lies in m or contains f(m): the comparison at m, which has the property as a member of F",
								"e ⊆ m ∨ f(m) ⊆ e",
								By(inflationary, mOutside, atMembers.At(m), eInTower, towerStepComparable.At(f, m, e)))
							b.Do(eBelowM.DismissRight(
								"e does not contain f(m): m lies in f(m), and m does not lie in e",
								Given(func(g *Argument, above Fact) {
									g.Show(
										"containing f(m), e would contain m, which lies in f(m)",
										By(above, mOutside, inflationary.At(m), set_order.SubsetTrans.At(m, imageOfM, e)))
								})))

							imageInM := b.Have(
								"the property of the members of F, read at m and e: m is e, or f(e) lies in m",
								"m = e ∨ f(e) ⊆ m",
								By(mOutside, eInTower, eBelowM, atMembers.At(m, e)))
							b.Do(imageInM.DismissLeft(
								"m is not e, for m does not lie in e",
								Given(func(g *Argument, same Fact) {
									g.Show(
										"equal sets lie in each other, and m does not lie in e",
										By(Normalized, same, mOutside, set_order.SubsetAntisymEq.At(m, e)))
								})))

							b.Show(
								"the second alternative: f(e) lies in m, and m lies in the union",
								By(
									imageInM,
									mOutside,
									set_order.MemberSubsetUnions.At(F, m),
									set_order.SubsetTrans.At(imageOfE, m, union)))
						}))))

			a.Show(
				"the property at d, read at c",
				By(cInTower, cBelowD, atD.At(c)))
		}),
})}

// TowerChain — the tower is a chain under inclusion. Compare c across
// the step from d to f(d): `TowerSuccessor` says f keeps inside d every
// set of the tower lying strictly inside it, which is what the
// comparison at d asks, so c lies in d or contains f(d) — and a set
// that contains f(d) contains d, f being inflationary.
var TowerChain = towerChainThm{family.Add(registry.ProofEntry{
	Name: "TowerChain",
	Key:  "prop_4faeaa1f9e32cfaf",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(set(A) → set(A)). ∀c d:set(A).",
			Hypotheses: []string{
				"∀s:set(A). s ⊆ f(s)",
				"set_tower(f, c) ∧ set_tower(f, d)",
			},
			Conclusion: "c ⊆ d ∨ d ⊆ c",
		},
		func(a *Argument, f *Arrow[Set[A], Set[A]], c, d *Expr[Set[A]], inflationary, both Fact) {
			imageOfD := f.Apply(d)
			inTower := a.Conjuncts(
				both,
				"c is a set of the tower",
				"d is a set of the tower")
			cInTower, dInTower := inTower[0], inTower[1]

			keepsInside := a.Have(
				"f keeps inside d every set of the tower lying strictly inside it",
				"∀e:set(A). set_tower(f, e) ∧ e ⊆ d ⇒ d = e ∨ f(e) ⊆ d",
				a.ForEach(func(e *Expr[Set[A]]) Action {
					return By(inflationary, dInTower, TowerSuccessor.At(f, e, d))
				}))
			oneSide := a.Have(
				"so c lies in d or contains f(d): the comparison at d",
				"c ⊆ d ∨ f(d) ⊆ c",
				By(inflationary, keepsInside, cInTower, towerStepComparable.At(f, d, c)))
			a.Show(
				"and a set that contains f(d) contains d, which lies in f(d)",
				By(oneSide, inflationary.At(d), set_order.SubsetTrans.At(d, imageOfD, c)))
		}),
})}

// ---------------------------------------------------------------------------
// The fixed point
// ---------------------------------------------------------------------------

// BourbakiWitt — the fixed point is the top of the tower of f: the
// union of all its sets. That union is a set of the tower by the second
// rule, so its image is one by the first, and lies in the union as
// every member of a family does; f being inflationary, the union lies
// in its image too, and the two are equal. The property reaches the top
// by rule induction along the tower. f preserves it by hypothesis; and
// a family of sets of the tower is a chain, the tower being one
// (`TowerChain`), so the hypothesis on chains hands the property to its
// union. The strengthened principle is what lets the union case call its
// family a chain: it hands over that the members are sets of the tower.
var BourbakiWitt = bourbakiWittThm{family.Add(registry.ProofEntry{
	Name: "BourbakiWitt",
	Key:  "prop_f78e327003d1f5e4",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(set(A) → set(A)). ∀P:(set(A) → bool).",
			Hypotheses: []string{
				"∀s:set(A). s ⊆ f(s)",
				"∀s:set(A). P(s) ⇒ P(f(s))",
				"∀F:set(set(A)). (∀s:set(A). s ∈ F ⇒ P(s)) ∧ (∀s t:set(A). s ∈ F ∧ t ∈ F ⇒ s ⊆ t ∨ t ⊆ s) ⇒ P(⋃F)",
			},
			Conclusion: "∃s:set(A). P(s) ∧ f(s) = s",
		},
		func(a *Argument, f *Arrow[Set[A], Set[A]], P *Expr[Set[Set[A]]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"f only enlarges its argument",
				"f preserves P",
				"P passes to the union of a chain of sets that have it")
			inflationary, preserved, passesToChainUnions := parts[0], parts[1], parts[2]

			// The tower as a family of sets, and its union.
			tower, towerDef := a.LetAs[Set[Set[A]]]("tower", "{t:set(A) | set_tower(f, t)}")
			top, topDef := a.LetAs[Set[A]]("top", "⋃tower")
			imageOfTop := f.Apply(top)

			inFamily := a.Have(
				"the members of that family are the sets of the tower",
				"∀s:set(A). s ∈ tower ⇔ set_tower(f, s)",
				BySets(towerDef))
			topInTower := a.Have(
				"so top, the union of a family of sets of the tower, is one of them: the second rule",
				"set_tower(f, top)",
				By(topDef, inFamily, setTowerRules.At(f)))
			imageInTower := a.Have(
				"and f(top) is one, by the first rule",
				"set_tower(f, f(top))",
				By(topInTower, setTowerRules.At(f)))
			imageBelow := a.Have(
				"f(top) is then a member of the family, and a member lies in the union",
				"f(top) ⊆ top",
				By(
					Normalized,
					topDef,
					imageInTower,
					inFamily.At(imageOfTop),
					set_order.MemberSubsetUnions.At(tower, imageOfTop)))
			fixed := a.Have(
				"top lies in f(top), f being inflationary, and the two inclusions are the equation",
				"f(top) = top",
				By(imageBelow, inflationary.At(top), set_order.SubsetAntisym.At(imageOfTop, top)))

			hasP := a.Have(
				"every set of the tower has P, by rule induction along it, and top is one",
				"P(top)",
				ByInduction(setTowerInductStrong, topInTower,
					Case(
						"f preserves it: the hypothesis on f, which asks nothing of the tower",
						By(preserved)),
					Case(
						"unions preserve it: a family of sets of the tower "+
							"that all have P is a chain, and P passes to its union",
						Derive(func(b *Argument) {
							F := b.FixAs[Set[Set[A]]]("F")
							members := b.Assume()

							chain := b.Have(
								"any two members of F are comparable, both being sets of the tower, which is a chain",
								"∀s t:set(A). s ∈ F ∧ t ∈ F ⇒ s ⊆ t ∨ t ⊆ s",
								b.ForEach(func(s *Expr[Set[A]]) Action {
									return b.ForEach(func(t *Expr[Set[A]]) Action {
										return By(inflationary, members.At(s), members.At(t), TowerChain.At(f, s, t))
									})
								}))
							b.Show(
								"so F is a chain of sets that have P, and the hypothesis on chains gives P of its union",
								By(chain, members, passesToChainUnions.At(F)))
						}))))

			a.Take(top)
			a.Show(
				"top has P, and f fixes it",
				By(hasP, fixed))
		}),
})}

// ---------------------------------------------------------------------------
// The tower is well-ordered
// ---------------------------------------------------------------------------

// TowerLeast — under an inflationary f the tower is well-ordered by
// inclusion: a family G of sets of the tower that is not empty has a
// member that lies in every member. The union u of the common lower
// bounds in the tower is that member. It lies in every member of G;
// were it no member, its successor would be another common lower
// bound, so f would not enlarge u, and u would contain the entire
// tower. A member of G, which G has, not being empty, would then lie
// in u and contain it: u equals that member, so it is in G after all.
var TowerLeast = towerLeastThm{family.Add(registry.ProofEntry{
	Name: "TowerLeast",
	Key:  "prop_35977568ab6b7288",
	Reading: "Both hypotheses are load-bearing. G ≠ ∅ supplies the member. Without " +
		"the inflationary hypothesis the tower need not be a chain: on a two-point " +
		"type {a, b}, an f with f(∅) = {a} and f({a}) = {b} puts {a} and {b} in its " +
		"tower, a family with no least member. With f the identity the tower is {∅}.",
	Build: family.Sections(Statement{
		Binders: "∀f:(set(A) → set(A)). ∀G:set(set(A)).",
		Hypotheses: []string{
			"∀s:set(A). s ⊆ f(s)",
			"G ≠ ∅",
			"∀s:set(A). s ∈ G ⇒ set_tower(f, s)",
		},
		Conclusion: "∃m:set(A). m ∈ G ∧ (∀s:set(A). s ∈ G ⇒ m ⊆ s)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			containsTower := ctx.Lemma(Statement{
				Binders: "∀f:(set(A) → set(A)). ∀u c:set(A).",
				Hypotheses: []string{
					"∀s:set(A). s ⊆ f(s)",
					"set_tower(f, u)",
					"f(u) ⊆ u",
					"set_tower(f, c)",
				},
				Conclusion: "c ⊆ u",
			},
				func(a *Argument, f *Arrow[Set[A], Set[A]], u, c *Expr[Set[A]], hypotheses Fact) {
					parts := a.Conjuncts(
						hypotheses,
						"f only enlarges its argument",
						"u is a set of the tower",
						"f does not enlarge u",
						"c is a set of the tower")
					inflationary, uInTower, imageBelow, cInTower := parts[0], parts[1], parts[2], parts[3]

					a.Show(
						"every set of the tower lies in u, by strong rule induction",
						ByInduction(setTowerInductStrong, cInTower,
							Case(
								"across f: a tower set inside u is u itself, or its image already lies in u",
								Derive(func(b *Argument) {
									s := b.FixAs[Set[A]]("s")
									atS := b.Assume()
									b.Show(
										"the successor comparison and f(u) contained in u keep the image inside u",
										By(inflationary, uInTower, imageBelow, atS, TowerSuccessor.At(f, s, u)))
								})),
							Case(
								"across unions: a union of sets inside u lies in u",
								Derive(func(b *Argument) {
									F := b.FixAs[Set[Set[A]]]("F")
									members := b.Assume()
									b.Show(
										"every member lies in u, and therefore so does the union",
										By(members, set_order.UnionsSubset.At(F, u)))
								}))))
				})

			return ctx.Theorem(headline,
				func(a *Argument, f *Arrow[Set[A], Set[A]], G *Expr[Set[Set[A]]], hypotheses Fact) {
					parts := a.Conjuncts(
						hypotheses,
						"f only enlarges its argument",
						"G has a member",
						"every member of G is a set of the tower")
					inflationary, nonempty, members := parts[0], parts[1], parts[2]
					H, hDef := a.LetAs[Set[Set[A]]](
						"H", "{s:set(A) | set_tower(f, s) ∧ (∀t:set(A). t ∈ G ⇒ s ⊆ t)}")
					u, uDef := a.LetAs[Set[A]]("u", "⋃H")
					imageOfU := f.Apply(u)

					inFamily := a.Have(
						"H consists of the common lower bounds that lie in the tower",
						"∀s:set(A). s ∈ H ⇔ set_tower(f, s) ∧ (∀t:set(A). t ∈ G ⇒ s ⊆ t)",
						BySets(hDef))
					uInTower := a.Have(
						"their union is a set of the tower",
						"set_tower(f, u)",
						By(inFamily, uDef, setTowerRules.At(f)))
					lower := a.Have(
						"their union lies in every member of G",
						"∀t:set(A). t ∈ G ⇒ u ⊆ t",
						a.ForEach(func(t *Expr[Set[A]]) Action {
							return By(inFamily, uDef, set_order.UnionsSubset.At(H, t))
						}))
					inG := a.Have(
						"the union is itself a member of G",
						"u ∈ G",
						Derive(func(b *Argument) {
							notInG := b.SupposeNot()
							imageLower := b.Have(
								"every member of G properly contains u, so it contains the successor of u",
								"∀t:set(A). t ∈ G ⇒ f(u) ⊆ t",
								b.ForEach(func(t *Expr[Set[A]]) Action {
									return By(notInG, inflationary, members.At(t), lower.At(t), uInTower, TowerSuccessor.At(f, u, t))
								}))
							imageInH := b.Have(
								"f(u) is another common lower bound in the tower, hence belongs to H",
								"f(u) ∈ H",
								By(inFamily.At(imageOfU), imageLower, uInTower, setTowerRules.At(f)))
							imageBelow := b.Have(
								"as a member of H, f(u) lies in its union u",
								"f(u) ⊆ u",
								By(Normalized, uDef, imageInH, set_order.MemberSubsetUnions.At(H, imageOfU)))
							allBelow := b.Have(
								"a tower set that f does not enlarge contains the entire tower, including every member of G",
								"∀t:set(A). t ∈ G ⇒ t ⊆ u",
								b.ForEach(func(t *Expr[Set[A]]) Action {
									return By(inflationary, members.At(t), uInTower, imageBelow, At(containsTower, f, u, t))
								}))
							t, tInG := b.ObtainAs[Set[A]](
								"choose a member of the nonempty family G",
								"∃t:set(A). t ∈ G",
								By(nonempty, set_basic.MemberNotEmpty.At(G)))
							same := b.Have(
								"the chosen member and u contain each other, so they are equal",
								"t = u",
								By(tInG, lower.At(t), allBelow.At(t), set_order.SubsetAntisym.At(t, u)))
							b.Show(
								"the chosen member is u, contradicting its absence from G",
								By(Normalized, notInG, same, tInG))
						}))
					a.Take(u)
					a.Show(
						"u is a member of G lying in every member",
						By(lower, inG))
				})
		}),
})}
