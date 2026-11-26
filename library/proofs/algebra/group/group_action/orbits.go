// orbits.go — the axioms of an action and its restrictions to a subgroup
// and to a subset the group keeps; the orbits, which partition X and
// regroup a sum over it; the stabilizers; and the orbit–stabilizer theorem.

package group_action

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The axioms
// ---------------------------------------------------------------------------

// ActingGroup — the acting group is a group on its carrier: the
// structure at which the group chapter's laws apply to the elements
// that act.
var ActingGroup = actingGroupThm{family.Add(registry.ProofEntry{
	Name:  "ActingGroup",
	Key:   "prop_af1c674a8ace3080",
	Build: GroupAction.Axiom("group_on(G)"),
})}

// ActIn — acting by an element of the group keeps the points of X in X.
var ActIn = actInThm{family.Add(registry.ProofEntry{
	Name: "ActIn",
	Key:  "prop_766a24d9b8a373d8",
	Build: GroupAction.Axiom(Statement{
		Binders: "∀g:A. ∀x:B.",
		Hypotheses: []string{
			"g ∈ G.carrier",
			"x ∈ X",
		},
		Conclusion: "act(g, x) ∈ X",
	}),
})}

// ActOne — the identity moves no point of X.
var ActOne = actOneThm{family.Add(registry.ProofEntry{
	Name: "ActOne",
	Key:  "prop_835dae1fa1459569",
	Build: GroupAction.Axiom(Statement{
		Binders: "∀x:B.",
		Hypotheses: []string{
			"x ∈ X",
		},
		Conclusion: "act(G.one, x) = x",
	}),
})}

// ActMul — acting by a product is acting by its factors in turn, the
// right-hand factor first.
var ActMul = actMulThm{family.Add(registry.ProofEntry{
	Name: "ActMul",
	Key:  "prop_aec61a32d22c932d",
	Build: GroupAction.Axiom(Statement{
		Binders: "∀g h:A. ∀x:B.",
		Hypotheses: []string{
			"g ∈ G.carrier",
			"h ∈ G.carrier",
			"x ∈ X",
		},
		Conclusion: "act(g * h, x) = act(g, act(h, x))",
	}),
})}

// InvActCancel — acting by the inverse of g undoes acting by g: the two
// in turn are acting by G.inv(g) * g, the identity.
var InvActCancel = invActCancelThm{family.Add(registry.ProofEntry{
	Name: "InvActCancel",
	Key:  "prop_ef7f3c46bb57af0b",
	Build: GroupAction.Law(Statement{
		Binders: "∀g:A. ∀x:B.",
		Hypotheses: []string{
			"g ∈ G.carrier",
			"x ∈ X",
		},
		Conclusion: "act(G.inv(g), act(g, x)) = x",
	},
		func(a *Argument, action Fact, g *Expr[A], gIn Fact, x *Expr[B], xIn Fact) {
			acting := ActingGroup.Read(action)
			gm, xm := a.MemberOf[on.Any](g, gIn), a.MemberOf[on.Any](x, xIn)
			inverse := group.InvIn.Read(acting).At(gm)
			a.Show(
				"acting by G.inv(g) after g is acting by G.inv(g) * g, which is G.one, and G.one fixes x",
				By(
					Normalized,
					ActMul.Read(action).At(inverse, gm, xm),
					group.LeftInverseOn.Read(acting).At(gm),
					ActOne.Read(action).At(xm)))
		}),
})}

// RestrictAction — an action restricts to every subgroup of the acting
// group: the restricted record is a group on K (group.SubgroupGroupOn),
// its identity and product are G's, and K lies in G.carrier, so each axiom
// at the points of K is the ambient one.
var RestrictAction = restrictActionThm{family.Add(registry.ProofEntry{
	Name: "RestrictAction",
	Key:  "prop_1f1f7c861e3ab984",
	Build: GroupAction.Law(Statement{
		Binders: "∀K:set(A).",
		Hypotheses: []string{
			"subgroup(G, K)",
		},
		Conclusion: "group_action(restrict_group(G, K), X, act)",
	},
		func(a *Argument, action Fact, K *Expr[Set[A]], subgroup Fact) {
			a.Do(GroupAction.Intro(
				Case(
					"the restricted record is a group on K",
					By(group.SubgroupGroupOn.Read(ActingGroup.Read(action)), subgroup)),
				Case(
					"an element of K lies in G.carrier, so it keeps X in X",
					By(ActIn.Read(action), subgroup, group.SubgroupSubset, set_basic.SubsetDef)),
				Case(
					"the restricted record's identity is G's, which fixes every point",
					By(ActOne.Read(action))),
				Case(
					"its product is G's and the elements of K lie in "+
						"G.carrier, so a product acts by its factors in turn",
					By(ActMul.Read(action), subgroup, group.SubgroupSubset, set_basic.SubsetDef)),
			))
		}),
})}

// SubsetAction — an action restricts to every subset of X the group keeps
// in itself: the acting group is the same, Y is kept by hypothesis, and the
// identity and product axioms hold at the points of Y because they lie in
// X.
var SubsetAction = subsetActionThm{family.Add(registry.ProofEntry{
	Name: "SubsetAction",
	Key:  "prop_aee1e80ce3bd7325",
	Build: GroupAction.Law(Statement{
		Binders: "∀Y:set(B).",
		Hypotheses: []string{
			"Y ⊆ X",
			"∀g:A. ∀y:B. g ∈ G.carrier ∧ y ∈ Y ⇒ act(g, y) ∈ Y",
		},
		Conclusion: "group_action(G, Y, act)",
	},
		func(a *Argument, action Fact, Y *Expr[Set[B]], inside, kept Fact) {
			a.Do(GroupAction.Intro(
				Case(
					"the acting group is the same group",
					By(ActingGroup.Read(action))),
				Case(
					"its elements keep Y in Y, as given",
					By(kept)),
				Case(
					"the points of Y lie in X, where the identity fixes them",
					By(ActOne.Read(action), inside, set_basic.SubsetDef)),
				Case(
					"and where acting by a product is acting by its factors in turn",
					By(ActMul.Read(action), inside, set_basic.SubsetDef)),
			))
		}),
})}

// ---------------------------------------------------------------------------
// The orbits
// ---------------------------------------------------------------------------

// InOwnOrbit — a point of X lies in its own orbit: the identity moves it
// nowhere.
var InOwnOrbit = inOwnOrbitThm{family.Add(registry.ProofEntry{
	Name: "InOwnOrbit",
	Key:  "prop_c5fa250763bf1acf",
	Build: GroupAction.Law(Statement{
		Binders: "∀x:B.",
		Hypotheses: []string{
			"x ∈ X",
		},
		Conclusion: "x ∈ group_orbit(G, act, x)",
	},
		func(a *Argument, action Fact, x *Expr[B], xIn Fact) {
			acting := ActingGroup.Read(action)
			xm := a.MemberOf[on.Any](x, xIn)
			moves := a.TermAs[Fun[A, B]]("λg:A. act(g, x)")
			carrier, one := a.TermAs[Set[A]]("G.carrier"), a.TermAs[A]("G.one")
			a.Show(
				"x is act(G.one, x), where the identity of G.carrier moves it",
				Simp(Fwd(GroupOrbitDef)),
				By(
					Normalized,
					ActOne.Read(action).At(xm),
					group.OneIn.Read(acting),
					set_image.FunInImage.At(moves, carrier, one)))
		}),
})}

// OrbitSubset — the orbit of a point of X lies in X: every element of the
// group keeps X in X.
var OrbitSubset = orbitSubsetThm{family.Add(registry.ProofEntry{
	Name: "OrbitSubset",
	Key:  "prop_48853450dffc0585",
	Build: GroupAction.Law(Statement{
		Binders: "∀x:B.",
		Hypotheses: []string{
			"x ∈ X",
		},
		Conclusion: "group_orbit(G, act, x) ⊆ X",
	},
		func(a *Argument, action Fact, x *Expr[B], xIn Fact) {
			a.Show(
				"each act(g, x) with g in G.carrier lies in X",
				Simp(Fwd(GroupOrbitDef)),
				By(ActIn.Read(action), set_image.ImageSubsetIff, xIn))
		}),
})}

// OrbitOfAct — a point of X and its image under an element of the group
// have one orbit. Acting by k first moves the orbit of a point into the
// orbit of the point it started from, act(m, act(k, w)) being
// act(m * k, w); and acting by G.inv(g) brings act(g, x) back to x, so
// the inclusion holds both ways.
var OrbitOfAct = orbitOfActThm{family.Add(registry.ProofEntry{
	Name: "OrbitOfAct",
	Key:  "prop_5eb80e759103330d",
	Build: GroupAction.Law(Statement{
		Binders: "∀g:A. ∀x:B.",
		Hypotheses: []string{
			"g ∈ G.carrier",
			"x ∈ X",
		},
		Conclusion: "group_orbit(G, act, act(g, x)) = group_orbit(G, act, x)",
	},
		func(a *Argument, action Fact, g *Expr[A], gIn Fact, x *Expr[B], xIn Fact) {
			acting := ActingGroup.Read(action)
			into := a.Have(
				"the orbit of act(k, w) lies in the orbit of w: act(m, act(k, w)) is act(m * k, w)",
				"∀k:A. ∀w:B. k ∈ G.carrier ∧ w ∈ X ⇒ group_orbit(G, act, act(k, w)) ⊆ group_orbit(G, act, w)",
				Derive(func(b *Argument) {
					b.FixAs[A]("k")
					b.FixAs[B]("w")
					given := b.Assume()
					b.Show(
						"m * k lies in G.carrier for every m there",
						Simp(Fwd(GroupOrbitDef)),
						BySets(ActMul.Read(action), group.MulIn.Read(acting), given))
				}))
			gm, xm := a.MemberOf[on.Any](g, gIn), a.MemberOf[on.Any](x, xIn)
			inverse := group.InvIn.Read(acting).At(gm)
			moved := ActIn.Read(action).At(gm, xm)
			back := a.Have(
				"and the orbit of x, which is the orbit of "+
					"act(G.inv(g), act(g, x)), lies in the orbit of act(g, x)",
				"group_orbit(G, act, x) ⊆ group_orbit(G, act, act(g, x))",
				By(Normalized, into.At(inverse, moved), InvActCancel.Read(action).At(gm, xm), inverse, moved))
			a.Show(
				"so the two orbits are equal",
				By(set_order.SubsetAntisym, into.At(g, x), back, gIn, xIn))
		}),
})}

// OrbitOfMember — every point of the orbit of x has the orbit of x: it is
// act(h, x) for some h in the group (OrbitOfAct).
var OrbitOfMember = orbitOfMemberThm{family.Add(registry.ProofEntry{
	Name: "OrbitOfMember",
	Key:  "prop_9299760c6bf8c729",
	Build: GroupAction.Law(Statement{
		Binders: "∀x y:B.",
		Hypotheses: []string{
			"x ∈ X",
			"y ∈ group_orbit(G, act, x)",
		},
		Conclusion: "group_orbit(G, act, y) = group_orbit(G, act, x)",
	},
		func(a *Argument, action Fact, x, y *Expr[B], xIn, yIn Fact) {
			h, moved := a.ObtainAs[A](
				"y is where some element h of G.carrier moves x",
				"∃h:A. h ∈ G.carrier ∧ y = act(h, x)",
				By(yIn, GroupOrbitDef, set_basic.InImage))
			parts := a.Conjuncts(
				moved,
				"h lies in G.carrier",
				"y is act(h, x)")
			hm, xm := a.MemberOf[on.Any](h, parts[0]), a.MemberOf[on.Any](x, xIn)
			a.Show(
				"and act(h, x) has the orbit of x",
				parts[1].Rw(),
				By(OrbitOfAct.Read(action).At(hm, xm)))
		}),
})}

// OrbitFibre — the points of X whose orbit is the orbit of x are exactly
// the orbit of x: each lies in its own orbit, and each point of the orbit
// lies in X with the orbit of x. So the orbits partition X, the orbit map
// x ↦ group_orbit(G, act, x) having the orbits as its fibres.
var OrbitFibre = orbitFibreThm{family.Add(registry.ProofEntry{
	Name: "OrbitFibre",
	Key:  "prop_c5e77f1885befdea",
	Build: GroupAction.Law(Statement{
		Binders: "∀x:B.",
		Hypotheses: []string{
			"x ∈ X",
		},
		Conclusion: "«fibre» = group_orbit(G, act, x)",
		Abbrev: Abbrev{
			{Name: "fibre", Text: "{y:B | y ∈ X ∧ group_orbit(G, act, y) = group_orbit(G, act, x)}"},
		},
	},
		func(a *Argument, action Fact, x *Expr[B], xIn Fact) {
			into := a.Have(
				"a point of X with the orbit of x lies in its own orbit, which is the orbit of x",
				"«fibre» ⊆ group_orbit(G, act, x)",
				BySets(InOwnOrbit.Read(action)))
			xm := a.MemberOf[on.Any](x, xIn)
			a.Show(
				"and a point of the orbit of x lies in X and has the orbit of x",
				BySets(into, OrbitSubset.Read(action).At(xm), OrbitOfMember.Read(action)))
		}),
})}

// FixedIffSingletonOrbit — a point of X is fixed by every element of the
// group exactly when its orbit is the singleton of the point: the orbit is
// the set of the points act(g, x), and it holds x itself.
var FixedIffSingletonOrbit = fixedIffSingletonOrbitThm{family.Add(registry.ProofEntry{
	Name: "FixedIffSingletonOrbit",
	Key:  "prop_b58b1ff880e99241",
	Build: GroupAction.Law(Statement{
		Binders: "∀x:B.",
		Hypotheses: []string{
			"x ∈ X",
		},
		Conclusion: "(∀g:A. g ∈ G.carrier ⇒ act(g, x) = x) ⇔ group_orbit(G, act, x) = {x}",
	},
		func(a *Argument, action Fact, x *Expr[B], xIn Fact) {
			G, act := a.TermAs[GroupOps[A]]("G"), a.TermAs[Fun2[A, B, B]]("act")
			xm := a.MemberOf[on.Any](x, xIn)
			a.Show(
				"the orbit is the set of the points act(g, x), and it holds x",
				BySets(GroupOrbitDef.At(G, act, x), InOwnOrbit.Read(action).At(xm)))
		}),
})}

// SumOverOrbits — a sum over a finite set the group acts on is the sum,
// over the orbits, of the sums over each: a finite sum regroups by the
// fibres of any map (monoidal.Fibres), and the fibres of the map taking a
// point to its orbit are the orbits (OrbitFibre).
var SumOverOrbits = sumOverOrbitsThm{family.Add(registry.ProofEntry{
	Name: "SumOverOrbits",
	Key:  "prop_803729bf0d81b83b",
	Build: GroupAction.Law(Statement{
		Binders: "∀f:(B → num).",
		Hypotheses: []string{
			"finite(X)",
		},
		Conclusion: "Σ_{x∈X} f(x) = Σ_{O∈«orbits»} Σ_{y∈O} f(y)",
		Abbrev: Abbrev{
			{Name: "orbitFibre", Text: "λO:set(B). {y:B | y ∈ X ∧ group_orbit(G, act, y) = O}"},
		},
	},
		func(a *Argument, action, finiteX Fact, f *Arrow[B, Nat]) {
			fibres := a.Have(
				"the fibres of the orbit map are the orbits, so a sum over a fibre is the sum over its orbit",
				"∀O:set(B). O ∈ «orbits» ⇒ Σ_{y∈«orbitFibre»(O)} f(y) = Σ_{y∈O} f(y)",
				Simp(Fwd(set_image.ForallInImage)),
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					xIn := b.Assume()
					b.Show(
						"the points of X with the orbit of a point x of X are that orbit",
						By(OrbitFibre.Read(action).At(b.MemberOf[on.Any](x, xIn))))
				}))
			a.Show(
				"group the sum by the fibres of the orbit map, then read each fibre as its orbit",
				Unfold(nat_sum.NatSumDef),
				CalcEq(
					Leg(
						a.Term("iterated_op(+, «orbits», λO:set(B). iterated_op(+, «orbitFibre»(O), f))"),
						"the orbit map groups the sum into its fibres",
						By(finiteX, monoidal.Fibres, nat_sum.MonoidalNatAdd)),
					FinalLeg(
						"each fibre contributes the sum over its orbit",
						By(fibres, monoidal.Congruence, nat_sum.MonoidalNatAdd))))
		}),
})}

// ---------------------------------------------------------------------------
// The stabilizer
// ---------------------------------------------------------------------------

// StabilizerSubgroup — the elements of the group fixing a point of X
// form a subgroup: the identity fixes it, a product of two elements
// fixing it acts by its factors in turn, and the inverse of an element
// fixing it undoes the element.
var StabilizerSubgroup = stabilizerSubgroupThm{family.Add(registry.ProofEntry{
	Name: "StabilizerSubgroup",
	Key:  "prop_f5fdafd940b6f619",
	Build: GroupAction.Law(Statement{
		Binders: "∀x:B.",
		Hypotheses: []string{
			"x ∈ X",
		},
		Conclusion: "subgroup(G, group_stabilizer(G, act, x))",
	},
		func(a *Argument, action Fact, x *Expr[B], xIn Fact) {
			acting := ActingGroup.Read(action)
			a.Do(Unfold(group.SubgroupDef), SplitConjAll(
				Case(
					"the stabilizer lies in G.carrier",
					BySets(GroupStabilizerDef)),
				Case(
					"the identity fixes x",
					Simp(Fwd(GroupStabilizerDef)),
					By(group.OneIn.Read(acting), ActOne.Read(action), xIn)),
				Case(
					"a product g * h of two elements fixing x fixes x: it acts by h, then by g",
					Simp(Fwd(GroupStabilizerDef)),
					Derive(func(b *Argument) {
						g, h := b.FixAs[A]("g"), b.FixAs[A]("h")
						fixing := b.Assume()
						b.Show(
							"g * h lies in G.carrier, and acting by h and then by g leaves x in place",
							By(Normalized, group.MulIn.Read(acting), ActMul.Read(action).AsFact().At(g, h, x), fixing, xIn))
					})),
				Case(
					"the inverse of an element g fixing x fixes x: it undoes g, which moves x to x",
					Simp(Fwd(GroupStabilizerDef)),
					Derive(func(b *Argument) {
						g := b.FixAs[A]("g")
						fixing := b.Assume()
						b.Show(
							"G.inv(g) lies in G.carrier, and it moves act(g, x), which is x, back to x",
							By(Normalized, group.InvIn.Read(acting), InvActCancel.Read(action).AsFact().At(g, x), fixing, xIn))
					})),
			))
		}),
})}

// ActEqIffStabilizer — two elements of the group move a point of X to
// the same point exactly when the quotient G.inv(g) * h fixes it. If
// act(g, x) = act(h, x), acting by G.inv(g) * h is acting by h and then
// undoing g; conversely h is g * (G.inv(g) * h), which acts by a quotient
// fixing x and then by g.
var ActEqIffStabilizer = actEqIffStabilizerThm{family.Add(registry.ProofEntry{
	Name: "ActEqIffStabilizer",
	Key:  "prop_517cc617eacc58c",
	Build: GroupAction.Law(Statement{
		Binders: "∀g h:A. ∀x:B.",
		Hypotheses: []string{
			"g ∈ G.carrier",
			"h ∈ G.carrier",
			"x ∈ X",
		},
		Conclusion: "act(g, x) = act(h, x) ⇔ G.inv(g) * h ∈ group_stabilizer(G, act, x)",
	},
		func(a *Argument, action Fact, g, h *Expr[A], gIn, hIn Fact, x *Expr[B], xIn Fact) {
			acting := ActingGroup.Read(action)
			gm, hm, xm := a.MemberOf[on.Any](g, gIn), a.MemberOf[on.Any](h, hIn), a.MemberOf[on.Any](x, xIn)
			inverse := group.InvIn.Read(acting).At(gm)
			quotient := group.MulIn.Read(acting).At(inverse, hm)
			a.Do(Simp(Fwd(GroupStabilizerDef)))
			a.Iff()
			a.Forward(
				"if g and h move x to one point, the quotient G.inv(g) * h fixes x",
				func(b *Argument, same Fact) {
					b.Show(
						"the quotient lies in G.carrier and acts by h, which "+
							"moves x where g does, then by G.inv(g), which undoes g",
						By(quotient, same, ActMul.Read(action).At(inverse, hm, xm), InvActCancel.Read(action).At(gm, xm)))
				})
			a.Backward(
				"if the quotient G.inv(g) * h fixes x, g and h move x to one point",
				func(b *Argument, fixes Fact) {
					b.Show(
						"h is g * (G.inv(g) * h), which acts by the quotient, leaving x in place, and then by g",
						By(
							Normalized,
							fixes,
							group.MulInvCancelLeftOn.Read(acting).At(gm, hm),
							ActMul.Read(action).At(gm, quotient, xm)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Counting an orbit
// ---------------------------------------------------------------------------

// OrbitStabilizer — the orbit–stabilizer theorem: the order of a finite
// group is an orbit's size times its point's stabilizer's order. The orbit
// is as large as the set of cosets of the stabilizer, and Lagrange's
// theorem counts those.
var OrbitStabilizer = orbitStabilizerThm{family.Add(registry.ProofEntry{
	Name: "OrbitStabilizer",
	Key:  "prop_f1ce6194e0887915",
	Build: GroupAction.Law(Statement{
		Binders: "∀x:B.",
		Hypotheses: []string{
			"finite(G.carrier)",
			"x ∈ X",
		},
		Conclusion: "card(G.carrier) = card(group_orbit(G, act, x)) * card(group_stabilizer(G, act, x))",
		Abbrev: Abbrev{
			{Name: "coset", Text: "coset_map(G.mul, group_stabilizer(G, act, x))"},
		},
	},
		func(a *Argument, action, finite Fact, x *Expr[B], xIn Fact) {
			acting := ActingGroup.Read(action)
			stabilizer := a.Have(
				"the stabilizer of x is a subgroup",
				"subgroup(G, group_stabilizer(G, act, x))",
				By(StabilizerSubgroup.Read(action), xIn))
			lagrange := a.Have(
				"by Lagrange's theorem the group is the stabilizer's order times the number of its cosets",
				"card(G.carrier) = card(group_stabilizer(G, act, x)) * card(image(«coset», G.carrier))",
				By(
					finite_group.LagrangeOn.Read(acting),
					stabilizer,
					group.CarrierSubgroupOn.Read(acting),
					group.SubgroupSubset,
					finite))
			stabilizerSet := a.TermAs[Set[A]]("group_stabilizer(G, act, x)")
			fibres := a.Have(
				"two elements move x to one point exactly when they have one coset of the stabilizer",
				"∀g h:A. g ∈ G.carrier ∧ h ∈ G.carrier ⇒ (act(g, x) = act(h, x) ⇔ «coset»(g) = «coset»(h))",
				Derive(func(b *Argument) {
					g, h := b.FixAs[A]("g"), b.FixAs[A]("h")
					members := b.Assume()
					b.Show(
						"both say that G.inv(g) * h lies in the stabilizer",
						Simp(Fwd(group.CosetMapDef)),
						By(
							members,
							xIn,
							stabilizer,
							ActEqIffStabilizer.Read(action).AsFact().At(g, h, x),
							group.LeftCosetEqOn.Read(acting).AsFact().At(g, h, stabilizerSet)))
				}))
			sameCount := a.Have(
				"so the orbit, the image of the group under g ↦ act(g, x), is as large as the set of cosets",
				"card(group_orbit(G, act, x)) = card(image(«coset», G.carrier))",
				Simp(Fwd(GroupOrbitDef)),
				By(cardinality.CardImageSameFibres, finite, fibres))
			a.Show(
				"so the group is the orbit's size times the stabilizer's order",
				By(lagrange, sameCount, nat_arith.MulSym))
		}),
})}
