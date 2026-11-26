package twisted_counting

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// FreeActionTwistedFixedPoints — under a free action of a finite group, a
// map phi commuting with the action of a subgroup H moves a point as some
// element of H does, counted over H, card(H) times for every H-orbit phi
// preserves. Both sides count the points phi keeps in their H-orbit: the
// sum sorts them by the element of H, which freeness makes unique, and
// the product by their orbit, since such points fill the orbits phi
// preserves and each orbit has card(H) points.
var FreeActionTwistedFixedPoints = freeActionTwistedFixedPointsThm{family.Add(registry.ProofEntry{
	Name: "FreeActionTwistedFixedPoints",
	Key:  "prop_2dde07f5e52fe731",
	Build: family.Sections(Statement{
		Binders: "∀G:group_ops(A). ∀H:set(A). ∀X:set(B). ∀act:(A → B → B). ∀phi:(B → B).",
		Hypotheses: []string{
			"free_finite_action(G, X, act)",
			"subgroup(G, H)",
			"∀g:A. ∀x:B. g ∈ H ∧ x ∈ X ⇒ phi(act(g, x)) = act(g, phi(x))",
		},
		Conclusion: "nat_sum(H, λg:A. card(«movedAs»(g))) = card(H) * card(«stableOrbits»)",
		Abbrev: Abbrev{
			{Name: "orbit", Text: "λx:B. {act(h, x) | h:A | h ∈ H}"},
			{Name: "movedAs", Text: "λg:A. {x:B | x ∈ X ∧ phi(x) = act(g, x)}"},
			{Name: "keptInOrbit", Text: "{x:B | x ∈ X ∧ phi(x) ∈ «orbit»(x)}"},
			{Name: "stableOrbits", Text: "{O:set(B) | O ∈ {«orbit»(x) | x:B | x ∈ X} ∧ image(phi, O) = O}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// Freeness, as the form both counts read: at a point of X the
		// translate determines the element.
		freeness := ctx.Lemma(Statement{
			Binders: "∀G:group_ops(A). ∀X:set(B). ∀act:(A → B → B). ∀g h:A. ∀x:B.",
			Hypotheses: []string{
				"free_finite_action(G, X, act)",
				"g ∈ G.carrier",
				"h ∈ G.carrier",
				"x ∈ X",
				"act(g, x) = act(h, x)",
			},
			Conclusion: "g = h",
		}, func(
			a *Argument,
			G *Expr[GroupOps[A]],
			X *Expr[Set[B]],
			act *Arrow2[A, B, B],
			g, h *Expr[A],
			x *Expr[B],
			action, gIn, hIn, xIn, sameTranslate Fact,
		) {
			parts := a.Conjuncts(
				a.Unfolded(action, FreeFiniteActionDef),
				"G is a group on its carrier",
				"the carrier is finite",
				"X is finite",
				"the identity acts trivially",
				"G acts on X multiplicatively and freely")
			isGroup, unit, acts := parts[0], parts[3], parts[4]
			inverseH := a.TermAs[A]("G.inv(h)")
			fixed := a.Have(
				"the quotient of g by h fixes x",
				"act(G.inv(h) * g, x) = x",
				By(
					acts.At(inverseH, g, x),
					acts.At(inverseH, h, x),
					unit.At(x),
					sameTranslate,
					gIn,
					hIn,
					xIn,
					At(group.InvIn.Read(isGroup), h),
					At(group.LeftInverseOn.Read(isGroup), h)))
			a.Show(
				"so by freeness that quotient is the identity, and g is h",
				By(
					acts.At(a.TermAs[A]("G.inv(h) * g"), h, x),
					fixed,
					gIn,
					hIn,
					xIn,
					At(group.InvIn.Read(isGroup), h),
					At(group.MulIn.Read(isGroup), inverseH, g),
					At(group.InvMulEqOneOn.Read(isGroup), h, g)))
		})

		countByElements := ctx.Lemma(Statement{
			Binders: "∀G:group_ops(A). ∀H:set(A). ∀X:set(B). ∀act:(A → B → B). ∀phi:(B → B).",
			Hypotheses: []string{
				"free_finite_action(G, X, act)",
				"subgroup(G, H)",
			},
			Conclusion: "nat_sum(H, λg:A. card(«movedAs»(g))) = card(«keptInOrbit»)",
		}, func(
			a *Argument,
			G *Expr[GroupOps[A]],
			H *Expr[Set[A]],
			X *Expr[Set[B]],
			act *Arrow2[A, B, B],
			phi *Arrow[B, B],
			action, subgroup Fact,
		) {
			finiteness := a.Have(
				"H lies in the finite carrier, and X is finite by definition",
				"finite(H) ∧ finite(X)",
				By(action, subgroup, FreeFiniteActionDef, group.SubgroupSubset, finite_set.FiniteSubset))
			finite := a.Conjuncts(
				finiteness,
				"H is finite",
				"X is finite")
			finiteH, finiteX := finite[0], finite[1]
			inCarrier := subgroupInCarrier(a, G, H, subgroup)
			finiteSets := a.Have(
				"each set is cut out of the finite set X",
				"∀g:A. finite(«movedAs»(g))",
				Derive(func(b *Argument) {
					b.FixAs[A]("g")
					b.Show(
						"a part of a finite set is finite",
						By(finiteX, finite_set.FiniteRestrict.At(X, b.TermAs[Fun[B, Bool]]("λx:B. phi(x) = act(g, x)"))))
				}))
			apart := a.Have(
				"two different elements of H agree at no point, so their sets are disjoint",
				"∀g k:A. g ∈ H ∧ k ∈ H ∧ g ≠ k ⇒ disjoint(«movedAs»(g), «movedAs»(k))",
				Derive(func(b *Argument) {
					g, k := b.FixAs[A]("g"), b.FixAs[A]("k")
					given := b.Conjuncts(
						b.Assume(),
						"g lies in H",
						"k lies in H",
						"g and k differ")
					differAt := b.Have(
						"at a point of X their translates differ, by freeness",
						"∀x:B. x ∈ X ⇒ act(g, x) ≠ act(k, x)",
						Derive(func(c *Argument) {
							x := c.FixAs[B]("x")
							xIn := c.Assume()
							c.Show(
								"H lies in the carrier, and elements agreeing at x are equal",
								By(
									given[0],
									given[1],
									given[2],
									xIn,
									action,
									subgroup,
									At(freeness, G, X, act, g, k, x),
									inCarrier))
						}))
					b.Show(
						"a common point would be a point where they agree",
						BySets(differAt))
				}))
			union := a.Have(
				"a point is in one of the sets exactly when phi keeps it in its orbit",
				"⋃image(«movedAs», H) = «keptInOrbit»",
				BySets())
			a.Show(
				"so the kept points are counted by the disjoint family",
				By(
					finiteH,
					finiteSets,
					apart,
					union,
					nat_sum.CardOfDisjointFamily.At(a.TermAs[Fun[A, Set[B]]]("«movedAs»"), H)))
		})

		countByOrbits := ctx.Lemma(Statement{
			Binders: "∀G:group_ops(A). ∀H:set(A). ∀X:set(B). ∀act:(A → B → B). ∀phi:(B → B).",
			Hypotheses: []string{
				"free_finite_action(G, X, act)",
				"subgroup(G, H)",
				"∀g:A. ∀x:B. g ∈ H ∧ x ∈ X ⇒ phi(act(g, x)) = act(g, phi(x))",
			},
			Conclusion: "card(«keptInOrbit») = card(H) * card(«stableOrbits»)",
		}, func(
			a *Argument,
			G *Expr[GroupOps[A]],
			H *Expr[Set[A]],
			X *Expr[Set[B]],
			act *Arrow2[A, B, B],
			phi *Arrow[B, B],
			action, subgroup, commutes Fact,
		) {
			parts := a.Conjuncts(
				a.Unfolded(action, FreeFiniteActionDef),
				"G is a group on its carrier",
				"the carrier is finite",
				"X is finite",
				"the identity acts trivially",
				"G acts on X multiplicatively and freely")
			isGroup, finiteX, unit, acts := parts[0], parts[2], parts[3], parts[4]
			finiteH := a.Have(
				"H lies in the finite carrier",
				"finite(H)",
				By(parts[1], subgroup, group.SubgroupSubset, finite_set.FiniteSubset))
			inCarrier := subgroupInCarrier(a, G, H, subgroup)

			staysInX := translatesStayInX(a, acts, inCarrier)
			productActs := a.Have(
				"elements of H multiply inside H, and a product acts as the composite",
				"∀h k:A. ∀x:B. h ∈ H ∧ k ∈ H ∧ x ∈ X ⇒ h * k ∈ H ∧ act(h * k, x) = act(h, act(k, x))",
				Derive(func(b *Argument) {
					h, k, x := b.FixAs[A]("h"), b.FixAs[A]("k"), b.FixAs[B]("x")
					given := b.Assume()
					b.Show(
						"H lies in the carrier, where the action laws hold",
						By(given, subgroup, acts.At(h, k, x), group.SubgroupMul.At(G, H, h, k), inCarrier))
				}))
			ownPoint := a.Have(
				"a point of X lies in its orbit, the identity being an element of H",
				"∀x:B. x ∈ X ⇒ x ∈ «orbit»(x)",
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					xIn := b.Assume()
					b.Show(
						"x is its translate by the identity",
						BySets(xIn, subgroup, unit.At(x), group.SubgroupOne.At(G, H)))
				}))
			translate := a.Have(
				"the points of an orbit are the translates by elements of H",
				"∀x z:B. z ∈ «orbit»(x) ⇒ ∃k:A. k ∈ H ∧ z = act(k, x)",
				BySets())
			orbitInX := a.Have(
				"an orbit lies in X",
				"∀x z:B. x ∈ X ∧ z ∈ «orbit»(x) ⇒ z ∈ X",
				Derive(func(b *Argument) {
					x, z := b.FixAs[B]("x"), b.FixAs[B]("z")
					given := b.Conjuncts(
						b.Assume(),
						"x lies in X",
						"z lies in its orbit")
					k, moved := b.UnpackAs[A](GroupPremises(given[1], translate.At(x, z)), "k")
					b.Show(
						"z is a translate of x, and a translate of a point of X lies in X",
						By(Normalized, given[0], moved, staysInX.At(k, x)))
				}))
			sameOrbit := a.Have(
				"a point of an orbit has that orbit as its own",
				"∀x z:B. x ∈ X ∧ z ∈ «orbit»(x) ⇒ «orbit»(z) = «orbit»(x)",
				Derive(func(b *Argument) {
					x, z := b.FixAs[B]("x"), b.FixAs[B]("z")
					given := b.Conjuncts(
						b.Assume(),
						"x lies in X",
						"z lies in its orbit")
					k, moved := b.UnpackAs[A](GroupPremises(given[1], translate.At(x, z)), "k")
					translates := b.Conjuncts(
						moved,
						"k lies in H",
						"z is the translate of x by k")
					kIn, zIs := translates[0], translates[1]
					inX := b.Have(
						"translating z by h is translating x by h * k",
						"∀h:A. h ∈ H ⇒ h * k ∈ H ∧ act(h, z) = act(h * k, x)",
						Derive(func(c *Argument) {
							h := c.FixAs[A]("h")
							hIn := c.Assume()
							c.Show(
								"a product acts as the composite",
								By(Normalized, given[0], zIs, hIn, kIn, productActs.At(h, k, x)))
						}))
					inZ := b.Have(
						"translating x by h is translating z by h * G.inv(k)",
						"∀h:A. h ∈ H ⇒ h * G.inv(k) ∈ H ∧ act(h, x) = act(h * G.inv(k), z)",
						Derive(func(c *Argument) {
							h := c.FixAs[A]("h")
							hIn := c.Assume()
							c.Show(
								"the inverse of k cancels k",
								By(
									Normalized,
									hIn,
									kIn,
									subgroup,
									inX.At(c.TermAs[A]("h * G.inv(k)")),
									group.SubgroupMulInv.At(G, H, h, k),
									inCarrier,
									At(group.InvMulCancelRightOn.Read(isGroup), k, h)))
						}))
					b.Show(
						"so the two orbits hold the same points",
						BySets(inX, inZ))
				}))
			sized := a.Have(
				"an orbit has card(H) points, h ↦ h·x being one-to-one on H by freeness",
				"∀x:B. x ∈ X ⇒ has_size(«orbit»(x), card(H))",
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					xIn := b.Assume()
					oneToOne := b.Have(
						"elements of H with one translate of x are equal",
						"injective_on(H, λh:A. act(h, x))",
						Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]()))),
						Derive(func(c *Argument) {
							u, v := c.FixAs[A]("u"), c.FixAs[A]("v")
							given := c.Assume()
							c.Show(
								"H lies in the carrier, where the translate determines the element",
								By(given, xIn, action, subgroup, At(freeness, G, X, act, u, v, x), inCarrier))
						}))
					asImage := b.Have(
						"the orbit is the image of H under h ↦ h·x",
						"«orbit»(x) = image(λh:A. act(h, x), H)",
						BySets())
					b.Show(
						"and a one-to-one image of H has as many points as H",
						asImage.Rw(),
						By(oneToOne, finiteH, cardinality.HasSizeImageInj, cardinality.FiniteHasSize))
				}))
			apart := a.Have(
				"two orbits that differ are disjoint, a common point having both as its own",
				"∀x y:B. x ∈ X ∧ y ∈ X ∧ «orbit»(x) ≠ «orbit»(y) ⇒ disjoint(«orbit»(x), «orbit»(y))",
				Derive(func(b *Argument) {
					x, y := b.FixAs[B]("x"), b.FixAs[B]("y")
					given := b.Conjuncts(
						b.Assume(),
						"x lies in X",
						"y lies in X",
						"the orbits differ")
					noCommonPoint := b.Have(
						"no point lies in both orbits",
						"∀z:B. z ∈ «orbit»(x) ⇒ z ∉ «orbit»(y)",
						Derive(func(c *Argument) {
							z := c.FixAs[B]("z")
							inFirst := c.Assume()
							c.Show(
								"it would have both as its own orbit",
								By(given[0], given[1], given[2], inFirst, sameOrbit.At(x, z), sameOrbit.At(y, z)))
						}))
					b.Show(
						"which is disjointness",
						BySets(noCommonPoint))
				}))
			imageOfOrbit := phiCarriesOrbits(a, commutes)
			stableIffKept := a.Have(
				"the orbit of a point is stable exactly when phi keeps the point in it",
				"∀y:B. y ∈ X ⇒ (image(phi, «orbit»(y)) = «orbit»(y) ⇔ phi(y) ∈ «orbit»(y))",
				Derive(func(b *Argument) {
					y := b.FixAs[B]("y")
					yIn := b.Assume()
					b.Iff()
					b.Forward(
						"phi(y) lies in the image of the orbit, which is the orbit",
						func(c *Argument, isStable Fact) {
							c.Show(
								"y lies in its orbit",
								BySets(isStable, ownPoint.At(y), yIn))
						})
					b.Backward(
						"the orbit of phi(y) is then the orbit of y",
						func(c *Argument, kept Fact) {
							c.Show(
								"and phi carries the one onto the other",
								By(yIn, kept, imageOfOrbit.At(y), sameOrbit.At(y, phi.Apply(y))))
						})
				}))

			stableSet, stableDef := a.LetAs[Set[Set[B]]]("stable", "«stableOrbits»")
			member := a.Have(
				"the stable orbits are the orbits of points of X that phi preserves",
				"∀O:set(B). O ∈ stable ⇔ (∃x:B. x ∈ X ∧ O = «orbit»(x)) ∧ image(phi, O) = O",
				stableDef.Rw(),
				BySets())
			basePoint := a.Have(
				"a stable orbit is the orbit of a point of X",
				"∀O:set(B). O ∈ stable ⇒ ∃x:B. x ∈ X ∧ O = «orbit»(x)",
				BySets(member))
			eachSized := a.Have(
				"each stable orbit has card(H) points",
				"∀c:set(B). c ∈ stable ⇒ has_size(c, card(H))",
				Derive(func(b *Argument) {
					c := b.FixAs[Set[B]]("c")
					inStable := b.Assume()
					x, based := b.ObtainAs[B](
						"it is the orbit of a point of X",
						"∃x:B. x ∈ X ∧ c = «orbit»(x)",
						By(inStable, basePoint.At(c)))
					b.Show(
						"which has card(H) points",
						By(based, sized.At(x)))
				}))
			pairwiseApart := a.Have(
				"different stable orbits are disjoint",
				"∀c d:set(B). c ∈ stable ∧ d ∈ stable ∧ c ≠ d ⇒ disjoint(c, d)",
				Derive(func(b *Argument) {
					c, d := b.FixAs[Set[B]]("c"), b.FixAs[Set[B]]("d")
					given := b.Conjuncts(
						b.Assume(),
						"c is stable",
						"d is stable",
						"c and d differ")
					x, basedC := b.UnpackAs[B](GroupPremises(given[0], basePoint.At(c)), "x")
					y, basedD := b.UnpackAs[B](GroupPremises(given[1], basePoint.At(d)), "y")
					onC := b.Conjuncts(
						basedC,
						"x lies in X",
						"c is the orbit of x")
					onD := b.Conjuncts(
						basedD,
						"y lies in X",
						"d is the orbit of y")
					b.Show(
						"c and d are orbits that differ, and such orbits are disjoint",
						onC[1].Rw(),
						onD[1].Rw(),
						By(onC[0], onD[0], given[2], apart.At(x, y)))
				}))
			amongOrbits := a.Have(
				"the stable orbits lie among the orbits of points of X",
				"stable ⊆ image(«orbit», X)",
				BySets(member))
			finiteStable := a.Have(
				"so there are finitely many of them, X being finite",
				"finite(stable)",
				By(
					amongOrbits,
					finiteX,
					finite_set.FiniteImage.At(a.TermAs[Fun[B, Set[B]]]("«orbit»"), X),
					finite_set.FiniteSubset.At(stableSet, a.TermAs[Set[Set[B]]]("image(«orbit», X)"))))
			inUnion := a.Have(
				"a point lies in a stable orbit exactly when phi keeps it in its orbit",
				"∀z:B. z ∈ ⋃stable ⇔ z ∈ X ∧ phi(z) ∈ «orbit»(z)",
				Derive(func(b *Argument) {
					z := b.FixAs[B]("z")
					b.Iff()
					b.Forward(
						"the stable orbit through z is the orbit of z",
						func(c *Argument, inUnionOfStable Fact) {
							u, block := c.ObtainAs[Set[B]](
								"z lies in a stable orbit u",
								"∃u:set(B). u ∈ stable ∧ z ∈ u",
								By(inUnionOfStable, set_basic.InUnions.At(stableSet, z)))
							blockParts := c.Conjuncts(
								block,
								"u is stable",
								"z lies in u")
							preserved := c.Have(
								"phi preserves u",
								"image(phi, u) = u",
								By(blockParts[0], member.At(u)))
							x, based := c.UnpackAs[B](GroupPremises(blockParts[0], basePoint.At(u)), "x")
							onX := c.Conjuncts(
								based,
								"x lies in X",
								"u is the orbit of x")
							zInOrbit := c.Have(
								"z lies in the orbit of x",
								"z ∈ «orbit»(x)",
								By(Normalized, blockParts[1], onX[1]))
							zIn := c.Have(
								"so z lies in X",
								"z ∈ X",
								By(onX[0], zInOrbit, orbitInX.At(x, z)))
							c.Show(
								"and the stable orbit u is the orbit of z, in which phi keeps z",
								By(zIn, preserved, onX[1], onX[0], zInOrbit, sameOrbit.At(x, z), stableIffKept.At(z)))
						})
					b.Backward(
						"the orbit of z is stable and holds z",
						func(c *Argument, kept Fact) {
							facts := c.Conjuncts(
								kept,
								"z lies in X",
								"phi keeps z in its orbit")
							based := c.Have(
								"the orbit of z is the orbit of a point of X, namely z",
								"∃x:B. x ∈ X ∧ «orbit»(z) = «orbit»(x)",
								Derive(func(d *Argument) {
									d.Take(z)
									d.Show(
										"z itself",
										By(facts[0]))
								}))
							preserved := c.Have(
								"and phi preserves it",
								"image(phi, «orbit»(z)) = «orbit»(z)",
								By(facts[0], facts[1], stableIffKept.At(z)))
							isStable := c.Have(
								"so the orbit of z is a stable orbit",
								"«orbit»(z) ∈ stable",
								By(based, preserved, member.At(c.TermAs[Set[B]]("«orbit»(z)"))))
							c.Show(
								"and z lies in it, hence in the union of the stable orbits",
								By(facts[0], ownPoint.At(z), isStable, set_basic.InUnions.At(stableSet, z)))
						})
				}))
			union := a.Have(
				"so the union of the stable orbits is the set of kept points",
				"⋃stable = «keptInOrbit»",
				BySets(inUnion))
			a.Show(
				"and the union of disjoint sets of card(H) points counts card(H) for each",
				By(
					union,
					cardinality.HasSizeUnions.At(stableSet, a.TermAs[Nat]("card(H)")),
					finiteStable,
					eachSized,
					pairwiseApart,
					cardinality.CardOfSized))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			G *Expr[GroupOps[A]],
			H *Expr[Set[A]],
			X *Expr[Set[B]],
			act *Arrow2[A, B, B],
			phi *Arrow[B, B],
			action, subgroup, commutes Fact,
		) {
			a.Show(
				"both sides count the points phi keeps in their orbit",
				CalcEq(
					Leg(
						a.Term("card(«keptInOrbit»)"),
						"sorted by the element of H that moves them as phi does",
						By(action, subgroup, At(countByElements, G, H, X, act, phi))),
					FinalLeg(
						"sorted by their orbit, which phi preserves",
						By(action, subgroup, commutes, At(countByOrbits, G, H, X, act, phi)))))
		})
	}),
})}

// SubgroupSumInverse — a sum over a subgroup does not see inversion: the
// inverse is one-to-one on the subgroup and carries it onto itself.
var SubgroupSumInverse = subgroupSumInverseThm{family.Add(registry.ProofEntry{
	Name: "SubgroupSumInverse",
	Key:  "prop_c64a44b6b6c1808c",
	Build: family.Theorem(Statement{
		Binders:    "∀G:group_on(A). ∀H:set(A). ∀f:(A → num).",
		Hypotheses: []string{"subgroup(G, H)"},
		Conclusion: "nat_sum(H, λg:A. f(G.inv(g))) = nat_sum(H, f)",
	}, func(a *Argument, G group.GroupFact[on.G], H *Expr[Set[A]], f *Arrow[A, Nat], subgroup Fact) {
		groupG := a.TermAs[GroupOps[A]]("G")
		inverse := a.TermAs[Fun[A, A]]("G.inv")
		inCarrier := subgroupInCarrier(a, groupG, H, subgroup)
		twice := a.Have(
			"inverting an element of H twice returns it",
			"∀h:A. h ∈ H ⇒ G.inv(G.inv(h)) = h",
			Derive(func(b *Argument) {
				b.FixAs[A]("h")
				hIn := b.Assume()
				b.Show(
					"H lies in the carrier, where inversion is an involution",
					By(G, hIn, inCarrier, group.InvInvOn))
			}))
		inverseIn := a.Have(
			"H holds the inverses of its elements",
			"∀h:A. h ∈ H ⇒ G.inv(h) ∈ H",
			Derive(func(b *Argument) {
				h := b.FixAs[A]("h")
				hIn := b.Assume()
				b.Show(
					"a subgroup is closed under inverses",
					By(hIn, subgroup, group.SubgroupInv.At(groupG, H, h)))
			}))
		oneToOne := a.Have(
			"so inversion is one-to-one on H",
			"injective_on(H, G.inv)",
			Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]()))),
			Derive(func(b *Argument) {
				u, v := b.FixAs[A]("u"), b.FixAs[A]("v")
				given := b.Conjuncts(
					b.Assume(),
					"u lies in H",
					"v lies in H",
					"they have one inverse")
				b.Show(
					"each is the inverse of that inverse",
					By(given[0], given[1], given[2], twice.At(u), twice.At(v)))
			}))
		onto := a.Have(
			"and carries H onto itself",
			"image(G.inv, H) = H",
			BySets(inverseIn, twice))
		composite := a.Have(
			"reading a summand at the inverse is composing with inversion",
			"(λg:A. f(G.inv(g))) = f ∘ G.inv",
			Funext(),
			By(functions.ComposeApply))
		reindexed := a.Have(
			"so the sum over H is the sum over the inverses of its elements",
			"nat_sum(image(G.inv, H), f) = nat_sum(H, f ∘ G.inv)",
			By(oneToOne, nat_sum.Image.At(H, inverse, f)))
		a.Show(
			"which is the sum of the summand read at the inverse",
			composite.Rw(),
			By(a.Simplified(reindexed, Fwd(onto))))
	}),
})}

// FreeActionTwistedCountByInvariant — the fixed-orbit formula read on a map r
// that tells the H-orbits of X apart: where phi keeps X, an orbit is a fibre
// of r inside X, and phi preserves it exactly when phi does not change the
// value of r at its points, so the stable orbits are the values of r at the
// points where phi leaves that value alone.
var FreeActionTwistedCountByInvariant = freeActionTwistedCountByInvariantThm{family.Add(registry.ProofEntry{
	Name: "FreeActionTwistedCountByInvariant",
	Key:  "prop_50e5a7676fe907c2",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀H:set(A). ∀X:set(B). ∀act:(A → B → B). ∀phi:(B → B). ∀r:(B → C).",
		Hypotheses: []string{
			"free_finite_action(G, X, act)",
			"subgroup(G, H)",
			"∀g:A. ∀x:B. g ∈ H ∧ x ∈ X ⇒ phi(act(g, x)) = act(g, phi(x))",
			"∀x:B. x ∈ X ⇒ phi(x) ∈ X",
			"∀x y:B. x ∈ X ∧ y ∈ X ⇒ (r(x) = r(y) ⇔ ∃h:A. h ∈ H ∧ act(h, x) = y)",
		},
		Conclusion: "nat_sum(H, λg:A. card(«movedAs»(g))) = card(H) * card(«stableValues»)",
		Abbrev: Abbrev{
			{Name: "orbit", Text: "λx:B. {act(h, x) | h:A | h ∈ H}"},
			{Name: "movedAs", Text: "λg:A. {x:B | x ∈ X ∧ phi(x) = act(g, x)}"},
			{Name: "stableOrbits", Text: "{O:set(B) | O ∈ {«orbit»(x) | x:B | x ∈ X} ∧ image(phi, O) = O}"},
			{Name: "fibre", Text: "λe:C. {y:B | y ∈ X ∧ r(y) = e}"},
			{Name: "stablePoints", Text: "{x:B | x ∈ X ∧ r(phi(x)) = r(x)}"},
			{Name: "stableValues", Text: "{r(x) | x:B | x ∈ X ∧ r(phi(x)) = r(x)}"},
		},
	}, func(
		a *Argument,
		G *Expr[GroupOps[A]],
		H *Expr[Set[A]],
		X *Expr[Set[B]],
		act *Arrow2[A, B, B],
		phi *Arrow[B, B],
		r *Arrow[B, C],
		action, subgroup, commutes, keepsX, separates Fact,
	) {
		parts := a.Conjuncts(
			a.Unfolded(action, FreeFiniteActionDef),
			"G is a group on its carrier",
			"the carrier is finite",
			"X is finite",
			"the identity acts trivially",
			"G acts on X multiplicatively and freely")
		finiteX, acts := parts[2], parts[4]
		inCarrier := subgroupInCarrier(a, G, H, subgroup)
		staysInX := translatesStayInX(a, acts, inCarrier)
		orbitIsFibre := a.Have(
			"the orbit of a point of X is the fibre of r through it",
			"∀x:B. x ∈ X ⇒ «orbit»(x) = «fibre»(r(x))",
			Derive(func(b *Argument) {
				x := b.FixAs[B]("x")
				xIn := b.Assume()
				pointwise := b.Have(
					"a point is a translate of x exactly when it lies in X with the value of x",
					"∀y:B. (∃h:A. h ∈ H ∧ act(h, x) = y) ⇔ y ∈ X ∧ r(y) = r(x)",
					Derive(func(c *Argument) {
						y := c.FixAs[B]("y")
						c.Show(
							"a translate stays in X, and r tells the orbits apart",
							By(xIn, staysInX, separates.At(x, y)))
					}))
				b.Show(
					"which is the equation of the two sets",
					BySets(pointwise))
			}))
		imageOfOrbit := phiCarriesOrbits(a, commutes)
		stableIff := a.Have(
			"phi preserves the orbit of a point exactly when it does not change the value of r there",
			"∀x:B. x ∈ X ⇒ (image(phi, «orbit»(x)) = «orbit»(x) ⇔ r(phi(x)) = r(x))",
			Derive(func(b *Argument) {
				x := b.FixAs[B]("x")
				xIn := b.Assume()
				b.Iff()
				b.Forward(
					"phi(x) lies in the image of the orbit, which is the orbit, a fibre of r",
					func(c *Argument, preserved Fact) {
						c.Show(
							"x lies in that fibre",
							BySets(preserved, orbitIsFibre.At(x), xIn))
					})
				b.Backward(
					"x and phi(x) lie on one fibre of r, so their orbits are one",
					func(c *Argument, sameValue Fact) {
						c.Show(
							"and phi carries the one onto the other",
							By(
								xIn,
								sameValue,
								keepsX.At(x),
								orbitIsFibre.At(x),
								orbitIsFibre.At(phi.Apply(x)),
								imageOfOrbit.At(x)))
					})
			}))
		stableMember := a.Have(
			"the stable orbits are the orbits of points of X that phi preserves",
			"∀O:set(B). O ∈ «stableOrbits» ⇔ (∃x:B. x ∈ X ∧ O = «orbit»(x)) ∧ image(phi, O) = O",
			BySets())
		sameOrbits := a.Have(
			"the stable orbits are the fibres over the stable values",
			"∀O:set(B). O ∈ «stableOrbits» ⇔ O ∈ image(«fibre», «stableValues»)",
			Derive(func(b *Argument) {
				O := b.FixAs[Set[B]]("O")
				b.Iff()
				b.Forward(
					"a stable orbit is the fibre through any of its points, and r keeps its value there",
					func(c *Argument, inStable Fact) {
						opened := c.Conjuncts(
							c.Have(
								"O is the orbit of a point of X, and phi preserves it",
								"(∃x:B. x ∈ X ∧ O = «orbit»(x)) ∧ image(phi, O) = O",
								By(inStable, stableMember.At(O))),
							"O is the orbit of a point of X",
							"phi preserves O")
						x, based := c.UnpackAs[B](opened[0], "x")
						onX := c.Conjuncts(
							based,
							"x lies in X",
							"O is the orbit of x")
						stableAtX := c.Have(
							"so phi does not change the value of r at x",
							"r(phi(x)) = r(x)",
							By(onX[0], onX[1], opened[1], stableIff.At(x)))
						c.Show(
							"O is the fibre over r(x)",
							BySets(onX[0], onX[1], stableAtX, orbitIsFibre.At(x)))
					})
				b.Backward(
					"the fibre over a stable value is the orbit of a point there, which phi preserves",
					func(c *Argument, inImage Fact) {
						x, based := c.ObtainAs[B](
							"O is the fibre through a point where r is stable",
							"∃x:B. x ∈ X ∧ r(phi(x)) = r(x) ∧ O = «fibre»(r(x))",
							BySets(inImage))
						onX := c.Conjuncts(
							based,
							"x lies in X",
							"phi does not change r at x",
							"O is the fibre through x")
						orbitIsO := c.Have(
							"O is the orbit of x",
							"O = «orbit»(x)",
							By(onX[0], onX[2], orbitIsFibre.At(x)))
						preserved := c.Have(
							"which phi preserves",
							"image(phi, O) = O",
							orbitIsO.Rw(),
							By(onX[0], onX[1], stableIff.At(x)))
						isOrbit := c.Have(
							"and O is the orbit of a point of X",
							"∃y:B. y ∈ X ∧ O = «orbit»(y)",
							Derive(func(d *Argument) {
								d.Take(x)
								d.Show(
									"namely x",
									By(onX[0], orbitIsO))
							}))
						c.Show(
							"so O is a stable orbit",
							By(isOrbit, preserved, stableMember.At(O)))
					})
			}))
		tagged := a.Have(
			"a stable value is the value at a point of X, and that point lies on its fibre",
			"∀e:C. e ∈ «stableValues» ⇒ ∃x:B. x ∈ «fibre»(e) ∧ r(x) = e",
			BySets())
		oneToOne := a.Have(
			"different stable values have different fibres, a fibre determining the value of r on it",
			"injective_on(«stableValues», «fibre»)",
			Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[C](), TypeBinder.BindB[Set[B]]()))),
			Derive(func(b *Argument) {
				u := b.FixAs[C]("u")
				b.FixAs[C]("v")
				given := b.Conjuncts(
					b.Assume(),
					"u is a stable value",
					"v is a stable value",
					"they have one fibre")
				_, point := b.UnpackAs[B](GroupPremises(given[0], tagged.At(u)), "x")
				b.Show(
					"x lies on both fibres, so r(x) is u and is v",
					BySets(given[2], point))
			}))
		finiteValues := a.Have(
			"the stable values are the image of a part of the finite set X",
			"finite(«stableValues»)",
			Derive(func(b *Argument) {
				asImage := b.Have(
					"the stable values are the image of the points where r is stable",
					"«stableValues» = image(r, «stablePoints»)",
					BySets())
				b.Show(
					"an image of a finite set is finite",
					asImage.Rw(),
					By(
						finiteX,
						finite_set.FiniteRestrict.At(X, b.TermAs[Fun[B, Bool]]("λx:B. r(phi(x)) = r(x)")),
						finite_set.FiniteImage.At(r, b.TermAs[Set[B]]("«stablePoints»"))))
			}))
		sameCount := a.Have(
			"so there are as many stable orbits as stable values",
			"card(«stableOrbits») = card(«stableValues»)",
			Derive(func(b *Argument) {
				asImage := b.Have(
					"the stable orbits are the fibres over the stable values",
					"«stableOrbits» = image(«fibre», «stableValues»)",
					BySets(sameOrbits))
				b.Show(
					"and fibres over different values are different",
					asImage.Rw(),
					By(
						oneToOne,
						finiteValues,
						cardinality.CardImageInj.At(
							b.TermAs[Fun[C, Set[B]]]("«fibre»"), b.TermAs[Set[C]]("«stableValues»"))))
			}))
		a.Show(
			"which turns the fixed-orbit formula into a count of stable values",
			sameCount.RwRev(),
			By(action, subgroup, commutes, FreeActionTwistedFixedPoints.At(G, H, X, act, phi)))
	}),
})}

// subgroupInCarrier reads off that the elements of the subgroup H lie in the
// carrier of G. Its claim spells the caller's letters G and H.
func subgroupInCarrier(a *Argument, G *Expr[GroupOps[A]], H *Expr[Set[A]], subgroup Fact) Fact {
	return a.Have(
		"H lies in the carrier",
		"∀h:A. h ∈ H ⇒ h ∈ G.carrier",
		BySets(subgroup, group.SubgroupSubset.At(G, H)))
}

// translatesStayInX reads off that an element of H keeps X, H lying in the
// carrier, where the action keeps X. Its claim spells the caller's H, X and act.
func translatesStayInX(a *Argument, acts, inCarrier Fact) Fact {
	return a.Have(
		"a translate of a point of X by an element of H stays in X",
		"∀h:A. ∀x:B. h ∈ H ∧ x ∈ X ⇒ act(h, x) ∈ X",
		Derive(func(b *Argument) {
			h, x := b.FixAs[A]("h"), b.FixAs[B]("x")
			given := b.Assume()
			b.Show(
				"H lies in the carrier, where the action keeps X",
				By(given, acts.At(h, h, x), inCarrier))
		}))
}

// phiCarriesOrbits reads off that a map phi commuting with H carries the
// H-orbit of a point onto that of its image. Its claim spells the callers' H, X,
// act and phi, and the «orbit» both of them declare.
func phiCarriesOrbits(a *Argument, commutes Fact) Fact {
	return a.Have(
		"phi carries the orbit of x onto the orbit of phi(x)",
		"∀x:B. x ∈ X ⇒ image(phi, «orbit»(x)) = «orbit»(phi(x))",
		Derive(func(b *Argument) {
			b.FixAs[B]("x")
			xIn := b.Assume()
			b.Show(
				"phi commutes with each element of H, so it moves the translates of x to those of phi(x)",
				BySets(commutes, xIn))
		}))
}
