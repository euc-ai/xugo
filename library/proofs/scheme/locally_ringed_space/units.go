// units.go — a section is invertible exactly where its germs are invertible.

package locally_ringed_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/presheaf"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// GermUnitIffRestrictUnit — the germ of a section t at x is a unit of the
// stalk exactly when t restricts to a unit on some open neighbourhood of x
// inside U. A section v over W inverting the restriction of t has a germ
// inverting the germ of t: t and its restriction share a germ, and over W
// the germ operations are those of the sections. Conversely an inverse
// germ is the germ of a section s over some open V ∋ x inside U; the germ
// of the product of s with the restriction of t is then the germ of one,
// so the two sections agree on a smaller open W, over which the
// restriction of s inverts the restriction of t. The argument reads germs
// and restriction homomorphisms only, so a presheaf of rings suffices:
// neither locality nor gluing is used.
var GermUnitIffRestrictUnit = germUnitIffRestrictUnitThm{family.Add(registry.ProofEntry{
	Name: "GermUnitIffRestrictUnit",
	Key:  "prop_21e945b87832560b",
	Build: family.Theorem(Statement{
		Binders: "∀F:presheaf_of_rings(A, B). ∀U:set(A). ∀t:B. ∀x:A.",
		Hypotheses: []string{
			"U ∈ T",
			"t ∈ F(U).carrier",
			"x ∈ U",
		},
		Conclusion: "ring_unit(stalk_ring(T, F, res, x), " +
			"    sheaf_germ(T, λU:set(A). F(U).carrier, res, x, U, t)) ⇔ " +
			"∃W:set(A). W ∈ T ∧ x ∈ W ∧ W ⊆ U ∧ ring_unit(F(W), res(U, W, t))",
	},
		func(
			a *Argument,
			F PresheafOfRingsFact[on.T],
			U *Expr[Set[A]],
			t *Expr[B],
			x *Expr[A],
			hypotheses Fact,
		) {
			underlying := Presheaf.Read(F)
			a.Iff()
			a.Backward(
				"the germ of a local inverse inverts the germ of t",
				func(b *Argument, local Fact) {
					_, onW := b.UnpackAs[Set[A]](b.Unfolded(local, ring_ideal.RingUnitDef), "W")
					_, inverse := b.ObtainAs[B](
						"a section v over W inverts the restriction of t",
						"∃v:B. v ∈ F(W).carrier ∧ F(W).mul(res(U, W, t), v) = F(W).one",
						By(onW))
					restricted := b.Have(
						"the restriction of t is a section over W",
						"res(U, W, t) ∈ F(W).carrier",
						By(presheaf.RestrictIn.Read(underlying), hypotheses, onW))
					sameGerm := b.Have(
						"restricting t to W keeps its germ",
						"sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, W, res(U, W, t)) = "+
							"sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, U, t)",
						By(presheaf.GermRestrict.Read(underlying), hypotheses, onW))
					product := b.Have(
						"the germ of v inverts the germ of t",
						"stalk_mul(T, "+
							"    F, "+
							"    res, "+
							"    x, "+
							"    sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, U, t), "+
							"    sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, W, v)) = "+
							"stalk_one(T, F, res, x)",
						CalcEq(
							Leg(
								b.Term(
									"stalk_mul(T, "+
										"    F, "+
										"    res, "+
										"    x, "+
										"    sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, W, res(U, W, t)), "+
										"    sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, W, v))"),
								"the germ of t is the germ of its restriction to W",
								By(sameGerm)),
							Leg(
								b.Term("sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, W, F(W).mul(res(U, W, t), v))"),
								"over W the product of the germs is the germ of the product",
								By(GermMul.Read(F), restricted, inverse, onW)),
							Leg(
								b.Term("sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, W, F(W).one)"),
								"where v inverts the restriction of t",
								By(inverse)),
							FinalLeg(
								"and the germ of one over W is the one of the stalk",
								By(GermOne.Read(F), onW)),
						))
					inverseGerm := b.Have(
						"so the stalk holds an inverse of the germ of t",
						"∃h:set(prod(set(A), B)). "+
							"    h ∈ stalk(T, (λU:set(A). F(U).carrier), res, x) ∧ "+
							"    stalk_mul(T, F, res, x, sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, U, t), h) = "+
							"    stalk_one(T, F, res, x)",
						Derive(func(c *Argument) {
							c.Take(c.TermAs[Set[Prod[Set[A], B]]]("sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, W, v)"))
							c.Show(
								"the germ of v, a section over an open neighbourhood of x",
								By(presheaf.GermInStalk.Read(underlying), product, inverse, onW))
						}))
					b.Show(
						"hence the germ of t is a unit of the stalk",
						By(presheaf.GermInStalk.Read(underlying), inverseGerm, hypotheses, ring_ideal.RingUnitDef))
				})
			a.Forward(
				"an inverse germ is represented inside U, and its product with t is one on a smaller open W",
				func(b *Argument, unit Fact) {
					invertible := b.Unfolded(unit, ring_ideal.RingUnitDef)
					_, inverse := b.ObtainAs[Set[Prod[Set[A], B]]](
						"the germ of t has an inverse h in the stalk",
						"∃h:set(prod(set(A), B)). "+
							"    h ∈ stalk(T, (λU:set(A). F(U).carrier), res, x) ∧ "+
							"    stalk_mul(T, F, res, x, sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, U, t), h) = "+
							"    stalk_one(T, F, res, x)",
						By(invertible))
					V, _, onV := b.Obtain2As[Set[A], B](
						"h is the germ of a section s over an open V ∋ x inside U",
						"∃V:set(A). ∃s:B. "+
							"    V ∈ T ∧ "+
							"    x ∈ V ∧ "+
							"    V ⊆ U ∧ "+
							"    s ∈ F(V).carrier ∧ "+
							"    h = sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, V, s)",
						By(presheaf.GermRepresentativeWithin.Read(underlying), inverse, hypotheses))
					restricted := b.Have(
						"the restriction of t is a section over V",
						"res(U, V, t) ∈ F(V).carrier",
						By(presheaf.RestrictIn.Read(underlying), hypotheses, onV))
					sameGerm := b.Have(
						"restricting t to V keeps its germ",
						"sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, V, res(U, V, t)) = "+
							"sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, U, t)",
						By(presheaf.GermRestrict.Read(underlying), hypotheses, onV))
					sectionRing := b.Have(
						"the sections over V form a ring",
						"comm_ring_on(F(V))",
						By(SectionRing.Read(F), onV))
					germsAgree := b.Have(
						"over V the product of s with the restriction of t has the germ of one",
						"sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, V, F(V).mul(res(U, V, t), s)) = "+
							"sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, V, F(V).one)",
						CalcEq(
							Leg(
								b.Term(
									"stalk_mul(T, "+
										"    F, "+
										"    res, "+
										"    x, "+
										"    sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, V, res(U, V, t)), "+
										"    sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, V, s))"),
								"the germ of a product over V is the product of the germs",
								By(GermMul.Read(F), restricted, onV)),
							Leg(
								b.Term("stalk_one(T, F, res, x)"),
								"which is the germ of t times its inverse h",
								By(sameGerm, inverse, onV)),
							FinalLeg(
								"and the one of the stalk is the germ of one over V",
								By(GermOne.Read(F), onV)),
						))
					W, agreement := b.ObtainAs[Set[A]](
						"so the product and one agree on an open W ∋ x inside V",
						"∃W:set(A). W ∈ T ∧ x ∈ W ∧ W ⊆ V ∩ V ∧ res(V, W, F(V).mul(res(U, V, t), s)) = res(V, W, F(V).one)",
						By(
							presheaf.GermEq.Read(underlying).AsFact().At(
								x, V, V, b.TermAs[B]("F(V).mul(res(U, V, t), s)"), b.TermAs[B]("F(V).one")),
							germsAgree,
							onV,
							restricted,
							comm_ring.MulIn.Read(sectionRing),
							comm_ring.OneIn.Read(sectionRing)))
					inside := b.Have(
						"W lies in V, hence in U",
						"W ⊆ V ∧ W ⊆ U",
						BySets(agreement, onV))
					restriction := b.Have(
						"restricting from V to W is a ring homomorphism",
						"ring_homomorphism(F(V), F(W), res(V, W))",
						By(PresheafRestrictHomomorphism.Read(F), onV, agreement, inside))
					productOne := b.Have(
						"over W the restrictions of t and s multiply to one",
						"F(W).mul(res(U, W, t), res(V, W, s)) = F(W).one",
						CalcEq(
							Leg(
								b.Term("F(W).mul(res(V, W, res(U, V, t)), res(V, W, s))"),
								"restricting t to W passes through V",
								By(
									Normalized,
									presheaf.RestrictTwice.Read(underlying).AsFact().At(U, V, W, t),
									hypotheses,
									onV,
									agreement,
									inside)),
							Leg(
								b.Term("res(V, W, F(V).mul(res(U, V, t), s))"),
								"restriction keeps the product",
								By(ring_homomorphism.MapMul.Read(restriction), restricted, onV)),
							Leg(
								b.Term("res(V, W, F(V).one)"),
								"on W the product and one agree",
								By(agreement)),
							FinalLeg(
								"and restriction keeps one",
								By(ring_homomorphism.MapOne.Read(restriction))),
						))
					localInverse := b.Have(
						"the restriction of s inverts the restriction of t over W",
						"∃v:B. v ∈ F(W).carrier ∧ F(W).mul(res(U, W, t), v) = F(W).one",
						Derive(func(c *Argument) {
							c.Take(c.TermAs[B]("res(V, W, s)"))
							c.Show(
								"a section over W, as a restriction",
								By(presheaf.RestrictIn.Read(underlying), productOne, onV, agreement, inside))
						}))
					b.Take(W)
					b.Show(
						"W is an open neighbourhood of x inside U over which the restriction of t is a unit",
						By(
							ring_ideal.RingUnitDef,
							localInverse,
							agreement,
							inside,
							hypotheses,
							presheaf.RestrictIn.Read(underlying)))
				})
		}),
})}

// UnitLocusOpen — the points of U where the germ of a section t is a unit
// form an open set L. At a point x of L, GermUnitIffRestrictUnit gives an
// open W ∋ x inside U on which t is a unit. Read backwards at any point y
// of W, through the same W, it makes the germ of t at y a unit, so W lies
// inside L. Each point of L thus has an open neighbourhood inside L, and L
// is open by the pointwise criterion. A presheaf of rings suffices, as it
// does for GermUnitIffRestrictUnit: no sheaf axiom is used.
var UnitLocusOpen = unitLocusOpenThm{family.Add(registry.ProofEntry{
	Name: "UnitLocusOpen",
	Key:  "prop_5bf7616d26a5a312",
	Build: family.Theorem(Statement{
		Binders: "∀F:presheaf_of_rings(A, B). ∀U:set(A). ∀t:B.",
		Hypotheses: []string{
			"U ∈ T",
			"t ∈ F(U).carrier",
		},
		Conclusion: "{x:A | " +
			"    x ∈ U ∧ " +
			"    ring_unit(stalk_ring(T, F, res, x), " +
			"        sheaf_germ(T, λU:set(A). F(U).carrier, res, x, U, t))} ∈ " +
			"T",
	},
		func(a *Argument, F PresheafOfRingsFact[on.T], U *Expr[Set[A]], t *Expr[B], hypotheses Fact) {
			locus := a.Let(
				"L",
				a.Term(
					"{x:A | "+
						"    x ∈ U ∧ "+
						"    ring_unit(stalk_ring(T, F, res, x), sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, U, t))}"))
			inLocus := a.Have(
				"a point lies in L when it lies in U and the germ of t there is a unit",
				"∀x:A. "+
					"    x ∈ L ⇔ "+
					"    x ∈ U ∧ "+
					"    ring_unit(stalk_ring(T, F, res, x), sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, U, t))",
				BySets(locus))
			germUnit := Read(GermUnitIffRestrictUnit, F)
			neighbourhood := a.Have(
				"every point of L has an open neighbourhood inside L",
				"∀x:A. x ∈ L ⇒ ∃W:set(A). W ∈ T ∧ W ⊆ L ∧ x ∈ W",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xInL := b.Assume()
					W, local := b.ObtainAs[Set[A]](
						"the germ of t at x is a unit, so t is a unit on an open W ∋ x inside U",
						"∃W:set(A). W ∈ T ∧ x ∈ W ∧ W ⊆ U ∧ ring_unit(F(W), res(U, W, t))",
						By(inLocus.At(x), xInL, hypotheses, germUnit.At(U, t, x)))
					inside := b.Have(
						"every point of W lies in L: the same W makes the germ of t there a unit",
						"∀y:A. y ∈ W ⇒ y ∈ L",
						Derive(func(c *Argument) {
							y := c.FixAs[A]("y")
							yInW := c.Assume()
							yInU := c.Have(
								"y lies in U, as W does",
								"y ∈ U",
								BySets(yInW, local))
							nearY := c.Have(
								"W is an open neighbourhood of y inside U on which t is a unit",
								"∃V:set(A). V ∈ T ∧ y ∈ V ∧ V ⊆ U ∧ ring_unit(F(V), res(U, V, t))",
								Witness(W),
								By(yInW, local))
							c.Show(
								"so the germ of t at y is a unit, and y lies in L",
								By(inLocus.At(y), yInU, hypotheses, nearY, germUnit.At(U, t, y)))
						}))
					b.Take(W)
					b.Show(
						"W is open, lies inside L and holds x",
						BySets(inside, local))
				}))
			topology := presheaf.Topology.Read(Presheaf.Read(F))
			a.Show(
				"so L is open, by the pointwise criterion for openness",
				By(topological_space.OpenPointwise.Read(topology), neighbourhood))
		}),
})}

// UnitIffGermsUnit — an inverse of t over U makes the germ of t a unit at
// every point of U, U itself being the neighbourhood GermUnitIffRestrictUnit
// asks for. Conversely the open sets inside U on which t restricts to a
// unit cover U, by GermUnitIffRestrictUnit at each point. Choose an inverse
// g(W) of t over each of them. Over an overlap W₁ ∩ W₂ the restrictions of
// g(W₁) and g(W₂) both invert the restriction of t, so they are equal,
// inverses in one commutative ring being unique. The chosen inverses
// therefore glue to a section v over U, and t·v agrees with one on every
// member of the cover, so t·v is one by locality. Gluing and locality are
// the two places the sheaf axioms enter; the germ criterion is read at
// the underlying presheaf of rings.
var UnitIffGermsUnit = unitIffGermsUnitThm{family.Add(registry.ProofEntry{
	Name: "UnitIffGermsUnit",
	Key:  "prop_e3f40f9ee9054322",
	Reading: "No nonempty-open hypothesis is needed: the sheaf " +
		"condition makes the section ring on the empty open a zero ring.",
	Build: family.Theorem(Statement{
		Binders: "∀F:sheaf_of_rings(A, B). ∀U:set(A). ∀t:B.",
		Hypotheses: []string{
			"U ∈ T",
			"t ∈ F(U).carrier",
		},
		Conclusion: "ring_unit(F(U), t) ⇔ " +
			"∀x:A. " +
			"    x ∈ U ⇒ " +
			"    ring_unit(stalk_ring(T, F, res, x), sheaf_germ(T, λU:set(A). F(U).carrier, res, x, U, t))",
	},
		func(a *Argument, F SheafOfRingsFact[on.T], U *Expr[Set[A]], t *Expr[B], hypotheses Fact) {
			ringPresheaf := SheafPresheafOfRings.Read(F)
			underlying := Presheaf.Read(ringPresheaf)
			sheaf := Sheaf.Read(F)
			germUnit := Read(GermUnitIffRestrictUnit, ringPresheaf)
			a.Iff()
			a.Forward(
				"an inverse over U makes every germ of t a unit, U "+
					"being an open neighbourhood of each of its points",
				func(b *Argument, unit Fact) {
					x := b.FixAs[A]("x")
					xInU := b.Assume()
					nearX := b.Have(
						"t is a unit on U itself, an open neighbourhood of x inside U, since t restricts to itself",
						"∃W:set(A). W ∈ T ∧ x ∈ W ∧ W ⊆ U ∧ ring_unit(F(W), res(U, W, t))",
						Witness(U),
						By(
							Normalized,
							presheaf.RestrictSelf.Read(underlying).AsFact().At(U, t),
							set_order.SubsetRefl.At(U),
							hypotheses,
							unit,
							xInU))
					b.Show(
						"so the germ of t at x is a unit",
						By(germUnit.At(U, t, x), hypotheses, xInU, nearX))
				})
			a.Backward(
				"inverses of t over the opens where t is a unit glue to an inverse over U",
				func(b *Argument, germs Fact) {
					V, cover := b.LetAs[Set[Set[A]]]("V", "{W:set(A) | W ∈ T ∧ W ⊆ U ∧ ring_unit(F(W), res(U, W, t))}")
					inCover := b.Have(
						"a set lies in V when it is open, lies inside U and t restricts to a unit over it",
						"∀W:set(A). W ∈ V ⇔ W ∈ T ∧ W ⊆ U ∧ ring_unit(F(W), res(U, W, t))",
						BySets(cover))
					open := b.Have(
						"the members of V are open",
						"V ⊆ T",
						Simp(Fwd(set_basic.SubsetDef.Inst[Set[A]]())),
						b.ForEach(func(W *Expr[Set[A]]) Action { return By(inCover.At(W)) }))
					reached := b.Have(
						"each point of U lies in a member of V",
						"∀x:A. x ∈ U ⇒ ∃W:set(A). W ∈ V ∧ x ∈ W",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xInU := c.Assume()
							W, near := c.ObtainAs[Set[A]](
								"the germ of t at x is a unit, so t is a unit on an open W ∋ x inside U",
								"∃W:set(A). W ∈ T ∧ x ∈ W ∧ W ⊆ U ∧ ring_unit(F(W), res(U, W, t))",
								By(germs.At(x), xInU, hypotheses, germUnit.At(U, t, x)))
							c.Take(W)
							c.Show(
								"W lies in V and holds x",
								By(inCover.At(W), near))
						}))
					covers := b.Have(
						"so V covers U, its members lying inside U",
						"⋃V = U",
						BySets(reached, inCover))
					inverses := b.Have(
						"t has an inverse over each member of V",
						"∀W:set(A). W ∈ V ⇒ ∃u:B. u ∈ F(W).carrier ∧ F(W).mul(res(U, W, t), u) = F(W).one",
						Derive(func(c *Argument) {
							W := c.FixAs[Set[A]]("W")
							inV := c.Assume()
							unitOverW := c.Have(
								"t restricts to a unit over W",
								"ring_unit(F(W), res(U, W, t))",
								By(inCover.At(W), inV))
							c.Show(
								"so its restriction has an inverse in F(W)",
								By(c.Unfolded(unitOverW, ring_ideal.RingUnitDef)))
						}))
					g, chosen := b.ObtainAs[Fun[Set[A], B]](
						"choose an inverse g(W) of t over each member W of V",
						"∃g:(set(A) → B). ∀W:set(A). W ∈ V ⇒ g(W) ∈ F(W).carrier ∧ F(W).mul(res(U, W, t), g(W)) = F(W).one",
						By(inverses))
					restrictInverse := b.Have(
						"restricting an inverse of t over W to an open O ⊆ W inverts t over O",
						Statement{
							Binders: "∀W O:set(A). ∀u:B.",
							Hypotheses: []string{
								"W ∈ T",
								"O ∈ T",
								"O ⊆ W",
								"W ⊆ U",
								"u ∈ F(W).carrier",
								"F(W).mul(res(U, W, t), u) = F(W).one",
							},
							Conclusion: "F(O).mul(res(U, O, t), res(W, O, u)) = F(O).one",
						},
						Derive(func(c *Argument) {
							W, O := c.FixAs[Set[A]]("W"), c.FixAs[Set[A]]("O")
							c.FixAs[B]("u")
							inverse := c.Assume()
							restriction := c.Have(
								"restricting from W to O is a ring homomorphism",
								"ring_homomorphism(F(W), F(O), res(W, O))",
								By(RestrictHomomorphism.Read(F), inverse))
							restricted := c.Have(
								"the restriction of t is a section over W",
								"res(U, W, t) ∈ F(W).carrier",
								By(presheaf.RestrictIn.Read(underlying), hypotheses, inverse))
							c.Show(
								"restriction keeps the product and keeps one",
								CalcEq(
									Leg(
										c.Term("F(O).mul(res(W, O, res(U, W, t)), res(W, O, u))"),
										"restricting t to O passes through W",
										By(
											Normalized,
											presheaf.RestrictTwice.Read(underlying).AsFact().At(U, W, O, t),
											hypotheses,
											inverse)),
									Leg(
										c.Term("res(W, O, F(W).mul(res(U, W, t), u))"),
										"restriction keeps the product",
										By(ring_homomorphism.MapMul.Read(restriction), restricted, inverse)),
									Leg(
										c.Term("res(W, O, F(W).one)"),
										"where u inverts t over W",
										By(inverse)),
									FinalLeg(
										"and restriction keeps one",
										By(ring_homomorphism.MapOne.Read(restriction))),
								))
						}))
					agree := b.Have(
						"the chosen inverses agree on overlaps",
						"∀W₁ W₂:set(A). W₁ ∈ V ∧ W₂ ∈ V ⇒ res(W₁, W₁ ∩ W₂, g(W₁)) = res(W₂, W₁ ∩ W₂, g(W₂))",
						Derive(func(c *Argument) {
							W1, W2 := c.FixAs[Set[A]]("W₁"), c.FixAs[Set[A]]("W₂")
							both := c.Assume()
							overlap := c.Have(
								"W₁ and W₂ are open sets inside U, and W₁ ∩ W₂ is open and lies in W₁, in W₂ and in U",
								"W₁ ∈ T ∧ W₂ ∈ T ∧ W₁ ⊆ U ∧ W₂ ⊆ U ∧ W₁ ∩ W₂ ∈ T ∧ W₁ ∩ W₂ ⊆ W₁ ∧ W₁ ∩ W₂ ⊆ W₂ ∧ W₁ ∩ W₂ ⊆ U",
								BySets(
									inCover.At(W1),
									inCover.At(W2),
									both,
									topological_space.InterOpen.Read(presheaf.Topology.Read(underlying)).AsFact().At(W1, W2)))
							first := c.Have(
								"the restriction of g(W₁) inverts t over W₁ ∩ W₂",
								"F(W₁ ∩ W₂).mul(res(U, W₁ ∩ W₂, t), res(W₁, W₁ ∩ W₂, g(W₁))) = F(W₁ ∩ W₂).one",
								By(
									restrictInverse.At(W1, c.TermAs[Set[A]]("W₁ ∩ W₂"), c.TermAs[B]("g(W₁)")),
									chosen.At(W1),
									both,
									overlap))
							second := c.Have(
								"and so does the restriction of g(W₂)",
								"F(W₁ ∩ W₂).mul(res(U, W₁ ∩ W₂, t), res(W₂, W₁ ∩ W₂, g(W₂))) = F(W₁ ∩ W₂).one",
								By(
									restrictInverse.At(W2, c.TermAs[Set[A]]("W₁ ∩ W₂"), c.TermAs[B]("g(W₂)")),
									chosen.At(W2),
									both,
									overlap))
							ring := c.Have(
								"the sections over W₁ ∩ W₂ form a ring",
								"comm_ring_on(F(W₁ ∩ W₂))",
								By(SectionRing.Read(ringPresheaf), overlap))
							members := c.Have(
								"t and both restricted inverses are sections over W₁ ∩ W₂",
								"res(U, W₁ ∩ W₂, t) ∈ F(W₁ ∩ W₂).carrier ∧ "+
									"res(W₁, W₁ ∩ W₂, g(W₁)) ∈ F(W₁ ∩ W₂).carrier ∧ "+
									"res(W₂, W₁ ∩ W₂, g(W₂)) ∈ F(W₁ ∩ W₂).carrier",
								By(presheaf.RestrictIn.Read(underlying), chosen.At(W1), chosen.At(W2), hypotheses, both, overlap))
							c.Show(
								"so the two restrictions are equal, inverses in a commutative ring being unique",
								CalcEq(
									Leg(
										c.Term(
											"F(W₁ ∩ W₂).mul(res(W₁, W₁ ∩ W₂, g(W₁)), "+
												"    F(W₁ ∩ W₂).mul(res(U, W₁ ∩ W₂, t), res(W₂, W₁ ∩ W₂, g(W₂))))"),
										"multiply the first by t times the second, which is one",
										ByArith(ring, members, Scaled(c.TermAs[B]("res(W₁, W₁ ∩ W₂, g(W₁))"), second))),
									FinalLeg(
										"regroup as the second times t times the first, and t times the first is one",
										ByArith(ring, members, Scaled(c.TermAs[B]("res(W₂, W₁ ∩ W₂, g(W₂))"), first))),
								))
						}))
					v, glued := b.ObtainAs[B](
						"the chosen inverses glue to a section v over U",
						"∃v:B. v ∈ F(U).carrier ∧ (∀W:set(A). W ∈ V ⇒ res(U, W, v) = g(W))",
						By(presheaf.Gluing.Read(sheaf).AsFact().At(U, V, g), hypotheses, open, covers, chosen, agree))
					gluedParts := b.Conjuncts(
						glued,
						"v is a section over U",
						"v restricts to g(W) over each member W of V")
					vIn, restricts := gluedParts[0], gluedParts[1]
					sectionRing := b.Have(
						"the sections over U form a ring",
						"comm_ring_on(F(U))",
						By(SectionRing.Read(ringPresheaf), hypotheses))
					agreeOnCover := b.Have(
						"t·v and one agree on every member of V",
						"∀W:set(A). W ∈ V ⇒ res(U, W, F(U).mul(t, v)) = res(U, W, F(U).one)",
						Derive(func(c *Argument) {
							W := c.FixAs[Set[A]]("W")
							inV := c.Assume()
							restriction := c.Have(
								"restricting from U to W is a ring homomorphism",
								"ring_homomorphism(F(U), F(W), res(U, W))",
								By(RestrictHomomorphism.Read(F).AsFact().At(U, W), inCover.At(W), inV, hypotheses))
							c.Show(
								"over W the product is t times g(W), which is one",
								CalcEq(
									Leg(
										c.Term("F(W).mul(res(U, W, t), res(U, W, v))"),
										"restriction keeps the product",
										By(ring_homomorphism.MapMul.Read(restriction), hypotheses, vIn)),
									Leg(
										c.Term("F(W).mul(res(U, W, t), g(W))"),
										"v restricts to g(W)",
										By(Normalized, restricts.At(W), inV)),
									Leg(
										c.Term("F(W).one"),
										"g(W) inverts t over W",
										By(chosen.At(W), inV)),
									FinalLeg(
										"and restriction keeps one",
										By(ring_homomorphism.MapOne.Read(restriction))),
								))
						}))
					product := b.Have(
						"so t·v is one over U, by locality",
						"F(U).mul(t, v) = F(U).one",
						By(
							presheaf.Locality.Read(sheaf).AsFact().At(
								U, V, b.TermAs[B]("F(U).mul(t, v)"), b.TermAs[B]("F(U).one")),
							hypotheses,
							open,
							covers,
							agreeOnCover,
							vIn,
							comm_ring.MulIn.Read(sectionRing),
							comm_ring.OneIn.Read(sectionRing)))
					inverse := b.Have(
						"v inverts t in F(U)",
						"∃y:B. y ∈ F(U).carrier ∧ F(U).mul(t, y) = F(U).one",
						Witness(v),
						By(vIn, product))
					b.Show(
						"hence t is a unit of F(U)",
						By(ring_ideal.RingUnitDef, hypotheses, inverse))
				})
		}),
})}
