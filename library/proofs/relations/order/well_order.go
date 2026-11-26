// well_order.go — well-orders: a total order under which every set
// that is not empty has a least point. Every type has one.

package order

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Well-orders
// ---------------------------------------------------------------------------

// WellOrder — a well-order: a total order under which every set that
// is not empty has a least point. The total order is the definition's
// first conjunct.
var WellOrder = wellOrderThm{family.DefineStructure(registry.DefEntry{
	Name:    "WellOrder",
	Key:     "prop_32437e544602d315",
	Const:   "well_order",
	Subject: "R",
	Type:    "(A → A → bool) → bool",
	Equations: []string{"∀R:(A → A → bool). " +
		"    well_order(R) ⇔ total_order(R) ∧ (∀s:set(A). s ≠ ∅ ⇒ ∃m:A. least(R, s, m))"},
	Deps: []registry.EntryLike{TotalOrder, LeastDef},
})}

// WellOrderTotalOrder — a well-order is a total order: the
// sub-structure at which the laws of a total order apply.
var WellOrderTotalOrder = wellOrderTotalOrderThm{family.Add(registry.ProofEntry{
	Name:  "WellOrderTotalOrder",
	Key:   "prop_d229429fb97e107c",
	Build: WellOrder.Axiom("total_order(R)"),
})}

// WellOrderLeast — a set that is not empty has a least point.
var WellOrderLeast = wellOrderLeastThm{family.Add(registry.ProofEntry{
	Name: "WellOrderLeast",
	Key:  "prop_e789642ac04c3d56",
	Build: WellOrder.Axiom(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ≠ ∅",
		},
		Conclusion: "∃m:A. least(R, s, m)",
	}),
})}

// WellOrderingTheorem — every type has a well-order: order points by
// their prefixes in the tower that adds one chosen point at a time. The
// prefix of x is the union of the tower's sets that miss x, and x is the
// point the tower adds to its prefix.
var WellOrderingTheorem = wellOrderingTheoremThm{family.Add(registry.ProofEntry{
	Name: "WellOrderingTheorem",
	Key:  "prop_c0ef5e7b929b361d",
	Reading: "Claimed of every type, a one-point type included, where " +
		"the one relation serves. Choice enters once, at the function " +
		"that picks a point outside each set other than the whole type.",
	Build: family.Sections(Statement{
		Conclusion: "∃R:(A → A → bool). well_order(R)",
		Abbrev: Abbrev{
			{Name: "g", Text: "λs:set(A). εx:A. x ∉ s"},
			{Name: "f", Text: "λs:set(A). insert(«g»(s), s)"},
			{Name: "prefix", Text: "λx:A. ⋃{s:set(A) | set_tower(«f», s) ∧ x ∉ s}"},
			{Name: "R", Text: "λx:A. λy:A. «prefix»(x) ⊆ «prefix»(y)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		inflationary := ctx.Lemma("∀s:set(A). s ⊆ «f»(s)", BySets())
		prefixInTower := ctx.Lemma("∀x:A. set_tower(«f», «prefix»(x)) ∧ x ∉ «prefix»(x)",
			func(a *Argument, x *Expr[A]) {
				f := a.TermAs[Fun[Set[A], Set[A]]]("«f»")
				a.Do(SplitConj(
					Case(
						"the union of these tower sets is a tower set",
						BySets(setTowerRules.At(f))),
					Case(
						"a union of sets missing x still misses x",
						BySets()),
				))
			})
		successorContains := ctx.Lemma("∀x:A. x ∈ «f»(«prefix»(x))",
			func(a *Argument, x *Expr[A]) {
				f := a.TermAs[Fun[Set[A], Set[A]]]("«f»")
				_, qDef := a.LetAs[Set[A]]("q", "«prefix»(x)")
				inTower := a.Have(
					"q is a tower set missing x",
					"set_tower(«f», q) ∧ x ∉ q",
					By(qDef, At(prefixInTower, x)))
				outside := a.Have(
					"x itself lies outside q, so the point g(q) chosen outside q does too",
					"«g»(q) ∉ q",
					BySets(inTower))
				imageInTower := a.Have(
					"the successor of q is a tower set",
					"set_tower(«f», «f»(q))",
					By(inTower, setTowerRules.At(f)))
				missing := a.SupposeNot()
				inside := a.Have(
					"a successor missing x is part of its prefix",
					"«f»(q) ⊆ q",
					BySets(missing, qDef, imageInTower))
				a.Show(
					"c, the point the successor of q inserts, would lie both in q and outside q",
					BySets(DenotedAs("c", a.TermAs[A]("«g»(q)")), outside, inside))
			})
		recoverPoint := ctx.Lemma("∀x:A. x = «g»(«prefix»(x))",
			func(a *Argument, x *Expr[A]) {
				a.Show(
					"x is the point inserted at its prefix",
					BySets(
						DenotedAs("q", a.TermAs[Set[A]]("«prefix»(x)")),
						At(prefixInTower, x),
						At(successorContains, x)))
			})
		antisymmetric := ctx.Lemma(Statement{
			Binders:    "∀x y:A.",
			Hypotheses: []string{"«R»(x, y)", "«R»(y, x)"},
			Conclusion: "x = y",
		}, func(a *Argument, x, y *Expr[A], both Fact) {
			px := a.TermAs[Set[A]]("«prefix»(x)")
			py := a.TermAs[Set[A]]("«prefix»(y)")
			a.Show(
				"two prefixes containing each other are equal, and equal prefixes recover the same point",
				By(both, set_order.SubsetAntisym.At(px, py), At(recoverPoint, x), At(recoverPoint, y)))
		})
		preorder := ctx.Lemma("preorder(«R»)",
			Preorder.Intro(
				Case(
					"reflexive: inclusion makes every prefix below itself",
					Unfold(equivalence.ReflexiveDef),
					BySets()),
				Case(
					"transitive: inclusion of prefixes is transitive",
					Unfold(equivalence.TransitiveDef),
					BySets())))
		partial := ctx.Lemma("partial_order(«R»)",
			PartialOrder.Intro(
				Case(
					"the prefix relation is a preorder",
					Cite(preorder)),
				Case(
					"antisymmetric: equal prefixes determine equal points",
					Unfold(AntisymmetricDef),
					Cite(antisymmetric))))
		total := ctx.Lemma("total_order(«R»)",
			TotalOrder.Intro(
				Case(
					"the prefix relation is a partial order",
					Cite(partial)),
				Case(
					"any two prefixes are comparable in the tower",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						y := b.FixAs[A]("y")
						f := b.TermAs[Fun[Set[A], Set[A]]]("«f»")
						px := b.TermAs[Set[A]]("«prefix»(x)")
						py := b.TermAs[Set[A]]("«prefix»(y)")
						b.Show(
							"the tower chain compares their prefixes",
							By(inflationary, At(prefixInTower, x), At(prefixInTower, y), TowerChain.At(f, px, py)))
					}))))

		// Pull a least member of an image family back to a point. It is stated for
		// any inflationary f and any p into its tower, the hypotheses TowerLeast
		// reads, since the pull-back uses nothing more of «f» and «prefix».
		leastPrefix := ctx.Lemma(Statement{
			Binders: "∀f:(set(A) → set(A)). ∀p:(A → set(A)). ∀s:set(A).",
			Hypotheses: []string{
				"∀t:set(A). t ⊆ f(t)",
				"∀x:A. set_tower(f, p(x))",
				"s ≠ ∅",
			},
			Conclusion: "∃m:A. m ∈ s ∧ (∀x:A. x ∈ s ⇒ p(m) ⊆ p(x))",
		}, func(
			a *Argument,
			f *Arrow[Set[A], Set[A]],
			p *Arrow[A, Set[A]],
			s *Expr[Set[A]],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"f is inflationary",
				"p sends every point to a tower set",
				"s has a point")
			inflates, allInTower, nonempty := parts[0], parts[1], parts[2]
			G, gDef := a.LetAs[Set[Set[A]]]("G", "{p(x) | x:A | x ∈ s}")
			familyInTower := a.Have(
				"the image family is nonempty and lies in the tower",
				"G ≠ ∅ ∧ (∀t:set(A). t ∈ G ⇒ set_tower(f, t))",
				BySets(nonempty, allInTower, gDef))
			_, minimal := a.ObtainAs[Set[A]](
				"a least member of the family",
				"∃q:set(A). q ∈ G ∧ (∀t:set(A). t ∈ G ⇒ q ⊆ t)",
				By(familyInTower, inflates, TowerLeast.At(f, G)))
			least := a.Conjuncts(
				minimal,
				"q belongs to G",
				"q lies in every member of G")
			qInG, belowAll := least[0], least[1]
			m, realizes := a.ObtainAs[A](
				"a point of s whose image is q",
				"∃m:A. m ∈ s ∧ q = p(m)",
				BySets(gDef, qInG))
			a.Take(m)
			a.Do(SplitConj(
				Case(
					"the chosen point belongs to s",
					By(realizes)),
				Case(
					"its image lies in the image of each point of s",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						xIn := b.Assume()
						b.Show(
							"leastness of q gives the inclusion",
							BySets(Normalized, gDef, xIn, realizes, belowAll.At(p.Apply(x))))
					})),
			))
		})
		leastPoint := ctx.Lemma(Statement{
			Binders:    "∀s:set(A).",
			Hypotheses: []string{"s ≠ ∅"},
			Conclusion: "∃m:A. least(«R», s, m)",
		}, func(a *Argument, s *Expr[Set[A]], nonempty Fact) {
			f := a.TermAs[Fun[Set[A], Set[A]]]("«f»")
			prefix := a.TermAs[Fun[A, Set[A]]]("«prefix»")
			m, minimal := a.ObtainAs[A](
				"a point whose prefix is least among those from s",
				"∃m:A. m ∈ s ∧ (∀x:A. x ∈ s ⇒ «R»(m, x))",
				By(nonempty, prefixInTower, inflationary, At(leastPrefix, f, prefix, s)))
			a.Take(m)
			R := a.TermAs[Fun2[A, A, Bool]]("«R»")
			a.Show(
				"this is a least point under the prefix relation",
				By(minimal, LeastDef.At(R, s, m), LowerBoundDef.At(R, s, m)))
		})
		return ctx.Theorem(headline, func(a *Argument) {
			R := a.TermAs[Fun2[A, A, Bool]]("«R»")
			a.Take(R)
			a.Show(
				"the prefix relation is a well-order",
				By(total, leastPoint, WellOrder.At(R)))
		})
	}),
})}
