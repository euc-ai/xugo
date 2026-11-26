package d_separation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/closure"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// DSeparatedSymmetric swaps the two separated sets while keeping the
// conditioning set fixed.
var DSeparatedSymmetric = dSeparatedSymmetricThm{family.Add(registry.ProofEntry{
	Name: "DSeparatedSymmetric",
	Key:  "prop_1a19f4c0d919b168",
	Build: family.Sections(Statement{
		Binders:    "∀E:(A → A → bool). ∀X Y Z:set(A).",
		Hypotheses: []string{"d_separated(E, X, Y, Z)"},
		Conclusion: "d_separated(E, Y, X, Z)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		reverseWalk := ctx.Lemma(Statement{
			Binders:    "∀E:(A → A → bool). ∀U Z:set(A). ∀u v:A.",
			Hypotheses: []string{"transitive_closure(«R», u, v)"},
			Conclusion: "transitive_closure(«R», v, u)",
			Abbrev: Abbrev{
				{Name: "R", Text: "relation_on(U ∖ Z, dag_moral(E, U))"},
			},
		}, func(a *Argument, E *Arrow2[A, A, Bool], U, Z *Expr[Set[A]], u, v *Expr[A], walk Fact) {
			restricted := a.TermAs[Fun2[A, A, Bool]]("«R»")
			rules := closure.TransitiveClosureRules.At(restricted)
			a.Do(ByInduction(
				closure.TransitiveClosureInduct, walk,
				Case(
					"reverse one moral edge within U ∖ Z",
					Derive(func(b *Argument) {
						x := b.FixAs[A]()
						y := b.FixAs[A]()
						edge := b.Assume()
						allowed := b.TermAs[Set[A]]("U ∖ Z")
						moral := b.TermAs[Fun2[A, A, Bool]]("dag_moral(E, U)")
						b.Show(
							"the reversed edge gives a walk",
							By(
								edge,
								equivalence.RelationOnDef.At(allowed, moral, x, y),
								equivalence.RelationOnDef.At(allowed, moral, y, x),
								MoralDef.At(E, U, x, y),
								MoralDef.At(E, U, y, x),
								rules))
					})),
				Case(
					"join the reversed walks in reverse order",
					By(rules)),
			))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			E *Arrow2[A, A, Bool],
			X, Y, Z *Expr[Set[A]],
			separated Fact,
		) {
			noWalk := a.Unfolded(separated, DSeparatedDef)
			a.Do(Simp(Fwd(DSeparatedDef)))
			sameUnion := a.Have(
				"swapping X and Y keeps their union with Z",
				"Y ∪ X ∪ Z = X ∪ Y ∪ Z",
				BySets())
			a.Do(sameUnion.Rw())

			from := a.FixAs[A]()
			to := a.FixAs[A]()
			endpoints := a.Assume()
			ancestors := a.TermAs[Set[A]]("dag_ancestors(E, X ∪ Y ∪ Z)")
			a.Show(
				"a walk from Y to X would reverse to a forbidden walk",
				By(endpoints, noWalk.At(to, from), At(reverseWalk, E, ancestors, Z, from, to)))
		})
	}),
})}

// SeparationCertificate proves separation by trapping every moral walk
// from X in a set disjoint from Y.
var SeparationCertificate = separationCertificateThm{family.Add(registry.ProofEntry{
	Name: "SeparationCertificate",
	Reading: "Moral adjacency on the ancestral set implies moral adjacency on U " +
		"(a common child in U need not be an ancestor); only that direction is needed.",
	Key: "prop_93ae7a816121cd5f",
	Build: family.Theorem(Statement{
		Binders: "∀E:(A → A → bool). ∀X Y Z U S:set(A).",
		Hypotheses: []string{
			"X ∪ Y ∪ Z ⊆ U",
			"dag_ancestral(E, U)",
			"X ⊆ S",
			"S ∩ Y = ∅",
			"∀u v:A. u ∈ S ∧ v ∈ U ∖ Z ∧ dag_moral(E, U, u, v) ⇒ v ∈ S",
		},
		Conclusion: "d_separated(E, X, Y, Z)",
		Abbrev: Abbrev{
			{Name: "C", Text: "dag_ancestors(E, X ∪ Y ∪ Z)"},
			{Name: "R", Text: "relation_on(«C» ∖ Z, dag_moral(E, «C»))"},
		},
	}, func(
		a *Argument,
		E *Arrow2[A, A, Bool],
		X, Y, Z, U, S *Expr[Set[A]],
		containsSeeds, ancestral, containsX, disjointY, moralClosed Fact,
	) {
		seeds := a.TermAs[Set[A]]("X ∪ Y ∪ Z")
		ancestors := a.TermAs[Set[A]]("«C»")
		allowed := a.TermAs[Set[A]]("«C» ∖ Z")
		moral := a.TermAs[Fun2[A, A, Bool]]("dag_moral(E, «C»)")
		walkRelation := a.TermAs[Fun2[A, A, Bool]]("«R»")
		containsAncestors := a.Have(
			"the ancestral set U contains the ancestors of the three sets",
			"«C» ⊆ U",
			By(containsSeeds, ancestral, dag.AncestorsUpperBound.At(E, seeds, U)))
		stepsStayInS := a.Have(
			"each restricted moral edge from S stays in S",
			"∀u v:A. «R»(u, v) ∧ u ∈ S ⇒ v ∈ S",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				edgeFromS := b.Assume()
				restricted := b.Have(
					"the edge is a moral edge on the ancestors whose target is outside Z",
					"v ∈ «C» ∖ Z ∧ dag_moral(E, «C», u, v)",
					By(edgeFromS, equivalence.RelationOnDef.At(allowed, moral, u, v)))
				parts := b.Conjuncts(
					restricted,
					"the target belongs to the restricted set",
					"the moral edge")
				targetInU := b.Have(
					"the target belongs to U outside Z",
					"v ∈ U ∖ Z",
					BySets(parts[0], containsAncestors))
				moralInU := b.Have(
					"any shared child witnessing moral adjacency also belongs to U",
					"dag_moral(E, U, u, v)",
					BySets(parts[1], containsAncestors, MoralDef.At(E, ancestors, u, v), MoralDef.At(E, U, u, v)))
				b.Show(
					"moral closure in U keeps the target in S",
					By(edgeFromS, targetInU, moralInU, moralClosed.At(u, v)))
			}))
		a.Do(Simp(Fwd(DSeparatedDef)))
		x := a.FixAs[A]()
		y := a.FixAs[A]()
		endpoints := a.Assume()
		start := a.Have(
			"the point of X belongs to S",
			"x ∈ S",
			BySets(endpoints, containsX))
		end := a.Have(
			"S is disjoint from Y",
			"y ∉ S",
			BySets(endpoints, disjointY))
		inS := a.TermAs[Set[A]]("λp:A. p ∈ S")
		a.Show(
			"a walk from x would keep y in S, contradicting its membership in Y",
			By(
				start,
				end,
				stepsStayInS,
				closure.ReflexiveTransitiveClosureDef.At(walkRelation, x, y),
				closure.ReflexiveTransitiveClosurePreserves.At(walkRelation, inS, x, y)))
	}),
})}

// SeparationGivesCertificate — a separation yields its certificate: inside
// a carrier U that contains X and lies in the ancestral set, the points of
// U ∖ Z reached from X by moral walks outside Z contain X, miss Y, and are
// closed under moral steps in U outside Z.
var SeparationGivesCertificate = separationGivesCertificateThm{family.Add(registry.ProofEntry{
	Name: "SeparationGivesCertificate",
	Key:  "prop_392a74d27fd21aef",
	Build: family.Theorem(Statement{
		Binders: "∀E:(A → A → bool). ∀X Y Z U:set(A).",
		Hypotheses: []string{
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"X ⊆ U",
			"U ⊆ dag_ancestors(E, X ∪ Y ∪ Z)",
			"d_separated(E, X, Y, Z)",
		},
		Conclusion: "∃S:set(A). " +
			"    X ⊆ S ∧ S ⊆ U ∖ Z ∧ S ∩ Y = ∅ ∧ (∀u v:A. u ∈ S ∧ v ∈ U ∖ Z ∧ dag_moral(E, U, u, v) ⇒ v ∈ S)",
		Abbrev: Abbrev{
			{Name: "C", Text: "dag_ancestors(E, X ∪ Y ∪ Z)"},
			{Name: "R", Text: "relation_on(«C» ∖ Z, dag_moral(E, «C»))"},
			{Name: "Reached", Text: "{v:A | " +
				"    v ∈ U ∖ Z ∧ (∃x:A. x ∈ X ∧ reflexive_transitive_closure(«R», x, v))}"},
		},
	}, func(
		a *Argument,
		E *Arrow2[A, A, Bool],
		X, Y, Z, U *Expr[Set[A]],
		apartXY, apartXZ, containsX, withinAncestors, separated Fact,
	) {
		ancestors := a.TermAs[Set[A]]("«C»")
		allowed := a.TermAs[Set[A]]("«C» ∖ Z")
		moral := a.TermAs[Fun2[A, A, Bool]]("dag_moral(E, «C»)")
		walk := a.TermAs[Fun2[A, A, Bool]]("«R»")
		a.Take(a.TermAs[Set[A]]("«Reached»"))
		read := a.Have(
			"a reached point lies in U outside Z at the end of a walk from X",
			"∀v:A. v ∈ «Reached» ⇔ v ∈ U ∖ Z ∧ (∃x:A. x ∈ X ∧ reflexive_transitive_closure(«R», x, v))",
			BySets())
		contains := a.Have(
			"every point of X reaches itself",
			"X ⊆ «Reached»",
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(b *Argument) {
				x := b.FixAs[A]()
				start := b.Assume()
				permitted := b.Have(
					"a point of X lies in U outside Z",
					"x ∈ U ∖ Z",
					BySets(start, containsX, apartXZ))
				b.Show(
					"take the walk of length zero",
					By(read.At(x), permitted, start, closure.ReflexiveTransitiveClosureDef.At(walk, x, x)))
			}))
		inside := a.Have(
			"the reached points lie in U outside Z",
			"«Reached» ⊆ U ∖ Z",
			BySets())
		noWalk := a.Unfolded(separated, DSeparatedDef)
		noMeet := a.Have(
			"no point of Y is reached",
			"∀v:A. v ∈ «Reached» ∧ v ∈ Y ⇒ ⊥",
			Derive(func(b *Argument) {
				v := b.FixAs[A]()
				inBoth := b.Assume()
				x, reach := b.ObtainAs[A](
					"take the start of the walk",
					"∃x:A. x ∈ X ∧ reflexive_transitive_closure(«R», x, v)",
					By(read.At(v), inBoth))
				distinct := b.Have(
					"the walk joins disjoint sets, so it has positive length",
					"x ≠ v",
					BySets(reach, inBoth, apartXY))
				b.Show(
					"a positive-length walk from X to Y contradicts separation",
					By(noWalk.At(x, v), reach, inBoth, distinct, closure.ReflexiveTransitiveClosureDef.At(walk, x, v)))
			}))
		misses := a.Have(
			"the reached points miss Y",
			"«Reached» ∩ Y = ∅",
			BySets(noMeet))
		closed := a.Have(
			"a moral step in U outside Z extends a walk",
			"∀u v:A. u ∈ «Reached» ∧ v ∈ U ∖ Z ∧ dag_moral(E, U, u, v) ⇒ v ∈ «Reached»",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				link := b.Assume()
				endpoints := b.Have(
					"both endpoints lie in the ancestral set outside Z",
					"u ∈ «C» ∖ Z ∧ v ∈ «C» ∖ Z",
					BySets(link, withinAncestors))
				moralInC := b.Have(
					"a common child in U is a common child in the ancestral set",
					"dag_moral(E, «C», u, v)",
					By(
						link,
						withinAncestors,
						set_basic.SubsetDef.At(U, ancestors),
						MoralDef.At(E, U, u, v),
						MoralDef.At(E, ancestors, u, v)))
				x, reach := b.ObtainAs[A](
					"take the start of the walk to u",
					"∃x:A. x ∈ X ∧ reflexive_transitive_closure(«R», x, u)",
					By(read.At(u), link))
				step := b.Have(
					"the moral step is a walk of one step",
					"reflexive_transitive_closure(«R», u, v)",
					By(
						endpoints,
						moralInC,
						equivalence.RelationOnDef.At(allowed, moral, u, v),
						closure.TransitiveClosureRules.At(walk),
						closure.ReflexiveTransitiveClosureDef.At(walk, u, v)))
				b.Show(
					"append the moral step",
					By(read.At(v), link, step, reach, closure.ReflexiveTransitiveClosureTransitive.At(walk, x, u, v)))
			}))
		a.Show(
			"the reached points are the certificate",
			By(contains, inside, misses, closed))
	}),
})}

// DSeparatedIsolatedRoots — a group Y with no edges into it that is no
// ancestor of X ∪ Z is separated from X given Z: the ancestors of X ∪ Z
// certify it inside the carrier they form with Y, where a point of Y has
// no parent and no child.
var DSeparatedIsolatedRoots = dSeparatedIsolatedRootsThm{family.Add(registry.ProofEntry{
	Name: "DSeparatedIsolatedRoots",
	Key:  "prop_a4749df36ab8e82a",
	Reading: "No DAG and no disjointness hypothesis: a point of Y in X ∪ Z would be " +
		"its own ancestor there. The deletion step of Rule 3, the third line of ID and the " +
		"back-door derivation read it in a graph whose edges into Y are already deleted.",
	Build: family.Theorem(Statement{
		Binders: "∀E:(A → A → bool). ∀X Y Z:set(A).",
		Hypotheses: []string{
			"∀u y:A. y ∈ Y ⇒ ¬E(u, y)",
			"dag_ancestors(E, X ∪ Z) ∩ Y = ∅",
		},
		Conclusion: "d_separated(E, X, Y, Z)",
		Abbrev: Abbrev{
			{Name: "S", Text: "dag_ancestors(E, X ∪ Z)"},
			{Name: "U", Text: "«S» ∪ Y"},
		},
	}, func(a *Argument, E *Arrow2[A, A, Bool], X, Y, Z *Expr[Set[A]], noParents, disjoint Fact) {
		groups := a.TermAs[Set[A]]("X ∪ Z")
		ancestors := a.TermAs[Set[A]]("«S»")
		carrier := a.TermAs[Set[A]]("«U»")
		ancestorFacts := a.Conjuncts(
			dag.AncestorsClosed.At(E, groups),
			"X ∪ Z belongs to its ancestor set",
			"the ancestor set is ancestral")
		parentsOfAncestors := a.Unfolded(ancestorFacts[1], dag.AncestralDef)
		ancestral := a.Have(
			"adjoining Y keeps the set ancestral because Y has no parents",
			"dag_ancestral(E, «U»)",
			Unfold(dag.AncestralDef),
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				edge := b.Assume()
				b.Show(
					"the edge ends in the ancestor set, which contains its parent",
					BySets(edge, parentsOfAncestors.At(u, v), noParents.At(u, v)))
			}))
		noChildren := a.Have(
			"points of Y have no children in U",
			"∀u v:A. u ∈ Y ∧ v ∈ «U» ⇒ ¬E(u, v)",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				endpoints := b.Assume()
				b.Show(
					"a child in Y would be an edge into Y, and a child among the ancestors would make u one of them",
					BySets(endpoints, disjoint, parentsOfAncestors.At(u, v), noParents.At(u, v)))
			}))
		moralClosed := a.Have(
			"moral neighbours of the ancestor set in U stay in the ancestor set",
			"∀u v:A. u ∈ «S» ∧ v ∈ «U» ∖ Z ∧ dag_moral(E, «U», u, v) ⇒ v ∈ «S»",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				adjacent := b.Assume()
				b.Show(
					"a moral edge to Y would need an edge into Y or a child of a point of Y in U",
					BySets(adjacent, noChildren.At(v), noParents.At(u, v), MoralDef.At(E, carrier, u, v)))
			}))
		containsGroups := a.Have(
			"U contains the three groups",
			"X ∪ Y ∪ Z ⊆ «U»",
			BySets(ancestorFacts[0]))
		containsX := a.Have(
			"the ancestor set contains X",
			"X ⊆ «S»",
			BySets(ancestorFacts[0]))
		a.Show(
			"the ancestor set contains X and keeps every moral walk away from Y",
			By(
				containsGroups,
				ancestral,
				containsX,
				disjoint,
				moralClosed,
				SeparationCertificate.At(E, X, Y, Z, carrier, ancestors)))
	}),
})}

// DeleteInSeparatesNonDescendants separates X from its non-descendants
// after deleting the edges into X.
var DeleteInSeparatesNonDescendants = deleteInSeparatesNonDescendantsThm{family.Add(registry.ProofEntry{
	Name: "DeleteInSeparatesNonDescendants",
	Key:  "prop_caf03d0b409b780c",
	Build: family.Theorem(Statement{
		Binders:    "∀E:(A → A → bool). ∀X Y:set(A).",
		Hypotheses: []string{"dag_ancestors(E, Y) ∩ X = ∅"},
		Conclusion: "d_separated(dag_delete_in(E, X), Y, X, ∅)",
	}, func(a *Argument, E *Arrow2[A, A, Bool], X, Y *Expr[Set[A]], originalDisjoint Fact) {
		deleted := a.TermAs[Fun2[A, A, Bool]]("dag_delete_in(E, X)")
		empty := a.TermAs[Set[A]]("∅")
		noParents := a.Have(
			"deletion leaves X without parents",
			"∀u x:A. x ∈ X ⇒ ¬dag_delete_in(E, X, u, x)",
			By(dag.DeleteInDef))
		disjoint := a.Have(
			"the ancestors of Y after deletion are the original ones, which avoid X",
			"dag_ancestors(dag_delete_in(E, X), Y) ∩ X = ∅",
			By(Normalized, originalDisjoint, dag.AncestorsDeleteIn.At(E, Y, X)))
		a.Show(
			"X, without parents and no ancestor of Y, is separated from Y",
			By(
				noParents,
				disjoint,
				set_algebra.UnionEmpty.At(Y),
				DSeparatedIsolatedRoots.At(deleted, Y, X, empty)))
	}),
})}

// DSeparatedAncestorsReachConditioningSet says that an ancestor of Y
// in the separated set X is also an ancestor of the conditioning set.
var DSeparatedAncestorsReachConditioningSet = dSeparatedAncestorsReachConditioningSetThm{family.Add(registry.ProofEntry{
	Name: "DSeparatedAncestorsReachConditioningSet",
	Key:  "prop_51272b18feef0367",
	Build: family.Theorem(Statement{
		Binders: "∀E:(A → A → bool). ∀X Y W:set(A).",
		Hypotheses: []string{
			"X ∩ Y = ∅",
			"d_separated(E, X, Y, W)",
		},
		Conclusion: "dag_ancestors(E, Y) ∩ X ⊆ dag_ancestors(E, W)",
		Abbrev: Abbrev{
			{Name: "U", Text: "dag_ancestors(E, X ∪ Y ∪ W)"},
			{Name: "R", Text: "relation_on(«U» ∖ W, dag_moral(E, «U»))"},
		},
	}, func(a *Argument, E *Arrow2[A, A, Bool], X, Y, W *Expr[Set[A]], disjoint, separated Fact) {
		conditioningAncestors := a.Conjuncts(
			dag.AncestorsClosed.At(E, W),
			"W is contained in its ancestors",
			"the ancestors of W are ancestral")
		parentsOfConditioning := a.Unfolded(conditioningAncestors[1], dag.AncestralDef)
		union := a.TermAs[Set[A]]("X ∪ Y ∪ W")
		unionAncestors := a.Conjuncts(
			dag.AncestorsClosed.At(E, union),
			"U contains all three sets",
			"U is ancestral")
		parentsInU := a.Unfolded(unionAncestors[1], dag.AncestralDef)
		staysOutside := a.Have(
			"an edge from outside the ancestors of W stays outside them",
			"∀u v:A. E(u, v) ∧ u ∉ dag_ancestors(E, W) ⇒ v ∉ dag_ancestors(E, W)",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				edge := b.Assume()
				b.Show(
					"a target reaching W would put its parent among the ancestors of W",
					By(edge, parentsOfConditioning.At(u, v)))
			}))
		ancestralSet := a.TermAs[Set[A]]("«U»")
		allowedSet := a.TermAs[Set[A]]("«U» ∖ W")
		moralRelation := a.TermAs[Fun2[A, A, Bool]]("dag_moral(E, «U»)")
		restrictedRelation := a.TermAs[Fun2[A, A, Bool]]("«R»")
		edgeWalk := a.Have(
			"a directed edge outside the ancestors of W into U gives a restricted moral walk",
			"∀u v:A. E(u, v) ∧ u ∉ dag_ancestors(E, W) ∧ v ∈ «U» ⇒ reflexive_transitive_closure(«R», u, v)",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				edge := b.Assume()
				allowed := b.Have(
					"both ends of the edge are in U and outside W",
					"u ∈ «U» ∖ W ∧ v ∈ «U» ∖ W",
					BySets(edge, conditioningAncestors[0], staysOutside.At(u, v), parentsInU.At(u, v)))
				next := b.Have(
					"distinct endpoints are adjacent in the restricted moral graph",
					"u = v ∨ «R»(u, v)",
					By(
						allowed,
						edge,
						MoralDef.At(E, ancestralSet, u, v),
						equivalence.RelationOnDef.At(allowedSet, moralRelation, u, v)))
				b.Show(
					"this gives a walk of zero or one step",
					By(
						next,
						closure.TransitiveClosureRules.At(restrictedRelation),
						closure.ReflexiveTransitiveClosureDef.At(restrictedRelation, u, v)))
			}))
		a.Do(Simp(Fwd(set_basic.SubsetDef)))
		x := a.FixAs[A]()
		inIntersection := a.Assume()
		inBoth := a.Have(
			"the point is in X and reaches Y",
			"x ∈ dag_ancestors(E, Y) ∧ x ∈ X",
			By(inIntersection, set_basic.InInter.At(a.TermAs[Set[A]]("dag_ancestors(E, Y)"), X, x)))
		parts := a.Conjuncts(
			inBoth,
			"x reaches Y",
			"x belongs to X")
		y, witness := a.UnpackAs[A](a.Unfolded(parts[0], dag.AncestorsDef), "y")
		outside := a.SupposeNot()
		preserve := a.Have(
			"a directed edge preserves avoidance and extends the restricted moral walk inside U",
			Statement{
				Binders: "∀u v:A.",
				Hypotheses: []string{
					"E(u, v)",
					"u ∉ dag_ancestors(E, W) ∧ (u ∈ «U» ⇒ reflexive_transitive_closure(«R», x, u))",
				},
				Conclusion: "v ∉ dag_ancestors(E, W) ∧ (v ∈ «U» ⇒ reflexive_transitive_closure(«R», x, v))",
			},
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				step := b.Assume()
				b.Do(SplitConj(
					Case(
						"the target stays outside the ancestors of W",
						By(step, staysOutside.At(u, v))),
					Case(
						"if the target lies in U the source also lies in U and the moral walk extends",
						Derive(func(c *Argument) {
							targetInU := c.Assume()
							c.Show(
								"join the walk to the source with the walk along the edge",
								By(
									step,
									targetInU,
									parentsInU.At(u, v),
									edgeWalk.At(u, v),
									closure.ReflexiveTransitiveClosureTransitive.At(restrictedRelation, x, u, v)))
						})),
				))
			}))
		start := a.Have(
			"x avoids the ancestors of W and reaches itself by the empty walk",
			"x ∉ dag_ancestors(E, W) ∧ (x ∈ «U» ⇒ reflexive_transitive_closure(«R», x, x))",
			By(outside, closure.ReflexiveTransitiveClosureDef.At(restrictedRelation, x, x)))
		invariant := a.TermAs[Set[A]](
			"λp:A. p ∉ dag_ancestors(E, W) ∧ (p ∈ «U» ⇒ reflexive_transitive_closure(«R», x, p))")
		atY := a.Have(
			"the directed walk from x carries avoidance and restricted reachability to y",
			"y ∉ dag_ancestors(E, W) ∧ (y ∈ «U» ⇒ reflexive_transitive_closure(«R», x, y))",
			By(preserve, witness, start, closure.ReflexiveTransitiveClosurePreserves.At(E, invariant, x, y)))
		yInU := a.Have(
			"U contains Y",
			"y ∈ «U»",
			BySets(witness, unionAncestors[0]))
		distinct := a.Have(
			"x and y lie in disjoint sets",
			"x ≠ y",
			BySets(parts[1], witness, disjoint))
		noWalk := a.Unfolded(separated, DSeparatedDef)
		a.Show(
			"the nonempty restricted moral walk from x to y contradicts separation",
			By(
				parts[1],
				witness,
				atY,
				yInU,
				distinct,
				noWalk.At(x, y),
				closure.ReflexiveTransitiveClosureDef.At(restrictedRelation, x, y)))
	}),
})}

// DSeparatedEdgeMonotone preserves a separation when edges are deleted.
var DSeparatedEdgeMonotone = dSeparatedEdgeMonotoneThm{family.Add(registry.ProofEntry{
	Name: "DSeparatedEdgeMonotone",
	Key:  "prop_9318080bd85c2412",
	Build: family.Theorem(Statement{
		Binders:    "∀E F:(A → A → bool). ∀X Y Z:set(A).",
		Hypotheses: []string{"∀u v:A. F(u, v) ⇒ E(u, v)", "d_separated(E, X, Y, Z)"},
		Conclusion: "d_separated(F, X, Y, Z)",
		Abbrev: Abbrev{
			{Name: "SmallerAncestors", Text: "dag_ancestors(F, X ∪ Y ∪ Z)"},
			{Name: "LargerAncestors", Text: "dag_ancestors(E, X ∪ Y ∪ Z)"},
			{Name: "SmallerRestriction", Text: "relation_on(«SmallerAncestors» ∖ Z, " +
				"    dag_moral(F, «SmallerAncestors»))"},
			{Name: "LargerRestriction", Text: "relation_on(«LargerAncestors» ∖ Z, " +
				"    dag_moral(E, «LargerAncestors»))"},
		},
	}, func(a *Argument, E, F *Arrow2[A, A, Bool], X, Y, Z *Expr[Set[A]], edges, separated Fact) {
		groups := a.TermAs[Set[A]]("X ∪ Y ∪ Z")
		smaller := a.TermAs[Set[A]]("«SmallerAncestors»")
		larger := a.TermAs[Set[A]]("«LargerAncestors»")
		smallerInLarger := a.Have(
			"the ancestors in the smaller graph are ancestors in the larger graph",
			"«SmallerAncestors» ⊆ «LargerAncestors»",
			By(edges, set_order.SubsetRefl.At(groups), dag.AncestorsMonotone.At(F, E, groups, groups)))
		moralEdges := a.Have(
			"each moral edge in the smaller graph survives in the larger graph",
			"∀u v:A. dag_moral(F, «SmallerAncestors», u, v) ⇒ dag_moral(E, «LargerAncestors», u, v)",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				moral := b.Assume()
				smallEdge := MoralDef.At(F, smaller, u, v)
				largeEdge := MoralDef.At(E, larger, u, v)
				distinct := b.Have(
					"the endpoints are distinct",
					"u ≠ v",
					By(moral, smallEdge))
				adjacent := b.Have(
					"a directed edge or a common child witnesses adjacency",
					"(F(u, v) ∨ F(v, u)) ∨ (∃w:A. w ∈ «SmallerAncestors» ∧ F(u, w) ∧ F(v, w))",
					By(moral, smallEdge))
				b.Do(adjacent.SplitDisj(
					LeftHolds(
						"a directed edge survives in either orientation",
						Given(func(c *Argument, direct Fact) {
							c.Show(
								"the directed edge gives moral adjacency",
								By(distinct, direct, edges.At(u, v), edges.At(v, u), largeEdge))
						})),
					RightHolds(
						"both arrows to a common child survive",
						Given(func(c *Argument, commonChild Fact) {
							w, child := c.UnpackAs[A](commonChild)
							inLarger := c.Have(
								"the child is among the larger ancestral set",
								"w ∈ «LargerAncestors»",
								BySets(child, smallerInLarger))
							sameChild := c.Have(
								"the same child witnesses the adjacency",
								"∃w:A. w ∈ «LargerAncestors» ∧ E(u, w) ∧ E(v, w)",
								Derive(func(d *Argument) {
									d.Take(w)
									d.Show(
										"the two arrows and membership supply the witness",
										By(child, inLarger, edges.At(u, w), edges.At(v, w)))
								}))
							c.Show(
								"the common child gives moral adjacency",
								By(distinct, sameChild, largeEdge))
						}))))
			}))
		restrictedEdges := a.Have(
			"the inclusion survives removal of the conditioning set",
			"∀u v:A. «SmallerRestriction»(u, v) ⇒ «LargerRestriction»(u, v)",
			Derive(func(b *Argument) {
				u := b.FixAs[A]()
				v := b.FixAs[A]()
				restricted := b.Assume()
				edge := b.Simplified(restricted, Fwd(equivalence.RelationOnDef))
				endpoints := b.Have(
					"both endpoints belong to the larger scope outside Z",
					"u ∈ «LargerAncestors» ∖ Z ∧ v ∈ «LargerAncestors» ∖ Z",
					BySets(edge, smallerInLarger))
				allowed := b.TermAs[Set[A]]("«LargerAncestors» ∖ Z")
				largerMoral := b.TermAs[Fun2[A, A, Bool]]("dag_moral(E, «LargerAncestors»)")
				b.Show(
					"the transferred edge belongs to the larger restriction",
					By(edge, endpoints, moralEdges.At(u, v), equivalence.RelationOnDef.At(allowed, largerMoral, u, v)))
			}))

		noWalk := a.Unfolded(separated, DSeparatedDef)
		a.Do(Simp(Fwd(DSeparatedDef)))
		x := a.FixAs[A]()
		y := a.FixAs[A]()
		endpoints := a.Assume()
		smallerRelation := a.TermAs[Fun2[A, A, Bool]]("«SmallerRestriction»")
		largerRelation := a.TermAs[Fun2[A, A, Bool]]("«LargerRestriction»")
		a.Show(
			"a connecting walk in the smaller restriction would connect the original sets",
			By(endpoints, noWalk, restrictedEdges, closure.Monotone.At(smallerRelation, largerRelation, x, y)))
	}),
})}
