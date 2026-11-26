package dag

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/closure"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// AncestorsClosed says that the ancestors of a set contain the set and
// are ancestral: every parent of an ancestor is an ancestor.
var AncestorsClosed = ancestorsClosedThm{family.Add(registry.ProofEntry{
	Name: "AncestorsClosed",
	Key:  "prop_658fa0251bdb2bd4",
	Build: family.Theorem(Statement{
		Binders:    "∀E:(A → A → bool). ∀X:set(A).",
		Conclusion: "X ⊆ dag_ancestors(E, X) ∧ dag_ancestral(E, dag_ancestors(E, X))",
	}, func(a *Argument, E *Arrow2[A, A, Bool], X *Expr[Set[A]]) {
		a.Do(SplitConj(
			Case(
				"each point of X reaches itself",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					b.FixAs[A]()
					inX := b.Assume()
					b.Show(
						"the empty walk from x to itself witnesses membership",
						Unfold(AncestorsDef),
						By(inX, closure.ReflexiveTransitiveClosureDef))
				})),
			Case(
				"a parent of an ancestor reaches the same point of X",
				Unfold(AncestralDef),
				Derive(func(b *Argument) {
					u := b.FixAs[A]()
					v := b.FixAs[A]()
					parts := b.Conjuncts(
						b.Assume(),
						"the edge from u to v",
						"v is an ancestor")
					x, witness := b.UnpackAs[A](b.Unfolded(parts[1], AncestorsDef))
					edgeWalk := b.Have(
						"the edge is a walk from u to v",
						"reflexive_transitive_closure(E, u, v)",
						By(parts[0], closure.TransitiveClosureRules.At(E), closure.ReflexiveTransitiveClosureDef))
					endpoint := b.Conjuncts(
						witness,
						"x belongs to X",
						"v reaches x")
					b.Show(
						"prepending the edge gives a walk from u to x",
						Unfold(AncestorsDef),
						By(endpoint[0], edgeWalk, endpoint[1], closure.ReflexiveTransitiveClosureTransitive.At(E, u, v, x)))
				})),
		))
	}),
})}

// AncestorsUpperBound says that an ancestral set containing X contains
// every ancestor of X.
var AncestorsUpperBound = ancestorsUpperBoundThm{family.Add(registry.ProofEntry{
	Name: "AncestorsUpperBound",
	Key:  "prop_d483fc5d982fdd62",
	Build: family.Theorem(Statement{
		Binders:    "∀E:(A → A → bool). ∀X U:set(A).",
		Hypotheses: []string{"X ⊆ U", "dag_ancestral(E, U)"},
		Conclusion: "dag_ancestors(E, X) ⊆ U",
	}, func(a *Argument, E *Arrow2[A, A, Bool], X, U *Expr[Set[A]], included, ancestral Fact) {
		parentsInU := a.Unfolded(ancestral, AncestralDef)
		outsideSteps := a.Have(
			"an edge from outside U stays outside U",
			"∀s t:A. E(s, t) ∧ s ∉ U ⇒ t ∉ U",
			Derive(func(b *Argument) {
				s := b.FixAs[A]()
				t := b.FixAs[A]()
				edgeFromOutside := b.Assume()
				b.Show(
					"an edge into U would put its parent in U",
					By(edgeFromOutside, parentsInU.At(s, t)))
			}))
		includedPoints := a.Unfolded(included, set_basic.SubsetDef)
		a.Do(Simp(Fwd(set_basic.SubsetDef)))
		u := a.FixAs[A]("u")
		ancestor := a.Assume()
		x, witness := a.UnpackAs[A](a.Unfolded(ancestor, AncestorsDef))
		outside := a.SupposeNot()
		complement := a.TermAs[Set[A]]("λw:A. w ∉ U")
		a.Show(
			"the walk would end outside U, contradicting that its endpoint belongs to X",
			By(
				outside,
				outsideSteps,
				witness,
				includedPoints.At(x),
				closure.ReflexiveTransitiveClosurePreserves.At(E, complement, u, x)))
	}),
})}

// AncestorsMonotone says that enlarging the edge relation and the target
// set enlarges the set of ancestors.
var AncestorsMonotone = ancestorsMonotoneThm{family.Add(registry.ProofEntry{
	Name: "AncestorsMonotone",
	Key:  "prop_a6934bd488ff3ac9",
	Build: family.Theorem(Statement{
		Binders:    "∀E F:(A → A → bool). ∀X Y:set(A).",
		Hypotheses: []string{"∀u v:A. E(u, v) ⇒ F(u, v)", "X ⊆ Y"},
		Conclusion: "dag_ancestors(E, X) ⊆ dag_ancestors(F, Y)",
	}, func(a *Argument, E, F *Arrow2[A, A, Bool], X, Y *Expr[Set[A]], moreEdges, included Fact) {
		includedPoints := a.Unfolded(included, set_basic.SubsetDef)
		a.Do(Simp(Fwd(set_basic.SubsetDef)))
		u := a.FixAs[A]("u")
		ancestor := a.Assume()
		x, witness := a.UnpackAs[A](a.Unfolded(ancestor, AncestorsDef))
		a.Show(
			"the same walk uses edges of F and ends at x in Y",
			Simp(Fwd(AncestorsDef)),
			By(
				witness,
				includedPoints.At(x),
				moreEdges,
				closure.ReflexiveTransitiveClosureMonotone.At(E, F, u, x)))
	}),
})}

// AncestorsRootUnion says that vertices without parents contribute
// themselves to the ancestors of their union with W.
var AncestorsRootUnion = ancestorsRootUnionThm{family.Add(registry.ProofEntry{
	Name:    "AncestorsRootUnion",
	Reading: "The hypothesis also forbids self-loops on X; no dag_on is needed.",
	Key:     "prop_3d47e18093936d44",
	Build: family.Theorem(Statement{
		Binders:    "∀E:(A → A → bool). ∀X W:set(A).",
		Hypotheses: []string{"∀u x:A. x ∈ X ⇒ ¬E(u, x)"},
		Conclusion: "dag_ancestors(E, X ∪ W) = X ∪ dag_ancestors(E, W)",
	}, func(a *Argument, E *Arrow2[A, A, Bool], X, W *Expr[Set[A]], noParents Fact) {
		seed := a.TermAs[Set[A]]("X ∪ W")
		withRoots := a.TermAs[Set[A]]("X ∪ dag_ancestors(E, W)")
		upper := a.Have(
			"the roots and ancestors of W contain all ancestors of the union",
			"dag_ancestors(E, X ∪ W) ⊆ X ∪ dag_ancestors(E, W)",
			Derive(func(b *Argument) {
				ancestorsOfW := b.Conjuncts(
					AncestorsClosed.At(E, W),
					"W is contained in its ancestors",
					"the ancestors of W are ancestral")
				parentsOfAncestors := b.Unfolded(ancestorsOfW[1], AncestralDef)
				containsSeed := b.Have(
					"adjoining X preserves the inclusion of W",
					"X ∪ W ⊆ X ∪ dag_ancestors(E, W)",
					BySets(ancestorsOfW[0]))
				ancestral := b.Have(
					"adjoining vertices without parents keeps the set ancestral",
					"dag_ancestral(E, X ∪ dag_ancestors(E, W))",
					Unfold(AncestralDef),
					Derive(func(c *Argument) {
						u := c.FixAs[A]()
						v := c.FixAs[A]()
						edge := c.Assume()
						c.Show(
							"the edge ends at an ancestor of W, whose parent is also an ancestor of W",
							BySets(edge, noParents.At(u, v), parentsOfAncestors.At(u, v)))
					}))
				b.Show(
					"every ancestor lies in an ancestral set containing the seed",
					By(containsSeed, ancestral, AncestorsUpperBound.At(E, seed, withRoots)))
			}))
		lower := a.Have(
			"the ancestors of the union contain X and all ancestors of W",
			"X ∪ dag_ancestors(E, W) ⊆ dag_ancestors(E, X ∪ W)",
			Derive(func(b *Argument) {
				ancestorsOfSeed := b.Conjuncts(
					AncestorsClosed.At(E, seed),
					"the union is contained in its ancestors",
					"the ancestors of the union are ancestral")
				containsW := b.Have(
					"W is contained in the ancestors of the union",
					"W ⊆ dag_ancestors(E, X ∪ W)",
					BySets(ancestorsOfSeed[0]))
				containsAncestorsOfW := b.Have(
					"the ancestral set containing W contains the ancestors of W",
					"dag_ancestors(E, W) ⊆ dag_ancestors(E, X ∪ W)",
					By(
						containsW,
						ancestorsOfSeed[1],
						AncestorsUpperBound.At(E, W, b.TermAs[Set[A]]("dag_ancestors(E, X ∪ W)"))))
				b.Show(
					"both X and the ancestors of W lie in the ancestors of the union",
					BySets(ancestorsOfSeed[0], containsAncestorsOfW))
			}))
		a.Show(
			"the two inclusions give equality",
			By(upper, lower, set_order.SubsetAntisym))
	}),
})}

// DescendantsAncestorsDual reads a walk from X to Z by its two endpoints.
var DescendantsAncestorsDual = descendantsAncestorsDualThm{family.Add(registry.ProofEntry{
	Name: "DescendantsAncestorsDual",
	Key:  "prop_67a85bbf655f5db",
	Build: family.Theorem(Statement{
		Binders:    "∀E:(A → A → bool). ∀X Z:set(A).",
		Conclusion: "dag_descendants(E, X) ∩ Z = ∅ ⇔ dag_ancestors(E, Z) ∩ X = ∅",
	}, func(a *Argument, E *Arrow2[A, A, Bool], X, Z *Expr[Set[A]]) {
		a.Show(
			"each intersection is empty exactly when no point of X reaches a point of Z",
			Unfold(DescendantsDef),
			Unfold(AncestorsDef),
			BySets())
	}),
})}
