// frontier.go — the limit points and the frontier of a set. A limit point
// of s is a point of the space every open neighbourhood of which holds a
// point of s other than itself; the closure of a set is the set with its
// limit points, so a set is closed exactly when it holds them. The
// frontier of s is its closure less its interior: the points of the space
// every open neighbourhood of which meets both s and its complement. It is
// closed, it is the frontier of the complement too, and it is empty exactly
// for the sets both open and closed.

package topological_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Limit points
// ---------------------------------------------------------------------------

// DerivedMono — a larger set has more limit points: the point of s other
// than x found in each open neighbourhood of a limit point x is a point
// of t. No axiom enters.
var DerivedMono = derivedMonoThm{family.Add(registry.ProofEntry{
	Name: "DerivedMono",
	Key:  "prop_d933582d89225143",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s t:set(A).",
		Hypotheses: []string{
			"s ⊆ t",
		},
		Conclusion: "derived_set(T, s) ⊆ derived_set(T, t)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s, t *Expr[Set[A]], inside Fact) {
			a.Show(
				"each neighbourhood's point of s other than x is a point of t",
				Unfold(DerivedSetDef),
				BySets(inside))
		}),
})}

// ClosureDerived — the closure of a subset of the space is the set with
// its limit points. Read at a point through ClosurePointwise: a point of
// the closure outside s has each open neighbourhood meeting s, at a point
// other than itself, so it is a limit point. Conversely a point of s lies
// in the closure, which holds s (SubsetClosure), and a limit point of s
// outside s lies in the space with each open neighbourhood meeting s, so
// in the closure by the same pointwise criterion.
var ClosureDerived = closureDerivedThm{family.Add(registry.ProofEntry{
	Name: "ClosureDerived",
	Key:  "prop_1810ddd5e471b81",
	Build: IsTopology.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ ⋃T",
		},
		Conclusion: "closure(s) = s ∪ derived_set(s)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology IsTopologyFact[on.T],
			s *Expr[Set[A]],
			inSpace Fact,
		) {
			// The equation point by point.
			a.Do(Simp(Fwd(set_basic.Extension)))
			x := a.FixAs[A]("x")
			a.Iff()

			a.Forward(
				"a point of the closure lies in s, or else each of its "+
					"neighbourhoods meets s at a point other than itself",
				func(b *Argument, inClosure Fact) {
					near := b.Have(
						"x lies in the space, and every open set holding x meets s",
						"x ∈ ⋃T ∧ (∀u:set(A). u ∈ T ∧ x ∈ u ⇒ ¬(u ∩ s = ∅))",
						By(ClosurePointwise.Read(topology).At(s, x), inSpace, inClosure))
					parts := b.Conjuncts(
						near,
						"x lies in the space",
						"every open set holding x meets s")
					b.Cases(b.Term("x ∈ s"))
					b.When(
						"a point of s lies in s",
						func(c *Argument, xIn Fact) {
							c.Show(
								"so x lies in s ∪ derived_set(s)",
								BySets(xIn))
						})
					b.Otherwise(
						"a point of the closure outside s is a limit point of s",
						func(c *Argument, xOut Fact) {
							others := c.Have(
								"x is not in s, so each open set holding x meets s at a point other than x",
								"∀u:set(A). u ∈ T ∧ x ∈ u ⇒ ∃y:A. y ≠ x ∧ y ∈ s ∧ y ∈ u",
								BySets(parts[1], xOut))
							limit := c.Have(
								"so x, a point of the space, is a limit point of s",
								"x ∈ derived_set(s)",
								Unfold(DerivedSetDef),
								By(parts[0], others))
							c.Show(
								"so x lies in s ∪ derived_set(s)",
								BySets(limit))
						})
				})

			a.Backward(
				"a point of s lies in the closure, which holds s, and a limit point of "+
					"s outside s lies in the space with every open neighbourhood meeting s",
				func(b *Argument, inEither Fact) {
					b.Cases(b.Term("x ∈ s"))
					b.When(
						"a point of s lies in the closure of s",
						func(c *Argument, xIn Fact) {
							c.Show(
								"s lies in its closure",
								BySets(SubsetClosure.At(T, s), xIn))
						})
					b.Otherwise(
						"a point of s ∪ derived_set(s) outside s is a limit point of s",
						func(c *Argument, xOut Fact) {
							limit := c.Have(
								"x is a limit point of s",
								"x ∈ derived_set(s)",
								BySets(inEither, xOut))
							parts := c.Conjuncts(
								c.Unfolded(limit, DerivedSetDef),
								"x lies in the space",
								"each open set holding x holds a point of s other than x")
							meets := c.Have(
								"so every open set holding x meets s",
								"∀u:set(A). u ∈ T ∧ x ∈ u ⇒ ¬(u ∩ s = ∅)",
								BySets(parts[1]))
							c.Show(
								"a point of the space whose every open neighbourhood meets s lies in the closure of s",
								By(ClosurePointwise.Read(topology).At(s, x), inSpace, parts[0], meets))
						})
				})
		}),
})}

// ---------------------------------------------------------------------------
// The frontier
// ---------------------------------------------------------------------------

// FrontierClosures — the frontier of a subset of the space is the meet
// of its closure and the closure of its complement: the frontier is the
// closure less the interior, the interior is the complement in the space
// of the closure of the complement, and the closure lies in the space, so
// removing that complement from it keeps exactly its meet with the
// closure of the complement.
var FrontierClosures = frontierClosuresThm{family.Add(registry.ProofEntry{
	Name: "FrontierClosures",
	Key:  "prop_130246a77c041f55",
	Build: IsTopology.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ ⋃T",
		},
		Conclusion: "frontier(s) = closure(s) ∩ closure(⋃T ∖ s)",
	},
		func(a *Argument, topology IsTopologyFact[on.T], s *Expr[Set[A]], inSpace Fact) {
			a.Show(
				"the closure less the interior, which is the space less the "+
					"closure of the complement, the closure lying in the space",
				Unfold(FrontierDef),
				BySets(
					InteriorClosureComplement.Read(topology).At(s),
					ClosureSubsetSpace.Read(topology).At(s),
					inSpace))
		}),
})}

// FrontierClosed — the frontier of a subset of the space is closed: it
// is the meet of the closure of s and the closure of its complement in
// the space, each a closure of a subset of the space and so closed, and
// two closed sets meet in a closed set.
var FrontierClosed = frontierClosedThm{family.Add(registry.ProofEntry{
	Name: "FrontierClosed",
	Key:  "prop_93e0fb087cee9f17",
	Build: IsTopology.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ ⋃T",
		},
		Conclusion: "closed_in(frontier(s))",
	},
		func(a *Argument, topology IsTopologyFact[on.T], s *Expr[Set[A]], inSpace Fact) {
			space := a.TermAs[Set[A]]("⋃T")
			complement := a.TermAs[Set[A]]("⋃T ∖ s")
			// ↦ closed_in(closure(s) ∩ closure(⋃T ∖ s))
			a.Do(GroupPremises(inSpace, FrontierClosures.Read(topology).At(s)).Rw())
			a.Show(
				"the closures of s and of its complement, both "+
					"subsets of the space, are closed, and so is their meet",
				By(
					InterClosed.Read(topology),
					ClosureClosed.Read(topology).At(s),
					inSpace,
					ClosureClosed.Read(topology).At(complement),
					set_order.SubsetDiff.At(space, s)))
		}),
})}
