// fibre_bound.go — a set counted through a map into a finite set with bounded
// fibres.

package nat_sum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// CardFibresBound — a set mapped into a finite set T with finite fibres of at
// most n points is finite, with at most card(T) · n points: finite induction on
// the values, a new value adding its fibre.
var CardFibresBound = cardFibresBoundThm{family.Add(registry.ProofEntry{
	Name: "CardFibresBound",
	Key:  "prop_2a06602ce9fa373",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀T:set(B). ∀f:(A → B). ∀n:num.",
		Hypotheses: []string{
			"finite(T)",
			"∀x:A. x ∈ s ⇒ f(x) ∈ T",
			"∀y:B. y ∈ T ⇒ finite(«fibre»(y)) ∧ card(«fibre»(y)) ≤ n",
		},
		Conclusion: "finite(s) ∧ card(s) ≤ card(T) * n",
		Abbrev: Abbrev{
			{Name: "fibre", Text: "λy:B. {x:A | x ∈ s ∧ f(x) = y}"},
			{Name: "part", Text: "λu:set(B). {x:A | x ∈ s ∧ f(x) ∈ u}"},
		},
	},
		func(
			a *Argument,
			s *Expr[Set[A]],
			T *Expr[Set[B]],
			f *Arrow[A, B],
			n *Expr[Nat],
			finiteT, into, fibres Fact,
		) {
			induction := a.Have(
				"finite induction on the values counts the points over T",
				"finite(«part»(T)) ∧ card(«part»(T)) ≤ card(T) * n",
				ByInduction(finite_set.FiniteInductFreshOn, finiteT, fibres,
					Case(
						"no value, no point",
						Derive(func(b *Argument) {
							noPoint := b.Have(
								"nothing lies over the empty set",
								"«part»(∅) = ∅",
								BySets())
							b.Do(noPoint.Rw())
							b.Do(SplitConj(
								Case(
									"the empty set is finite",
									By(finite_set.FiniteRules)),
								Case(
									"and has no point",
									ByArith(cardinality.CardClauses))))
						})),
					Case(
						"a new value adds its fibre",
						Derive(func(b *Argument) {
							b.FixAs[B]("y")
							b.FixAs[Set[B]]("u")
							carried := b.Conjuncts(
								b.Assume(),
								"the points over u are finite",
								"they number at most card(u) · n",
								"y is new to u",
								"u is finite",
								"the fibre over y is finite",
								"it has at most n points",
								"every fibre over u is bounded")
							partFinite, partBound, fresh, finiteU, fibreFinite, fibreBound :=
								carried[0], carried[1], carried[2], carried[3], carried[4], carried[5]
							grown := b.Have(
								"the points over insert(y, u) are the fibre over y beside the points over u",
								"«part»(insert(y, u)) = «fibre»(y) ∪ «part»(u)",
								BySets())
							fibreSet := b.TermAs[Set[A]]("«fibre»(y)")
							partSet := b.TermAs[Set[A]]("«part»(u)")
							b.Do(grown.Rw())
							bound := b.Have(
								"so they number at most their sum",
								"card(«fibre»(y) ∪ «part»(u)) ≤ card(«fibre»(y)) + card(«part»(u))",
								By(fibreFinite, partFinite, cardinality.CardUnionLe.At(fibreSet, partSet)))
							larger := b.Have(
								"and the new value counts once more",
								"card(insert(y, u)) = suc(card(u))",
								By(finiteU, fresh, cardinality.CardClauses))
							b.Do(SplitConj(
								Case(
									"a union of two finite sets is finite",
									By(fibreFinite, partFinite, finite_set.FiniteUnion.At(fibreSet, partSet))),
								Case(
									"and the bound grows by n",
									ByArith(bound, larger, fibreBound, partBound))))
						}))))
			whole := a.Have(
				"every point of s lies over T",
				"«part»(T) = s",
				BySets(into))
			a.Show(
				"so s is counted",
				By(induction, whole))
		}),
})}
