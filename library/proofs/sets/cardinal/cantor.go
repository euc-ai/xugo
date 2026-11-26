// cantor.go — Cantor's theorem: a set is strictly smaller than the set
// of its subsets.

package cardinal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// CantorStrict — Cantor's theorem, both halves of the strict order.
// Sending each point to its singleton puts s among its subsets without
// identifying two points, so s is no larger. Were the subsets no larger
// than s, some map from s would cover them — the comparison's surjective
// reading; the diagonal argument finds a subset of s that the map
// reaches at no point of s.
var CantorStrict = cantorStrictThm{family.Add(registry.ProofEntry{
	Name: "CantorStrict",
	Key:  "prop_d44fc9e0a76b4410",
	Build: family.Theorem("∀s:set(A). card_lt(s, {t:set(A) | t ⊆ s})",
		Opening(Unfold(CardLtDef), func(a *Argument, s *Expr[Set[A]]) {
			subsets := a.TermAs[Set[Set[A]]]("{t:set(A) | t ⊆ s}")
			a.Do(SplitConj(
				Case(
					"the singletons inject s into its subsets",
					Unfold(CardLeDef),
					Unfold(functions.InjectiveOnDef),
					Derive(func(b *Argument) {
						b.Take(b.Term("λx:A. {x}"))
						b.Show(
							"{x} ⊆ s for each x ∈ s, and {x} = {y} puts x = y",
							BySets())
					})),
				Case(
					"no map from s covers its subsets — Cantor's diagonal",
					Derive(func(b *Argument) {
						subsetsNoLarger := b.SupposeNot()
						g, covers := b.ObtainAs[Fun[A, Set[A]]](
							"then some map g from s reaches every subset of s",
							"∃g:(A → set(A)). {t:set(A) | t ⊆ s} ⊆ image(g, s)",
							By(subsetsNoLarger, CardLeCover.At(subsets, s)))
						b.Show(
							"yet the diagonal argument gives a subset of s that g reaches at no point of s",
							BySets(covers, functions.Cantor.At(s, g)))
					})),
			))
		})),
})}

// CantorUniv — Cantor's theorem for a whole type: the sets of A's
// outnumber the A's. The subsets of 𝕌 are every set.
var CantorUniv = cantorUnivThm{family.Add(registry.ProofEntry{
	Name: "CantorUniv",
	Key:  "prop_968249dd0d0cb5a0",
	Build: family.Theorem("card_lt(𝕌⟨A:A⟩, 𝕌⟨A:set(A)⟩)",
		func(a *Argument) {
			univ := a.TermAs[Set[A]]("𝕌⟨A:A⟩")
			everySet := a.Have(
				"every set of A's is a subset of 𝕌",
				"{t:set(A) | t ⊆ 𝕌⟨A:A⟩} = 𝕌⟨A:set(A)⟩",
				BySets())
			a.Show(
				"Cantor's theorem at 𝕌",
				everySet.RwRev(),
				Cite(CantorStrict, univ))
		}),
})}
