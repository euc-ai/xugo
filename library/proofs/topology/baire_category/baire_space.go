// baire_space.go — a Polish space is a Baire space: in the topology of a
// complete metric, no non-empty open set is meager.

package baire_category

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PolishBaire — a Polish space is a Baire space. Its open sets are those
// of a complete metric d on its carrier. A meager open set u lies in the
// union of closed nowhere dense sets G(n) (MeagerClosedCover), whose
// complements are open and dense (ClosedNowhereDenseComplement); they are
// so for d as well, and the Baire category theorem for d makes their
// intersection dense. The intersection misses u, and an open set missing
// a dense set is empty (DenseMeetsOpen).
var PolishBaire = polishBaireThm{family.Add(registry.ProofEntry{
	Name: "PolishBaire",
	Key:  "prop_84c2dfd2daab3121",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)).",
		Hypotheses: []string{
			"polish_space(T)",
		},
		Conclusion: "baire_space(T)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], polish Fact) {
			given := a.Conjuncts(
				a.Unfolded(polish, polish_space.PolishSpaceDef),
				"T is a topology",
				"T is separable",
				"T is the topology of a complete metric on its carrier")
			topology := given[0]
			d, metrized := a.UnpackAs[Fun2[A, A, Real]](given[2])
			metric := a.Conjuncts(
				metrized,
				"d is a metric on the carrier",
				"d is complete",
				"the open sets of d are those of T")

			noMeagerOpen := a.Have(
				"every meager open set is empty",
				"∀u:set(A). u ∈ T ∧ meager(T, u) ⇒ u = ∅",
				Derive(func(b *Argument) {
					u := b.FixAs[Set[A]]()
					assumed := b.Conjuncts(
						b.Assume(),
						"u is open",
						"u is meager")
					_, covered := b.ObtainAs[Fun[Nat, Set[A]]](
						"u lies in the union of closed nowhere dense sets G(n)",
						"∃G:(num → set(A)). (∀n:num. closed_in(T, G(n)) ∧ nowhere_dense(T, G(n))) ∧ u ⊆ ⋃image(G, 𝕌)",
						By(assumed[1], MeagerClosedCover.Read(topology).At(u)))
					cover := b.Conjuncts(
						covered,
						"each G(n) is closed and nowhere dense",
						"u lies in their union")
					complements := b.Have(
						"the complement of each G(n) is open and dense",
						"∀n:num. ⋃T ∖ G(n) ∈ T ∧ closure(T, ⋃T ∖ G(n)) = ⋃T",
						By(cover[0], ClosedNowhereDenseComplement.Read(topology)))
					space := b.TermAs[Set[A]]("⋃T")
					g := b.TermAs[Fun[Nat, Set[A]]]("λn:num. ⋃T ∖ G(n)")
					baire := b.Simplified(complete_metric.BaireCategory.At(space, d, g), Fwd(metric[2]))
					meet, meetDef := b.LetAs[Set[A]]("W", "⋂image(λn:num. ⋃T ∖ G(n), 𝕌)")
					dense := b.Have(
						"d is a complete metric, so the open dense complements meet in a dense set W",
						"closure(T, W) = ⋃T",
						By(baire, metric[0], metric[1], complements))
					disjoint := b.Have(
						"u lies in the union of the G(n), so it misses W, the intersection of their complements",
						"u ∩ W = ∅",
						Simp(Fwd(meetDef), Fwd(set_image.IntersImage)),
						BySets(cover[1]))
					b.Show(
						"u is open and misses the dense W, which lies in the space inside its closure, so u is empty",
						By(
							assumed[0],
							disjoint,
							dense,
							topological_space.DenseMeetsOpen.Read(topology).At(meet),
							topological_space.SubsetClosure.At(T, meet)))
				}))

			a.Show(
				"T is a topology whose meager open sets are empty",
				By(topology, noMeagerOpen, BaireSpaceDef.At(T)))
		}),
	Reading: "Completeness is of some compatible metric, which is all " +
		"BaireCategory asks. The empty Polish space is a Baire space trivially.",
})}
