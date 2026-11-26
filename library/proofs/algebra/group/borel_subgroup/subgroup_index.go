// subgroup_index.go — an open subgroup of a Polish group has countably many cosets.

package borel_subgroup

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/countability"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// OpenSubgroupCountableIndex — an open subgroup of a Polish group has
// countably many cosets: each coset is a translate of the subgroup, open
// and not empty, so a countable dense set D meets it, and every coset is
// the coset of a point of D.
var OpenSubgroupCountableIndex = openSubgroupCountableIndexThm{family.Add(registry.ProofEntry{
	Name: "OpenSubgroupCountableIndex",
	Key:  "prop_1a1c21cc78059fe6",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀T:set(set(A)). ∀N:set(A).",
		Hypotheses: []string{
			"polish_abelian_group(G, T)",
			"subgroup(G, N)",
			"N ∈ T",
		},
		Conclusion: "countable(left_cosets(G.mul, G.carrier, N))",
	}, func(
		a *Argument,
		G *Expr[GroupOps[A]],
		T *Expr[Set[Set[A]]],
		N *Expr[Set[A]],
		polish, subgroup, open Fact,
	) {
		parts := a.Conjuncts(
			a.Unfolded(polish, polish_group.PolishAbelianGroupDef),
			"G is an abelian group on its carrier",
			"T is a Polish space",
			"the points of T are the carrier",
			"multiplication is continuous",
			"inversion is continuous")
		groupG := abelian_group.GroupOn.Read(parts[0])
		space := a.Conjuncts(
			a.Unfolded(parts[1], polish_space.PolishSpaceDef),
			"T is a topology",
			"T is separable",
			"T is the topology of a complete metric on its carrier")
		_, separable := a.UnpackAs[Set[A]](a.Unfolded(space[1], countability.SeparableSpaceDef), "D")
		aboutD := a.Conjuncts(
			separable,
			"D is countable",
			"D lies in the space",
			"D is dense")
		countableD, inSpaceD, denseD := aboutD[0], aboutD[1], aboutD[2]
		represented := a.Have(
			"every coset is the coset of a point of D",
			"left_cosets(G.mul, G.carrier, N) ⊆ image(coset_map(G.mul, N), D)",
			Derive(func(b *Argument) {
				b.Do(Simp(Fwd(set_basic.SubsetDef)))
				b.FixAs[Set[A]]("s")
				sIn := b.Assume()
				g, sIs := b.ObtainAs[A](
					"s is the coset of a point g of the group",
					"∃g:A. s = left_coset(G.mul, g, N) ∧ g ∈ G.carrier",
					By(sIn, subgroup, group.SubgroupSubset, quotient_group.InLeftCosets.Read(groupG)))
				rep := b.Conjuncts(
					sIs,
					"s is the coset of g",
					"g is a point of the group")
				gm := b.MemberOf[on.Any](g, rep[1])
				cosetOpen := b.Have(
					"the coset of g is open, a translate of the open subgroup",
					"left_coset(G.mul, g, N) ∈ T",
					By(polish, rep[1], open, polish_group.LeftTranslateOpen))
				meets := b.Have(
					"the coset of g is open and holds g, so the dense set D meets it",
					"¬(left_coset(G.mul, g, N) ∩ D = ∅)",
					By(
						cosetOpen,
						inSpaceD,
						denseD,
						subgroup,
						group.InOwnLeftCosetOn.Read(groupG).At(gm, N),
						set_basic.NotInEmpty,
						topological_space.DenseMeetsOpen.Read(space[0])))
				d, dIn := b.ObtainAs[A](
					"a point d of D in the coset of g",
					"∃d:A. d ∈ left_coset(G.mul, g, N) ∧ d ∈ D",
					By(meets, set_basic.MemberNotEmpty, set_basic.InInter))
				placed := b.Conjuncts(
					dIn,
					"d lies in the coset of g",
					"d is a point of D")
				dInCoset, dInD := placed[0], placed[1]
				same := b.Have(
					"so d, a point of the group with g⁻¹d in N, has the coset of g",
					"left_coset(G.mul, g, N) = left_coset(G.mul, d, N)",
					By(
						dInCoset,
						rep[1],
						subgroup,
						group.SubgroupSubset.At(G, N),
						group.CosetClosedOn.Read(groupG).At(N, gm, d),
						group.InLeftCosetOn.Read(groupG).AsFact().At(g, d, N),
						group.LeftCosetEqOn.Read(groupG).AsFact().At(g, d, N)))
				b.Show(
					"s is the coset of d, a point of D",
					By(rep[0], same, dInD, set_basic.InImage, group.CosetMapDef))
			}))
		a.Show(
			"so the cosets are countably many, as the image of the countable set D is",
			By(countableD, represented, cardinal.CountableImage, cardinal.CountableSubset))
	}),
	Reading: "Separability of the Polish topology is the hypothesis at work; completeness is not used.",
})}
