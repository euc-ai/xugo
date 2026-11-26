// translates.go — a left translate of an open set of a Polish group is open.

package polish_group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// LeftTranslateOpen — in a Polish group the left translate g·u of an open
// set u by a point g of the group is open: g·u is the preimage of u under
// x ↦ g⁻¹x, which is continuous as the multiplication after the slice
// y ↦ (g⁻¹, y).
var LeftTranslateOpen = leftTranslateOpenThm{family.Add(registry.ProofEntry{
	Name: "LeftTranslateOpen",
	Key:  "prop_a9e4571d71cf848",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀T:set(set(A)). ∀g:A. ∀u:set(A).",
		Hypotheses: []string{
			"polish_abelian_group(G, T)",
			"g ∈ G.carrier",
			"u ∈ T",
		},
		Conclusion: "left_coset(G.mul, g, u) ∈ T",
		Abbrev: Abbrev{
			{Name: "slice", Text: "λy:A. (G.inv(g), y)"},
			{Name: "shift", Text: "λx:A. G.inv(g) * x"},
		},
	}, func(
		a *Argument,
		G *Expr[GroupOps[A]],
		T *Expr[Set[Set[A]]],
		g *Expr[A],
		u *Expr[Set[A]],
		polish, gIn, uOpen Fact,
	) {
		parts := a.Conjuncts(
			a.Unfolded(polish, PolishAbelianGroupDef),
			"G is an abelian group on its carrier",
			"T is a Polish space",
			"the points of T are the carrier",
			"multiplication is continuous",
			"inversion is continuous")
		groupG := abelian_group.GroupOn.Read(parts[0])
		points, mulContinuous := parts[2], parts[3]
		gm := a.MemberOf[on.Any](g, gIn)
		sliceMap := a.TermAs[Fun[A, Prod[A, A]]]("«slice»")
		multiply := a.TermAs[Fun[Prod[A, A], A]]("λp:prod(A, A). fst(p) * snd(p)")
		slice := a.Have(
			"the slice y ↦ (g⁻¹, y) into the square is continuous, g⁻¹ being a point of the space",
			"continuous_map(T, product_topology(T, T), «slice»)",
			By(
				parts[1],
				polish_space.PolishSpaceDef,
				points,
				product_topology.SliceRightContinuous.At(T, T, a.TermAs[A]("G.inv(g)")),
				group.InvIn.Read(groupG).At(gm)))
		translation := a.Have(
			"so x ↦ g⁻¹x is continuous, the multiplication after the slice",
			"continuous_map(T, T, «shift»)",
			By(
				mulContinuous,
				continuous.Compose.Read(slice).At(T, multiply),
				functions.ComposeApply.At(multiply, sliceMap),
				pairs.Fst,
				pairs.Snd))
		inside := a.Have(
			"u lies in the carrier",
			"u ⊆ G.carrier",
			By(Normalized, points, uOpen, set_order.MemberSubsetUnions.At(T, u)))
		preimage := a.Have(
			"g·u is the preimage of u under x ↦ g⁻¹x",
			"left_coset(G.mul, g, u) = preimage_on(⋃T, «shift», u)",
			Derive(func(b *Argument) {
				b.Do(Simp(Fwd(set_basic.Extension), Fwd(functions.PreimageOnDef)))
				x := b.FixAs[A]("x")
				b.Iff()
				b.Forward(
					"a point of g·u lies in the carrier, and g⁻¹ carries it into u",
					func(c *Argument, xIn Fact) {
						c.Show(
							"x is a point of the space with g⁻¹x in u",
							By(
								points,
								xIn,
								inside,
								group.InLeftCosetOn.Read(groupG).AsFact().At(g, x, u),
								group.LeftCosetIn.Read(groupG).At(gm, u),
								set_basic.SubsetDef))
					})
				b.Backward(
					"a point of the carrier that g⁻¹ carries into u lies in g·u",
					func(c *Argument, xIn Fact) {
						c.Show(
							"x lies in g·u",
							By(points, xIn, inside, gIn, group.InLeftCosetOn.Read(groupG).AsFact().At(g, x, u)))
					})
			}))
		a.Show(
			"so g·u is open, the preimage of an open set",
			By(preimage, uOpen, translation, continuous.PreimageOpen))
	}),
	Reading: "Only the group laws, T being a topology, ⋃T = G.carrier " +
		"and the joint continuity of multiplication are read: commutativity, " +
		"continuity of inversion, separability and completeness do not enter.",
})}
