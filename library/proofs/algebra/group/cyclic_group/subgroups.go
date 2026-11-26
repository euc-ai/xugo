// subgroups.go — the subgroups of a cyclic group, and the images of one.

package cyclic_group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// generator opens an argument about a cyclic group G: it takes a generator
// g of G, returned as a member of G beside the equation
// G.carrier = cyclic_subgroup(G, g).
func generator(a *Argument, cyclic Fact) (*Member[A, on.G], Fact) {
	g, generates := a.ObtainAs[A](
		"let g generate G",
		"∃g:A. g ∈ G.carrier ∧ G.carrier = cyclic_subgroup(G, g)",
		By(cyclic, CyclicGroupDef))
	parts := a.Conjuncts(
		generates,
		"g lies in G",
		"and G is its powers and their inverses")
	return a.MemberOf[on.G](g, parts[0]), parts[1]
}

// SubgroupOfCyclic — every subgroup H of a cyclic group is cyclic. Let g
// generate G: the powers of g lying in H are those at the multiples of
// one exponent d (group.PowInSubgroupIffDivides), and H is the subgroup g ^ d
// generates in it. A member of H is g ^ n or the inverse of g ^ n, so g ^ n
// lies in H, n is a multiple d · k, and g ^ n is (g ^ d) ^ k; and g ^ d, a
// member of the group H, generates a subgroup of it.
var SubgroupOfCyclic = subgroupOfCyclicThm{family.Add(registry.ProofEntry{
	Name: "SubgroupOfCyclic",
	Key:  "prop_7ec12fc7a933d759",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀H:set(A).",
		Hypotheses: []string{
			"cyclic_group(G)",
			"subgroup(G, H)",
		},
		Conclusion: "cyclic_group(restrict_group(G, H))",
	},
		func(a *Argument, grp group.GroupFact[on.G], H *Expr[Set[A]], cyclic, subgroup Fact) {
			gm, generates := generator(a, cyclic)
			d, exponents := a.UnpackAs[Nat](
				GroupPremises(subgroup, group.PowInSubgroupIffDivides.Read(grp).At(gm, H)),
				"d")
			onH := a.Have(
				"H is a group under the operations of G",
				"group_on(restrict_group(G, H))",
				By(grp, subgroup, group.SubgroupGroupOn))
			dIn := a.Have(
				"g ^ d lies in H, d dividing itself",
				"monoid_pow(G.mul, G.one, g, d) ∈ H",
				By(exponents.At(d), nat_divides.DividesRefl))
			dm := a.MemberOf[on.Any](a.TermAs[A]("monoid_pow(G.mul, G.one, g, d)"), dIn)
			generated := a.Have(
				"g ^ d, a member of the group H, generates a subgroup of it",
				"cyclic_subgroup(restrict_group(G, H), monoid_pow(G.mul, G.one, g, d)) ⊆ H",
				By(CyclicSubgroupSubgroup.Read(onH).At(dm), group.SubgroupSubset))
			covered := a.Have(
				"every member of H is a power of g ^ d or the inverse of one",
				"∀y:A. y ∈ H ⇒ y ∈ cyclic_subgroup(restrict_group(G, H), monoid_pow(G.mul, G.one, g, d))",
				Derive(func(b *Argument) {
					b.FixAs[A]("y")
					yIn := b.Assume()
					yInG := b.Have(
						"y lies in G, so it is a power of g or the inverse of one",
						"y ∈ cyclic_subgroup(G, g)",
						By(generates, yIn, subgroup, group.SubgroupSubset, set_basic.SubsetDef))
					n, form := b.UnpackAs[Nat](b.Unfolded(yInG, CyclicSubgroupDef), "n")
					powerIn := b.Have(
						"either way g ^ n lies in H, which is closed under inverses",
						"monoid_pow(G.mul, G.one, g, n) ∈ H",
						By(form, yIn, subgroup, group.SubgroupInvIffOn.Read(grp).At(H, group.PowIn.Read(grp).At(gm, n))))
					k, multiple := b.ObtainAs[Nat](
						"so d divides n: n is d · k",
						"∃k:num. n = d * k",
						By(exponents.At(n), powerIn, nat_divides.DividesFactor))
					b.Show(
						"and g ^ n is (g ^ d) ^ k",
						Unfold(CyclicSubgroupDef),
						By(form, multiple, group.PowPow.Read(grp).At(gm, d, k)))
				}))
			whole := a.Have(
				"so H is the subgroup g ^ d generates in it",
				"H = cyclic_subgroup(restrict_group(G, H), monoid_pow(G.mul, G.one, g, d))",
				BySets(generated, covered))
			a.Show(
				"so g ^ d generates the group H",
				By(onH, dIn, whole, CyclicGroupDef))
		}),
})}

// MapCyclicSubgroup — a homomorphism carries the subgroup x generates onto
// the subgroup f(x) generates: it takes x ^ n to f(x) ^ n
// (group_homomorphism.MapPow), and the inverse of x ^ n to the inverse of
// f(x) ^ n.
var MapCyclicSubgroup = mapCyclicSubgroupThm{family.Add(registry.ProofEntry{
	Name: "MapCyclicSubgroup",
	Key:  "prop_3484660d7c92cc10",
	Build: group_homomorphism.GroupHomomorphism.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "image(f, cyclic_subgroup(G, x)) = cyclic_subgroup(H, f(x))",
	},
		func(a *Argument, hom group_homomorphism.GroupHomomorphismFact[on.G, on.H], x *Member[A, on.G]) {
			source := group_homomorphism.Source.Read(hom)
			inverses := a.Have(
				"f carries the inverse of each power of x to the inverse of the power of f(x)",
				"∀n:num. f(G.inv(monoid_pow(G.mul, G.one, x, n))) = H.inv(monoid_pow(H.mul, H.one, f(x), n))",
				a.ForEach(func(n *Expr[Nat]) Action {
					return By(
						group_homomorphism.MapInv.Read(hom).At(group.PowIn.Read(source).At(x, n)),
						group_homomorphism.MapPow.Read(hom).At(x, n))
				}))
			a.Show(
				"both sides are the powers of f(x) and their inverses, f carrying x ^ n to f(x) ^ n",
				Unfold(CyclicSubgroupDef),
				BySets(hom, x, group_homomorphism.MapPow, inverses))
		}),
})}

// ImageOfCyclic — a homomorphism onto H carries a cyclic group to a cyclic
// group: if g generates G, H is the image of the subgroup g generates,
// which is the subgroup f(g) generates (MapCyclicSubgroup).
var ImageOfCyclic = imageOfCyclicThm{family.Add(registry.ProofEntry{
	Name: "ImageOfCyclic",
	Key:  "prop_78ddd324446cac28",
	Build: group_homomorphism.GroupHomomorphism.Law(Statement{
		Hypotheses: []string{
			"image(f, G.carrier) = H.carrier",
			"cyclic_group(G)",
		},
		Conclusion: "cyclic_group(H)",
	},
		func(a *Argument, hom group_homomorphism.GroupHomomorphismFact[on.G, on.H], onto, cyclic Fact) {
			gm, generates := generator(a, cyclic)
			whole := a.Have(
				"H is the image of the subgroup g generates, which is the subgroup f(g) generates",
				"H.carrier = cyclic_subgroup(H, f(g))",
				By(Normalized, onto, generates, MapCyclicSubgroup.Read(hom).At(gm)))
			a.Show(
				"so f(g) generates H",
				By(
					whole,
					group_homomorphism.Target.Read(hom),
					group_homomorphism.MapIn.Read(hom).At(gm),
					CyclicGroupDef))
		}),
})}
