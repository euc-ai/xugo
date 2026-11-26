// finite_group.go — the order of a finite group, Lagrange’s theorem, and
// p-groups and p-subgroups.

package finite_group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The order of a finite group
// ---------------------------------------------------------------------------

// CarrierCardPositive — a finite group has positive order: its carrier
// holds the identity, so it counts one more than what is left once the
// identity goes.
var CarrierCardPositive = carrierCardPositiveThm{family.Add(registry.ProofEntry{
	Name: "CarrierCardPositive",
	Key:  "prop_40a08802336656d",
	Build: group.GroupOn.Law(Statement{
		Hypotheses: []string{
			"finite(G.carrier)",
		},
		Conclusion: "0 < card(G.carrier)",
	},
		func(a *Argument, grp group.GroupFact[on.G], finite Fact) {
			a.Show(
				"the carrier holds G.one, so it counts one more than the rest of it",
				ByArith(
					finite,
					group.OneIn.Read(grp),
					cardinality.CountsOneMore.At(a.TermAs[Set[A]]("G.carrier"), a.TermAs[A]("G.one"))))
		}),
})}

// SubgroupFinite — a subgroup of a finite group is finite: it lies in the
// carrier, and a subset of a finite set is finite. No group law is read, so
// the record need not be a group.
var SubgroupFinite = subgroupFiniteThm{family.Add(registry.ProofEntry{
	Name: "SubgroupFinite",
	Key:  "prop_ed7a7d6adbed4a00",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀h:set(A).",
		Hypotheses: []string{
			"finite(G.carrier)",
			"subgroup(G, h)",
		},
		Conclusion: "finite(h)",
	}, func(a *Argument, G *Expr[GroupOps[A]], h *Expr[Set[A]], finite, subgroup Fact) {
		a.Show(
			"h lies in the finite carrier",
			By(finite, subgroup, finite_set.FiniteSubset, group.SubgroupSubset))
	}),
})}

// ---------------------------------------------------------------------------
// Lagrange's theorem
// ---------------------------------------------------------------------------

// LeftCosetSizeOn — a left coset of a subset of the carrier by a point
// of the carrier is as large as the subset it moves: x·h is the image of
// h under multiplication by x on the left, which separates the points of
// the carrier (group.LeftCancelOn), and an injective image keeps its size.
var LeftCosetSizeOn = leftCosetSizeOnThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetSizeOn",
	Key:  "prop_ae0ab963a1ba090f",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A. ∀h:set(A). ∀n:num.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"h ⊆ G.carrier",
			"has_size(h, n)",
		},
		Conclusion: "has_size(left_coset(x, h), n)",
	},
		func(
			a *Argument,
			grp group.GroupFact[on.G],
			x *Expr[A],
			h *Expr[Set[A]],
			n *Expr[Nat],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"x lies in G.carrier",
				"h lies in G.carrier",
				"h has n points")
			carrier := a.TermAs[Set[A]]("G.carrier")
			separates := a.Have(
				"multiplying by x on the left separates the points of h, which lie in G.carrier, where x cancels",
				"injective_on(h, λy:A. x * y)",
				Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]()))),
				Derive(func(b *Argument) {
					u, v := b.FixAs[A]("u"), b.FixAs[A]("v")
					equalImages := b.Assume()
					b.Show(
						"u and v lie in G.carrier, and x * u = x * v there cancels to u = v",
						By(
							parts[0],
							parts[1],
							equalImages,
							set_basic.SubsetDef.At(h, carrier),
							group.LeftCancelOn.Read(grp).AsFact().At(x, u, v)))
				}))
			a.Show(
				"so the coset, the image of h under it, is as large as h",
				Unfold(group.LeftCosetDef),
				By(separates, parts[2], cardinality.HasSizeImageInj))
		}),
})}

// LeftCosetSize — LeftCosetSizeOn on the whole type.
var LeftCosetSize = leftCosetSizeThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetSize",
	Key:  "prop_4141c6785af2dfda",
	Build: group.GroupAtUniverse.Law(Statement{
		Binders: "∀x:A. ∀h:set(A). ∀n:num.",
		Hypotheses: []string{
			"has_size(h, n)",
		},
		Conclusion: "has_size(left_coset(x, h), n)",
	}, LeftCosetSizeOn),
})}

// LagrangeOn — Lagrange's theorem, relative form, for a group on a set:
// a finite subgroup k containing a subgroup h has card(h) elements for
// every left coset of h in k. The theorem a textbook states — the order
// of a finite group is the order of a subgroup times its index — is the
// case k = G.carrier with the carrier finite.
//
// The coset relation of h is an equivalence on the carrier
// (group.CosetEquivalenceOn), so on k (equivalence.EquivalenceOnMono),
// and k is counted by its classes inside k (equivalence.CountByClassesOn).
// k is a group on its own set (group.SubgroupGroupOn) holding h, so the
// class inside k of a point of k is its coset (group.LeftCosetClassOn),
// which is as large as h (LeftCosetSizeOn), h being finite inside the
// finite k; and k is closed under the relation (group.CosetClosedOn), so
// its quotient is the image of k under the class map
// (equivalence.QuotientOnClosed), which is the coset map
// (group.LeftCosetClass).
var LagrangeOn = lagrangeOnThm{family.Add(registry.ProofEntry{
	Name: "LagrangeOn",
	Key:  "prop_552a0cab0f1897b3",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀h k:set(A).",
		Hypotheses: []string{
			"subgroup(G, h)",
			"subgroup(G, k)",
			"h ⊆ k",
			"finite(k)",
		},
		Conclusion: "card(k) = card(h) * card(image(coset_map(G.mul, h), k))",
	},
		func(a *Argument, grp group.GroupFact[on.G], h, k *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"h is a subgroup",
				"so is k",
				"h lies in k",
				"k is finite")
			subgroupH, subgroupK, hInK, finiteK := parts[0], parts[1], parts[2], parts[3]

			kInC := a.Have(
				"k lies in G.carrier",
				"k ⊆ G.carrier",
				By(group.SubgroupSubset, subgroupK))
			onK := a.Have(
				"k, a subgroup, is a group on its own set",
				"group_on(restrict_group(G, k))",
				By(subgroupK, group.SubgroupGroupOn.Read(grp).At(k)))
			related, carrier :=
				a.TermAs[Fun2[A, A, Bool]]("λu:A. λv:A. v ∈ left_coset(u, h)"), a.TermAs[Set[A]]("G.carrier")
			cosets := a.Have(
				"lying in a point's coset is an equivalence on G.carrier, h being a subgroup, and so on k",
				"equivalence_on(k, λu:A. λv:A. v ∈ left_coset(u, h))",
				By(
					subgroupH,
					group.CosetEquivalenceOn.Read(grp).At(h),
					equivalence.EquivalenceOnMono.At(carrier, related, k),
					kInC))
			// The closure stays resident: it is the side condition of
			// QuotientOnClosed in the rewrite below.
			a.Have(
				"k is closed under the relation: a point of the coset of a point of k lies in k",
				"∀x y:A. x ∈ k ∧ y ∈ left_coset(x, h) ⇒ y ∈ k",
				By(hInK, group.CosetClosedOn.Read(onK)))
			quotient := a.Have(
				"so the quotient of k is the image of k under the class map, which is the coset map",
				"quotient_on(k, λu:A. λv:A. v ∈ left_coset(u, h)) = image(coset_map(G.mul, h), k)",
				Simp(Fwd(equivalence.QuotientOnClosed), Fwd(group.CosetMapDef)),
				By(group.LeftCosetClass))

			finiteH := a.Have(
				"h is finite, lying in the finite k",
				"finite(h)",
				By(finite_set.FiniteSubset.At(h, k), finiteK, hInK))
			sizedH := a.Have(
				"so h has card(h) elements",
				"has_size(h, card(h))",
				By(finiteH, cardinality.FiniteHasSize))
			classSized := a.Have(
				"the class inside k of each point of k is its coset, which is as large as h",
				Statement{
					Binders: "∀x:A.",
					Hypotheses: []string{
						"x ∈ k",
					},
					Conclusion: "has_size(equivalence_class(relation_on(k, λu:A. λv:A. v ∈ left_coset(u, h)), x), " +
						"    card(h))",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					xIn := b.Assume()
					coset := b.Have(
						"the class of x inside k is its coset, k being a group holding h",
						"equivalence_class(relation_on(k, λu:A. λv:A. v ∈ left_coset(u, h)), x) = left_coset(x, h)",
						By(xIn, hInK, group.LeftCosetClassOn.Read(onK)))
					b.Show(
						"and the coset is as large as h, x lying in the group on k and h inside it",
						coset.Rw(),
						By(sizedH, xIn, hInK, LeftCosetSizeOn.Read(onK)))
				}))

			a.Show(
				"so k is counted by its classes, and its quotient is the set of cosets",
				quotient.RwRev(),
				By(equivalence.CountByClassesOn.Read(cosets), finiteK, classSized))
		}),
})}

// Lagrange — LagrangeOn on the whole type: a finite group is a finite
// subgroup of the group on 𝕌.
var Lagrange = lagrangeThm{family.Add(registry.ProofEntry{
	Name: "Lagrange",
	Key:  "prop_1492424fb52a28c6",
	Build: group.GroupAtUniverse.Law(Statement{
		Binders: "∀h k:set(A).",
		Hypotheses: []string{
			"subgroup(restrict_group(G, 𝕌), h)",
			"subgroup(restrict_group(G, 𝕌), k)",
			"h ⊆ k",
			"finite(k)",
		},
		Conclusion: "card(k) = card(h) * card(image(coset_map(G.mul, h), k))",
	}, LagrangeOn),
})}

// LagrangeDivides — the order of a subgroup divides the order of every
// finite subgroup containing it: by Lagrange's theorem the number of
// left cosets is the cofactor.
var LagrangeDivides = lagrangeDividesThm{family.Add(registry.ProofEntry{
	Name: "LagrangeDivides",
	Key:  "prop_7a04d923c2eb973f",
	Build: group.Group.Law(Statement{
		Binders: "∀h k:set(A).",
		Hypotheses: []string{
			"subgroup(restrict_group(G, 𝕌), h)",
			"subgroup(restrict_group(G, 𝕌), k)",
			"h ⊆ k",
			"finite(k)",
		},
		Conclusion: "card(h) ∣ card(k)",
	},
		func(a *Argument, grp Fact, h, k *Expr[Set[A]], given Fact) {
			count := a.Have(
				"k has card(h) points for each left coset of h in k",
				"card(k) = card(h) * card(image(coset_map(G.mul, h), k))",
				By(given, Read(Lagrange, grp).At(h, k)))
			// ↦ ∃x. card(k) = card(h) · x — nat_divides is minted by its
			// chapter's vocabulary rather than a define door, so it is
			// unfolded through that chapter's constant handle.
			a.Do(Unfold(nat_divides.DividesFactor))
			a.Take(a.TermAs[Nat]("card(image(coset_map(G.mul, h), k))"))
			a.Show(
				"the number of cosets is the cofactor",
				By(count))
		}),
})}

// LagrangeDividesOn — the size of a subgroup of a finite group divides the
// size of the group: by Lagrange's theorem (LagrangeOn, read with the
// carrier as the larger subgroup) the group has card(h) elements for each
// left coset of h, so the number of cosets is the cofactor. It is
// LagrangeDivides for a group on a set.
var LagrangeDividesOn = lagrangeDividesOnThm{family.Add(registry.ProofEntry{
	Name: "LagrangeDividesOn",
	Key:  "prop_4445e71b172d1839",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀h:set(A).",
		Hypotheses: []string{
			"subgroup(G, h)",
			"finite(G.carrier)",
		},
		Conclusion: "card(h) ∣ card(G.carrier)",
	},
		func(a *Argument, grp group.GroupFact[on.G], h *Expr[Set[A]], subgroup, finite Fact) {
			count := a.Have(
				"G has card(h) elements for each left coset of h",
				"card(G.carrier) = card(h) * card(image(coset_map(G.mul, h), G.carrier))",
				By(
					grp,
					subgroup,
					finite,
					LagrangeOn.Read(grp).At(h, a.TermAs[Set[A]]("G.carrier")),
					group.CarrierSubgroupOn,
					group.SubgroupSubset))
			a.Show(
				"so card(h) divides card(G.carrier), the number of cosets being the cofactor",
				By(
					count,
					nat_divides.DividesOwnMultiple.At(
						a.TermAs[Nat]("card(h)"),
						a.TermAs[Nat]("card(image(coset_map(G.mul, h), G.carrier))"))))
		}),
})}

// ---------------------------------------------------------------------------
// p-groups and p-subgroups
// ---------------------------------------------------------------------------

// PGroupDef — G is a p-group: a finite group whose order is a power of p.
// The definition does not ask p to be prime; the theorems that need it say so.
var PGroupDef = pGroupDefThm{family.Define(registry.DefEntry{
	Name:  "PGroupDef",
	Key:   "prop_f38b345e424f8cf",
	Const: "p_group",
	Type:  "group_ops(A) → num → bool",
	Equations: []string{
		"∀G:group_ops(A). ∀p:num. " +
			"    p_group(G, p) ⇔ group_on(G) ∧ finite(G.carrier) ∧ (∃n:num. card(G.carrier) = p ^ n)",
	},
})}

// PGroupFinite — a p-group is finite.
var PGroupFinite = pGroupFiniteThm{family.Add(registry.ProofEntry{
	Name:  "PGroupFinite",
	Key:   "prop_b512764dede16ad4",
	Build: PGroupDef.Entry().Conjunct("finite(G.carrier)"),
})}

// PGroupPowerOrder — the order of a p-group is a power of p.
var PGroupPowerOrder = pGroupPowerOrderThm{family.Add(registry.ProofEntry{
	Name:  "PGroupPowerOrder",
	Key:   "prop_4c7507a128ea4a62",
	Build: PGroupDef.Entry().Conjunct("∃n:num. card(G.carrier) = p ^ n"),
})}

// PSubgroupDef — H is a p-subgroup of G: a subgroup that is a p-group.
var PSubgroupDef = pSubgroupDefThm{family.Define(registry.DefEntry{
	Name:  "PSubgroupDef",
	Key:   "prop_78e1c6d9befe413d",
	Const: "p_subgroup",
	Type:  "group_ops(A) → num → set(A) → bool",
	Equations: []string{
		"∀G:group_ops(A). ∀p:num. ∀h:set(A). " +
			"    p_subgroup(G, p, h) ⇔ subgroup(G, h) ∧ p_group(restrict_group(G, h), p)",
	},
	Deps: []registry.EntryLike{PGroupDef},
})}

// PSubgroupSubgroup — a p-subgroup is a subgroup.
var PSubgroupSubgroup = pSubgroupSubgroupThm{family.Add(registry.ProofEntry{
	Name:  "PSubgroupSubgroup",
	Key:   "prop_58c8a4757012ccf5",
	Build: PSubgroupDef.Entry().Conjunct("subgroup(G, h)"),
})}

// PSubgroupPGroup — a p-subgroup is a p-group under the operations of G.
var PSubgroupPGroup = pSubgroupPGroupThm{family.Add(registry.ProofEntry{
	Name:  "PSubgroupPGroup",
	Key:   "prop_1435c81bde6482",
	Build: PSubgroupDef.Entry().Conjunct("p_group(restrict_group(G, h), p)"),
})}

// PSubgroupIff — a p-subgroup of a group is a finite subgroup whose order
// is a power of p: the p-group condition is said of the restricted record,
// whose carrier is h and which is a group exactly when h is a subgroup
// (group.SubgroupGroupOn).
var PSubgroupIff = pSubgroupIffThm{family.Add(registry.ProofEntry{
	Name: "PSubgroupIff",
	Key:  "prop_6a7bc564f9773888",
	Build: group.GroupOn.Law("∀p:num. ∀h:set(A). "+
		"    p_subgroup(G, p, h) ⇔ subgroup(G, h) ∧ finite(h) ∧ (∃n:num. card(h) = p ^ n)",
		func(a *Argument, grp group.GroupFact[on.G], p *Expr[Nat], h *Expr[Set[A]]) {
			a.Show(
				"unfolded, the p-group is h under the operations of G, a group exactly when h is a subgroup",
				Simp(Fwd(PSubgroupDef), Fwd(PGroupDef)),
				By(group.SubgroupGroupOn.Read(grp).At(h)))
		}),
})}
