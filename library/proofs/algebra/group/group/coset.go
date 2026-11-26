// coset.go — subgroups, normal subgroups and cosets for a group record
// and the subsets of its carrier.

package group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// Subgroups
// ---------------------------------------------------------------------------

// SubgroupDef — subgroup(G, h) says h lies in G’s carrier and is closed
// under its product and inverse and contains its identity.
var SubgroupDef = subgroupDefThm{family.Define(registry.DefEntry{
	Name: "SubgroupDef",
	Key:  "prop_3979215c1f191158",

	Const: "subgroup",
	Type:  "group_ops(A) → set(A) → bool",
	Equations: []string{
		"∀G:group_ops(A). ∀h:set(A). " +
			"    subgroup(G, h) ⇔ " +
			"    h ⊆ G.carrier ∧ " +
			"    G.one ∈ h ∧ " +
			"    (∀x y:A. x ∈ h ∧ y ∈ h ⇒ G.mul(x, y) ∈ h) ∧ " +
			"    (∀x:A. x ∈ h ⇒ G.inv(x) ∈ h)",
	},
	Deps: []registry.EntryLike{
		GroupOpsData.Fields[0],
		GroupOpsData.Fields[1],
		GroupOpsData.Fields[2],
		GroupOpsData.Fields[3],
	},
})}

// The four conditions, each a law a proof cites instead of unfolding
// the definition and picking a conjunct. They ask nothing of the group —
// a subgroup's closure is its definition — so each is one conjunct of it
// read off (`Conjunct`), stated with no group in scope: the text spells
// `mul(x, y)`, since no structure binds `*` there. SubgroupMulInv, after
// them, combines two of the four, so it is a Law with a proof of its own
// rather than a conjunct read off.

// SubgroupSubset — a subgroup lies in the carrier.
var SubgroupSubset = subgroupSubsetThm{family.Add(registry.ProofEntry{
	Name: "SubgroupSubset",
	Key:  "prop_e30c1b248cd4dd61",

	Build: SubgroupDef.Entry().Conjunct("h ⊆ G.carrier"),
})}

// SubgroupOne — a subgroup holds the identity.
var SubgroupOne = subgroupOneThm{family.Add(registry.ProofEntry{
	Name: "SubgroupOne",
	Key:  "prop_33023ead34c7835b",

	Build: SubgroupDef.Entry().Conjunct("G.one ∈ h"),
})}

// SubgroupMul — a subgroup holds the product of two of its members.
var SubgroupMul = subgroupMulThm{family.Add(registry.ProofEntry{
	Name: "SubgroupMul",
	Key:  "prop_e17bbe1afd56d4a7",

	Build: SubgroupDef.Entry().Conjunct(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ h",
			"y ∈ h",
		},
		Conclusion: "G.mul(x, y) ∈ h",
	}),
})}

// SubgroupInv — a subgroup holds the inverse of each of its members.
var SubgroupInv = subgroupInvThm{family.Add(registry.ProofEntry{
	Name: "SubgroupInv",
	Key:  "prop_b154b8933a49d6fb",

	Build: SubgroupDef.Entry().Conjunct(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ h",
		},
		Conclusion: "G.inv(x) ∈ h",
	}),
})}

// SubgroupMulInv — a subgroup holds the product of one of its members
// with the inverse of another.
var SubgroupMulInv = subgroupMulInvThm{family.Add(registry.ProofEntry{
	Name: "SubgroupMulInv",
	Key:  "prop_b2820cd64a2d09fe",
	Build: SubgroupDef.Entry().Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ h",
			"y ∈ h",
		},
		Conclusion: "G.mul(x, G.inv(y)) ∈ h",
	}, func(a *Argument, subgroup Fact, x, y *Expr[A], members Fact) {
		a.Show(
			"h holds the inverse of y, and the product of x with it",
			By(members, SubgroupMul.Read(subgroup), SubgroupInv.Read(subgroup)))
	}),
})}

// SubgroupInvIffOn — a subgroup holds the inverse of a point of the
// carrier exactly when it holds the point: closure under the inverse
// one way, and the other way closure applied to inv(x), whose inverse
// is x. The quotient chapter reads memberships through the inverse and
// cites this instead of running the two-line argument each time.
var SubgroupInvIffOn = subgroupInvIffOnThm{family.Add(registry.ProofEntry{
	Name: "SubgroupInvIffOn",
	Key:  "prop_6aecef96017cf119",

	Build: GroupOn.Law(Statement{
		Binders: "∀h:set(A). ∀x:A.",
		Hypotheses: []string{
			"subgroup(G, h)",
			"x ∈ G.carrier",
		},
		Conclusion: "G.inv(x) ∈ h ⇔ x ∈ h",
	},
		func(a *Argument, group GroupFact[on.G], h *Expr[Set[A]], x *Member[A, on.G], subgroup Fact) {
			a.Iff()
			a.Forward(
				"h holds the inverse of its member G.inv(x), and that is x",
				func(b *Argument, invIn Fact) {
					// The backward arm's goal is the closure law's conclusion as
					// stated. Here the law concludes inv(inv(x)) ∈ h, and the goal
					// x ∈ h meets it only once the ground instance inv(inv(x)) = x
					// is substituted in — hence Normalized.
					inverse := proof.MemberOf(b.TermAs[A]("G.inv(x)"), invIn)
					b.Show(
						"G.inv(G.inv(x)) lies in h, and G.inv undoes itself on the carrier",
						By(Normalized, SubgroupInv.Read(subgroup).At(inverse), InvInvOn.Read(group).At(x)))
				})
			a.Backward(
				"h holds the inverse of its member x",
				func(b *Argument, inH Fact) {
					b.Show(
						"G.inv(x) lies in h",
						By(SubgroupInv, subgroup, inH))
				})
		}),
})}

// SubgroupInvIff — SubgroupInvIffOn on the whole type.
var SubgroupInvIff = subgroupInvIffThm{family.Add(registry.ProofEntry{
	Name: "SubgroupInvIff",
	Key:  "prop_9a4788f2a8dfed8b",
	Build: GroupAtUniverse.Law(Statement{
		Binders: "∀h:set(A). ∀x:A.",
		Hypotheses: []string{
			"subgroup(restrict_group(G, 𝕌), h)",
		},
		Conclusion: "G.inv(x) ∈ h ⇔ x ∈ h",
	}, SubgroupInvIffOn),
})}

// TrivialSubgroupOn — the trivial subgroup: {one} lies in the carrier,
// which holds one; a member of {one} is one itself, so closure under the
// product is one * one = one, the identity law, and closure under the
// inverse is inv(one) = one.
var TrivialSubgroupOn = trivialSubgroupOnThm{family.Add(registry.ProofEntry{
	Name: "TrivialSubgroupOn",
	Key:  "prop_e30004c362d54240",

	Build: GroupOn.Law("subgroup(G, {G.one})",
		func(a *Argument, group GroupFact[on.G]) {
			a.Do(Unfold(SubgroupDef), Unfold(set_basic.SubsetDef), Simp(Fwd(set_basic.InSing)), SplitConjAll(
				Case(
					"{G.one} lies in G.carrier: its G.one member is G.one, which G.carrier holds",
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						isOne := b.Assume()
						b.Show(
							"so x is G.one, a member of G.carrier",
							isOne.Rw(),
							By(OneIn, group))
					})),
				Case(
					"G.one is a member: it is G.one",
					Basic()),
				Case(
					"the product of two members is a member: both are G.one, and G.one * G.one is G.one",
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						b.FixAs[A]("y")
						both := b.Assume()
						ones := b.Conjuncts(
							both,
							"x is G.one",
							"and so is y")
						b.Show(
							"so x * y is G.one * G.one, which is G.one by the identity law at G.one, a member of G.carrier",
							ones[0].Rw(),
							ones[1].Rw(),
							By(LeftIdentityOn, group, OneIn))
					})),
				Case(
					"the inverse of a member is a member: it is G.one, and G.one is its own inverse",
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						isOne := b.Assume()
						b.Show(
							"so G.inv(x) is G.inv(G.one), which is G.one",
							isOne.Rw(),
							By(InvOneOn, group))
					})),
			))
		}),
})}

// TrivialSubgroup — TrivialSubgroupOn on the whole type.
var TrivialSubgroup = trivialSubgroupThm{family.Add(registry.ProofEntry{
	Name:  "TrivialSubgroup",
	Key:   "prop_d2a1d98e3e49791e",
	Build: GroupAtUniverse.Law("subgroup(restrict_group(G, 𝕌), {G.one})", TrivialSubgroupOn),
})}

// CarrierSubgroupOn — the carrier is a subgroup of itself: it lies in
// itself, holds the identity, and is closed under the two operations —
// the group's own closure axioms.
var CarrierSubgroupOn = carrierSubgroupOnThm{family.Add(registry.ProofEntry{
	Name: "CarrierSubgroupOn",
	Key:  "prop_c5d8d86c2dfac7d8",

	Build: GroupOn.Law("subgroup(G, G.carrier)",
		func(a *Argument, group GroupFact[on.G]) {
			a.Do(Unfold(SubgroupDef), SplitConjAll(
				Case(
					"G.carrier lies in G.carrier",
					BySets()),
				Case(
					"G.carrier holds G.one",
					By(OneIn, group)),
				Case(
					"G.carrier is closed under the product",
					By(MulIn, group)),
				Case(
					"G.carrier is closed under the inverse",
					By(InvIn, group)),
			))
		}),
})}

// CarrierSubgroup — CarrierSubgroupOn on the whole type: the whole
// type is a subgroup of itself.
var CarrierSubgroup = carrierSubgroupThm{family.Add(registry.ProofEntry{
	Name:  "CarrierSubgroup",
	Key:   "prop_cc90f235529edf89",
	Build: GroupAtUniverse.Law("subgroup(restrict_group(G, 𝕌), 𝕌)", CarrierSubgroupOn),
})}

// SubgroupGroupOn — under a group on c, a subgroup of it is exactly a
// subset of c that is a group on its own set: the closure conditions are
// the subgroup's, and the axioms hold on the subset because they hold
// on c. Stated on the carrier only: it is how a subgroup reaches the
// laws of the group on a set.
var SubgroupGroupOn = subgroupGroupOnThm{family.Add(registry.ProofEntry{
	Name: "SubgroupGroupOn",
	Key:  "prop_1fa13ffc90d53c59",

	Build: GroupOn.Law("∀h:set(A). subgroup(G, h) ⇔ h ⊆ G.carrier ∧ group_on(restrict_group(G, h))",
		func(a *Argument, group GroupFact[on.G], h *Expr[Set[A]]) {
			a.Iff()
			a.Forward(
				"the closure conditions are the subgroup's, and each "+
					"axiom on h is an instance of the group's on G.carrier",
				func(b *Argument, subgroup Fact) {
					hInC := b.Have(
						"h lies in G.carrier",
						"h ⊆ G.carrier",
						By(SubgroupSubset, subgroup))
					inclusion := b.Unfolded(hInC, set_basic.SubsetDef)
					// The three axioms at members of h, each had from the axiom
					// on c before group_on is unfolded — the unfolding opens the
					// resident group on c as well, and a fact had before it stays.
					assoc := b.Have(
						"the product associates on h, as on G.carrier",
						"∀x y z:A. x ∈ h ∧ y ∈ h ∧ z ∈ h ⇒ x * (y * z) = (x * y) * z",
						Derive(func(d *Argument) {
							d.FixAs[A]("x")
							d.FixAs[A]("y")
							d.FixAs[A]("z")
							members := d.Conjuncts(
								d.Assume(),
								"x lies in h",
								"so does y",
								"and z")
							inC := []Fact{
								d.Have(
									"x lies in G.carrier",
									"x ∈ G.carrier",
									By(inclusion, members[0])),
								d.Have(
									"so does y",
									"y ∈ G.carrier",
									By(inclusion, members[1])),
								d.Have(
									"and z",
									"z ∈ G.carrier",
									By(inclusion, members[2])),
							}
							d.Show(
								"the axiom on G.carrier",
								By(AssocOn, group, inC[0], inC[1], inC[2]))
						}))
					leftIdentity := b.Have(
						"G.one is a left identity on h, as on G.carrier",
						"∀x:A. x ∈ h ⇒ G.one * x = x",
						Derive(func(d *Argument) {
							d.FixAs[A]("x")
							member := d.Assume()
							xInC := d.Have(
								"x lies in G.carrier",
								"x ∈ G.carrier",
								By(inclusion, member))
							d.Show(
								"the axiom on G.carrier",
								By(LeftIdentityOn, group, xInC))
						}))
					leftInverse := b.Have(
						"G.inv(x) is a left inverse on h, as on G.carrier",
						"∀x:A. x ∈ h ⇒ G.inv(x) * x = G.one",
						Derive(func(d *Argument) {
							d.FixAs[A]("x")
							member := d.Assume()
							xInC := d.Have(
								"x lies in G.carrier",
								"x ∈ G.carrier",
								By(inclusion, member))
							d.Show(
								"the axiom on G.carrier",
								By(LeftInverseOn, group, xInC))
						}))
					// Unfolded, group_on on h asks the three closure conditions,
					// which are the subgroup's, and the three axioms just had.
					b.Do(SplitConj(
						Case(
							"h lies in G.carrier",
							By(hInC)),
						Case(
							"and h is a group on its own set",
							Unfold(RestrictGroupDef),
							Unfold(GroupOn),
							SplitConjAll(
								Case(
									"h holds the identity",
									By(SubgroupOne, subgroup)),
								Case(
									"h is closed under the product",
									By(SubgroupMul, subgroup)),
								Case(
									"h is closed under the inverse",
									By(SubgroupInv, subgroup)),
								Case(
									"the product associates on h",
									By(assoc)),
								Case(
									"G.one is a left identity on h",
									By(leftIdentity)),
								Case(
									"G.inv(x) is a left inverse on h",
									By(leftInverse)),
							)),
					))
				})
			a.Backward(
				"a subset of G.carrier that is a group on its own set is closed under the three operations",
				func(b *Argument, given Fact) {
					parts := b.Conjuncts(
						given,
						"h lies in G.carrier",
						"h is a group on its own set")
					// Unfolded, subgroup(G, h) asks the inclusion in hand and the
					// three closure conditions, each a law of the group on h.
					b.Do(Unfold(SubgroupDef), SplitConjAll(
						Case(
							"h lies in G.carrier",
							By(parts[0])),
						Case(
							"h holds the identity: its own",
							By(OneIn.Read(parts[1]))),
						Case(
							"h is closed under the product",
							By(MulIn.Read(parts[1]))),
						Case(
							"h is closed under the inverse",
							By(InvIn.Read(parts[1]))),
					))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Normal subgroups
// ---------------------------------------------------------------------------

// NormalSubgroupDef — a subgroup invariant under conjugation by G’s carrier.
var NormalSubgroupDef = normalSubgroupDefThm{family.Define(registry.DefEntry{
	Name: "NormalSubgroupDef",
	Key:  "prop_a0b5b20965b778dd",

	Const: "normal_subgroup",
	Type:  "group_ops(A) → set(A) → bool",
	Equations: []string{
		"∀G:group_ops(A). ∀h:set(A). " +
			"    normal_subgroup(G, h) ⇔ " +
			"    subgroup(G, h) ∧ (∀g x:A. g ∈ G.carrier ∧ x ∈ h ⇒ G.mul(G.mul(g, x), G.inv(g)) ∈ h)",
	},
	Deps: []registry.EntryLike{SubgroupDef},
})}

// NormalSubgroupSubgroup — a normal subgroup is a subgroup.
var NormalSubgroupSubgroup = normalSubgroupSubgroupThm{family.Add(registry.ProofEntry{
	Name: "NormalSubgroupSubgroup",
	Key:  "prop_5ff766750ec10072",

	Build: NormalSubgroupDef.Entry().Conjunct("subgroup(G, h)"),
})}

// NormalSubgroupConjugate — a normal subgroup holds every conjugate by
// the carrier of each of its members.
var NormalSubgroupConjugate = normalSubgroupConjugateThm{family.Add(registry.ProofEntry{
	Name: "NormalSubgroupConjugate",
	Key:  "prop_5fc360b3912c12ee",

	Build: NormalSubgroupDef.Entry().Conjunct(Statement{
		Binders: "∀g x:A.",
		Hypotheses: []string{
			"g ∈ G.carrier",
			"x ∈ h",
		},
		Conclusion: "G.mul(G.mul(g, x), G.inv(g)) ∈ h",
	}),
})}

// NormalSubgroupSwapOn — a normal subgroup holds a product of two
// points of the carrier exactly when it holds the reversed product:
// y * x is the conjugate of x * y by inv(x), since inv(x) undoes x and
// inv undoes itself, and the other direction is the same with the roles
// of x and y exchanged.
var NormalSubgroupSwapOn = normalSubgroupSwapOnThm{family.Add(registry.ProofEntry{
	Name: "NormalSubgroupSwapOn",
	Key:  "prop_494ae37f3fb6542a",

	Build: GroupOn.Law(Statement{
		Binders: "∀h:set(A). ∀x y:A.",
		Hypotheses: []string{
			"normal_subgroup(G, h)",
			"x ∈ G.carrier ∧ y ∈ G.carrier",
		},
		Conclusion: "x * y ∈ h ⇔ y * x ∈ h",
	},
		func(a *Argument, group GroupFact[on.G], h *Expr[Set[A]], x, y *Expr[A], normal, members Fact) {
			parts := a.Conjuncts(
				members,
				"x lies in G.carrier",
				"so does y")
			xIn, yIn := parts[0], parts[1]
			a.Iff()
			a.Forward(
				"y * x is the conjugate of x * y by G.inv(x)",
				func(b *Argument, inH Fact) {
					inverseIn := b.Have(
						"G.inv(x) lies in G.carrier",
						"G.inv(x) ∈ G.carrier",
						By(InvIn, group, xIn))
					conjugate := b.Have(
						"G.inv(x) * (x * y) is y, and G.inv(G.inv(x)) is x",
						"(G.inv(x) * (x * y)) * G.inv(G.inv(x)) = y * x",
						Simp(Fwd(InvMulCancelLeftOn), Fwd(InvInvOn)),
						Refl())
					b.Show(
						"and h holds every conjugate by the carrier of its member x * y",
						conjugate.RwRev(),
						By(NormalSubgroupConjugate, normal, inverseIn, inH))
				})
			a.Backward(
				"x * y is the conjugate of y * x by G.inv(y)",
				func(b *Argument, inH Fact) {
					inverseIn := b.Have(
						"G.inv(y) lies in G.carrier",
						"G.inv(y) ∈ G.carrier",
						By(InvIn, group, yIn))
					conjugate := b.Have(
						"G.inv(y) * (y * x) is x, and G.inv(G.inv(y)) is y",
						"(G.inv(y) * (y * x)) * G.inv(G.inv(y)) = x * y",
						Simp(Fwd(InvMulCancelLeftOn), Fwd(InvInvOn)),
						Refl())
					b.Show(
						"and h holds every conjugate by the carrier of its member y * x",
						conjugate.RwRev(),
						By(NormalSubgroupConjugate, normal, inverseIn, inH))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Cosets
// ---------------------------------------------------------------------------

// NormalSubgroupSwap — NormalSubgroupSwapOn on the whole type.
var NormalSubgroupSwap = normalSubgroupSwapThm{family.Add(registry.ProofEntry{
	Name: "NormalSubgroupSwap",
	Key:  "prop_e10b66b7869f772e",
	Build: GroupAtUniverse.Law(Statement{
		Binders: "∀h:set(A). ∀x y:A.",
		Hypotheses: []string{
			"normal_subgroup(restrict_group(G, 𝕌), h)",
		},
		Conclusion: "x * y ∈ h ⇔ y * x ∈ h",
	}, NormalSubgroupSwapOn),
})}

// LeftCosetDef — `left_coset(mul, x, h)`: the left coset x·h, the set h
// moved by multiplying each of its members by x on the left. The
// operation can be any binary operation; a group record supplies G.mul.
var LeftCosetDef = leftCosetDefThm{family.Define(registry.DefEntry{
	Name:     "LeftCosetDef",
	Key:      "prop_ecb811c1bb4302ba",
	Const:    "left_coset",
	Type:     "(A → A → A) → A → set(A) → set(A)",
	Implicit: []string{"mul"},
	Equations: []string{
		"∀mul:(A → A → A). ∀x:A. ∀h:set(A). left_coset(mul, x, h) = image(λy:A. mul(x, y), h)",
	},
})}

// CosetMapDef — `coset_map(mul, h)`: the coset map x ↦ x·h, carrying a
// point to its left coset of h. At a normal subgroup it is the
// projection onto the quotient group, at a submodule the projection
// u ↦ u + K onto the quotient module.
var CosetMapDef = cosetMapDefThm{family.Define(registry.DefEntry{
	Name:      "CosetMapDef",
	Key:       "prop_91a2dcadde2a1388",
	Const:     "coset_map",
	Type:      "(A → A → A) → set(A) → A → set(A)",
	Equations: []string{"∀mul:(A → A → A). ∀h:set(A). coset_map(mul, h) = λx:A. left_coset(mul, x, h)"},
	Deps:      []registry.EntryLike{LeftCosetDef},
})}

// LeftCosetIn — a coset of a subset of the carrier by a point of the
// carrier lies in the carrier: each of its points is a product of two
// points of c.
var LeftCosetIn = leftCosetInThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetIn",
	Key:  "prop_62eb2d0bf3fda4b6",

	Build: GroupOn.Law(Statement{
		Binders: "∀x:A. ∀h:set(A).",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"h ⊆ G.carrier",
		},
		Conclusion: "left_coset(x, h) ⊆ G.carrier",
	},
		func(a *Argument, group GroupFact[on.G], x *Expr[A], h *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"x lies in G.carrier",
				"h lies in G.carrier")
			inclusion := a.Unfolded(parts[1], set_basic.SubsetDef)
			// InImage is pinned at A → A: a Go Simp rule is not instantiated
			// at a type on its own.
			a.Do(Unfold(set_basic.SubsetDef), Simp(
				Fwd(LeftCosetDef),
				Fwd(set_basic.InImage.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]()))))
			a.FixAs[A]("z")
			member := a.Assume()
			_, product := a.UnpackAs[A](member, "y")
			productParts := a.Conjuncts(
				product,
				"z is x * y",
				"y lies in h")
			a.Show(
				"so z is a product of two points of G.carrier",
				productParts[0].Rw(),
				By(MulIn, group, parts[0], inclusion, productParts[1]))
		}),
})}

// InLeftCosetOn — membership in a left coset, read back through the
// inverse, for points of the carrier and a subset of it. The coset is h
// moved by x, so its members are the products x * z with z in h.
// Multiplying such a product by inv(x) on the left reads z back out, so
// inv(x) * y is the z that y came from; and conversely inv(x) * y,
// multiplied by x, is y again.
var InLeftCosetOn = inLeftCosetOnThm{family.Add(registry.ProofEntry{
	Name: "InLeftCosetOn",
	Key:  "prop_5c56a2302ddee144",

	Build: GroupOn.Law(Statement{
		Binders: "∀x y:A. ∀h:set(A).",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
			"h ⊆ G.carrier",
		},
		Conclusion: "y ∈ left_coset(x, h) ⇔ G.inv(x) * y ∈ h",
	},
		func(a *Argument, group GroupFact[on.G], x, y *Expr[A], h *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"x lies in G.carrier",
				"so does y",
				"h lies in G.carrier")
			inclusion := a.Unfolded(parts[2], set_basic.SubsetDef)
			// The coset is the image of h under x * ·, and a point of an
			// image is a value the map takes on h. InImage is pinned at
			// A → A: a Go Simp rule is not instantiated at a type on its own.
			a.Do(Simp(
				Fwd(LeftCosetDef),
				Fwd(set_basic.InImage.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]()))))
			a.Iff()
			a.Forward(
				"y is x * z for some z in h, and multiplying by G.inv(x) on the left reads z back out",
				func(b *Argument, member Fact) {
					_, product := b.Unpack(member, "z")
					members := b.Conjuncts(
						product,
						"y is x * z",
						"z lies in h")
					readBack := b.Have(
						"G.inv(x) * y is the z that y came from: y is x * z, and G.inv(x) undoes x on the carrier",
						"G.inv(x) * y = z",
						members[0].Rw(),
						By(InvMulCancelLeftOn, group, parts[0], inclusion, members[1]))
					b.Show(
						"so G.inv(x) * y is z, which lies in h",
						readBack.Rw(),
						By(members[1]))
				})
			a.Backward(
				"G.inv(x) * y is a member of h that x carries to y",
				func(b *Argument, inH Fact) {
					b.Take(b.TermAs[A]("G.inv(x) * y"))
					putBack := b.Have(
						"x carries G.inv(x) * y back to y: x undoes G.inv(x) on the carrier",
						"y = x * (G.inv(x) * y)",
						By(MulInvCancelLeftOn, group, parts[0], parts[1]))
					b.Show(
						"so y is x times a member of h",
						By(putBack, inH))
				})
		}),
})}

// InLeftCoset — InLeftCosetOn on the whole type: every point lies in
// the carrier and every set in it.
var InLeftCoset = inLeftCosetThm{family.Add(registry.ProofEntry{
	Name: "InLeftCoset",
	Key:  "prop_2b626043697083a5",
	Build: GroupAtUniverse.Law(
		"∀x y:A. ∀h:set(A). y ∈ left_coset(x, h) ⇔ G.inv(x) * y ∈ h", InLeftCosetOn),
})}

// LeftCosetOneOn — the identity moves nothing: one·h is h for a subset
// h of the carrier. A point of one·h is one * z for some z in h, and
// one * z is z on the carrier; and a point of h is one times itself.
var LeftCosetOneOn = leftCosetOneOnThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetOneOn",
	Key:  "prop_bd1b176b5732e681",

	Build: GroupOn.Law(Statement{
		Binders: "∀h:set(A).",
		Hypotheses: []string{
			"h ⊆ G.carrier",
		},
		Conclusion: "left_coset(G.one, h) = h",
	},
		func(a *Argument, group GroupFact[on.G], h *Expr[Set[A]], subset Fact) {
			inclusion := a.Unfolded(subset, set_basic.SubsetDef)
			a.Do(Simp(Fwd(set_basic.Extension)))
			a.FixAs[A]("y")
			a.Do(Simp(
				Fwd(LeftCosetDef),
				Fwd(set_basic.InImage.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]()))))
			a.Iff()
			a.Forward(
				"y is G.one * z for some z in h, and G.one * z is z",
				func(b *Argument, member Fact) {
					_, product := b.Unpack(member, "z")
					parts := b.Conjuncts(
						product,
						"y is G.one * z",
						"z lies in h")
					isZ := b.Have(
						"G.one * z is z, z lying in G.carrier",
						"G.one * z = z",
						By(LeftIdentityOn, group, inclusion, parts[1]))
					b.Show(
						"so y is z, a member of h",
						parts[0].Rw(),
						isZ.Rw(),
						By(parts[1]))
				})
			a.Backward(
				"y is one times itself",
				func(b *Argument, inH Fact) {
					b.Take(y_(b))
					b.Show(
						"G.one * y is y, y lying in G.carrier",
						By(LeftIdentityOn, group, inclusion, inH))
				})
		}),
})}

// y_ is the point the extension fixed, read back for a Take.
func y_(b *Argument) *Expr[A] { return b.TermAs[A]("y") }

// LeftCosetOne — LeftCosetOneOn on the whole type.
var LeftCosetOne = leftCosetOneThm{family.Add(registry.ProofEntry{
	Name:  "LeftCosetOne",
	Key:   "prop_e7f63743b4baa862",
	Build: GroupAtUniverse.Law("∀h:set(A). left_coset(G.one, h) = h", LeftCosetOneOn),
})}

// TranslateCoset — moving a coset again: g·(x·h) is (g * x)·h for points
// g and x of the carrier and a subset h of it, each g * (x * y) with y in h
// being g * x * y.
var TranslateCoset = translateCosetThm{family.Add(registry.ProofEntry{
	Name: "TranslateCoset",
	Key:  "prop_a70e6f0f28964c94",
	Build: GroupOn.Law(Statement{
		Binders: "∀g x:A. ∀h:set(A).",
		Hypotheses: []string{
			"g ∈ G.carrier",
			"x ∈ G.carrier",
			"h ⊆ G.carrier",
		},
		Conclusion: "left_coset(g, left_coset(x, h)) = left_coset(g * x, h)",
	},
		func(a *Argument, group GroupFact[on.G], g, x *Member[A, on.G], h *Expr[Set[A]], inside Fact) {
			a.Show(
				"each g * (x * y) with y in h is g * x * y",
				Simp(Fwd(LeftCosetDef)),
				BySets(inside, AssocOn.Read(group).AsFact().At(g, x), g, x))
		}),
})}

// InOwnLeftCosetOn — a point of the carrier lies in its own coset of a
// subgroup: read through the inverse, the membership asks that
// inv(x) * x, the identity, lie in h.
var InOwnLeftCosetOn = inOwnLeftCosetOnThm{family.Add(registry.ProofEntry{
	Name: "InOwnLeftCosetOn",
	Key:  "prop_f7f4e54fa829e676",

	Build: GroupOn.Law(Statement{
		Binders: "∀x:A. ∀h:set(A).",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"subgroup(G, h)",
		},
		Conclusion: "x ∈ left_coset(x, h)",
	},
		func(a *Argument, group GroupFact[on.G], x *Expr[A], h *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"x lies in G.carrier",
				"h is a subgroup")
			a.Have(
				"h lies in G.carrier",
				"h ⊆ G.carrier",
				By(SubgroupSubset, parts[1]))
			a.Show(
				"G.inv(x) * x is the identity, which the subgroup holds",
				Simp(Fwd(InLeftCosetOn), Fwd(LeftInverseOn)),
				By(SubgroupOne, parts[1]))
		}),
})}

// ---------------------------------------------------------------------------
// The coset relation as an equivalence
// ---------------------------------------------------------------------------

// InOwnLeftCoset — InOwnLeftCosetOn on the whole type.
var InOwnLeftCoset = inOwnLeftCosetThm{family.Add(registry.ProofEntry{
	Name: "InOwnLeftCoset",
	Key:  "prop_d2cf264a907cd3a3",
	Build: GroupAtUniverse.Law(Statement{
		Binders: "∀x:A. ∀h:set(A).",
		Hypotheses: []string{
			"subgroup(restrict_group(G, 𝕌), h)",
		},
		Conclusion: "x ∈ left_coset(x, h)",
	}, InOwnLeftCosetOn),
})}

// LeftCosetClass — the left coset x·h is the class of x under the
// relation "lies in the coset of": a point is related to x exactly when it
// lies in x·h. Stated for any operation, no group.
var LeftCosetClass = leftCosetClassThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetClass",
	Key:  "prop_5dd2169fb66145b0",
	Build: family.Theorem("∀mul:(A → A → A). ∀x:A. ∀h:set(A). "+
		"    equivalence_class(λu:A. λv:A. v ∈ left_coset(mul, u, h), x) = left_coset(mul, x, h)",
		func(a *Argument, mul *Arrow2[A, A, A], x *Expr[A], h *Expr[Set[A]]) {
			a.Show(
				"sets with the same members are equal, and a point "+
					"lies in the class of x exactly when it lies in x·h",
				Simp(Fwd(set_basic.Extension)),
				By(equivalence.InClass))
		}),
})}

// LeftCosetClassOn — the coset of a point of the carrier by a subset of
// it is also its class inside c: the coset lies in c (LeftCosetIn), so the
// restriction to c asks nothing more (equivalence.ClassOnClosed).
var LeftCosetClassOn = leftCosetClassOnThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetClassOn",
	Key:  "prop_7d2b475405df99df",

	Build: GroupOn.Law(Statement{
		Binders: "∀x:A. ∀h:set(A).",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"h ⊆ G.carrier",
		},
		Conclusion: "equivalence_class(relation_on(G.carrier, λu:A. λv:A. v ∈ left_coset(u, h)), x) = " +
			"left_coset(x, h)",
	},
		func(a *Argument, group GroupFact[on.G], x *Expr[A], h *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"x lies in G.carrier",
				"h lies in G.carrier")
			cosetInC := a.Unfolded(a.Have(
				"x·h lies in G.carrier",
				"left_coset(x, h) ⊆ G.carrier",
				By(LeftCosetIn, group, parts[0], parts[1])), set_basic.SubsetDef)
			unrestricted := a.Have(
				"the class of x inside G.carrier is its class, x·h lying in G.carrier",
				"equivalence_class(relation_on(G.carrier, λu:A. λv:A. v ∈ left_coset(u, h)), x) = "+
					"equivalence_class(λu:A. λv:A. v ∈ left_coset(u, h), x)",
				By(equivalence.ClassOnClosed, parts[0], cosetInC))
			a.Show(
				"and the class is the coset",
				unrestricted.Rw(),
				By(LeftCosetClass))
		}),
})}

// CosetClosedOn — the carrier is closed under the coset relation of a
// subset of it: a point of the coset x·h of a point x of c lies in c,
// since the coset does (LeftCosetIn). It is the closure the class laws of
// relations/equivalence ask of a set before they read its classes inside
// it as the classes of the relation itself.
var CosetClosedOn = cosetClosedOnThm{family.Add(registry.ProofEntry{
	Name: "CosetClosedOn",
	Key:  "prop_4028cce7195c40c4",

	Build: GroupOn.Law(Statement{
		Binders: "∀h:set(A). ∀x y:A.",
		Hypotheses: []string{
			"h ⊆ G.carrier",
			"x ∈ G.carrier ∧ y ∈ left_coset(x, h)",
		},
		Conclusion: "y ∈ G.carrier",
	},
		func(a *Argument, group GroupFact[on.G], h *Expr[Set[A]], x, y *Expr[A], hInC, given Fact) {
			cosetInC := a.Have(
				"x·h lies in G.carrier",
				"left_coset(x, h) ⊆ G.carrier",
				By(LeftCosetIn, group, hInC, given))
			a.Show(
				"so does its point y",
				BySets(cosetInC, given))
		}),
})}

// CosetEquivalenceOn — lying in a point's left coset of a subgroup is an
// equivalence on the carrier, so the quotient of c by it, the cosets, is
// read through the class laws of relations/equivalence. Read through the
// inverse, y ∈ x·h says that inv(x) * y lies in h, and the three axioms
// are then the subgroup's three closure conditions: x lies in its own
// coset because inv(x) * x is the identity; the relation turns round
// because inv(y) * x is the inverse of inv(x) * y; and it composes because
// inv(x) * z is the product of inv(x) * y and inv(y) * z.
var CosetEquivalenceOn = cosetEquivalenceOnThm{family.Add(registry.ProofEntry{
	Name: "CosetEquivalenceOn",
	Key:  "prop_2e78d11bcf885609",

	Build: GroupOn.Law(Statement{
		Binders: "∀h:set(A).",
		Hypotheses: []string{
			"subgroup(G, h)",
		},
		Conclusion: "equivalence_on(G.carrier, λx:A. λy:A. y ∈ left_coset(x, h))",
	},
		func(a *Argument, group GroupFact[on.G], h *Expr[Set[A]], subgroup Fact) {
			hInC := a.Have(
				"h lies in G.carrier",
				"h ⊆ G.carrier",
				By(SubgroupSubset, subgroup))
			a.Do(Unfold(equivalence.EquivalenceOn), SplitConjAll(
				Case(
					"reflexive: a point of G.carrier lies in its own coset",
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						xIn := b.Assume()
						b.Show(
							"G.inv(x) * x is the identity, which h holds",
							By(InOwnLeftCosetOn, group, xIn, subgroup))
					})),
				Case(
					"symmetric: G.inv(y) * x is the inverse of G.inv(x) * y",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						y := b.FixAs[A]("y")
						points := b.Conjuncts(
							b.Assume(),
							"x lies in G.carrier",
							"so does y")
						xM, yM := b.MemberOf[on.G](x, points[0]), b.MemberOf[on.G](y, points[1])
						related := b.Assume()
						inH := b.Have(
							"read through the inverse, G.inv(x) * y lies in h",
							"G.inv(x) * y ∈ h",
							By(related, InLeftCosetOn.Read(group).At(xM, yM, h), hInC))
						turned := b.Have(
							"G.inv(y) * x is the inverse of G.inv(x) * y",
							"G.inv(y) * x = G.inv(G.inv(x) * y)",
							Simp(Fwd(InvMulOn), Fwd(InvInvOn), Fwd(InvIn)),
							Basic())
						back := b.Have(
							"so h holds G.inv(y) * x",
							"G.inv(y) * x ∈ h",
							turned.Rw(),
							By(SubgroupInv, subgroup, inH))
						b.Show(
							"read through the inverse, x lies in y·h",
							By(back, InLeftCosetOn.Read(group).At(yM, xM, h), hInC))
					})),
				Case(
					"transitive: G.inv(x) * z is the product of G.inv(x) * y and G.inv(y) * z",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						y := b.FixAs[A]("y")
						z := b.FixAs[A]("z")
						points := b.Conjuncts(
							b.Assume(),
							"x lies in G.carrier",
							"so does y",
							"and z")
						xM, yM, zM :=
							b.MemberOf[on.G](x, points[0]), b.MemberOf[on.G](y, points[1]), b.MemberOf[on.G](z, points[2])
						steps := b.Conjuncts(
							b.Assume(),
							"y lies in x·h",
							"z lies in y·h")
						first := b.Have(
							"G.inv(x) * y lies in h",
							"G.inv(x) * y ∈ h",
							By(steps[0], InLeftCosetOn.Read(group).At(xM, yM, h), hInC))
						second := b.Have(
							"G.inv(y) * z lies in h",
							"G.inv(y) * z ∈ h",
							By(steps[1], InLeftCosetOn.Read(group).At(yM, zM, h), hInC))
						regroup := b.Have(
							"G.inv(x) * z is (G.inv(x) * y) * (G.inv(y) * z)",
							"G.inv(x) * z = (G.inv(x) * y) * (G.inv(y) * z)",
							Simp(Rev(AssocOn), Fwd(MulInvCancelLeftOn), Fwd(MulIn), Fwd(InvIn)),
							Basic())
						inH := b.Have(
							"so h holds G.inv(x) * z, the product of two of its members",
							"G.inv(x) * z ∈ h",
							regroup.Rw(),
							By(SubgroupMul, subgroup, first, second))
						b.Show(
							"read through the inverse, z lies in x·h",
							By(inH, InLeftCosetOn.Read(group).At(xM, zM, h), hInC))
					})),
			))
		}),
})}

// CosetEquivalence — lying in a point's left coset of a subgroup is an
// equivalence relation on the whole type: CosetEquivalenceOn at 𝕌, read
// through equivalence.EquivalenceOnUniverse. Lagrange's theorem counts by
// its classes.
var CosetEquivalence = cosetEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "CosetEquivalence",
	Key:  "prop_f45be5e39d293c9",
	Build: Group.Law(Statement{
		Binders: "∀h:set(A).",
		Hypotheses: []string{
			"subgroup(restrict_group(G, 𝕌), h)",
		},
		Conclusion: "equivalence(λx:A. λy:A. y ∈ left_coset(x, h))",
	},
		func(a *Argument, group Fact, h *Expr[Set[A]], subgroup Fact) {
			onUniverse := a.Have(
				"the group is a group on 𝕌",
				"group_on(restrict_group(G, 𝕌))",
				By(group, GroupOnUniverse))
			cosets := a.Have(
				"so lying in a point's coset is an equivalence on 𝕌",
				"equivalence_on(𝕌, λx:A. λy:A. y ∈ left_coset(x, h))",
				By(CosetEquivalenceOn, onUniverse, subgroup))
			a.Show(
				"and an equivalence on 𝕌 is an equivalence",
				By(cosets, equivalence.EquivalenceOnUniverse))
		}),
})}

// LeftCosetEqOn — two left cosets of a subgroup by points of the
// carrier are equal exactly when inv(x) * y lies in it. The coset relation
// is an equivalence on c (CosetEquivalenceOn) under which c is closed
// (CosetClosedOn), so the classes of x and y are equal exactly when y lies
// in x·h (equivalence.ClassEqIffClosed); the classes are the cosets
// (LeftCosetClass), and y ∈ x·h read through the inverse is
// inv(x) * y ∈ h (InLeftCosetOn).
var LeftCosetEqOn = leftCosetEqOnThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetEqOn",
	Key:  "prop_f58ad2ca7ff39d61",

	Build: GroupOn.Law(Statement{
		Binders: "∀x y:A. ∀h:set(A).",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
			"subgroup(G, h)",
		},
		Conclusion: "left_coset(x, h) = left_coset(y, h) ⇔ G.inv(x) * y ∈ h",
	},
		func(a *Argument, group GroupFact[on.G], x, y *Expr[A], h *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"x lies in G.carrier",
				"so does y",
				"h is a subgroup")
			xIn, yIn, subgroup := parts[0], parts[1], parts[2]
			hInC := a.Have(
				"h lies in G.carrier",
				"h ⊆ G.carrier",
				By(SubgroupSubset, subgroup))
			cosets := a.Have(
				"lying in a point's coset is an equivalence on G.carrier",
				"equivalence_on(G.carrier, λu:A. λv:A. v ∈ left_coset(u, h))",
				By(CosetEquivalenceOn, group, subgroup))
			classes := a.Have(
				"G.carrier being closed under it, the classes of x and y are equal exactly when y lies in x·h",
				"equivalence_class(λu:A. λv:A. v ∈ left_coset(u, h), x) = "+
					"equivalence_class(λu:A. λv:A. v ∈ left_coset(u, h), y) ⇔ "+
					"y ∈ left_coset(x, h)",
				By(equivalence.ClassEqIffClosed.Read(cosets), CosetClosedOn.Read(group), hInC, xIn, yIn))
			a.Show(
				"the classes are the cosets, and y lies in x·h exactly when G.inv(x) * y lies in h",
				classes.Simp(Fwd(LeftCosetClass), Fwd(InLeftCosetOn.Read(group))),
				By(classes))
		}),
})}

// LeftCosetEq — LeftCosetEqOn on the whole type.
var LeftCosetEq = leftCosetEqThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetEq",
	Key:  "prop_8b671b9d207b7417",
	Build: GroupAtUniverse.Law(Statement{
		Binders: "∀x y:A. ∀h:set(A).",
		Hypotheses: []string{
			"subgroup(restrict_group(G, 𝕌), h)",
		},
		Conclusion: "left_coset(x, h) = left_coset(y, h) ⇔ G.inv(x) * y ∈ h",
	}, LeftCosetEqOn),
})}
