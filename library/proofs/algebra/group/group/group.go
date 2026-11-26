// group.go — whole-type groups and groups on record carriers.
// Each carrier law is proved once, with its whole-type view beside it.

package group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// Group — G's product, identity and inverse satisfy the group axioms
// on the whole type A. This predicate does not constrain G.carrier.
// Under a law, x * y means G.mul(x, y); the inverse is G.inv(x).
// The axioms require only the left identity and left inverse; the right
// laws are consequences.
var Group = groupThm{family.DefineStructure(registry.DefEntry{
	Name:    "Group",
	Key:     "prop_615fe6c1287b6cc1",
	Const:   "group",
	Subject: "G",
	Type:    "group_ops(A) → bool",
	Equations: []string{
		"∀G:group_ops(A). " +
			"    group(G) ⇔ " +
			"    (∀x y z:A. G.mul(x, G.mul(y, z)) = G.mul(G.mul(x, y), z)) ∧ " +
			"    (∀x:A. G.mul(G.one, x) = x) ∧ " +
			"    (∀x:A. G.mul(G.inv(x), x) = G.one)",
	},
	Deps: []registry.EntryLike{GroupOpsData.Fields[0], GroupOpsData.Fields[1], GroupOpsData.Fields[2]},
})}

// GroupOn — G's carrier holds its identity, is closed under product and
// inverse, and satisfies associativity, left identity and left inverse.
var GroupOn = groupOnThm{family.DefineStructure(registry.DefEntry{
	Name: "GroupOn",
	Key:  "prop_ebd7e7c33c3d9e0",

	Const:   "group_on",
	Subject: "G",
	Type:    "group_ops(A) → bool",
	Equations: []string{
		"∀G:group_ops(A). " +
			"    group_on(G) ⇔ " +
			"    G.one ∈ G.carrier ∧ " +
			"    (∀x y:A. x ∈ G.carrier ∧ y ∈ G.carrier ⇒ G.mul(x, y) ∈ G.carrier) ∧ " +
			"    (∀x:A. x ∈ G.carrier ⇒ G.inv(x) ∈ G.carrier) ∧ " +
			"    (∀x y z:A. " +
			"        x ∈ G.carrier ∧ y ∈ G.carrier ∧ z ∈ G.carrier ⇒ " +
			"        G.mul(x, G.mul(y, z)) = G.mul(G.mul(x, y), z)) ∧ " +
			"    (∀x:A. x ∈ G.carrier ⇒ G.mul(G.one, x) = x) ∧ " +
			"    (∀x:A. x ∈ G.carrier ⇒ G.mul(G.inv(x), x) = G.one)",
	},
	Deps: []registry.EntryLike{
		GroupOpsData.Fields[0],
		GroupOpsData.Fields[1],
		GroupOpsData.Fields[2],
		GroupOpsData.Fields[3],
	},
})}

// ---------------------------------------------------------------------------
// The axioms
// ---------------------------------------------------------------------------
//
// The axioms are stated for the members of G's carrier.

// GroupOnUniverse — a group on the whole type is a group: every
// membership in 𝕌 holds, so the closure conditions ask nothing and the
// guarded axioms are the axioms.
var GroupOnUniverse = groupOnUniverseThm{family.Add(registry.ProofEntry{
	Name: "GroupOnUniverse",
	Key:  "prop_95528bc942563639",
	Build: family.Theorem("∀G:group_ops(A). group(G) ⇔ group_on(restrict_group(G, 𝕌))",
		func(a *Argument, G *Expr[GroupOps[A]]) {
			a.Show(
				"with every membership in 𝕌 true, the two predicates unfold to the same three axioms",
				Unfold(Group),
				Unfold(GroupOn),
				Simp(Fwd(set_basic.InUniv)),
				Basic())
		}),
})}

// GroupAtUniverse — the whole-type group is the group on 𝕌: a law of
// the group is proved once on the carrier set, and the whole-type member
// is its view through this door, the carrier read as 𝕌 and each guard
// discharged by InUniv (constitution §Structures, "One proof per law").
var GroupAtUniverse = Group.AtUniverseRecord(
	GroupOn, GroupOnUniverse, "restrict_group(G, 𝕌)", set_basic.InUniv, set_order.SubsetUniv)

// OneIn — the identity lies in the carrier.
var OneIn = oneInThm{family.Add(registry.ProofEntry{
	Name: "OneIn",
	Key:  "prop_40bb6e221821d6ab",

	Build: GroupOn.Axiom("G.one ∈ G.carrier"),
})}

// MulIn — the carrier is closed under the operation.
var MulIn = mulInThm{family.Add(registry.ProofEntry{
	Name: "MulIn",
	Key:  "prop_d2e94eb0a4ebedb2",

	Build: GroupOn.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
		},
		Conclusion: "x * y ∈ G.carrier",
	}),
})}

// InvIn — and under the inverse.
var InvIn = invInThm{family.Add(registry.ProofEntry{
	Name: "InvIn",
	Key:  "prop_8ba435b67d364d29",

	Build: GroupOn.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "G.inv(x) ∈ G.carrier",
	}),
})}

// AssocOn — the operation associates.
var AssocOn = assocOnThm{family.Add(registry.ProofEntry{
	Name: "AssocOn",
	Key:  "prop_53c725bb4dc52772",

	Build: GroupOn.Axiom(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
			"z ∈ G.carrier",
		},
		Conclusion: "x * (y * z) = x * y * z",
	}),
})}

// Assoc — AssocOn on the whole type.
var Assoc = assocThm{family.Add(registry.ProofEntry{
	Name:  "Assoc",
	Key:   "prop_afde97e830f288af",
	Build: GroupAtUniverse.Law("∀x y z:A. x * (y * z) = (x * y) * z", AssocOn),
})}

// LeftIdentityOn — the identity, from the left.
var LeftIdentityOn = leftIdentityOnThm{family.Add(registry.ProofEntry{
	Name: "LeftIdentityOn",
	Key:  "prop_3f910c487c55697",

	Build: GroupOn.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "G.one * x = x",
	}),
})}

// LeftIdentity — LeftIdentityOn on the whole type.
var LeftIdentity = leftIdentityThm{family.Add(registry.ProofEntry{
	Name:  "LeftIdentity",
	Key:   "prop_edbb00967bbc8f6d",
	Build: GroupAtUniverse.Law("∀x:A. G.one * x = x", LeftIdentityOn),
})}

// LeftInverseOn — the inverse, from the left.
var LeftInverseOn = leftInverseOnThm{family.Add(registry.ProofEntry{
	Name: "LeftInverseOn",
	Key:  "prop_5627b5d1c1422629",

	Build: GroupOn.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "G.inv(x) * x = G.one",
	}),
})}

// ---------------------------------------------------------------------------
// The other sides
// ---------------------------------------------------------------------------
//
// The axioms speak from the left only. Their first consequence is that
// inv(x) undoes x from the left, whatever stands to the right of it; the
// right-hand identity and inverse follow from that and one observation:
// the identity is the only element that is its own square. Once the
// right inverse is known, the same undoing works on the other side, and
// the three undoing laws are what every later chain cites instead of
// regrouping by hand.

// LeftInverse — LeftInverseOn on the whole type.
var LeftInverse = leftInverseThm{family.Add(registry.ProofEntry{
	Name:  "LeftInverse",
	Key:   "prop_649843679a068543",
	Build: GroupAtUniverse.Law("∀x:A. G.inv(x) * x = G.one", LeftInverseOn),
})}

// InvMulCancelLeftOn — inv(x) undoes x from the left: regroup, and the
// pair inv(x) * x collapses to the identity, which drops off.
var InvMulCancelLeftOn = invMulCancelLeftOnThm{family.Add(registry.ProofEntry{
	Name: "InvMulCancelLeftOn",
	Key:  "prop_a3a9d68b87208736",

	Build: GroupOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
		},
		Conclusion: "G.inv(x) * (x * y) = y",
	},
		func(a *Argument, group GroupFact[on.G], x, y *Member[A, on.G]) {
			a.Show(
				"regroup, collapse the inverse pair, drop the identity",
				CalcEq(
					Leg(
						a.TermAs[A]("(G.inv(x) * x) * y"),
						"regroup, so G.inv(x) meets x",
						By(AssocOn, group, x, y, InvIn)),
					Leg(
						a.TermAs[A]("G.one * y"),
						"that pair collapses to G.one",
						Simp(Fwd(LeftInverseOn)),
						Basic()),
					FinalLeg(
						"and the G.one drops off",
						By(LeftIdentityOn, group, y)),
				))
		}),
})}

// InvMulCancelLeft — InvMulCancelLeftOn on the whole type.
var InvMulCancelLeft = invMulCancelLeftThm{family.Add(registry.ProofEntry{
	Name:  "InvMulCancelLeft",
	Key:   "prop_99c3a827f771fdc3",
	Build: GroupAtUniverse.Law("∀x y:A. G.inv(x) * (x * y) = y", InvMulCancelLeftOn),
})}

// IdempotentIsOneOn — an element of the carrier equal to its own square
// is the identity: e is what inv(e) leaves of e * e, and e * e is e, and
// inv(e) * e is one.
var IdempotentIsOneOn = idempotentIsOneOnThm{family.Add(registry.ProofEntry{
	Name: "IdempotentIsOneOn",
	Key:  "prop_f2b7dfb56ef04b9a",

	Build: GroupOn.Law(Statement{
		Binders: "∀e:A.",
		Hypotheses: []string{
			"e ∈ G.carrier",
			"e * e = e",
		},
		Conclusion: "e = G.one",
	},
		func(a *Argument, group GroupFact[on.G], e *Member[A, on.G], square Fact) {
			a.Show(
				"walk from e to G.one through G.inv(e) * (e * e)",
				CalcEq(
					Leg(
						a.TermAs[A]("G.inv(e) * (e * e)"),
						"e is what G.inv(e) leaves of e * e",
						By(InvMulCancelLeftOn, group, e)),
					Leg(
						a.TermAs[A]("G.inv(e) * e"),
						"the square is e",
						square.Rw(),
						Basic()),
					FinalLeg(
						"and G.inv(e) * e is G.one",
						By(LeftInverseOn, group, e)),
				))
		}),
})}

// IdempotentIsOne — IdempotentIsOneOn on the whole type.
var IdempotentIsOne = idempotentIsOneThm{family.Add(registry.ProofEntry{
	Name: "IdempotentIsOne",
	Key:  "prop_7abafdbb998625ad",
	Build: GroupAtUniverse.Law(Statement{
		Binders: "∀e:A.",
		Hypotheses: []string{
			"e * e = e",
		},
		Conclusion: "e = G.one",
	}, IdempotentIsOneOn),
})}

// RightInverseOn — the inverse from the right: x * inv(x) is its own
// square — inside the square, inv(x) undoes the x after it — and the
// identity is the only such element of the carrier.
var RightInverseOn = rightInverseOnThm{family.Add(registry.ProofEntry{
	Name: "RightInverseOn",
	Key:  "prop_2c5fd78cb0e41b4b",

	Build: GroupOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "x * G.inv(x) = G.one",
	},
		func(a *Argument, group GroupFact[on.G], x *Member[A, on.G]) {
			square := a.Have(
				"x * G.inv(x) is its own square",
				"(x * G.inv(x)) * (x * G.inv(x)) = x * G.inv(x)",
				CalcEq(
					Leg(
						a.TermAs[A]("x * (G.inv(x) * (x * G.inv(x)))"),
						"regroup, so G.inv(x) faces the second x",
						By(AssocOn, group, x, InvIn, MulIn)),
					FinalLeg(
						"which G.inv(x) undoes, leaving G.inv(x)",
						Simp(Fwd(InvMulCancelLeftOn), Fwd(InvIn)),
						Basic()),
				))
			a.Show(
				"so it is the identity",
				By(square, IdempotentIsOneOn, group, x, InvIn, MulIn))
		}),
})}

// RightInverse — RightInverseOn on the whole type.
var RightInverse = rightInverseThm{family.Add(registry.ProofEntry{
	Name:  "RightInverse",
	Key:   "prop_6a1a2a56fcebff27",
	Build: GroupAtUniverse.Law("∀x:A. x * G.inv(x) = G.one", RightInverseOn),
})}

// MulInvCancelLeftOn — and x undoes inv(x) from the left: the right
// inverse collapses the pair x * inv(x) as the left inverse collapsed the
// other.
var MulInvCancelLeftOn = mulInvCancelLeftOnThm{family.Add(registry.ProofEntry{
	Name: "MulInvCancelLeftOn",
	Key:  "prop_7b129f6bb6aca961",

	Build: GroupOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
		},
		Conclusion: "x * (G.inv(x) * y) = y",
	},
		func(a *Argument, group GroupFact[on.G], x, y *Member[A, on.G]) {
			a.Show(
				"regroup, collapse the inverse pair, drop the identity",
				CalcEq(
					Leg(
						a.TermAs[A]("(x * G.inv(x)) * y"),
						"regroup, so x meets its inverse",
						By(AssocOn, group, x, y, InvIn)),
					Leg(
						a.TermAs[A]("G.one * y"),
						"that pair collapses to G.one",
						Simp(Fwd(RightInverseOn)),
						Basic()),
					FinalLeg(
						"and the G.one drops off",
						By(LeftIdentityOn, group, y)),
				))
		}),
})}

// MulInvCancelLeft — MulInvCancelLeftOn on the whole type.
var MulInvCancelLeft = mulInvCancelLeftThm{family.Add(registry.ProofEntry{
	Name:  "MulInvCancelLeft",
	Key:   "prop_5d3ac6f271cdefa5",
	Build: GroupAtUniverse.Law("∀x y:A. x * (G.inv(x) * y) = y", MulInvCancelLeftOn),
})}

// RightIdentityOn — the identity from the right: write it as inv(x) * x,
// and x undoes the inv(x) in front.
var RightIdentityOn = rightIdentityOnThm{family.Add(registry.ProofEntry{
	Name: "RightIdentityOn",
	Key:  "prop_c079ccc450459a93",

	Build: GroupOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "x * G.one = x",
	},
		func(a *Argument, group GroupFact[on.G], x *Member[A, on.G]) {
			a.Show(
				"the G.one is G.inv(x) * x, and x undoes G.inv(x)",
				CalcEq(
					Leg(
						a.TermAs[A]("x * (G.inv(x) * x)"),
						"the G.one is G.inv(x) * x",
						Simp(Fwd(LeftInverseOn)),
						Basic()),
					FinalLeg(
						"which x undoes, leaving x",
						By(MulInvCancelLeftOn, group, x)),
				))
		}),
})}

// RightIdentity — RightIdentityOn on the whole type.
var RightIdentity = rightIdentityThm{family.Add(registry.ProofEntry{
	Name:  "RightIdentity",
	Key:   "prop_eb6df52bebe2486",
	Build: GroupAtUniverse.Law("∀x:A. x * G.one = x", RightIdentityOn),
})}

// MulInvCancelRightOn — inv(x) undoes x from the right: regroup, and the
// pair x * inv(x) collapses to the identity, which drops off.
var MulInvCancelRightOn = mulInvCancelRightOnThm{family.Add(registry.ProofEntry{
	Name: "MulInvCancelRightOn",
	Key:  "prop_d843cd0f31b56f12",

	Build: GroupOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
		},
		Conclusion: "y * x * G.inv(x) = y",
	},
		func(a *Argument, group GroupFact[on.G], x, y *Member[A, on.G]) {
			a.Show(
				"regroup, collapse the inverse pair, drop the identity",
				CalcEq(
					Leg(
						a.TermAs[A]("y * (x * G.inv(x))"),
						"regroup, so x meets its inverse",
						By(AssocOn, group, x, y, InvIn)),
					Leg(
						a.TermAs[A]("y * G.one"),
						"that pair collapses to G.one",
						Simp(Fwd(RightInverseOn)),
						Basic()),
					FinalLeg(
						"and the G.one drops off",
						By(RightIdentityOn, group, y)),
				))
		}),
})}

// InvMulCancelRightOn — x undoes inv(x) from the right: regroup, and the
// pair inv(x) * x collapses to the identity, which drops off.
var InvMulCancelRightOn = invMulCancelRightOnThm{family.Add(registry.ProofEntry{
	Name: "InvMulCancelRightOn",
	Key:  "prop_fff07b2fb2e10727",

	Build: GroupOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
		},
		Conclusion: "y * G.inv(x) * x = y",
	},
		func(a *Argument, group GroupFact[on.G], x, y *Member[A, on.G]) {
			a.Show(
				"regroup, collapse the inverse pair, drop the identity",
				CalcEq(
					Leg(
						a.TermAs[A]("y * (G.inv(x) * x)"),
						"regroup, so G.inv(x) meets x",
						By(AssocOn, group, x, y, InvIn)),
					Leg(
						a.TermAs[A]("y * G.one"),
						"that pair collapses to G.one",
						Simp(Fwd(LeftInverseOn)),
						Basic()),
					FinalLeg(
						"and the G.one drops off",
						By(RightIdentityOn, group, y)),
				))
		}),
})}

// ---------------------------------------------------------------------------
// Cancellation and the inverse
// ---------------------------------------------------------------------------

// MulInvCancelRight — MulInvCancelRightOn on the whole type.
var MulInvCancelRight = mulInvCancelRightThm{family.Add(registry.ProofEntry{
	Name:  "MulInvCancelRight",
	Key:   "prop_7d609a5b2987d79a",
	Build: GroupAtUniverse.Law("∀x y:A.(y * x) * G.inv(x) = y", MulInvCancelRightOn),
})}

// InvMulCancelRight — InvMulCancelRightOn on the whole type.
var InvMulCancelRight = invMulCancelRightThm{family.Add(registry.ProofEntry{
	Name:  "InvMulCancelRight",
	Key:   "prop_eadadc54803ebc3f",
	Build: GroupAtUniverse.Law("∀x y:A. y * G.inv(x) * x = y", InvMulCancelRightOn),
})}

// LeftCancelOn — multiplying by x on the left is injective on the
// carrier. The ⇐ direction is congruence; the ⇒ direction reads each
// factor back out: y is what inv(x) leaves of x * y, and z of x * z.
var LeftCancelOn = leftCancelOnThm{family.Add(registry.ProofEntry{
	Name: "LeftCancelOn",
	Key:  "prop_d0727d3b67bf5d11",

	Build: GroupOn.Law(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
			"z ∈ G.carrier",
		},
		Conclusion: "x * y = x * z ⇔ y = z",
	},
		func(a *Argument, group GroupFact[on.G], x, y, z *Member[A, on.G]) {
			a.Iff()
			a.Forward(
				"read each factor back out of its product with G.inv(x)",
				func(b *Argument, product Fact) {
					b.Show(
						"y is what G.inv(x) leaves of x * y, which is x * z, of which it leaves z",
						CalcEq(
							Leg(
								b.TermAs[A]("G.inv(x) * (x * y)"),
								"y is what G.inv(x) leaves of x * y",
								By(InvMulCancelLeftOn, group, x, y)),
							Leg(
								b.TermAs[A]("G.inv(x) * (x * z)"),
								"the hypothesis, under G.inv(x) * ·",
								product.Rw(),
								Basic()),
							FinalLeg(
								"which leaves z",
								By(InvMulCancelLeftOn, group, x, z)),
						))
				})
			a.Backward(
				"y and z are the same element, so x * y and x * z are the same product",
				func(b *Argument, eq Fact) {
					b.Do(eq.Rw(), Basic())
				})
		}),
})}

// LeftCancel — LeftCancelOn on the whole type.
var LeftCancel = leftCancelThm{family.Add(registry.ProofEntry{
	Name:  "LeftCancel",
	Key:   "prop_1c4c2f082bfeb277",
	Build: GroupAtUniverse.Law("∀x y z:A. x * y = x * z ⇔ y = z", LeftCancelOn),
})}

// RightCancelOn — multiplying by x on the right is injective on the
// carrier: the mirror of LeftCancelOn, with inv(x) multiplied on the
// right. The group is not commutative, so the mirror is a second
// argument, not a reading of the first.
var RightCancelOn = rightCancelOnThm{family.Add(registry.ProofEntry{
	Name: "RightCancelOn",
	Key:  "prop_ae236485c3ebd996",

	Build: GroupOn.Law(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
			"z ∈ G.carrier",
		},
		Conclusion: "y * x = z * x ⇔ y = z",
	},
		func(a *Argument, group GroupFact[on.G], x, y, z *Member[A, on.G]) {
			a.Iff()
			a.Forward(
				"read each factor back out of its product with G.inv(x)",
				func(b *Argument, product Fact) {
					b.Show(
						"y is what G.inv(x) leaves of y * x, which is z * x, of which it leaves z",
						CalcEq(
							Leg(
								b.TermAs[A]("(y * x) * G.inv(x)"),
								"y is what G.inv(x) leaves of y * x",
								By(MulInvCancelRightOn, group, x, y)),
							Leg(
								b.TermAs[A]("(z * x) * G.inv(x)"),
								"the hypothesis, under · * G.inv(x)",
								product.Rw(),
								Basic()),
							FinalLeg(
								"which leaves z",
								By(MulInvCancelRightOn, group, x, z)),
						))
				})
			a.Backward(
				"y and z are the same element, so y * x and z * x are the same product",
				func(b *Argument, eq Fact) {
					b.Do(eq.Rw(), Basic())
				})
		}),
})}

// RightCancel — RightCancelOn on the whole type.
var RightCancel = rightCancelThm{family.Add(registry.ProofEntry{
	Name:  "RightCancel",
	Key:   "prop_5d507083b735d47a",
	Build: GroupAtUniverse.Law("∀x y z:A. y * x = z * x ⇔ y = z", RightCancelOn),
})}

// InvUniqueOn — the inverse is the only left inverse in the carrier: a
// factor whose product with y is one is already inv(y).
//
// The ⇐ direction is the left-inverse axiom read at y. The ⇒ direction
// reads x back out of x * y = one with inv(y) on the right, leaving
// one * inv(y), which is inv(y).
var InvUniqueOn = invUniqueOnThm{family.Add(registry.ProofEntry{
	Name: "InvUniqueOn",
	Key:  "prop_56ec669abbde31a8",

	Build: GroupOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
		},
		Conclusion: "x * y = G.one ⇔ x = G.inv(y)",
	},
		func(a *Argument, group GroupFact[on.G], x, y *Member[A, on.G]) {
			a.Iff()
			a.Forward(
				"read x back out of x * y = G.one with G.inv(y) on the right",
				func(b *Argument, product Fact) {
					b.Show(
						"x is what G.inv(y) leaves of x * y, which is G.one",
						CalcEq(
							Leg(
								b.TermAs[A]("(x * y) * G.inv(y)"),
								"x is what G.inv(y) leaves of x * y",
								By(MulInvCancelRightOn, group, x, y)),
							Leg(
								b.TermAs[A]("G.one * G.inv(y)"),
								"the hypothesis, under · * G.inv(y)",
								product.Rw(),
								Basic()),
							FinalLeg(
								"and the leading G.one drops off G.inv(y)",
								By(LeftIdentityOn, group, y, InvIn)),
						))
				})
			a.Backward(
				"x is G.inv(y), so the product is the inverse pair G.inv(y) * y",
				func(b *Argument, eq Fact) {
					b.Do(eq.Rw())
					b.Show(
						"the left inverse sends G.inv(y) * y to G.one",
						By(LeftInverseOn, group, y))
				})
		}),
})}

// InvUnique — InvUniqueOn on the whole type.
var InvUnique = invUniqueThm{family.Add(registry.ProofEntry{
	Name:  "InvUnique",
	Key:   "prop_abfb93391b1ed8c7",
	Build: GroupAtUniverse.Law("∀x y:A. x * y = G.one ⇔ x = G.inv(y)", InvUniqueOn),
})}

// InvMulEqOneOn — two elements of the carrier are one element exactly
// when the first's inverse times the second is the identity.
//
// The ⇐ direction is the left-inverse axiom read at y. The ⇒ direction
// reads y back out of inv(x) * y with x on the left, which leaves x once
// the product is one.
var InvMulEqOneOn = invMulEqOneOnThm{family.Add(registry.ProofEntry{
	Name: "InvMulEqOneOn",
	Key:  "prop_b4af01b41db06b3",

	Build: GroupOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
		},
		Conclusion: "G.inv(x) * y = G.one ⇔ x = y",
	},
		func(a *Argument, group GroupFact[on.G], x, y *Member[A, on.G]) {
			a.Iff()
			a.Forward(
				"read y back out of G.inv(x) * y = G.one with x on the left",
				func(b *Argument, product Fact) {
					b.Show(
						"x is x * G.one, the product is G.one, and x undoes G.inv(x), leaving y",
						CalcEq(
							Leg(
								b.TermAs[A]("x * G.one"),
								"G.one drops off x * G.one",
								By(RightIdentityOn, group, x)),
							Leg(
								b.TermAs[A]("x * (G.inv(x) * y)"),
								"the hypothesis, under x * ·",
								product.Rw(),
								Basic()),
							FinalLeg(
								"and x undoes G.inv(x) from the left",
								By(MulInvCancelLeftOn, group, x, y)),
						))
				})
			a.Backward(
				"x is y, so the product is the inverse pair G.inv(y) * y",
				func(b *Argument, eq Fact) {
					b.Do(eq.Rw())
					b.Show(
						"the left inverse sends G.inv(y) * y to G.one",
						By(LeftInverseOn, group, y))
				})
		}),
})}

// InvMulEqOne — InvMulEqOneOn on the whole type.
var InvMulEqOne = invMulEqOneThm{family.Add(registry.ProofEntry{
	Name:  "InvMulEqOne",
	Key:   "prop_7770fb5bebc3c86",
	Build: GroupAtUniverse.Law("∀x y:A. G.inv(x) * y = G.one ⇔ x = y", InvMulEqOneOn),
})}

// InvInvOn — inversion is an involution on the carrier: x is a left
// inverse of inv(x), and the inverse is unique, so x is the inverse of
// inv(x).
var InvInvOn = invInvOnThm{family.Add(registry.ProofEntry{
	Name: "InvInvOn",
	Key:  "prop_689c9607b169feb",

	Build: GroupOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "G.inv(G.inv(x)) = x",
	},
		func(a *Argument, group GroupFact[on.G], x *Member[A, on.G]) {
			leftInverse := a.Have(
				"x is a left inverse of G.inv(x)",
				"x * G.inv(x) = G.one",
				By(RightInverseOn, group, x))
			a.Show(
				"so x is the inverse of G.inv(x)",
				By(leftInverse, InvUniqueOn, group, x, InvIn))
		}),
})}

// InvInv — InvInvOn on the whole type.
var InvInv = invInvThm{family.Add(registry.ProofEntry{
	Name:  "InvInv",
	Key:   "prop_ee488c09d40bf2ee",
	Build: GroupAtUniverse.Law("∀x:A. G.inv(G.inv(x)) = x", InvInvOn),
})}

// InvMulOn — the inverse of a product is the product of the inverses in
// the other order: inv(y) * inv(x) is a left inverse of x * y — laid
// against x * y, inv(x) undoes x and then inv(y) meets y — and the
// inverse is unique.
var InvMulOn = invMulOnThm{family.Add(registry.ProofEntry{
	Name: "InvMulOn",
	Key:  "prop_83d550c73347ae2a",

	Build: GroupOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
		},
		Conclusion: "G.inv(x * y) = G.inv(y) * G.inv(x)",
	},
		func(a *Argument, group GroupFact[on.G], x, y *Member[A, on.G]) {
			leftInverse := a.Have(
				"G.inv(y) * G.inv(x) tested against x * y: the product is G.one",
				"(G.inv(y) * G.inv(x)) * (x * y) = G.one",
				CalcEq(
					Leg(
						a.TermAs[A]("G.inv(y) * (G.inv(x) * (x * y))"),
						"regroup, so G.inv(x) faces x * y",
						By(AssocOn, group, x, y, InvIn, MulIn)),
					Leg(
						a.TermAs[A]("G.inv(y) * y"),
						"G.inv(x) undoes x, leaving y",
						Simp(Fwd(InvMulCancelLeftOn)),
						Basic()),
					FinalLeg(
						"and G.inv(y) * y is G.one",
						By(LeftInverseOn, group, y)),
				))
			a.Show(
				"uniqueness of the inverse: a left inverse of x * y is G.inv(x * y)",
				By(leftInverse, InvUniqueOn, group, x, y, InvIn, MulIn))
		}),
})}

// InvMul — InvMulOn on the whole type.
var InvMul = invMulThm{family.Add(registry.ProofEntry{
	Name:  "InvMul",
	Key:   "prop_56a4a666eec49531",
	Build: GroupAtUniverse.Law("∀x y:A. G.inv(x * y) = G.inv(y) * G.inv(x)", InvMulOn),
})}

// InvOneOn — the identity is its own inverse: one times one is one, and
// the inverse is unique. The statement binds nothing, so it carries no
// guard; the identity's membership is the carrier's own axiom.
var InvOneOn = invOneOnThm{family.Add(registry.ProofEntry{
	Name: "InvOneOn",
	Key:  "prop_b47c681163c5b11a",

	Build: GroupOn.Law("G.inv(G.one) = G.one",
		func(a *Argument, group GroupFact[on.G]) {
			doubled := a.Have(
				"G.one beside itself is G.one",
				"G.one * G.one = G.one",
				By(LeftIdentityOn, group, OneIn))
			a.Show(
				"so G.one is the inverse of G.one",
				By(doubled, InvUniqueOn, group, OneIn))
		}),
})}

// InvOne — InvOneOn on the whole type.
var InvOne = invOneThm{family.Add(registry.ProofEntry{
	Name:  "InvOne",
	Key:   "prop_5a121c10887ba8ad",
	Build: GroupAtUniverse.Law("G.inv(G.one) = G.one", InvOneOn),
})}
