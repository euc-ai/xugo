// comm_ring.go — the chapter: a commutative ring with one, and the ring
// on a set.
//
// Every law of the ring is proved once, on a carrier set c, and stated
// beside it on the whole type as the view of that proof
// (CommRingAtUniverse; constitution §Structures, "One proof per law").
// The three projections onto the additive group and the two monoids are
// axioms or laws of each form; the fold laws stay on the whole type,
// where the fold lives, and the alternating-sign laws on the carrier,
// where every reader states them.

package comm_ring

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structures and their axioms
// ---------------------------------------------------------------------------

// CommRing — a commutative ring on the whole type, using the operations
// held in R. Its carrier field does not restrict these axioms.
var CommRing = commRingThm{family.DefineStructure(registry.DefEntry{
	Name: "CommRing", Key: "prop_276edb7f107a56c6", Const: "comm_ring", Subject: "R",
	Type: "ring_ops(A) → bool",
	Equations: []string{"∀R:ring_ops(A). " +
		"    comm_ring(R) ⇔ " +
		"    abelian_group(additive_group(R)) ∧ " +
		"    comm_monoid(R.mul, R.one) ∧ " +
		"    (∀x y z:A. R.mul(x, R.add(y, z)) = R.add(R.mul(x, y), R.mul(x, z))) ∧ " +
		"    (∀x y:A. R.sub(x, y) = R.add(x, R.neg(y)))"},
})}

// CommRingOn — a ring's additive group and multiplicative monoid,
// distributivity, and subtraction as addition of the negation.
var CommRingOn = commRingOnThm{family.DefineStructure(registry.DefEntry{
	Name:  "CommRingOn",
	Key:   "prop_d6dc515bf8a5092c",
	Const: "comm_ring_on", Subject: "R",
	Type: "ring_ops(A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"    comm_ring_on(R) ⇔ " +
			"    abelian_group_on(additive_group(R)) ∧ " +
			"    comm_monoid_on(R.carrier, R.mul, R.one) ∧ " +
			"    (∀x y z:A. " +
			"        x ∈ R.carrier ∧ y ∈ R.carrier ∧ z ∈ R.carrier ⇒ " +
			"        R.mul(x, R.add(y, z)) = R.add(R.mul(x, y), R.mul(x, z))) ∧ " +
			"    (∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ⇒ R.sub(x, y) = R.add(x, R.neg(y)))",
	},
})}

// CharacteristicZeroDef — no positive natural multiple of one vanishes.
var CharacteristicZeroDef = characteristicZeroDefThm{family.Define(registry.DefEntry{
	Name:  "CharacteristicZeroDef",
	Key:   "prop_68709e14740ad5f0",
	Deps:  []registry.EntryLike{},
	Const: "characteristic_zero",
	Type:  "ring_ops(A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"    characteristic_zero(R) ⇔ (∀n:num. 0 < n ⇒ monoid_pow(R.add, R.zero, R.one, n) ≠ R.zero)",
	},
})}

// CommRingOnUniverse — a ring on the whole type is the carrier ring
// obtained by retaining its operations and replacing its carrier by 𝕌.
var CommRingOnUniverse = commRingOnUniverseThm{family.Add(registry.ProofEntry{
	Name: "CommRingOnUniverse", Key: "prop_f6dc7a8fdd02a70b",
	Build: family.Theorem("∀R:ring_ops(A). comm_ring(R) ⇔ comm_ring_on(restrict_ring(R, 𝕌))",
		func(a *Argument, R *Expr[RingOps[A]]) {
			a.Show(
				"the two sub-structure conjuncts are their whole-type forms, and the two laws lose their guards",
				Unfold(CommRing),
				Unfold(CommRingOn),
				Simp(
					Fwd(module_record.AdditiveGroupDef),
					Fwd(module_record.RestrictRingDef),
					Fwd(abelian_group.AbelianGroupOnUniverse),
					Fwd(group.RestrictGroupDef),
					Fwd(comm_monoid.CommMonoidOnUniverse),
					Fwd(set_basic.InUniv)),
				Basic())
		}),
})}

// CommRingAtUniverse — the whole-type view of a law proved on the carrier.
var CommRingAtUniverse = CommRing.AtUniverseRecord(
	CommRingOn, CommRingOnUniverse, "restrict_ring(R, 𝕌)", set_basic.InUniv)

// AddGroup — the additive structure is an abelian group.
var AddGroup = addGroupThm{family.Add(registry.ProofEntry{
	Name:  "AddGroup",
	Key:   "prop_52fb09f39e581b56",
	Build: CommRing.Axiom("abelian_group(additive_group(R))"),
})}

// AddGroupOn — the additive structure on c is an abelian group on c.
var AddGroupOn = addGroupOnThm{family.Add(registry.ProofEntry{
	Name:  "AddGroupOn",
	Key:   "prop_b0b34b5cc5653cb0",
	Build: CommRingOn.Axiom("abelian_group_on(additive_group(R))"),
})}

// AddMonoid — the additive structure's operation and identity form a
// commutative monoid: the group's own projection, stated once at the
// ring so that a consumer of an additive-monoid law at a ring cites one
// fact rather than chaining the two projections.
var AddMonoid = addMonoidThm{family.Add(registry.ProofEntry{
	Name: "AddMonoid",
	Key:  "prop_1a330e1670587b53",
	Build: CommRing.Law("comm_monoid(R.add, R.zero)",
		func(a *Argument, ring Fact) {
			a.Show(
				"the additive group's monoid",
				By(Read(abelian_group.Monoid, Read(AddGroup, ring))))
		}),
})}

// AddMonoidOn — the additive structure on c as a commutative monoid on
// c: the abelian group's own projection, stated once at the ring.
var AddMonoidOn = addMonoidOnThm{family.Add(registry.ProofEntry{
	Name: "AddMonoidOn",
	Key:  "prop_e8afa8a5ef87d42a",
	Build: CommRingOn.Law("comm_monoid_on(R.carrier, R.add, R.zero)",
		func(a *Argument, ring CommRingFact[on.R]) {
			a.Show(
				"the additive group's monoid",
				By(Read(abelian_group.MonoidOn, Read(AddGroupOn, ring))))
		}),
})}

// MulMonoid — the multiplicative structure is a commutative monoid.
var MulMonoid = mulMonoidThm{family.Add(registry.ProofEntry{
	Name:  "MulMonoid",
	Key:   "prop_f28face7cf44c9ac",
	Build: CommRing.Axiom("comm_monoid(R.mul, R.one)"),
})}

// MulMonoidOn — the multiplicative structure on c is a commutative
// monoid on c.
var MulMonoidOn = mulMonoidOnThm{family.Add(registry.ProofEntry{
	Name:  "MulMonoidOn",
	Key:   "prop_7ce07cddc27cf98f",
	Build: CommRingOn.Axiom("comm_monoid_on(R.carrier, R.mul, R.one)"),
})}

// The ring's closure laws, read through its two sub-structures: what a
// proof names beside a law asking a formed term's membership, so the
// rung decides it from the ring fact alone.

// ZeroIn — zero lies in the carrier.
var ZeroIn = zeroInThm{family.Add(registry.ProofEntry{
	Name: "ZeroIn",
	Key:  "prop_f498000d04e9e29f",
	Build: CommRingOn.Law("R.zero ∈ R.carrier",
		func(a *Argument, ring CommRingFact[on.R]) {
			a.Show(
				"the additive group's identity",
				By(Read(group.OneIn, Read(abelian_group.GroupOn, Read(AddGroupOn, ring)))))
		}),
})}

// AddIn — the carrier is closed under the sum.
var AddIn = addInThm{family.Add(registry.ProofEntry{
	Name: "AddIn",
	Key:  "prop_a12b7ae060db7a01",
	Build: CommRingOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
		},
		Conclusion: "x + y ∈ R.carrier",
	},
		func(a *Argument, ring CommRingFact[on.R]) {
			a.Show(
				"the additive group's closure",
				By(Read(group.MulIn, Read(abelian_group.GroupOn, Read(AddGroupOn, ring)))))
		}),
})}

// NegIn — the carrier is closed under the negation.
var NegIn = negInThm{family.Add(registry.ProofEntry{
	Name: "NegIn",
	Key:  "prop_3f4b5045b1d0a9df",
	Build: CommRingOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
		},
		Conclusion: "-x ∈ R.carrier",
	},
		func(a *Argument, ring CommRingFact[on.R]) {
			a.Show(
				"the additive group's closure under the inverse",
				By(Read(group.InvIn, Read(abelian_group.GroupOn, Read(AddGroupOn, ring)))))
		}),
})}

// OneIn — one lies in the carrier.
var OneIn = oneInThm{family.Add(registry.ProofEntry{
	Name: "OneIn",
	Key:  "prop_c137647e7e0be73",
	Build: CommRingOn.Law("R.one ∈ R.carrier",
		func(a *Argument, ring CommRingFact[on.R]) {
			a.Show(
				"the multiplicative monoid's identity",
				By(Read(comm_monoid.IdentityIn, Read(MulMonoidOn, ring))))
		}),
})}

// MulIn — the carrier is closed under the product.
var MulIn = mulInThm{family.Add(registry.ProofEntry{
	Name: "MulIn",
	Key:  "prop_fa5fe4640b31b4da",
	Build: CommRingOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
		},
		Conclusion: "x * y ∈ R.carrier",
	},
		func(a *Argument, ring CommRingFact[on.R]) {
			a.Show(
				"the multiplicative monoid's closure",
				By(Read(comm_monoid.OpIn, Read(MulMonoidOn, ring))))
		}),
})}

// SubIn — the carrier is closed under the difference: x - y is x + -y.
var SubIn = subInThm{family.Add(registry.ProofEntry{
	Name: "SubIn",
	Key:  "prop_b54748323e77b5f7",
	Build: CommRingOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
		},
		Conclusion: "x - y ∈ R.carrier",
	},
		func(a *Argument, ring CommRingFact[on.R], x, y *Member[A, on.R]) {
			a.Show(
				"x - y is x + -y, a sum of members",
				Simp(Fwd(SubAddNegOn.Read(ring))),
				By(AddIn.Read(ring), NegIn.Read(ring), x, y))
		}),
})}

// ClosedSubsetRingOn — a subset of the carrier holding zero and one and
// closed under the sum, the negation and the product is a ring on its own
// set: each axiom on T is the axiom on c read at members of T, and the
// closure conditions are the hypotheses.
var ClosedSubsetRingOn = closedSubsetRingOnThm{family.Add(registry.ProofEntry{
	Name: "ClosedSubsetRingOn",
	Key:  "prop_6ca55f22feb34523",
	Build: CommRingOn.Law(Statement{
		Binders: "∀T:set(A).",
		Hypotheses: []string{
			"T ⊆ R.carrier",
			"R.zero ∈ T",
			"∀x y:A. x ∈ T ∧ y ∈ T ⇒ x + y ∈ T",
			"∀x:A. x ∈ T ⇒ -x ∈ T",
			"R.one ∈ T",
			"∀x y:A. x ∈ T ∧ y ∈ T ⇒ x * y ∈ T",
		},
		Conclusion: "comm_ring_on(restrict_ring(R, T))",
	},
		func(a *Argument, ring CommRingFact[on.R], T *Expr[Set[A]], closed Fact) {
			parts := a.Conjuncts(
				closed,
				"T lies in c",
				"T holds zero",
				"T is closed under the sum",
				"and under the negation",
				"T holds one",
				"and T is closed under the product")
			inC := a.Unfolded(parts[0], set_basic.SubsetDef)
			abelian := AddGroupOn.Read(ring)
			additive := abelian_group.GroupOn.Read(abelian)
			multiplicative := MulMonoidOn.Read(ring)
			// Each axiom on T is had before comm_ring_on(T) is unfolded: the
			// unfolding opens the ring on c as well.
			addAssoc := a.Have(
				"the sum associates on T",
				"∀x y z:A. x ∈ T ∧ y ∈ T ∧ z ∈ T ⇒ x + (y + z) = x + y + z",
				By(group.AssocOn.Read(additive), inC))
			addZero := a.Have(
				"zero is a left identity on T",
				"∀x:A. x ∈ T ⇒ R.zero + x = x",
				By(group.LeftIdentityOn.Read(additive), inC))
			addNeg := a.Have(
				"-x is a left inverse of x on T",
				"∀x:A. x ∈ T ⇒ -x + x = R.zero",
				By(group.LeftInverseOn.Read(additive), inC))
			addComm := a.Have(
				"the sum commutes on T",
				"∀x y:A. x ∈ T ∧ y ∈ T ⇒ x + y = y + x",
				By(abelian_group.CommOn.Read(abelian), inC))
			mulAssoc := a.Have(
				"the product associates on T",
				"∀x y z:A. x ∈ T ∧ y ∈ T ∧ z ∈ T ⇒ x * (y * z) = x * y * z",
				By(comm_monoid.AssocOn.Read(multiplicative), inC))
			mulOne := a.Have(
				"one is a left identity on T",
				"∀x:A. x ∈ T ⇒ R.one * x = x",
				By(comm_monoid.LeftIdentityOn.Read(multiplicative), inC))
			mulComm := a.Have(
				"the product commutes on T",
				"∀x y:A. x ∈ T ∧ y ∈ T ⇒ x * y = y * x",
				By(comm_monoid.CommOn.Read(multiplicative), inC))
			distributes := a.Have(
				"the product distributes over the sum on T",
				"∀x y z:A. x ∈ T ∧ y ∈ T ∧ z ∈ T ⇒ x * (y + z) = x * y + x * z",
				By(LeftDistribOn.Read(ring), inC))
			subtraction := a.Have(
				"the difference is the sum with the negation on T",
				"∀x y:A. x ∈ T ∧ y ∈ T ⇒ x - y = x + -y",
				By(SubAddNegOn.Read(ring), inC))
			a.Show(
				"so T is a ring on its own set: unfolded, comm_ring_on(T) "+
					"asks T's closure conditions and these nine axioms",
				Unfold(CommRingOn),
				Unfold(abelian_group.AbelianGroupOn),
				Unfold(group.GroupOn),
				Unfold(comm_monoid.CommMonoidOn),
				By(
					parts[1],
					parts[2],
					parts[3],
					parts[4],
					parts[5],
					addAssoc,
					addZero,
					addNeg,
					addComm,
					mulAssoc,
					mulOne,
					mulComm,
					distributes,
					subtraction))
		}),
})}

// LeftDistribOn — multiplication distributes over addition, from the
// left; the right-handed law is commutativity's to give.
var LeftDistribOn = leftDistribOnThm{family.Add(registry.ProofEntry{
	Name: "LeftDistribOn",
	Key:  "prop_b3bac3732c7df305",
	Build: CommRingOn.Axiom(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
			"z ∈ R.carrier",
		},
		Conclusion: "x * (y + z) = x * y + x * z",
	}),
})}

// LeftDistrib — LeftDistribOn on the whole type.
var LeftDistrib = leftDistribThm{family.Add(registry.ProofEntry{
	Name:  "LeftDistrib",
	Key:   "prop_be271bb774435072",
	Build: CommRingAtUniverse.Law("∀x y z:A. x * (y + z) = x * y + x * z", LeftDistribOn),
})}

// SubAddNegOn — subtraction is addition of the negation: the ring's own
// spelling of the difference, so that a difference on any carrier reads
// through the additive group.
var SubAddNegOn = subAddNegOnThm{family.Add(registry.ProofEntry{
	Name: "SubAddNegOn",
	Key:  "prop_2e344404a7936063",
	Build: CommRingOn.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
		},
		Conclusion: "x - y = x + -y",
	}),
})}

// SubAddNeg — SubAddNegOn on the whole type.
var SubAddNeg = subAddNegThm{family.Add(registry.ProofEntry{
	Name:  "SubAddNeg",
	Key:   "prop_30802dcad1e5d29a",
	Build: CommRingAtUniverse.Law("∀x y:A. x - y = x + -y", SubAddNegOn),
})}

// ---------------------------------------------------------------------------
// What the two operations say to each other
// ---------------------------------------------------------------------------

// Every proof here works on the carrier: the two monoids on c are had
// as facts, so that a term the argument forms — a sum, a product, a
// negation — lies in c by their closure axioms, named where a law asks.

// RightDistribOn — commutativity carries the left-handed law to the
// right: the whole product swings around, the left-handed law fires
// once, and each summand swings back.
var RightDistribOn = rightDistribOnThm{family.Add(registry.ProofEntry{
	Name: "RightDistribOn",
	Key:  "prop_1c081c9b621627f5",
	Build: CommRingOn.Law(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
			"z ∈ R.carrier",
		},
		Conclusion: "(x + y) * z = x * z + y * z",
	},
		func(a *Argument, ring CommRingFact[on.R], x, y, z *Member[A, on.R]) {
			addMonoid := a.Have(
				"the additive monoid on c",
				"comm_monoid_on(R.carrier, R.add, R.zero)",
				By(AddMonoidOn, ring))
			commute := Read(comm_monoid.CommOn, Read(MulMonoidOn, ring))
			swing := a.Have(
				"the product swings around",
				"(x + y) * z = z * (x + y)",
				By(commute, x, y, z, addMonoid, comm_monoid.OpIn))
			left := a.Have(
				"z * x is x * z",
				"z * x = x * z",
				By(commute, x, y, z))
			right := a.Have(
				"and z * y is y * z",
				"z * y = y * z",
				By(commute, x, y, z))
			a.Show(
				"swing the product around, distribute on the left, swing each summand back",
				swing.Rw(),
				Simp(Fwd(LeftDistribOn)),
				left.Rw(),
				right.Rw(),
				Basic())
		}),
})}

// RightDistrib — RightDistribOn on the whole type.
var RightDistrib = rightDistribThm{family.Add(registry.ProofEntry{
	Name:  "RightDistrib",
	Key:   "prop_e26f66d466427c83",
	Build: CommRingAtUniverse.Law("∀x y z:A. (x + y) * z = x * z + y * z", RightDistribOn),
})}

// MulLeftZero — zero absorbs on the left. Distributivity links the two
// operations: x under the sum zero + zero is mul(zero, x) added to
// itself, and it is also mul(zero, x) alone, so mul(zero, x) is a
// summand that can be added without moving anything — the additive
// identity, which left-cancellation reads back out.
// MulLeftZeroOn — zero absorbs multiplication from the left.
var MulLeftZeroOn = mulLeftZeroOnThm{family.Add(registry.ProofEntry{
	Name: "MulLeftZeroOn",
	Key:  "prop_4fab5b63d84423f",
	Build: CommRingOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
		},
		Conclusion: "R.zero * x = R.zero",
	},
		func(a *Argument, ring CommRingFact[on.R], x *Member[A, on.R]) {
			abelian := a.Have(
				"the additive structure on c is an abelian group on c",
				"abelian_group_on(additive_group(R))",
				By(AddGroupOn, ring))
			addMonoid := a.Have(
				"whose operation and identity form a commutative monoid on c, whose laws the chain rewrites by",
				"comm_monoid_on(R.carrier, R.add, R.zero)",
				By(AddMonoidOn, ring))
			mulMonoid := a.Have(
				"and the multiplicative monoid on c, whose closure keeps the products in c",
				"comm_monoid_on(R.carrier, R.mul, R.one)",
				By(MulMonoidOn, ring))
			doubled := a.Have(
				"adding R.zero * x to itself does the same as adding R.zero to it",
				"R.zero * x + R.zero * x = R.zero * x + R.zero",
				CalcEq(
					Leg(
						a.TermAs[A]("(R.zero + R.zero) * x"),
						"distributivity backwards: the two copies are x under the sum zero + zero",
						Simp(Rev(RightDistribOn), Fwd(comm_monoid.IdentityIn)),
						Basic()),
					Leg(
						a.TermAs[A]("R.zero * x"),
						"the inner sum collapses: zero + zero is zero",
						Simp(Fwd(comm_monoid.LeftIdentityOn), Fwd(comm_monoid.IdentityIn)),
						Basic()),
					FinalLeg(
						"and re-attaching a zero on the right changes nothing",
						Simp(Fwd(comm_monoid.RightIdentityOn), Fwd(comm_monoid.OpIn), Fwd(comm_monoid.IdentityIn)),
						Basic()),
				))
			product := a.TermAs[A]("R.zero * x")
			a.Show(
				"cancel the common zero * x on the left: the two right-hand summands must agree",
				By(
					doubled,
					Read(group.LeftCancelOn, Read(abelian_group.GroupOn, abelian)).At(
						product, product, a.TermAs[A]("R.zero")),
					x,
					mulMonoid,
					comm_monoid.OpIn,
					addMonoid,
					comm_monoid.IdentityIn))
		}),
})}

// MulLeftZero — MulLeftZeroOn on the whole type.
var MulLeftZero = mulLeftZeroThm{family.Add(registry.ProofEntry{
	Name:  "MulLeftZero",
	Key:   "prop_42a21eb65d29314",
	Build: CommRingAtUniverse.Law("∀x:A. R.zero * x = R.zero", MulLeftZeroOn),
})}

// MulLeftNeg — a negation passes out of a product on the left. In the
// additive group the inverse is characterised by what it annihilates,
// so mul(neg(x), y) is neg(mul(x, y)) as soon as the two products sum
// to zero — and they do: distributivity gathers them into a single
// product whose left factor is the inverse pair add(neg(x), x), which
// is zero, and zero absorbs.
// MulLeftNegOn — a negation passes out of a product from the left.
var MulLeftNegOn = mulLeftNegOnThm{family.Add(registry.ProofEntry{
	Name: "MulLeftNegOn",
	Key:  "prop_e3ba3e9abaa078cc",
	Build: CommRingOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
		},
		Conclusion: "-x * y = -(x * y)",
	},
		func(a *Argument, ring CommRingFact[on.R], x, y *Member[A, on.R]) {
			// The group on c is read as a value, never made resident: its
			// `*` would meet the ring's.
			additive := Read(abelian_group.GroupOn, Read(AddGroupOn, ring))
			mulMonoid := a.Have(
				"the multiplicative monoid on c",
				"comm_monoid_on(R.carrier, R.mul, R.one)",
				By(MulMonoidOn, ring))
			vanishes := a.Have(
				"the two products cancel each other",
				"-x * y + x * y = R.zero",
				CalcEq(
					Leg(
						a.TermAs[A]("(-x + x) * y"),
						"distributivity backwards: the two products share the factor y",
						Simp(Rev(RightDistribOn), Fwd(group.InvIn.Read(additive))),
						Basic()),
					Leg(
						a.TermAs[A]("R.zero * y"),
						"and the left factor is the inverse pair, which is zero",
						Simp(Fwd(group.LeftInverseOn.Read(additive))),
						Basic()),
					FinalLeg(
						"zero absorbs on the left",
						By(MulLeftZeroOn, ring, x, y)),
				))
			a.Show(
				"a summand that cancels x * y is its inverse",
				By(
					vanishes,
					group.InvUniqueOn.Read(additive),
					x,
					y,
					group.InvIn.Read(additive),
					mulMonoid,
					comm_monoid.OpIn))
		}),
})}

// MulLeftNeg — MulLeftNegOn on the whole type.
var MulLeftNeg = mulLeftNegThm{family.Add(registry.ProofEntry{
	Name:  "MulLeftNeg",
	Key:   "prop_55c6c3ae7158176c",
	Build: CommRingAtUniverse.Law("∀x y:A. -x * y = -(x * y)", MulLeftNegOn),
})}

// MulRightZero — and on the right: commutativity mirrors the law.
// MulRightZeroOn — zero absorbs multiplication from the right.
var MulRightZeroOn = mulRightZeroOnThm{family.Add(registry.ProofEntry{
	Name: "MulRightZeroOn",
	Key:  "prop_2a10ae2e9ffc320b",
	Build: CommRingOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
		},
		Conclusion: "x * R.zero = R.zero",
	},
		func(a *Argument, ring CommRingFact[on.R], x *Member[A, on.R]) {
			addMonoid := a.Have(
				"the additive monoid on c, whose identity lies in c",
				"comm_monoid_on(R.carrier, R.add, R.zero)",
				By(AddMonoidOn, ring))
			swap := a.Have(
				"the product commutes",
				"x * R.zero = R.zero * x",
				By(Read(comm_monoid.CommOn, Read(MulMonoidOn, ring)), x, addMonoid, comm_monoid.IdentityIn))
			a.Show(
				"so zero absorbs on the left",
				swap.Rw(),
				By(MulLeftZeroOn, ring, x))
		}),
})}

// MulRightZero — MulRightZeroOn on the whole type.
var MulRightZero = mulRightZeroThm{family.Add(registry.ProofEntry{
	Name:  "MulRightZero",
	Key:   "prop_2135ed96f7b1b211",
	Build: CommRingAtUniverse.Law("∀x:A. x * R.zero = R.zero", MulRightZeroOn),
})}

// MulRightNeg — a negation passes out of a product on the right, by
// commuting it to the left and back.
// MulRightNegOn — a negation passes out of a product from the right.
var MulRightNegOn = mulRightNegOnThm{family.Add(registry.ProofEntry{
	Name: "MulRightNegOn",
	Key:  "prop_288553dd1b2fe303",
	Build: CommRingOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
		},
		Conclusion: "x * -y = -(x * y)",
	},
		func(a *Argument, ring CommRingFact[on.R], x, y *Member[A, on.R]) {
			additive := Read(abelian_group.GroupOn, Read(AddGroupOn, ring))
			commute := Read(comm_monoid.CommOn, Read(MulMonoidOn, ring))
			swap := a.Have(
				"the product commutes",
				"x * -y = -y * x",
				By(commute, x, y, group.InvIn.Read(additive)))
			back := a.Have(
				"and so does the one under the negation",
				"y * x = x * y",
				By(commute, x, y))
			a.Show(
				"commute, pass the negation out on the left, commute back",
				swap.Rw(),
				Simp(Fwd(MulLeftNegOn)),
				back.Rw(),
				Basic())
		}),
})}

// MulRightNeg — MulRightNegOn on the whole type.
var MulRightNeg = mulRightNegThm{family.Add(registry.ProofEntry{
	Name:  "MulRightNeg",
	Key:   "prop_9ac75d8a30776a93",
	Build: CommRingAtUniverse.Law("∀x y:A. x * -y = -(x * y)", MulRightNegOn),
})}

// MulNegNeg — two negations in a product cancel: each passes out, and
// the inverse is an involution.
// MulNegNegOn — two negations in a product cancel.
var MulNegNegOn = mulNegNegOnThm{family.Add(registry.ProofEntry{
	Name: "MulNegNegOn",
	Key:  "prop_7f954e5ded40271b",
	Build: CommRingOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
		},
		Conclusion: "-x * -y = x * y",
	},
		func(a *Argument, ring CommRingFact[on.R], x, y *Member[A, on.R]) {
			additive := Read(abelian_group.GroupOn, Read(AddGroupOn, ring))
			a.Have(
				"the multiplicative monoid on c",
				"comm_monoid_on(R.carrier, R.mul, R.one)",
				By(MulMonoidOn, ring))
			a.Show(
				"pass both negations out of the product; they cancel",
				Simp(
					Fwd(MulLeftNegOn),
					Fwd(MulRightNegOn),
					Fwd(group.InvInvOn.Read(additive)),
					Fwd(group.InvIn.Read(additive)),
					Fwd(comm_monoid.OpIn)),
				Basic())
		}),
})}

// MulNegNeg — MulNegNegOn on the whole type.
var MulNegNeg = mulNegNegThm{family.Add(registry.ProofEntry{
	Name:  "MulNegNeg",
	Key:   "prop_7e9e56471796ea5",
	Build: CommRingAtUniverse.Law("∀x y:A. -x * -y = x * y", MulNegNegOn),
})}

// NegOneMul — negation is multiplication by the negative of one: the
// negation passes out of the product, leaving one times x.
// NegOneMulOn — multiplication by negative one negates.
var NegOneMulOn = negOneMulOnThm{family.Add(registry.ProofEntry{
	Name: "NegOneMulOn",
	Key:  "prop_3a6a9c2c9906bd8f",
	Build: CommRingOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
		},
		Conclusion: "-R.one * x = -x",
	},
		func(a *Argument, ring CommRingFact[on.R], x *Member[A, on.R]) {
			mulMonoid := a.Have(
				"the multiplicative monoid on c, whose identity lies in c",
				"comm_monoid_on(R.carrier, R.mul, R.one)",
				By(MulMonoidOn, ring))
			a.Show(
				"pass the negation out, then one is the identity",
				Simp(
					Fwd(MulLeftNegOn),
					Fwd(comm_monoid.LeftIdentityOn.Read(mulMonoid)),
					Fwd(comm_monoid.IdentityIn)),
				Basic())
		}),
})}

// NegOneMul — NegOneMulOn on the whole type.
var NegOneMul = negOneMulThm{family.Add(registry.ProofEntry{
	Name:  "NegOneMul",
	Key:   "prop_86580fd9f4b38a6b",
	Build: CommRingAtUniverse.Law("∀x:A. -R.one * x = -x", NegOneMulOn),
})}

// ---------------------------------------------------------------------------
// Powers of a negation
// ---------------------------------------------------------------------------
//
// The ring's power is its multiplicative monoid's
// (comm_monoid.MonoidPowDef), spelled with the ring's components: the
// short `x ^ n` reads `op` and `e`, and here they are `mul` and `one`.

// NegPowEven — an even power forgets the sign: (−x)²ⁿ = ((−x)²)ⁿ and
// x²ⁿ = (x²)ⁿ, and the two squares agree, (−x)·(−x) = x·x.
var NegPowEven = negPowEvenThm{family.Add(registry.ProofEntry{
	Name: "NegPowEven",
	Key:  "prop_1e45b078e2d6c75e",
	Build: CommRing.Law("∀x:A. ∀n:num. "+
		"    monoid_pow(R.mul, R.one, -x, 2 * n) = monoid_pow(R.mul, R.one, x, 2 * n)",
		func(a *Argument, ring Fact, x, n Term) {
			monoid := Read(MulMonoid, ring)
			negEven := a.Have(
				"(−x)²ⁿ is ((−x)²)ⁿ",
				"monoid_pow(R.mul, R.one, -x, 2 * n) = "+
					"monoid_pow(R.mul, R.one, monoid_pow(R.mul, R.one, -x, 2), n)",
				By(comm_monoid.PowPow.Read(monoid)))
			even := a.Have(
				"x²ⁿ is (x²)ⁿ",
				"monoid_pow(R.mul, R.one, x, 2 * n) = monoid_pow(R.mul, R.one, monoid_pow(R.mul, R.one, x, 2), n)",
				By(comm_monoid.PowPow.Read(monoid)))
			negTwo := a.Have(
				"(−x)² is (−x)·(−x)",
				"monoid_pow(R.mul, R.one, -x, 2) = -x * -x",
				By(comm_monoid.PowTwo.Read(monoid)))
			two := a.Have(
				"x² is x·x",
				"monoid_pow(R.mul, R.one, x, 2) = x * x",
				By(comm_monoid.PowTwo.Read(monoid)))
			square := a.Have(
				"and the two squares agree",
				"-x * -x = x * x",
				By(Read(MulNegNeg, ring)))
			a.Show(
				"both are the n-th power of one square",
				negEven.Rw(),
				even.Rw(),
				negTwo.Rw(),
				two.Rw(),
				square.Rw(),
				Basic())
		}),
})}

// NegPowOdd — an odd power keeps the sign: (−x)²ⁿ⁺¹ is −x times the even
// power, which forgets the sign, and the negation passes out of the
// product.
var NegPowOdd = negPowOddThm{family.Add(registry.ProofEntry{
	Name: "NegPowOdd",
	Key:  "prop_d07d0cbb52773b17",
	Build: CommRing.Law("∀x:A. ∀n:num. "+
		"    monoid_pow(R.mul, R.one, -x, 2 * n + 1) = -monoid_pow(R.mul, R.one, x, 2 * n + 1)",
		func(a *Argument, ring Fact, x, n Term) {
			negOdd := a.Have(
				"(−x)²ⁿ⁺¹ is −x times (−x)²ⁿ",
				"monoid_pow(R.mul, R.one, -x, 2 * n + 1) = -x * monoid_pow(R.mul, R.one, -x, 2 * n)",
				Simp(Rev(nat_arith.Add1)),
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				Refl())
			odd := a.Have(
				"x²ⁿ⁺¹ is x times x²ⁿ",
				"monoid_pow(R.mul, R.one, x, 2 * n + 1) = x * monoid_pow(R.mul, R.one, x, 2 * n)",
				Simp(Rev(nat_arith.Add1)),
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				Refl())
			even := a.Have(
				"the even power forgets the sign",
				"monoid_pow(R.mul, R.one, -x, 2 * n) = monoid_pow(R.mul, R.one, x, 2 * n)",
				By(NegPowEven, ring))
			a.Show(
				"so the sign of −x passes out of the product",
				negOdd.Rw(),
				odd.Rw(),
				even.Rw(),
				By(Read(MulLeftNeg, ring)))
		}),
})}

// ---------------------------------------------------------------------------
// The alternating signs
// ---------------------------------------------------------------------------
//
// The signs one, −one, one, … of the ring: they lie in the carrier,
// follow the exponent law, square to one, and cancel in adjacent pairs.

// AlternatingSignDef — `alternating_sign(one, neg, i)`: (−1)^i in the
// ring, one at 0 and negated at each step. Under the ring the text
// writes `alternating_sign(i)`.
var AlternatingSignDef = alternatingSignDefThm{family.Define(registry.DefEntry{
	Name:     "AlternatingSignDef",
	Key:      "prop_aa724367e7a9e55a",
	Const:    "alternating_sign",
	Type:     "A → (A → A) → num → A",
	Implicit: []string{"one", "neg"},
	Equations: []string{
		"∀one:A. ∀neg:(A → A). alternating_sign(one, neg, 0) = one",
		"∀one:A. ∀neg:(A → A). ∀i:num. " +
			"    alternating_sign(one, neg, suc(i)) = neg(alternating_sign(one, neg, i))",
	},
})}

// AlternatingSignIn — the signs lie in the ring's carrier: the sign at
// 0 is the ring's one, and each later sign negates the one before, so
// induction on i runs through the two closure laws of the ring on c.
var AlternatingSignIn = alternatingSignInThm{family.Add(registry.ProofEntry{
	Name: "AlternatingSignIn",
	Key:  "prop_31caed4a7e0355ac",
	Build: CommRingOn.Law("∀i:num. alternating_sign(i) ∈ R.carrier",
		func(a *Argument, ring CommRingFact[on.R]) {
			a.Induct("i")
			a.Base(
				"the sign at 0 is the ring's one, which lies in c",
				Simp(Fwd(AlternatingSignDef)),
				Cite(OneIn.Read(ring)))
			a.Step(
				"the sign at i + 1 negates the sign at i, and c is closed under negation",
				func(b *Argument, signIn Fact) {
					sign := b.MemberOf[on.R](b.TermAs[A]("alternating_sign(i)"), signIn)
					b.Show(
						"the negation of a member of c",
						Simp(Fwd(AlternatingSignDef)),
						By(NegIn.Read(ring).At(sign)))
				})
		}),
})}

// AlternatingSignAdd — the alternating signs follow the exponent law:
// the sign at p + j is the product of the signs at p and at j. By
// induction on j: at 0 the right factor is one, and one step further
// negates both sides, the negation passing out of the right factor.
var AlternatingSignAdd = alternatingSignAddThm{family.Add(registry.ProofEntry{
	Name: "AlternatingSignAdd",
	Key:  "prop_160c09e614297412",
	Build: CommRingOn.Law("∀p j:num. "+
		"    alternating_sign(p + j) = alternating_sign(p) * alternating_sign(j)",
		func(a *Argument, ring CommRingFact[on.R]) {
			signIn := AlternatingSignIn.Read(ring)
			a.Induct("j")
			a.Base(
				"the sign at 0 is one, so the right factor drops",
				func(b *Argument) {
					p := b.FixAs[Nat]("p")
					b.Show(
						"the sign at p times one is the sign at p",
						Simp(Fwd(AlternatingSignDef)),
						ByArith(ring, signIn.At(p)))
				})
			a.Step(
				"one step further negates both sides",
				func(b *Argument, ih Fact) {
					p := b.FixAs[Nat]("p")
					j := b.TermAs[Nat]("j")
					b.Show(
						"the negation of the product passes out of its right factor",
						Simp(Fwd(nat_arith.AddSuc), Fwd(AlternatingSignDef)),
						ByArith(ring, ih.At(p), signIn.At(p), signIn.At(j), signIn.At(b.TermAs[Nat]("p + j"))))
				})
		}),
})}

// AlternatingSignSquare — every alternating sign squares to one. By
// induction on n: one squares to one, and (−x)(−x) is x·x.
var AlternatingSignSquare = alternatingSignSquareThm{family.Add(registry.ProofEntry{
	Name: "AlternatingSignSquare",
	Key:  "prop_f2772409e0b111c8",
	Build: CommRingOn.Law("∀n:num. alternating_sign(n) * alternating_sign(n) = R.one",
		func(a *Argument, ring CommRingFact[on.R]) {
			signIn := AlternatingSignIn.Read(ring)
			a.Induct("n")
			a.Base(
				"the sign at 0 is one, which squares to one",
				Simp(Fwd(AlternatingSignDef)),
				ByArith(ring, OneIn.Read(ring)))
			a.Step(
				"the sign at n + 1 negates the sign at n, and (−x)(−x) is x·x",
				func(b *Argument, ih Fact) {
					b.Show(
						"the square of the negation is the square",
						Simp(Fwd(AlternatingSignDef)),
						ByArith(ring, ih, signIn.At(b.TermAs[Nat]("n"))))
				})
		}),
})}

// AlternatingSignSuc — each alternating sign cancels against the next,
// the sign at n + 1 being the negation of the sign at n.
var AlternatingSignSuc = alternatingSignSucThm{family.Add(registry.ProofEntry{
	Name: "AlternatingSignSuc",
	Key:  "prop_e55ff1827264c924",
	Build: CommRingOn.Law("∀n:num. alternating_sign(n + 1) + alternating_sign(n) = R.zero",
		func(a *Argument, ring CommRingFact[on.R], n *Expr[Nat]) {
			a.Show(
				"a sign plus its negation is zero",
				Simp(Rev(nat_arith.Add1), Fwd(AlternatingSignDef)),
				ByArith(ring, AlternatingSignIn.Read(ring).At(n)))
		}),
})}

// ---------------------------------------------------------------------------
// The ring's numerals, and the two fold laws a ring carries
// ---------------------------------------------------------------------------
//
// The additive powers of one are the ring's numerals (AddPowMulOn). Each
// of the ring's operations is a commutative monoid, so each folds: Σ and
// Π over any ring are the fold mechanism read at these two laws, with
// the neutral elements computed alongside.

// MonoidalMul — multiplication folds. Each of these four is the
// monoid chapter's law read at the ring's projected monoid — one
// reading, nothing searched.
var MonoidalMul = monoidalMulThm{family.Add(registry.ProofEntry{
	Name: "MonoidalMul",
	Key:  "prop_cea745fe23fdd5dc",
	Build: CommRing.Law("monoidal_op(R.mul)",
		func(a *Argument, ring Fact) {
			a.Show(
				"the multiplicative monoid folds",
				By(Read(comm_monoid.Monoidal, Read(MulMonoid, ring))))
		}),
})}

// NeutralMul — and it folds from one.
var NeutralMul = neutralMulThm{family.Add(registry.ProofEntry{
	Name: "NeutralMul",
	Key:  "prop_272d0accaa614a05",
	Build: CommRing.Law("neutral_elem(R.mul) = R.one",
		func(a *Argument, ring Fact) {
			a.Show(
				"the multiplicative monoid's identity",
				By(Read(comm_monoid.Neutral, Read(MulMonoid, ring))))
		}),
})}

// MonoidalAdd — addition folds: the additive group's monoid does.
var MonoidalAdd = monoidalAddThm{family.Add(registry.ProofEntry{
	Name: "MonoidalAdd",
	Key:  "prop_3737bd860e70dc4a",
	Build: CommRing.Law("monoidal_op(R.add)",
		func(a *Argument, ring Fact) {
			a.Show(
				"the additive group's monoid folds",
				By(Read(comm_monoid.Monoidal, Read(abelian_group.Monoid, Read(AddGroup, ring)))))
		}),
})}

// NeutralAdd — and it folds from zero.
var NeutralAdd = neutralAddThm{family.Add(registry.ProofEntry{
	Name: "NeutralAdd",
	Key:  "prop_85b24a4620d3036",
	Build: CommRing.Law("neutral_elem(R.add) = R.zero",
		func(a *Argument, ring Fact) {
			a.Show(
				"the additive group's identity",
				By(Read(comm_monoid.Neutral, Read(abelian_group.Monoid, Read(AddGroup, ring)))))
		}),
})}

// AddPowMulOn — the additive power of one at a product of exponents is
// the product of the powers: n copies of one, taken m times, is m·n
// copies. By induction on m; at the step the exponent grows by n and
// the power by one, and distributivity spreads the extra one over the n
// copies, every power lying in c (PowIn at the additive monoid). With
// PowAddOn at the additive monoid this makes the additive powers of one
// a copy of ℕ inside every commutative ring — the ring's numerals, which
// the arithmetic closer's structure ring folds coefficients with.
var AddPowMulOn = addPowMulOnThm{family.Add(registry.ProofEntry{
	Name: "AddPowMulOn",
	Key:  "prop_8968dac65d9ed3db",
	Build: CommRingOn.Law("∀m n:num. "+
		"    monoid_pow(R.add, R.zero, R.one, m * n) = "+
		"    monoid_pow(R.add, R.zero, R.one, m) * monoid_pow(R.add, R.zero, R.one, n)",
		func(a *Argument, ring CommRingFact[on.R], m, n Term) {
			additive := AddMonoidOn.Read(ring)
			multiplicative := MulMonoidOn.Read(ring)
			powers := comm_monoid.PowIn.Read(additive)
			a.Induct(m)
			a.Base(
				"at m = 0 both sides are R.zero: no copies of R.one, "+
					"and R.zero absorbs the n copies, which lie in R.carrier",
				Simp(Fwd(nat_arith.MulLeftZeroClause), Fwd(comm_monoid.MonoidPowDef)),
				Simp(Fwd(MulLeftZeroOn.Read(ring)), Fwd(powers), Fwd(OneIn.Read(ring))),
				Refl())
			a.Step(
				"one more copy of one: the exponent grows by n, and the extra one spreads over the n copies",
				func(d *Argument, ih Fact) {
					d.Do(Simp(Fwd(nat_arith.Mul), Fwd(comm_monoid.MonoidPowDef)),
						Simp(Fwd(comm_monoid.PowAddOn.Read(additive)), Fwd(OneIn.Read(ring))), ih.Rw(),
						Simp(
							Fwd(RightDistribOn.Read(ring)),
							Fwd(comm_monoid.LeftIdentityOn.Read(multiplicative)),
							Fwd(powers),
							Fwd(OneIn.Read(ring)),
							Fwd(MulIn.Read(ring))),
						By(comm_monoid.CommOn.Read(additive), powers, OneIn.Read(ring), MulIn.Read(ring)))
				})
		}),
})}

// AddPowMul — AddPowMulOn on the whole type.
var AddPowMul = addPowMulThm{family.Add(registry.ProofEntry{
	Name: "AddPowMul",
	Key:  "prop_fc26fed743794c51",
	Build: CommRingAtUniverse.Law(
		"∀m n:num. "+
			"    monoid_pow(R.add, R.zero, R.one, m * n) = "+
			"    monoid_pow(R.add, R.zero, R.one, m) * monoid_pow(R.add, R.zero, R.one, n)",
		AddPowMulOn),
})}
