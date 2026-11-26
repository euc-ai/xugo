// division.go — division, as multiplication by the inverse: the laws that open a quotient.

package field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// DivRightMulOn — dividing by a nonzero member y and multiplying back
// by y returns what was divided. The quotient opens to x * inv(y);
// regrouped, inv(y) stands beside the y it inverts — the three factors
// lie in F.carrier, the inverse by closure — that pair is one, and one drops
// off x.
var DivRightMulOn = divRightMulOnThm{family.Add(registry.ProofEntry{
	Name: "DivRightMulOn",
	Key:  "prop_fa0bf35d203a261f",
	Build: FieldOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
			"y ≠ F.zero",
		},
		Conclusion: "x / y * y = x",
	},
		func(a *Argument, field FieldFact[on.F], x, y *Member[A, on.F], nonzero Fact) {
			monoid := Read(comm_ring.MulMonoidOn, Read(RingOn, field))
			a.Do(CalcEq(
				Leg(
					a.TermAs[A]("x * F.inv(y) * y"),
					"x / y is x times the inverse of y",
					Simp(Fwd(Read(DivMulInvOn, field))),
					Refl()),
				Leg(
					a.TermAs[A]("x * (F.inv(y) * y)"),
					"regroup, so that inv(y) stands beside the y it inverts",
					By(Read(comm_monoid.AssocOn, monoid), x, y, field, InvIn)),
				Leg(
					a.TermAs[A]("x * F.one"),
					"and that pair is one, the left-inverse axiom at y, which y ≠ zero unlocks",
					By(Normalized, x, y, nonzero, At(Read(MulLeftInverseOn, field), y))),
				FinalLeg(
					"and one drops off the member x",
					By(Read(comm_monoid.RightIdentityOn, monoid), x, y)),
			))
		}),
})}

// DivRightMul — DivRightMulOn on the whole type.
var DivRightMul = divRightMulThm{family.Add(registry.ProofEntry{
	Name: "DivRightMul",
	Key:  "prop_10a7109feb2ebfea",
	Build: FieldAtUniverse.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"y ≠ F.zero",
		},
		Conclusion: "x / y * y = x",
	}, DivRightMulOn),
})}

// DivLeftMulOn — a quotient multiplied from the left by its nonzero
// divisor gives back the dividend. The quotient opens to x * inv(y);
// y passes x to stand beside its own inverse — the three factors lie
// in F.carrier, the inverse by closure — that pair is one, and one drops off
// x.
var DivLeftMulOn = divLeftMulOnThm{family.Add(registry.ProofEntry{
	Name: "DivLeftMulOn",
	Key:  "prop_58c2ae9d1d056f72",
	Build: FieldOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
			"y ≠ F.zero",
		},
		Conclusion: "y * (x / y) = x",
	},
		func(a *Argument, field FieldFact[on.F], x, y *Member[A, on.F], nonzero Fact) {
			monoid := Read(comm_ring.MulMonoidOn, Read(RingOn, field))
			a.Show(
				"open the quotient, and let y meet its own inverse",
				CalcEq(
					Leg(
						a.TermAs[A]("y * (x * F.inv(y))"),
						"x / y is x times the inverse of y",
						Simp(Fwd(Read(DivMulInvOn, field))),
						Refl()),
					Leg(
						a.TermAs[A]("x * (y * F.inv(y))"),
						"y passes x to stand beside its inverse",
						By(Read(comm_monoid.LeftCommOn, monoid), x, y, field, InvIn)),
					Leg(
						a.TermAs[A]("x * F.one"),
						"and that pair is one, the right-inverse law at y, which y ≠ zero unlocks",
						By(Normalized, x, y, nonzero, At(Read(MulRightInverseOn, field), y))),
					FinalLeg(
						"and one drops off the member x",
						By(Read(comm_monoid.RightIdentityOn, monoid), x, y)),
				))
		}),
})}

// DivLeftMul — DivLeftMulOn on the whole type.
var DivLeftMul = divLeftMulThm{family.Add(registry.ProofEntry{
	Name: "DivLeftMul",
	Key:  "prop_a0542b7de28a2cab",
	Build: FieldAtUniverse.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"y ≠ F.zero",
		},
		Conclusion: "y * (x / y) = x",
	}, DivLeftMulOn),
})}

// DivOneOn — dividing a member by one changes nothing. The quotient
// x / one opens to x * inv(one) — a quotient of members, since the
// ring's one lies in F.carrier; one is its own inverse, and one drops off the
// member x.
var DivOneOn = divOneOnThm{family.Add(registry.ProofEntry{
	Name: "DivOneOn",
	Key:  "prop_6e3c42efbb811d6e",
	Build: FieldOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
		},
		Conclusion: "x / F.one = x",
	},
		func(a *Argument, field FieldFact[on.F], x *Member[A, on.F]) {
			ring := Read(RingOn, field)
			monoid := Read(comm_ring.MulMonoidOn, ring)
			a.Do(CalcEq(
				Leg(
					a.TermAs[A]("x * F.inv(F.one)"),
					"x / one is x times the inverse of one: x is a member, and so is the ring's one",
					Simp(Fwd(Read(DivMulInvOn, field)), Fwd(Read(comm_ring.OneIn, ring))),
					Refl()),
				Leg(
					a.TermAs[A]("x * F.one"),
					"one is its own inverse",
					Cite(Read(InvOneOn, field))),
				FinalLeg(
					"and one drops off the member x",
					By(Read(comm_monoid.RightIdentityOn, monoid), x)),
			))
		}),
})}

// DivOne — DivOneOn on the whole type.
var DivOne = divOneThm{family.Add(registry.ProofEntry{
	Name:  "DivOne",
	Key:   "prop_27fdf751805baa73",
	Build: FieldAtUniverse.Law("∀x:A. x / F.one = x", DivOneOn),
})}

// DivReflOn — a nonzero member divided by itself is one. Opened, the
// quotient of the member x by itself is x times its inverse, and that
// product is one by the right-inverse law, which x ≠ zero unlocks.
var DivReflOn = divReflOnThm{family.Add(registry.ProofEntry{
	Name: "DivReflOn",
	Key:  "prop_43a9a5166d79aea1",
	Build: FieldOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"x ≠ F.zero",
		},
		Conclusion: "x / x = F.one",
	},
		func(a *Argument, field FieldFact[on.F], x *Member[A, on.F], nonzero Fact) {
			a.Show(
				"x / x opens to x * inv(x), and a nonzero member times its inverse is one",
				Simp(Fwd(Read(DivMulInvOn, field))),
				By(x, nonzero, At(Read(MulRightInverseOn, field), x)))
		}),
})}

// DivRefl — DivReflOn on the whole type.
var DivRefl = divReflThm{family.Add(registry.ProofEntry{
	Name: "DivRefl",
	Key:  "prop_652ac70984962e0c",
	Build: FieldAtUniverse.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ≠ F.zero",
		},
		Conclusion: "x / x = F.one",
	}, DivReflOn),
})}

// InvDivOn — the inverse of a quotient of members is the quotient
// reversed. A quotient is a product with the divisor inverted, so the
// inverse reaches both factors, the divisor's two inverses cancel, and
// the factors commute into y / x — every factor a member of F.carrier, the
// inverses by closure. Neither x nor y need be nonzero: the inverse's
// laws for a product and for an inverse ask only that their arguments
// lie in F.carrier.
var InvDivOn = invDivOnThm{family.Add(registry.ProofEntry{
	Name: "InvDivOn",
	Key:  "prop_143a2b89d73806c2",
	Build: FieldOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
		},
		Conclusion: "F.inv(x / y) = y / x",
	},
		func(a *Argument, field FieldFact[on.F], x, y *Member[A, on.F]) {
			quotient := Read(DivMulInvOn, field)
			commute := Read(comm_monoid.CommOn, Read(comm_ring.MulMonoidOn, Read(RingOn, field)))
			a.Show(
				"open both quotients and compute with the inverse's laws",
				CalcEq(
					Leg(
						a.TermAs[A]("F.inv(x * F.inv(y))"),
						"x / y is x times the inverse of y",
						Simp(Fwd(quotient)),
						Refl()),
					Leg(
						a.TermAs[A]("F.inv(x) * F.inv(F.inv(y))"),
						"the inverse of a product is the product of the inverses: x and inv(y) lie in F.carrier",
						By(Read(InvMulOn, field), x, y, field, InvIn)),
					Leg(
						a.TermAs[A]("F.inv(x) * y"),
						"the inverse of inv(y) is the member y",
						Simp(Fwd(Read(InvInvOn, field))),
						Refl()),
					Leg(
						a.TermAs[A]("y * F.inv(x)"),
						"the two factors, in the other order",
						By(commute, x, y, field, InvIn)),
					FinalLeg(
						"which is y / x, opened the same way",
						Simp(Fwd(quotient)),
						Refl()),
				))
		}),
})}

// InvDiv — InvDivOn on the whole type.
var InvDiv = invDivThm{family.Add(registry.ProofEntry{
	Name:  "InvDiv",
	Key:   "prop_961e588e06a42867",
	Build: FieldAtUniverse.Law("∀x y:A. F.inv(x / y) = y / x", InvDivOn),
})}
