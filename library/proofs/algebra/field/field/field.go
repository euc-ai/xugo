// field.go — the chapter: a field, the commutative ring whose one is not
// its zero and whose every nonzero element has an inverse; and the field
// on a set.
//
// Every law of the field is proved once, on a carrier set c, and stated
// beside it on the whole type as the view of that proof
// (FieldAtUniverse; constitution §Structures, "One proof per law"). The
// name of a carrier law ends in `On`, and the whole-type view takes the
// bare name; the closure axiom and the closure law have no view and
// carry no suffix. The projection to the ring is an axiom of each form:
// the whole-type one is no view, since its conclusion is the whole-type
// ring and not the ring on 𝕌.

package field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structures
// ---------------------------------------------------------------------------

// Field — a field on the whole type, using the operations held in F.
// Its carrier field does not restrict the ring or inverse axioms.
var Field = fieldThm{family.DefineStructure(registry.DefEntry{
	Name: "Field", Key: "prop_d90bb64810c057a", Const: "field", Subject: "F",
	Type: "field_ops(A) → bool",
	Equations: []string{"∀F:field_ops(A). " +
		"    field(F) ⇔ " +
		"    comm_ring(field_ring(F)) ∧ " +
		"    F.one ≠ F.zero ∧ " +
		"    (∀x:A. x ≠ F.zero ⇒ F.mul(F.inv(x), x) = F.one) ∧ " +
		"    F.inv(F.zero) = F.zero ∧ " +
		"    (∀x y:A. F.div(x, y) = F.mul(x, F.inv(y)))"},
	Deps: []registry.EntryLike{FieldRingDef},
})}

// FieldOn — F is a commutative ring on its carrier, closed under inverse,
// with distinct zero and one, a left inverse for each nonzero member,
// inverse zero equal to zero, and division given by multiplication by inverse.
var FieldOn = fieldOnThm{family.DefineStructure(registry.DefEntry{
	Name:  "FieldOn",
	Key:   "prop_62602eb4d43e5be8",
	Const: "field_on", Subject: "F",
	Type: "field_ops(A) → bool",
	Equations: []string{
		"∀F:field_ops(A). " +
			"    field_on(F) ⇔ " +
			"    comm_ring_on(field_ring(F)) ∧ " +
			"    (∀x:A. x ∈ F.carrier ⇒ F.inv(x) ∈ F.carrier) ∧ " +
			"    F.one ≠ F.zero ∧ " +
			"    (∀x:A. x ∈ F.carrier ⇒ x ≠ F.zero ⇒ F.mul(F.inv(x), x) = F.one) ∧ " +
			"    F.inv(F.zero) = F.zero ∧ " +
			"    (∀x y:A. x ∈ F.carrier ∧ y ∈ F.carrier ⇒ F.div(x, y) = F.mul(x, F.inv(y)))",
	},
	Deps: []registry.EntryLike{FieldRingDef},
})}

// FieldOnUniverse — a field on the whole type is its carrier form with
// the same operations and carrier 𝕌; all its membership guards hold.
var FieldOnUniverse = fieldOnUniverseThm{family.Add(registry.ProofEntry{
	Name: "FieldOnUniverse", Key: "prop_c86bfe65300338b5",
	Build: family.Theorem("∀F:field_ops(A). field(F) ⇔ field_on(restrict_field(F, 𝕌))",
		func(a *Argument, F *Expr[FieldOps[A]]) {
			a.Show(
				"the ring conjunct is the ring on 𝕌, the closure asks "+
					"nothing, and the two guarded axioms lose their guards",
				Unfold(Field),
				Unfold(FieldOn),
				Simp(
					Fwd(FieldRingDef),
					Fwd(RestrictFieldDef),
					Fwd(module_record.RestrictRingDef),
					Fwd(comm_ring.CommRingOnUniverse),
					Fwd(set_basic.InUniv)),
				Basic())
		}),
})}

// FieldAtUniverse — the whole-type view of a law proved on the carrier.
var FieldAtUniverse = Field.AtUniverseRecord(
	FieldOn, FieldOnUniverse, "restrict_field(F, 𝕌)", set_basic.InUniv)

// ---------------------------------------------------------------------------
// The axioms
// ---------------------------------------------------------------------------
//
// The axioms of the field on a set, each with its whole-type view, and
// the closure under division they give.

// Ring — a field is a commutative ring: the projection at which the
// ring chapter's laws, and every law stated under the ring, apply.
var Ring = ringThm{family.Add(registry.ProofEntry{
	Name:  "Ring",
	Key:   "prop_4c5e8164919afb72",
	Build: Field.Axiom("comm_ring(field_ring(F))"),
})}

// RingOn — a field on F.carrier is a commutative ring on F.carrier: the projection at
// which the ring chapter's carrier laws apply.
var RingOn = ringOnThm{family.Add(registry.ProofEntry{
	Name:  "RingOn",
	Key:   "prop_7f37ec8d2a06dbfb",
	Build: FieldOn.Axiom("comm_ring_on(field_ring(F))"),
})}

// InvIn — the carrier is closed under the inverse. The ring's closure
// laws (comm_ring.ZeroIn, OneIn, AddIn, NegIn, MulIn, SubIn) are read at
// RingOn.
var InvIn = invInThm{family.Add(registry.ProofEntry{
	Name: "InvIn",
	Key:  "prop_4112fd502ebace05",
	Build: FieldOn.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
		},
		Conclusion: "F.inv(x) ∈ F.carrier",
	}),
})}

// OneNotZeroOn — a field has at least two elements.
var OneNotZeroOn = oneNotZeroOnThm{family.Add(registry.ProofEntry{
	Name:  "OneNotZeroOn",
	Key:   "prop_e602abb30978ca8d",
	Build: FieldOn.Axiom("F.one ≠ F.zero"),
})}

// OneNotZero — OneNotZeroOn on the whole type.
var OneNotZero = oneNotZeroThm{family.Add(registry.ProofEntry{
	Name:  "OneNotZero",
	Key:   "prop_44df0cd8f91398ea",
	Build: FieldAtUniverse.Law("F.one ≠ F.zero", OneNotZeroOn),
})}

// MulLeftInverseOn — a nonzero member has an inverse, from the left.
var MulLeftInverseOn = mulLeftInverseOnThm{family.Add(registry.ProofEntry{
	Name: "MulLeftInverseOn",
	Key:  "prop_a36f7e0d863bdab1",
	Build: FieldOn.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"x ≠ F.zero",
		},
		Conclusion: "F.inv(x) * x = F.one",
	}),
})}

// MulLeftInverse — MulLeftInverseOn on the whole type.
var MulLeftInverse = mulLeftInverseThm{family.Add(registry.ProofEntry{
	Name: "MulLeftInverse",
	Key:  "prop_bed21671fe9df452",
	Build: FieldAtUniverse.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ≠ F.zero",
		},
		Conclusion: "F.inv(x) * x = F.one",
	}, MulLeftInverseOn),
})}

// InvZeroOn — the inverse of zero is zero.
var InvZeroOn = invZeroOnThm{family.Add(registry.ProofEntry{
	Name:  "InvZeroOn",
	Key:   "prop_21a3bf086cc29dba",
	Build: FieldOn.Axiom("F.inv(F.zero) = F.zero"),
})}

// InvZero — InvZeroOn on the whole type.
var InvZero = invZeroThm{family.Add(registry.ProofEntry{
	Name:  "InvZero",
	Key:   "prop_81dd46ca11c786fd",
	Build: FieldAtUniverse.Law("F.inv(F.zero) = F.zero", InvZeroOn),
})}

// DivMulInvOn — division is multiplication by the inverse: the field's
// own spelling of the quotient, as the ring's `SubAddNegOn` is of the
// difference.
var DivMulInvOn = divMulInvOnThm{family.Add(registry.ProofEntry{
	Name: "DivMulInvOn",
	Key:  "prop_1ee0b29252f1ed8b",
	Build: FieldOn.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
		},
		Conclusion: "x / y = x * F.inv(y)",
	}),
})}

// DivMulInv — DivMulInvOn on the whole type.
var DivMulInv = divMulInvThm{family.Add(registry.ProofEntry{
	Name:  "DivMulInv",
	Key:   "prop_822b31a46dd1f8d",
	Build: FieldAtUniverse.Law("∀x y:A. x / y = x * F.inv(y)", DivMulInvOn),
})}

// DivIn — the carrier is closed under division: a quotient is a product
// of a member with an inverse, and the carrier holds both.
var DivIn = divInThm{family.Add(registry.ProofEntry{
	Name: "DivIn",
	Key:  "prop_2dc0c7dccd750987",
	Build: FieldOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
		},
		Conclusion: "x / y ∈ F.carrier",
	},
		func(a *Argument, field FieldFact[on.F], x, y *Member[A, on.F]) {
			a.Show(
				"x / y is x * inv(y), a product of members",
				Simp(Fwd(Read(DivMulInvOn, field))),
				By(Read(comm_ring.MulIn, Read(RingOn, field)), Read(InvIn, field), x, y))
		}),
})}
