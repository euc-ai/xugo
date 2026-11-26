package real_ordered_instance

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// RealOrderedField — the reals with their strict order form an ordered
// field on the whole line. The field is ℝ's own, read on its universe
// carrier; each order axiom is the matching law of ℝ's order.
var RealOrderedField = realOrderedFieldThm{family.Add(registry.ProofEntry{
	Name: "RealOrderedField",
	Key:  "prop_7ee32895f07cb589",
	Build: family.Instance(ordered_field.OrderedFieldOn, "ordered_field_on(real_field_ops, real_lt)",
		Case(
			"ℝ is a field on the whole line",
			Derive(func(a *Argument) {
				reals := a.TermAs[field.FieldOps[Real]]("real_field_ops")
				a.Show(
					"the whole-type field of reals, read on its universe carrier",
					By(
						real_field.Field,
						field.FieldOnUniverse.At(reals),
						field.RestrictFieldDef.At(reals, a.TermAs[Set[Real]]("𝕌")),
						real_field.RealFieldOpsDef))
			})),
		Case(
			"no real lies below itself",
			By(real_order_ring.LessThanIrrefl)),
		Case(
			"the strict order is transitive",
			By(real_order_ring.LessThanTrans)),
		Case(
			"any two reals are comparable",
			By(real_order_ring.LessThanTrichotomy)),
		Case(
			"adding a real on the right preserves the order",
			By(real_order_ring.LessThanAddRight)),
		Case(
			"a product of positive reals is positive",
			By(real_order_ring.MulPos))),
})}

// RealOrderedLe — the weak order of the real strict order is ≤.
var RealOrderedLe = realOrderedLeThm{family.Add(registry.ProofEntry{
	Name: "RealOrderedLe",
	Key:  "prop_fd87f7a743407266",
	Build: family.Theorem(
		"∀a b:real. ordered_le(real_lt, a, b) ⇔ a ≤ b",
		func(arg *Argument, a, b *Expr[Real]) {
			arg.Show(
				"equal or less is at most",
				By(Normalized, ordered_field.OrderedLeDef, real_order_ring.LessEqSplit.At(a, b)))
		}),
})}
