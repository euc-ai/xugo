// definitions.go — regular function fields.

package function_field

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/perfect_field"
	"github.com/euc-ai/xugo/library/registry"
)

var RegularFunctionFieldDef = regularFunctionFieldDefThm{family.Define(registry.DefEntry{
	Name:  "RegularFunctionFieldDef",
	Key:   "prop_a865dc42f38e80af",
	Deps:  []registry.EntryLike{},
	Const: "regular_function_field",
	Type:  "field_ops(A) → set(A) → set(A) → bool",
	Equations: []string{
		"∀F:field_ops(A). ∀k K:set(A). " +
			"    regular_function_field(F, k, K) ⇔ " +
			"    subfield(F, k) ∧ " +
			"    subfield(F, K) ∧ " +
			"    k ⊆ K ∧ " +
			"    perfect_field(restrict_field(F, k)) ∧ " +
			"    (∃E:set(A). finite(E) ∧ E ⊆ K ∧ field_adjoin(F, k, E) = K) ∧ " +
			"    (∃t:A. " +
			"        t ∈ K ∧ " +
			"        ¬algebraic_over(F, k, t) ∧ " +
			"        (∀x:A. x ∈ K ⇒ algebraic_over(F, field_adjoin(F, k, {t}), x))) ∧ " +
			"    (∀x:A. x ∈ K ∧ algebraic_over(F, k, x) ⇒ x ∈ k)",
	},
})}
