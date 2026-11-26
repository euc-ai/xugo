// definitions.go — an algebraically closed field, one field record
// extending another, and the field record a chain of extensions unites to.

package algebraic_closure

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/registry"
)

// AlgebraicallyClosedDef — `algebraically_closed_field(F)`: every
// polynomial of positive degree over the carrier has a root in it.
var AlgebraicallyClosedDef = algebraicallyClosedDefThm{family.Define(registry.DefEntry{
	Name:  "AlgebraicallyClosedDef",
	Key:   "prop_a77b875a97d22263",
	Const: "algebraically_closed_field",
	Type:  "field_ops(A) → bool",
	Equations: []string{
		"∀F:field_ops(A). " +
			"    algebraically_closed_field(F) ⇔ " +
			"    ∀p:(num → A). " +
			"        polynomial_over(F.zero, F.carrier, p) ∧ 0 < polynomial_degree(F.zero, p) ⇒ " +
			"        ∃x:A. x ∈ F.carrier ∧ polynomial_eval(F.add, F.zero, F.mul, F.one, p, x) = F.zero",
	},
	Reading: "The predicate carries no field axiom: a " +
		"statement about a closed field also asks field_on.",
})}

// fieldExtendsDef — `field_extends(F, G)`: G's carrier holds F's, and the
// eight operations of the two records agree wherever F's are read, on F's
// carrier.
var fieldExtendsDef = fieldExtendsDefThm{family.Define(registry.DefEntry{
	Name:  "fieldExtendsDef",
	Key:   "prop_b6667903e7d0b4bd",
	Const: "field_extends",
	Type:  "field_ops(A) → field_ops(A) → bool",
	Equations: []string{
		"∀F G:field_ops(A). " +
			"    field_extends(F, G) ⇔ " +
			"    F.carrier ⊆ G.carrier ∧ " +
			"    F.zero = G.zero ∧ " +
			"    F.one = G.one ∧ " +
			"    (∀x:A. x ∈ F.carrier ⇒ F.neg(x) = G.neg(x) ∧ F.inv(x) = G.inv(x)) ∧ " +
			"    (∀x y:A. " +
			"        x ∈ F.carrier ∧ y ∈ F.carrier ⇒ " +
			"        F.add(x, y) = G.add(x, y) ∧ " +
			"        F.mul(x, y) = G.mul(x, y) ∧ " +
			"        F.sub(x, y) = G.sub(x, y) ∧ " +
			"        F.div(x, y) = G.div(x, y))",
	},
	Reading: "The records are total maps on the type, and off F's carrier nothing is compared, " +
		"so two records extending each other may still differ there: the relation is a preorder, not " +
		"an order. Zorn's lemma asks no more (relations/order.Zorn uses no antisymmetry).",
})}

// chainUnionFieldDef — `chain_union_field(c)`: the carrier is the union
// of the members' carriers, and an operation at given arguments is the
// operation of a member, chosen, whose carrier holds them.
var chainUnionFieldDef = chainUnionFieldDefThm{family.Define(registry.DefEntry{
	Name:  "chainUnionFieldDef",
	Key:   "prop_fbd8b5c234a25649",
	Const: "chain_union_field",
	Type:  "set(field_ops(A)) → field_ops(A)",
	Equations: []string{"∀c:set(field_ops(A)). " +
		"    chain_union_field(c) = " +
		"    mk_field(λx:A. λy:A. (εF:field_ops(A). F ∈ c ∧ x ∈ F.carrier ∧ y ∈ F.carrier).add(x, y), " +
		"        (εF:field_ops(A). F ∈ c).zero, " +
		"        λx:A. (εF:field_ops(A). F ∈ c ∧ x ∈ F.carrier).neg(x), " +
		"        λx:A. λy:A. (εF:field_ops(A). F ∈ c ∧ x ∈ F.carrier ∧ y ∈ F.carrier).mul(x, y), " +
		"        (εF:field_ops(A). F ∈ c).one, " +
		"        λx:A. λy:A. (εF:field_ops(A). F ∈ c ∧ x ∈ F.carrier ∧ y ∈ F.carrier).sub(x, y), " +
		"        λx:A. (εF:field_ops(A). F ∈ c ∧ x ∈ F.carrier).inv(x), " +
		"        λx:A. λy:A. (εF:field_ops(A). F ∈ c ∧ x ∈ F.carrier ∧ y ∈ F.carrier).div(x, y), " +
		"        ⋃{F.carrier | F:field_ops(A) | F ∈ c})"},
	Reading: "Which member is chosen matters only when two members disagree at the " +
		"arguments; along a chain under field_extends they never do (ChainUnionExtends). " +
		"For the empty family the carrier is empty and the record is no field.",
})}
