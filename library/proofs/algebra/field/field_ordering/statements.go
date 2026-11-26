package field_ordering

import (
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/datatypes/option"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	_ "github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// SumsSquaresDef — Finite sums of squares, including zero as the empty sum.
var SumsSquaresDef = sumsSquaresDefThm{family.Define(registry.DefEntry{
	Name: "SumsSquaresDef", Const: "field_sums_squares", Type: "field_ops(A) → set(A)",
	Key: "prop_c4f90b1ae7fcc82a",
	Equations: []string{
		"∀F:field_ops(A). " +
			"    field_sums_squares(F) = " +
			"    {module_sum(F.add, F.zero, {j:num | j < k}, λj:num. F.mul(a(j), a(j))) | " +
			"        k:num, " +
			"        a:(num → A) | " +
			"        ∀j:num. j < k ⇒ a(j) ∈ F.carrier}",
	},
})}

// FormallyRealDef — A field in which minus one is not a sum of squares.
var FormallyRealDef = formallyRealDefThm{family.Define(registry.DefEntry{
	Name: "FormallyRealDef", Const: "formally_real_field", Type: "field_ops(A) → bool",
	Key: "prop_eab7d119b7be3fb0",
	Equations: []string{
		"∀F:field_ops(A). formally_real_field(F) ⇔ field_on(F) ∧ F.neg(F.one) ∉ field_sums_squares(F)",
	},
	Deps: []registry.EntryLike{SumsSquaresDef},
})}

// PreorderingDef — A subset of the carrier containing squares and closed under addition and multiplication.
var PreorderingDef = preorderingDefThm{family.Define(registry.DefEntry{
	Name: "PreorderingDef", Const: "field_preordering", Type: "field_ops(A) → set(A) → bool",
	Key: "prop_839a20c83e8e83fb",
	Equations: []string{
		"∀F:field_ops(A). ∀T:set(A). " +
			"    field_preordering(F, T) ⇔ " +
			"    T ⊆ F.carrier ∧ " +
			"    (∀x:A. x ∈ F.carrier ⇒ F.mul(x, x) ∈ T) ∧ " +
			"    (∀x y:A. x ∈ T ∧ y ∈ T ⇒ F.add(x, y) ∈ T ∧ F.mul(x, y) ∈ T)",
	},
})}

// PositiveConeDef — A proper total preordering, whose elements are the nonnegative elements.
var PositiveConeDef = positiveConeDefThm{family.Define(registry.DefEntry{
	Name: "PositiveConeDef", Const: "field_positive_cone", Type: "field_ops(A) → set(A) → bool",
	Key: "prop_c357af3248a8bcb",
	Equations: []string{
		"∀F:field_ops(A). ∀P:set(A). " +
			"    field_positive_cone(F, P) ⇔ " +
			"    field_preordering(F, P) ∧ F.neg(F.one) ∉ P ∧ (∀x:A. x ∈ F.carrier ⇒ x ∈ P ∨ F.neg(x) ∈ P)",
	},
	Deps: []registry.EntryLike{PreorderingDef},
})}

// ConeOrderDef — The strict order associated with a nonnegative cone.
var ConeOrderDef = coneOrderDefThm{family.Define(registry.DefEntry{
	Name: "ConeOrderDef", Const: "field_cone_order", Type: "field_ops(A) → set(A) → A → A → bool",
	Key: "prop_436db48f481c2a2e",
	Equations: []string{
		"∀F:field_ops(A). ∀P:set(A). ∀x y:A. " +
			"    field_cone_order(F, P, x, y) ⇔ x ∈ F.carrier ∧ y ∈ F.carrier ∧ x ≠ y ∧ F.sub(y, x) ∈ P",
	},
})}

// SumsSquaresPreordering — Finite sums of squares form a preordering.
var SumsSquaresPreordering = sumsSquaresPreorderingThm{family.Add(registry.ProofEntry{
	Name: "SumsSquaresPreordering",
	Key:  "prop_9560089d79b9a3b5",
	Deps: []registry.EntryLike{
		module.ModuleSumIn,
		module.ModuleSumSingle,
		module.ModuleSumDisjointUnion,
		module.ModuleSumImage,
		module.ModuleSumSmul,
		module.ModuleSumCross,
	},
	Build: family.Card(Statement{
		Binders: "∀F:field_ops(A).",
		Hypotheses: []string{
			"field_on(F)",
		},
		Conclusion: "field_preordering(F, field_sums_squares(F))",
	},
		"Real closed field transfer design, Artin algebra. A sum lies in the carrier by "+
			"ModuleSumIn and a square is the sum of one term by ModuleSumSingle. Concatenate "+
			"sums for addition, the second shifted past the first (ModuleSumDisjointUnion, "+
			"ModuleSumImage); distribute a product of two sums (ModuleSumSmul twice), take it "+
			"over the cross of the index sets (ModuleSumCross) and renumber the pairs below "+
			"k·l (ModuleSumImage); each product term a(i)²·b(j)² is the square of a(i)·b(j)."),
})}

// PreorderingExtension — Every proper field preordering extends to a positive cone.
var PreorderingExtension = preorderingExtensionThm{family.Add(registry.ProofEntry{
	Name: "PreorderingExtension",
	Key:  "prop_2286a35b1bac903f",
	Deps: []registry.EntryLike{order.Zorn},
	Build: family.Card(Statement{
		Binders: "∀F:field_ops(A). ∀T:set(A).",
		Hypotheses: []string{
			"field_on(F)",
			"field_preordering(F, T)",
			"F.neg(F.one) ∉ T",
		},
		Conclusion: "∃P:set(A). T ⊆ P ∧ field_positive_cone(F, P)",
	},
		"Real closed field transfer design, order extension. Use Zorn on proper preorderings above "+
			"T; chain unions stay proper, and maximality forces either a or minus a into the cone."),
})}

// PositiveConeOrder — A positive cone defines an ordered field.
var PositiveConeOrder = positiveConeOrderThm{family.Add(registry.ProofEntry{
	Name: "PositiveConeOrder",
	Key:  "prop_9524aeaa2af18e8e",
	Build: family.Card(Statement{
		Binders: "∀F:field_ops(A). ∀P:set(A).",
		Hypotheses: []string{
			"field_on(F)",
			"field_positive_cone(F, P)",
		},
		Conclusion: "ordered_field_on(F, field_cone_order(F, P))",
	},
		"Real closed field transfer design, positive cones. Properness and "+
			"inverses force P intersect minus P to contain only zero, giving "+
			"strict trichotomy and compatibility with the field operations."),
})}

// OrderedFormallyReal — An ordered field is formally real.
var OrderedFormallyReal = orderedFormallyRealThm{family.Add(registry.ProofEntry{
	Name: "OrderedFormallyReal",
	Key:  "prop_d67558afdc8670fe",
	Deps: []registry.EntryLike{ordered_field.SquareNonnegative, ordered_field.OnePositive},
	Build: family.Card(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool).",
		Hypotheses: []string{
			"ordered_field_on(F, lt)",
		},
		Conclusion: "formally_real_field(F)",
	},
		"Real closed field transfer design, ordered fields. Every finite "+
			"sum of squares is nonnegative, whereas minus one is negative."),
})}

// SeparateNonsquareSum — A nonsum of squares in a formally real field is negative in some ordering.
var SeparateNonsquareSum = separateNonsquareSumThm{family.Add(registry.ProofEntry{
	Name: "SeparateNonsquareSum",
	Key:  "prop_73b6f19523208e78",
	Deps: []registry.EntryLike{SumsSquaresPreordering, PreorderingExtension, PositiveConeOrder},
	Reading: "The empty sum puts zero in the square-sum cone, so the nonsum " +
		"hypothesis excludes zero. In the separation argument formal reality " +
		"forces the auxiliary square sum t to be nonzero before division by t².",
	Build: family.Card(Statement{
		Binders: "∀F:field_ops(A). ∀a:A.",
		Hypotheses: []string{
			"formally_real_field(F)",
			"a ∈ F.carrier",
			"a ∉ field_sums_squares(F)",
		},
		Conclusion: "∃lt:(A → A → bool). ordered_field_on(F, lt) ∧ lt(a, F.zero)",
	},
		"Real closed field transfer design, Artin separation. The preordering ΣF² "+
			"+ (-a)ΣF² is proper: an equation -1=s-at would express a as a sum of "+
			"squares after dividing by t². Extend it to a positive cone and use a ≠ 0."),
})}
