package semialgebraic_properties

import (
	"github.com/euc-ai/xugo/library/registry"

	// The definitions spell the constants of field, ordered_field, polynomial_encoding,
	// polynomial_eval, set_basic and nat_order: the imports initialize those mints before the
	// definitions here are parsed.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_encoding"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
)

// ConstraintSetDef — The normalized tuples satisfying the closed polynomial constraints.
var ConstraintSetDef = constraintSetDefThm{family.Define(registry.DefEntry{
	Name:  "ConstraintSetDef",
	Const: "polynomial_constraint_set",
	Type: "field_ops(A) → " +
		"(A → A → bool) → " +
		"num → " +
		"num → " +
		"num → " +
		"(num → (num → num) → A) → " +
		"(num → (num → num) → A) → " +
		"set(num → A)",
	Key: "prop_66b70a6e899c275b",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀n s t:num. ∀g h:(num → (num → num) → A). " +
			"    polynomial_constraint_set(F, lt, n, s, t, g, h) = " +
			"    {x:(num → A) | " +
			"        ring_tuple(field_ring(F), n, x) ∧ " +
			"        (∀j:num. j < s ⇒ ordered_le(lt, F.zero, polynomial_value(field_ring(F), g(j), x))) ∧ " +
			"        (∀j:num. j < t ⇒ polynomial_value(field_ring(F), h(j), x) = F.zero)}",
	},
})}

// BoundedSetDef — A positive carrier element bounds every active coordinate of the set.
var BoundedSetDef = boundedSetDefThm{family.Define(registry.DefEntry{
	Name:  "BoundedSetDef",
	Const: "polynomial_box_bound",
	Type:  "field_ops(A) → (A → A → bool) → num → set(num → A) → A → bool",
	Key:   "prop_5785fe4975bc6979",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀n:num. ∀S:set(num → A). ∀M:A. " +
			"    polynomial_box_bound(F, lt, n, S, M) ⇔ " +
			"    M ∈ F.carrier ∧ " +
			"    lt(F.zero, M) ∧ " +
			"    (∀x:(num → A). " +
			"        x ∈ S ⇒ ∀j:num. j < n ⇒ ordered_le(lt, F.neg(M), x(j)) ∧ ordered_le(lt, x(j), M))",
	},
})}

// LexMinimizerDef — Minimize f first, then minimize q among all primary minimizers; uniqueness is not asserted.
var LexMinimizerDef = lexMinimizerDefThm{family.Define(registry.DefEntry{
	Name:  "LexMinimizerDef",
	Const: "polynomial_lex_minimizer",
	Type: "field_ops(A) → " +
		"(A → A → bool) → " +
		"set(num → A) → " +
		"((num → num) → A) → " +
		"((num → num) → A) → " +
		"(num → A) → " +
		"bool",
	Key: "prop_3d166f11133dcc8a",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀S:set(num → A). ∀f q:((num → num) → A). ∀x:(num → A). " +
			"    polynomial_lex_minimizer(F, lt, S, f, q, x) ⇔ " +
			"    x ∈ S ∧ " +
			"    (∀y:(num → A). " +
			"        y ∈ S ⇒ " +
			"        ordered_le(lt, " +
			"            polynomial_value(field_ring(F), f, x), " +
			"            polynomial_value(field_ring(F), f, y))) ∧ " +
			"    (∀y:(num → A). " +
			"        y ∈ S ∧ " +
			"        (∀z:(num → A). " +
			"            z ∈ S ⇒ " +
			"            ordered_le(lt, " +
			"                polynomial_value(field_ring(F), f, y), " +
			"                polynomial_value(field_ring(F), f, z))) ⇒ " +
			"        ordered_le(lt, " +
			"            polynomial_value(field_ring(F), q, x), " +
			"            polynomial_value(field_ring(F), q, y)))",
	},
})}

// LexPropertyDef — The degree-bounded lexicographic minimum statement universal in all coefficient data.
var LexPropertyDef = lexPropertyDefThm{family.Define(registry.DefEntry{
	Name:  "LexPropertyDef",
	Const: "lexicographic_minimum_property",
	Type:  "field_ops(A) → (A → A → bool) → num → num → num → num → bool",
	Key:   "prop_fef2abd9690df795",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀n s t d:num. " +
			"    lexicographic_minimum_property(F, lt, n, s, t, d) ⇔ " +
			"    ∀f q:((num → num) → A). ∀g h:(num → (num → num) → A). ∀M:A. " +
			"        polynomial_bound(field_ring(F), n, d, f) ∧ " +
			"        polynomial_bound(field_ring(F), n, d, q) ∧ " +
			"        (∀j:num. j < s ⇒ polynomial_bound(field_ring(F), n, d, g(j))) ∧ " +
			"        (∀j:num. j < t ⇒ polynomial_bound(field_ring(F), n, d, h(j))) ∧ " +
			"        polynomial_constraint_set(F, lt, n, s, t, g, h) ≠ ∅ ∧ " +
			"        polynomial_box_bound(F, lt, n, polynomial_constraint_set(F, lt, n, s, t, g, h), M) ⇒ " +
			"        ∃x:(num → A). " +
			"            polynomial_lex_minimizer(F, " +
			"                lt, " +
			"                polynomial_constraint_set(F, lt, n, s, t, g, h), " +
			"                f, " +
			"                q, " +
			"                x)",
	},
	Deps: []registry.EntryLike{BoundedSetDef, ConstraintSetDef, LexMinimizerDef},
})}

// CarrierCubeDef — The carrier cube: the n-tuples of carrier points with every coordinate between 0 and 1.
var CarrierCubeDef = carrierCubeDefThm{family.Define(registry.DefEntry{
	Name:  "CarrierCubeDef",
	Const: "carrier_cube",
	Type:  "field_ops(A) → (A → A → bool) → num → set(num → A)",
	Key:   "prop_89cd5c1a5ce3948a",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀n:num. " +
			"    carrier_cube(F, lt, n) = " +
			"    {x:(num → A) | " +
			"        ring_tuple(field_ring(F), n, x) ∧ " +
			"        (∀j:num. j < n ⇒ ordered_le(lt, F.zero, x(j)) ∧ ordered_le(lt, x(j), F.one))}",
	},
})}

// BrouwerPropertyDef — Every degree-bounded polynomial self-map of the cube has a fixed point.
var BrouwerPropertyDef = brouwerPropertyDefThm{family.Define(registry.DefEntry{
	Name:  "BrouwerPropertyDef",
	Const: "polynomial_brouwer_property",
	Type:  "field_ops(A) → (A → A → bool) → num → num → bool",
	Key:   "prop_58878c8f5ed345c",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀n d:num. " +
			"    polynomial_brouwer_property(F, lt, n, d) ⇔ " +
			"    ∀P:(num → (num → num) → A). " +
			"        (∀j:num. j < n ⇒ polynomial_bound(field_ring(F), n, d, P(j))) ∧ " +
			"        (∀x:(num → A). " +
			"            x ∈ carrier_cube(F, lt, n) ⇒ " +
			"            polynomial_map(field_ring(F), n, P, x) ∈ carrier_cube(F, lt, n)) ⇒ " +
			"        ∃x:(num → A). x ∈ carrier_cube(F, lt, n) ∧ polynomial_map(field_ring(F), n, P, x) = x",
	},
	Deps: []registry.EntryLike{CarrierCubeDef},
})}

// CubePositiveBoundPropertyDef — The degree-bounded statement that a polynomial positive on the carrier cube has a positive lower bound there.
var CubePositiveBoundPropertyDef = cubePositiveBoundPropertyDefThm{family.Define(registry.DefEntry{
	Name:  "CubePositiveBoundPropertyDef",
	Const: "cube_positive_bound_property",
	Type:  "field_ops(A) → (A → A → bool) → num → num → bool",
	Key:   "prop_4bb042eba4c22674",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀n d:num. " +
			"    cube_positive_bound_property(F, lt, n, d) ⇔ " +
			"    ∀p:((num → num) → A). " +
			"        polynomial_bound(field_ring(F), n, d, p) ∧ " +
			"        (∀x:(num → A). " +
			"            x ∈ carrier_cube(F, lt, n) ⇒ lt(F.zero, polynomial_value(field_ring(F), p, x))) ⇒ " +
			"        ∃e:A. " +
			"            e ∈ F.carrier ∧ " +
			"            lt(F.zero, e) ∧ " +
			"            (∀x:(num → A). " +
			"                x ∈ carrier_cube(F, lt, n) ⇒ " +
			"                ordered_le(lt, e, polynomial_value(field_ring(F), p, x)))",
	},
	Deps: []registry.EntryLike{CarrierCubeDef},
})}

// IntervalMinimumPropertyDef — The statement that a polynomial in one variable with at most n coefficients attains its minimum on every nonempty closed interval.
var IntervalMinimumPropertyDef = intervalMinimumPropertyDefThm{family.Define(registry.DefEntry{
	Name:  "IntervalMinimumPropertyDef",
	Const: "interval_minimum_property",
	Type:  "field_ops(A) → (A → A → bool) → num → bool",
	Key:   "prop_b9b2108b2e9c6bd8",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀n:num. " +
			"    interval_minimum_property(F, lt, n) ⇔ " +
			"    ∀p:(num → A). ∀a b:A. " +
			"        ring_tuple(field_ring(F), n, p) ∧ " +
			"        a ∈ F.carrier ∧ " +
			"        b ∈ F.carrier ∧ " +
			"        ordered_le(lt, a, b) ⇒ " +
			"        ∃u:A. " +
			"            u ∈ F.carrier ∧ " +
			"            ordered_le(lt, a, u) ∧ " +
			"            ordered_le(lt, u, b) ∧ " +
			"            (∀x:A. " +
			"                x ∈ F.carrier ∧ ordered_le(lt, a, x) ∧ ordered_le(lt, x, b) ⇒ " +
			"                ordered_le(lt, polynomial_eval(p, u), polynomial_eval(p, x)))",
	},
})}
