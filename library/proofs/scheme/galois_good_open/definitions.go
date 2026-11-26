package galois_good_open

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/registry"
)

var GeometricEvaluationPointsDef = geometricEvaluationPointsDefThm{family.Define(registry.DefEntry{
	Name: "GeometricEvaluationPointsDef",
	Key:  "prop_2e93e6ddfb9c2149",
	Reading: "The geometric points of the chart C over k: the k-algebra " +
		"maps from C to the algebraic closure of k in M, each the identity on k.",
	Deps:  []registry.EntryLike{},
	Const: "geometric_evaluation_points",
	Type:  "field_ops(A) → set(A) → set(A) → (set(A → A))",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀C:set(A). " +
			"    geometric_evaluation_points(R, k, C) = " +
			"    algebra_points(restrict_ring(field_ring(R), C), " +
			"        restrict_ring(field_ring(R), algebraic_elements(R, k)), " +
			"        k, " +
			"        (λx:A. x))",
	},
})}

var GeometricFibreDef = geometricFibreDefThm{family.Define(registry.DefEntry{
	Name:    "GeometricFibreDef",
	Key:     "prop_360dd867e0199a2d",
	Reading: "The geometric points of the chart C lying over the point x of the t-line.",
	Deps:    []registry.EntryLike{GeometricEvaluationPointsDef},
	Const:   "geometric_fibre",
	Type:    "field_ops(A) → set(A) → set(A) → A → A → (set(A → A))",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀C:set(A). ∀t:A. ∀x:A. " +
			"    geometric_fibre(R, k, C, t, x) = " +
			"    {ev:(A → A) | ev ∈ geometric_evaluation_points(R, k, C) ∧ ev(t) = x}",
	},
})}

var EvaluationActionDef = evaluationActionDefThm{family.Define(registry.DefEntry{
	Name:  "EvaluationActionDef",
	Key:   "prop_491b310a4f321bdd",
	Deps:  []registry.EntryLike{},
	Const: "evaluation_action",
	Type:  "ring_ops(A) → set(A) → permutation(A) → (A → A) → A → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀C:set(A). ∀s:permutation(A). ∀ev:(A → A). ∀x:A. " +
			"    evaluation_action(R, C, s, ev, x) = " +
			"    COND(x ∈ C, ev(permutation_map(permutation_inverse(s), x)), R.zero)",
	},
})}

var InvariantChartDef = invariantChartDefThm{family.Define(registry.DefEntry{
	Name:  "InvariantChartDef",
	Key:   "prop_27e045e4766dda98",
	Deps:  []registry.EntryLike{},
	Const: "invariant_chart",
	Type:  "set(A) → set(permutation(A)) → set(A)",
	Equations: []string{
		"∀C:set(A). ∀H:set(permutation(A)). " +
			"    invariant_chart(C, H) = " +
			"    {x:A | x ∈ C ∧ (∀s:permutation(A). s ∈ H ⇒ permutation_map(s, x) = x)}",
	},
})}

var GaloisGoodOpenDef = galoisGoodOpenDefThm{family.Define(registry.DefEntry{
	Name: "GaloisGoodOpenDef",
	Key:  "prop_cc8708fd562fc4fc",
	Reading: "(C, a) is a good open of the Galois cover L/k(t): L is a regular function field " +
		"over the finite field k, t in L is transcendental over k, and L is Galois over k(t). C is a " +
		"ring inside L holding k[t] with a(t) inverted, for a nonzero polynomial a over k, and " +
		"inverting a(t); L is its fraction field, it is a finite module over k[t] with a(t) inverted, " +
		"and every automorphism of L over k(t) keeps it. Over each algebraic point x with a(x) ≠ 0 " +
		"the geometric fibre of C is a torsor of the Galois group of L over k(t): the group acts " +
		"freely on it, it has as many points as the group, any two of its points are translates, and " +
		"for each subgroup H its restrictions to the invariant chart of H are the fibre of that " +
		"chart, two points agreeing there exactly when an element of H moves one to the other.",
	Deps: []registry.EntryLike{
		GeometricEvaluationPointsDef,
		GeometricFibreDef,
		EvaluationActionDef,
		InvariantChartDef,
	},
	Const: "galois_good_open",
	Type:  "field_ops(A) → set(A) → set(A) → A → set(A) → (num → A) → bool",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀L:set(A). ∀C:set(A). ∀t:A. ∀a:(num → A). " +
			"    galois_good_open(R, k, L, t, C, a) ⇔ " +
			"    regular_function_field(R, k, L) ∧ " +
			"    finite(k) ∧ " +
			"    t ∈ L ∧ " +
			"    ¬algebraic_over(R, k, t) ∧ " +
			"    galois_over(R, field_adjoin(R, k, {t}), L) ∧ " +
			"    C ⊆ L ∧ " +
			"    comm_ring_on(restrict_ring(field_ring(R), C)) ∧ " +
			"    polynomial_over(R.zero, k, a) ∧ " +
			"    a ≠ vec_zero(R.zero) ∧ " +
			"    ring_away(field_ring(R), " +
			"        polynomial_image(field_ring(R), k, t), " +
			"        polynomial_eval(R.add, R.zero, R.mul, R.one, a, t)) ⊆ " +
			"    C ∧ " +
			"    C = ring_away(field_ring(R), C, polynomial_eval(R.add, R.zero, R.mul, R.one, a, t)) ∧ " +
			"    fraction_field_carrier(restrict_ring(field_ring(R), L), C) ∧ " +
			"    module_finitely_generated(restrict_ring(field_ring(R), " +
			"            ring_away(field_ring(R), " +
			"                polynomial_image(field_ring(R), k, t), " +
			"                polynomial_eval(R.add, R.zero, R.mul, R.one, a, t))), " +
			"        restrict_module(regular_module(field_ring(R)), C)) ∧ " +
			"    (∀s:permutation(A). " +
			"        s ∈ field_automorphisms(R, field_adjoin(R, k, {t}), L) ⇒ " +
			"        image(permutation_map(s), C) = C) ∧ " +
			"    (∀x:A. " +
			"        x ∈ algebraic_elements(R, k) ∧ " +
			"        polynomial_eval(R.add, R.zero, R.mul, R.one, a, x) ≠ R.zero ⇒ " +
			"        free_finite_action(galois_group(R, field_adjoin(R, k, {t}), L), " +
			"            geometric_fibre(R, k, C, t, x), " +
			"            evaluation_action(field_ring(R), C)) ∧ " +
			"        card(geometric_fibre(R, k, C, t, x)) = " +
			"        card(field_automorphisms(R, field_adjoin(R, k, {t}), L)) ∧ " +
			"        (∀ev ew:(A → A). " +
			"            ev ∈ geometric_fibre(R, k, C, t, x) ∧ ew ∈ geometric_fibre(R, k, C, t, x) ⇒ " +
			"            ∃s:permutation(A). " +
			"                s ∈ field_automorphisms(R, field_adjoin(R, k, {t}), L) ∧ " +
			"                evaluation_action(field_ring(R), C, s, ev) = ew) ∧ " +
			"        (∀H:set(permutation(A)). " +
			"            subgroup(galois_group(R, field_adjoin(R, k, {t}), L), H) ⇒ " +
			"            image((λev:(A → A). (λy:A. COND(y ∈ invariant_chart(C, H), ev(y), R.zero))), " +
			"                geometric_fibre(R, k, C, t, x)) = " +
			"            geometric_fibre(R, k, invariant_chart(C, H), t, x) ∧ " +
			"            (∀ev ew:(A → A). " +
			"                ev ∈ geometric_fibre(R, k, C, t, x) ∧ ew ∈ geometric_fibre(R, k, C, t, x) ⇒ " +
			"                ((∀y:A. y ∈ invariant_chart(C, H) ⇒ ev(y) = ew(y)) ⇔ " +
			"                    ∃s:permutation(A). " +
			"                        s ∈ H ∧ evaluation_action(field_ring(R), C, s, ev) = ew))))",
	},
})}
