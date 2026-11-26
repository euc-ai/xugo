package weighted_divisors

import (
	_ "github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/registry"
)

var WeightedEffectiveDef = weightedEffectiveDefThm{family.Define(registry.DefEntry{
	Name:  "WeightedEffectiveDef",
	Key:   "prop_7629dfc36ac8de72",
	Deps:  []registry.EntryLike{},
	Const: "weighted_effective",
	Type:  "set(A) → (A → num) → (A → num) → bool",
	Equations: []string{
		"∀S:set(A). ∀w D:(A → num). " +
			"    weighted_effective(S, w, D) ⇔ finite(fun_support(0, D)) ∧ (∀x:A. D(x) ≠ 0 ⇒ x ∈ S ∧ 0 < w(x))",
	},
})}

var WeightedDegreeDef = weightedDegreeDefThm{family.Define(registry.DefEntry{
	Name:  "WeightedDegreeDef",
	Key:   "prop_8f8656bc92a72954",
	Deps:  []registry.EntryLike{},
	Const: "weighted_degree",
	Type:  "(A → num) → (A → num) → num",
	Equations: []string{
		"∀w D:(A → num). weighted_degree(w, D) = nat_sum(fun_support(0, D), λx:A. w(x) * D(x))",
	},
})}

var WeightedCountDef = weightedCountDefThm{family.Define(registry.DefEntry{
	Name:  "WeightedCountDef",
	Key:   "prop_9581404d439330f7",
	Deps:  []registry.EntryLike{WeightedEffectiveDef, WeightedDegreeDef},
	Const: "weighted_count",
	Type:  "set(A) → (A → num) → num → num",
	Equations: []string{
		"∀S:set(A). ∀w:(A → num). ∀n:num. " +
			"    weighted_count(S, w, n) = " +
			"    card({D:(A → num) | weighted_effective(S, w, D) ∧ weighted_degree(w, D) = n})",
	},
})}

var WeightedMultiplesDef = weightedMultiplesDefThm{family.Define(registry.DefEntry{
	Name:  "WeightedMultiplesDef",
	Key:   "prop_943551c7f9c07993",
	Deps:  []registry.EntryLike{},
	Const: "weighted_multiples",
	Type:  "set(A) → (A → num) → num → num",
	Equations: []string{
		"∀S:set(A). ∀w:(A → num). ∀m:num. " +
			"    weighted_multiples(S, w, m) = COND(m = 0, 0, nat_sum({x:A | x ∈ S ∧ w(x) ∣ m}, w))",
	},
})}
