// Chartwise nullity, critical points and regular values retain their manifold carriers.

package manifold_critical_point

import (
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_critical_point"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_null"
	"github.com/euc-ai/xugo/library/registry"
)

var NullSetDef = nullSetDefThm{family.Define(registry.DefEntry{
	Name:       "NullSetDef",
	Key:        "prop_6d9020a556ee38e3",
	Const:      "manifold_null_set",
	Type:       "num → set(set(A)) → set(prod(set(A), A → num → real)) → set(A) → bool",
	Dimensions: []string{"n"},
	Reading: "Nullity is measured in every smoothly compatible chart, and K must lie in " +
		"the manifold carrier. No measure or orientation is chosen. The laws supply the " +
		"manifold hypothesis; on a genuine zero-dimensional manifold only the empty set is null.",
	Deps: []registry.EntryLike{},
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀K:set(A). " +
			"    manifold_null_set⟨n⟩(T, 𝒜, K) ⇔ " +
			"    K ⊆ ⋃T ∧ " +
			"    (∀c:prod(set(A), A → num → real). " +
			"        compatible_chart⟨n⟩(T, 𝒜, c) ⇒ vec_null_set⟨n⟩(image(snd(c), K ∩ fst(c))))",
	},
})}

var CriticalPointDef = criticalPointDefThm{family.Define(registry.DefEntry{
	Name:  "CriticalPointDef",
	Key:   "prop_a5b781bf4770ddee",
	Const: "manifold_critical_point",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"(A → B) → " +
		"A → " +
		"bool",
	Dimensions: []string{"n", "m"},
	Reading: "The existential chart test uses failure of surjectivity on " +
		"normalized finite-dimensional vectors. Smoothness is not part of this " +
		"predicate and is a premise of its coordinate-invariance laws. Only " +
		"active chart pairs are tested, on their open chart-preimage domains.",
	Deps: []registry.EntryLike{},
	Equations: []string{
		"∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀x:A. " +
			"    manifold_critical_point⟨n, m⟩(T, 𝒜, S, ℬ, f, x) ⇔ " +
			"    x ∈ ⋃T ∧ " +
			"    (∃c:prod(set(A), A → num → real). ∃d:prod(set(B), B → num → real). " +
			"        compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
			"        compatible_chart⟨m⟩(S, ℬ, d) ∧ " +
			"        x ∈ fst(c) ∧ " +
			"        f(x) ∈ fst(d) ∧ " +
			"        vec_critical_point⟨n, m⟩(«coordinate map»(c, d, f), snd(c)(x)))",
	},
})}

var RegularValueDef = regularValueDefThm{family.Define(registry.DefEntry{
	Name:  "RegularValueDef",
	Key:   "prop_7d1fdb1d0e74284d",
	Const: "manifold_regular_value",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"(A → B) → " +
		"B → " +
		"bool",
	Dimensions: []string{"n", "m"},
	Reading: "A regular value lies in the target carrier and has no critical point " +
		"in its fiber. An empty fiber is allowed. Without the smooth-map hypothesis this " +
		"is only the displayed predicate, not a theorem about differentials.",
	Deps: []registry.EntryLike{CriticalPointDef},
	Equations: []string{
		"∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀y:B. " +
			"    manifold_regular_value⟨n, m⟩(T, 𝒜, S, ℬ, f, y) ⇔ " +
			"    y ∈ ⋃S ∧ (∀z:A. z ∈ ⋃T ∧ f(z) = y ⇒ ¬manifold_critical_point⟨n, m⟩(T, 𝒜, S, ℬ, f, z))",
	},
})}
