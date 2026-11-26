package principal_ideal_domain

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/registry"
)

var FinitelyGeneratedDef = finitelyGeneratedDefThm{family.Define(registry.DefEntry{
	Name:    "FinitelyGeneratedDef",
	Key:     "prop_996a707516bc1c6",
	Reading: "A finite generating set is not a basis; this definition permits torsion modules.",
	Deps:    []registry.EntryLike{},
	Const:   "module_finitely_generated",
	Type:    "ring_ops(A) → module_ops(A, B) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). " +
			"    module_finitely_generated(R, M) ⇔ " +
			"    ∃E:set(B). finite(E) ∧ E ⊆ M.carrier ∧ module_span(R, M, E) = M.carrier",
	},
})}

var PrincipalIdealDomainDef = principalIdealDomainDefThm{family.Define(registry.DefEntry{
	Name:  "PrincipalIdealDomainDef",
	Key:   "prop_a39d95b5d66d1ec5",
	Deps:  []registry.EntryLike{},
	Const: "principal_ideal_domain",
	Type:  "ring_ops(A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"    principal_ideal_domain(R) ⇔ " +
			"    integral_domain_on(R) ∧ " +
			"    (∀I:set(A). ring_ideal(R, I) ⇒ ∃d:A. d ∈ R.carrier ∧ I = image(R.mul(d), R.carrier))",
	},
})}

var TorsionFreeDef = torsionFreeDefThm{family.Define(registry.DefEntry{
	Name:  "TorsionFreeDef",
	Key:   "prop_85c8ca10573ffebf",
	Deps:  []registry.EntryLike{},
	Const: "module_torsion_free",
	Type:  "ring_ops(A) → module_ops(A, B) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). " +
			"    module_torsion_free(R, M) ⇔ " +
			"    (∀c:A. ∀v:B. c ∈ R.carrier ∧ c ≠ R.zero ∧ v ∈ M.carrier ∧ M.smul(c, v) = M.zero ⇒ v = M.zero)",
	},
})}

var ModuleSaturationDef = moduleSaturationDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleSaturationDef",
	Key:   "prop_16be784239ddd88a",
	Deps:  []registry.EntryLike{},
	Const: "module_saturation",
	Type:  "ring_ops(A) → module_ops(A, B) → A → set(B) → set(B)",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀s:A. ∀U:set(B). " +
			"    module_saturation(R, M, s, U) = " +
			"    {v:B | v ∈ M.carrier ∧ (∃n:num. M.smul(monoid_pow(R.mul, R.one, s, n), v) ∈ U)}",
	},
})}
