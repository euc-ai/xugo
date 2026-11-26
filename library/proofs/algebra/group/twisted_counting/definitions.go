package twisted_counting

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/registry"
)

var FreeFiniteActionDef = freeFiniteActionDefThm{family.Define(registry.DefEntry{
	Name:  "FreeFiniteActionDef",
	Key:   "prop_96e77968fae417c2",
	Deps:  []registry.EntryLike{},
	Const: "free_finite_action",
	Type:  "group_ops(A) → set(B) → (A → B → B) → bool",
	Equations: []string{
		"∀G:group_ops(A). ∀X:set(B). ∀act:(A → B → B). " +
			"    free_finite_action(G, X, act) ⇔ " +
			"    group_on(G) ∧ " +
			"    finite(G.carrier) ∧ " +
			"    finite(X) ∧ " +
			"    (∀x:B. x ∈ X ⇒ act(G.one, x) = x) ∧ " +
			"    (∀g h:A. ∀x:B. " +
			"        g ∈ G.carrier ∧ h ∈ G.carrier ∧ x ∈ X ⇒ " +
			"        act(g, x) ∈ X ∧ act(G.mul(g, h), x) = act(g, act(h, x)) ∧ (act(g, x) = x ⇒ g = G.one))",
	},
})}
