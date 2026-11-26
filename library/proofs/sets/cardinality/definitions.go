// definitions.go — the chapter's definitional layer: the fold over a
// finite set, and the count read off it.

package cardinality

import (
	"github.com/euc-ai/xugo/library/registry"
)

// SetFoldDef — the fold of f from b over a set: the function chosen to
// satisfy the recursion clauses on finite sets, read at s.
var SetFoldDef = setFoldDefThm{family.Define(registry.DefEntry{
	Name:  "SetFoldDef",
	Key:   "prop_18aec931c2468a13",
	Const: "set_fold",
	Type:  "(A → B → B) → set(A) → B → B",
	Equations: []string{
		"∀f:(A → B → B). ∀s:set(A). ∀b:B. " +
			"    set_fold(f, s, b) = " +
			"    (εg:(set(A) → B). " +
			"        g(∅) = b ∧ " +
			"        ∀x:A. ∀t:set(A). finite(t) ⇒ g(insert(x, t)) = COND(x ∈ t, g(t), f(x, g(t))))(s)",
	},
})}

// CardDef — the count: the fold that adds one per element.
var CardDef = cardDefThm{family.Define(registry.DefEntry{
	Name:      "CardDef",
	Key:       "prop_a1dbe6c1f6e8cc8e",
	Const:     "card",
	Type:      "set(A) → num",
	Equations: []string{"∀s:set(A). card(s) = set_fold((λx:A. λn:num. suc(n)), s, 0)"},
	Deps:      []registry.EntryLike{SetFoldDef},
})}

// HasSizeDef — having a size: finite, and counted so.
var HasSizeDef = hasSizeDefThm{family.Define(registry.DefEntry{
	Name:      "HasSizeDef",
	Key:       "prop_10598ef607cb9930",
	Const:     "has_size",
	Type:      "set(A) → num → bool",
	Equations: []string{"∀s:set(A). ∀n:num. has_size(s, n) ⇔ finite(s) ∧ card(s) = n"},
	Deps:      []registry.EntryLike{CardDef},
})}
