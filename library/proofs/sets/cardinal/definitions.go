// definitions.go — the chapter's definitional layer: the three ways two
// sets compare in size, and countability.
//
// Each comparison asks for a map, and says nothing about counting: the
// sets may be infinite, and the map is the whole content. The two sets
// may sit in different types, so every relation here is stated at a
// pair of element types.

package cardinal

import (
	"github.com/euc-ai/xugo/library/registry"
)

// CardLeDef — `card_le(s, t)`: s is no larger than t, some map sending
// s into t and injective on s.
var CardLeDef = cardLeDefThm{family.Define(registry.DefEntry{
	Name:  "CardLeDef",
	Key:   "prop_5f7abd7de4154860",
	Const: "card_le",
	Type:  "set(A) → set(B) → bool",
	Equations: []string{
		"∀s:set(A). ∀t:set(B). card_le(s, t) ⇔ ∃f:(A → B). (∀x:A. x ∈ s ⇒ f(x) ∈ t) ∧ injective_on(s, f)",
	},
})}

// CardEqDef — `card_eq(s, t)`: s and t are the same size, some map
// injective on s whose image of s is t — a bijection of s onto t.
var CardEqDef = cardEqDefThm{family.Define(registry.DefEntry{
	Name:  "CardEqDef",
	Key:   "prop_bbb7f08dff8b1e56",
	Const: "card_eq",
	Type:  "set(A) → set(B) → bool",
	Equations: []string{
		"∀s:set(A). ∀t:set(B). card_eq(s, t) ⇔ ∃f:(A → B). injective_on(s, f) ∧ image(f, s) = t",
	},
})}

// CardLtDef — `card_lt(s, t)`: s is strictly smaller than t, no larger
// and not the other way round.
var CardLtDef = cardLtDefThm{family.Define(registry.DefEntry{
	Name:      "CardLtDef",
	Key:       "prop_cd28b4321237b81d",
	Const:     "card_lt",
	Type:      "set(A) → set(B) → bool",
	Equations: []string{"∀s:set(A). ∀t:set(B). card_lt(s, t) ⇔ card_le(s, t) ∧ ¬card_le(t, s)"},
	Deps:      []registry.EntryLike{CardLeDef},
})}

// CountableDef — `countable(s)`: s is no larger than ℕ.
var CountableDef = countableDefThm{family.Define(registry.DefEntry{
	Name:      "CountableDef",
	Key:       "prop_9a08fd01cdae5c4",
	Const:     "countable",
	Type:      "set(A) → bool",
	Equations: []string{"∀s:set(A). countable(s) ⇔ card_le(s, 𝕌⟨A:num⟩)"},
	Deps:      []registry.EntryLike{CardLeDef},
})}
