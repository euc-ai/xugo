// definitions.go — the chapter's definitional layer: `>` and `≥`.
//
// `<` is defined too, but beside the laws it is stated among
// (NotLessEq, real_order_ring.go): it was already a member of this
// chapter before the definition moved into Go, and the equation the
// member states IS the definition. `>` and `≥` have no such twin, so
// they live here. None carries content of its own — every law about
// them in this chapter unfolds to a statement about `≤`.

package real_order_ring

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealGtDef — strictly above: the strict order, read backwards.
var RealGtDef = realGtDefThm{family.Define(registry.DefEntry{
	Name:      "RealGtDef",
	Key:       "prop_a5e00e7bf6429b95",
	Const:     "real_gt",
	Type:      "real → real → bool",
	Equations: []string{"∀x y:real. real_gt(x, y) ⇔ y < x"},
	Deps:      []registry.EntryLike{NotLessEq},
})}

// RealGeDef — at least: the order, read backwards.
var RealGeDef = realGeDefThm{family.Define(registry.DefEntry{
	Name:      "RealGeDef",
	Key:       "prop_a16e7686982a8587",
	Const:     "real_ge",
	Type:      "real → real → bool",
	Equations: []string{"∀x y:real. real_ge(x, y) ⇔ y ≤ x"},
})}
