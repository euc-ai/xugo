// definitions.go — the chapter's one definition: the real image of an
// integer sequence, entry by entry.
//
// `vec_of_int(u)` is the sequence `i ↦ real_of_int(u(i))` — the map along
// which the chapter reads ℝⁿ's order theory of the form; the README says
// why that is the chapter's whole definitional layer.

package lattice

import (
	"github.com/euc-ai/xugo/library/registry"
)

// VecOfIntDef — the real image of an integer sequence.
var VecOfIntDef = vecOfIntDefThm{family.Define(registry.DefEntry{
	Name:      "VecOfIntDef",
	Key:       "prop_cd54da8899c5371d",
	Const:     "vec_of_int",
	Type:      "(num → int) → num → real",
	Equations: []string{"∀u:(num → int). ∀i:num. vec_of_int(u, i) = real_of_int(u(i))"},
})}
