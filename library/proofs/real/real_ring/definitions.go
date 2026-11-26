// definitions.go — the chapter's definitional layer: subtraction.
//
// The tower delivers ℝ with addition, negation and multiplication;
// subtraction is not among them, because it is not needed to state the
// axioms. It is defined here, where the ring laws that first use it
// are proved: `x − y` is `x + (−y)`, and every fact about it in this
// chapter is that equation read in one direction or the other.

package real_ring

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/registry"
)

// RealSubDef — subtraction is addition of the negation.
var RealSubDef = realSubDefThm{family.Define(registry.DefEntry{
	Name:      "RealSubDef",
	Key:       "prop_b2464898216f6125",
	Const:     "real_sub",
	Type:      "real → real → real",
	Equations: []string{"∀x y:real. real_sub(x, y) = x + -y"},
})}

// RealRingDef — the real ring operations and its whole-type carrier.
var RealRingDef = realRingDefThm{family.Define(registry.DefEntry{
	Name: "RealRingDef",
	Key:  "prop_82a2afd0460f2b8f", Const: "real_ring", Type: "ring_ops(real)",
	Equations: []string{"real_ring = mk_ring(real_add, &0, real_neg, real_mul, &1, real_sub, 𝕌)"},
	Deps:      []registry.EntryLike{RealSubDef},
})}
