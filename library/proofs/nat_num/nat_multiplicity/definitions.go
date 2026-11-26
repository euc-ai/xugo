package nat_multiplicity

import (
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/registry"
)

// NatMultiplicityDef — the exponent of p in n: the e with p ^ e dividing
// n and p ^ (e + 1) not, chosen. It is determined when 2 ≤ p and n ≠ 0.
var NatMultiplicityDef = natMultiplicityDefThm{family.Define(registry.DefEntry{
	Name:      "NatMultiplicityDef",
	Key:       "prop_9345cb8f93c38064",
	Const:     "nat_multiplicity",
	Type:      "num → num → num",
	Equations: []string{"∀p n:num. nat_multiplicity(p, n) = εe:num. p ^ e ∣ n ∧ ¬(p ^ (e + 1) ∣ n)"},
})}
