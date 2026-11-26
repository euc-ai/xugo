package totient

import (
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// TotientDef — Euler's φ(n): the residues below n that are coprime to n.
// The residue 0 counts at n = 1, where it is coprime to n.
var TotientDef = totientDefThm{family.Define(registry.DefEntry{
	Name:      "TotientDef",
	Key:       "prop_632fd94e8db2bd6c",
	Const:     "totient",
	Type:      "num → num",
	Equations: []string{"∀n:num. totient(n) = card({a:num | a < n ∧ nat_coprime(a, n)})"},
})}
