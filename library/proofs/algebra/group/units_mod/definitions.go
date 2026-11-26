package units_mod

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/registry"
)

// UnitsModDef — the units of the integers mod n, as residues: the
// residues below n coprime to n, multiplied and reduced mod n, with
// identity the residue of 1 and each residue's inverse the residue b
// with a * b ≡ 1 (mod n), chosen.
var UnitsModDef = unitsModDefThm{family.Define(registry.DefEntry{
	Name:  "UnitsModDef",
	Key:   "prop_d7dda5e8aa824168",
	Const: "units_mod",
	Type:  "num → group_ops(num)",
	Equations: []string{"∀n:num. " +
		"    units_mod(n) = " +
		"    mk_group(λa:num. λb:num. rem(a * b, n), " +
		"        rem(1, n), " +
		"        λa:num. εb:num. b < n ∧ rem(a * b, n) = rem(1, n), " +
		"        {a:num | a < n ∧ nat_coprime(a, n)})"},
})}
