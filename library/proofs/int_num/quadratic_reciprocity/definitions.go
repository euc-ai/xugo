package quadratic_reciprocity

import (
	_ "github.com/euc-ai/xugo/library/proofs/int_num/quadratic_residue"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/int/int_product"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_multiplicity"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/registry"
)

// JacobiSymbolDef — (a/n): the product over the primes p dividing n of
// (a/p) raised to the multiplicity of p in n.
var JacobiSymbolDef = jacobiSymbolDefThm{family.Define(registry.DefEntry{
	Name:  "JacobiSymbolDef",
	Key:   "prop_f91686ca62bebd39",
	Const: "jacobi_symbol",
	Type:  "int → num → int",
	Equations: []string{"∀a:int. ∀n:num. " +
		"    jacobi_symbol(a, n) = " +
		"    int_product({p:num | nat_prime(p) ∧ p ∣ n}, " +
		"        λp:num. legendre_symbol(a, p) ^ nat_multiplicity(p, n))"},
})}
