package gauss_sum

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/quadratic_residue"
	"github.com/euc-ai/xugo/library/registry"
)

// GaussSumDef — the quadratic Gauss sum Σ_{a<p} (a/p) ζ^a in the field F,
// each Legendre symbol read in F through the integers' map into it.
var GaussSumDef = gaussSumDefThm{family.Define(registry.DefEntry{
	Name:  "GaussSumDef",
	Key:   "prop_67acd97de90c5661",
	Const: "gauss_sum",
	Type:  "field_ops(A) → A → num → A",
	Equations: []string{"∀F:field_ops(A). ∀ζ:A. ∀p:num. " +
		"    gauss_sum(F, ζ, p) = " +
		"    module_sum(F.add, " +
		"        F.zero, " +
		"        {a:num | a < p}, " +
		"        λa:num. " +
		"            F.mul(integer_map(field_ring(F), legendre_symbol(a, p)), " +
		"                monoid_pow(F.mul, F.one, ζ, a)))"},
})}
