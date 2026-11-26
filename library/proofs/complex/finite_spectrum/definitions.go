package finite_spectrum

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/formal_series"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/registry"
)

var PowerSumDef = powerSumDefThm{family.Define(registry.DefEntry{
	Name:  "PowerSumDef",
	Key:   "prop_93cee35ddb55c882",
	Deps:  []registry.EntryLike{},
	Const: "finite_power_sum",
	Type:  "num → (num → complex) → num → complex",
	Equations: []string{
		"∀s m:num. ∀a:(num → complex). " +
			"    finite_power_sum(s, a, m) = " +
			"    module_sum(complex_add, " +
			"        complex_of_real(real_of_num(0)), " +
			"        {i:num | i < s}, " +
			"        λi:num. monoid_pow(complex_mul, complex_of_real(real_of_num(1)), a(i), m))",
	},
})}

var ReciprocalProductDef = reciprocalProductDefThm{family.Define(registry.DefEntry{
	Name:  "ReciprocalProductDef",
	Key:   "prop_6949985402f02051",
	Deps:  []registry.EntryLike{},
	Const: "reciprocal_product",
	Type:  "num → (num → complex) → num → complex",
	Equations: []string{
		"∀s:num. ∀a:(num → complex). " +
			"    reciprocal_product(s, a) = " +
			"    set_fold(λi:num. λP:(num → complex). " +
			"            polynomial_mul(complex_add, " +
			"                complex_of_real(real_of_num(0)), " +
			"                complex_mul, " +
			"                (λn:num. " +
			"                    COND(n = 0, " +
			"                        complex_of_real(real_of_num(1)), " +
			"                        COND(n = 1, complex_neg(a(i)), complex_of_real(real_of_num(0))))), " +
			"                P), " +
			"        {i:num | i < s}, " +
			"        basis_vector(complex_of_real(real_of_num(0)), complex_of_real(real_of_num(1)), 0))",
	},
})}
