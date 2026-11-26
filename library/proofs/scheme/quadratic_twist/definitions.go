package quadratic_twist

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/closed_point"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/elliptic_curve"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/zeta_recurrence"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

var twistCoefficientsDef = twistCoefficientsDefThm{family.Define(registry.DefEntry{
	Name:  "twistCoefficientsDef",
	Key:   "prop_ebe74cc466c9f337",
	Const: "twist_coefficients",
	Type:  "field_ops(A) → A → A → A → prod(A, A)",
	Equations: []string{
		"∀R:field_ops(A). ∀a:A. ∀b:A. ∀e:A. " +
			"    twist_coefficients(R, a, b, e) = " +
			"    (R.mul(a, monoid_pow(R.mul, R.one, R.inv(e), 2)), " +
			"        R.mul(b, monoid_pow(R.mul, R.one, R.inv(e), 3)))",
	},
	Deps: []registry.EntryLike{},
	Reading: "The output is a coefficient pair, never a curve or a datum in the original " +
		"function field. Nonzero nonsquare e and the field hypotheses are supplied by the laws.",
})}
