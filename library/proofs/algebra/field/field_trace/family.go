// family.go — the field_trace registry and its shared replay record.

package field_trace

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed field_trace.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/field_trace", familyCNF).WithAbbrev(Abbrev{
	{Name: "ftDerivative", Text: "polynomial_eval( " +
		"    polynomial_derivative(minimal_polynomial(L, K, y)), y)"},
	{Name: "ftQuotient", Text: "ideal_quotient_ring(mk_ring(vec_add, " +
		"        vec_zero, " +
		"        vec_neg, " +
		"        polynomial_mul, " +
		"        basis_vector(0), " +
		"        vec_sub, " +
		"        {h:(num → A) | polynomial_over(L.carrier, h)}), " +
		"    ideal_span(mk_ring(vec_add, " +
		"            vec_zero, " +
		"            vec_neg, " +
		"            polynomial_mul, " +
		"            basis_vector(0), " +
		"            vec_sub, " +
		"            {h:(num → A) | polynomial_over(L.carrier, h)}), " +
		"        {minimal_polynomial(L, K, y)}))"},
	{Name: "ftQuotientModule", Text: "trace_quotient_module(L, minimal_polynomial(L, K, y))"},
})
