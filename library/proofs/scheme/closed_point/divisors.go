package closed_point

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_colength"
	"github.com/euc-ai/xugo/library/registry"
)

var MaximalPowerColength = maximalPowerColengthThm{family.Add(registry.ProofEntry{
	Name: "MaximalPowerColength",
	Key:  "prop_2d87dda7e1a5539e",
	Deps: []registry.EntryLike{
		ClosedPointDef,
		PointDegreeDef,
		ClosedPointDegreePositive,
		ChartZeroMaximalInvertible,
		ideal_colength.InvertibleQuotientDim,
		module_dimension.DimFiniteIffSubAndQuotient,
		module_dimension.QuotientChainDim,
	},
	Reading: "",
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀P:prod(set(A), set(A)). ∀t:num.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"finite(k)",
			"elliptic_closed_point(L, k, x, y, P)",
			"P ≠ weierstrass_origin(L, k, x, y)",
		},
		Conclusion: "finite_dimensional(restrict_ring(field_ring(L), k), " +
			"    quotient_module(restrict_module(regular_module(field_ring(L)), «curveChart0»), " +
			"        ideal_pow(restrict_ring(field_ring(L), «curveChart0»), fst(P), t))) ∧ " +
			"module_dim(restrict_ring(field_ring(L), k), " +
			"    quotient_module(restrict_module(regular_module(field_ring(L)), «curveChart0»), " +
			"        ideal_pow(restrict_ring(field_ring(L), «curveChart0»), fst(P), t))) = " +
			"t * elliptic_point_degree(L, k, x, y, P)",
	},
		"Induct on t. InvertibleQuotientDim identifies each successive quotient "+
			"m^j/m^(j+1) in dimension with A₀/m, and QuotientChainDim adds the "+
			"layers. At t=0 the ideal is A₀ and the quotient has dimension zero."),
})}
