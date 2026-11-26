package regular_point

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed regular_point.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/regular_point", familyCNF).WithAbbrev(Abbrev{
	{Name: "rpScalars", Text: "restrict_ring(field_ring(L), k)"},
	{Name: "rpCurve", Text: "curve_over_line(L, k, t, A₀, A₁, A₀₁)"},
	{Name: "rpPoint", Text: "biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁)"},
	{Name: "rpGenus", Text: "curve_genus(field_ring(L), k, A₀, A₁, A₀₁)"},
	{Name: "rpPoles", Text: "single_point_pole_space(field_ring(L), A₀, A₁, P)"},
	{Name: "rpPoleDim", Text: "λn:num. module_dim(«rpScalars», «rpPoles»(n))"},
	{Name: "rpPolePair", Text: "λn:num. " +
		"    monoid_pow(λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). " +
		"            lattice_pair_mul(field_ring(L), A₀, A₁, X, Y), " +
		"        (A₀, A₁), " +
		"        lattice_pair_inverse(field_ring(L), A₀, A₁, P), " +
		"        n)"},
	{Name: "rpOrder", Text: "regular_point_order(field_ring(L), A₀, A₁, P)"},
	{Name: "rpEvaluation", Text: "regular_point_evaluation(field_ring(L), k, A₀, A₁)"},
})

// _LatticePair is the Go type of a pair of subsets of the field: a lattice
// pair, a point.
type _LatticePair = Prod[Set[A], Set[A]]
