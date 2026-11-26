package rational_point_bound

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed rational_point_bound.cnf.pb
var familyCNF []byte

// _LatticePair is the Go type of a pair of subsets of the field: a lattice
// pair, a point.
type _LatticePair = Prod[Set[A], Set[A]]

var family = registry.NewFamily("scheme/rational_point_bound", familyCNF).WithAbbrev(Abbrev{
	{Name: "rbAmbientRing", Text: "restrict_ring(field_ring(M), K)"},
	{Name: "rbScalars", Text: "restrict_ring(field_ring(L), k)"},
	{Name: "rbCurve", Text: "curve_over_line(L, k, t, A₀, A₁, A₀₁)"},
	{Name: "rbPoint", Text: "biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁)"},
	{Name: "rbGenus", Text: "curve_genus(field_ring(L), k, A₀, A₁, A₀₁)"},
	{Name: "rbPoles", Text: "single_point_pole_space(field_ring(L), A₀, A₁, P)"},
	{Name: "rbPoleDim", Text: "λn:num. module_dim(«rbScalars», «rbPoles»(n))"},
	{Name: "rbPolePair", Text: "λn:num. " +
		"    monoid_pow(λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). " +
		"            lattice_pair_mul(field_ring(L), A₀, A₁, X, Y), " +
		"        (A₀, A₁), " +
		"        lattice_pair_inverse(field_ring(L), A₀, A₁, P), " +
		"        n)"},
	{Name: "rbOrder", Text: "regular_point_order(field_ring(L), A₀, A₁, P)"},
	{Name: "rbEvaluation", Text: "regular_point_evaluation(field_ring(L), k, A₀, A₁)"},
	{Name: "rbTensor", Text: "frobenius_tensor(field_ring(L), E, F, s)"},
	{Name: "rbSwap", Text: "frobenius_swap(field_ring(L), E, F, s)"},
})
