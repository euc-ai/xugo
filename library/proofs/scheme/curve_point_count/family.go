package curve_point_count

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed curve_point_count.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/curve_point_count", familyCNF).WithAbbrev(Abbrev{
	{Name: "ambientRing", Text: "restrict_ring(field_ring(M), K)"},
	{Name: "ambientCurve", Text: "smooth_finite_curve(restrict_field(M, K), k, t, A₀, A₁, A₀₁)"},
	{Name: "ambientInvertible", Text: "invertible_lattice_pair(restrict_ring(field_ring(M), K), " +
		"    A₀, " +
		"    A₁, " +
		"    A₀₁)"},
	{Name: "ambientPoint", Text: "curve_closed_point(restrict_ring(field_ring(M), K), A₀, A₁, A₀₁)"},
	{Name: "ambientPointDegree", Text: "curve_closed_degree(restrict_ring(field_ring(M), K), " +
		"    k, " +
		"    A₀, " +
		"    A₁)"},
	{Name: "scOver", Text: "λp:prod(bool, A → A). λP:prod(set(A), set(A)). " +
		"    (fst(p) ⇔ fst(P) = A₀) ∧ " +
		"    ring_kernel(M.zero, point_chart(A₀, A₁, P), snd(p)) = point_ideal(A₀, P)"},
})
