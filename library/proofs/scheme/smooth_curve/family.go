package smooth_curve

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed smooth_curve.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/smooth_curve", familyCNF).WithAbbrev(Abbrev{
	{Name: "chart", Text: "restrict_ring(field_ring(L), A₀)"},
	{Name: "overlap", Text: "restrict_ring(field_ring(L), A₀₁)"},
	{Name: "scCurve", Text: "smooth_finite_curve(L, k, t, A₀, A₁, A₀₁)"},
	{Name: "scPoint", Text: "curve_closed_point(field_ring(L), A₀, A₁, A₀₁)"},
	{Name: "scPointDegree", Text: "curve_closed_degree(field_ring(L), k, A₀, A₁)"},
	{Name: "ambientRing", Text: "restrict_ring(field_ring(M), K)"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
