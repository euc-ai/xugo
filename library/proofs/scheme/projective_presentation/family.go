package projective_presentation

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_form_chart"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed projective_presentation.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/projective_presentation", familyCNF).WithOuterAbbrev(
	projective_form_chart.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "points", Text: "λm:num. " +
		"    projective_equation_points(field_ring(M), " +
		"        k, " +
		"        finite_constants(field_ring(M), card(k), m), " +
		"        n, " +
		"        E)"},
})
