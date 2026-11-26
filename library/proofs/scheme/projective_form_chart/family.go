package projective_form_chart

import (
	_ "embed"

	// algebraic_curve mints constants the statements here spell.
	_ "github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_sections"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed projective_form_chart.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/projective_form_chart", familyCNF).WithOuterAbbrev(
	projective_sections.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "overlap", Text: "ring_away(restrict_ring(field_ring(M), K), «chart»(F), «parameter»)"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
