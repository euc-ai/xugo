package functional_dual

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed functional_dual.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/functional_dual", familyCNF).WithAbbrev(Abbrev{
	{Name: "ScalarK", Text: "restrict_ring(field_ring(L), K)"},
	{Name: "ScalarS", Text: "restrict_ring(field_ring(L), S)"},
	{Name: "ScalarB", Text: "restrict_ring(field_ring(L), B)"},
	{Name: "Regular", Text: "regular_module(field_ring(L))"},
	{Name: "VectorsK", Text: "restrict_module(«Regular», K)"},
	{Name: "VectorsB", Text: "restrict_module(«Regular», B)"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
