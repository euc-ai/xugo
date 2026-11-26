package lattice_determinant

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed lattice_determinant.cnf.pb
var familyCNF []byte

var family = registry.NewFamily(
	"algebra/field/number_field/lattice_determinant", familyCNF).WithAbbrev(Abbrev{
	{Name: "ℤ", Text: "restrict_ring(field_ring(L), integer_image(field_ring(L)))"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
