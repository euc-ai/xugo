package ring_formula

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed ring_formula.cnf.pb
var familyCNF []byte

// family is the family handle. Its table names the carrier of a field, the
// carrier the models of a quantifier-free equivalent over fields are read
// at; a statement over the fields on B ties it there, «carrier»⟨A:B⟩.
var family = registry.NewFamily("algebra/field/ring_formula", familyCNF).WithAbbrev(Abbrev{
	{Name: "carrier", Text: "λF:field_ops(A). F.carrier"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under it
// name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
