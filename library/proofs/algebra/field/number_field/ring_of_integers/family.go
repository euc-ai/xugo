package ring_of_integers

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/lattice_determinant"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed ring_of_integers.cnf.pb
var familyCNF []byte

var family = registry.NewFamily(
	"algebra/field/number_field/ring_of_integers", familyCNF).WithOuterAbbrev(
	lattice_determinant.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "O", Text: "ring_of_integers(field_ring(L))"},
	// The ring of integers as a ring, the subring of L on «O».
	{Name: "R", Text: "restrict_ring(field_ring(L), «O»)"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
