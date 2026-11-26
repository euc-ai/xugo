package number_ideals

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ring_of_integers"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed number_ideals.cnf.pb
var familyCNF []byte

var family = registry.NewFamily(
	"algebra/field/number_field/number_ideals", familyCNF).WithOuterAbbrev(
	ring_of_integers.ChapterAbbrev)

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
