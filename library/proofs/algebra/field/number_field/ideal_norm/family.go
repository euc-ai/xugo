package ideal_norm

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/number_ideals"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed ideal_norm.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/number_field/ideal_norm", familyCNF).WithOuterAbbrev(
	number_ideals.ChapterAbbrev)

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
