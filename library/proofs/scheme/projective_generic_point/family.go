package projective_generic_point

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed projective_generic_point.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/projective_generic_point", familyCNF).WithOuterAbbrev(
	projective_curve.ChapterAbbrev)

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
