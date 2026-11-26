package trace_dual

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/field/functional_dual"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed trace_dual.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/trace_dual", familyCNF).WithOuterAbbrev(
	functional_dual.ChapterAbbrev)
