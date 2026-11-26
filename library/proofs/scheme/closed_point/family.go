package closed_point

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/scheme/elliptic_curve"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed closed_point.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/closed_point", familyCNF).WithOuterAbbrev(
	elliptic_curve.ChapterAbbrev, polynomial_division.ChapterAbbrev)
