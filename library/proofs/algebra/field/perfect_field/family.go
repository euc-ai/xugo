package perfect_field

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed perfect_field.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/perfect_field", familyCNF).WithOuterAbbrev(
	polynomial_roots.ChapterAbbrev)
