package real_closed_field

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_closed_field.cnf.pb
var familyCNF []byte

// family is the family handle. The chapter reads polynomial_roots' table,
// whose «linear»(a) is the linear factor x − a.
var family = registry.NewFamily("algebra/field/real_closed_field", familyCNF).WithOuterAbbrev(
	polynomial_roots.ChapterAbbrev)
