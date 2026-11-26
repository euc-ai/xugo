// family.go — the polynomial_evaluation family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=polynomial_evaluation.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/polynomial/polynomial_evaluation go test -run TestRecordFamilyCNF ./library/integrity/gates/

package polynomial_evaluation

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polynomial_evaluation.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// polynomial_eval/polynomial_evaluation.cnf.pb from the name's basename, and the
// registered entry prefix is `polynomial_evaluation.<Member>`.
var family = registry.NewFamily(
	"algebra/ring/polynomial/polynomial_evaluation", familyCNF).WithOuterAbbrev(
	polynomial.ChapterAbbrev)
