// family.go — the polynomial_algebra_evaluation family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=polynomial_algebra_evaluation.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/polynomial/polynomial_algebra_evaluation go test -run TestRecordFamilyCNF ./library/integrity/gates/

package polynomial_algebra_evaluation

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polynomial_algebra_evaluation.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// polynomial_algebra_evaluation/polynomial_algebra_evaluation.cnf.pb from the name's basename, and the
// registered entry prefix is `polynomial_algebra_evaluation.<Member>`.
var family = registry.NewFamily(
	"algebra/ring/polynomial/polynomial_algebra_evaluation", familyCNF).WithOuterAbbrev(
	polynomial_algebra.ChapterAbbrev)
