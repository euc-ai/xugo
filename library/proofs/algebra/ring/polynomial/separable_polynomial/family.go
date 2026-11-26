// family.go — the separable_polynomial family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=separable_polynomial.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/polynomial/separable_polynomial go test -run TestRecordFamilyCNF ./library/integrity/gates/

package separable_polynomial

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed separable_polynomial.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// separable_polynomial/separable_polynomial.cnf.pb from the name's basename,
// and the registered entry prefix is `separable_polynomial.<Member>`.
var family = registry.NewFamily(
	"algebra/ring/polynomial/separable_polynomial", familyCNF).WithOuterAbbrev(
	polynomial_division.ChapterAbbrev, polynomial_roots.ChapterAbbrev)
