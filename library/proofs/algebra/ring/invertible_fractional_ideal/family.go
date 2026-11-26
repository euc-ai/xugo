// family.go — the invertible_fractional_ideal family manifest: the registry
// handle every member registers into, and the family's ONE shared recorded
// CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=invertible_fractional_ideal.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/invertible_fractional_ideal go test -run TestRecordFamilyCNF ./library/integrity/gates/

package invertible_fractional_ideal

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed invertible_fractional_ideal.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// invertible_fractional_ideal/invertible_fractional_ideal.cnf.pb from the
// name's basename, and the registered entry prefix is
// `invertible_fractional_ideal.<Member>`.
var family = registry.NewFamily(
	"algebra/ring/invertible_fractional_ideal", familyCNF).WithOuterAbbrev(
	fractional_ideal.ChapterAbbrev)
