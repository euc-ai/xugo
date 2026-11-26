// family.go — the subring_localization family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=subring_localization.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/subring_localization go test -run TestRecordFamilyCNF ./library/integrity/gates/

package subring_localization

import (
	_ "embed"

	// The chapter whose constant the statements spell, initialized
	// before them.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/valuation_order"

	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_colength"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed subring_localization.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// subring_localization/subring_localization.cnf.pb from the name's basename,
// and the registered entry prefix is `subring_localization.<Member>`.
var family = registry.NewFamily("algebra/ring/subring_localization", familyCNF).WithOuterAbbrev(
	ideal_colength.ChapterAbbrev)
