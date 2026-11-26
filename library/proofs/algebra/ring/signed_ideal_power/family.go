// family.go — the signed_ideal_power family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=signed_ideal_power.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/signed_ideal_power go test -run TestRecordFamilyCNF ./library/integrity/gates/

package signed_ideal_power

import (
	_ "embed"

	// The chapter whose constant the statements spell, initialized
	// before them.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/valuation_order"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed signed_ideal_power.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// signed_ideal_power/signed_ideal_power.cnf.pb from the name's basename, and
// the registered entry prefix is `signed_ideal_power.<Member>`.
var family = registry.NewFamily("algebra/ring/signed_ideal_power", familyCNF)
