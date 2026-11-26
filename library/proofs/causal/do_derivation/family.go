// family.go — the do_derivation family manifest: the registry handle every member registers
// into and the family's shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=do_derivation.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=causal/do_derivation go test -run TestRecordFamilyCNF ./library/integrity/gates/

package do_derivation

import (
	_ "embed"

	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/d_separation"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed do_derivation.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("causal/do_derivation", familyCNF)
