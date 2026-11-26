// family.go — the ring_transport family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=ring_transport.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/ring_transport go test -run TestRecordFamilyCNF ./library/integrity/gates/

package ring_transport

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed ring_transport.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// ring_transport/ring_transport.cnf.pb from the name's basename, and the
// registered entry prefix is `ring_transport.<Member>`.
var family = registry.NewFamily("algebra/ring/ring_transport", familyCNF)
