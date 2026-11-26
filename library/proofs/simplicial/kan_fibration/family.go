// family.go — the kan_fibration family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=kan_fibration.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=simplicial/kan_fibration go test -run TestRecordFamilyCNF ./library/integrity/gates/

package kan_fibration

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed kan_fibration.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// kan_fibration/kan_fibration.cnf.pb from the name's basename, and the registered entry
// prefix is `kan_fibration.<Member>`.
var family = registry.NewFamily("simplicial/kan_fibration", familyCNF)
