// family.go — the yoneda family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=yoneda.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=category/yoneda go test -run TestRecordFamilyCNF ./library/integrity/gates/

package yoneda

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed yoneda.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// yoneda/yoneda.cnf.pb from the name's basename, and the registered
// entry prefix is `yoneda.<Member>`.
var family = registry.NewFamily("category/yoneda", familyCNF)
