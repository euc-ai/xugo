// family.go — the nerve family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=nerve.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=simplicial/nerve go test -run TestRecordFamilyCNF ./library/integrity/gates/

package nerve

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed nerve.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// nerve/nerve.cnf.pb from the name's basename, and the registered entry
// prefix is `nerve.<Member>`.
var family = registry.NewFamily("simplicial/nerve", familyCNF)
