// family.go — the simplicial_group family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=simplicial_group.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=simplicial/simplicial_group go test -run TestRecordFamilyCNF ./library/integrity/gates/

package simplicial_group

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed simplicial_group.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// simplicial_group/simplicial_group.cnf.pb from the name's basename, and the
// registered entry prefix is `simplicial_group.<Member>`.
var family = registry.NewFamily("simplicial/simplicial_group", familyCNF)
