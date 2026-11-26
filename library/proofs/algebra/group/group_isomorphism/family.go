// family.go — the group_isomorphism family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=group_isomorphism.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/group/group_isomorphism go test -run TestRecordFamilyCNF ./library/integrity/gates/

package group_isomorphism

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed group_isomorphism.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// group_isomorphism/group_isomorphism.cnf.pb from the name's basename,
// and the registered entry prefix is `group_isomorphism.<Member>`.
var family = registry.NewFamily("algebra/group/group_isomorphism", familyCNF)
