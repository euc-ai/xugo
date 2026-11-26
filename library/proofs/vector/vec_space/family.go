// family.go — the vec_space family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=vec_space.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=vector/vec_space go test -run TestRecordFamilyCNF ./library/integrity/gates/

package vec_space

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed vec_space.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives vec_space/vec_space.cnf.pb
// from the name's basename, and the registered entry prefix is
// `vec_space.<Member>`.
var family = registry.NewFamily("vector/vec_space", familyCNF)
