// family.go — the mapping_complex family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=mapping_complex.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=simplicial/mapping_complex go test -run TestRecordFamilyCNF ./library/integrity/gates/

package mapping_complex

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed mapping_complex.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// mapping_complex/mapping_complex.cnf.pb from the name's basename, and the registered
// entry prefix is `mapping_complex.<Member>`.
var family = registry.NewFamily("simplicial/mapping_complex", familyCNF)
