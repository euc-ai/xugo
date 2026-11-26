// family.go — the kan_complex family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=kan_complex.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=simplicial/kan_complex go test -run TestRecordFamilyCNF ./library/integrity/gates/

package kan_complex

import (
	// nat_monus mints constants this family's definitions spell, and no
	// other import reaches it: the import initializes those mints
	// before the definitions here are parsed.
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"

	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed kan_complex.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// kan_complex/kan_complex.cnf.pb from the name's basename, and the registered entry
// prefix is `kan_complex.<Member>`.
var family = registry.NewFamily("simplicial/kan_complex", familyCNF)
