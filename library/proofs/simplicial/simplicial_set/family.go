// family.go — the simplicial_set family manifest: the registry handle
// every member registers into, and the family's one shared recorded
// CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=simplicial_set.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=simplicial/simplicial_set go test -run TestRecordFamilyCNF ./library/integrity/gates/

package simplicial_set

import (
	// nat_monus mints constants this family's definitions spell, and no
	// other import reaches it: the import initializes those mints
	// before the definitions here are parsed.
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"

	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed simplicial_set.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// simplicial_set/simplicial_set.cnf.pb from the name's basename, and
// the registered entry prefix is `simplicial_set.<Member>`.
var family = registry.NewFamily("simplicial/simplicial_set", familyCNF)
