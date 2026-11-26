// family.go — the category family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=category.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=category/category go test -run TestRecordFamilyCNF ./library/integrity/gates/

package category

import (
	// set_basic mints set_member, a constant this family's definitions
	// spell which no other import reaches: the import initializes the
	// mint before the definitions here are parsed.
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"

	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed category.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// category/category.cnf.pb from the name's basename, and the
// registered entry prefix is `category.<Member>`.
var family = registry.NewFamily("category/category", familyCNF)
