// family.go — the preorder_category family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=preorder_category.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=category/preorder_category go test -run TestRecordFamilyCNF ./library/integrity/gates/

package preorder_category

import (
	// The constants this family's statements spell are minted by these
	// families: the imports initialize the mints before the statements
	// are parsed.
	_ "github.com/euc-ai/xugo/library/proofs/relations/order"

	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed preorder_category.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// preorder_category/preorder_category.cnf.pb from the name's basename, and the registered
// entry prefix is `preorder_category.<Member>`.
var family = registry.NewFamily("category/preorder_category", familyCNF)
