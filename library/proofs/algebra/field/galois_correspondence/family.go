// family.go — the galois_correspondence family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=galois_correspondence.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/field/galois_correspondence go test -run TestRecordFamilyCNF ./library/integrity/gates/

package galois_correspondence

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed galois_correspondence.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// galois_correspondence/galois_correspondence.cnf.pb from the name's basename, and
// the registered entry prefix is `galois_correspondence.<Member>`.
var family = registry.NewFamily("algebra/field/galois_correspondence", familyCNF)
