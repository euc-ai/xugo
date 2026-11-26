// family.go — the simplicial_homotopy family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=simplicial_homotopy.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=simplicial/simplicial_homotopy go test -run TestRecordFamilyCNF ./library/integrity/gates/

package simplicial_homotopy

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed simplicial_homotopy.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// simplicial_homotopy/simplicial_homotopy.cnf.pb from the name's basename, and the
// registered entry prefix is `simplicial_homotopy.<Member>`.
var family = registry.NewFamily("simplicial/simplicial_homotopy", familyCNF)
