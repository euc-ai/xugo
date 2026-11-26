// family.go — the presheaf family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=presheaf.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=topology/presheaf go test -run TestRecordFamilyCNF ./library/integrity/gates/

package presheaf

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed presheaf.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives presheaf/presheaf.cnf.pb
// from the name's basename, and the registered entry prefix is
// `presheaf.<Member>`.
var family = registry.NewFamily("topology/presheaf", familyCNF)
