// family.go — the tor_ext family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=tor_ext.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/tor_ext go test -run TestRecordFamilyCNF ./library/integrity/gates/

package tor_ext

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed tor_ext.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// tor_ext/tor_ext.cnf.pb from the name's basename, and the
// registered entry prefix is `tor_ext.<Member>`.
var family = registry.NewFamily("algebra/module/tor_ext", familyCNF)
