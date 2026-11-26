// family.go — the scheme family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=scheme.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/scheme go test -run TestRecordFamilyCNF ./library/integrity/gates/

package scheme

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed scheme.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives scheme/scheme.cnf.pb
// from the name's basename, and the registered entry prefix is
// `scheme.<Member>`.
var family = registry.NewFamily("scheme/scheme", familyCNF)
