// family.go — the field_automorphism family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=field_automorphism.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/field/field_automorphism go test -run TestRecordFamilyCNF ./library/integrity/gates/

package field_automorphism

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed field_automorphism.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// field_automorphism/field_automorphism.cnf.pb from the name's basename, and
// the registered entry prefix is `field_automorphism.<Member>`.
var family = registry.NewFamily("algebra/field/field_automorphism", familyCNF)
