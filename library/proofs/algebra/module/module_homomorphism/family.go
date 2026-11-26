// family.go — the module_homomorphism family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=module_homomorphism.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/module_homomorphism go test -run TestRecordFamilyCNF ./library/integrity/gates/

package module_homomorphism

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed module_homomorphism.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// module_homomorphism/module_homomorphism.cnf.pb from the name's basename, and the
// registered entry prefix is `module_homomorphism.<Member>`.
var family = registry.NewFamily("algebra/module/module_homomorphism", familyCNF)
