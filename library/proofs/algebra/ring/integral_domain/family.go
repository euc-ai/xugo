// family.go — the integral_domain family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=integral_domain.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/integral_domain go test -run TestRecordFamilyCNF ./library/integrity/gates/

package integral_domain

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed integral_domain.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// integral_domain/integral_domain.cnf.pb from the name's basename, and
// the registered entry prefix is `integral_domain.<Member>`.
var family = registry.NewFamily("algebra/ring/integral_domain", familyCNF)
