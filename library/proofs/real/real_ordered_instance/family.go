// family.go — the real_ordered_instance family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=real_ordered_instance.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/real_ordered_instance go test -run TestRecordFamilyCNF ./library/integrity/gates/

package real_ordered_instance

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_ordered_instance.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `real_ordered_instance.<Member>`.
var family = registry.NewFamily("real/real_ordered_instance", familyCNF).WithCoerceDomain(
	RealDomain)
