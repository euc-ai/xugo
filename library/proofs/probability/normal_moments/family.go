// family.go — the normal_moments family manifest: the registry handle
// every member registers into and the family's shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=normal_moments.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=probability/normal_moments go test -run TestRecordFamilyCNF ./library/integrity/gates/

package normal_moments

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/probability/normal_distribution"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed normal_moments.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("probability/normal_moments", familyCNF).WithCoerceDomain(
	RealDomain)
