// family.go — the density_measure family manifest: the registry handle
// every member registers into and the family's shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=density_measure.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=measure/density_measure go test -run TestRecordFamilyCNF ./library/integrity/gates/

package density_measure

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	_ "github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed density_measure.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("measure/density_measure", familyCNF).WithCoerceDomain(RealDomain)
