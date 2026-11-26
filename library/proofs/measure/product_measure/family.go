// family.go — the product_measure family manifest: the registry handle
// every member registers into and the family's shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=product_measure.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=measure/product_measure go test -run TestRecordFamilyCNF ./library/integrity/gates/

package product_measure

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	_ "github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed product_measure.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("measure/product_measure", familyCNF).WithCoerceDomain(RealDomain)
