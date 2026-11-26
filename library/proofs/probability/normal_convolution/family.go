// family.go — the normal_convolution family manifest: the registry handle
// every member registers into and the family's shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=normal_convolution.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=probability/normal_convolution go test -run TestRecordFamilyCNF ./library/integrity/gates/

package normal_convolution

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/probability/normal_distribution"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed normal_convolution.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("probability/normal_convolution", familyCNF).WithCoerceDomain(
	RealDomain)
