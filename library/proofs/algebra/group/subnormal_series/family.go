// family.go — the subnormal_series family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=subnormal_series.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/group/subnormal_series go test -run TestRecordFamilyCNF ./library/integrity/gates/

package subnormal_series

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed subnormal_series.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// subnormal_series/subnormal_series.cnf.pb from the name's basename, and the
// registered entry prefix is `subnormal_series.<Member>`.
var family = registry.NewFamily("algebra/group/subnormal_series", familyCNF)
