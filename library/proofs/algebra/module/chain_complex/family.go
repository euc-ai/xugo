// family.go — the chain_complex family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=chain_complex.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/chain_complex go test -run TestRecordFamilyCNF ./library/integrity/gates/

package chain_complex

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed chain_complex.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// chain_complex/chain_complex.cnf.pb from the name's basename, and the
// registered entry prefix is `chain_complex.<Member>`.
var family = registry.NewFamily("algebra/module/chain_complex", familyCNF).WithAbbrev(Abbrev{
	{Name: "doubleTotal", Text: "double_total(V, D, h, v, alternating_sign)"},
})
