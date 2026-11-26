// family.go — the do_semantics family manifest: the registry handle every member registers
// into and the family's shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=do_semantics.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=causal/do_semantics go test -run TestRecordFamilyCNF ./library/integrity/gates/

package do_semantics

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/causal/do_derivation"
	_ "github.com/euc-ai/xugo/library/proofs/causal/identifiability"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	_ "github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed do_semantics.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("causal/do_semantics", familyCNF).WithCoerceDomain(RealDomain)
