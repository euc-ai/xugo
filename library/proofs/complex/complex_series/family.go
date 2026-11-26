// family.go — the complex_series family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=complex_series.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/complex_series go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the full
// registered entry name, CNF_GC the family's own Name — the whole
// domain path.

package complex_series

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed complex_series.cnf.pb
var familyCNF []byte

// family is the family handle. The domain is ℂ: `&` of a real is
// complex_of_real, and a bare `&n` is a real — the parts of a complex
// series are real.
var family = registry.NewFamily("complex/complex_series", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
