// family.go — the complex_log family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=complex_log.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/complex_log go test -run TestRecordFamilyCNF ./library/integrity/gates/

package complex_log

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed complex_log.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `complex_log.<Member>`. The domain is ℂ: `&` of a real is
// complex_of_real, and a bare `&n` is a real.
var family = registry.NewFamily("complex/complex_log", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
