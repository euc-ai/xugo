// family.go — the complex_cpow family manifest: the registry handle every member
// registers into, and the family's one shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=complex_cpow.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/complex_cpow go test -run TestRecordFamilyCNF ./library/integrity/gates/

package complex_cpow

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_log"
	_ "github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed complex_cpow.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `complex_cpow.<Member>`. The domain is ℂ: `&` of a real is complex_of_real,
// and a bare `&n` is a real. The multiplicative monoid of ℂ is bound, so
// `z ^ n` is the complex power.
var family = registry.NewFamily("complex/complex_cpow", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain).
	WithInstance(comm_monoid.CommMonoid, complex_field.MulMonoid)
