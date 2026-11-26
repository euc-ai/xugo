// family.go — the complex_power_series family manifest: the registry
// handle every member registers into, and the family's one shared
// recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=complex_power_series.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/complex_power_series go test -run TestRecordFamilyCNF ./library/integrity/gates/

package complex_power_series

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed complex_power_series.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `complex_power_series.<Member>`. The domain is ℂ: `&` of a real is
// complex_of_real, and a bare `&n` is a real. The multiplicative monoid
// of ℂ is bound, so `z ^ n` is the complex power.
var family = registry.NewFamily("complex/complex_power_series", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain).
	WithInstance(comm_monoid.CommMonoid, complex_field.MulMonoid)
