// family.go — the dirichlet_series family manifest: the registry handle every member
// registers into, and the family's one shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=dirichlet_series.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/dirichlet_series go test -run TestRecordFamilyCNF ./library/integrity/gates/

package dirichlet_series

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_cpow"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/prime_distribution"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed dirichlet_series.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `dirichlet_series.<Member>`. The domain is ℂ: `&` of a real is complex_of_real,
// and a bare `&n` is a real. The multiplicative monoid of ℂ is bound, so
// `z ^ n` is the complex power.
var family = registry.NewFamily("complex/dirichlet_series", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain).
	WithInstance(comm_monoid.CommMonoid, complex_field.MulMonoid)
