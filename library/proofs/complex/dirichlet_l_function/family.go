// family.go — the dirichlet_l_function family manifest: the registry handle every member
// registers into, and the family's one shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=dirichlet_l_function.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/dirichlet_l_function go test -run TestRecordFamilyCNF ./library/integrity/gates/

package dirichlet_l_function

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/complex/dirichlet_character"
	_ "github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	_ "github.com/euc-ai/xugo/library/proofs/complex/riemann_zeta"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/prime_distribution"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed dirichlet_l_function.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `dirichlet_l_function.<Member>`. The domain is ℂ: `&` of a real is complex_of_real,
// and a bare `&n` is a real. The multiplicative monoid of ℂ is bound, so
// `z ^ n` is the complex power. Its table names the two terms of Monsky's
// argument for a real character: «divisorSum», the sum of the character's
// real values over the divisors of n, and «weight», the decreasing weight
// 1/(n(1 − t)) − tⁿ/(1 − tⁿ).
var family = registry.NewFamily("complex/dirichlet_l_function", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain).
	WithInstance(comm_monoid.CommMonoid, complex_field.MulMonoid).
	WithAbbrev(Abbrev{
		{Name: "divisorSum", Text: "λχ:(num → complex). λn:num. Σ_{d∈{d:num | d ∣ n}} re(χ(d))"},
		{Name: "weight", Text: "λn:num. λt:real. &1 / (&n * (&1 - t)) - t ^ n / (&1 - t ^ n)"},
	})
