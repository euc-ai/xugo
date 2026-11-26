// family.go — the dirichlet_character family manifest: the registry handle every member
// registers into, and the family's one shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=dirichlet_character.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/dirichlet_character go test -run TestRecordFamilyCNF ./library/integrity/gates/

package dirichlet_character

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/units_mod"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/complex/group_character"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/totient"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed dirichlet_character.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `dirichlet_character.<Member>`. The domain is ℂ: `&` of a real is complex_of_real,
// and a bare `&n` is a real. The multiplicative monoid of ℂ is bound, so
// `z ^ n` is the complex power.
var family = registry.NewFamily("complex/dirichlet_character", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain).
	WithInstance(comm_monoid.CommMonoid, complex_field.MulMonoid)
