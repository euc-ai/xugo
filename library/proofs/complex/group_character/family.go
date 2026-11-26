// family.go — the group_character family manifest: the registry handle every member
// registers into, and the family's one shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=group_character.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/group_character go test -run TestRecordFamilyCNF ./library/integrity/gates/

package group_character

import (
	_ "embed"

	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/roots_of_unity"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/cyclic_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed group_character.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `group_character.<Member>`. The domain is ℂ: `&` of a real is complex_of_real,
// and a bare `&n` is a real. The multiplicative monoid of ℂ is bound, so
// `z ^ n` is the complex power.
var family = registry.NewFamily("complex/group_character", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain).
	WithInstance(comm_monoid.CommMonoid, complex_field.MulMonoid)
