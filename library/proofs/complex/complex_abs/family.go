// family.go — the complex_abs family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded
// CNF cache. Proof files carry entry vars; they never call
// InstallCNFCache — the replay harness installs familyCNF env-side
// before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=complex_abs.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/complex_abs go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the full
// registered entry name, CNF_GC the family's own Name — the whole
// domain path.

package complex_abs

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed complex_abs.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// complex_abs/complex_abs.cnf.pb from the name's basename. The domain is
// ℂ: `&` of a real is complex_of_real, and a bare `&n` a real number —
// a modulus is one, and so are the parts it is computed from. The
// family binds ℂ's product monoid, so `z ^ n` is ℂ's power.
var family = registry.NewFamily("complex/complex_abs", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain).
	WithInstance(comm_monoid.CommMonoid, complex_field.MulMonoid)
