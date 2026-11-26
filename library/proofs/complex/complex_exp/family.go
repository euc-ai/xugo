// family.go — the complex_exp family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=complex_exp.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/complex_exp go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the full
// registered entry name, CNF_GC the family's own Name — the whole
// domain path.

package complex_exp

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed complex_exp.cnf.pb
var familyCNF []byte

// family is the family handle. It binds ℂ's product monoid, so `z ^ n`
// is ℂ's power; the domain is ℂ, so `&` of a real is complex_of_real
// and a bare `&n` a real number, the factorials and signs lifting into
// ℂ where the position asks.
var family = registry.NewFamily("complex/complex_exp", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain).
	WithInstance(comm_monoid.CommMonoid, complex_field.MulMonoid).WithAbbrev(Abbrev{
	{Name: "cosTerm", Text: "complex_of_real(real_pow(-&1, n)) * " +
		"z ^ (2 * n) / " +
		"complex_of_real(&factorial(2 * n))"},
	{Name: "sinTerm", Text: "complex_of_real(real_pow(-&1, n)) * " +
		"z ^ (2 * n + 1) / " +
		"complex_of_real(&factorial(2 * n + 1))"},
	{Name: "evenSizeTerm", Text: "real_pow(|z|, 2 * n) / &factorial(2 * n)"},
	{Name: "oddSizeTerm", Text: "real_pow(|z|, 2 * n + 1) / &factorial(2 * n + 1)"},
})
