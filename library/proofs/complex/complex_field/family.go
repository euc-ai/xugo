// family.go — the complex_field family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded
// CNF cache. Proof files carry entry vars; they never call
// InstallCNFCache — the replay harness installs familyCNF env-side
// before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=complex_field.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/complex_field go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the full
// registered entry name, CNF_GC the family's own Name — the whole
// domain path.

package complex_field

import (
	_ "embed"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed complex_field.cnf.pb
var familyCNF []byte

// ComplexDomain is ℂ as the declared domain of the complex chapters:
// `&` of a real is complex_of_real (ComplexOfRealDef's Coercion), and
// a numeral under `&` is a real — a complex number's parts — that
// lifts where a complex position or partner asks.
var ComplexDomain = ext.MakeType("complex")

// family is the family handle. The recorder derives
// complex_field/complex_field.cnf.pb from the name's basename. The
// chapter mints its own type and constants and declares ℂ as its
// domain.
var family = registry.NewFamily("complex/complex_field", familyCNF).WithCoerceDomain(ComplexDomain)
