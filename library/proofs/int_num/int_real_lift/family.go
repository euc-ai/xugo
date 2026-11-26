// family.go — the int_real_lift family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF cache.
// Proof files carry entry vars (`var AddLeftIdentity = family.Add(...)`); they
// never call InstallCNFCache — the replay harness installs familyCNF
// env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=int_real_lift.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=int_num/int_real_lift go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the full
// registered entry name (registry.ByName is keyed on it; a bare entry
// name reports "not in proof registry"), while CNF_GC takes the
// family's own Name — the whole domain path — and rejects the bare
// basename with "no such family".

package int_real_lift

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed int_real_lift.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// int_real_lift/int_real_lift.cnf.pb from the name's basename.
var family = registry.NewFamily("int_num/int_real_lift", familyCNF).WithVocabSpec(vocab)
