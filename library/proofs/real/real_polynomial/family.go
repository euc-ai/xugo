// family.go — the real_polynomial family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var Add = family.Add(...)`);
// they never call InstallCNFCache — the replay harness installs
// familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=real_polynomial.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/real_polynomial go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the full
// registered entry name (registry.ByName is keyed on it; a bare entry
// name reports "not in proof registry"), while CNF_GC takes the
// family's own Name — the whole domain path — and rejects the bare
// basename with "no such family".

package real_polynomial

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_polynomial.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// real_polynomial/real_polynomial.cnf.pb from the name's basename.
// The chapter's numbers are reals: an `&` no operand anchors is ℝ's
// embedding, by the declaration on the handle.
var family = registry.NewFamily("real/real_polynomial", familyCNF).WithCoerceDomain(RealDomain)
