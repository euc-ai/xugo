// family.go — the nat_congruence family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var ModLeft = family.Add(...)`);
// they never call InstallCNFCache — the replay harness installs
// familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=nat_congruence.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=nat_num/nat_congruence go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the full
// registered entry name (registry.ByName is keyed on it; a bare entry
// name reports "not in proof registry"), while CNF_GC takes the
// family's own Name — the whole domain path — and rejects the bare
// basename with "no such family".

package nat_congruence

import (
	_ "embed"

	// equivalence mints constants the statements here spell.
	_ "github.com/euc-ai/xugo/library/proofs/relations/equivalence"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed nat_congruence.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates nat_num/nat_congruence/nat_congruence.cnf.pb from it, and the
// registered entry prefix is the name's last segment
// (`nat_congruence.<Member>`).
var family = registry.NewFamily("nat_num/nat_congruence", familyCNF).WithVocabSpec(vocab)
