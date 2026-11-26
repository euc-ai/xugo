// family.go — the int_construction family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var RepresentativeInjective =
// family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=int_construction.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=int_num/int_construction go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT spellings and each rejects the other's:
// RECORD_CNF takes the full registered MEMBER name, whose prefix is the
// family name's last segment (registry.ByName is keyed on it), while
// CNF_GC takes the FAMILY name, which is the whole domain path.
//
// The blob is recorded, so this family replays STRICT: a refute with no
// cached key panics rather than running live, and a green replay does
// constrain refute count. A new member's first replay is expected to
// MISS; read the panic's own `Checked:` line before recording, since it
// says whether the leaf wants a key or wants shaping.

package int_construction

import (
	// real_sup_inf mints constants this family's definitions spell, and no
	// other import reaches it: the import initializes those mints
	// before the definitions here are parsed.
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"

	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed int_construction.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates int_num/int_construction/int_construction.cnf.pb
// from it, and the registered entry prefix is the name's last segment
// (`int_construction.<Member>`).
var family = registry.NewFamily("int_num/int_construction", familyCNF).WithVocabSpec(vocab)
