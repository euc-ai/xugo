// family.go — the carrier family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var Extensionality =
// family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header).
// Mind the two spellings: the per-member selectors take the REGISTERED
// name (`carrier.<Member>`), the family-wide GC takes the family's
// full domain path.
//
//	XUGO_RECORD_FAMILY_CNF=carrier.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=cartesian/carrier go test -run TestRecordFamilyCNF ./library/integrity/gates/

package carrier

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed carrier.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates cartesian/carrier/carrier.cnf.pb from it, and the
// registered entry prefix is the name's last segment
// (`carrier.<Member>`). The statement vocabulary — the chapter's
// minted constants and the junk element its members state — is
// declared in vocab.go.
var family = registry.NewFamily("cartesian/carrier", familyCNF).WithVocabSpec(vocab)
