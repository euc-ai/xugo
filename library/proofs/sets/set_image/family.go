// family.go — the set_image family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF cache.
// Proof files carry entry vars (`var ImageUnion = family.Add(...)`); they
// never call InstallCNFCache — the replay harness installs familyCNF
// env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=set_image.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=sets/set_image go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The first live-records ONE member and merges its keys in, and takes
// the FULL registered name. The second re-records the family's union
// from scratch and takes `Family.Name` — the whole domain path — and
// rejects the bare basename with `no such family`.

package set_image

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed set_image.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates sets/set_image/set_image.cnf.pb from it, and the
// registered entry prefix is the name's last segment
// (`set_image.<Member>`).
// The chapter's statement vocabulary is the VocabSpec in vocab.go.
var family = registry.NewFamily("sets/set_image", familyCNF).
	WithVocabSpec(vocab)
