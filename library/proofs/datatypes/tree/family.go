// family.go — the tree family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var MirrorMirror =
// family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// The dependency direction is one-way: `btree_flatten` lands in a list,
// so this package imports `datatypes/list` and that package may not
// import back.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header).
// Mind the two spellings: the per-member selectors take the REGISTERED
// name (`tree.<Member>`), the family-wide GC takes the family's full
// domain path.
//
//	XUGO_RECORD_FAMILY_CNF=tree.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=datatypes/tree go test -run TestRecordFamilyCNF ./library/integrity/gates/

package tree

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed tree.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates datatypes/tree/tree.cnf.pb from it, and the
// registered entry prefix is the name's last segment (`tree.<Member>`).
// The vocabulary (vocab.go) is the chapter's statement alphabet,
// installed into every member's ParseScope before its first section.
var family = registry.NewFamily("datatypes/tree", familyCNF).WithVocabSpec(vocab)
