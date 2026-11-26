// family.go — the option family manifest: the registry handle every
// entry registers into, and the family's ONE shared recorded CNF cache.
// This chapter's entries all come from the door (`family.DefineData`)
// rather than from `family.Add`; either way they never call
// InstallCNFCache — the replay harness installs familyCNF env-side
// before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header).
// Mind the two spellings: the per-member selectors take the REGISTERED
// name (`option.<Member>`), the family-wide GC takes the family's full
// domain path.
//
//	XUGO_RECORD_FAMILY_CNF=option.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=datatypes/option go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The first live-records one member and merges its keys in (what a
// restructure needs); the second drops keys no member reaches any more.

package option

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed option.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates datatypes/option/option.cnf.pb from it, and the
// registered entry prefix is the name's last segment (`option.<Member>`).
// The vocabulary (vocab.go) is the chapter's statement alphabet,
// installed into every member's ParseScope before its first section.
var family = registry.NewFamily("datatypes/option", familyCNF).WithVocabSpec(vocab)
