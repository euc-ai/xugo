// family.go — the datatype_universe family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var ConstrInj = family.Add(...)`);
// they never call InstallCNFCache — the replay harness installs
// familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header).
// Mind the two spellings: the per-member selectors take the REGISTERED
// name (`datatype_universe.<Member>`), the family-wide GC takes the family's full
// domain path.
//
//	XUGO_RECORD_FAMILY_CNF=datatype_universe.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=datatypes/datatype_universe go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The first live-records one member and merges its keys in (what a
// restructure needs); the second drops keys no member reaches any more.

package datatype_universe

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed datatype_universe.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates datatypes/datatype_universe/datatype_universe.cnf.pb from it, and the
// registered entry prefix is the name's last segment
// (`datatype_universe.<Member>`). The chapter carries no vocabulary: every
// constant a statement here names (the pairing functions, the
// injections, the universe's constructors) is minted by the chapter's
// own definitional layer (definitions.go), and a statement resolves it
// through the parser's const resolver at that mint.
var family = registry.NewFamily("datatypes/datatype_universe", familyCNF)
