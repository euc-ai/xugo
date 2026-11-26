// family.go — the singular_homology family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call
// InstallCNFCache — the replay harness installs familyCNF env-side
// before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=singular_homology.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=simplicial/singular_homology go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the registered
// member name, which carries the family's BASE name; CNF_GC takes the
// family's FULL domain path.

package singular_homology

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed singular_homology.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `singular_homology.<Member>`. The chapter has no vocabulary of its own:
// the chains are resolution's free complex on the singular simplices,
// their boundary simplicial_chain's, and homology chain_complex's.
var family = registry.NewFamily("simplicial/singular_homology", familyCNF)
