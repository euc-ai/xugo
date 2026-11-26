// family.go — the set_product family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call
// InstallCNFCache — the replay harness installs familyCNF env-side
// before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=set_product.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=sets/set_product go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the registered
// member name, which carries the family's BASE name; CNF_GC takes the
// family's FULL domain path.

package set_product

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed set_product.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates sets/set_product/set_product.cnf.pb from it, and the
// registered entry prefix is the name's last segment (`set_product.<Member>`).
// The chapter has no vocabulary of its own: every name its statements
// spell resolves through its mint.
var family = registry.NewFamily("sets/set_product", familyCNF)
