// family.go — the real_product family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF cache.
// Proof files carry entry vars; they never call InstallCNFCache — the
// replay harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=real_product.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=iterate/real/real_product go test -run TestRecordFamilyCNF ./library/integrity/gates/

package real_product

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_product.cnf.pb
var familyCNF []byte

// family is the family handle. The chapter's numbers are reals: an `&`
// no operand anchors is ℝ's embedding, by the declaration on the handle.
var family = registry.NewFamily("iterate/real/real_product", familyCNF).WithCoerceDomain(RealDomain)
