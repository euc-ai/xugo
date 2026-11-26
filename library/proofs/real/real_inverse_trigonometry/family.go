// family.go — the real_inverse_trigonometry family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=real_inverse_trigonometry.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/real_inverse_trigonometry go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// Note the two spellings: RECORD_CNF takes the registered member name,
// which carries the family's BASE name; CNF_GC takes the family's FULL
// domain path.

package real_inverse_trigonometry

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_inverse_trigonometry.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates real/real_inverse_trigonometry/real_inverse_trigonometry.cnf.pb from it, and the registered
// entry prefix is the name's last segment (`real_inverse_trigonometry.<Member>`). Its
// numbers are reals: an `&` no operand anchors is ℝ's embedding, by
// the declaration on the handle.
var family = registry.NewFamily("real/real_inverse_trigonometry", familyCNF).WithCoerceDomain(
	RealDomain)
