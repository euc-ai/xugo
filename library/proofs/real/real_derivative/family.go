// family.go — the real_derivative family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=real_derivative.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/real_derivative go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// Note the two spellings: RECORD_CNF takes the registered member name,
// which carries the family's BASE name; CNF_GC takes the family's FULL
// domain path.

package real_derivative

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_derivative.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates real/real_derivative/real_derivative.cnf.pb from it,
// and the registered entry prefix is the name's last segment
// (`real_derivative.<Member>`). The chapter mints one constant,
// real_derivative_at; every other name a statement spells — the limit
// `⟶ (at c)`, continuity, the field operations, real_pow — resolves
// through its mint. Its numbers are reals: an `&` no operand anchors
// is ℝ's embedding, by the declaration on the handle.
var family = registry.NewFamily("real/real_derivative", familyCNF).WithCoerceDomain(RealDomain)
