// family.go — the rational family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var IntegerRational =
// family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=rational.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/rational go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// Note the two spellings: RECORD_CNF takes the registered member name,
// which carries the family's BASE name; CNF_GC takes the family's FULL
// domain path, and the base name fails `no such family`.

package rational

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed rational.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates real/rational/rational.cnf.pb from it, and the
// registered entry prefix is the name's last segment
// (`rational.<Member>`). The chapter has no vocabulary of its own:
// every name its statements spell — `rational`, `integer`, `real_sqrt`,
// `nat_prime`, the field operations and the embedding `&` — resolves
// through its mint. Its numbers are reals: an `&` no operand anchors
// is ℝ's embedding, by the declaration on the handle.
var family = registry.NewFamily("real/rational", familyCNF).WithCoerceDomain(RealDomain)
