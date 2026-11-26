// family.go — the real_function_limits family manifest: the registry
// handle every member registers into, and the family's ONE shared
// recorded CNF cache. Proof files carry entry vars (`var LimitAtUnique
// = family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=real_function_limits.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/real_function_limits go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// Note the two spellings: RECORD_CNF takes the registered member name,
// which carries the family's BASE name; CNF_GC takes the family's FULL
// domain path, and the base name fails `no such family`.

package real_function_limits

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_function_limits.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates real/real_function_limits/real_function_limits.cnf.pb
// from it, and the registered entry prefix is the name's last segment
// (`real_function_limits.<Member>`). The chapter has no vocabulary of
// its own: every name a statement spells — real_abs, real_inv, `<`, the
// field operations, the embedding `&`, real_sequences' `⟶`, composition
// `∘` — resolves through its mint.
var family = registry.NewFamily("real/real_function_limits", familyCNF).WithCoerceDomain(RealDomain)
