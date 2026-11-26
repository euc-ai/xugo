// family.go — the extended_nonneg_real family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=extended_nonneg_real.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/extended_nonneg_real go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// Note the two spellings: RECORD_CNF takes the registered member name,
// which carries the family's BASE name; CNF_GC takes the family's FULL
// domain path.

package extended_nonneg_real

import (
	// real_sup_inf mints `max`, which this family's definitions spell,
	// and no other import reaches it: the import initializes that mint
	// before the definitions here are parsed.
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"

	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed extended_nonneg_real.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates real/extended_nonneg_real/extended_nonneg_real.cnf.pb from it, and the registered
// entry prefix is the name's last segment (`extended_nonneg_real.<Member>`). Its
// numbers are reals: an `&` no operand anchors is ℝ's embedding, by
// the declaration on the handle.
var family = registry.NewFamily("real/extended_nonneg_real", familyCNF).WithCoerceDomain(
	RealDomain).WithAbbrev(Abbrev{
	{Name: "fibre", Text: "λk:num. {p:prod(num, num) | φ(fst(p), snd(p)) = k}"},
})
