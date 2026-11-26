// family.go — the lebesgue_measure family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=lebesgue_measure.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/lebesgue_measure go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// Note the two spellings: RECORD_CNF takes the registered member name,
// which carries the family's BASE name; CNF_GC takes the family's FULL
// domain path.

package lebesgue_measure

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	// borel_sets, which MeasurableBorel states, is minted there.
	_ "github.com/euc-ai/xugo/library/proofs/topology/borel_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed lebesgue_measure.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates real/lebesgue_measure/lebesgue_measure.cnf.pb from it, and the registered
// entry prefix is the name's last segment (`lebesgue_measure.<Member>`). Its
// numbers are reals: an `&` no operand anchors is ℝ's embedding, by
// the declaration on the handle.
var family = registry.NewFamily("real/lebesgue_measure", familyCNF).WithCoerceDomain(RealDomain)
