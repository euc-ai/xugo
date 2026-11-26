// family.go — the hermite_function family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache —
// the replay harness installs familyCNF env-side before every member's
// Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=hermite_function.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/hermite_function go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the registered
// member name, which carries the family's BASE name; CNF_GC takes the
// family's FULL domain path.

package hermite_function

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	_ "github.com/euc-ai/xugo/library/proofs/real/lebesgue_integral"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_pow"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed hermite_function.cnf.pb
var familyCNF []byte

// family is the family handle; an unanchored numeral `&k` is a real one.
var family = registry.NewFamily("real/hermite_function", familyCNF).WithCoerceDomain(RealDomain)
