// family.go — the adjustment family manifest: the registry handle every member registers
// into and the family's shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=adjustment.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=causal/adjustment go test -run TestRecordFamilyCNF ./library/integrity/gates/

package adjustment

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/causal/do_calculus"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed adjustment.cnf.pb
var familyCNF []byte

// family is the family handle. Its table names the distribution of a
// model M under do(X = v).
var family = registry.NewFamily("causal/adjustment", familyCNF).WithCoerceDomain(
	RealDomain).WithAbbrev(Abbrev{
	{Name: "Px", Text: "scm_distribution(scm_do(M, X, v))"},
})
