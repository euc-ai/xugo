// family.go — the identifiability family manifest: the registry handle every member registers
// into and the family's shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=identifiability.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=causal/identifiability go test -run TestRecordFamilyCNF ./library/integrity/gates/

package identifiability

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/causal/adjustment"
	_ "github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed identifiability.cnf.pb
var familyCNF []byte

// family is the family handle. Its table names the positive class over the
// graph (V, E) with observed nodes O and carriers D, and the probability
// of Y at v under do(X = v) as a query on models.
var family = registry.NewFamily("causal/identifiability", familyCNF).WithCoerceDomain(
	RealDomain).WithAbbrev(Abbrev{
	{Name: "positiveClass", Text: "λM:scm_model(A, B, I). positive_scm(V, E, O, D, M)"},
	{Name: "effect", Text: "λM:scm_model(A, B, I). " +
		"    extended_to_real(scm_distribution(scm_do(M, X, v), agree_on(Y, v)))"},
})
