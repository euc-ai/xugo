// family.go — the central_limit family manifest: the registry handle
// every member registers into and the family's shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=central_limit.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=probability/central_limit go test -run TestRecordFamilyCNF ./library/integrity/gates/

package central_limit

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	_ "github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	_ "github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	_ "github.com/euc-ai/xugo/library/proofs/probability/filtration"
	_ "github.com/euc-ai/xugo/library/proofs/probability/independence"
	_ "github.com/euc-ai/xugo/library/proofs/probability/normal_distribution"
	_ "github.com/euc-ai/xugo/library/proofs/probability/random_variable"
	_ "github.com/euc-ai/xugo/library/proofs/probability/weak_convergence"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed central_limit.cnf.pb
var familyCNF []byte

// family is the family handle; an unanchored numeral `&k` is a real one.
// Its table spells the normalization the central limit theorem reads:
//
//   - `«normalizedSum»(n, x)`: the sum of X(0), …, X(n − 1) at x, centred by
//     n·m and scaled by σ·√n — written over the binders X, m and σ of the
//     statements that spell it.
var family = registry.NewFamily("probability/central_limit", familyCNF).
	WithCoerceDomain(RealDomain).
	WithAbbrev(Abbrev{
		{Name: "normalizedSum", Text: "λn:num. λx:A. " +
			"    (real_sum({k:num | k < n}, λk:num. X(k, x)) - &n * m) / (σ * real_sqrt(&n))"},
	})
