// family.go — the weak_convergence family manifest: the registry handle
// every member registers into and the family's shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=weak_convergence.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=probability/weak_convergence go test -run TestRecordFamilyCNF ./library/integrity/gates/

package weak_convergence

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_topology"
	_ "github.com/euc-ai/xugo/library/proofs/topology/borel_space"
	_ "github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed weak_convergence.cnf.pb
var familyCNF []byte

// family is the family handle; an unanchored numeral `&k` is a real one.
// Its table spells the measures on the line that every member reads:
//
//   - `«lineProbability»(μ)`: μ is a probability on the Borel sets of the line;
//   - `«lineIntegral»(μ, f)`, `«lineIntegrable»(μ, f)`: the integral of f
//     against μ on the Borel sets of the line, and its integrability.
var family = registry.NewFamily("probability/weak_convergence", familyCNF).
	WithCoerceDomain(RealDomain).
	WithAbbrev(Abbrev{
		{Name: "lineProbability", Text: "λμ:(set(real) → extended_nonneg_real). " +
			"    probability_on(𝕌, borel_sets(real_topology), μ)"},
		{Name: "lineIntegral", Text: "λμ:(set(real) → extended_nonneg_real). λf:(real → real). " +
			"    measure_integral(𝕌, borel_sets(real_topology), μ, f)"},
		{Name: "lineIntegrable", Text: "λμ:(set(real) → extended_nonneg_real). λf:(real → real). " +
			"    real_integrable(𝕌, borel_sets(real_topology), μ, f)"},
	})
