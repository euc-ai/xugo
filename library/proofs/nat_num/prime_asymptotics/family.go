// family.go — the prime_asymptotics family manifest: the registry handle every member
// registers into, and the family's one shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=prime_asymptotics.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=nat_num/prime_asymptotics go test -run TestRecordFamilyCNF ./library/integrity/gates/

package prime_asymptotics

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	_ "github.com/euc-ai/xugo/library/proofs/complex/riemann_zeta"
	_ "github.com/euc-ai/xugo/library/proofs/complex/tauberian"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/prime_distribution"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed prime_asymptotics.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `prime_asymptotics.<Member>`. The domain is ℝ: a bare `&n` is a real,
// and a complex number is written with complex_of_real. Its table names the
// terms the chapter's statements share: the coefficients ψ(n)/n, ψ(n)/n − 1
// and Λ(n) of its Dirichlet series and the half-plane Re s > 0; the
// «correction», the sum of the series of the «correctionTerm»s
// ψ(n + 1)·((n + 1)^(−s−1) − ((n + 1)^(−s) − (n + 2)^(−s))/s), by which the
// Dirichlet series of ψ(n)/n differs from D(Λ, s)/s, with the parts of its
// term and the power (n + 1)^(−Re s − 1) that bounds it; and the
// «centeredTerm» (ψ(k + 1)/(k + 1) − 1)/(k + 1), the real term of the series
// of ψ(n)/n − 1 at s = 1.
var family = registry.NewFamily("nat_num/prime_asymptotics", familyCNF).WithCoerceDomain(
	RealDomain).WithAbbrev(Abbrev{
	{Name: "psiRatio", Text: "λn:num. complex_of_real(chebyshev_psi(n) / &n)"},
	{Name: "centeredRatio", Text: "λn:num. complex_of_real(chebyshev_psi(n) / &n - &1)"},
	{Name: "mangoldt", Text: "λn:num. complex_of_real(von_mangoldt(n))"},
	{Name: "halfPlane", Text: "{s:complex | &0 < re(s)}"},
	{Name: "shiftedPower", Text: "λs:complex. λn:num. " +
		"    complex_cpow(complex_of_real(&(n + 1)), -s - complex_of_real(&1))"},
	{Name: "powerDifference", Text: "λs:complex. λn:num. " +
		"    complex_cpow(complex_of_real(&(n + 1)), -s) - complex_cpow(complex_of_real(&(n + 2)), -s)"},
	{Name: "correctionBracket", Text: "λs:complex. λn:num. " +
		"    «shiftedPower»(s, n) - «powerDifference»(s, n) / s"},
	{Name: "correctionTerm", Text: "λs:complex. λn:num. " +
		"    complex_of_real(chebyshev_psi(n + 1)) * «correctionBracket»(s, n)"},
	{Name: "correction", Text: "λs:complex. εv:complex. complex_sums(«correctionTerm»(s), v)"},
	{Name: "correctionPower", Text: "λs:complex. λn:num. real_rpow(&(n + 1), -(re(s) + &1))"},
	{Name: "centeredTerm", Text: "λk:num. (chebyshev_psi(k + 1) / &(k + 1) - &1) / &(k + 1)"},
})
