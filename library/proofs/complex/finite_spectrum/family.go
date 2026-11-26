package finite_spectrum

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed finite_spectrum.cnf.pb
var familyCNF []byte

// family is the family handle. The domain is ℂ: `&` of a real is
// complex_of_real, and a bare `&n` is a real, since a modulus is one.
// The table names the series the chapter's statements share: the reciprocal
// linear factor 1 − rT, its geometric inverse with coefficients rⁿ, the
// counting sequence of that factor (−rⁿ past the zero at n = 0), the counting
// sequence of a reciprocal product (the negative power sums past the zero at
// n = 0), the denominator (1 − T)(1 − qT), and its inverse, the product of the
// two geometric series.
var family = registry.NewFamily("complex/finite_spectrum", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain).
	WithInstance(comm_ring.CommRing, complex_field.CommRing).
	WithInstance(comm_monoid.CommMonoid, complex_field.MulMonoid).WithAbbrev(Abbrev{
	{Name: "linearFactor", Text: "λr:complex. λn:num. " +
		"    COND(n = 0, complex_of_real(&1), COND(n = 1, -r, complex_of_real(&0)))"},
	{Name: "geometric", Text: "λr:complex. λn:num. r ^ n"},
	{Name: "linearCounts", Text: "λr:complex. λn:num. COND(n = 0, complex_of_real(&0), -(r ^ n))"},
	{Name: "spectrumCounts", Text: "λs:num. λa:(num → complex). λn:num. " +
		"    COND(n = 0, complex_of_real(&0), -finite_power_sum(s, a, n))"},
	{Name: "denominator", Text: "λq:num. " +
		"    polynomial_mul(«linearFactor»(complex_of_real(&1)), «linearFactor»(complex_of_real(&q)))"},
	{Name: "denominatorInverse", Text: "λq:num. " +
		"    polynomial_mul(«geometric»(complex_of_real(&1)), «geometric»(complex_of_real(&q)))"},
})
