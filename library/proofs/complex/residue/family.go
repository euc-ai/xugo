// family.go — the residue family manifest: the registry handle every member
// registers into, and the family's one shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=residue.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/residue go test -run TestRecordFamilyCNF ./library/integrity/gates/

package residue

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/cauchy_integral"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed residue.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `residue.<Member>`. The domain is ℂ: `&` of a real is complex_of_real, and a
// bare `&n` is a real. The multiplicative monoid of ℂ is bound, so `z ^ n` is
// the complex power. It reads cauchy_integral's table, and through it
// path_integral's. Its own table names the punctured disc, the index of a
// circle run once round, and the shapes a function takes near a point: at most
// a pole («meromorphicAt», its numerator allowed to vanish at the point), a
// pole factor and a zero factor of order m, each with a cofactor not 0 there,
// and a pole proper («properPole»).
var family = registry.NewFamily("complex/residue", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain).
	WithInstance(comm_monoid.CommMonoid, complex_field.MulMonoid).
	WithOuterAbbrev(cauchy_integral.ChapterAbbrev).
	WithAbbrev(Abbrev{
		{Name: "punctured", Text: "λc:complex. λr:real. {u:complex | &0 < |u - c| ∧ |u - c| < r}"},
		{Name: "circleIndex", Text: "λc:complex. λr:real. λw:complex. " +
			"    winding_index(circle_path(c, r), " +
			"        λt:real. complex_i * &r * exp(complex_i * &t), " +
			"        &0, " +
			"        &2 * pi, " +
			"        w)"},
		{Name: "meromorphicAt", Text: "λf:(complex → complex). " +
			"λp:complex. " +
			"∃ρ:real. " +
			"∃g:(complex → complex). " +
			"∃m:num. " +
			"    &0 < ρ ∧ " +
			"    holomorphic_on(«disc»(p, ρ), g) ∧ " +
			"    ∀z:complex. z ∈ «punctured»(p, ρ) ⇒ f(z) = g(z) / (z - p) ^ (m + 1)"},
		{Name: "poleFactor", Text: "λf:(complex → complex). " +
			"λc:complex. " +
			"λm:num. " +
			"∃ρ:real. " +
			"∃g:(complex → complex). " +
			"    &0 < ρ ∧ " +
			"    holomorphic_on(«disc»(c, ρ), g) ∧ " +
			"    g(c) ≠ &0 ∧ " +
			"    ∀z:complex. z ∈ «punctured»(c, ρ) ⇒ f(z) = g(z) / (z - c) ^ m"},
		{Name: "zeroFactor", Text: "λf:(complex → complex). " +
			"λc:complex. " +
			"λm:num. " +
			"∃ρ:real. " +
			"∃g:(complex → complex). " +
			"    &0 < ρ ∧ " +
			"    holomorphic_on(«disc»(c, ρ), g) ∧ " +
			"    g(c) ≠ &0 ∧ " +
			"    ∀z:complex. |z - c| < ρ ⇒ f(z) = (z - c) ^ m * g(z)"},
		{Name: "properPole", Text: "λf:(complex → complex). λp:complex. ∃m:num. «poleFactor»(f, p, m + 1)"},
	})
