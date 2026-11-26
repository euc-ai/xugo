// family.go — the tauberian family manifest: the registry handle every member
// registers into, and the family's one shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=tauberian.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/tauberian go test -run TestRecordFamilyCNF ./library/integrity/gates/

package tauberian

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/cauchy_integral"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_cpow"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_log"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	_ "github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	_ "github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed tauberian.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `tauberian.<Member>`. The domain is ℂ: `&` of a real is complex_of_real,
// and a bare `&n` is a real. The multiplicative monoid of ℂ is bound, so
// `z ^ n` is the complex power. It reads cauchy_integral's table, which
// carries path_integral's: «segInt», the integral along the segment from z
// to w, «convex», a convex set of the plane, and «disc», the open disc
// about c of radius r. Its own table names «kernel», Newman's factor
// 1/z + z/R²; «partial», the N-th partial sum of a Dirichlet series;
// «numerator» and «weightedKernel», G(z)·N^z times 1 + z²/R² and times the
// kernel; and the pieces of Newman's contour: «arcInt», the integral along
// the circle of radius R about 0 over a parameter interval, «sides», the
// three sides iR → −δ + iR → −δ − iR → −iR of the rectangle to the left of
// the imaginary axis, «sidesInt», the integral along them, and «box», the
// closed box −δ ≤ Re z ≤ R, |Im z| ≤ R holding the contour.
var family = registry.NewFamily("complex/tauberian", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain).
	WithInstance(comm_monoid.CommMonoid, complex_field.MulMonoid).
	WithOuterAbbrev(cauchy_integral.ChapterAbbrev).
	WithAbbrev(Abbrev{
		{Name: "kernel", Text: "λR:real. λz:complex. complex_inv(z) + z / &(R * R)"},
		{Name: "partial", Text: "λa:(num → complex). λN:num. λs:complex. " +
			"    Σ_{n∈1 .. N} a(n) * complex_cpow(complex_of_real(&n), -s)"},
		{Name: "numerator", Text: "λG:(complex → complex). λR:real. λN:num. λz:complex. " +
			"    G(z) * complex_cpow(&N, z) * (&1 + (z * z) / &(R * R))"},
		{Name: "weightedKernel", Text: "λG:(complex → complex). λR:real. λN:num. λz:complex. " +
			"    G(z) * complex_cpow(&N, z) * «kernel»(R, z)"},
		{Name: "arcInt", Text: "λG:(complex → complex). λR:real. λa:real. λb:real. " +
			"    path_integral(G, " +
			"        circle_path(complex_of_real(&0), R), " +
			"        λt:real. complex_i * &R * exp(complex_i * &t), " +
			"        a, " +
			"        b)"},
		{Name: "sides", Text: "λR:real. λδ:real. " +
			"    {z:complex | (re(z) = -δ ∧ |im(z)| ≤ R) ∨ (-δ ≤ re(z) ∧ re(z) ≤ &0 ∧ |im(z)| = R)}"},
		{Name: "sidesInt", Text: "λG:(complex → complex). λR:real. λδ:real. " +
			"    «segInt»(G, complex_i * &R, -&δ + complex_i * &R) + " +
			"    «segInt»(G, -&δ + complex_i * &R, -&δ - complex_i * &R) + " +
			"    «segInt»(G, -&δ - complex_i * &R, -(complex_i * &R))"},
		{Name: "box", Text: "λR:real. λδ:real. {z:complex | -δ ≤ re(z) ∧ re(z) ≤ R ∧ |im(z)| ≤ R}"},
	})
