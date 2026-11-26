// family.go — the cauchy_integral family manifest: the registry handle
// every member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=cauchy_integral.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/cauchy_integral go test -run TestRecordFamilyCNF ./library/integrity/gates/

package cauchy_integral

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed cauchy_integral.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `cauchy_integral.<Member>`. The domain is ℂ: `&` of a real is
// complex_of_real, and a bare `&n` is a real. The multiplicative monoid of
// ℂ is bound, so `z ^ n` is the complex power. It reads path_integral's
// table, «segInt» the integral along the segment from z to w and
// «circleInt» the integral once round the circle about c of radius r; its
// own table names the other terms the chapter's statements share: the
// closed triangle with vertices a, b, c, the integral round its boundary,
// its perimeter, a convex set of the plane, the open disc about c of radius
// r, and the k-th coefficient of f about c read off the circle of radius r,
// the integral of f(u)/(u − c)ᵏ⁺¹ round it over 2πi.
var family = registry.NewFamily("complex/cauchy_integral", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain).
	WithInstance(comm_monoid.CommMonoid, complex_field.MulMonoid).
	WithOuterAbbrev(path_integral.ChapterAbbrev).
	WithAbbrev(Abbrev{
		{Name: "triangle", Text: "λa:complex. λb:complex. λc:complex. " +
			"    {z:complex | ∃s t:real. &0 ≤ s ∧ &0 ≤ t ∧ s + t ≤ &1 ∧ z = a + &s * (b - a) + &t * (c - a)}"},
		{Name: "boundaryInt", Text: "λf:(complex → complex). λa:complex. λb:complex. λc:complex. " +
			"    «segInt»(f, a, b) + «segInt»(f, b, c) + «segInt»(f, c, a)"},
		{Name: "perimeter", Text: "λa:complex. λb:complex. λc:complex. |b - a| + |c - b| + |a - c|"},
		{Name: "convex", Text: "λK:set(complex). ∀x y:complex. ∀θ:real. " +
			"    x ∈ K ∧ y ∈ K ∧ &0 ≤ θ ∧ θ ≤ &1 ⇒ segment_path(x, y, θ) ∈ K"},
		{Name: "disc", Text: "λc:complex. λr:real. {u:complex | |u - c| < r}"},
		{Name: "coef", Text: "λf:(complex → complex). λc:complex. λr:real. λk:num. " +
			"    «circleInt»(λu:complex. f(u) / (u - c) ^ (k + 1), c, r) / (&(&2 * pi) * complex_i)"},
	})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
