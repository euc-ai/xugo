// family.go — the elliptic_curve family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=elliptic_curve.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/elliptic_curve go test -run TestRecordFamilyCNF ./library/integrity/gates/

package elliptic_curve

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed elliptic_curve.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// elliptic_curve/elliptic_curve.cnf.pb from the name's basename, and the
// registered entry prefix is `elliptic_curve.<Member>`.
var family = registry.NewFamily("scheme/elliptic_curve", familyCNF).WithAbbrev(Abbrev{
	{Name: "curveChart0", Text: "weierstrass_chart_zero(field_ring(L), k, x, y)"},
	{Name: "curveOverlap", Text: "ring_away(field_ring(L), «curveChart0», x)"},
	{Name: "omegaContainer", Text: "curve_dualizing_module(field_ring(L), k, x, «curveOverlap»)"},
	{Name: "omegaGenerator", Text: "weierstrass_dual_generator(field_ring(L), k, x, y)"},
	{Name: "overlapThroughInclusion", Text: "scalar_restriction(λx:A. x, " +
		"    regular_module(restrict_ring(field_ring(L), «curveOverlap»)))"},
	{Name: "curveKx", Text: "polynomial_image(field_ring(L), k, x)"},
	{Name: "curveLaurent", Text: "ring_away(field_ring(L), «curveKx», x)"},
	{Name: "omegaMaps", Text: "hom_set(restrict_ring(field_ring(L), «curveLaurent»), " +
		"    «overlapThroughInclusion», " +
		"    restrict_module(regular_module(field_ring(L)), «curveLaurent»))"},
	{Name: "curveChart1", Text: "weierstrass_chart_one(L, k, x, y)"},
	{Name: "curveOverLine", Text: "curve_over_line(L, " +
		"    k, " +
		"    x, " +
		"    «curveChart0», " +
		"    «curveChart1», " +
		"    «curveOverlap»)"},
	{Name: "omegaPair", Text: "curve_dualizing_pair(L, " +
		"    k, " +
		"    x, " +
		"    «curveChart0», " +
		"    «curveChart1», " +
		"    «curveOverlap»)"},
	{Name: "omegaChart0", Text: "fst(«omegaPair»)"},
	{Name: "omegaScaled", Text: "λr:A. λz:A. " +
		"    COND(z ∈ «curveOverlap», «omegaGenerator»(r * z), L.zero)"},
	{Name: "curveS2", Text: "(L.inv(x) * L.inv(x))"},
	{Name: "curveU", Text: "(y * «curveS2»)"},
	{Name: "omegaChart1", Text: "snd(«omegaPair»)"},
	{Name: "curveKs", Text: "polynomial_image(field_ring(L), k, L.inv(x))"},
	{Name: "curveOverlapRing", Text: "restrict_ring(field_ring(L), «curveOverlap»)"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
