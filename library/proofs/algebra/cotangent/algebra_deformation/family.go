// family.go — the algebra_deformation family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=algebra_deformation.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/cotangent/algebra_deformation go test -run TestRecordFamilyCNF ./library/integrity/gates/

package algebra_deformation

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/square_zero_extension"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed algebra_deformation.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// algebra_deformation/algebra_deformation.cnf.pb from the name's basename, and the
// registered entry prefix is `algebra_deformation.<Member>`.
var family = registry.NewFamily("algebra/cotangent/algebra_deformation", familyCNF).WithOuterAbbrev(
	square_zero_extension.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "overT", Text: "square_zero_extension(R, T, λa:A. g(f(a)), N)"},
	{Name: "overS", Text: "square_zero_extension(R, S, f, scalar_restriction(g, N))"},
	{Name: "liftOfG", Text: "square_zero_lift(R, S, f, g)"},
	{Name: "cohomologyTS", Text: "cotangent_cohomology⟨U:U⟩(S, T, g, T, λc:C. c, N)"},
	{Name: "classT", Text: "square_zero_class(R, T, λa:A. g(f(a)), N)"},
	{Name: "rightMap", Text: "co_transitivity_right_map(R, S, f, T, g, N, 1)"},
	{Name: "classS", Text: "square_zero_class(R, S, f, scalar_restriction(g, N))"},
	{Name: "leftMap", Text: "co_transitivity_left_map(R, S, f, T, g, N, 1)"},
	{Name: "deformation", Text: "algebra_deformation(R, R₀, f, T, g, M, ι)"},
	{Name: "deformationTReduced", Text: "cotangent_cohomology(R₀, T, g, T, λc:C. c, M)"},
	{Name: "classOfT", Text: "square_zero_class(R, T, λa:A. g(f(a)), M)"},
	{Name: "deformationTR", Text: "cotangent_cohomology(R, T, λa:A. g(f(a)), T, λc:C. c, M)"},
	{Name: "deformationLeft", Text: "co_transitivity_left_map(R, R₀, f, T, g, M, 1)"},
})
