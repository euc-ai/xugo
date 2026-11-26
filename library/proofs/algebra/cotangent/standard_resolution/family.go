// family.go — the standard_resolution family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=standard_resolution.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/cotangent/standard_resolution go test -run TestRecordFamilyCNF ./library/integrity/gates/

package standard_resolution

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed standard_resolution.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// standard_resolution/standard_resolution.cnf.pb from the name's basename, and the
// registered entry prefix is `standard_resolution.<Member>`.
var family = registry.NewFamily(
	"algebra/cotangent/standard_resolution", familyCNF).WithAbbrev(Abbrev{
	{Name: "baseInclusion", Text: "universe_algebra_map(R, R, λa:A. a, universe_tag(0))"},
	{Name: "columnEps", Text: "relative_vertical_eps⟨U:U⟩(R, S, f, T, g)"},
	{Name: "verticalFace", Text: "relative_vertical_face(R, S, f, T, g)"},
	{Name: "hostZero", Text: "universe_algebra_ring(R, 𝕌⟨A:U⟩).zero"},
	{Name: "diagonalNames", Text: "λn:num. " +
		"    image(universe_tag(0), standard_names(R, S, n)) ∪ " +
		"    image(universe_tag(1), relative_names(R, S, T, n, n))"},
	{Name: "diagonalFaces", Text: "bisimplicial_diagonal_face( " +
		"    λp:num. λq:num. λi:num. relative_horizontal_map(R, standard_face(R, S, f, p, i), q), " +
		"    relative_vertical_face(R, S, f, T, g))"},
	{Name: "diagonalDegeneracies", Text: "bisimplicial_diagonal_degeneracy( " +
		"    λp:num. λq:num. λi:num. relative_horizontal_map(R, standard_degeneracy(R, p, i), q), " +
		"    λp:num. relative_vertical_degeneracy(R))"},
})
