// family.go — the projective_line_free_pair family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=projective_line_free_pair.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/projective_line_free_pair go test -run TestRecordFamilyCNF ./library/integrity/gates/

package projective_line_free_pair

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed projective_line_free_pair.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// projective_line_free_pair/projective_line_free_pair.cnf.pb from the name's basename, and
// the registered entry prefix is `projective_line_free_pair.<Member>`.
var family = registry.NewFamily("scheme/projective_line_free_pair", familyCNF).WithOuterAbbrev(
	projective_line.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "plFreePair", Text: "projective_line_free_pair(L, k, t, E, N)"},
	{Name: "plGenerators", Text: "{laurent_monomial(t, N(x)) * x | x:A | x ∈ E}"},
	{Name: "plFreeChart0", Text: "module_span(«plRing0», «plField», E)"},
	{Name: "plFreeChart1", Text: "module_span(«plRing1», «plField», «plGenerators»)"},
	{Name: "plOverlapSpanE", Text: "module_span(«plRing», «plField», E)"},
	{Name: "plPairAtE", Text: "projective_line_pair(L, k, t, N(e))"},
	{Name: "plScaledPairAtE", Text: "lattice_pair_scale(e, «plPairAtE»)"},
	{Name: "plAmbientOf", Text: "lattice_pair_ambient(«plRing», «plField»)"},
	{Name: "plScaledPairN", Text: "lattice_pair_scale(e, «plPairN»)"},
	{Name: "plFreePairEmpty", Text: "projective_line_free_pair(L, k, t, ∅, N)"},
	{Name: "plFreePairD", Text: "projective_line_free_pair(L, k, t, D, N)"},
	{Name: "plFreePairInsertD", Text: "projective_line_free_pair(L, k, t, insert(e, D), N)"},
})
