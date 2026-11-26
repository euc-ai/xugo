// family.go — the fractional_ideal family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=fractional_ideal.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/fractional_ideal go test -run TestRecordFamilyCNF ./library/integrity/gates/

package fractional_ideal

import (
	_ "embed"

	// The chapters whose constants the definitions and the statements
	// spell, initialized before them.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed fractional_ideal.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// fractional_ideal/fractional_ideal.cnf.pb from the name's basename, and
// the registered entry prefix is `fractional_ideal.<Member>`.
var family = registry.NewFamily("algebra/ring/fractional_ideal", familyCNF).WithAbbrev(Abbrev{
	{Name: "wfScalars", Text: "restrict_ring(field_ring(L), S)"},
	{Name: "wfField", Text: "regular_module(field_ring(L))"},
	{Name: "wfFractional", Text: "submodule(«wfScalars», «wfField»)"},
	{Name: "wfMul", Text: "fractional_mul(field_ring(L), S)"},
	{Name: "wfInverse", Text: "fractional_inverse(field_ring(L), S)"},
	{Name: "wfInvertible", Text: "invertible_fractional(field_ring(L), S)"},
	{Name: "wfSpan", Text: "module_span(«wfScalars», «wfField»)"},
	{Name: "oneAndElement", Text: "{p + q * e | p:A, q:A | p ∈ S ∧ q ∈ S}"},
	{Name: "wfIdeal", Text: "ring_ideal(restrict_ring(field_ring(L), S))"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
