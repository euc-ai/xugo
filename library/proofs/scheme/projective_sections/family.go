package projective_sections

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_form_pair"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed projective_sections.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/projective_sections", familyCNF).WithOuterAbbrev(
	projective_form_pair.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "parameter", Text: "«at»(G) * M.inv(«at»(F))"},
	{Name: "scaled", Text: "λj:num. " +
		"    image(M.mul(monoid_pow(M.mul, M.one, «parameter», j)), «chart»(G))"},
	{Name: "formsOver", Text: "λj:num. " +
		"    {y:A | " +
		"        y ∈ K ∧ " +
		"        ∃H:((num → num) → A). " +
		"            homogeneous_polynomial(«hilbertCoefficients», n, r * j, H) ∧ " +
		"            y * monoid_pow(M.mul, M.one, «at»(F), j) = «at»(H)}"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
