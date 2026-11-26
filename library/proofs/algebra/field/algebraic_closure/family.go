package algebraic_closure

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_quotient"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed algebraic_closure.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/algebraic_closure", familyCNF).WithOuterAbbrev(
	polynomial_quotient.ChapterAbbrev, polynomial_roots.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "closureEmbedding", Text: "(λa:A. {(0, λn:num. a)})"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
