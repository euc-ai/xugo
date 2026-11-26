package quadratic_residue

import (
	_ "embed"

	// int_sum mints constants the statements here spell.
	_ "github.com/euc-ai/xugo/library/proofs/iterate/int/int_sum"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed quadratic_residue.cnf.pb
var familyCNF []byte

// family is the family handle. The chapter names two terms its proofs keep
// returning to: h(n) = (n − 1)/2, half of n − 1, which writes an odd prime as
// p = 2h + 1 and is the exponent of the sign (−1)^((n−1)/2) of an odd n; and
// the absolute least residue s of k·a modulo p, the one of r and p − r that
// lies in 1 .. h for the residue r of k·a.
var family = registry.NewFamily("int_num/quadratic_residue", familyCNF).WithAbbrev(Abbrev{
	{Name: "h", Text: "λn:num. div(n - 1, 2)"},
	{Name: "s", Text: "λp:num. λa:num. λk:num. " +
		"    COND(«h»(p) < rem(k * a, p), p - rem(k * a, p), rem(k * a, p))"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under it
// name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
