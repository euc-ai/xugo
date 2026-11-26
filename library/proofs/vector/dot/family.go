// family.go — the dot family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=dot.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=vector/dot go test -run TestRecordFamilyCNF ./library/integrity/gates/

package dot

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed dot.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives dot/dot.cnf.pb from
// the name's basename, and the registered entry prefix is `dot.<Member>`.
var family = registry.NewFamily("vector/dot", familyCNF).WithAbbrev(Abbrev{
	{Name: "activeRange", Text: "{i:num | i < n}"},
	{Name: "products", Text: "Σ_{i<n} u(i) * v(i)"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
