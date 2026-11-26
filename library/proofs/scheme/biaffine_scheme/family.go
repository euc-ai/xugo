// family.go — the biaffine_scheme family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=biaffine_scheme.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/biaffine_scheme go test -run TestRecordFamilyCNF ./library/integrity/gates/

package biaffine_scheme

import (
	_ "embed"

	// The chapters whose constants the definitions spell, initialized
	// before them.
	_ "github.com/euc-ai/xugo/library/proofs/scheme/locally_ringed_space"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/structure_sheaf"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed biaffine_scheme.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// biaffine_scheme/biaffine_scheme.cnf.pb from the name's basename, and
// the registered entry prefix is `biaffine_scheme.<Member>`.
var family = registry.NewFamily("scheme/biaffine_scheme", familyCNF).WithAbbrev(Abbrev{
	{Name: "wa1Biaffine", Text: "biaffine(R, A₀, A₁, t, s)"},
})
