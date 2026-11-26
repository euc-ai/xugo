// family.go — the lattice_pair family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=lattice_pair.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/lattice_pair go test -run TestRecordFamilyCNF ./library/integrity/gates/

package lattice_pair

import (
	_ "embed"

	// The chapters whose constants the definitions spell, initialized
	// before them.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed lattice_pair.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// lattice_pair/lattice_pair.cnf.pb from the name's basename, and
// the registered entry prefix is `lattice_pair.<Member>`.
var family = registry.NewFamily("scheme/lattice_pair", familyCNF).WithAbbrev(Abbrev{
	{Name: "waPair", Text: "lattice_pair(R, A₀, A₁, V)"},
	{Name: "waBiaffine", Text: "biaffine(R, A₀, A₁, t, s)"},
	{Name: "waDim", Text: "module_dim(restrict_ring(R, k))"},
	{Name: "waFinite", Text: "finite_dimensional(restrict_ring(R, k))"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
