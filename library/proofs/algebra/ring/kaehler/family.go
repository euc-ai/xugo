// family.go — the kaehler family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=kaehler.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/kaehler go test -run TestRecordFamilyCNF ./library/integrity/gates/

package kaehler

import (
	_ "embed"

	// The chapters whose constants the statements here spell.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed kaehler.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// kaehler/kaehler.cnf.pb from the name's basename, and the
// registered entry prefix is `kaehler.<Member>`.
var family = registry.NewFamily("algebra/ring/kaehler", familyCNF)
