// family.go — the nonneg_real family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var AddSym =
// family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=nonneg_real.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/tower/nonneg_real go test -run TestRecordFamilyCNF ./library/integrity/gates/

package nonneg_real

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed nonneg_real.cnf.pb
var familyCNF []byte

// family is the family handle. The subtest name is real/tower/nonneg_real; the
// package directory (for the recorder's pb path) is carried
// explicitly because internal/ breaks the name↔dir convention.
var family = registry.NewFamilyIn(
	"real/tower/nonneg_real", "real/tower/internal/nonneg_real", familyCNF).WithVocabSpec(
	vocab)
