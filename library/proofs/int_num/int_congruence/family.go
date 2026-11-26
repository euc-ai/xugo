// family.go — the int_congruence family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars
// (`var CongruentIffMultiple = family.Add(...)`);
// they never call InstallCNFCache — the replay harness installs
// familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=int_congruence.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=int_num/int_congruence go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT spellings and each rejects the other's:
// RECORD_CNF takes the full registered MEMBER name, whose prefix is the
// family name's last segment (registry.ByName is keyed on it), while
// CNF_GC takes the FAMILY name, which is the whole domain path.

package int_congruence

import (
	_ "embed"

	// int_product mints constants the statements here spell.
	_ "github.com/euc-ai/xugo/library/proofs/iterate/int/int_product"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed int_congruence.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates int_num/int_congruence/int_congruence.cnf.pb from it,
// and the registered entry prefix is the name's last segment
// (`int_congruence.<Member>`).
//
// The vocabulary is the VocabSpec in vocab.go, whose rows also render
// member bodies' build handles (zz_vocab_gen.go).
var family = registry.NewFamily("int_num/int_congruence", familyCNF).WithVocabSpec(
	vocab).WithAbbrev(Abbrev{
	{Name: "multiplesOf", Text: "{y:int | n ∣ y}"},
})
