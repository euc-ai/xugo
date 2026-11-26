// family.go — the nonneg_real_formal_diff family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var AddSym =
// family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=nonneg_real_formal_diff.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/tower/nonneg_real_formal_diff go test -run TestRecordFamilyCNF ./library/integrity/gates/

package nonneg_real_formal_diff

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	nn "github.com/euc-ai/xugo/library/proofs/real/tower/internal/nonneg_real"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/algebra"
)

//go:embed nonneg_real_formal_diff.cnf.pb
var familyCNF []byte

// family is the family handle. The subtest name is real/tower/nonneg_real_formal_diff;
// the package directory (for the recorder's pb path) is carried
// explicitly because internal/ breaks the name↔dir convention.
var family = registry.NewFamilyIn(
	"real/tower/nonneg_real_formal_diff",
	"real/tower/internal/nonneg_real_formal_diff",
	familyCNF).WithVocabSpec(
	vocab)

// hrealAdd is the family's AC spec for the hreal additive monoid,
// built from nonneg_real's own AddSym / AddAssoc entries. Every nonneg_real_formal_diff
// proof that regroups a sum of hreal atoms — the two welldef proofs,
// TrealEqTrans, MulAssoc, LeftDistrib — wants the same spec, so the family
// states it once and each member asks for the bracketing it needs
// (Group.RegroupSection / Group.Perm4Text).
func hrealAdd(ctx *Script) algebra.Group {
	return algebra.Group{
		TypeText: "hreal", OpText: "hreal_add",
		Sym:   ctx.DepNormalized(nn.AddSym),
		Assoc: ctx.DepNormalized(nn.AddAssoc),
	}
}
