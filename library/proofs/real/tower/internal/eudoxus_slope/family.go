// family.go — the eudoxus_slope family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var AddSym =
// family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=slope.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/tower/eudoxus_slope go test -run TestRecordFamilyCNF ./library/integrity/gates/

package eudoxus_slope

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed eudoxus_slope.cnf.pb
var familyCNF []byte

// family is the family handle. The subtest name is real/tower/eudoxus_slope; the
// package directory (for the recorder's pb path) is carried
// explicitly because internal/ breaks the name↔dir convention. The
// alphabet it installs is vocab.go's.
var family = registry.NewFamilyIn(
	"real/tower/eudoxus_slope", "real/tower/internal/eudoxus_slope", familyCNF).WithVocabSpec(
	vocab)

// naddTypeDefAxioms reads the two nadd type-definition axioms —
//
//	retraction: ⊢ mk_nadd(dest_nadd(x)) = x
//	membership: ⊢ is_nadd(r) ⇔ (dest_nadd(mk_nadd(r)) = r)
//
// — off the type's own definition (NaddDef, definitions.go). A member
// calling this reads both entries through its own script.
func naddTypeDefAxioms(ctx *Script) (retraction, membership Thm) {
	return ctx.Dep(NaddDef.Retraction), ctx.Dep(NaddDef.Membership)
}

// naddMembership is naddTypeDefAxioms for the common case that keeps
// only the membership direction — a proof that packages a carrier
// into mk_nadd and never starts from one has no use for retraction.
func naddMembership(ctx *Script) Thm {
	return ctx.Dep(NaddDef.Membership)
}
