package registry_test

// define_membership_read_test.go — DefEntry.MembershipRead: a direct
// definition whose definiens is a set-builder over its arguments enters
// the closers' membership reading and the set driver's vocabulary; any
// other definition declaring it is refused at the door.

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/stretchr/testify/require"
)

func TestDefine_MembershipRead(t *testing.T) {
	fam := registry.NewFamily("zz_define_membership_read_test", nil)
	fam.Define(registry.DefEntry{
		Name:           "Below",
		Const:          "zz_reg_below",
		Type:           "num → num → bool",
		Equations:      []string{"∀n:num. zz_reg_below(n) = {i:num | i < n}"},
		MembershipRead: true,
	})
	require.Contains(t, tactic.MembershipReadConstants(), core.TermName("zz_reg_below"))
	require.Contains(t, proof.StandardSetVocabulary(), "zz_reg_below")

	// The same definiens undeclared stays out of both.
	fam.Define(registry.DefEntry{
		Name:      "BelowClosed",
		Const:     "zz_reg_below_closed",
		Type:      "num → num → bool",
		Equations: []string{"∀n:num. zz_reg_below_closed(n) = {i:num | i < n}"},
	})
	require.NotContains(t, tactic.MembershipReadConstants(), core.TermName("zz_reg_below_closed"))
	require.NotContains(t, proof.StandardSetVocabulary(), "zz_reg_below_closed")

	// A set that is no set-builder over the arguments is refused.
	refusal := func(e registry.DefEntry) (r any) {
		defer func() { r = recover() }()
		fam.Define(e)
		return nil
	}
	require.Contains(t, fmt.Sprint(refusal(registry.DefEntry{
		Name:           "Lambda",
		Const:          "zz_reg_below_lambda",
		Type:           "num → num → bool",
		Equations:      []string{"∀n i:num. zz_reg_below_lambda(n, i) ⇔ i < n"},
		MembershipRead: true,
	})), "registry.Define(Lambda): MembershipRead: the definiens of zz_reg_below_lambda is no set-builder over its arguments")
	// So is a recursive definition.
	require.Contains(t, fmt.Sprint(refusal(registry.DefEntry{
		Name:  "Upto",
		Const: "zz_reg_upto",
		Type:  "num → num → bool",
		Equations: []string{
			"zz_reg_upto(0) = {i:num | i = 0}",
			"∀n:num. zz_reg_upto(suc(n)) = {i:num | i = suc(n) ∨ i ∈ zz_reg_upto(n)}",
		},
		MembershipRead: true,
	})), "registry.Define(Upto): MembershipRead declares a set-builder definition")
}
