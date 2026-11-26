// External test package: corpus imports registry, so the spec
// define's corpus-backed force test must live outside package registry
// to keep the import graph acyclic (the define_recursive_test.go
// convention).
package registry_test

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// TestFamilyDefineSpecBodyForced — the spec shape's FRESH provenance
// through the ctx-hosted ExistenceBody form (the form emit-section
// renders), kernel-forced end to end: family.DefineSpec mints the
// constant's ε at registration, the Build's composite surfaces the
// pointwise existence obligation, the ExistenceBody closes it (ctx
// declarations + a By whose cite is the entry's declared dep), and
// the spec compiler Select-chains the closed obligation into the
// characterizing certificate. The specification pins the constant
// between n and n — choice against a two-sided bound — so the
// existence is one witness and one LessEqRefl cite; the deep-proof twin
// (transcript S's nat_sqrt — induction, the advance bridge, the
// nonlinear kernel) runs live in engine.TestTranscriptS_Battery.
func TestFamilyDefineSpecBodyForced(t *testing.T) {
	fam := registry.NewFamily("zz_define_spec_test", nil)
	entry := fam.DefineSpec(registry.SpecEntry{
		Name:   "SpecPin",
		Consts: []registry.SpecConst{{Const: "zz_reg_spec_pin", Type: "num → num"}},
		Spec:   "∀n:num. n ≤ zz_reg_spec_pin(n) ∧ zz_reg_spec_pin(n) ≤ n",
		ExistenceBody: func(ctx *proof.Script) []proof.Action {
			n0 := ctx.Var("n_0", dsl.NumType)
			return []proof.Action{
				proof.StripQuant(),
				proof.Witness(n0),
				proof.By(nat_order.LessEqRefl.Entry()),
			}
		},
		Deps: []registry.EntryLike{nat_order.LessEqRefl},
	})
	require.Equal(t, []*registry.ProofEntry{nat_order.LessEqRefl.Entry()}, entry.DepEntries()[:1],
		"the existence proof's cite is the declared dep, ahead of the spelled definers")
	require.Equal(t, proof.DefinitionSpec, entry.Definition, "the entry carries the served shape")

	// The harness realizes and installs a declared dep before Build
	// (the By cite wants a certificate); mirror it. The scope is a
	// recording scope (the live-session posture): the static policy
	// witness certifies only LANDED members — a test-only entry can have
	// no variant (fail-closed by design).
	serve.InstallProofPolicy()
	serve.InstallNatBundle()
	env := serve.NewSeedEnv()
	env.Scope = proof.NewProofScope(entry.Statement().Key())
	lessEqRefl := core.Force(context.Background(), core.AsThm(serve.EntryThm(env, nat_order.LessEqRefl)))
	registry.InstallLibraryDep(env, nat_order.LessEqRefl.Entry(), lessEqRefl)
	thm, _ := entry.Build.Fn(env)
	require.NotNil(t, thm)
	cert := core.Force(context.Background(), core.AsThm(thm))
	require.False(t, cert.IsZero(), "forcing the definition's theorem must yield a kernel cert")
	stmt := entry.Statement().Prop
	require.True(t, cert.Conclusion().AlphaEquals(stmt.Conclusion()),
		"the forced certificate must prove the characterizing statement")
}

// TestFamilyDefineSpecOverload — a spec constant's Overload word is
// registered once the mint has made the name a constant, the entry
// records it as the constant's surface, and a word that is not a
// lowercase identifier is refused at registration.
func TestFamilyDefineSpecOverload(t *testing.T) {
	fam := registry.NewFamily("zz_define_spec_overload_test", nil)
	entry := fam.DefineSpec(registry.SpecEntry{
		Name:   "SpecWord",
		Consts: []registry.SpecConst{{Const: "zz_reg_spec_worded", Type: "num → num", Overload: "zz_spec_word"}},
		Spec:   "∀n:num. n ≤ zz_reg_spec_worded(n) ∧ zz_reg_spec_worded(n) ≤ n",
		ExistenceBody: func(ctx *proof.Script) []proof.Action {
			n0 := ctx.Var("n_0", dsl.NumType)
			return []proof.Action{proof.StripQuant(), proof.Witness(n0), proof.By(nat_order.LessEqRefl.Entry())}
		},
		Deps: []registry.EntryLike{nat_order.LessEqRefl},
	})
	require.Equal(t, []string{"zz_reg_spec_worded"}, registry.GetConstMetaManager().OverloadConsts("zz_spec_word"),
		"the word names the spec constant")
	require.Equal(t, "zz_spec_word", entry.Notation("zz_reg_spec_worded"), "the entry carries the word as the constant's surface")
	require.Equal(t, "", entry.Notation("zz_other"), "a constant the entry does not define has no surface")

	require.PanicsWithValue(t,
		`registry.DefineSpec(SpecBadWord): Consts[0] Overload "Zz_Bad": a word is a lowercase identifier`,
		func() {
			fam.DefineSpec(registry.SpecEntry{
				Name:      "SpecBadWord",
				Consts:    []registry.SpecConst{{Const: "zz_reg_spec_badword", Type: "num → num", Overload: "Zz_Bad"}},
				Spec:      "∀n:num. n ≤ zz_reg_spec_badword(n)",
				Existence: []proof.Action{proof.By(nat_order.LessEqRefl.Entry())},
				Deps:      []registry.EntryLike{nat_order.LessEqRefl},
			})
		})
}
