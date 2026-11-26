// External test package: corpus imports registry, so the recursive
// define's corpus-backed force test must live outside package registry
// to keep the import graph acyclic.
package registry_test

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/relations/well_founded"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// TestFamilyDefineRecursiveSumtoForced is transcript A1's
// twin, kernel-forced end to end: family.Define mints sumto's ε at
// registration, the Build's composite compiles the existence from the
// REAL num_recursion (peano.Recursion, which the door finds by its served
// name and adds as the entry's dep), and forcing the returned promise runs
// the whole cone to a kernel certificate.
func TestFamilyDefineRecursiveSumtoForced(t *testing.T) {
	fam := registry.NewFamily("zz_define_rec_test", nil)
	entry := fam.Define(registry.DefEntry{
		Name:  "Sumto",
		Const: "zz_reg_sumto",
		Type:  "num → num",
		Equations: []string{
			"zz_reg_sumto(0) = 0",
			"∀n:num. zz_reg_sumto(suc(n)) = zz_reg_sumto(n) + suc(n)",
		},
	})
	require.Equal(t, []registry.EntryLike{peano.Recursion.Entry()}, entry.Deps,
		"the door finds the carrier's schema by its served name and declares it")
	require.Equal(t, proof.DefinitionRecursive, entry.Definition, "the entry carries the served shape")
	require.Equal(t, registry.UnmintedKeyPrefix+entry.Name, entry.Key,
		"declared without a Key, the definition carries the unminted sentinel")

	env := serve.NewSeedEnv()
	env.Scope = proof.NewProofScope(entry.Statement().Key())
	thm, _ := entry.Build.Fn(env)
	require.NotNil(t, thm)

	cert := core.Force(context.Background(), core.AsThm(thm))
	require.False(t, cert.IsZero(), "forcing the definition's theorem must yield a kernel cert")
	stmt := entry.Statement().Prop
	require.True(t, cert.Conclusion().AlphaEquals(stmt.Conclusion()),
		"the forced certificate must prove the characterizing statement")
}

// forceDefineEntry builds and kernel-forces a define entry against the
// real corpus, checking the certificate proves the characterizing
// statement. The corpus proof policy and nat bundle are installed
// first (idempotent — the replay-harness TestMain convention): forcing
// a list-theory schema's cone runs generated proofs whose Arith steps
// need them.
func forceDefineEntry(t *testing.T, entry *registry.ProofEntry) {
	t.Helper()
	serve.InstallProofPolicy()
	serve.InstallNatBundle()
	env := serve.NewSeedEnv()
	env.Scope = proof.NewProofScope(entry.Statement().Key())
	thm, _ := entry.Build.Fn(env)
	require.NotNil(t, thm)
	cert := core.Force(context.Background(), core.AsThm(thm))
	require.False(t, cert.IsZero(), "forcing the definition's theorem must yield a kernel cert")
	stmt := entry.Statement().Prop
	require.True(t, cert.Conclusion().AlphaEquals(stmt.Conclusion()),
		"the forced certificate must prove the characterizing statement")
}

// TestFamilyDefineCurriedAddForced — the v1.1a shape (recursion
// argument first, one curried extra parameter) kernel-forced through
// the REAL num_recursion: the ADD twin.
func TestFamilyDefineCurriedAddForced(t *testing.T) {
	fam := registry.NewFamily("zz_define_curry_add_test", nil)
	entry := fam.Define(registry.DefEntry{
		Name:  "CAdd",
		Const: "zz_reg_cadd",
		Type:  "num → num → num",
		Equations: []string{
			"∀n:num. zz_reg_cadd(0, n) = n",
			"∀m n:num. zz_reg_cadd(suc(m), n) = suc(zz_reg_cadd(m, n))",
		},
	})
	require.Equal(t, []registry.EntryLike{peano.Recursion.Entry()}, entry.Deps)
	forceDefineEntry(t, entry)
}

// TestFamilyDefineCurriedSubForced — the v1.1b shape (recursion on the
// SECOND argument — the reshuffle) kernel-forced through the REAL
// num_recursion: the SUB twin. The characterizing statement keeps the
// author's argument order.
func TestFamilyDefineCurriedSubForced(t *testing.T) {
	fam := registry.NewFamily("zz_define_curry_sub_test", nil)
	entry := fam.Define(registry.DefEntry{
		Name:  "CSub",
		Const: "zz_reg_csub",
		Type:  "num → num → num",
		Equations: []string{
			"∀m:num. zz_reg_csub(m, 0) = m",
			"∀m n:num. zz_reg_csub(m, suc(n)) = predecessor(zz_reg_csub(m, n))",
		},
	})
	require.Equal(t, []registry.EntryLike{peano.Recursion.Entry()}, entry.Deps)
	forceDefineEntry(t, entry)
}

// TestFamilyDefineCurriedMapForced — the v1.1b reshuffle at a
// POLYMORPHIC list carrier (recursion on the second argument past a
// function-typed extra parameter) through the REAL list_recursion
// statement: the list_map twin. Kernel-forced end to end like the num_recursion
// twins above: the corpus serves list_recursion from the datatypes/list
// chapter, whose cone forces.
func TestFamilyDefineCurriedMapForced(t *testing.T) {
	fam := registry.NewFamily("zz_define_curry_map_test", nil)
	entry := fam.Define(registry.DefEntry{
		Name:  "CMap",
		Const: "zz_reg_cmap",
		Type:  "(A → B) → list(A) → list(B)",
		Equations: []string{
			"∀f:A → B. zz_reg_cmap(f, nil) = nil",
			"∀f:A → B. ∀h:A. ∀t:list(A). zz_reg_cmap(f, cons(h, t)) = cons(f(h), zz_reg_cmap(f, t))",
		},
	})
	require.Equal(t, []registry.EntryLike{list.Recursion.Entry()}, entry.Deps)
	forceDefineEntry(t, entry)
}

// TestFamilyDefineWFGcdForced — transcript D1's twin (the WF
// shape), kernel-forced end to end: family.Define mints gcd2's ε
// at registration; the Build's composite surfaces the termination
// obligation, the entry's Termination actions close it (By against the
// nat_div_mod.Division entry), and the WF compiler discharges the existence
// from the served wellfounded_recursion/wellfounded_measure_less rows — all declared as the
// entry's typed deps (the wellfounded entries serve those names).
func TestFamilyDefineWFGcdForced(t *testing.T) {
	fam := registry.NewFamily("zz_define_wf_test", nil)
	entry := fam.Define(registry.DefEntry{
		Name:  "Gcd2",
		Const: "zz_reg_gcd2",
		Type:  "num → num → num",
		Equations: []string{
			"∀m n:num. zz_reg_gcd2(m, n) = COND(n = 0, m, zz_reg_gcd2(n, nat_mod(m, n)))",
		},
		Measure:     "λn:num. n",
		Termination: []proof.Action{proof.By(nat_div_mod.Division.Entry())},
		Deps:        []registry.EntryLike{well_founded.Recursion, well_founded.Measure, nat_div_mod.Division},
	})
	require.Equal(t, []*registry.ProofEntry{well_founded.Recursion.Entry(), well_founded.Measure.Entry(), nat_div_mod.Division.Entry()},
		entry.DepEntries()[:3], "the schema rows and the termination cite are the declared deps, ahead of the spelled definers")
	require.Equal(t, proof.DefinitionWF, entry.Definition, "the entry carries the served shape")

	// The harness realizes and installs a declared dep before Build
	// (Script.Dep wants a ThmCert); mirror it for the termination cite. The
	// schema rows stay promises — the WF compile is promise-
	// transparent.
	env := serve.NewSeedEnv()
	env.Scope = proof.NewProofScope(entry.Statement().Key())
	division := core.Force(context.Background(), core.AsThm(serve.EntryThm(env, nat_div_mod.Division)))
	registry.InstallLibraryDep(env, nat_div_mod.Division.Entry(), division)
	thm, _ := entry.Build.Fn(env)
	require.NotNil(t, thm)
	cert := core.Force(context.Background(), core.AsThm(thm))
	require.False(t, cert.IsZero(), "forcing the definition's theorem must yield a kernel cert")
	stmt := entry.Statement().Prop
	require.True(t, cert.Conclusion().AlphaEquals(stmt.Conclusion()),
		"the forced certificate must prove the characterizing statement")
}

// TestFamilyDefineWF_DefaultRulesFollowTheShape is the import half's
// contract in miniature: an entry's Definition shape plus its replayed
// theorem, through proof.DefinitionSimpRules, yield exactly what the
// session `define` installs for the same definition — the WF shape's
// two guarded readings, derived from the forced certificate, never
// re-analyzed from the equation text.
func TestFamilyDefineWF_DefaultRulesFollowTheShape(t *testing.T) {
	fam := registry.NewFamily("zz_define_wf_rules_test", nil)
	entry := fam.Define(registry.DefEntry{
		Name:  "Gcd2Rules",
		Const: "zz_reg_gcd2_rules",
		Type:  "num → num → num",
		Equations: []string{
			"∀m n:num. zz_reg_gcd2_rules(m, n) = COND(n = 0, m, zz_reg_gcd2_rules(n, nat_mod(m, n)))",
		},
		Measure:     "λn:num. n",
		Termination: []proof.Action{proof.By(nat_div_mod.Division.Entry())},
		Deps:        []registry.EntryLike{well_founded.Recursion, well_founded.Measure, nat_div_mod.Division},
	})
	require.Equal(t, proof.DefinitionWF, entry.Definition)

	env := serve.NewSeedEnv()
	env.Scope = proof.NewProofScope(entry.Statement().Key())
	division := core.Force(context.Background(), core.AsThm(serve.EntryThm(env, nat_div_mod.Division)))
	registry.InstallLibraryDep(env, nat_div_mod.Division.Entry(), division)
	thm, _ := entry.Build.Fn(env)
	require.NotNil(t, thm)
	cert := core.Force(context.Background(), core.AsThm(thm))
	require.False(t, cert.IsZero())

	rules, err := proof.DefinitionSimpRules(entry.Definition, cert)
	require.NoError(t, err)
	require.Len(t, rules, 2, "base + step readings, as the session's simp_installed reports")
	for i, r := range rules {
		require.NotNil(t, r.Cert, "reading %d is certified", i)
		require.Zero(t, r.Rule.NumHyps(), "reading %d is hyp-free", i)
		require.False(t, core.Force(context.Background(), core.AsThm(r.Cert)).IsZero(), "reading %d forces from the entry's certificate alone", i)
	}
}
