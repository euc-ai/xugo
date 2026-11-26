package registry_test

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// TestFamilyDefineInductiveForced: finite's rule set under a fresh
// name through the chapter door — three entries registered with the
// inductive shapes and no rewrite rules, each forced against the real
// corpus to a kernel certificate of its declared statement; then a
// member citing the Rules entry builds through the harness's dep
// preload, and the closure form is refused at the Unfold surface.
func TestFamilyDefineInductiveForced(t *testing.T) {
	serve.InstallNatBundle()
	fam := registry.NewFamily("zz_define_inductive_test", nil)
	ie := fam.DefineInductive(registry.InductiveEntry{
		Name:  "Fin",
		Const: "zz_reg_fin",
		Type:  "(A → bool) → bool",
		Rules: []string{
			"zz_reg_fin(∅)",
			"∀x:A. ∀s:(A → bool). zz_reg_fin(s) ⇒ zz_reg_fin(insert(x, s))",
		},
		Deps: []registry.EntryLike{set_basic.EmptySetDef, set_basic.InsertDef},
	})
	require.NotNil(t, ie.Rules)
	require.NotNil(t, ie.Induct)
	require.NotNil(t, ie.Cases)
	require.Equal(t, "zz_define_inductive_test.FinRules", ie.Rules.Name)
	require.Equal(t, "zz_define_inductive_test.FinInduct", ie.Induct.Name)
	require.Equal(t, "zz_define_inductive_test.FinCases", ie.Cases.Name)
	require.Equal(t, proof.DefinitionInductiveRules, ie.Rules.Definition)
	require.Equal(t, proof.DefinitionInductiveInduct, ie.Induct.Definition)
	require.Equal(t, proof.DefinitionInductiveCases, ie.Cases.Definition)
	require.Equal(t, ie.Rules, ie.Entry(proof.InductiveRules))
	for _, entry := range []*registry.ProofEntry{ie.Rules, ie.Induct, ie.Cases} {
		require.Contains(t, entry.DepEntries(), set_basic.EmptySetDef.Entry())
		require.Contains(t, entry.DepEntries(), set_basic.InsertDef.Entry())
		rules, err := proof.DefinitionSimpRules(entry.Definition, core.TestThm(entry.Statement().Prop.Conclusion()))
		require.NoError(t, err)
		require.Empty(t, rules, "%s installs no rewrite rule", entry.Name)
	}

	// Force every entry against the real corpus.
	ctx := context.Background()
	for _, entry := range []*registry.ProofEntry{ie.Rules, ie.Induct, ie.Cases} {
		env := serve.NewSeedEnv()
		env.Scope = proof.NewProofScope(entry.Statement().Key())
		thm, _ := entry.Build.Fn(env)
		require.NotNil(t, thm, "%s builds", entry.Name)
		cert := core.Force(ctx, core.AsThm(thm))
		require.False(t, cert.IsZero(), "%s forces to a kernel cert", entry.Name)
		require.True(t, cert.AlphaEquals(entry.Statement().Prop),
			"%s's forced certificate proves the declared statement", entry.Name)
	}

	// A member citing the Rules entry: the singleton is finite by the
	// two rules.
	singleton := fam.Add(registry.ProofEntry{
		Name: "FinSingleton",
		Build: fam.Theorem("∀x:A. zz_reg_fin(insert(x, ∅))", func(a *proof.Argument, x proof.Term) {
			a.Show("the empty set is finite and one insertion keeps it so",
				proof.By(ie.Rules))
		}),
	})
	env := serve.NewSeedEnv()
	registry.InstallLibraryDep(env, ie.Rules, core.TestThm(ie.Rules.Statement().Prop.Conclusion()))
	env.Scope = proof.NewProofScope(singleton.Statement().Key())
	thm, _ := singleton.Build.Fn(env)
	require.NotNil(t, thm, "the use member builds against the preloaded Rules entry")

	// The closure form is not a proof surface.
	require.Panics(t, func() {
		proof.DefExpandStep(ie.Const)
	})
	require.Error(t, proof.InductiveUnfoldRefusal(ie.Const))
}

// TestFamilyDefineInductiveReadsItsKeys: the door registers each entry
// under the key the literal spells for it, whatever the statement's own
// key is — the key gate is what compares the two — and an entry whose
// key is left out registers unminted. A key spelled for the
// strengthened induction of a definition that has none is refused at
// registration.
func TestFamilyDefineInductiveReadsItsKeys(t *testing.T) {
	serve.InstallNatBundle()
	fam := registry.NewFamily("zz_define_inductive_keys_test", nil)
	ie := fam.DefineInductive(registry.InductiveEntry{
		Name:  "Fin",
		Const: "zz_reg_keys_fin",
		Type:  "(A → bool) → bool",
		Rules: []string{
			"zz_reg_keys_fin(∅)",
			"∀x:A. ∀s:(A → bool). zz_reg_keys_fin(s) ⇒ zz_reg_keys_fin(insert(x, s))",
		},
		Deps: []registry.EntryLike{set_basic.EmptySetDef, set_basic.InsertDef},
		Keys: registry.InductiveKeys{
			Rules:        "prop_spelled_for_rules",
			Cases:        "prop_spelled_for_cases",
			InductStrong: "prop_spelled_for_strong",
		},
	})
	require.Equal(t, "prop_spelled_for_rules", ie.Rules.Key)
	require.Equal(t, "prop_spelled_for_cases", ie.Cases.Key)
	require.Equal(t, "prop_spelled_for_strong", ie.InductStrong.Key)
	require.Equal(t, registry.UnmintedKeyPrefix+ie.Induct.Name, ie.Induct.Key,
		"the entry whose key the literal leaves out registers unminted")
	require.NotEqual(t, ie.Rules.Key, string(ie.Rules.Statement().Key()),
		"the door did not replace the spelled key by the statement's own")

	require.PanicsWithValue(t,
		"registry.DefineInductive(Base): Keys spells InductStrong, and no rule has a premise to strengthen: "+
			"the definition registers no BaseInductStrong entry — drop the key",
		func() {
			fam.DefineInductive(registry.InductiveEntry{
				Name:  "Base",
				Const: "zz_reg_keys_base",
				Type:  "(A → bool) → bool",
				Rules: []string{"zz_reg_keys_base(∅)"},
				Deps:  []registry.EntryLike{set_basic.EmptySetDef},
				Keys:  registry.InductiveKeys{InductStrong: "prop_spelled_for_nothing"},
			})
		})
}
