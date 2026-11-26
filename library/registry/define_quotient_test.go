package registry_test

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	_ "github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/stretchr/testify/require"
)

// The quotient of num by a relation defined as equality: the door's
// mechanics — seven entries, their names and bindings, the class
// notation, the forced derivations — at the simplest relation, the
// equivalence proved by a trusted test theorem (the derivations
// themselves are the proof package's test).
func TestFamilyDefineQuotient(t *testing.T) {
	fam := registry.NewFamily("zz_define_quotient_test", nil)
	fam.Define(registry.DefEntry{
		Name:      "ZzQeqDef",
		Const:     "zz_qeq",
		Type:      "num → num → bool",
		Equations: []string{"∀x y:num. zz_qeq(x, y) ⇔ x = y"},
	})
	equivalence := fam.Add(registry.ProofEntry{
		Name: "ZzQeqEquivalence",
		Build: registry.BuildSpec{Headline: "equivalence(zz_qeq)", Fn: func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
			ctx := proof.NewScript(env)
			return core.TestThm(fam.Entries()[1].Statement().Prop.Conclusion()), &ctx.Proof
		}},
	})

	qe := fam.DefineQuotient(registry.QuotientEntry{
		Name:        "Qnum",
		Type:        "zz_qnum",
		Mk:          "zz_qnum_class",
		Abs:         "zz_qnum_abs",
		Rep:         "zz_qnum_rep",
		Relation:    "zz_qeq",
		Equivalence: equivalence,
	})

	// Registration facts: the seven entries, their names, bindings and
	// shapes; the class map spells ⁅x⁆.
	require.True(t, qe.ClassNotation)
	require.Equal(t, "zz_qnum", string(qe.Meta.Name()))
	require.Equal(t, "zz_define_quotient_test.QnumSurjectivity", qe.Surjectivity.Name)
	require.Equal(t, "zz_define_quotient_test.QnumEq", qe.Eq.Name)
	require.Equal(t, "zz_qnum_induction", qe.Induct.ServesAs)
	require.Equal(t, "zz_qnum_sound", qe.Sound.ServesAs)
	require.Equal(t, "zz_qnum_exact", qe.Exact.ServesAs)
	require.Equal(t, "", qe.Eq.ServesAs)
	// The package reaches each theorem through the handle's field, as the
	// chapter spells it (`RealDef.Eq`): no variable carries the name.
	require.Equal(t, "QnumDef.Eq", qe.Eq.GoRef())
	require.Equal(t, "QnumDef.Induct", qe.Induct.GoRef())
	require.Equal(t, proof.DefinitionQuotientEq, qe.Eq.Definition)
	require.Equal(t, proof.DefinitionQuotientInduct, qe.Induct.Definition)
	for _, k := range proof.QuotientTheoremKinds {
		entry := qe.Entry(k)
		require.NotNil(t, entry, "%v registers", k)
		require.Equal(t, []*registry.ProofEntry{equivalence}, entry.DepEntries(), "%v declares the equivalence", k)
		require.Contains(t, entry.Key, "prop_")
	}
	got, ok := registry.QuotientEntriesFor("zz_qnum")
	require.True(t, ok)
	require.Same(t, qe, got)

	// Eq is a use rule, the principles are not.
	rules, err := proof.DefinitionSimpRules(qe.Eq.Definition, core.TestThm(qe.Eq.Statement().Prop.Conclusion()))
	require.NoError(t, err)
	require.Len(t, rules, 1)
	rules, err = proof.DefinitionSimpRules(qe.Induct.Definition, core.TestThm(qe.Induct.Statement().Prop.Conclusion(), qe.Induct.Statement().Prop.Hyps()...))
	require.NoError(t, err)
	require.Empty(t, rules)

	// The notation: ⁅n⁆ and class(n) both read as the class map.
	mgr := registry.GetConstMetaManager()
	scope := &dsl.ParseScope{
		ConstResolver: func(name string) core.ConstTermMeta {
			if meta, ok := mgr.LoadConstMeta(core.TermName(name)); ok {
				return meta
			}
			return core.ConstTermMeta{}
		},
		Syntax: mgr, TypeResolver: mgr.TypeArity, StrictResolution: true, FreshenMetaLetters: true,
	}
	parse := func(text string) core.Prop {
		res := dsl.ParsePropTextInScope(text, scope)
		require.Empty(t, res.Errors, "%s", text)
		return res.Prop
	}
	longhand := parse("∀n m:num. zz_qnum_class(n) = zz_qnum_class(m) ⇔ zz_qeq(n, m)")
	require.True(t, parse("∀n m:num. ⁅n⁆ = ⁅m⁆ ⇔ zz_qeq(n, m)").AlphaEquals(longhand))
	require.True(t, parse("∀n m:num. class(n) = class(m) ⇔ zz_qeq(n, m)").AlphaEquals(longhand))
	require.True(t, qe.Eq.Statement().Prop.AlphaEquals(longhand), "Eq states class equality as the relation")
	spelled, err := dsl.ChapterSpelling(prop.FormatPropForParser(qe.Eq.Statement().Prop), mgr, nil)
	require.NoError(t, err)
	require.Contains(t, spelled, "⁅x⁆ = ⁅y⁆")

	// The induction principle, as the harness serves it, is in the
	// standard form the analyzer reads.
	{
		env := serve.NewSeedEnv()
		registry.InstallLibraryDep(env, qe.Induct, core.TestThm(
			qe.Induct.Statement().Prop.Conclusion(), qe.Induct.Statement().Prop.Hyps()...))
		thm, ok := env.LookupLibraryThm("zz_qnum_induction")
		require.True(t, ok, "ServesAs binds the principle name")
		tmpl, terr := tactic.AnalyzeInductionPrinciple(thm)
		require.NoError(t, terr)
		require.Len(t, tmpl.Cases, 1)
	}

	// Replay: every entry forced against the equivalence dep, the
	// built theorem α-equal to the statement.
	ctx := context.Background()
	equivalenceCert := core.TestThm(equivalence.Statement().Prop.Conclusion())
	for _, k := range proof.QuotientTheoremKinds {
		entry := qe.Entry(k)
		env := serve.NewSeedEnv()
		registry.InstallLibraryDep(env, equivalence, equivalenceCert)
		env.Scope = proof.NewProofScope(entry.Statement().Key())
		thm, _ := entry.Build.Fn(env)
		require.NotNil(t, thm, "%s builds", entry.Name)
		cert := core.Force(ctx, core.AsThm(thm))
		require.True(t, cert.AlphaEquals(entry.Statement().Prop),
			"%s's forced certificate proves the declared statement:\n  %s", entry.Name, prop.PrintProp(cert))
	}

	// A lift: the first argument's class, stated at the classes with
	// the respectfulness as its Respects proof. The door declares the
	// quotient's Sound and Exact as its deps; forced, the stated rule
	// comes back a kernel certificate.
	first := fam.Define(registry.DefEntry{
		Name:      "ZzQfirstDef",
		Const:     "zz_qfirst",
		Type:      "zz_qnum → zz_qnum → zz_qnum",
		Equations: []string{"∀a b:num. zz_qfirst(⁅a⁆, ⁅b⁆) = ⁅a⁆"},
		Respects:  []proof.Action{proof.CnfRefute()},
	})
	require.Equal(t, proof.DefinitionLift, first.Definition)
	require.ElementsMatch(t, []*registry.ProofEntry{qe.Sound, qe.Exact}, first.DepEntries()[:2],
		"the door declares the quotient's Sound and Exact, ahead of the spelled definers")
	require.True(t, first.Statement().Prop.AlphaEquals(parse("∀a b:num. zz_qfirst(zz_qnum_class(a), zz_qnum_class(b)) = zz_qnum_class(a)")))
	{
		lawCert := func(entry *registry.ProofEntry) core.Thm {
			env := serve.NewSeedEnv()
			registry.InstallLibraryDep(env, equivalence, equivalenceCert)
			env.Scope = proof.NewProofScope(entry.Statement().Key())
			thm, _ := entry.Build.Fn(env)
			return core.Force(ctx, core.AsThm(thm))
		}
		env := serve.NewSeedEnv()
		registry.InstallLibraryDep(env, qe.Sound, lawCert(qe.Sound))
		registry.InstallLibraryDep(env, qe.Exact, lawCert(qe.Exact))
		env.Scope = proof.NewProofScope(first.Statement().Key())
		thm, _ := first.Build.Fn(env)
		require.NotNil(t, thm)
		cert := core.Force(ctx, core.AsThm(thm))
		require.True(t, cert.AlphaEquals(first.Statement().Prop), "the lift's forced certificate proves its stated rule:\n  %s", prop.PrintProp(cert))
	}
	require.Panics(t, func() {
		fam.Define(registry.DefEntry{
			Name: "ZzQnoRespects", Const: "zz_qsecond", Type: "zz_qnum → zz_qnum → zz_qnum",
			Equations: []string{"∀a b:num. zz_qsecond(⁅a⁆, ⁅b⁆) = ⁅b⁆"},
		})
	}, "a lift without Respects is refused")
	require.Panics(t, func() {
		fam.Define(registry.DefEntry{
			Name: "ZzQplainRespects", Const: "zz_qplain", Type: "num → num",
			Equations: []string{"∀a:num. zz_qplain(a) = a"},
			Respects:  []proof.Action{proof.CnfRefute()},
		})
	}, "Respects on a non-lift is refused")

	// A dep proving something else fails the Build loudly.
	{
		wrong := fam.Add(registry.ProofEntry{
			Name: "ZzQeqWrong",
			Build: registry.BuildSpec{Headline: "equivalence(zz_qeq) ∧ ⊤", Fn: func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
				ctx := proof.NewScript(env)
				return core.TestThm(fam.Entries()[len(fam.Entries())-1].Statement().Prop.Conclusion()), &ctx.Proof
			}},
		})
		qe2 := registry.NewFamily("zz_define_quotient_test_wrong", nil).DefineQuotient(registry.QuotientEntry{
			Name: "Qwrong", Type: "zz_qnum_wrong", Mk: "zz_qnum_wrong_class", Abs: "zz_qnum_wrong_abs", Rep: "zz_qnum_wrong_rep",
			Relation: "zz_qeq", Equivalence: wrong,
		})
		// A second quotient over num: the class notation is the first's,
		// and still reads as the first's.
		require.False(t, qe2.ClassNotation)
		require.True(t, parse("∀n:num. ⁅n⁆ = zz_qnum_class(n)").AlphaEquals(parse("∀n:num. zz_qnum_class(n) = zz_qnum_class(n)")))
		env := serve.NewSeedEnv()
		registry.InstallLibraryDep(env, wrong, core.TestThm(wrong.Statement().Prop.Conclusion()))
		env.Scope = proof.NewProofScope(qe2.Eq.Statement().Key())
		require.Panics(t, func() { qe2.Eq.Build.Fn(env) })
	}

	// The mint is exclusive: the class map's name is taken.
	require.Panics(t, func() {
		registry.NewFamily("zz_define_quotient_test_dup", nil).DefineQuotient(registry.QuotientEntry{
			Name: "Again", Type: "zz_qnum2", Mk: "zz_qnum_class", Abs: "zz_qnum2_abs", Rep: "zz_qnum2_rep",
			Relation: "zz_qeq", Equivalence: equivalence,
		})
	})
}
