package engine

import (
	"context"
	"github.com/euc-ai/xugo/library/registry"
	"go/format"
	"regexp"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// TestTranscriptI_Battery is the `inductive:` payload as a literal
// battery — every author move as written, against the real registry
// and corpus: finite's shape re-minted under a fresh name, then the
// parameterized transitive-closure shape.
//
//	I1  define inductive zz_fin over (A → bool) with finite's two rules
//	    → four PROVED sections: Rules, Induct (the weak form), Cases
//	      (the canonical disjunction) and InductStrong (the step carries
//	      the relation); nothing installed
//	I2  add-goal  ∀x:A. zz_fin(insert(x, ∅))
//	I3  cite-node (the Rules section) + by             — the USE
//	I4  emit-section (the use)                         — cites zz_fam.ZzFinRules
//	I5  emit-section (any of the three sections)      — family.DefineInductive, 1:1,
//	    the rules in the author's spelling
//	I6  def_expand zz_fin                              — refused by name
//	I7  define inductive zz_tc(R, x, y): the parameterized shape, two
//	    premises; Cases reads as closure.TransitiveClosureCases; emit carries Params
//
// Names are zz-prefixed (the A-battery convention): the mint is
// process-global and permanent for the test process.
func TestTranscriptI_Battery(t *testing.T) {

	env := testEnv()
	env.ProofService = &proof.ProofService{
		LoadConstMeta:        registry.GetConstMetaManager().LoadConstMeta,
		LoadOrStoreConstMeta: registry.GetConstMetaManager().LoadOrStoreConstMeta,
		Syntax:               registry.GetConstMetaManager(),
		RangeConstMeta: func(yield func(core.ConstTermMeta) bool) {
			registry.GetConstMetaManager().Range(yield)
		},
		CNFStore: proof.NewMemoryCNFStore(),
	}
	env.LibraryThms = serve.InductionPrinciples()
	serve.RegisterAll(env)
	serve.InstallProofPolicy()
	installTestNatBundle()
	e := newEngine(env)
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)

	apply := func(goalID, tacticType string, tac *TacticReq) *StepResult {
		t.Helper()
		req := TacticReq{Type: tacticType}
		if tac != nil {
			req = *tac
			req.Type = tacticType
		}
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: req})
		require.NoError(t, err, "apply %s on %s", tacticType, goalID)
		require.True(t, res.Success, "apply %s on %s: %+v", tacticType, goalID, res.Diagnostics)
		return res
	}
	addGoal := func(text string) string {
		t.Helper()
		parsed := dsl.ParsePropTextInScope(text, &dsl.ParseScope{
			ConstResolver:      envConstResolver(s.env),
			StrictResolution:   true,
			FreshenMetaLetters: true,
		})
		require.Empty(t, parsed.Errors, "add-goal %q", text)
		s.mu.Lock()
		defer s.mu.Unlock()
		return s.AddGoal(parsed.Prop)
	}
	states := func(root *proof.GoalStackNode, text string) {
		t.Helper()
		parsed := dsl.ParsePropTextInScope(text, &dsl.ParseScope{
			ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
		})
		require.Empty(t, parsed.Errors, "%s", text)
		require.True(t, root.Goal.AlphaEquals(parsed.Prop), "states %s, want %s",
			ext.PrintTerm(root.Goal.Conclusion()), text)
	}

	// The door refuses a premise outside the first charter, by name.
	_, err = e.Define(&DefineRequest{SessionID: info.ID, Inductive: &DefineInductive{
		Name: "zz_fin_bad", Type: "(A → bool) → bool",
		Rules: []string{"∀s:(A → bool). (∃x:A. zz_fin_bad(insert(x, s))) ⇒ zz_fin_bad(s)"},
	}})
	require.Error(t, err)
	require.Contains(t, err.Error(), "outside it")

	// I1 — finite's shape under a fresh name.
	defRes, err := e.Define(&DefineRequest{SessionID: info.ID, Inductive: &DefineInductive{
		Name: "zz_fin", Type: "(A → bool) → bool",
		Rules: []string{
			"zz_fin(∅)",
			"∀x:A. ∀s:(A → bool). zz_fin(s) ⇒ zz_fin(insert(x, s))",
		},
	}})
	require.NoError(t, err)
	require.Equal(t, "inductive", defRes.Shape)
	require.Equal(t, "inductive_definition", defRes.Schema)
	require.Equal(t,
		[]string{"zz_fin_rules", "zz_fin_induction", "zz_fin_cases", "zz_fin_induction_strong"},
		defRes.Derived)
	require.Zero(t, defRes.SimpInstalled, "an inductive definition installs nothing")
	require.Len(t, defRes.DerivedSections, 4)
	for _, sec := range defRes.DerivedSections {
		root := s.sections[sec.Section].root
		require.True(t, root.Proved(), "I1: the %s section is proved on return", sec.Kind)
		require.Empty(t, root.Children(), "I1: the %s composite opens no child", sec.Kind)
	}
	rulesRoot := s.sections[defRes.DerivedSections[0].Section].root
	inductRoot := s.sections[defRes.DerivedSections[1].Section].root
	casesRoot := s.sections[defRes.DerivedSections[2].Section].root
	states(rulesRoot, "zz_fin⟨A:A⟩(∅⟨A:A⟩) ∧ (∀x:A. ∀s:(A → bool). zz_fin(s) ⇒ zz_fin(insert(x, s)))")
	states(inductRoot, "∀P:((A → bool) → bool). ∀t:(A → bool). P(∅⟨A:A⟩) ∧ (∀x:A. ∀s:(A → bool). P(s) ⇒ P(insert(x, s))) ∧ zz_fin(t) ⇒ P(t)")
	states(casesRoot, "∀s:(A → bool). zz_fin(s) ⇔ s = ∅ ∨ (∃x:A. ∃t:(A → bool). s = insert(x, t) ∧ zz_fin(t))")
	states(s.sections[defRes.DerivedSections[3].Section].root,
		"∀P:((A → bool) → bool). ∀t:(A → bool). P(∅⟨A:A⟩) ∧ (∀x:A. ∀s:(A → bool). zz_fin(s) ∧ P(s) ⇒ P(insert(x, s))) ∧ zz_fin(t) ⇒ P(t)")

	// A second mint of the same name is refused.
	_, err = e.Define(&DefineRequest{SessionID: info.ID, Inductive: &DefineInductive{
		Name: "zz_fin", Type: "(A → bool) → bool", Rules: []string{"zz_fin(∅)"},
	}})
	require.Error(t, err)

	// I2/I3 — a USE: a singleton is finite, from the rules.
	use := addGoal("∀x:A. zz_fin(insert(x, ∅))")
	useSection := len(s.sections) - 1
	cited := apply(use, "cite-node", &TacticReq{NodeID: defRes.DerivedSections[0].GoalID})
	require.Len(t, cited.Produced, 1)
	h0 := 0
	require.Equal(t, "close", apply(cited.Produced[0].GoalID, "by", &TacticReq{
		ByHyps: []ByHypSpec{{HypIndex: &h0}},
	}).Effect, "I3: the singleton is finite by the two rules")

	// I4 — the use member cites the Rules entry by its future name.
	useEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: useSection,
		FuncName: "Build_ZzFinSingleton", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted use member:\n%s", useEmit.Go)
	require.Contains(t, useEmit.Go, "ZzFinRules")
	require.NotContains(t, useEmit.Go, "DefineInductiveStep")
	require.NotContains(t, useEmit.Go, "TODO")
	_, uerr := format.Source([]byte(useEmit.Go))
	require.NoError(t, uerr, "the emitted use member must be well-formed Go")

	// I5 — emit: any of the three sections renders as the ONE
	// family.DefineInductive call, the rules in the author's spelling.
	defEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: defRes.DerivedSections[1].Section,
		FuncName: "ZzFinDef", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted inductive definition:\n%s", defEmit.Go)
	require.Contains(t, defEmit.Go, "var ZzFinDef = family.DefineInductive(registry.InductiveEntry{")
	require.Contains(t, defEmit.Go, `Name: "ZzFinDef",`)
	require.Contains(t, defEmit.Go, `Const: "zz_fin",`)
	require.Contains(t, defEmit.Go, `Type:  "(A → bool) → bool",`)
	require.Contains(t, defEmit.Go, `"zz_fin(∅)",`)
	require.Contains(t, defEmit.Go, `"∀x:A. ∀s:(A → bool). zz_fin(s) ⇒ zz_fin(insert(x, s))",`)
	require.NotContains(t, defEmit.Go, "Params:")
	require.NotContains(t, defEmit.Go, "TODO")
	// The literal spells the key of each entry it registers: the derived
	// section's own normalized key, under the entry's field.
	require.Contains(t, defEmit.Go, "Keys: registry.InductiveKeys{")
	for i, field := range []string{"Rules", "Induct", "Cases", "InductStrong"} {
		normalized, _ := prop.Normalize(s.sections[defRes.DerivedSections[i].Section].root.Goal)
		require.Regexp(t, field+`:\s+"`+regexp.QuoteMeta(string(normalized.AlphaKey()))+`",`, defEmit.Go,
			"the %s entry's key", field)
	}
	_, ferr := format.Source([]byte(defEmit.Go))
	require.NoError(t, ferr, "the emitted file must be well-formed Go")
	for _, sec := range defRes.DerivedSections {
		other, err := e.EmitSection(&EmitSectionRequest{
			SessionID: info.ID, Section: sec.Section,
			FuncName: "ZzFinDef", Family: "zz_fam", IncludePrior: []int{},
		})
		require.NoError(t, err)
		require.Equal(t, defEmit.Go, other.Go, "the %s section renders the same call", sec.Kind)
	}

	// I6 — the closure form is not a proof surface.
	probe := addGoal("∀s:(A → bool). zz_fin(s) ⇒ zz_fin(s)")
	refused, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: probe,
		Tactic: TacticReq{Type: "def_expand", Const: "zz_fin"}})
	require.NoError(t, err)
	require.False(t, refused.Success, "I6: the closure form is refused")
	require.NotEmpty(t, refused.Diagnostics)
	require.Contains(t, refused.Diagnostics[0].Message, "not a proof surface")
	require.Contains(t, refused.Diagnostics[0].Message, "zz_fin")
	require.NotContains(t, refused.Diagnostics[0].Message, "zz_fin_induction",
		"the refusal must not name a principle the registry does not hold")

	// I7 — the parameterized shape: transitive closure.
	tcRes, err := e.Define(&DefineRequest{SessionID: info.ID, Inductive: &DefineInductive{
		Name: "zz_tc", Type: "(A → A → bool) → A → A → bool", Params: []string{"R"},
		Rules: []string{
			"∀x y:A. R(x, y) ⇒ zz_tc(R, x, y)",
			"∀x y z:A. zz_tc(R, x, y) ∧ zz_tc(R, y, z) ⇒ zz_tc(R, x, z)",
		},
	}})
	require.NoError(t, err)
	require.Len(t, tcRes.DerivedSections, 4)
	states(s.sections[tcRes.DerivedSections[1].Section].root,
		"∀R:(A → A → bool). ∀P:(A → A → bool). ∀a b:A. (∀x y:A. R(x, y) ⇒ P(x, y)) ∧ (∀x y z:A. P(x, y) ∧ P(y, z) ⇒ P(x, z)) ∧ zz_tc(R, a, b) ⇒ P(a, b)")
	states(s.sections[tcRes.DerivedSections[2].Section].root,
		"∀R:(A → A → bool). ∀a b:A. zz_tc(R, a, b) ⇔ R(a, b) ∨ (∃y:A. zz_tc(R, a, y) ∧ zz_tc(R, y, b))")
	tcEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: tcRes.DerivedSections[0].Section,
		FuncName: "ZzTcDef", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted parameterized definition:\n%s", tcEmit.Go)
	require.Contains(t, tcEmit.Go, `Params: []string{"R"},`)
	require.Contains(t, tcEmit.Go, `"∀x y z:A. zz_tc(R, x, y) ∧ zz_tc(R, y, z) ⇒ zz_tc(R, x, z)",`)
	_, terr := format.Source([]byte(tcEmit.Go))
	require.NoError(t, terr)
}
