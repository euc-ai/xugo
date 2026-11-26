package engine

import (
	"context"
	"github.com/euc-ai/xugo/library/registry"
	"go/format"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// TestTranscriptT_Battery is the `typedef:` payload as a literal
// battery — every author move as written, against the real registry
// and corpus: a de novo subset type of the naturals, the positive
// ones.
//
//	T1  add-goal  ∃n:num. 0 < n          — the inhabitation, proved FIRST
//	    witness 1; arith
//	T2  define typedef zz_pos_t = {n:num | 0 < n} with mk/dest
//	    → two PROVED sections: Retraction ∀a. mk(dest(a)) = a and
//	      Membership ∀r. 0 < r ⇔ dest(mk(r)) = r; nothing installed
//	T3  add-goal  ∀p:zz_pos_t. 0 < zz_dest_pos_t(p)
//	T4  cite-node ×2 (the two facts) + by      — the USE
//	T5  emit-section (a typedef section)      — family.DefineType, 1:1,
//	    Existence naming the inhabitation's future entry
//	T6  emit-section (the inhabitation)       — an ordinary member
//	T7  define typedef zz_unit_t = {b:bool | b = b}  — the normalizer
//	    decides the inhabitation: no goal first, no Existence rendered
//
// Names are zz-prefixed (the A-battery convention): the mint is
// process-global and permanent for the test process.
func TestTranscriptT_Battery(t *testing.T) {

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

	// The door refuses a type whose inhabitation is not yet a proved
	// section, naming the statement to prove.
	_, err = e.Define(&DefineRequest{SessionID: info.ID, Typedef: &DefineTypedef{
		Type: "zz_pos_t", Abs: "zz_mk_pos_t", Rep: "zz_dest_pos_t", Pred: "λn:num. 0 < n",
	}})
	require.Error(t, err)
	require.Contains(t, err.Error(), "is not a proved section")

	// T1 — the inhabitation, as an ordinary goal.
	inhabited := addGoal("∃n:num. 0 < n")
	w := apply(inhabited, "witness", &TacticReq{Const: "1"})
	require.Len(t, w.Produced, 1)
	require.Equal(t, "close", apply(w.Produced[0].GoalID, "arith", nil).Effect, "T1 closes")
	inhabitedSection := len(s.sections) - 1
	require.True(t, s.sections[inhabitedSection].root.Proved())

	// T2 — the type: the door finds T1 by its statement.
	defRes, err := e.Define(&DefineRequest{SessionID: info.ID, Typedef: &DefineTypedef{
		Type: "zz_pos_t", Abs: "zz_mk_pos_t", Rep: "zz_dest_pos_t", Pred: "λn:num. 0 < n",
	}})
	require.NoError(t, err)
	require.Equal(t, "typedef", defRes.Shape)
	require.Equal(t, "type_definition", defRes.Schema)
	require.Equal(t, "zz_pos_t", defRes.TypeDefined)
	require.Equal(t, []string{"zz_mk_pos_t", "zz_dest_pos_t"}, defRes.Consts)
	require.Zero(t, defRes.SimpInstalled, "a type definition installs nothing")
	require.Len(t, defRes.DerivedSections, 2)
	require.Equal(t, "Retraction", defRes.DerivedSections[0].Kind)
	require.Equal(t, "Membership", defRes.DerivedSections[1].Kind)
	for _, sec := range defRes.DerivedSections {
		require.True(t, s.sections[sec.Section].root.Proved(),
			"T2: the %s section is proved on return", sec.Kind)
	}
	retraction := s.sections[defRes.DerivedSections[0].Section].root
	membership := s.sections[defRes.DerivedSections[1].Section].root
	states := func(root *proof.GoalStackNode, text string) {
		t.Helper()
		parsed := dsl.ParsePropTextInScope(text, &dsl.ParseScope{
			ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
		})
		require.Empty(t, parsed.Errors, "%s", text)
		require.True(t, root.Goal.AlphaEquals(parsed.Prop), "states %s, want %s",
			ext.PrintTerm(root.Goal.Conclusion()), text)
	}
	states(retraction, "∀a:zz_pos_t. zz_mk_pos_t(zz_dest_pos_t(a)) = a")
	states(membership, "∀r:num. 0 < r ⇔ zz_dest_pos_t(zz_mk_pos_t(r)) = r")
	// The composite's inhabitation child was closed by T1's theorem —
	// one child under each section's root.
	require.Len(t, retraction.Children(), 1, "the Retraction composite cites the inhabitation")
	require.Len(t, membership.Children(), 1, "the Membership composite cites the inhabitation")

	// A second mint of the same type name is refused.
	_, err = e.Define(&DefineRequest{SessionID: info.ID, Typedef: &DefineTypedef{
		Type: "zz_pos_t", Abs: "zz_mk_pos_t2", Rep: "zz_dest_pos_t2", Pred: "λn:num. 0 < n",
	}})
	require.Error(t, err)
	require.Contains(t, err.Error(), "already in use")

	// T3/T4 — a USE of the type: every positive's representative is
	// positive, from the two facts.
	use := addGoal("∀p:zz_pos_t. 0 < zz_dest_pos_t(p)")
	useSection := len(s.sections) - 1
	citedM := apply(use, "cite-node", &TacticReq{NodeID: defRes.DerivedSections[1].GoalID})
	require.Len(t, citedM.Produced, 1)
	citedR := apply(citedM.Produced[0].GoalID, "cite-node", &TacticReq{NodeID: defRes.DerivedSections[0].GoalID})
	require.Len(t, citedR.Produced, 1)
	h0, h1 := 0, 1
	require.Equal(t, "close", apply(citedR.Produced[0].GoalID, "by", &TacticReq{
		ByHyps: []ByHypSpec{{HypIndex: &h0}, {HypIndex: &h1}},
	}).Effect, "T4: the representative is positive")
	// The cites of the two facts record known-theorem leaves, not the
	// composite: the use member emits citing the type's entries.
	useEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: useSection,
		FuncName: "Build_ZzPosTRepPositive", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted use member:\n%s", useEmit.Go)
	require.Contains(t, useEmit.Go, "ZzPosTMembership")
	require.Contains(t, useEmit.Go, "ZzPosTRetraction")
	require.NotContains(t, useEmit.Go, "DefineTypeStep")
	require.NotContains(t, useEmit.Go, "TODO")
	_, uerr := format.Source([]byte(useEmit.Go))
	require.NoError(t, uerr, "the emitted use member must be well-formed Go")

	// T5 — emit: either typedef section renders as the ONE
	// family.DefineType call, the inhabitation named as its future
	// entry.
	defEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: defRes.DerivedSections[1].Section,
		FuncName: "ZzPosTDef", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted typedef:\n%s", defEmit.Go)
	require.Contains(t, defEmit.Go, "var ZzPosTDef = family.DefineType(registry.TypeEntry{")
	require.Contains(t, defEmit.Go, `Name:      "ZzPosT",`)
	require.Contains(t, defEmit.Go, `Type:      "zz_pos_t",`)
	require.Contains(t, defEmit.Go, `Abs:       "zz_mk_pos_t",`)
	require.Contains(t, defEmit.Go, `Rep:       "zz_dest_pos_t",`)
	require.Contains(t, defEmit.Go, `Pred:      "λn:num. 0 < n",`)
	require.Contains(t, defEmit.Go, "Existence: ZzPosTInhabited,",
		"the inhabitation names its future sibling entry")
	require.NotContains(t, defEmit.Go, "Witness:")
	require.NotContains(t, defEmit.Go, "TODO")
	_, ferr := format.Source([]byte(defEmit.Go))
	require.NoError(t, ferr, "the emitted file must be well-formed Go")
	retractionEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: defRes.DerivedSections[0].Section,
		FuncName: "ZzPosTDef", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	require.Equal(t, defEmit.Go, retractionEmit.Go, "both sections render the same call")

	// T6 — the inhabitation emits as an ordinary member under the
	// name the typedef's Existence field expects.
	inhEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: inhabitedSection,
		FuncName: "Build_ZzPosTInhabited", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	require.Contains(t, inhEmit.Go, "family.Add(registry.ProofEntry{")
	require.Contains(t, inhEmit.Go, `Name: "ZzPosTInhabited",`)

	// T7 — a trivially inhabited shape: no goal first, no Existence.
	unitRes, err := e.Define(&DefineRequest{SessionID: info.ID, Typedef: &DefineTypedef{
		Type: "zz_unit_t", Abs: "zz_mk_unit_t", Rep: "zz_dest_unit_t", Pred: "λb:bool. b = b",
	}})
	require.NoError(t, err)
	require.Len(t, unitRes.DerivedSections, 2)
	for _, sec := range unitRes.DerivedSections {
		root := s.sections[sec.Section].root
		require.True(t, root.Proved())
		require.Empty(t, root.Children(), "a trivial inhabitation opens no child")
	}
	unitEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: unitRes.DerivedSections[0].Section,
		FuncName: "ZzUnitTDef", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted trivial typedef:\n%s", unitEmit.Go)
	require.Contains(t, unitEmit.Go, `Pred: "λb:bool. b ⇔ b",`, "the predicate renders in the round-trip printer's canonical form")
	require.NotContains(t, unitEmit.Go, "Existence:")
	require.NotContains(t, unitEmit.Go, "Deps:")
	// A witness for a trivial shape is refused.
	_, err = e.Define(&DefineRequest{SessionID: info.ID, Typedef: &DefineTypedef{
		Type: "zz_unit_t2", Abs: "zz_mk_unit_t2", Rep: "zz_dest_unit_t2", Pred: "λb:bool. b = b",
		Witness: "⊤",
	}})
	require.Error(t, err)
	require.Contains(t, err.Error(), "holds by normalization")
}
