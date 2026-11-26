package engine

import (
	"context"
	"fmt"
	"github.com/euc-ai/xugo/library/registry"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// TestTranscriptA_Battery is the recursive-function transcript as a
// literal battery test — every author move as written, against the
// real registry and the real corpus:
//
//	A1  define sumto (recursive, two equations)
//	A2  add-goal  ∀n. 2·sumto(n) = n·suc(n)
//	A3  induction n
//	A4  simp; arith                     — base focus
//	A5  by — premises: IH; lemmas: left distributivity, commutativity of · — step
//	A6  add-goal  ∀n. n ≤ sumto(n)
//	A7  induction n
//	A8  simp; arith                     — both foci
//	A9  emit-section                    — family.Define + the theorem member
//
// The engine env mirrors initEngine's production wiring (global const
// manager, corpus LibraryThms + RegisterAll, proof policy, omega nat
// bundle).
func TestTranscriptA_Battery(t *testing.T) {

	env := testEnv()
	env.ProofService = &proof.ProofService{
		LoadConstMeta:        registry.GetConstMetaManager().LoadConstMeta,
		LoadOrStoreConstMeta: registry.GetConstMetaManager().LoadOrStoreConstMeta,
		Syntax:               registry.GetConstMetaManager(),
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

	// A1 — define sumto from its two constructor equations.
	defRes, err := e.Define(&DefineRequest{
		SessionID: info.ID,
		Recursive: &DefineRecursive{
			Name: "zz_sumto_a",
			Type: "num → num",
			Equations: []string{
				"zz_sumto_a(0) = 0",
				"∀n:num. zz_sumto_a(suc(n)) = zz_sumto_a(n) + suc(n)",
			},
		},
	})
	require.NoError(t, err)
	require.Equal(t, "recursive", defRes.Shape)
	require.Equal(t, "num_recursion", defRes.Schema)
	require.Contains(t, defRes.Characterizing, "zz_sumto_a")
	require.Equal(t, 2, defRes.SimpInstalled)
	require.True(t, s.sections[defRes.Section].root.Proved(),
		"the recursive definition's section is proved on return: no obligation is left to the author")

	// A2–A3 — the Gauss closed form, induction on n.
	gauss := addGoal("∀n:num. 2 * zz_sumto_a(n) = n * suc(n)")
	ind := apply(gauss, "induction", &TacticReq{Const: "n"})
	require.Len(t, ind.Produced, 2)

	// A4 — base focus: simp fires sumto(0) from the installed set;
	// arith finishes the numeral residual (the A8 idiom on one line).
	base := apply(ind.Produced[0].GoalID, "simp", nil)
	require.Len(t, base.Produced, 1)
	require.True(t, base.Produced[0].Changes.ConclusionChanged, "the installed base equation rewrote the focus")
	closed := apply(base.Produced[0].GoalID, "arith", nil)
	require.Equal(t, "close", closed.Effect, "A4: base focus closes")

	// A5 — step focus: simp fires the suc clause (zero setup), then the
	// transcript's revised three-move close — distribute
	// (simp_with nat_arith.LeftAddDistrib, the member by its registered name),
	// substitute the IH (rw hyp 0), ring (arith). The original
	// bare-cite `by` spelling measured over the CNF ceiling; the
	// revision is recorded in the transcript's post-listing note.
	step := apply(ind.Produced[1].GoalID, "simp", nil)
	require.Len(t, step.Produced, 1)
	require.True(t, step.Produced[0].Changes.ConclusionChanged, "the installed step equation rewrote the focus")
	stepGoalID := step.Produced[0].GoalID
	stepNode := s.goalIndex[stepGoalID].node
	require.Equal(t, 1, stepNode.Goal.NumHyps(), "the step focus carries exactly the IH")
	ih := 0
	distributed := apply(stepGoalID, "simp_with", &TacticReq{
		WithLemmas: []LemmaWithSpec{{Key: "nat_arith.LeftAddDistrib"}}})
	require.Len(t, distributed.Produced, 1)
	substituted := apply(distributed.Produced[0].GoalID, "rw", &TacticReq{HypIndex: &ih})
	require.Len(t, substituted.Produced, 1)
	closedStep := apply(substituted.Produced[0].GoalID, "arith", nil)
	require.Equal(t, "close", closedStep.Effect, "A5: the step focus closes")
	require.True(t, s.sections[1].root.Proved(), "SumtoGauss section proved")

	// A6–A8 — the growth bound, same rhythm, both foci simp; arith.
	le := addGoal("∀n:num. n ≤ zz_sumto_a(n)")
	ind2 := apply(le, "induction", &TacticReq{Const: "n"})
	require.Len(t, ind2.Produced, 2)
	for i, g := range ind2.Produced {
		simped := apply(g.GoalID, "simp", nil)
		require.Len(t, simped.Produced, 1)
		closed := apply(simped.Produced[0].GoalID, "arith", nil)
		require.Equal(t, "close", closed.Effect, "A8: focus %d closes", i)
	}
	for i, sec := range s.sections {
		require.True(t, sec.root.Proved(), "section %d proved at A9", i)
	}

	// A9 — emit: the definition renders 1:1 as family.Define, and the
	// Gauss member renders as a family entry whose simp rule child
	// resolves against the included define section.
	defEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: defRes.Section,
		FuncName: "Build_Sumto", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	require.Contains(t, defEmit.Go, "family.Define(registry.DefEntry{")
	require.Contains(t, defEmit.Go, `Const: "zz_sumto_a"`)
	// Each clause is its own equation string, in the author's text.
	require.Contains(t, defEmit.Go, `"zz_sumto_a(0) = 0"`)
	require.Contains(t, defEmit.Go, `"∀n:num. zz_sumto_a(suc(n)) = zz_sumto_a(n) + suc(n)"`)
	// The entry's Key is the characterizing statement's own, written as
	// a theorem entry's is: registration reads it and computes none.
	require.Contains(t, defEmit.Go,
		fmt.Sprintf("\tKey:   %q,\n", registry.KeyOf(s.sections[defRes.Section].root.Goal)))

	gaussEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: 1,
		FuncName: "Build_SumtoGauss", Family: "zz_fam",
		IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted SumtoGauss member:\n%s", gaussEmit.Go)
	require.Contains(t, gaussEmit.Go, "family.Add(registry.ProofEntry{")
	require.NotContains(t, gaussEmit.Go, "TODO",
		"every leaf must classify — the define-installed rule included")
	// The define entry is a same-family sibling, so the cite is its
	// bare var — the conventional dep name, package-local — never the
	// registered name as a string.
	require.Contains(t, gaussEmit.Go, "ZzSumtoA",
		"the simp rule child cites the define entry by its sibling var")
	require.NotContains(t, gaussEmit.Go, `"zz_fam.ZzSumtoA"`)
}
