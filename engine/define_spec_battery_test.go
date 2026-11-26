package engine

import (
	"context"
	"fmt"
	"github.com/euc-ai/xugo/library/registry"
	"go/format"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// TestTranscriptS_Battery is the definition-by-specification transcript
// as a literal battery test — every author move as written, against the
// real registry and corpus:
//
//	S1  define spec nat_sqrt (one constant, the discrete square root)
//	    → the pointwise existence obligation opens:
//	      ∀n. ∃v. v * v ≤ n ∧ n < suc(v) * suc(v)
//	S2  induction n; base: witness 0 + arith; step: the ∀-closed
//	    advance bridge (assert → intro² → case_split → witness each
//	    case, the squares expanded by nat_arith.MulClauses), then one small `by`
//	    from the IH and the bridge — the author's math
//	    → on close: schema specification, simp_installed 0
//	S3  add-goal  ∀n. nat_sqrt(n) * nat_sqrt(n) ≤ n
//	S4  cite-node (the definition section) + by — the USE cites the
//	    characterizing theorem (no installation, the manual's R4, for
//	    spec: a specification is not a directed rewrite)
//	S5  emit-section                    — family.DefineSpec, 1:1
//
// Env wiring mirrors the D battery.
func TestTranscriptS_Battery(t *testing.T) {

	env := testEnv()
	// In-memory CNF proof store: S2/S4's `by` runs live refutes whose
	// proofs the S5 emit-time capture re-reads (the D battery's wiring;
	// production wires the file-backed session store here).
	env.ProofService = &proof.ProofService{
		LoadConstMeta:        registry.GetConstMetaManager().LoadConstMeta,
		LoadOrStoreConstMeta: registry.GetConstMetaManager().LoadOrStoreConstMeta,
		Syntax:               registry.GetConstMetaManager(),
		CNFStore:             proof.NewMemoryCNFStore(),
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

	// S1 — define nat_sqrt by spec: the specification is the whole
	// payload; the pointwise existence obligation opens for the
	// author. Nothing is installed and nothing is proved yet.
	defRes, err := e.Define(&DefineRequest{
		SessionID: info.ID,
		Spec: &DefineSpec{
			Consts: []SpecConstDecl{{Name: "zz_nat_sqrt_e", Type: "num → num"}},
			Spec: "∀n:num. zz_nat_sqrt_e(n) * zz_nat_sqrt_e(n) ≤ n ∧ " +
				"n < suc(zz_nat_sqrt_e(n)) * suc(zz_nat_sqrt_e(n))",
		},
	})
	require.NoError(t, err)
	require.Equal(t, "spec", defRes.Shape)
	require.Equal(t, "specification", defRes.Schema)
	require.Equal(t, []string{"zz_nat_sqrt_e"}, defRes.Consts)
	require.Zero(t, defRes.SimpInstalled, "no R4 installation for the spec shape")
	require.Contains(t, defRes.Obligation, "∃v_zz_nat_sqrt_e",
		"the obligation quantifies a fresh VALUE binder in the constant's place")
	require.NotEmpty(t, defRes.ObligationGoalID)

	// S2 — the pointwise existence: induction on the point. The base
	// takes witness 0 (0·0 ≤ 0 < 1); the step is one `by` — strict monotonicity
	// of · carries the nonlinear step, transitivity and `suc m ≤ n ⇔ m < n` the linear glue.
	ind := apply(defRes.ObligationGoalID, "induction", &TacticReq{Const: "n"})
	require.Len(t, ind.Produced, 2, "induction: base + step")

	w := apply(ind.Produced[0].GoalID, "witness", &TacticReq{Const: "0"})
	require.Len(t, w.Produced, 1)
	closedBase := apply(w.Produced[0].GoalID, "arith", nil)
	require.Equal(t, "close", closedBase.Effect, "S2 base closes")
	require.Empty(t, closedBase.DefineCompleted, "the step branch is still open")

	// The step decomposes through a ∀-closed bridge (the refuter's
	// premise-economy discipline: one big search walls at the budget;
	// with the one-step advance as its own fact, the resident-∃ IH
	// closes the step by a small resolution).
	stepGoal := ind.Produced[1].GoalID
	bridge := apply(stepGoal, "assert", &TacticReq{
		ClaimText: "∀u:num. u * u ≤ n ∧ n < suc(u) * suc(u) ⇒ " +
			"∃w:num. w * w ≤ suc(n) ∧ suc(n) < suc(w) * suc(w)",
	})
	require.Len(t, bridge.Produced, 2, "assert: claim child + main")
	claimID, mainID := bridge.Produced[0].GoalID, bridge.Produced[1].GoalID

	// The bridge: fix u, split on whether the current square still
	// bounds suc(n).
	fixed := apply(claimID, "intro", nil)
	require.Len(t, fixed.Produced, 1)
	opened := apply(fixed.Produced[0].GoalID, "intro", nil)
	require.Len(t, opened.Produced, 1)
	cased := apply(opened.Produced[0].GoalID, "case_split", &TacticReq{
		Const: "suc(n) < suc(u) * suc(u)",
	})
	require.Len(t, cased.Produced, 2)
	// Still bounded: the same root works; the residual is linear.
	wy := apply(cased.Produced[0].GoalID, "witness", &TacticReq{Const: "u"})
	require.Len(t, wy.Produced, 1)
	require.Equal(t, "close", apply(wy.Produced[0].GoalID, "arith", nil).Effect,
		"bridge, bounded case")
	// Exhausted: advance the root; the nonlinear step is an expansion.
	wn := apply(cased.Produced[1].GoalID, "witness", &TacticReq{Const: "suc(u)"})
	require.Len(t, wn.Produced, 1)
	advanceID := wn.Produced[0].GoalID
	// The nonlinear kernel first, as its own fact (the premise-economy
	// discipline — the one-shot 8-premise refutation walls at the
	// search budget): squaring is monotone across the advance. Both
	// squares expand by the successor clauses of multiplication to
	// u * u plus a linear rest, and arith compares the rests.
	grows := apply(advanceID, "assert", &TacticReq{
		ClaimText: "suc(u) * suc(u) < suc(suc(u)) * suc(suc(u))",
	})
	require.Len(t, grows.Produced, 2)
	expanded := apply(grows.Produced[0].GoalID, "simp_with", &TacticReq{
		WithLemmas: []LemmaWithSpec{{Key: "nat_arith.MulClauses"}},
	})
	require.Len(t, expanded.Produced, 1)
	require.Equal(t, "close", apply(expanded.Produced[0].GoalID, "arith", nil).Effect,
		"the square grows across the advance")
	// What remains is linear in the square atoms; arith reads the
	// resident facts (the case bound, the spec bound, the growth).
	require.Equal(t, "close", apply(grows.Produced[1].GoalID, "arith", nil).Effect,
		"bridge, advance case")

	// Main: the IH and the bridge close by one small refutation.
	m0, m1 := 0, 1
	closedStep := apply(mainID, "by", &TacticReq{
		ByHyps: []ByHypSpec{{HypIndex: &m0}, {HypIndex: &m1}},
	})
	require.Equal(t, "close", closedStep.Effect, "S2 step closes")
	require.Len(t, closedStep.DefineCompleted, 1, "the define completes on this apply")
	done := closedStep.DefineCompleted[0]
	require.Equal(t, "zz_nat_sqrt_e", done.Defined)
	require.Equal(t, []string{"zz_nat_sqrt_e"}, done.Consts)
	require.Equal(t, "specification", done.Schema)
	require.Zero(t, done.SimpInstalled, "no R4 installation for the spec shape")
	require.True(t, s.sections[defRes.Section].root.Proved(), "the definition section is proved")

	// S3–S4 — a USE of the definition: the characterizing theorem is
	// cited (cite-node), not fired from a simp set — the spec shape
	// installs no rewrite rules by ruling.
	use := addGoal("∀n:num. zz_nat_sqrt_e(n) * zz_nat_sqrt_e(n) ≤ n")
	useSection := len(s.sections) - 1
	cited := apply(use, "cite-node", &TacticReq{NodeID: defRes.GoalID})
	require.Len(t, cited.Produced, 1)
	c0 := 0
	require.Equal(t, "close", apply(cited.Produced[0].GoalID, "by", &TacticReq{
		ByHyps: []ByHypSpec{{HypIndex: &c0}},
	}).Effect, "S4: the conjunct follows from the cited characterizing theorem")
	// The cite of a definition records a known-theorem leaf, not the
	// spec composite: the use member emits citing the spec's entry.
	useEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: useSection,
		FuncName: "Build_NatSqrtBelow", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted use member:\n%s", useEmit.Go)
	require.Contains(t, useEmit.Go, "family.Add(registry.ProofEntry{")
	require.Contains(t, useEmit.Go, "ZzNatSqrtE", "the cite names the spec's entry")
	require.NotContains(t, useEmit.Go, "DefineSpecStep")
	require.NotContains(t, useEmit.Go, "TODO")
	_, uerr := format.Source([]byte(useEmit.Go))
	require.NoError(t, uerr, "the emitted use member must be well-formed Go")

	// S5 — emit: the definition renders 1:1 as family.DefineSpec with
	// the specification literal and the existence proof as the entry's
	// own fields.
	defEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: defRes.Section,
		FuncName: "Build_NatSqrt", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted spec define:\n%s", defEmit.Go)
	require.Contains(t, defEmit.Go, "family.DefineSpec(registry.SpecEntry{")
	require.Contains(t, defEmit.Go,
		fmt.Sprintf("\tKey:  %q,\n", registry.KeyOf(s.sections[defRes.Section].root.Goal)),
		"the entry's Key is the characterizing statement's own")
	// The author's type text, as the define RPC received it — not the
	// printer's parenthesized spelling.
	require.Contains(t, defEmit.Go, `{Const: "zz_nat_sqrt_e", Type: "num → num"}`)
	require.Contains(t, defEmit.Go, "ExistenceBody: func(ctx *Script) []Action {")
	require.Contains(t, defEmit.Go, "nat_arith.MulClauses",
		"the existence cites are rendered and declared")
	// The existence cite set is the declared dep set, every dep a typed
	// entry: a session cites nothing a member does not state, so there
	// is no frontier to render.
	require.Contains(t, defEmit.Go, "Deps: []registry.EntryLike{nat_arith.MulClauses}",
		"the existence cite set is the declared dep set")
	require.NotContains(t, defEmit.Go, "TODO", "every leaf classifies")
	_, ferr := format.Source([]byte(defEmit.Go))
	require.NoError(t, ferr, "the emitted file must be well-formed Go")
}
