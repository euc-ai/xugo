package engine

import (
	"context"
	"fmt"
	"os"
	"sync"
	"testing"
	"time"

	"github.com/euc-ai/xugo/library/registry"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestMain installs, for the whole engine test binary, the canonical
// proof-policy table and the record normal form — the analogue of the
// startup installs cmd/xugo does in initEngine before its engine, and
// of the replay harnesses' own TestMains.
//
// The policy table belongs here rather than in the individual tests
// because the missing-table failure is SILENT: with no table a
// target's scope applies the raw foundation alone, so a test asserting
// "this target must NOT use arith" on an indirectly-denied key passes
// for the wrong reason when the table is absent. A per-test opt-in
// that is forgotten therefore does not fail — it quietly voids the
// assertion.
//
// The record normal form belongs here because a bundle install
// installs it too, so without it a test would read instances one way
// or the other by the tests run before it. The readings tests build
// their index after this install, using the same normal form.
//
// The tests run under tactic.HoldStrongerCloses: every step one of
// them builds has its reconstruction run on children closed by
// contradiction and on children closed from no hypothesis, as well as
// on children closed at their conclusions, and a refusal fails the
// binary even where the engine's dispatch recovered it into an answer.
//
// They run under holdFaults for the same reason: a panic inside a
// command comes back as a failed move, so a test that asserts a move is
// refused passes on a closer that panicked. A fault met outside a test
// that expects one (expectFaults) fails the binary.
func TestMain(m *testing.M) {
	serve.InstallProofPolicy()
	serve.InstallRecordNormal()
	code := holdFaults(func() int { return tactic.HoldStrongerCloses(m.Run) })
	if code == 0 {
		if err := replayEmittedBatch(); err != nil {
			fmt.Fprintln(os.Stderr, err)
			code = 1
		}
	}
	os.Exit(code)
}

// faultWatch is what holdFaults keeps: how many running tests expect a
// fault, and each fault filed while none did.
var faultWatch struct {
	sync.Mutex
	expecting  int
	unexpected []string
}

// holdFaults runs run, the test binary's m.Run, with every engine fault
// observed, and returns its exit code — not 0 where a fault was filed
// outside a test that called expectFaults, each one printed.
func holdFaults(run func() int) int {
	faultObserver = func(record *FaultRecord) {
		faultWatch.Lock()
		defer faultWatch.Unlock()
		if faultWatch.expecting == 0 {
			faultWatch.unexpected = append(faultWatch.unexpected,
				fmt.Sprintf("%s in %s at %s: %s", record.ID, record.Command, record.Site, record.Panic))
		}
	}
	code := run()
	faultWatch.Lock()
	defer faultWatch.Unlock()
	if len(faultWatch.unexpected) == 0 {
		return code
	}
	fmt.Fprintf(os.Stderr, "%d engine fault(s) met by a test that expects none — a panic the engine answered as a failed move; "+
		"the stack of each is in the output of the test that met it:\n", len(faultWatch.unexpected))
	for _, fault := range faultWatch.unexpected {
		fmt.Fprintln(os.Stderr, "  "+fault)
	}
	if code == 0 {
		code = 1
	}
	return code
}

// expectFaults marks t as a test that provokes engine faults: the ones
// filed until it ends are its own.
func expectFaults(t *testing.T) {
	t.Helper()
	faultWatch.Lock()
	faultWatch.expecting++
	faultWatch.Unlock()
	t.Cleanup(func() {
		faultWatch.Lock()
		faultWatch.expecting--
		faultWatch.Unlock()
	})
}

func testEnv() *proof.ProverEnv {
	var cnfCache utils.Map[core.TermKey, core.Prop]
	return &proof.ProverEnv{
		ProofService:          proof.MockConstMetaService(),
		CnfRefuterTimeout:     2 * time.Second,
		CnfNormalizationCache: &cnfCache,
		CnfNormalizeCache:     proof.NewCNFNormalizeCache(),
	}
}

func TestCreateCloseSession(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	assert.NotEmpty(t, info.ID)

	err = e.CloseSession(ctx, info.ID)
	require.NoError(t, err)

	// Double close should fail.
	err = e.CloseSession(ctx, info.ID)
	assert.Error(t, err)
}

// ---------------------------------------------------------------------------
// Stateless checks: CheckDerivation
// ---------------------------------------------------------------------------

func TestCheckDerivation_Tautology(t *testing.T) {
	// p ⇒ p is a tautology, needs no premises.
	e := newEngine(testEnv())
	ctx := context.Background()

	p := ext.Var("p", core.TypeBool())
	// Goal: ⊢ p ⇒ p
	goal := prop.MakeProp(p.Imply(p))

	res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
		Conclusion: goal,
		TimeoutMs:  2000,
	})
	require.NoError(t, err)
	assert.Equal(t, ResultValid, res.Result, "p ⇒ p should be provable as tautology")
}

func TestCheckDerivation_WithPremise(t *testing.T) {
	// p, p ⇒ q ⊢ q (modus ponens)
	e := newEngine(testEnv())
	ctx := context.Background()

	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())

	premise := prop.MakeProp(p.Imply(q), p) // p ⊢ p ⇒ q
	goal := prop.MakeProp(q, p)             // p ⊢ q

	res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
		Premises:   []core.Prop{premise},
		Conclusion: goal,
		TimeoutMs:  2000,
	})
	require.NoError(t, err)
	require.NotNil(t, res)
	assert.Equal(t, ResultValid, res.Result, "the premise proves q under hypothesis p")
}

// A search cut short by the context is no evidence of invalidity, even
// on a propositional goal where a finished search would be.
func TestCheckDerivation_CancelledIsUnknown(t *testing.T) {
	e := newEngine(testEnv())
	ctx, cancel := context.WithCancel(t.Context())
	cancel()

	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())

	res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
		Conclusion: prop.MakeProp(q, p), // p ⊢ q
		TimeoutMs:  2000,
	})
	require.NoError(t, err)
	assert.Equal(t, ResultUnknown, res.Result)
	require.NotNil(t, res.CapabilityHint)
	assert.Equal(t, "timeout", res.CapabilityHint.Reason)
}

// ---------------------------------------------------------------------------
// Stateless checks: CheckConsistency
// ---------------------------------------------------------------------------

func TestCheckConsistency_Consistent(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())

	res, err := e.CheckConsistency(ctx, &CheckConsistencyRequest{
		Statements: []core.Prop{
			prop.MakeProp(p),          // ⊢ p
			prop.MakeProp(q),          // ⊢ q
			prop.MakeProp(p.Imply(q)), // ⊢ p ⇒ q
		},
		TimeoutMs: 2000,
	})
	require.NoError(t, err)
	assert.Equal(t, ConsistencyConsistent, res.Result, "p, q and p ⇒ q hold together")
}

func TestCheckConsistency_Contradictory(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	p := ext.Var("p", core.TypeBool())

	res, err := e.CheckConsistency(ctx, &CheckConsistencyRequest{
		Statements: []core.Prop{
			prop.MakeProp(p),          // ⊢ p
			prop.MakeProp(ext.Not(p)), // ⊢ ¬p
		},
		TimeoutMs: 2000,
	})
	require.NoError(t, err)
	assert.Equal(t, ConsistencyInconsistent, res.Result, "p and ¬p are contradictory")
	assert.NotEmpty(t, res.ConflictSubset)
}

// The conflict is the statements the refutation used; a statement it did
// not need stays out.
func TestCheckConsistency_ConflictSubsetIsWhatTheRefutationUsed(t *testing.T) {
	e := newEngine(testEnv())

	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	r := ext.Var("r", core.TypeBool())

	res, err := e.CheckConsistency(t.Context(), &CheckConsistencyRequest{
		Statements: []core.Prop{
			prop.MakeProp(p.Imply(q)),          // 0
			prop.MakeProp(r),                   // 1 — unused
			prop.MakeProp(p.Imply(ext.Not(q))), // 2
			prop.MakeProp(p),                   // 3
			prop.MakeProp(q.Imply(r)),          // 4 — unused
		},
		TimeoutMs: 2000,
	})
	require.NoError(t, err)
	assert.Equal(t, ConsistencyInconsistent, res.Result)
	assert.Equal(t, []int{0, 2, 3}, res.ConflictSubset)
}

// A search cut short by the context is no evidence of consistency, even
// on a propositional set where a finished search would be.
func TestCheckConsistency_CancelledIsUnknown(t *testing.T) {
	e := newEngine(testEnv())
	ctx, cancel := context.WithCancel(t.Context())
	cancel()

	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())

	res, err := e.CheckConsistency(ctx, &CheckConsistencyRequest{
		Statements: []core.Prop{prop.MakeProp(p), prop.MakeProp(q)},
		TimeoutMs:  2000,
	})
	require.NoError(t, err)
	assert.Equal(t, ConsistencyUnknown, res.Result)
	require.NotNil(t, res.CapabilityHint)
	assert.Equal(t, "timeout", res.CapabilityHint.Reason)
}

// ---------------------------------------------------------------------------
// Session: workflow
// ---------------------------------------------------------------------------

func TestSession_AddGoalAndInspect(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, _ := e.getSession(info.ID)

	p := ext.Var("p", core.TypeBool())
	goal := prop.MakeProp(p.Imply(p))
	goalID := s.AddGoal(goal)
	assert.NotEmpty(t, goalID)

	state, err := e.InspectState(ctx, info.ID)
	require.NoError(t, err)
	assert.Equal(t, 1, state.NumOpen)
	assert.False(t, state.Complete)
}

func TestSession_ApplyStep(t *testing.T) {
	env := testEnv()
	e := newEngine(env)
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, _ := e.getSession(info.ID)

	// Add a tautology goal: ⊢ p ⇒ p
	p := ext.Var("p", core.TypeBool())
	goal := prop.MakeProp(p.Imply(p))
	goalID := s.AddGoal(goal)

	// Apply AutoExpand — should close it.
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "auto"},
	})
	require.NoError(t, err)
	assert.True(t, res.Success)
	assert.NotNil(t, res.State)
	assert.True(t, res.State.Complete, "tautology should be closed by AutoExpand")
}

func TestSession_ApplyStep_Failure(t *testing.T) {
	env := testEnv()
	e := newEngine(env)
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, _ := e.getSession(info.ID)

	// Add a goal that can't be proved: ⊢ p
	p := ext.Var("p", core.TypeBool())
	goalID := s.AddGoal(prop.MakeProp(p))

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "auto"},
	})
	require.NoError(t, err)
	assert.False(t, res.Success)
	assert.NotEmpty(t, res.Diagnostics)
	assert.Equal(t, DiagTacticFailure, res.Diagnostics[0].Type)
}

// TestParsePropTextInGoalScope_BareFreeVarResolvesType: a bare session
// free-var (n) in text-DSL resolves to its goal type (num) without an
// explicit `n:num ⊢ …` declaration prefix. The scope-blind
// dsl.ParsePropText leaves n as a fresh type variable, which is what the
// prefix is for.
func TestParsePropTextInGoalScope_BareFreeVarResolvesType(t *testing.T) {
	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))
	n := ext.Var("n", numType)
	goal := prop.MakeProp(core.Eq(n, n)) // ⊢ n = n  (n free, type num)

	claim, err := parsePropTextInGoalScope("n = n", goal, nil)
	require.NoError(t, err)
	frees := claim.Conclusion().Frees(nil)
	require.Len(t, frees, 1)
	assert.Equal(t, "n", string(frees[0].Name()))
	assert.True(t, frees[0].Type().Equals(numType),
		"bare n must resolve to the goal's num type, got %s", frees[0].Type())

	// Contrast: the scope-blind parse cannot type the bare n at all — it
	// errors demanding the `n : <type>` declaration. That error is exactly
	// what forced the `n_0:num ⊢ …` prefix the fix removes.
	scopeless := dsl.ParsePropText("n = n")
	require.NotEmpty(t, scopeless.Errors,
		"scope-blind parse must reject a bare untyped free-var n")
	assert.Contains(t, scopeless.Errors[0].Message, "no type declaration")
}

// TestParsePropTextInGoalScope_ConstantLettersAreItsOwn: a lemma text
// over its own type variable A may hold a constant at an instance
// containing that A — composition's letters are A, B, C, and `g ∘ f`
// here is at (num → A) for each — at the lemma-text door as at the
// claim door, and both read what the statement door reads. A door
// reading the letters as declared refuses the text (`arg type … does
// not match domain …`), and the text a proved section is cited by
// (its statement_typed) would be refused as a premise.
func TestParsePropTextInGoalScope_ConstantLettersAreItsOwn(t *testing.T) {
	const text = "∀f:((num → var:A) → (num → var:A)).∀g:((num → var:A) → (num → var:A)).(g ∘ f = g ∘ f)"
	goal := parseEMatchGoal(t, "∀n:num. n = n")
	statement := dsl.ParsePropTextInScope(text, StatementDoorScope(nil))
	require.Empty(t, statement.Errors)
	lemma, err := parsePropTextInGoalScope(text, goal, nil)
	require.NoError(t, err, "the lemma-text door reads the text")
	claim, err := parseClaimTextInGoalScope(text, goal, nil)
	require.NoError(t, err, "the claim door reads the text")
	assert.Equal(t, statement.Prop.AlphaKey(), lemma.AlphaKey())
	assert.Equal(t, statement.Prop.AlphaKey(), claim.AlphaKey())
	e, _, sessionID := ematchSessionWithGoal(t, "∀n:num. n = n")
	preview, err := e.ParsePropInGoalScope(sessionID, "", text)
	require.NoError(t, err)
	require.Empty(t, preview.Errors, "the session preview reads what the doors read")
	assert.Equal(t, statement.Prop.AlphaKey(), preview.Prop.AlphaKey())
}

// TestApplyStep_AssertClaimText_BareFreeVar is the end-to-end counterpart:
// an `assert` whose claim arrives as raw ClaimText naming a bare session
// free-var (n) parses and applies against the live goal, splitting it into
// the claim subgoal and the continuation. Exercises the full wire→engine
// ClaimText path, not just the parser helper.
func TestApplyStep_AssertClaimText_BareFreeVar(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))
	n := ext.Var("n", numType)
	sucMeta := core.MakeConstMeta("suc", core.MakeFun(numType, numType))
	suc := core.MakeConstTerm(sucMeta, core.MakeFun(numType, numType))
	sucN := ext.Apply(suc, n)
	// Goal: ⊢ suc n = suc n  (n free, type num). assert(n = n) is a genuine
	// sub-claim (≠ conclusion), so it splits the goal in two.
	goalID := s.AddGoal(prop.MakeProp(core.Eq(sucN, sucN)))

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "assert", ClaimText: "n = n"},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "assert with ClaimText naming a bare num free-var should succeed")
	assert.Equal(t, 2, res.State.NumOpen, "assert splits into the claim subgoal and the continuation")
}

// TestApplyStep_RepairHintsMatchExplore: a failed tactic's repair hints
// are the moves that apply to the goal (collectRecommendations), not one
// "try expanding <const>" line per definable constant whether or not the
// expansion applies, and the tactic that just failed is never among them.
func TestApplyStep_RepairHintsMatchExplore(t *testing.T) {
	env := testEnv()
	e := newEngine(env)
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	// Goal: ⊢ p ⇒ p — `expand` decomposes it to ⊢ p ⊢ p and closes it.
	// `known` is the failing tactic: it is cheap and fails cleanly when
	// nothing is cached.
	p := ext.Var("p", core.TypeBool())
	s, _ := e.getSession(info.ID)
	goal := prop.MakeProp(p.Imply(p))
	goalID := s.AddGoal(goal)

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "known"},
	})
	require.NoError(t, err)
	require.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	hints := res.Diagnostics[0].RepairHints

	// The hints name the move that applies: `expand` closes `p ⇒ p` in
	// one step.
	joined := ""
	for _, h := range hints {
		joined += h.Description + "\n"
	}
	assert.Contains(t, joined, "try expand (",
		"hints should surface the expand recommendation on `p ⇒ p`, got: %s", joined)

	// The tactic that just failed is filtered out: had `expand` been the
	// one that failed, its recommendation would not come back as a hint.
	for _, h := range recommendationsToHints(e.collectRecommendations(ctx, goal, 10), "expand", 5) {
		assert.NotContains(t, h.Description, "try expand (",
			"hints should not suggest retrying the failed tactic (`expand`): %q", h.Description)
	}
}

// TestProbe_AutoCloses verifies the probe-as-fast-oracle path: probing
// {auto} on a tautology must report success/effect=close without
// modifying the session. Probe is the cheap "what would happen?" check
// that the agent can hammer dozens of times per round.
func TestProbe_AutoCloses(t *testing.T) {
	env := testEnv()
	e := newEngine(env)
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, _ := e.getSession(info.ID)
	p := ext.Var("p", core.TypeBool())
	goalID := s.AddGoal(prop.MakeProp(p.Imply(p)))

	res, err := e.Probe(ctx, info.ID, &ProbeRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "auto"},
	})
	require.NoError(t, err)
	assert.Equal(t, ProbeSuccess, res.Outcome)
	assert.Equal(t, "close", res.Effect)
	// Session must NOT have been mutated by the probe.
	state := s.buildStateView()
	assert.Equal(t, 1, state.NumOpen, "probe must not mutate session state")
}

// TestRetrieve_AmbiguousGoalRejected ensures the same "explicit goal_id
// when ≥2 are open" rule that explore had now lives on retrieve(by
// goal). The agent juggling multiple subgoals must be forced to specify
// which one it cares about.
func TestRetrieve_AmbiguousGoalRejected(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	_ = s.AddGoal(prop.MakeProp(p.Imply(p)))
	_ = s.AddGoal(prop.MakeProp(q.Imply(q)))

	_, err = e.Retrieve(ctx, info.ID, &RetrieveRequest{Mode: RetrieveByGoal})
	require.Error(t, err, "retrieve(goal) without goal_id must error when multiple goals are open")
	assert.Contains(t, err.Error(), "goal_id")
}

// TestInspect_StructuralFactsForFocusedGoal pins the augmented inspect
// shape: passing a goal_id (or having exactly one open goal) populates
// structural_facts with applicable moves; ambiguity yields an empty list.
func TestInspect_StructuralFactsForFocusedGoal(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))
	target := prop.MakeProp(ext.ForAll(x)(P.Apply(x).Imply(Q.Apply(x))))

	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(target)

	res, err := e.Inspect(ctx, info.ID, &InspectRequest{})
	require.NoError(t, err)
	assert.Equal(t, goalID, res.FocusedGoalID, "single-goal session focuses implicitly")
	kinds := make([]string, 0, len(res.StructuralFacts))
	for _, f := range res.StructuralFacts {
		kinds = append(kinds, f.Kind)
	}
	assert.Contains(t, kinds, "strip_quant",
		"strip_quant must appear as a structural fact on ∀-headed goals; got %v", kinds)
}

func TestSession_BatchApply_FirstSuccess(t *testing.T) {
	env := testEnv()
	e := newEngine(env)
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, _ := e.getSession(info.ID)

	// Use a non-trivial goal: ⊢ (p ∧ q) ⇒ p
	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	goalID := s.AddGoal(prop.MakeProp(p.And(q).Imply(p)))

	// BatchApply: two identical AutoExpand actions — first should win.
	res, err := e.BatchApply(ctx, info.ID, &BatchApplyRequest{
		GoalID:  goalID,
		Tactics: []TacticReq{{Type: "auto"}, {Type: "auto"}},
		Mode:    FirstSuccess,
	})
	require.NoError(t, err)
	assert.Equal(t, 0, res.WinnerIndex, "first action should win")
	assert.True(t, res.Results[0].Success)
	// The second action is never tried: it would succeed as the first did.
	assert.False(t, res.Results[1].Success, "FirstSuccess stops at the winner")
}

// ---------------------------------------------------------------------------
// Clone & Fork Tests
// ---------------------------------------------------------------------------

func TestClone_Independence(t *testing.T) {
	// Cloning a goal tree produces an independent copy: expanding a leaf in
	// the clone does not affect the original.
	p := ext.Var("p", core.TypeBool())
	root := proof.CreateGoalStack(prop.MakeProp(p.Imply(p)))

	clone := root.Clone()

	// Expand clone.
	env := testEnv()
	plan, ok := proof.TryExpandPlan(clone, env.AutoExpand())
	require.True(t, ok)
	clone.Commit(plan)

	// Original should still be unexpanded (1 unsolved leaf = itself).
	assert.Equal(t, 1, root.NumUnsolvedLeaves(), "original must not be affected by clone mutation")
	// Clone should be proved.
	assert.False(t, clone.ProvedThm().IsZero(), "clone should be proved after commit")
}

// TestClone_ProvedSubtreeSharing: a clone copies the open part of the
// tree, wraps each proved child for its parent pointer and shares
// everything under it.
func TestClone_ProvedSubtreeSharing(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// p, q, r ⊢ (p ∧ q) ∧ r: the left conjunct is split again and both
	// its leaves closed, the right one stays open.
	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	r := ext.Var("r", core.TypeBool())
	goalID := s.AddGoal(prop.MakeProp(p.And(q).And(r), p, q, r))
	step := func(goalID, tactic string) *StepResult {
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: tactic}})
		require.NoError(t, err)
		require.True(t, res.Success, "%s on %s: %+v", tactic, goalID, res.Diagnostics)
		return res
	}
	outer := step(goalID, "split_conj")
	require.Len(t, outer.Produced, 2)
	inner := step(outer.Produced[0].GoalID, "split_conj")
	require.Len(t, inner.Produced, 2)
	for _, leaf := range inner.Produced {
		step(leaf.GoalID, "auto")
	}

	root := s.sections[0].root
	require.False(t, root.Proved(), "⊢ r is open")
	clone := root.Clone()
	shared := 0
	var walk func(node, copied *proof.GoalStackNode)
	walk = func(node, copied *proof.GoalStackNode) {
		for i, child := range node.Children() {
			childCopy := copied.Child(i)
			assert.NotSame(t, child, childCopy, "the clone has a node of its own at each child of an open node")
			if !child.Proved() {
				walk(child, childCopy)
				continue
			}
			if len(child.Children()) > 0 {
				assert.Same(t, child.Children()[0], childCopy.Children()[0], "the subtree under a proved child is shared")
				shared++
			}
		}
	}
	walk(root, clone)
	require.Positive(t, shared, "the tree holds a proved child with children of its own")
}

// TestNodePath_NodeAt_Roundtrip: the path of an open leaf under the
// root reaches the leaf's copy in a clone.
func TestNodePath_NodeAt_Roundtrip(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	goalID := s.AddGoal(prop.MakeProp(p.And(q)))
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "split_conj"}})
	require.NoError(t, err)
	require.True(t, res.Success)

	root := s.sections[0].root
	leaves := root.UnsolvedLeaves()
	require.Len(t, leaves, 2, "⊢ p and ⊢ q")
	clone := root.Clone()
	for _, target := range leaves {
		path := root.NodePath(target)
		require.NotNil(t, path, "the leaf is under the root")
		found := clone.NodeAt(path)
		assert.NotSame(t, target, found, "an open leaf is copied")
		assert.True(t, found.Goal.AlphaEquals(target.Goal), "the path reaches the same goal in the clone")
	}
}

// TestCheckpoint_PreservesIntermediateState: a checkpoint taken between
// two steps restores to that state — the split made and its two leaves
// open — and to neither the goal as added nor the finished proof.
func TestCheckpoint_PreservesIntermediateState(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	goalID := s.AddGoal(prop.MakeProp(p.And(q), p, q))
	split, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "split_conj"}})
	require.NoError(t, err)
	require.True(t, split.Success)
	require.Equal(t, 2, split.State.NumOpen)

	cpID, err := e.Checkpoint(ctx, info.ID, "partial")
	require.NoError(t, err)

	for _, g := range split.State.Goals {
		closed, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: g.ID, Tactic: TacticReq{Type: "auto"}})
		require.NoError(t, err)
		require.True(t, closed.Success, "auto closes %s", g.ID)
	}
	finished, err := e.InspectState(ctx, info.ID)
	require.NoError(t, err)
	require.True(t, finished.Complete)

	require.NoError(t, e.Restore(ctx, info.ID, cpID))
	restored, err := e.InspectState(ctx, info.ID)
	require.NoError(t, err)
	assert.Equal(t, 2, restored.NumOpen, "the two leaves of the split are open again")
	assert.False(t, restored.Complete)
}

func TestCheckpoint_Reusable(t *testing.T) {
	// Restoring from the same checkpoint twice should work.
	env := testEnv()
	e := newEngine(env)
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, _ := e.getSession(info.ID)
	p := ext.Var("p", core.TypeBool())
	s.AddGoal(prop.MakeProp(p.Imply(p)))

	cpID, err := e.Checkpoint(ctx, info.ID, "reusable")
	require.NoError(t, err)

	// Prove, restore, prove, restore.
	for range 2 {
		state, _ := e.InspectState(ctx, info.ID)
		for _, g := range state.Goals {
			e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
				GoalID: g.ID,
				Tactic: TacticReq{Type: "auto"},
			})
		}
		state, _ = e.InspectState(ctx, info.ID)
		assert.True(t, state.Complete)

		err = e.Restore(ctx, info.ID, cpID)
		require.NoError(t, err)
		state, _ = e.InspectState(ctx, info.ID)
		assert.Equal(t, 1, state.NumOpen, "should have 1 open goal after restore")
	}
}

func TestBatchApply_CompareAll(t *testing.T) {
	// CompareAll should return previews for each successful action without
	// mutating the session state.
	env := testEnv()
	e := newEngine(env)
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, _ := e.getSession(info.ID)
	p := ext.Var("p", core.TypeBool())
	goalID := s.AddGoal(prop.MakeProp(p.Imply(p)))

	// Snapshot state before.
	stateBefore, _ := e.InspectState(ctx, info.ID)

	res, err := e.BatchApply(ctx, info.ID, &BatchApplyRequest{
		GoalID:  goalID,
		Tactics: []TacticReq{{Type: "auto"}, {Type: "auto"}},
		Mode:    CompareAll,
	})
	require.NoError(t, err)

	// Both should succeed.
	assert.True(t, res.Results[0].Success)
	assert.True(t, res.Results[1].Success)
	// Each should have a preview state.
	assert.NotNil(t, res.Results[0].State)
	assert.NotNil(t, res.Results[1].State)
	// Each should have a plan ref.
	assert.NotEmpty(t, res.Results[0].PlanRef)
	assert.NotEmpty(t, res.Results[1].PlanRef)

	// Session state should be unchanged.
	stateAfter, _ := e.InspectState(ctx, info.ID)
	assert.Equal(t, stateBefore.NumOpen, stateAfter.NumOpen,
		"CompareAll must not mutate session state")
}

func TestCommitPlan_AppliesWinner(t *testing.T) {
	// After CompareAll, CommitPlan should apply the chosen plan.
	env := testEnv()
	e := newEngine(env)
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, _ := e.getSession(info.ID)
	p := ext.Var("p", core.TypeBool())
	goalID := s.AddGoal(prop.MakeProp(p.Imply(p)))

	res, err := e.BatchApply(ctx, info.ID, &BatchApplyRequest{
		GoalID:  goalID,
		Tactics: []TacticReq{{Type: "auto"}},
		Mode:    CompareAll,
	})
	require.NoError(t, err)
	require.True(t, res.Results[0].Success)

	// Commit the plan.
	commitRes, err := e.CommitPlan(ctx, info.ID, &CommitPlanRequest{
		GoalID:  goalID,
		PlanRef: res.Results[0].PlanRef,
	})
	require.NoError(t, err)
	assert.True(t, commitRes.Success)
	assert.True(t, commitRes.State.Complete, "goal should be proved after commit")
}

func TestCommitPlan_RejectsStalePlan(t *testing.T) {
	// After committing one plan, other plans for the same goal should be rejected.
	env := testEnv()
	e := newEngine(env)
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, _ := e.getSession(info.ID)
	p := ext.Var("p", core.TypeBool())
	goalID := s.AddGoal(prop.MakeProp(p.Imply(p)))

	res, err := e.BatchApply(ctx, info.ID, &BatchApplyRequest{
		GoalID:  goalID,
		Tactics: []TacticReq{{Type: "auto"}, {Type: "auto"}},
		Mode:    CompareAll,
	})
	require.NoError(t, err)

	// Commit the first plan.
	_, err = e.CommitPlan(ctx, info.ID, &CommitPlanRequest{
		GoalID:  goalID,
		PlanRef: res.Results[0].PlanRef,
	})
	require.NoError(t, err)

	// Second plan should be rejected — pending plans cleared after commit.
	_, err = e.CommitPlan(ctx, info.ID, &CommitPlanRequest{
		GoalID:  goalID,
		PlanRef: res.Results[1].PlanRef,
	})
	assert.Error(t, err, "stale plan ref should be rejected")
}

// TestRetrieve_AnswersFromTheCorpus: Retrieve reads the corpus alone —
// a goal no member states or applies to, and no reading, gets no
// groups, and no error.
func TestRetrieve_AnswersFromTheCorpus(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, _ := e.getSession(info.ID)
	// A goal no member states or applies to — and not a tautology, which
	// normalization closes on its own and no member should be credited for.
	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	goalID := s.AddGoal(prop.MakeProp(p.Imply(q)))

	// The readings are walked off the request path; a request before
	// the walk is done reports their group truncated and empty
	// (TestRetrieveReadings_NegativeControl), so the test waits for it.
	registry.Readables()
	res, err := e.Retrieve(ctx, info.ID, &RetrieveRequest{Mode: RetrieveByGoal, GoalID: goalID})
	require.NoError(t, err, "retrieve reads the corpus")
	assert.Empty(t, res.Groups, "nothing in the corpus answers p ⇒ q")
}

// TestRetrieve_RelatedTo_RequiresKey checks the input-validation contract:
// the mode requires a non-empty related_to, mirroring the same discipline
// as consts (non-empty consts list) and name_pattern (non-empty pattern).
func TestRetrieve_RelatedTo_RequiresKey(t *testing.T) {
	env := testEnv()
	e := newEngine(env)
	ctx := context.Background()

	_, err := e.Retrieve(ctx, "", &RetrieveRequest{
		Mode:      RetrieveByRelated,
		RelatedTo: "",
	})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "related_to")
}

// TestRetrieve_RelatedTo_UnknownEntry verifies that a key no entry has
// returns no groups (rather than erroring). Same shape as a name_pattern
// with no matches.
func TestRetrieve_RelatedTo_UnknownEntry(t *testing.T) {
	env := testEnv()
	e := newEngine(env)
	ctx := context.Background()

	res, err := e.Retrieve(ctx, "", &RetrieveRequest{
		Mode:      RetrieveByRelated,
		RelatedTo: "prop_does_not_exist",
	})
	require.NoError(t, err)
	assert.Empty(t, res.Groups,
		"unknown related_to should return zero groups, not error")
}

// --- Ranking Tests ---

func makeRecs() []Recommendation {
	return []Recommendation{
		{Description: "simplify-high-branch", Effect: "simplify", Confidence: 0.8, BranchCount: 3},
		{Description: "close-low-conf", Effect: "close", Confidence: 0.7, BranchCount: 0},
		{Description: "simplify-low-branch", Effect: "simplify", Confidence: 0.6, BranchCount: 1},
		{Description: "close-high-conf", Effect: "close", Confidence: 1.0, BranchCount: 0},
		{Description: "simplify-mid", Effect: "simplify", Confidence: 0.9, BranchCount: 2},
	}
}

func TestRankRecommendations_Order(t *testing.T) {
	recs := makeRecs()
	rankRecommendations(recs)

	// Close actions first, then by branch count asc, then confidence desc.
	assert.Equal(t, "close", recs[0].Effect)
	assert.Equal(t, "close", recs[1].Effect)
	// Among close: higher confidence first.
	assert.Equal(t, "close-high-conf", recs[0].Description)
	assert.Equal(t, "close-low-conf", recs[1].Description)
	// Among simplify: lower branch count first.
	assert.Equal(t, 1, recs[2].BranchCount)
	assert.Equal(t, 2, recs[3].BranchCount)
	assert.Equal(t, 3, recs[4].BranchCount)
}

func TestRankRecommendations_StableSort(t *testing.T) {
	// Two items with same effect, confidence, and branch count
	// should preserve original order (stable sort).
	recs := []Recommendation{
		{Description: "first", Effect: "simplify", Confidence: 0.5, BranchCount: 1},
		{Description: "second", Effect: "simplify", Confidence: 0.5, BranchCount: 1},
	}
	rankRecommendations(recs)
	assert.Equal(t, "first", recs[0].Description)
	assert.Equal(t, "second", recs[1].Description)
}

// --- Helpers for Induction tests ---

func inductionTestEnv() (*proof.ProverEnv, core.ConstTermMeta, core.ConstTermMeta, core.ThmCert) {
	env := testEnv()
	numMetaType := core.MakeMetaType("num", 0)
	numType := core.MakeCompositeType(numMetaType)

	zeroMeta := core.MakeConstMeta("_0", numType)
	sucMeta := core.MakeConstMeta("suc", core.MakeFun(numType, numType))
	env.ProofService.LoadOrStoreConstMeta(zeroMeta)
	env.ProofService.LoadOrStoreConstMeta(sucMeta)

	zero := core.MakeConstTerm(zeroMeta, numType)
	suc := core.MakeConstTerm(sucMeta, core.MakeFun(numType, numType))

	P := ext.Var("P", core.MakeFun(numType, core.TypeBool()))
	n := ext.Var("n", numType)
	Pn := P.Apply(n)
	P0 := P.Apply(zero)
	Psuc := P.Apply(ext.Apply(suc, n))
	step := ext.ForAll(n)(Pn.Imply(Psuc))
	numInductionThm := core.TestThm(ext.ForAll(P)(ext.ForAll(n)(P0.And(step).Imply(Pn))))
	env.LibraryThms = map[string]core.Thm{"num_induction": numInductionThm}
	return env, zeroMeta, sucMeta, numInductionThm
}

// --- ByCaseAction / InductionAction via ApplyStep ---

// TestApplyStep_ByCaseAction_AcceptsBothSubscriptForms: the printer
// renders an internal `m_0` as `m₀` (Unicode), and
// trans/witness/instantiate/lemma.text/assert.text accept the ASCII
// `m_0` form via the text-DSL parser. case_split accepts both, like the
// other parameterized tactics, so there is no per-tactic input
// convention to remember.
func TestApplyStep_ByCaseAction_AcceptsBothSubscriptForms(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	// Goal: COND(m_0, p, q) — the case-split term carries a subscripted
	// name so the printer's Unicode upgrade matters.
	m0 := ext.Var("m_0", core.TypeBool())
	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	goal := prop.MakeProp(ext.Cond(m0, p, q))

	printed := ext.PrintTerm(m0) // "m₀" — the printer's Unicode-subscript form
	require.Equal(t, "m₀", printed,
		"test invariant: printer must Unicode-upgrade the subscript (else this test doesn't exercise the asymmetry)")

	for _, form := range []string{"m₀" /* Unicode */, "m_0" /* ASCII DSL */} {
		form := form
		t.Run("input="+form, func(t *testing.T) {
			info, err := e.CreateSession(ctx)
			require.NoError(t, err)
			s, _ := e.getSession(info.ID)
			goalID := s.AddGoal(goal)

			res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
				GoalID: goalID,
				Tactic: TacticReq{Type: "case_split", Const: form},
			})
			require.NoError(t, err)
			require.True(t, res.Success,
				"case_split must accept both subscript forms; got diagnostics=%+v", res.Diagnostics)
			assert.Equal(t, 2, res.State.NumOpen, "case_split produces 2 branches")
		})
	}
}

// TestApplyStep_ByCaseAction_AcceptsFreshBoolTerm: a case term need not
// appear in the goal. The underlying prover/tactic.ByCaseTactic
// reconstructs via prop.ExcludedMiddle(caseTerm) — sound for any
// well-typed bool — so the engine accepts a fresh discriminant, and this
// test exercises the WLOG idiom on one.
func TestApplyStep_ByCaseAction_AcceptsFreshBoolTerm(t *testing.T) {
	env, zeroMeta, _, _ := inductionTestEnv()
	e := newEngine(env)
	ctx := context.Background()

	numType := zeroMeta.AbsType()
	zero := core.MakeConstTerm(zeroMeta, numType)
	// Goal: m_0:num, n_0:num ⊢ p — p is just a bool placeholder; the
	// case-split term `m_0 = 0` does NOT occur in the conclusion or hyps.
	m0 := ext.Var("m_0", numType)
	n0 := ext.Var("n_0", numType)
	p := ext.Var("p", core.TypeBool())
	goal := prop.MakeProp(p, ext.Var("h_m", numType).Eq(m0), ext.Var("h_n", numType).Eq(n0))

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(goal)

	// case_split on the fresh discriminant `m_0 = 0` (a well-typed bool
	// term whose head equality does NOT appear anywhere in the goal — m_0
	// itself appears only as the RHS of a free-var hyp, not as part of an
	// equality with 0). The conclusion is just the placeholder `p`, and
	// none of the hyps mention `m_0 = 0`.
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "case_split", Const: ext.PrintTerm(m0.Eq(zero))},
	})
	require.NoError(t, err, "case_split with a fresh bool term must not error (it used to fail \"case term not found in goal\")")
	require.True(t, res.Success, "case_split tactic should succeed; diagnostics=%+v", res.Diagnostics)
	assert.Equal(t, 2, res.State.NumOpen, "case_split produces 2 branches (m_0 = 0 / ¬(m_0 = 0))")
	_ = n0 // n_0 declared to widen the goal scope; not directly exercised
}

func TestApplyStep_InductionAction_ProducesTwoBranches(t *testing.T) {
	env, zeroMeta, _, _ := inductionTestEnv()
	e := newEngine(env)
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// Goal: ⊢ ∀n:num. P(n)
	numType := zeroMeta.AbsType()
	P := ext.Var("P", core.MakeFun(numType, core.TypeBool()))
	n := ext.Var("n", numType)
	goal := prop.MakeProp(ext.ForAll(n)(P.Apply(n)))
	goalID := s.AddGoal(goal)

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "induction", Const: string(n.AssertVar().Name())},
	})
	require.NoError(t, err)
	assert.True(t, res.Success, "induction tactic should succeed")
	assert.Equal(t, 2, res.State.NumOpen, "should produce 2 open subgoals (base + step)")
	assert.False(t, res.State.Complete)
}

func TestApplyStep_InductionAction_AfterStripQuantUsesFocusedVar(t *testing.T) {
	env, zeroMeta, _, _ := inductionTestEnv()
	e := newEngine(env)
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	numType := zeroMeta.AbsType()
	P := ext.Var("P", core.MakeFun(numType, core.TypeBool()))
	n := ext.Var("n", numType)
	goalID := s.AddGoal(prop.MakeProp(ext.ForAll(n)(P.Apply(n))))

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "strip_quant"},
	})
	require.NoError(t, err)
	require.True(t, res.Success)
	require.Equal(t, 1, res.State.NumOpen)

	strippedGoal := res.State.Goals[0]
	vars := proof.CollectInductionVars(strippedGoal.Statement, numType)
	require.Len(t, vars, 1)
	res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: strippedGoal.ID,
		Tactic: TacticReq{Type: "induction", Const: string(vars[0].Name())},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "induction should resolve n to the free var introduced by strip_quant; diagnostics=%+v", res.Diagnostics)
	assert.Equal(t, 2, res.State.NumOpen)
}

func TestResolveInduction_RejectsSameNameWrongType(t *testing.T) {
	env, _, _, _ := inductionTestEnv()
	e := newEngine(env)

	// Variable named "n" but of type bool: no induction principle is
	// registered for bool, so the engine refuses cleanly.
	n := ext.Var("n", core.TypeBool())
	_, _, err := e.resolveInduction("n", prop.MakeProp(n))
	require.Error(t, err)
	assert.Contains(t, err.Error(), `has type bool`)
	assert.Contains(t, err.Error(), "no induction principle registered")
}

func TestResolveInductionVar_FreeVarInHyp(t *testing.T) {
	_, zeroMeta, _, _ := inductionTestEnv()
	numType := zeroMeta.AbsType()
	P := ext.Var("P", core.MakeFun(numType, core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(numType, core.TypeBool()))
	n := ext.Var("n", numType).AssertVar()
	goal := prop.MakeProp(P.Apply(n), Q.Apply(n))

	got, err := resolveInductionVar(goal, "n")
	require.NoError(t, err)
	assert.True(t, got.Equals(n))
}

func TestResolveInductionVar_ForAllBound(t *testing.T) {
	_, zeroMeta, _, _ := inductionTestEnv()
	numType := zeroMeta.AbsType()
	P := ext.Var("P", core.MakeFun(numType, core.TypeBool()))
	n := ext.Var("n", numType).AssertVar()
	goal := prop.MakeProp(ext.ForAll(n)(P.Apply(n)))

	got, err := resolveInductionVar(goal, "n")
	require.NoError(t, err)
	assert.True(t, got.Equals(n))
}

func TestResolveInductionVar_MissingName(t *testing.T) {
	_, zeroMeta, _, _ := inductionTestEnv()
	numType := zeroMeta.AbsType()
	P := ext.Var("P", core.MakeFun(numType, core.TypeBool()))
	n := ext.Var("n", numType)
	goal := prop.MakeProp(P.Apply(n))

	_, err := resolveInductionVar(goal, "m")
	require.Error(t, err)
	assert.Contains(t, err.Error(), `induction variable "m" is no variable of the focused goal — free: P, n; bound by the conclusion's leading ∀: none`)
}

func TestResolveInductionVar_RequiresVariableName(t *testing.T) {
	_, err := resolveInductionVar(prop.MakeProp(ext.T), "")
	require.Error(t, err)
	assert.Contains(t, err.Error(), "induction requires a variable name")
}

func TestResolveInductionVar_SubscriptPrintedName(t *testing.T) {
	_, zeroMeta, _, _ := inductionTestEnv()
	numType := zeroMeta.AbsType()
	P := ext.Var("P", core.MakeFun(numType, core.TypeBool()))
	n1 := ext.Var("n_1", numType).AssertVar()
	goal := prop.MakeProp(P.Apply(n1))

	got, err := resolveInductionVar(goal, "n₁")
	require.NoError(t, err)
	assert.True(t, got.Equals(n1))
}

// listInductionTestEnv extends inductionTestEnv with a list_induction
// principle registered in LibraryThms. The element type is fixed at
// TypeA (polymorphic) — the kernel's principle is polymorphic, so
// TermInst handles the monomorphization at apply time.
func listInductionTestEnv() (*proof.ProverEnv, core.HolType) {
	env, _, _, _ := inductionTestEnv()
	listMetaType := core.MakeMetaType("list", 1)
	listType := core.MakeCompositeType(listMetaType, core.TypeA())
	nilMeta := core.MakeConstMeta("nil", listType)
	consMeta := core.MakeConstMeta("cons",
		core.MakeFun(core.TypeA(), core.MakeFun(listType, listType)))
	env.ProofService.LoadOrStoreConstMeta(nilMeta)
	env.ProofService.LoadOrStoreConstMeta(consMeta)
	nilT := core.MakeConstTerm(nilMeta, listType)
	consT := core.MakeConstTerm(consMeta,
		core.MakeFun(core.TypeA(), core.MakeFun(listType, listType)))
	P := ext.Var("P", core.MakeFun(listType, core.TypeBool()))
	l := ext.Var("l", listType)
	h := ext.Var("h", core.TypeA())
	tail := ext.Var("t", listType)
	Pl := P.Apply(l)
	Pnil := P.Apply(nilT)
	Pt := P.Apply(tail)
	Pcons := P.Apply(ext.Apply(consT, h, tail))
	step := ext.ForAll(h)(ext.ForAll(tail)(Pt.Imply(Pcons)))
	listInductThm := core.TestThm(ext.ForAll(P)(ext.ForAll(l)(Pnil.And(step).Imply(Pl))))
	env.LibraryThms["list_induction"] = listInductThm
	return env, listType
}

func TestApplyStep_InductionAction_ListInduct_ProducesTwoBranches(t *testing.T) {
	env, listType := listInductionTestEnv()
	e := newEngine(env)
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// Goal: ⊢ ∀l:(A)list. P(l)
	P := ext.Var("P", core.MakeFun(listType, core.TypeBool()))
	l := ext.Var("l", listType)
	goal := prop.MakeProp(ext.ForAll(l)(P.Apply(l)))
	goalID := s.AddGoal(goal)

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "induction", Const: string(l.AssertVar().Name())},
	})
	require.NoError(t, err)
	require.True(t, res.Success,
		"list induction should succeed once list_induction is loaded; diagnostics=%+v",
		res.Diagnostics)
	assert.Equal(t, 2, res.State.NumOpen,
		"should produce 2 open subgoals (nil base + cons step)")
}

// Regression: list_induction is registered polymorphically (element type A
// is a type variable). When the agent inducts on a concrete `l :
// list(num)`, the engine must type-instantiate A := num before
// analyzing the principle.
func TestApplyStep_InductionAction_ListInduct_PolymorphicSpecialization(t *testing.T) {
	env, _ := listInductionTestEnv()
	e := newEngine(env)
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// Concrete element type: num.
	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))
	listNum := core.MakeCompositeType(core.MakeMetaType("list", 1), numType)
	P := ext.Var("P", core.MakeFun(listNum, core.TypeBool()))
	l := ext.Var("l", listNum)
	goal := prop.MakeProp(ext.ForAll(l)(P.Apply(l)))
	goalID := s.AddGoal(goal)

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "induction", Const: string(l.AssertVar().Name())},
	})
	require.NoError(t, err)
	require.True(t, res.Success,
		"polymorphic list_induction must specialize to list(num); diagnostics=%+v",
		res.Diagnostics)
	assert.Equal(t, 2, res.State.NumOpen)
}

func TestMakeInductionAction_ListVar_WithoutPrincipleReturnsActionableError(t *testing.T) {
	// Same setup as listInductionTestEnv but WITHOUT registering
	// list_induction — the engine should refuse with an error pointing
	// at the missing entry.
	env, _, _, _ := inductionTestEnv()
	listMetaType := core.MakeMetaType("list", 1)
	listType := core.MakeCompositeType(listMetaType, core.TypeA())
	e := newEngine(env)

	P := ext.Var("P", core.MakeFun(listType, core.TypeBool()))
	l := ext.Var("l", listType)
	_, _, err := e.resolveInduction("l", prop.MakeProp(P.Apply(l)))
	require.Error(t, err)
	assert.Contains(t, err.Error(), "list_induction")
}

func TestApplyStep_ByCaseAction_SolveBothBranches(t *testing.T) {
	// case_split leaves two branches, and auto closes each.
	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// Goal: COND(b, p ⇒ p, q ⇒ q)
	// After the split: b ⊢ p ⇒ p and ¬b ⊢ q ⇒ q, both left open.
	b := ext.Var("b", core.TypeBool())
	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	goal := prop.MakeProp(ext.Cond(b, p.Imply(p), q.Imply(q)))
	goalID := s.AddGoal(goal)

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "case_split", Const: ext.PrintTerm(b)},
	})
	require.NoError(t, err)
	require.True(t, res.Success)
	require.Equal(t, 2, res.State.NumOpen)

	for _, g := range res.State.Goals {
		res2, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: g.ID,
			Tactic: TacticReq{Type: "auto"},
		})
		require.NoError(t, err)
		assert.True(t, res2.Success, "auto should close branch %s", g.ID)
	}

	state, err := e.InspectState(ctx, info.ID)
	require.NoError(t, err)
	assert.True(t, state.Complete, "all branches closed → proof complete")
}

// TestProbe_StructuralFail asserts the strong-fail contract for
// structural tactics: probing strip_quant on a non-∀ goal returns
// fail (not unknown).
func TestProbe_StructuralFail(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	p := ext.Var("p", core.TypeBool())
	goalID := s.AddGoal(prop.MakeProp(p))

	res, err := e.Probe(ctx, info.ID, &ProbeRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "strip_quant"},
	})
	require.NoError(t, err)
	assert.Equal(t, ProbeFail, res.Outcome,
		"structural tactic on shape-incompatible goal must return fail (strong negative)")
}

// probeAutoMatchTestProps builds two structurally-distinct propositions
// using the shared num/suc test consts. Bare bool free-vars all
// normalize to ⊥ (and thus collide on AlphaKey) — concrete const heads
// are required for the key match to discriminate.
//
//	matched   = ⊢ 0 = suc(0)            (a proved sibling will state it)
//	unmatched = ⊢ 0 = suc(suc(0))       (no sibling will state it)
//	conj      = ⊢ (0 = suc(0)) ∧ (suc(suc(0)) = 0)
//
// split_conj on conj produces two leaves whose normalized AlphaKeys are
// distinct (verified by the prop.Normalize debug pass — see git history
// of this test for the diagnostic).
func probeAutoMatchTestProps(t *testing.T) (env *proof.ProverEnv, matched, unmatched, conj core.Prop) {
	t.Helper()
	env, zeroMeta, sucMeta, _ := inductionTestEnv()
	numType := zeroMeta.AbsType()
	zero := core.MakeConstTerm(zeroMeta, numType)
	suc := core.MakeConstTerm(sucMeta, core.MakeFun(numType, numType))
	sucZero := ext.Apply(suc, zero)
	sucSucZero := ext.Apply(suc, sucZero)
	zeroW := ext.WrapTerm(zero)
	ssZeroW := ext.WrapTerm(sucSucZero)
	matched = prop.MakeProp(zeroW.Eq(sucZero))
	unmatched = prop.MakeProp(zeroW.Eq(sucSucZero))
	conj = prop.MakeProp(zeroW.Eq(sucZero).And(ssZeroW.Eq(zero)))
	return
}

// probeSiblingSession opens a session whose first sections are the
// given statements, each closed (a white-box stand-in for "the author
// proved it"), and whose last section is conj — the goal the probe
// runs on. Auto-match reads proved siblings, never the library.
func probeSiblingSession(t *testing.T, e *Engine, conj core.Prop, proved ...core.Prop) (*Session, string, string) {
	t.Helper()
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	for _, p := range proved {
		s.AddGoal(p)
		closeSectionTrusted(t, s.sections[len(s.sections)-1].root)
	}
	goalID := s.AddGoal(conj)
	s.rebuildGoalIndex()
	return s, info.ID, goalID
}

// TestProbe_PredictsAutoMatch_BranchToSimplify is the regression test for
// the agent UX issue: a probe that produces multiple leaves where one
// would be silently closed by auto-match must report effect with the
// post-auto-match leaf count AND surface the closed leaf in auto_matched,
// so the agent doesn't have to reverse-engineer "where did the second
// branch go" via follow-up RPCs.
//
// split_conj on the conjunction produces two leaves; only the first is
// a proved sibling section's statement.
func TestProbe_PredictsAutoMatch_BranchToSimplify(t *testing.T) {
	env, matchedProp, _, conjGoal := probeAutoMatchTestProps(t)
	e := newEngine(env)
	ctx := context.Background()
	s, sid, goalID := probeSiblingSession(t, e, conjGoal, matchedProp)

	res, err := e.Probe(ctx, sid, &ProbeRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "split_conj"},
	})
	require.NoError(t, err)
	assert.Equal(t, ProbeSuccess, res.Outcome)
	assert.Equal(t, "simplify", res.Effect,
		"after auto-match closes the matched branch, only the unmatched leaf remains — effect must be simplify, not branch")
	require.Len(t, res.AutoMatched, 1,
		"the matched branch must surface in auto_matched so the agent sees why effect dropped from branch to simplify")
	require.NotNil(t, res.AutoMatched[0].MatchedSection)
	assert.Equal(t, 0, *res.AutoMatched[0].MatchedSection)
	require.Len(t, res.Subgoals, 1, "only the unmatched subgoal should remain in the predicted residual")

	// Probe must not mutate session state.
	assert.Equal(t, 1, s.sections[1].root.NumUnsolvedLeaves(), "probe must not mutate session state even when it predicts auto-match")
}

// TestProbe_PredictsAutoMatch_BranchToClose covers the case where every
// produced leaf is auto-matched: probe must collapse to effect=close and
// surface all matches.
func TestProbe_PredictsAutoMatch_BranchToClose(t *testing.T) {
	env, matchedProp, _, conjGoal := probeAutoMatchTestProps(t)
	// conj = (0 = suc(0)) ∧ (suc(suc(0)) = 0): its second conjunct is
	// its own sibling statement here.
	second := probeConjunct(t, conjGoal, 1)
	e := newEngine(env)
	ctx := context.Background()
	_, sid, goalID := probeSiblingSession(t, e, conjGoal, matchedProp, second)

	res, err := e.Probe(ctx, sid, &ProbeRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "split_conj"},
	})
	require.NoError(t, err)
	assert.Equal(t, ProbeSuccess, res.Outcome)
	assert.Equal(t, "close", res.Effect,
		"both branches auto-matched — effect must collapse to close, matching what apply would commit")
	assert.Len(t, res.Subgoals, 0)
	require.Len(t, res.AutoMatched, 2, "both branches must surface in auto_matched")
}

// probeConjunct returns the i-th conjunct of a binary conjunction as a
// hyp-free prop.
func probeConjunct(t *testing.T, conj core.Prop, i int) core.Prop {
	t.Helper()
	l, r, ok := ext.MatchesAND(conj.Conclusion())
	require.True(t, ok, "fixture: a binary conjunction")
	if i == 0 {
		return prop.MakeProp(l)
	}
	return prop.MakeProp(r)
}

// TestProbe_AutoMatch_NoSessionMutation guards against the scratch-cache
// invariant: probe must not pollute s.autoMatchCache or s.sections, so
// the same probe can be repeated and the actual apply downstream still
// has a clean cache to work with.
func TestProbe_AutoMatch_NoSessionMutation(t *testing.T) {
	env, matchedProp, _, conjGoal := probeAutoMatchTestProps(t)
	e := newEngine(env)
	ctx := context.Background()
	s, sid, goalID := probeSiblingSession(t, e, conjGoal, matchedProp)
	info := struct{ ID string }{sid}

	// Run the same probe twice — second call must give identical results,
	// not "the cache already has this so effect is close" or any other
	// state-leak signal.
	res1, err := e.Probe(ctx, info.ID, &ProbeRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "split_conj"},
	})
	require.NoError(t, err)
	res2, err := e.Probe(ctx, info.ID, &ProbeRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "split_conj"},
	})
	require.NoError(t, err)

	assert.Equal(t, res1.Effect, res2.Effect)
	assert.Equal(t, len(res1.Subgoals), len(res2.Subgoals))
	assert.Equal(t, len(res1.AutoMatched), len(res2.AutoMatched))

	// Section root must still have exactly one unsolved leaf — the
	// original goal — confirming no commit happened.
	assert.Equal(t, 1, s.sections[1].root.NumUnsolvedLeaves(),
		"probe must not commit any tactic to the session")
}

// Original bug covered by this test: auto fails, the engine
// then runs collectRecommendations to build RepairHints; TryInductionTactic on
// the step subgoal invokes InductionTactic's reconstruct callback via
// MakeSubGoals' IsStronger assertion. During reconstruction, num_induction is
// instantiated with predicate λm.concl and beta-reduced — capture-avoiding
// substitution renames inner ∀-bound vars that would otherwise be captured by
// num_induction's step ∀n. MoveConclDisjComponentToHyp was then called
// with the pre-rename h from movedHyps, whose post-ArrangeORChain form in the
// OR chain was α-equal but not Equal, tripping a structural Assert.
//
// Minimal trigger: a goal of shape
//
//	∀n.((m*n) = (n*m)) ⊢ ∀n.((suc(m)*n) = (n + suc(m)))
//
// (m free; hypothesis bound var n colliding with num_induction's step ∀n;
// conclusion is intentionally NOT a ring identity, so the under-binder arith
// decider declines and auto really does fall through to its failure path),
// against which ApplyStep with tactic=auto should (1) fail cleanly — the auto
// pipeline cannot close it without the `*`/suc definitions — and (2) surface
// RepairHints via collectRecommendations without panicking. This exercises the
// exact TryInductionTactic → InductionTactic reconstruct path that was broken.
func TestApplyStep_Auto_RepairHints_CaptureAvoidingRename(t *testing.T) {
	env, zeroMeta, sucMeta, _ := inductionTestEnv()

	// Register the `*` const so DecomposesOR / BasicTactics downstream have a
	// meta for the binop. No def thm is needed — the auto tactic just needs to
	// see the constant; it will fail to close the step goal, which is the path
	// that drives the RepairHints pipeline.
	numType := zeroMeta.AbsType()
	multMeta := core.MakeConstMeta("*", core.MakeFun(numType, numType, numType))
	env.ProofService.LoadOrStoreConstMeta(multMeta)
	mult := core.MakeConstTerm(multMeta, multMeta.AbsType())
	suc := core.MakeConstTerm(sucMeta, sucMeta.AbsType())
	times := func(a, b core.Term) core.Term { return ext.Apply(ext.Apply(mult, a), b) }

	m := ext.Var("m", numType)
	n := ext.Var("n", numType)

	// Goal: ∀n.((m*n) = (n*m)) ⊢ ∀n.((suc(m)*n) = (n + suc(m)))
	// The hyp is the induction hypothesis of commutativity of · after induction on m.
	// Its bound n collides with num_induction's step ∀n, which triggers the
	// capture-avoiding α-rename during emit. The conclusion's equality
	// is deliberately NOT a ring identity: `suc(m)*n` ringnormalizes to `m*n+n`
	// while `n + suc(m)` is `n+m+1` — different polynomials, so the unified
	// arith decider declines the atom and auto really falls into its failure
	// path (the regression check), instead of fabricating a no-bundle TestThm
	// cert from a goal that happened to be a ring identity (which was the
	// original `(suc(m)*n) = (n*suc(m))` shape).
	plusMeta := core.MakeConstMeta("+", core.MakeFun(numType, numType, numType))
	env.ProofService.LoadOrStoreConstMeta(plusMeta)
	plus := core.MakeConstTerm(plusMeta, plusMeta.AbsType())
	add := func(a, b core.Term) core.Term { return ext.Apply(ext.Apply(plus, a), b) }
	hyp := ext.ForAll(n)(ext.Eq(times(m, n), times(n, m)))
	sucM := ext.Apply(suc, m)
	concl := ext.ForAll(n)(ext.Eq(times(sucM, n), add(n.Core(), sucM)))
	stepGoal := prop.MakeProp(concl, hyp)

	e := newEngine(env)
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(stepGoal)

	assert.NotPanics(t, func() {
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: goalID,
			Tactic: TacticReq{Type: "auto"},
		})
		require.NoError(t, err)
		assert.False(t, res.Success,
			"auto is expected to fail on this step goal (no * definition); the "+
				"regression is about the failure path not panicking.")
		assert.NotEmpty(t, res.Diagnostics,
			"failed auto should produce a tactic_failure diagnostic with RepairHints")
	}, "auto on capture-avoiding step goal must not panic in the RepairHints pipeline")
}

// TestResolveTermWithFallback_RegisteredConstNotInGoal pins the
// registered-const fallback: a term-parameter tactic (witness /
// instantiate / trans) may name a registered constant that does NOT
// occur in the goal. The motivating case is the canonical
// pair_recursion witness `λp. PAIR'(fst(p), snd(p))`: fst/snd are registered
// constants but are absent from the goal, so goalConstScope
// (goal-local) leaves them as free variables, and the scope guard alone
// would reject the whole witness.
func TestResolveTermWithFallback_RegisteredConstNotInGoal(t *testing.T) {
	A := core.MakeVarType("A")
	B := core.MakeVarType("B")
	C := core.MakeVarType("C")
	prod := ext.MakeProdType(A, B)

	// Seed fst/snd into the process-global const registry, mimicking a
	// chapter's mint. PAIR' is deliberately NOT a constant — it is a
	// goal-local free variable (the ∀-stripped recursor parameter).
	mgr := registry.GetConstMetaManager()
	mgr.LoadOrStoreConstMeta(core.MakeConstMeta("fst", core.MakeFun(prod, A)))
	mgr.LoadOrStoreConstMeta(core.MakeConstMeta("snd", core.MakeFun(prod, B)))

	pairOp := ext.Var("PAIR'", core.MakeFun(A, core.MakeFun(B, C)))
	a0 := ext.Var("a0", A)
	a1 := ext.Var("a1", B)
	// Goal conclusion mentions PAIR' (and a0/a1) so they are free in the
	// goal; the witness expected type is the recursor's domain→codomain.
	applied := pairOp.Apply(a0.Core()).Apply(a1.Core()) // PAIR'(a0)(a1) : C
	goal := prop.MakeProp(applied.Eq(applied.Core()).Core()).Core()
	expected := core.MakeFun(prod, C)

	e := newEngine(testEnv())

	t.Run("registered_const_resolves", func(t *testing.T) {
		term, err := e.resolveTermWithFallback(
			"λp. PAIR'(fst(p), snd(p))", goal, expected, nil)
		require.NoError(t, err,
			"fst/snd are registered consts not in the goal; the fallback must seed them")
		require.NotNil(t, term)
		assert.True(t, term.Type().Equals(expected),
			"witness must have the recursor domain→codomain type; got %s",
			ext.FormatType(term.Type()))
		// The only free name left must be PAIR' (a genuine goal free);
		// fst/snd must have resolved as constants, not leaked as frees.
		for _, v := range term.Frees(nil) {
			assert.Equal(t, "PAIR'", string(v.Name()),
				"fst/snd must resolve as constants, not free variables")
		}
	})

	t.Run("unknown_name_still_rejected", func(t *testing.T) {
		// A name that is neither goal-local nor a registered const is
		// rejected with the scope-guard error.
		_, err := e.resolveTermWithFallback(
			"λp. PAIR'(NO_SUCH_CONST(p), snd(p))", goal, expected, nil)
		require.Error(t, err)
		assert.Contains(t, err.Error(), "NO_SUCH_CONST",
			"genuinely-unknown name must surface in the unbound-variable error")
	})

	t.Run("goal_var_not_shadowed", func(t *testing.T) {
		// A term using only a goal-local free variable still resolves to
		// that variable — the global fallback must not change this path.
		term, err := e.resolveTermWithFallback("PAIR'", goal,
			core.MakeFun(A, core.MakeFun(B, C)), nil)
		require.NoError(t, err)
		_, isConst := term.AsConst()
		assert.False(t, isConst, "PAIR' is a goal free var, must not become a const")
	})
}

// TestTacticTerm_ConstantLettersAreItsOwn: a tactic's term parameter (a
// `witness`, an `instantiate` or `trans` term) and the `parse-term`
// preview read a polymorphic constant's type letters as the constant's
// own, as the statement, claim and lemma-text doors do. The composite
// `f ∘ e` below needs composition at A := num, B := A, C := B over a
// goal whose own letters are A and B.
func TestTacticTerm_ConstantLettersAreItsOwn(t *testing.T) {
	e, s, sessionID := ematchSessionWithGoal(t,
		"∀f:(A → B). ∀e:(num → A). ∃g:(num → B). ∀x:num. g(x) = f(e(x))")
	ctx := context.Background()
	gid := ematchOpenLeafID(t, s)
	stripped, err := e.ApplyStep(ctx, sessionID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "strip_quant"}})
	require.NoError(t, err)
	require.True(t, stripped.Success, "%+v", stripped.Diagnostics)
	require.Len(t, stripped.Produced, 1)
	leaf := stripped.Produced[0].GoalID

	preview, err := e.ParseTermInGoalScope(sessionID, leaf, "f ∘ e", nil)
	require.NoError(t, err)
	require.Empty(t, preview.Errors, "parse-term reads the composite")

	out, err := e.ApplyStep(ctx, sessionID, &ApplyStepRequest{
		GoalID: leaf, Tactic: TacticReq{Type: "witness", Const: "f ∘ e"},
	})
	require.NoError(t, err)
	require.True(t, out.Success, "the witness door reads what parse-term reads: %+v", out.Diagnostics)
}

// TestAssertClaim_UnpinnedTypeLetterIsRefused: the session's claim door
// refuses what the Go claim door refuses — a polymorphic constant's
// letter no term of the claim fixes — and reads the claim once the
// constant is pinned. An ad-hoc lemma text may be polymorphic and is
// not asked.
func TestAssertClaim_UnpinnedTypeLetterIsRefused(t *testing.T) {
	goal := parseEMatchGoal(t, "∀n:num. n = n")
	_, err := parseClaimTextInGoalScope("∅ = ∅", goal, nil)
	require.Error(t, err)
	assert.Contains(t, err.Error(), "unpinned")
	assert.Contains(t, err.Error(), "⟨A:A⟩")

	_, err = parseClaimTextInGoalScope("∅⟨A:num⟩ = ∅", goal, nil)
	require.NoError(t, err, "pinned where the constant is written")

	_, err = parsePropTextInGoalScope("∅ = ∅", goal, nil)
	require.NoError(t, err, "the lemma-text door states a lemma, which may be polymorphic")
}
