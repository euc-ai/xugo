package proof

import (
	"strings"
	"testing"
	"time"
	"unicode/utf8"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// TestByStep_RecordsOneCompositeWithPayload: a macro By close records
// ONE `by` ministep whose proto payload carries the CALL — premise
// list (resident flag, stated-order witnesses), shaping, closer — and
// whose children are exactly the named premises' claim obligations.
// This is the wire contract emit renders from and the session `by`
// dispatch records through; a change in the recorded shape shows up
// here before it shows up as an emit-section regression.
func TestByStep_RecordsOneCompositeWithPayload(t *testing.T) {
	// The witnessed premise must be one whose install neither absorbs the
	// goal nor forward-chains to it — otherwise the tuple is never
	// applied and By refuses the spelling (the unapplied-witnesses
	// contract). The configuration is
	// TestUnpack_NamedTheorem's, empirically inert at install: the nested
	// implication resident, the R1 instance resident, and the diagonal
	// fact ∀x. S(x,x) grounded at the witness — the install's one-step MP
	// cannot chain through both antecedents, so the grounding is
	// genuinely load-bearing.
	e := makeSpineTestEnv()
	x, y := Var("x", TypeInd), Var("y", TypeInd)
	allS := core.TestThm(ext.ForAll(x)(e.S.Apply(x, x)))
	imp := ext.ForAll(x)(e.R1.Apply(x).Imply(ext.ForAll(y)(e.S.Apply(x, y).Imply(e.Qb))))
	a := Var("a", TypeInd)

	goal := prop.MakeProp(e.Qb.Core(), imp.Core(), e.R1.Apply(a).Core())
	sec := e.ctx.Section(goal)
	sec.Do(Derive(func(arg *Argument) {
		hImp := arg.Hyp(imp.Core())
		hR1 := arg.Hyp(e.R1.Apply(a).Core())
		arg.Show("the diagonal at a walks the nested implication", By(Normalized, hImp, hR1, At(MakeFact(allS), a)))
	}))
	require.True(t, sec.Proved())

	// Locate the recorded composite.
	var byNode *GoalStackNode
	var walk func(n *GoalStackNode)
	walk = func(n *GoalStackNode) {
		if _, ok := n.miniStep.(_ByStep); ok {
			require.Nil(t, byNode, "exactly one by composite expected")
			byNode = n
		}
		for _, c := range n.children {
			walk(c)
		}
	}
	walk(sec)
	require.NotNil(t, byNode, "the By close must record a `by` composite ministep")

	// Children: the ONE named premise's claim obligation, closed.
	require.Len(t, byNode.Children(), 1)
	require.True(t, byNode.Children()[0].Proved(), "the claim child must be certified by the macro")

	// Wire payload round-trip.
	detailed := sec.DetailedProofProto()
	require.NotNil(t, detailed)
	var byProto *ByProto
	for _, s := range detailed.GetSteps() {
		if bp, ok := s.Step.(*StepProto_By); ok {
			require.Nil(t, byProto, "exactly one by proto expected")
			byProto = bp.By
		}
	}
	require.NotNil(t, byProto)
	require.Len(t, byProto.GetPremises(), 3)
	require.True(t, byProto.GetPremises()[0].GetResident(), "hyp premise records resident")
	require.True(t, byProto.GetPremises()[1].GetResident(), "hyp premise records resident")
	require.False(t, byProto.GetPremises()[2].GetResident())
	require.Len(t, byProto.GetPremises()[2].GetWitnesses(), 1, "stated-order witnesses recorded")
	require.NotNil(t, byProto.GetShape(), "Normalized records a present shape")
	require.False(t, byProto.GetArith())
}

// TestApplyByStep_EngineSurface: the exported engine surface — resolved
// premises in, ONE recorded composite out, claim obligations left open
// for the caller to certify (the session auto-match's job).
func TestApplyByStep_EngineSurface(t *testing.T) {
	// Same inert-at-install configuration as the payload test above —
	// the witnessed ∀-premise must not absorb the goal, or the
	// unapplied-witnesses contract refuses it.
	e := makeSpineTestEnv()
	env := e.ctx.Env
	x, y := Var("x", TypeInd), Var("y", TypeInd)
	a := Var("a", TypeInd)
	allS := ext.ForAll(x)(e.S.Apply(x, x))
	imp := ext.ForAll(x)(e.R1.Apply(x).Imply(ext.ForAll(y)(e.S.Apply(x, y).Imply(e.Qb))))

	goal := prop.MakeProp(e.Qb.Core(), imp.Core(), e.R1.Apply(a).Core())

	n := CreateGoalStack(goal.AsProp())
	ok := ApplyByStep(n, env, t.Context(), BySpec{
		Premises: []ByPremiseSpec{
			{Install: prop.MakeProp(imp.Core()), Resident: true, Describe: "hyp imp"},
			{Install: prop.MakeProp(e.R1.Apply(a).Core()), Resident: true, Describe: "hyp r1"},
			{Install: prop.MakeProp(allS.Core()), Witnesses: []Term{a}, Describe: "the ∀ premise"},
		},
		Shapes: []ByShape{Normalized},
	})
	require.True(t, ok)

	// The composite applied; the residual refuted inside; the claim
	// obligation is the one open leaf, waiting for the caller.
	leaves := n.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(allS.Core().Core()))

	// Certify it the way the session's auto-match would; the whole
	// section closes.
	cert := core.TestThm(allS)
	require.True(t, leaves[0].runStep(_KnownThmStep{strongerGoal: cert}))
	require.True(t, n.Proved())
}

// TestClipRunes_MultiByteBoundary: premise descriptions clip rune-safe.
// The byte-indexed cut this replaced could split a math glyph, and the
// invalid tail then failed the session RPC's strict-UTF-8 marshal —
// the WHOLE response replaced by a transport error, which loop drivers
// misread as a close.
func TestClipRunes_MultiByteBoundary(t *testing.T) {
	long := strings.Repeat("∀x ∈ 𝕌.", 40)
	got := clipRunes(long, 80)
	require.True(t, utf8.ValidString(got))
	require.LessOrEqual(t, len([]rune(got)), 80)
	require.True(t, strings.HasSuffix(got, "…"))

	// At or under the budget: untouched, no ellipsis.
	require.Equal(t, "∀x. p(x)", clipRunes("∀x. p(x)", 80))

	// Every cut position across a glyph-dense string stays valid —
	// the exact boundary was the failing case.
	for max := 2; max < 24; max++ {
		require.True(t, utf8.ValidString(clipRunes("∈∈∈∈∈∈∈∈∈∈∈∈", max)), "max=%d", max)
	}
}

// TestUnmaterializedAfter: the over-specification check names the
// premises after the closing one that never entered the leaf, and
// never a bare resident, which By kept in the leaf before the first
// install — so a resident the closing install's simplification
// consumed is not "unused" for being listed after it, and the two
// orders of `By(law, h)` are one close.
func TestUnmaterializedAfter(t *testing.T) {
	pb := ext.WrapTerm(ext.Var("pb", core.TypeBool()))
	install := byPremise{}
	resident := byPremise{resident: true}
	witnessed := byPremise{resident: true, witnesses: []Term{pb.Core()}}
	derived := byPremise{derivedCert: prop.MakeProp(pb.Core())}
	kept := byPremise{resident: true, kept: true}

	// Install closes, residents after it: nothing to report.
	require.Empty(t, unmaterializedAfter([]byPremise{install, resident, resident}, 0))
	require.Empty(t, unmaterializedAfter([]byPremise{resident, install, kept}, 1))
	// An install, a witnessed resident or a kit premise after the close
	// never entered the leaf.
	require.Equal(t, []int{1}, unmaterializedAfter([]byPremise{install, install}, 0))
	require.Equal(t, []int{1, 2}, unmaterializedAfter([]byPremise{install, witnessed, derived}, 0))
	require.Equal(t, []int{3}, unmaterializedAfter([]byPremise{resident, install, resident, install}, 1))
}

// TestByNothingClearedAdvice: the nothing-was-cleared advice must not
// convert "no hyp was cleared" into "no premise is missing". The clear
// pass only ever sees RESIDENT hyps, so it is silent about lemma
// premises, and on a hyp-free leaf it is vacuous — yet that is exactly
// the leaf shape of a member whose body is one By after a strip. An
// advice claiming a complete premise list there sends the author
// reshaping when a premise is missing.
func TestByNothingClearedAdvice(t *testing.T) {
	hypFree := byNothingClearedAdvice(0)
	withHyps := byNothingClearedAdvice(3)

	// Neither branch may assert the premise list is complete.
	for name, got := range map[string]string{"hyp-free": hypFree, "with-hyps": withHyps} {
		require.NotContains(t, got, "no premise is missing", name)
		// The tail that two independent authors confirmed correct stays.
		require.Contains(t, got, "By(DenotedAs(name, term), …)", name)
		// The refuter runs ground congruence closure, so a ground
		// equation premise is consumed by demodulation — the tail
		// teaches no hand-Rw workaround for it, only the residual
		// ∀-quantified case.
		require.NotContains(t, got, "apply it as a rewrite (f.Rw)", name)
		require.Contains(t, got, "congruence demodulation", name)
	}

	// Hyp-free: no evidence, and the MISSING premise leads.
	require.Contains(t, hypFree, "no ambient hyps")
	require.Contains(t, hypFree, "no evidence either way")
	require.Contains(t, hypFree, "MISSING premise first")
	require.Less(t, strings.Index(hypFree, "MISSING premise"), strings.Index(hypFree, "wrong shape"),
		"a missing premise is the commoner cause on a hyp-free leaf and must be offered first")

	// With hyps, none cleared: the inference is sound but only for
	// RESIDENT facts, and it must say so.
	require.Contains(t, withHyps, "no RESIDENT fact is missing")
	require.Contains(t, withHyps, "LEMMA premises")
	require.NotContains(t, withHyps, "no ambient hyps")
}

// TestByBudgetAdvice: a close that spends its whole search budget was
// CUT OFF, and that dominates both the premise and the shape reading —
// an unfinished search establishes neither. Measured on a rotation-composition proof
// (5084ms and 5236ms against the 5s ceiling) and a second agent's
// `by` with two premises (5006ms): all three printed shape advice, and
// on all three the real repair was a smaller search. The panic itself
// cannot say — _CNFRefute.apply returns nil identically for a deadline
// and for an exhausted space — so the discriminator is wall clock
// against the budget, and the branch must stay measurement-shaped.
func TestByBudgetAdvice(t *testing.T) {
	const budget = 5 * time.Second

	// At and over the ceiling — the observed overshoots.
	for _, elapsed := range []time.Duration{
		5006 * time.Millisecond, 5084 * time.Millisecond, 5236 * time.Millisecond,
	} {
		got := byBudgetAdvice(true, budget, elapsed)
		require.NotEmpty(t, got, "elapsed=%s must be read as a cut-off search", elapsed)
		require.Contains(t, got, "CUT OFF")
		// It must report the measurement, not assert a timeout it cannot see.
		require.Contains(t, got, elapsed.Round(time.Millisecond).String())
		require.Contains(t, got, "5s search budget")
		// And it must not send the author reshaping.
		require.Contains(t, got, "do not reshape")
		require.NotContains(t, got, "By(Normalized")
	}

	// Comfortably under the ceiling: not a budget case, fall through.
	require.Empty(t, byBudgetAdvice(true, budget, 800*time.Millisecond))
	// Boundary: 90% fires, just under does not.
	require.NotEmpty(t, byBudgetAdvice(true, budget, 4500*time.Millisecond))
	require.Empty(t, byBudgetAdvice(true, budget, 4499*time.Millisecond))

	// The budget belongs to the CNF refuter: a non-CNF closer must not
	// be measured against it, and the replay sentinel (<= 0, no live
	// search) is never a budget case however long the call took.
	require.Empty(t, byBudgetAdvice(false, budget, 9*time.Second))
	require.Empty(t, byBudgetAdvice(true, 0, 9*time.Second))
}

// TestApplyByStep_SettacCloser: the settac closer variant — a bare
// (premise-free) by{settac} runs the membership-mode set driver on the
// anchor and closes it, and the recorded payload carries the closer
// choice. The premise-free form is legal for the DRIVER closer, whose
// vocabulary unfolding is its content (BySets, fact.go); By and ByArith
// still require a premise list.
func TestApplyByStep_SettacCloser(t *testing.T) {
	m := makeFullMiniSetTheory()
	env := makeStepTestEnv()
	env.CnfRefuterTimeout = 10 * time.Second

	n := CreateGoalStack(m.unionsInsertGoal())
	require.True(t, ApplyByStep(n, env, t.Context(), BySpec{Settac: true}),
		"bare by{settac} must close a membership-mode goal")
	require.True(t, n.Proved())

	st, ok := n.miniStep.(_ByStep)
	require.True(t, ok, "the close must record a `by` composite ministep")
	require.True(t, st.settac)
	pb := ext.NewPoolBuilder()
	byProto, ok := st.proto(pb).(*StepProto_By)
	require.True(t, ok)
	require.True(t, byProto.By.GetSettac(), "the wire payload must carry the settac closer")
	require.False(t, byProto.By.GetArith())
}

// TestApplyByStep_ArithSettacConflict: the non-default closers are
// mutually exclusive — the constructors set at most one, so a spec
// carrying both is a caller bug and must fail loudly.
func TestApplyByStep_ArithSettacConflict(t *testing.T) {
	m := makeFullMiniSetTheory()
	env := makeStepTestEnv()
	require.PanicsWithValue(t, "By: Arith and Settac are mutually exclusive closers — pick one", func() {
		ApplyByStep(CreateGoalStack(m.unionsInsertGoal()), env, t.Context(), BySpec{Arith: true, Settac: true})
	})
}
