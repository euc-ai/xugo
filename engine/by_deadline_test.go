package engine

import (
	"context"
	"fmt"
	"strings"
	"testing"
	"time"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/clause"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// byDeadlineGoal adds stmt to a fresh session, strips its ∀-prefix and its
// antecedent, and returns the session and the residual's goal id.
func byDeadlineGoal(t *testing.T, e *Engine, stmt string) (string, string) {
	t.Helper()
	ctx := t.Context()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	parsed := dsl.ParsePropTextInScope(stmt, &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
	})
	require.Empty(t, parsed.Errors, "add-goal %q", stmt)
	s.mu.Lock()
	gid := s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	for _, typ := range []string{"strip_quant", "strip_imp"} {
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
		require.NoError(t, err, "strip %s", typ)
		require.Len(t, res.Produced, 1, "strip %s", typ)
		gid = res.Produced[0].GoalID
	}
	return info.ID, gid
}

// TestBy_StopsAtTheDeadline: a session `by {arith:true}` stops at its
// context's deadline and releases the session. The goal is a theorem by
// induction alone, which no closer has: a chain P(0), P(y) ⇒ P(y + 1)
// with its first churnPoints points spelled as resident numeral facts.
// The grounding stage instantiates the step at every spelled point in
// its first round, and each Arith firing then drops one spelled point
// (a tautology) or resolves one instance — nine firings a round, each
// a unit of work that leaves a different leaf, so the rounds make
// progress until the leaf holds nothing but the chain and the rounds
// cycle, which the close refuses. The attempt runs about churnPoints/9
// rounds over a leaf of churnPoints hypotheses, seconds on an idle
// machine, and the default-budget row needs it to outlast
// ProbeDefaultBudgetMs by a wide margin. A closer that did not poll its
// context between firings, rounds and rungs would run the attempt out
// on every rung of the ladder first, with the session locked.
func TestBy_StopsAtTheDeadline(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	const churnPoints = 80
	points := make([]string, 0, churnPoints)
	for k := range churnPoints {
		points = append(points, fmt.Sprintf("%d ≤ %d", k, k+1))
	}
	churn := "∀P:num→bool. ∀x:num. P(0) ∧ (∀y:num. P(y) ⇒ P(y + 1)) ∧ " +
		strings.Join(points, " ∧ ") + " ⇒ P(x)"
	idx := func(i int) *int { return &i }
	tactic := TacticReq{Type: "by", Arith: true, ByHyps: []ByHypSpec{{HypIndex: idx(0)}}}
	const budget = 500 * time.Millisecond
	// One unit of the closer's work on this goal is milliseconds; the
	// slack is for a loaded machine. A closer without the polls fails
	// the rows below on their reason and elapsed time, not on this timer.
	const slack = 10 * time.Second

	// within runs call, failing the test if it has not returned by
	// budget+slack (the call goes on in the background then: it holds
	// the session, which no other row uses).
	within := func(t *testing.T, call func()) time.Duration {
		t.Helper()
		done := make(chan struct{})
		t0 := time.Now()
		go func() {
			defer close(done)
			call()
		}()
		select {
		case <-done:
			return time.Since(t0)
		case <-time.After(budget + slack):
			t.Fatalf("still running %v after a %v deadline", budget+slack, budget)
			return 0
		}
	}

	t.Run("probe answers unknown(timeout) at its budget", func(t *testing.T) {
		sid, gid := byDeadlineGoal(t, e, churn)
		var res *ProbeResult
		var err error
		elapsed := within(t, func() {
			res, err = e.Probe(t.Context(), sid, &ProbeRequest{GoalID: gid, BudgetMs: int(budget.Milliseconds()), Tactic: tactic})
		})
		require.NoError(t, err)
		require.Equal(t, ProbeUnknown, res.Outcome, "diagnostic: %s", res.Diagnostic)
		require.Equal(t, ProbeReasonTimeout, res.Reason)
		require.Contains(t, res.Diagnostic, "was cut off")
		t.Logf("probe returned after %v", elapsed)
	})

	// A probe that names no budget runs under ProbeDefaultBudgetMs, and
	// the cut-off names the budget it ran under.
	t.Run("probe with no budget_ms runs under the default budget", func(t *testing.T) {
		sid, gid := byDeadlineGoal(t, e, churn)
		var res *ProbeResult
		var err error
		elapsed := within(t, func() {
			res, err = e.Probe(t.Context(), sid, &ProbeRequest{GoalID: gid, Tactic: tactic})
		})
		require.NoError(t, err)
		require.Equal(t, ProbeReasonTimeout, res.Reason, "diagnostic: %s", res.Diagnostic)
		require.Contains(t, res.Diagnostic, fmt.Sprintf("within the %dms probe budget", ProbeDefaultBudgetMs))
		require.GreaterOrEqual(t, elapsed, time.Duration(ProbeDefaultBudgetMs)*time.Millisecond,
			"the probe ran to the default budget")
	})

	t.Run("apply stops at the request deadline", func(t *testing.T) {
		sid, gid := byDeadlineGoal(t, e, churn)
		ctx, cancel := context.WithTimeout(t.Context(), budget)
		defer cancel()
		var res *StepResult
		var err error
		elapsed := within(t, func() {
			res, err = e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: gid, Tactic: tactic})
		})
		require.NoError(t, err)
		require.False(t, res.Success)
		require.NotEmpty(t, res.Diagnostics)
		require.Contains(t, res.Diagnostics[0].Message, "was cut off")
		t.Logf("apply returned after %v", elapsed)
	})

	// An apply's own budget_ms is the same deadline, set by the request.
	t.Run("apply stops at its budget_ms", func(t *testing.T) {
		sid, gid := byDeadlineGoal(t, e, churn)
		var res *StepResult
		var err error
		elapsed := within(t, func() {
			res, err = e.ApplyStep(t.Context(), sid, &ApplyStepRequest{GoalID: gid, BudgetMs: int(budget.Milliseconds()), Tactic: tactic})
		})
		require.NoError(t, err)
		require.False(t, res.Success)
		require.NotEmpty(t, res.Diagnostics)
		require.Contains(t, res.Diagnostics[0].Message, "was cut off")
		t.Logf("apply returned after %v", elapsed)
	})

	// The polls between units of work never come before the first, so a
	// close the first Arith firing makes inside its budget is not
	// refused for the time the stages before it took.
	t.Run("a close the first firing makes inside its budget is not refused", func(t *testing.T) {
		sid, gid := byDeadlineGoal(t, e, "∀a b c:num. a ≤ b ∧ b ≤ c ⇒ a ≤ c")
		res, err := e.Probe(t.Context(), sid, &ProbeRequest{GoalID: gid, Tactic: tactic})
		require.NoError(t, err)
		require.Equal(t, ProbeSuccess, res.Outcome, "diagnostic: %s", res.Diagnostic)
		require.Equal(t, "close", res.Effect)
	})

	// An Arith firing reads the deadline inside its decision, so a
	// budget shorter than the close cuts it off. Cut off is what it
	// answers then, never that the close failed.
	t.Run("a budget shorter than the close cuts it off and does not fail it", func(t *testing.T) {
		sid, gid := byDeadlineGoal(t, e, "∀a b c:num. a ≤ b ∧ b ≤ c ⇒ a ≤ c")
		res, err := e.Probe(t.Context(), sid, &ProbeRequest{GoalID: gid, BudgetMs: 1, Tactic: tactic})
		require.NoError(t, err)
		require.NotEqual(t, ProbeFail, res.Outcome, "diagnostic: %s", res.Diagnostic)
		if res.Outcome == ProbeUnknown {
			require.Equal(t, ProbeReasonTimeout, res.Reason)
			require.Contains(t, res.Diagnostic, "was cut off")
		}
	})
}

// slowArithFiring is a statement on whose residual one Arith firing
// takes far longer than a test waits: a conjunction of 120 nonlinear
// real comparisons over eight variables, under seven hypotheses of the
// same kind. The firing is the conclusion's decision,
// one deep rewrite that asks the real decider about every atom, each
// atom a search over the products of the hypotheses that ends without
// a proof: tenths of a second an atom. With 40 atoms the firing took
// 9 s; with these 120 it was still running at two minutes on a loaded
// machine.
func slowArithFiring() string {
	const vars, atoms = 8, 120
	var names, hyps, concl []string
	for i := range vars {
		names = append(names, fmt.Sprintf("x%d", i))
	}
	for i := range vars - 1 {
		hyps = append(hyps, fmt.Sprintf("x%d * x%d ≤ x%d + &%d", i, i+1, (i+2)%vars, i+1))
	}
	for j := range atoms {
		a, b, c := j%vars, (j*7+3)%vars, (j*5+1)%vars
		concl = append(concl, fmt.Sprintf("x%d * x%d ≤ x%d * x%d + &%d", a, b, c, a, j+2))
	}
	return fmt.Sprintf("∀%s:real. %s ⇒ %s", strings.Join(names, " "), strings.Join(hyps, " ∧ "), strings.Join(concl, " ∧ "))
}

// TestArith_AFiringThatDoesNotEndIsCutOffAtItsBudget: the budget of a
// request reaches inside one Arith firing. A `by {arith:true}` probe
// whose first firing takes minutes answers unknown(timeout) at its
// budget, naming the decision it was cut off in; so does a probe of
// the `arith` tactic, which answered `fail` only once its firing had
// run out; an apply fails with the cut-off; and inspect, whose
// structural pass probes `arith`, answers with the fact marked
// unverified. Each releases the session at the budget.
func TestArith_AFiringThatDoesNotEndIsCutOffAtItsBudget(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	const budget = 500 * time.Millisecond
	// One leaf of the decision is the unit a cut waits for, tenths of a
	// second here; the slack is for that and a loaded machine. A firing
	// that read no clock fails on it.
	const slack = 12 * time.Second
	idx := func(i int) *int { return &i }
	budgetMs := int(budget.Milliseconds())

	t.Run("probe of by {arith}", func(t *testing.T) {
		sid, gid := byDeadlineGoal(t, e, slowArithFiring())
		var res *ProbeResult
		var err error
		elapsed := answersWithin(t, budget+slack, func() {
			res, err = e.Probe(t.Context(), sid, &ProbeRequest{GoalID: gid, BudgetMs: budgetMs,
				Tactic: TacticReq{Type: "by", Arith: true, ByHyps: []ByHypSpec{{HypIndex: idx(0)}}}})
		})
		require.NoError(t, err)
		require.Equal(t, ProbeUnknown, res.Outcome, "diagnostic: %s", res.Diagnostic)
		require.Equal(t, ProbeReasonTimeout, res.Reason)
		require.Contains(t, res.Diagnostic, "was cut off inside an arith decision")
		require.Nil(t, res.EngineFault)
		t.Logf("probe returned after %v", elapsed)
	})

	t.Run("probe of arith", func(t *testing.T) {
		sid, gid := byDeadlineGoal(t, e, slowArithFiring())
		var res *ProbeResult
		var err error
		elapsed := answersWithin(t, budget+slack, func() {
			res, err = e.Probe(t.Context(), sid, &ProbeRequest{GoalID: gid, BudgetMs: budgetMs, Tactic: TacticReq{Type: "arith"}})
		})
		require.NoError(t, err)
		require.Equal(t, ProbeUnknown, res.Outcome, "diagnostic: %s", res.Diagnostic)
		require.Equal(t, ProbeReasonTimeout, res.Reason)
		require.Contains(t, res.Diagnostic, "arith was cut off inside an arith decision")
		t.Logf("probe returned after %v", elapsed)
	})

	t.Run("apply of arith", func(t *testing.T) {
		sid, gid := byDeadlineGoal(t, e, slowArithFiring())
		var res *StepResult
		var err error
		answersWithin(t, budget+slack, func() {
			res, err = e.ApplyStep(t.Context(), sid, &ApplyStepRequest{GoalID: gid, BudgetMs: budgetMs, Tactic: TacticReq{Type: "arith"}})
		})
		require.NoError(t, err)
		require.False(t, res.Success)
		require.NotEmpty(t, res.Diagnostics)
		require.Contains(t, res.Diagnostics[0].Message, "arith was cut off inside an arith decision")
		require.Nil(t, res.EngineFault)
	})

	t.Run("inspect marks the arith fact unverified", func(t *testing.T) {
		sid, gid := byDeadlineGoal(t, e, slowArithFiring())
		var res *InspectResult
		var err error
		answersWithin(t, budget+slack, func() {
			res, err = e.Inspect(t.Context(), sid, &InspectRequest{GoalID: gid, BudgetMs: budgetMs})
		})
		require.NoError(t, err)
		var arith *StructuralFact
		for i := range res.StructuralFacts {
			if res.StructuralFacts[i].Kind == "arith" {
				arith = &res.StructuralFacts[i]
			}
		}
		require.NotNil(t, arith, "the arith fact is listed, not left out: %+v", res.StructuralFacts)
		require.Contains(t, arith.Unverified, "cut off at inspect's 500 ms probe budget")
	})
}

// TestBy_SetBuilderSearchStopsAtTheDeadline: a `by` probe whose refuter
// unifies over a finite set-builder stops at its budget. The leaf is
// finite(S) ∧ S ⊆ M ⊢ finite({m | m ∈ S ∧ m(v) = k}) with
// finite_set.FiniteSubset at the set-builder and S as its one premise;
// the subset premise it also needs (set_basic.SubsetDef) is withheld, so
// no close exists and the refuter searches. Its resolution unifies with
// every free variable instantiable, p₀ : (num → num) → int among them,
// and Huet's imitation then builds pair terms whose tree doubles per
// level over a DAG that grows by a few nodes; a core walk per tree path
// over those terms is one unit of work that never reaches a poll, so the
// probe ran minutes past a 5 s budget while its serve grew by gigabytes
// a second. The walks are bounded by the DAG now, and the probe answers
// unknown(timeout) at its budget.
func TestBy_SetBuilderSearchStopsAtTheDeadline(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	stmt := "∀p:((num → num) → int). ∀v k:num. finite(fun_support(int_of_num(0), p)) ∧ " +
		"fun_support(int_of_num(0), p) ⊆ monomials(integer_polynomial_vars(p)) ⇒ " +
		"finite({m:(num → num) | m ∈ fun_support(int_of_num(0), p) ∧ m(v) = k})"
	sid, gid := byDeadlineGoal(t, e, stmt)
	idx := func(i int) *int { return &i }
	tactic := TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: idx(0)}}, WithLemmas: []LemmaWithSpec{{
		Key: "finite_set.FiniteSubset",
		TermSpecialize: map[string]string{
			"s": "{m:(num → num) | m ∈ fun_support(int_of_num(0), p₀) ∧ m(v₀) = k₀}",
			"t": "fun_support(int_of_num(0), p₀)",
		},
	}}}
	// The reported budget: the search is deeper at five seconds than at
	// one, and the walks it asks for grow with the depth.
	const budget = 5 * time.Second
	// The slack is for the unit in flight at the deadline and a loaded
	// machine; the unbounded walk ran past a minute here.
	const slack = 15 * time.Second
	done := make(chan struct{})
	var res *ProbeResult
	var err error
	t0 := time.Now()
	go func() {
		defer close(done)
		res, err = e.Probe(t.Context(), sid, &ProbeRequest{GoalID: gid, BudgetMs: int(budget.Milliseconds()), Tactic: tactic})
	}()
	select {
	case <-done:
	case <-time.After(budget + slack):
		t.Fatalf("the probe is still running %v after its %v budget", budget+slack, budget)
	}
	elapsed := time.Since(t0)
	require.NoError(t, err)
	require.Equal(t, ProbeUnknown, res.Outcome, "diagnostic: %s", res.Diagnostic)
	require.Equal(t, ProbeReasonTimeout, res.Reason, "diagnostic: %s", res.Diagnostic)
	require.Contains(t, res.Diagnostic, "was cut off")
	t.Logf("probe returned after %v", elapsed)
}

// TestBy_NormalizationStopsAtTheDeadline: the deadline reaches the
// normalization the refuter is built from, not only its search. The leaf
// is product_topology.IndexedCylinderOpen's with the product topology
// unfolded: a cylinder's membership in the topology generated by the
// family `{u | ∃i v. … ∧ u = {f | …}}`. Its clauses are made by denoting
// the family's set-builder, whose instances are folded by unification,
// and on this leaf those unifications run their work budgets out — minutes
// before a clause exists. A probe of `by` answers at its budget all the
// same: the denoting stage ends with the context, and what it had made is
// dropped.
func TestBy_NormalizationStopsAtTheDeadline(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	const cylinder = "{f:I → A | f ∈ indexed_functions(J, z, λj:I. ⋃T(j)) ∧ f(i) ∈ v}"
	const leaf = "∀J:set(I). ∀z:(I → A). ∀T:(I → set(set(A))). ∀i:I. ∀v:set(A). i ∈ J ∧ v ∈ T(i) ⇒ " +
		cylinder + " ∈ topology_generated_on(indexed_functions(J, z, λi:I. ⋃T(i)), " +
		"{u:set(I → A) | ∃i:I. ∃v:set(A). i ∈ J ∧ v ∈ T(i) ∧ u = " + cylinder + "})"
	sid, gid := bareArithLeaf(t, e, leaf, "strip_quant", "strip_imp")
	zero := 0
	const budget = time.Second
	// The stage polls its context once a unification step; the slack is
	// for a loaded machine. Without the deadline the probe runs minutes.
	const slack = 20 * time.Second
	type answer struct {
		res *ProbeResult
		err error
	}
	done := make(chan answer, 1)
	t0 := time.Now()
	go func() {
		res, err := e.Probe(t.Context(), sid, &ProbeRequest{GoalID: gid, BudgetMs: int(budget.Milliseconds()),
			Tactic: TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: &zero}},
				WithLemmas: []LemmaWithSpec{{Key: "topological_space.GeneratedOnContains"}}}})
		done <- answer{res, err}
	}()
	select {
	case got := <-done:
		require.NoError(t, got.err)
		require.Equal(t, ProbeUnknown, got.res.Outcome, "diagnostic: %s", got.res.Diagnostic)
		require.Equal(t, ProbeReasonTimeout, got.res.Reason, "diagnostic: %s", got.res.Diagnostic)
		t.Logf("answered in %v", time.Since(t0))
	case <-time.After(budget + slack):
		t.Fatalf("the probe is still running %v after a %v budget", budget+slack, budget)
	}
}

// TestCNF_DenotingStageEndsUnderAShadowingBinder: the refuter's clauses
// of a premise with a condition under a λ are built. The premise is a
// law of a simplex's vertices, λi. v(i) + COND(i < n ∧ τ(i) < k, 1, 0),
// at one vertex: membership in the vertex set less a vertex ⇔ ∃j. … Its
// normal form has ∃j and, from the equation between two vertices, ∀i at
// prenex level, and the denoting stage takes the condition
// `i < n ∧ τ(i) < 1` out from under the vertex's λi. The fold enters that
// λ under a fresh name, since it shadows ∀i; with the name after i — j,
// which the environment holds — the fold left the instance where it was,
// the stage chose it again in the next round, and the rounds did not end:
// a `by` citing the law never built its refuter, in a session until its
// deadline and in a recording without one.
func TestCNF_DenotingStageEndsUnderAShadowingBinder(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	info, err := e.CreateSession(t.Context())
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	vertex := func(k string) string {
		return "(λi:num. v(i) + COND(i < n ∧ τ(i) < " + k + ", 1, 0))"
	}
	// The law's conclusion: a `by` whose hypotheses supply the law's
	// antecedents holds this much of it as its premise.
	law := "∀n:num. ∀v τ:(num → num). ∀s:set(num → num). " +
		vertex("1") + " ∈ delete(s, " + vertex("0") + ") ⇔ " +
		"∃j:num. j ≤ n ∧ ¬(j = 0) ∧ " + vertex("1") + " = " + vertex("j")
	parsed := dsl.ParsePropTextInScope(law, &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
		Syntax: constSyntax(),
	})
	require.Empty(t, parsed.Errors)
	// The law at fixed n, v, τ and s, as a `by` grounds it, and as the
	// one hypothesis of a refutation.
	instance := parsed.Prop.Conclusion()
	for range 4 {
		instance = ext.MatchesFORALL(instance).Body()
	}
	goal := prop.MakeProp(ext.F, instance)

	// The stage is two rounds and milliseconds on this premise; the
	// deadline is what ends a run whose rounds do not end.
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	t0 := time.Now()
	res, err := clause.NegateGoalCNFFromPreNormalized(ctx, goal, nil)
	require.NoError(t, err, "the premise's clauses were not built in %v", time.Since(t0))
	require.NotNil(t, res)
	t.Logf("clauses built in %v", time.Since(t0))
}

// TestBy_ShapingStopsAtTheDeadline: the deadline reaches the Basic() a
// `by` runs as its shaping stage (by_shape normalized), not only the
// closer after it. The leaf is the membership of a partial derivative in
// a free algebra, from the two definitions and the polynomial fact: once
// the premises are resident, Basic() reads the definitions as equations
// and rewrites the leaf by unification, case split under case split. A
// shaping stage that read no clock ran that fixpoint to its end with the
// session held, whatever the probe's budget (measured: 22 s on a 5 s
// probe).
func TestBy_ShapingStopsAtTheDeadline(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	const leaf = "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀x:D. ∀u:E. ∀S:set(D). ∀f:((D → num) → A). " +
		"comm_ring_on(R) ∧ inverse_on(polynomial_algebra(R, 𝕌), ι, u) = f ∧ f ∈ polynomial_algebra(R, S) ⇒ " +
		"free_algebra_partial(ι, R, x, u) ∈ free_algebra(ι, R, S)"
	sid, gid := bareArithLeaf(t, e, leaf, "strip_quant", "strip_imp")
	zero := 0
	tactic := TacticReq{Type: "by", ByShape: &ByShapeReq{Normalized: true}, ByHyps: []ByHypSpec{{HypIndex: &zero}},
		WithLemmas: []LemmaWithSpec{
			{Key: "partial_derivative.FreeAlgebraPartialDef"},
			{Key: "free_algebra.FreeAlgebraDef"},
			{Key: "partial_derivative.PolynomialPartialIn",
				TermSpecialize: map[string]string{"R": "R₀", "S": "S₀", "x": "x₀", "f": "f₀"}},
			{Key: "set_image.FunInImage", TermSpecialize: map[string]string{
				"f": "ι₀", "s": "polynomial_algebra(R₀, S₀)", "x": "polynomial_algebra_partial(R₀, x₀, f₀)"}},
		}}
	const budget = time.Second
	// The fixpoint polls its deadline between its steps; the slack is for
	// a loaded machine. Without the deadline the stage runs to its end.
	const slack = 10 * time.Second
	type answer struct {
		res *ProbeResult
		err error
	}
	done := make(chan answer, 1)
	t0 := time.Now()
	go func() {
		res, err := e.Probe(t.Context(), sid, &ProbeRequest{GoalID: gid, BudgetMs: int(budget.Milliseconds()), Tactic: tactic})
		done <- answer{res, err}
	}()
	select {
	case got := <-done:
		require.NoError(t, got.err)
		require.Equal(t, ProbeUnknown, got.res.Outcome, "diagnostic: %s", got.res.Diagnostic)
		require.Equal(t, ProbeReasonTimeout, got.res.Reason, "diagnostic: %s", got.res.Diagnostic)
		require.Contains(t, got.res.Diagnostic, "was cut off")
		t.Logf("answered in %v", time.Since(t0))
	case <-time.After(budget + slack):
		t.Fatalf("the probe is still running %v after a %v budget", budget+slack, budget)
	}
}
