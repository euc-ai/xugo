package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// bareArithLeaf adds a statement to a fresh session and strips it, and
// returns the session id and the residual leaf's goal id.
func bareArithLeaf(t *testing.T, e *Engine, stmt string, strips ...string) (sid, gid string) {
	t.Helper()
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	parsed := dsl.ParsePropTextInScope(stmt, &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
		Syntax: constSyntax(),
	})
	require.Empty(t, parsed.Errors)
	s.mu.Lock()
	gid = s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	for _, typ := range strips {
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
		require.NoError(t, err, "apply %s", typ)
		require.Len(t, res.Produced, 1, typ)
		gid = res.Produced[0].GoalID
	}
	return info.ID, gid
}

// TestByArith_PremiseFree_ClosesAFactOfArithmeticAlone: `by {arith:true}`
// with no premise is the statement "this is a fact of arithmetic alone",
// the arithmetic sibling of the premise-free `by {settac:true}`. The two
// rows are the known issue's own: the right-summand guard of an index
// argument, and an estimate that asks nothing of its point.
func TestByArith_PremiseFree_ClosesAFactOfArithmeticAlone(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	for _, row := range []struct {
		name, stmt string
		strips     []string
	}{
		{"nat guard", "∀m n:num. n ≤ m + n", []string{"strip_quant"}},
		// A gcd-unsat equality with variables on both sides: refuted by the
		// rounding cuts of its two ≤ rows (omega.IntRefuteProof).
		{"nat parity, two-sided", "∀m n:num. ¬(m + m = n + n + 3)", []string{"strip_quant"}},
		{"real estimate", "∀a x y:real. real_abs(y - x) < x - a ⇒ a < y", nil},
	} {
		t.Run(row.name, func(t *testing.T) {
			sid, gid := bareArithLeaf(t, e, row.stmt, row.strips...)
			res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
				GoalID: gid, Tactic: TacticReq{Type: "by", Arith: true},
			})
			require.NoError(t, err)
			require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
			require.Equal(t, "close", res.Effect)
		})
	}
}

// TestByArith_PremiseFree_ClearsTheAmbientHypotheses: the premise-free
// form reads the goal ALONE. A leaf whose close needs a resident
// hypothesis fails under it and closes once the hypothesis is named —
// the discipline every other `by` keeps.
func TestByArith_PremiseFree_ClearsTheAmbientHypotheses(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	const stmt = "∀x y:num. x < y ⇒ x + 1 ≤ y"

	sid, gid := bareArithLeaf(t, e, stmt, "strip_quant", "strip_imp")
	bare, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid, Tactic: TacticReq{Type: "by", Arith: true},
	})
	require.NoError(t, err)
	require.False(t, bare.Success, "x < y is cleared, and x + 1 ≤ y is no fact of arithmetic alone")

	zero := 0
	named, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid, Tactic: TacticReq{Type: "by", Arith: true, ByHyps: []ByHypSpec{{HypIndex: &zero}}},
	})
	require.NoError(t, err)
	require.True(t, named.Success, "diagnostics: %+v", named.Diagnostics)
	require.Equal(t, "close", named.Effect)
}

// TestByArith_CondWithAResidentGuard: the arithmetic closer reads a COND
// at the arm a resident hypothesis selects, whatever the guard is — here
// a membership, which is no atom of the decider's own case splits. The
// two shapes are real_cardinality's ternary expansion's.
func TestByArith_CondWithAResidentGuard(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	for _, row := range []struct{ name, stmt string }{
		{"the guard holds",
			"∀p:real. ∀s:set(num). ∀n:num. &0 ≤ p ⇒ n ∈ s ⇒ real_abs(COND(n ∈ s, p, real_of_num(0))) ≤ p"},
		{"the guard fails",
			"∀p:real. ∀s:set(num). ∀n:num. &0 ≤ p ⇒ ¬(n ∈ s) ⇒ &0 ≤ COND(n ∈ s, real_of_num(0), p)"},
	} {
		t.Run(row.name, func(t *testing.T) {
			sid, gid := bareArithLeaf(t, e, row.stmt, "strip_quant", "strip_imp", "strip_imp")
			zero, one := 0, 1
			res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
				GoalID: gid, Tactic: TacticReq{Type: "by", Arith: true,
					ByHyps: []ByHypSpec{{HypIndex: &zero}, {HypIndex: &one}}},
			})
			require.NoError(t, err)
			require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
			require.Equal(t, "close", res.Effect)
		})
	}
}

// byArithOverHyps runs `by {arith:true}` on the leaf over the first n
// hypotheses, under the given budget (0: the request's default).
func byArithOverHyps(t *testing.T, e *Engine, sid, gid string, n, budgetMs int) *StepResult {
	t.Helper()
	req := TacticReq{Type: "by", Arith: true}
	for i := range n {
		req.ByHyps = append(req.ByHyps, ByHypSpec{HypIndex: &i})
	}
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: req, BudgetMs: budgetMs})
	require.NoError(t, err)
	return res
}

// TestByArith_GuardAssertedByAHypothesis: an implication whose guard a
// resident hypothesis asserts is read as its consequent, and an ⇔ one of
// whose sides a hypothesis asserts as its other side, whatever that side
// is — a propositional variable, a membership — as an arithmetic one is.
// The control row is the consequent alone; the ⇔ rows are a membership
// law read at its instance (`m ∈ 0 .. n ⇔ m ≤ n`) beside the membership,
// the goal spelled otherwise than the law's arithmetic side.
func TestByArith_GuardAssertedByAHypothesis(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	for _, row := range []struct {
		name, stmt string
		strips     []string
	}{
		{"the consequent alone", "n:num, i:num ⊢ i ≤ n + 1 ⇒ i ≤ n + 2", []string{"strip_imp"}},
		{"an arithmetic guard", "n:num, i:num ⊢ i ≤ 5 ⇒ (i ≤ 5 ⇒ i ≤ n + 1) ⇒ i ≤ n + 2",
			[]string{"strip_imp", "strip_imp"}},
		{"a propositional guard", "n:num, i:num, P:bool ⊢ P ⇒ (P ⇒ i ≤ n + 1) ⇒ i ≤ n + 2",
			[]string{"strip_imp", "strip_imp"}},
		{"a propositional guard beside its implication", "n:num, i:num, P:bool ⊢ P ∧ (P ⇒ i ≤ n + 1) ⇒ i ≤ n + 2",
			[]string{"strip_imp"}},
		{"a membership guard", "n:num, i:num, H:set(num) ⊢ i ∈ H ⇒ (i ∈ H ⇒ i ≤ n + 1) ⇒ i ≤ n + 2",
			[]string{"strip_imp", "strip_imp"}},
		{"a propositional side of an ⇔", "j:num, r:num, P:bool ⊢ (P ⇔ j ≤ r) ∧ P ⇒ j < r + 1",
			[]string{"strip_imp"}},
		{"a membership side of an ⇔", "j:num, r:num, H:set(num) ⊢ (j ∈ H ⇔ j ≤ r) ⇒ j ∈ H ⇒ j < r + 1",
			[]string{"strip_imp", "strip_imp"}},
	} {
		t.Run(row.name, func(t *testing.T) {
			sid, gid := bareArithLeaf(t, e, row.stmt, row.strips...)
			res := byArithOverHyps(t, e, sid, gid, len(row.strips), 0)
			require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
			require.Equal(t, "close", res.Effect)
		})
	}
}

// TestByArith_OrderLawClauseBesideItsSignFacts: an order law installed in
// its clause form, `¬(&0 ≤ z) ∨ x·z ≤ &1·z`, beside the facts that give
// `&0 ≤ z` (z a square over a factorial) — the clause reads as its
// consequent and the goal follows from it. Reading a formula a hypothesis
// states is not applied to an arithmetic one: the case split on `&0 ≤ z`
// assumes `¬(&0 ≤ z)` in a branch the sign facts contradict, and reading
// the clause's literal there as ⊤ would decide the whole clause redundant,
// which the retention rule keeps unread.
//
// The consequent is one the closer does not prove from the other facts —
// `x ≤ &1` scales z down only with `&0 ≤ z` resident, and here that is
// the clause's own guard. Where it does prove the consequent the clause is
// redundant in earnest and is dropped, and the close is left to prove the
// goal as the goal spells it: a quotient of a product, `(x·h²)/f`, is not
// the monotone scaling `x·(h²/f)` to it. The second row is that leaf with
// the guard named as a fact, which closes with no law beside it
// (real_exp_log.ExpQuadraticBound's calc leg).
func TestByArith_OrderLawClauseBesideItsSignFacts(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	const positive = "real_of_num(0) < real_of_num(factorial(n + 2)) ⇒ "
	for _, row := range []struct {
		name, stmt string
		hyps       int
	}{
		{"the clause read as its consequent", "h:real, x:real, n:num ⊢ " +
			"x ≤ &1 ⇒ " + positive +
			"¬(&0 ≤ (h ^ 2) / &factorial(n + 2)) ∨ (x * ((h ^ 2) / &factorial(n + 2)) ≤ &1 * ((h ^ 2) / &factorial(n + 2))) ⇒ " +
			"(x * (h ^ 2)) / &factorial(n + 2) ≤ (h ^ 2) / &factorial(n + 2)", 3},
		{"the guard named, no law", "h:real, n:num ⊢ " +
			"real_abs(h) ^ n ≤ &1 ⇒ " + positive +
			"&0 ≤ (h ^ 2) / &factorial(n + 2) ⇒ " +
			"((real_abs(h) ^ n) * (h ^ 2)) / &factorial(n + 2) ≤ (h ^ 2) / &factorial(n + 2)", 3},
	} {
		t.Run(row.name, func(t *testing.T) {
			strips := make([]string, row.hyps)
			for i := range strips {
				strips[i] = "strip_imp"
			}
			sid, gid := bareArithLeaf(t, e, row.stmt, strips...)
			res := byArithOverHyps(t, e, sid, gid, row.hyps, 0)
			require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
			require.Equal(t, "close", res.Effect)
		})
	}
}

// TestByArith_MembershipGuardedFaceEquations: a filler's face equations
// read at two faces, each guarded by the face's membership in a set the
// closer does not unfold, beside the memberships — the guards are read,
// the numeral `1 + 1` folds, and the leaf closes inside the budget; an
// implication the close does not need costs it nothing.
func TestByArith_MembershipGuardedFaceEquations(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	const scope = "d:(num → (num → (var:A → var:A))), y:(num → var:A), w:var:A, g:var:A, h:var:A, S:set(num) ⊢ "
	const face1 = "(1 ∈ S ⇒ d(1 + 1, 1, w) = y(1)) ⇒ "
	const face2 = "(2 ∈ S ⇒ d(1 + 1, 2, w) = y(2)) ⇒ "
	const rest = "1 ∈ S ⇒ 2 ∈ S ⇒ y(1) = g ⇒ y(2) = h ⇒ d(2, 1, w) = g"
	for _, row := range []struct {
		name, stmt string
		hyps       int
	}{
		{"the face the goal reads", scope + face1 + rest, 5},
		{"both faces", scope + face1 + face2 + rest, 6},
	} {
		t.Run(row.name, func(t *testing.T) {
			strips := make([]string, row.hyps)
			for i := range strips {
				strips[i] = "strip_imp"
			}
			sid, gid := bareArithLeaf(t, e, row.stmt, strips...)
			res := byArithOverHyps(t, e, sid, gid, row.hyps, 10000)
			require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
			require.Equal(t, "close", res.Effect)
		})
	}
}

// TestByArith_LiteralQuotientAsAFactor: a quotient by a numeral is read
// where it MULTIPLIES as it is where it is added — `&1 / &2 * d` beside
// `d / &2` — in the goal and in a hypothesis alike. The rows are the
// exponential series' ratio bound, its mirror with the product in the
// hypothesis, and the ternary expansion's geometric value.
func TestByArith_LiteralQuotientAsAFactor(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	for _, row := range []struct {
		name, stmt string
		strips     []string
	}{
		{"a left factor, in the goal", "a:real, d:real ⊢ &2 * a ≤ d ⇒ a ≤ &1 / &2 * d", []string{"strip_imp"}},
		{"a right factor, in the goal", "a:real, d:real ⊢ &2 * a ≤ d ⇒ a ≤ d * (&1 / &2)", []string{"strip_imp"}},
		{"a factor, in the hypothesis", "a:real, d:real ⊢ &1 / &2 * d ≤ a ⇒ d ≤ &2 * a", []string{"strip_imp"}},
		{"two halves make the whole", "d:real ⊢ &1 / &2 * d + &1 / &2 * d = d", nil},
		{"beside a numeral's inverse", "p:real ⊢ real_inv(&3) * p * (&3 / &2) = p / &2", nil},
	} {
		t.Run(row.name, func(t *testing.T) {
			sid, gid := bareArithLeaf(t, e, row.stmt, row.strips...)
			req := TacticReq{Type: "by", Arith: true}
			if len(row.strips) > 0 {
				zero := 0
				req.ByHyps = []ByHypSpec{{HypIndex: &zero}}
			}
			res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: req})
			require.NoError(t, err)
			require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
			require.Equal(t, "close", res.Effect)
		})
	}
}

// TestByArith_StrictBoundBesideASum: a strict hypothesis is read over ℤ as
// `i + 1 ≤ q` in every row the integer core builds, whatever order the
// context's atoms were met in. The rows are the truncation branch of the
// monus split — `i < q ⊢ p + q - 1 + 1 = p + q` pins `p + q ≤ 1` and asks
// `1 = p + q`, an equation between a numeral and a sum whose atoms the
// strict hypothesis had entered out of order — and that branch stated on
// its own. Both closed only with the hypothesis already stated as
// `i + 1 ≤ q`.
func TestByArith_StrictBoundBesideASum(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"under the monus split",
			"∀i p q:num. i < q ⇒ p + q - 1 + 1 = p + q",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"the truncation branch on its own",
			"∀i p q:num. i < q ∧ p + q ≤ 1 ⇒ 1 = p + q",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
	})
}
