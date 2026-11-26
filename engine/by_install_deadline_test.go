package engine

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
)

// formModulePointwise is differential_form's statement that the degree-k
// module of forms has the k-forms as its carrier and acts pointwise: its
// zero, addition, negation and scaling are the real ones at every chart,
// point and matrix.
const formModulePointwise = "∀n k:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀a:real. " +
	"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
	"manifold_form_module⟨n⟩(T, 𝒜, k).carrier = " +
	"{ω:prod(set(A), A → num → real) → (num → real) → (num → num → real) → real | " +
	"manifold_form_on⟨n⟩(T, 𝒜, k, ω)} ∧ " +
	"manifold_form_module⟨n⟩(T, 𝒜, k).zero = " +
	"(λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). real_of_num(0)) ∧ " +
	"manifold_form_module⟨n⟩(T, 𝒜, k).add(α, β) = " +
	"(λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). α(c, y, P) + β(c, y, P)) ∧ " +
	"manifold_form_module⟨n⟩(T, 𝒜, k).neg(α) = " +
	"(λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). -α(c, y, P)) ∧ " +
	"manifold_form_module⟨n⟩(T, 𝒜, k).smul(a, α) = " +
	"(λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). a * α(c, y, P))"

// TestBy_PremiseInstallStopsAtTheDeadline: the deadline reaches the
// install of a `by`'s premises. The leaf is the statement above with
// the module unfolded to three nested function modules over the real
// ring: five conjuncts, four of them equations between an unapplied
// fun_zero, fun_add, fun_neg or fun_smul three deep and its pointwise
// λ. The premises are the four definitions. Each installs through the
// preserving chain, which reads an equation as a rewrite rule, and
// FunAddDef's clause form is `add(f(x), g(x)) = fun_add(add, f, g, x)`,
// two sides of one size, so the rule is read as written: its pattern is
// headed by the bound variable `add`, no term of the leaf is passed over
// for its head, and each unification of the pattern against one leaves a
// function variable free and runs its work budget out before it answers
// "no unifier" — seconds a term, minutes for the leaf, and no clock on
// any of it. A probe of `by` answers at its budget all the same, names
// the premise whose install it was cut off in, and leaves the session
// free.
func TestBy_PremiseInstallStopsAtTheDeadline(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	sid, gid := bareArithLeaf(t, e, formModulePointwise, "strip_quant")
	unfolded, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type: "simp_with",
		WithLemmas: []LemmaWithSpec{
			{Key: "differential_form.FormModuleDef"},
			{Key: "module_record.RestrictModuleDef"},
			{Key: "function_module.FunctionModuleDef"},
			{Key: "module_record.RegularModuleDef"},
			{Key: "real_ring.RealRingDef"},
		}}})
	require.NoError(t, err)
	require.Len(t, unfolded.Produced, 1)
	gid = unfolded.Produced[0].GoalID

	const budget = time.Second
	// One unification of the pattern polls its context at every step;
	// the slack is for a loaded machine. Without the deadline the probe
	// runs minutes.
	const slack = 20 * time.Second
	type answer struct {
		res *ProbeResult
		err error
	}
	done := make(chan answer, 1)
	t0 := time.Now()
	go func() {
		res, err := e.Probe(t.Context(), sid, &ProbeRequest{GoalID: gid, BudgetMs: int(budget.Milliseconds()),
			Tactic: TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{
				{Key: "function_module.FunAddDef"},
				{Key: "function_module.FunZeroDef"},
				{Key: "function_module.FunNegDef"},
				{Key: "function_module.FunSmulDef"},
			}}})
		done <- answer{res, err}
	}()
	select {
	case got := <-done:
		require.NoError(t, got.err)
		require.Equal(t, ProbeUnknown, got.res.Outcome, "diagnostic: %s", got.res.Diagnostic)
		require.Equal(t, ProbeReasonTimeout, got.res.Reason, "diagnostic: %s", got.res.Diagnostic)
		require.Contains(t, got.res.Diagnostic, "was cut off inside the install of premise function_module.FunAddDef")
		t.Logf("answered in %v", time.Since(t0))
	case <-time.After(budget + slack):
		t.Fatalf("the probe is still running %v after a %v budget", budget+slack, budget)
	}

	// The session is free: its next request is served.
	state := make(chan error, 1)
	go func() {
		_, err := e.InspectState(t.Context(), sid)
		state <- err
	}()
	select {
	case err := <-state:
		require.NoError(t, err)
	case <-time.After(slack):
		t.Fatalf("the session is still held %v after the probe answered", slack)
	}
}
