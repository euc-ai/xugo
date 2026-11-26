package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// stateAndStrip states statement in a session bound to family and applies
// the strips, then the let where one is given.
func stateAndStrip(t *testing.T, family, statement string, strips []string, let *TacticReq) (*Engine, *Session) {
	t.Helper()
	e, s := boundSession(t, family)
	parsed := dsl.ParsePropTextInScope(statement, s.StatementDoorScope())
	require.Empty(t, parsed.Errors, "add-goal %q", statement)
	s.mu.Lock()
	s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	for _, typ := range strips {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: typ})
	}
	if let != nil {
		applyOnSoleGoal(t, e, s.ID, *let)
	}
	return e, s
}

// byOver applies `by` on the sole goal over the hypotheses that open with
// the prefixes given.
func byOver(t *testing.T, e *Engine, s *Session, settac bool, prefixes ...string) *StepResult {
	t.Helper()
	sole := func(core.Prop) bool { return true }
	var hyps []ByHypSpec
	for _, p := range prefixes {
		hyps = append(hyps, ByHypSpec{HypIndex: hypAt(t, e, s, sole, p)})
	}
	res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: soleGoal(t, e, s.ID).ID,
		Tactic: TacticReq{Type: "by", ByHyps: hyps, Settac: settac}})
	require.NoError(t, err)
	return res
}

// TestBy_AProjectionOfALetNamedRecord: a record value a Let names is
// read at its parts as the value itself is. A fact arrives with the
// record's projection computed — `fun_add(R.add)` for the free module's
// addition, the form a cited instance is handed over in — and the leaf
// spells the projection of the Let's name, `Zn.add`; with the Let's
// equation among the premises the two meet (prover/tactic,
// RecordPartsTactic). Without the equation the name is a variable and
// nothing is read.
func TestBy_AProjectionOfALetNamedRecord(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	const family = "algebra/module/free_module"
	strips := []string{"strip_quant", "strip_imp"}
	let := &TacticReq{Type: "let", Name: "Zn", Const: "free_module_record(R₀, S₀)"}
	for _, row := range []struct {
		name, stmt, fact string
	}{
		{"the goal at the name, an operation",
			"∀R:ring_ops(A). ∀S:set(B). ∀P:(((B → A) → (B → A) → (B → A)) → bool). " +
				"P(fun_add(R.add)) ⇒ P(free_module_record(R, S).add)", "P₀("},
		{"the goal at the name, the carrier",
			"∀R:ring_ops(A). ∀S:set(B). ∀K:set(B → A). " +
				"K ⊆ finite_supp(R.zero, R.carrier, S) ⇒ K ⊆ free_module_record(R, S).carrier", "K₀ ⊆"},
		{"the fact at the name",
			"∀R:ring_ops(A). ∀S:set(B). ∀K:set(B → A). " +
				"K ⊆ free_module_record(R, S).carrier ⇒ K ⊆ finite_supp(R.zero, R.carrier, S)", "K₀ ⊆"},
	} {
		t.Run(row.name, func(t *testing.T) {
			e, s := stateAndStrip(t, family, row.stmt, strips, let)
			res := byOver(t, e, s, false, row.fact, "Zn =")
			require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
			require.Equal(t, "close", res.Effect)
		})
		t.Run(row.name+", the Let's equation not cited", func(t *testing.T) {
			e, s := stateAndStrip(t, family, row.stmt, strips, let)
			res := byOver(t, e, s, false, row.fact)
			require.False(t, res.Success, "the leaf closed with the name's value unread")
		})
		t.Run(row.name+", with no Let", func(t *testing.T) {
			e, s := stateAndStrip(t, family, row.stmt, strips, nil)
			res := byOver(t, e, s, false, row.fact)
			require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		})
	}
}

// TestBy_TheSetDriversFailureNamesThePlainClose: the set driver reads an
// equation between sets pointwise, and a leaf that closes by the equation
// itself fails under it — two names of one set-builder whose predicate
// holds a set equation; a set under card. The failure says so and names
// By, as a refuter's failure on a leaf of set vocabulary names BySets; and
// By closes the leaf.
func TestBy_TheSetDriversFailureNamesThePlainClose(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	const stmt = "∀C H:set(A). ∀f:(A → A → A). ∀X Y:set(A). X = {g:A | g ∈ C ∧ image(f(g), H) = H} ⇒ " +
		"Y = {g:A | g ∈ C ∧ image(f(g), H) = H} ⇒ X = Y"
	strips := []string{"strip_quant", "strip_imp", "strip_imp"}
	e, s := stateAndStrip(t, "sets/set_image", stmt, strips, nil)
	failed := byOver(t, e, s, true, "X₀ =", "Y₀ =")
	require.False(t, failed.Success, "the set driver closed the leaf: the note's example is stale")
	require.NotEmpty(t, failed.Diagnostics)
	message := failed.Diagnostics[0].Message
	require.True(t, strings.Contains(message, "this leaf holds an equation between sets") &&
		strings.Contains(message, "By(…) over the same premises"), "the failure does not name the plain close:\n%s", message)

	e, s = stateAndStrip(t, "sets/set_image", stmt, strips, nil)
	closed := byOver(t, e, s, false, "X₀ =", "Y₀ =")
	require.True(t, closed.Success, "diagnostics: %+v", closed.Diagnostics)
	require.Equal(t, "close", closed.Effect)
}
