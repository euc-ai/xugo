package engine

// A `by` installs its premises in list order, each into the leaf the
// premises before it have built. A bare law listed after the instance
// its rewrite meets closes the goal at its install; listed ahead of it,
// the close fails and the failure names the law and its place
// (proof.listOrderNote). emit-section keeps the session's order, so the
// member it renders is the close the session made.

import (
	"context"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestBy_ABareLawClosesAfterTheInstanceAndTheMemberKeepsTheOrder: the
// composite's law, cited bare after the instance that states
// injective_on(s, f ∘ g), closes injective_on(s, λx. f(g(x))) at its
// install — no refutation, nothing recorded — and the emitted member
// lists the instance ahead of the law and replays.
func TestBy_ABareLawClosesAfterTheInstanceAndTheMemberKeepsTheOrder(t *testing.T) {
	e, s := boundSession(t, "sets/functions")
	addTextGoal(t, s, "∀f:(B → C). ∀g:(A → B). ∀s:set(A). ∀t:set(B). "+
		"injective_on(t, f) ⇒ injective_on(s, g) ⇒ (∀x:A. x ∈ s ⇒ g(x) ∈ t) ⇒ injective_on(s, λx:A. f(g(x)))")
	for _, step := range []string{"strip_quant", "strip_imp", "strip_imp", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	res := applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by",
		ByHyps: []ByHypSpec{
			{HypIndex: hypAt(t, e, s, sole, "injective_on(t₀")},
			{HypIndex: hypAt(t, e, s, sole, "injective_on(s₀")},
			{HypIndex: hypAt(t, e, s, sole, "∀")},
		},
		WithLemmas: []LemmaWithSpec{
			{Key: "functions.InjectiveOnCompose", TermSpecialize: map[string]string{"f": "f₀", "g": "g₀", "s": "s₀", "t": "t₀"}},
			{Key: "functions.ComposeApply"},
		}})
	closer := ""
	for _, d := range res.Diagnostics {
		if d.Type == DiagByCloser {
			closer = d.Message
		}
	}
	assert.Equal(t, "Closed by: premise", closer, "diagnostics: %v", res.Diagnostics)
	const pkg = "zzbarelawlast"
	src := emitInto(t, e, s, pkg, "ZzBareLawLast")
	instance := strings.Index(src, "functions.InjectiveOnCompose")
	law := strings.Index(src, "functions.ComposeApply")
	require.True(t, law >= 0 && instance >= 0, "--- source: ---\n%s", src)
	assert.Less(t, instance, law, "the member lists the premises in the session's order\n--- source: ---\n%s", src)
	replayEmitted(t, pkg, "ZzBareLawLast", src)
}

// TestBy_ABareLawAheadOfItsInstanceFailsNamingTheOrder: the composite
// and the identity of a module, each by its homomorphism law at an
// instance beside the law that reads the map pointwise. Listed after the
// instance the pointwise law closes the goal; listed ahead of it the
// close fails, and the failure names the law and says to list it last.
func TestBy_ABareLawAheadOfItsInstanceFailsNamingTheOrder(t *testing.T) {
	probe := func(t *testing.T, e *Engine, s *Session, req TacticReq) *ProbeResult {
		t.Helper()
		state, err := e.InspectState(context.Background(), s.ID)
		require.NoError(t, err)
		require.Len(t, state.Goals, 1)
		res, err := e.Probe(context.Background(), s.ID, &ProbeRequest{GoalID: state.Goals[0].ID, Tactic: req})
		require.NoError(t, err)
		return res
	}
	opened := func(t *testing.T, statement string, strips ...string) (*Engine, *Session) {
		e, s := boundSession(t, "algebra/module/module_homomorphism")
		addTextGoal(t, s, statement)
		for _, step := range strips {
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
		}
		return e, s
	}
	namesTheOrder := func(t *testing.T, res *ProbeResult, law string) {
		t.Helper()
		require.Equal(t, ProbeOutcome("fail"), res.Outcome, "%+v", res)
		assert.Contains(t, res.Diagnostic, "the order of the premise list (checked): premise "+law+", a bare law, "+
			"closes this goal at its install when it is listed last")
		assert.Contains(t, res.Diagnostic, "Move it to the end of the list.")
	}
	t.Run("composite", func(t *testing.T) {
		e, s := opened(t, "∀R:ring_ops(A). ∀V:module_ops(A, B). ∀S T:(B → B). module_homomorphism(R, V, V, S) ⇒ "+
			"module_homomorphism(R, V, V, T) ⇒ module_homomorphism(R, V, V, λw:B. T(S(w)))",
			"strip_quant", "strip_imp", "strip_imp")
		maps := []ByHypSpec{
			{HypIndex: hypAt(t, e, s, sole, "module_homomorphism(R₀, V₀, V₀, S₀)")},
			{HypIndex: hypAt(t, e, s, sole, "module_homomorphism(R₀, V₀, V₀, T₀)")},
		}
		instance := LemmaWithSpec{Key: "module_homomorphism.HomCompose", TermSpecialize: map[string]string{
			"R": "R₀", "M": "V₀", "N": "V₀", "L": "V₀", "f": "S₀", "g": "T₀"}}
		pointwise := LemmaWithSpec{Key: "functions.ComposeApply"}
		last := probe(t, e, s, TacticReq{Type: "by", ByHyps: maps, WithLemmas: []LemmaWithSpec{instance, pointwise}})
		assert.Equal(t, ProbeOutcome("success"), last.Outcome, "%+v", last)
		namesTheOrder(t, probe(t, e, s, TacticReq{Type: "by", ByHyps: maps, WithLemmas: []LemmaWithSpec{pointwise, instance}}),
			"functions.ComposeApply")
	})
	t.Run("identity", func(t *testing.T) {
		e, s := opened(t, "∀R:ring_ops(A). ∀V:module_ops(A, B). ∀S:(B → B). module_homomorphism(R, V, V, S) ⇒ "+
			"module_homomorphism(R, V, V, λw:B. w)",
			"strip_quant", "strip_imp")
		source := LemmaWithSpec{Key: "module_homomorphism.HomSource",
			ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, sole, "module_homomorphism(R₀, V₀, V₀, S₀)")}}
		instance := LemmaWithSpec{Key: "module_homomorphism.HomIdentity", TermSpecialize: map[string]string{"R": "R₀", "M": "V₀"}}
		pointwise := LemmaWithSpec{Key: "functions.IdentityApply"}
		last := probe(t, e, s, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{source, instance, pointwise}})
		assert.Equal(t, ProbeOutcome("success"), last.Outcome, "%+v", last)
		namesTheOrder(t, probe(t, e, s, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{pointwise, source, instance}}),
			"functions.IdentityApply")
	})
}
