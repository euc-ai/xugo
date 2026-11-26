package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

// A claim that applies a λ in place is asserted with the redex in it:
// the claim door keeps what the text spells. A law taken at that λ
// hands its instance over reduced, so the claim an author copies from
// the law by substituting the λ in his head is not the premise the
// instance asks for in spelling, and every later text carries the
// redex on. The step stands and says so, once for each such
// application: the redex and the term it reduces to. A redex inside
// another is part of what the outer one reduces to; a claim that
// applies no λ, and a lemma given by text, carry no such note.
func TestAssert_NotesALambdaAppliedInPlace(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	ctx := context.Background()
	open := func() (*Session, string) {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		_, err = e.SetSessionFamily(info.ID, "real/real_integral", nil)
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		addDoorGoal(t, s, "∀f:(real → real). ∀t:real. &0 ≤ t ⇒ f(t) ≤ f(t) + t")
		applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "strip_quant"})
		state, err := e.InspectState(ctx, info.ID)
		require.NoError(t, err)
		return s, state.Goals[0].ID
	}
	redexNotes := func(res *StepResult) []string {
		var said []string
		for _, d := range res.Diagnostics {
			if d.Type == DiagWrittenRedex {
				said = append(said, d.Message)
			}
		}
		return said
	}
	asserted := func(claim string) []string {
		t.Helper()
		s, gid := open()
		res, err := e.ApplyStep(ctx, s.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "assert", ClaimText: claim}})
		require.NoError(t, err)
		require.True(t, res.Success, "%s: %+v", claim, res.Diagnostics)
		return redexNotes(res)
	}

	said := asserted("∀x:real. &0 ≤ x ∧ x ≤ t₀ ⇒ (λx:real. &0)(x) ≤ (λx:real. x * x)(x)")
	require.Len(t, said, 1, "one note for the claim")
	require.Contains(t, said[0], "the claim applies a λ in place and is asserted with that redex in it")
	require.Contains(t, said[0], "`(λx. &0)(x)`, reduced `&0`")
	require.Contains(t, said[0], "`(λx. x * x)(x)`, reduced `x * x`")
	require.Contains(t, said[0], "state the claim reduced")

	// The outer redex is listed with its whole reduction, and the one
	// inside it is not listed again.
	said = asserted("(λx:real. (λy:real. y * y)(x) + &1)(t₀) = t₀ * t₀ + &1")
	require.Len(t, said, 1)
	require.Equal(t, 1, strings.Count(said[0], ", reduced `"), "the outermost application alone: %s", said[0])
	require.Contains(t, said[0], "reduced `t₀ * t₀ + &1`")

	require.Empty(t, asserted("∀x:real. &0 ≤ x ∧ x ≤ t₀ ⇒ &0 ≤ x * x"), "the reduced claim applies no λ")
	require.Empty(t, asserted("real_continuous_on(𝕌, λx:real. x * x) ⇒ real_continuous_on(𝕌, λx:real. x * x)"),
		"a λ handed whole is no redex")

	// A lemma given by text states what its install leaves to prove,
	// and is not the claim door's.
	s, gid := open()
	res, err := e.ApplyStep(ctx, s.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type: "lemma", LemmaText: "∀x:real. (λy:real. y * y)(x) = x * x"}})
	require.NoError(t, err)
	require.True(t, res.Success, "%+v", res.Diagnostics)
	require.Empty(t, redexNotes(res))
}
