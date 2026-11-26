package registry

import (
	"testing"

	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// A card registers like any member: it has a statement (the Card
// build's headline), a key, a family — and no proof.
func TestCard_RegistersWithoutAProof(t *testing.T) {
	fam := NewFamily("zz_card_registers", nil)
	card := fam.Add(ProofEntry{
		Name:  "Antisym",
		Build: fam.Card("∀P:(bool → bool). ∀a b:bool. a ∧ b ⇒ P(a)", "the conjunction commutes under P"),
	})
	require.True(t, card.IsCard())
	require.Equal(t, "the conjunction commutes under P", card.CardNote())
	require.Nil(t, card.Build.Fn)
	st := card.Statement()
	require.Equal(t, 0, st.Prop.NumHyps())
	require.Equal(t, st.Key(), KeyOf(card.CardStatement()), "the card is served at its own statement")
	found, ok := ByName("zz_card_registers.Antisym")
	require.True(t, ok)
	require.Same(t, card, found)

	proved := fam.Add(ProofEntry{
		Name:  "Proved",
		Build: BuildSpec{Headline: "∀P:(bool → bool). ∀a b:bool. a ∨ b ⇒ P(b)", Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
	})
	require.False(t, proved.IsCard())
	require.Empty(t, proved.CardNote())
	require.Panics(t, func() { proved.CardStatement() }, "a proved member is not a card")
}

// Registration refuses the shapes that are not a card and not a
// proof: a card carrying a build function, a card without a note, a
// member with neither a build nor a card.
func TestCard_RegistrationRefusals(t *testing.T) {
	fam := NewFamily("zz_card_refusals", nil)
	stmt := "∀P:(bool → bool). ∀a b:bool. (a ⇔ b) ⇒ P(a)"
	require.PanicsWithValue(t,
		"proof registry: zz_card_refusals.Both is a card with a proof — a card has no Build.Fn; state it with Family.Card, or prove it",
		func() {
			spec := fam.Card(stmt, "a note")
			spec.Fn = func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }
			fam.Add(ProofEntry{Name: "Both", Build: spec})
		})
	require.PanicsWithValue(t,
		"proof registry: the card zz_card_refusals.Mute has no note — a card says why it is a member and what its proof must establish",
		func() { fam.Add(ProofEntry{Name: "Mute", Build: fam.Card(stmt, "  ")}) })
	require.PanicsWithValue(t,
		"proof registry: incomplete ProofEntry: zz_card_refusals.Neither",
		func() { fam.Add(ProofEntry{Name: "Neither", Build: BuildSpec{Headline: stmt}}) })
}
