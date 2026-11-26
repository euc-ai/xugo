package registry

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// statementStub is a build that builds nothing: the statement tests
// read statements and compute keys, they prove nothing.
var statementStub = Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })

// A member's statement is read on first use and its key computed on
// first ask: the corpus scans read every member and ask no key but the
// hits', so reading must not normalize.
func TestStatement_KeyIsComputedOnAsk(t *testing.T) {
	fam := NewFamily("zz_statement_key", nil)
	entry := fam.Add(ProofEntry{
		Name:  "Member",
		Build: BuildSpec{Fn: statementStub.Fn, Headline: "P:bool → bool ⊢ ∀a b:bool. P(a) ⇒ P(b)"},
	})
	st := entry.Statement()
	require.NotNil(t, st.Prop)
	require.Empty(t, st.key, "reading the statement computes no key")
	require.Same(t, st, entry.Statement(), "read once")

	key := st.Key()
	require.NotEmpty(t, key)
	require.NotEmpty(t, st.key, "asked once, the key is kept")
	require.Equal(t, key, entry.Statement().Key())
	require.Equal(t, key, KeyOf(st.Prop), "KeyOf is the statement's own key")
}

// ReadStatements reads every member and computes no key.
func TestReadStatements_ReadsWithoutKeys(t *testing.T) {
	fam := NewFamily("zz_statement_read_all", nil)
	entry := fam.Add(ProofEntry{
		Name:  "Member",
		Build: BuildSpec{Fn: statementStub.Fn, Headline: "Q:bool → bool ⊢ ∀a b:bool. Q(a) ∧ Q(b) ⇒ Q(b)"},
	})
	ReadStatements()
	require.NotNil(t, entry.stmt.value, "read")
	require.Empty(t, entry.stmt.value.key, "no key asked")
}

// The registry refuses ⊤ as a member's key at both doors: the spelled
// key at registration, the computed key at the first ask. A member
// whose spelled key lies about a tautological statement reads without
// complaint and panics — naming itself — when its key is asked.
func TestStatement_RefusesTheKeyOfTautologyOnAsk(t *testing.T) {
	fam := NewFamily("zz_statement_tautology", nil)
	entry := fam.Add(ProofEntry{
		Name:  "Trivial",
		Key:   "not-the-key-of-top",
		Build: BuildSpec{Fn: statementStub.Fn, Headline: "∀a:bool. a ⇒ a"},
	})
	require.NotPanics(t, func() { entry.Statement() }, "reading is not asking")
	require.PanicsWithValue(t,
		"proof registry: zz_statement_tautology.Trivial states a tautology (its normalized statement is ⊤): "+
			"normalization closes such a statement everywhere, so no member can prove it and none can be cited for it",
		func() { entry.Statement().Key() })
	require.NotPanics(t, func() { NewStatement(entry.Statement().Prop).Key() },
		"a statement no member states is refused nothing")
}

// The statement door refuses a statement that names a polymorphic
// constant and no term of the letter's type: the parse leaves the
// constant at the parser's stand-in for a type variable, which no
// binder of the statement and no letter of the family names. The
// refusal names the constant and the letter to pin; pinned, the same
// statement reads.
func TestStatement_RefusesAnUnpinnedTypeLetter(t *testing.T) {
	fam := NewFamily("zz_statement_unpinned", nil)
	fam.Define(DefEntry{
		Name:      "WholeDef",
		Const:     "zz_whole",
		Type:      "A → bool",
		Equations: []string{"∀x:A. zz_whole(x) ⇔ ⊤"},
	})
	fam.Define(DefEntry{
		Name:      "InhabitedDef",
		Const:     "zz_inhabited",
		Type:      "(A → bool) → bool",
		Equations: []string{"∀s:(A → bool). zz_inhabited(s) ⇔ ∃x:A. s(x)"},
	})

	unpinned := fam.Add(ProofEntry{
		Name:  "Unpinned",
		Build: BuildSpec{Fn: statementStub.Fn, Headline: "zz_inhabited(zz_whole) ⇒ ∀b:bool. b ∨ ¬b ∨ zz_inhabited(zz_whole)"},
	})
	require.PanicsWithValue(t,
		"proof registry: the statement of zz_statement_unpinned.Unpinned leaves a type letter unpinned: "+
			"no term of the statement has that type, so nothing says at which type the constant is read. "+
			"Pin it once where the constant is written:\n"+
			"  zz_inhabited's A — write zz_inhabited⟨A:A⟩, or the type it is meant at\n"+
			"  zz_whole's A — write zz_whole⟨A:A⟩, or the type it is meant at",
		func() { unpinned.Statement() })
	_, err := unpinned.KeyOfText("zz_inhabited(zz_whole)")
	require.ErrorContains(t, err, "leaves a type letter unpinned", "the key door reports the same refusal")

	pinned := fam.Add(ProofEntry{
		Name:  "Pinned",
		Build: BuildSpec{Fn: statementStub.Fn, Headline: "zz_inhabited(zz_whole⟨A:A⟩)"},
	})
	require.NotPanics(t, func() { pinned.Statement() })
	require.False(t, strings.Contains(ext.PrintTerm(pinned.Statement().Prop.Conclusion()), "?"),
		"the pinned statement carries the author's letter")

	bound := fam.Add(ProofEntry{
		Name:  "Bound",
		Build: BuildSpec{Fn: statementStub.Fn, Headline: "∀s:(B → bool). zz_inhabited(s) ⇒ zz_inhabited(s)"},
	})
	require.NotPanics(t, func() { bound.Statement() }, "a binder of the letter's type pins the constant")
}

// A statement's constants are read off it, by name, once each, the
// logic's own excluded, and asking them asks no key: the scan listing
// the members by constant reads what ReadStatements read.
func TestStatement_ConstantsAreReadWithIt(t *testing.T) {
	fam := NewFamily("zz_statement_constants", nil)
	pred := fam.Define(DefEntry{
		Name: "Pred", Const: "zz_sc_pred", Type: "bool → bool",
		Equations: []string{"∀a:bool. zz_sc_pred(a) ⇔ ¬a"},
	})
	entry := fam.Add(ProofEntry{
		Name:  "Member",
		Build: BuildSpec{Fn: statementStub.Fn, Headline: "∀a b:bool. zz_sc_pred(a) ∧ ¬b ⇒ zz_sc_pred(b) ∨ a = b"},
	})
	bare := fam.Add(ProofEntry{
		Name:  "Bare",
		Build: BuildSpec{Fn: statementStub.Fn, Headline: "∀a b:bool. a ∧ b ⇒ (a ⇔ b)"},
	})
	require.Equal(t, []core.TermName{"zz_sc_pred"}, entry.Statement().Constants(), "once, the connectives and equality excluded")
	require.Equal(t, []core.TermName{"zz_sc_pred"}, pred.Statement().Constants())
	require.Empty(t, bare.Statement().Constants())
	require.Empty(t, entry.stmt.value.key, "no key asked")
	require.Empty(t, pred.stmt.value.key)
}

// A statement's head is prepared once, over the statement closed: the
// scan by goal reads what ReadStatements prepared.
func TestStatement_HeadIsPreparedOnce(t *testing.T) {
	fam := NewFamily("zz_statement_head", nil)
	entry := fam.Add(ProofEntry{
		Name:  "Member",
		Build: BuildSpec{Fn: statementStub.Fn, Headline: "P:bool → bool ⊢ ∀a b:bool. P(a) ⇒ P(b)"},
	})
	st := entry.Statement()
	head := st.Head()
	require.Same(t, head, st.Head())
	require.Empty(t, head.Stated().Conclusion().Frees(nil), "the declared variable is closed")
	require.Empty(t, st.key, "no key asked")
}

// A member states a closed theorem: a headline with hypotheses left of
// ⊢ registers, and its statement door panics naming the closed
// spelling, which reads at the sequent's own key — for a proved member
// and a card alike.
func TestStatement_SequentIsRefused(t *testing.T) {
	const sequent = "a:num, b:num, a ≤ b ⊢ a < suc(b)"
	fam := NewFamily("zz_statement_sequent", nil)
	for _, e := range []*ProofEntry{
		fam.Add(ProofEntry{Name: "Proved", Build: BuildSpec{Fn: statementStub.Fn, Headline: sequent}}),
		fam.Add(ProofEntry{Name: "Open", Build: fam.Card(sequent, "stated with a premise")}),
	} {
		var refusal string
		func() {
			defer func() { refusal, _ = recover().(string) }()
			e.Statement()
		}()
		prefix := "proof registry: " + e.Name + " states a sequent (hypotheses left of ⊢) — a member " +
			"states a closed theorem: ∀-bind its variables and ⇒ its premises: "
		require.True(t, strings.HasPrefix(refusal, prefix), "refusal: %q", refusal)
		closed := strings.TrimPrefix(refusal, prefix)
		require.NotContains(t, closed, "⊢")
		closedKey, err := e.KeyOfText(closed)
		require.NoError(t, err)
		sequentKey, err := e.KeyOfText(sequent)
		require.NoError(t, err)
		require.Equal(t, sequentKey, closedKey, "the closed spelling is the sequent's statement")
	}
}
