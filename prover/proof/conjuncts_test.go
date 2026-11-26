package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Conjuncts splits an assumed conjunction into one resident Fact per
// conjunct, each closed against the conjunction by normalization
// alone, and the parts drive the deduction as Haves would.
func TestConjuncts_SplitsAResidentConjunction(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	P := ext.WrapTerm(Var("P", TypeBool))
	Q := ext.WrapTerm(Var("Q", TypeBool))
	R := ext.WrapTerm(Var("R", TypeBool))
	// P ∧ Q ∧ R ⇒ Q ∧ P: the parts, recombined.
	sec := ctx.Section(prop.MakeProp(P.And(Q).And(R).Imply(Q.And(P)).Core()))
	sec.Do(Derive(func(a *Argument) {
		all := a.Assume()
		parts := a.Conjuncts(all, "P holds", "Q holds", "R holds")
		require.Len(t, parts, 3)
		p, q := parts[0], parts[1]
		pc, _ := p.BoundContent()
		qc, _ := q.BoundContent()
		require.True(t, pc.AlphaEquals(P.Core()), "first conjunct: %s", ext.PrintTerm(pc))
		require.True(t, qc.AlphaEquals(Q.Core()), "second conjunct: %s", ext.PrintTerm(qc))
		a.Show("Q and P are resident", By(Normalized, q, p))
	}))
	require.True(t, sec.Proved())
}

// The verb refuses a fact that is not a conjunction, and a label count
// that does not match the conjuncts.
func TestConjuncts_RefusesNonConjunctionsAndWrongLabelCounts(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	P := ext.WrapTerm(Var("P", TypeBool))
	Q := ext.WrapTerm(Var("Q", TypeBool))
	sec := ctx.Section(prop.MakeProp(P.And(Q).Imply(Q.And(P)).Core()))
	sec.Do(Derive(func(a *Argument) {
		both := a.Assume()
		requirePanicContains(t,
			"Argument.Conjuncts: the fact has 2 conjuncts and 1 label(s) were given — one per conjunct, in order; "+
				"the conjuncts as the fact states them (a cited instance is handed over in the instance normal form, so a "+
				"projection of a packed value is computed here):\n  1. P\n  2. Q",
			func() { a.Conjuncts(both, "only one") })
		parts := a.Conjuncts(both, "P", "Q")
		require.Panics(t, func() { a.Conjuncts(parts[0], "P alone") })
		a.Show("Q and P are resident", By(Normalized, parts[1], parts[0]))
	}))
	require.True(t, sec.Proved())
	_ = core.TypeA()
}

// A conjunct that is the goal's conclusion is refused with the repair
// named: the author wanted the whole fact, and closes with it.
func TestConjuncts_RefusesAConjunctThatIsTheGoal(t *testing.T) {
	env := makeStepTestEnv()
	P := ext.WrapTerm(Var("P", TypeBool))
	Q := ext.WrapTerm(Var("Q", TypeBool))
	// P ∧ Q ⇒ P: the first conjunct IS the goal.
	sec := NewScript(env).Section(prop.MakeProp(P.And(Q).Imply(P).Core()))
	require.PanicsWithValue(t,
		"Argument.Conjuncts: conjunct 1, \"P holds\", is the goal's conclusion — close with By(f) instead of splitting",
		func() {
			sec.Do(Derive(func(a *Argument) {
				all := a.Assume()
				a.Conjuncts(all, "P holds", "Q holds")
			}))
		})
}

// A conjunct already resident — the same statement as a hypothesis the
// leaf holds — is bound to that hypothesis, and only the others are
// installed: a fact that restates parts of what the context holds is
// split for the rest, its parts handed back in the conjunction's order.
func TestConjuncts_BindsAConjunctAlreadyResident(t *testing.T) {
	env := makeStepTestEnv()
	P := ext.WrapTerm(Var("P", TypeBool))
	Q := ext.WrapTerm(Var("Q", TypeBool))
	R := ext.WrapTerm(Var("R", TypeBool))
	requireBoundTo := func(t *testing.T, a *Argument, part Fact, want core.Term, resident Fact) {
		t.Helper()
		content, ok := part.BoundContent()
		require.True(t, ok)
		require.True(t, content.AlphaEquals(want), "conjunct: %s", ext.PrintTerm(content))
		at, err := part.handle.resolve(a.cur)
		require.NoError(t, err)
		held, err := resident.handle.resolve(a.cur)
		require.NoError(t, err)
		require.Equal(t, held, at, "the conjunct names the resident hypothesis")
	}
	t.Run("the first conjunct", func(t *testing.T) {
		// P ⇒ P ∧ Q ⇒ Q ∧ P.
		sec := NewScript(env).Section(prop.MakeProp(P.Imply(P.And(Q).Imply(Q.And(P))).Core()))
		sec.Do(Derive(func(a *Argument) {
			p := a.Assume()
			all := a.Assume()
			parts := a.Conjuncts(all, "P holds", "Q holds")
			require.Len(t, parts, 2)
			requireBoundTo(t, a, parts[0], P.Core(), p)
			require.Equal(t, 3, a.cur.Goal.NumHyps(), "Q alone joins P and P ∧ Q")
			a.Show("Q and P are resident", By(Normalized, parts[1], parts[0]))
		}))
		require.True(t, sec.Proved())
	})
	t.Run("a middle conjunct", func(t *testing.T) {
		// Q ⇒ P ∧ Q ∧ R ⇒ R ∧ Q ∧ P.
		sec := NewScript(env).Section(prop.MakeProp(Q.Imply(P.And(Q).And(R).Imply(R.And(Q).And(P))).Core()))
		sec.Do(Derive(func(a *Argument) {
			q := a.Assume()
			all := a.Assume()
			parts := a.Conjuncts(all, "P holds", "Q holds", "R holds")
			require.Len(t, parts, 3)
			requireBoundTo(t, a, parts[1], Q.Core(), q)
			pc, _ := parts[0].BoundContent()
			rc, _ := parts[2].BoundContent()
			require.True(t, pc.AlphaEquals(P.Core()), "first conjunct: %s", ext.PrintTerm(pc))
			require.True(t, rc.AlphaEquals(R.Core()), "third conjunct: %s", ext.PrintTerm(rc))
			require.Equal(t, 4, a.cur.Goal.NumHyps(), "P and R alone join Q and the conjunction")
			a.Show("R, Q and P are resident", By(Normalized, parts[2], parts[1], parts[0]))
		}))
		require.True(t, sec.Proved())
	})
	t.Run("every conjunct", func(t *testing.T) {
		// P ⇒ Q ⇒ P ∧ Q ⇒ Q ∧ P: the split installs nothing.
		sec := NewScript(env).Section(prop.MakeProp(P.Imply(Q.Imply(P.And(Q).Imply(Q.And(P)))).Core()))
		sec.Do(Derive(func(a *Argument) {
			p := a.Assume()
			q := a.Assume()
			all := a.Assume()
			parts := a.Conjuncts(all, "P holds", "Q holds")
			requireBoundTo(t, a, parts[0], P.Core(), p)
			requireBoundTo(t, a, parts[1], Q.Core(), q)
			require.Equal(t, 3, a.cur.Goal.NumHyps())
			a.Show("Q and P are resident", By(Normalized, parts[1], parts[0]))
		}))
		require.True(t, sec.Proved())
	})
	t.Run("a conjunct the split itself made resident", func(t *testing.T) {
		// P ∧ Q ∧ P ⇒ Q ∧ P: the third conjunct is the first's.
		sec := NewScript(env).Section(prop.MakeProp(P.And(Q).And(P).Imply(Q.And(P)).Core()))
		sec.Do(Derive(func(a *Argument) {
			all := a.Assume()
			parts := a.Conjuncts(all, "P holds", "Q holds", "P holds again")
			require.Len(t, parts, 3)
			requireBoundTo(t, a, parts[2], P.Core(), parts[0])
			require.Equal(t, 3, a.cur.Goal.NumHyps(), "P and Q join the conjunction once each")
			a.Show("Q and P are resident", By(Normalized, parts[1], parts[2]))
		}))
		require.True(t, sec.Proved())
	})
}
