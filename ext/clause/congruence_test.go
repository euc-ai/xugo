// congruence_test.go — the ground congruence-closure demodulation
// (Simplifies' order-gated same-size case; see Simplifies' doc):
//
//  1. a same-size ground compound equality rewrites in EXACTLY the
//     (size, Compare)-decreasing direction, whichever way it is
//     spelled — both spellings normalize a clause to the same
//     canonical atom, and the canonical form is a fixpoint (no
//     oscillation);
//  2. a ∀-quantified same-size equality keeps declining (the license
//     is ground-only);
//  3. the recorded _RuleSimplifies recipe reproduces the commuted-
//     orientation result at replay (Simplifies stays pure in its
//     inputs).
package clause

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

func TestGroundCongruenceDemodulation(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	z := Var("z", TypeA)
	m := Var("m", MakeFun(TypeA, MakeFun(TypeA, TypeA)))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	xz := m.Apply(x.Core()).Apply(z.Core()) // m(x, z)
	zx := m.Apply(z.Core()).Apply(x.Core()) // m(z, x)
	require.Equal(t, xz.Core().Size(), zx.Core().Size(), "fixture must be same-size")

	// The order-least spelling — the congruence class representative.
	canonical := xz.Core()
	if zx.Core().Compare(xz.Core()) < 0 {
		canonical = zx.Core()
	}

	eqAsWritten := MakeClause(xz.Eq(zx.Core()).Core()) // m(x,z) = m(z,x)
	eqCommuted := MakeClause(zx.Eq(xz.Core()).Core())  // m(z,x) = m(x,z)
	targetXZ := MakeClause(Q.Apply(xz.Core()).Core())  // Q(m(x,z))
	targetZX := MakeClause(Q.Apply(zx.Core()).Core())  // Q(m(z,x))

	wantConcl := Q.Apply(canonical).Core()
	for _, eq := range []*Clause{eqAsWritten, eqCommuted} {
		rewritten, kept := 0, 0
		for _, target := range []*Clause{targetXZ, targetZX} {
			u := eq.Simplifies(target)
			if target.EffectiveLit().AlphaEquals(wantConcl) {
				// Already canonical: the demodulation must DECLINE —
				// rewriting away from the representative would grow the
				// term in the order and oscillate.
				assert.Nil(t, u, "the canonical spelling must be a fixpoint")
				kept++
				continue
			}
			require.NotNil(t, u, "the non-canonical spelling must demodulate (eq %s)",
				eq.Term())
			assert.True(t, u.ConclClause().EffectiveLit().AlphaEquals(wantConcl),
				"demodulation must land on the class representative")
			rewritten++
		}
		assert.Equal(t, 1, rewritten, "exactly one spelling rewrites")
		assert.Equal(t, 1, kept, "exactly one spelling is already canonical")
	}

	// Interreduction: the two equation spellings normalize each other
	// to triviality (b=a rewritten by the oriented a-side collapses to
	// a reflexivity, an EquatesT conclusion the pump discards) or
	// decline — never a new fact, never a loop.
	if u := eqAsWritten.Simplifies(eqCommuted); u != nil {
		assert.True(t, u.ConclClause().EquatesT(),
			"an equation rewriting its own commuted twin must collapse it to triviality")
	}
	if u := eqCommuted.Simplifies(eqAsWritten); u != nil {
		assert.True(t, u.ConclClause().EquatesT(),
			"an equation rewriting its own commuted twin must collapse it to triviality")
	}
}

func TestGroundCongruence_QuantifiedStaysOut(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	x := Var("x", TypeA)
	z := Var("z", TypeA)
	m := Var("m", MakeFun(TypeA, MakeFun(TypeA, TypeA)))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	wideComm := MakeClause(
		ForAll(a.Core(), b.Core())(
			m.Apply(a.Core()).Apply(b.Core()).Eq(
				m.Apply(b.Core()).Apply(a.Core()).Core()).Core()).Core())
	target := MakeClause(Q.Apply(m.Apply(x.Core()).Apply(z.Core()).Core()).Core())

	assert.Nil(t, wideComm.Simplifies(target),
		"a ∀-quantified same-size equality must keep declining — the congruence license is ground-only")
}

func TestGroundCongruence_RecipeReplays(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	z := Var("z", TypeA)
	m := Var("m", MakeFun(TypeA, MakeFun(TypeA, TypeA)))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	xz := m.Apply(x.Core()).Apply(z.Core())
	zx := m.Apply(z.Core()).Apply(x.Core())

	// Pick the spelling whose STORED orientation is the growing one, so
	// the live derivation must have used the commuted attempt — the
	// replay-sensitive path.
	bigger, smaller := xz.Core(), zx.Core()
	if zx.Core().Compare(xz.Core()) > 0 {
		bigger, smaller = zx.Core(), xz.Core()
	}
	eq := MakeClause(WrapTerm(smaller).Eq(bigger).Core()) // stored orientation: smaller → bigger
	target := MakeClause(Q.Apply(bigger).Core())

	live := eq.Simplifies(target)
	require.NotNil(t, live, "the commuted orientation must rescue the badly-spelled equation")
	assert.True(t, live.ConclClause().EffectiveLit().AlphaEquals(Q.Apply(smaller).Core()))

	replayed := reconstructFromRecipe(live.ConclClause(), &deduceRecipe{
		rule:   _RuleSimplifies,
		inputs: []*Clause{eq, target},
	})
	require.NotNil(t, replayed, "the _RuleSimplifies recipe must reproduce the commuted result")
	assert.True(t, replayed.ConclClause().Equivalent(live.ConclClause()))
}
