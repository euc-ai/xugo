package proof

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// byLadderFailure is the failure of a plain By over the resident
// hypotheses of the leaf text states, its leading antecedents assumed,
// run through the whole ladder — the conditioned rung, where the apply
// rung runs, included — in the proof scope is of; "" where it closes.
func byLadderFailure(t *testing.T, scope *ProofScope, text string, antecedents int) (failure string) {
	t.Helper()
	return ladderFailure(t, scope, text, antecedents, func(*_ByStep) {})
}

// ladderFailure is byLadderFailure of the By closer picks: the set
// driver's, the arithmetic closer's.
func ladderFailure(t *testing.T, scope *ProofScope, text string, antecedents int, closer func(*_ByStep)) (failure string) {
	t.Helper()
	res := dsl.ParsePropTextInScope(text, lawScope())
	require.Empty(t, res.Errors, "%v", res.Errors)
	sec := NewScript(makeStepTestEnv()).Section(res.Prop)
	for range antecedents {
		sec.Do(StripImp())
	}
	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	leaf := leaves[0].Goal
	step := residentByStep(makeStepTestEnv(), t.Context(), leaf)
	step.scope = scope
	closer(&step)
	defer func() {
		if r := recover(); r != nil {
			failure = fmt.Sprint(r)
		}
	}()
	step.apply(leaf)
	return ""
}

// A plain By reads a statement at its numerals where it compares
// statements: a guard that reads ⊤ asks for no supplier, a goal that
// reads ⊤ is closed, a hypothesis that reads ⊥ closes the leaf, and two
// statements one numeral term apart are one.
func TestBy_ReadsNumeralsOnTheRung(t *testing.T) {
	for _, row := range []struct {
		name, text  string
		antecedents int
	}{
		{"a guard that is a comparison of numerals", "(0 < 2 ⇒ Q) ⇒ Q", 1},
		{"a disequation of numerals as a guard", "(4 ≠ 0 ⇒ Q) ⇒ Q", 1},
		{"an equation of numerals as a guard", "(1 + 1 = 2 ⇒ Q) ⇒ Q", 1},
		{"a conjunctive guard one side of which is a comparison of numerals", "P(n) ⇒ (0 < 2 ∧ P(n) ⇒ Q) ⇒ Q", 2},
		{"a goal that is a comparison of numerals", "Q ⇒ 0 < 2", 1},
		{"a goal resident up to a numeral term", "P(0 + 1) ⇒ P(1)", 1},
		{"a guard resident up to a numeral term", "P(3) ⇒ (P(2 + 1) ⇒ Q) ⇒ Q", 2},
		{"a consequent that is the goal up to a numeral term", "P(n) ⇒ (P(n) ⇒ K(2 + 1)) ⇒ K(3)", 2},
		{"a law read at a numeral, its guards and its conclusion at sums",
			"P(3) ⇒ (P(2 + 1) ∧ 1 ≤ 2 + 1 ⇒ K(2 + 1)) ⇒ K(3)", 2},
		{"a hypothesis that is a false comparison of numerals", "2 < 0 ⇒ Q", 1},
		{"a disjunction one side of which is a false comparison of numerals", "(8 = 0 ∨ Q) ⇒ Q", 1},
		{"a quantified guard whose body is a comparison of numerals", "((∀i:num. P(i) ⇒ 0 ≤ 0) ⇒ Q) ⇒ Q", 1},
	} {
		require.Empty(t, byLadderFailure(t, nil, row.text, row.antecedents), row.name)
	}
}

// What names a variable is not read: a reflexive bound, a bound a law
// gives, a consequence of a resident bound stay the arithmetic closer's
// or a cited law's, and the failure still says so.
func TestBy_ReadsNoArithmeticOfVariables(t *testing.T) {
	for _, row := range []struct {
		name, text  string
		antecedents int
	}{
		{"a reflexive bound", "(n + 1 ≤ n + 1 ⇒ Q) ⇒ Q", 1},
		{"a bound a law gives", "(0 ≤ n ⇒ Q) ⇒ Q", 1},
		{"a consequence of a resident bound", "n + 1 < 3 ⇒ (n < 3 ⇒ Q) ⇒ Q", 2},
	} {
		failure := byLadderFailure(t, nil, row.text, row.antecedents)
		require.Contains(t, failure, "still guarded", "%s: the By must fail on the guard: %s", row.name, failure)
		require.Contains(t, failure, "arithmetic decides this guard", row.name)
	}
}

// The reading's rungs are the refuter's By's. The set driver's By has
// none and reads no numeral: its rung is run once, with no By as written
// tried before it.
func TestBy_TheSetDriverReadsNoNumeral(t *testing.T) {
	settac := func(step *_ByStep) { step.settac = true }
	require.NotEmpty(t, ladderFailure(t, nil, "(0 < 2 ⇒ Q) ⇒ Q", 1, settac))
	require.NotEmpty(t, ladderFailure(t, nil, "P(0 + 1) ⇒ P(1)", 1, settac))
	require.Empty(t, ladderFailure(t, nil, "0 < 2 ⇒ (0 < 2 ⇒ Q) ⇒ Q", 2, settac), "a listed fact supplies the guard as it always did")
}

// The match as spelled comes first: a law stated at `m + 1`, cited bare,
// is pinned from a goal spelled `2 + 1` as it was before the reading.
func TestBy_ALawAtASumIsPinnedFromTheGoalAsSpelled(t *testing.T) {
	require.Empty(t, byLadderFailure(t, nil, "P(2) ⇒ (∀m:num. P(m) ⇒ K(m + 1)) ⇒ K(2 + 1)", 2))
}

// The reading is the rung's: the leaf the refuter is handed keeps every
// hypothesis as written. A numeral fact the author listed is what the
// refuter uses once its own substitution has made the comparison — it
// does not compute — so a close that needs `3 ≠ 0` after `e = 3` closes
// with the fact listed, and the fact is not read away.
func TestBy_TheRefutersLeafKeepsAListedNumeralFact(t *testing.T) {
	require.Empty(t, byLadderFailure(t, nil, "f(0) = 3 ⇒ 3 ≠ 0 ⇒ (∀i:num. i ≠ 0 ⇒ P(i)) ⇒ P(f(0))", 3))
}

// On the spine a fact's guard is discharged from the context alone, and
// a guard that reads ⊤ needs none of it: the instance is brought down to
// its consequent with no fact listed.
func TestDischargeGuards_AGuardThatReadsTrueNeedsNoSupplier(t *testing.T) {
	res := dsl.ParsePropTextInScope("(0 < 2 ∧ 1 ≤ 2 + 1 ⇒ Q) ⇒ S", lawScope())
	require.Empty(t, res.Errors, "%v", res.Errors)
	sec := NewScript(makeStepTestEnv()).Section(res.Prop)
	sec.Do(StripImp())
	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	leaf := leaves[0]
	node, instance := dischargeGuards(leaf, leaf.Goal.Hyp(0), false, rungOpts{}, nil)
	require.Equal(t, "Q", ext.PrintTerm(instance), "the instance is its consequent once the guard is discharged")
	require.True(t, node.Goal.AnyHyp(instance.AlphaEquals), "and the consequent is resident")
}

// A law cited at its witnesses whose instance's guard is a comparison of
// numerals, or is resident up to a numeral term, takes its stated form:
// the By closes with no refutation and no plan, and replays from an
// empty store. Before the reading the first fell to its clause form on
// the guard `0 < 2`, and the second on a size `2 + 1` beside a resident
// size 3 — a law stated at `n + 1` and read at 2, against a goal spelled
// at 3.
func TestBy_AWitnessedLawReadAtANumeralClosesKeyless(t *testing.T) {
	requireKeyless(t, "a comparison of numerals beside a resident guard",
		runGuardSupply(t, []string{"zz_gs_finite(t)"}, "zz_gs_finite(zz_gs_insert(a, t))", residentAt(0),
			lawAt("∀b:num. ∀u:(num → bool). 0 < 2 ∧ zz_gs_finite(u) ⇒ zz_gs_finite(zz_gs_insert(b, u))", "a", "t")))
	requireKeyless(t, "a law stated at n + 1, read at 2",
		runGuardSupply(t, []string{"zz_gs_has_size(t, 3)"}, "zz_gs_ok(3)", residentAt(0),
			lawAt("∀n:num. ∀u:(num → bool). zz_gs_has_size(u, n + 1) ∧ 1 ≤ n + 1 ⇒ zz_gs_ok(n + 1)", "2", "t")))
}

// A fact in hand discharges its guards from the facts listed with it,
// and a guard that is a comparison of numerals from none: the instance
// comes down to its consequent with nothing listed. A fact that states
// that guard, listed, is not one the instance does not need — a proof
// written before the reading listed it because it had to, and it still
// states a guard of the instance.
func TestFactInHand_ANumeralGuardNeedsNoFactAndToleratesOne(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	const statement = "∀P R:num → bool. ∀u:num. (∀x. 0 < 2 ⇒ P(x) ∧ R(x)) ⇒ R(u) ∧ P(u)"
	unlisted := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(statement,
			func(a *Argument, P, R *ext.Expr[natSet], u *ext.Expr[ext.Nat], both Fact) {
				parts := a.Conjuncts(both.At(u), "P at u", "R at u")
				a.Show("both parts", By(parts[1], parts[0]))
			})
	})
	require.True(t, unlisted != nil && unlisted.Proved())
	listed := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(statement,
			func(a *Argument, P, R *ext.Expr[natSet], u *ext.Expr[ext.Nat], both Fact) {
				positive := a.Have("two is positive", "0 < 2", ByArith())
				parts := a.Conjuncts(GroupPremises(positive, both.At(u)), "P at u", "R at u")
				a.Show("both parts", By(parts[1], parts[0]))
			})
	})
	require.True(t, listed != nil && listed.Proved())
}

// The numerals are evaluated by the theorems of the arithmetic bundles,
// so a proof those rest on reads none: under a scope whose policy
// withholds ℕ's bundle the By is the By it was. A proof that may use the
// bundle has the reading, and a reading that closed something is on its
// record as a use of the bundle.
func TestBy_TheNumeralReadingFollowsTheProofsPolicy(t *testing.T) {
	installTestArith()
	const guarded = "(0 < 2 ⇒ Q) ⇒ Q"

	withheld := NewProofScope(scopeTestNatBlocked)
	require.False(t, withheld.ArithPolicy().Nat, "fixture: the scope's target is in ℕ's bundle's foundation")
	failure := byLadderFailure(t, withheld, guarded, 1)
	require.Contains(t, failure, "still guarded", "a proof ℕ's bundle rests on reads no numeral: %s", failure)
	require.Empty(t, withheld.Used(), "and records no use of it")

	allowed := NewProofScope(core.PropKey("prop_numeral_reading_free"))
	require.True(t, allowed.ArithPolicy().Nat, "fixture: the scope may use ℕ's bundle")
	require.Empty(t, byLadderFailure(t, allowed, guarded, 1))
	require.Equal(t, []string{CapabilityArithNat}, allowed.Used(), "the reading is a use of ℕ's bundle and of no other")

	unread := NewProofScope(core.PropKey("prop_numeral_reading_unread"))
	require.Empty(t, byLadderFailure(t, unread, "Q ⇒ (Q ⇒ S) ⇒ S", 2))
	require.Empty(t, unread.Used(), "a By that read no numeral records no use")
}

// The facts come first: a guard a listed fact states is supplied by that
// fact, as written or conjunct by conjunct, and the numeral reading is
// not asked — so a proof written before the reading closes by the steps
// it closed by, and records no use of the bundle.
func TestBy_AListedNumeralFactSuppliesItsGuardWithoutTheReading(t *testing.T) {
	installTestArith()
	for _, row := range []struct {
		name, text  string
		antecedents int
	}{
		{"the guard listed as written", "0 < 2 ⇒ (0 < 2 ⇒ Q) ⇒ Q", 2},
		{"a conjunctive guard listed conjunct by conjunct", "0 < 2 ⇒ P(n) ⇒ (0 < 2 ∧ P(n) ⇒ Q) ⇒ Q", 3},
	} {
		scope := NewProofScope(core.PropKey("prop_numeral_reading_listed_" + row.name))
		require.Empty(t, byLadderFailure(t, scope, row.text, row.antecedents), row.name)
		require.Empty(t, scope.Used(), "%s: the listed fact supplies the guard, and no bundle is used", row.name)
	}
}
