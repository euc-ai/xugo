package omega

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// numeralStatement parses text over two index variables, a predicate, a
// family of sets and two propositions.
func numeralStatement(t *testing.T, text string, expected core.HolType) Term {
	t.Helper()
	num := dsl.NumType
	vars := map[string]core.HolType{
		"n": num, "m": num, "a": num, "b": num,
		"x": dsl.RealType, "y": dsl.RealType,
		"P": core.MakeFun(num, core.TypeBool()),
		"R": core.MakeFun(dsl.RealType, core.TypeBool()),
		"Q": core.TypeBool(), "S": core.TypeBool(),
	}
	r := dsl.ParseTermTextInScope(text, vars, &dsl.ParseScope{Consts: tParseConsts}, expected)
	require.Empty(t, r.Errors, "%s: %v", text, r.Errors)
	return r.Term
}

func allNumerals() ArithPolicy { return ArithPolicy{Nat: true, Real: true, Int: true} }

// readNumerals is text read at its numerals, printed; the kernel's
// equation is checked to run from the statement to its reading.
func readNumerals(t *testing.T, policy ArithPolicy, text string, expected core.HolType) string {
	t.Helper()
	term := numeralStatement(t, text, expected)
	w := NumeralReading(policy)(term)
	if w == nil {
		require.True(t, NumeralNormal(policy, term).Equals(term))
		return ext.PrintTerm(term)
	}
	require.Zero(t, w.NumHyps(), "%s: the reading stands on no hypothesis", text)
	l, r, ok := prop.MatchesEQ(w.Conclusion())
	require.True(t, ok, "%s: the reading is an equation", text)
	require.True(t, l.AlphaEquals(term), "%s: the equation's left side is the statement", text)
	require.True(t, r.AlphaEquals(NumeralNormal(policy, term)), "%s: NumeralNormal is the equation's right side", text)
	return ext.PrintTerm(r)
}

// A term with no variable is read at its value, wherever it stands.
func TestNumeralReading_ATermIsItsValue(t *testing.T) {
	for _, row := range []struct{ text, want string }{
		{"2 + 1", "3"},
		{"3 - 1", "2"},
		{"2 * 3", "6"},
		{"suc(2)", "3"},
		{"(1 + 1) + 1", "3"},
		{"(2 + 1) - (1 + 1)", "1"},
	} {
		require.Equal(t, row.want, readNumerals(t, allNumerals(), row.text, dsl.NumType), row.text)
	}
	for _, row := range []struct{ text, want string }{
		{"P(0 + 1)", "P(1)"},
		{"P(n + (2 + 1))", "P(n + 3)"},
		{"∀n:num. P(n) ⇒ P(1 + 1)", "∀n.(P(n) ⇒ P(2))"},
	} {
		require.Equal(t, row.want, readNumerals(t, allNumerals(), row.text, core.TypeBool()), row.text)
	}
}

// A comparison with no variable is ⊤ or ⊥, and the constant is folded
// out of what holds it.
func TestNumeralReading_AComparisonIsATruthConstant(t *testing.T) {
	for _, row := range []struct{ text, want string }{
		{"0 < 2", "⊤"},
		{"2 < 0", "⊥"},
		{"4 ≠ 0", "⊤"},
		{"1 + 1 = 2", "⊤"},
		{"0 ≤ 2 + 1", "⊤"},
		{"3 ≥ 5", "⊥"},
		{"0 < 2 ⇒ Q", "Q"},
		{"0 < 2 ∧ P(n)", "P(n)"},
		{"8 = 0 ∨ Q", "Q"},
		{"2 < 0 ⇒ Q", "⊤"},
		{"¬(0 ≤ 0 + 1)", "⊥"},
		{"P(COND(2 = 3, a, b))", "P(b)"},
		{"(0 < 1 ∧ 1 ≤ 2) ∧ P(n) ⇒ P(n + 1)", "P(n) ⇒ P(n + 1)"},
		{"∀n:num. P(n) ⇒ 0 ≤ 0", "⊤"},
		{"(∃n:num. P(n) ∧ 2 < 0) ∨ Q", "Q"},
	} {
		require.Equal(t, row.want, readNumerals(t, allNumerals(), row.text, core.TypeBool()), row.text)
	}
}

// The reading reaches ℝ's literals under the real bundle: a sum or a
// product of `&` literals is its value, and a comparison of numeral
// terms, quotients among them, is decided. A truncated difference, a
// negation and ℝ's difference are read through bundle theorems this package's tests have no
// stand-in for: the engine's TestBy_ReadsNumerals reads them under the
// corpus's bundles.
func TestNumeralReading_RealLiterals(t *testing.T) {
	SetRealLemmaBundle(&RealLemmaBundle{})
	t.Cleanup(func() { SetRealLemmaBundle(nil) })
	for _, row := range []struct{ text, want string }{
		{"R(&2 * &3)", "R(&6)"},
		{"R(&2 + &1)", "R(&3)"},
		{"&0 ≤ &1", "⊤"},
		{"&0 < &1 / &2", "⊤"},
		{"&1 / &2 < &1", "⊤"},
		{"&1 < &0", "⊥"},
		{"&0 < &1 ⇒ Q", "Q"},
	} {
		require.Equal(t, row.want, readNumerals(t, allNumerals(), row.text, core.TypeBool()), row.text)
	}
}

// What names a variable is not read, and neither is what the reading
// leaves to the arithmetic closer: a factorial, a power, a quotient of
// naturals, a quotient by zero. A statement that holds no numeral
// statement is not touched, its trivial equations and double negations
// included.
func TestNumeralReading_WhatIsNotRead(t *testing.T) {
	SetRealLemmaBundle(&RealLemmaBundle{})
	t.Cleanup(func() { SetRealLemmaBundle(nil) })
	for _, text := range []string{
		"0 ≤ n",
		"n ≤ n",
		"P((n + 1) + 1)",
		"P(0 + n)",
		"n + 1 < 3 ⇒ n < 3",
		"P(factorial(3))",
		"P(2 ^ 3)",
		"P(nat_div(4, 2))",
		"n = n",
		"¬¬Q",
		"Q ∧ S",
		"&0 ≤ x",
		"R(&1 / &0)",
		"&1 / &0 < &1",
	} {
		term := numeralStatement(t, text, core.TypeBool())
		require.Nil(t, NumeralReading(allNumerals())(term), "%s: nothing here is the reading's to read", text)
		require.False(t, SpellsNumeralStatement(term), text)
	}
}

// With ℕ's bundle not installed and no stand-in for it, there is nothing
// to evaluate with, and the reading reads nothing: the rung reads at
// every comparison, whatever the process has installed.
func TestNumeralReading_ReadsNothingWithNoBundle(t *testing.T) {
	bundle, standIn := natLemmaBundle, fabricatePlaceholder
	natLemmaBundle, fabricatePlaceholder = nil, nil
	t.Cleanup(func() { natLemmaBundle, fabricatePlaceholder = bundle, standIn })
	for _, text := range []string{"0 < 2 ⇒ Q", "P(0 + 1)", "P(suc(1))"} {
		term := numeralStatement(t, text, core.TypeBool())
		require.Nil(t, NumeralReading(allNumerals())(term), text)
		require.True(t, NumeralNormal(allNumerals(), term).Equals(term), text)
	}
}

// A type whose bundle the proof's policy withholds is not read.
func TestNumeralReading_FollowsThePolicy(t *testing.T) {
	SetRealLemmaBundle(&RealLemmaBundle{})
	t.Cleanup(func() { SetRealLemmaBundle(nil) })
	none := ArithPolicy{}
	for _, text := range []string{"0 < 2 ⇒ Q", "P(0 + 1)", "&0 ≤ &1"} {
		term := numeralStatement(t, text, core.TypeBool())
		require.Nil(t, NumeralReading(none)(term), text)
	}
	natOnly := ArithPolicy{Nat: true}
	require.Equal(t, "Q", readNumerals(t, natOnly, "0 < 2 ⇒ Q", core.TypeBool()))
	real := numeralStatement(t, "&0 ≤ &1 ⇒ Q", core.TypeBool())
	require.Nil(t, NumeralReading(natOnly)(real), "ℝ is not read under a policy that withholds its bundle")
}
