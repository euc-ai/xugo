package tactic

import (
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// ClosureSimpClauses names exactly the clauses simp_with reads as
// closure rules: an atom under a Horn antecedent (or its clause form),
// and nothing else — a plain equation, a conditional REWRITE (an
// equation under the antecedent) and a bare fact all pass unnamed.
func TestClosureSimpClauses(t *testing.T) {
	parse := func(text string) Prop {
		res := dsl.ParsePropText(text)
		require.Empty(t, res.Errors, "parse %q: %v", text, res.Errors)
		return res.Prop
	}
	for _, tc := range []struct {
		text string
		want int
	}{
		{"∀x:num. P(x) ⇒ Q(x)", 1},                         // Horn atom — the shape of FiniteRules' insert half
		{"∀x:num. ¬P(x) ∨ Q(x)", 1},                        // its clause form
		{"∀x:num. P(x) ⇒ f(x) = x", 0},                     // a conditional rewrite
		{"∀x:num. f(x) = x", 0},                            // a plain rewrite
		{"∀x:num. Q(x)", 0},                                // a bare fact
		{"Q(0) ∧ (∀x:num. P(x) ⇒ Q(suc(x)))", 1},           // a pack: the fact half passes, the atom half is named
		{"∀x:num. P(x) ⇒ (∀y:num. g(x, y) = y)", 0},        // Horn with an inner ∀ block, still an equation
		{"∀x:num. P(x) ⇒ (∀y:num. Q(y) ⇒ g(x, y) = y)", 0}, // a guard under the inner block: a two-segment telescope, an equation
		{"∀x:num. P(x) ⇒ (∀y:num. Q(y) ⇒ R(x, y))", 1},     // the same telescope ending in an atom: a closure rule
	} {
		got := ClosureSimpClauses(parse(tc.text))
		require.Len(t, got, tc.want, "%s: %v", tc.text, got)
	}
}
