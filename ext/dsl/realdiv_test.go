// Round-trip tests for `/` — ℝ's division infix. Same discipline as
// funcops_test.go: (1) the sugar parses; (2) it builds the same term as
// the applied `real_div(x, y)` spelling; (3) print → reparse round-trips;
// plus the precedence, and the ONE thing that makes this operator
// different from every other overloaded arith symbol.
//
// That difference: `/` has no num instance. Every other overloaded symbol
// (+ - * < ≤ > ≥ ∣ ..) is anchored at num and the other domains add
// instances for symbols num already spells, which is why isArithOperator
// could once be `natOperator(op) != nil`. ℕ's truncated division keeps its
// applied `nat_div(m, n)` spelling — giving `/` a second meaning at num would
// make one symbol denote two different operations — so membership is now
// the union over domains, and `m / n` at num is a typed refusal rather
// than a parse error about an unknown character.
package dsl

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// realDivScope supplies `real_div` by name the way a proof's
// ParseScope does, so the applied spelling can be compared against the
// `/` sugar.
func realDivScope() *ParseScope {
	return &ParseScope{ConstMetas: map[string]core.ConstTermMeta{"real_div": RealDivMeta}}
}

// assertRealDivFormsAgree parses the `/` form scope-less and the applied
// form in realDivScope, and requires the two conclusions to be α-equal.
func assertRealDivFormsAgree(t *testing.T, sugar, applied string) {
	t.Helper()
	sRes := ParsePropText(sugar)
	require.Empty(t, sRes.Errors,
		"sugar form %q failed to parse: %v", sugar, diagMessages(sRes.Errors))
	aRes := ParsePropTextInScope(applied, realDivScope())
	require.Empty(t, aRes.Errors,
		"applied form %q failed to parse: %v", applied, diagMessages(aRes.Errors))
	assert.True(t, sRes.Prop.Conclusion().AlphaEquals(aRes.Prop.Conclusion()),
		"`/` and `real_div(...)` must build α-equal terms; sugar=%s applied=%s",
		ext.FormatTermForParser(sRes.Prop.Conclusion()),
		ext.FormatTermForParser(aRes.Prop.Conclusion()))
}

func TestRealDiv_ParsesAsAppliedRealDiv(t *testing.T) {
	assertRealDivFormsAgree(t,
		"∀x y:real. x / y = x * real_inv(y)",
		"∀x y:real. real_div(x, y) = x * real_inv(y)")
}

func TestRealDiv_RoundTrip(t *testing.T) {
	assertRoundTrip(t, "∀x y:real. x / y = x * real_inv(y)")
}

// The round-trip above would also pass if nothing were printed as `/` at
// all, so pin the printer's half of the inverse pair explicitly — the
// parser and printer notation tables are uncoupled, and a re-pointed
// parser with an unchanged printer is a silent identity change across a
// round trip the corpus performs constantly.
func TestRealDiv_PrintsInfix(t *testing.T) {
	res := ParsePropText("∀x y:real. x / y = x / y")
	require.Empty(t, res.Errors, "parse failed: %v", diagMessages(res.Errors))
	printed := prop.FormatPropForParser(res.Prop)
	assert.Contains(t, printed, "/",
		"real_div must print with the infix sugar; got %s", printed)
	assert.NotContains(t, printed, "real_div(",
		"real_div must not print applied once it has an infix; got %s", printed)
}

// `/` shares `*`'s level and associates left, so `x / y * z` reads
// `(x / y) * z` — the ordinary convention.
func TestRealDiv_LeftAssociativeWithStar(t *testing.T) {
	assertRealDivFormsAgree(t,
		"∀x y z:real. x / y * z = x",
		"∀x y z:real. real_div(x, y) * z = x")
}

// …and it binds tighter than `+`, like `*`.
func TestRealDiv_TighterThanPlus(t *testing.T) {
	assertRealDivFormsAgree(t,
		"∀x y z:real. x + y / z = x",
		"∀x y z:real. x + real_div(y, z) = x")
}

// Bracketing. `/` and `*` share one left-associative level, so a
// right-nested quotient and a sum in numerator position both need
// brackets on the way out or the printed form reparses to a different
// term. The infix template itself emits none — bracketing is the
// caller's — so pin the two shapes that would expose a gap.
func TestRealDiv_BracketsRoundTrip(t *testing.T) {
	assertRoundTrip(t, "∀x y z:real. x / (y * z) = x")
	assertRoundTrip(t, "∀x y z:real. x / (y / z) = x")
	assertRoundTrip(t, "∀x y z:real. (x + y) / z = x")
}

// The deliberate refusal. ℕ has no `/`, so the symbol reaches the arith
// dispatch and is rejected THERE, naming the operand domain — not at the
// lexer as an unknown character, and never by silently resolving to nat_div.
func TestRealDiv_NoNumInstance(t *testing.T) {
	res := ParsePropText("∀m n:num. m / n = m")
	require.NotEmpty(t, res.Errors, "`m / n` at num must be rejected")
	assert.Contains(t, diagMessages(res.Errors)[0], "no instance for operand type",
		"the refusal must name the missing operand-domain instance; got %v",
		diagMessages(res.Errors))
}
