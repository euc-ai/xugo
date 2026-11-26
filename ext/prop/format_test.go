package prop

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
)

func checkFormat[T any](t *testing.T, s T, f string) {
	assert.Equal(t, fmt.Sprint(s), f)
}

func TestFormatProp(t *testing.T) {
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	q := Var("q", TypeBool)
	P := Var("P", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeBool, TypeA, TypeBool))

	checkFormat(t, testProp(P.Apply(x)), "⊢ P(x)")
	checkFormat(t, testProp(F, P.Apply(x)), "P(x)\n\t⊢ ⊥")
	checkFormat(t, testProp(P.Apply(x), q, R.Apply(q, y)), "q,\nR(q, y)\n\t⊢ P(x)")
}

// TestFormatPropForParserPairInfix pins the emit text path. emit's
// proof-text formatter is FormatPropForParser → ext.FormatTermForParser;
// the strings it produces are baked into generated proofs as
// MakePropText / SectionText / Case args and re-parsed at replay. A pair
// must render in the natural infix tuple form `(a, b)`, never the
// leading-comma prefix `,(a, b)` — the prefix is logically misleading and
// reads worse, and the infix form is what the parser now round-trips. The
// parse half of the round-trip is covered by ext/dsl's
// TestParsePairLiteralSyntax (kept there to avoid an ext/dsl↔ext/prop
// import cycle).
func TestFormatPropForParserPairInfix(t *testing.T) {
	a := Var("a", TypeA)
	b := Var("b", TypeB)
	comma := Const(ext.CommaConstMeta,
		MakeFun(TypeA, MakeFun(TypeB, ext.MakeProdType(TypeA, TypeB))))
	pair := comma.Apply(a, b) // the term whose old render was `,(a, b)`

	text := FormatPropForParser(testProp(pair.Eq(pair)))
	// Free vars now appear in a `name:type, … ⊢ …` decl prelude so
	// the parser can round-trip without "no type declaration" errors;
	// the pair's infix shape (the point of this pin) sits in the
	// conclusion after the turnstile.
	assert.Equal(t, "a:var:A, b:var:B ⊢ (a, b) = (a, b)", text,
		"FormatPropForParser must emit pairs infix; got %q", text)
	assert.NotContains(t, text, ",(",
		"emitted proof text must not carry the prefix `,(...)` form; got %q", text)
}

func TestPropLatex(t *testing.T) {
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	q := Var("q", TypeBool)
	P := Var("P", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeBool, TypeA, TypeBool))

	s := testProp(P.Apply(x))
	assert.Equal(t, LatexProp(s),
		"\\vdash{P}\\left({x}\\right)")
	s = testProp(P.Apply(x), q, R.Apply(q, y))
	assert.Equal(t, LatexProp(s),
		"&{q},\\\\&{R}\\left({q}, {y}\\right)\\\\&\\quad\\vdash{P}\\left({x}\\right)")
}
