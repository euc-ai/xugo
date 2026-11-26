// Tests for the pair-pattern lambda surface `λ(u:T, x:T). body` (parser
// desugar to the pattern_abstraction encoding, buildPatternAbs) and for the printer's
// shadow-binder α-rename (ext.RenameShadowedBinders) — together the
// print→parse round-trip story for pattern abstractions whose
// bodies reference an ambient variable named like the pattern_abstraction internal
// binder.
package dsl

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

var patternAbstractionTestMeta = core.MakeConstMeta(
	"pattern_abstraction", core.MakeFun(core.MakeFun(core.MakeVarType("A"), core.TypeBool()), core.MakeVarType("A")))

func patternAbstractionScope() *ParseScope {
	return &ParseScope{
		ConstMetas: map[string]core.ConstTermMeta{
			"pattern_abstraction": patternAbstractionTestMeta,
			",":                   ext.CommaConstMeta,
		},
	}
}

// mustParse parses text in the pattern_abstraction scope and fails the test on any
// diagnostic.
func mustParse(t *testing.T, text string) core.Prop {
	t.Helper()
	res := ParsePropTextInScope(text, patternAbstractionScope())
	require.Empty(t, res.Errors, "parse %q: %v", text, res.Errors)
	return res.Prop
}

// TestPatternLambdaParsesToPatternAbstractionEncoding checks the lowering shape: a
// pattern lambda builds pattern_abstraction(λf. ∀u x. f((u, x)) = body) with the ∀
// chain in pattern order and the equation head applied to the pair.
func TestPatternLambdaParsesToPatternAbstractionEncoding(t *testing.T) {
	p := mustParse(t,
		"∀h:((prod(num,bool) → num) → bool).h(λ(u:num, x:bool).u)")

	patternAbstraction := findConstOfName(p.Conclusion(), "pattern_abstraction")
	require.False(t, patternAbstraction.IsZero(), "lowered term must contain a pattern_abstraction const")
	comma := findConstOfName(p.Conclusion(), ",")
	require.False(t, comma.IsZero(), "lowered term must contain the pair const")

	// Round-trip: the printer re-sugars the canonical encoding, and the
	// re-parse must be α-equal.
	text := ext.FormatTermForParser(p.Conclusion())
	assert.Contains(t, text, "λ(u:num, x:bool)",
		"printer must render the encoding as a pattern lambda")
	assert.NotContains(t, text, "pattern_abstraction",
		"pattern sugar must hide the pattern_abstraction const")
	p2 := mustParse(t, text)
	assert.Equal(t, p.AlphaKey(), p2.AlphaKey())
}

// TestPatternLambdaNestedPattern exercises a nested pattern
// `λ((a, b), c). …` — the pair tree mirrors the nesting and the ∀ chain
// is the in-order leaf sequence.
func TestPatternLambdaNestedPattern(t *testing.T) {
	p := mustParse(t,
		"∀h:((prod(prod(num,num),bool) → num) → bool).h(λ((a:num, b:num), c:bool).b)")
	text := ext.FormatTermForParser(p.Conclusion())
	assert.Contains(t, text, "λ((a:num, b:num), c:bool)")
	p2 := mustParse(t, text)
	assert.Equal(t, p.AlphaKey(), p2.AlphaKey())
}

// TestPatternLambdaOperandIsBracketed: a pattern lambda prints as a λ,
// so an infix operand brackets it as it brackets any λ — on the left
// of `=` the unbracketed text reads the equation into the λ's body
// (pairs.PairedLambda's sugared print did not parse back to it). The
// name-faithful profile spells the application and adds nothing.
func TestPatternLambdaOperandIsBracketed(t *testing.T) {
	p := mustParse(t,
		"∀g:(num → (bool → num)).∀k:(prod(num,bool) → num).(λ(u:num, x:bool).g(u, x)) = k")

	for name, text := range map[string]string{
		"parser":  ext.FormatTermForParser(p.Conclusion()),
		"display": ext.PrintTerm(p.Conclusion()),
	} {
		assert.Contains(t, text, "(λ(u", "%s print brackets the operand: %s", name, text)
	}
	text := ext.FormatTermForParser(p.Conclusion())
	back := mustParse(t, text)
	assert.Equal(t, p.AlphaKey(), back.AlphaKey(), "the sugared print parses back: %s", text)

	faithful := ext.FormatTermForParserInConflictsNameFaithful(p.Conclusion(), nil)
	assert.Contains(t, faithful, "pattern_abstraction(λf")
	assert.NotContains(t, faithful, "((pattern_abstraction", "the name-faithful print spells the application unbracketed: %s", faithful)
	assert.Equal(t, p.AlphaKey(), mustParse(t, faithful).AlphaKey())
}

// TestPatternLambdaBodyRefsOuterSameName is the capture regression: the
// pattern body references an outer variable named `f`, the conventional
// name of the pattern_abstraction internal binder. The desugar must pick a FRESH
// internal binder so the outer `f` stays free.
func TestPatternLambdaBodyRefsOuterSameName(t *testing.T) {
	p := mustParse(t,
		"∀f:(var:A → var:B).∀p:((var:A → var:B) → bool)."+
			"∀h:((prod(num,num) → bool) → bool).h(λ(u:num, x:num).p(f))")

	patternAbstraction := findConstOfName(p.Conclusion(), "pattern_abstraction")
	require.False(t, patternAbstraction.IsZero())

	// Round-trip α-stability proves no capture happened in either
	// direction.
	text := ext.FormatTermForParser(p.Conclusion())
	p2 := mustParse(t, text)
	assert.Equal(t, p.AlphaKey(), p2.AlphaKey())
}

// TestPatternLambdaDuplicateBinderRejected — pattern components must be
// distinct.
func TestPatternLambdaDuplicateBinderRejected(t *testing.T) {
	res := ParsePropTextInScope(
		"∀h:((prod(num,num) → num) → bool).h(λ(u:num, u:num).u)", patternAbstractionScope())
	require.NotEmpty(t, res.Errors)
	assert.Contains(t, res.Errors[0].Message, "duplicate binder")
}

// TestParenGroupedMultiBinderStillParses — the pre-existing
// `λ(x:T) (y:T). body` form must be unaffected by the pattern probe (no
// comma in the group → not a pattern).
func TestParenGroupedMultiBinderStillParses(t *testing.T) {
	p := mustParse(t,
		"∀h:((num → (num → num)) → bool).h(λ(x:num) (y:num). x)")
	abs, ok := p.Conclusion().(core.AppliedTerm)
	require.True(t, ok)
	_ = abs
	// No pattern_abstraction involved — plain curried lambdas.
	assert.True(t, findConstOfName(p.Conclusion(), "pattern_abstraction").IsZero())
}

// buildShadowedPatternAbstractionFragment constructs the failure
// shape of a paired λ under a λ directly at the kernel level: an outer λf:(A→B) whose body is a
// pattern_abstraction spec whose internal binder is ALSO named f (legal — kernel var
// identity is (name, type)) and whose equation body references the
// OUTER f. Printed bare, `p(f, x)` would be captured by the inner
// binder; the printer must α-rename or pattern-sugar its way out.
func buildShadowedPatternAbstractionFragment(t *testing.T) core.Term {
	t.Helper()
	tyA, tyB := core.MakeVarType("A"), core.MakeVarType("B")
	tyAB := core.MakeFun(tyA, tyB)
	prodCP := ext.MakeProdType(NumType, core.TypeBool())
	specTy := core.MakeFun(prodCP, core.TypeBool())

	fOuter := core.Var("f", tyAB)
	fInner := core.Var("f", specTy)
	u := core.Var("u", NumType)
	x := core.Var("x", core.TypeBool())
	p := core.Var("p", core.MakeFun(tyAB, core.MakeFun(core.TypeBool(), core.TypeBool())))

	pair, err := buildAppViaMeta(newTypeEnv(), ext.CommaConstMeta, []core.Term{u, x})
	require.NoError(t, err)
	eq := core.Eq(core.Apply(fInner, pair), core.Apply(core.Apply(p, fOuter), x))
	spec := core.Abs(fInner, ext.ForAll(u, x)(eq))
	patternAbstraction, err := buildAppViaMeta(newTypeEnv(), patternAbstractionTestMeta, []core.Term{spec})
	require.NoError(t, err)
	return core.Abs(fOuter, patternAbstraction).Core()
}

// TestShadowedPatternAbstractionPrintParseRoundTrip is the end-to-end regression for
// the 87564bc46 failure class: the kernel-level shadowed term must
// print to parseable text (pattern sugar hides the internal binder; the
// outer f reference survives) and re-parse α-equal.
func TestShadowedPatternAbstractionPrintParseRoundTrip(t *testing.T) {
	term := buildShadowedPatternAbstractionFragment(t)
	text := ext.FormatTermForParser(term)
	assert.Contains(t, text, "λ(u:num, x:bool)")

	// Embed under binders declaring the frees so the fragment parses as
	// a prop conclusion.
	full := "∀p:((var:A → var:B) → (bool → bool)).∀g:(((var:A → var:B) → (prod(num,bool) → bool)) → bool).g(" + text + ")"
	res := ParsePropTextInScope(full, patternAbstractionScope())
	require.Empty(t, res.Errors, "round-trip parse: %v", res.Errors)

	gVar := core.Var("g", core.MakeFun(core.MakeFun(core.MakeFun(core.MakeVarType("A"), core.MakeVarType("B")), core.MakeFun(ext.MakeProdType(NumType, core.TypeBool()), core.TypeBool())), core.TypeBool()))
	pVar := core.Var("p", core.MakeFun(core.MakeFun(core.MakeVarType("A"), core.MakeVarType("B")), core.MakeFun(core.TypeBool(), core.TypeBool())))
	expected := core.MakeProp(ext.ForAll(pVar, gVar)(core.Apply(gVar, term)))
	assert.Equal(t, expected.AlphaKey(), res.Prop.AlphaKey())
}

// TestRenameShadowedBinders_NonCanonicalShadow covers the A-fix on its
// own, without the pattern_abstraction sugar: a plain λ binder shadowing a same-named
// different-typed outer var. The printer must rename the INNER binder
// (α-neutral, variant chosen by utils.NextName) so the outer reference
// survives the round trip.
func TestRenameShadowedBinders_NonCanonicalShadow(t *testing.T) {
	tyAB := core.MakeFun(core.MakeVarType("A"), core.MakeVarType("B"))
	fOuter := core.Var("f", tyAB)
	fInner := core.Var("f", core.MakeFun(NumType, core.TypeBool()))
	p := core.Var("p", core.MakeFun(tyAB, core.TypeBool()))
	// λf:(num→bool). p(f_outer)  — inner f unused except as the binder.
	inner := core.Abs(fInner, core.Apply(p, fOuter))
	term := core.Abs(fOuter, inner).Core()

	text := ext.FormatTermForParser(term)
	assert.Contains(t, text, "λf:(var:A → var:B)",
		"outer binder keeps its name: %s", text)
	assert.NotContains(t, text, "λf:(num → bool)",
		"inner binder must print under a variant name: %s", text)

	full := "∀p:((var:A → var:B) → bool).∀h:(((var:A → var:B) → ((num → bool) → bool)) → bool).h(" + text + ")"
	res := ParsePropTextInScope(full, patternAbstractionScope())
	require.Empty(t, res.Errors, "renamed text must parse: %v", res.Errors)

	hVar := core.Var("h", core.MakeFun(core.MakeFun(tyAB, core.MakeFun(core.MakeFun(NumType, core.TypeBool()), core.TypeBool())), core.TypeBool()))
	pVar := core.Var("p", core.MakeFun(tyAB, core.TypeBool()))
	expected := core.MakeProp(ext.ForAll(pVar, hVar)(core.Apply(hVar, term)))
	assert.Equal(t, expected.AlphaKey(), res.Prop.AlphaKey(),
		"rename is α-neutral and capture-free")
}

// TestRenameShadowedBinders_NoCollisionPointerStable — terms without a
// same-name/different-type pair must come back pointer-identical (the
// cheap gate).
func TestRenameShadowedBinders_NoCollisionPointerStable(t *testing.T) {
	x := core.Var("x", NumType)
	y := core.Var("y", NumType)
	term := core.Abs(x, core.Abs(y, core.Eq(x, y))).Core()
	assert.True(t, any(term) == any(ext.RenameShadowedBinders(term).Core()))
}

// TestRenameShadowedBinders_NameFaithfulProfile — the name-faithful
// profile applies the same rename: a collision term has no faithful
// text, so its inner binder prints under the variant and the text
// re-parses α-equal instead of the profile producing no text at all.
func TestRenameShadowedBinders_NameFaithfulProfile(t *testing.T) {
	tyAB := core.MakeFun(core.MakeVarType("A"), core.MakeVarType("B"))
	fOuter := core.Var("f", tyAB)
	fInner := core.Var("f", core.MakeFun(NumType, core.TypeBool()))
	p := core.Var("p", core.MakeFun(tyAB, core.TypeBool()))
	term := core.Abs(fOuter, core.Abs(fInner, core.Apply(p, fOuter))).Core()

	text := ext.FormatTermForParserInConflictsNameFaithful(term, nil)
	assert.Contains(t, text, "λf:(var:A → var:B)", "outer binder keeps its name: %s", text)
	assert.NotContains(t, text, "λf:(num → bool)", "inner binder prints under a variant: %s", text)

	full := "∀p:((var:A → var:B) → bool).∀h:(((var:A → var:B) → ((num → bool) → bool)) → bool).h(" + text + ")"
	res := ParsePropTextInScope(full, patternAbstractionScope())
	require.Empty(t, res.Errors, "renamed text must parse: %v", res.Errors)
	hVar := core.Var("h", core.MakeFun(core.MakeFun(tyAB, core.MakeFun(core.MakeFun(NumType, core.TypeBool()), core.TypeBool())), core.TypeBool()))
	pVar := core.Var("p", core.MakeFun(tyAB, core.TypeBool()))
	expected := core.MakeProp(ext.ForAll(pVar, hVar)(core.Apply(hVar, term)))
	assert.Equal(t, expected.AlphaKey(), res.Prop.AlphaKey(), "rename is α-neutral and capture-free")

	// No collision: the profile stays exact, pointer-identical input.
	x := core.Var("x", NumType)
	plain := core.Abs(x, core.Eq(x, x)).Core()
	assert.Equal(t, ext.FormatTermForParser(plain), ext.FormatTermForParserInConflictsNameFaithful(plain, nil))
}
