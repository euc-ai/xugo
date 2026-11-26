// Round-trip tests for the set-theory surface: ∈/∉/⊆/⊊/∪/∩/∖ infix, ∅/𝕌
// nullary atoms, ⋃/⋂ unary big-op prefixes, `{a₁, …, aₙ}` enumeration,
// `{x | φ(x)}` set-builder identity form. Each assertion follows the same
// discipline as the pair-constructor tests: (1) new-form parses without
// diagnostics; (2) new-form and old-form (set_member/subset/… const names)
// build the same term (AlphaEquals); (3) print → reparse round-trips.
package dsl

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// assertBothParseAndAlphaEqual is the shared helper: parse `newForm` and
// `oldForm`, require both to build, and assert the two conclusions are
// α-equal. Used across every set-theory infix / atom test.
func assertBothParseAndAlphaEqual(t *testing.T, newForm, oldForm string) {
	t.Helper()
	nRes := ParsePropText(newForm)
	require.Empty(t, nRes.Errors,
		"new-form %q failed to parse: %v", newForm, diagMessages(nRes.Errors))
	require.NotNil(t, nRes.Prop)
	oRes := ParsePropText(oldForm)
	require.Empty(t, oRes.Errors,
		"old-form %q failed to parse: %v", oldForm, diagMessages(oRes.Errors))
	require.NotNil(t, oRes.Prop)
	assert.True(t, nRes.Prop.Conclusion().AlphaEquals(oRes.Prop.Conclusion()),
		"new-form and old-form should build α-equal terms; new=%s old=%s",
		ext.FormatTermForParser(nRes.Prop.Conclusion()),
		ext.FormatTermForParser(oRes.Prop.Conclusion()))
}

// assertRoundTrip parses `text`, prints via FormatTermForParser, and
// re-parses — the two builds must be α-equal.
func assertRoundTrip(t *testing.T, text string) {
	t.Helper()
	r1 := ParsePropText(text)
	require.Empty(t, r1.Errors, "initial parse of %q failed: %v",
		text, diagMessages(r1.Errors))
	require.NotNil(t, r1.Prop)
	printed := prop.FormatPropForParser(r1.Prop)
	r2 := ParsePropText(printed)
	require.Empty(t, r2.Errors,
		"round-trip re-parse of %q (printed as %q) failed: %v",
		text, printed, diagMessages(r2.Errors))
	require.NotNil(t, r2.Prop)
	assert.True(t, r1.Prop.Conclusion().AlphaEquals(r2.Prop.Conclusion()),
		"round-trip term must be α-equal; original=%q printed=%q reparsed=%s",
		text, printed, ext.FormatTermForParser(r2.Prop.Conclusion()))
}

func TestSetOps_Membership(t *testing.T) {
	assertBothParseAndAlphaEqual(t,
		"∀s:(var:A → bool).∀x:var:A.(x ∈ s)",
		"∀s:(var:A → bool).∀x:var:A.set_member(x, s)")
	assertRoundTrip(t, "∀s:(var:A → bool).∀x:var:A.(x ∈ s)")
}

// TestSetOps_NonMembership — `x ∉ s` builds ¬(x ∈ s), at the same
// relational level as `∈`, and the printer writes ¬(x ∈ s) back as
// `x ∉ s`, bracketed as an operand the way `≠` is.
func TestSetOps_NonMembership(t *testing.T) {
	assertBothParseAndAlphaEqual(t,
		"∀s:(var:A → bool).∀x:var:A.(x ∉ s)",
		"∀s:(var:A → bool).∀x:var:A.¬(x ∈ s)")
	assertBothParseAndAlphaEqual(t,
		"∀s:(var:A → bool).∀x:var:A.(x ∉ s)",
		"∀s:(var:A → bool).∀x:var:A.¬set_member(x, s)")
	assertBothParseAndAlphaEqual(t,
		"∀s:(var:A → bool).∀t:(var:A → bool).∀x:var:A.(x ∉ s ∪ t)",
		"∀s:(var:A → bool).∀t:(var:A → bool).∀x:var:A.¬set_member(x, union(s, t))")
	assertBothParseAndAlphaEqual(t,
		"∀x:num.(x ∉ ∅)",
		"∀x:num.¬(x ∈ ∅)")
	for _, text := range []string{
		"∀s:(var:A → bool).∀x:var:A.(x ∉ s)",
		"∀s:(var:A → bool).∀x:var:A.∀p:bool.((x ∉ s) = p)",
		"∀s:(var:A → bool).∀x:var:A.∀y:var:A.(x ∉ s ∧ y ∈ s ⇒ ¬(x = y))",
	} {
		assertRoundTrip(t, text)
	}
	res := ParsePropText("∀s:(var:A → bool).∀x:var:A.¬(x ∈ s)")
	require.Empty(t, res.Errors, "%v", diagMessages(res.Errors))
	assert.Equal(t, "∀s:(var:A → bool).∀x:var:A.(x ∉ s)", prop.FormatPropForParser(res.Prop))
	assert.Contains(t, ext.FormatTerm(res.Prop.Conclusion(), true), "{x}\\notin{s}")
	res = ParsePropText("∀s:(var:A → bool).∀x:var:A.∀p:bool.(¬(x ∈ s) = p)")
	require.Empty(t, res.Errors, "%v", diagMessages(res.Errors))
	assert.Contains(t, prop.FormatPropForParser(res.Prop), "((x ∉ s) ⇔ p)")
	assert.NotEmpty(t, ParsePropText("∀x:num.(x ∉ 3)").Errors, "a num partner is not a set")
	assert.NotEmpty(t, ParsePropText("∀s:(num → bool).∀t:((num → bool) → bool).∀x:num.(x ∉ s ∉ t)").Errors,
		"∉ is non-associative, as ∈ is")
}

// TestSetOps_BareNullaryTakesInstanceFromPartner — a bare ∅/𝕌 under a
// set infix is typed by its partner operand, at a concrete type and at
// a type variable that is NOT the surface meta's own letter A. The
// letter-A forms parse regardless of imposition (the generic instance
// happens to coincide), which is why they are not the witnesses here.
func TestSetOps_BareNullaryTakesInstanceFromPartner(t *testing.T) {
	for _, text := range []string{
		"∀x:num.¬(x ∈ ∅)",
		"∀y:var:B.(y ∈ 𝕌)",
		"∀s:(var:B → bool).(s ⊆ ∅)",
		"∀s:(num → bool).((s ∪ ∅) = s)",
		"∀s:(num → bool).((∅ ∩ s) = ∅)",
		"∀s:(var:B → bool).((s ∖ ∅) = s)",
		"∀x:num.∀s:(num → bool).(x ∈ (s ∪ ∅))",
	} {
		res := ParsePropText(text)
		require.Empty(t, res.Errors, "%q: %v", text, diagMessages(res.Errors))
		assertRoundTrip(t, text)
	}
	assertBothParseAndAlphaEqual(t,
		"∀x:num.¬(x ∈ ∅)",
		"∀x:num.¬set_member(x, empty_set⟨A:num⟩)")
	// A genuine mismatch is still one.
	res := ParsePropText("∀x:num.(x ∈ 3)")
	assert.NotEmpty(t, res.Errors, "a num partner is not a set")
}

func TestSetOps_Subset(t *testing.T) {
	assertBothParseAndAlphaEqual(t,
		"∀s:(var:A → bool).∀t:(var:A → bool).(s ⊆ t)",
		"∀s:(var:A → bool).∀t:(var:A → bool).subset(s, t)")
	assertRoundTrip(t, "∀s:(var:A → bool).∀t:(var:A → bool).(s ⊆ t)")
}

func TestSetOps_PSubset(t *testing.T) {
	assertBothParseAndAlphaEqual(t,
		"∀s:(var:A → bool).∀t:(var:A → bool).(s ⊊ t)",
		"∀s:(var:A → bool).∀t:(var:A → bool).proper_subset(s, t)")
	assertRoundTrip(t, "∀s:(var:A → bool).∀t:(var:A → bool).(s ⊊ t)")
}

func TestSetOps_Union(t *testing.T) {
	assertBothParseAndAlphaEqual(t,
		"∀s:(var:A → bool).∀t:(var:A → bool).(s ∪ t = s ∪ t)",
		"∀s:(var:A → bool).∀t:(var:A → bool).(union(s, t) = union(s, t))")
	assertRoundTrip(t, "∀s:(var:A → bool).∀t:(var:A → bool).(s ∪ t = s ∪ t)")
}

func TestSetOps_Inter(t *testing.T) {
	assertBothParseAndAlphaEqual(t,
		"∀s:(var:A → bool).∀t:(var:A → bool).(s ∩ t = s ∩ t)",
		"∀s:(var:A → bool).∀t:(var:A → bool).(intersection(s, t) = intersection(s, t))")
	assertRoundTrip(t, "∀s:(var:A → bool).∀t:(var:A → bool).(s ∩ t = s ∩ t)")
}

func TestSetOps_Diff(t *testing.T) {
	assertBothParseAndAlphaEqual(t,
		"∀s:(var:A → bool).∀t:(var:A → bool).(s ∖ t = s ∖ t)",
		"∀s:(var:A → bool).∀t:(var:A → bool).(set_difference(s, t) = set_difference(s, t))")
	assertRoundTrip(t, "∀s:(var:A → bool).∀t:(var:A → bool).(s ∖ t = s ∖ t)")
}

func TestSetOps_Precedence_InterTighterThanUnion(t *testing.T) {
	// `s ∪ t ∩ u` must parse as `s ∪ (t ∩ u)` — intersection binds tighter.
	assertBothParseAndAlphaEqual(t,
		"∀s:(var:A → bool).∀t:(var:A → bool).∀u:(var:A → bool).(s ∪ t ∩ u = s ∪ t ∩ u)",
		"∀s:(var:A → bool).∀t:(var:A → bool).∀u:(var:A → bool).(union(s, intersection(t, u)) = union(s, intersection(t, u)))")
}

func TestSetOps_Precedence_MembershipLoosestOfAll(t *testing.T) {
	// `x ∈ s ∪ t` must parse as `x ∈ (s ∪ t)`.
	assertBothParseAndAlphaEqual(t,
		"∀s:(var:A → bool).∀t:(var:A → bool).∀x:var:A.(x ∈ s ∪ t)",
		"∀s:(var:A → bool).∀t:(var:A → bool).∀x:var:A.set_member(x, union(s, t))")
}

// TestSetOps_MixedInstanceInfixExemption is the decisive check for the
// conflict-annotation exemption of the six binary set ops. set_basic.InImage's goal
// carries set_member at two distinct element-type instances in one prop —
// `y ∈ image(f,s)` (set_member⟨A:B⟩) and `x ∈ s` (set_member⟨A:A⟩). Before the exemption the
// printer put set_member in the conflict set and fell back to the annotated prefix
// form `set_member⟨A:var:B⟩(...)`. After the exemption it must (1) render both as the
// `∈` infix with NO `set_member⟨` prefix anywhere, and (2) still round-trip α-equal —
// the parser re-infers each instance from the operands, so the type-erasing
// infix form is sound. Both halves are asserted; (2) is the load-bearing one.
func TestSetOps_MixedInstanceInfixExemption(t *testing.T) {
	// InImage's goal shape: set_member at element types B (y ∈ image(f,s)) and A (x ∈ s).
	// image is declared in the prop's hyp scope (no registry in a bare parse).
	text := "image : ((var:A → var:B) → (var:A → bool) → (var:B → bool)) ⊢ " +
		"∀s:(var:A → bool).∀f:(var:A → var:B).∀y:var:B." +
		"((∃x:var:A.((y = f(x)) ∧ (x ∈ s))) ⇔ (y ∈ image(f, s)))"
	r1 := ParsePropText(text)
	require.Empty(t, r1.Errors, "parse of %q failed: %v", text, diagMessages(r1.Errors))
	require.NotNil(t, r1.Prop)

	printed := prop.FormatPropForParser(r1.Prop)

	// (1) behavior change: infix ∈ surfaces even under the mixed-instance
	// conflict; the annotated prefix fallback `set_member⟨` must NOT appear.
	assert.Contains(t, printed, "∈", "mixed-instance set_member should print as ∈ infix; got %q", printed)
	assert.NotContains(t, printed, "set_member⟨",
		"mixed-instance set_member must not fall back to the annotated prefix form; got %q", printed)

	// (2) soundness: print → reparse is α-equal despite the two set_member instances
	// sharing the bare `∈` symbol. This is what would break if the parser
	// could not re-infer A from the operands.
	r2 := ParsePropText(printed)
	require.Empty(t, r2.Errors,
		"round-trip re-parse of printed %q failed: %v", printed, diagMessages(r2.Errors))
	require.NotNil(t, r2.Prop)
	assert.True(t, r1.Prop.Conclusion().AlphaEquals(r2.Prop.Conclusion()),
		"mixed-instance ∈ round-trip must be α-equal; printed=%q reparsed=%s",
		printed, ext.FormatTermForParser(r2.Prop.Conclusion()))
}

// TestSetOps_MixedInstanceBinaryOps extends the exemption check to ⊆/∪/∩/∖ at
// two element-type instances in one prop, mirroring the set_member case: infix
// surfaces (no annotated prefix) and the print→reparse stays α-equal.
func TestSetOps_MixedInstanceBinaryOps(t *testing.T) {
	// union at A (s ∪ t) and at B (u ∪ v) plus subset at both — one prop,
	// four distinct polymorphic instances across two op names.
	text := "∀s:(var:A → bool).∀t:(var:A → bool).∀u:(var:B → bool).∀v:(var:B → bool)." +
		"(((s ∪ t) ⊆ s) ∧ ((u ∪ v) ⊆ u))"
	r1 := ParsePropText(text)
	require.Empty(t, r1.Errors, "parse of %q failed: %v", text, diagMessages(r1.Errors))
	require.NotNil(t, r1.Prop)

	printed := prop.FormatPropForParser(r1.Prop)
	assert.NotContains(t, printed, "union⟨",
		"mixed-instance union must stay infix; got %q", printed)
	assert.NotContains(t, printed, "subset⟨",
		"mixed-instance subset must stay infix; got %q", printed)

	r2 := ParsePropText(printed)
	require.Empty(t, r2.Errors,
		"round-trip re-parse of printed %q failed: %v", printed, diagMessages(r2.Errors))
	require.NotNil(t, r2.Prop)
	assert.True(t, r1.Prop.Conclusion().AlphaEquals(r2.Prop.Conclusion()),
		"mixed-instance binary-op round-trip must be α-equal; printed=%q reparsed=%s",
		printed, ext.FormatTermForParser(r2.Prop.Conclusion()))
}

// TestSetOps_MixedInstanceBigOps extends the exemption to the unary big-op
// prefixes ⋃/⋂ at two element-type instances in one prop. big_union/big_intersection write
// their single operand verbatim, so like the infix ops they must surface the
// prefix symbol (no annotated `big_union⟨…⟩`) and round-trip α-equal even when
// the same op name appears at distinct instances.
func TestSetOps_MixedInstanceBigOps(t *testing.T) {
	// ⋃ at element type A (s : (A→bool)→bool) and at B (u : (B→bool)→bool);
	// ⋂ likewise — one prop, both big-op names at two instances each.
	text := "∀s:((var:A → bool) → bool).∀u:((var:B → bool) → bool)." +
		"((⋃s = ⋃s) ∧ ((⋂s = ⋃s) ∧ ((⋃u = ⋃u) ∧ (⋂u = ⋃u))))"
	r1 := ParsePropText(text)
	require.Empty(t, r1.Errors, "parse of %q failed: %v", text, diagMessages(r1.Errors))
	require.NotNil(t, r1.Prop)

	printed := prop.FormatPropForParser(r1.Prop)
	assert.Contains(t, printed, "⋃", "mixed-instance big_union should print as ⋃; got %q", printed)
	assert.NotContains(t, printed, "big_union⟨",
		"mixed-instance big_union must stay prefix; got %q", printed)
	assert.NotContains(t, printed, "big_intersection⟨",
		"mixed-instance big_intersection must stay prefix; got %q", printed)

	r2 := ParsePropText(printed)
	require.Empty(t, r2.Errors,
		"round-trip re-parse of printed %q failed: %v", printed, diagMessages(r2.Errors))
	require.NotNil(t, r2.Prop)
	assert.True(t, r1.Prop.Conclusion().AlphaEquals(r2.Prop.Conclusion()),
		"mixed-instance big-op round-trip must be α-equal; printed=%q reparsed=%s",
		printed, ext.FormatTermForParser(r2.Prop.Conclusion()))
}

func TestSetOps_Empty(t *testing.T) {
	assertBothParseAndAlphaEqual(t,
		"∀x:var:A.(x ∈ ∅)",
		"∀x:var:A.set_member(x, empty_set)")
	assertRoundTrip(t, "∀x:var:A.(x ∈ ∅)")
}

func TestSetOps_EmptyBraces(t *testing.T) {
	// `{}` also lowers to empty_set — printer canonicalizes to ∅.
	assertBothParseAndAlphaEqual(t,
		"∀x:var:A.(x ∈ {})",
		"∀x:var:A.set_member(x, empty_set)")
}

func TestSetOps_Univ(t *testing.T) {
	assertBothParseAndAlphaEqual(t,
		"∀x:var:A.(x ∈ 𝕌)",
		"∀x:var:A.set_member(x, universe)")
	assertRoundTrip(t, "∀x:var:A.(x ∈ 𝕌)")
}

func TestSetOps_BigUnion(t *testing.T) {
	assertBothParseAndAlphaEqual(t,
		"∀S:((var:A → bool) → bool).⋃(S) = ⋃(S)",
		"∀S:((var:A → bool) → bool).big_union(S) = big_union(S)")
	assertRoundTrip(t, "∀S:((var:A → bool) → bool).⋃(S) = ⋃(S)")
}

func TestSetOps_BigInter(t *testing.T) {
	assertBothParseAndAlphaEqual(t,
		"∀S:((var:A → bool) → bool).⋂(S) = ⋂(S)",
		"∀S:((var:A → bool) → bool).big_intersection(S) = big_intersection(S)")
	assertRoundTrip(t, "∀S:((var:A → bool) → bool).⋂(S) = ⋂(S)")
}

func TestSetOps_Enumeration_Singleton(t *testing.T) {
	// `{a}` desugars to insert(a, empty_set).
	assertBothParseAndAlphaEqual(t,
		"∀a:var:A.∀x:var:A.(x ∈ {a})",
		"∀a:var:A.∀x:var:A.set_member(x, insert(a, empty_set))")
	assertRoundTrip(t, "∀a:var:A.∀x:var:A.(x ∈ {a})")

	// The `{a}` rendering belongs to the insert-chain detector
	// (matchSetEnum) — pin that the singleton literal PRINTS as `{a}`.
	r := ParsePropText("∀a:var:A.∀x:var:A.(x ∈ {a})")
	require.Empty(t, r.Errors)
	printed := prop.FormatPropForParser(r.Prop)
	assert.Contains(t, printed, "{a}",
		"insert(a, empty_set) singleton literal should print as `{a}`; got %s", printed)
}

func TestSetOps_Enumeration_Multi(t *testing.T) {
	// `{a, b, c}` → insert(a, insert(b, insert(c, empty_set))).
	assertBothParseAndAlphaEqual(t,
		"∀a:var:A.∀b:var:A.∀c:var:A.∀x:var:A.(x ∈ {a, b, c})",
		"∀a:var:A.∀b:var:A.∀c:var:A.∀x:var:A.set_member(x, insert(a, insert(b, insert(c, empty_set))))")
	assertRoundTrip(t, "∀a:var:A.∀b:var:A.∀c:var:A.∀x:var:A.(x ∈ {a, b, c})")
}

// TestSetOps_RegistryMetaMeetsDSLMeta pins the mixed-meta contract: a
// registered meta (machine-named type var) meeting the same-named
// DSL surface meta in ConstTermMeta.Equals PANICS. The two are α-variant
// in absType but differ in def wiring (registered metas carry
// def/defSource, the surface meta is bare), so treating them as equal
// would make DefThm() answers and generic-instance AlphaKeys depend on
// which pointer the caller holds — a silent divergence, a cnfKey miss
// among its symptoms. The producer layer keeps the two apart (scope-first
// / resolver-first resolution); Equals carries NO tolerance: in a
// correctly-wired session the surface meta never meets the registered
// one, and when a leak regresses, the panic is the tripwire.
func TestSetOps_RegistryMetaMeetsDSLMeta(t *testing.T) {
	machineVar := core.MakeVarType("?66608")
	machineSet := core.MakeFun(machineVar, core.TypeBool())
	registryMeta := core.MakeConstMeta("subset", core.MakeFun(machineSet, machineSet, core.TypeBool()))

	assert.Panics(t, func() {
		SubsetMeta.Equals(registryMeta)
	}, "α-variant same-named metas must trip the Equals soundness panic")

	// The head comparison the unifier makes on instantiated consts hits
	// the same tripwire.
	indSet := core.MakeFun(TypeInd, core.TypeBool())
	instType := core.MakeFun(indSet, indSet, core.TypeBool())
	dslConst := core.MakeConstTerm(SubsetMeta, instType)
	registryConst := core.MakeConstTerm(registryMeta, instType)
	assert.Panics(t, func() {
		dslConst.Equals(registryConst)
	})
}

func TestSetOps_SetBuilder_Identity(t *testing.T) {
	// `{y | y ∈ s}` desugars to set_comprehension(λv:A. ∃y:A. comprehension_spec(v, set_member(y, s), y)).
	// The identity single-binder form is what parseSetBuilder handles;
	// non-identity shapes stay as explicit set_comprehension in the source.
	r := ParsePropText("∀s:(var:A → bool).∀x:var:A.(x ∈ {y | y ∈ s})")
	require.Empty(t, r.Errors,
		"set-builder identity form should parse: %v", diagMessages(r.Errors))
	require.NotNil(t, r.Prop)
	assertRoundTrip(t, "∀s:(var:A → bool).∀x:var:A.(x ∈ {y | y ∈ s})")
}

func TestSetOps_SetBuilder_WithConjunctPred(t *testing.T) {
	assertRoundTrip(t,
		"∀s:(var:A → bool).∀f:(var:A → bool).∀x:var:A.(x ∈ {y | y ∈ s ∧ f(y)})")
}

func TestSetOps_SetBuilder_General_SingleBinder(t *testing.T) {
	// Three-part general form `{f(x) | x | x ∈ s}` (image shape): the
	// middle segment is the explicit ∃-binder list. Desugars to
	// set_comprehension(λv. ∃x. comprehension_spec(v, x ∈ s, f(x))).
	assertBothParseAndAlphaEqual(t,
		"∀f:(var:A → var:B).∀s:(var:A → bool).∀y:var:B.(y ∈ {f(x) | x | x ∈ s})",
		"∀f:(var:A → var:B).∀s:(var:A → bool).∀y:var:B.(y ∈ set_comprehension(λv:var:B.(∃x:var:A.comprehension_spec(v, x ∈ s, f(x)))))")
	assertRoundTrip(t,
		"∀f:(var:A → var:B).∀s:(var:A → bool).∀y:var:B.(y ∈ {f(x) | x | x ∈ s})")
}

func TestSetOps_SetBuilder_General_MultiBinderPairOutput(t *testing.T) {
	// Multi-binder + pair output (cross-product shape):
	// `{,(x, y) | x, y | (x ∈ s) ∧ (y ∈ t)}` desugars to
	// set_comprehension(λv. ∃x. ∃y. comprehension_spec(v, (x ∈ s) ∧ (y ∈ t), (x, y))) — the ∃
	// order is the binder list's, surface-determined.
	assertBothParseAndAlphaEqual(t,
		"∀s:(var:A → bool).∀t:(var:B → bool).∀z:prod(var:A, var:B).(z ∈ {,(x, y) | x, y | (x ∈ s) ∧ (y ∈ t)})",
		"∀s:(var:A → bool).∀t:(var:B → bool).∀z:prod(var:A, var:B).(z ∈ set_comprehension(λv:prod(var:A, var:B).(∃x:var:A.(∃y:var:B.comprehension_spec(v, (x ∈ s) ∧ (y ∈ t), ,(x, y))))))")
	assertRoundTrip(t,
		"∀s:(var:A → bool).∀t:(var:B → bool).∀z:prod(var:A, var:B).(z ∈ {,(x, y) | x, y | (x ∈ s) ∧ (y ∈ t)})")
}

func TestSetOps_SetBuilder_General_AnnotatedBinders(t *testing.T) {
	// Explicit `:T` annotations inside the binder list — the shape the
	// printer emits in parser mode (FormatTermForParser).
	assertBothParseAndAlphaEqual(t,
		"∀f:(var:A → var:B).∀s:(var:A → bool).∀y:var:B.(y ∈ {f(x) | x:var:A | x ∈ s})",
		"∀f:(var:A → var:B).∀s:(var:A → bool).∀y:var:B.(y ∈ {f(x) | x | x ∈ s})")
}

func TestSetOps_SetBuilder_General_AnnotatedOutput(t *testing.T) {
	// The output annotation carries the general comprehension's element
	// type — equivalently, the hidden set_comprehension λ-binder and comprehension_spec first/third
	// argument type. This is the conflict-safe parser-profile surface.
	assertBothParseAndAlphaEqual(t,
		"∀f:(var:A → var:B).∀s:(var:A → bool).∀y:var:B.(y ∈ {f(x):var:B | x:var:A | x ∈ s})",
		"∀f:(var:A → var:B).∀s:(var:A → bool).∀y:var:B.(y ∈ set_comprehension(λv:var:B.(∃x:var:A.comprehension_spec(v, x ∈ s, f(x)))))")
	assertRoundTrip(t,
		"∀f:(var:A → var:B).∀s:(var:A → bool).∀y:var:B.(y ∈ {f(x):var:B | x:var:A | x ∈ s})")
}

func TestSetOps_SetBuilder_MixedInstanceIdentityUsesTypedSugar(t *testing.T) {
	// set_comprehension and comprehension_spec each occur at A and B in one prop. The canonical
	// identity comprehension carries that instance naturally on its surviving
	// witness binder, so neither const needs an angle-bracket annotation.
	text := "∀s:(var:A → bool).∀t:(var:B → bool).∀a:var:A.∀b:var:B." +
		"((a ∈ set_comprehension(λv:var:A.(∃x:var:A.comprehension_spec(v, x ∈ s, x)))) ∧ " +
		"(b ∈ set_comprehension(λw:var:B.(∃y:var:B.comprehension_spec(w, y ∈ t, y)))))"
	r1 := ParsePropText(text)
	require.Empty(t, r1.Errors, "parse failed: %v", diagMessages(r1.Errors))
	require.NotNil(t, r1.Prop)

	printed := prop.FormatPropForParser(r1.Prop)
	assert.Contains(t, printed, "{x:var:A | x ∈ s}", "A-instance should use typed sugar; got %q", printed)
	assert.Contains(t, printed, "{y:var:B | y ∈ t}", "B-instance should use typed sugar; got %q", printed)
	assert.NotContains(t, printed, "set_comprehension", "canonical mixed instances should hide set_comprehension; got %q", printed)
	assert.NotContains(t, printed, "comprehension_spec", "canonical mixed instances should hide comprehension_spec; got %q", printed)

	r2 := ParsePropText(printed)
	require.Empty(t, r2.Errors, "re-parse of %q failed: %v", printed, diagMessages(r2.Errors))
	require.NotNil(t, r2.Prop)
	assert.True(t, r1.Prop.Conclusion().AlphaEquals(r2.Prop.Conclusion()),
		"mixed identity comprehensions must round-trip; printed=%q", printed)

	// Mirror emit execution: the last override fixes each const name at the B
	// instance. The typed A builder must reject that fast path and re-instantiate
	// through the meta, while the B builder may use the fixed term directly.
	typeB := core.MakeVarType("B")
	setB := core.MakeFun(typeB, core.TypeBool())
	scope := &ParseScope{
		Consts: map[string]core.ConstTerm{
			"set_comprehension":  core.MakeConstTerm(SetComprehensionMeta, core.MakeFun(setB, setB)),
			"comprehension_spec": core.MakeConstTerm(ComprehensionSpecMeta, core.MakeFun(typeB, core.TypeBool(), typeB, core.TypeBool())),
		},
		ConstMetas: map[string]core.ConstTermMeta{
			"set_comprehension":  SetComprehensionMeta,
			"comprehension_spec": ComprehensionSpecMeta,
		},
	}
	r3 := ParsePropTextInScope(printed, scope)
	require.Empty(t, r3.Errors,
		"runtime-style last-override re-parse of %q failed: %v", printed, diagMessages(r3.Errors))
	require.NotNil(t, r3.Prop)
	assert.True(t, r1.Prop.Conclusion().AlphaEquals(r3.Prop.Conclusion()),
		"typed sugar must survive emit's last fixed-instance override; printed=%q", printed)
}

func TestSetOps_SetBuilder_MixedInstanceGeneralUsesTypedSugar(t *testing.T) {
	// General comprehensions need the OUTPUT type, not merely the explicit
	// witness-binder types: f(x):B pins the first set_comprehension/comprehension_spec pair while
	// g(y):D pins the second.
	text := "∀f:(var:A → var:B).∀g:(var:C → var:D)." +
		"∀s:(var:A → bool).∀t:(var:C → bool).∀b:var:B.∀d:var:D." +
		"((b ∈ set_comprehension(λv:var:B.(∃x:var:A.comprehension_spec(v, x ∈ s, f(x))))) ∧ " +
		"(d ∈ set_comprehension(λw:var:D.(∃y:var:C.comprehension_spec(w, y ∈ t, g(y))))))"
	r1 := ParsePropText(text)
	require.Empty(t, r1.Errors, "parse failed: %v", diagMessages(r1.Errors))
	require.NotNil(t, r1.Prop)

	printed := prop.FormatPropForParser(r1.Prop)
	assert.Contains(t, printed, "{f(x):var:B | x:var:A | x ∈ s}",
		"B-output comprehension should use typed sugar; got %q", printed)
	assert.Contains(t, printed, "{g(y):var:D | y:var:C | y ∈ t}",
		"D-output comprehension should use typed sugar; got %q", printed)
	assert.NotContains(t, printed, "set_comprehension", "canonical mixed instances should hide set_comprehension; got %q", printed)
	assert.NotContains(t, printed, "comprehension_spec", "canonical mixed instances should hide comprehension_spec; got %q", printed)

	r2 := ParsePropText(printed)
	require.Empty(t, r2.Errors, "re-parse of %q failed: %v", printed, diagMessages(r2.Errors))
	require.NotNil(t, r2.Prop)
	assert.True(t, r1.Prop.Conclusion().AlphaEquals(r2.Prop.Conclusion()),
		"mixed general comprehensions must round-trip; printed=%q", printed)
}

func TestSetOps_SetBuilder_MixedInstanceDisplayKeepsNaturalTypeWitness(t *testing.T) {
	// Human display normally omits binder types, but a mixed set_comprehension/comprehension_spec
	// conflict needs one visible witness to keep distinct typed terms distinct.
	// Prefer `{x:num | ...}` over exposing both polymorphic const annotations.
	text := "∀a:num.∀b:bool." +
		"((a ∈ set_comprehension(λv:num.(∃x:num.comprehension_spec(v, ⊤, x)))) ∧ " +
		"(b ∈ set_comprehension(λw:bool.(∃y:bool.comprehension_spec(w, ⊤, y)))))"
	r := ParsePropText(text)
	require.Empty(t, r.Errors, "parse failed: %v", diagMessages(r.Errors))
	require.NotNil(t, r.Prop)

	printed := prop.PrintProp(r.Prop)
	assert.Contains(t, printed, "{x:num | ⊤}", "num instance needs a natural type witness; got %q", printed)
	assert.Contains(t, printed, "{y:bool | ⊤}", "bool instance needs a natural type witness; got %q", printed)
	assert.NotContains(t, printed, "set_comprehension", "canonical display should hide set_comprehension; got %q", printed)
	assert.NotContains(t, printed, "comprehension_spec", "canonical display should hide comprehension_spec; got %q", printed)
}

func TestSetOps_SetBuilder_MixedInstanceNonCanonicalStillAnnotated(t *testing.T) {
	// Only the canonical A occurrence is exempt at the notation level. In the
	// B occurrence the hidden λ-binder appears inside the predicate, so sugar
	// would drop a binding; it must retain the explicit, annotated fallback.
	text := "∀s:(var:A → bool).∀t:(var:B → bool).∀a:var:A.∀b:var:B." +
		"((a ∈ set_comprehension(λv:var:A.(∃x:var:A.comprehension_spec(v, x ∈ s, x)))) ∧ " +
		"(b ∈ set_comprehension(λw:var:B.(∃y:var:B.comprehension_spec(w, w ∈ t, y)))))"
	r1 := ParsePropText(text)
	require.Empty(t, r1.Errors, "parse failed: %v", diagMessages(r1.Errors))
	require.NotNil(t, r1.Prop)

	printed := prop.FormatPropForParser(r1.Prop)
	assert.Contains(t, printed, "{x:var:A | x ∈ s}",
		"canonical occurrence should still use sugar; got %q", printed)
	assert.Contains(t, printed, "set_comprehension⟨A:var:B⟩",
		"non-canonical occurrence must keep its set_comprehension annotation; got %q", printed)
	assert.Contains(t, printed, "comprehension_spec⟨A:var:B⟩",
		"non-canonical occurrence must keep its comprehension_spec annotation; got %q", printed)

	r2 := ParsePropText(printed)
	require.Empty(t, r2.Errors, "re-parse of %q failed: %v", printed, diagMessages(r2.Errors))
	require.NotNil(t, r2.Prop)
	assert.True(t, r1.Prop.Conclusion().AlphaEquals(r2.Prop.Conclusion()),
		"mixed canonical/non-canonical comprehensions must round-trip; printed=%q", printed)
}

func TestSetOps_SetBuilder_IdentityPrintsShortForm(t *testing.T) {
	// The identity shape must keep the two-part rendering even though the
	// general matcher also accepts it (matcher order in formatTermImpl).
	r := ParsePropText("∀s:(var:A → bool).∀x:var:A.(x ∈ {y | y ∈ s})")
	require.Empty(t, r.Errors)
	printed := prop.FormatPropForParser(r.Prop)
	// Three-part would render as `{y | y:var:A | y ∈ s}` — assert the
	// binder-list segment is absent.
	assert.NotContains(t, printed, "| y:var:A |",
		"identity shape must print two-part, not a binder list; got %s", printed)
}

func TestSetOps_SetBuilder_TwoPartNonIdentityStillErrors(t *testing.T) {
	// The two-part form stays identity-only: no shared-frees heuristic.
	r := ParsePropText("∀f:(var:A → var:B).∀s:(var:A → bool).∀y:var:B.(y ∈ {f(x) | x ∈ s})")
	require.NotEmpty(t, r.Errors,
		"two-part with non-ident output must error (binder list required)")
}

func TestSetOps_SetBuilder_GeneralDeclines_OuterBinderInPred(t *testing.T) {
	// A set_comprehension whose λ binder occurs INSIDE the predicate is not the
	// comprehension desugar shape — printing a set-builder would drop the
	// binding. Must stay explicit set_comprehension form.
	r := ParsePropText("∀s:(var:A → bool).∀x:var:A.(x ∈ set_comprehension(λv:var:A.(∃y:var:A.comprehension_spec(v, v ∈ s, y))))")
	require.Empty(t, r.Errors, "explicit set_comprehension with v-in-pred should parse: %v",
		diagMessages(r.Errors))
	printed := prop.FormatPropForParser(r.Prop)
	assert.Contains(t, printed, "set_comprehension",
		"v-in-pred shape must not print as set-builder; got %s", printed)
	assertRoundTrip(t,
		"∀s:(var:A → bool).∀x:var:A.(x ∈ set_comprehension(λv:var:A.(∃y:var:A.comprehension_spec(v, v ∈ s, y))))")
}

func TestSetOps_BigOpPrefix_IdentHeadedOperand(t *testing.T) {
	// ⋃/⋂ are tight prefixes taking one spine operand (like `&`):
	// `⋂g(x)` must be big_intersection(g(x)), NOT (big_intersection g)(x) — the
	// mis-binding this replaced.
	assertBothParseAndAlphaEqual(t,
		"∀g:(var:A → ((var:B → bool) → bool)).∀x:var:A.(⋂g(x) = ⋂g(x))",
		"∀g:(var:A → ((var:B → bool) → bool)).∀x:var:A.(big_intersection(g(x)) = big_intersection(g(x)))")
	assertRoundTrip(t,
		"∀g:(var:A → ((var:B → bool) → bool)).∀x:var:A.(⋂g(x) = ⋂g(x))")
}

func TestSetOps_BigOpPrefix_Nested(t *testing.T) {
	// `⋃⋃s` nests: big_union(big_union(s)).
	assertBothParseAndAlphaEqual(t,
		"∀s:(((var:A → bool) → bool) → bool).(⋃⋃s = ⋃⋃s)",
		"∀s:(((var:A → bool) → bool) → bool).(big_union(big_union(s)) = big_union(big_union(s)))")
	assertRoundTrip(t,
		"∀s:(((var:A → bool) → bool) → bool).(⋃⋃s = ⋃⋃s)")
}

func TestSetOps_BigOpPrefix_SetBuilderOperand(t *testing.T) {
	// The brace operand keeps working through the prefix path.
	assertBothParseAndAlphaEqual(t,
		"∀t:(var:A → (var:B → bool)).∀s:(var:A → bool).(⋃{t(x) | x | x ∈ s} = ⋃{t(x) | x | x ∈ s})",
		"∀t:(var:A → (var:B → bool)).∀s:(var:A → bool).(big_union(set_comprehension(λv:(var:B → bool).(∃x:var:A.comprehension_spec(v, x ∈ s, t(x))))) = big_union(set_comprehension(λv:(var:B → bool).(∃x:var:A.comprehension_spec(v, x ∈ s, t(x))))))")
}

func TestSetOps_BigOpPrefix_ParenCallFormsUnchanged(t *testing.T) {
	// Paren groups after the op stay plain calls (NOT tuple operands):
	// `⋃(s)` and the 2-arg membership-unfold `⋃(s, x)` keep their old
	// readings.
	assertBothParseAndAlphaEqual(t,
		"∀s:((var:A → bool) → bool).(⋃(s) = ⋃(s))",
		"∀s:((var:A → bool) → bool).(big_union(s) = big_union(s))")
	assertBothParseAndAlphaEqual(t,
		"∀s:((var:A → bool) → bool).∀x:var:A.(⋃(s, x) ⇔ ⋃(s, x))",
		"∀s:((var:A → bool) → bool).∀x:var:A.(big_union(s, x) ⇔ big_union(s, x))")
}

func TestSetOps_SetBuilder_NestedInPred(t *testing.T) {
	// A set-builder nested inside another's predicate: the probe must not
	// misread the nested `|` tokens.
	assertRoundTrip(t,
		"∀f:(var:A → var:A).∀s:(var:A → bool).∀y:var:A.(y ∈ {f(x) | x | x ∈ {w | w ∈ s}})")
}

func TestSetOps_InsertNonEmptyTail_StaysAsInsert(t *testing.T) {
	// insert(a, s) with s a variable (not empty_set) must NOT print as `{a}`;
	// the enumeration parser only reconstructs insert chains terminating
	// in empty_set, so the shorthand would break round-trip.
	r := ParsePropText("∀a:var:A.∀s:(var:A → bool).insert(a, s) = insert(a, s)")
	require.Empty(t, r.Errors)
	printed := prop.FormatPropForParser(r.Prop)
	assert.Contains(t, printed, "insert(a, s)",
		"insert(a, s) with non-EMPTY tail must stay insert-form; got %s", printed)
	assertRoundTrip(t, "∀a:var:A.∀s:(var:A → bool).insert(a, s) = insert(a, s)")
}

func TestSetOps_ChainedInfixError(t *testing.T) {
	// Non-associative relational chain: `s ⊆ t ⊆ u` should error, matching
	// how `a < b < c` errors (the second relational trips a "chained"
	// diagnostic in parseRelational's single-op semantics).
	r := ParsePropText("∀s:(var:A → bool).∀t:(var:A → bool).∀u:(var:A → bool).(s ⊆ t ⊆ u)")
	if len(r.Errors) == 0 {
		require.NotNil(t, r.Prop)
		t.Fatalf("chained ⊆ ⊆ should error; got %s",
			ext.FormatTermForParser(r.Prop.Conclusion()))
	}
}

func TestSetOps_UnionAssociativity(t *testing.T) {
	// Left-associative: `s ∪ t ∪ u` = `(s ∪ t) ∪ u`.
	assertBothParseAndAlphaEqual(t,
		"∀s:(var:A → bool).∀t:(var:A → bool).∀u:(var:A → bool).(s ∪ t ∪ u = s ∪ t ∪ u)",
		"∀s:(var:A → bool).∀t:(var:A → bool).∀u:(var:A → bool).(union(union(s, t), u) = union(union(s, t), u))")
}

func TestSetOps_MixedWithLegacyPrefixForms(t *testing.T) {
	// A statement that mixes new-form and old-form must build the same
	// term — this is what already-emit'd corpus text looks like during
	// the migration window.
	assertBothParseAndAlphaEqual(t,
		"∀s:(var:A → bool).∀t:(var:A → bool).∀x:var:A.((x ∈ s) ∧ set_member(x, t))",
		"∀s:(var:A → bool).∀t:(var:A → bool).∀x:var:A.(set_member(x, s) ∧ set_member(x, t))")
}

func TestSetOps_InfixUsesCallerScopeMeta(t *testing.T) {
	// Scope-first meta resolution for the set-theory infix surface. The
	// `∈ ⊆ ⊊ ∪ ∩ ∖` operators dispatch through setOperator's DSL-side
	// surface metas, which carry NO def wiring (they exist so bare
	// ParsePropText keeps working). When the caller's ParseScope supplies
	// a registered meta for the same const (emit's SectionText / MakePropText
	// always does), the built ConstTerm must carry the CALLER's meta — the
	// same caller-wins precedence seedSetScopeConstFallback implements for
	// the name path. Regression: an `∈`-built set_member carrying the def-less
	// surface meta is α-equal to the `set_member(x, s)` form but silently defeats
	// def-sensitive consumers (SetTacExpand's per-occurrence DefThm gate
	// skipped it, diverging set_tac residuals — and their CNF cache keys —
	// from record: a strict-replay MISS on a sum-nonnegativity proof).
	elem := core.MakeVarType("A")
	set := core.MakeFun(elem, core.TypeBool())
	cases := []struct {
		name string // const the infix lowers to
		text string // infix form mentioning it
		meta core.ConstTermMeta
	}{
		{"set_member", "∀s:(var:A → bool).∀x:var:A.(x ∈ s)",
			core.MakeConstMeta("set_member", core.MakeFun(elem, set, core.TypeBool()))},
		{"subset", "∀s:(var:A → bool).∀u:(var:A → bool).(s ⊆ u)",
			core.MakeConstMeta("subset", core.MakeFun(set, set, core.TypeBool()))},
		{"union", "∀s:(var:A → bool).∀u:(var:A → bool).((s ∪ u) = u)",
			core.MakeConstMeta("union", core.MakeFun(set, set, set))},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			scope := &ParseScope{ConstMetas: map[string]core.ConstTermMeta{tc.name: tc.meta}}
			res := ParsePropTextInScope(tc.text, scope)
			require.Empty(t, res.Errors, "parse failed: %v", diagMessages(res.Errors))
			require.NotNil(t, res.Prop)
			found := false
			var walk func(core.Term)
			walk = func(sub core.Term) {
				if c, ok := sub.AsConst(); ok && c.Name() == core.TermName(tc.name) {
					found = true
					assert.True(t, any(tc.meta) == any(c.Meta()), "infix-built %s must carry the caller-scope meta, not the DSL surface meta", tc.name)
					return
				}
				switch sub := sub.Core().(type) {
				case core.AppliedTerm:
					walk(sub.Fun())
					walk(sub.Arg())
				case core.AbsTerm:
					walk(sub.Body())
				}
			}
			walk(res.Prop.Conclusion())
			assert.True(t, found, "no %s const found in built term", tc.name)
		})
	}
}

// registryStyleSetMeta mimics a registered meta: same structural shape as
// the DSL surface meta but with a machine-named type variable (like
// `?66608`), and a DIFFERENT pointer.
func registryStyleSetMeta(t *testing.T, name string) core.ConstTermMeta {
	t.Helper()
	v := core.MakeVarType("?66608")
	setOf := core.MakeFun(v, core.TypeBool())
	switch name {
	case "set_member":
		return core.MakeConstMeta("set_member", core.MakeFun(v, setOf, core.TypeBool()))
	case "comprehension_spec":
		return core.MakeConstMeta("comprehension_spec", core.MakeFun(v, core.TypeBool(), v, core.TypeBool()))
	}
	t.Fatalf("registryStyleSetMeta: unsupported name %q", name)
	return core.ConstTermMeta{}
}

// findConstMeta returns the meta of the first const named `name` in the
// conclusion of p, or nil.
func findConstMeta(p core.Prop, name core.TermName) core.ConstTermMeta {
	var found core.ConstTermMeta
	var walk func(core.Term)
	walk = func(tm core.Term) {
		if !found.IsZero() {
			return
		}
		switch n := tm.Core().(type) {
		case core.ConstTerm:
			if n.Name() == name {
				found = n.Meta()
			}
		case core.AppliedTerm:
			walk(n.Fun())
			walk(n.Arg())
		case core.AbsTerm:
			walk(n.Body())
		}
	}
	walk(p.Conclusion())
	return found
}

// TestSetOps_MetaResolutionPrecedence pins the full three-level meta
// resolution order for set-theory consts: caller scope > const
// resolver > DSL surface fallback. The resolver level matters because
// pure surface forms (`x ∈ s`, `{x | φ}`'s comprehension_spec) never mention the
// const name as source text, so the resolver walker must surface the
// LOWERED name of every set surface form and ask the resolver for it
// before the def-less surface meta is seeded. Two orders are excluded:
// a fallback that pre-fills all 14 set names BEFORE the resolver
// pre-seed runs, so that the const resolver is never asked and the
// surface meta leaks into resolver-wired sessions (the assert.text
// shape: goal text never mentions the const, only the resolver can
// supply it); and one that asks the resolver for all 14 names on EVERY
// parse, so that a statement with no set notation at all serves the
// whole set vocabulary — which, with constants minted by chapters,
// locks a name against its mint (the "already served" refusal). The
// third subtest pins the on-demand contract.
func TestSetOps_MetaResolutionPrecedence(t *testing.T) {
	t.Run("infix resolves through const resolver", func(t *testing.T) {
		registryMeta := registryStyleSetMeta(t, "set_member")
		asked := false
		scope := &ParseScope{
			ConstResolver: func(name string) core.ConstTermMeta {
				if name == "set_member" {
					asked = true
					return registryMeta
				}
				return core.ConstTermMeta{}
			},
		}
		res := ParsePropTextInScope("x : num, s : num → bool ⊢ x ∈ s", scope)
		require.Empty(t, res.Errors, "parse failed: %v", diagMessages(res.Errors))
		assert.True(t, asked, "const resolver was never consulted for set_member")
		assert.True(t, any(registryMeta) == any(findConstMeta(res.Prop, "set_member")), "infix ∈ must carry the resolver-supplied meta")
	})

	t.Run("name-form resolves through const resolver", func(t *testing.T) {
		registryMeta := registryStyleSetMeta(t, "comprehension_spec")
		scope := &ParseScope{
			ConstResolver: func(name string) core.ConstTermMeta {
				if name == "comprehension_spec" {
					return registryMeta
				}
				return core.ConstTermMeta{}
			},
		}
		res := ParsePropTextInScope(
			"y : num, c : num ⊢ set_comprehension(λv:num. ∃x:num. comprehension_spec(v, x = c, x))(y)", scope)
		require.Empty(t, res.Errors, "parse failed: %v", diagMessages(res.Errors))
		assert.True(t, any(registryMeta) == any(findConstMeta(res.Prop, "comprehension_spec")), "comprehension_spec must carry the resolver-supplied meta, not the surface fallback")
	})

	t.Run("caller scope beats resolver", func(t *testing.T) {
		scopeMeta := registryStyleSetMeta(t, "set_member")
		resolverMeta := registryStyleSetMeta(t, "set_member")
		scope := &ParseScope{
			ConstMetas: map[string]core.ConstTermMeta{"set_member": scopeMeta},
			ConstResolver: func(name string) core.ConstTermMeta {
				if name == "set_member" {
					return resolverMeta
				}
				return core.ConstTermMeta{}
			},
		}
		res := ParsePropTextInScope("x : num, s : num → bool ⊢ x ∈ s", scope)
		require.Empty(t, res.Errors, "parse failed: %v", diagMessages(res.Errors))
		assert.True(t, any(scopeMeta) == any(findConstMeta(res.Prop, "set_member")), "caller-scope meta must win over the resolver's")
	})

	t.Run("bare parse falls back to surface meta", func(t *testing.T) {
		res := ParsePropText("x : num, s : num → bool ⊢ x ∈ s")
		require.Empty(t, res.Errors, "parse failed: %v", diagMessages(res.Errors))
		assert.True(t, any(InMeta) == any(findConstMeta(res.Prop, "set_member")), "scope-less parse must still resolve ∈ via the DSL surface meta")
	})

	t.Run("resolver is asked only for the set names the text lowers to", func(t *testing.T) {
		asked := func(text string) map[string]bool {
			names := map[string]bool{}
			scope := &ParseScope{
				ConstResolver: func(name string) core.ConstTermMeta {
					if _, isSet := SurfaceFallbackMetas()[name]; isSet {
						names[name] = true
					}
					return core.ConstTermMeta{}
				},
			}
			res := ParsePropTextInScope(text, scope)
			require.Empty(t, res.Errors, "parse failed: %v", diagMessages(res.Errors))
			return names
		}
		assert.Empty(t, asked("∀n:num. n + 0 = n"),
			"a statement with no set notation must not touch the set vocabulary")
		assert.Equal(t, map[string]bool{"set_member": true, "union": true},
			asked("x : num, s : num → bool, t : num → bool ⊢ x ∈ s ∪ t"),
			"each set infix surfaces exactly its lowered name")
		assert.Equal(t, map[string]bool{"set_comprehension": true, "comprehension_spec": true, "insert": true, "empty_set": true},
			asked("c : num ⊢ {x:num | x = c} = {c}"),
			"comprehension and enumeration surface the names they lower to")
		assert.Equal(t, map[string]bool{"big_union": true, "universe": true},
			asked("u : (num → bool) → bool ⊢ ⋃u = 𝕌"),
			"the big-ops and 𝕌 surface their lowered names")
	})

	t.Run("a big operator's half-open range surfaces the set names it lowers to", func(t *testing.T) {
		// `Σ_{i<m}` sums over `{i | i < m}`, synthesized at build time
		// (belowRangeAST), so no source-text name mentions its two set
		// constants. The pre-seed asks the resolver before the build
		// runs; this bare scope declares no sum, so the parse itself may
		// refuse the fold's head, which is after the asking.
		names := map[string]bool{}
		scope := &ParseScope{
			ConstResolver: func(name string) core.ConstTermMeta {
				if _, isSet := SurfaceFallbackMetas()[name]; isSet {
					names[name] = true
				}
				return core.ConstTermMeta{}
			},
		}
		ParsePropTextInScope("t : num, f : num → num ⊢ Σ_{i<t} f(i) = Σ_{i<t} f(i)", scope)
		assert.Equal(t, map[string]bool{"set_comprehension": true, "comprehension_spec": true}, names,
			"the range's set-builder must be resolved like a written one")
	})
}
