// Tests for the `⟨V:T,...⟩` polymorphic type-substitution annotation
// suffix on identifiers. The formatter emits this suffix
// (ext/formatConstTypeAnnotation) to disambiguate polymorphic-const
// conflicts; the parser accepts it so print→parse round-trips.
package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// polyScope builds a ParseScope pre-populated with the polymorphic metas
// most annotation tests need: finite, universe, set_member, has_size.
func polyScope() *ParseScope {
	typeA := core.MakeVarType("A")
	num := NumType
	finiteMeta := core.MakeConstMeta(
		"finite", core.MakeFun(core.MakeFun(typeA, core.TypeBool()), core.TypeBool()))
	univMeta := core.MakeConstMeta(
		"universe", core.MakeFun(typeA, core.TypeBool()))
	inMeta := core.MakeConstMeta(
		"set_member", core.MakeFun(typeA, core.MakeFun(core.MakeFun(typeA, core.TypeBool()), core.TypeBool())))
	hasSizeMeta := core.MakeConstMeta(
		"has_size", core.MakeFun(core.MakeFun(typeA, core.TypeBool()), core.MakeFun(num, core.TypeBool())))
	return &ParseScope{
		ConstMetas: map[string]core.ConstTermMeta{
			"finite":     finiteMeta,
			"universe":   univMeta,
			"set_member": inMeta,
			"has_size":   hasSizeMeta,
		},
	}
}

// findConstOfName returns the first ConstTerm named `name` in `t`, or
// nil.
func findConstOfName(t core.Term, name core.TermName) core.ConstTerm {
	var found core.ConstTerm
	var walk func(core.Term)
	walk = func(t core.Term) {
		if !found.IsZero() {
			return
		}
		switch x := t.(type) {
		case core.ConstTerm:
			if x.Name() == name {
				found = x
			}
		case core.AppliedTerm:
			walk(x.Fun())
			walk(x.Arg())
		case core.AbsTerm:
			walk(x.Body())
		}
	}
	walk(t)
	return found
}

// TestParseAngleBracket_UnivBare parses `universe⟨A:bool⟩` — a bare-atom
// (no arg list) polymorphic const with an annotation. Verifies the
// resulting ConstTerm has the substitution and the concrete type.
func TestParseAngleBracket_UnivBare(t *testing.T) {
	res := ParseTermTextInScope("universe⟨A:bool⟩", nil, polyScope(), nil)
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)
	require.NotNil(t, res.Term)

	c := findConstOfName(res.Term, "universe")
	require.False(t, c.IsZero(), "expected universe const in %s", ext.FormatTerm(res.Term, false))
	assert.Equal(t, "(bool → bool)", ext.FormatType(c.Type()))

	subs := c.TypeSubsts()
	require.Len(t, subs, 1)
	assert.Equal(t, "A", string(subs[0].VarType.Name()))
	assert.True(t, subs[0].HolType.Equals(core.TypeBool()))
}

// TestParseAngleBracket_FiniteApplied parses `finite⟨A:bool⟩(x)` — the
// annotation on a function head followed by an argument list.
func TestParseAngleBracket_FiniteApplied(t *testing.T) {
	scope := polyScope()
	ctx := map[string]core.HolType{
		"x": core.MakeFun(core.TypeBool(), core.TypeBool()),
	}
	res := ParseTermTextInScope("finite⟨A:bool⟩(x)", ctx, scope, core.TypeBool())
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)

	c := findConstOfName(res.Term, "finite")
	require.False(t, c.IsZero())
	subs := c.TypeSubsts()
	require.Len(t, subs, 1)
	assert.Equal(t, "A", string(subs[0].VarType.Name()))
	assert.True(t, subs[0].HolType.Equals(core.TypeBool()))
}

// TestParseAngleBracket_InTypeVar exercises a `var:` type in the
// annotation — the printer's canonical form for type-vars.
func TestParseAngleBracket_InTypeVar(t *testing.T) {
	typeB := core.MakeVarType("B")
	scope := polyScope()
	ctx := map[string]core.HolType{
		"y": typeB,
		"t": core.MakeFun(typeB, core.TypeBool()),
	}
	res := ParseTermTextInScope("set_member⟨A:var:B⟩(y, t)", ctx, scope, core.TypeBool())
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)

	c := findConstOfName(res.Term, "set_member")
	require.False(t, c.IsZero())
	subs := c.TypeSubsts()
	require.Len(t, subs, 1)
	assert.Equal(t, "A", string(subs[0].VarType.Name()))
	assert.True(t, subs[0].HolType.Equals(typeB))
}

// TestParseAngleBracket_HasSizeSkolemVar exercises the `?<name>` Skolem
// type-var syntax inside an annotation. `?83621` names a fresh type-var
// (prop.Normalize emits names like this) — the parser turns it into
// `var:?83621`.
func TestParseAngleBracket_HasSizeSkolemVar(t *testing.T) {
	skolem := core.MakeVarType("?83621")
	scope := polyScope()
	ctx := map[string]core.HolType{
		"m": NumType,
	}
	// Universe over the Skolem type — universe : ?83621 → bool.
	res := ParseTermTextInScope(
		"has_size⟨A:?83621⟩(universe⟨A:?83621⟩, m)",
		ctx, scope, core.TypeBool())
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)

	hsC := findConstOfName(res.Term, "has_size")
	require.False(t, hsC.IsZero())
	hsSubs := hsC.TypeSubsts()
	require.Len(t, hsSubs, 1)
	assert.True(t, hsSubs[0].HolType.Equals(skolem),
		"has_size subst mismatch, got %s", ext.FormatType(hsSubs[0].HolType))

	uC := findConstOfName(res.Term, "universe")
	require.False(t, uC.IsZero())
	uSubs := uC.TypeSubsts()
	require.Len(t, uSubs, 1)
	assert.True(t, uSubs[0].HolType.Equals(skolem))
}

// TestParseAngleBracket_UnivFunType exercises a compound type (var:A → var:B)
// inside the annotation. This is the exact shape the formatter emits when
// a const is instantiated at a function type.
func TestParseAngleBracket_UnivFunType(t *testing.T) {
	scope := polyScope()
	res := ParseTermTextInScope("universe⟨A:(var:A → var:B)⟩", nil, scope, nil)
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)

	c := findConstOfName(res.Term, "universe")
	require.False(t, c.IsZero())
	subs := c.TypeSubsts()
	require.Len(t, subs, 1)
	// The substituted type is (A → B) — a compound function type.
	assert.Equal(t, "(var:A → var:B)", ext.FormatType(subs[0].HolType))
}

// TestParseAngleBracket_EqualsSeparator ensures both `:` (formatter's
// current output) and `=` (earlier internal/JSON-shape sources) are
// accepted as the binding separator.
func TestParseAngleBracket_EqualsSeparator(t *testing.T) {
	scope := polyScope()
	res := ParseTermTextInScope("universe⟨A=bool⟩", nil, scope, nil)
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)

	c := findConstOfName(res.Term, "universe")
	require.False(t, c.IsZero())
	subs := c.TypeSubsts()
	require.Len(t, subs, 1)
	assert.True(t, subs[0].HolType.Equals(core.TypeBool()))
}

// TestParseAngleBracket_RoundTrip exercises the printer→parser round
// trip that motivated adding this suffix in the first place. Two
// finite(universe) applications at different types produce output like
// `finite⟨A:bool⟩(universe⟨A:bool⟩) ⇔ finite⟨A:ind⟩(universe⟨A:ind⟩)`; the
// parser must accept that back.
func TestParseAngleBracket_RoundTrip(t *testing.T) {
	scope := polyScope()

	typeA := core.MakeVarType("A")
	finiteMeta := core.MakeConstMeta(
		"finite", core.MakeFun(core.MakeFun(typeA, core.TypeBool()), core.TypeBool()))
	univMeta := core.MakeConstMeta(
		"universe", core.MakeFun(typeA, core.TypeBool()))

	finiteBool := core.MakeConstTerm(finiteMeta,
		core.MakeFun(core.MakeFun(core.TypeBool(), core.TypeBool()), core.TypeBool()))
	univBool := core.MakeConstTerm(univMeta,
		core.MakeFun(core.TypeBool(), core.TypeBool()))
	finiteInd := core.MakeConstTerm(finiteMeta,
		core.MakeFun(core.MakeFun(TypeInd, core.TypeBool()), core.TypeBool()))
	univInd := core.MakeConstTerm(univMeta,
		core.MakeFun(TypeInd, core.TypeBool()))

	lhs := core.Apply(finiteBool, univBool)
	rhs := core.Apply(finiteInd, univInd)
	iff := core.Eq(lhs, rhs)

	printed := ext.FormatTerm(iff, false)
	// Sanity: the printer produces the disambiguated form.
	require.Contains(t, printed, "⟨A:bool⟩")
	require.Contains(t, printed, "⟨A:ind⟩")

	res := ParseTermTextInScope(printed, nil, scope, core.TypeBool())
	require.Empty(t, res.Errors,
		"parse of printed disambiguated form failed: %v\nprinted: %s",
		res.Errors, printed)

	// Reprint and confirm the type annotations survive.
	reprinted := ext.FormatTerm(res.Term, false)
	assert.Contains(t, reprinted, "⟨A:bool⟩")
	assert.Contains(t, reprinted, "⟨A:ind⟩")
}

// TestParseAngleBracket_Error_UnknownConst rejects an annotation on a
// name that isn't a scope constant.
func TestParseAngleBracket_Error_UnknownConst(t *testing.T) {
	scope := polyScope()
	res := ParseTermTextInScope("wibble⟨A:bool⟩", nil, scope, nil)
	require.NotEmpty(t, res.Errors, "expected an error for annotation on non-const")
	msg := diagJoined(res.Errors)
	assert.Contains(t, msg, "wibble")
	assert.Contains(t, msg, "not a scope constant")
}

// TestParseAngleBracket_Error_UnknownTypeVar rejects an annotation whose
// key is not among the const's abstract type-vars.
func TestParseAngleBracket_Error_UnknownTypeVar(t *testing.T) {
	scope := polyScope()
	res := ParseTermTextInScope("universe⟨X:bool⟩", nil, scope, nil)
	require.NotEmpty(t, res.Errors, "expected an error for unknown type-var")
	msg := diagJoined(res.Errors)
	assert.Contains(t, msg, "universe")
	assert.Contains(t, msg, "X")
}

// TestParseAngleBracket_MultiBinding parses an annotation with two
// bindings separated by comma. The abstract meta only has one type-var
// (universe : A→bool), so we construct a fresh meta with two type-vars.
func TestParseAngleBracket_MultiBinding(t *testing.T) {
	typeA := core.MakeVarType("A")
	typeB := core.MakeVarType("B")
	// pairMeta : A → B → prod(A,B) — not a library const, but a
	// convenient polymorphic 2-var shape.
	pairMeta := core.MakeConstMeta("PAIRK",
		core.MakeFun(typeA, core.MakeFun(typeB,
			core.MakeCompositeType(core.MakeMetaType("prod", 2), typeA, typeB))))
	scope := &ParseScope{
		ConstMetas: map[string]core.ConstTermMeta{"PAIRK": pairMeta},
	}
	res := ParseTermTextInScope("PAIRK⟨A:bool, B:ind⟩", nil, scope, nil)
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)

	c := findConstOfName(res.Term, "PAIRK")
	require.False(t, c.IsZero())
	subs := c.TypeSubsts()
	require.Len(t, subs, 2)

	byName := map[string]core.HolType{}
	for _, s := range subs {
		byName[string(s.VarType.Name())] = s.HolType
	}
	assert.True(t, byName["A"].Equals(core.TypeBool()))
	assert.True(t, byName["B"].Equals(TypeInd))
}

// TestParseAngleBracket_SkolemVarName exercises a Skolem `?N` name in
// the annotation NAME position — the printer emits the const meta's raw
// abstract type-var name, which for Normalize-fresh metas looks like
// `?83621` (e.g. `has_size⟨?83621:var:A⟩`). The lexer tokenizes bare
// `?83621` as the synthesized ident `var:?83621`; parseTypeAnnotation
// must strip that prefix back off so the binding targets the meta's
// type-var `?83621`.
func TestParseAngleBracket_SkolemVarName(t *testing.T) {
	skolem := core.MakeVarType("?83621")
	typeA := core.MakeVarType("A")
	hasSizeMeta := core.MakeConstMeta("has_size",
		core.MakeFun(core.MakeFun(skolem, core.TypeBool()), core.MakeFun(NumType, core.TypeBool())))
	scope := &ParseScope{
		ConstMetas: map[string]core.ConstTermMeta{"has_size": hasSizeMeta},
	}
	ctx := map[string]core.HolType{
		"s": core.MakeFun(typeA, core.TypeBool()),
		"m": NumType,
	}
	res := ParseTermTextInScope("has_size⟨?83621:var:A⟩(s, m)", ctx, scope, core.TypeBool())
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)

	c := findConstOfName(res.Term, "has_size")
	require.False(t, c.IsZero())
	subs := c.TypeSubsts()
	require.Len(t, subs, 1)
	assert.Equal(t, "?83621", string(subs[0].VarType.Name()))
	assert.True(t, subs[0].HolType.Equals(typeA))
}

// TestParseAngleBracket_IdentityAnnotation exercises the printer's
// identity annotation for an abstract-instance occurrence of a
// conflicted const (`universe⟨A:var:A⟩`): it must pin the ABSTRACT
// instance — empty TypeSubsts — even when the scope carries a fixed
// concrete instance for the same name that would otherwise win.
func TestParseAngleBracket_IdentityAnnotation(t *testing.T) {
	typeA := core.MakeVarType("A")
	univMeta := core.MakeConstMeta("universe", core.MakeFun(typeA, core.TypeBool()))
	univBool := core.MakeConstTerm(univMeta,
		core.MakeFun(core.TypeBool(), core.TypeBool()))
	scope := &ParseScope{
		// Fixed bool instance in Consts — the trap the identity
		// annotation exists to bypass.
		Consts:     map[string]core.ConstTerm{"universe": univBool},
		ConstMetas: map[string]core.ConstTermMeta{"universe": univMeta},
	}
	res := ParseTermTextInScope("universe⟨A:var:A⟩", nil, scope, nil)
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)

	c := findConstOfName(res.Term, "universe")
	require.False(t, c.IsZero())
	assert.Empty(t, c.TypeSubsts(), "identity annotation must yield the abstract instance")
	assert.True(t, c.Type().Equals(univMeta.AbsType()))
}

// TestParseBareOperatorAtom exercises the bare-operator value atom:
// `monoidal_op(+)` passes the num `+` const (name literally "+") as a
// first-class argument. Only fires when the operator is immediately
// followed by `,` or `)`.
func TestParseBareOperatorAtom(t *testing.T) {
	typeA := core.MakeVarType("A")
	monMeta := core.MakeConstMeta("monoidal_op",
		core.MakeFun(core.MakeFun(typeA, core.MakeFun(typeA, typeA)), core.TypeBool()))
	plusMeta := core.MakeConstMeta("+", core.MakeFun(NumType, core.MakeFun(NumType, NumType)))
	scope := &ParseScope{
		Consts: map[string]core.ConstTerm{
			"+": core.MakeConstTerm(plusMeta, plusMeta.AbsType()),
		},
		ConstMetas: map[string]core.ConstTermMeta{
			"monoidal_op": monMeta,
			"+":           plusMeta,
		},
	}
	res := ParsePropTextInScope("monoidal_op(+)", scope)
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)

	plus := findConstOfName(res.Prop.Conclusion(), "+")
	require.False(t, plus.IsZero(), "expected + const, got %s", ext.FormatTerm(res.Prop.Conclusion(), false))
	assert.True(t, plus.Type().Equals(plusMeta.AbsType()))
	mon := findConstOfName(res.Prop.Conclusion(), "monoidal_op")
	require.False(t, mon.IsZero())
	// monoidal_op's A must have unified with num from +'s type.
	assert.Empty(t, res.Errors)
}

// TestParseBareOperatorAtom_ConnectivesAndPrefixCall: the connectives,
// negation and the quantifiers stand as first-class arguments the way
// `+` does — `word_bitwise_binary(k, ∧, x, y)`, `word_bitwise_unary(n, ¬, x)`,
// `insert(s, ∃)` — and an operator before `(` heads a prefix call,
// the printer's form of a partial application (`*(k)` is `λn. k * n`).
// Each is the constant of that name, resolved through the scope.
func TestParseBareOperatorAtom_ConnectivesAndPrefixCall(t *testing.T) {
	boolBin := core.MakeFun(core.TypeBool(), core.MakeFun(core.TypeBool(), core.TypeBool()))
	numBin := core.MakeFun(NumType, core.MakeFun(NumType, NumType))
	typeA := core.MakeVarType("A")
	setA := core.MakeFun(typeA, core.TypeBool())
	metas := map[string]core.ConstTermMeta{
		"binop":         core.MakeConstMeta("binop", core.MakeFun(boolBin, core.TypeBool())),
		"unop":          core.MakeConstMeta("unop", core.MakeFun(core.MakeFun(core.TypeBool(), core.TypeBool()), core.TypeBool())),
		"quant":         core.MakeConstMeta("quant", core.MakeFun(core.MakeFun(setA, core.TypeBool()), core.TypeBool())),
		"apply1":        core.MakeConstMeta("apply1", core.MakeFun(core.MakeFun(NumType, NumType), core.MakeFun(NumType, NumType))),
		"*":             core.MakeConstMeta("*", numBin),
		utils.AndStr:    ext.AND.Meta(),
		utils.OrStr:     ext.OR.Meta(),
		utils.ImplyStr:  ext.IMPLY.Meta(),
		utils.NegStr:    ext.NOT.Meta(),
		utils.ExistsStr: ext.EXISTS.Meta(),
		utils.ForAllStr: ext.FORALL.Meta(),
	}
	scope := &ParseScope{ConstMetas: metas}
	for _, tc := range []struct{ text, want string }{
		{"binop(∧)", utils.AndStr},
		{"binop(∨)", utils.OrStr},
		{"binop(⇒)", utils.ImplyStr},
		{"unop(¬)", utils.NegStr},
		{"quant(∃)", utils.ExistsStr},
		{"quant(∀)", utils.ForAllStr},
		{"k:num ⊢ apply1(*(k), 2) = 2 * k", "*"},
		{"k:num ⊢ apply1((*)(k), 2) = 2 * k", "*"},
	} {
		res := ParsePropTextInScope(tc.text, scope)
		require.Empty(t, res.Errors, "%s: %v", tc.text, res.Errors)
		require.False(t, findConstOfName(res.Prop.Conclusion(), core.TermName(tc.want)).IsZero(), "%s: no %s constant in %s", tc.text, tc.want, ext.FormatTerm(res.Prop.Conclusion(), false))
	}
	// A partial application reads as the operator applied: `*(k)` at 2
	// is `k * 2`.
	partial := ParsePropTextInScope("k:num ⊢ (*(k))(2) = k * 2", scope)
	require.Empty(t, partial.Errors, "%v", partial.Errors)
	eq := partial.Prop.Conclusion()
	l, r, ok := ext.MatchesEQ(eq)
	require.True(t, ok)
	assert.True(t, l.AlphaEquals(r), "%s", ext.FormatTerm(eq, false))
	// An operator at the START of an operand is still a missing
	// operand: the readings are for a standalone argument, a
	// parenthesized value and a prefix call, nothing else.
	for _, text := range []string{"x:bool, y:bool ⊢ x ∧ ∧ y", "x:bool ⊢ ¬ ∧ x", "x:num ⊢ x * *"} {
		res := ParsePropTextInScope(text, scope)
		require.NotEmpty(t, res.Errors, "%s must remain a parse error", text)
	}
}

// TestParseBareOperatorAtom_StrictInfixTypo ensures the bare-operator
// atom does NOT soften mistyped infix chains: `x + + y` (second `+` is
// followed by an identifier, not `,`/`)`) must still be a parse error,
// not a partial application guess.
func TestParseBareOperatorAtom_StrictInfixTypo(t *testing.T) {
	res := ParsePropTextInScope("x:num, y:num ⊢ (x + + y) = y", nil)
	require.NotEmpty(t, res.Errors, "mistyped `x + + y` must remain a parse error")
	assert.Contains(t, diagJoined(res.Errors), "expected expression")
}

// TestLex_AngleBrackets is a lexer-level smoke test that the new
// `⟨` / `⟩` tokens are recognized.
func TestLex_AngleBrackets(t *testing.T) {
	tokens, err := lex("universe⟨A:bool⟩")
	require.Nil(t, err)
	kinds := make([]tokenKind, 0, len(tokens))
	for _, tk := range tokens {
		kinds = append(kinds, tk.kind)
	}
	// universe ⟨ A : bool ⟩ EOF
	require.Equal(t, []tokenKind{tokIdent, tokLangle, tokIdent, tokColon, tokIdent, tokRangle, tokEOF}, kinds)
}

// TestParseCartAccessDollarConst exercises the `$` cart-access
// combinator const (`$(v, i)` reads the i-th component of a cart-typed
// vector). The parser tokenizes `$` as an identifier (via symbolicIdents
// in the lexer) so the standard function-application path handles it.
// Previously, the lexer rejected `$` as an "unexpected character" and
// every statement using $
// fell back to the Go-expr Stmt form.
func TestParseCartAccessDollarConst(t *testing.T) {
	typeA := core.MakeVarType("A")
	typeB := core.MakeVarType("B")
	cartAB := core.MakeCompositeType(core.MakeMetaType("cart", 2), typeA, typeB)
	// $ : cart(A, B) → num → A
	dollarMeta := core.MakeConstMeta("$",
		core.MakeFun(cartAB, core.MakeFun(NumType, typeA)))
	dollarConcrete := core.MakeConstTerm(dollarMeta,
		core.MakeFun(cartAB, core.MakeFun(NumType, typeA)))
	scope := &ParseScope{
		Consts:     map[string]core.ConstTerm{"$": dollarConcrete},
		ConstMetas: map[string]core.ConstTermMeta{"$": dollarMeta},
	}
	ctx := map[string]core.HolType{
		"v": cartAB,
		"i": NumType,
	}
	res := ParseTermTextInScope("$(v, i)", ctx, scope, typeA)
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)
	require.NotNil(t, res.Term)

	c := findConstOfName(res.Term, "$")
	require.False(t, c.IsZero(), "expected $ const in %s", ext.FormatTerm(res.Term, false))
}

// TestParseCartAccessDollarConst_WithAnnotation exercises the annotated
// form `$⟨A:...,B:...⟩(v, i)` — the printer's disambiguation shape when
// $ appears at multiple instances in the same prop (a
// two-index range statement's shape).
func TestParseCartAccessDollarConst_WithAnnotation(t *testing.T) {
	skolA := core.MakeVarType("?123307")
	skolN := core.MakeVarType("?123317")
	cartS := core.MakeCompositeType(core.MakeMetaType("cart", 2), skolA, skolN)
	dollarMeta := core.MakeConstMeta("$",
		core.MakeFun(cartS, core.MakeFun(NumType, skolA)))
	scope := &ParseScope{
		ConstMetas: map[string]core.ConstTermMeta{"$": dollarMeta},
	}
	typeA := core.MakeVarType("A")
	typeN := core.MakeVarType("N")
	cartAN := core.MakeCompositeType(core.MakeMetaType("cart", 2), typeA, typeN)
	ctx := map[string]core.HolType{
		"x": cartAN,
		"i": NumType,
	}
	res := ParseTermTextInScope(
		"$⟨?123307:var:A,?123317:var:N⟩(x, i)", ctx, scope, typeA)
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)
	c := findConstOfName(res.Term, "$")
	require.False(t, c.IsZero())
	subs := c.TypeSubsts()
	require.Len(t, subs, 2)
}

// TestLex_DollarAsIdent asserts the lexer tokenizes bare `$` as an
// identifier — a single-char symbolic ident. Guards against a regression
// where `$` becomes an "unexpected character" again.
func TestLex_DollarAsIdent(t *testing.T) {
	tokens, err := lex("$(x, i)")
	require.Nil(t, err)
	require.GreaterOrEqual(t, len(tokens), 1)
	assert.Equal(t, tokIdent, tokens[0].kind)
	assert.Equal(t, "$", tokens[0].text)
}

// TestScopeConstFixedInstancePreferred is the regression test for the
// round-trip failure of a statement quantifying over finite_index. When the scope has both a
// fixed instance (e.g. `finite_index : (num → finite_image(var:N))`)
// and a meta (the abstract type-var name is `A`, not `N`), the fixed
// instance is authoritative if its curry-prefix types agree with the
// arguments — using the meta path in that case would produce a term
// whose type-var name differs from — and fails to unify with — a
// sibling use that pins the type via a bound-var annotation. Before
// the fix, buildApp preferred the meta path unconditionally, so
// `Q(finite_index(i))` where `Q : (finite_image(var:N) → bool)` and
// `finite_index` is in scope at `(num → finite_image(var:N))` failed
// with "ill-typed term".
func TestScopeConstFixedInstancePreferred(t *testing.T) {
	typeN := core.MakeVarType("N")
	finiteImageN := core.MakeCompositeType(
		core.MakeMetaType("finite_image", 1), typeN)
	// Meta has abstract type-var A; fixed instance has type-var N — the
	// name collision that the previous meta-first path introduced.
	typeA := core.MakeVarType("A")
	finiteImageA := core.MakeCompositeType(
		core.MakeMetaType("finite_image", 1), typeA)
	metaFI := core.MakeConstMeta("finite_index",
		core.MakeFun(NumType, finiteImageA))
	fixedFI := core.MakeConstTerm(metaFI,
		core.MakeFun(NumType, finiteImageN))
	scope := &ParseScope{
		Consts:     map[string]core.ConstTerm{"finite_index": fixedFI},
		ConstMetas: map[string]core.ConstTermMeta{"finite_index": metaFI},
	}
	// The prop pins the type-var to `N` via Q's binder. The parser must
	// use the fixed `finite_index` instance so Q's application type-checks.
	res := ParsePropTextInScope(
		"∀Q:(finite_image(var:N) → bool). ∀i:num. Q(finite_index(i))",
		scope)
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)

	c := findConstOfName(res.Prop.Conclusion(), "finite_index")
	require.False(t, c.IsZero())
	// The const must be at the fixed instance's type (with `N`), not
	// the meta's abstract type (with `A`).
	assert.True(t, c.Type().Equals(core.MakeFun(NumType, finiteImageN)),
		"finite_index resolved to %s, expected fixed instance (num → finite_image(var:N))",
		ext.FormatType(c.Type()))
}

func diagJoined(ds []InputDiagnostic) string {
	parts := make([]string, len(ds))
	for i, d := range ds {
		parts[i] = d.Message
	}
	return strings.Join(parts, " | ")
}

// TestParseBareOperatorAtom_WholeText: an operator that is the whole
// text is its constant, as one standing as an argument is — the
// printer's spelling of a bare operator read back on its own, as a
// layout's template is (templateOf). An operator with a missing
// operand at the end of the text is still an error, at the type: the
// `+` of `x + +` is read as the constant and is no number.
func TestParseBareOperatorAtom_WholeText(t *testing.T) {
	boolBin := core.MakeFun(core.TypeBool(), core.MakeFun(core.TypeBool(), core.TypeBool()))
	numBin := core.MakeFun(NumType, core.MakeFun(NumType, NumType))
	numRel := core.MakeFun(NumType, core.MakeFun(NumType, core.TypeBool()))
	scope := &ParseScope{ConstMetas: map[string]core.ConstTermMeta{
		"+":          core.MakeConstMeta("+", numBin),
		"*":          core.MakeConstMeta("*", numBin),
		"<=":         core.MakeConstMeta("<=", numRel),
		utils.AndStr: ext.AND.Meta(),
		utils.NegStr: ext.NOT.Meta(),
	}}
	for _, tc := range []struct {
		text string
		want core.HolType
	}{
		{"+", numBin},
		{"*", numBin},
		{"<=", numRel},
		{"∧", boolBin},
		{"¬", core.MakeFun(core.TypeBool(), core.TypeBool())},
	} {
		res := ParseTermTextInScope(tc.text, nil, scope, nil)
		require.Empty(t, res.Errors, "%s: %v", tc.text, res.Errors)
		c, ok := res.Term.AsConst()
		require.True(t, ok, "%s: %s", tc.text, ext.FormatTerm(res.Term, false))
		require.Equal(t, tc.text, string(c.Name()))
		require.True(t, c.Type().Equals(tc.want), "%s: %s", tc.text, c.Type())
		// The printer's spelling of the constant alone reads back as it.
		printed := ext.FormatTermForParser(res.Term)
		back := ParseTermTextInScope(printed, nil, scope, nil)
		require.Empty(t, back.Errors, "%s printed as %s: %v", tc.text, printed, back.Errors)
		require.True(t, back.Term.AlphaEquals(res.Term), "%s printed as %s reads as %s", tc.text, printed, ext.FormatTerm(back.Term, false))
	}
	res := ParsePropTextInScope("x:num ⊢ x + +", scope)
	require.NotEmpty(t, res.Errors, "`x + +` must remain an error")
}
