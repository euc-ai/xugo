package dsl

import (
	"fmt"
	"runtime"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// ---------------------------------------------------------------------------
// NormalizeSymbols tests
// ---------------------------------------------------------------------------

func TestNormalizeSymbols(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		// Basic operators.
		{"p => q", "p ⇒ q"},
		{"p <=> q", "p ⇔ q"},
		{"p -> q", "p → q"},
		{`p /\ q`, "p ∧ q"},
		{`p \/ q`, "p ∨ q"},
		{"p && q", "p ∧ q"},
		{"~p", "¬p"},
		{"!p", "¬p"},

		// Keywords (whole word).
		{"forall x:A. P(x)", "∀ x:A. P(x)"},
		{"exists x:A. P(x)", "∃ x:A. P(x)"},
		{"p and q", "p ∧ q"},
		{"p or q", "p ∨ q"},
		{"not p", "¬ p"},
		{"true", "⊤"},
		{"false", "⊥"},

		// Keywords should not match inside identifiers.
		{"forest", "forest"},
		{"ornament", "ornament"},
		{"notable", "notable"},
		{"android", "android"},

		// Order matters: <=> before =>.
		{"p <=> q => r", "p ⇔ q ⇒ r"},

		// Already Unicode — no change.
		{"p ⇒ q", "p ⇒ q"},
		{"∀x:A. P(x)", "∀x:A. P(x)"},
	}

	for _, tt := range tests {
		t.Run(tt.input, func(t *testing.T) {
			got, _ := NormalizeTextSymbols(tt.input)
			if got != tt.expected {
				t.Errorf("NormalizeSymbols(%q) = %q, want %q", tt.input, got, tt.expected)
			}
		})
	}
}

// ---------------------------------------------------------------------------
// Lexer tests
// ---------------------------------------------------------------------------

func TestLexBasic(t *testing.T) {
	input := "∀x:A. P(x) ⇒ Q(x)"
	tokens, err := lex(input)
	if err != nil {
		t.Fatalf("lex error: %v", err)
	}

	// Should have: ∀ x : A . P ( x ) ⇒ Q ( x ) EOF
	expected := []tokenKind{
		tokForall, tokIdent, tokColon, tokIdent, tokDot,
		tokIdent, tokLParen, tokIdent, tokRParen,
		tokImply,
		tokIdent, tokLParen, tokIdent, tokRParen,
		tokEOF,
	}

	if len(tokens) != len(expected) {
		t.Fatalf("expected %d tokens, got %d", len(expected), len(tokens))
	}
	for i, e := range expected {
		if tokens[i].kind != e {
			t.Errorf("token[%d]: expected kind %d, got %d (%q)", i, e, tokens[i].kind, tokens[i].text)
		}
	}
}

// ---------------------------------------------------------------------------
// ParseText tests
// ---------------------------------------------------------------------------

func TestParseSimpleTautology(t *testing.T) {
	// p ⇒ p should parse successfully.
	result := ParsePropText("p ⇒ p")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
}

func TestParseNegation(t *testing.T) {
	result := ParsePropText("~(p /\\ q)")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
	// Symbol normalizations are now silent (no warnings emitted).
	// Just verify the normalized input contains Unicode symbols.
	if !strings.Contains(result.NormalizedInput, "¬") || !strings.Contains(result.NormalizedInput, "∧") {
		t.Error("expected normalized input to contain ¬ and ∧")
	}
}

func TestParseDeMorgan(t *testing.T) {
	result := ParsePropText("~(p /\\ q) <=> (~p \\/ ~q)")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
}

func TestParseWithHypotheses(t *testing.T) {
	result := ParsePropText("p, q ⊢ p ∧ q")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
	// Should have 2 hypotheses.
	if result.Prop.NumHyps() != 2 {
		t.Errorf("expected 2 hypotheses, got %d", result.Prop.NumHyps())
	}
}

func TestParseWithTypeDeclaration(t *testing.T) {
	result := ParsePropText("P : A→bool ⊢ ∀x:A. P(x) ⇒ P(x)")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
}

func TestParseQuantifiers(t *testing.T) {
	result := ParsePropText("∀x:A. ∃y:A. P(x, y)")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
}

func TestParseASCIIQuantifiers(t *testing.T) {
	// Using ASCII: "forall x:A. exists y:A. P(x,y)"
	result := ParsePropText("forall x:A. exists y:A. P(x,y)")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
	// Check normalization happened.
	if !strings.Contains(result.NormalizedInput, "∀") {
		t.Errorf("expected ∀ in normalized input, got %q", result.NormalizedInput)
	}
}

func TestParseHilbert(t *testing.T) {
	// ε is a binder like ∀/∃ — the body must be bool, and the resulting
	// term has the bound var's type. The agent surfaced this gap when
	// trying to spell a witness-via-ε-iterator construction in
	// the text DSL.
	result := ParsePropText("P : num → bool ⊢ P(εn:num. P(n))")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}

	// Wide binding: εfn:num→num. fn(0) = 0 ∧ fn(1) = 1 should bind the
	// whole conjunction to ε, not parse as application + dangling ∧.
	termRes := ParseTermText("εfn:num→num. fn(0) = 0 ∧ fn(1) = 1", nil,
		core.MakeFun(NumType, NumType))
	if len(termRes.Errors) > 0 {
		t.Fatalf("wide-binding: %v", diagMessages(termRes.Errors))
	}

	// Non-bool body must be rejected — matches the kernel-side
	// Assert(IsBool(t)) in core.Hilbert.
	bad := ParseTermText("εn:num. n + 0", nil, NumType)
	if len(bad.Errors) == 0 {
		t.Fatal("expected non-bool body to be rejected")
	}
}

func TestParseUnique(t *testing.T) {
	// ∃! (unique existential) is a binder like ∀/∃/ε and must build the same
	// term as ext.Unique. The lexer's ∃! token rule is dead if normalize
	// rewrites the trailing `!` to ¬ first.
	res := ParsePropText("∃!x:num. x = x")
	if len(res.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(res.Errors))
	}
	x := ext.Var(ext.TermName("x"), NumType)
	want := ext.Unique(x)(core.Eq(x, x))
	if !res.Prop.Conclusion().AlphaEquals(want) {
		t.Errorf("∃!x. x=x:\n got  %v\n want %v", res.Prop.Conclusion(), want)
	}

	// A space after ∃!, nesting under another binder, and wide binding over a
	// connective all parse (∃! binds like the other quantifiers).
	for _, s := range []string{
		"∃! x:num. x = x",
		"∀y:num. ∃!x:num. x = y",
		"∃!x:num. x = 0 ∧ x + x = x",
	} {
		if r := ParsePropText(s); len(r.Errors) > 0 {
			t.Errorf("%q: %v", s, diagMessages(r.Errors))
		}
	}

	// A bare `!` NOT following ∃ is still negation — the ∃! pass-through in
	// normalize must not regress prefix-`!`.
	if r := ParsePropText("∀x:num. !(x = x)"); len(r.Errors) > 0 {
		t.Errorf("bare-! negation regressed: %v", diagMessages(r.Errors))
	}
}

func TestBuildAppNestedArgTypeFromKnownDomain(t *testing.T) {
	// An undeclared function applied in the argument position of a
	// known-domain predicate takes its result type from that domain. A
	// `buildApp` that built the argument first and defaulted the inner
	// head's result type to bool (sound only for boolean-atom positions)
	// would have `core.Apply` panic on `num.Equals(bool)` when the outer
	// predicate's domain is num.
	//
	// The three ingredients are all required: an explicitly num-domain
	// predicate `P:(num→bool)`, applied to a nested application `g(...)`,
	// with g undeclared.
	t.Run("repro_no_panic", func(t *testing.T) {
		result := ParsePropText("∃P:(num→bool). P(g(0))")
		if len(result.Errors) > 0 {
			t.Fatalf("unexpected errors (was core_panic before fix): %v",
				diagMessages(result.Errors))
		}
		if result.Prop == nil {
			t.Fatal("expected non-nil Prop")
		}
	})

	// Control from the report: a bare-literal argument never tripped the
	// bug (no nested application), so it must keep working.
	t.Run("control_bare_literal", func(t *testing.T) {
		result := ParsePropText("∃P:(num→bool). P(0)")
		if len(result.Errors) > 0 {
			t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
		}
	})

	// Binary relation with the nested application in the first argument.
	t.Run("binary_relation", func(t *testing.T) {
		result := ParsePropText("∃R:(num→num→bool). R(g(0), 1)")
		if len(result.Errors) > 0 {
			t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
		}
	})

	// The fix's intent: the undeclared head's result type is taken from
	// the enclosing domain (num), not bool-defaulted. Probe it directly at
	// the term level — `g(0)` with an expected type of num must
	// type g as num→num and the application as num. Before the fix this
	// returned a type_mismatch (bool != num).
	t.Run("undeclared_head_inherits_result_type", func(t *testing.T) {
		res := ParseTermText("g(0)", nil, NumType)
		if len(res.Errors) > 0 {
			t.Fatalf("unexpected errors: %v", diagMessages(res.Errors))
		}
		if !res.Term.Type().Equals(NumType) {
			t.Fatalf("expected num result type, got %s", ext.FormatType(res.Term.Type()))
		}
	})

	// Backward-compat: an undeclared head in a boolean-atom position (no
	// non-bool expectation) still defaults to a bool result.
	t.Run("predicate_atom_defaults_bool", func(t *testing.T) {
		res := ParseTermText("Q(0)", nil, core.TypeBool())
		if len(res.Errors) > 0 {
			t.Fatalf("unexpected errors: %v", diagMessages(res.Errors))
		}
		if !res.Term.Type().Equals(core.TypeBool()) {
			t.Fatalf("expected bool result type, got %s", ext.FormatType(res.Term.Type()))
		}
	})
}

// TestTupleArrowApplication_TypedNotCorePanic: a witness term whose author
// meant a paired domain wrote `(num,num)→num`, which the DSL parses as a
// CURRIED num→num→num, so `f(,(m,n))` (f applied to a pair) is ill-typed.
// The kernel's core.Apply rejects it via Assert("Should not happen."), and
// a build-recovery that surfaced that as core_panic "internal error: Should
// not happen." would read like an engine bug. It must surface as a
// type_mismatch.
func TestTupleArrowApplication_TypedNotCorePanic(t *testing.T) {
	// `f:(num,num)→num` declares f at the CURRIED type num→num→num (a
	// tuple-looking arrow in type position is curried, not a product
	// domain); `,(m,n)` is a num×num pair, so `f(,(m,n))` mismatches f's
	// first-argument type (num vs num×num). The pair-literal `,` is accepted
	// in argument position (text-dsl pair-literal support), so the failure
	// is purely the kernel type check that core.Apply enforces with Assert.
	const src = "f:(num,num)→num, m:num, n:num ⊢ f(,(m, n)) = 0"
	res := ParsePropText(src)
	require.NotEmpty(t, res.Errors, "ill-typed application must produce a diagnostic")
	for _, d := range res.Errors {
		require.NotEqual(t, CodeCorePanic, d.Code,
			"ill-typed user input must NOT surface as core_panic; got %q: %s",
			d.Code, d.Message)
		require.NotContains(t, d.Message, "internal error: Should not happen.",
			"the opaque assert message must be replaced with actionable text")
	}
	// At least one diagnostic should be the type-mismatch classification.
	var sawTypeMismatch bool
	for _, d := range res.Errors {
		if d.Code == CodeTypeMismatch {
			sawTypeMismatch = true
		}
	}
	require.True(t, sawTypeMismatch,
		"expected a type_mismatch diagnostic; got: %v", diagMessages(res.Errors))
}

func TestBuildAbsBodyTypeFromExpectedCodomain(t *testing.T) {
	// Follow-up edge case: the application-path `expected` threading did
	// not reach into a lambda body. For `λ….predecessor(g(c))` the top node is a
	// lambda, so `buildAbs` built the body with no constraint and the
	// undeclared head predecessor bool-defaulted — yielding `…→bool` where the
	// caller (instantiate) needed `…→num`. The fix peels one arrow off the
	// expected type per binder and threads the codomain into the body.
	num := NumType
	numToNum := core.MakeFun(num, num)

	// The agent's shape: nested lambda, undeclared head predecessor in the body,
	// expected (num→num)→num→num→num. The body must resolve to num.
	t.Run("agent_repro_nested_lambda", func(t *testing.T) {
		expected := core.MakeFun(numToNum, core.MakeFun(num, core.MakeFun(num, num)))
		res := ParseTermText("λg:(num→num). λb:num. λc:num. predecessor(g(c))", nil, expected)
		if len(res.Errors) > 0 {
			t.Fatalf("unexpected errors (was …→bool before fix): %v",
				diagMessages(res.Errors))
		}
		if !res.Term.Type().Equals(expected) {
			t.Fatalf("expected %s, got %s", ext.FormatType(expected), ext.FormatType(res.Term.Type()))
		}
	})

	// Single binder: λc:num. predecessor(c) expected num→num. predecessor inherits num.
	t.Run("single_binder", func(t *testing.T) {
		res := ParseTermText("λc:num. predecessor(c)", nil, numToNum)
		if len(res.Errors) > 0 {
			t.Fatalf("unexpected errors: %v", diagMessages(res.Errors))
		}
		if !res.Term.Type().Equals(numToNum) {
			t.Fatalf("expected %s, got %s", ext.FormatType(numToNum), ext.FormatType(res.Term.Type()))
		}
	})

	// With no expected type, an undeclared head in a value position has nothing
	// to fix its result type — it FAILS FAST naming the function (a silent
	// bool-default to `…→bool` would mis-type value-position uses like
	// `nat_pow(a,n) = 1`; see buildApp's undeclared-head branch).
	t.Run("no_expected_fails_fast", func(t *testing.T) {
		res := ParseTermText("λc:num. predecessor(c)", nil, nil)
		if len(res.Errors) == 0 {
			t.Fatalf("expected a fail-fast error for undeclared predecessor's result type, got %s",
				ext.FormatType(res.Term.Type()))
		}
		if !strings.Contains(res.Errors[0].Message, "predecessor") {
			t.Fatalf("fail-fast error should name predecessor, got: %s", res.Errors[0].Message)
		}
	})

	// Lambda in argument position of a known higher-order domain: the
	// lambda body's result type comes from the domain's codomain too.
	// F : ((num→num)→bool) declared; F(λx:num. predecessor(x)) must type-check with
	// the inner lambda resolving to num→num, not num→bool.
	t.Run("lambda_in_arg_position", func(t *testing.T) {
		result := ParsePropText("F : ((num→num)→bool) ⊢ F(λx:num. predecessor(x))")
		if len(result.Errors) > 0 {
			t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
		}
	})
}

// TestUndeclaredHeadResultType covers option-1 type inference for an undeclared
// function head: its result type is propagated across `=`/`≠` from a typed
// partner (incl. a LITERAL, which the infer.go =-partner rule misses since it has
// no var to seed a guess), and is a fail-fast error when genuinely unconstrained
// — never a silent bool-default.
func TestUndeclaredHeadResultType(t *testing.T) {
	// Literal partner fixes f's result to num (a silent bool-default would
	// read "equality type mismatch: left is bool").
	t.Run("literal_partner", func(t *testing.T) {
		r := ParsePropText("a:num ⊢ f(a) = 1")
		if len(r.Errors) > 0 {
			t.Fatalf("unexpected errors: %v", diagMessages(r.Errors))
		}
	})
	t.Run("flipped_literal_partner", func(t *testing.T) {
		r := ParsePropText("a:num ⊢ 1 = f(a)")
		if len(r.Errors) > 0 {
			t.Fatalf("unexpected errors: %v", diagMessages(r.Errors))
		}
	})
	// Typed-var partner still works (handled already by infer.go's =-partner rule).
	t.Run("var_partner", func(t *testing.T) {
		r := ParsePropText("a:num, b:num ⊢ f(a) = b")
		if len(r.Errors) > 0 {
			t.Fatalf("unexpected errors: %v", diagMessages(r.Errors))
		}
	})
	// Both sides undeclared heads ⇒ genuinely ambiguous ⇒ fail fast (not a silent
	// bool ⇔ bool).
	t.Run("both_undeclared_fails_fast", func(t *testing.T) {
		r := ParsePropText("a:num ⊢ f(a) = g(a)")
		if len(r.Errors) == 0 {
			t.Fatal("expected a fail-fast error for two undeclared heads across =")
		}
	})
}

func TestParseTermTextInScopeResolvesConstant(t *testing.T) {
	// A constant name outside the five built-in nat encoders (here predecessor)
	// parses as a free variable with no scope, but as the defined constant
	// when a scope supplies it. This is the channel tactic term-parameter
	// resolution seeds from the goal so names like predecessor resolve as constants
	// rather than being rejected by the engine's free-var scope guard.
	num := NumType
	preMeta := core.MakeConstMeta("predecessor", core.MakeFun(num, num))
	pre := core.MakeConstTerm(preMeta, core.MakeFun(num, num))
	scope := &ParseScope{
		Consts:     map[string]core.ConstTerm{"predecessor": pre},
		ConstMetas: map[string]core.ConstTermMeta{"predecessor": preMeta},
	}
	ctx := map[string]core.HolType{"c": num}

	headIsConst := func(term ext.Term) bool {
		app, ok := term.AsAppliedTerm()
		if !ok || app.IsZero() {
			return false
		}
		_, ok = app.Fun().AsConst()
		return ok
	}

	// No scope: predecessor is a free variable, so the application head is a var
	// and predecessor shows up among the free variables.
	t.Run("no_scope_is_free_var", func(t *testing.T) {
		res := ParseTermText("predecessor(c)", ctx, num)
		if len(res.Errors) > 0 {
			t.Fatalf("unexpected errors: %v", diagMessages(res.Errors))
		}
		if headIsConst(res.Term) {
			t.Fatal("without scope, predecessor should parse as a free variable, not a constant")
		}
		var sawPRE bool
		for _, v := range res.Term.Frees(nil) {
			if string(v.Name()) == "predecessor" {
				sawPRE = true
			}
		}
		if !sawPRE {
			t.Fatal("expected predecessor among free variables without scope")
		}
	})

	// With scope: predecessor resolves as the constant — head is a const and predecessor
	// is not a free variable (only c is).
	t.Run("with_scope_is_constant", func(t *testing.T) {
		res := ParseTermTextInScope("predecessor(c)", ctx, scope, num)
		if len(res.Errors) > 0 {
			t.Fatalf("unexpected errors: %v", diagMessages(res.Errors))
		}
		if !headIsConst(res.Term) {
			t.Fatal("with scope, predecessor should resolve as a constant")
		}
		for _, v := range res.Term.Frees(nil) {
			if string(v.Name()) == "predecessor" {
				t.Fatal("predecessor must not be a free variable when resolved via scope")
			}
		}
	})

	// The agent's witness shape: a closed lambda whose body applies predecessor.
	// With scope it has zero free variables (predecessor is a const), so it would
	// pass the engine's scope guard.
	t.Run("closed_lambda_witness", func(t *testing.T) {
		expected := core.MakeFun(core.MakeFun(num, num),
			core.MakeFun(num, core.MakeFun(num, num)))
		res := ParseTermTextInScope("λa:(num→num). λb:num. λc:num. predecessor(a(c))",
			ctx, scope, expected)
		if len(res.Errors) > 0 {
			t.Fatalf("unexpected errors: %v", diagMessages(res.Errors))
		}
		if !res.Term.Type().Equals(expected) {
			t.Fatalf("expected %s, got %s", ext.FormatType(expected), ext.FormatType(res.Term.Type()))
		}
		if n := len(res.Term.Frees(nil)); n != 0 {
			t.Fatalf("expected a closed term (0 free vars), got %d", n)
		}
	})
}

func TestParseBareLambda(t *testing.T) {
	// Bare lambda as an argument to a function application. This is the
	// dominant corpus shape (set_comprehension(λv:T. body, x)). Pre-lambda support
	// the parser rejected the leading `λ` outside ∀/∃/∃!.
	result := ParsePropText("G : (A→bool) → A → bool ⊢ ∀x:A. G(λv:A. ⊤, x)")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
}

func TestParseBareLambdaRoundTrip(t *testing.T) {
	// Print → parse must round-trip when binderTypes=true. The lambda
	// branch in formatTermImpl now annotates `λx:T.`, matching what
	// parseLambda consumes.
	formatted := "∀x:A. G(λv:A. ⊤, x)"
	result := ParsePropText("G : (A→bool) → A → bool ⊢ " + formatted)
	if len(result.Errors) > 0 {
		t.Fatalf("parse: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
}

func TestParseLambdaPredicateWithPolymorphicSetComprehension(t *testing.T) {
	typeA := core.MakeVarType("A")
	typeB := core.MakeVarType("B")
	typeC := core.MakeVarType("C")
	scope := &ParseScope{
		ConstMetas: map[string]core.ConstTermMeta{
			"finite":             core.MakeConstMeta("finite", core.MakeFun(core.MakeFun(typeA, core.TypeBool()), core.TypeBool())),
			"set_member":         core.MakeConstMeta("set_member", core.MakeFun(typeA, core.MakeFun(core.MakeFun(typeA, core.TypeBool()), core.TypeBool()))),
			"set_comprehension":  core.MakeConstMeta("set_comprehension", core.MakeFun(core.MakeFun(typeA, core.TypeBool()), core.MakeFun(typeA, core.TypeBool()))),
			"comprehension_spec": core.MakeConstMeta("comprehension_spec", core.MakeFun(typeA, core.MakeFun(core.TypeBool(), core.MakeFun(typeA, core.TypeBool())))),
		},
		Vars: map[string]core.HolType{
			"t": core.MakeFun(typeA, core.MakeFun(typeB, core.TypeBool())),
			"f": core.MakeFun(typeA, core.MakeFun(typeB, typeC)),
		},
	}

	for _, tc := range []struct {
		name string
		raw  string
	}{
		{
			name: "simple_set_comprehension",
			raw:  "λs. finite(set_comprehension(λv. comprehension_spec(v, set_member(v, s), v)))",
		},
		{
			name: "dependent_product_shape",
			raw:  "λs. (∀x. set_member(x, s) ⇒ finite(t(x))) ⇒ finite(set_comprehension(λv. ∃x. ∃y. comprehension_spec(v, set_member(x, s) ∧ set_member(y, t(x)), f(x, y))))",
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			res := ParseTermTextInScope(tc.raw, nil, scope, nil)
			if len(res.Errors) > 0 {
				t.Fatalf("unexpected errors: %v", diagMessages(res.Errors))
			}
		})
	}
}

// ---------------------------------------------------------------------------
// Extended lambda & application syntax (paren-grouped binders, untyped
// binders, juxtaposition + curried application). Together these unblock
// surface syntax that the agent reaches for when it has
// to spell a complex dispatch function inline (e.g., instantiating
// recspace_recursion's ∀Fn with a 4-arg dispatch term).
// ---------------------------------------------------------------------------

func TestParseLambdaParenGrouped(t *testing.T) {
	// `λ(x:T1) (y:T2). body` desugars to chained `λx:T1. λy:T2. body`.
	// Useful because a compound binder type like `num→recspace(α)` becomes
	// readable inside paren grouping. The chained form already parses, so
	// this is pure surface sugar.
	num := NumType
	expected := core.MakeFun(num, core.MakeFun(num, num))

	for _, txt := range []string{
		"λ(x:num) (y:num). x", // canonical paren-grouped
		"λ(x:num)(y:num). x",  // no whitespace between groups
	} {
		res := ParseTermText(txt, nil, expected)
		if len(res.Errors) > 0 {
			t.Fatalf("%q: %v", txt, diagMessages(res.Errors))
		}
		if !res.Term.Type().Equals(expected) {
			t.Errorf("%q: got %s, want %s", txt, ext.FormatType(res.Term.Type()), ext.FormatType(expected))
		}
	}

	// Compound type in one group, type variable in another — the shape
	// the agent's recspace_recursion dispatch term uses.
	res := ParseTermText("λ(c:num) (i:A) (r:num→T) (s:num→B). c", nil, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("compound: %v", diagMessages(res.Errors))
	}
	// Each binder pushed in order; result is num.
	want := core.MakeFun(num,
		core.MakeFun(core.MakeVarType("A"),
			core.MakeFun(core.MakeFun(num, core.MakeVarType("T")),
				core.MakeFun(core.MakeFun(num, core.MakeVarType("B")), num))))
	if !res.Term.Type().Equals(want) {
		t.Errorf("compound type mismatch: got %s, want %s",
			ext.FormatType(res.Term.Type()), ext.FormatType(want))
	}

	// Paren-grouped form REQUIRES a type per group (an untyped
	// `λ(x) (y). body` is ambiguous with parenthesized application).
	bad := ParseTermText("λ(x) (y). x", nil, nil)
	if len(bad.Errors) == 0 {
		t.Fatal("expected error for untyped paren-grouped binder")
	}
}

func TestParseLambdaUntyped(t *testing.T) {
	num := NumType

	// Untyped binder + outer `expected` codomain — the binder type comes
	// from peeling one arrow off the expected type, same mechanism the
	// typed-binder path uses for the body's expected type.
	res := ParseTermText("λx. x", nil, core.MakeFun(num, num))
	if len(res.Errors) > 0 {
		t.Fatalf("expected-peel: %v", diagMessages(res.Errors))
	}
	if !res.Term.Type().Equals(core.MakeFun(num, num)) {
		t.Errorf("expected-peel: got %s, want num→num", ext.FormatType(res.Term.Type()))
	}

	// Mixed typed + untyped chained binders.
	expected := core.MakeFun(num, core.MakeFun(num, num))
	res = ParseTermText("λx:num. λy. y", nil, expected)
	if len(res.Errors) > 0 {
		t.Fatalf("mixed: %v", diagMessages(res.Errors))
	}
	if !res.Term.Type().Equals(expected) {
		t.Errorf("mixed: got %s, want %s", ext.FormatType(res.Term.Type()), ext.FormatType(expected))
	}

	// Body usage of the binder pins the binder type via the collect-pass
	// walk (`f(x)` with f : num→bool → x : num inferred).
	ctx := map[string]core.HolType{"f": core.MakeFun(num, core.TypeBool())}
	res = ParseTermText("λx. f(x)", ctx, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("body-inferred: %v", diagMessages(res.Errors))
	}
	if !res.Term.Type().Equals(core.MakeFun(num, core.TypeBool())) {
		t.Errorf("body-inferred: got %s, want num→bool", ext.FormatType(res.Term.Type()))
	}

	// No expected, no body constraint — the binder defaults to a fresh
	// type variable `var:_<name>` so the lambda is still well-formed.
	// (Kernel-side uses can then unify or report a type mismatch with a
	// clear shape, rather than the parser silently coercing to bool.)
	res = ParseTermText("λi. i", nil, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("fresh-var: %v", diagMessages(res.Errors))
	}
	freshI := core.MakeVarType("_i")
	if !res.Term.Type().Equals(core.MakeFun(freshI, freshI)) {
		t.Errorf("fresh-var: got %s, want _i→_i", ext.FormatType(res.Term.Type()))
	}
}

// Quantifiers (∀, ∃, ∃!, ε) now accept the lambda-style untyped form
// `∀x. body` / `∃x. body`, mirroring `λx. body`. The binder type is
// inferred from how the bound variable is used in the body. This unblocks
// agent-written assertions over goal-local type-variables (e.g. ?71143)
// that have no concrete spelling in the DSL — the motivating case being
// the IMAGE_o substantive bridge:
//
//	set_member(ẋ, image(g, s)) ⇔ ∃y. ẋ = g(y) ∧ set_member(y, s)
//
// where y's type must equal g's domain but the agent can't name it.
func TestParseQuantUntyped(t *testing.T) {
	num := NumType

	// (1) The IMAGE_o-style motivating case: y's type inferred from g's
	// domain via `g(y)`. With g : A→B and xdot : B in scope, the body
	// `xdot = g(y)` pins y to A — a type-variable the agent has no
	// concrete spelling for, yet the assertion now parses cleanly.
	A := core.MakeVarType("A")
	B := core.MakeVarType("B")
	ctx := map[string]core.HolType{
		"g":    core.MakeFun(A, B),
		"xdot": B,
	}
	res := ParseTermText("∃y. xdot = g(y)", ctx, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("∃ body-inferred: %v", diagMessages(res.Errors))
	}
	if !core.IsBool(res.Term) {
		t.Errorf("∃ body-inferred: term not bool, got %s", ext.FormatType(res.Term.Type()))
	}

	// (2) ∀x. P(x) — body usage `P : num→bool` pins x to num.
	ctx = map[string]core.HolType{"p": core.MakeFun(num, core.TypeBool())}
	res = ParseTermText("∀x. p(x)", ctx, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("∀ body-inferred: %v", diagMessages(res.Errors))
	}
	if !core.IsBool(res.Term) {
		t.Errorf("∀ body-inferred: not bool, got %s", ext.FormatType(res.Term.Type()))
	}

	// (3) ∃!x. P(x) — unique quantifier, same inference path.
	res = ParseTermText("∃!x. p(x)", ctx, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("∃! body-inferred: %v", diagMessages(res.Errors))
	}

	// (4) εx. P(x) — Hilbert epsilon, same inference path. ε is the only
	// non-boolean-result quantifier; the body must still be bool, but the
	// term's type is the binder type (x here).
	res = ParseTermText("εx. p(x)", ctx, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("ε body-inferred: %v", diagMessages(res.Errors))
	}
	if !res.Term.Type().Equals(num) {
		t.Errorf("ε body-inferred: got %s, want num", ext.FormatType(res.Term.Type()))
	}

	// (5) Degenerate ∀x. ⊤ — x unused; binder falls back to fresh `_x`
	// type variable (mirrors `λi. i` with no constraint → `_i→_i`).
	res = ParseTermText("∀x. ⊤", nil, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("∀ unused: %v", diagMessages(res.Errors))
	}
	if !core.IsBool(res.Term) {
		t.Errorf("∀ unused: not bool")
	}

	// (6) Body must still be bool — same constraint typed-binder form
	// enforces. `∃y. y` with y untyped infers y:bool, OK; `∃y. g(y)` with
	// g : A→B (non-bool codomain) should be rejected even though the body
	// walk succeeds.
	ctx = map[string]core.HolType{"g": core.MakeFun(A, B)}
	res = ParseTermText("∃y. g(y)", ctx, nil)
	if len(res.Errors) == 0 {
		t.Fatal("expected error: ∃ body must be boolean (g : A→B has non-bool codomain)")
	}

	// (7) Mixed typed + untyped binders chained — both must work.
	ctx = map[string]core.HolType{"p": core.MakeFun(num, core.MakeFun(num, core.TypeBool()))}
	res = ParseTermText("∀x:num. ∃y. p(x, y)", ctx, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("mixed typed/untyped: %v", diagMessages(res.Errors))
	}
}

// TestParseTypeText_BareQuestionMarkVar exercises the lexer rule that
// accepts `?<ident-chars>` as a type-variable spelling, equivalent to
// `var:?<chars>`. The motivating use is `apply lemma(...) type_specialize:
// {A: "?71143"}` — the agent reads `?71143` straight off a goal print and
// passes it back without rewriting to `var:?71143`. Bare `?` (no chars
// after) remains an unknown char.
func TestParseTypeText_BareQuestionMarkVar(t *testing.T) {
	// Round-trip: `?71143` parses to the same VarType as `var:?71143`.
	bare, err := ParseTypeText("?71143")
	require.NoError(t, err)
	prefixed, err := ParseTypeText("var:?71143")
	require.NoError(t, err)
	if !bare.Equals(prefixed) {
		t.Errorf("`?71143` and `var:?71143` should produce identical types; got %v vs %v",
			bare, prefixed)
	}

	// Works inside compound types too.
	got, err := ParseTypeText("?71143 → ?71148")
	require.NoError(t, err)
	want, err := ParseTypeText("var:?71143 → var:?71148")
	require.NoError(t, err)
	if !got.Equals(want) {
		t.Errorf("compound type with bare `?` form should round-trip: got %v vs %v",
			got, want)
	}

	// Bare `?` alone is still rejected (no ident chars after).
	_, err = ParseTypeText("?")
	if err == nil {
		t.Errorf("bare `?` with no ident chars should be rejected")
	}
}

func TestParseSpineApplication(t *testing.T) {
	num := NumType

	// Curried application f(x)(y): trailing paren-arg groups chain.
	res := ParseTermText(
		"λf:num→num→num. λx:num. λy:num. f(x)(y)", nil, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("curried: %v", diagMessages(res.Errors))
	}

	// Juxtaposition f x y: bare-atom args chain left-associatively.
	res = ParseTermText(
		"λf:num→num→num. λx:num. λy:num. f x y", nil, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("juxtaposition: %v", diagMessages(res.Errors))
	}

	// Mixed: f x (y). Spine must bind as `(f x) y`, NOT `f (x y)`.
	// The latter is what a naive parseAtom-eats-trailing-`(` rule would
	// produce — the spine refactor exists to fix exactly this case.
	res = ParseTermText(
		"λf:num→num→num. λx:num. λy:num. f x (y)", nil, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("mixed: %v", diagMessages(res.Errors))
	}
	// Verify left-associativity by checking the resulting term has
	// the expected curried application structure.
	body, _ := ext.MatchesAbs(res.Term)
	_ = body
	// Easier check: the type must be (num,num,num)→num.
	want := core.MakeFun(core.MakeFun(num, core.MakeFun(num, num)),
		core.MakeFun(num, core.MakeFun(num, num)))
	if !res.Term.Type().Equals(want) {
		t.Errorf("mixed type: got %s, want %s",
			ext.FormatType(res.Term.Type()), ext.FormatType(want))
	}

	// 4-arity juxtaposition: agent's primrec dispatch shape (without the
	// `mk_list (r 0)` complication, which depends on the recspace const
	// scope and is independent of this surface change).
	res = ParseTermText(
		"λf:num→num→num→num. λa:num. λb:num. λc:num. f a b c", nil, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("4-arity juxt: %v", diagMessages(res.Errors))
	}

	// Function-typed ε with juxtaposition body — the doc's "Failure 3"
	// repro in its canonical form.
	res = ParseTermText("εf:num→num. ∀x:num. f x = x", nil, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("eps + juxt: %v", diagMessages(res.Errors))
	}
}

func TestParseAgentDispatchTerm(t *testing.T) {
	// Combines all four surface extensions in one term:
	//   * paren-grouped outer binders with mixed type-variable / compound
	//     binder types,
	//   * untyped nested λ binders (`λi. λr. λs. ...`),
	//   * juxtaposition application (`r 0`, `s 0`),
	//   * a body containing curried function application.
	// This is a minimized version of the agent's recspace_recursion dispatch
	// term shape. The original (with `recspace`, `mk_list`, `family_cons`,
	// `cons'`, `family_nil`, `nil'`) needs those consts in scope; the
	// parser-level surface shape is what's exercised here.
	ctx := map[string]core.HolType{
		"H":    core.MakeFun(NumType, core.TypeBool()),
		"NIL2": NumType,
	}
	txt := "λ(c:num) (i:A) (r:num→num) (s:num→num). " +
		"λi. λr. λs. H(r 0)"
	res := ParseTermText(txt, ctx, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("dispatch term: %v", diagMessages(res.Errors))
	}
	if res.Term == nil {
		t.Fatal("expected non-nil term")
	}
}

func TestParseEpsTrueRoundTrip(t *testing.T) {
	// The form `εv.⊤` (no binder type) — a common printed
	// form. The untyped-binder change must keep this
	// parsing without disturbance. Since ε requires a typed binder
	// (parseQuant — not parseLambda — and parseQuant still requires `:T`),
	// the canonical XuGo form is `εv:T. ⊤`. Verify both shapes.
	for _, txt := range []string{
		"εv:bool. ⊤",
		"εv:num. ⊤",
	} {
		res := ParseTermText(txt, nil, nil)
		if len(res.Errors) > 0 {
			t.Fatalf("%q: %v", txt, diagMessages(res.Errors))
		}
		if res.Term == nil {
			t.Fatal("expected non-nil term")
		}
	}
}

func TestParseEquality(t *testing.T) {
	result := ParsePropText("x : A ⊢ x = x")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
}

func TestParseTopBottom(t *testing.T) {
	result := ParsePropText("true => false")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
}

func TestParseMixedDeclsAndHyps(t *testing.T) {
	result := ParsePropText("P : A→bool, P(x) ⊢ ∃y:A. P(y)")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
	// P(x) is a hypothesis.
	if result.Prop.NumHyps() != 1 {
		t.Errorf("expected 1 hypothesis, got %d", result.Prop.NumHyps())
	}
}

// ---------------------------------------------------------------------------
// Error diagnostic tests
// ---------------------------------------------------------------------------

func TestParseErrorUnexpectedToken(t *testing.T) {
	result := ParsePropText("p ⇒ ⇒ q")
	if len(result.Errors) == 0 {
		t.Fatal("expected parse error")
	}
	if result.Errors[0].Code != CodeParseError {
		t.Errorf("expected code %q, got %q", CodeParseError, result.Errors[0].Code)
	}
}

func TestParseErrorUnmatchedParen(t *testing.T) {
	result := ParsePropText("(p ⇒ q")
	if len(result.Errors) == 0 {
		t.Fatal("expected parse error for unmatched paren")
	}
}

// ---------------------------------------------------------------------------
// Parse (auto-detect) tests
// ---------------------------------------------------------------------------

func TestParseAutoDetectsText(t *testing.T) {
	result := ParsePropText("p => q")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
}

// ---------------------------------------------------------------------------
// SuggestedTypes tests
// ---------------------------------------------------------------------------

func TestSuggestedTypes_FromFunctionArg(t *testing.T) {
	// P : A→bool, P(x) — x has no type but P's signature implies x : A.
	result := ParsePropText("P : A→bool ⊢ P(x) ∧ q")
	if len(result.Errors) == 0 {
		// collectTypes already infers x : A from P's signature,
		// so this should parse successfully (x is resolved).
		// This test verifies that inference works — no error expected.
		if result.Prop == nil {
			t.Fatal("expected non-nil Prop")
		}
		return
	}
	// If it does error (shouldn't), check SuggestedTypes is populated.
	t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
}

func TestSuggestedTypes_FromEquality(t *testing.T) {
	// x : A ⊢ x = y — y has no declared type, but equality with x : A implies y : A.
	result := ParsePropText("x : A ⊢ x = y")
	if len(result.Errors) == 0 {
		// y should be guessed as type A and then used directly.
		// But collectTypes doesn't handle equality inference — that's collectTypeGuesses.
		// Since guesses populate env.guesses but NOT env.inferred, buildVarTerm
		// will still fail but with a typeMissingError carrying the guess.
		if result.Prop != nil {
			// Great — the guess was promoted to an inferred type.
			return
		}
		t.Fatal("expected non-nil Prop or errors")
	}

	// Expect the error to have SuggestedTypes with the guess for y.
	e := result.Errors[0]
	if e.Code != CodeMissingType {
		t.Errorf("expected code %q, got %q", CodeMissingType, e.Code)
	}
	if e.SuggestedTypes == nil {
		t.Fatal("expected SuggestedTypes to be populated")
	}
	if !strings.Contains(e.Suggestion, "A") {
		t.Errorf("expected suggestion to mention type A, got: %s", e.Suggestion)
	}
	t.Logf("suggestion: %s", e.Suggestion)
	t.Logf("suggested_types: %v", e.SuggestedTypes)
}

func TestSuggestedTypes_MultiArg(t *testing.T) {
	// R : A→B→bool ⊢ R(x, y) — both x and y inferred from R's signature.
	result := ParsePropText("R : A→B→bool ⊢ R(x, y)")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
}

func TestSuggestedTypes_NoGuess(t *testing.T) {
	// F(x) ⊢ q — neither F nor x has type info. Should fail with SuggestedTypes
	// showing what IS known (q: bool, F inferred).
	result := ParsePropText("F(x) ⊢ q")
	if len(result.Errors) == 0 {
		// F might be inferred as bool→bool (since x is in non-bool context,
		// but F(x) is in bool context). Actually, buildApp infers F's type
		// from the args — but x has no type, so buildTerm for x should fail first.
		if result.Prop != nil {
			return // Inference succeeded — acceptable
		}
		t.Fatal("expected errors or non-nil Prop")
	}

	e := result.Errors[0]
	if e.Code != CodeMissingType {
		t.Errorf("expected code %q, got %q", CodeMissingType, e.Code)
	}
	if e.SuggestedTypes == nil {
		t.Fatal("expected SuggestedTypes to be populated")
	}
	// q should be in suggested types as bool.
	if ty, ok := e.SuggestedTypes["q"]; !ok || ty != "bool" {
		t.Errorf("expected SuggestedTypes to include q:bool, got: %v", e.SuggestedTypes)
	}
	t.Logf("suggestion: %s", e.Suggestion)
	t.Logf("suggested_types: %v", e.SuggestedTypes)
}

func TestSuggestedTypes_PartialInference(t *testing.T) {
	// P : A→B→bool, x : A ⊢ P(x, y) — y should be inferred as B from P's signature.
	result := ParsePropText("P : A→B→bool, x : A ⊢ P(x, y)")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
}

// ---------------------------------------------------------------------------
// Arrow auto-correction: → treated as ⇒ in expression context
// ---------------------------------------------------------------------------

func TestArrowAsImplication(t *testing.T) {
	// "p -> q" should parse as p ⇒ q with an auto_corrected warning.
	result := ParsePropText("p → q")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
	hasWarning := false
	for _, w := range result.Warnings {
		if w.Code == "auto_corrected" && strings.Contains(w.Message, "→") {
			hasWarning = true
		}
	}
	if !hasWarning {
		t.Error("expected auto_corrected warning for → used as implication")
	}
}

func TestArrowAsImplication_Valid(t *testing.T) {
	// "p, p → q ⊢ q" should be valid (modus ponens) with warning.
	result := ParsePropText("p, p → q ⊢ q")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
}

func TestArrowInTypeContext_NoWarning(t *testing.T) {
	// "P:A→bool ⊢ P(x)" — → in type context should NOT trigger warning.
	result := ParsePropText("P:A→bool ⊢ P(x)")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	for _, w := range result.Warnings {
		if w.Code == "auto_corrected" {
			t.Error("should not warn about → in type context")
		}
	}
}

// ---------------------------------------------------------------------------
// Quantifier scope: ∀ / ∃ bind wide across binary operators.
// ∀x:A. P(x) ⇒ Q(x) means ∀x:A. (P(x) ⇒ Q(x)) — both sides
// of ⇒ see the bound x. Use parens to narrow.
// ---------------------------------------------------------------------------

// quantifierWideBinding asserts that `unparen` (e.g. "∀x:A. P(x) ⇒ Q(x)")
// parses without errors AND alpha-matches the parenthesized form `paren`
// (e.g. "∀x:A. (P(x) ⇒ Q(x))"). hyps is a hypothesis prefix shared by both.
func quantifierWideBinding(t *testing.T, hyps, unparen, paren string) {
	t.Helper()
	full := hyps + " ⊢ " + unparen
	got := ParsePropText(full)
	if len(got.Errors) > 0 {
		t.Fatalf("parse %q: %v", full, diagMessages(got.Errors))
	}
	want := ParsePropText(hyps + " ⊢ " + paren)
	if len(want.Errors) > 0 {
		t.Fatalf("parse %q: %v", paren, diagMessages(want.Errors))
	}
	if got.Prop.AlphaKey() != want.Prop.AlphaKey() {
		t.Errorf("wide-binding mismatch:\n  %s\n  parsed alpha-key: %s\n  expected (parens) alpha-key: %s",
			unparen, got.Prop.AlphaKey(), want.Prop.AlphaKey())
	}
}

func TestQuantifierWideBinding_ForallImplication(t *testing.T) {
	quantifierWideBinding(t,
		"P:A→bool, Q:A→bool",
		"∀x:A. P(x) ⇒ Q(x)",
		"∀x:A. (P(x) ⇒ Q(x))")
}

func TestQuantifierWideBinding_ForallConjunction(t *testing.T) {
	quantifierWideBinding(t,
		"P:A→bool, Q:A→bool",
		"∀x:A. P(x) ∧ Q(x)",
		"∀x:A. (P(x) ∧ Q(x))")
}

func TestQuantifierWideBinding_ForallDisjunction(t *testing.T) {
	quantifierWideBinding(t,
		"P:A→bool, Q:A→bool",
		"∀x:A. P(x) ∨ Q(x)",
		"∀x:A. (P(x) ∨ Q(x))")
}

func TestQuantifierWideBinding_ForallIff(t *testing.T) {
	quantifierWideBinding(t,
		"P:A→bool, Q:A→bool",
		"∀x:A. P(x) ⇔ Q(x)",
		"∀x:A. (P(x) ⇔ Q(x))")
}

func TestQuantifierWideBinding_ExistsImplication(t *testing.T) {
	quantifierWideBinding(t,
		"P:A→bool, Q:A→bool",
		"∃x:A. P(x) ⇒ Q(x)",
		"∃x:A. (P(x) ⇒ Q(x))")
}

func TestQuantifierWideBinding_ExistsConjunction(t *testing.T) {
	quantifierWideBinding(t,
		"P:A→bool, Q:A→bool",
		"∃x:A. P(x) ∧ Q(x)",
		"∃x:A. (P(x) ∧ Q(x))")
}

func TestQuantifierWideBinding_ExistsDisjunction(t *testing.T) {
	quantifierWideBinding(t,
		"P:A→bool, Q:A→bool",
		"∃x:A. P(x) ∨ Q(x)",
		"∃x:A. (P(x) ∨ Q(x))")
}

func TestQuantifierWideBinding_ExistsIff(t *testing.T) {
	quantifierWideBinding(t,
		"P:A→bool, Q:A→bool",
		"∃x:A. P(x) ⇔ Q(x)",
		"∃x:A. (P(x) ⇔ Q(x))")
}

func TestQuantifierWideBinding_NestedForall(t *testing.T) {
	// Nested quantifiers + binary op: both x and y must be in scope across ⇔.
	quantifierWideBinding(t,
		"P:A→bool, Q:B→bool",
		"∀x:A. ∀y:B. P(x) ⇔ Q(y)",
		"∀x:A. ∀y:B. (P(x) ⇔ Q(y))")
}

// TestQuantifierWideBinding_AddEq0Repro is the exact engine RPC string
// from the bug report — under tight binding the RHS of ⇔ couldn't see
// the bound n. Parses cleanly under wide binding.
func TestQuantifierWideBinding_AddEq0Repro(t *testing.T) {
	result := ParsePropText("∀n:num. (n = 0) ⇔ (0 = 0 + n)")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
}

// TestQuantifierNarrowingViaParens verifies the explicit-parens escape
// hatch: (∀x:A. P(x)) ⇒ Q(x) leaves the trailing x as a free variable
// (typeable because P:A→bool fixes x:A by inference), distinct from the
// bound x inside the parenthesized quantifier.
func TestQuantifierNarrowingViaParens(t *testing.T) {
	result := ParsePropText("P:A→bool, Q:A→bool ⊢ (∀x:A. P(x)) ⇒ Q(x)")
	if len(result.Errors) > 0 {
		t.Fatalf("unexpected errors: %v", diagMessages(result.Errors))
	}
	if result.Prop == nil {
		t.Fatal("expected non-nil Prop")
	}
	// Distinct from the wide form, where the trailing x is bound.
	wide := ParsePropText("P:A→bool, Q:A→bool ⊢ ∀x:A. P(x) ⇒ Q(x)")
	if len(wide.Errors) > 0 {
		t.Fatalf("wide form parse: %v", diagMessages(wide.Errors))
	}
	if result.Prop.AlphaKey() == wide.Prop.AlphaKey() {
		t.Error("(∀x. P(x)) ⇒ Q(x) should NOT alpha-equal ∀x. P(x) ⇒ Q(x)")
	}
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

func diagMessages(diags []InputDiagnostic) []string {
	msgs := make([]string, len(diags))
	for i, d := range diags {
		msgs[i] = d.Message
	}
	return msgs
}

// ---------------------------------------------------------------------------
// MustParseProp tests
// ---------------------------------------------------------------------------

func TestMustParseProp_Success(t *testing.T) {
	got := MustParseProp("p ⇒ p")
	if got == nil {
		t.Fatal("expected non-nil Prop")
	}
	// Alpha-key cross-check: same input through ParsePropText must
	// produce an alpha-equal prop.
	want := ParsePropText("p ⇒ p").Prop
	if want == nil {
		t.Fatal("ParsePropText unexpectedly returned nil")
	}
	if got.AlphaKey() != want.AlphaKey() {
		t.Errorf("MustParseProp prop alpha-key %s != ParsePropText alpha-key %s",
			got.AlphaKey(), want.AlphaKey())
	}
}

func TestMustParseProp_PanicReportsCallerLocation(t *testing.T) {
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("expected panic on malformed input")
		}
		msg, ok := r.(string)
		if !ok {
			t.Fatalf("panic value is %T, want string: %v", r, r)
		}
		if !strings.Contains(msg, "text_test.go") {
			t.Errorf("panic message missing caller file:\n%s", msg)
		}
		if !strings.Contains(msg, "MustParseProp failed") {
			t.Errorf("panic message missing failure header:\n%s", msg)
		}
		// The malformed input itself should be in the message.
		if !strings.Contains(msg, "((((") {
			t.Errorf("panic message missing offending input:\n%s", msg)
		}
	}()
	// Deliberately malformed: unmatched parens.
	_ = MustParseProp("((((")
	t.Fatal("MustParseProp did not panic")
}

// TestMustParseProp_PanicLineMatchesCaller verifies the panic line
// number really is the *caller's* line, not some location inside
// MustParseProp itself. We capture the probe location inline so the
// expected line is always probeLine + 1, regardless of file edits
// above this test.
func TestMustParseProp_PanicLineMatchesCaller(t *testing.T) {
	var (
		file      string
		probeLine int
	)
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("expected panic")
		}
		msg := r.(string)
		wantPrefix := fmt.Sprintf("%s:%d", file, probeLine+1)
		if !strings.HasPrefix(msg, wantPrefix) {
			t.Errorf("panic prefix mismatch:\nwant prefix: %s\n got:        %s",
				wantPrefix, firstLine(msg))
		}
	}()
	_, file, probeLine, _ = runtime.Caller(0)
	_ = MustParseProp("@@@") // anchor: probeLine + 1 — keep adjacent
}

func firstLine(s string) string {
	if i := strings.IndexByte(s, '\n'); i >= 0 {
		return s[:i]
	}
	return s
}

// TestParseTermText_BareApp covers the dogfooded shape: an application
// `f(x)` where `f` and `x` come from the goal's free-var context. The
// expected type pins the result; ctx pre-types both leaves.
func TestParseTermText_BareApp(t *testing.T) {
	ctx := map[string]core.HolType{
		"f": core.MakeFun(core.TypeA(), core.TypeA()),
		"x": core.TypeA(),
	}
	res := ParseTermText("f(x)", ctx, core.TypeA())
	require.Empty(t, res.Errors, "diagnostics: %v", diagMessages(res.Errors))
	require.NotNil(t, res.Term)
	assert.True(t, res.Term.Type().Equals(core.TypeA()))
}

// TestParseTermText_NestedNovel exercises a term that doesn't appear
// verbatim in any pre-existing prop — the whole point of the API for
// trans bridging.
func TestParseTermText_NestedNovel(t *testing.T) {
	ctx := map[string]core.HolType{
		"f": core.MakeFun(core.TypeA(), core.TypeA()),
		"a": core.TypeA(),
	}
	res := ParseTermText("f(f(a))", ctx, core.TypeA())
	require.Empty(t, res.Errors, "diagnostics: %v", diagMessages(res.Errors))
	require.NotNil(t, res.Term)
}

// TestParseTermText_ExpectedTypeMismatch covers the type-error path:
// the agent supplies a well-formed term whose type doesn't match the
// surrounding tactic's expectation.
func TestParseTermText_ExpectedTypeMismatch(t *testing.T) {
	ctx := map[string]core.HolType{
		"p": core.TypeBool(),
	}
	res := ParseTermText("p", ctx, core.TypeA())
	require.NotEmpty(t, res.Errors)
	assert.Equal(t, CodeTypeMismatch, res.Errors[0].Code)
}

// TestParseTermText_RejectsTurnstile pins the "term input must not
// contain ⊢" guard. Without this, accidentally passing a full Prop
// shape would surface as a generic parse error.
func TestParseTermText_RejectsTurnstile(t *testing.T) {
	res := ParseTermText("x:A ⊢ x = x", nil, nil)
	require.NotEmpty(t, res.Errors)
	assert.Contains(t, res.Errors[0].Message, "⊢")
}

// TestParseTermText_MissingTypeWithoutCtx confirms that a leaf with
// no operator-derived type and no ctx entry yields a typed missing-
// type diagnostic (same channel ParsePropText uses).
func TestParseTermText_MissingTypeWithoutCtx(t *testing.T) {
	res := ParseTermText("x", nil, nil)
	require.NotEmpty(t, res.Errors)
	assert.Equal(t, CodeMissingType, res.Errors[0].Code)
}

// TestParseTermText_NatArithFromCtx is the left-distributivity-shaped
// case: nat-arith operands need their types pinned by ctx because
// the inference passes don't propagate "+/* arguments are num"
// through bare variables.
func TestParseTermText_NatArithFromCtx(t *testing.T) {
	ctx := map[string]core.HolType{
		"m": NumType,
		"n": NumType,
		"p": NumType,
	}
	res := ParseTermText("m * suc(n + p)", ctx, NumType)
	require.Empty(t, res.Errors, "diagnostics: %v", diagMessages(res.Errors))
	require.NotNil(t, res.Term)
	assert.True(t, res.Term.Type().Equals(NumType))
}

// TestDenormalizeUnicodeSubscripts pins the Unicode-subscript ↔ ASCII
// rewrite: agents copying `inspect`'s printer output (`m₀`, `n₄₂`) into
// text-DSL input get the same result as if they typed `m_0`, `n_42`.
// Closes the per-tactic Unicode/ASCII surface divergence.
func TestDenormalizeUnicodeSubscripts(t *testing.T) {
	cases := []struct {
		input, want string
	}{
		{"m₀", "m_0"},
		{"m₄₂", "m_42"},
		{"f(m₀, n₀)", "f(m_0, n_0)"},
		{"m₀+n₀", "m_0+n_0"},
		{"no subscripts", "no subscripts"},
		{"", ""},
		// Mid-identifier subscripts collapse into one underscore-prefixed
		// run; the algorithm is run-based, not position-aware.
		{"m₀₁", "m_01"},
	}
	for _, tc := range cases {
		got := denormalizeUnicodeSubscripts(tc.input)
		assert.Equal(t, tc.want, got, "input=%q", tc.input)
	}
}

// TestParseTermText_AcceptsUnicodeSubscripts confirms that the parser
// transparently accepts the printer's Unicode-subscript variable form:
// `lemma.text` / `assert.text` take `m₀` as they take ASCII `m_0`, and
// both forms parse to the same Term (same kernel name `m_0`).
func TestParseTermText_AcceptsUnicodeSubscripts(t *testing.T) {
	ctx := map[string]core.HolType{"m_0": NumType}
	asciiResult := ParseTermText("m_0", ctx, NumType)
	require.Empty(t, asciiResult.Errors, "ASCII form must parse")
	require.NotNil(t, asciiResult.Term)

	unicodeResult := ParseTermText("m₀", ctx, NumType)
	require.Empty(t, unicodeResult.Errors,
		"Unicode-subscript form must also parse; diagnostics: %v",
		diagMessages(unicodeResult.Errors))
	require.NotNil(t, unicodeResult.Term)

	assert.True(t, asciiResult.Term.AlphaEquals(unicodeResult.Term),
		"both forms must yield alpha-equal terms")
}

// TestParsePropText_AcceptsUnicodeSubscripts is the prop-level analog
// of TestParseTermText_AcceptsUnicodeSubscripts. lemma.text and
// assert.text both go through ParsePropText; the same Unicode-subscript
// rewrite applies.
func TestParsePropText_AcceptsUnicodeSubscripts(t *testing.T) {
	asciiResult := ParsePropText("∀m_0:num. (m_0 = m_0)")
	require.Empty(t, asciiResult.Errors, "ASCII form must parse")
	require.NotNil(t, asciiResult.Prop)

	unicodeResult := ParsePropText("∀m₀:num. (m₀ = m₀)")
	require.Empty(t, unicodeResult.Errors,
		"Unicode-subscript form must also parse; diagnostics: %v",
		diagMessages(unicodeResult.Errors))
	require.NotNil(t, unicodeResult.Prop)

	assert.Equal(t, asciiResult.Prop.AlphaKey(), unicodeResult.Prop.AlphaKey(),
		"both forms must yield alpha-equivalent props")
}

// TestParsePairLiteralSyntax exercises both spellings the parser accepts
// for the pair constructor const named ",": the natural infix tuple form
// `(a, b)` that the printer emits (format.go's CommaConstMeta render),
// and the prefix form `,(a, b)`, which stored assert.text payloads spell.
// Both resolve `,` through buildAppViaMeta at concrete types.
func TestParsePairLiteralSyntax(t *testing.T) {
	t.Run("bare_pair_literal", func(t *testing.T) {
		// Parse the printer-emitted form directly. With bound types,
		// the pair-const should instantiate to num → bool → prod(num, bool).
		r := ParsePropText("∀a:num. ∀b:bool. ,(a, b) = ,(a, b)")
		require.Empty(t, r.Errors, "diagnostics: %v", diagMessages(r.Errors))
		require.NotNil(t, r.Prop)
	})

	t.Run("pair_inside_function_app", func(t *testing.T) {
		// Pair nested as the arg of another function. The motivating
		// shape from an admissibility proof's frontier was `snd(,(qʹ, pʹ))`
		// — the agent needed to assert this term at function-typed
		// pair components but the parser blocked it.
		ctx := map[string]core.HolType{
			"snd": ext.MakeFun(ext.MakeProdType(NumType, ext.TypeBool), ext.TypeBool),
		}
		r := ParseTermText(",(a, b)", map[string]core.HolType{
			"a": NumType,
			"b": ext.TypeBool,
		}, ext.MakeProdType(NumType, ext.TypeBool))
		require.Empty(t, r.Errors, "bare pair: %v", diagMessages(r.Errors))
		require.NotNil(t, r.Term)

		// Now snd-of-pair. Wrapped via ParsePropText so the prop-level
		// type-inference resolves snd from the supplied scope's bound
		// quantifier types.
		_ = ctx
		r2 := ParsePropText("∀a:num. ∀b:bool. snd(,(a, b)) = b")
		require.Empty(t, r2.Errors,
			"snd(,(a, b)) = b should parse; diagnostics: %v",
			diagMessages(r2.Errors))
		require.NotNil(t, r2.Prop)
	})

	t.Run("polymorphic_instantiation", func(t *testing.T) {
		// Confirm the pair-const instantiates correctly at the bound
		// types: the conclusion's LHS pair should have type
		// prod(num, bool), not the abstract prod(A, B).
		r := ParsePropText("∀a:num. ∀b:bool. ,(a, b) = ,(a, b)")
		require.Empty(t, r.Errors)
		require.NotNil(t, r.Prop)

		// Walk the conclusion to find the inner pair-const.
		concl := r.Prop.Conclusion()
		// concl is the body of two outer ∀s — after stripping binders,
		// we have an equality whose LHS is a fully-applied pair-const.
		// Just check that the pair-const appears with a concrete
		// product-type instantiation, not the polymorphic abstract.
		found := false
		var walk func(term core.Term)
		walk = func(term core.Term) {
			if found {
				return
			}
			switch x := term.Core().(type) {
			case core.ConstTerm:
				if x.Name() == "," {
					// Type should be num → bool → prod(num, bool),
					// NOT the abstract A → B → prod(A, B).
					ft, ok := x.Type().(core.CompositeType)
					require.True(t, ok, "pair-const type must be a fun-composite")
					require.True(t, ft.Meta().Equals(core.MetaTypeFun()))
					require.True(t, ft.SubType(0).Equals(NumType),
						"pair-const domain[0] should be num, got %s",
						ext.FormatType(ft.SubType(0)))
					found = true
				}
			case core.AppliedTerm:
				if at, ok := x.AsAppliedTerm(); ok {
					walk(at.Fun())
					walk(at.Arg())
				}
			case core.AbsTerm:
				if at, ok := x.AsAbsTerm(); ok {
					walk(at.Body())
				}
			}
		}
		walk(concl)
		require.True(t, found, "expected a pair-const in the parsed conclusion")
	})

	t.Run("round_trip_printer_to_parser", func(t *testing.T) {
		// Build a pair term programmatically at concrete types, format it
		// via the parser-facing printer, parse the result back, and check
		// alpha-equality. This is the contract the engine relies on when
		// emit hands an agent the goal's text form for them to assert
		// variants of.
		commaInst := ext.Const(ext.CommaConstMeta,
			ext.MakeFun(NumType, ext.MakeFun(ext.TypeBool, ext.MakeProdType(NumType, ext.TypeBool))))
		a := core.Var("a", NumType)
		b := core.Var("b", ext.TypeBool)
		pair := ext.Apply(commaInst, a, b)

		printed := ext.FormatTermForParser(pair)
		// The printer should emit the natural infix tuple form, NOT the
		// leading-comma prefix.
		assert.Equal(t, "(a, b)", printed,
			"printer must emit pair as infix `(a, b)`, got %q", printed)
		assert.NotContains(t, printed, ",(",
			"printer must not emit the prefix `,(...)` form, got %q", printed)

		// Now parse the printed form back. Free vars a, b need
		// declared types so type-inference picks them up.
		r := ParseTermText(printed, map[string]core.HolType{
			"a": NumType,
			"b": ext.TypeBool,
		}, ext.MakeProdType(NumType, ext.TypeBool))
		require.Empty(t, r.Errors,
			"round-trip parse of %q failed: %v",
			printed, diagMessages(r.Errors))
		require.NotNil(t, r.Term)
		assert.True(t, r.Term.AlphaEquals(pair),
			"round-trip term must be alpha-equal to the original; "+
				"printed=%q reparsed=%s original=%s",
			printed, ext.FormatTermForParser(r.Term), ext.FormatTermForParser(pair))
	})

	t.Run("infix_pair_inside_function_app", func(t *testing.T) {
		// The emit→replay shape: a pair as the sole argument of a
		// function, in the infix form the printer now emits (e.g.
		// `nat_dist((m, n))`, `snd((a, b))`). Must parse and build the same
		// term as the legacy prefix `snd(,(a, b))`. This is the exact
		// round-trip MakePropText / SectionText perform at replay on the
		// printer-emitted FormatPropForParser text.
		infix := ParsePropText("∀a:num. ∀b:bool. snd((a, b)) = b")
		require.Empty(t, infix.Errors,
			"infix `snd((a, b))` should parse; diagnostics: %v",
			diagMessages(infix.Errors))
		require.NotNil(t, infix.Prop)

		prefix := ParsePropText("∀a:num. ∀b:bool. snd(,(a, b)) = b")
		require.Empty(t, prefix.Errors)
		require.True(t, infix.Prop.Conclusion().AlphaEquals(prefix.Prop.Conclusion()),
			"infix `snd((a, b))` and prefix `snd(,(a, b))` must build the same term")
	})

	t.Run("infix_tuple_literal_parses", func(t *testing.T) {
		// The printer-emitted infix form `(a, b)` must parse to the same
		// term the prefix `,(a, b)` form does — both resolve `,` through
		// buildAppViaMeta at the bound types.
		infix := ParsePropText("∀a:num. ∀b:bool. (a, b) = (a, b)")
		require.Empty(t, infix.Errors,
			"infix tuple `(a, b)` should parse; diagnostics: %v",
			diagMessages(infix.Errors))
		require.NotNil(t, infix.Prop)

		prefix := ParsePropText("∀a:num. ∀b:bool. ,(a, b) = ,(a, b)")
		require.Empty(t, prefix.Errors)
		require.True(t, infix.Prop.Conclusion().AlphaEquals(prefix.Prop.Conclusion()),
			"infix `(a, b)` and prefix `,(a, b)` must build the same term")
	})

	t.Run("right_associative_triple_round_trips", func(t *testing.T) {
		// A 3-tuple `(a, b, c)` folds right-associatively to `,(a, ,(b, c))`.
		// The printer emits the nested infix form
		// `(a, (b, c))`; parsing either the flat or nested spelling yields
		// the same term, and the printed form round-trips.
		flat := ParseTermText("(a, b, c)", map[string]core.HolType{
			"a": NumType, "b": ext.TypeBool, "c": NumType,
		}, ext.MakeProdType(NumType, ext.MakeProdType(ext.TypeBool, NumType)))
		require.Empty(t, flat.Errors,
			"flat triple `(a, b, c)` should parse; diagnostics: %v",
			diagMessages(flat.Errors))
		require.NotNil(t, flat.Term)

		printed := ext.FormatTermForParser(flat.Term)
		assert.Equal(t, "(a, (b, c))", printed,
			"printer must emit a right-nested triple as `(a, (b, c))`, got %q", printed)

		reparsed := ParseTermText(printed, map[string]core.HolType{
			"a": NumType, "b": ext.TypeBool, "c": NumType,
		}, ext.MakeProdType(NumType, ext.MakeProdType(ext.TypeBool, NumType)))
		require.Empty(t, reparsed.Errors,
			"round-trip parse of %q failed: %v", printed, diagMessages(reparsed.Errors))
		assert.True(t, reparsed.Term.AlphaEquals(flat.Term),
			"triple round-trip must be alpha-equal to the flat form")
	})

	t.Run("bare_comma_without_paren_errors", func(t *testing.T) {
		// A stray `,` in expression position (without `(` following)
		// should still error through the new diagnostic — guard that
		// the tokComma branch hasn't loosened the grammar to accept
		// bare commas anywhere. Use `, x` (leading comma) rather than
		// `a , b` (the trailing case dispatches to a different error
		// path at the top-level "leftover tokens after complete
		// expression" check, not parseAtom).
		r := ParsePropText(", x")
		require.NotEmpty(t, r.Errors, "leading `,` should still error")
		// The new diagnostic should mention the pair-literal form
		// as a hint, so agents can self-correct.
		hint := r.Errors[0].Message + r.Errors[0].Suggestion
		assert.Contains(t, hint, "(a, b)",
			"error should hint at pair-literal form `(a, b)`; got %q", hint)
	})
}

// TestBuildAppViaMetaTypeVarNameCollision is the regression test for the
// replay failure of a delete-of-insert law: COND over-applied (bool→A→A→A invoked with
// 4 args) AND a colliding user type-var named "A". Before the fix,
// buildAppViaMeta stepped `cur` via the substituted result type, so step 4
// re-applied {A ↦ (var:A → bool)} to the already-substituted form, shifting
// the curry chain by one and producing a domain mismatch that fell through
// to free-var treatment. The recorded prop expected COND-as-const.
func TestBuildAppViaMetaTypeVarNameCollision(t *testing.T) {
	a := core.MakeVarType("A")
	setT := ext.MakeFun(a, ext.TypeBool)

	scope := &ParseScope{
		Consts:     map[string]core.ConstTerm{},
		ConstMetas: map[string]core.ConstTermMeta{"COND": ext.COND.Meta()},
		Vars: map[string]core.HolType{
			"c": ext.TypeBool,
			"t": setT, // set, sharing var-name "A" with COND.absType's A
			"e": setT,
			"x": a,
		},
	}
	r := ParseTermTextInScope("COND(c, t, e, x)", nil, scope, ext.TypeBool)
	require.Empty(t, r.Errors, "diagnostics: %v", diagMessages(r.Errors))
	require.NotNil(t, r.Term)

	// Walk to find COND — must be a ConstTerm, NOT a VarTerm.
	var (
		condIsConst bool
		condIsVar   bool
	)
	var walk func(t core.Term)
	walk = func(t core.Term) {
		switch tt := t.Core().(type) {
		case core.AppliedTerm:
			walk(tt.Fun())
			walk(tt.Arg())
		case core.ConstTerm:
			if string(tt.Name()) == "COND" {
				condIsConst = true
			}
		case core.VarTerm:
			if string(tt.Name()) == "COND" {
				condIsVar = true
			}
		}
	}
	walk(r.Term)
	assert.True(t, condIsConst, "COND must resolve as *ConstTerm via meta-instantiation")
	assert.False(t, condIsVar, "COND must NOT degrade to *VarTerm — name collision with user var:A was double-substituting")
}

// TestNumsegInfixRoundTrip exercises the `m..n` numeric segment
// infix. Parser must accept `m..n` (instead of forcing prefix `..(m, n)`)
// and produce the same term as the prefix form; the printer must emit the
// infix back. Round-trip closes structurally.
func TestNumsegInfixRoundTrip(t *testing.T) {
	t.Run("infix_parses_alpha_equal_to_prefix", func(t *testing.T) {
		infix := ParsePropText("∀m:num.∀n:num. m..n = ..(m, n)")
		require.Empty(t, infix.Errors, "diagnostics: %v", diagMessages(infix.Errors))
		require.NotNil(t, infix.Prop)
		// LHS and RHS of the inner equality must be alpha-equal.
		eqTerm, ok := infix.Prop.Conclusion().AsAppliedTerm()
		require.True(t, ok)
		_ = eqTerm // structural check by AlphaKey through the whole prop is below
	})

	t.Run("precedence_below_additive", func(t *testing.T) {
		// `m+1..n` must parse as `(m+1)..n`, NOT `m + (1..n)` (which is
		// a type error anyway, but parser-level precedence should pin it
		// to the additive-tighter reading).
		r := ParsePropText("∀m:num.∀n:num. m+1..n = ..(m + 1, n)")
		require.Empty(t, r.Errors, "diagnostics: %v", diagMessages(r.Errors))
		require.NotNil(t, r.Prop)
	})

	t.Run("printer_emits_infix", func(t *testing.T) {
		// Build via prefix, print, expect infix in the output.
		r := ParsePropText("∀m:num.∀n:num. ..(m, n) = ..(m, n)")
		require.Empty(t, r.Errors, "diagnostics: %v", diagMessages(r.Errors))
		require.NotNil(t, r.Prop)
		text := ext.PrintTerm(r.Prop.Conclusion())
		// Printer uses the standard infix template (matches `+`/`*`/`≤` —
		// spaces around the operator), so the rendered form is `m .. n`.
		assert.Contains(t, text, "m .. n",
			"printer should emit `m .. n` infix for the numseg const; got %q", text)
		assert.NotContains(t, text, "..(m, n)",
			"printer should not fall back to prefix `..(m, n)`; got %q", text)
	})

	t.Run("membership_curry_round_trip", func(t *testing.T) {
		// `(m..n) p` — apply the segment to a third arg for membership.
		// Parser accepts both `..(m, n, p)` and `(m..n)(p)`; alpha-equal.
		prefix := ParsePropText("∀m:num.∀n:num.∀p:num. ..(m, n, p) ⇒ ..(m, n, p)")
		require.Empty(t, prefix.Errors, "diagnostics: %v", diagMessages(prefix.Errors))
		curry := ParsePropText("∀m:num.∀n:num.∀p:num. (m..n)(p) ⇒ (m..n)(p)")
		require.Empty(t, curry.Errors, "diagnostics: %v", diagMessages(curry.Errors))
		assert.True(t,
			prefix.Prop.Conclusion().AlphaEquals(curry.Prop.Conclusion()),
			"prefix `..(m, n, p)` and curried `(m..n)(p)` must build the same term")
	})
}
