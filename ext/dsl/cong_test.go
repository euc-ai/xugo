package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// congNumTerm builds the reference term nat_cong(x, y, m) — ℕ's own
// congruence, a three-place relation.
func congNumTerm(x, y, m core.Term) core.Term {
	tm, err := buildAppViaMeta(newTypeEnv(), NatCongMeta, []core.Term{x, y, m})
	if err != nil {
		panic(err)
	}
	return tm
}

// congIntTerm builds int_cong(x, y, m) — ℤ's congruence, the same
// three-place shape as ℕ's.
func congIntTerm(x, y, m core.Term) core.Term {
	tm, err := buildAppViaMeta(newTypeEnv(), IntCongMeta, []core.Term{x, y, m})
	if err != nil {
		panic(err)
	}
	return tm
}

// TestCongMixfix pins the `x ≡ y (mod m)` congruence surface: dispatched
// to nat_cong / int_cong by operand type, `&` coercion operands forced to
// int (num is impossible for a coercion and real is not dispatched),
// relational precedence, real operands rejected toward the application
// form, and equivalence with the longhand `nat_cong(x, y, m)`.
func TestCongMixfix(t *testing.T) {
	x := core.Var("x", NumType)
	y := core.Var("y", NumType)
	n := core.Var("n", NumType)
	numVars := map[string]core.HolType{"x": NumType, "y": NumType, "n": NumType}

	// num operands → nat_cong.
	got, errs := parseReal(t, "x ≡ y (mod n)", numVars, core.TypeBool())
	if len(errs) > 0 {
		t.Fatalf("num ≡ parse: %v", errs)
	}
	if want := congNumTerm(x, y, n); !got.AlphaEquals(want) {
		t.Errorf("num ≡ built %v, want %v", got, want)
	}

	// The mixfix and the longhand application build the identical term.
	// The longhand needs the meta in scope (production texts get it from
	// the family vocab or the registry resolver; the mixfix carries its
	// own surface metas, scope-first).
	longScope := &ParseScope{ConstMetas: map[string]core.ConstTermMeta{
		"nat_cong": NatCongMeta,
	}}
	lr := ParseTermTextInScope("nat_cong(x, y, n)", numVars, longScope, core.TypeBool())
	if len(lr.Errors) > 0 {
		t.Fatalf("longhand parse: %v", lr.Errors)
	}
	if !got.AlphaEquals(lr.Term) {
		t.Errorf("mixfix %v ≠ longhand %v", got, lr.Term)
	}

	// int operands → int_cong.
	xi := core.Var("x", IntType)
	yi := core.Var("y", IntType)
	ni := core.Var("n", IntType)
	got, errs = parseReal(t, "x ≡ y (mod n)",
		map[string]core.HolType{"x": IntType, "y": IntType, "n": IntType}, core.TypeBool())
	if len(errs) > 0 {
		t.Fatalf("int ≡ parse: %v", errs)
	}
	if want := congIntTerm(xi, yi, ni); !got.AlphaEquals(want) {
		t.Errorf("int ≡ built %v, want %v", got, want)
	}

	// `&` coercion operands always mean int under ≡: `&x ≡ &y (mod &n)`
	// with x, y, n : num builds int_of_num embeddings and int_cong.
	got, errs = parseReal(t, "&x ≡ &y (mod &n)", numVars, core.TypeBool())
	if len(errs) > 0 {
		t.Fatalf("coercion ≡ parse: %v", errs)
	}
	emb := func(v core.Term) core.Term { return ext.Apply(IntOfNumMeta.Term(), v) }
	if want := congIntTerm(emb(x), emb(y), emb(n)); !got.AlphaEquals(want) {
		t.Errorf("coercion ≡ built %v, want %v", got, want)
	}

	// Application operands: `nat_mod(x, n) ≡ y (mod n)` — the reduced-side
	// shape (nat_congruence.ModLeft's). The spine must NOT curry `(mod n)` onto the
	// preceding application.
	got, errs = parseReal(t, "nat_mod(x, n) ≡ y (mod n)", numVars, core.TypeBool())
	if len(errs) > 0 {
		t.Fatalf("application-operand ≡ parse: %v", errs)
	}
	modxn := ext.Apply(NatModMeta.Term(), x, n)
	if want := congNumTerm(modxn, y, n); !got.AlphaEquals(want) {
		t.Errorf("application-operand ≡ built %v, want %v", got, want)
	}

	// Right-operand application: `x ≡ nat_mod(y, n) (mod n)` (nat_congruence.ModRight's
	// shape) — the trailing-group guard again, on the right slot.
	got, errs = parseReal(t, "x ≡ nat_mod(y, n) (mod n)", numVars, core.TypeBool())
	if len(errs) > 0 {
		t.Fatalf("right-application ≡ parse: %v", errs)
	}
	modyn := ext.Apply(NatModMeta.Term(), y, n)
	if want := congNumTerm(x, modyn, n); !got.AlphaEquals(want) {
		t.Errorf("right-application ≡ built %v, want %v", got, want)
	}

	// Relational precedence: arith binds tighter (`x + y ≡ y (mod n)`),
	// and ⇔ binds looser (`x ≡ y (mod n) ⇔ x ≡ y (mod n)`).
	got, errs = parseReal(t, "x + y ≡ y (mod n)", numVars, core.TypeBool())
	if len(errs) > 0 {
		t.Fatalf("precedence parse: %v", errs)
	}
	if want := congNumTerm(ext.Apply(NatPlusMeta.Term(), x, y), y, n); !got.AlphaEquals(want) {
		t.Errorf("precedence built %v, want %v", got, want)
	}
	if _, errs = parseReal(t, "x ≡ y (mod n) ⇔ x ≡ y (mod n)", numVars, core.TypeBool()); len(errs) > 0 {
		t.Fatalf("⇔ level parse: %v", errs)
	}

	// Real operands rejected.
	_, errs = parseReal(t, "a ≡ b (mod c)",
		map[string]core.HolType{"a": RealType, "b": RealType, "c": RealType}, core.TypeBool())
	if len(errs) == 0 {
		t.Errorf("real ≡ must be rejected")
	}

	// A bare `x ≡ y` without the modulus clause is a parse error.
	_, errs = parseReal(t, "x ≡ y", numVars, core.TypeBool())
	if len(errs) == 0 {
		t.Errorf("≡ without (mod …) must be rejected")
	} else if !strings.Contains(errs[0].Message, "modulus") {
		t.Errorf("diagnostic should name the modulus clause, got: %v", errs[0].Message)
	}
}

// TestCongPrint pins the printer half: nat_cong and int_cong render as
// the mixfix, and print → parse round-trips — including
// the mixed ℕ⇔ℤ transfer statement, which needs no ⟨A:τ⟩ annotations in
// sugar form because both instances re-derive from operand types.
func TestCongPrint(t *testing.T) {
	x := core.Var("x", NumType)
	y := core.Var("y", NumType)
	n := core.Var("n", NumType)

	s := ext.FormatTermForParser(congNumTerm(x, y, n))
	if want := "x ≡ y (mod n)"; s != want {
		t.Errorf("num print = %q, want %q", s, want)
	}

	// int instance, embedded operands: int_of_num prints longhand (the
	// `&` re-parse ambiguity keeps it that way), inside the mixfix.
	emb := func(v core.Term) core.Term { return ext.Apply(IntOfNumMeta.Term(), v) }
	s = ext.FormatTermForParser(congIntTerm(emb(x), emb(y), emb(n)))
	if want := "int_of_num(x) ≡ int_of_num(y) (mod int_of_num(n))"; s != want {
		t.Errorf("int print = %q, want %q", s, want)
	}

	// Round-trips, including the transfer statement both ways and the
	// reduced-side shapes.
	assertRoundTrip(t, "∀x:num.∀y:num.∀n:num.(x ≡ y (mod n))")
	assertRoundTrip(t, "∀x:num.∀y:num.∀n:num.(x ≡ y (mod n) ⇔ nat_mod(x, n) = nat_mod(y, n))")
	assertRoundTrip(t, "∀x:num.∀y:num.∀n:num.(x ≡ y (mod n) ⇔ nat_mod(x, n) ≡ y (mod n))")
	assertRoundTrip(t,
		"∀x:num.∀y:num.∀n:num.(x ≡ y (mod n) ⇔ &x ≡ &y (mod &n))")
}
