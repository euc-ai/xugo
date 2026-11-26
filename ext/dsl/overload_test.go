package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
)

// overloadTestScope is a toy corpus of overloaded words: `sum` on three
// carriers' sums, `sup` on one constant, and `dist` on two constants of
// different arity. The constants reach the parse the way the corpus's
// do — through the scope's resolver, never declared by the caller —
// and the resolver also serves a HOL-like constant literally named
// `sum`, which the word must outrank.
func overloadTestScope(t *testing.T) *ParseScope {
	t.Helper()
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatalf("type %q: %v", text, err)
		}
		return ty
	}
	metas := map[string]core.ConstTermMeta{}
	syntax := testSyntax{}
	declare := func(name, ty, word string) {
		metas[name] = core.MakeConstMeta(core.TermName(name), typ(ty))
		if word != "" {
			syntax[name] = &ConstSyntax{Overload: &Overload{Word: word, Arity: funArity(typ(ty)), Type: typ(ty)}}
		}
	}
	declare("real_sum", "(A → bool) → (A → real) → real", "sum")
	declare("nat_sum", "(A → bool) → (A → num) → num", "sum")
	declare("int_sum", "(A → bool) → (A → int) → int", "sum")
	declare("real_sup", "(real → bool) → real", "sup")
	declare("nat_dist", "prod(num, num) → num", "dist")
	declare("vec_dist", "num → (num → real) → (num → real) → real", "dist")
	// A resolver constant named `sum`, which the
	// overloaded word must outrank.
	declare("sum", "(A → bool) → (A → real) → real", "")
	syntax["real_sum"].BigOp = &BigOp{Symbol: "Σ", Carrier: RealType}
	syntax["nat_sum"].BigOp = &BigOp{Symbol: "Σ", Carrier: NumType}
	return &ParseScope{
		ConstResolver: func(name string) core.ConstTermMeta { return metas[name] },
		Syntax:        syntax,
	}
}

func TestOverload_PicksByArguments(t *testing.T) {
	scope := overloadTestScope(t)
	for _, c := range []struct{ short, long string }{
		// the summand's values pick the carrier
		{"∀s:(num → bool). ∀f:(num → real). sum(s, f) = sum(s, f)",
			"∀s:(num → bool). ∀f:(num → real). real_sum(s, f) = real_sum(s, f)"},
		{"∀s:(num → bool). ∀f:(num → num). sum(s, f) = 0",
			"∀s:(num → bool). ∀f:(num → num). nat_sum(s, f) = 0"},
		{"∀s:(num → bool). ∀f:(num → int). sum(s, f) = sum(s, f)",
			"∀s:(num → bool). ∀f:(num → int). int_sum(s, f) = int_sum(s, f)"},
		// a λ summand: its body's type decides, as Σ's does
		{"∀n:num. sum({i:num | i < n}, λi:num. &i) = &0",
			"∀n:num. real_sum({i:num | i < n}, λi:num. &i) = &0"},
		{"∀n:num. sum({i:num | i < n}, λi:num. i) = 0",
			"∀n:num. nat_sum({i:num | i < n}, λi:num. i) = 0"},
		// one constant under the word: its domains type the arguments
		{"∀s:(real → bool). sup(s) = sup(s)",
			"∀s:(real → bool). real_sup(s) = real_sup(s)"},
		// the number of arguments picks first
		{"∀m n:num. dist((m, n)) = dist((n, m))",
			"∀m n:num. nat_dist((m, n)) = nat_dist((n, m))"},
		{"∀k:num. ∀u v:(num → real). dist(k, u, v) = dist(k, v, u)",
			"∀k:num. ∀u v:(num → real). vec_dist(k, u, v) = vec_dist(k, v, u)"},
		// the word outranks a resolver's constant of the same name
		{"∀s:(num → bool). ∀f:(num → real). sum(s, f) = &0",
			"∀s:(num → bool). ∀f:(num → real). real_sum(s, f) = &0"},
	} {
		assertSameProp(t, scope, c.short, c.long)
	}
}

func TestOverload_ANameInTheTextShadowsTheWord(t *testing.T) {
	scope := overloadTestScope(t)
	for _, text := range []string{
		"∀sum:(num → num). sum(1) = sum(1)",
		"sum:(num → num) ⊢ sum(1) = sum(1)",
	} {
		p := prop.PrintProp(parseImplicit(t, scope, text))
		if strings.Contains(p, "real_sum") || strings.Contains(p, "nat_sum") {
			t.Fatalf("%q: a bound or declared `sum` must stay the variable, got %s", text, p)
		}
	}
}

func TestOverload_Refusals(t *testing.T) {
	scope := overloadTestScope(t)
	strict := *scope
	strict.StrictResolution = true
	for _, c := range []struct {
		scope *ParseScope
		text  string
		want  string
	}{
		{scope, "∀s:(num → bool). sum(s) = &0", "takes no 1 arguments"},
		{scope, "∀s:(A → bool). ∀f:(A → B). sum(s, f) = sum(s, f)", "none of"},
		// A bare word where no position type reaches it: `sum` is the
		// equation's own operand, typed by nothing.
		{&strict, "∀s:(A → bool). ∀f:(A → real). sum = sum", "overloaded word"},
		{scope, "∀s:(num → bool). ∀f:(num → real). sum⟨A:num⟩(s, f) = &0", "overloaded word"},
	} {
		res := ParsePropTextInScope(c.text, c.scope)
		if len(res.Errors) == 0 {
			t.Fatalf("%q must be refused", c.text)
		}
		if !strings.Contains(res.Errors[0].Message, c.want) {
			t.Fatalf("%q: the refusal should say %q, got: %s", c.text, c.want, res.Errors[0].Message)
		}
	}
}

func TestOverload_ChapterSpellingFoldsToTheWord(t *testing.T) {
	scope := overloadTestScope(t)
	long := "∀s:(num → bool). ∀f:(num → real). ∀m n:num. real_sum(s, f) ≤ real_sup({x:real | x < &1}) ∧ nat_dist((m, n)) = nat_dist((n, m))"
	out, err := ChapterSpelling(long, scope.Syntax, nil)
	if err != nil {
		t.Fatal(err)
	}
	for _, frag := range []string{"sum(s, f)", "sup({x:real | x < &1})", "dist((m, n))"} {
		if !strings.Contains(out, frag) {
			t.Errorf("chapter spelling lacks %q: %s", frag, out)
		}
	}
	for _, name := range []string{"real_sum", "real_sup", "nat_dist"} {
		if strings.Contains(out, name) {
			t.Errorf("chapter spelling still spells %s: %s", name, out)
		}
	}
	assertSameProp(t, scope, out, long)

	// A λ summand is a big operator first: the binder, not the word.
	sigma, err := ChapterSpelling("∀n:num. real_sum({i:num | i < n}, λi:num. &i) = &0", scope.Syntax, nil)
	if err != nil || !strings.Contains(sigma, "Σ_{") {
		t.Fatalf("a λ summand must fold into Σ: %q (%v)", sigma, err)
	}

	// The word already names something in the text: no fold.
	kept, err := ChapterSpelling("∀sum:(num → num). ∀s:(num → bool). ∀f:(num → real). real_sum(s, f) = &(sum(0))", scope.Syntax, nil)
	if err != nil || !strings.Contains(kept, "real_sum(s, f)") {
		t.Fatalf("a text that spells `sum` must keep real_sum: %q (%v)", kept, err)
	}
	// An annotated head keeps its name and its annotation.
	annotated, err := ChapterSpelling("∀s:(num → bool). ∀f:(num → real). real_sum⟨A:num⟩(s, f) = &0", scope.Syntax, nil)
	if err != nil || !strings.Contains(annotated, "real_sum⟨") {
		t.Fatalf("an annotated head must not fold: %q (%v)", annotated, err)
	}
}

// A word written BARE. A nullary constant declaring a word (`π` for
// pi) is the word anywhere; a word for applied constants read as a
// value resolves where the position's type is known — an application
// argument against the head's domain — and nowhere else. The fold runs
// the other way for both, and the round-trip holds.
func TestOverload_BareWords(t *testing.T) {
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatalf("type %q: %v", text, err)
		}
		return ty
	}
	metas := map[string]core.ConstTermMeta{}
	syntax := testSyntax{}
	declare := func(name, ty, word string) {
		metas[name] = core.MakeConstMeta(core.TermName(name), typ(ty))
		if word != "" {
			syntax[name] = &ConstSyntax{Overload: &Overload{Word: word, Arity: funArity(typ(ty)), Type: typ(ty)}}
		}
	}
	declare("zz_pi", "real", "π")
	declare("zz_sin", "real → real", "sin")
	declare("zz_csin", "complex → complex", "sin")
	declare("zz_deriv", "(real → real) → real → real → bool", "")
	declare("zz_abs", "real → real", "abs")
	declare("zz_iabs", "int → int", "abs")
	declare("zz_compose", "(real → real) → (real → real) → real → real", "")
	scope := &ParseScope{
		ConstResolver:    func(name string) core.ConstTermMeta { return metas[name] },
		Syntax:           syntax,
		StrictResolution: true,
	}
	same := func(short, long string) {
		t.Helper()
		a, b := parseImplicit(t, scope, short), parseImplicit(t, scope, long)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", short, long, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	// A word's arguments are read against the constant it picked: the
	// `&` in `abs(&n)` is anchored by zz_abs's domain, as `zz_abs(&n)`
	// anchors it, and strict mode has no surviving default to refuse.
	same("∀n:num. abs(&n) = &n", "∀n:num. zz_abs(&n) = &n")
	// The nullary word, bare, in every position.
	same("∀x:real. x < π", "∀x:real. x < zz_pi")
	same("∀x:real. zz_sin(π) = x", "∀x:real. zz_sin(zz_pi) = x")
	// The applied constants' word, read as a value against the head's
	// domain: `sin` at `real → real` is zz_sin, not zz_csin.
	same("∀c:real. zz_deriv(sin, c, sin(c))", "∀c:real. zz_deriv(zz_sin, c, zz_sin(c))")
	same("∀c:real. zz_compose(sin, sin, c) = c", "∀c:real. zz_compose(zz_sin, zz_sin, c) = c")
	// Bare where no type reaches it, the word is still refused.
	if res := ParsePropTextInScope("∀c:real. sin = sin", scope); len(res.Errors) == 0 {
		t.Fatal("a bare word with no position type must be refused")
	}
	// A bare word in argument position whose type picks a constant is
	// that constant, type variables included.
	same("∀P:((real → real) → bool). P(sin)", "∀P:((real → real) → bool). P(zz_sin)")
	// A variable spelled like the word shadows it.
	same("∀π:real. π = π", "∀π:real. π = π")
	if p := parseImplicit(t, scope, "∀π:real. π = π"); strings.Contains(prop.PrintProp(p), "zz_pi") {
		t.Fatalf("a binder named π must shadow the word: %s", prop.PrintProp(p))
	}
	// The fold: the long spellings print as the words, and parse back.
	for raw, want := range map[string]string{
		"∀x:real. x < zz_pi":                      "x < π",
		"∀c:real. zz_deriv(zz_sin, c, zz_sin(c))": "zz_deriv(sin, c, sin(c))",
	} {
		out, err := ChapterSpelling(raw, scope.Syntax, nil)
		if err != nil || !strings.Contains(out, want) {
			t.Errorf("ChapterSpelling(%q) = %q (%v), want %q", raw, out, err, want)
			continue
		}
		if parseImplicit(t, scope, out).AlphaKey() != parseImplicit(t, scope, raw).AlphaKey() {
			t.Errorf("%q does not parse back to %q", out, raw)
		}
	}
	// A value in no argument position keeps its name: the parse could
	// not read it, so the fold leaves it.
	out, err := ChapterSpelling("∀f:(real → real). f = zz_sin", scope.Syntax, nil)
	if err != nil || strings.Contains(out, "= sin") {
		t.Fatalf("a bare constant outside an argument must not fold: %q (%v)", out, err)
	}
}

// A bare `&` reads as ℝ on its own, and that reading picks the
// constant where ℝ is one of the candidates. Where it fits none, each
// candidate reads the arguments against its own domains and the one
// that reads them is the constant; two reading them is a refusal.
func TestOverload_BareCoercionReadsAtTheOneCandidate(t *testing.T) {
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatalf("type %q: %v", text, err)
		}
		return ty
	}
	metas := map[string]core.ConstTermMeta{}
	syntax := testSyntax{"zz_lift": {Coercion: &Coercion{Into: typ("complex")}}}
	declare := func(name, ty, word string) {
		metas[name] = core.MakeConstMeta(core.TermName(name), typ(ty))
		if word != "" {
			syntax[name] = &ConstSyntax{Overload: &Overload{Word: word, Arity: funArity(typ(ty)), Type: typ(ty)}}
		}
	}
	declare("zz_lift", "real → complex", "")
	declare("zz_ndiv", "num → num → num", "div")
	declare("zz_idiv", "int → int → int", "div")
	declare("zz_rsgn", "real → real", "sgn")
	declare("zz_isgn", "int → int", "sgn")
	declare("zz_nmax", "num → num → num", "max")
	declare("zz_rmax", "real → real → real", "max")
	declare("zz_imax", "int → int → int", "max")
	declare("zz_itwice", "int → int", "twice")
	declare("zz_ctwice", "complex → complex", "twice")
	scope := &ParseScope{ConstResolver: func(name string) core.ConstTermMeta { return metas[name] }, Syntax: syntax}
	strict := *scope
	strict.StrictResolution = true
	for _, sc := range []*ParseScope{scope, &strict} {
		for _, c := range []struct{ short, long string }{
			// ℝ is no candidate: the integer partner's constant reads the `&`
			{"∀n:int. div(&0, n) = n", "∀n:int. zz_idiv(&0, n) = n"},
			{"∀n:int. div(n, &2) = n", "∀n:int. zz_idiv(n, &2) = n"},
			{"div(&7, &2) = &3", "zz_idiv(&7, &2) = &3"},
			{"∀m n:num. div(m, n) = m", "∀m n:num. zz_ndiv(m, n) = m"},
			// A natural argument embeds when the other one fixes int.
			{"∀m:num. ∀n:int. div(m, n) = n", "∀m:num. ∀n:int. zz_idiv(int_of_num(m), n) = n"},
			{"∀m:num. ∀n:int. div(n, m) = n", "∀m:num. ∀n:int. zz_idiv(n, int_of_num(m)) = n"},
			// The natural instance wins before any embedding is tried.
			{"∀m n:num. ∀z:int. div(m, n) = z", "∀m n:num. ∀z:int. int_of_num(zz_ndiv(m, n)) = z"},
			// ℝ is a candidate: the default is the reading
			{"sgn(&0) = &0", "zz_rsgn(&0) = &0"},
			{"∀m n:num. &max(m, n) = max(&m, &n)", "∀m n:num. &zz_nmax(m, n) = zz_rmax(&m, &n)"},
		} {
			assertSameProp(t, sc, c.short, c.long)
		}
	}
	// Two candidates off the real line both read the `&`: refused, naming them.
	res := ParsePropTextInScope("twice(&1) = twice(&1)", scope)
	if len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "alike") ||
		!strings.Contains(res.Errors[0].Message, "zz_itwice") || !strings.Contains(res.Errors[0].Message, "zz_ctwice") {
		t.Fatalf("a bare & two candidates anchor must be refused naming both, got %v", res.Errors)
	}
	// Nothing reads them either way: the refusal names every candidate.
	res = ParsePropTextInScope("∀P:(real → bool). div(P, P) = P", scope)
	if len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "none of") {
		t.Fatalf("arguments no candidate takes must be refused, got %v", res.Errors)
	}
}
