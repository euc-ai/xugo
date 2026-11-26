package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Outfix notation (outfix.go), pinned on a toy norm: `‖u‖_n` is
// `norm(n, u)`, and a dimension-free `⟪u, v⟫` is `pair2(u, v)`.

func notationTestScope(t *testing.T) *ParseScope {
	t.Helper()
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatalf("type %q: %v", text, err)
		}
		return ty
	}
	metas := map[string]core.ConstTermMeta{
		"norm":     core.MakeConstMeta("norm", typ("num → (num → real) → real")),
		"pair2":    core.MakeConstMeta("pair2", typ("(num → real) → (num → real) → real")),
		"vec_add":  core.MakeConstMeta("vec_add", typ("(A → A → A) → (num → A) → (num → A) → num → A")),
		"real_add": core.MakeConstMeta("real_add", typ("real → real → real")),
	}
	realVec, _ := ParseTypeText("num → real")
	return &ParseScope{
		ConstMetas: metas,
		Vars:       map[string]core.HolType{"u": realVec, "v": realVec, "n": NumType, "m": NumType},
		Syntax: testSyntax{
			"norm":    {Outfix: &Outfix{Open: "‖", Close: "‖", Body: []int{1}, Sub: 0}},
			"pair2":   {Outfix: &Outfix{Open: "⟪", Close: "⟫", Body: []int{0, 1}, Sub: -1}},
			"vec_add": {Implicit: []string{"add"}},
		},
		StrictResolution: true,
		CoerceDomain:     RealType,
	}
}

func TestNotation_Parse(t *testing.T) {
	scope := notationTestScope(t)
	same := func(sugar, plain string) {
		t.Helper()
		a, b := parseImplicit(t, scope, sugar), parseImplicit(t, scope, plain)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", sugar, plain, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	same("‖u‖_n = ‖v‖_n", "norm(n, u) = norm(n, v)")
	same("‖u‖_(m + 1) = ‖u‖_2", "norm(m + 1, u) = norm(2, u)")
	same("‖u‖_n ≤ ‖u‖_n + ‖v‖_m", "norm(n, u) ≤ norm(n, u) + norm(m, v)")
	// A notation composes with the implicit prefix inside it, and with
	// another notation around it.
	scope.ImplicitBindings = map[string]core.Term{"add": ParseTermTextInScope("real_add", nil, scope, nil).Term}
	same("‖vec_add(u, v)‖_n = ‖vec_add(u, v)‖_n", "norm(n, vec_add(real_add, u, v)) = norm(n, vec_add(real_add, u, v))")
	same("⟪u, v⟫ = ⟪v, u⟫", "pair2(u, v) = pair2(v, u)")
	// The term path.
	res := ParseTermTextInScope("‖u‖_n", nil, scope, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("term: %s", res.Errors[0].Message)
	}
	plain := ParseTermTextInScope("norm(n, u)", nil, scope, nil)
	if !res.Term.Equals(plain.Term) {
		t.Fatalf("term notation differs")
	}
}

func TestNotation_Refusals(t *testing.T) {
	scope := notationTestScope(t)
	expectErr := func(text, want string) {
		t.Helper()
		res := ParsePropTextInScope(text, scope)
		if len(res.Errors) == 0 {
			t.Fatalf("%q: expected a refusal, parsed %s", text, prop.PrintProp(res.Prop))
		}
		if !strings.Contains(res.Errors[0].Message, want) {
			t.Fatalf("%q: error %q does not mention %q", text, res.Errors[0].Message, want)
		}
	}
	expectErr("‖u‖ = ‖v‖", "takes 1 body argument(s) and a subscript")
	expectErr("‖u, v‖_n = ‖u‖_n", "takes 1 body argument(s)")
	expectErr("‖u‖_ = ‖u‖_n", "subscript")
	// No table: the notation names nothing.
	bare := *scope
	bare.Syntax = nil
	res := ParsePropTextInScope("‖u‖_n = ‖u‖_n", &bare)
	if len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "no constant in scope declares this notation") {
		t.Fatalf("expected the no-scope refusal, got %v", res.Errors)
	}
}

func TestNotation_ChapterSpelling(t *testing.T) {
	scope := notationTestScope(t)
	scope.ImplicitBindings = map[string]core.Term{"add": ParseTermTextInScope("real_add", nil, scope, nil).Term}
	out, err := ChapterSpelling(
		"u:(num → real), v:(num → real), n:num, m:num ⊢ norm(n, vec_add(real_add, u, v)) ≤ norm(m + 1, u) + norm(2, v) ∧ pair2(u, v) = pair2(v, u)",
		scope.Syntax, scope.ImplicitBindings)
	if err != nil {
		t.Fatal(err)
	}
	for _, frag := range []string{"‖vec_add(u, v)‖_n", "‖u‖_(m + 1)", "‖v‖_2", "⟪u, v⟫ = ⟪v, u⟫"} {
		if !strings.Contains(out, frag) {
			t.Errorf("chapter spelling lacks %q: %s", frag, out)
		}
	}
	// It parses back to the statement it came from.
	a := parseImplicit(t, scope, out)
	b := parseImplicit(t, scope, "u:(num → real), v:(num → real), n:num, m:num ⊢ norm(n, vec_add(real_add, u, v)) ≤ norm(m + 1, u) + norm(2, v) ∧ pair2(u, v) = pair2(v, u)")
	if a.AlphaKey() != b.AlphaKey() {
		t.Fatalf("chapter spelling parses to a different statement: %s", out)
	}
	// A partial application keeps the call form.
	kept, err := ChapterSpelling("n:num ⊢ norm(n) = norm(n)", scope.Syntax, nil)
	if err != nil || strings.Contains(kept, "‖") {
		t.Fatalf("a partial application must keep the call form: %q (%v)", kept, err)
	}
	// The scope-free formatter round-trips a notation as an AST.
	formatted, err := FormatStmtText("∀u:(num → real). ‖u‖_(m+1) = ‖u‖_(m+1)")
	if err != nil || !strings.Contains(formatted, "‖u‖_(m + 1)") {
		t.Fatalf("FormatStmtText: %q (%v)", formatted, err)
	}
}

// Operator and big-operator notation (operator.go, bigop.go), pinned on
// the toy scope: `+ - •` and the prefix `-` at vectors are the chapter's
// constants at the components the scope binds, and `Σ` is the corpus's
// sum at the body's type — `real_sum` at real, `nat_sum` at num, the fold at
// `vec_add` at vectors.
func operatorTestScope(t *testing.T) *ParseScope {
	t.Helper()
	scope := notationTestScope(t)
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatalf("type %q: %v", text, err)
		}
		return ty
	}
	for name, ty := range map[string]string{
		"vec_sub":           "(A → A → A) → (A → A) → (num → A) → (num → A) → num → A",
		"vec_scalar_mul":    "(A → A → A) → A → (num → A) → num → A",
		"vec_neg":           "(A → A) → (num → A) → num → A",
		"real_sum":          "(A → bool) → (A → real) → real",
		"nat_sum":           "(A → bool) → (A → num) → num",
		"real_product":      "(A → bool) → (A → real) → real",
		"iterated_op":       "(B → B → B) → (A → bool) → (A → B) → B",
		"real_mul":          "real → real → real",
		"real_neg":          "real → real",
		"real_converges_to": "(num → real) → real → bool",
		"real_limit_at":     "(real → real) → real → real → bool",
	} {
		scope.ConstMetas[name] = core.MakeConstMeta(name, typ(ty))
	}
	syntax := scope.Syntax.(testSyntax)
	syntax["vec_add"] = &ConstSyntax{Implicit: []string{"add"}, Operator: &Operator{Symbol: "+", Args: []int{0, 1}}}
	syntax["vec_sub"] = &ConstSyntax{Implicit: []string{"add", "neg"}, Operator: &Operator{Symbol: "-", Args: []int{0, 1}}}
	syntax["vec_scalar_mul"] = &ConstSyntax{Implicit: []string{"mul"}, Operator: &Operator{Symbol: "•", Args: []int{0, 1}}}
	syntax["vec_neg"] = &ConstSyntax{Implicit: []string{"neg"}, Operator: &Operator{Symbol: "-", Args: []int{0}}}
	syntax["real_converges_to"] = &ConstSyntax{Operator: &Operator{Symbol: "⟶", Args: []int{0, 1}}}
	// The clause form at arity 3, its holes read in the notation's order
	// (function, limit, point) against a constant whose arguments go
	// (function, point, limit).
	syntax["real_limit_at"] = &ConstSyntax{Operator: &Operator{Symbol: "⟶", Args: []int{0, 2, 1}}}
	syntax["real_sum"] = &ConstSyntax{BigOp: &BigOp{Symbol: "Σ", Carrier: RealType}}
	syntax["nat_sum"] = &ConstSyntax{BigOp: &BigOp{Symbol: "Σ", Carrier: NumType}}
	syntax["real_product"] = &ConstSyntax{BigOp: &BigOp{Symbol: "Π", Carrier: RealType}}
	scope.Vars["c"] = RealType
	scope.Vars["s"] = typ("num → bool")
	scope.Vars["F"] = typ("num → (num → real)")
	scope.Vars["g"] = typ("real → real")
	scope.ImplicitBindings = map[string]core.Term{}
	for _, comp := range []struct{ name, term string }{{"add", "real_add"}, {"mul", "real_mul"}, {"neg", "real_neg"}} {
		res := ParseTermTextInScope(comp.term, nil, scope, nil)
		if len(res.Errors) > 0 {
			t.Fatalf("%s: %s", comp.term, res.Errors[0].Message)
		}
		scope.ImplicitBindings[comp.name] = res.Term
	}
	return scope
}

func TestOperators_Parse(t *testing.T) {
	scope := operatorTestScope(t)
	same := func(sugar, plain string) {
		t.Helper()
		a, b := parseImplicit(t, scope, sugar), parseImplicit(t, scope, plain)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", sugar, plain, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	// Each symbol at a vector type is the chapter's constant at the
	// bound components.
	same("u + v = v + u", "vec_add(real_add, u, v) = vec_add(real_add, v, u)")
	same("c • u = vec_scalar_mul(c, u)", "vec_scalar_mul(real_mul, c, u) = vec_scalar_mul(real_mul, c, u)")
	same("‖u - v‖_n = ‖vec_sub(u, v)‖_n", "norm(n, vec_sub(real_add, real_neg, u, v)) = norm(n, vec_sub(real_add, real_neg, u, v))")
	same("-u = vec_neg(u)", "vec_neg(real_neg, u) = vec_neg(real_neg, u)")
	same("u − v = vec_sub(u, v)", "vec_sub(real_add, real_neg, u, v) = vec_sub(real_add, real_neg, u, v)")
	// A vector `+` beside a real `*` and `≤` in one statement: each
	// operator on its own operands.
	same("c * c ≤ ‖c • u + v‖_n", "real_mul(c, c) ≤ norm(n, vec_add(real_add, vec_scalar_mul(real_mul, c, u), v))")
	// Precedence: `•` between `+ -` and `* /`, right-associative.
	same("‖v‖_n • u - ‖u‖_n • v = u", "vec_sub(real_add, real_neg, vec_scalar_mul(real_mul, norm(n, v), u), vec_scalar_mul(real_mul, norm(n, u), v)) = u")
	same("c * c • u = (c * c) • u", "vec_scalar_mul(real_mul, real_mul(c, c), u) = vec_scalar_mul(real_mul, real_mul(c, c), u)")
	same("c • c • u = c • (c • u)", "vec_scalar_mul(real_mul, c, vec_scalar_mul(real_mul, c, u)) = vec_scalar_mul(real_mul, c, vec_scalar_mul(real_mul, c, u))")
	same("-u + v = vec_add(vec_neg(u), v)", "vec_add(real_add, vec_neg(real_neg, u), v) = vec_add(real_add, vec_neg(real_neg, u), v)")
	// The operation applied to a point.
	same("(u + v)(n) = u(n) + v(n)", "vec_add(real_add, u, v, n) = real_add(u(n), v(n))")
	// A declared RELATION: `⟶` at the comparison level, its operands of
	// two types, no implicit prefix, and it binds looser than `+`.
	same("u ⟶ c ∧ u ⟶ c + c ⇒ c = c + c", "real_converges_to(u, c) ∧ real_converges_to(u, real_add(c, c)) ⇒ c = real_add(c, c)")
	same("u + v ⟶ c", "real_converges_to(vec_add(real_add, u, v), c)")
	// The clause form: `f ⟶ l (at c)` is the constant declaring `⟶` at
	// arity THREE, its holes mapped to the constant's argument order,
	// the point clause self-delimiting, and a `+` on either side of
	// `⟶` or inside the clause binds tighter.
	same("g ⟶ c (at c + c)", "real_limit_at(g, real_add(c, c), c)")
	same("g ⟶ c + c (at c) ∧ g ⟶ c (at c) ⇒ c = c + c", "real_limit_at(g, c, real_add(c, c)) ∧ real_limit_at(g, c, c) ⇒ c = real_add(c, c)")
	// An application in the limit slot does not swallow the clause.
	same("g ⟶ g(c) (at c)", "real_limit_at(g, c, g(c))")
	// The term path.
	res := ParseTermTextInScope("c • u + v", nil, scope, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("term: %s", res.Errors[0].Message)
	}
	plain := ParseTermTextInScope("vec_add(real_add, vec_scalar_mul(real_mul, c, u), v)", nil, scope, nil)
	if !res.Term.Equals(plain.Term) {
		t.Fatalf("term operator differs")
	}
}

func TestBigOp_Parse(t *testing.T) {
	scope := operatorTestScope(t)
	same := func(sugar, plain string) {
		t.Helper()
		a, b := parseImplicit(t, scope, sugar), parseImplicit(t, scope, plain)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", sugar, plain, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	// The head follows the body's type: the declared sum at real and
	// num, the fold at `vec_add` at vectors; the range is the half-open
	// range or the set.
	same("Σ_{i<n} u(i) * v(i) = &0", "real_sum({i:num | i < n}, λi:num. u(i) * v(i)) = &0")
	same("Σ_{i∈s} u(i) = &0", "real_sum(s, λi:num. u(i)) = &0")
	same("Σ_{i<n} i = 0", "nat_sum({i:num | i < n}, λi:num. i) = 0")
	same("Π_{i<n} u(i) = &0", "real_product({i:num | i < n}, λi:num. u(i)) = &0")
	same("‖Σ_{i∈s} F(i)‖_n = &0", "norm(n, iterated_op(vec_add, s, λi:num. F(i))) = &0")
	same("‖Σ_{i<n} u(i) • F(i)‖_m = &0", "norm(m, iterated_op(vec_add, {i:num | i < n}, λi:num. vec_scalar_mul(real_mul, u(i), F(i)))) = &0")
	// The body is read at the scalar action's level: a product is in,
	// a sum is out unless parenthesized, and a sum of sums nests.
	same("Σ_{i<n} u(i) + c = &0", "real_sum({i:num | i < n}, λi:num. u(i)) + c = &0")
	same("Σ_{i<n} (u(i) + c) = &0", "real_sum({i:num | i < n}, λi:num. u(i) + c) = &0")
	same("Σ_{i<n} Σ_{j<m} u(i) * v(j) = &0", "real_sum({i:num | i < n}, λi:num. real_sum({j:num | j < m}, λj:num. u(i) * v(j))) = &0")
	same("∑_{i<n} u(i) = Σ_{i<n} u(i)", "real_sum({i:num | i < n}, λi:num. u(i)) = real_sum({i:num | i < n}, λi:num. u(i))")
	// A bound naming the index is the outer variable of that name.
	same("∀i:num. Σ_{i<i} u(i) = &0", "∀i:num. real_sum({k:num | k < i}, λi:num. u(i)) = &0")
	// The term path.
	res := ParseTermTextInScope("Σ_{i<n} ‖F(i)‖_m", nil, scope, nil)
	if len(res.Errors) > 0 {
		t.Fatalf("term: %s", res.Errors[0].Message)
	}
	// Up to α: the range's synthesized binder is position-named, as the
	// parser's own set-builder binder is.
	plain := ParseTermTextInScope("real_sum({i:num | i < n}, λi:num. norm(m, F(i)))", nil, scope, nil)
	if !res.Term.AlphaEquals(plain.Term) {
		t.Fatalf("term big operator differs")
	}
}

func TestOperators_Refusals(t *testing.T) {
	scope := operatorTestScope(t)
	expectErr := func(sc *ParseScope, text, want string) {
		t.Helper()
		res := ParsePropTextInScope(text, sc)
		if len(res.Errors) == 0 {
			t.Fatalf("%q: expected a refusal, parsed %s", text, prop.PrintProp(res.Prop))
		}
		if !strings.Contains(res.Errors[0].Message, want) {
			t.Fatalf("%q: error %q does not mention %q", text, res.Errors[0].Message, want)
		}
	}
	// Operands of two domains, and a type no operator serves.
	expectErr(scope, "c + u = u", "same arithmetic domain")
	expectErr(scope, "c • c = c", "no instance for operand types real and real")
	expectErr(scope, "c ⟶ c", "operator ⟶ has no instance for operand types real and real")
	expectErr(scope, "u ⟶ c ⟶ c", "")
	// The clause form declines what its declaring constant does not
	// serve, and is refused outright where no constant declares arity 3.
	expectErr(scope, "u ⟶ c (at c)", "operator ⟶ (at) has no instance for operand types (num → real), real and real")
	expectErr(scope, "g ⟶ c (at c) ⟶ c", "")
	noClause := *scope
	noClause.Syntax = testSyntax{"real_converges_to": scope.Syntax.ConstSyntax("real_converges_to")}
	expectErr(&noClause, "g ⟶ c (at c)", "no constant in scope declares it")
	expectErr(scope, "s + s = s", "no instance for operand type (num → bool)")
	// Where nothing binds the component, the operator is the short
	// spelling it stands for, and is refused as that is.
	unbound := *scope
	unbound.ImplicitBindings = nil
	expectErr(&unbound, "u + v = u", "implicit argument add is not in scope")
	expectErr(&unbound, "Σ_{i∈s} F(i) = F(0)", "implicit argument add is not in scope")
	// A big operator at a type variable: no sum, no `+`.
	expectErr(scope, "∀g:(num → A). Σ_{i<n} g(i) = g(0)", "no instance at var:A")
	// The binder form.
	expectErr(scope, "Σ i<n. u(i) = &0", "binds its index")
	expectErr(scope, "Σ_{i≤n} u(i) = &0", "runs below a bound")
	expectErr(scope, "Σ_{i∈c} u(i) = &0", "not a set")
}

func TestOperators_ChapterSpelling(t *testing.T) {
	scope := operatorTestScope(t)
	decls := "u:(num → real), v:(num → real), n:num, m:num, c:real, s:(num → bool), F:(num → (num → real)), g:(real → real) ⊢ "
	raw := decls + "norm(n, vec_sub(real_add, real_neg, vec_scalar_mul(real_mul, c, u), v)) ≤ real_sum(s, λi:num. norm(n, F(i))) ∧ " +
		"norm(n, iterated_op(vec_add(real_add), {i:num | i < n}, λi:num. vec_scalar_mul(real_mul, u(i), F(i)))) = &0 ∧ " +
		"vec_neg(real_neg, u) = u ∧ real_sum(s, λi:num. u(i)) ≤ c ∧ real_sum(s, λi:num. u(i)) * c = &0 ∧ " +
		"nat_sum({i:num | i < n}, λi:num. i) = 0 ∧ vec_add(real_add, u, v, n) = u(n) + v(n) ∧ " +
		"real_converges_to(vec_add(real_add, u, v), c + c) ∧ real_limit_at(g, c + c, g(c))"
	out, err := ChapterSpelling(raw, scope.Syntax, scope.ImplicitBindings)
	if err != nil {
		t.Fatal(err)
	}
	for _, frag := range []string{
		"‖c • u - v‖_n ≤ Σ_{i∈s} ‖F(i)‖_n",
		"‖Σ_{i<n} u(i) • F(i)‖_n = &0",
		"-u = u",
		"Σ_{i∈s} u(i) ≤ c",
		"(Σ_{i∈s} u(i)) * c = &0",
		"u + v ⟶ c + c",
		"g ⟶ g(c) (at c + c)",
		"Σ_{i<n} i = 0",
		"(u + v)(n) = u(n) + v(n)",
	} {
		if !strings.Contains(out, frag) {
			t.Errorf("chapter spelling lacks %q: %s", frag, out)
		}
	}
	// It parses back to the statement it came from.
	a := parseImplicit(t, scope, out)
	b := parseImplicit(t, scope, raw)
	if a.AlphaKey() != b.AlphaKey() {
		t.Fatalf("chapter spelling parses to a different statement: %s", out)
	}
	// A fold over a bare function has no binder to fold into: it keeps
	// the application, the term the statement was made at.
	kept, err := ChapterSpelling(decls+"iterated_op(vec_add(real_add), s, F) = iterated_op(vec_add(real_add), s, F)", scope.Syntax, scope.ImplicitBindings)
	if err != nil || strings.Contains(kept, "Σ") || !strings.Contains(kept, "iterated_op(vec_add, s, F)") {
		t.Fatalf("a fold over a bare function must keep the application: %q (%v)", kept, err)
	}
	// The scope-free formatter round-trips the forms as ASTs.
	formatted, err := FormatStmtText("∀u:(num → real). ‖Σ_{i<n} c • u‖_n = &0 ∧ (Σ_{i<n} c) • u = -u")
	if err != nil || !strings.Contains(formatted, "‖Σ_{i<n} c • u‖_n") || !strings.Contains(formatted, "(Σ_{i<n} c) • u = -u") {
		t.Fatalf("FormatStmtText: %q (%v)", formatted, err)
	}
	formatted, err = FormatStmtText("∀g:(real → real). g ⟶ g(c)+c (at c+c) ∧ u ⟶ c")
	if err != nil || !strings.Contains(formatted, "g ⟶ g(c) + c (at c + c) ∧ u ⟶ c") {
		t.Fatalf("FormatStmtText: %q (%v)", formatted, err)
	}
}

// Structure components carrying symbols (structure.go), pinned on a toy
// ring: under a law's antecedent, or a goal's resident fact, `x + y` at
// the carrier is the bound component `add(x, y)`.
func structureTestScope(t *testing.T) *ParseScope {
	t.Helper()
	scope := operatorTestScope(t)
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatalf("type %q: %v", text, err)
		}
		return ty
	}
	scope.ConstMetas["zz_ring"] = core.MakeConstMeta("zz_ring", typ("(A → A → A) → A → (A → A) → (A → A → A) → A → (A → A → A) → bool"))
	scope.Syntax.(testSyntax)["zz_ring"] = &ConstSyntax{Structure: &StructureSyntax{Components: []StructureComponent{
		{Symbol: "+", Arity: 2}, {}, {Symbol: "-", Arity: 1}, {Symbol: "*", Arity: 2}, {}, {Symbol: "-", Arity: 2},
	}}}
	// A toy module: the scalars' `+` and `*`, the vectors' `+`, and the
	// scalar action `•`, a component whose two operands differ in type.
	scope.ConstMetas["zz_module"] = core.MakeConstMeta("zz_module", typ("(A → A → A) → (A → A → A) → (B → B → B) → (A → B → B) → (B → bool) → bool"))
	scope.Syntax.(testSyntax)["zz_module"] = &ConstSyntax{Structure: &StructureSyntax{Components: []StructureComponent{
		{Symbol: "+", Arity: 2}, {Symbol: "*", Arity: 2}, {Symbol: "+", Arity: 2}, {Symbol: "•", Arity: 2}, {},
	}}}
	// The table serves the scope's constant metadata, as the registry's
	// does: the chapter spelling resolves a constant declaring an
	// operator to the meta the parse builds with.
	scope.Syntax = structFieldsSyntax{SyntaxTable: scope.Syntax, metas: scope.ConstMetas}
	return scope
}

// testTable is the scope's test table, under whatever metadata wrapper
// a scope builder put around it: where a test declares a further
// constant's syntax.
func testTable(scope *ParseScope) testSyntax {
	table := scope.Syntax
	for {
		wrapper, wrapped := table.(structFieldsSyntax)
		if !wrapped {
			return table.(testSyntax)
		}
		table = wrapper.SyntaxTable
	}
}

// declareStructure adds a structure predicate to a structureTestScope:
// its meta to the scope and its component symbols to the test table.
func declareStructure(t *testing.T, scope *ParseScope, name, typeText string, components []StructureComponent) {
	t.Helper()
	ty, err := ParseTypeText(typeText)
	if err != nil {
		t.Fatalf("type %q: %v", typeText, err)
	}
	scope.ConstMetas[name] = core.MakeConstMeta(core.TermName(name), ty)
	testTable(scope)[name] = &ConstSyntax{Structure: &StructureSyntax{Components: components}}
}

const zzModulePrefix = "∀add:(A → A → A). ∀mul:(A → A → A). ∀add':(B → B → B). ∀smul:(A → B → B). ∀M:(B → bool). zz_module(add, mul, add', smul, M) ⇒ "

// A component whose operands differ in type — the module's scalar
// action `smul : A → B → B` — carries its symbol like any other: `c • u`
// at a scalar and a vector is `smul(c, u)`, read at the operands'
// types, beside the two additions each at its own carrier; the printer
// folds it back; the symbol at operands no component takes declines.
func TestStructureSymbols_HeterogeneousOperands(t *testing.T) {
	scope := structureTestScope(t)
	sugar := zzModulePrefix + "∀c d:A. ∀u v:B. (c + d) • u = c • u + d • u ∧ c • (u + v) = c • u + c • v ∧ (c * d) • u = c • (d • u)"
	plain := zzModulePrefix + "∀c d:A. ∀u v:B. smul(add(c, d), u) = add'(smul(c, u), smul(d, u)) ∧ smul(c, add'(u, v)) = add'(smul(c, u), smul(c, v)) ∧ smul(mul(c, d), u) = smul(c, smul(d, u))"
	a, b := parseImplicit(t, scope, sugar), parseImplicit(t, scope, plain)
	if a.AlphaKey() != b.AlphaKey() {
		t.Fatalf("%q ≠ %q:\n  %s\n  %s", sugar, plain, prop.PrintProp(a), prop.PrintProp(b))
	}
	out, err := ChapterSpelling(plain, scope.Syntax, scope.ImplicitBindings)
	if err != nil {
		t.Fatal(err)
	}
	// `*` binds tighter than `•`, and `•` associates to the right, so the
	// third law prints without parentheses.
	for _, frag := range []string{"(c + d) • u = c • u + d • u", "c • (u + v) = c • u + c • v", "c * d • u = c • d • u"} {
		if !strings.Contains(out, frag) {
			t.Errorf("chapter spelling lacks %q: %s", frag, out)
		}
	}
	if parseImplicit(t, scope, out).AlphaKey() != b.AlphaKey() {
		t.Fatalf("chapter spelling parses to a different statement: %s", out)
	}
	// The action takes a scalar then a vector: a vector then a scalar is
	// no instance of it.
	res := ParsePropTextInScope(zzModulePrefix+"∀c:A. ∀u:B. u • c = smul(c, u)", scope)
	if len(res.Errors) == 0 {
		t.Fatalf("expected a refusal of • at (B, A), got none")
	}
}

const zzRingPrefix = "∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). zz_ring(add, zero, neg, mul, one, sub) ⇒ "

func TestStructureSymbols_Parse(t *testing.T) {
	scope := structureTestScope(t)
	same := func(sugar, plain string) {
		t.Helper()
		a, b := parseImplicit(t, scope, sugar), parseImplicit(t, scope, plain)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", sugar, plain, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	same(zzRingPrefix+"∀x y z:A. x * (y + z) = x * y + x * z ∧ x - y = x + -y ∧ -(-x) = x",
		zzRingPrefix+"∀x y z:A. mul(x, add(y, z)) = add(mul(x, y), mul(x, z)) ∧ sub(x, y) = add(x, neg(y)) ∧ neg(neg(x)) = x")
	// The ring's `+` beside the module's `+` at vectors over it: two
	// operators, each on its own operands.
	same(zzRingPrefix+"∀c d:A. ∀u:(num → A). vec_add(add, vec_scalar_mul(mul, c, u), vec_scalar_mul(mul, d, u)) = vec_scalar_mul(mul, add(c, d), u)",
		zzRingPrefix+"∀c d:A. ∀u:(num → A). c • u + d • u = (c + d) • u")
	// The big operator folds at the bound component.
	same(zzRingPrefix+"∀s:(num → bool). ∀f:(num → A). Σ_{i∈s} f(i) = iterated_op(add, s, λi:num. f(i))",
		zzRingPrefix+"∀s:(num → bool). ∀f:(num → A). iterated_op(add, s, λi:num. f(i)) = iterated_op(add, s, λi:num. f(i))")
	// A goal's resident fact binds the same way for a claim text.
	fact := parseImplicit(t, scope, "∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). zz_ring(add, zero, neg, mul, one, sub)")
	claimScope := *scope
	claimScope.Vars = map[string]core.HolType{}
	for k, v := range scope.Vars {
		claimScope.Vars[k] = v
	}
	body := fact.Conclusion()
	for abs := ext.MatchesFORALL(body); !abs.IsZero(); abs = ext.MatchesFORALL(body) {
		claimScope.Vars[string(abs.Var().Name())] = abs.Var().Type()
		body = abs.Body()
	}
	claimScope.ResidentFacts = []core.Term{body}
	a := parseImplicit(t, &claimScope, "∀x y:A. x * y - y * x = zero")
	b := parseImplicit(t, &claimScope, "∀x y:A. sub(mul(x, y), mul(y, x)) = zero")
	if a.AlphaKey() != b.AlphaKey() {
		t.Fatalf("resident fact: short ≠ explicit\n  %s\n  %s", prop.PrintProp(a), prop.PrintProp(b))
	}
	// Without the fact nothing binds: `+` at a type variable has no instance.
	res := ParsePropTextInScope("∀add:(A → A → A). ∀x y:A. x + y = add(x, y)", scope)
	if len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "no instance for operand type") {
		t.Fatalf("expected a refusal at the unbound carrier, got %v", res.Errors)
	}
	// Two structures on one carrier: the component must be spelled.
	two := ParsePropTextInScope(zzRingPrefix+"∀add2:(A → A → A). ∀neg2:(A → A). ∀sub2:(A → A → A). zz_ring(add2, zero, neg2, mul, one, sub2) ⇒ ∀x y:A. x + y = add(x, y)", scope)
	if len(two.Errors) == 0 || !strings.Contains(two.Errors[0].Message, "two structures") {
		t.Fatalf("expected the two-structures refusal, got %v", two.Errors)
	}
}

func TestStructureSymbols_ChapterSpelling(t *testing.T) {
	scope := structureTestScope(t)
	raw := zzRingPrefix + "∀x y z:A. mul(x, add(y, z)) = add(mul(x, y), mul(x, z)) ∧ sub(x, y) = add(x, neg(y)) ∧ " +
		"(∀s:(num → bool). ∀f:(num → A). iterated_op(add, s, λi:num. f(i)) = iterated_op(add, s, λi:num. f(i)))"
	out, err := ChapterSpelling(raw, scope.Syntax, scope.ImplicitBindings)
	if err != nil {
		t.Fatal(err)
	}
	for _, frag := range []string{"x * (y + z) = x * y + x * z", "x - y = x + -y", "Σ_{i∈s} f(i) = Σ_{i∈s} f(i)"} {
		if !strings.Contains(out, frag) {
			t.Errorf("chapter spelling lacks %q: %s", frag, out)
		}
	}
	if !strings.Contains(out, "zz_ring(add, zero, neg, mul, one, sub)") {
		t.Errorf("the antecedent must keep its applied spelling: %s", out)
	}
	if parseImplicit(t, scope, out).AlphaKey() != parseImplicit(t, scope, raw).AlphaKey() {
		t.Fatalf("chapter spelling parses to a different statement: %s", out)
	}
	// The definitional layer, with no structure fact in the text, is
	// left as written.
	kept, err := ChapterSpelling("∀add:(A → A → A). ∀x y:A. add(x, y) = add(y, x)", scope.Syntax, nil)
	if err != nil || strings.Contains(kept, "+") {
		t.Fatalf("no structure fact, no fold: %q (%v)", kept, err)
	}
}

// A component two structure facts spell differently — `add` is
// zz_abelian's `+` and zz_group's `*` in one definition — folds into the
// symbol of the fact that comes FIRST in the text, on every run: a
// choice falling out of a map walk would flip the corpus index's page
// for abelian_group between `x + y` and `x * y` from one generation to
// the next.
func TestStructureSymbols_ChapterSpellingFirstFactWins(t *testing.T) {
	scope := structureTestScope(t)
	for name, mul := range map[string]string{"zz_abelian": "+", "zz_group": "*"} {
		declareStructure(t, scope, name, "(A → A → A) → A → (A → A) → bool", []StructureComponent{
			{Symbol: mul, Arity: 2}, {}, {Symbol: "-", Arity: 1},
		})
	}
	raw := "∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). zz_abelian(add, zero, neg) ⇔ zz_group(add, zero, neg) ∧ (∀x y:A. add(x, y) = add(y, x))"
	for i := 0; i < 32; i++ {
		out, err := ChapterSpelling(raw, scope.Syntax, scope.ImplicitBindings)
		if err != nil {
			t.Fatal(err)
		}
		if !strings.Contains(out, "x + y = y + x") {
			t.Fatalf("run %d: the first fact binds add to +, the fold chose otherwise: %s", i, out)
		}
	}
}

// A symbol two structure facts bind on two components is printed for
// neither where the parser would refuse it back: zz_group's `*` on add
// beside zz_ring's `*` on mul, both at the carrier A, is "bound by two
// structures" at (A, A), so add prints under the `+` it alone holds and
// mul by its name. At two carriers the parser tells the components
// apart by type, and each keeps the symbol. Every spelling parses back
// to the statement it came from.
func TestStructureSymbols_ChapterSpellingSymbolHeldByTwoComponents(t *testing.T) {
	scope := structureTestScope(t)
	declareStructure(t, scope, "zz_group", "(A → A → A) → A → (A → A) → bool", []StructureComponent{
		{Symbol: "*", Arity: 2}, {}, {Symbol: "-", Arity: 1},
	})
	spell := func(raw string) string {
		t.Helper()
		out, err := ChapterSpelling(raw, scope.Syntax, scope.ImplicitBindings)
		if err != nil {
			t.Fatal(err)
		}
		if parseImplicit(t, scope, out).AlphaKey() != parseImplicit(t, scope, raw).AlphaKey() {
			t.Fatalf("chapter spelling parses to a different statement: %s", out)
		}
		return out
	}
	// One carrier: the group fact comes first and would give add the
	// `*` that the ring gives mul.
	one := spell("∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). " +
		"zz_group(add, zero, neg) ∧ zz_ring(add, zero, neg, mul, one, sub) ⇒ ∀x y:A. add(x, y) = add(y, x) ∧ mul(x, y) = mul(y, x)")
	for _, frag := range []string{"x + y = y + x", "mul(x, y) = mul(y, x)"} {
		if !strings.Contains(one, frag) {
			t.Errorf("one carrier: lacks %q: %s", frag, one)
		}
	}
	if strings.Contains(one, "*") {
		t.Errorf("one carrier: a symbol two components hold is printed for neither: %s", one)
	}
	// Two carriers: `*` at (A, A) reads as mul and at (B, B) as add'.
	two := spell("∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). ∀add':(B → B → B). ∀zero':B. ∀neg':(B → B). " +
		"zz_group(add', zero', neg') ∧ zz_ring(add, zero, neg, mul, one, sub) ⇒ ∀x y:A. ∀u v:B. mul(x, y) = mul(y, x) ∧ add'(u, v) = add'(v, u)")
	for _, frag := range []string{"x * y = y * x", "u * v = v * u"} {
		if !strings.Contains(two, frag) {
			t.Errorf("two carriers: lacks %q: %s", frag, two)
		}
	}
}

// A display's facts type nothing — Skolems carry no declaration and
// its binders no annotation — so there a symbol folds only for the one
// component it is bound on at that arity, whatever the types turn out
// to be: add₀ keeps its `+`, and mul₀ and add'₀, which share `*`, print
// by name.
func TestDisplaySpelling_SymbolHeldByTwoComponents(t *testing.T) {
	scope := structureTestScope(t)
	declareStructure(t, scope, "zz_group", "(A → A → A) → A → (A → A) → bool", []StructureComponent{
		{Symbol: "*", Arity: 2}, {}, {Symbol: "-", Arity: 1},
	})
	in := "zz_group(add'_0, zero'_0, neg'_0),\n\tzz_ring(add_0, zero_0, neg_0, mul_0, one_0, sub_0)\n\t⊢ ∀x.∀y.∀u.∀v.(((add_0(x, y) = add_0(y, x)) ∧ (mul_0(x, y) = mul_0(y, x))) ∧ (add'_0(u, v) = add'_0(v, u)))"
	want := "zz_group(add'₀, zero'₀, neg'₀), zz_ring(add₀, zero₀, neg₀, mul₀, one₀, sub₀) ⊢ ∀x y u v. x + y = y + x ∧ mul₀(x, y) = mul₀(y, x) ∧ add'₀(u, v) = add'₀(v, u)"
	if got := DisplaySpelling(in, scope.Syntax, scope.ImplicitBindings); got != want {
		t.Errorf("DisplaySpelling:\n  got  %q\n  want %q", got, want)
	}
}

// An application whose implicit prefix the scope would not put back —
// under no bindings the components stay spelled — keeps the call form:
// its leading arguments are components, not an operator's holes or a
// sum's set, and `vec_add(real_add, u, v)` is not `(real_add + u)(v)`.
// A notation with no implicit prefix folds under the same scope.
func TestOperators_ChapterSpellingKeepsSpelledPrefix(t *testing.T) {
	scope := operatorTestScope(t)
	decls := "u:(num → real), v:(num → real), n:num, i:num, s:(num → bool) ⊢ "
	raw := decls + "vec_add(real_add, u, v, i) = u(i) ∧ vec_neg(real_neg, u) = u ∧ norm(n, vec_add(real_add, u, v)) ≤ real_sum(s, λi:num. u(i))"
	out, err := ChapterSpelling(raw, scope.Syntax, nil)
	if err != nil {
		t.Fatal(err)
	}
	for _, frag := range []string{"vec_add(real_add, u, v, i) = u(i)", "vec_neg(real_neg, u) = u", "‖vec_add(real_add, u, v)‖_n ≤ Σ_{i∈s} u(i)"} {
		if !strings.Contains(out, frag) {
			t.Errorf("the spelled prefix must keep the call form; lacks %q: %s", frag, out)
		}
	}
	for _, bad := range []string{"real_add +", "+ u)(v", "-u"} {
		if strings.Contains(out, bad) {
			t.Errorf("a component was read as a hole (%q): %s", bad, out)
		}
	}
	// Under the bindings the same text folds all the way.
	bound, err := ChapterSpelling(raw, scope.Syntax, scope.ImplicitBindings)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(bound, "(u + v)(i) = u(i) ∧ -u = u ∧ ‖u + v‖_n ≤ Σ_{i∈s} u(i)") {
		t.Errorf("under the bindings the prefix elides and the operators fold: %s", bound)
	}
}

// DisplaySpelling reads the display printers' text: the bare turnstile
// of a hypothesis-free statement is kept, hypotheses before the
// turnstile and a bare term read as statements, and a text the
// spelling cannot read comes back as it is.
func TestDisplaySpelling(t *testing.T) {
	scope := operatorTestScope(t)
	cases := []struct{ in, want string }{
		{"⊢ ∀n.∀u.(norm(n, u) ≤ norm(n, vec_add(real_add, u, u)))", "⊢ ∀n u. ‖u‖_n ≤ ‖u + u‖_n"},
		{"norm(n, u) ≤ norm(m, v),\n\tpair2(u, v) = pair2(v, u)\n\t⊢ (norm(n, u) ≤ norm(m, v))", "‖u‖_n ≤ ‖v‖_m, ⟪u, v⟫ = ⟪v, u⟫ ⊢ ‖u‖_n ≤ ‖v‖_m"},
		{"vec_add(real_add, u, v, i) = u(i)", "(u + v)(i) = u(i)"},
		// Nothing to fold: the display printer's parenthesized form is
		// still re-printed in the chapter's — binders grouped, the ∧
		// chain unbracketed.
		{"⊢ ∀n.∀u.((u(n) = u(n)) ∧ (n = n))", "⊢ ∀n u. u(n) = u(n) ∧ n = n"},
		{"⊢ u = u", "⊢ u = u"},
		{"⊢ ⊢ u", "⊢ ⊢ u"},
	}
	for _, c := range cases {
		if got := DisplaySpelling(c.in, scope.Syntax, scope.ImplicitBindings); got != c.want {
			t.Errorf("DisplaySpelling(%q):\n  got  %q\n  want %q", c.in, got, c.want)
		}
	}
	if got := DisplaySpelling("⊢ norm(n, u) = norm(n, u)", nil, nil); got != "⊢ norm(n, u) = norm(n, u)" {
		t.Errorf("no table: %q", got)
	}
}
