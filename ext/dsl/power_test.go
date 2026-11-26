package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
)

// The power `x ^ n` (parser.go's parsePower) at a carrier no built-in
// domain serves, pinned on a toy monoid power `zz_pow(op, e, x, n)`
// whose operation and identity are implicit, bound to the declared
// variables `mul` and `one` of a carrier type A.
func powerTestScope(t *testing.T, bind bool) *ParseScope {
	t.Helper()
	scope := operatorTestScope(t)
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatalf("type %q: %v", text, err)
		}
		return ty
	}
	scope.ConstMetas["zz_pow"] = core.MakeConstMeta("zz_pow", typ("(A → A → A) → A → A → num → A"))
	scope.Syntax.(testSyntax)["zz_pow"] = &ConstSyntax{Implicit: []string{"op", "e"}, Operator: &Operator{Symbol: "^", Args: []int{0, 1}}}
	for name, ty := range map[string]string{"mul": "A → A → A", "one": "A", "c": "A", "g": "A → A"} {
		scope.Vars[name] = typ(ty)
	}
	if bind {
		scope.ImplicitBindings = map[string]core.Term{
			"op": core.Var("mul", typ("A → A → A")),
			"e":  core.Var("one", typ("A")),
		}
	}
	return scope
}

func TestPower_Parse(t *testing.T) {
	scope := powerTestScope(t, true)
	same := func(sugar, plain string) {
		t.Helper()
		a, b := parseImplicit(t, scope, sugar), parseImplicit(t, scope, plain)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", sugar, plain, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	// The operator is the declaring constant at the bound components;
	// the short application completes to the same term.
	same("c ^ n = zz_pow(c, n)", "zz_pow(mul, one, c, n) = zz_pow(mul, one, c, n)")
	// Looser than application, a sum as the exponent, right-associative.
	same("g(c) ^ n = c ^ (n + 1)", "zz_pow(mul, one, g(c), n) = zz_pow(mul, one, c, n + 1)")
	same("(c ^ n) ^ m = c", "zz_pow(mul, one, zz_pow(mul, one, c, n), m) = c")
}

func TestPower_Refusal(t *testing.T) {
	scope := powerTestScope(t, false)
	res := ParsePropTextInScope("c ^ n = c", scope)
	if len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "implicit argument op is not in scope") {
		t.Fatalf("a power with no bound monoid must be refused, naming the component: %v", res.Errors)
	}
}

// The built-in power domains: the BASE's type picks nat_pow, real_pow
// or int_pow, the exponent is a num, and the printer writes all three
// back as `^` — round-tripping through the parser.
func TestPower_BuiltInDomains(t *testing.T) {
	scope := powerTestScope(t, true)
	for name, meta := range map[string]core.ConstTermMeta{"nat_pow": NatExpMeta, "real_pow": RealPowMeta, "int_pow": IntPowMeta} {
		scope.ConstMetas[name] = meta
	}
	scope.Vars["x"] = RealType
	scope.Vars["a"] = IntType
	same := func(sugar, plain string) {
		t.Helper()
		a, b := parseImplicit(t, scope, sugar), parseImplicit(t, scope, plain)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", sugar, plain, prop.PrintProp(a), prop.PrintProp(b))
		}
		// The printer writes the power as `^` and the parser reads it back.
		printed := prop.FormatPropForParser(a)
		if !strings.Contains(printed, "^") {
			t.Fatalf("%q prints without ^: %s", sugar, printed)
		}
		if parseImplicit(t, scope, printed).AlphaKey() != a.AlphaKey() {
			t.Fatalf("%q does not round-trip through its print %q", sugar, printed)
		}
	}
	same("x ^ n = real_pow(x, n)", "real_pow(x, n) = real_pow(x, n)")
	same("2 ^ n = nat_pow(2, n)", "nat_pow(2, n) = nat_pow(2, n)")
	same("a ^ n = int_pow(a, n)", "int_pow(a, n) = int_pow(a, n)")
	// Tighter than the prefix minus; a negated base is written bracketed.
	same("-x ^ 2 = -(x ^ 2)", "-real_pow(x, 2) = -real_pow(x, 2)")
	same("(-x) ^ 2 = x", "real_pow(-x, 2) = x")
	// Right-associative, the exponent a power at num; a coerced base; a
	// base in a sum; the power under `*`.
	same("x ^ m ^ n = x ^ (m ^ n)", "real_pow(x, nat_pow(m, n)) = real_pow(x, nat_pow(m, n))")
	same("&2 ^ n = real_pow(&2, n)", "real_pow(&2, n) = real_pow(&2, n)")
	same("(x + x) ^ m = x", "real_pow(x + x, m) = x")
	same("x * x ^ n = x * (x ^ n)", "x * real_pow(x, n) = x * real_pow(x, n)")
	// A base at the toy carrier still reaches the declaring constant (the
	// term printer folds no declared operator; ChapterSpelling does).
	if parseImplicit(t, scope, "c ^ n = zz_pow(c, n)").AlphaKey() != parseImplicit(t, scope, "zz_pow(mul, one, c, n) = zz_pow(mul, one, c, n)").AlphaKey() {
		t.Fatal("a base outside the built-in domains must still reach the declaring constant")
	}
	// The exponent must be a num.
	res := ParsePropTextInScope("x ^ x = x", scope)
	if len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "exponent must be a num") {
		t.Fatalf("a real exponent must be refused: %v", res.Errors)
	}
}

// A declared operator whose implicit prefix the spelling cannot drop
// — the components bound by nothing in the text — stays an
// application: the prefix is not operands. (The text is still
// re-printed in the chapter's form; what must not change is the
// application.)
func TestPower_UnboundImplicitPrefixStaysSpelled(t *testing.T) {
	scope := powerTestScope(t, false)
	raw := "c:A, n:num ⊢ zz_pow(mul, one, c, n) = c"
	out, err := ChapterSpelling(raw, scope.Syntax, nil)
	if err != nil || !strings.Contains(out, "zz_pow(mul, one, c, n) = c") {
		t.Fatalf("ChapterSpelling(%q) = %q (%v), want the application spelled as written", raw, out, err)
	}
}

func TestPower_ChapterSpelling(t *testing.T) {
	scope := powerTestScope(t, true)
	decls := "mul:(A → A → A), one:A, c:A, n:num, m:num, g:(A → A) ⊢ "
	raw := decls + "zz_pow(mul, one, c, 2) = zz_pow(mul, one, c, n + 1) ∧ " +
		"zz_pow(mul, one, g(c), m) = c ∧ " +
		"zz_pow(mul, one, zz_pow(mul, one, c, n), m) = c"
	out, err := ChapterSpelling(raw, scope.Syntax, scope.ImplicitBindings)
	if err != nil {
		t.Fatal(err)
	}
	for _, frag := range []string{
		"c ^ 2 = c ^ (n + 1)",
		"g(c) ^ m = c",
		"(c ^ n) ^ m = c",
	} {
		if !strings.Contains(out, frag) {
			t.Errorf("chapter spelling lacks %q: %s", frag, out)
		}
	}
	a, b := parseImplicit(t, scope, out), parseImplicit(t, scope, raw)
	if a.AlphaKey() != b.AlphaKey() {
		t.Fatalf("chapter spelling parses to a different statement: %s", out)
	}
	// The built-in powers fold into the symbol too, from their long
	// spelling — a headline written before `^` reached real.
	scope.ConstMetas["real_pow"] = RealPowMeta
	scope.ConstMetas["nat_pow"] = NatExpMeta
	scope.Vars["x"] = RealType
	long := "x:real, n:num ⊢ real_pow(real_pow(-x, 2), n) = real_pow(x, nat_pow(2, n))"
	folded, err := ChapterSpelling(long, scope.Syntax, nil)
	if err != nil || !strings.Contains(folded, "((-x) ^ 2) ^ n = x ^ 2 ^ n") {
		t.Fatalf("built-in powers must fold: %q (%v)", folded, err)
	}
	if parseImplicit(t, scope, folded).AlphaKey() != parseImplicit(t, scope, long).AlphaKey() {
		t.Fatalf("the folded powers parse to a different statement: %s", folded)
	}
	// The scope-free formatter keeps the grouping the parser reads.
	for in, want := range map[string]string{
		"x ^ m ^ n = y":   "x ^ m ^ n = y",
		"(x ^ m) ^ n = y": "(x ^ m) ^ n = y",
		"-x ^ 2 = (-x)^2": "-x ^ 2 = (-x) ^ 2",
		// A prefix exponent, a coerced power and a coerced base.
		"x ^ -n = y":          "x ^ -n = y",
		"&(x ^ n) = &2 ^ n":   "&(x ^ n) = &2 ^ n",
		"&(-x) = -&x":         "&(-x) = -&x",
		"(Σ_{i<n} c) ^ 2 = y": "(Σ_{i<n} c) ^ 2 = y",
	} {
		got, err := FormatStmtText(in)
		if err != nil || !strings.Contains(got, want) {
			t.Errorf("FormatStmtText(%q) = %q (%v), want %q", in, got, err, want)
		}
	}
}

// A lambda can spell the operation of an explicit power under an
// unrelated exponent called e, the implicit identity's name. Its type
// distinguishes that full application from the short reading.
func TestPower_ExplicitLambdaUnderIdentityName(t *testing.T) {
	scope := powerTestScope(t, false)
	for _, op := range []string{"λp:A. λq:A. p", "λe:A. λq:A. e"} {
		raw := "∀e:num. zz_pow((" + op + "), c, c, e) = c"
		explicit := "∀e:num. zz_pow⟨A:A⟩((" + op + "), c, c, e) = c"
		assertSameProp(t, scope, raw, explicit)
		original := parseImplicit(t, scope, raw)
		printed := prop.FormatPropForParser(original)
		if parseImplicit(t, scope, printed).AlphaKey() != original.AlphaKey() {
			t.Fatalf("explicit lambda power does not round-trip: %s", printed)
		}
	}
}

// A variable of the text named like one component, beside a component
// the scope binds elsewhere, is no component: the prefix would hold
// pieces of two structures. The operator and the short application
// refuse it and name the variable; a text that binds every component
// reads them as before, and so does one that binds none.
func TestPower_AVariableNamedLikeOneComponent(t *testing.T) {
	scope := powerTestScope(t, true)
	for _, text := range []string{
		"∃e:A. c ^ n = e",
		"∃e:A. zz_pow(c, n) = e",
		"∃e:num. c ^ e = c",
	} {
		res := ParsePropTextInScope(text, scope)
		if len(res.Errors) == 0 {
			t.Errorf("%q is read, its e the identity of the power", text)
			continue
		}
		msg := res.Errors[0].Message
		if !strings.Contains(msg, "zz_pow") || !strings.Contains(msg, "the variable e") || !strings.Contains(msg, "op") {
			t.Errorf("%q: the refusal does not name the constant, the variable e and the component read elsewhere: %s", text, msg)
		}
	}
	same := func(sugar, plain string) {
		t.Helper()
		a, b := parseImplicit(t, scope, sugar), parseImplicit(t, scope, plain)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", sugar, plain, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	same("∀op:A → A → A. ∀e:A. c ^ n = e", "∀op:A → A → A. ∀e:A. zz_pow(op, e, c, n) = e")
	same("∃d:A. c ^ n = d", "∃d:A. zz_pow(mul, one, c, n) = d")

	// A variable that carries a structure is a component beside one read
	// elsewhere: a structure predicate applied to it in the text, or in
	// a fact of the goal the text is read under.
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatalf("type %q: %v", text, err)
		}
		return ty
	}
	scope.ConstMetas["zz_pointed"] = core.MakeConstMeta("zz_pointed", typ("A → bool"))
	scope.Syntax.(testSyntax)["zz_pointed"] = &ConstSyntax{StructurePredicate: true}
	same("∀e:A. zz_pointed(e) ⇒ c ^ n = e", "∀e:A. zz_pointed(e) ⇒ zz_pow(mul, e, c, n) = e")
	scope.Vars["e"] = typ("A")
	if res := ParsePropTextInScope("c ^ n = e", scope); len(res.Errors) == 0 {
		t.Errorf("a declared e with no structure fact over it is read as the identity of the power")
	}
	pointed := core.MakeConstTerm(scope.ConstMetas["zz_pointed"], typ("A → bool"))
	scope.ResidentFacts = []core.Term{core.Apply(pointed, core.Var("e", typ("A")))}
	same("c ^ n = e", "zz_pow(mul, e, c, n) = e")
}
