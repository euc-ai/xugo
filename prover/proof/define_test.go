package proof

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// Test-local ℕ-ish vocabulary. The metas live only in values this test
// builds; nothing registers globally (MintDirectDefinition registers
// into the per-env MockConstMetaService).
var (
	defTestNumMeta = MakeMetaType("num", 0)
	defTestNum     = MakeCompositeType(defTestNumMeta)
)

func defTestMulConst() ConstTerm {
	t := MakeFun(defTestNum, MakeFun(defTestNum, defTestNum))
	return MakeConstTerm(MakeConstMeta("zz_test_mul", t), t)
}

// dvdEquation builds the nat_divides shape with a fresh definiendum
// name: ∀d n. name(d, n) ⇔ ∃x. n = mul(d, x)
func dvdEquation(name string) (Prop, VarTerm) {
	mul := defTestMulConst()
	d, n, x := Var("d", defTestNum), Var("n", defTestNum), Var("x", defTestNum)
	dvd := Var(TermName(name), MakeFun(defTestNum, MakeFun(defTestNum, TypeBool)))
	body := Exists(x)(n.Eq(Apply(mul, d, x)))
	eq := dvd.Apply(d, n).Eq(body)
	return prop.MakeProp(ForAll(d)(ForAll(n)(eq))), dvd.Core().(VarTerm)
}

func TestAnalyzeDirectDefinition(t *testing.T) {
	equation, defVar := dvdEquation("zz_dvd_analyze")
	dd, err := AnalyzeDirectDefinition(equation, defVar)
	if err != nil {
		t.Fatal(err)
	}
	if len(dd.Args) != 2 || string(dd.Args[0].Name()) != "d" || string(dd.Args[1].Name()) != "n" {
		t.Fatalf("args = %v, want [d n]", dd.Args)
	}
	// Lambda is λd n. body.
	d, n := Var("d", defTestNum), Var("n", defTestNum)
	x := Var("x", defTestNum)
	wantLambda := d.To(n.To(Exists(x)(n.Eq(Apply(defTestMulConst(), d, x)))))
	if !dd.Lambda.AlphaEquals(wantLambda.Core()) {
		t.Errorf("lambda = %s, want %s", PrintTerm(dd.Lambda), PrintTerm(wantLambda))
	}
}

func TestAnalyzeDirectDefinitionRejects(t *testing.T) {
	mul := defTestMulConst()
	d, n := Var("d", defTestNum), Var("n", defTestNum)
	fNum := Var("zz_f", MakeFun(defTestNum, defTestNum))
	fVar := fNum.Core().(VarTerm)
	dvd := Var("zz_dvd_rej", MakeFun(defTestNum, MakeFun(defTestNum, TypeBool)))
	dvdVar := dvd.Core().(VarTerm)

	for _, tc := range []struct {
		name string
		p    Prop
		v    VarTerm
		want string
	}{
		{
			"free variable besides the definiendum",
			prop.MakeProp(ForAll(d)(dvd.Apply(d, n).Eq(n.Eq(n)))),
			dvdVar,
			"free variable",
		},
		{
			"definiendum on the right",
			prop.MakeProp(ForAll(d)(ForAll(n)(n.Eq(n).Eq(dvd.Apply(d, n))))),
			dvdVar,
			"must head the LEFT side",
		},
		{
			"recursive occurrence",
			prop.MakeProp(ForAll(n)(fNum.Apply(n).Eq(fNum.Apply(n)))),
			fVar,
			"recursive",
		},
		{
			"pattern argument",
			prop.MakeProp(ForAll(n)(fNum.Apply(Apply(mul, n, n)).Eq(n))),
			fVar,
			"plain ∀-bound variable",
		},
		{
			"repeated argument",
			prop.MakeProp(ForAll(n)(dvd.Apply(n, n).Eq(n.Eq(n)))),
			dvdVar,
			"repeats",
		},
		{
			"unused binder",
			prop.MakeProp(ForAll(d)(ForAll(n)(fNum.Apply(d).Eq(d)))),
			fVar,
			"is not an argument",
		},
		{
			"not an equation",
			prop.MakeProp(ForAll(d)(ForAll(n)(dvd.Apply(d, n)))),
			dvdVar,
			"must be an equation",
		},
	} {
		_, err := AnalyzeDirectDefinition(tc.p, tc.v)
		if err == nil {
			t.Errorf("%s: expected an error", tc.name)
			continue
		}
		if !strings.Contains(err.Error(), tc.want) {
			t.Errorf("%s: error %q does not mention %q", tc.name, err.Error(), tc.want)
		}
	}
}

func TestMintAndDeriveDirectDefinition(t *testing.T) {
	env := makeStepTestEnv()
	equation, defVar := dvdEquation("zz_dvd_mint")
	dd, err := AnalyzeDirectDefinition(equation, defVar)
	if err != nil {
		t.Fatal(err)
	}
	c, characterizing, err := MintDirectDefinition(env, dd)
	if err != nil {
		t.Fatal(err)
	}
	if string(c.Name()) != "zz_dvd_mint" {
		t.Fatalf("minted const name = %q", c.Name())
	}
	if frees := characterizing.Conclusion().Frees(nil); len(frees) != 0 {
		t.Fatalf("characterizing statement must be closed; frees = %v", frees)
	}

	// The executor's core: derive the characterizing theorem from the
	// stored definition, landing exactly on the goal form.
	derived := deriveDirectCharacterizing(c, characterizing)
	if derived == nil {
		t.Fatal("deriveDirectCharacterizing returned nil on the characterizing goal")
	}
	if !derived.Proved() {
		t.Fatal("derived characterizing theorem is not proved")
	}
	if !derived.AlphaEquals(characterizing) {
		t.Fatalf("derived %v does not α-match the characterizing goal %v", derived, characterizing)
	}

	// Exclusive registration: the same name errors on a second mint.
	if _, _, err := MintDirectDefinition(env, dd); err == nil ||
		!strings.Contains(err.Error(), "already registered") {
		t.Fatalf("second mint of the same name must error; got %v", err)
	}

	// A goal that is not this const's characterizing shape declines.
	if got := deriveDirectCharacterizing(c, equation); got != nil {
		t.Fatalf("definiendum-var goal must decline, got %v", got)
	}
}

// TestParseDefinitionEquationDoor exercises the text door end-to-end
// on a self-contained boolean definition (no registry needed: ∧∨¬ are
// DSL operators, the binders declare their own types):
// text → parse-with-definiendum → analyze → mint → derive.
func TestParseDefinitionEquationDoor(t *testing.T) {
	equation, defVar, err := ParseDefinitionEquation(
		"∀p q:bool. zz_xor(p, q) ⇔ (p ∨ q) ∧ ¬(p ∧ q)",
		"zz_xor", "bool → bool → bool", &dsl.ParseScope{})
	if err != nil {
		t.Fatal(err)
	}
	dd, err := AnalyzeDirectDefinition(equation, defVar)
	if err != nil {
		t.Fatal(err)
	}
	env := makeStepTestEnv()
	c, characterizing, err := MintDirectDefinition(env, dd)
	if err != nil {
		t.Fatal(err)
	}
	derived := deriveDirectCharacterizing(c, characterizing)
	if derived == nil || !derived.Proved() || !derived.AlphaEquals(characterizing) {
		t.Fatalf("text-door characterizing derivation failed: %v", derived)
	}
}

func TestParseDefinitionEquationRejects(t *testing.T) {
	// Strict resolution stays armed for every name that is NOT the
	// definiendum: an undeclared body name errors instead of freshening.
	_, _, err := ParseDefinitionEquation(
		"∀p:bool. zz_bad(p) ⇔ p ∧ oops",
		"zz_bad", "bool → bool", &dsl.ParseScope{})
	if err == nil || !strings.Contains(err.Error(), "oops") {
		t.Errorf("undeclared body name must error naming it; got %v", err)
	}

	// A name the scope already resolves as a constant is refused before
	// any parse — a definition mints a FRESH name.
	taken := defTestMulConst()
	base := &dsl.ParseScope{ConstMetas: map[string]ConstTermMeta{
		string(taken.Name()): taken.Meta(),
	}}
	_, _, err = ParseDefinitionEquation(
		"∀p:bool. zz_test_mul(p) ⇔ p",
		"zz_test_mul", "bool → bool", base)
	if err == nil || !strings.Contains(err.Error(), "already names a constant") {
		t.Errorf("taken name must be refused; got %v", err)
	}

	// Garbage type text errors at the type, not mid-parse.
	_, _, err = ParseDefinitionEquation("∀p:bool. f(p) ⇔ p", "f", "→→", &dsl.ParseScope{})
	if err == nil || !strings.Contains(err.Error(), "definition type") {
		t.Errorf("bad type text must error at the type; got %v", err)
	}
}

// ---------------------------------------------------------------------------
// The recursive shape — compiler tests against a TestThm-backed schema
// (the corpus-forced end-to-end lives in library/registry's
// external test; here the pipeline logic is exercised in isolation).
// ---------------------------------------------------------------------------

func defTestZeroConst() ConstTerm {
	return MakeConstTerm(MakeConstMeta("_0", defTestNum), defTestNum)
}

func defTestSucConst() ConstTerm {
	t := MakeFun(defTestNum, defTestNum)
	return MakeConstTerm(MakeConstMeta("suc", t), t)
}

func defTestAddConst() ConstTerm {
	t := MakeFun(defTestNum, MakeFun(defTestNum, defTestNum))
	return MakeConstTerm(MakeConstMeta("zz_add", t), t)
}

// numAxiomTestSchema builds the corpus num_recursion arrangement over the
// test-local num, polymorphic in the motive A:
//
//	∀f e. ∃!fn. ∀n. (e = fn(_0)) ∧ (fn(suc n) = f(fn n, n))
func numAxiomTestSchema() Term {
	A := TypeA
	zero, suc := defTestZeroConst(), defTestSucConst()
	f := Var("f", MakeFun(A, MakeFun(defTestNum, A)))
	e := Var("e", A)
	fn := Var("fn", MakeFun(defTestNum, A))
	n := Var("n", defTestNum)
	base := e.Eq(fn.Apply(WrapTerm(zero)))
	step := fn.Apply(Apply(suc, n)).Eq(f.Apply(fn.Apply(n), n))
	return ForAll(f)(ForAll(e)(Unique(fn)(ForAll(n)(base.And(step))))).Core()
}

// sumtoEquations builds transcript A1's equations with a fresh
// definiendum var: f(_0) = _0 and ∀n. f(suc n) = add(f(n), suc(n)) —
// author-natural orientation and per-clause binders, deliberately NOT
// the schema's arrangement.
func sumtoEquations() ([]Prop, VarTerm) {
	zero, suc, add := defTestZeroConst(), defTestSucConst(), defTestAddConst()
	f := Var("zz_sumto", MakeFun(defTestNum, defTestNum))
	n := Var("n", defTestNum)
	eq1 := prop.MakeProp(f.Apply(WrapTerm(zero)).Eq(WrapTerm(zero)))
	eq2 := prop.MakeProp(ForAll(n)(
		f.Apply(Apply(suc, n)).Eq(Apply(add, f.Apply(n), Apply(suc, n)))))
	return []Prop{eq1, eq2}, f.Core().(VarTerm)
}

func TestCompileRecursiveExistenceSumto(t *testing.T) {
	env := makeStepTestEnv()
	env.LibraryThms = map[string]Thm{"num_recursion": core.TestThm(numAxiomTestSchema())}

	equations, defVar := sumtoEquations()
	rd, err := AnalyzeRecursiveDefinition(equations, defVar)
	if err != nil {
		t.Fatal(err)
	}
	if len(rd.Clauses) != 2 {
		t.Fatalf("clauses = %d, want 2", len(rd.Clauses))
	}
	if got := string(rd.Clauses[0].Constructor.Name()); got != "_0" {
		t.Errorf("clause 0 constructor = %q, want _0", got)
	}
	if got := string(rd.Clauses[1].Constructor.Name()); got != "suc" {
		t.Errorf("clause 1 constructor = %q, want suc", got)
	}

	proved, schema, err := CompileRecursiveExistence(env, rd)
	if err != nil {
		t.Fatal(err)
	}
	if schema != "num_recursion" {
		t.Errorf("schema = %q, want num_recursion", schema)
	}
	if proved == nil || !proved.Proved() {
		t.Fatal("compiled existence is not proved")
	}
	if !proved.AlphaEquals(rd.ExistsStmt) {
		t.Fatalf("compiled existence:\n  %s\nwants the obligation form:\n  %s",
			PrintProp(proved), PrintProp(rd.ExistsStmt))
	}

	// The obligation round-trips through the ∃-side analyzer — the
	// _DefineStep executor's replay entry.
	rd2, err := AnalyzeRecursiveExistence(rd.ExistsStmt)
	if err != nil {
		t.Fatal(err)
	}
	if len(rd2.Clauses) != 2 || !rd2.ExistsStmt.AlphaEquals(rd.ExistsStmt) {
		t.Fatal("AnalyzeRecursiveExistence does not round-trip the obligation")
	}
}

func TestCompileRecursiveExistenceRejects(t *testing.T) {
	env := makeStepTestEnv()
	env.LibraryThms = map[string]Thm{"num_recursion": core.TestThm(numAxiomTestSchema())}
	zero, suc := defTestZeroConst(), defTestSucConst()
	pairN := defTestMulConst() // any non-constructor binary head
	f := Var("zz_rej", MakeFun(defTestNum, defTestNum))
	fVar := f.Core().(VarTerm)
	n, m := Var("n", defTestNum), Var("m", defTestNum)

	// Missing constructor equation: base only.
	rd, err := AnalyzeRecursiveDefinition(
		[]Prop{prop.MakeProp(f.Apply(WrapTerm(zero)).Eq(WrapTerm(zero)))}, fVar)
	if err != nil {
		t.Fatal(err)
	}
	if _, _, err := CompileRecursiveExistence(env, rd); err == nil ||
		!strings.Contains(err.Error(), "missing equation for constructor") {
		t.Errorf("missing suc equation must fail naming it; got %v", err)
	}

	// An equation whose pattern head is not a schema constructor.
	rd, err = AnalyzeRecursiveDefinition([]Prop{
		prop.MakeProp(f.Apply(WrapTerm(zero)).Eq(WrapTerm(zero))),
		prop.MakeProp(ForAll(n)(f.Apply(Apply(suc, n)).Eq(f.Apply(n)))),
		prop.MakeProp(ForAll(n)(ForAll(m)(f.Apply(Apply(pairN, n, m)).Eq(WrapTerm(zero))))),
	}, fVar)
	if err != nil {
		t.Fatal(err)
	}
	if _, _, err := CompileRecursiveExistence(env, rd); err == nil ||
		!strings.Contains(err.Error(), "matches no constructor clause") {
		t.Errorf("non-constructor pattern must fail naming it; got %v", err)
	}

	// Nested recursion is out of the v1 shape — rejected at analysis.
	_, err = AnalyzeRecursiveDefinition([]Prop{
		prop.MakeProp(f.Apply(WrapTerm(zero)).Eq(WrapTerm(zero))),
		prop.MakeProp(ForAll(n)(f.Apply(Apply(suc, n)).Eq(f.Apply(f.Apply(n))))),
	}, fVar)
	if err == nil || !strings.Contains(err.Error(), "pattern argument at the recursion position") {
		t.Errorf("nested recursion must be rejected at analysis; got %v", err)
	}

	// A bare (unapplied) definiendum on the right: f passed as a VALUE
	// to a λ — no recursion slot can serve that.
	h := Var("h", MakeFun(defTestNum, defTestNum))
	_, err = AnalyzeRecursiveDefinition([]Prop{
		prop.MakeProp(f.Apply(WrapTerm(zero)).Eq(WrapTerm(zero))),
		prop.MakeProp(ForAll(n)(f.Apply(Apply(suc, n)).Eq(
			h.To(h.Apply(n)).Apply(f)))),
	}, fVar)
	if err == nil || !strings.Contains(err.Error(), "bare value") {
		t.Errorf("a bare definiendum occurrence must be rejected; got %v", err)
	}
}

// TestSimpWithConjunctionRule pins the fact installation (the manual's R4)
// rests on: a define's characterizing CONJUNCTION is itself a valid
// simp_with rule (the proto contract's "∀-prefixed = / ⇔, conjunctions
// thereof"), so the session simp set installs the theorem WHOLE — the
// surfaced rule child is the conjunction statement, closed from the
// definition section's own cert, and no per-clause splitting exists
// anywhere.
func TestSimpWithConjunctionRule(t *testing.T) {
	env := makeStepTestEnv()
	equations, defVar := sumtoEquations()
	rd, err := AnalyzeRecursiveDefinition(equations, defVar)
	if err != nil {
		t.Fatal(err)
	}
	c, characterizing, err := MintRecursiveDefinition(env, rd)
	if err != nil {
		t.Fatal(err)
	}

	// Goal: add(zz_sumto(_0), a) = add(_0, a) — the base clause rewrites
	// the left side; the residual is refl-closable.
	zero, add := defTestZeroConst(), defTestAddConst()
	a := Var("a", defTestNum)
	goal := prop.MakeProp(
		WrapTerm(Apply(add, Apply(c, zero), a)).
			Eq(Apply(add, WrapTerm(zero), a)))

	ctx := NewScript(env)
	sec := ctx.Section(goal)
	if !ApplySimpWith(sec, []Prop{characterizing}) {
		t.Fatal("the characterizing conjunction did not fire as a simp rule")
	}
	leaves := sec.UnsolvedLeaves()
	if len(leaves) != 2 {
		t.Fatalf("expected [rule child, residual], got %d leaves", len(leaves))
	}
	if !characterizing.AlphaEquals(leaves[0].Goal) {
		t.Fatalf("rule child %s is not the conjunction statement",
			PrintProp(leaves[0].Goal))
	}

	// Close the rule child from the definition's own cert (the session
	// stores the define section's promise; here a derived cert stands in),
	// and the residual by refl.
	cert := deriveDirectCharacterizingStandin(t, env, c, characterizing)
	leaves[0].Do(CiteKnown(cert))
	leaves[1].Do(Refl())
	if !sec.Proved() {
		t.Fatal("closing rule child + residual must prove the section")
	}
}

// deriveDirectCharacterizingStandin builds a real proved cert for the
// characterizing statement the way a define section would (the
// composite's own executor), so the simp test's rule child closes from
// a genuine kernel object rather than a TestThm.
func deriveDirectCharacterizingStandin(t *testing.T, env *ProverEnv, c ConstTerm, characterizing Prop) Prop {
	t.Helper()
	ctx := NewScript(env)
	sec := ctx.Section(characterizing)
	sec.Do(DefineStep(c))
	leaves := sec.UnsolvedLeaves()
	if len(leaves) != 1 {
		t.Fatalf("expected the one existence obligation, got %d leaves", len(leaves))
	}
	// No schema in this env — close the ∃ by witnessing the ε itself?
	// No: the obligation is real mathematics here. A TestThm-backed
	// close keeps the simp test focused on the RULE mechanics.
	leaves[0].Do(CiteKnown(core.TestThm(leaves[0].Goal.Conclusion())))
	if !sec.Proved() {
		t.Fatal("standin definition section did not close")
	}
	return sec.PromisedThm()
}

func TestMintAndDeriveNullaryDefinition(t *testing.T) {
	env := makeStepTestEnv()
	mul := defTestMulConst()
	k := Var("zz_k_nullary", mul.Type())
	equation := prop.MakeProp(k.Eq(WrapTerm(mul)))
	dd, err := AnalyzeDirectDefinition(equation, k.Core().(VarTerm))
	if err != nil {
		t.Fatal(err)
	}
	if len(dd.Args) != 0 {
		t.Fatalf("nullary definition has %d args", len(dd.Args))
	}
	c, characterizing, err := MintDirectDefinition(env, dd)
	if err != nil {
		t.Fatal(err)
	}
	derived := deriveDirectCharacterizing(c, characterizing)
	if derived == nil || !derived.Proved() || !derived.AlphaEquals(characterizing) {
		t.Fatalf("nullary characterizing derivation failed: %v", derived)
	}
}

// =======================================================================
// v1.1 — curried parameters
// =======================================================================

// The v1.1 shape tests: curried extra parameters through the equation
// compiler, against the TestThm-backed num_recursion schema — the
// conventions of the v1 tests above. The corpus-forced end-to-end
// lives in library/registry's external test, the
// six-twin shape battery in engine/define_curry_battery_test.go.

func defTestPreConst() ConstTerm {
	t := MakeFun(defTestNum, defTestNum)
	return MakeConstTerm(MakeConstMeta("zz_pre", t), t)
}

func defTestTlConst() ConstTerm {
	t := MakeFun(defTestNum, defTestNum)
	return MakeConstTerm(MakeConstMeta("zz_tl", t), t)
}

// addShapeEquations is the ADD shape — recursion argument FIRST, one
// extra curried parameter, constant through the recursion (v1.1a):
//
//	∀n. f(0, n) = n
//	∀m n. f(suc m, n) = suc(f(m, n))
func addShapeEquations(name string) ([]Prop, VarTerm) {
	zero, suc := defTestZeroConst(), defTestSucConst()
	f := Var(TermName(name), MakeFun(defTestNum, MakeFun(defTestNum, defTestNum)))
	m, n := Var("m", defTestNum), Var("n", defTestNum)
	eq1 := prop.MakeProp(ForAll(n)(
		f.Apply(WrapTerm(zero), n).Eq(n)))
	eq2 := prop.MakeProp(ForAll(m)(ForAll(n)(
		f.Apply(Apply(suc, m), n).Eq(Apply(suc, f.Apply(m, n))))))
	return []Prop{eq1, eq2}, f.Core().(VarTerm)
}

// TestIsCompiledDefinitionEquation — the doors' shape classifier for a
// single equation: it compiles when it recurs, and when an argument on
// its left is a constructor pattern although nothing recurs (a
// one-constructor datatype's projection); a body free of the
// definiendum over plain variables is the direct shape.
func TestIsCompiledDefinitionEquation(t *testing.T) {
	direct, dvdVar := dvdEquation("zz_dvd_classify")
	if IsCompiledDefinitionEquation(direct, dvdVar) {
		t.Error("a direct definition over plain variables was sent to the compiler")
	}
	suc := defTestSucConst()
	n := Var("n", defTestNum)
	pred := Var("zz_pred_classify", MakeFun(defTestNum, defTestNum))
	pattern := prop.MakeProp(ForAll(n)(pred.Apply(Apply(suc, n)).Eq(n)))
	if !IsCompiledDefinitionEquation(pattern, pred.Core().(VarTerm)) {
		t.Error("a single non-recursive pattern clause was sent to the direct shape")
	}
	equations, defVar := addShapeEquations("zz_cadd_classify")
	if !IsCompiledDefinitionEquation(equations[1], defVar) {
		t.Error("a recursive clause was sent to the direct shape")
	}
}

// subShapeEquations is the SUB shape — recursion on the SECOND
// argument (v1.1b, the reshuffle):
//
//	∀m. f(m, 0) = m
//	∀m n. f(m, suc n) = pre(f(m, n))
func subShapeEquations(name string) ([]Prop, VarTerm) {
	zero, suc, pre := defTestZeroConst(), defTestSucConst(), defTestPreConst()
	f := Var(TermName(name), MakeFun(defTestNum, MakeFun(defTestNum, defTestNum)))
	m, n := Var("m", defTestNum), Var("n", defTestNum)
	eq1 := prop.MakeProp(ForAll(m)(
		f.Apply(m, WrapTerm(zero)).Eq(m)))
	eq2 := prop.MakeProp(ForAll(m)(ForAll(n)(
		f.Apply(m, Apply(suc, n)).Eq(Apply(pre, f.Apply(m, n))))))
	return []Prop{eq1, eq2}, f.Core().(VarTerm)
}

func numAxiomTestEnv() *ProverEnv {
	env := makeStepTestEnv()
	env.LibraryThms = map[string]Thm{"num_recursion": core.TestThm(numAxiomTestSchema())}
	return env
}

func TestCompileCurriedAddShape(t *testing.T) {
	env := numAxiomTestEnv()
	equations, defVar := addShapeEquations("zz_cadd")
	rd, err := AnalyzeRecursiveDefinition(equations, defVar)
	if err != nil {
		t.Fatal(err)
	}
	if rd.RecArgPos != 0 {
		t.Fatalf("RecArgPos = %d, want 0", rd.RecArgPos)
	}
	if !rd.ResultType.Equals(MakeFun(defTestNum, defTestNum)) {
		t.Fatalf("motive = %s, want num → num", FormatType(rd.ResultType))
	}
	if len(rd.Clauses[1].ExtraParams) != 1 ||
		string(rd.Clauses[1].ExtraParams[0].Name()) != "n" {
		t.Fatalf("suc clause extra params = %v, want [n]", rd.Clauses[1].ExtraParams)
	}

	proved, schema, err := CompileRecursiveExistence(env, rd)
	if err != nil {
		t.Fatal(err)
	}
	if schema != "num_recursion" {
		t.Errorf("schema = %q, want num_recursion", schema)
	}
	if proved == nil || !proved.Proved() {
		t.Fatal("compiled existence is not proved")
	}
	if !proved.AlphaEquals(rd.ExistsStmt) {
		t.Fatalf("compiled existence:\n  %s\nwants the obligation form:\n  %s",
			PrintProp(proved), PrintProp(rd.ExistsStmt))
	}
}

// TestCompileCurriedElShape — recursion argument first, the extra
// argument CHANGES in the recursive call (the nth-element class): pure
// result-type currying must cover it — the recursive result is a
// function, applied to whatever the clause says.
//
//	∀a. f(0, a) = a
//	∀n a. f(suc n, a) = f(n, tl(a))
func TestCompileCurriedElShape(t *testing.T) {
	env := numAxiomTestEnv()
	zero, suc, tl := defTestZeroConst(), defTestSucConst(), defTestTlConst()
	f := Var("zz_cel", MakeFun(defTestNum, MakeFun(defTestNum, defTestNum)))
	n, a := Var("n", defTestNum), Var("a", defTestNum)
	equations := []Prop{
		prop.MakeProp(ForAll(a)(f.Apply(WrapTerm(zero), a).Eq(a))),
		prop.MakeProp(ForAll(n)(ForAll(a)(
			f.Apply(Apply(suc, n), a).Eq(f.Apply(n, Apply(tl, a)))))),
	}
	rd, err := AnalyzeRecursiveDefinition(equations, f.Core().(VarTerm))
	if err != nil {
		t.Fatal(err)
	}
	proved, _, err := CompileRecursiveExistence(env, rd)
	if err != nil {
		t.Fatal(err)
	}
	if !proved.Proved() || !proved.AlphaEquals(rd.ExistsStmt) {
		t.Fatalf("nth-element-shape existence:\n  %s\nwants:\n  %s",
			PrintProp(proved), PrintProp(rd.ExistsStmt))
	}
}

func TestCompileCurriedSubShape(t *testing.T) {
	env := numAxiomTestEnv()
	equations, defVar := subShapeEquations("zz_csub")
	rd, err := AnalyzeRecursiveDefinition(equations, defVar)
	if err != nil {
		t.Fatal(err)
	}
	if rd.RecArgPos != 1 {
		t.Fatalf("RecArgPos = %d, want 1", rd.RecArgPos)
	}
	if !rd.CarrierType.Equals(defTestNum) {
		t.Fatalf("carrier = %s, want num", FormatType(rd.CarrierType))
	}
	if !rd.ResultType.Equals(MakeFun(defTestNum, defTestNum)) {
		t.Fatalf("motive = %s, want num → num", FormatType(rd.ResultType))
	}

	proved, schema, err := CompileRecursiveExistence(env, rd)
	if err != nil {
		t.Fatal(err)
	}
	if schema != "num_recursion" {
		t.Errorf("schema = %q, want num_recursion", schema)
	}
	if proved == nil || !proved.Proved() {
		t.Fatal("compiled existence is not proved")
	}
	if !proved.AlphaEquals(rd.ExistsStmt) {
		t.Fatalf("reshuffled existence:\n  %s\nwants the obligation form (author "+
			"argument order):\n  %s", PrintProp(proved), PrintProp(rd.ExistsStmt))
	}

	// The obligation round-trips through the ∃-side analyzer — the
	// _DefineStep executor's replay entry — with the reshuffle intact.
	rd2, err := AnalyzeRecursiveExistence(rd.ExistsStmt)
	if err != nil {
		t.Fatal(err)
	}
	if rd2.RecArgPos != 1 || !rd2.ExistsStmt.AlphaEquals(rd.ExistsStmt) {
		t.Fatal("AnalyzeRecursiveExistence does not round-trip the reshuffled obligation")
	}
}

// TestCompileCurriedHigherOrderExtra — a function-typed extra
// parameter used in the RHS (the list_map flavor, over num):
//
//	∀g. f(g, 0) = 0
//	∀g n. f(g, suc n) = g(f(g, n))
func TestCompileCurriedHigherOrderExtra(t *testing.T) {
	env := numAxiomTestEnv()
	zero, suc := defTestZeroConst(), defTestSucConst()
	fnTy := MakeFun(defTestNum, defTestNum)
	f := Var("zz_citer", MakeFun(fnTy, MakeFun(defTestNum, defTestNum)))
	g, n := Var("g", fnTy), Var("n", defTestNum)
	equations := []Prop{
		prop.MakeProp(ForAll(g)(
			f.Apply(g, WrapTerm(zero)).Eq(WrapTerm(zero)))),
		prop.MakeProp(ForAll(g)(ForAll(n)(
			f.Apply(g, Apply(suc, n)).Eq(g.Apply(f.Apply(g, n)))))),
	}
	rd, err := AnalyzeRecursiveDefinition(equations, f.Core().(VarTerm))
	if err != nil {
		t.Fatal(err)
	}
	if rd.RecArgPos != 1 {
		t.Fatalf("RecArgPos = %d, want 1", rd.RecArgPos)
	}
	proved, _, err := CompileRecursiveExistence(env, rd)
	if err != nil {
		t.Fatal(err)
	}
	if !proved.Proved() || !proved.AlphaEquals(rd.ExistsStmt) {
		t.Fatalf("higher-order-extra existence:\n  %s\nwants:\n  %s",
			PrintProp(proved), PrintProp(rd.ExistsStmt))
	}
}

// TestCurriedDefineStepEndToEnd runs the v1.1b shape through the mint
// and the composite: the section's one _DefineStep closes engine-side
// from the schema in env.LibraryThms.
func TestCurriedDefineStepEndToEnd(t *testing.T) {
	env := numAxiomTestEnv()
	equations, defVar := subShapeEquations("zz_csub_step")
	rd, err := AnalyzeRecursiveDefinition(equations, defVar)
	if err != nil {
		t.Fatal(err)
	}
	c, characterizing, err := MintRecursiveDefinition(env, rd)
	if err != nil {
		t.Fatal(err)
	}
	ctx := NewScript(env)
	sec := ctx.Section(characterizing)
	sec.Do(DefineStep(c))
	if !sec.Proved() {
		t.Fatal("the curried define composite did not close from the schema")
	}
}

func TestAnalyzeCurriedRejects(t *testing.T) {
	zero, suc := defTestZeroConst(), defTestSucConst()
	f := Var("zz_crej", MakeFun(defTestNum, MakeFun(defTestNum, defTestNum)))
	fVar := f.Core().(VarTerm)
	m, n := Var("m", defTestNum), Var("n", defTestNum)

	for _, tc := range []struct {
		name string
		eqs  []Prop
		want string
	}{
		{
			"patterns at two positions",
			[]Prop{
				prop.MakeProp(ForAll(n)(f.Apply(WrapTerm(zero), n).Eq(n))),
				prop.MakeProp(ForAll(m)(ForAll(n)(
					f.Apply(Apply(suc, m), Apply(suc, n)).Eq(n)))),
			},
			"argument positions",
		},
		{
			"arity mismatch across clauses",
			[]Prop{
				prop.MakeProp(ForAll(n)(f.Apply(WrapTerm(zero), n).Eq(n))),
				prop.MakeProp(ForAll(m)(f.Apply(Apply(suc, m)).Eq(f.Apply(m)))),
			},
			"different argument counts",
		},
		{
			"pattern variable doubling as extra parameter",
			[]Prop{
				prop.MakeProp(ForAll(m)(f.Apply(m, Apply(suc, m)).Eq(m))),
			},
			"both a pattern argument and an extra parameter",
		},
		{
			"recursive call missing the recursion argument",
			[]Prop{
				prop.MakeProp(ForAll(m)(f.Apply(m, WrapTerm(zero)).Eq(m))),
				prop.MakeProp(ForAll(m)(ForAll(n)(
					f.Apply(m, Apply(suc, n)).Eq(
						Var("h", MakeFun(defTestNum, defTestNum)).
							To(Var("h", MakeFun(defTestNum, defTestNum)).Apply(n)).
							Apply(f.Apply(m)))))),
			},
			"reaches only 1 argument",
		},
	} {
		_, err := AnalyzeRecursiveDefinition(tc.eqs, fVar)
		if err == nil {
			t.Errorf("%s: expected an error", tc.name)
			continue
		}
		if !strings.Contains(err.Error(), tc.want) {
			t.Errorf("%s: error %q does not mention %q", tc.name, err.Error(), tc.want)
		}
	}
}
