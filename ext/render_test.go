package ext

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// numTypeForTest mirrors dsl.NumType (the HOL `num` type) built straight
// from core, so this internal test of ext need not import ext/dsl —
// which would create a test-only import cycle (dsl imports ext).
// HolType equality is structural, so the printer still dispatches on the
// "num" meta name and emits `dsl.NumType` exactly as for the real type.
var numTypeForTest = core.MakeCompositeType(core.MakeMetaType("num", 0))

// makeTestPrinter builds a GoTermPrinter whose VarIdent resolves the
// supplied vars to their HOL names verbatim — convenient for table
// tests where the wanted output uses bare identifiers.
func makeTestPrinter(vars ...core.VarTerm) *GoTermPrinter {
	idents := make(map[varTestKey]string, len(vars))
	for _, v := range vars {
		idents[varTestKey{v.Name(), v.Type().Key()}] = string(v.Name())
	}
	return &GoTermPrinter{
		VarIdent: func(v core.VarTerm) (string, bool) {
			id, ok := idents[varTestKey{v.Name(), v.Type().Key()}]
			return id, ok
		},
	}
}

type varTestKey struct {
	name core.TermName
	tkey core.TypeKey
}

// TestGoPrinter_Term exercises term-level rendering: connectives,
// multi-binder quantifiers, multi-arg application, and the interaction
// between them.
func TestGoPrinter_Term(t *testing.T) {
	x := core.Var("x", core.TypeBool())
	y := core.Var("y", core.TypeBool())
	z := core.Var("z", core.TypeBool())
	// f : bool → bool → bool, exercises multi-arg Apply flattening.
	f := core.Var("f", core.MakeFun(core.TypeBool(), core.TypeBool(), core.TypeBool()))
	p := makeTestPrinter(x, y, z, f)

	cases := []struct {
		name string
		term core.Term
		want string
	}{
		{
			name: "Eq",
			term: WrapTerm(x).Eq(y).Core(),
			want: "x.Eq(y)",
		},
		{
			name: "And",
			term: WrapTerm(x).And(y).Core(),
			want: "x.And(y)",
		},
		{
			name: "Imply",
			term: WrapTerm(x).Imply(y).Core(),
			want: "x.Imply(y)",
		},
		{
			name: "Not",
			term: Not(x).Core(),
			want: "ext.Not(x)",
		},
		{
			name: "ForAll_single",
			term: ForAll(x)(WrapTerm(x).Eq(x)).Core(),
			want: "ext.ForAll(x)(x.Eq(x))",
		},
		{
			// ∀x.∀y. x = y  must collapse to ForAll(x, y)(...) rather
			// than the right-leaning ForAll(x)(ForAll(y)(...)).
			// The DecomposesFORALL pass walks the binder chain.
			name: "ForAll_multiBinder",
			term: ForAll(x)(ForAll(y)(WrapTerm(x).Eq(y))).Core(),
			want: "ext.ForAll(x, y)(x.Eq(y))",
		},
		{
			// ∀x.∀y.∀z. (x ∧ y) ⇒ z  — three-binder chain plus
			// nested logical structure in the body.
			name: "ForAll_threeBinder",
			term: ForAll(x)(ForAll(y)(ForAll(z)(
				WrapTerm(x).And(y).Imply(z)))).Core(),
			want: "ext.ForAll(x, y, z)(x.And(y).Imply(z))",
		},
		{
			// ∃x.∃y. x = y  — multi-binder Exists.
			name: "Exists_multiBinder",
			term: Exists(x)(Exists(y)(WrapTerm(x).Eq(y))).Core(),
			want: "ext.Exists(x, y)(x.Eq(y))",
		},
		{
			// f(x, y) ≡ App(App(f, x), y)  — must flatten to
			// f.Apply(x, y), not f.Apply(x).Apply(y). Exercises the
			// MatchesApply rewrite at the AppliedTerm branch.
			name: "Apply_multiArg",
			term: WrapTerm(f).Apply(x, y).Core(),
			want: "f.Apply(x, y)",
		},
		{
			// ∀x. ∀y. f(x, y) — combination of multi-binder and
			// multi-arg flattening.
			name: "ForAll_multiBinder_with_multiArgApply",
			term: ForAll(x)(ForAll(y)(
				WrapTerm(f).Apply(x, y))).Core(),
			want: "ext.ForAll(x, y)(f.Apply(x, y))",
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			got := p.PrintTerm(tc.term)
			if got != tc.want {
				t.Errorf("PrintTerm = %q, want %q", got, tc.want)
			}
		})
	}
}

// TestGoPrinter_BareNames verifies that BareNames=true strips the
// `core.` and `ext.` package qualifiers — assuming the surrounding
// scope has aliased the names. Used by reconstruct/emit's package-
// level alias block.
func TestGoPrinter_BareNames(t *testing.T) {
	x := core.Var("x", core.TypeBool())
	y := core.Var("y", core.TypeBool())
	p := makeTestPrinter(x, y)
	p.BareNames = true

	cases := []struct {
		name string
		term core.Term
		want string
	}{
		// Quantifier
		{
			"ForAll",
			ForAll(x)(WrapTerm(x).Eq(y)).Core(),
			"ForAll(x)(x.Eq(y))",
		},
		// Unary
		{
			"Not",
			Not(x).Core(),
			"Not(x)",
		},
		// Inline Var(...) for an unbound var falls through to bare form
		{
			"InlineVar",
			core.Var("z", core.TypeBool()), // not pre-registered
			`Var("z", TypeBool)`,
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			got := p.PrintTerm(tc.term)
			if got != tc.want {
				t.Errorf("PrintTerm = %q, want %q", got, tc.want)
			}
		})
	}

	// Type printer mirrors term mode.
	if got := p.PrintType(core.TypeBool()); got != "TypeBool" {
		t.Errorf("PrintType(bool) = %q, want %q", got, "TypeBool")
	}
	if got := p.PrintType(core.MakeFun(core.TypeBool(), TypeInd)); got != `MakeFun(TypeBool, MakeType("ind"))` {
		t.Errorf("PrintType(fun) = %q, want %q", got, `MakeFun(TypeBool, MakeType("ind"))`)
	}
	if got := p.PrintType(numTypeForTest); got != "NumType" {
		t.Errorf("PrintType(num) = %q, want %q", got, "NumType")
	}
}

// TestGoPrinter_Type exercises the type printer on the basic shapes
// emitted Go will need.
// TestGoPrinter_WrapperlessIdent: a variable whose identifier is no
// *TermWrapper — a typed closure parameter — keeps the identifier where
// a method takes it as a TermLike, and prints as the inline Var where a
// method chain needs its receiver or a quantifier its body.
func TestGoPrinter_WrapperlessIdent(t *testing.T) {
	n := core.Var("n", numTypeForTest)
	f := core.Var("f", core.MakeFun(numTypeForTest, core.TypeBool()))
	p := makeTestPrinter(n, f)
	p.WrapperlessIdent = func(v core.VarTerm) bool { return v.Name() == "f" }

	assert.Equal(t, `ext.Var("f", core.MakeFun(dsl.NumType, core.TypeBool)).Apply(n)`,
		p.PrintTerm(WrapTerm(f).Apply(n).Core()), "an application's head")
	assert.Equal(t, "n.Eq(n)", p.PrintTerm(WrapTerm(n).Eq(n).Core()), "an identifier with the method set")
	g := core.Var("g", core.MakeFun(core.MakeFun(numTypeForTest, core.TypeBool()), core.TypeBool()))
	p = makeTestPrinter(n, f, g)
	p.WrapperlessIdent = func(v core.VarTerm) bool { return v.Name() == "f" }
	assert.Equal(t, "g.Apply(f)", p.PrintTerm(WrapTerm(g).Apply(f).Core()), "an argument")
	assert.Equal(t, `ext.ForAll(n)(ext.Var("f", core.MakeFun(dsl.NumType, core.TypeBool)).Apply(n))`,
		p.PrintTerm(ForAll(n)(WrapTerm(f).Apply(n)).Core()))
}

func TestGoPrinter_Type(t *testing.T) {
	p := &GoTermPrinter{}
	cases := []struct {
		name string
		typ  core.HolType
		want string
	}{
		{"bool", core.TypeBool(), "core.TypeBool"},
		{"ind", TypeInd, `ext.MakeType("ind")`},
		{"num", numTypeForTest, "dsl.NumType"},
		{"varA", core.TypeA(), `core.MakeVarType("A")`},
		{"fun", core.MakeFun(core.TypeBool(), TypeInd),
			`core.MakeFun(core.TypeBool, ext.MakeType("ind"))`},
		{"funCurried", core.MakeFun(core.TypeBool(), core.TypeBool(), TypeInd),
			`core.MakeFun(core.TypeBool, core.MakeFun(core.TypeBool, ext.MakeType("ind")))`},
		{"funNum", core.MakeFun(numTypeForTest, numTypeForTest, core.TypeBool()),
			"core.MakeFun(dsl.NumType, core.MakeFun(dsl.NumType, core.TypeBool))"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			got := p.PrintType(tc.typ)
			if got != tc.want {
				t.Errorf("PrintType = %q, want %q", got, tc.want)
			}
		})
	}
}

// TestGoPrinter_SpecialConstAtInstanceType covers specialConstGoAlias's
// poly path: a polymorphic special (∃!) at a non-generic instance type
// is rebuilt at its exact type via Const(GLOBAL.Meta(), T) — the bare
// WrapTerm(UNIQUE) alias carries only the generic definition type, so
// an eta-contracted occurrence (e.g. `∃!(COND(…))`) emitted through it
// would type-assert in core.Apply at replay. At the generic definition
// type the alias is kept.
func TestGoPrinter_SpecialConstAtInstanceType(t *testing.T) {
	p := &GoTermPrinter{}
	if got, want := p.PrintTerm(UNIQUE), "ext.WrapTerm(ext.UNIQUE)"; got != want {
		t.Errorf("generic UNIQUE: got %q, want %q", got, want)
	}
	instTy := core.MakeFun(core.MakeFun(numTypeForTest, core.TypeBool()), core.TypeBool())
	inst := core.MakeConstTerm(UNIQUE.Meta(), instTy)
	got := p.PrintTerm(inst)
	want := "ext.Const(ext.UNIQUE.Meta(), " +
		"core.MakeFun(core.MakeFun(dsl.NumType, core.TypeBool), core.TypeBool))"
	if got != want {
		t.Errorf("instance UNIQUE: got %q, want %q", got, want)
	}
}

// TestGoPrinter_SpecialConstMonoGuard: a const NAMED like a monomorphic
// special (¬) but at a different type cannot take the fixed-type alias.
// Under StrictConsts that is an emit-time panic — the alias rendering
// would silently lose the instance type and fail deep in replay.
func TestGoPrinter_SpecialConstMonoGuard(t *testing.T) {
	wrongTy := core.MakeFun(core.TypeBool(), core.TypeBool(), core.TypeBool())
	bad := core.MakeConstTerm(core.MakeConstMeta("¬", wrongTy), wrongTy)
	p := &GoTermPrinter{StrictConsts: true}
	defer func() {
		if recover() == nil {
			t.Fatal("StrictConsts printer did not panic on ¬ at non-alias type")
		}
	}()
	p.PrintTerm(bad)
}

// testAbbrevCleanup snapshots and restores the global registry so the
// registrations here cannot leak into other tests of the package.
func testAbbrevCleanup(t *testing.T) {
	displayAbbrevMu.Lock()
	saved := displayAbbrevs
	displayAbbrevMu.Unlock()
	t.Cleanup(func() {
		displayAbbrevMu.Lock()
		displayAbbrevs = saved
		displayAbbrevMu.Unlock()
	})
}

// The test concept: bounded(P, M) := ∃x:num. P(x) ∧ x ≤ M — the same
// shape class as the corpus's attainability predicates (a param applied
// to the pattern's own binder, plus a plain param).
func registerBoundedAbbrev(t *testing.T) {
	t.Helper()
	numBool := core.MakeFun(NumType, core.TypeBool())
	P := Var("P", numBool)
	M := Var("M", NumType)
	x := Var("x", NumType)
	le := WrapTerm(core.MakeConstMeta("<=", core.MakeFun(NumType, NumType, core.TypeBool())).Term())
	pattern := Exists(x)(P.Apply(x).And(le.Apply(x, M)))
	RegisterDisplayAbbrev("bounded",
		[]VarTerm{P.Core().(VarTerm), M.Core().(VarTerm)}, pattern.Core())
}

func TestDisplayAbbrev_FoldsInDisplayProfilesOnly(t *testing.T) {
	testAbbrevCleanup(t)
	registerBoundedAbbrev(t)

	numBool := core.MakeFun(NumType, core.TypeBool())
	P0 := Var("P_0", numBool)
	le := WrapTerm(core.MakeConstMeta("<=", core.MakeFun(NumType, NumType, core.TypeBool())).Term())
	// Actual instance with a DIFFERENT binder name (α-variant) and a
	// compound bound term: ∃y. P₀(y) ∧ y ≤ suc(z).
	y, z := Var("y", NumType), Var("z", NumType)
	suc := WrapTerm(core.MakeConstMeta("suc", core.MakeFun(NumType, NumType)).Term())
	actual := Exists(y)(P0.Apply(y).And(le.Apply(y, suc.Apply(z)))).Core()

	display := PrintTerm(actual)
	assert.Equal(t, "⟦bounded(P₀, suc(z))⟧", display)

	// The poly-binder inspect profile folds too.
	assert.Contains(t, FormatTermWithPolyBinders(actual, false), "⟦bounded(")

	// Parser round-trip profiles stay registry-blind.
	forParser := FormatTermForParser(actual)
	assert.NotContains(t, forParser, "⟦")
	assert.Contains(t, forParser, "∃y:num")
	nameFaithful := FormatTermForParserInConflictsNameFaithful(actual, nil)
	assert.NotContains(t, nameFaithful, "⟦")
}

func TestDisplayAbbrev_FoldNestsInsideLargerTerms(t *testing.T) {
	testAbbrevCleanup(t)
	registerBoundedAbbrev(t)

	numBool := core.MakeFun(NumType, core.TypeBool())
	P0 := Var("P_0", numBool)
	le := WrapTerm(core.MakeConstMeta("<=", core.MakeFun(NumType, NumType, core.TypeBool())).Term())
	x, m := Var("x", NumType), Var("m", NumType)
	inner := Exists(x)(P0.Apply(x).And(le.Apply(x, m)))
	whole := ForAll(m)(inner).Core()

	assert.Equal(t, "∀m.⟦bounded(P₀, m)⟧", PrintTerm(whole))
}

func TestDisplayAbbrev_EscapeAndMismatchDecline(t *testing.T) {
	testAbbrevCleanup(t)
	registerBoundedAbbrev(t)

	numBool := core.MakeFun(NumType, core.TypeBool())
	P0 := Var("P_0", numBool)
	le := WrapTerm(core.MakeConstMeta("<=", core.MakeFun(NumType, NumType, core.TypeBool())).Term())

	// Escape: the bound M-position term mentions the ∃-binder itself
	// (∃x. P₀(x) ∧ x ≤ suc(x)) — capturing suc(x) would dangle. No fold.
	x := Var("x", NumType)
	suc := WrapTerm(core.MakeConstMeta("suc", core.MakeFun(NumType, NumType)).Term())
	escaping := Exists(x)(P0.Apply(x).And(le.Apply(x, suc.Apply(x)))).Core()
	require.NotContains(t, PrintTerm(escaping), "⟦")

	// Shape mismatch: ∨ instead of ∧. No fold.
	other := Exists(x)(P0.Apply(x).Or(le.Apply(x, Var("m", NumType)))).Core()
	require.NotContains(t, PrintTerm(other), "⟦")
}

// A fold is single when its opening ⟦ closes at the end; the intervals
// share the glyphs and mix them, so a union of two intervals is not.
func TestIsSingleDisplayFold(t *testing.T) {
	for s, want := range map[string]bool{
		"⟦bounded(P₀, m)⟧": true,
		"⟦a(⟦b(x)⟧)⟧":      true,
		"⟦a(⟦c, d⟭)⟧":      true,
		"⟦a(x)⟧ ∧ ⟦b(y)⟧":  false,
		"⟦a, b⟭ ∪ ⟬c, d⟧":  false,
		"⟦a, b⟭ ⊆ ⟦c, d⟧":  false,
		"bounded(P₀, m)":   false,
	} {
		assert.Equal(t, want, isSingleDisplayFold(s), s)
	}
}
