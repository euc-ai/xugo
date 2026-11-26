package dsl

import (
	"sort"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// The implicit-argument contract (implicit.go), pinned on a toy
// vector vocabulary: `vec_add` reads `add`, `vec` reads `zero`, `dot`
// reads `add` and `mul`.

func implicitTestScope(t *testing.T) *ParseScope {
	t.Helper()
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatalf("type %q: %v", text, err)
		}
		return ty
	}
	metas := map[string]core.ConstTermMeta{
		"vec_add":    core.MakeConstMeta("vec_add", typ("(A → A → A) → (num → A) → (num → A) → num → A")),
		"vec":        core.MakeConstMeta("vec", typ("A → num → (num → A) → bool")),
		"dot":        core.MakeConstMeta("dot", typ("(A → A → A) → (A → A → A) → num → (num → A) → (num → A) → A")),
		"real_add":   core.MakeConstMeta("real_add", typ("real → real → real")),
		"real_mul":   core.MakeConstMeta("real_mul", typ("real → real → real")),
		"int_add":    core.MakeConstMeta("int_add", typ("int → int → int")),
		"int_mul":    core.MakeConstMeta("int_mul", typ("int → int → int")),
		"vec_zero":   core.MakeConstMeta("vec_zero", typ("A → num → A")),
		"set_op":     core.MakeConstMeta("set_op", typ("(A → A → A) → (A → bool) → (A → bool) → A → bool")),
		"pw_scale":   core.MakeConstMeta("pw_scale", typ("(A → C → C) → A → (D → C) → D → C")),
		"with_scale": core.MakeConstMeta("with_scale", typ("(A → B → B) → (A → bool) → B → B")),
		"vec_scalar_mul": core.MakeConstMeta("vec_scalar_mul",
			typ("(A → A → A) → A → (num → A) → num → A")),
		// A predicate over a family, reading the family implicitly: the
		// topology chapters' shape.
		"closed_in": core.MakeConstMeta("closed_in", typ("((A → bool) → bool) → (A → bool) → bool")),
		// Two SET-valued constants over a family, and a family at a fixed
		// point type: the shapes a second space is spelled at.
		"subtopology":   core.MakeConstMeta("subtopology", typ("((A → bool) → bool) → (A → bool) → (A → bool) → bool")),
		"interior":      core.MakeConstMeta("interior", typ("((A → bool) → bool) → (A → bool) → A → bool")),
		"real_topology": core.MakeConstMeta("real_topology", typ("(real → bool) → bool")),
		// A structure predicate over a family with the family implicit
		// (a cover of T), and a definition over a cover.
		"zz_cover": core.MakeConstMeta("zz_cover", typ("((A → bool) → bool) → ((A → bool) → bool) → bool")),
		"zz_fine":  core.MakeConstMeta("zz_fine", typ("((A → bool) → bool) → ((A → bool) → bool) → bool")),
	}
	return &ParseScope{
		ConstMetas: metas,
		Syntax: testSyntax{
			"vec_add": {Implicit: []string{"add"}}, "vec": {Implicit: []string{"zero"}},
			"dot": {Implicit: []string{"add", "mul"}}, "vec_zero": {Implicit: []string{"zero"}}, "set_op": {Implicit: []string{"add"}}, "pw_scale": {Implicit: []string{"mul"}}, "with_scale": {Implicit: []string{"smul"}},
			"vec_scalar_mul": {Implicit: []string{"mul"}},
			"closed_in":      {Implicit: []string{"T"}},
			"subtopology":    {Implicit: []string{"T"}}, "interior": {Implicit: []string{"T"}},
			"is_topology": {StructurePredicate: true}, "ring": {StructurePredicate: true},
			"zz_cover": {Implicit: []string{"T"}, StructurePredicate: true}, "zz_fine": {Implicit: []string{"T"}, StructurePredicate: true},
		},
		StrictResolution: true,
	}
}

func parseImplicit(t *testing.T, scope *ParseScope, text string) core.Prop {
	t.Helper()
	res := ParsePropTextInScope(text, scope)
	if len(res.Errors) > 0 {
		t.Fatalf("%q: %s", text, res.Errors[0].Message)
	}
	return res.Prop
}

func assertSameProp(t *testing.T, scope *ParseScope, short, explicit string) {
	t.Helper()
	a, b := parseImplicit(t, scope, short), parseImplicit(t, scope, explicit)
	if a.AlphaKey() != b.AlphaKey() {
		t.Fatalf("short and explicit spellings differ:\n  %s\n  %s", prop.PrintProp(a), prop.PrintProp(b))
	}
}

func TestImplicitArgs_BoundName(t *testing.T) {
	scope := implicitTestScope(t)
	prefix := "∀add:(A → A → A). ∀u v:(num → A). "
	assertSameProp(t, scope,
		prefix+"vec_add(u, v) = vec_add(v, u)",
		prefix+"vec_add(add, u, v) = vec_add(add, v, u)")
	// A bare head is the constant at its components.
	assertSameProp(t, scope,
		"∀add:(A → A → A). vec_add = vec_add",
		"∀add:(A → A → A). vec_add(add) = vec_add(add)")
	// Two implicit binders, and the explicit spelling is idempotent.
	prefix2 := "∀add mul:(A → A → A). ∀n:num. ∀u v:(num → A). "
	assertSameProp(t, scope,
		prefix2+"dot(n, u, v) = dot(n, v, u)",
		prefix2+"dot(add, mul, n, u, v) = dot(add, mul, n, v, u)")
	// A membership under the binder.
	assertSameProp(t, scope,
		"∀zero:A. ∀n:num. ∀u:(num → A). vec(n, u) ⇒ vec(n, u)",
		"∀zero:A. ∀n:num. ∀u:(num → A). vec(zero, n, u) ⇒ vec(zero, n, u)")
}

func TestImplicitArgs_SecondSpace(t *testing.T) {
	// A predicate reading its structure implicitly, applied at a SECOND
	// structure of the family's type under a binder for the first: a
	// statement about a map between two spaces. The short reading would
	// put an argument past the predicate's spine, whose result is bool
	// and takes nothing more, so the application is read as the prefix
	// it spells; under the same binder the short form still completes.
	scope := implicitTestScope(t)
	prefix := "∀T:((A → bool) → bool). ∀S:((B → bool) → bool). ∀c:(B → bool). "
	explicit := parseImplicit(t, scope, prefix+"closed_in(S, c) ⇒ closed_in(S, c)")
	if s := prop.PrintProp(explicit); strings.Contains(s, "closed_in(T") {
		t.Fatalf("second space completed with the bound family: %s", s)
	}
	assertSameProp(t, scope,
		"∀T:((A → bool) → bool). ∀c:(A → bool). closed_in(c) ⇒ closed_in(T, c)",
		"∀T:((A → bool) → bool). ∀c:(A → bool). closed_in(T, c) ⇒ closed_in(T, c)")
}

func TestImplicitArgs_SetValuedAtSecondSpace(t *testing.T) {
	// A SET-valued constant reading its family implicitly, applied at a
	// second family of another point type under a binder for the first:
	// `subtopology(real_topology, s)` under `T : set(set(A))`. The short
	// reading puts `real_topology` at the slot `set(A)`, which it fits on
	// its own by taking A to be `real → bool` — and the result, a set of
	// sets, has slots to spare for the written arguments, so neither
	// arity nor any one slot refutes it. What refutes it is the prefix
	// itself: T's own type pins A, and under that letter real_topology
	// no longer fits. The two readings are checked as one application
	// each, so the explicit spelling is kept; under the same binder the
	// short form still completes.
	scope := implicitTestScope(t)
	prefix := "∀T:((A → bool) → bool). ∀s:(real → bool). ∀F:((real → bool) → bool). "
	explicit := parseImplicit(t, scope, prefix+"subtopology(real_topology, s) = F ⇒ F = subtopology(real_topology, s)")
	if text := prop.PrintProp(explicit); strings.Contains(text, "subtopology(T") {
		t.Fatalf("second space completed with the bound family: %s", text)
	}
	assertSameProp(t, scope,
		"∀T:((A → bool) → bool). ∀s:(A → bool). subtopology(s) = subtopology(T, s)",
		"∀T:((A → bool) → bool). ∀s:(A → bool). subtopology(T, s) = subtopology(T, s)")
}

func TestImplicitArgs_SetValuedAtCompoundSpace(t *testing.T) {
	// A SET-valued constant applied at a space BUILT from the bound one:
	// `subtopology(subtopology(T, s), t)` under `T : set(set(A))`. The
	// first argument is an application of a polymorphic constant, whose
	// result the constant's own type does not fix; read off its
	// arguments it is a `set(set(A))`, which contradicts the short
	// reading's slot `set(A)` — so the explicit spelling is kept. Left
	// unknown, nothing refuted the short reading (the result of a
	// set-valued constant has a slot to spare for `t`) and T was put in
	// front of a full application. The inner short form still completes.
	scope := implicitTestScope(t)
	prefix := "∀T:((A → bool) → bool). ∀s t:(A → bool). "
	nested := parseImplicit(t, scope, prefix+"subtopology(subtopology(T, s), t) = subtopology(T, s ∩ t)")
	if text := prop.PrintProp(nested); strings.Contains(text, "subtopology(T, subtopology") {
		t.Fatalf("compound space completed with the bound family: %s", text)
	}
	assertSameProp(t, scope,
		prefix+"subtopology(subtopology(s), t) = subtopology(s ∩ t)",
		prefix+"subtopology(subtopology(T, s), t) = subtopology(T, s ∩ t)")
	assertSameProp(t, scope,
		prefix+"interior(subtopology(s), t) = interior(t) ∩ s",
		prefix+"interior(subtopology(T, s), t) = interior(T, t) ∩ s")
}

func TestImplicitArgs_SpelledComponentUnderAnotherName(t *testing.T) {
	// The family spelled under a name the scope does not bind as the
	// component — a session's Skolemized `T_0` beside the law's `T` —
	// with the set-valued constant's written arguments: `interior(T_0, s_0)`
	// where `T` is declared too. Slot by slot the short reading fits
	// (T_0 at `set(A)` with A a set, s_0 at the result's A likewise); read
	// as one application under T's own type it does not, so the spelled
	// arguments stand.
	scope := implicitTestScope(t)
	fam, _ := ParseTypeText("(A → bool) → bool")
	set, _ := ParseTypeText("A → bool")
	scope.Vars = map[string]core.HolType{"T": fam, "T_0": fam, "s_0": set}
	explicit := parseImplicit(t, scope, "interior(T_0, s_0) = s_0")
	if text := prop.PrintProp(explicit); strings.Contains(text, "interior(T,") {
		t.Fatalf("spelled component completed again: %s", text)
	}
	assertSameProp(t, scope, "interior(s_0) = s_0", "interior(T, s_0) = s_0")
}

func TestChapterSpelling_ElidesAVariableComponentOnlyUnderItsStructure(t *testing.T) {
	// The chapter's convention, served: a statement carrying no structure
	// over T spells `closed_in(T, c)` and is served so; under
	// `is_topology(T)` — in the body, or as a hypothesis before ⊢ — the
	// same application is served short. A component bound to an instance
	// term is not a variable and is elided regardless (the vector tests).
	scope := implicitTestScope(t)
	spell := func(text string) string {
		out, err := ChapterSpelling(text, scope.Syntax, nil)
		if err != nil {
			t.Fatalf("ChapterSpelling(%q): %v", text, err)
		}
		return out
	}
	plain := spell("∀T:((A → bool) → bool). ∀c:(A → bool). closed_in(T, c) ⇒ closed_in(T, c)")
	if !strings.Contains(plain, "closed_in(T, c)") || strings.Contains(plain, "closed_in(c)") {
		t.Fatalf("a theorem with no structure over T must keep T spelled: %q", plain)
	}
	law := spell("∀T:((A → bool) → bool). is_topology(T) ⇒ ∀c:(A → bool). closed_in(T, c) ⇒ closed_in(T, c)")
	if !strings.Contains(law, "closed_in(c)") || strings.Contains(law, "closed_in(T,") {
		t.Fatalf("under is_topology(T) the component is elided: %q", law)
	}
	goal := spell("T:((A → bool) → bool), c:(A → bool), is_topology(T) ⊢ closed_in(T, c)")
	if !strings.Contains(goal, "⊢ closed_in(c)") {
		t.Fatalf("a structure hypothesis before ⊢ licenses the elision: %q", goal)
	}
	bare := spell("T:((A → bool) → bool), c:(A → bool) ⊢ closed_in(T, c)")
	if !strings.Contains(bare, "⊢ closed_in(T, c)") {
		t.Fatalf("no structure anywhere: the component stays spelled: %q", bare)
	}
}

// A definition's equation states its structure facts and keeps their
// components (astApp.stated): the definiendum zz_fine(T, U) and the body
// conjunct zz_cover(T, U) spell T, which the elision drops from the uses
// in the body — closed_in under the guard — and from every application
// of a theorem.
func TestChapterSpelling_DefinitionStatementsKeepTheirComponents(t *testing.T) {
	scope := implicitTestScope(t)
	spell := func(text string) string {
		out, err := ChapterSpelling(text, scope.Syntax, nil)
		if err != nil {
			t.Fatalf("ChapterSpelling(%q): %v", text, err)
		}
		assertSameProp(t, scope, out, text)
		return out
	}
	binders := "∀T:((A → bool) → bool). ∀U:((A → bool) → bool). "
	definition := spell(binders + "zz_fine(T, U) ⇔ zz_cover(T, U) ∧ (∀c:(A → bool). closed_in(T, c) ⇒ closed_in(T, c))")
	if !strings.Contains(definition, "zz_fine(T, U) ⇔ zz_cover(T, U) ∧") {
		t.Fatalf("the definiendum and the stated cover keep T: %q", definition)
	}
	if !strings.Contains(definition, "closed_in(c) ⇒ closed_in(c)") {
		t.Fatalf("a use in the body is elided as anywhere: %q", definition)
	}
	theorem := spell(binders + "zz_cover(T, U) ⇒ zz_fine(T, U)")
	if !strings.Contains(theorem, "zz_cover(U) ⇒ zz_fine(U)") {
		t.Fatalf("a theorem's applications are elided under the structure: %q", theorem)
	}
	// An iff law at the root is no definition: its left side is not the
	// constant applied to the leading binders, and nothing is stated.
	law := spell(binders + "∀c:(A → bool). closed_in(T, c) ⇔ zz_cover(T, U)")
	if !strings.Contains(law, "closed_in(c) ⇔ zz_cover(U)") {
		t.Fatalf("an iff law's sides are elided under the structure: %q", law)
	}
}

func TestImplicitArgs_CompletedObserver(t *testing.T) {
	// The observer hears every argument the pass supplies — and nothing
	// for an argument the text spells — and the parse is unchanged.
	scope := implicitTestScope(t)
	type heard struct {
		c, n     string
		variable bool
	}
	var got []heard
	scope.ImplicitCompleted = func(c, n string, variable bool) { got = append(got, heard{c, n, variable}) }
	short := parseImplicit(t, scope, "∀T:((A → bool) → bool). ∀c:(A → bool). closed_in(c) ⇒ closed_in(T, c)")
	if len(got) != 1 || got[0] != (heard{"closed_in", "T", true}) {
		t.Fatalf("observer heard %v, want one completion of closed_in's T to a variable", got)
	}
	scope.ImplicitCompleted = nil
	plain := parseImplicit(t, scope, "∀T:((A → bool) → bool). ∀c:(A → bool). closed_in(c) ⇒ closed_in(T, c)")
	if short.AlphaKey() != plain.AlphaKey() {
		t.Fatalf("the observer changed the parse")
	}
}

func TestImplicitArgs_DeclaredName(t *testing.T) {
	scope := implicitTestScope(t)
	add, _ := ParseTypeText("A → A → A")
	vec, _ := ParseTypeText("num → A")
	scope.Vars = map[string]core.HolType{"add": add, "u": vec, "v": vec}
	assertSameProp(t, scope, "vec_add(u, v) = vec_add(v, u)", "vec_add(add, u, v) = vec_add(add, v, u)")
	// The term path completes the same way.
	short := ParseTermTextInScope("vec_add(u, v)", nil, scope, nil)
	long := ParseTermTextInScope("vec_add(add, u, v)", nil, scope, nil)
	if len(short.Errors) > 0 || len(long.Errors) > 0 {
		t.Fatalf("term parse: %v / %v", short.Errors, long.Errors)
	}
	if !short.Term.Equals(long.Term) {
		t.Fatalf("term completion differs: %s vs %s", ext.PrintTerm(short.Term), ext.PrintTerm(long.Term))
	}
}

func TestImplicitArgs_InstanceBindings(t *testing.T) {
	scope := implicitTestScope(t)
	realVec, _ := ParseTypeText("num → real")
	scope.Vars = map[string]core.HolType{"u": realVec, "v": realVec, "n": NumType}
	realAdd := ParseTermTextInScope("real_add", nil, scope, nil)
	zero := ParseTermTextInScope("&0", nil, scope, nil)
	if len(realAdd.Errors) > 0 || len(zero.Errors) > 0 {
		t.Fatalf("binding terms: %v / %v", realAdd.Errors, zero.Errors)
	}
	scope.ImplicitBindings = map[string]core.Term{"add": realAdd.Term, "zero": zero.Term}
	// A family at ℝ declares its coercion domain, as the real chapters do.
	scope.CoerceDomain = RealType

	assertSameProp(t, scope, "vec_add(u, v) = vec_add(v, u)", "vec_add(real_add, u, v) = vec_add(real_add, v, u)")
	// Both spellings of the instance's zero count as explicit.
	assertSameProp(t, scope, "vec(n, u) ⇒ vec(n, u)", "vec(&0, n, u) ⇒ vec(real_of_num(0), n, u)")
	// The completed term IS the binding's term, not a re-parse of it.
	p := parseImplicit(t, scope, "vec(n, u)")
	found := false
	for s := range ext.SubTerms(p.Conclusion()) {
		if s == zero.Term {
			found = true
		}
	}
	if !found {
		t.Fatalf("expected the instance zero, pointer-identical, in the completed statement: %s", prop.PrintProp(p))
	}
}

func TestImplicitArgs_Refusals(t *testing.T) {
	scope := implicitTestScope(t)
	vec, _ := ParseTypeText("num → A")
	scope.Vars = map[string]core.HolType{"u": vec, "v": vec}
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
	// Nothing binds `add`: nothing is completed, so the short form is the
	// ill-typed application it spells, and the explicit form parses.
	expectErr("vec_add(u, v) = vec_add(v, u)", "does not match domain")
	scope.Vars["add"] = nil
	delete(scope.Vars, "add")
	addTy, _ := ParseTypeText("A → A → A")
	scope.Vars["realish_add"] = addTy
	parseImplicit(t, scope, "vec_add(realish_add, u, v) = vec_add(realish_add, v, u)")
	// Some but not all bound: the short form names the missing binder.
	expectErr("∀add:(A → A → A). ∀n:num. dot(n, u, v) = dot(n, v, u)", "implicit argument mul is not in scope")
	// A prefix spelled in part.
	expectErr("∀add mul:(A → A → A). ∀n:num. dot(add, n, u, v) = dot(add, n, v, u)", "spelled in part")
}

func TestImplicitArgs_MintedNameOfABoundComponent(t *testing.T) {
	// A session prints a goal under a law's Skolemized binders in the
	// minted names — `delta(zero₀, one₀, x)`, the variables zero_0 and
	// one_0 — while the block spells them `zero` and `one` (ResidentNames). The print must
	// read back: the minted names are the bound components, so the
	// application is the explicit one, as `delta(zero, one, x)` is. No
	// argument's type tells the two readings apart here (the slots after
	// the prefix are the constant's own letters), so without the surface
	// names the short reading completed the components again and the
	// application ran past the constant's arity. A prefix spelled in part
	// is refused as before.
	scope := implicitTestScope(t)
	scope.ConstMetas["delta"] = core.MakeConstMeta("delta",
		mustType(t, "A → A → D → D → A"))
	scope.Syntax.(testSyntax)["delta"] = &ConstSyntax{Implicit: []string{"zero", "one"}}
	elem, pt := mustType(t, "A"), mustType(t, "D")
	scope.Vars = map[string]core.HolType{"zero": elem, "one": elem, "zero_0": elem, "one_0": elem, "x": pt, "y": pt}
	scope.ResidentNames = map[string]string{"zero_0": "zero", "one_0": "one"}
	var heard []string
	scope.ImplicitCompleted = func(c, n string, _ bool) { heard = append(heard, c+"."+n) }
	parseImplicit(t, scope, "delta(zero₀, one₀, x) = delta(zero₀, one₀, y)")
	parseImplicit(t, scope, "delta(zero₀, one₀, x, y) = zero₀")
	if len(heard) != 0 {
		t.Fatalf("the minted components were completed again: %v", heard)
	}
	parseImplicit(t, scope, "delta(x) = delta(zero, one, y)")
	res := ParsePropTextInScope("delta(zero₀, x) = delta(y)", scope)
	if len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "spelled in part") {
		t.Fatalf("a prefix spelled in part: %v", res.Errors)
	}
}

func TestImplicitArgs_PrefixCoincidingWithBoundNames(t *testing.T) {
	// A structure over two carriers whose components include a
	// sub-structure's: `mod_on(add, zero, add', S)` reads the scalars'
	// `add`, `zero` and the vectors' `add'`. Its instance is stated
	// under the scalars' own binders, so the leading arguments spell the
	// bound names and the next one is the instance's vector operation —
	// the explicit application, read by type, not a prefix spelled in
	// part. The same holds under a scope that binds all three, at a
	// second vector operation.
	scope := implicitTestScope(t)
	metas := map[string]core.ConstTermMeta{}
	for k, v := range scope.ConstMetas {
		metas[k] = v
	}
	modTy, err := ParseTypeText("(A → A → A) → A → (B → B → B) → (B → bool) → bool")
	if err != nil {
		t.Fatal(err)
	}
	metas["mod_on"] = core.MakeConstMeta("mod_on", modTy)
	scope.ConstMetas = metas
	syntax := testSyntax{}
	for k, v := range scope.Syntax.(testSyntax) {
		syntax[k] = v
	}
	syntax["mod_on"] = &ConstSyntax{Implicit: []string{"add", "zero", "add'"}, StructurePredicate: true}
	scope.Syntax = syntax

	someBound := "∀add:(A → A → A). ∀zero:A. ∀w:(B → B → B). ∀S:(B → bool). mod_on(add, zero, w, S) ⇒ mod_on(add, zero, w, S)"
	if s := prop.PrintProp(parseImplicit(t, scope, someBound)); !strings.Contains(s, "mod_on(add, zero, w, S)") {
		t.Fatalf("the explicit application was not read as written: %s", s)
	}
	allBound := "∀add:(A → A → A). ∀zero:A. ∀add' w:(B → B → B). ∀S:(B → bool). " +
		"mod_on(S) ⇒ mod_on(add, zero, w, S) ⇒ mod_on(add, zero, add', S)"
	if s := prop.PrintProp(parseImplicit(t, scope, allBound)); !strings.Contains(s, "mod_on(add, zero, w, S)") {
		t.Fatalf("a second vector operation was completed with the bound one: %s", s)
	}
}

func TestImplicitArgs_Shadowing(t *testing.T) {
	scope := implicitTestScope(t)
	// A quantifier-bound `vec_add` is a variable, not the constant.
	p := parseImplicit(t, scope, "∀vec_add:(num → num). vec_add(1) = vec_add(1)")
	if strings.Contains(prop.PrintProp(p), "add,") {
		t.Fatalf("a bound name must not be completed: %s", prop.PrintProp(p))
	}
}

// testSyntax is a SyntaxTable over a map, for the DSL's own tests.
type testSyntax map[string]*ConstSyntax

func (t testSyntax) ConstSyntax(name string) *ConstSyntax { return t[name] }

func (t testSyntax) StructSyntax(name string) *StructSyntax   { return nil }
func (t testSyntax) ConstMeta(name string) core.ConstTermMeta { return core.ConstTermMeta{} }
func (t testSyntax) OutfixConsts(open, close string) []string {
	var names []string
	for name, s := range t {
		if s.Outfix != nil && s.Outfix.Open == open && s.Outfix.Close == close {
			names = append(names, name)
		}
	}
	sort.Strings(names)
	return names
}
func (t testSyntax) OperatorConsts(symbol string, arity int) []string {
	var names []string
	for name, s := range t {
		if s.Operator != nil && s.Operator.Symbol == symbol && s.Operator.Arity() == arity {
			names = append(names, name)
		}
	}
	sort.Strings(names)
	return names
}
func (t testSyntax) BigOpConst(symbol string, carrier core.HolType) string {
	for name, s := range t {
		if s.BigOp != nil && s.BigOp.Symbol == symbol && s.BigOp.Carrier.Equals(carrier) {
			return name
		}
	}
	return ""
}
func (t testSyntax) TupleNames() []string {
	var names []string
	for name, s := range t {
		if s.Tuple != nil {
			names = append(names, name)
		}
	}
	sort.Strings(names)
	return names
}
func (t testSyntax) CoercionConst(into core.HolType) string {
	for name, s := range t {
		if s.Coercion != nil && s.Coercion.Into.Equals(into) {
			return name
		}
	}
	return ""
}
func (t testSyntax) OverloadConsts(word string) []string {
	var out []string
	for name, s := range t {
		if s.Overload != nil && s.Overload.Word == word {
			out = append(out, name)
		}
	}
	sort.Strings(out)
	return out
}

func TestElideImplicitArgs(t *testing.T) {
	scope := implicitTestScope(t)
	// A statement carrying no structure over `add` spells it, and is
	// served as it spells it (the constitution's VecMono case).
	plain, err := ChapterSpelling(
		"∀add:(A → A → A). ∀u v:(num → A). vec_add(add, u, v) = vec_add(add, v, u)",
		scope.Syntax, nil)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(plain, "vec_add(add, u, v)") {
		t.Fatalf("no structure over add: the component stays spelled: %q", plain)
	}
	// Under a structure over `add` the component is elided.
	law := "∀add:(A → A → A). ring(add) ⇒ ∀u v:(num → A). vec_add(add, u, v) = vec_add(add, v, u)"
	elided, err := ChapterSpelling(law, scope.Syntax, nil)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(elided, "vec_add(u, v)") || strings.Contains(elided, "vec_add(add") {
		t.Fatalf("elision: %q", elided)
	}
	// The elided text parses back to the same statement.
	ringT, _ := ParseTypeText("(A → A → A) → bool")
	scope.ConstMetas["ring"] = core.MakeConstMeta("ring", ringT)
	assertSameProp(t, scope, elided, law)

	// A bare head, and the instance spelling under bindings.
	realVec, _ := ParseTypeText("num → real")
	scope.Vars = map[string]core.HolType{"u": realVec, "v": realVec, "n": NumType}
	realAdd := ParseTermTextInScope("real_add", nil, scope, nil)
	zero := ParseTermTextInScope("&0", nil, scope, nil)
	scope.ImplicitBindings = map[string]core.Term{"add": realAdd.Term, "zero": zero.Term}
	elided, err = ChapterSpelling(
		"u:(num → real), v:(num → real), n:num ⊢ vec(&0, n, vec_add(real_add, u, v)) ⇒ vec_add(real_add) = vec_add(real_add)",
		scope.Syntax, scope.ImplicitBindings)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(elided, "vec(n, vec_add(u, v))") || !strings.Contains(elided, "vec_add = vec_add") {
		t.Fatalf("elision under bindings: %q", elided)
	}
	// A name the text does not bind is left explicit.
	kept, err := ChapterSpelling("∀u v:(num → A). vec_add(add, u, v) = vec_add(add, v, u)",
		scope.Syntax, nil)
	if err != nil || !strings.Contains(kept, "vec_add(add, u, v)") {
		t.Fatalf("an unbound component must stay explicit: %q (%v)", kept, err)
	}
	// Nothing to elide: the text comes back as it was.
	same, err := ChapterSpelling("∀x:num. x = x", scope.Syntax, nil)
	if err != nil || same != "∀x:num. x = x" {
		t.Fatalf("no-op elision: %q (%v)", same, err)
	}
}

func TestImplicitArgs_OtherInstance(t *testing.T) {
	// A chapter at one instance stating a term of another — ℤⁿ's chapter
	// stating the form of a real image. The bound instance's components
	// complete the short forms; another instance's, spelled in full, are
	// read as the prefix they are, by the leading argument's type.
	scope := implicitTestScope(t)
	intVec, _ := ParseTypeText("num → int")
	realVec, _ := ParseTypeText("num → real")
	scope.Vars = map[string]core.HolType{"u": intVec, "v": intVec, "x": realVec, "y": realVec, "n": NumType}
	scope.CoerceDomain = IntType
	intAdd := ParseTermTextInScope("int_add", nil, scope, nil)
	intMul := ParseTermTextInScope("int_mul", nil, scope, nil)
	intZero := ParseTermTextInScope("&0", nil, scope, nil)
	if len(intAdd.Errors) > 0 || len(intMul.Errors) > 0 || len(intZero.Errors) > 0 {
		t.Fatalf("binding terms: %v / %v / %v", intAdd.Errors, intMul.Errors, intZero.Errors)
	}
	scope.ImplicitBindings = map[string]core.Term{"add": intAdd.Term, "mul": intMul.Term, "zero": intZero.Term}

	assertSameProp(t, scope, "vec_add(u, v) = vec_add(v, u)", "vec_add(int_add, u, v) = vec_add(int_add, v, u)")
	// real_add fits `add` and cannot be a vector; a real zero cannot be a
	// dimension or an index: each is read as the component it spells.
	for _, text := range []string{
		"vec_add(real_add, x, y) = vec_add(real_add, y, x)",
		"vec(real_of_num(0), n, x) ⇒ vec(real_of_num(0), n, x)",
		"vec_zero(real_of_num(0)) = x",
		"vec_scalar_mul(real_mul, real_of_num(2), x) = x",
	} {
		p := parseImplicit(t, scope, text)
		if s := prop.PrintProp(p); strings.Contains(s, "int_") {
			t.Fatalf("%q: completed with the bound instance: %s", text, s)
		}
	}
	// A coercion is a real or an int, so `&0` in a real vector's slot is a
	// component too — the spelling the printers emit for a zero. Which
	// numeric type the coercion then takes is the scope's coercion
	// domain's business, not the completion's: at the real domain it is
	// the real zero.
	realDomain := *scope
	realDomain.CoerceDomain = RealType
	assertSameProp(t, &realDomain, "vec(&0, n, x) ⇒ vec(&0, n, x)", "vec(real_of_num(0), n, x) ⇒ vec(real_of_num(0), n, x)")
	// Where the type decides nothing the bound instance stands: a numeral
	// fits the component slot and the index alike, so `vec_zero(0)` is the
	// instance's zero vector at index 0; a coerced scalar is never an
	// operation, so `vec_scalar_mul(&2, u)` is the short form it looks like.
	assertSameProp(t, scope, "vec_zero(0) = u(0)", "vec_zero(&0, 0) = u(0)")
	assertSameProp(t, scope, "vec_scalar_mul(&2, u) = u", "vec_scalar_mul(int_mul, &2, u) = u")
	// An annotated binder of a vector type is no component either: a short
	// form over-applied at a carrier of rows stays the short form.
	assertSameProp(t, scope,
		"∀add:((num → A) → (num → A) → (num → A)). ∀P Q:(num → num → A). vec_add(P, Q, 0, 0) = vec_add(Q, P, 0, 0)",
		"∀add:((num → A) → (num → A) → (num → A)). ∀P Q:(num → num → A). vec_add(add, P, Q, 0, 0) = vec_add(add, Q, P, 0, 0)")
}

func TestImplicitArgs_AnnotatedHeadFixesItsLetters(t *testing.T) {
	// A head's instance annotation `⟨A:τ⟩` fixes the letters it names,
	// so a reading under it is read at that instance: `set_op⟨A:A⟩`
	// under a bound `add` is the operation on sets of A, and the
	// operation on sets of sets, `set_op⟨A:A → bool⟩(set_op⟨A:A⟩, S, T)`,
	// keeps its explicit spelling — the short reading, with `add` put in
	// front, is contradicted by the annotated slot. This is how the typed
	// print of a statement, which pins every instance, reads back as the
	// statement. The unannotated spelling read the same way already.
	scope := implicitTestScope(t)
	prefix := "∀add:(A → A → A). ∀S T:((A → bool) → bool). "
	explicit := prefix + "set_op(set_op(add), S, T) = set_op(set_op(add), T, S)"
	assertSameProp(t, scope, prefix+"set_op(set_op, S, T) = set_op(set_op, T, S)", explicit)
	assertSameProp(t, scope, prefix+"set_op⟨A:A → bool⟩(set_op⟨A:A⟩, S, T) = set_op⟨A:A → bool⟩(set_op⟨A:A⟩, T, S)", explicit)
	assertSameProp(t, scope, prefix+"set_op⟨A:A → bool⟩(set_op⟨A:A⟩(add), S, T) = set_op⟨A:A → bool⟩(set_op⟨A:A⟩(add), T, S)", explicit)
	// An annotated bare head is still the constant at its components.
	assertSameProp(t, scope, "∀add:(A → A → A). set_op⟨A:A⟩ = set_op⟨A:A⟩", "∀add:(A → A → A). set_op(add) = set_op(add)")
}

func TestImplicitArgs_AnnotationNamesAStatementLetterTheConstantAlsoSpells(t *testing.T) {
	// `pw_scale`'s own letters are A, C and D; the annotation fixes D to
	// the statement's `C → bool`. The constant's C is renamed apart
	// before the annotation is read, so the statement's C stays its own
	// and `pw_scale⟨D:C → bool⟩(mul)` is read at `A → ((C → bool) → A) →
	// (C → bool) → A`; the explicit reading of `with_scale` then stands
	// and the bound `smul` is not put in front.
	scope := implicitTestScope(t)
	prefix := "∀mul:(A → A → A). ∀smul:(A → B → B). ∀R:(A → bool). ∀x:((C → bool) → A). "
	assertSameProp(t, scope,
		prefix+"with_scale(pw_scale⟨D:C → bool⟩(mul), R, x) = x",
		prefix+"with_scale(pw_scale⟨D:C → bool⟩(mul), R, x) = x")
	res := ParsePropTextInScope(prefix+"with_scale(pw_scale⟨D:C → bool⟩(mul), R, x) = x", scope)
	if len(res.Errors) > 0 {
		t.Fatalf("explicit reading refused: %s", res.Errors[0].Message)
	}
	if text := prop.PrintProp(res.Prop); strings.Contains(text, "with_scale(smul") {
		t.Fatalf("the bound component was put in front of an explicit spelling: %s", text)
	}
}

// A polymorphic operation's arrow shape distinguishes an explicit
// prefix from the set argument of a short call.
func TestImplicitArgs_PolymorphicOperationPrefix(t *testing.T) {
	scope := implicitTestScope(t)
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatal(err)
		}
		return ty
	}
	scope.ConstMetas["zz_composition"] = core.MakeConstMeta("zz_composition", typ("(B → B) → (B → B) → B → B"))
	scope.ConstMetas["zz_set_mul"] = core.MakeConstMeta("zz_set_mul", typ("(A → A → A) → set(A) → set(A) → set(A)"))
	scope.Syntax.(testSyntax)["zz_set_mul"] = &ConstSyntax{Implicit: []string{"mul"}}
	result := ParsePropTextInScope("∀mul:(A → A → A). zz_set_mul(zz_composition) = zz_set_mul(zz_composition)", scope)
	if len(result.Errors) > 0 {
		t.Fatal(result.Errors)
	}
}
