// statement_imports_test.go — every constant and every type a member's
// statement spells is minted by a package the member's family imports.
//
// A statement is parsed on first use, against the process-global
// constant registry, so a binary that links the whole corpus reads a
// statement spelling any chapter's constant or type: nothing at the
// parse says whether the statement's own family stands on the chapter
// that mints it. The Go import graph is what says a chapter stands on
// another — what loads when the family alone is loaded, and what a
// reader takes the chapter to rest on — so this gate holds every
// registered entry's statement, a card's and a proved member's alike,
// to it: a constant or a type the statement spells is minted by the
// family's own package or by a package in its import closure. Where no
// file of the family otherwise imports the minting package, family.go
// imports it blank. A mint of a package that itself imports the family
// cannot be imported — the statement rests on a chapter above its own
// — and the gate says so instead of naming an import.
//
// A type is spelled wherever a variable, bound or free, or a constant
// carries it, so a statement may spell a chapter's type and none of
// its constants: `∀x:real. x + x = x + x` spells `real` under an
// operator the parser builds itself.
//
// Constants the parser builds on its own (dsl.NativeConstNames), the
// engine's built-ins and the kernel's types (bool, fun, ind) are minted
// by no chapter and are skipped. definition_deps_test.go holds a
// definition's equation to the same closure, and to more: the equation
// parses at init, so its mints are ordered before it.
package gates

import (
	"fmt"
	"maps"
	"slices"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/index"
	"github.com/euc-ai/xugo/library/registry"
)

// spelledStatement is one member with the constants and the types its
// statement spells.
type spelledStatement struct {
	// Member is the member's id, Family its family's name.
	Member, Family string
	Constants      []string
	Types          []string
}

// mintSite is the member whose door minted a constant or a type, and
// that member's family.
type mintSite struct {
	Member, Family string
}

// unimportedMint is one refusal: Member's statement spells Name — a
// constant, or a type where IsType — and the package minting it (To)
// is outside the import closure of the member's own package (From).
type unimportedMint struct {
	Member, Family string
	Name           string
	IsType         bool
	Mint           mintSite
	From, To       string
	// Above says To imports From, so From cannot import it.
	Above bool
}

func (u unimportedMint) String() string {
	spelled := "`" + u.Name + "`"
	if u.IsType {
		spelled = "the type " + spelled
	}
	head := fmt.Sprintf("%s states %s, minted by %s in %s, and %s imports that package through nothing",
		u.Member, spelled, u.Mint.Member, u.Mint.Family, u.Family)
	if u.Above {
		return head + fmt.Sprintf(" — and cannot: %s imports %s, so the statement rests on a chapter above its own",
			u.To, u.From)
	}
	return head + fmt.Sprintf(" — the family alone does not read its own statement: add\n\t_ %q\nto %s/family.go",
		corpusImportPrefix+u.To, u.From)
}

// statementMints is where the constants and the types of a corpus are
// minted: each answers for a name a chapter minted and for no other.
type statementMints struct {
	Constant, Type func(name string) (mintSite, bool)
	// Native are the constants the parser builds itself, skipped whoever
	// mints them.
	Native map[string]bool
}

// unimportedMints checks every statement's constants and types against
// its family's import closure and returns the refusals in the order
// the statements came, a statement's constants before its types, with
// the number of (statement, constant of another package) and of
// (statement, type of another package) pairs it checked. dirOf maps a
// family's name to its package dir.
func unimportedMints(
	stmts []spelledStatement,
	mints statementMints,
	dirOf map[string]string,
	closure *importClosure,
) (refused []unimportedMint, constants, types int) {
	for _, s := range stmts {
		from, ok := dirOf[s.Family]
		if !ok {
			panic("statement imports: " + s.Member + " is of family " + s.Family + ", which has no package dir")
		}
		// outside reports whether the mint is of another package, and
		// records the refusal where that package is not imported.
		outside := func(name string, isType bool, mint mintSite) bool {
			to, ok := dirOf[mint.Family]
			if !ok {
				panic("statement imports: `" + name + "` is minted in " + mint.Family + ", which has no package dir")
			}
			if to == from {
				return false
			}
			if !closure.of(from)[to] {
				refused = append(refused, unimportedMint{
					Member: s.Member, Family: s.Family, Name: name, IsType: isType, Mint: mint,
					From: from, To: to, Above: closure.of(to)[from],
				})
			}
			return true
		}
		for _, name := range s.Constants {
			if mints.Native[name] {
				continue
			}
			if mint, ok := mints.Constant(name); ok && outside(name, false, mint) {
				constants++
			}
		}
		for _, name := range s.Types {
			if mint, ok := mints.Type(name); ok && outside(name, true, mint) {
				types++
			}
		}
	}
	return refused, constants, types
}

// statementTypes lists, in name order, the type constructors a
// statement spells: those in the types of its variables, bound and
// free, and of its constants.
func statementTypes(p core.Prop) []string {
	names := map[string]bool{}
	collectTermTypes(p.Conclusion(), names, ext.SeenSetFor(p.Conclusion()))
	for _, h := range p.Hyps() {
		collectTermTypes(h, names, ext.SeenSetFor(h))
	}
	return slices.Sorted(maps.Keys(names))
}

func collectTermTypes(t ext.Term, names map[string]bool, seen *ext.SeenSet) {
	switch t := t.Core().(type) {
	case ext.VarTerm:
		collectTypeNames(t.Type(), names)
	case ext.ConstTerm:
		collectTypeNames(t.Type(), names)
	case ext.AppliedTerm:
		if seen.Visited(t) {
			return
		}
		collectTermTypes(t.Fun(), names, seen)
		collectTermTypes(t.Arg(), names, seen)
	case ext.AbsTerm:
		if seen.Visited(t) {
			return
		}
		collectTypeNames(t.Var().Type(), names)
		collectTermTypes(t.Body(), names, seen)
	default:
		panic(fmt.Sprintf("statement imports: a term of kind %T", t))
	}
}

func collectTypeNames(ty core.HolType, names map[string]bool) {
	switch ty := ty.(type) {
	case core.VarType:
	case core.CompositeType:
		names[string(ty.Meta().Name())] = true
		for i := range ty.Meta().Arity() {
			collectTypeNames(ty.SubType(i), names)
		}
	default:
		panic(fmt.Sprintf("statement imports: a type of kind %T", ty))
	}
}

func TestLintStatementMintsImported(t *testing.T) {
	c, err := index.Load(corpusRoot)
	if err != nil {
		t.Fatal(err)
	}
	dirOf := map[string]string{}
	for _, f := range c.Families {
		dirOf[f.Name] = f.Dir
	}
	typeMints := map[string]mintSite{}
	for _, td := range c.Types {
		typeMints[td.Type] = mintSite{Member: td.Member, Family: td.Family}
	}
	mints := statementMints{
		Constant: func(name string) (mintSite, bool) {
			d := c.DefinitionOf(name)
			if d == nil {
				return mintSite{}, false
			}
			return mintSite{Member: d.Member, Family: d.Family}, true
		},
		Type: func(name string) (mintSite, bool) {
			m, ok := typeMints[name]
			return m, ok
		},
		Native: dsl.NativeConstNames(),
	}
	var stmts []spelledStatement
	for _, e := range registry.All() {
		st := e.Statement()
		s := spelledStatement{Member: index.MemberID(e), Family: e.Family().Name, Types: statementTypes(st.Prop)}
		for _, name := range st.Constants() {
			s.Constants = append(s.Constants, string(name))
		}
		stmts = append(stmts, s)
	}
	refused, constants, types := unimportedMints(stmts, mints, dirOf, corpusImportClosure(t))
	for _, u := range refused {
		t.Error(u)
	}
	if constants == 0 || types == 0 {
		t.Fatalf("%d constants and %d types of another package were found in the statements: the gate checked nothing of one kind",
			constants, types)
	}
	t.Logf("%d statements; %d (statement, constant of another package) and %d (statement, type of another package) pairs checked",
		len(stmts), constants, types)
}

// TestLintStatementMintsImportedRefuses holds the check to a corpus of
// five packages, `top` → `mid` → `base` → `ground`, and `apart`,
// imported by none of them: a statement of `mid` may spell what `mid`,
// `base` and `ground` mint, and is refused at a constant or a type of
// `apart` (an import to add) and at one of `top` (which imports `mid`).
func TestLintStatementMintsImportedRefuses(t *testing.T) {
	imports := map[string][]string{
		"dom/top":  {"dom/mid"},
		"dom/mid":  {"dom/base"},
		"dom/base": {"dom/ground"},
	}
	closure := newImportClosure(func(dir string) []string { return imports[dir] })
	// The family `dom/mid_family` is nested: its package dir is not its
	// name.
	dirOf := map[string]string{
		"dom/top": "dom/top", "dom/mid_family": "dom/mid", "dom/base": "dom/base",
		"dom/ground": "dom/ground", "dom/apart": "dom/apart",
	}
	constMints := map[string]mintSite{
		"top_const":    {Member: "dom/top.TopDef", Family: "dom/top"},
		"mid_const":    {Member: "dom/mid_family.MidDef", Family: "dom/mid_family"},
		"base_const":   {Member: "dom/base.BaseDef", Family: "dom/base"},
		"ground_const": {Member: "dom/ground.GroundDef", Family: "dom/ground"},
		"apart_const":  {Member: "dom/apart.ApartDef", Family: "dom/apart"},
	}
	typeMints := map[string]mintSite{
		"top_type":    {Member: "dom/top.TopType", Family: "dom/top"},
		"mid_type":    {Member: "dom/mid_family.MidType", Family: "dom/mid_family"},
		"ground_type": {Member: "dom/ground.GroundType", Family: "dom/ground"},
		"apart_type":  {Member: "dom/apart.ApartType", Family: "dom/apart"},
	}
	mints := statementMints{
		Constant: func(name string) (mintSite, bool) {
			m, ok := constMints[name]
			return m, ok
		},
		Type: func(name string) (mintSite, bool) {
			m, ok := typeMints[name]
			return m, ok
		},
		Native: map[string]bool{"native_const": true},
	}
	mid := func(name string, constants, types []string) spelledStatement {
		return spelledStatement{Member: "dom/mid_family." + name, Family: "dom/mid_family", Constants: constants, Types: types}
	}
	stmts := []spelledStatement{
		mid("Own", []string{"mid_const"}, []string{"mid_type", "bool"}),
		mid("Imported", []string{"base_const", "ground_const"}, []string{"ground_type", "fun"}),
		mid("Unminted", []string{"native_const", "engine_const"}, []string{"bool", "fun", "ind"}),
		mid("Card", []string{"base_const", "apart_const"}, nil),
		mid("Upward", []string{"top_const"}, nil),
		// A type and no constant of the package that mints it.
		mid("TypeAlone", []string{"native_const"}, []string{"apart_type", "ground_type"}),
		mid("TypeUpward", nil, []string{"top_type"}),
		{Member: "dom/top.Imported", Family: "dom/top", Constants: []string{"mid_const", "ground_const"}, Types: []string{"mid_type"}},
	}
	refused, constants, types := unimportedMints(stmts, mints, dirOf, closure)
	if constants != 7 || types != 5 {
		t.Errorf("%d constant and %d type pairs checked, want the 7 and the 5 of another package", constants, types)
	}
	want := []unimportedMint{
		{
			Member: "dom/mid_family.Card", Family: "dom/mid_family", Name: "apart_const",
			Mint: constMints["apart_const"], From: "dom/mid", To: "dom/apart",
		},
		{
			Member: "dom/mid_family.Upward", Family: "dom/mid_family", Name: "top_const",
			Mint: constMints["top_const"], From: "dom/mid", To: "dom/top", Above: true,
		},
		{
			Member: "dom/mid_family.TypeAlone", Family: "dom/mid_family", Name: "apart_type", IsType: true,
			Mint: typeMints["apart_type"], From: "dom/mid", To: "dom/apart",
		},
		{
			Member: "dom/mid_family.TypeUpward", Family: "dom/mid_family", Name: "top_type", IsType: true,
			Mint: typeMints["top_type"], From: "dom/mid", To: "dom/top", Above: true,
		},
	}
	if len(refused) != len(want) {
		t.Fatalf("%d refusals, want %d: %v", len(refused), len(want), refused)
	}
	for i, u := range refused {
		if u != want[i] {
			t.Errorf("refusal %d is %+v, want %+v", i, u, want[i])
		}
	}
	importLine := `_ "` + corpusImportPrefix + `dom/apart"`
	names := func(refusal unimportedMint, parts ...string) {
		t.Helper()
		msg := refusal.String()
		for _, part := range parts {
			if !strings.Contains(msg, part) {
				t.Errorf("the refusal does not name %s: %s", part, msg)
			}
		}
	}
	names(refused[0], "dom/mid_family.Card", "states `apart_const`", "dom/apart.ApartDef", importLine, "dom/mid/family.go")
	names(refused[1], "dom/mid_family.Upward", "states `top_const`", "dom/top imports dom/mid")
	names(refused[2], "dom/mid_family.TypeAlone", "states the type `apart_type`", "dom/apart.ApartType", importLine, "dom/mid/family.go")
	names(refused[3], "dom/mid_family.TypeUpward", "states the type `top_type`", "dom/top imports dom/mid")
	for _, above := range []unimportedMint{refused[1], refused[3]} {
		if msg := above.String(); strings.Contains(msg, "family.go") {
			t.Errorf("a refusal at a chapter above names an import to add: %s", msg)
		}
	}
}

// TestLintStatementTypesRead holds the reading of a term's types to
// `λx:zz_box(A). f(u)` with f:zz_unit → bool: a type is read off a
// bound variable the body does not mention, off the free variables,
// through an arrow and through a type's own arguments, and a type
// variable is no type's name.
func TestLintStatementTypesRead(t *testing.T) {
	unit := ext.MakeType("zz_unit")
	x := core.Var("x", ext.MakeType("zz_box", ext.TypeA))
	f := core.Var("f", ext.MakeFun(unit, ext.TypeBool))
	u := core.Var("u", unit)
	got := map[string]bool{}
	collectTermTypes(core.Abs(x, core.Apply(f, u)), got, nil)
	want := []string{"bool", "fun", "zz_box", "zz_unit"}
	if names := slices.Sorted(maps.Keys(got)); !slices.Equal(names, want) {
		t.Errorf("the term's types read as %v, want %v", names, want)
	}
}
