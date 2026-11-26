// claim_lint_test.go — corpus-aware STATEMENT lints: the statically
// checkable part of claim-text parsing, moved from replay time (a slow
// proof failure) to lint time (seconds, file:line).
//
// Three levels:
//
// B0 — CLAIM LITERALS PARSE. Every string literal in a claim position
// (a.Have / a.Obtain … a.Obtain5 / a.ObtainChosen claims,
// a.Hyp statements, family/ctx headline constructors, package-level
// string consts used there; a typed verb — a.ObtainAs[T], a.TermAs[T],
// … — reads as its untyped twin, claimTypedVerbTwin) must LEX AND PARSE
// under the REAL parser in the family's statement scope: the family
// vocabulary (registry.Family.ParseScript — the same scope Statement
// elaborates member headlines in) plus the const resolver
// proof.NewScript wires from the env's ConstMetaManager.
//
// The gate is the SYNTAX stage only (lex + parse errors — parse_error /
// unknown_symbol — plus parser panics). The TYPE stage is measured but
// NOT gated: type resolution depends on the runtime scope — a claim
// naming a minted Skolem (`x₀`) or a statement binder types only
// because Fix/Obtain/section-boundary registration put the variable in
// Script.ParseScope.Vars, which does not exist statically. The type
// stage's failures are logged by code (missing_type /
// validation_error) as a census: claims over such variables. Surface
// names mean BOTH spellings are legal (`x` and `x₀` —
// prover/proof/derive.go §"Surface names"), so a statement binder name
// and its SurfaceBase-invertible variants are treated as known
// variables where a name is judged (the missing_type census below).
//
// Within the unGated type stage one shape is still worth reporting: a
// missing_type failure whose VARIABLE is not a Go-declared name of the
// file (closure param, := target), not a headline binder, and not a
// vocab var — even after SurfaceBase inversion. A typo'd constant name
// parses as exactly such a fresh variable. Census only (t.Logf).
//
// What is deliberately SKIPPED (silently — the false-positive
// discipline: a lint that rejects legal code is worse than no lint):
// - files outside a registered family directory (aggregators, shared
// vocab packages);
// - claim arguments that are not string literals or same-package
// string consts (Prop/Fact values, concatenations);
// - headline constructors carrying per-section const overrides
// (sectionConsts change the parse scope in a way this lint cannot
// reproduce statically);
// - claim verbs on a non-single-identifier receiver (ambiguous).
//
// a.Term literals are parsed term-level (nil expected type) and
// reported as a CENSUS, not a gate: a bare term has no boolean root to
// anchor type inference, so "cannot infer" failures are expected noise
// for spellings the runtime scope (minted Skolems, proof-declared vars)
// types fine.
//
// B0 census — SUSPICIOUS APPLIED HEADS. A name applied as a function
// that parsed as a fresh FREE variable (not a const, not bound in the
// claim, not a family-vocab var, not a Go-declared name of the file, not
// a headline binder or its SurfaceBase variant) is how a typo'd
// constant name parses LEGALLY.
// Census only (t.Logf), following TestCiteChainCommentCensus's
// precedent: the exclusion set is heuristic.
//
// B1 — STATEMENTS. Every entry's statement must elaborate — a headline
// that fails to parse under the family vocabulary, or that states a
// sequent, is an authoring error Statement escalates by design. The check is
// REDUNDANT at replay (the harness elaborates every statement for the
// trust set), so what this buys is purely speed: the same failure
// seconds after an edit instead of minutes into a replay.
//
// B2 — GROUND-CITE WITNESS ARITY. At(dep, w…) / Cite(dep, w…) /
// CiteKeep(dep, w…) whose dep statically resolves to a registry entry
// must not carry more witnesses than the dep's INSTALL form has leading
// ∀ slots. The install form for a named dep is NormalizedThm(Dep(name))
// (prover/proof/fact.go §Cite), i.e. Normalize of the served headline —
// whose ∀-prefix may be LONGER than the headline's stated leading run
// (Normalize prenexes inner quantifiers), so the bound is computed on
// the normalized form; a witness count above the stated leading run but
// within the normalized prefix is legal and only census-logged.
// Anything not statically resolvable (local certs, Fact values, deps
// whose statement is a sequent) is skipped silently.
package gates

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	propext "github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/library/xugofmt"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// Shared plumbing
// ---------------------------------------------------------------------------

var (
	claimEnvOnce sync.Once
	claimEnvVal  *proof.ProverEnv
)

// claimLintEnv returns the one shared parse env for every claim lint:
// a fresh seed env whose ProofService is wired to the global
// ConstMetaManager, so proof.NewScript's ConstResolver serves
// def-carrying metas for any const a claim names.
func claimLintEnv() *proof.ProverEnv {
	claimEnvOnce.Do(func() { claimEnvVal = serve.NewSeedEnv() })
	return claimEnvVal
}

// claimFamilyByDir maps a family package directory (relative to this
// package dir, slash-separated) to its registry.Family — keyed EXACTLY
// as a walked path's directory is spelled, `path.Dir(filepath.ToSlash(f))`
// over chapterProofFiles, which is what every consumer looks up with.
//
// A key spelled any other way — the corpus-relative `vector/matrix`,
// where the walk yields `../../proofs/vector/matrix` — hits no lookup:
// every file falls into "outside a registered family dir" and five gates
// — the claim parse, headline, cite-arity and var-scope lints, and the
// entry dead-dep census — pass while analyzing nothing.
// TestCorpusIsReachable counts the walk, not the key. familyDir is the
// one place a Family becomes a path, so it is the key.
func claimFamilyByDir() map[string]*registry.Family {
	m := map[string]*registry.Family{}
	for _, f := range registry.Families() {
		m[filepath.ToSlash(familyDir(f))] = f
	}
	return m
}

// claimScopeCache lazily builds ONE vocab-loaded ParseScope per family
// (registry.Family.ParseScript — Statement's scope). The scope maps
// are read-only during parsing (the resolver path seeds the parser's
// own typeEnv, never the scope), so one Script serves every literal.
type claimScopeCache struct {
	env    *proof.ProverEnv
	scopes map[*registry.Family]*dsl.ParseScope
	vars   map[*registry.Family]map[string]bool // vocab-declared free vars
}

func newClaimScopeCache(env *proof.ProverEnv) *claimScopeCache {
	return &claimScopeCache{
		env:    env,
		scopes: map[*registry.Family]*dsl.ParseScope{},
		vars:   map[*registry.Family]map[string]bool{},
	}
}

func (c *claimScopeCache) scope(f *registry.Family) *dsl.ParseScope {
	if s, ok := c.scopes[f]; ok {
		return s
	}
	ctx := f.ParseScript(c.env)
	s := &ctx.ParseScope
	c.scopes[f] = s
	vars := map[string]bool{}
	for name := range s.Vars {
		vars[name] = true
	}
	c.vars[f] = vars
	return s
}

// vocabVars returns the family vocabulary's declared free-variable
// names (a sequent chapter's standard frees).
func (c *claimScopeCache) vocabVars(f *registry.Family) map[string]bool {
	c.scope(f)
	return c.vars[f]
}

// ---------------------------------------------------------------------------
// B0 — claim-literal collection
// ---------------------------------------------------------------------------

// claimVerbArg maps a claim-bearing method name (called on a single
// identifier receiver) to the index of its claim/headline argument.
var claimVerbArg = map[string]int{
	// *proof.Argument claim verbs — 2nd argument is the claim.
	"Have": 1, "Obtain": 1, "Obtain2": 1, "Obtain3": 1, "Obtain4": 1, "Obtain5": 1, "ObtainChosen": 1,
	// *proof.Argument statement/term verbs — 1st argument.
	"Hyp": 0, "Term": 0,
	// Headline constructors (family.* and ctx.*) — 1st argument.
	"Theorem": 0, "Lemma": 0, "Sections": 0, "Derived": 0,
	"Lifted": 0,
}

// claimTypedVerbTwin maps each typed Argument verb to the untyped verb
// it composes with ext.As (prover/proof/typed.go: "never new
// semantics") — same claim position, same env effect. Every lint reads
// the typed spelling as its twin.
var claimTypedVerbTwin = map[string]string{
	"FixAs": "Fix", "TermAs": "Term",
	"ObtainAs": "Obtain", "Obtain2As": "Obtain2", "Obtain3As": "Obtain3",
	"Obtain4As": "Obtain4", "Obtain5As": "Obtain5",
	"UnpackAs": "Unpack", "Unpack2As": "Unpack2", "Unpack3As": "Unpack3",
	"Unpack4As": "Unpack4", "Unpack5As": "Unpack5",
}

// claimVerbSelector reads a method call's selector and verb name. A
// typed verb is a generic instantiation — `a.ObtainAs[Nat](…)` is an
// IndexExpr, `a.Obtain2As[Real, Real](…)` an IndexListExpr, around the
// selector — whose type arguments are peeled and whose name reads as
// its untyped twin. A generic call of any other name is no verb.
func claimVerbSelector(call *ast.CallExpr) (*ast.SelectorExpr, string, bool) {
	fun, generic := typeArgsPeeled(call.Fun)
	sel, ok := fun.(*ast.SelectorExpr)
	if !ok {
		return nil, "", false
	}
	if twin, typed := claimTypedVerbTwin[sel.Sel.Name]; typed {
		return sel, twin, true
	}
	if generic {
		return nil, "", false
	}
	return sel, sel.Sel.Name, true
}

// typeArgsPeeled is a callee with its explicit type arguments removed
// (an IndexExpr or IndexListExpr around it), and whether it had any.
func typeArgsPeeled(fun ast.Expr) (ast.Expr, bool) {
	switch f := fun.(type) {
	case *ast.IndexExpr:
		return f.X, true
	case *ast.IndexListExpr:
		return f.X, true
	}
	return fun, false
}

// verbName names the constructor or verb a call invokes, called bare or
// as a method. A typed verb reads as its untyped twin, as in
// claimVerbSelector, and any other generic call as none ("").
func verbName(call *ast.CallExpr) string {
	fun, generic := typeArgsPeeled(call.Fun)
	var name string
	switch f := fun.(type) {
	case *ast.Ident:
		name = f.Name
	case *ast.SelectorExpr:
		name = f.Sel.Name
	}
	if twin, typed := claimTypedVerbTwin[name]; typed {
		return twin
	}
	if generic {
		return ""
	}
	return name
}

// claimSectionConstVerbs: headline constructors whose arguments beyond
// this count are per-section const overrides — a parse scope this lint
// cannot reproduce statically, so such headlines are skipped.
var claimSectionConstVerbs = map[string]int{
	"Theorem": 2, "Lemma": 2, "Sections": 2, "Derived": 2,
}

// claimHeadlineVerbs marks the constructors whose literal is a member
// HEADLINE (used by the census's binder harvesting).
var claimHeadlineVerbs = map[string]bool{
	"Theorem": true, "Lemma": true, "Sections": true, "Derived": true,
	"Lifted": true,
}

// claimTableDoorVerbs marks the structure doors whose first argument is
// a statement with a proof closure after it: Structure.Law states its
// body through family.Theorem, so the body's abbreviation table is in
// scope for every text of the proof, as a headline's is. The body omits
// the door's own component binders, which the table may spell.
var claimTableDoorVerbs = map[string]bool{
	"Law": true,
}

type claimSite struct {
	file string
	line int
	dir  string
	verb string
	text string
	// abbreviations is the innermost span the text stands in — a
	// statement's call, or the func it is written in where a statement
	// reaches that func; nil outside every one.
	abbreviations *abbreviationSpan
	// exempt names the binders the text binds as its own, which the
	// door that reads it exempts from the abbreviation capture check: a
	// headline's leading binders, a claim in parts' Binders. A string
	// claim and a term text bind none of the statement's.
	exempt map[string]bool
	// literal and statement say how the argument writes the text: a
	// string literal or literals joined by +, or the Statement literal
	// itself; neither for a const or a structure door's statement.
	literal   bool
	statement *dsl.Statement
	// width is the columns of the line the argument stands on, written
	// as the one string (claimLineWidth).
	width int
}

// claimLineWidth is the columns of the line an argument spanning
// src[from:to] stands on once it is written as the one string text: the
// line up to the argument, the quoted text, and what follows the
// argument on its last line, measured as xugofmt measures a line, from
// its indentation.
func claimLineWidth(src []byte, from, to int, text string) int {
	lineStart := strings.LastIndexByte(string(src[:from]), '\n') + 1
	lineEnd := len(src)
	if next := strings.IndexByte(string(src[to:]), '\n'); next >= 0 {
		lineEnd = to + next
	}
	return xugofmt.ContentWidth(string(src[lineStart:from]) + strconv.Quote(text) + string(src[to:lineEnd]))
}

// claimTextOf is a claim verb's text as its argument writes it — a
// string literal or package string const, or, at a verb other than
// Term, a `Statement{…}` literal assembled as the claim door assembles
// it — and the binders the door exempts at that text: none for a
// string, the parts' own Binders for a Statement (prover/proof's
// Argument.claimParts).
func claimTextOf(verb string, arg ast.Expr, consts map[string]string) (string, map[string]bool, bool) {
	if text, ok := resolveClaimString(arg, consts); ok {
		return text, nil, true
	}
	if verb == "Term" {
		return "", nil, false
	}
	stmt, ok := statementLiteral(arg)
	if !ok {
		return "", nil, false
	}
	text, err := stmt.Text()
	if err != nil {
		return "", nil, false
	}
	names, err := stmt.BinderNames()
	if err != nil {
		return "", nil, false
	}
	return text, nameSet(names), true
}

// headlineExempt is the binders a statement text binds in front, which
// the statement door exempts from the capture check
// (registry.installAbbreviations, Script.withSectionAbbreviations).
func headlineExempt(text string) map[string]bool {
	return nameSet(dsl.LeadingBinderNames(text))
}

// nameSet is names as a set; nil for none.
func nameSet(names []string) map[string]bool {
	if len(names) == 0 {
		return nil
	}
	set := make(map[string]bool, len(names))
	for _, name := range names {
		set[name] = true
	}
	return set
}

// collectStringConsts harvests a package's string consts from its
// files — `const name = "…"`, and a const written as literals and
// consts of the package joined by `+`, in any declaration order — the
// one indirection form the collector follows: a named const is the
// rule's permitted assembly, and one built from consts is a const.
func collectStringConsts(files []*ast.File, out map[string]string) {
	type spec struct {
		name  string
		value ast.Expr
	}
	var pending []spec
	for _, af := range files {
		for _, d := range af.Decls {
			gd, ok := d.(*ast.GenDecl)
			if !ok || gd.Tok != token.CONST {
				continue
			}
			for _, s := range gd.Specs {
				vs, ok := s.(*ast.ValueSpec)
				if !ok || len(vs.Names) != len(vs.Values) {
					continue
				}
				for i, name := range vs.Names {
					pending = append(pending, spec{name.Name, vs.Values[i]})
				}
			}
		}
	}
	for progress := true; progress && len(pending) > 0; {
		progress = false
		var left []spec
		for _, s := range pending {
			if text, ok := constStringValue(s.value, out); ok {
				out[s.name] = text
				progress = true
				continue
			}
			left = append(left, s)
		}
		pending = left
	}
}

// constStringValue is the text of a const expression over string
// literals and the consts already known, joined by `+`; false for any
// other expression, or one naming a const not (yet) known.
func constStringValue(e ast.Expr, consts map[string]string) (string, bool) {
	switch e := e.(type) {
	case *ast.BasicLit:
		if e.Kind != token.STRING {
			return "", false
		}
		s, err := strconv.Unquote(e.Value)
		return s, err == nil
	case *ast.Ident:
		s, ok := consts[e.Name]
		return s, ok
	case *ast.ParenExpr:
		return constStringValue(e.X, consts)
	case *ast.BinaryExpr:
		if e.Op != token.ADD {
			return "", false
		}
		left, ok := constStringValue(e.X, consts)
		if !ok {
			return "", false
		}
		right, ok := constStringValue(e.Y, consts)
		if !ok {
			return "", false
		}
		return left + right, true
	}
	return "", false
}

func resolveClaimString(e ast.Expr, consts map[string]string) (string, bool) {
	return constStringValue(e, consts)
}

// headlineStatement is a headline constructor's statement as its first
// argument writes it: a string literal or package string const, or a
// `Statement{…}` literal with its abbreviations — bare, or as the body
// of a structure door's `X.Statement(body)`, which prefixes the door's
// components and keeps the body's table.
func headlineStatement(e ast.Expr, consts map[string]string) (string, dsl.Abbrev, bool) {
	e = doorStatementBody(e)
	if text, ok := resolveClaimString(e, consts); ok {
		return text, nil, true
	}
	stmt, ok := statementLiteral(e)
	if !ok {
		return "", nil, false
	}
	text, err := stmt.Text()
	if err != nil {
		return "", nil, false
	}
	return text, stmt.Abbrev, true
}

// doorStatementBody is the body argument of a structure door's
// `X.Statement(body)` call, or e itself when e is no such call.
func doorStatementBody(e ast.Expr) ast.Expr {
	call, ok := e.(*ast.CallExpr)
	if !ok || len(call.Args) != 1 {
		return e
	}
	if sel, ok := call.Fun.(*ast.SelectorExpr); !ok || sel.Sel.Name != "Statement" {
		return e
	}
	return call.Args[0]
}

// TestLintClaimSpansReadADoorsTable: a structure door's body reaches a
// proof closure two ways, as the body of the door's Law and as
// `X.Statement(body)` under a headline constructor. In both, the table
// the body declares is in scope for the claims inside, as
// registry.installAbbreviations gives it at runtime.
func TestLintClaimSpansReadADoorsTable(t *testing.T) {
	const src = `package p

var law = S.Law(Statement{
	Binders:       "∀x:A.",
	Conclusion:    "p(«y»)",
	Abbrev: Abbrev{{Name: "y", Text: "f(x)"}},
}, func(a *Argument) { a.Have("by the law", "q(«y»)") })

var wrapped = family.Theorem(S.Statement(Statement{
	Binders:       "∀x:A.",
	Conclusion:    "p(«z»)",
	Abbrev: Abbrev{{Name: "z", Text: "g(x)"}},
}), func(a *Argument) { a.Have("by the wrapped body", "q(«z»)") })
`
	fset := token.NewFileSet()
	af, err := parser.ParseFile(fset, "door.go", src, 0)
	if err != nil {
		t.Fatal(err)
	}
	spans := abbreviationSpans(af, nil, nil)
	file := fset.File(af.Pos())
	for _, c := range []struct{ claim, name string }{{`"q(«y»)"`, "y"}, {`"q(«z»)"`, "z"}} {
		at := abbreviationsAt(spans, file.Pos(strings.Index(src, c.claim)))
		if at == nil || at.table == nil || !at.table.Has(c.name) {
			t.Errorf("the claim %s has no table declaring «%s» in scope", c.claim, c.name)
		}
	}
}

// TestLintClaimExemptsWhatTheDoorExempts: a text may bind over an
// entry's names, in its leading ∀-chain, only what its own door exempts
// — a headline its leading binders, a claim in parts its own Binders, a
// string claim nothing (prover/proof's Argument.parseClaim reads a
// claim with no binder of the statement's exempt). So the one text
// `∀n:num. «s» = n + 1`, «s» written over the member's n, reads clean
// as the headline and as a claim in parts and is refused as a string
// claim, at its site as at the claim door at replay.
func TestLintClaimExemptsWhatTheDoorExempts(t *testing.T) {
	const src = `package p

var member = family.Theorem(Statement{
	Binders:       "∀n:num.",
	Conclusion:    "«s» = n + 1",
	Abbrev: Abbrev{{Name: "s", Text: "n + 1"}},
}, func(a *Argument, n *Expr[Nat]) {
	a.Have("a string claim binds none of the statement's binders", "∀n:num. «s» = n + 1")
	a.Have("a claim in parts binds its own", Statement{Binders: "∀n:num.", Conclusion: "«s» = n + 1"})
})
`
	var arith *registry.Family
	for _, f := range registry.Families() {
		if f.Name == "nat_num/nat_arith" {
			arith = f
		}
	}
	if arith == nil {
		t.Fatal("no family nat_num/nat_arith to read the texts in")
	}
	scope := newClaimScopeCache(claimLintEnv()).scope(arith)
	fset := token.NewFileSet()
	af, err := parser.ParseFile(fset, "member.go", src, 0)
	if err != nil {
		t.Fatal(err)
	}
	spans := abbreviationSpans(af, nil, nil)
	var sites []claimSite
	var headline string
	ast.Inspect(af, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}
		switch verbName(call) {
		case "Theorem":
			text, _, ok := headlineStatement(call.Args[0], nil)
			if !ok {
				t.Fatal("the headline does not read")
			}
			headline = text
			sites = append(sites, claimSite{verb: "Theorem", text: text,
				abbreviations: abbreviationsAt(spans, call.Args[0].Pos()), exempt: headlineExempt(text)})
		case "Have":
			text, exempt, ok := claimTextOf("Have", call.Args[1], nil)
			if !ok {
				t.Fatalf("the claim at %s does not read", fset.Position(call.Pos()))
			}
			sites = append(sites, claimSite{verb: "Have", text: text,
				abbreviations: abbreviationsAt(spans, call.Args[1].Pos()), exempt: exempt})
		}
		return true
	})
	if len(sites) != 3 {
		t.Fatalf("want the headline and two claims, got %d sites", len(sites))
	}
	for i, want := range []string{"", "rebinds", ""} {
		got := claimErrString(parseClaimSite(scope, sites[i]))
		switch {
		case want == "" && got != "":
			t.Errorf("%s %q: want no error, got %s", sites[i].verb, sites[i].text, got)
		case want != "" && !strings.Contains(got, want):
			t.Errorf("%s %q: want an error naming the capture, got %q", sites[i].verb, sites[i].text, got)
		}
	}
	// The control: read with the headline's binders exempt, as the
	// lint read every site inside a span before, the string claim
	// passes — the leniency the claim door does not have.
	lenient := sites[1]
	lenient.exempt = headlineExempt(headline)
	if got := claimErrString(parseClaimSite(scope, lenient)); got != "" {
		t.Errorf("control: with the headline's binders exempt the claim should read clean; got %s", got)
	}
}

// withAbbreviations is scope with a span's table installed and exempt —
// the binders the text binds as its own (claimSite.exempt) — exempt
// from the capture check, or scope itself where no table is in reach.
func withAbbreviations(scope *dsl.ParseScope, span *abbreviationSpan, exempt map[string]bool) *dsl.ParseScope {
	if span == nil || span.table == nil {
		return scope
	}
	installed := *scope
	installed.Abbreviations = span.table
	installed.AbbreviationBinders = exempt
	return &installed
}

// claimCollection is one full walk of the corpus: every claim
// literal, the per-file ASTs (for the census's Go-name harvesting), and
// the skip census.
type claimCollection struct {
	sites []claimSite
	skips map[string]int
	// asts holds each family file's parsed AST, fileset shared.
	fset *token.FileSet
	asts map[string]*ast.File
}

func collectClaimSites(t *testing.T) *claimCollection {
	t.Helper()
	famByDir := claimFamilyByDir()
	col := &claimCollection{
		skips: map[string]int{},
		fset:  token.NewFileSet(),
		asts:  map[string]*ast.File{},
	}
	byDir := map[string][]string{}
	for _, f := range chapterProofFiles(t) {
		dir := path.Dir(filepath.ToSlash(f))
		byDir[dir] = append(byDir[dir], f)
	}
	dirs := make([]string, 0, len(byDir))
	for dir := range byDir {
		dirs = append(dirs, dir)
	}
	sort.Strings(dirs)
	for _, dir := range dirs {
		files := byDir[dir]
		if famByDir[dir] == nil {
			col.skips["file outside a registered family dir"] += len(files)
			continue
		}
		consts := map[string]string{}
		parsed := make([]*ast.File, 0, len(files))
		sources := map[string][]byte{}
		for _, f := range files {
			src, err := os.ReadFile(f)
			if err != nil {
				t.Fatalf("read %s: %v", f, err)
			}
			af, err := parser.ParseFile(col.fset, f, src, 0)
			if err != nil {
				t.Fatalf("parse %s: %v", f, err)
			}
			col.asts[f] = af
			sources[f] = src
			parsed = append(parsed, af)
		}
		collectStringConsts(parsed, consts)
		packageSpans := packageAbbreviationSpans(parsed, consts, famByDir[dir].Abbrev())
		for _, f := range files {
			af := col.asts[f]
			src := sources[f]
			spans := packageSpans[af]
			ast.Inspect(af, func(n ast.Node) bool {
				call, ok := n.(*ast.CallExpr)
				if !ok {
					return true
				}
				sel, verb, ok := claimVerbSelector(call)
				if !ok {
					return true
				}
				idx, ok := claimVerbArg[verb]
				if !ok {
					return true
				}
				// Arity guards: same-named methods on OTHER types exist
				// (intvocab.Term(ctx, "name") is a const accessor, not
				// a.Term(raw)). A call whose shape cannot be the claim
				// verb is not the claim verb.
				switch verb {
				case "Hyp", "Term":
					if len(call.Args) != 1 {
						return true
					}
				case "Lifted":
					if len(call.Args) != 2 {
						return true
					}
				default:
					if len(call.Args) < 2 {
						return true
					}
				}
				if _, ok := sel.X.(*ast.Ident); !ok {
					col.skips["claim verb on a non-identifier receiver"]++
					return true
				}
				if min, gated := claimSectionConstVerbs[verb]; gated && len(call.Args) > min {
					col.skips["headline with per-section const overrides"]++
					return true
				}
				// A headline or a claim is written in parts as well
				// (a `Statement{…}` literal); a term text is a string.
				// Each binds as its own what its door exempts.
				var text string
				var exempt map[string]bool
				if claimHeadlineVerbs[verb] {
					text, _, ok = headlineStatement(call.Args[idx], consts)
					exempt = headlineExempt(text)
				} else {
					text, exempt, ok = claimTextOf(verb, call.Args[idx], consts)
				}
				if !ok {
					col.skips["claim argument is not a string literal, package string const or Statement literal"]++
					return true
				}
				arg := call.Args[idx]
				pos := col.fset.Position(arg.Pos())
				_, literal := joinedStringLiterals(arg)
				var statement *dsl.Statement
				if stmt, ok := statementLiteral(arg); ok {
					statement = &stmt
				}
				col.sites = append(col.sites, claimSite{
					file: f, line: pos.Line, dir: dir,
					verb: verb, text: text,
					abbreviations: abbreviationsAt(spans, arg.Pos()),
					exempt:        exempt,
					literal:       literal,
					statement:     statement,
					width:         claimLineWidth(src, pos.Offset, col.fset.Position(arg.End()).Offset, dsl.OneLine(text)),
				})
				return true
			})
		}
	}
	return col
}

// parseClaimSite runs the real parser on one literal in the family
// scope, under the abbreviations of the statements in reach of it,
// converting any parser panic into a diagnostic string. Tables that do
// not merge are the panic the section door raises.
func parseClaimSite(scope *dsl.ParseScope, s claimSite) (res dsl.ParseResult, panicked string) {
	if why := s.abbreviations.refusal(s.text); why != "" {
		return res, why
	}
	defer func() {
		if r := recover(); r != nil {
			panicked = trimPanic(r)
		}
	}()
	scope = withAbbreviations(scope, s.abbreviations, s.exempt)
	if s.verb == "Term" {
		return dsl.ParseTermTextInScope(s.text, nil, scope, nil), ""
	}
	return dsl.ParsePropTextInScope(s.text, scope), ""
}

func claimErrString(res dsl.ParseResult, panicked string) string {
	if panicked != "" {
		return "panic: " + panicked
	}
	if len(res.Errors) > 0 {
		e := res.Errors[0]
		return fmt.Sprintf("[%s] %s", e.Code, e.Message)
	}
	return ""
}

// claimSyntaxCodes: the diagnostic codes of the SYNTAX stage — fully
// static, so gated. Everything else is the type/build stage, which
// depends on the runtime scope's variable typing (see the file header).
var claimSyntaxCodes = map[string]bool{
	dsl.CodeParseError:    true,
	dsl.CodeUnknownSymbol: true,
}

// missingTypeVar extracts the variable name a missing_type diagnostic
// complains about ("variable \"w_0\" has no type declaration; …").
var missingTypeVar = regexp.MustCompile(`variable "([^"]+)"`)

// TestLintClaimParse is the B0 gate: every prop-position claim literal
// lexes and parses in its family scope. Type-stage failures and
// term-position literals (a.Term) are census-only — see the file
// header.
func TestLintClaimParse(t *testing.T) {
	env := claimLintEnv()
	scopes := newClaimScopeCache(env)
	famByDir := claimFamilyByDir()
	col := collectClaimSites(t)
	knownNames := buildClaimKnownNames(col, scopes, famByDir)

	// Instrument guard: the gate must be ABLE to fire (a filter matching
	// nothing proves nothing). A malformed text through the same path
	// corpus literals take must yield a syntax-stage error.
	if res, panicked := parseClaimSite(&dsl.ParseScope{}, claimSite{verb: "Have", text: "∀x:num. x + ("}); panicked == "" &&
		(len(res.Errors) == 0 || !claimSyntaxCodes[res.Errors[0].Code]) {
		t.Fatalf("instrument guard: malformed probe text did not produce a syntax-stage error (got %v)", res.Errors)
	}

	var propSites, termSites int
	typeStage := map[string]int{}
	var termFailures, unknownVarCensus []string
	for _, s := range col.sites {
		scope := scopes.scope(famByDir[s.dir])
		res, panicked := parseClaimSite(scope, s)
		errStr := claimErrString(res, panicked)
		if s.verb == "Term" {
			termSites++
			if errStr != "" {
				termFailures = append(termFailures,
					fmt.Sprintf("%s:%d: a.Term(%q): %s", s.file, s.line, s.text, errStr))
			}
			continue
		}
		propSites++
		if errStr == "" {
			continue
		}
		if panicked != "" || claimSyntaxCodes[res.Errors[0].Code] {
			t.Errorf("%s:%d: %s claim %q does not lex/parse: %s",
				s.file, s.line, s.verb, s.text, errStr)
			continue
		}
		// Type stage: needs the runtime scope — not gated.
		e := res.Errors[0]
		typeStage[e.Code]++
		if e.Code == dsl.CodeMissingType {
			if m := missingTypeVar.FindStringSubmatch(e.Message); m != nil && !knownNames.known(s, m[1]) {
				unknownVarCensus = append(unknownVarCensus,
					fmt.Sprintf("%s:%d: %s claim %q: untyped variable %q is not a known name of the file "+
						"(no Go declaration, headline binder or vocab var matches it or its SurfaceBase) — typo?",
						s.file, s.line, s.verb, s.text, m[1]))
			}
		}
	}
	t.Logf("B0: %d prop-position literals (syntax-gated), %d term-position literals (census)", propSites, termSites)
	for class, n := range col.skips {
		t.Logf("B0 skip: %-58s %4d", class, n)
	}
	for code, n := range typeStage {
		t.Logf("B0 type-stage (not gated, needs runtime scope): %-20s %4d", code, n)
	}
	for _, f := range unknownVarCensus {
		t.Logf("B0 unknown-variable census: %s", f)
	}
	for _, f := range termFailures {
		t.Logf("B0 term census: %s", f)
	}
}

// ---------------------------------------------------------------------------
// B0 census — suspicious applied heads
// ---------------------------------------------------------------------------

// collectGoDeclaredNames harvests every identifier a file's Go source
// declares — closure/function parameters, := and = assignment targets,
// var/const names. Statement binders reach claim texts through exactly
// these (the binder-closure parameter lint keeps them aligned), so the
// set is the census's "known to the file" baseline.
func collectGoDeclaredNames(af *ast.File) map[string]bool {
	names := map[string]bool{}
	addFields := func(fl *ast.FieldList) {
		if fl == nil {
			return
		}
		for _, f := range fl.List {
			for _, nm := range f.Names {
				names[nm.Name] = true
			}
		}
	}
	ast.Inspect(af, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit:
			addFields(n.Type.Params)
		case *ast.FuncDecl:
			addFields(n.Type.Params)
			addFields(n.Recv)
		case *ast.StructType:
			addFields(n.Fields) // prf-struct fields carry minted-var names
		case *ast.KeyValueExpr:
			if id, ok := n.Key.(*ast.Ident); ok {
				names[id.Name] = true // composite-literal field keys
			}
		case *ast.AssignStmt:
			for _, lhs := range n.Lhs {
				if id, ok := lhs.(*ast.Ident); ok {
					names[id.Name] = true
				}
			}
		case *ast.ValueSpec:
			for _, nm := range n.Names {
				names[nm.Name] = true
			}
		}
		return true
	})
	return names
}

// collectBinderNames adds every binder name (λ and quantifier — both
// walk through core.AbsTerm) of the prop's terms to out.
func collectBinderNames(p core.Prop, out map[string]bool) {
	var walk func(t core.Term)
	walk = func(t core.Term) {
		switch tt := t.Core().(type) {
		case core.AppliedTerm:
			walk(tt.Fun())
			walk(tt.Arg())
		case core.AbsTerm:
			out[string(tt.Var().Name())] = true
			walk(tt.Body())
		}
	}
	pp := p.AsProp()
	for i := 0; i < pp.NumHyps(); i++ {
		walk(pp.Hyp(i))
	}
	walk(pp.Conclusion())
}

// appliedFreeVarHeads returns the names of variables applied as a
// function head while FREE at that occurrence — the shape a typo'd
// constant name parses into.
func appliedFreeVarHeads(p core.Prop) map[string]bool {
	heads := map[string]bool{}
	bound := map[string]int{}
	var walk func(t core.Term)
	walk = func(t core.Term) {
		switch tt := t.Core().(type) {
		case core.AppliedTerm:
			if v, ok := tt.Fun().Core().(core.VarTerm); ok && bound[string(v.Name())] == 0 {
				heads[string(v.Name())] = true
			}
			walk(tt.Fun())
			walk(tt.Arg())
		case core.AbsTerm:
			n := string(tt.Var().Name())
			bound[n]++
			walk(tt.Body())
			bound[n]--
		}
	}
	pp := p.AsProp()
	for i := 0; i < pp.NumHyps(); i++ {
		walk(pp.Hyp(i))
	}
	walk(pp.Conclusion())
	return heads
}

// claimKnownNames answers "is this claim-text variable name accounted
// for?" — the exclusion set shared by the applied-head census and the
// missing_type census. Per file: Go-declared identifiers (statement
// binders reach claims through closure params and := targets — the
// binder-closure lint keeps them aligned) plus binders of the file's
// HEADLINE literals (statement binders; a headline's free names are
// deliberately NOT harvested — a headline's own typo must not
// whitelist itself); per family: the vocab's declared standard frees.
// Every check also tries proof.SurfaceBase — the mint-convention
// inverse — so `x`, `x₀` and `xʹ` all resolve to a declared `x`.
type claimKnownNames struct {
	scopes          *claimScopeCache
	famByDir        map[string]*registry.Family
	goNames         map[string]map[string]bool
	headlineBinders map[string]map[string]bool
}

func buildClaimKnownNames(col *claimCollection, scopes *claimScopeCache, famByDir map[string]*registry.Family) *claimKnownNames {
	k := &claimKnownNames{
		scopes:          scopes,
		famByDir:        famByDir,
		goNames:         map[string]map[string]bool{},
		headlineBinders: map[string]map[string]bool{},
	}
	for f, af := range col.asts {
		k.goNames[f] = collectGoDeclaredNames(af)
		k.headlineBinders[f] = map[string]bool{}
	}
	for _, s := range col.sites {
		if !claimHeadlineVerbs[s.verb] {
			continue
		}
		res, panicked := parseClaimSite(scopes.scope(famByDir[s.dir]), s)
		if panicked != "" || len(res.Errors) > 0 || res.Prop == nil {
			continue
		}
		collectBinderNames(res.Prop, k.headlineBinders[s.file])
	}
	return k
}

func (k *claimKnownNames) known(s claimSite, name string) bool {
	try := func(n string) bool {
		if k.goNames[s.file][n] || k.headlineBinders[s.file][n] {
			return true
		}
		return k.scopes.vocabVars(k.famByDir[s.dir])[n]
	}
	if try(name) {
		return true
	}
	if base := proof.SurfaceBase(name); base != name && try(base) {
		return true
	}
	// The ASCII Go spelling of a subscripted mint: claim `d₀`
	// (normalized d_0) is held in a Go variable/field named d0.
	if flat := strings.ReplaceAll(name, "_", ""); flat != name && try(flat) {
		return true
	}
	return false
}

// TestClaimAppliedHeadCensus reports claim-text names applied as a
// function that resolved to a fresh free variable and are not accounted
// for by any known-name source. Report-only (t.Logf), per the file
// header — read with go test -v -run TestClaimAppliedHeadCensus.
func TestClaimAppliedHeadCensus(t *testing.T) {
	env := claimLintEnv()
	scopes := newClaimScopeCache(env)
	famByDir := claimFamilyByDir()
	col := collectClaimSites(t)
	knownNames := buildClaimKnownNames(col, scopes, famByDir)

	// Instrument guard: an applied unknown name must be detected.
	probe := dsl.ParsePropText("zzNoSuchConst(0) = 0")
	if len(probe.Errors) > 0 || !appliedFreeVarHeads(probe.Prop)["zzNoSuchConst"] {
		t.Fatalf("instrument guard: appliedFreeVarHeads missed an applied free-variable head (errors: %v)", probe.Errors)
	}

	var findings []string
	for _, s := range col.sites {
		if s.verb == "Term" {
			continue
		}
		scope := scopes.scope(famByDir[s.dir])
		res, panicked := parseClaimSite(scope, s)
		if panicked != "" || len(res.Errors) > 0 || res.Prop == nil {
			continue
		}
		for name := range appliedFreeVarHeads(res.Prop) {
			if knownNames.known(s, name) {
				continue
			}
			findings = append(findings,
				fmt.Sprintf("%s:%d: %s claim applies %q as a function, but it parsed as a fresh free variable "+
					"(not a const, not a binder, not a known name) — typo'd constant name?",
					s.file, s.line, s.verb, name))
		}
	}
	sort.Strings(findings)
	for _, f := range findings {
		t.Logf("%s", f)
	}
	t.Logf("suspicious applied heads: %d", len(findings))
}

// ---------------------------------------------------------------------------
// B1 — headline check
// ---------------------------------------------------------------------------

func safeStatement(e *registry.ProofEntry) (p core.Prop, panicked string) {
	defer func() {
		if r := recover(); r != nil {
			panicked = trimPanic(r)
		}
	}()
	return e.Statement().Prop, ""
}

// TestLintClaimHeadline is the B1 gate: every entry's statement
// elaborates. A headline that does not parse under its family
// vocabulary, or that states a sequent, is an authoring error the
// harness would otherwise reach only at replay.
func TestLintClaimHeadline(t *testing.T) {
	checked := 0
	for _, e := range registry.All() {
		if _, panicked := safeStatement(e); panicked != "" {
			t.Errorf("%s: Statement panics: %s", e.Name, panicked)
			continue
		}
		checked++
	}
	t.Logf("B1: %d statements elaborated", checked)
}

// ---------------------------------------------------------------------------
// B2 — ground-cite witness arity
// ---------------------------------------------------------------------------

// chapterImportPrefix locates a family package import; the suffix is
// the directory relative to this package.
const chapterImportPrefix = "github.com/euc-ai/xugo/library/proofs/"

// citeVerbs: the package-level ground-cite constructors. Matched only
// as BARE identifiers (the zz_aliases surface) — the method form
// `f.At(w…)` is a *SelectorExpr and never reaches the check.
var citeVerbs = map[string]bool{"At": true, "Cite": true, "CiteKeep": true}

type depArity struct {
	skip    bool // statement is a sequent, or does not elaborate — not statically checkable
	stated  int  // leading ∀ run of the headline as written
	install int  // leading ∀ run of Normalize(headline) — the install form
}

func leadingForallCount(t core.Term) int {
	n := 0
	for {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			return n
		}
		n++
		t = abs.Body()
	}
}

func depArityFor(e *registry.ProofEntry, cache map[*registry.ProofEntry]depArity) depArity {
	if a, ok := cache[e]; ok {
		return a
	}
	a := depArity{skip: true}
	st, panicked := safeStatement(e)
	if panicked == "" && st.NumHyps() == 0 {
		norm, _ := propext.Normalize(st)
		a = depArity{
			stated:  leadingForallCount(st.Conclusion()),
			install: leadingForallCount(norm.Conclusion()),
		}
	}
	cache[e] = a
	return a
}

// TestLintClaimCiteWitnessArity is the B2 gate: a ground cite of a
// statically-resolved registry entry carries at most as many witnesses
// as the dep's install form has leading ∀ slots.
func TestLintClaimCiteWitnessArity(t *testing.T) {
	famByDir := claimFamilyByDir()
	col := collectClaimSites(t) // reuse the parsed family-file ASTs

	// Instrument guard: the ∀-counter must count.
	probe := dsl.ParsePropText("∀x:num. ∀y:num. x = y")
	if len(probe.Errors) > 0 || leadingForallCount(probe.Prop.Conclusion()) != 2 {
		t.Fatalf("instrument guard: leadingForallCount did not read 2 off a ∀∀ statement")
	}

	// Pass 1: entry vars. `var X = family.Add(registry.ProofEntry{Name:
	// "<bare>", …})` maps (dir, X) → the registered entry
	// (<short>.<bare> — Family.Add's prefixing rule).
	entryByDirVar := map[string]map[string]*registry.ProofEntry{}
	pkgNameByDir := map[string]string{}
	for f, af := range col.asts {
		dir := path.Dir(filepath.ToSlash(f))
		fam := famByDir[dir]
		if fam == nil {
			continue
		}
		pkgNameByDir[dir] = af.Name.Name
		short := path.Base(fam.Name)
		for _, d := range af.Decls {
			gd, ok := d.(*ast.GenDecl)
			if !ok || gd.Tok != token.VAR {
				continue
			}
			for _, spec := range gd.Specs {
				vs, ok := spec.(*ast.ValueSpec)
				if !ok || len(vs.Names) != 1 || len(vs.Values) != 1 {
					continue
				}
				val := vs.Values[0]
				// Every entry is generator-wrapped — `var Sing =
				// singThm{family.Add(…)}` — so the value is a composite
				// literal one level above the call. Without this unwrap
				// B2 sees a CompositeLit, `continue`s, and checks zero
				// ground cites corpus-wide; collectEntrySites unwraps
				// the same way.
				if wl, ok := val.(*ast.CompositeLit); ok && len(wl.Elts) == 1 {
					if inner, ok := wl.Elts[0].(*ast.CallExpr); ok {
						val = inner
					}
				}
				call, ok := val.(*ast.CallExpr)
				if !ok {
					continue
				}
				sel, ok := call.Fun.(*ast.SelectorExpr)
				if !ok || sel.Sel.Name != "Add" || len(call.Args) != 1 {
					continue
				}
				cl, ok := call.Args[0].(*ast.CompositeLit)
				if !ok {
					continue
				}
				for _, elt := range cl.Elts {
					kv, ok := elt.(*ast.KeyValueExpr)
					if !ok {
						continue
					}
					key, ok := kv.Key.(*ast.Ident)
					if !ok || key.Name != "Name" {
						continue
					}
					lit, ok := kv.Value.(*ast.BasicLit)
					if !ok || lit.Kind != token.STRING {
						continue
					}
					bare, err := strconv.Unquote(lit.Value)
					if err != nil {
						continue
					}
					if e, ok := registry.ByName(short + "." + bare); ok {
						if entryByDirVar[dir] == nil {
							entryByDirVar[dir] = map[string]*registry.ProofEntry{}
						}
						entryByDirVar[dir][vs.Names[0].Name] = e
					}
				}
			}
		}
	}

	// Pass 2: use sites.
	arity := map[*registry.ProofEntry]depArity{}
	resolved, skippedNilHeadline, censusPrenex := 0, 0, 0
	files := make([]string, 0, len(col.asts))
	for f := range col.asts {
		files = append(files, f)
	}
	sort.Strings(files)
	for _, f := range files {
		af := col.asts[f]
		dir := path.Dir(filepath.ToSlash(f))
		if famByDir[dir] == nil {
			continue
		}
		// Imports: local name → corpus-relative dir.
		importDir := map[string]string{}
		for _, imp := range af.Imports {
			p, err := strconv.Unquote(imp.Path.Value)
			if err != nil || !strings.HasPrefix(p, chapterImportPrefix) {
				continue
			}
			rel := filepath.Join(corpusRoot, filepath.FromSlash(strings.TrimPrefix(p, chapterImportPrefix)))
			local := path.Base(rel)
			if name, ok := pkgNameByDir[rel]; ok {
				local = name
			}
			if imp.Name != nil {
				if imp.Name.Name == "_" || imp.Name.Name == "." {
					continue
				}
				local = imp.Name.Name
			}
			importDir[local] = rel
		}
		ast.Inspect(af, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok || call.Ellipsis.IsValid() || len(call.Args) < 2 {
				return true
			}
			fn, ok := call.Fun.(*ast.Ident)
			if !ok || !citeVerbs[fn.Name] {
				return true
			}
			var entry *registry.ProofEntry
			switch dep := call.Args[0].(type) {
			case *ast.Ident:
				entry = entryByDirVar[dir][dep.Name]
			case *ast.SelectorExpr:
				if x, ok := dep.X.(*ast.Ident); ok {
					if rel, ok := importDir[x.Name]; ok {
						entry = entryByDirVar[rel][dep.Sel.Name]
					}
				}
			case *ast.BasicLit:
				if dep.Kind == token.STRING {
					if name, err := strconv.Unquote(dep.Value); err == nil {
						if e, ok := registry.ByName(name); ok {
							entry = e
						}
					}
				}
			}
			if entry == nil {
				return true // not statically resolvable — skip silently
			}
			a := depArityFor(entry, arity)
			if a.skip {
				skippedNilHeadline++
				return true
			}
			resolved++
			k := len(call.Args) - 1
			pos := col.fset.Position(call.Pos())
			if k > a.install {
				t.Errorf("%s:%d: %s(%s, …) carries %d witnesses but the dep's install form "+
					"(Normalize of its headline) has only %d leading ∀ slot(s) — the Specialize "+
					"would fail at replay", f, pos.Line, fn.Name, entry.Name, k, a.install)
			} else if k > a.stated {
				censusPrenex++
				t.Logf("%s:%d: %s(%s, …) grounds %d witnesses; the stated headline's leading run is %d "+
					"but Normalize prenexes to %d slots — legal", f, pos.Line, fn.Name, entry.Name, k, a.stated, a.install)
			}
			return true
		})
	}
	t.Logf("B2: %d ground cites resolved and checked; %d skipped (dep headline not statically known); %d within prenexed-but-not-stated slots",
		resolved, skippedNilHeadline, censusPrenex)
}

// ---------------------------------------------------------------------------
// B3 — a claim's text is data
// ---------------------------------------------------------------------------

// claimTextShape is what stands at a claim verb's text position.
type claimTextShape int

const (
	claimTextLiteral      claimTextShape = iota // one string literal
	claimTextSplitLiteral                       // string literals joined by +
	claimTextStatement                          // a Statement{…} literal
	claimTextSpliced                            // a + whose operands are not all string literals
	claimTextConst                              // a package string const
	claimTextHelper                             // a call of a package function returning string
	claimTextValue                              // anything else: a Prop, a Fact, a Term value
)

var claimTextShapeNames = map[claimTextShape]string{
	claimTextLiteral: "one literal", claimTextSplitLiteral: "literals joined by +",
	claimTextStatement: "Statement literal", claimTextSpliced: "spliced from Go strings by +",
	claimTextConst: "package string const", claimTextHelper: "string helper call",
	claimTextValue: "a value",
}

// joinedStringLiterals is the text of string literals joined by `+`,
// parenthesized or not; false where any operand is something else.
func joinedStringLiterals(e ast.Expr) (string, bool) {
	switch e := e.(type) {
	case *ast.BasicLit:
		if e.Kind != token.STRING {
			return "", false
		}
		s, err := strconv.Unquote(e.Value)
		return s, err == nil
	case *ast.ParenExpr:
		return joinedStringLiterals(e.X)
	case *ast.BinaryExpr:
		if e.Op != token.ADD {
			return "", false
		}
		left, ok := joinedStringLiterals(e.X)
		if !ok {
			return "", false
		}
		right, ok := joinedStringLiterals(e.Y)
		if !ok {
			return "", false
		}
		return left + right, true
	}
	return "", false
}

// collectStringHelpers harvests a file's package-level functions whose
// one result is a string — the helpers a text is assembled by.
func collectStringHelpers(af *ast.File, out map[string]bool) {
	for _, d := range af.Decls {
		fn, ok := d.(*ast.FuncDecl)
		if !ok || fn.Recv != nil || fn.Type.Results == nil || len(fn.Type.Results.List) != 1 {
			continue
		}
		result := fn.Type.Results.List[0]
		if len(result.Names) > 1 {
			continue
		}
		if id, isIdent := result.Type.(*ast.Ident); isIdent && id.Name == "string" {
			out[fn.Name.Name] = true
		}
	}
}

// shapeOfClaimText classifies a claim verb's text argument.
func shapeOfClaimText(arg ast.Expr, consts map[string]string, helpers map[string]bool) claimTextShape {
	switch e := arg.(type) {
	case *ast.BasicLit:
		if e.Kind == token.STRING {
			return claimTextLiteral
		}
	case *ast.ParenExpr, *ast.BinaryExpr:
		if _, ok := joinedStringLiterals(e); ok {
			return claimTextSplitLiteral
		}
		if be, isBinary := e.(*ast.BinaryExpr); isBinary && be.Op == token.ADD {
			// A `+` at a text position is a string concatenation.
			return claimTextSpliced
		}
	case *ast.Ident:
		if _, isConst := consts[e.Name]; isConst {
			return claimTextConst
		}
	case *ast.CallExpr:
		if id, isIdent := e.Fun.(*ast.Ident); isIdent && helpers[id.Name] {
			return claimTextHelper
		}
	case *ast.CompositeLit:
		if _, ok := statementLiteral(e); ok {
			return claimTextStatement
		}
	}
	return claimTextValue
}

// premiseShaped reports whether a claim text has a premise: under its
// leading ∀-prefix its root is an implication — the standard form
// `∀xs. H₁ ∧ … ∧ Hₙ ⇒ C` (dsl.SplitStatement reads the hypotheses), or
// a curried `H₁ ⇒ H₂ ⇒ C`, which splits no hypothesis and is what
// dsl.StandardParts refuses. A text with no premise it accepts.
func premiseShaped(text string) bool {
	s, ok := dsl.SplitStatement(text)
	if !ok {
		return false
	}
	if len(s.Hypotheses) > 0 {
		return true
	}
	_, err := dsl.StandardParts(text)
	return err != nil
}

// TestLintClaimTextIsData is the B3 gate: the text a claim verb reads
// (a.Have / a.Obtain … a.Obtain5 / a.ObtainChosen / a.Hyp
// and their typed twins, the term texts of a.Term / a.TermAs) is
// written as data, as a member's statement is (chapter_constitution.md
// §"The section boundary is a binding form": a statement's text is a
// literal, a `Statement` literal or a door's — never Go assembled from
// constants and helpers — and a claim's with it). Gated:
//
//   - a `Statement{…}` at a claim declares no abbreviations: a claim
//     reads the member's table, and the claim door refuses a table of
//     the claim's own;
//   - a text ASSEMBLED from Go strings — a `+` over a name or a call,
//     a const or a local string used bare, a string helper's or a local
//     builder's call (claim_text_assembly_test.go) — that the base
//     commit does not hold (XUGO_GATE_BASE; HEAD unset): the term that
//     recurs is an entry of the member's Abbreviations table, spelled
//     `«Name»`, never a const spliced in. The sites the base holds are
//     the sweep's, counted and not refused; a site is the same across
//     commits when its file and its argument, whitespace aside, are.
//
// Whether a claim with a premise is the one string or parts is its
// width's (TestLintClaimPartsByWidth), a split text's as a single
// literal's; a statement with a premise is in parts
// (TestLintStatementInParts).
//
// Census (t.Logf), not gated: the shape of every claim text, and the
// split literals kept.
func TestLintClaimTextIsData(t *testing.T) {
	fset := token.NewFileSet()
	byDir := map[string][]string{}
	for _, f := range chapterProofFiles(t) {
		dir := path.Dir(filepath.ToSlash(f))
		byDir[dir] = append(byDir[dir], f)
	}
	dirs := make([]string, 0, len(byDir))
	for dir := range byDir {
		dirs = append(dirs, dir)
	}
	sort.Strings(dirs)

	shapes := map[string]int{}
	var examples []string
	const examplesShown = 12
	for _, dir := range dirs {
		files := byDir[dir]
		consts := map[string]string{}
		helpers := map[string]bool{}
		asts := make([]*ast.File, 0, len(files))
		for _, f := range files {
			af, err := parser.ParseFile(fset, f, nil, 0)
			if err != nil {
				t.Fatalf("parse %s: %v", f, err)
			}
			asts = append(asts, af)
			collectStringHelpers(af, helpers)
		}
		collectStringConsts(asts, consts)
		for i, af := range asts {
			f := files[i]
			ast.Inspect(af, func(n ast.Node) bool {
				call, ok := n.(*ast.CallExpr)
				if !ok {
					return true
				}
				verb, arg, ok := claimTextArg(call)
				statement := false
				if !ok {
					verb, arg, ok = statementTextArg(call)
					statement = true
				}
				if !ok {
					return true
				}
				shape := shapeOfClaimText(arg, consts, helpers)
				pos := fset.Position(arg.Pos())
				where := fmt.Sprintf("%s:%d: %s", f, pos.Line, verb)
				switch shape {
				case claimTextStatement:
					stmt, _ := statementLiteral(arg)
					if !statement && len(stmt.Abbrev) > 0 {
						t.Errorf("%s claim's Statement declares abbreviations — a claim reads the member's table; "+
							"declare «%s» in the member's statement", where, stmt.Abbrev[0].Name)
						return true
					}
				case claimTextSpliced, claimTextConst, claimTextHelper:
					if len(examples) < examplesShown {
						examples = append(examples, where+" claim text is "+claimTextShapeNames[shape])
					}
				}
				shapes[claimTextShapeNames[shape]]++
				return true
			})
		}
	}
	names := make([]string, 0, len(shapes))
	for name := range shapes {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		t.Logf("B3: claim texts written as %-30s %5d", name, shapes[name])
	}
	for _, example := range examples {
		t.Logf("B3 census (not gated): %s", example)
	}

	t.Run("no claim text assembled from Go strings is added", func(t *testing.T) {
		// Instrument guard: the reader must find the one assembled text
		// a snippet holds, or the gate below proves nothing.
		if guard := assembledClaimTextsOf(t, "guard.go", "package x\n\nfunc f() {\n\tx := \"a\"\n\ta.Have(\"l\", \"p ∈ \"+x, nil)\n}\n", nil); len(guard) != 1 {
			t.Fatalf("instrument guard: the reader found %d assembled texts in a snippet holding one", len(guard))
		}
		repo, base := gateBase(t)
		var files []string
		for _, dir := range dirs {
			files = append(files, byDir[dir]...)
		}
		atBase := chapterFilesAtBase(t, repo, base, files)
		head, _ := assembledSitesByDir(t, dirs, byDir, func(f string) ([]byte, bool) {
			src, err := os.ReadFile(f)
			return src, err == nil
		})
		atBaseSites, unparsable := assembledSitesByDir(t, dirs, byDir, func(f string) ([]byte, bool) {
			src, ok := atBase[f]
			return src, ok
		})
		held := map[string]int{}
		for _, s := range atBaseSites {
			held[s.identity()]++
		}
		added := 0
		for _, s := range head {
			if unparsable[s.file] {
				continue // the base's copy of the file reads as nothing; nothing in it is refused
			}
			if held[s.identity()] > 0 {
				held[s.identity()]--
				continue
			}
			added++
			t.Errorf("%s:%d: %s text is %s — a statement's text and a claim's are data: one literal or a Statement literal "+
				"(chapter_constitution.md §\"Stable authoring rules\"); a term it shares with other texts is an entry of the "+
				"member's Abbrev table, or of the chapter's (Family.WithAbbrev), spelled «Name» in every text (engine/xugo-engine.md §\"Abbreviations\"), never a const spliced in. "+
				"The %d such sites %s holds are the sweep's; this one is new.\n  %s",
				chapterRel(s.file), s.line, s.verb, s.how, len(atBaseSites), base, s.shown())
		}
		for f := range unparsable {
			t.Logf("%s at %s does not parse — its texts are not compared", chapterRel(f), base)
		}
		t.Logf("B3: %d statement and claim texts assembled from Go strings in the tree, %d at %s (the sweep's), %d added", len(head), len(atBaseSites), base, added)
	})
}

// assembledSitesByDir reads every chapter proof file through read — the
// tree's copy, or a commit's — and returns the claim texts assembled
// from Go strings, with the package consts and string helpers of each
// directory read from its files at the same source, and the consts of
// the chapter packages a file imports read the same way; and the files
// whose source does not parse, which contribute no site.
func assembledSitesByDir(t *testing.T, dirs []string, byDir map[string][]string, read func(file string) ([]byte, bool)) ([]assembledSite, map[string]bool) {
	t.Helper()
	fset := token.NewFileSet()
	type parsed struct {
		file string
		src  []byte
		af   *ast.File
	}
	unparsable := map[string]bool{}
	parsedDirs := map[string][]parsed{}
	parseDir := func(dir string) []parsed {
		if files, done := parsedDirs[dir]; done {
			return files
		}
		var files []parsed
		for _, f := range byDir[dir] {
			src, ok := read(f)
			if !ok {
				continue
			}
			af, err := parser.ParseFile(fset, f, src, 0)
			if err != nil {
				unparsable[f] = true
				continue
			}
			files = append(files, parsed{f, src, af})
		}
		parsedDirs[dir] = files
		return files
	}
	constsByDir := map[string]map[string]string{}
	constsOf := func(dir string) map[string]string {
		if consts, done := constsByDir[dir]; done {
			return consts
		}
		files := parseDir(dir)
		afs := make([]*ast.File, len(files))
		for i, p := range files {
			afs[i] = p.af
		}
		consts := map[string]string{}
		collectStringConsts(afs, consts)
		constsByDir[dir] = consts
		return consts
	}
	var sites []assembledSite
	for _, dir := range dirs {
		files := parseDir(dir)
		consts := constsOf(dir)
		helpers := map[string]bool{}
		for _, p := range files {
			collectStringHelpers(p.af, helpers)
		}
		for _, p := range files {
			imported := map[string]map[string]string{}
			for name, importDir := range chapterImports(p.af) {
				if _, known := byDir[importDir]; known {
					imported[name] = constsOf(importDir)
				}
			}
			sites = append(sites, assembledClaimTexts(fset, p.af, p.src, p.file, consts, helpers, imported)...)
		}
	}
	return sites, unparsable
}

// chapterImports is a file's imports of chapter packages, by the name
// the file uses for each, as the directory the package's files are in
// (the key chapterProofFiles' dirs use).
func chapterImports(af *ast.File) map[string]string {
	out := map[string]string{}
	for _, imp := range af.Imports {
		importPath, err := strconv.Unquote(imp.Path.Value)
		if err != nil || !strings.HasPrefix(importPath, chapterImportPrefix) {
			continue
		}
		rel := strings.TrimPrefix(importPath, chapterImportPrefix)
		name := path.Base(rel)
		if imp.Name != nil {
			name = imp.Name.Name
		}
		out[name] = filepath.ToSlash(filepath.Join(corpusRoot, filepath.FromSlash(rel)))
	}
	return out
}

// assembledClaimTextsOf reads one source as a file of its own: its
// package consts and helpers are its own; imported is the consts of
// the chapter packages it imports, by the name it uses for each.
func assembledClaimTextsOf(t *testing.T, file, source string, imported map[string]map[string]string) []assembledSite {
	t.Helper()
	fset := token.NewFileSet()
	af, err := parser.ParseFile(fset, file, source, 0)
	if err != nil {
		t.Fatalf("parse %s: %v", file, err)
	}
	consts := map[string]string{}
	helpers := map[string]bool{}
	collectStringConsts([]*ast.File{af}, consts)
	collectStringHelpers(af, helpers)
	return assembledClaimTexts(fset, af, []byte(source), file, consts, helpers, imported)
}
