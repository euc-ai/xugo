// claim_scope_test.go — the abbreviation tables a text of a proof file
// reads under, as the claim lints rebuild them from the source.
//
// At replay a text parses under the script's table at the moment its
// door runs: the chapter's (registry.Family.WithAbbrev), the member's
// (registry.installAbbreviations) and the entries of each section open
// around it (Script.withSectionAbbreviations), read as one table.
// Inside one statement's call that is the nesting of the source. A func
// of the package runs under the table of whatever calls it — the
// Sections script a member names, a lemma written as its own func, a
// reader a section's closure calls — so its texts read the entries
// every statement that reaches it declares with one text.
package gates

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"slices"
	"sort"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
)

// abbreviationSpan is a stretch of source whose texts parse under one
// table: a statement's call — a headline constructor's, a structure
// door's Law — or the body of a func that statements reach. Which
// binders a text may bind over an entry's names is the text's own (a
// site's exempt), not the span's: the statement's leading binders are
// exempt for the statement alone, and a claim inside binds none of
// them.
type abbreviationSpan struct {
	from, to token.Pos
	table    *dsl.AbbreviationTable // nil when no statement in reach declares one
	err      error                  // the tables in reach do not merge
	// partial holds the names that one statement reaching the span's
	// func declares and another does not, or declares with another
	// text, each with the refusal of a text that spells it.
	partial map[string]string
}

// refusal is why text does not read at the span, before any parse: the
// tables in reach do not merge, or the text spells a name only some of
// the statements that reach it declare. Empty where it may be parsed.
func (span *abbreviationSpan) refusal(text string) string {
	if span == nil {
		return ""
	}
	if span.err != nil {
		return span.err.Error()
	}
	if len(span.partial) == 0 {
		return ""
	}
	for _, name := range dsl.AbbreviationNames(text) {
		if why, ok := span.partial[name]; ok {
			return why
		}
	}
	return ""
}

// abbreviationsAt is the innermost span enclosing pos, if any.
func abbreviationsAt(spans []abbreviationSpan, pos token.Pos) *abbreviationSpan {
	var at *abbreviationSpan
	for i := range spans {
		if spans[i].from <= pos && pos < spans[i].to {
			at = &spans[i]
		}
	}
	return at
}

// abbreviationSpans is packageAbbreviationSpans for a package of the
// one file af.
func abbreviationSpans(af *ast.File, consts map[string]string, chapter dsl.Abbrev) []abbreviationSpan {
	return packageAbbreviationSpans([]*ast.File{af}, consts, chapter)[af]
}

// packageAbbreviationSpans lists, for each file of one family's
// package, its spans in source order, an enclosing span before the
// spans inside it. The chapter's table (nil for none) spans every file
// as the outermost. A statement's call reads the chapter's entries,
// those of the func it stands in, those of the calls enclosing it in
// the source and its own, as one table. A func's body reads the
// chapter's entries and the func's.
//
// A func's entries are the ones every reference to it stands under,
// with one text: a reference stands under the entries of the statement
// calls enclosing it and of the func it is written in. Only a func a
// proof is written in has any — package level, no receiver, unexported:
// an exported func, a method and init are reached from outside the
// package's statements, so a reference in one stands under the calls
// enclosing it alone.
func packageAbbreviationSpans(files []*ast.File, consts map[string]string, chapter dsl.Abbrev) map[*ast.File][]abbreviationSpan {
	g := &scopeGraph{
		consts:     consts,
		funcs:      map[string]bool{},
		refs:       map[string][]scopeRef{},
		statements: map[*ast.File][]scopeStatement{},
	}
	for _, af := range files {
		for _, d := range af.Decls {
			if name, ok := proofFuncName(d); ok {
				g.funcs[name] = true
			}
		}
	}
	for _, af := range files {
		for _, d := range af.Decls {
			host, _ := proofFuncName(d)
			switch d := d.(type) {
			case *ast.FuncDecl:
				g.walk(af, d, host, d.Name.Name)
			case *ast.GenDecl:
				for _, spec := range d.Specs {
					label := "a declaration"
					if vs, ok := spec.(*ast.ValueSpec); ok && len(vs.Names) > 0 {
						label = vs.Names[0].Name
					}
					g.walk(af, spec, "", label)
				}
			}
		}
	}
	g.solve()

	out := make(map[*ast.File][]abbreviationSpan, len(files))
	for _, af := range files {
		var spans []abbreviationSpan
		if len(chapter) > 0 {
			spans = append(spans, tableSpan(af.Pos(), af.End(), chapter))
		}
		for _, d := range af.Decls {
			name, ok := proofFuncName(d)
			if !ok || len(g.entries[name]) == 0 && len(g.partial[name]) == 0 {
				continue
			}
			span := tableSpan(d.Pos(), d.End(), joinEntries(chapter, g.entries[name]))
			span.partial = g.partial[name]
			spans = append(spans, span)
		}
		for _, st := range g.statements[af] {
			span := tableSpan(st.from, st.to, joinEntries(chapter, g.entries[st.host], st.lexical))
			span.partial = g.partial[st.host]
			for _, e := range st.lexical {
				if _, some := span.partial[entryName(e)]; some && span.err == nil {
					span.err = fmt.Errorf("abbreviation «%s» is declared twice: here, and by a statement that reaches %s — one name, one meaning",
						entryName(e), st.host)
				}
			}
			spans = append(spans, span)
		}
		sort.SliceStable(spans, func(i, j int) bool {
			if spans[i].from != spans[j].from {
				return spans[i].from < spans[j].from
			}
			return spans[i].to > spans[j].to
		})
		out[af] = spans
	}
	return out
}

// tableSpan is the span from..to reading entries as one table.
func tableSpan(from, to token.Pos, entries dsl.Abbrev) abbreviationSpan {
	span := abbreviationSpan{from: from, to: to}
	if len(entries) > 0 {
		span.table, span.err = dsl.ParseAbbreviations(entries)
	}
	return span
}

func joinEntries(lists ...dsl.Abbrev) dsl.Abbrev {
	var out dsl.Abbrev
	for _, list := range lists {
		out = append(out, list...)
	}
	return out
}

// entryName and entryText are an entry as a table holds it
// (dsl.ParseAbbreviations), the form two entries compare in.
func entryName(e dsl.Abbreviation) string { return strings.TrimSpace(e.Name) }
func entryText(e dsl.Abbreviation) string { return dsl.OneLine(e.Text) }

// proofFuncName is the name of a func whose texts read under the
// statements that reach it (packageAbbreviationSpans).
func proofFuncName(d ast.Decl) (string, bool) {
	fn, ok := d.(*ast.FuncDecl)
	if !ok || fn.Recv != nil || fn.Body == nil {
		return "", false
	}
	name := fn.Name.Name
	if name == "init" || name == "_" || ast.IsExported(name) {
		return "", false
	}
	return name, true
}

// scopeGraph is one package's statements and the references to its
// proof funcs, and what solve reads from them.
type scopeGraph struct {
	consts     map[string]string
	funcs      map[string]bool
	refs       map[string][]scopeRef
	statements map[*ast.File][]scopeStatement
	// entries is each reached func's table: the entries every reference
	// to it stands under. partial is the names some reference stands
	// under and entries does not hold, each with its refusal.
	entries map[string]dsl.Abbrev
	partial map[string]map[string]string
}

// scopeStatement is one statement's call: lexical is the entries of the
// calls enclosing it in the source, outermost first, then its own; host
// is the proof func it stands in, empty for none.
type scopeStatement struct {
	from, to token.Pos
	host     string
	lexical  dsl.Abbrev
}

// scopeRef is one mention of the proof func target: in the proof func
// host (empty for none), in the declaration named label, under the
// entries lexical of the statement calls enclosing it.
type scopeRef struct {
	target, host, label string
	lexical             dsl.Abbrev
}

// walk reads one package-level declaration d, a func or one spec of a
// var block, named label; host is its name where it is a proof func.
// It collects the declaration's statement calls and its references to
// the package's proof funcs. A name the declaration binds itself — a
// parameter, a := target, a var — is its own wherever it stands in the
// declaration, not the package's func.
func (g *scopeGraph) walk(af *ast.File, d ast.Node, host, label string) {
	type open struct {
		to      token.Pos
		entries dsl.Abbrev
	}
	var stack []open
	enclosing := func(pos token.Pos) dsl.Abbrev {
		for len(stack) > 0 && stack[len(stack)-1].to <= pos {
			stack = stack[:len(stack)-1]
		}
		if len(stack) == 0 {
			return nil
		}
		return stack[len(stack)-1].entries
	}
	notAName := map[*ast.Ident]bool{}
	bound := map[string]bool{}
	bind := func(e ast.Expr) {
		if id, ok := e.(*ast.Ident); ok {
			bound[id.Name] = true
			notAName[id] = true
		}
	}
	var refs []scopeRef
	ast.Inspect(d, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncDecl:
			notAName[n.Name] = true
		case *ast.SelectorExpr:
			notAName[n.Sel] = true
		case *ast.KeyValueExpr:
			if id, ok := n.Key.(*ast.Ident); ok {
				notAName[id] = true
			}
		case *ast.Field:
			for _, name := range n.Names {
				bind(name)
			}
		case *ast.ValueSpec:
			for _, name := range n.Names {
				bind(name)
			}
		case *ast.AssignStmt:
			if n.Tok == token.DEFINE {
				for _, lhs := range n.Lhs {
					bind(lhs)
				}
			}
		case *ast.RangeStmt:
			if n.Tok == token.DEFINE {
				bind(n.Key)
				bind(n.Value)
			}
		case *ast.CallExpr:
			if len(n.Args) < 2 {
				break
			}
			if verb := verbName(n); !claimHeadlineVerbs[verb] && !claimTableDoorVerbs[verb] {
				break
			}
			_, own, ok := headlineStatement(n.Args[0], g.consts)
			if !ok {
				break
			}
			entries := joinEntries(enclosing(n.Pos()), own)
			stack = append(stack, open{n.End(), entries})
			g.statements[af] = append(g.statements[af],
				scopeStatement{from: n.Pos(), to: n.End(), host: host, lexical: entries})
		case *ast.Ident:
			if g.funcs[n.Name] && !notAName[n] {
				refs = append(refs, scopeRef{target: n.Name, host: host, label: label, lexical: enclosing(n.Pos())})
			}
		}
		return true
	})
	for _, r := range refs {
		if !bound[r.target] {
			g.refs[r.target] = append(g.refs[r.target], r)
		}
	}
}

// solve reads each proof func's entries and partial names off the
// references. A func no reference reaches from a statement or from
// outside the proof funcs has none: nothing in the package calls it
// under a table.
func (g *scopeGraph) solve() {
	targets := make([]string, 0, len(g.refs))
	for name := range g.refs {
		targets = append(targets, name)
	}
	sort.Strings(targets)

	// The entries: the largest tables such that each func's is common to
	// every reference to it. A func starts unreached and its table only
	// shrinks once reached, so the rounds end.
	g.entries = map[string]dsl.Abbrev{}
	reached := map[string]bool{}
	under := func(r scopeRef) (dsl.Abbrev, bool) {
		if r.host == "" {
			return r.lexical, true
		}
		if !reached[r.host] {
			return nil, false
		}
		return joinEntries(g.entries[r.host], r.lexical), true
	}
	for changed := true; changed; {
		changed = false
		for _, name := range targets {
			var common dsl.Abbrev
			seen := false
			for _, r := range g.refs[name] {
				table, ok := under(r)
				switch {
				case !ok:
				case !seen:
					common, seen = commonEntries(table, table), true
				default:
					common = commonEntries(common, table)
				}
			}
			if seen && (!reached[name] || len(common) != len(g.entries[name])) {
				reached[name], g.entries[name] = true, common
				changed = true
			}
		}
	}

	// The partial names: every name some reference stands under, by the
	// calls enclosing it or by its host's own table and partial names,
	// that the func's entries do not hold.
	names := map[string]map[string]bool{}
	for changed := true; changed; {
		changed = false
		for _, name := range targets {
			if !reached[name] {
				continue
			}
			held := map[string]bool{}
			for _, e := range g.entries[name] {
				held[entryName(e)] = true
			}
			add := func(n string) {
				if held[n] || names[name][n] {
					return
				}
				if names[name] == nil {
					names[name] = map[string]bool{}
				}
				names[name][n] = true
				changed = true
			}
			for _, r := range g.refs[name] {
				table, ok := under(r)
				if !ok {
					continue
				}
				for _, e := range table {
					add(entryName(e))
				}
				for n := range names[r.host] {
					add(n)
				}
			}
		}
	}
	g.partial = map[string]map[string]string{}
	for name, some := range names {
		var from []string
		for _, r := range g.refs[name] {
			if _, ok := under(r); ok && r.label != name && !slices.Contains(from, r.label) {
				from = append(from, r.label)
			}
		}
		sort.Strings(from)
		g.partial[name] = map[string]string{}
		for n := range some {
			g.partial[name][n] = fmt.Sprintf("«%s» is not in every table %s is read under, or not with one text: "+
				"the func is reached from %s, and its texts read the entries every one of them gives it",
				n, name, strings.Join(from, ", "))
		}
	}
}

// commonEntries is the entries of a that b holds with the same name and
// text, in a's order, each spelling no entry of a that was dropped
// before it: an entry that reads the same under both tables. A name an
// entry spells that a does not declare is the chapter's, under both.
func commonEntries(a, b dsl.Abbrev) dsl.Abbrev {
	type key struct{ name, text string }
	in := make(map[key]bool, len(b))
	for _, e := range b {
		in[key{entryName(e), entryText(e)}] = true
	}
	declared := make(map[string]bool, len(a))
	for _, e := range a {
		declared[entryName(e)] = true
	}
	kept := map[string]bool{}
	var out dsl.Abbrev
	for _, e := range a {
		name := entryName(e)
		if kept[name] || !in[key{name, entryText(e)}] {
			continue
		}
		whole := true
		for _, inner := range dsl.AbbreviationNames(e.Text) {
			whole = whole && (kept[inner] || !declared[inner])
		}
		if whole {
			kept[name] = true
			out = append(out, e)
		}
	}
	return out
}

// scopeFixture parses src as one proof file and returns the table in
// scope at a claim, by the claim's quoted text.
func scopeFixture(t *testing.T, src string) func(claim string) *abbreviationSpan {
	t.Helper()
	fset := token.NewFileSet()
	af, err := parser.ParseFile(fset, "scope.go", src, 0)
	if err != nil {
		t.Fatal(err)
	}
	spans := abbreviationSpans(af, nil, nil)
	file := fset.File(af.Pos())
	return func(claim string) *abbreviationSpan {
		t.Helper()
		at := strings.Index(src, claim)
		if at < 0 {
			t.Fatalf("the fixture has no text %s", claim)
		}
		return abbreviationsAt(spans, file.Pos(at))
	}
}

// TestLintClaimSpansFollowTheCalls: a member's proof written across the
// funcs of its package reads one table. The Sections script is a func
// the member names, a lemma is a func the script calls, and a reader is
// a func a section's closure calls; each runs under the table of the
// statement that reaches it, and a lemma's own entries extend it.
func TestLintClaimSpansFollowTheCalls(t *testing.T) {
	const src = `package p

var member = family.Add(registry.ProofEntry{Build: family.Sections(Statement{
	Binders:    "∀x:A.",
	Conclusion: "p(«y»)",
	Abbrev:     Abbrev{{Name: "y", Text: "f(x)"}},
}, script)})

func script(ctx *Script) {
	first := lemma(ctx)
	ctx.Theorem("p(«y»)", func(a *Argument) { reader(a, first) })
}

func lemma(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders:    "∀x:A.",
		Conclusion: "q(«y», «z»)",
		Abbrev:     Abbrev{{Name: "z", Text: "g(«y»)"}},
	}, func(a *Argument) { a.Have("in the lemma", "r(«y», «z»)") })
}

func reader(a *Argument, fact Fact) Fact { return a.Have("in the reader", "s(«y»)") }
`
	at := scopeFixture(t, src)
	for _, c := range []struct {
		claim string
		names []string
	}{
		{`"q(«y», «z»)"`, []string{"y", "z"}},
		{`"r(«y», «z»)"`, []string{"y", "z"}},
		{`"s(«y»)"`, []string{"y"}},
	} {
		span := at(c.claim)
		for _, name := range c.names {
			if span == nil || span.table == nil || !span.table.Has(name) {
				t.Errorf("the text %s has no table declaring «%s» in scope", c.claim, name)
			}
		}
		if span != nil && span.err != nil {
			t.Errorf("the text %s: %v", c.claim, span.err)
		}
	}
	if span := at(`"s(«y»)"`); span != nil && span.table.Has("z") {
		t.Error("the reader reads the lemma's «z», which no statement reaching it declares")
	}
}

// TestLintClaimSpansASharedFuncReadsTheCommonEntries: a func two
// members reach reads what both declare with one text. A name one of
// them lacks, one they give two texts, and one whose text spells such a
// name are each refused where a text of the func spells them, and where
// a statement of the func declares them again: under one of the members
// the door would refuse it at replay.
func TestLintClaimSpansASharedFuncReadsTheCommonEntries(t *testing.T) {
	const src = `package p

var first = family.Theorem(Statement{
	Binders:    "∀x:A.",
	Conclusion: "p(«y»)",
	Abbrev: Abbrev{
		{Name: "y", Text: "f(x)"},
		{Name: "w", Text: "h(x)"},
		{Name: "v", Text: "k(«w»)"},
		{Name: "u", Text: "m(x)"},
	},
}, func(a *Argument) { shared(a) })

var second = family.Theorem(Statement{
	Binders:    "∀x:A.",
	Conclusion: "p(«y»)",
	Abbrev: Abbrev{
		{Name: "y", Text: "f(x)"},
		{Name: "w", Text: "j(x)"},
		{Name: "v", Text: "k(«w»)"},
	},
}, func(a *Argument) { shared(a) })

func shared(a *Argument) {
	a.Have("both declare it", "s(«y»)")
	a.Have("two texts", "s1(«w»)")
	a.Have("spells the one with two texts", "s2(«v»)")
	a.Have("one member lacks it", "s3(«u»)")
	inner(a)
}

func inner(a *Argument) {
	a.Have("through the shared func", "s4(«y»)")
	a.Have("through the shared func, partial", "s5(«u»)")
}

func restated(ctx *Script) {
	ctx.Lemma(Statement{
		Conclusion: "s6(«u»)",
		Abbrev:     Abbrev{{Name: "u", Text: "n(x)"}},
	}, func(a *Argument) {})
}

var third = family.Sections("p(x)", restated)

var fourth = family.Sections(Statement{
	Conclusion: "p(«u»)",
	Abbrev:     Abbrev{{Name: "u", Text: "m(x)"}},
}, restated)
`
	at := scopeFixture(t, src)
	for _, claim := range []string{`"s(«y»)"`, `"s4(«y»)"`} {
		span := at(claim)
		if span == nil || !span.table.Has("y") {
			t.Fatalf("the text %s has no table declaring «y» in scope", claim)
		}
		if why := span.refusal(strings.Trim(claim, `"`)); why != "" {
			t.Errorf("the text %s: %s", claim, why)
		}
		for _, name := range []string{"w", "v", "u"} {
			if span.table.Has(name) {
				t.Errorf("the text %s reads «%s», which the two members do not both declare with one text", claim, name)
			}
		}
	}
	for claim, want := range map[string]string{
		`"s1(«w»)"`: "«w» is not in every table shared is read under, or not with one text: the func is reached from first, second",
		`"s2(«v»)"`: "«v» is not in every table shared is read under",
		`"s3(«u»)"`: "«u» is not in every table shared is read under",
		`"s5(«u»)"`: "«u» is not in every table inner is read under, or not with one text: the func is reached from shared",
		`"s6(«u»)"`: "abbreviation «u» is declared twice: here, and by a statement that reaches restated",
	} {
		if got := at(claim).refusal(strings.Trim(claim, `"`)); !strings.Contains(got, want) {
			t.Errorf("the text %s: want a refusal holding %q, got %q", claim, want, got)
		}
	}
}

// TestLintClaimSpansReadNoTableFromOutside: a func reads a statement's
// table only where the package's statements are all that reach it. An
// exported func and a method are called from anywhere, so they and what
// they call read no member's entries; nor does a func nothing in the
// package names. A parameter spelled as a func of the package is the
// parameter.
func TestLintClaimSpansReadNoTableFromOutside(t *testing.T) {
	const src = `package p

var member = family.Theorem(Statement{
	Binders:    "∀x:A.",
	Conclusion: "p(«y»)",
	Abbrev:     Abbrev{{Name: "y", Text: "f(x)"}},
}, func(a *Argument) {
	Exported(a)
	reached(a)
	named := func(shadowed Fact) Fact { return shadowed }
	named(nil)
})

func Exported(a *Argument) {
	a.Have("in an exported func", "s1(«y»)")
	fromExported(a)
}

func fromExported(a *Argument) { a.Have("called by the exported func", "s2(«y»)") }

func (r receiver) method(a *Argument) { fromMethod(a) }

func fromMethod(a *Argument) { a.Have("called by a method", "s3(«y»)") }

func unnamed(a *Argument) { a.Have("nothing names this func", "s4(«y»)") }

func shadowed(a *Argument) { a.Have("only a parameter has this name", "s5(«y»)") }

func reached(a *Argument) {
	a.Have("the member calls this one", "s6(«y»)")
	fromMethod(a)
}
`
	at := scopeFixture(t, src)
	for _, claim := range []string{`"s1(«y»)"`, `"s2(«y»)"`, `"s3(«y»)"`, `"s4(«y»)"`, `"s5(«y»)"`} {
		if span := at(claim); span != nil && span.table.Has("y") {
			t.Errorf("the text %s reads the member's «y»", claim)
		}
	}
	if span := at(`"s6(«y»)"`); span == nil || !span.table.Has("y") {
		t.Error(`the text "s6(«y»)" has no table declaring «y» in scope`)
	}
	want := "«y» is not in every table fromMethod is read under, or not with one text: the func is reached from method, reached"
	if got := at(`"s3(«y»)"`).refusal("s3(«y»)"); !strings.Contains(got, want) {
		t.Errorf("the text reached from a method and from the member: want a refusal holding %q, got %q", want, got)
	}
}

// TestLintClaimSpansCrossFilesAndReadTheChapter: the member and the
// funcs of its proof may stand in different files of the package, and
// the chapter's table is under each of them.
func TestLintClaimSpansCrossFilesAndReadTheChapter(t *testing.T) {
	const memberSrc = `package p

var member = family.Sections(Statement{
	Binders:    "∀x:A.",
	Conclusion: "p(«y»)",
	Abbrev:     Abbrev{{Name: "y", Text: "f(«c»)"}},
}, script)
`
	const scriptSrc = `package p

func script(ctx *Script) {
	ctx.Lemma(Statement{
		Conclusion: "q(«z»)",
		Abbrev:     Abbrev{{Name: "z", Text: "g(«y», «c»)"}},
	}, func(a *Argument) { a.Have("in the other file", "r(«c», «y», «z»)") })
}
`
	fset := token.NewFileSet()
	var files []*ast.File
	for name, src := range map[string]string{"member.go": memberSrc, "script.go": scriptSrc} {
		af, err := parser.ParseFile(fset, name, src, 0)
		if err != nil {
			t.Fatal(err)
		}
		files = append(files, af)
	}
	chapter := dsl.Abbrev{{Name: "c", Text: "chapter_datum(x)"}}
	spans := packageAbbreviationSpans(files, nil, chapter)
	for _, af := range files {
		if fset.File(af.Pos()).Name() != "script.go" {
			continue
		}
		span := abbreviationsAt(spans[af], fset.File(af.Pos()).Pos(strings.Index(scriptSrc, `"r(«c», «y», «z»)"`)))
		if span == nil || span.err != nil {
			t.Fatalf("the lemma's claim reads no table: %+v", span)
		}
		for _, name := range []string{"c", "y", "z"} {
			if !span.table.Has(name) {
				t.Errorf("the lemma's claim has no «%s» in scope", name)
			}
		}
	}
}
