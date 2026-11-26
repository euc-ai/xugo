// claim_text_assembly_test.go — the statement and claim texts a proof
// file assembles from Go strings, read off the source for the text gate
// (TestLintClaimTextIsData): which statement and claim arguments are
// text the Go puts together — a `+` over a name or a call, a const or
// a local string used bare, a string helper's or a local builder's
// call, a Statement literal with such a text among its parts — and the
// sites of them a commit holds, so the gate refuses the ones a change
// adds and counts the ones its base already has. A text is one literal
// or a Statement literal: a term it shares with other texts is an
// entry of the member's abbreviation table or of the chapter's, never a
// const spliced in.
package gates

import (
	"go/ast"
	"go/token"
	"strings"
	"testing"
)

// bindKind is what a name bound in a function body holds, as far as
// the source says: a string value, a string-returning func literal, a
// string const, or something this reader does not read as text.
type bindKind int

const (
	bindOther   bindKind = iota
	bindString           // `x := "…" + y`, `x := helper(…)`: text the Go assembled
	bindBuilder          // `f := func(…) string {…}`: a local builder of text
	bindConst            // `const c = "…"`: a named const, text the Go assembled where a claim splices it
)

// claimTextArg is a claim verb call's text argument, by the verb table
// the lints share (claimVerbArg; a typed verb reads as its untyped
// twin): the verb and the argument, or false for a call that is no
// claim verb, has the wrong arity, or is called on anything but a
// single identifier.
func claimTextArg(call *ast.CallExpr) (string, ast.Expr, bool) {
	sel, verb, ok := claimVerbSelector(call)
	if !ok || claimHeadlineVerbs[verb] {
		return "", nil, false
	}
	idx, ok := claimVerbArg[verb]
	if !ok || len(call.Args) <= idx {
		return "", nil, false
	}
	switch verb {
	case "Hyp", "Term":
		if len(call.Args) != 1 {
			return "", nil, false
		}
	default:
		if len(call.Args) < 2 {
			return "", nil, false
		}
	}
	if _, ok := sel.X.(*ast.Ident); !ok {
		return "", nil, false
	}
	return verb, call.Args[idx], true
}

// statementTextVerbs is the constructors whose argument at the index is
// a member's or a section's statement — the headline constructors, the
// structure doors' Law and Axiom, a predicate definition's Law and
// Conjunct, the postulate — read as a text is (claimTextArg reads the
// claim verbs). A structure door's `X.Statement(body)` around the
// argument is read through to the body.
var statementTextVerbs = map[string]int{
	"Card": 0, "Theorem": 0, "Lemma": 0, "Sections": 0, "Derived": 0, "Lifted": 0,
	"Law": 0, "Axiom": 0, "Conjunct": 0, "Postulate": 1,
}

// statementTextArg is a statement constructor call's text argument
// (statementTextVerbs), or false for a call that is no such
// constructor, has too few arguments, or is called on anything but a
// door's name (statementReceiver).
func statementTextArg(call *ast.CallExpr) (string, ast.Expr, bool) {
	sel, ok := call.Fun.(*ast.SelectorExpr)
	if !ok {
		return "", nil, false
	}
	if !statementReceiver(sel.X) {
		return "", nil, false
	}
	idx, ok := statementTextVerbs[sel.Sel.Name]
	if !ok || len(call.Args) <= idx {
		return "", nil, false
	}
	return sel.Sel.Name, doorStatementBody(call.Args[idx]), true
}

// statementReceiver reports whether e names the door a statement
// constructor is called on: a name (`family`, `ctx`, `IsTopology`), a
// door another family exports (`topological_space.IsTopology`), or the
// entry a definition hands out (`SubmoduleDef.Entry()`) — names joined
// by selectors and calls without arguments.
func statementReceiver(e ast.Expr) bool {
	switch x := e.(type) {
	case *ast.Ident:
		return true
	case *ast.SelectorExpr:
		return statementReceiver(x.X)
	case *ast.CallExpr:
		return len(x.Args) == 0 && statementReceiver(x.Fun)
	}
	return false
}

// statementLiteralTexts is the text positions of a `Statement{…}`
// literal — Binders, each hypothesis, Conclusion, each entry's Text —
// or nil for any other expression.
func statementLiteralTexts(e ast.Expr) []ast.Expr {
	cl, ok := e.(*ast.CompositeLit)
	if !ok {
		return nil
	}
	if id, ok := cl.Type.(*ast.Ident); !ok || id.Name != "Statement" {
		return nil
	}
	var texts []ast.Expr
	for _, el := range cl.Elts {
		kv, ok := el.(*ast.KeyValueExpr)
		if !ok {
			continue
		}
		key, ok := kv.Key.(*ast.Ident)
		if !ok {
			continue
		}
		switch key.Name {
		case "Binders", "Conclusion":
			texts = append(texts, kv.Value)
		case "Hypotheses":
			if list, ok := kv.Value.(*ast.CompositeLit); ok {
				texts = append(texts, list.Elts...)
			}
		case "Abbrev":
			list, ok := kv.Value.(*ast.CompositeLit)
			if !ok {
				continue
			}
			for _, entry := range list.Elts {
				fields, ok := entry.(*ast.CompositeLit)
				if !ok {
					continue
				}
				for _, field := range fields.Elts {
					if fkv, ok := field.(*ast.KeyValueExpr); ok {
						if name, ok := fkv.Key.(*ast.Ident); ok && name.Name == "Text" {
							texts = append(texts, fkv.Value)
						}
					}
				}
			}
		}
	}
	return texts
}

// assembledSite is one statement or claim text assembled from Go
// strings.
type assembledSite struct {
	file string
	line int
	verb string
	text string // the argument as written
	how  string // the assembly, named for the finding
}

// identity is the site's name across commits: its file and its
// argument with the whitespace taken out, so a re-layout of the same
// expression is the same site and an edit of it is a new one.
func (s assembledSite) identity() string {
	return s.file + "\x00" + strings.Join(strings.Fields(s.text), "")
}

// shown is the argument as a finding prints it: whole up to 200 runes,
// then cut with an ellipsis.
func (s assembledSite) shown() string {
	runes := []rune(s.text)
	if len(runes) <= 200 {
		return s.text
	}
	return string(runes[:200]) + "…"
}

// assembledClaimTexts reads a parsed file for the claim texts it
// assembles from Go strings. consts and helpers are the package's
// string consts and string-returning functions (collectStringConsts,
// collectStringHelpers), imported the consts of the chapter packages
// the file imports by the name it uses for each (`word_bits.WindowOpAnd`);
// a name bound in a function body is read in its block, innermost
// first, as the source binds it before the use. A const of any of the
// three kinds is text the Go assembled when a claim spells it or joins
// it. A function parameter is a value handed in, not an assembly, and
// is not read.
func assembledClaimTexts(fset *token.FileSet, af *ast.File, src []byte, file string, consts map[string]string, helpers map[string]bool, imported map[string]map[string]string) []assembledSite {
	var out []assembledSite
	var entered []ast.Node
	var scopes []map[string]bindKind
	lookup := func(name string) bindKind {
		for i := len(scopes) - 1; i >= 0; i-- {
			if k, ok := scopes[i][name]; ok {
				return k
			}
		}
		return bindOther
	}
	bind := func(name string, k bindKind) {
		if name == "_" || len(scopes) == 0 {
			return
		}
		scopes[len(scopes)-1][name] = k
	}
	source := func(e ast.Expr) string {
		return string(src[fset.Position(e.Pos()).Offset:fset.Position(e.End()).Offset])
	}
	// textOf reads an expression: whether it is text this reader can
	// see, and if so whether the Go assembled it and how.
	var textOf func(e ast.Expr) (how string, assembled, text bool)
	textOf = func(e ast.Expr) (string, bool, bool) {
		switch e := e.(type) {
		case *ast.BasicLit:
			return "", false, e.Kind == token.STRING
		case *ast.ParenExpr:
			return textOf(e.X)
		case *ast.SelectorExpr:
			if pkg, ok := e.X.(*ast.Ident); ok {
				if _, ok := imported[pkg.Name][e.Sel.Name]; ok {
					return "a named const, " + pkg.Name + "." + e.Sel.Name, true, true
				}
			}
			return "", false, false
		case *ast.Ident:
			if _, ok := consts[e.Name]; ok {
				return "a named const, " + e.Name, true, true
			}
			switch lookup(e.Name) {
			case bindConst:
				return "a named const, " + e.Name, true, true
			case bindString:
				return "a local string, " + e.Name, true, true
			}
			return "", false, false
		case *ast.CallExpr:
			if id, ok := e.Fun.(*ast.Ident); ok && (helpers[id.Name] || lookup(id.Name) == bindBuilder) {
				return "a call of the string builder " + id.Name, true, true
			}
			return "", false, false
		case *ast.BinaryExpr:
			if e.Op != token.ADD {
				return "", false, false
			}
			lHow, lAssembled, lText := textOf(e.X)
			rHow, rAssembled, rText := textOf(e.Y)
			if !lText && !rText {
				return "", false, false
			}
			// A + with a string among its operands is a string, so an
			// operand this reader cannot see is a Go string too.
			var parts []string
			for _, side := range []struct {
				how        string
				assembled  bool
				text       bool
				expression ast.Expr
			}{{lHow, lAssembled, lText, e.X}, {rHow, rAssembled, rText, e.Y}} {
				switch {
				case side.assembled && strings.HasPrefix(side.how, "spliced"):
					parts = append(parts, strings.TrimSuffix(strings.TrimPrefix(side.how, "spliced from Go strings by + ("), ")"))
				case side.assembled:
					parts = append(parts, side.how)
				case !side.text:
					parts = append(parts, source(side.expression))
				}
			}
			if len(parts) == 0 {
				return "", false, true
			}
			return "spliced from Go strings by + (" + strings.Join(parts, ", ") + ")", true, true
		}
		return "", false, false
	}
	bindValue := func(name string, value ast.Expr) {
		if fn, ok := value.(*ast.FuncLit); ok {
			if r := fn.Type.Results; r != nil && len(r.List) == 1 && len(r.List[0].Names) <= 1 {
				if id, ok := r.List[0].Type.(*ast.Ident); ok && id.Name == "string" {
					bind(name, bindBuilder)
					return
				}
			}
			bind(name, bindOther)
			return
		}
		if _, _, text := textOf(value); text {
			bind(name, bindString)
			return
		}
		bind(name, bindOther)
	}
	ast.Inspect(af, func(n ast.Node) bool {
		if n == nil {
			top := entered[len(entered)-1]
			entered = entered[:len(entered)-1]
			if _, ok := top.(*ast.BlockStmt); ok {
				scopes = scopes[:len(scopes)-1]
			}
			return true
		}
		entered = append(entered, n)
		switch x := n.(type) {
		case *ast.BlockStmt:
			scopes = append(scopes, map[string]bindKind{})
		case *ast.AssignStmt:
			if len(x.Lhs) != len(x.Rhs) {
				return true
			}
			for i, l := range x.Lhs {
				if id, ok := l.(*ast.Ident); ok {
					bindValue(id.Name, x.Rhs[i])
				}
			}
		case *ast.DeclStmt:
			gd, ok := x.Decl.(*ast.GenDecl)
			if !ok {
				return true
			}
			for _, spec := range gd.Specs {
				vs, ok := spec.(*ast.ValueSpec)
				if !ok || len(vs.Names) != len(vs.Values) {
					continue
				}
				for i, name := range vs.Names {
					if gd.Tok == token.CONST {
						if _, _, text := textOf(vs.Values[i]); text {
							bind(name.Name, bindConst)
						}
						continue
					}
					bindValue(name.Name, vs.Values[i])
				}
			}
		case *ast.CallExpr:
			verb, arg, ok := claimTextArg(x)
			if !ok {
				verb, arg, ok = statementTextArg(x)
			}
			if !ok {
				return true
			}
			if how, assembled, _ := textOf(arg); assembled {
				out = append(out, assembledSite{file: file, line: fset.Position(arg.Pos()).Line, verb: verb, text: source(arg), how: how})
				return true
			}
			for _, part := range statementLiteralTexts(arg) {
				if how, assembled, _ := textOf(part); assembled {
					out = append(out, assembledSite{file: file, line: fset.Position(part.Pos()).Line, verb: verb, text: source(part), how: "a part of a Statement literal, " + how})
				}
			}
		}
		return true
	})
	return out
}

// TestAssembledClaimTextsReadsTheSource pins the reader on the shapes
// the corpus writes: what it reads as assembled text, with its how —
// a const of any kind joined in or used bare among them — and what it
// leaves alone: a literal, literals joined, a value that is no text,
// a func literal returning a Prop.
func TestAssembledClaimTextsReadsTheSource(t *testing.T) {
	const src = `package x

import "github.com/euc-ai/xugo/library/proofs/words/word_bits"

const pkgConst = "c"

const builtConst = "b(" + pkgConst + ")"

func helper(s string) string { return "h(" + s + ")" }

func member(a *Argument, given Fact) {
	local := "l"
	const localConst = "k"
	build := func(f string) string { return f + " ∈ S" }
	prop := func(x, y Term) Prop { return MakeProp(Equal(x, y)) }
	a.Have("1", "p ∈ "+pkgConst, nil)
	a.Have("2", "p ∈ "+localConst, nil)
	a.Have("3", "p ∈ "+"q", nil)
	a.Have("4", "p ∈ "+local, nil)
	a.Have("5", local, nil)
	a.Have("6", build("p"), nil)
	a.Have("7", helper("p"), nil)
	a.Have("8", prop(x, y), nil)
	a.Have("9", MakeProp(x), nil)
	a.Have("10", "p ∈ "+unknown, nil)
	a.Have("11", given, nil)
	a.Term(local)
	func() {
		inner := "i"
		a.Have("12", "p ∈ "+inner+pkgConst, nil)
	}()
	a.Have("13", "p ∈ "+inner, nil)
	a.Hyp("p = " + "q")
	a.Have("14", "p ∈ "+builtConst, nil)
	a.Have("15", "op("+word_bits.WindowOpAnd+")", nil)
	a.Have("16", "op("+word_bits.Unknown+")", nil)
}

var card = family.Card(pkgConst+" ⇒ q", "a note")

var law = S.Law(Statement{Binders: pkgConst, Conclusion: "q"}, func(a *Argument) {})

var wrapped = family.Theorem(S.Statement(Statement{Conclusion: helper("q")}), func(a *Argument) {})

var plain = family.Theorem(Statement{Conclusion: "q", Abbrev: Abbrev{{Name: "x", Text: "p"}}}, func(a *Argument) {})
`
	sites := assembledClaimTextsOf(t, "member.go", src, map[string]map[string]string{"word_bits": {"WindowOpAnd": "(λa:bool.λb:bool. a ∧ b)"}})
	got := map[string]string{}
	for _, s := range sites {
		got[s.text] = s.how
	}
	want := map[string]string{
		`"p ∈ "+pkgConst`:                 "spliced from Go strings by + (a named const, pkgConst)",
		`"p ∈ "+localConst`:               "spliced from Go strings by + (a named const, localConst)",
		`"p ∈ "+local`:                    "spliced from Go strings by + (a local string, local)",
		`local`:                           "a local string, local",
		`build("p")`:                      "a call of the string builder build",
		`helper("p")`:                     "a call of the string builder helper",
		`"p ∈ "+unknown`:                  "spliced from Go strings by + (unknown)",
		`"p ∈ "+inner+pkgConst`:           "spliced from Go strings by + (a local string, inner, a named const, pkgConst)",
		`"p ∈ "+inner`:                    "spliced from Go strings by + (inner)",
		`"p ∈ "+builtConst`:               "spliced from Go strings by + (a named const, builtConst)",
		`"op("+word_bits.WindowOpAnd+")"`: "spliced from Go strings by + (a named const, word_bits.WindowOpAnd)",
		`"op("+word_bits.Unknown+")"`:     "spliced from Go strings by + (word_bits.Unknown)",
		`pkgConst+" ⇒ q"`:                 "spliced from Go strings by + (a named const, pkgConst)",
		`pkgConst`:                        "a part of a Statement literal, a named const, pkgConst",
		`helper("q")`:                     "a part of a Statement literal, a call of the string builder helper",
	}
	for text, how := range want {
		if got[text] != how {
			t.Errorf("%s: read as %q, want %q", text, got[text], how)
		}
	}
	for text, how := range got {
		if _, ok := want[text]; !ok {
			t.Errorf("%s: read as assembled (%s), but it is a literal or a value", text, how)
		}
	}
	// a.Term(local) is the same local string at a term position: one
	// site of the eight is it, under the text `local` once each
	if n := len(sites); n != len(want)+1 {
		t.Errorf("%d sites read, want %d (the texts above, `local` twice: at Have and at Term)", n, len(want)+1)
	}
}
