package index

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"path/filepath"
	"strconv"
	"strings"
	"sync"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/xugofmt"
)

// A member's chapter file is read as text, once per file and only
// when a question asks for what the registry does not hold: the doc
// comment above the declaration that registered the member, its
// Gloss, and the narration of its proof, its Outline. The registry is
// the program evaluated — statements as terms, deps as a set — and the
// text keeps what evaluation drops. What is read is the landed Go the
// kernel replays, so a step's claim is the claim the replay proved;
// its label is prose, checked by no one, and is served as written.
//
// A member is found in its file by the line the registry recorded at
// registration: the top-level declaration whose span holds that line.
// One declaration may register several members — a door minting rules
// and faces — and they share its comment.

// OutlineStep is one narration step of a proof as its chapter writes
// it: a call of a narration verb (xugofmt.NarrationVerbs, with Cases
// and Induct) on the argument, in source order.
type OutlineStep struct {
	// Verb is the call's name as written: Have, Show, ObtainAs, When,
	// Cases, …
	Verb string `json:"verb"`
	// Label is the step's prose, the verb's first string; Claim the
	// formal text that follows it where the verb takes one (Have,
	// Obtain, Cases over a term) and the chapter writes it as a string.
	// A Show states no claim: it closes the goal in force.
	Label string `json:"label,omitempty"`
	Claim string `json:"claim,omitempty"`
	// Cites are the members the step's proof names, by id, each once in
	// the order written — directly, or through a local a `:=` bound to
	// a citation. Uses are the other names it passes: the facts and
	// terms of the argument, the aliases among them.
	Cites []string `json:"cites,omitempty"`
	Uses  []string `json:"uses,omitempty"`
	// Depth is the step's nesting under the member's argument: 0 at the
	// top, one more inside each closure (Derive, When, Step, …).
	Depth int `json:"depth,omitempty"`
	// Line is the call's line in the chapter file.
	Line int `json:"line"`
}

// structureVerbs are the label-less verbs an outline lists beside the
// narration verbs: the split and the induction a proof turns on.
var structureVerbs = map[string]bool{"Cases": true, "Induct": true}

// sourceFile is one chapter file read: its top-level declarations in
// order, each with its span, its doc comment and its outline.
type sourceFile struct {
	once  sync.Once
	err   error
	decls []sourceDecl
}

// sourceDecl is one top-level declaration of a chapter file.
type sourceDecl struct {
	start, end int
	gloss      string
	outline    []OutlineStep
}

// source reads a member's chapter file once, in the process, and
// returns it. A file that fails to parse is an error: the tree on disk
// is outside input, and the binary that answers may have been built
// from a tree the disk no longer holds.
func (c *Corpus) source(m *Member) (*sourceFile, error) {
	file, _, _ := strings.Cut(m.Source, ":")
	c.sourcesMu.Lock()
	sf := c.sources[file]
	if sf == nil {
		sf = &sourceFile{}
		c.sources[file] = sf
	}
	c.sourcesMu.Unlock()
	sf.once.Do(func() { sf.err = sf.read(c, m.Family, filepath.Join(c.Root, filepath.FromSlash(file))) })
	return sf, sf.err
}

func (sf *sourceFile) read(c *Corpus, family, path string) error {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, path, nil, parser.ParseComments)
	if err != nil {
		return fmt.Errorf("index: %v", err)
	}
	imports := map[string]bool{}
	for _, imp := range f.Imports {
		p, _ := strconv.Unquote(imp.Path.Value)
		name := p[strings.LastIndex(p, "/")+1:]
		if imp.Name != nil {
			name = imp.Name.Name
		}
		imports[name] = true
	}
	line := func(n ast.Node) int { return fset.Position(n.Pos()).Line }
	end := func(n ast.Node) int { return fset.Position(n.End()).Line }
	for _, decl := range f.Decls {
		switch d := decl.(type) {
		case *ast.GenDecl:
			for _, s := range d.Specs {
				spec, ok := s.(*ast.ValueSpec)
				if !ok || len(spec.Values) == 0 {
					continue
				}
				doc := spec.Doc
				if doc == nil && len(d.Specs) == 1 {
					doc = d.Doc
				}
				sd := sourceDecl{start: line(d), end: end(spec)}
				if len(d.Specs) > 1 {
					sd.start = line(spec)
				}
				if doc != nil {
					sd.gloss = gloss(spec.Names[0].Name, doc.Text())
				}
				r := outlineReader{c: c, family: family, fset: fset, imports: imports, locals: map[string]bool{}, aliases: map[string][]string{}}
				for _, v := range spec.Values {
					if closure := argumentClosure(v); closure != nil {
						r.bind(closure)
						r.walk(closure, 0)
					}
				}
				sd.outline = r.steps
				sf.decls = append(sf.decls, sd)
			}
		case *ast.FuncDecl:
			sd := sourceDecl{start: line(d), end: end(d)}
			if d.Doc != nil {
				sd.gloss = gloss(d.Name.Name, d.Doc.Text())
			}
			sf.decls = append(sf.decls, sd)
		}
	}
	return nil
}

// gloss is a declaration's doc comment as one line, the `name — ` the
// house style opens it with left off.
func gloss(name, text string) string {
	text = strings.Join(strings.Fields(text), " ")
	for _, dash := range []string{" — ", " - "} {
		text = strings.TrimPrefix(text, name+dash)
	}
	return text
}

// declaring is the declaration that registered a member: the one whose
// span holds the member's registered line. A file that declares
// nothing there was not the file the binary was built from.
func (sf *sourceFile) declaring(m *Member) (*sourceDecl, error) {
	_, at, _ := strings.Cut(m.Source, ":")
	line, _ := strconv.Atoi(at)
	for i := range sf.decls {
		if d := &sf.decls[i]; d.start <= line && line <= d.end {
			return d, nil
		}
	}
	return nil, fmt.Errorf("index: %s is registered at %s, where the file on disk declares nothing — the binary and the tree differ", m.ID, m.Source)
}

// argumentClosure is the member's argument: the first function
// literal in its value. Nil for a card, a definition door's entry and
// every other member stated without a Go proof.
func argumentClosure(value ast.Expr) *ast.FuncLit {
	var found *ast.FuncLit
	ast.Inspect(value, func(n ast.Node) bool {
		if found != nil {
			return false
		}
		if fl, ok := n.(*ast.FuncLit); ok {
			found = fl
			return false
		}
		return true
	})
	return found
}

// outlineReader walks an argument and lists its steps.
type outlineReader struct {
	c       *Corpus
	family  string
	fset    *token.FileSet
	imports map[string]bool
	// locals are the names the argument binds — its closures'
	// parameters and what its statements define — which shadow a
	// chapter member of the same name (`nonzero Fact` beside a lemma
	// nonzero).
	locals map[string]bool
	// aliases are the locals a `:=` binds to a citation — `invT :=
	// field.InvIn.Read(L).At(tm)` — each with the members the citation
	// names: a step that passes the local names them too. A local bound
	// to a narration step holds that step's fact, and is no alias.
	aliases map[string][]string
	steps   []OutlineStep
}

// bind collects the names an argument binds anywhere inside it, and
// the aliases among them, in source order so an alias of an alias
// resolves.
func (r *outlineReader) bind(closure *ast.FuncLit) {
	ast.Inspect(closure, func(n ast.Node) bool {
		switch x := n.(type) {
		case *ast.FuncLit:
			for _, field := range x.Type.Params.List {
				for _, name := range field.Names {
					r.locals[name.Name] = true
				}
			}
		case *ast.AssignStmt:
			if x.Tok == token.DEFINE {
				for _, lhs := range x.Lhs {
					if id, ok := lhs.(*ast.Ident); ok {
						r.locals[id.Name] = true
					}
				}
				r.alias(x)
			}
		case *ast.ValueSpec:
			for _, name := range x.Names {
				r.locals[name.Name] = true
			}
		case *ast.RangeStmt:
			for _, e := range []ast.Expr{x.Key, x.Value} {
				if id, ok := e.(*ast.Ident); ok {
					r.locals[id.Name] = true
				}
			}
		}
		return true
	})
}

// alias records a `name := citation` binding: one name, one value that
// is no narration step, naming at least one member.
func (r *outlineReader) alias(assign *ast.AssignStmt) {
	if len(assign.Lhs) != 1 || len(assign.Rhs) != 1 {
		return
	}
	id, ok := assign.Lhs[0].(*ast.Ident)
	if !ok {
		return
	}
	if call, isCall := assign.Rhs[0].(*ast.CallExpr); isCall {
		if verb, _ := narrationCall(call); verb != "" {
			return
		}
	}
	var s OutlineStep
	r.names("", assign.Rhs[0], &s, map[string]bool{})
	if len(s.Cites) > 0 {
		r.aliases[id.Name] = s.Cites
	}
}

// walk lists the steps of a closure at a depth: the narration calls on
// the closure's argument — its first parameter — in source order, each
// closure inside one deeper.
func (r *outlineReader) walk(closure *ast.FuncLit, depth int) {
	receiver := ""
	if params := closure.Type.Params.List; len(params) > 0 && len(params[0].Names) > 0 {
		receiver = params[0].Names[0].Name
	}
	ast.Inspect(closure.Body, func(n ast.Node) bool {
		switch x := n.(type) {
		case *ast.FuncLit:
			r.walk(x, depth+1)
			return false
		case *ast.CallExpr:
			if verb, recv := narrationCall(x); verb != "" && recv == receiver {
				r.steps = append(r.steps, r.step(verb, receiver, x, depth))
			}
		}
		return true
	})
}

// narrationCall reads a call as a narration or structure verb on an
// argument: the verb and the receiver's name, or "" and "" for any
// other call. A generic verb, `a.ObtainAs[Nat](…)`, is read past its
// type arguments.
func narrationCall(call *ast.CallExpr) (verb, receiver string) {
	fun := call.Fun
	switch f := fun.(type) {
	case *ast.IndexExpr:
		fun = f.X
	case *ast.IndexListExpr:
		fun = f.X
	}
	sel, ok := fun.(*ast.SelectorExpr)
	if !ok {
		return "", ""
	}
	recv, ok := sel.X.(*ast.Ident)
	if !ok || !(xugofmt.NarrationVerbs[sel.Sel.Name] || structureVerbs[sel.Sel.Name]) {
		return "", ""
	}
	return sel.Sel.Name, recv.Name
}

// step reads one narration call: the leading strings as label and
// claim, the rest as the proof whose names it lists. A structure verb
// takes no label; its claim is the term it splits or inducts on.
func (r *outlineReader) step(verb, receiver string, call *ast.CallExpr, depth int) OutlineStep {
	s := OutlineStep{Verb: verb, Depth: depth, Line: r.fset.Position(call.Pos()).Line}
	args := call.Args
	if structureVerbs[verb] {
		for _, a := range args {
			ast.Inspect(a, func(n ast.Node) bool {
				if e, ok := n.(ast.Expr); ok && s.Claim == "" {
					if text, isString := xugofmt.StringValue(e); isString {
						s.Claim = dsl.OneLine(text)
					}
				}
				return s.Claim == ""
			})
		}
	} else if text, ok := stringArg(args); ok {
		s.Label, args = text, args[1:]
		if text, ok := stringArg(args); ok {
			s.Claim, args = dsl.OneLine(text), args[1:]
		}
	}
	seen := map[string]bool{}
	for _, a := range args {
		r.names(receiver, a, &s, seen)
	}
	return s
}

// stringArg is the first argument when it is a string: a literal, or a
// chain of them joined by `+` (xugofmt.StringValue).
func stringArg(args []ast.Expr) (string, bool) {
	if len(args) == 0 {
		return "", false
	}
	return xugofmt.StringValue(args[0])
}

// names lists the names a proof expression passes: a member it cites
// — a bare name the chapter registers and the argument does not bind,
// or `chapter.Name` through an import — under Cites, and every other
// root name under Uses. A combinator called by name (By, Derive, a
// package's helper), the argument itself and the type arguments of a
// generic call name nothing, and a closure's names are its own steps'.
// A member named to form a statement — `Entry.Statement(…)`,
// `Entry.Law(…)` — or a structure entry, named to read a fact as an
// instance of the structure, is no citation: nothing is read by it.
func (r *outlineReader) names(receiver string, e ast.Expr, s *OutlineStep, seen map[string]bool) {
	add := func(list *[]string, name string) {
		if !seen[name] {
			seen[name] = true
			*list = append(*list, name)
		}
	}
	cite := func(m *Member) {
		if m.Kind != "structure" {
			add(&s.Cites, m.ID)
		}
	}
	switch x := e.(type) {
	case *ast.FuncLit, *ast.BasicLit:
	case *ast.Ident:
		if x.Name == receiver || x.Name == "_" {
			return
		}
		if m := r.chapterMember(x.Name); m != nil && !r.locals[x.Name] {
			cite(m)
		} else {
			add(&s.Uses, x.Name)
			for _, id := range r.aliases[x.Name] {
				add(&s.Cites, id)
			}
		}
	case *ast.SelectorExpr:
		if statementDoor(x.Sel.Name) {
			if _, root := x.X.(*ast.Ident); root {
				return
			}
			if sel, ok := x.X.(*ast.SelectorExpr); ok {
				if _, pkg := sel.X.(*ast.Ident); pkg {
					return
				}
			}
		}
		if pkg, ok := x.X.(*ast.Ident); ok {
			if r.imports[pkg.Name] {
				if m, ok := r.c.byEntry[pkg.Name+"."+x.Sel.Name]; ok {
					cite(m)
				}
				return
			}
		}
		r.names(receiver, x.X, s, seen)
	case *ast.CallExpr:
		if _, byName := x.Fun.(*ast.Ident); !byName {
			r.names(receiver, x.Fun, s, seen)
		}
		for _, a := range x.Args {
			r.names(receiver, a, s, seen)
		}
	case *ast.IndexExpr:
		r.names(receiver, x.X, s, seen)
		if _, generic := x.X.(*ast.SelectorExpr); !generic {
			r.names(receiver, x.Index, s, seen)
		}
	case *ast.IndexListExpr:
		r.names(receiver, x.X, s, seen)
	case *ast.ParenExpr:
		r.names(receiver, x.X, s, seen)
	case *ast.UnaryExpr:
		r.names(receiver, x.X, s, seen)
	case *ast.CompositeLit:
		for _, elt := range x.Elts {
			r.names(receiver, elt, s, seen)
		}
	case *ast.KeyValueExpr:
		r.names(receiver, x.Value, s, seen)
	}
}

// statementDoor says a selector forms a statement from an entry rather
// than reading it: Entry.Statement(…) states a local lemma or a card
// over the entry's structure, Entry.Law(…) a law of it.
func statementDoor(sel string) bool {
	return sel == "Statement" || sel == "Law"
}

// chapterMember is the member a bare name denotes in the chapter the
// file belongs to, or nil.
func (r *outlineReader) chapterMember(bare string) *Member {
	for _, m := range r.c.byBare[bare] {
		if m.Family == r.family {
			return m
		}
	}
	return nil
}

// readGlosses fills the gloss of each member of a family from its
// chapter files.
func (c *Corpus) readGlosses(f *Family) error {
	for _, m := range f.Members {
		if err := c.readGloss(m); err != nil {
			return err
		}
	}
	return nil
}

// readGloss fills a member's gloss from the declaration that
// registered it, refusing a file that declares nothing at the member's
// registered line.
func (c *Corpus) readGloss(m *Member) error {
	d, err := c.declaration(m)
	if err != nil {
		return err
	}
	m.Gloss = d.gloss
	return nil
}

// declaration reads a member's chapter file and finds the declaration
// that registered it.
func (c *Corpus) declaration(m *Member) (*sourceDecl, error) {
	sf, err := c.source(m)
	if err != nil {
		return nil, err
	}
	return sf.declaring(m)
}

// Outline reads a member's proof as its chapter narrates it: the steps
// in source order. Empty for a member with no Go argument — a card, a
// definition door's entry.
func (c *Corpus) Outline(m *Member) ([]OutlineStep, error) {
	d, err := c.declaration(m)
	if err != nil {
		return nil, err
	}
	return d.outline, nil
}
