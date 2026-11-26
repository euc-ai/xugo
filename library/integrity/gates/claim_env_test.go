// claim_env_test.go — the static claim-site binding-reconstruction
// library: for every claim literal in a proof body, reconstruct the
// ENVIRONMENT the runtime would parse it in — the ordered set of
// in-scope binder names with their types — without running a single
// proof step.
//
// Shared by the B3 variable-scope lint (claim_scope_lint_test.go) and
// the surface-spelling sweep (surface_sweep_test.go). Built on the B0
// machinery of claim_lint_test.go (file walking, family scopes, claim
// collection) — this file adds the ENV dimension B0 deliberately
// skipped.
//
// # What is reconstructed
//
// The runtime environment of a claim is Script.ParseScope (family
// vocabulary + every Script.Var registration) overlaid with the
// Argument chain's surface aliases (prover/proof/derive.go §"Surface
// names"). Statically that is:
//
// - the family vocabulary (registry.Family.ParseScript — B0's scope);
// - `ctx.Var("name", …)` literals of the file (names known, types
// not — the type argument is a Go expression);
// - the BINDING CHAIN of the enclosing bodies, reconstructed
// statement by statement below. Each binding carries its binder
// TYPE (read off the parsed statement/claim) and whether the
// runtime registers a surface ALIAS for it (Fix / Obtain /
// section-boundary param — the sweep's eligibility bit).
//
// # Tracking rules (per verb, from derive.go / section.go)
//
// - family.Theorem / ctx.Theorem / ctx.Lemma closure: the headline
// parses in the family scope; closure params consume leading slots
// left-to-right per section.go (sequent ⊢-hyps first, then the
// conclusion's ∀/⇒ chain). Each Term param introduces the
// STATEMENT's binder name (TestLintBinderClosureNames keeps the Go
// name equal) at the binder's type, aliased.
// - A typed verb (a.FixAs[T], a.TermAs[T], a.ObtainAs[T] and
// a.UnpackAs[T], and the forms of two to five witnesses of each,
// a.Obtain2As[T, U] to a.Unpack5As[T, U, V, W, X] — the thin
// verb+ext.As compositions of prover/proof/typed.go) is tracked as
// its untyped twin (claimTypedVerbTwin); Script.VarAs[T]("name")
// registers like Script.Var.
// - a.Obtain and a.Obtain2 to a.Obtain5 with a string-literal claim: the
// claim's leading ∃-binder names enter the env (plus their
// SurfaceBase variants — skolemizeSpine binds both), aliased; with a
// Named(…) marker of literal names, those names alone, as Fix("u").
// A non-literal or unparsable claim, or a Named marker of anything
// but literals, OPENs the env (the runtime minted a name this walk
// cannot know).
// - Inner Derive/Given bodies in a claim's proof position inherit
// the outer env; a cursor into the claim's binder prefix feeds
// each in-body a.Fix() (consumes one leading ∀, introduces the
// binder name + SurfaceBase, aliased; a.Fix("u") introduces `u`
// alone, the runtime's one spelling) and a.Assume() (consumes one
// leading ⇒, introduces nothing).
// - a.Denote(name, …) introduces the literal name (no static type —
// the term is a Go expression); a.Binder("name") introduces the
// name at the cursor binder's type when findable. Neither is
// runtime-aliased.
// - a.Induct(name) registers the binder name (via a.Binder);
// branch bodies under Cases/Induct/Iff are OPEN environments
// entirely (phase-1 defers branch mints).
// - Env-NEUTRAL verbs (checked against derive.go): Assume,
// SupposeNot, Take, Have, ObtainChosen (asserts P(ε) — registers
// no name), Hyp, Term, Show, Calc/CalcOrder/CalcLeibniz,
// Assuming/Unless (side bodies keep the conclusion, so the cursor
// survives), Do (actions cannot reach the ParseScope), Ctx, Goal.
// - OPEN triggers: Unpack and Unpack2 to Unpack5 (witness names come off the
// RESIDENT hyp's spelling — not static), Fix without a tracked
// binder prefix, Fix/Denote/Binder/Induct with non-literal names, and
// ANY unrecognized method on an Argument receiver. Claims after an
// OPEN point (and claims in unclassified positions) are recorded
// with a nil env and skipped by both consumers.
//
// # Shadowing
//
// Bindings accumulate in introduction order, shadowed entries
// included. A name introduced twice in the chain is AMBIGUOUS below
// the second introduction: B3 still accepts either spelling as "in
// scope", the sweep refuses to rewrite the base there.
//
// # The sweep's static safety check
//
// A rewrite `n₀ → n` is modeled EXACTLY as the runtime resolves it
// (Script.parseScopeWithAliases + core.Substitute, replicated locally):
// both the original and the rewritten text parse in the family scope
// with every relevant name seeded at its binder type, both parses then
// have their free surface names renamed to the minted spellings, and
// the rewrite is accepted only when the two Props are EXACTLY equal
// (never merely α-equal — recorded CNF keys must keep hitting).
package gates

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
	"path"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"testing"
	"unicode"
	"unicode/utf8"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/xugofmt"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// Claim-text tokenization (the DSL lexer's identifier rules)
// ---------------------------------------------------------------------------

// envIdentToken is one identifier token of a claim text: its byte span
// in the RAW literal and its subscript-normalized spelling (the DSL
// pre-lex folds `n₀` to `n_0`, so both spell the same identifier).
type envIdentToken struct {
	start, end int
	raw        string
	norm       string
}

func envIsSubscriptDigit(r rune) bool { return r >= '₀' && r <= '₉' }

func envIsIdentStart(r rune) bool { return unicode.IsLetter(r) || r == '_' }

// envIsIdentChar mirrors dsl/lex.go isIdentChar, plus the Unicode
// subscript digits the normalize pre-pass folds into the identifier.
func envIsIdentChar(r rune) bool {
	return unicode.IsLetter(r) || unicode.IsDigit(r) || r == '_' || r == '\'' || r == '%' ||
		envIsSubscriptDigit(r)
}

// envFoldSubscripts rewrites every contiguous run of Unicode subscript
// digits as `_` + ASCII digits — dsl.denormalizeUnicodeSubscripts's
// rule, replicated so token spellings compare in the lexer's normal
// form.
func envFoldSubscripts(s string) string {
	if !strings.ContainsAny(s, "₀₁₂₃₄₅₆₇₈₉") {
		return s
	}
	var b strings.Builder
	b.Grow(len(s))
	inRun := false
	for _, r := range s {
		if envIsSubscriptDigit(r) {
			if !inRun {
				b.WriteByte('_')
				inRun = true
			}
			b.WriteRune('0' + (r - '₀'))
		} else {
			b.WriteRune(r)
			inRun = false
		}
	}
	return b.String()
}

// envTokenize scans a claim text for identifier tokens. The fused
// `var:M` / `var:?123` type-variable form (dsl/lex.go) is consumed
// whole and DROPPED — a type variable is not a term variable and must
// never look like one to the sweep.
func envTokenize(text string) []envIdentToken {
	var out []envIdentToken
	for i := 0; i < len(text); {
		r, sz := utf8.DecodeRuneInString(text[i:])
		if !envIsIdentStart(r) {
			i += sz
			continue
		}
		j := i + sz
		for j < len(text) {
			r2, sz2 := utf8.DecodeRuneInString(text[j:])
			if !envIsIdentChar(r2) {
				break
			}
			j += sz2
		}
		raw := text[i:j]
		if raw == "var" && j < len(text) && text[j] == ':' {
			k := j + 1
			if k < len(text) && text[k] == '?' {
				k++
			}
			for k < len(text) {
				r2, sz2 := utf8.DecodeRuneInString(text[k:])
				if !envIsIdentChar(r2) {
					break
				}
				k += sz2
			}
			i = k
			continue
		}
		out = append(out, envIdentToken{start: i, end: j, raw: raw, norm: envFoldSubscripts(raw)})
		i = j
	}
	return out
}

// ---------------------------------------------------------------------------
// The environment
// ---------------------------------------------------------------------------

// envBinding is one name the claim-site environment holds.
type envBinding struct {
	name    string
	typ     core.HolType // nil when statically unknown (Denote, un-cursored Binder)
	aliased bool         // the runtime registers a surface alias (sweep eligibility)
}

// envSnap is an immutable snapshot of the binding chain at one claim
// site, outermost introduction first (shadowed entries included).
type envSnap struct{ bindings []envBinding }

// lookup returns the INNERMOST binding of name, or nil.
func (s *envSnap) lookup(name string) *envBinding {
	for i := len(s.bindings) - 1; i >= 0; i-- {
		if s.bindings[i].name == name {
			return &s.bindings[i]
		}
	}
	return nil
}

// introductions counts how many times name was introduced along the
// chain — >1 means the base is shadowed (ambiguous for the sweep).
func (s *envSnap) introductions(name string) int {
	n := 0
	for i := range s.bindings {
		if s.bindings[i].name == name {
			n++
		}
	}
	return n
}

// envSite is one claim literal with its reconstructed environment.
type envSite struct {
	file string
	dir  string
	fam  *registry.Family
	line int
	verb string // Have / Obtain … Obtain5 / ObtainChosen / Hyp / Term / Headline

	call     *ast.CallExpr
	lit      ast.Expr // the string literal, or chain of them, that spells the claim; nil when it reached the verb through a package const
	labelLit ast.Expr // the same call's label, a string literal or a chain of them (claim-bearing verbs)
	text     string

	env        *envSnap // nil ⇔ OPEN / unclassified region — skipped by B3 and the sweep
	openReason string
	bodyID     int // section-body identity, for body-wide mint consistency

	// abbreviations is the innermost span the text stands in
	// (claimSite.abbreviations); nil outside every one.
	abbreviations *abbreviationSpan
	// exempt names the binders the text binds as its own, exempt from
	// the abbreviation capture check (claimSite.exempt).
	exempt map[string]bool
}

func (s *envSite) where() string { return fmt.Sprintf("%s:%d", s.file, s.line) }

// ---------------------------------------------------------------------------
// Collection: one walk of the corpus
// ---------------------------------------------------------------------------

type envCollection struct {
	fset  *token.FileSet
	sites []*envSite
	skips map[string]int
	// scriptVars: family DIR → names declared via `.Var("name", …)`
	// literals anywhere in the package (Script-level registrations —
	// known to claims, types not static). Per-dir because vocab helpers
	// (`ops(ctx)`, `registerSlopeVocab(ctx)`) declare in sibling files.
	scriptVars map[string]map[string]bool
	famByDir   map[string]*registry.Family
}

// envSectionInfo describes one section-constructor call found in a file.
type envSectionInfo struct {
	verb      string
	fn        *ast.FuncLit
	text      string
	lit       ast.Expr // the string literal, or chain of them, that spells the headline
	stated    bool     // the headline is a Statement{…} literal
	resolved  bool
	hasConsts bool
	isArgBody bool // funclit's first param is *Argument (a section proof body)
}

// envFileWalk is the per-file walking state.
type envFileWalk struct {
	col      *envCollection
	t        *testing.T
	scopes   *claimScopeCache
	file     string
	dir      string
	fam      *registry.Family
	af       *ast.File
	consts   map[string]string
	sections map[*ast.CallExpr]*envSectionInfo
	handled  map[*ast.CallExpr]bool
	visited  map[*ast.CallExpr]bool
	bodySeq  *int
	spans    []abbreviationSpan
}

// collectEnvSites walks every family proof file and reconstructs the
// environment of every claim literal.
func collectEnvSites(t *testing.T, scopes *claimScopeCache) *envCollection {
	t.Helper()
	col := &envCollection{
		fset:       token.NewFileSet(),
		skips:      map[string]int{},
		scriptVars: map[string]map[string]bool{},
		famByDir:   claimFamilyByDir(),
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
	bodySeq := 0
	for _, dir := range dirs {
		files := byDir[dir]
		fam := col.famByDir[dir]
		if fam == nil {
			col.skips["file outside a registered family dir"] += len(files)
			continue
		}
		sort.Strings(files)
		consts := map[string]string{}
		asts := map[string]*ast.File{}
		parsed := make([]*ast.File, 0, len(files))
		for _, f := range files {
			af, err := envParseGoFile(col.fset, f)
			if err != nil {
				t.Fatalf("parse %s: %v", f, err)
			}
			asts[f] = af
			parsed = append(parsed, af)
		}
		collectStringConsts(parsed, consts)
		spans := packageAbbreviationSpans(parsed, consts, fam.Abbrev())
		walks := make([]*envFileWalk, 0, len(files))
		for _, f := range files {
			w := &envFileWalk{
				col: col, t: t, scopes: scopes,
				file: f, dir: dir, fam: fam, af: asts[f],
				consts:   consts,
				sections: map[*ast.CallExpr]*envSectionInfo{},
				handled:  map[*ast.CallExpr]bool{},
				visited:  map[*ast.CallExpr]bool{},
				bodySeq:  &bodySeq,
				spans:    spans[asts[f]],
			}
			walks = append(walks, w)
			// The whole dir's `.Var` names must be known before any file
			// walks — a vocab helper in a sibling file serves them all.
			w.collectScriptVars()
		}
		for _, w := range walks {
			w.run()
		}
	}
	return col
}

func envParseGoFile(fset *token.FileSet, f string) (*ast.File, error) {
	return parser.ParseFile(fset, f, nil, 0)
}

// envWalkSource runs the walk over one proof file given as source, read
// as a file of the family at famRel (relative to the corpus root): the
// instrument guards' road to the walker itself.
func envWalkSource(t *testing.T, scopes *claimScopeCache, famRel, src string) *envCollection {
	t.Helper()
	col := &envCollection{
		fset:       token.NewFileSet(),
		skips:      map[string]int{},
		scriptVars: map[string]map[string]bool{},
		famByDir:   claimFamilyByDir(),
	}
	dir := filepath.ToSlash(filepath.Join(corpusRoot, filepath.FromSlash(famRel)))
	fam := col.famByDir[dir]
	if fam == nil {
		t.Fatalf("instrument guard: no registered family at %s", famRel)
	}
	af, err := parser.ParseFile(col.fset, path.Join(dir, "guard.go"), src, 0)
	if err != nil {
		t.Fatalf("instrument guard: parse the guard source: %v", err)
	}
	bodySeq := 0
	w := &envFileWalk{
		col: col, t: t, scopes: scopes,
		file: path.Join(dir, "guard.go"), dir: dir, fam: fam, af: af,
		consts:   map[string]string{},
		sections: map[*ast.CallExpr]*envSectionInfo{},
		handled:  map[*ast.CallExpr]bool{},
		visited:  map[*ast.CallExpr]bool{},
		bodySeq:  &bodySeq,
		spans:    abbreviationSpans(af, nil, fam.Abbrev()),
	}
	w.collectScriptVars()
	w.run()
	return col
}

func envUnquote(v string) (string, error) { return strconv.Unquote(v) }

func (w *envFileWalk) run() {
	w.collectSections()
	// Drive: dispatch every section-constructor call once. Script
	// bodies (Sections/Derived) are simply descended into — their
	// nested Theorem/Lemma calls are dispatched by this same walk.
	ast.Inspect(w.af, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}
		if info, ok := w.sections[call]; ok && !w.handled[call] {
			w.handled[call] = true
			w.recordHeadline(call, info)
			if info.isArgBody {
				w.walkSection(info)
				return false // walkSection covered the body
			}
		}
		return true
	})
	// Reconciliation: any claim-verb call the classified walk never
	// reached is recorded as an unclassified (open) site.
	w.reconcile()
}

// collectScriptVars harvests `.Var("name", …)` literals — Script-level
// ParseScope registrations whose names later claims may spell —
// accumulated per family DIR (see envCollection.scriptVars).
func (w *envFileWalk) collectScriptVars() {
	vars := w.col.scriptVars[w.dir]
	if vars == nil {
		vars = map[string]bool{}
		w.col.scriptVars[w.dir] = vars
	}
	ast.Inspect(w.af, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok || len(call.Args) == 0 {
			return true
		}
		// ctx.Var("name", ty), or the typed ctx.VarAs[T]("name").
		switch {
		case len(call.Args) == 2:
			if sel, ok := call.Fun.(*ast.SelectorExpr); !ok || sel.Sel.Name != "Var" {
				return true
			}
		case len(call.Args) == 1:
			ix, ok := call.Fun.(*ast.IndexExpr)
			if !ok {
				return true
			}
			if sel, ok := ix.X.(*ast.SelectorExpr); !ok || sel.Sel.Name != "VarAs" {
				return true
			}
		default:
			return true
		}
		if lit, ok := call.Args[0].(*ast.BasicLit); ok && lit.Kind == token.STRING {
			if s, err := envUnquote(lit.Value); err == nil {
				vars[s] = true
			}
		}
		return true
	})
}

// collectSections finds every section-constructor call and resolves its
// headline text. Two passes: Sections spans first, so a nested
// `ctx.Theorem(headline, …)` can resolve the headline PARAMETER back to
// the Sections literal.
func (w *envFileWalk) collectSections() {
	type span struct {
		from, to token.Pos
		param    string
		text     string
		resolved bool
	}
	var spans []span
	ast.Inspect(w.af, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok || len(call.Args) < 2 {
			return true
		}
		sel, ok := call.Fun.(*ast.SelectorExpr)
		if !ok || sel.Sel.Name != "Sections" {
			return true
		}
		fn, ok := call.Args[1].(*ast.FuncLit)
		if !ok || len(fn.Type.Params.List) < 2 {
			return true
		}
		text, _, resolved := headlineStatement(call.Args[0], w.consts)
		names := fn.Type.Params.List[1].Names
		if len(names) != 1 {
			return true
		}
		spans = append(spans, span{fn.Pos(), fn.End(), names[0].Name, text, resolved})
		return true
	})
	resolveText := func(call *ast.CallExpr) (string, ast.Expr, bool) {
		if s, ok := xugofmt.StringValue(call.Args[0]); ok {
			return s, call.Args[0], true
		}
		if stmt, ok := statementLiteral(call.Args[0]); ok {
			text, err := stmt.Text()
			return text, nil, err == nil
		}
		if id, ok := call.Args[0].(*ast.Ident); ok {
			if s, ok := w.consts[id.Name]; ok {
				return s, nil, true
			}
			// Innermost enclosing Sections whose headline param this is.
			best := -1
			for i, sp := range spans {
				if sp.param != id.Name || call.Pos() < sp.from || call.End() > sp.to {
					continue
				}
				if best < 0 || (spans[best].from < sp.from) {
					best = i
				}
			}
			if best >= 0 && spans[best].resolved {
				return spans[best].text, nil, true
			}
		}
		return "", nil, false
	}
	ast.Inspect(w.af, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok || len(call.Args) < 2 {
			return true
		}
		sel, ok := call.Fun.(*ast.SelectorExpr)
		if !ok {
			return true
		}
		verb := sel.Sel.Name
		if verb != "Theorem" && verb != "Lemma" && verb != "Sections" && verb != "Derived" {
			return true
		}
		fn, ok := call.Args[1].(*ast.FuncLit)
		if !ok {
			return true
		}
		info := &envSectionInfo{verb: verb, fn: fn, hasConsts: len(call.Args) > 2}
		info.text, info.lit, info.resolved = resolveText(call)
		_, info.stated = call.Args[0].(*ast.CompositeLit)
		if len(fn.Type.Params.List) > 0 {
			info.isArgBody = strings.Contains(types.ExprString(fn.Type.Params.List[0].Type), "Argument")
		}
		w.sections[call] = info
		return true
	})
}

// recordHeadline records the headline literal itself as a claim site
// with an EMPTY (closed) environment — a headline parses in the bare
// family scope, so its free variables answer to the vocabulary alone.
func (w *envFileWalk) recordHeadline(call *ast.CallExpr, info *envSectionInfo) {
	w.visited[call] = true
	if info.lit == nil && !(info.stated && info.resolved) {
		return // const- or param-carried text: literal recorded at its own site
	}
	if info.hasConsts {
		w.col.skips["headline with per-section const overrides"]++
		return
	}
	w.record(&envSite{
		verb: "Headline", call: call, lit: info.lit, text: info.text,
		env: &envSnap{}, exempt: headlineExempt(info.text),
	})
}

func (w *envFileWalk) record(s *envSite) {
	s.file, s.dir, s.fam = w.file, w.dir, w.fam
	if s.call != nil {
		s.line = w.col.fset.Position(s.call.Pos()).Line
		s.abbreviations = abbreviationsAt(w.spans, s.call.Pos())
	}
	w.col.sites = append(w.col.sites, s)
}

// ---------------------------------------------------------------------------
// The Argument-body walk
// ---------------------------------------------------------------------------

var envMatchesImply = ext.MatchesBinaryOp(ext.IMPLY)

// argCtx is the walking state of one Argument body.
type argCtx struct {
	w       *envFileWalk
	outer   *argCtx
	argName string
	env     []envBinding
	open    bool
	reason  string
	cursor  core.Term // remaining ∀/⇒ prefix of the body's statement; nil = not tracked
	bodyID  int
}

func (c *argCtx) markOpen(reason string) {
	if !c.open {
		c.open, c.reason = true, reason
	}
}

func (c *argCtx) snap() (*envSnap, string) {
	if c.open {
		return nil, c.reason
	}
	return &envSnap{bindings: append([]envBinding(nil), c.env...)}, ""
}

// introduce appends a binding; withBase additionally binds the
// SurfaceBase variant (skolemizeSpine / bare-Fix behavior — the
// section boundary binds ONLY the statement name). The name is stored
// in the lexer's normal form, as claim tokens are looked up: an
// author's surface name `n₀` binds `n_0`.
func (c *argCtx) introduce(name string, typ core.HolType, aliased, withBase bool) {
	if name == "" {
		return
	}
	name = envFoldSubscripts(name)
	c.env = append(c.env, envBinding{name: name, typ: typ, aliased: aliased})
	if withBase {
		if base := proof.SurfaceBase(name); base != name && base != "" {
			c.env = append(c.env, envBinding{name: base, typ: typ, aliased: aliased})
		}
	}
}

func (c *argCtx) findArg(name string) *argCtx {
	for x := c; x != nil; x = x.outer {
		if x.argName == name {
			return x
		}
	}
	return nil
}

// walkSection opens one section body: parse the headline, bind the
// closure parameters to its leading slots, walk the statements.
func (w *envFileWalk) walkSection(info *envSectionInfo) {
	*w.bodySeq++
	c := &argCtx{w: w, bodyID: *w.bodySeq}
	fn := info.fn
	if len(fn.Type.Params.List) == 0 || len(fn.Type.Params.List[0].Names) != 1 {
		c.markOpen("section body without a readable Argument parameter")
		w.openInspect(fn, c.reason)
		return
	}
	c.argName = fn.Type.Params.List[0].Names[0].Name
	switch {
	case info.hasConsts:
		c.markOpen("headline with per-section const overrides")
	case !info.resolved:
		c.markOpen("headline not statically resolvable")
	default:
		hp, panicked := envSafeParseProp(w.scopes.scope(w.fam), abbreviationsAt(w.spans, info.fn.Pos()), info.text, headlineExempt(info.text))
		if panicked != "" || hp == nil {
			c.markOpen("headline does not parse statically")
		} else {
			w.bindSectionParams(c, fn, hp)
		}
	}
	c.stmts(fn.Body.List)
}

// bindSectionParams consumes the statement's leading slots with the
// closure's parameters (section.go's rule: sequent ⊢-hyps first, then
// the conclusion's ∀/⇒ chain), introducing each Term param's binder.
func (w *envFileWalk) bindSectionParams(c *argCtx, fn *ast.FuncLit, hp core.Prop) {
	pp := hp.AsProp()
	hypLeft := pp.NumHyps()
	c.cursor = pp.Conclusion()
	for i, fld := range fn.Type.Params.List {
		if i == 0 {
			continue
		}
		isFact := strings.Contains(types.ExprString(fld.Type), "Fact")
		for range fld.Names {
			if isFact {
				if hypLeft > 0 {
					hypLeft--
					continue
				}
				if _, concl, ok := envMatchesImply(c.cursor); ok {
					c.cursor = concl
					continue
				}
				c.markOpen("Fact parameter without a matching slot")
				return
			}
			abs := ext.MatchesFORALL(c.cursor)
			if abs.IsZero() {
				c.markOpen("Term parameter without a leading ∀ slot")
				return
			}
			// The STATEMENT's binder name is authoritative (the
			// param-name lint keeps the Go spelling equal); the section
			// boundary binds exactly this name (fixImpl(slot.name)).
			c.introduce(string(abs.Var().Name()), abs.Var().Type(), true, false)
			c.cursor = abs.Body()
		}
	}
}

func (c *argCtx) stmts(list []ast.Stmt) {
	for _, st := range list {
		switch st := st.(type) {
		case *ast.ExprStmt:
			c.expr(st.X)
		case *ast.AssignStmt:
			for _, r := range st.Rhs {
				c.expr(r)
			}
		case *ast.ReturnStmt:
			for _, r := range st.Results {
				c.expr(r)
			}
		case *ast.DeclStmt:
			if gd, ok := st.Decl.(*ast.GenDecl); ok {
				for _, spec := range gd.Specs {
					if vs, ok := spec.(*ast.ValueSpec); ok {
						for _, v := range vs.Values {
							c.expr(v)
						}
					}
				}
			}
		case *ast.BlockStmt:
			c.stmts(st.List)
		default:
			// Control flow inside a deduction body — execution order is
			// not the statement order this walk models.
			c.w.openInspect(st, fmt.Sprintf("claim inside unmodelled %T", st))
		}
	}
}

func (c *argCtx) expr(e ast.Expr) {
	switch e := e.(type) {
	case *ast.CallExpr:
		c.call(e)
	case *ast.FuncLit:
		c.w.openInspect(e, "function literal in unmodelled position")
	case *ast.ParenExpr:
		c.expr(e.X)
	case *ast.UnaryExpr:
		c.expr(e.X)
	case *ast.BinaryExpr:
		c.expr(e.X)
		c.expr(e.Y)
	case *ast.CompositeLit:
		for _, el := range e.Elts {
			c.expr(el)
		}
	case *ast.KeyValueExpr:
		c.expr(e.Value)
	case *ast.IndexExpr:
		c.expr(e.X)
		c.expr(e.Index)
	case *ast.IndexListExpr:
		c.expr(e.X)
		for _, ix := range e.Indices {
			c.expr(ix)
		}
	case *ast.SelectorExpr:
		c.expr(e.X)
	case *ast.Ident:
		// The Argument VALUE reaching an unmodelled position — a helper
		// call (`samePoints(a, …)`), an assignment, a struct field —
		// hands the whole verb surface to code this walk does not
		// model: the callee may Fix/Obtain/Denote at will, so the env
		// is unknown from here on.
		if tc := c.findArg(e.Name); tc != nil {
			tc.markOpen("Argument value escapes into unmodelled code")
		}
	default:
		// Literals — nothing to walk.
	}
}

func (c *argCtx) call(call *ast.CallExpr) {
	// A nested section constructor (ctx.Lemma inside a body) opens a
	// FRESH section — dispatch it, don't descend generically.
	if info, ok := c.w.sections[call]; ok && !c.w.handled[call] {
		c.w.handled[call] = true
		c.w.recordHeadline(call, info)
		if info.isArgBody {
			c.w.walkSection(info)
		} else {
			for _, a := range call.Args {
				c.expr(a)
			}
		}
		return
	}
	if sel, verb, ok := claimVerbSelector(call); ok {
		if recv, ok := sel.X.(*ast.Ident); ok {
			if tc := c.findArg(recv.Name); tc != nil {
				tc.verb(call, verb, c)
				return
			}
		}
	}
	switch calleeName(call) {
	case "Derive", "Given":
		// A block body in a position this walk gives no meaning.
		c.w.openInspect(call, "Derive/Given in unmodelled position")
		return
	case "Case", "MakeCase":
		c.w.openInspect(call, "case branch body")
		return
	}
	// The callee expression itself may carry a chained receiver
	// (`helper(a).Foo(…)`) — walk it for escapes and nested verbs.
	if _, bare := call.Fun.(*ast.Ident); !bare {
		c.expr(call.Fun)
	}
	for _, a := range call.Args {
		c.expr(a)
	}
}

// verb dispatches one method call on THIS Argument (possibly reached
// from a nested body — `from` is the syntactic location's context).
func (c *argCtx) verb(call *ast.CallExpr, name string, from *argCtx) {
	switch name {
	case "Have":
		cl := c.claimSite(call, "Have", 1, true)
		c.proofArgs(call.Args[2:], from, envConclOf(cl))
	case "Obtain":
		c.obtainVerb(call, "Obtain", 1, from)
	case "Obtain2":
		c.obtainVerb(call, "Obtain2", 2, from)
	case "Obtain3":
		c.obtainVerb(call, "Obtain3", 3, from)
	case "Obtain4":
		c.obtainVerb(call, "Obtain4", 4, from)
	case "Obtain5":
		c.obtainVerb(call, "Obtain5", 5, from)
	case "ObtainChosen":
		cl := c.claimSite(call, "ObtainChosen", 1, true)
		_ = cl
		c.proofArgs(call.Args[2:], from, nil)
	case "Hyp":
		if len(call.Args) == 1 {
			c.claimSite(call, "Hyp", 0, false)
		}
	case "Term":
		if len(call.Args) == 1 {
			c.claimSite(call, "Term", 0, false)
		}
	case "Show":
		if len(call.Args) >= 1 {
			c.proofArgs(call.Args[1:], from, c.cursor)
		}
	case "Fix":
		c.doFix(call)
	case "Assume":
		if c.cursor != nil {
			if _, concl, ok := envMatchesImply(c.cursor); ok {
				c.cursor = concl
			} else {
				c.cursor = nil
			}
		}
	case "SupposeNot":
		c.cursor = nil
	case "Take":
		for _, a := range call.Args {
			from.expr(a)
		}
		c.cursor = nil
	case "Denote":
		c.doDenote(call, from)
	case "Binder":
		c.doBinder(call)
	case "Cases":
		if len(call.Args) >= 1 {
			from.expr(call.Args[0])
		}
		for _, a := range call.Args[1:] {
			c.w.openInspect(a, "case branch body")
		}
		// The surviving branch keeps the conclusion — cursor survives.
	case "Iff":
		for _, a := range call.Args {
			c.w.openInspect(a, "case branch body")
		}
		c.cursor = nil
	case "Induct":
		c.doInduct(call)
	case "Assuming", "Unless":
		if len(call.Args) >= 1 {
			from.expr(call.Args[0])
		}
		if len(call.Args) >= 3 {
			// The side body proves the same conclusion (a hyp was added)
			// — the cursor survives into it.
			c.proofArgs(call.Args[2:], from, c.cursor)
		}
	case "Calc", "CalcOrder", "CalcLeibniz":
		for _, a := range call.Args {
			from.expr(a)
		}
	case "Do":
		for _, a := range call.Args {
			from.expr(a)
		}
		c.cursor = nil
	case "Unpack", "Unpack2", "Unpack3", "Unpack4", "Unpack5":
		for _, a := range call.Args {
			from.expr(a)
		}
		c.markOpen(name + " mints witnesses whose names are not static")
	case "Ctx", "Goal":
		// Reads — no env effect.
	default:
		c.markOpen("unrecognized Argument verb " + name)
		for _, a := range call.Args {
			c.w.openInspect(a, c.reason)
		}
	}
}

// doFix strips one tracked ∀. Bare Fix binds the binder's name and its
// SurfaceBase; Fix("u") binds `u` alone (derive.go fixImpl).
func (c *argCtx) doFix(call *ast.CallExpr) {
	if c.open {
		return
	}
	surface := ""
	if len(call.Args) == 1 {
		lit, ok := call.Args[0].(*ast.BasicLit)
		if !ok || lit.Kind != token.STRING {
			c.markOpen("Fix with a non-literal surface name")
			return
		}
		name, err := envUnquote(lit.Value)
		if err != nil {
			c.markOpen("Fix with an unreadable surface name literal")
			return
		}
		surface = name
	}
	if c.cursor == nil {
		c.markOpen("Fix with no statically tracked binder prefix")
		return
	}
	abs := ext.MatchesFORALL(c.cursor)
	if abs.IsZero() {
		c.markOpen("Fix beyond the tracked ∀ prefix")
		return
	}
	if surface != "" {
		c.introduce(surface, abs.Var().Type(), true, false)
	} else {
		c.introduce(string(abs.Var().Name()), abs.Var().Type(), true, true)
	}
	c.cursor = abs.Body()
}

func (c *argCtx) doDenote(call *ast.CallExpr, from *argCtx) {
	for _, a := range call.Args[1:] {
		from.expr(a)
	}
	if len(call.Args) < 1 {
		return
	}
	lit, ok := call.Args[0].(*ast.BasicLit)
	if !ok || lit.Kind != token.STRING {
		c.markOpen("Denote with a non-literal name")
		return
	}
	name, err := envUnquote(lit.Value)
	if err != nil {
		c.markOpen("Denote with an unreadable name literal")
		return
	}
	c.introduce(name, nil, false, false)
}

func (c *argCtx) doBinder(call *ast.CallExpr) {
	if len(call.Args) != 1 {
		c.markOpen("Binder with unexpected arity")
		return
	}
	lit, ok := call.Args[0].(*ast.BasicLit)
	if !ok || lit.Kind != token.STRING {
		c.markOpen("Binder with a non-literal name")
		return
	}
	name, err := envUnquote(lit.Value)
	if err != nil {
		c.markOpen("Binder with an unreadable name literal")
		return
	}
	c.introduce(name, envBinderTypeIn(c.cursor, name), false, false)
}

func (c *argCtx) doInduct(call *ast.CallExpr) {
	if len(call.Args) >= 1 {
		switch on := call.Args[0].(type) {
		case *ast.BasicLit:
			if on.Kind == token.STRING {
				if name, err := envUnquote(on.Value); err == nil {
					c.introduce(name, envBinderTypeIn(c.cursor, name), false, false)
				} else {
					c.markOpen("Induct with an unreadable name literal")
				}
			}
		case *ast.Ident:
			// The term a.Binder returned — already introduced there.
		default:
			c.markOpen("Induct on a non-literal, non-identifier target")
		}
	}
	for _, a := range call.Args[1:] {
		c.w.openInspect(a, "case branch body")
	}
	c.cursor = nil
}

// envBinderTypeIn finds the named binder in the leading ∀ chain of t.
func envBinderTypeIn(t core.Term, name string) core.HolType {
	for t != nil {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			return nil
		}
		if string(abs.Var().Name()) == name {
			return abs.Var().Type()
		}
		t = abs.Body()
	}
	return nil
}

// claimSite records one claim literal at the current env and returns
// its parsed Prop (nil when unavailable). labeled: the call's first
// argument is a display label.
func (c *argCtx) claimSite(call *ast.CallExpr, verb string, idx int, labeled bool) core.Prop {
	c.w.visited[call] = true
	if len(call.Args) <= idx {
		return nil
	}
	text, exempt, ok := claimTextOf(verb, call.Args[idx], c.w.consts)
	if !ok {
		c.w.col.skips["claim argument is not a string literal, package string const or Statement literal"]++
		return nil
	}
	site := &envSite{verb: verb, call: call, text: text, bodyID: c.bodyID, exempt: exempt}
	if _, isString := xugofmt.StringValue(call.Args[idx]); isString {
		site.lit = call.Args[idx]
	}
	if labeled {
		if _, isString := xugofmt.StringValue(call.Args[0]); isString {
			site.labelLit = call.Args[0]
		}
	}
	site.env, site.openReason = c.snap()
	c.w.record(site)
	if site.env == nil || verb == "Term" {
		return nil
	}
	out := envSeededParse(c.w.scopes.scope(c.w.fam), c.w.col.scriptVars[c.w.dir], site)
	if out.panicked != "" || len(out.res.Errors) > 0 || out.res.Prop == nil {
		return nil
	}
	return out.res.Prop
}

func envConclOf(p core.Prop) core.Term {
	if p == nil {
		return nil
	}
	return p.AsProp().Conclusion()
}

// obtainVerb: claim site + the claim's leading ∃-binder names enter the
// env (skolemizeSpine binds the binder name AND its SurfaceBase).
func (c *argCtx) obtainVerb(call *ast.CallExpr, verb string, n int, from *argCtx) {
	cl := c.claimSite(call, verb, 1, true)
	c.proofArgs(call.Args[2:], from, envConclOf(cl))
	if c.open {
		return
	}
	if cl == nil {
		c.markOpen(verb + " with a claim this walk cannot parse")
		return
	}
	surfaces, ok := c.witnessNames(verb, n, call.Args[2:])
	if !ok {
		return
	}
	t := cl.AsProp().Conclusion()
	for i := 0; i < n; i++ {
		abs := ext.MatchesEXISTS(t)
		if abs.IsZero() {
			c.markOpen(verb + " claim with too few leading ∃ binders")
			return
		}
		if surfaces != nil {
			c.introduce(surfaces[i], abs.Var().Type(), true, false)
		} else {
			c.introduce(string(abs.Var().Name()), abs.Var().Type(), true, true)
		}
		t = abs.Body()
	}
}

// witnessNames reads the Named(…) marker in an Obtain's proof list —
// the witnesses' surface names, which the runtime binds ALONE, offering
// none of the claim's binder spellings (derive.go splitWitnessNames,
// skolemizeSpine): nil and ok when there is no marker. A marker this
// walk cannot read — a non-literal name, a count other than the
// witnesses', a second marker — OPENs the env.
func (c *argCtx) witnessNames(verb string, n int, proof []ast.Expr) (names []string, ok bool) {
	seen := false
	for _, a := range proof {
		call, isCall := a.(*ast.CallExpr)
		if !isCall || calleeName(call) != "Named" {
			continue
		}
		if seen {
			c.markOpen(verb + " with two Named markers")
			return nil, false
		}
		seen = true
		if len(call.Args) != n || call.Ellipsis != token.NoPos {
			c.markOpen(fmt.Sprintf("%s with a Named marker not naming its %d witness(es)", verb, n))
			return nil, false
		}
		for _, arg := range call.Args {
			lit, isLit := arg.(*ast.BasicLit)
			if !isLit || lit.Kind != token.STRING {
				c.markOpen("Named with a non-literal surface name")
				return nil, false
			}
			name, err := envUnquote(lit.Value)
			if err != nil {
				c.markOpen("Named with an unreadable surface name literal")
				return nil, false
			}
			names = append(names, name)
		}
	}
	return names, true
}

// proofArgs walks a claim's proof actions: Derive/Given bodies inherit
// the env with the claim's binder prefix as their cursor; Chain passes
// through; anything else is walked generically.
func (c *argCtx) proofArgs(args []ast.Expr, from *argCtx, innerCursor core.Term) {
	for _, a := range args {
		call, ok := a.(*ast.CallExpr)
		if !ok {
			from.expr(a)
			continue
		}
		switch calleeName(call) {
		case "Derive", "Given":
			if len(call.Args) == 1 {
				if fn, ok := call.Args[0].(*ast.FuncLit); ok {
					c.walkInnerBody(fn, innerCursor)
					continue
				}
			}
			c.w.openInspect(call, "Derive/Given without a direct func literal")
		case "Chain":
			c.proofArgs(call.Args, from, innerCursor)
		default:
			from.expr(a)
		}
	}
}

// walkInnerBody runs a Derive/Given block: same env (fresh copy), the
// claim's conclusion as its strip cursor.
func (c *argCtx) walkInnerBody(fn *ast.FuncLit, cursor core.Term) {
	if len(fn.Type.Params.List) == 0 || len(fn.Type.Params.List[0].Names) != 1 {
		c.w.openInspect(fn, "block body without a readable Argument parameter")
		return
	}
	inner := &argCtx{
		w:       c.w,
		outer:   c,
		argName: fn.Type.Params.List[0].Names[0].Name,
		env:     append([]envBinding(nil), c.env...),
		open:    c.open,
		reason:  c.reason,
		cursor:  cursor,
		bodyID:  c.bodyID,
	}
	inner.stmts(fn.Body.List)
}

// openInspect records every claim-verb call under n as an OPEN site.
func (w *envFileWalk) openInspect(n ast.Node, reason string) {
	ast.Inspect(n, func(x ast.Node) bool {
		call, ok := x.(*ast.CallExpr)
		if !ok {
			return true
		}
		if info, ok := w.sections[call]; ok && !w.handled[call] {
			// A fresh section nested under an open region still opens
			// with its own headline env.
			w.handled[call] = true
			w.recordHeadline(call, info)
			if info.isArgBody {
				w.walkSection(info)
				return false
			}
			return true
		}
		if w.visited[call] {
			return true
		}
		verb, idx, ok := envClaimVerbOf(call)
		if !ok {
			return true
		}
		w.visited[call] = true
		text, exempt, _ := claimTextOf(verb, call.Args[idx], w.consts)
		site := &envSite{verb: verb, call: call, text: text, openReason: reason, exempt: exempt}
		w.record(site)
		return true
	})
}

// envClaimVerbOf applies B0's claim-verb recognition (single-ident
// receiver, arity guards) to one call, for the non-headline verbs.
func envClaimVerbOf(call *ast.CallExpr) (verb string, idx int, ok bool) {
	sel, name, isSel := claimVerbSelector(call)
	if !isSel {
		return "", 0, false
	}
	if _, isIdent := sel.X.(*ast.Ident); !isIdent {
		return "", 0, false
	}
	i, tracked := claimVerbArg[name]
	if !tracked || claimHeadlineVerbs[name] {
		return "", 0, false
	}
	switch name {
	case "Hyp", "Term":
		if len(call.Args) != 1 {
			return "", 0, false
		}
	default:
		if len(call.Args) < 2 {
			return "", 0, false
		}
	}
	return name, i, true
}

// reconcile records claim-verb calls the classified walk never reached
// (helper functions, unmodelled constructs) as unclassified sites, and
// headline constructors without func-literal bodies as headline sites.
func (w *envFileWalk) reconcile() {
	ast.Inspect(w.af, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok || w.visited[call] {
			return true
		}
		sel, isSel := call.Fun.(*ast.SelectorExpr)
		if isSel {
			if _, isIdent := sel.X.(*ast.Ident); isIdent && claimHeadlineVerbs[sel.Sel.Name] {
				arity := 2
				if min, gated := claimSectionConstVerbs[sel.Sel.Name]; gated {
					arity = min
				}
				if len(call.Args) >= arity {
					if min, gated := claimSectionConstVerbs[sel.Sel.Name]; gated && len(call.Args) > min {
						w.visited[call] = true
						w.col.skips["headline with per-section const overrides"]++
						return true
					}
					if text, isString := xugofmt.StringValue(call.Args[0]); isString {
						w.visited[call] = true
						w.record(&envSite{
							verb: "Headline", call: call, lit: call.Args[0], text: text,
							env: &envSnap{}, exempt: headlineExempt(text),
						})
						return true
					}
					if stmt, ok := statementLiteral(call.Args[0]); ok {
						if text, err := stmt.Text(); err == nil {
							w.visited[call] = true
							w.record(&envSite{
								verb: "Headline", call: call, text: text,
								env: &envSnap{}, exempt: headlineExempt(text),
							})
							return true
						}
					}
				}
				return true
			}
		}
		if verb, idx, ok := envClaimVerbOf(call); ok {
			w.visited[call] = true
			text, exempt, _ := claimTextOf(verb, call.Args[idx], w.consts)
			w.record(&envSite{
				verb: verb, call: call, text: text,
				openReason: "outside the classified body walk",
				exempt:     exempt,
			})
		}
		return true
	})
}

// ---------------------------------------------------------------------------
// Env-seeded parsing
// ---------------------------------------------------------------------------

// envParseOutcome is one claim parsed under its reconstructed env.
type envParseOutcome struct {
	res      dsl.ParseResult
	panicked string
	seeds    map[string]core.HolType
	// mints: base name → normalized mint spellings seen in this text
	// (tokens whose SurfaceBase is an env binding).
	mints map[string]map[string]bool
}

// envSeededParse parses one claim text with every env-resolvable token
// declared at its binding's type — the static image of the runtime's
// parseScopeWithAliases seeding.
func envSeededParse(scope *dsl.ParseScope, scriptVars map[string]bool, site *envSite) *envParseOutcome {
	out := &envParseOutcome{
		seeds: map[string]core.HolType{},
		mints: map[string]map[string]bool{},
	}
	if why := site.abbreviations.refusal(site.text); why != "" {
		out.panicked = why
		return out
	}
	scope = withAbbreviations(scope, site.abbreviations, site.exempt)
	for _, tk := range envTokenize(site.text) {
		n := tk.norm
		if _, done := out.seeds[n]; done {
			continue
		}
		if b := site.env.lookup(n); b != nil {
			if b.typ != nil {
				out.seeds[n] = b.typ
			}
			continue
		}
		base := proof.SurfaceBase(n)
		if base == n || base == "" {
			continue
		}
		b := site.env.lookup(base)
		if b == nil {
			continue
		}
		if b.typ != nil {
			out.seeds[n] = b.typ
		}
		if out.mints[base] == nil {
			out.mints[base] = map[string]bool{}
		}
		out.mints[base][n] = true
	}
	_ = scriptVars // names known, types not — they cannot be seeded
	seeded := envScopeWith(scope, out.seeds)
	func() {
		defer func() {
			if r := recover(); r != nil {
				out.panicked = trimPanic(r)
			}
		}()
		if site.verb == "Term" {
			out.res = dsl.ParseTermTextInScope(site.text, nil, seeded, nil)
		} else {
			out.res = dsl.ParsePropTextInScope(site.text, seeded)
		}
	}()
	return out
}

// envScopeWith copies a family scope with extra variable declarations
// (the parseScopeWithAliases overlay, statically).
func envScopeWith(scope *dsl.ParseScope, seeds map[string]core.HolType) *dsl.ParseScope {
	if len(seeds) == 0 {
		return scope
	}
	vars := make(map[string]core.HolType, len(scope.Vars)+len(seeds))
	for k, v := range scope.Vars {
		vars[k] = v
	}
	for k, v := range seeds {
		vars[k] = v
	}
	seeded := *scope
	seeded.Vars = vars
	return &seeded
}

// envSafeParseProp parses a closed statement in the family scope,
// under the abbreviations of the statements in reach of it with exempt
// exempt from the capture check, converting parser panics into a
// diagnostic.
func envSafeParseProp(scope *dsl.ParseScope, span *abbreviationSpan, text string, exempt map[string]bool) (p core.Prop, panicked string) {
	if why := span.refusal(text); why != "" {
		return nil, why
	}
	defer func() {
		if r := recover(); r != nil {
			panicked = trimPanic(r)
		}
	}()
	res := dsl.ParsePropTextInScope(text, withAbbreviations(scope, span, exempt))
	if len(res.Errors) > 0 {
		return nil, ""
	}
	return res.Prop, ""
}

// ---------------------------------------------------------------------------
// Free-variable accounting (B3's core question)
// ---------------------------------------------------------------------------

// envFreeNames lists the free variable names of a parse result
// (conclusion + hyps for props; the term itself for term sites).
func envFreeNames(out *envParseOutcome, isTerm bool) []string {
	seen := map[string]bool{}
	var names []string
	add := func(t core.Term) {
		if t == nil {
			return
		}
		for _, v := range t.Frees(nil) {
			n := string(v.Name())
			if !seen[n] {
				seen[n] = true
				names = append(names, n)
			}
		}
	}
	if isTerm {
		add(out.res.Term)
		return names
	}
	if out.res.Prop == nil {
		return names
	}
	pp := out.res.Prop.AsProp()
	add(pp.Conclusion())
	for i := 0; i < pp.NumHyps(); i++ {
		add(pp.Hyp(i))
	}
	return names
}

// envNameKnown answers B3's question for one free-variable name at one
// site: an in-scope binding (surface or mint spelling), a family-vocab
// variable, or a Script-level .Var registration.
func envNameKnown(site *envSite, name string, vocab, scriptVars map[string]bool) bool {
	try := func(n string) bool {
		if site.env != nil && site.env.lookup(n) != nil {
			return true
		}
		return vocab[n] || scriptVars[n]
	}
	if try(name) {
		return true
	}
	if base := proof.SurfaceBase(name); base != name && try(base) {
		return true
	}
	return false
}

// ---------------------------------------------------------------------------
// Sweep candidates and the static safety check
// ---------------------------------------------------------------------------

// envBodyMints aggregates, per section body, every mint spelling seen
// for each base across the body's CLOSED claim sites — a base spelled
// two different ways anywhere in one body is skipped body-wide (one of
// the spellings cannot be this binding's mint).
func envBodyMints(col *envCollection, scopes *claimScopeCache) map[int]map[string]map[string]bool {
	agg := map[int]map[string]map[string]bool{}
	for _, s := range col.sites {
		if s.env == nil || s.lit == nil {
			continue
		}
		out := envSeededParse(scopes.scope(s.fam), col.scriptVars[s.dir], s)
		for base, ms := range out.mints {
			if agg[s.bodyID] == nil {
				agg[s.bodyID] = map[string]map[string]bool{}
			}
			if agg[s.bodyID][base] == nil {
				agg[s.bodyID][base] = map[string]bool{}
			}
			for m := range ms {
				agg[s.bodyID][base][m] = true
			}
		}
	}
	return agg
}

// envSweepCandidates computes base → mint for one closed site: the
// bases whose mint spelling may be rewritten to the surface name here.
func envSweepCandidates(site *envSite, out *envParseOutcome, bodyMints map[string]map[string]bool,
	scope *dsl.ParseScope, scriptVars map[string]bool) map[string]string {
	cands := map[string]string{}
	for base, ms := range out.mints {
		if len(ms) != 1 {
			continue // two mints share the base in this claim
		}
		var mint string
		for m := range ms {
			mint = m
		}
		b := site.env.lookup(base)
		if b == nil || !b.aliased || b.typ == nil {
			continue // no runtime surface alias — the bare name would not resolve
		}
		if site.env.introductions(base) > 1 {
			continue // shadowed — the mint may belong to the outer binding
		}
		if bm := bodyMints[base]; len(bm) > 1 {
			continue // body-wide: two spellings claim this base
		}
		if _, vocabOwns := scope.Vars[mint]; vocabOwns || scriptVars[mint] {
			continue // the mint spelling is itself a declared variable
		}
		cands[base] = mint
	}
	return cands
}

// envRewriteText replaces whole tokens per the candidate map
// (normalized-mint → base) and reports which replacements fired.
func envRewriteText(text string, cands map[string]string) (string, map[string]string) {
	mintToBase := map[string]string{}
	for base, mint := range cands {
		mintToBase[mint] = base
	}
	applied := map[string]string{}
	var b strings.Builder
	last := 0
	for _, tk := range envTokenize(text) {
		base, hit := mintToBase[tk.norm]
		if !hit {
			continue
		}
		b.WriteString(text[last:tk.start])
		b.WriteString(base)
		last = tk.end
		applied[tk.norm] = base
	}
	if len(applied) == 0 {
		return text, nil
	}
	b.WriteString(text[last:])
	return b.String(), applied
}

// envRuntimeModel parses a claim text and applies the runtime's alias
// substitution (surface base → minted spelling at the binder type) for
// the given bases — the static image of Argument.parseClaim.
func envRuntimeModel(scope *dsl.ParseScope, scriptVars map[string]bool, site *envSite,
	text string, cands map[string]string) (concl core.Term, hyps []core.Term, term core.Term, err string) {
	probe := &envSite{verb: site.verb, text: text, env: site.env}
	out := envSeededParse(scope, scriptVars, probe)
	if out.panicked != "" {
		return nil, nil, nil, "panic: " + out.panicked
	}
	if len(out.res.Errors) > 0 {
		e := out.res.Errors[0]
		return nil, nil, nil, fmt.Sprintf("[%s] %s", e.Code, e.Message)
	}
	var substs []core.TermSubst
	for base, mint := range cands {
		b := site.env.lookup(base)
		if b == nil || b.typ == nil {
			return nil, nil, nil, "candidate base lost its binding"
		}
		substs = append(substs, core.MakeTermSubst(
			core.Var(core.TermName(base), b.typ),
			core.Var(core.TermName(mint), b.typ)))
	}
	apply := func(t core.Term) core.Term {
		if t == nil || len(substs) == 0 {
			return t
		}
		return t.Substitute(substs...)
	}
	if site.verb == "Term" {
		if out.res.Term == nil {
			return nil, nil, nil, "term parse produced nothing"
		}
		return nil, nil, apply(out.res.Term), ""
	}
	if out.res.Prop == nil {
		return nil, nil, nil, "prop parse produced nothing"
	}
	pp := out.res.Prop.AsProp()
	concl = apply(pp.Conclusion())
	for i := 0; i < pp.NumHyps(); i++ {
		hyps = append(hyps, apply(pp.Hyp(i)))
	}
	return concl, hyps, nil, ""
}

// envSweepCheck is the accept/reject decision for one candidate
// rewrite: both spellings must denote EXACTLY the same terms under the
// runtime model (never merely α-equal).
func envSweepCheck(scope *dsl.ParseScope, scriptVars map[string]bool, site *envSite,
	newText string, cands map[string]string) (ok bool, reason string) {
	oc, oh, ot, oerr := envRuntimeModel(scope, scriptVars, site, site.text, cands)
	if oerr != "" {
		return false, "original does not parse under the model: " + oerr
	}
	nc, nh, nt, nerr := envRuntimeModel(scope, scriptVars, site, newText, cands)
	if nerr != "" {
		return false, "rewritten does not parse under the model: " + nerr
	}
	if site.verb == "Term" {
		if ot == nil || nt == nil || !ot.Equals(nt) {
			return false, "term parse differs"
		}
		return true, ""
	}
	if !oc.Equals(nc) {
		return false, "conclusion differs"
	}
	if len(oh) != len(nh) {
		return false, "hypothesis count differs"
	}
	for i := range oh {
		if !oh[i].Equals(nh[i]) {
			return false, "hypothesis differs"
		}
	}
	return true, ""
}
