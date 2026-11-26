// abbreviation.go — a statement's abbreviations: the names its text
// and the texts of its proof spell as `«Name»`.
//
// A long term that recurs in a statement — the ring restricted to an
// overlap, a free pair along a set — gets a name in the statement's
// own table (Statement.Abbrev), and the statement, the claims
// of its proof body and the witnesses its cites pass spell the name
// between guillemets. The name is a spelling and nothing else: no
// equation joins the goal (Argument.Denote and Let do that), a closer
// sees the term, the key is the expanded statement's.
//
// Expansion is a pass over the parsed AST, before any pass that
// resolves names: an astAbbrev node is replaced by a copy of the
// entry's own AST, so every name the entry spells resolves where the
// abbreviation is written — the statement's binder, the proof block's
// surface alias, the chapter's constant — exactly as if the author had
// written the text out. A table is ordered, and an entry may spell the
// entries before it.
//
// One name, one meaning: an entry's free name that a binder of the
// text rebinds at the point of use would be captured, and the
// expansion refuses it — except the statement's own leading binders,
// which are what the entries are written over (ParseScope.
// AbbreviationBinders names them; the claim doors name none).

package dsl

import (
	"fmt"
	"maps"
	"slices"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
)

// Abbreviation is one entry of a statement's table: the name the texts
// spell as «Name», and the term it stands for, as text.
type Abbreviation struct {
	Name string `json:"name"`
	Text string `json:"text"`
}

// Abbrev is a statement's table, in order: an entry may spell
// the entries before it.
type Abbrev []Abbreviation

// AbbreviationTable is a parsed table: each entry's text read once, its
// references to earlier entries checked, and the free names it spells
// after expansion computed for the capture check.
type AbbreviationTable struct {
	entries []*abbreviationEntry
	byName  map[string]*abbreviationEntry
}

type abbreviationEntry struct {
	Abbreviation
	// ast is the entry's text as parsed, unexpanded: an astAbbrev in it
	// names an earlier entry.
	ast astNode
	// frees are the names the entry spells free after expansion,
	// sorted — a variable, a constant, an applied head alike: at the AST
	// level the three are one kind of name, and the capture check asks
	// only whether a binder of the text rebinds one.
	frees []string
	// letters are the type letters the entry's own text is written at
	// — a binder's type, a tie's target — in order of first occurrence:
	// the letters a use instantiates (instantiateLetters).
	letters []string
}

// ParseAbbreviations reads a table: every name non-empty and unique,
// every text a term that parses, every «…» in a text an entry declared
// before it. The error names the entry.
//
// An entry's text is held on one line (OneLine), as a chapter laying it
// out over lines writes it, so a table's entries read and compare as
// the terms they spell.
func ParseAbbreviations(table Abbrev) (*AbbreviationTable, error) {
	if len(table) == 0 {
		return nil, nil
	}
	out := &AbbreviationTable{byName: make(map[string]*abbreviationEntry, len(table))}
	if err := out.read(table); err != nil {
		return nil, err
	}
	return out, nil
}

// read appends entries to the table, each read as ParseAbbreviations
// reads it and against the entries before it, the table's own among
// them. An entry is numbered, in an error, by its place in the whole
// table.
func (t *AbbreviationTable) read(entries Abbrev) error {
	for _, a := range entries {
		name := strings.TrimSpace(a.Name)
		switch {
		case name == "":
			return fmt.Errorf("abbreviation %d has no name", len(t.entries)+1)
		case strings.ContainsAny(name, string(abbrevOpen)+string(abbrevClose)+"\n"):
			return fmt.Errorf("abbreviation %q: a name is spelled without guillemets and on one line", a.Name)
		case t.byName[name] != nil:
			return fmt.Errorf("abbreviation «%s» is declared twice", name)
		}
		node, err := parseTupleTerm(a.Text)
		if err != nil {
			return fmt.Errorf("abbreviation «%s»: %v", name, err)
		}
		var missing string
		walkAST(node, func(n astNode) {
			if ab, ok := n.(*astAbbrev); ok && t.byName[ab.name] == nil && missing == "" {
				missing = ab.name
			}
		})
		if missing != "" {
			return fmt.Errorf("abbreviation «%s» spells «%s», which is not declared before it — an entry may use only the entries above it", name, missing)
		}
		entry := &abbreviationEntry{Abbreviation: Abbreviation{Name: name, Text: OneLine(a.Text)}, ast: node}
		entry.frees = t.freeNamesOf(node)
		entry.letters = writtenLetters(node)
		t.entries = append(t.entries, entry)
		t.byName[name] = entry
	}
	return nil
}

// Extend is t's entries followed by entries, read as one table: what a
// text under both reads — a member's table under its chapter's
// (registry.Family.WithAbbrev), a section's under its member's. An
// entry of entries may spell t's. A name both declare is an error: one
// name, one meaning. A nil t is entries alone.
//
// The extended table holds t's entries themselves, as t read them, and
// reads only the new ones: an entry is never written after it is read,
// so the tables under one chapter share the chapter's.
func (t *AbbreviationTable) Extend(entries Abbrev) (*AbbreviationTable, error) {
	if t == nil {
		return ParseAbbreviations(entries)
	}
	if len(entries) == 0 {
		return t, nil
	}
	for _, a := range entries {
		if name := strings.TrimSpace(a.Name); t.Has(name) {
			return nil, fmt.Errorf("abbreviation «%s» is declared twice: by the table this one is read under, and here — one name, one meaning", name)
		}
	}
	out := &AbbreviationTable{
		entries: append(make([]*abbreviationEntry, 0, len(t.entries)+len(entries)), t.entries...),
		byName:  make(map[string]*abbreviationEntry, len(t.entries)+len(entries)),
	}
	maps.Copy(out.byName, t.byName)
	if err := out.read(entries); err != nil {
		return nil, err
	}
	return out, nil
}

// Join is t's entries followed by those of entries t does not hold,
// read as one table: what a chapter reads under two tables
// (registry.Family.WithOuterAbbrev). An entry both hold, one name with
// one text, is one entry reached twice — two chapters cut from one
// parent each export the parent's entries — and is read once, where t
// has it. One name with two texts is an error: one name, one meaning.
// A nil t is entries alone.
func (t *AbbreviationTable) Join(entries Abbrev) (*AbbreviationTable, error) {
	if t == nil {
		return ParseAbbreviations(entries)
	}
	var added Abbrev
	for _, a := range entries {
		name := strings.TrimSpace(a.Name)
		held := t.byName[name]
		if held == nil {
			added = append(added, a)
			continue
		}
		if text := OneLine(a.Text); held.Text != text {
			return nil, fmt.Errorf("abbreviation «%s» is declared by two of the tables read, as `%s` and as `%s` — one name, one meaning",
				name, held.Text, text)
		}
	}
	if len(added) == 0 {
		return t, nil
	}
	return ParseAbbreviations(append(t.Entries(), added...))
}

// Entries is the table as declared, in order.
func (t *AbbreviationTable) Entries() Abbrev {
	if t == nil {
		return nil
	}
	out := make(Abbrev, len(t.entries))
	for i, e := range t.entries {
		out[i] = e.Abbreviation
	}
	return out
}

// Names is the table's names, in order.
func (t *AbbreviationTable) Names() []string {
	if t == nil {
		return nil
	}
	out := make([]string, len(t.entries))
	for i, e := range t.entries {
		out[i] = e.Name
	}
	return out
}

// Has reports whether the table declares name.
func (t *AbbreviationTable) Has(name string) bool {
	return t != nil && t.byName[name] != nil
}

// WrittenOutArity is the most arguments a constant at plain arguments
// takes and still reads, written out, as plainly as any name for it.
const WrittenOutArity = 3

// IsShortConstantApplication reports whether an entry's text is one
// name applied to at most WrittenOutArity arguments that are each a
// name, a field of one, or a numeral: `polynomial_degree(p)`,
// `free_algebra(ι, R)`, `left_cosets(G.carrier, n)`. Such a term is
// written out where it is used, in every table (the constitution's
// statement rule); a longer one — the datum a chapter fixes at its six
// binders — may be named. An argument spelled through an entry («O»),
// or any other compound argument, makes the term compound; a bare name
// or a constant at a type, applied to nothing, is not counted. The text
// is read alone, so an «…» in it need not be declared; a text that does
// not parse is the error.
func IsShortConstantApplication(text string) (bool, error) {
	node, err := parseTupleTerm(text)
	if err != nil {
		return false, err
	}
	return isShortConstantApplication(node), nil
}

func isShortConstantApplication(node astNode) bool {
	app, ok := node.(*astApp)
	if !ok || len(app.args) == 0 || len(app.args) > WrittenOutArity {
		return false
	}
	if _, ok := app.fun.(*astVar); !ok {
		return false
	}
	for _, arg := range app.args {
		if !isPlainArgument(arg) {
			return false
		}
	}
	return true
}

func isPlainArgument(node astNode) bool {
	switch n := node.(type) {
	case *astVar, *astNumLit:
		return true
	case *astField:
		return isPlainArgument(n.receiver)
	}
	return false
}

// Needed is the entries the named abbreviations stand on, in table
// order: the names themselves and, transitively, the entries their
// texts spell — what a statement spelling those names must declare.
// A name the table does not declare is skipped.
func (t *AbbreviationTable) Needed(names []string) Abbrev {
	if t == nil || len(names) == 0 {
		return nil
	}
	needed := map[string]bool{}
	var mark func(name string)
	mark = func(name string) {
		e := t.byName[name]
		if e == nil || needed[name] {
			return
		}
		needed[name] = true
		for _, inner := range AbbreviationNames(e.Text) {
			mark(inner)
		}
	}
	for _, name := range names {
		mark(name)
	}
	var out Abbrev
	for _, e := range t.entries {
		if needed[e.Name] {
			out = append(out, e.Abbreviation)
		}
	}
	return out
}

// AbbreviationNames is the names text spells as «Name», in order of
// first occurrence.
func AbbreviationNames(text string) []string {
	var names []string
	for {
		open := strings.IndexRune(text, abbrevOpen)
		if open < 0 {
			return names
		}
		rest := text[open+len(string(abbrevOpen)):]
		end := strings.IndexRune(rest, abbrevClose)
		if end < 0 {
			return names
		}
		name := strings.TrimSpace(rest[:end])
		if name != "" && !slices.Contains(names, name) {
			names = append(names, name)
		}
		text = rest[end+len(string(abbrevClose)):]
	}
}

// freeNamesOf is the names node spells free after expansion, sorted:
// a name no binder of node binds, counting the names the abbreviations
// node spells bring in.
func (t *AbbreviationTable) freeNamesOf(node astNode) []string {
	seen := map[string]bool{}
	var walk func(n astNode, bound map[string]int)
	walk = func(n astNode, bound map[string]int) {
		switch x := n.(type) {
		case *astAbbrev:
			if e := t.byName[x.name]; e != nil {
				for _, f := range e.frees {
					if bound[f] == 0 {
						seen[f] = true
					}
				}
			}
			return
		case *astVar:
			head, _, _ := strings.Cut(x.name, ".")
			if bound[head] == 0 {
				seen[head] = true
			}
			return
		case *astQuantNode:
			for _, b := range x.boundNames() {
				bound[b]++
			}
			walk(x.body, bound)
			for _, b := range x.boundNames() {
				bound[b]--
			}
			return
		case *astAbsNode:
			bound[x.varName]++
			walk(x.body, bound)
			bound[x.varName]--
			return
		case *astPatternAbs:
			leaves := x.pat.leaves(nil)
			for _, lf := range leaves {
				bound[lf.name]++
			}
			walk(x.body, bound)
			for _, lf := range leaves {
				bound[lf.name]--
			}
			return
		case *astBigOp:
			walk(x.bound, bound)
			bound[x.binder]++
			walk(x.body, bound)
			bound[x.binder]--
			return
		}
		for _, c := range children(n) {
			walk(c, bound)
		}
	}
	walk(node, map[string]int{})
	out := make([]string, 0, len(seen))
	for name := range seen {
		out = append(out, name)
	}
	sort.Strings(out)
	return out
}

// children is the sub-nodes of n in reading order, for the walks that
// do not bind names.
func children(n astNode) []astNode {
	switch x := n.(type) {
	case *astOutfix:
		out := append([]astNode(nil), x.args...)
		if x.sub != nil {
			out = append(out, x.sub)
		}
		return out
	case *astField:
		return []astNode{x.receiver}
	case *astApp:
		return append([]astNode{x.fun}, x.args...)
	case *astBinOp:
		return []astNode{x.left, x.right}
	case *astCong:
		return []astNode{x.left, x.right, x.modulus}
	case *astTendsAt:
		return []astNode{x.fn, x.limit, x.point}
	case *astNotNode:
		return []astNode{x.body}
	case *astCoerce:
		return []astNode{x.operand}
	case *astNeg:
		return []astNode{x.operand}
	case *astQuantNode:
		return []astNode{x.body}
	case *astAbsNode:
		return []astNode{x.body}
	case *astPatternAbs:
		return []astNode{x.body}
	case *astBigOp:
		return []astNode{x.bound, x.body}
	}
	return nil
}

// cloneNode is a deep copy of node with every position set to pos —
// the use site's, so a diagnostic inside an expansion points at the
// abbreviation that brought the text in.
func cloneNode(node astNode, pos int) astNode {
	switch n := node.(type) {
	case nil:
		return nil
	case *astAbbrev:
		return &astAbbrev{name: n.name, ties: slices.Clone(n.ties), pos: pos}
	case *astVar:
		return &astVar{name: n.name, typeAnnot: slices.Clone(n.typeAnnot), pos: pos}
	case *astNumLit:
		return &astNumLit{value: n.value, pos: pos}
	case *astConst:
		return &astConst{name: n.name, pos: pos}
	case *astTermLit:
		return &astTermLit{term: n.term, pos: pos}
	case *astOutfix:
		out := &astOutfix{open: n.open, close: n.close, pos: pos}
		for _, a := range n.args {
			out.args = append(out.args, cloneNode(a, pos))
		}
		out.sub = cloneNode(n.sub, pos)
		return out
	case *astField:
		return &astField{receiver: cloneNode(n.receiver, pos), name: n.name, pos: pos}
	case *astApp:
		out := &astApp{fun: cloneNode(n.fun, pos), pos: pos, elided: n.elided, dims: n.dims, dimsPlaced: n.dimsPlaced}
		for _, a := range n.args {
			out.args = append(out.args, cloneNode(a, pos))
		}
		return out
	case *astBinOp:
		return &astBinOp{op: n.op, left: cloneNode(n.left, pos), right: cloneNode(n.right, pos), pos: pos, parens: n.parens}
	case *astCong:
		return &astCong{left: cloneNode(n.left, pos), right: cloneNode(n.right, pos), modulus: cloneNode(n.modulus, pos), pos: pos}
	case *astTendsAt:
		return &astTendsAt{fn: cloneNode(n.fn, pos), limit: cloneNode(n.limit, pos), point: cloneNode(n.point, pos), pos: pos}
	case *astNotNode:
		return &astNotNode{body: cloneNode(n.body, pos), pos: pos}
	case *astCoerce:
		return &astCoerce{operand: cloneNode(n.operand, pos), pos: pos}
	case *astNeg:
		return &astNeg{operand: cloneNode(n.operand, pos), pos: pos}
	case *astQuantNode:
		return &astQuantNode{quantifier: n.quantifier, varName: n.varName, varType: n.varType, body: cloneNode(n.body, pos),
			resolvedVarType: n.resolvedVarType, pos: pos, binds: slices.Clone(n.binds)}
	case *astAbsNode:
		out := *n
		out.body = cloneNode(n.body, pos)
		out.pos = pos
		return &out
	case *astPatternAbs:
		return &astPatternAbs{pat: clonePat(n.pat, pos), body: cloneNode(n.body, pos), pos: pos}
	case *astBigOp:
		return &astBigOp{symbol: n.symbol, binder: n.binder, rel: n.rel, bound: cloneNode(n.bound, pos), body: cloneNode(n.body, pos), pos: pos}
	}
	panic(fmt.Sprintf("dsl: cloneNode: unknown AST node %T", node))
}

func clonePat(p *astPat, pos int) *astPat {
	if p == nil {
		return nil
	}
	return &astPat{name: p.name, ty: p.ty, resolvedTy: p.resolvedTy, left: clonePat(p.left, pos), right: clonePat(p.right, pos), pos: pos}
}

// abbrevBinding is one binder of the text on the expansion's stack:
// the name, and whether it is one of the leading binders the entries
// are written over.
type abbrevBinding struct {
	name    string
	leading bool
	// ty is the type the binder is written at; nil where the text
	// writes none, or the binder is one a bundle binder's expansion
	// mints beside its own name (it then carries the bundle's type).
	ty astType
}

// abbrevExpansion is one text's expansion: the table, the leading
// binders the entries are written over, and the uses read so far —
// each use of an entry its own instance of the letters the entry is
// written at.
type abbrevExpansion struct {
	table   *AbbreviationTable
	binders map[string]bool
	// generic: an applied use reads the letters its arguments' slots
	// are written at off the arguments (instantiateLetters) — the
	// scope's FreshenMetaLetters. Unset, an entry is read at the
	// letters it is written at, or at its ties.
	generic bool
	// vars types the text's free names (ParseScope.Vars, a term's
	// context): the letters an entry spelling one is read at.
	vars map[string]core.HolType
}

// expandAbbreviations replaces every «Name» in root by the entry's AST
// (a copy, expanded in turn, at the use's letters), refusing a name
// the table lacks and a capture: an entry's free name that a binder of
// root rebinds at the use site, unless that binder is one of root's
// leading quantifiers and binders names it. A nil table refuses the
// first «Name» it meets, naming the missing table.
func expandAbbreviations(root astNode, x *abbrevExpansion) (astNode, *InputDiagnostic) {
	if !spellsAbbreviation(root) {
		return root, nil
	}
	return x.expandNode(root, nil)
}

// spellsAbbreviation reports whether root spells any «Name».
func spellsAbbreviation(root astNode) bool {
	found := false
	walkAST(root, func(n astNode) {
		if _, ok := n.(*astAbbrev); ok {
			found = true
		}
	})
	return found
}

// expandNode is expandAbbreviations over the binder stack reached so
// far. The text's leading quantifier chain is marked leading on the
// way down: the chain of quantifiers at the root, before any other
// node.
func (x *abbrevExpansion) expandNode(node astNode, stack []abbrevBinding) (astNode, *InputDiagnostic) {
	switch n := node.(type) {
	case nil:
		return nil, nil
	case *astAbbrev:
		use, _, diag := x.expandUse(n, 0, stack)
		return use, diag
	case *astQuantNode:
		// The leading chain: universal quantifiers from the root down,
		// each binding a name nothing above it binds — a rebinding is a
		// new binder whatever its position.
		leading := n.quantifier == utils.ForAllStr && (len(stack) == 0 || stack[len(stack)-1].leading)
		for _, b := range n.boundNames() {
			if innermost(stack, b) != nil {
				leading = false
			}
			stack = append(stack, abbrevBinding{name: b, leading: leading, ty: n.varType})
		}
		body, diag := x.expandNode(n.body, stack)
		if diag != nil {
			return nil, diag
		}
		n.body = body
		return n, nil
	case *astAbsNode:
		body, diag := x.expandNode(n.body, append(stack, abbrevBinding{name: n.varName, ty: n.varType}))
		if diag != nil {
			return nil, diag
		}
		n.body = body
		return n, nil
	case *astPatternAbs:
		inner := stack
		for _, lf := range n.pat.leaves(nil) {
			inner = append(inner, abbrevBinding{name: lf.name, ty: lf.ty})
		}
		body, diag := x.expandNode(n.body, inner)
		if diag != nil {
			return nil, diag
		}
		n.body = body
		return n, nil
	case *astBigOp:
		bound, diag := x.expandNode(n.bound, stack)
		if diag != nil {
			return nil, diag
		}
		n.bound = bound
		body, diag := x.expandNode(n.body, append(stack, abbrevBinding{name: n.binder}))
		if diag != nil {
			return nil, diag
		}
		n.body = body
		return n, nil
	case *astOutfix:
		for i, a := range n.args {
			out, diag := x.expandNode(a, stack)
			if diag != nil {
				return nil, diag
			}
			n.args[i] = out
		}
		sub, diag := x.expandNode(n.sub, stack)
		if diag != nil {
			return nil, diag
		}
		n.sub = sub
		return n, nil
	case *astField:
		r, diag := x.expandNode(n.receiver, stack)
		if diag != nil {
			return nil, diag
		}
		n.receiver = r
		return n, nil
	case *astApp:
		var fun astNode
		var letters []string
		var diag *InputDiagnostic
		use, applied := n.fun.(*astAbbrev)
		if applied {
			fun, letters, diag = x.expandUse(use, len(n.args), stack)
		} else {
			fun, diag = x.expandNode(n.fun, stack)
		}
		if diag != nil {
			return nil, diag
		}
		n.fun = fun
		// An abbreviation of a partial application, applied — «P»(m)
		// for P ≔ f(a, b) — is the one application f(a, b, m), as the
		// author would have written it out, the dimensions P's text
		// wrote in f's ⟨…⟩ still the suffix's (astApp.appliedTo): «P»(u)
		// for P ≔ vec⟨n⟩ is vec⟨n⟩(u). One of a λ, applied —
		// «P»(m) for P ≔ λx. body — is body at m, as the author would
		// have written it out, and the builder reduces it (astApp.reduced):
		// a claim headed by it has the ∃ or ∀ its body has, for the
		// doors that read a binder (Obtain, Take, At), and its key is
		// the body's, whatever order the abbreviation took its
		// arguments in.
		if inner, isApp := fun.(*astApp); applied && isApp {
			n = inner.appliedTo(n.args, n.pos)
		}
		if _, isAbs := fun.(*astAbsNode); applied && isAbs {
			n.reduced = true
			n.letters = letters
		}
		for i, a := range n.args {
			out, diag := x.expandNode(a, stack)
			if diag != nil {
				return nil, diag
			}
			n.args[i] = out
		}
		return n, nil
	case *astBinOp:
		l, diag := x.expandNode(n.left, stack)
		if diag != nil {
			return nil, diag
		}
		r, diag := x.expandNode(n.right, stack)
		if diag != nil {
			return nil, diag
		}
		n.left, n.right = l, r
		return n, nil
	case *astCong:
		for _, slot := range []*astNode{&n.left, &n.right, &n.modulus} {
			out, diag := x.expandNode(*slot, stack)
			if diag != nil {
				return nil, diag
			}
			*slot = out
		}
		return n, nil
	case *astTendsAt:
		for _, slot := range []*astNode{&n.fn, &n.limit, &n.point} {
			out, diag := x.expandNode(*slot, stack)
			if diag != nil {
				return nil, diag
			}
			*slot = out
		}
		return n, nil
	case *astNotNode:
		body, diag := x.expandNode(n.body, stack)
		if diag != nil {
			return nil, diag
		}
		n.body = body
		return n, nil
	case *astCoerce:
		out, diag := x.expandNode(n.operand, stack)
		if diag != nil {
			return nil, diag
		}
		n.operand = out
		return n, nil
	case *astNeg:
		out, diag := x.expandNode(n.operand, stack)
		if diag != nil {
			return nil, diag
		}
		n.operand = out
		return n, nil
	}
	return node, nil
}

// expandUse is the AST a use n, applied to applied arguments, reads
// as — the entry's, at the use's ties, expanded in turn — and the
// letters its arguments fix (instantiateLetters), refusing a name the
// table lacks and a capture.
func (x *abbrevExpansion) expandUse(n *astAbbrev, applied int, stack []abbrevBinding) (astNode, []string, *InputDiagnostic) {
	t := x.table
	if t == nil || t.byName[n.name] == nil {
		return nil, nil, t.missing(n)
	}
	e := t.byName[n.name]
	var captured []string
	for _, f := range e.frees {
		if b := innermost(stack, f); b != nil && !(b.leading && x.binders[f]) {
			captured = append(captured, f)
		}
	}
	if len(captured) > 0 {
		return nil, nil, &InputDiagnostic{
			Position: n.pos,
			Length:   len(n.name),
			Code:     CodeParseError,
			Message: fmt.Sprintf("«%s» spells %s, which a binder of this text rebinds here — the abbreviation would be captured",
				n.name, captured[0]),
			Suggestion: "rename the text's binder, or write the term out",
		}
	}
	use, letters, diag := x.instantiateLetters(e, n, applied, stack)
	if diag != nil {
		return nil, nil, diag
	}
	expanded, diag := x.expandNode(use, stack)
	return expanded, letters, diag
}

// instantiateLetters is the AST a use n of entry e, applied to applied
// arguments, reads as: a copy of the entry's text, each letter the
// use ties (`«Name»⟨A:T⟩`) at the tie's type; and, under x.generic, the
// letters the types of the λ-binders the arguments fill write that no
// tie and no free name of the entry fix (pinnedLetters) — the ones the
// builder reads off the arguments' built types before it builds the λ
// (build.go, entryLetterTypes), the copy keeping them as written until
// then, so every pass before the build reads the entry as written. So
// one entry reads at every type pair a statement applies it at, and a
// use no argument fixes reads as the entry's text written out, or at
// its tie. A tie naming a letter the entry is not written at is
// refused, naming the letters it is.
func (x *abbrevExpansion) instantiateLetters(e *abbreviationEntry, n *astAbbrev, applied int, stack []abbrevBinding) (astNode, []string, *InputDiagnostic) {
	use := cloneNode(e.ast, n.pos)
	at := map[string]astType{}
	for _, tie := range n.ties {
		if !slices.Contains(e.letters, tie.varName) {
			written := "no type letter"
			if len(e.letters) > 0 {
				written = "the letters " + strings.Join(e.letters, ", ")
			}
			return nil, nil, &InputDiagnostic{
				Position:   tie.pos,
				Length:     len(tie.varName),
				Code:       CodeParseError,
				Message:    fmt.Sprintf("«%s»⟨%s:…⟩: the entry is written at %s, not %s", n.name, tie.varName, written, tie.varName),
				Suggestion: "tie a letter the entry's text writes",
			}
		}
		at[tie.varName] = tie.ty
	}
	if len(at) > 0 {
		retypeLetters(use, at)
	}
	var fixed []string
	if x.generic && applied > 0 {
		pinned := x.pinnedLetters(e, stack)
		for i, node := 0, astNode(e.ast); i < applied; i++ {
			abs, ok := node.(*astAbsNode)
			if !ok || abs.varType == nil {
				break
			}
			walkTypeLetters(abs.varType, func(letter string) {
				if _, tied := at[letter]; !tied && !pinned(letter) && !slices.Contains(fixed, letter) {
					fixed = append(fixed, letter)
				}
			})
			node = abs.body
		}
	}
	return use, fixed, nil
}

// pinnedLetters reports which of e's letters a free name it spells
// types where the use stands — a binder of the text, a variable of its
// scope: the entry is written over those names, its letter the one
// their types spell, and a use reads it there. A name a binder the text
// writes no type at binds pins every letter; a name nothing types — a
// constant — pins none.
func (x *abbrevExpansion) pinnedLetters(e *abbreviationEntry, stack []abbrevBinding) func(string) bool {
	pinned := map[string]bool{}
	all := false
	for _, f := range e.frees {
		if b := innermost(stack, f); b != nil {
			if b.ty == nil {
				all = true
			}
			walkTypeLetters(b.ty, func(letter string) { pinned[letter] = true })
			continue
		}
		if ty, ok := x.vars[f]; ok {
			for _, v := range ty.TypeVars() {
				pinned[string(v.Name())] = true
			}
		}
	}
	return func(letter string) bool { return all || pinned[letter] }
}

// writtenLetters is the type letters node's own text writes — at a
// binder, in a tie's target — in order of first occurrence; an entry
// node spells is its own entry's.
func writtenLetters(node astNode) []string {
	var out []string
	note := func(t astType) {
		walkTypeLetters(t, func(letter string) {
			if !slices.Contains(out, letter) {
				out = append(out, letter)
			}
		})
	}
	walkAnnotations(node, note)
	return out
}

// walkAnnotations calls visit on every type node's text writes: a
// quantifier's or a λ's binder, a pattern's leaves, the targets of a
// constant's or an abbreviation's ties.
func walkAnnotations(node astNode, visit func(astType)) {
	walkAST(node, func(n astNode) {
		switch n := n.(type) {
		case *astQuantNode:
			if n.varType != nil {
				visit(n.varType)
			}
		case *astAbsNode:
			if n.varType != nil {
				visit(n.varType)
			}
		case *astPatternAbs:
			for _, lf := range n.pat.leaves(nil) {
				if lf.ty != nil {
					visit(lf.ty)
				}
			}
		case *astVar:
			for _, b := range n.typeAnnot {
				visit(b.ty)
			}
		case *astAbbrev:
			for _, b := range n.ties {
				visit(b.ty)
			}
		}
	})
}

// typeLetter is the type variable t names, if it names one: a single
// capital, `var:X`, or a variable node.
func typeLetter(t astType) (string, bool) {
	switch t := t.(type) {
	case *astTypeVar:
		return t.name, true
	case *astTypeNamed:
		if len(t.args) > 0 {
			return "", false
		}
		if rest, ok := strings.CutPrefix(t.name, "var:"); ok {
			return rest, true
		}
		if len(t.name) == 1 && t.name[0] >= 'A' && t.name[0] <= 'Z' {
			return t.name, true
		}
	}
	return "", false
}

// walkTypeLetters calls visit on every type variable t names.
func walkTypeLetters(t astType, visit func(string)) {
	if letter, ok := typeLetter(t); ok {
		visit(letter)
		return
	}
	switch t := t.(type) {
	case *astTypeNamed:
		for _, a := range t.args {
			walkTypeLetters(a, visit)
		}
	case *astTypeFun:
		walkTypeLetters(t.domain, visit)
		walkTypeLetters(t.codomain, visit)
	}
}

// retypeLetters rewrites, in node — a copy no other text shares — every
// type its text writes, each letter at in names replaced by its type.
// The type nodes are rebuilt, never edited: the entry's own share them.
func retypeLetters(node astNode, at map[string]astType) {
	walkAST(node, func(n astNode) {
		switch n := n.(type) {
		case *astQuantNode:
			n.varType = substituteLetters(n.varType, at)
		case *astAbsNode:
			n.varType = substituteLetters(n.varType, at)
		case *astPatternAbs:
			for _, lf := range n.pat.leaves(nil) {
				lf.ty = substituteLetters(lf.ty, at)
			}
		case *astVar:
			for i := range n.typeAnnot {
				n.typeAnnot[i].ty = substituteLetters(n.typeAnnot[i].ty, at)
			}
		case *astAbbrev:
			for i := range n.ties {
				n.ties[i].ty = substituteLetters(n.ties[i].ty, at)
			}
		}
	})
}

// substituteLetters is t with each letter at names replaced by its
// type, rebuilt where it changes; nil stays nil.
func substituteLetters(t astType, at map[string]astType) astType {
	if t == nil {
		return nil
	}
	if letter, ok := typeLetter(t); ok {
		if to, bound := at[letter]; bound {
			return to
		}
		return t
	}
	switch x := t.(type) {
	case *astTypeNamed:
		args := make([]astType, len(x.args))
		changed := false
		for i, a := range x.args {
			args[i] = substituteLetters(a, at)
			changed = changed || args[i] != a
		}
		if !changed {
			return t
		}
		return &astTypeNamed{name: x.name, args: args, pos: x.pos, end: x.end}
	case *astTypeFun:
		dom, cod := substituteLetters(x.domain, at), substituteLetters(x.codomain, at)
		if dom == x.domain && cod == x.codomain {
			return t
		}
		return &astTypeFun{domain: dom, codomain: cod, pos: x.pos, end: x.end, tuple: x.tuple}
	}
	return t
}

// missing is the refusal of a «Name» the table does not declare.
func (t *AbbreviationTable) missing(n *astAbbrev) *InputDiagnostic {
	d := &InputDiagnostic{
		Position: n.pos,
		Length:   len(n.name),
		Code:     CodeParseError,
	}
	if t == nil || len(t.entries) == 0 {
		d.Message = fmt.Sprintf("«%s»: no abbreviation table is in scope here", n.name)
		d.Suggestion = "an abbreviation is declared in the statement's Abbreviations and spelled in that statement and its proof; write the term out here"
		return d
	}
	d.Message = fmt.Sprintf("«%s» is not an abbreviation of this statement (declared: «%s»)", n.name, strings.Join(t.Names(), "», «"))
	d.Suggestion = "declare it in the statement's Abbreviations, or write the term out"
	return d
}

// innermost is the innermost binding of name on the stack, nil when
// none binds it.
func innermost(stack []abbrevBinding, name string) *abbrevBinding {
	for i := len(stack) - 1; i >= 0; i-- {
		if stack[i].name == name {
			return &stack[i]
		}
	}
	return nil
}

// expandProp runs the expansion over a parsed proposition — its body
// and the hypotheses of a sequent form — with the scope's table and
// leading binders.
func expandProp(ast *astProp, scope *ParseScope) *InputDiagnostic {
	x := &abbrevExpansion{}
	if scope != nil {
		x.table, x.binders, x.generic, x.vars = scope.Abbreviations, scope.AbbreviationBinders, scope.FreshenMetaLetters, scope.Vars
	}
	body, diag := expandAbbreviations(ast.body, x)
	if diag != nil {
		return diag
	}
	ast.body = body
	for i := range ast.decls {
		if ast.decls[i].hyp == nil {
			continue
		}
		hyp, diag := expandAbbreviations(ast.decls[i].hyp, x)
		if diag != nil {
			return diag
		}
		ast.decls[i].hyp = hyp
	}
	return nil
}
