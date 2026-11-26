package dsl

import (
	"fmt"
	"sort"
	"strings"
)

// Sets on the surface.
//
// `set(τ)` is `τ → bool` (typenames.go); the alias carries the author's
// intent — this binder is a set, used with ∈ ⊆ ∪ …, not a predicate
// applied to a point — and two checks keep the spelling honest:
//
//   - checkSetApplications, at every parse door: an application never
//     consumes a `set(…)` position. `∀s:set(A). s(x)` is refused, and so
//     is `∀t:(A → set(B)). t(x)(y)` — the residual after one argument
//     is a set. A set is written `x ∈ s`.
//   - AnalyzeSetSpelling, for the corpus gate and the respelling sweep:
//     per binder, how the variable is used (applied, or an operand of a
//     set operator, or handed whole to a constant) and the spelling the
//     fold rule gives it. The gate reports a binder declared `X → bool`
//     that is never applied and stands in a set position — a set
//     spelled as a predicate.
//
// The fold rule, for a binder of surface type T applied to at most k
// arguments in its scope: the k consumed domains D₁…Dₖ each fold when
// they are `Y → bool` (a function that takes a set takes a `set(Y)` —
// the DOMAIN direction, reported as such since it is the less certain
// one), and the residual after k arrows folds when it is `X → bool`
// (a residual nobody applies is a set); inside a folded set the element
// type folds again when it is itself `Y → bool` (a set of sets), and
// never through an arrow with a non-bool codomain (a set of relations
// stays `set(A → A → bool)`); `bool → bool` never folds — a boolean
// operation is not a set of truth values. A relation `A → A → bool` applied to two
// arguments folds nothing; applied to one whose result stands in a
// set position it is `A → set(B)`; never applied at all it stays a
// relation — an unapplied residual with a non-bool codomain is not a
// set.

// SetBinder is one binder occurrence of a statement text with its
// declared surface type and the analysis over its scope.
type SetBinder struct {
	Name string
	Pos  int // byte offset of the binder name in the normalized input

	// The declared type's span in the normalized input and its text;
	// a parenthesized type spans its parens.
	TypeStart, TypeEnd int
	TypeText           string

	// Applied is the largest argument count the variable is applied to
	// in its scope; 0 when it only ever stands whole.
	Applied int
	// Evidence classifies the strongest unapplied use: "operator" (an
	// operand of ∈ ∉ ⊆ ⊊ ∪ ∩ ∖, ⋃ ⋂, a Σ range, or an equation with a
	// set-shaped partner), "constant:<head>" (handed whole to a
	// constant), "" (none: unused, or only beside variables).
	Evidence string

	// Folded is the type respelled by the fold rule, "" when the rule
	// changes nothing. DomainFold marks a fold in a parameter position.
	Folded     string
	DomainFold bool
	// Shared: the type text is one node shared by several binders
	// (`∀x y:T.`); Conflict: those binders disagree on the fold, so the
	// text is left alone. Tuple: the type uses the `(A, B) → C` sugar,
	// which has no contiguous subterm text to splice; left alone.
	// Unspliced: RespellSets left the fold out because the raw input
	// spells the type's span differently from the normalized text
	// (an ASCII arrow, a subscript) — byte surgery would change more
	// than the fold.
	Shared, Conflict, Tuple, Unspliced bool
}

// SpelledAsPredicate is the gate's finding: a binder declared as an
// arrow that is never applied and stands in a set position — a set
// spelled `X → bool`.
func (b SetBinder) SpelledAsPredicate() bool {
	return b.Applied == 0 && b.Evidence == "operator" && b.Folded != "" && !b.Tuple && !b.Conflict
}

// SetSpellingReport is AnalyzeSetSpelling's result.
type SetSpellingReport struct {
	// Normalized is the input after symbol normalization — the text
	// every span indexes. Verbatim reports whether it equals the raw
	// input byte for byte.
	Normalized string
	Verbatim   bool
	Binders    []SetBinder
	Errors     []InputDiagnostic
}

// AnalyzeSetSpelling parses raw as a statement (a prop, or a bare
// expression — a λ-term claim) and reports every typed binder with its
// use and fold. A parse error is reported, not built around.
func AnalyzeSetSpelling(raw string) SetSpellingReport {
	normalized, _ := NormalizeTextSymbols(raw)
	rep := SetSpellingReport{Normalized: normalized, Verbatim: normalized == raw}
	tokens, lexErr := lex(normalized)
	if lexErr != nil {
		rep.Errors = append(rep.Errors, *lexErr)
		return rep
	}
	par := &parser{tokens: tokens}
	ast, perr := par.parseProp()
	if perr != nil {
		rep.Errors = append(rep.Errors, *perr)
		return rep
	}
	if par.pos < len(par.tokens) && par.tokens[par.pos].kind != tokEOF {
		tok := par.tokens[par.pos]
		rep.Errors = append(rep.Errors, InputDiagnostic{Position: tok.pos, Length: len(tok.text), Code: CodeParseError,
			Message: fmt.Sprintf("unexpected token %q after complete expression", tok.text)})
		return rep
	}
	w := &surfaceWalker{scope: map[string][]*binderRec{}}
	w.walk(ast)

	// Fold per record; then consensus per shared type node.
	byType := map[astType][]int{}
	for _, r := range w.recs {
		if r.ty == nil {
			continue
		}
		b := SetBinder{Name: r.name, Pos: r.pos, TypeStart: r.ty.typePos(), TypeEnd: r.ty.typeEnd(),
			Applied: r.applied, Evidence: r.evidence}
		b.TypeText = normalized[b.TypeStart:b.TypeEnd]
		folds, domainFold := foldPlan(r.ty, r.applied)
		if len(folds) > 0 {
			if text, ok := renderFold(normalized, r.ty, folds); ok {
				if text != b.TypeText {
					b.Folded, b.DomainFold = text, domainFold
				}
			} else {
				b.Tuple = true
			}
		}
		byType[r.ty] = append(byType[r.ty], len(rep.Binders))
		rep.Binders = append(rep.Binders, b)
	}
	for _, idxs := range byType {
		if len(idxs) < 2 {
			continue
		}
		first := rep.Binders[idxs[0]].Folded
		conflict := false
		for _, i := range idxs[1:] {
			if rep.Binders[i].Folded != first {
				conflict = true
			}
		}
		for _, i := range idxs {
			rep.Binders[i].Shared = true
			rep.Binders[i].Conflict = conflict
		}
	}
	return rep
}

// Respelling is one splice of the fold: the raw bytes [Start, End) of
// a binder's type, the text that replaces them, and the binder's name.
type Respelling struct {
	Start, End int
	Text       string
	Name       string
}

// SetRespellings computes the fold rule's splices for raw: every binder
// whose fold changes its spelling, is not in conflict and is not
// tuple-sugared — each type span located back through the symbol
// normalizer's offset map and kept only when the raw bytes of the span
// are the normalized ones (Unspliced otherwise). The splices come in
// descending order of Start, non-overlapping, so applying them in
// order is byte surgery on raw; an input that does not parse yields
// none.
func SetRespellings(raw string) ([]Respelling, SetSpellingReport) {
	rep := AnalyzeSetSpelling(raw)
	if len(rep.Errors) > 0 {
		return nil, rep
	}
	rawOffset := normalizedOffsetMap(raw)
	seen := map[int]bool{}
	var splices []Respelling
	for i := range rep.Binders {
		b := &rep.Binders[i]
		if b.Folded == "" || b.Conflict || b.Tuple || seen[b.TypeStart] {
			continue
		}
		seen[b.TypeStart] = true
		rs, re := rawOffset(b.TypeStart), rawOffset(b.TypeEnd)
		if raw[rs:re] != rep.Normalized[b.TypeStart:b.TypeEnd] {
			b.Unspliced = true
			continue
		}
		splices = append(splices, Respelling{rs, re, b.Folded, b.Name})
	}
	sort.Slice(splices, func(i, j int) bool { return splices[i].Start > splices[j].Start })
	last := len(raw) + 1
	for _, s := range splices {
		if s.End > last {
			// Overlapping spans cannot happen for distinct binder types;
			// refuse the whole rewrite rather than corrupt the text.
			return nil, rep
		}
		last = s.Start
	}
	return splices, rep
}

// RespellSets applies SetRespellings to raw.
func RespellSets(raw string) (string, SetSpellingReport) {
	splices, rep := SetRespellings(raw)
	out := raw
	for _, s := range splices {
		out = out[:s.Start] + s.Text + out[s.End:]
	}
	return out, rep
}

// normalizedOffsetMap replays NormalizeTextSymbols' two passes — the
// subscript denormalization (`t₁` → `t_1`) and the ASCII symbol
// rewrites (`->` → `→`) — as an offset map from the normalized text
// back to raw. A byte inside a rewritten stretch maps to that stretch's
// start; the byte after it maps to the byte after the raw stretch.
func normalizedOffsetMap(raw string) func(int) int {
	// Pass 1: subscripts. midToRaw[i] is the raw offset of mid byte i.
	var mid strings.Builder
	var midToRaw []int
	inRun := false
	for off, r := range raw {
		if r >= '₀' && r <= '₉' {
			if !inRun {
				mid.WriteByte('_')
				midToRaw = append(midToRaw, off)
				inRun = true
			}
			mid.WriteRune('0' + (r - '₀'))
			midToRaw = append(midToRaw, off)
		} else {
			n := mid.Len()
			mid.WriteRune(r)
			for j := n; j < mid.Len(); j++ {
				midToRaw = append(midToRaw, off+(j-n))
			}
			inRun = false
		}
	}
	midToRaw = append(midToRaw, len(raw))
	midText := mid.String()
	// Pass 2: the symbol rewrites, positions in the mid text.
	normalized, symbols := NormalizeTextSymbols(raw)
	normToMid := make([]int, 0, len(normalized)+1)
	m := 0
	for _, sym := range symbols {
		for ; m < sym.Position; m++ {
			normToMid = append(normToMid, m)
		}
		for range len(sym.To) {
			normToMid = append(normToMid, sym.Position)
		}
		m = sym.Position + sym.Length
	}
	for ; m < len(midText); m++ {
		normToMid = append(normToMid, m)
	}
	normToMid = append(normToMid, len(midText))
	return func(n int) int {
		if n < 0 || n >= len(normToMid) {
			return len(raw)
		}
		return midToRaw[normToMid[n]]
	}
}

// checkSetApplications is the parse-door check: an application that
// consumes a `set(…)` position of a declared binder is an error.
func checkSetApplications(root astNode) []InputDiagnostic {
	w := &surfaceWalker{scope: map[string][]*binderRec{}, check: true}
	w.walk(root)
	return w.diags
}

// ---------------------------------------------------------------------------
// The walk
// ---------------------------------------------------------------------------

type binderRec struct {
	name     string
	pos      int
	ty       astType // nil: an untyped binder (it still shadows)
	applied  int
	evidence string
}

type surfaceWalker struct {
	scope map[string][]*binderRec
	recs  []*binderRec
	diags []InputDiagnostic
	check bool
}

func (w *surfaceWalker) push(name string, ty astType, pos int) {
	r := &binderRec{name: name, pos: pos, ty: ty}
	w.scope[name] = append(w.scope[name], r)
	w.recs = append(w.recs, r)
}

func (w *surfaceWalker) pop(name string) {
	st := w.scope[name]
	w.scope[name] = st[:len(st)-1]
}

func (w *surfaceWalker) lookup(name string) *binderRec {
	st := w.scope[name]
	if len(st) == 0 {
		return nil
	}
	return st[len(st)-1]
}

// evidenceRank orders the classes so a stronger use is never overwritten.
func evidenceRank(ev string) int {
	switch {
	case ev == "operator":
		return 2
	case strings.HasPrefix(ev, "constant:"):
		return 1
	}
	return 0
}

// operand visits n in the position described by ev: a bare bound
// variable records the evidence, anything else is walked.
func (w *surfaceWalker) operand(n astNode, ev string) {
	if v, ok := n.(*astVar); ok {
		if r := w.lookup(v.name); r != nil && evidenceRank(ev) > evidenceRank(r.evidence) {
			r.evidence = ev
		}
		return
	}
	w.walk(n)
}

func (w *surfaceWalker) walk(n astNode) {
	switch n := n.(type) {
	case *astProp:
		var pushed []string
		for _, d := range n.decls {
			if d.name != "" && d.typeStr != nil {
				w.push(d.name, d.typeStr, d.pos)
				pushed = append(pushed, d.name)
			}
		}
		for _, d := range n.decls {
			if d.hyp != nil {
				w.walk(d.hyp)
			}
		}
		w.walk(n.body)
		for i := len(pushed) - 1; i >= 0; i-- {
			w.pop(pushed[i])
		}
	case *astField:
		w.walk(n.receiver)
	case *astApp:
		w.app(n)
	case *astBinOp:
		w.binop(n)
	case *astCong:
		w.walk(n.left)
		w.walk(n.right)
		w.walk(n.modulus)
	case *astTendsAt:
		w.walk(n.fn)
		w.walk(n.limit)
		w.walk(n.point)
	case *astNotNode:
		w.walk(n.body)
	case *astCoerce:
		w.walk(n.operand)
	case *astNeg:
		w.walk(n.operand)
	case *astQuantNode:
		w.push(n.varName, n.varType, n.pos)
		w.walk(n.body)
		w.pop(n.varName)
	case *astAbsNode:
		w.push(n.varName, n.varType, n.pos)
		w.walk(n.body)
		w.pop(n.varName)
	case *astPatternAbs:
		leaves := n.pat.leaves(nil)
		for _, lf := range leaves {
			w.push(lf.name, lf.ty, lf.pos)
		}
		w.walk(n.body)
		for i := len(leaves) - 1; i >= 0; i-- {
			w.pop(leaves[i].name)
		}
	case *astBigOp:
		if n.rel == "∈" {
			w.operand(n.bound, "operator")
		} else {
			w.walk(n.bound)
		}
		w.push(n.binder, nil, n.pos)
		w.walk(n.body)
		w.pop(n.binder)
	case *astOutfix:
		for _, a := range n.args {
			w.walk(a)
		}
		if n.sub != nil {
			w.walk(n.sub)
		}
	case *astVar:
		w.operand(n, "")
	case *astConst, *astNumLit, *astTermLit, nil:
	}
}

// isSetOperator: the infix set operators; both operands are sets (for
// ∈ and ∉ the left is an element — of a family of sets when it is a
// set-typed binder, which the corpus reads as a set too).
func isSetOperator(op string) bool {
	switch op {
	case "∈", "∉", "⊆", "⊊", "∪", "∩", "∖":
		return true
	}
	return false
}

func (w *surfaceWalker) binop(n *astBinOp) {
	switch {
	case isSetOperator(n.op):
		w.operand(n.left, "operator")
		w.operand(n.right, "operator")
	case n.op == "=" || n.op == "≠":
		left, right := "", ""
		if isSetShaped(n.right) {
			left = "operator"
		}
		if isSetShaped(n.left) {
			right = "operator"
		}
		w.operand(n.left, left)
		w.operand(n.right, right)
	default:
		w.walk(n.left)
		w.walk(n.right)
	}
}

// isSetShaped: an expression that is a set by its head — the nullary
// set constants, a set-builder or enumeration, a big operator, an
// image, or a set operator application.
func isSetShaped(n astNode) bool {
	switch n := n.(type) {
	case *astVar:
		return n.name == "empty_set" || n.name == "universe"
	case *astApp:
		if f, ok := n.fun.(*astVar); ok {
			switch f.name {
			case "set_comprehension", "insert", "big_union", "big_intersection", "image":
				return true
			}
		}
	case *astBinOp:
		return n.op == "∪" || n.op == "∩" || n.op == "∖"
	}
	return false
}

func (w *surfaceWalker) app(n *astApp) {
	switch f := n.fun.(type) {
	case *astVar:
		r := w.lookup(f.name)
		if r != nil {
			if len(n.args) > r.applied {
				r.applied = len(n.args)
			}
			if w.check {
				w.checkApplied(f.name, r.ty, n)
			}
		}
		ev := ""
		if r == nil {
			switch f.name {
			case "big_union", "big_intersection":
				ev = "operator"
			default:
				ev = "constant:" + f.name
			}
		}
		for _, a := range n.args {
			w.operand(a, ev)
		}
	case *astApp:
		w.walk(f)
		if w.check {
			if name, ty := w.surfaceAfter(f); ty != nil {
				w.checkApplied(name, ty, n)
			}
		}
		for _, a := range n.args {
			w.operand(a, "")
		}
	default:
		w.walk(n.fun)
		for _, a := range n.args {
			w.operand(a, "")
		}
	}
}

// surfaceAfter is the surface type of an applied head after its own
// arguments, for a curried outer application; nil when unknown or when
// the inner application already consumed a set position (reported
// there).
func (w *surfaceWalker) surfaceAfter(n astNode) (string, astType) {
	switch n := n.(type) {
	case *astVar:
		if r := w.lookup(n.name); r != nil {
			return n.name, r.ty
		}
	case *astApp:
		name, cur := w.surfaceAfter(n.fun)
		for range n.args {
			fun, ok := cur.(*astTypeFun)
			if !ok {
				return name, nil
			}
			cur = fun.codomain
		}
		return name, cur
	}
	return "", nil
}

func (w *surfaceWalker) checkApplied(name string, ty astType, n *astApp) {
	cur := ty
	for i := range n.args {
		if named, ok := cur.(*astTypeNamed); ok && named.name == typeAliasSet {
			consumed := ""
			if i > 0 {
				consumed = fmt.Sprintf(" after %d argument(s)", i)
			}
			w.diags = append(w.diags, InputDiagnostic{
				Position: n.pos, Length: len(name), Code: CodeSetApplied,
				Message: fmt.Sprintf("%s is declared %s and applied as a function%s; a set is used with ∈, never applied",
					name, typeText(ty), consumed),
				Suggestion: fmt.Sprintf("write x ∈ %s; if %s is a predicate, declare it %s", name, name, typeText(unfoldSet(ty))),
			})
			return
		}
		fun, ok := cur.(*astTypeFun)
		if !ok {
			return
		}
		cur = fun.codomain
	}
}

// unfoldSet respells every set(τ) of a surface type as τ → bool, for
// the suggestion of the applied-set diagnostic.
func unfoldSet(t astType) astType {
	switch t := t.(type) {
	case *astTypeNamed:
		if t.name == typeAliasSet && len(t.args) == 1 {
			return &astTypeFun{domain: unfoldSet(t.args[0]), codomain: &astTypeNamed{name: "bool"}}
		}
		if len(t.args) == 0 {
			return t
		}
		args := make([]astType, len(t.args))
		for i, a := range t.args {
			args[i] = unfoldSet(a)
		}
		return &astTypeNamed{name: t.name, args: args}
	case *astTypeFun:
		return &astTypeFun{domain: unfoldSet(t.domain), codomain: unfoldSet(t.codomain)}
	}
	return t
}

// ---------------------------------------------------------------------------
// The fold rule and its rendering
// ---------------------------------------------------------------------------

func isBoolName(t astType) bool {
	n, ok := t.(*astTypeNamed)
	return ok && n.name == "bool" && len(n.args) == 0
}

// isUnaryBool: `X → bool` on the surface (not the tuple sugar), with X
// not bool itself — `bool → bool` is a boolean operation, never a set.
func isUnaryBool(t astType) bool {
	f, ok := t.(*astTypeFun)
	return ok && !f.tuple && isBoolName(f.codomain) && !isBoolName(f.domain)
}

func markElem(x astType, folds map[astType]bool) {
	if isUnaryBool(x) {
		folds[x] = true
		markElem(x.(*astTypeFun).domain, folds)
	}
}

// foldPlan applies the fold rule to a binder of surface type t applied
// to at most applied arguments; the result names the nodes to respell
// as set(…) and whether any is a parameter position.
func foldPlan(t astType, applied int) (folds map[astType]bool, domainFold bool) {
	folds = map[astType]bool{}
	cur := t
	for i := 0; i < applied; i++ {
		fun, ok := cur.(*astTypeFun)
		if !ok || fun.tuple {
			return folds, domainFold
		}
		if isUnaryBool(fun.domain) {
			folds[fun.domain] = true
			domainFold = true
			markElem(fun.domain.(*astTypeFun).domain, folds)
		}
		cur = fun.codomain
	}
	if isUnaryBool(cur) {
		folds[cur] = true
		markElem(cur.(*astTypeFun).domain, folds)
	}
	return folds, domainFold
}

// renderFold spells t with the planned folds applied, keeping every
// unfolded byte of src as it was. ok is false at the tuple sugar.
func renderFold(src string, t astType, folds map[astType]bool) (string, bool) {
	switch t := t.(type) {
	case *astTypeFun:
		if t.tuple {
			return "", false
		}
		if folds[t] {
			inner, ok := renderFold(src, t.domain, folds)
			if !ok {
				return "", false
			}
			return "set(" + stripOuterParens(inner) + ")", true
		}
		dom, ok := renderFold(src, t.domain, folds)
		if !ok {
			return "", false
		}
		cod, ok := renderFold(src, t.codomain, folds)
		if !ok {
			return "", false
		}
		return src[t.pos:t.domain.typePos()] + dom +
			src[t.domain.typeEnd():t.codomain.typePos()] + cod +
			src[t.codomain.typeEnd():t.end], true
	case *astTypeNamed:
		return src[t.pos:t.end], true
	case *astTypeVar:
		return src[t.pos:t.end], true
	}
	return "", false
}

// stripOuterParens removes one pair of parens enclosing the whole text.
func stripOuterParens(s string) string {
	if !strings.HasPrefix(s, "(") || !strings.HasSuffix(s, ")") {
		return s
	}
	depth := 0
	for i, r := range s {
		switch r {
		case '(':
			depth++
		case ')':
			depth--
			if depth == 0 && i != len(s)-1 {
				return s
			}
		}
	}
	return strings.TrimSpace(s[1 : len(s)-1])
}
