// dimension.go — a constant's dimensions, written in its head's ⟨…⟩.
//
// A term-level vector chapter reads its vectors at a num argument:
// `vec(zero, n, u)` is membership in dimension n, `dot(add, mul, n, u,
// v)` folds the first n products, `matrix(zero, n, m, A)` is membership
// in the n×m matrices. The kernel term carries the dimension as an
// ordinary argument. A chapter declares which arguments are dimensions
// (registry.DefEntry.Dim, RowDim/ColumnDim, SourceDim/TargetDim): the
// leading EXPLICIT ones, ConstSyntax.Dims of them. The text writes them
// in the suffix on the constant's name, where an instance's type
// letters stand (`fun_add⟨D:D⟩`), and everything else in the
// parentheses:
//
//	vec⟨n⟩(u)          ↦ vec(zero, n, u)        the scope binds zero
//	vec⟨n⟩(zero, u)    ↦ vec(zero, n, u)        the prefix spelled
//	matrix⟨n, m⟩(A)    ↦ matrix(zero, n, m, A)
//	vec_dist⟨n⟩        ↦ vec_dist(n)            the metric of ℝⁿ
//	dist⟨n⟩(u, v)      ↦ vec_dist(n, u, v)      the overloaded word
//	vec⟨A:real, n⟩(u)                           a type letter beside it
//
// The suffix is the dimension's one place among applications: a
// dimension in the parentheses is refused, with the text to write. A
// notation's subscript is the same argument in the notation
// (`‖u‖_n`, outfix.go).
//
// The parser is scope-free: it reads the suffix's terms as the leading
// arguments of one application and counts them (astApp.dims). Where
// they go depends on whether the parentheses spell the implicit prefix,
// which is the completion pass's decision (implicit.go), so that pass
// places them — completeDimensions, below. foldDimensions is the
// printer's half, run by ChapterSpelling. Nothing below the AST
// changes: the kernel term is the plain application, and so are the key
// and every consumer; the kernel printers print the plain application
// and ChapterSpelling folds it.

package dsl

import (
	"fmt"
	"slices"
	"strings"
)

// Definiendum is the syntax of the name a definition's equation defines,
// which the equation's scope declares as a variable until the mint
// (ParseScope.Definiendum): its implicit prefix and its dimension count,
// as the constant's ConstSyntax will carry them.
type Definiendum struct {
	Name     string
	Implicit []string
	Dims     int
}

// parseHeadAnnotation consumes the `⟨…⟩` suffix of an identifier: type
// bindings `V:T` and dimension terms, comma-separated. The opening `⟨`
// must be the current token. An entry that opens with a name and a `:`
// or `=` is a binding; any other is a term.
func (p *parser) parseHeadAnnotation() ([]typeAnnotBinding, []astNode, *InputDiagnostic) {
	if _, err := p.expect(tokLangle); err != nil {
		return nil, nil, err
	}
	var bindings []typeAnnotBinding
	var dims []astNode
	for {
		if p.peekIsTypeBinding() {
			b, err := p.parseTypeBinding()
			if err != nil {
				return nil, nil, err
			}
			bindings = append(bindings, b)
		} else {
			d, err := p.parseExpr()
			if err != nil {
				return nil, nil, err
			}
			dims = append(dims, d)
		}
		if p.peek().kind == tokComma {
			p.advance()
			continue
		}
		break
	}
	if _, err := p.expect(tokRangle); err != nil {
		return nil, nil, err
	}
	return bindings, dims, nil
}

// peekIsTypeBinding reports whether a `V:T` binding opens at the
// current token: a name and a `:` or `=`.
func (p *parser) peekIsTypeBinding() bool {
	if p.pos+1 >= len(p.tokens) || p.tokens[p.pos].kind != tokIdent {
		return false
	}
	sep := p.tokens[p.pos+1].kind
	return sep == tokColon || sep == tokEq
}

// dimensionError is the completion pass's refusal of a dimension: what
// is wrong, and the text to write.
type dimensionError struct {
	msg string
}

func (e *dimensionError) Error() string { return e.msg }

const dimensionSuggestion = "a constant that declares a dimension (registry.DefEntry.Dim) takes it in the ⟨…⟩ after its name — vec⟨n⟩(u) — and the rest in the parentheses"

// completeDimensions reads an application whose head is a name: where
// the name declares dimensions, it puts the ones the text wrote in ⟨…⟩
// behind the implicit prefix — the scope's, or the one the parentheses
// spell — and refuses one written in the parentheses. handled reports
// that the application is complete as returned; otherwise the ordinary
// completion reads it.
func (c *implicitCompletion) completeDimensions(n *astApp, head *astVar, bound map[string]int) (node astNode, handled bool, err error) {
	definiendum := c.definiendum != nil && c.definiendum.Name == head.name && bound[head.name] == 0 && c.declared(head.name)
	var names []string
	declared := 0
	switch {
	case definiendum:
		names, declared = c.definiendum.Implicit, c.definiendum.Dims
	case bound[head.name] > 0 || c.declared(head.name):
		if n.dims > 0 {
			return nil, true, &dimensionError{fmt.Sprintf(
				"%s⟨…⟩: %s is a variable here, and a dimension in ⟨…⟩ is a constant's", head.name, head.name)}
		}
		return n, false, nil
	default:
		if s := c.syntax.ConstSyntax(head.name); s != nil {
			names, declared = s.Implicit, s.Dims
		}
	}
	if declared == 0 {
		// An overloaded word's dimensions are read where the word is
		// resolved (buildOverload): its constants take no implicit prefix,
		// so the arguments already stand in order.
		if n.dims == 0 || len(c.syntax.OverloadConsts(head.name)) > 0 {
			return n, false, nil
		}
		return nil, true, &dimensionError{fmt.Sprintf(
			"%s declares no dimension: a term in the ⟨…⟩ after a name is a dimension of a constant that declares one", head.name)}
	}
	if n.dimsPlaced {
		return n, false, nil
	}
	if n.dims > declared {
		return nil, true, &dimensionError{fmt.Sprintf(
			"%s takes %d dimension(s) in its ⟨…⟩; the text writes %d", head.name, declared, n.dims)}
	}
	dims, rest := n.args[:n.dims], n.args[n.dims:]
	explicit := true
	if len(names) > 0 && !definiendum {
		matched := c.matchedPrefix(head.name, names, rest, bound)
		recordPrefix := len(rest) > 0 && c.recordSlotMatches(rest[0], names[0], bound)
		switch {
		case matched == len(names):
		case c.spellsPrefix(head.name, head.typeAnnot, names, dims, rest, bound, recordPrefix):
		case matched == 0:
			explicit = false
		default:
			return nil, true, &implicitArgError{fmt.Sprintf(
				"%s: its implicit arguments (%s) are spelled in part — spell all of them or none",
				head.name, strings.Join(names, ", "))}
		}
	}
	if n.dims == 0 {
		// The text wrote no ⟨…⟩: every argument past the implicit prefix
		// would fill a dimension's slot from the parentheses.
		lead := 0
		if explicit {
			lead = len(names)
		}
		if len(rest) > lead {
			return nil, true, dimensionInParentheses(head, rest, lead, declared)
		}
		return n, false, nil
	}
	var lead []astNode
	if explicit {
		if len(rest) < len(names) {
			return nil, true, &dimensionError{fmt.Sprintf(
				"%s⟨…⟩: its implicit arguments (%s) stand before the dimension — spell all of them in the parentheses or none",
				head.name, strings.Join(names, ", "))}
		}
		lead, rest = rest[:len(names)], rest[len(names):]
	} else {
		// The scope's components are picked by the short reading's types:
		// the dimensions, then the written arguments.
		lead, err = c.prefix(head.name, head.typeAnnot, names, n.args, n.pos, bound)
		if err != nil {
			return nil, true, err
		}
	}
	n.args = slices.Concat(lead, dims, rest)
	n.dims, n.dimsPlaced = 0, true
	return n, true, nil
}

// dimensionInParentheses is the refusal of an application that fills a
// dimension's slot from its parentheses, naming the text to write: the
// arguments after the first lead, which are the implicit prefix the
// text spelled, move into the head's ⟨…⟩.
func dimensionInParentheses(head *astVar, args []astNode, lead, declared int) error {
	moved := min(declared, len(args)-lead)
	rewritten := &astApp{
		fun:  head,
		args: slices.Concat(args[lead:lead+moved], args[:lead], args[lead+moved:]),
		dims: moved,
	}
	var pr stmtPrinter
	text, err := pr.node(rewritten, levExpr, true)
	if err != nil {
		text = head.name + "⟨…⟩(…)"
	}
	return &dimensionError{fmt.Sprintf(
		"%s takes its dimension in the ⟨…⟩ after its name, not in the parentheses — write %s", head.name, text)}
}

// refuseDimensionsUnread reports a ⟨…⟩ dimension in a text read with no
// syntax table: which constants declare one is the table's to say.
func refuseDimensionsUnread(roots []*astNode) *InputDiagnostic {
	for _, root := range roots {
		var found *astApp
		walkAST(*root, func(n astNode) {
			if app, ok := n.(*astApp); ok && app.dims > 0 && found == nil {
				found = app
			}
		})
		if found != nil {
			return &InputDiagnostic{Position: found.pos, Code: CodeValidation,
				Message:    "a dimension in ⟨…⟩ is read in a chapter's scope: no syntax table here says which constants declare one",
				Suggestion: dimensionSuggestion}
		}
	}
	return nil
}

// foldDimensions rewrites, bottom-up, every application of a constant
// that declares dimensions into the ⟨…⟩ form: the dimensions it is
// applied to move to the front and are counted. An application whose
// implicit prefix the elision dropped has them first already; one that
// still spells the prefix has them behind it.
func foldDimensions(node astNode, table SyntaxTable, bound map[string]int, declared map[string]bool, changed *bool) astNode {
	fold := func(n astNode) astNode { return foldDimensions(n, table, bound, declared, changed) }
	switch n := node.(type) {
	case *astField:
		n.receiver = fold(n.receiver)
	case *astApp:
		for i, a := range n.args {
			n.args[i] = fold(a)
		}
		head, isVar := n.fun.(*astVar)
		if !isVar {
			n.fun = fold(n.fun)
			return n
		}
		if n.dims > 0 || bound[head.name] > 0 || declared[head.name] {
			return n
		}
		syntax := table.ConstSyntax(head.name)
		if syntax == nil || syntax.Dims == 0 {
			return n
		}
		lead := 0
		if !n.elided {
			lead = len(syntax.Implicit)
		}
		if len(n.args) <= lead {
			return n
		}
		moved := min(syntax.Dims, len(n.args)-lead)
		n.args = slices.Concat(n.args[lead:lead+moved], n.args[:lead], n.args[lead+moved:])
		n.dims = moved
		*changed = true
		return n
	case *astBinOp:
		n.left = fold(n.left)
		n.right = fold(n.right)
	case *astCong:
		n.left = fold(n.left)
		n.right = fold(n.right)
		n.modulus = fold(n.modulus)
	case *astTendsAt:
		n.fn = fold(n.fn)
		n.limit = fold(n.limit)
		n.point = fold(n.point)
	case *astNotNode:
		n.body = fold(n.body)
	case *astCoerce:
		n.operand = fold(n.operand)
	case *astNeg:
		n.operand = fold(n.operand)
	case *astOutfix:
		for i, a := range n.args {
			n.args[i] = fold(a)
		}
		if n.sub != nil {
			n.sub = fold(n.sub)
		}
	case *astQuantNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		n.body = fold(n.body)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astAbsNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		n.body = fold(n.body)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astPatternAbs:
		leaves := n.pat.leaves(nil)
		for _, lf := range leaves {
			bound[lf.name]++
		}
		n.body = fold(n.body)
		for _, lf := range leaves {
			bound[lf.name]--
		}
	case *astBigOp:
		n.bound = fold(n.bound)
		bound[n.binder]++
		n.body = fold(n.body)
		bound[n.binder]--
	}
	return node
}

// dimensioned prints an application in the ⟨…⟩ form: the head's type
// bindings and the dimensions in one suffix, the remaining arguments in
// parentheses, none where the dimensions are all it is applied to.
func (p *stmtPrinter) dimensioned(n *astApp) (string, error) {
	head, ok := n.fun.(*astVar)
	if !ok || n.dims > len(n.args) {
		return "", fmt.Errorf("a ⟨…⟩ dimension on an application whose head is no name")
	}
	entries := make([]string, 0, len(head.typeAnnot)+n.dims)
	for _, b := range head.typeAnnot {
		ty, err := p.typ(b.ty, false)
		if err != nil {
			return "", err
		}
		entries = append(entries, b.varName+":"+ty)
	}
	for _, d := range n.args[:n.dims] {
		s, err := p.node(d, levExpr, true)
		if err != nil {
			return "", err
		}
		entries = append(entries, s)
	}
	out := prettyName(head.name) + "⟨" + strings.Join(entries, ", ") + "⟩"
	if n.dims == len(n.args) {
		return out, nil
	}
	args := make([]string, 0, len(n.args)-n.dims)
	for _, a := range n.args[n.dims:] {
		s, err := p.node(a, levExpr, true)
		if err != nil {
			return "", err
		}
		args = append(args, s)
	}
	return out + "(" + strings.Join(args, ", ") + ")", nil
}
