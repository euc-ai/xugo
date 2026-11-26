// outfix.go — the outfix notation form: `‖u‖_n`, `|x|`.
//
// A chapter declares an outfix notation for a constant at its
// definition (registry.DefEntry.Notation, spelled with the definition's
// own binders — `"‖u‖_n"` for `vnorm(n, u)`), and it arrives here as
// ConstSyntax.Outfix (syntax.go):
//
//	‖u‖_n      ↦ vnorm(n, u)
//	‖u‖_(m+1)  ↦ vnorm(m + 1, u)
//
// The grammar is fixed: an opening delimiter from the lexer's outfix
// alphabet, the body arguments comma-separated, a closing delimiter the
// opening one pairs with — the pair is the notation, so `⟦a, b⟧` and
// `⟦a, b⟭` are two — then an optional subscript `_` followed by an atom
// (a name, a numeral, or a parenthesized expression). The parser is
// scope-free, so it reads any outfix into an astOutfix node; the build
// resolves the pair to the constant in scope that declares it — or,
// where several constants share the delimiters under one overloaded
// word (`|x|` on real_abs, int_abs and complex_abs, the word `abs`), to
// that word, whose build picks the constant by the body's type
// (overload.go) — and re-orders the holes into the constant's argument
// order, before the resolver pre-seed asks after the names and before
// implicit completion supplies the prefix. Nothing below the AST changes: the
// kernel term is the plain application, and so are the key and every
// consumer. foldOutfix and printOutfix are the printer's half, run by
// ChapterSpelling.

package dsl

import (
	"fmt"
	"math/big"
	"strings"
)

// outfixDelimiters is the lexer's outfix alphabet: opening delimiter →
// the closing delimiters it pairs with. A chapter picks a pair from
// here, and a notation is its PAIR: `⟦` and `⟬` each close with `⟧` or
// `⟭`, so `⟦a, b⟧`, `⟬a, b⟭`, `⟦a, b⟭` and `⟬a, b⟧` are four notations
// four constants declare. The lexer knows nothing else about
// notations. `‖` and `|` close themselves. `|` is also the
// set-builder's separator, and the two never meet: the separator
// follows an expression (`{x | φ}`), the notation opens one
// (`{x | |x| < 1}`, `{ |x| | x ∈ s }`), and the parser reads a `|`
// only where an expression begins as a notation.
var outfixDelimiters = map[string][]string{
	"‖": {"‖"},
	"|": {"|"},
	"⟪": {"⟫"},
	"⁅": {"⁆"},
	"⟦": {"⟧", "⟭"},
	"⟬": {"⟭", "⟧"},
}

// OutfixCloses returns the closing delimiters open pairs with, and
// whether open is an outfix delimiter at all — the define door's check
// on a declared notation.
func OutfixCloses(open string) ([]string, bool) {
	c, ok := outfixDelimiters[open]
	return c, ok
}

// outfixTokens maps the delimiter tokens to their spellings, for the
// parser's dispatch and the printer.
func outfixOpenOf(kind tokenKind) (string, bool) {
	switch kind {
	case tokNormBar:
		return "‖", true
	case tokPipe:
		return "|", true
	case tokLDAngle:
		return "⟪", true
	case tokLQuill:
		return "⁅", true
	case tokLDBracket:
		return "⟦", true
	case tokLShell:
		return "⟬", true
	}
	return "", false
}

func outfixCloseKind(close string) tokenKind {
	switch close {
	case "‖":
		return tokNormBar
	case "|":
		return tokPipe
	case "⟫":
		return tokRDAngle
	case "⁆":
		return tokRQuill
	case "⟧":
		return tokRDBracket
	case "⟭":
		return tokRShell
	}
	panic("dsl: outfix close delimiter without a token: " + close)
}

// astOutfix is a parsed outfix notation before the scope names its
// constant: the delimiter pair, the body arguments in reading order,
// and the subscript (nil when absent).
type astOutfix struct {
	open, close string
	args        []astNode
	sub         astNode
	pos         int
}

func (a *astOutfix) nodePos() int { return a.pos }

// parseOutfix reads `<open> args <close> [_ atom]` with the opening
// delimiter token already peeked.
func (p *parser) parseOutfix() (astNode, *InputDiagnostic) {
	tok := p.advance()
	open, _ := outfixOpenOf(tok.kind)
	closes, _ := OutfixCloses(open)
	var args []astNode
	for {
		arg, err := p.parseExpr()
		if err != nil {
			return nil, err
		}
		args = append(args, arg)
		if p.peek().kind != tokComma {
			break
		}
		p.advance()
	}
	closeText := ""
	for _, c := range closes {
		if p.peek().kind == outfixCloseKind(c) {
			closeText = c
		}
	}
	if closeText == "" {
		got := p.peek()
		return nil, &InputDiagnostic{
			Position: got.pos, Length: len(got.text), Code: CodeParseError,
			Message:    fmt.Sprintf("expected %s to close the notation opened by %s, got %q", strings.Join(closes, " or "), open, got.text),
			Suggestion: "a nested notation inside the delimiters needs parentheses",
		}
	}
	p.advance()
	node := &astOutfix{open: open, close: closeText, args: args, pos: tok.pos}
	// The subscript: `_name` lexes as one identifier, `_` alone
	// precedes a parenthesized expression.
	if next := p.peek(); next.kind == tokIdent && strings.HasPrefix(next.text, "_") {
		p.advance()
		rest := strings.TrimPrefix(next.text, "_")
		switch {
		case rest == "":
			if p.peek().kind != tokLParen {
				return nil, &InputDiagnostic{
					Position: next.pos, Length: len(next.text), Code: CodeParseError,
					Message:    "a notation's subscript is `_name`, `_numeral` or `_(expression)`",
					Suggestion: "write the dimension after the underscore",
				}
			}
			p.advance()
			sub, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			if _, err := p.expect(tokRParen); err != nil {
				return nil, err
			}
			node.sub = sub
		case isDigits(rest):
			lit, err := numLitFromText(rest, next.pos+1)
			if err != nil {
				return nil, err
			}
			node.sub = lit
		default:
			node.sub = &astVar{name: rest, pos: next.pos + 1}
		}
	}
	return node, nil
}

// SameOutfixShape says whether two notations place their holes alike —
// what constants sharing one pair of delimiters must agree on.
func SameOutfixShape(a, b *Outfix) bool {
	if a.Open != b.Open || a.Close != b.Close || a.Sub != b.Sub || len(a.Body) != len(b.Body) {
		return false
	}
	for i := range a.Body {
		if a.Body[i] != b.Body[i] {
			return false
		}
	}
	return true
}

// numLitFromText builds a numeral literal node from its decimal text.
func numLitFromText(text string, pos int) (*astNumLit, *InputDiagnostic) {
	v, ok := new(big.Int).SetString(text, 10)
	if !ok {
		return nil, &InputDiagnostic{Position: pos, Length: len(text), Code: CodeParseError,
			Message: fmt.Sprintf("invalid numeric literal %q", text)}
	}
	return &astNumLit{value: v, pos: pos}, nil
}

func isDigits(s string) bool {
	if s == "" {
		return false
	}
	for _, r := range s {
		if r < '0' || r > '9' {
			return false
		}
	}
	return true
}

// ---------------------------------------------------------------------------
// Resolution: the scope names the constant
// ---------------------------------------------------------------------------

// resolveOutfixNotation rewrites every astOutfix under root into the
// application of the constant the scope's syntax table owns the
// delimiter with — or of the overloaded word the constants sharing it
// declare, `|x|` being `abs(x)` in bars, so that the word's build picks
// among them by the body's type exactly as it does for the word
// written out (a variable of the word's name shadows the notation as it
// shadows the word) — the holes reordered into the constant's argument
// order. Runs before implicit completion, which then supplies the
// prefix.
func resolveOutfixNotation(root astNode, table SyntaxTable) (astNode, error) {
	switch n := root.(type) {
	case *astOutfix:
		for i, a := range n.args {
			r, err := resolveOutfixNotation(a, table)
			if err != nil {
				return nil, err
			}
			n.args[i] = r
		}
		if n.sub != nil {
			r, err := resolveOutfixNotation(n.sub, table)
			if err != nil {
				return nil, err
			}
			n.sub = r
		}
		if table == nil {
			return nil, fmt.Errorf("%s…%s: no constant in scope declares this notation", n.open, n.close)
		}
		names := table.OutfixConsts(n.open, n.close)
		if len(names) == 0 {
			return nil, fmt.Errorf("%s…%s: no constant in scope declares this notation", n.open, n.close)
		}
		name := names[0]
		syntax := table.ConstSyntax(name)
		if syntax == nil || syntax.Outfix == nil {
			return nil, fmt.Errorf("%s…%s: %s declares no outfix notation", n.open, n.close, name)
		}
		head := name
		if len(names) > 1 {
			if syntax.Overload == nil {
				return nil, fmt.Errorf("%s…%s: %d constants share the notation and %s declares no overloaded word to read it by", n.open, n.close, len(names), name)
			}
			for _, other := range names[1:] {
				os := table.ConstSyntax(other)
				if os == nil || os.Overload == nil || os.Overload.Word != syntax.Overload.Word || os.Outfix == nil || !SameOutfixShape(os.Outfix, syntax.Outfix) {
					return nil, fmt.Errorf("%s…%s: %s and %s share the notation under different words or shapes", n.open, n.close, name, other)
				}
			}
			head = syntax.Overload.Word
		}
		o := syntax.Outfix
		if len(n.args) != len(o.Body) || (n.sub != nil) != (o.Sub >= 0) {
			return nil, fmt.Errorf("%s: the notation takes %d body argument(s)%s; got %d%s",
				name, len(o.Body), subscriptPhrase(o.Sub >= 0), len(n.args), subscriptPhrase(n.sub != nil))
		}
		args := make([]astNode, o.Arity())
		for i, pos := range o.Body {
			args[pos] = n.args[i]
		}
		if o.Sub >= 0 {
			args[o.Sub] = n.sub
		}
		// The notation writes the constant's dimensions itself — its
		// subscript, `‖u‖_n` — so the application it stands for carries
		// them in argument order, and is not one that wrote a dimension
		// in parentheses (dimension.go).
		return &astApp{fun: &astVar{name: head, pos: n.pos}, args: args, dimsPlaced: syntax.Dims > 0, pos: n.pos}, nil
	case *astField:
		var err error
		n.receiver, err = resolveOutfixNotation(n.receiver, table)
		return n, err
	case *astApp:
		for i, a := range n.args {
			r, err := resolveOutfixNotation(a, table)
			if err != nil {
				return nil, err
			}
			n.args[i] = r
		}
		r, err := resolveOutfixNotation(n.fun, table)
		if err != nil {
			return nil, err
		}
		n.fun = r
		return n, nil
	case *astBinOp:
		var err error
		if n.left, err = resolveOutfixNotation(n.left, table); err != nil {
			return nil, err
		}
		if n.right, err = resolveOutfixNotation(n.right, table); err != nil {
			return nil, err
		}
		return n, nil
	case *astCong:
		var err error
		if n.left, err = resolveOutfixNotation(n.left, table); err != nil {
			return nil, err
		}
		if n.right, err = resolveOutfixNotation(n.right, table); err != nil {
			return nil, err
		}
		if n.modulus, err = resolveOutfixNotation(n.modulus, table); err != nil {
			return nil, err
		}
		return n, nil
	case *astTendsAt:
		var err error
		if n.fn, err = resolveOutfixNotation(n.fn, table); err != nil {
			return nil, err
		}
		if n.limit, err = resolveOutfixNotation(n.limit, table); err != nil {
			return nil, err
		}
		if n.point, err = resolveOutfixNotation(n.point, table); err != nil {
			return nil, err
		}
		return n, nil
	case *astNotNode:
		r, err := resolveOutfixNotation(n.body, table)
		if err != nil {
			return nil, err
		}
		n.body = r
		return n, nil
	case *astCoerce:
		r, err := resolveOutfixNotation(n.operand, table)
		if err != nil {
			return nil, err
		}
		n.operand = r
		return n, nil
	case *astNeg:
		r, err := resolveOutfixNotation(n.operand, table)
		if err != nil {
			return nil, err
		}
		n.operand = r
		return n, nil
	case *astQuantNode:
		r, err := resolveOutfixNotation(n.body, table)
		if err != nil {
			return nil, err
		}
		n.body = r
		return n, nil
	case *astAbsNode:
		r, err := resolveOutfixNotation(n.body, table)
		if err != nil {
			return nil, err
		}
		n.body = r
		return n, nil
	case *astPatternAbs:
		r, err := resolveOutfixNotation(n.body, table)
		if err != nil {
			return nil, err
		}
		n.body = r
		return n, nil
	case *astBigOp:
		var err error
		if n.bound, err = resolveOutfixNotation(n.bound, table); err != nil {
			return nil, err
		}
		if n.body, err = resolveOutfixNotation(n.body, table); err != nil {
			return nil, err
		}
		return n, nil
	}
	return root, nil
}

func subscriptPhrase(has bool) string {
	if has {
		return " and a subscript"
	}
	return ""
}

// resolveNotationRoots runs the resolution over a parse's roots,
// reporting the refusal as a diagnostic.
func resolveNotationRoots(scope *ParseScope, roots []*astNode) *InputDiagnostic {
	var table SyntaxTable
	if scope != nil {
		table = scope.Syntax
	}
	for _, root := range roots {
		if !containsOutfix(*root) {
			continue
		}
		r, err := resolveOutfixNotation(*root, table)
		if err != nil {
			return &InputDiagnostic{Code: CodeValidation, Message: err.Error(),
				Suggestion: "a notation is declared at a chapter's definition (registry.DefEntry.Notation) and read in that chapter's scope"}
		}
		*root = r
	}
	return nil
}

func containsOutfix(node astNode) bool {
	found := false
	walkAST(node, func(n astNode) {
		if _, ok := n.(*astOutfix); ok {
			found = true
		}
	})
	return found
}

// walkAST visits every node under root, parents before children.
func walkAST(root astNode, visit func(astNode)) {
	if root == nil {
		return
	}
	visit(root)
	switch n := root.(type) {
	case *astOutfix:
		for _, a := range n.args {
			walkAST(a, visit)
		}
		walkAST(n.sub, visit)
	case *astField:
		walkAST(n.receiver, visit)
	case *astApp:
		walkAST(n.fun, visit)
		for _, a := range n.args {
			walkAST(a, visit)
		}
	case *astBinOp:
		walkAST(n.left, visit)
		walkAST(n.right, visit)
	case *astCong:
		walkAST(n.left, visit)
		walkAST(n.right, visit)
		walkAST(n.modulus, visit)
	case *astTendsAt:
		walkAST(n.fn, visit)
		walkAST(n.limit, visit)
		walkAST(n.point, visit)
	case *astNotNode:
		walkAST(n.body, visit)
	case *astCoerce:
		walkAST(n.operand, visit)
	case *astNeg:
		walkAST(n.operand, visit)
	case *astQuantNode:
		walkAST(n.body, visit)
	case *astAbsNode:
		walkAST(n.body, visit)
	case *astPatternAbs:
		walkAST(n.body, visit)
	case *astBigOp:
		walkAST(n.bound, visit)
		walkAST(n.body, visit)
	}
}

// foldOutfix rewrites, bottom-up, every full application of a constant
// with an outfix notation into the notation.
func foldOutfix(node astNode, table SyntaxTable, bound map[string]int, declared map[string]bool, changed *bool) astNode {
	switch n := node.(type) {
	case *astField:
		n.receiver = foldOutfix(n.receiver, table, bound, declared, changed)
	case *astApp:
		for i, a := range n.args {
			n.args[i] = foldOutfix(a, table, bound, declared, changed)
		}
		head, isVar := n.fun.(*astVar)
		if !isVar {
			n.fun = foldOutfix(n.fun, table, bound, declared, changed)
			return n
		}
		if bound[head.name] > 0 || declared[head.name] || len(head.typeAnnot) > 0 {
			return n
		}
		syntax := table.ConstSyntax(head.name)
		if syntax == nil || syntax.Outfix == nil || len(n.args) != syntax.Outfix.Arity() {
			return n
		}
		o := syntax.Outfix
		out := &astOutfix{open: o.Open, close: o.Close, pos: n.pos}
		for _, pos := range o.Body {
			out.args = append(out.args, n.args[pos])
		}
		if o.Sub >= 0 {
			out.sub = n.args[o.Sub]
		}
		*changed = true
		return out
	case *astBinOp:
		n.left = foldOutfix(n.left, table, bound, declared, changed)
		n.right = foldOutfix(n.right, table, bound, declared, changed)
	case *astCong:
		n.left = foldOutfix(n.left, table, bound, declared, changed)
		n.right = foldOutfix(n.right, table, bound, declared, changed)
		n.modulus = foldOutfix(n.modulus, table, bound, declared, changed)
	case *astTendsAt:
		n.fn = foldOutfix(n.fn, table, bound, declared, changed)
		n.limit = foldOutfix(n.limit, table, bound, declared, changed)
		n.point = foldOutfix(n.point, table, bound, declared, changed)
	case *astNotNode:
		n.body = foldOutfix(n.body, table, bound, declared, changed)
	case *astCoerce:
		n.operand = foldOutfix(n.operand, table, bound, declared, changed)
	case *astNeg:
		n.operand = foldOutfix(n.operand, table, bound, declared, changed)
	case *astQuantNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		n.body = foldOutfix(n.body, table, bound, declared, changed)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astAbsNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		n.body = foldOutfix(n.body, table, bound, declared, changed)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astPatternAbs:
		leaves := n.pat.leaves(nil)
		for _, lf := range leaves {
			bound[lf.name]++
		}
		n.body = foldOutfix(n.body, table, bound, declared, changed)
		for _, lf := range leaves {
			bound[lf.name]--
		}
	case *astBigOp:
		n.bound = foldOutfix(n.bound, table, bound, declared, changed)
		bound[n.binder]++
		n.body = foldOutfix(n.body, table, bound, declared, changed)
		bound[n.binder]--
	}
	return node
}

// printOutfix renders an astOutfix: the body arguments between the
// delimiters, and the subscript as an atom — a bare name or numeral,
// anything else parenthesized.
func (p *stmtPrinter) printOutfix(n *astOutfix) (string, error) {
	closeText := n.close
	var args []string
	for _, a := range n.args {
		s, err := p.node(a, levExpr, true)
		if err != nil {
			return "", err
		}
		args = append(args, s)
	}
	out := n.open + strings.Join(args, ", ") + closeText
	if n.sub == nil {
		return out, nil
	}
	switch s := n.sub.(type) {
	case *astVar:
		if len(s.typeAnnot) == 0 {
			return out + "_" + prettyName(s.name), nil
		}
	case *astNumLit:
		return out + "_" + s.value.String(), nil
	}
	sub, err := p.node(n.sub, levExpr, true)
	if err != nil {
		return "", err
	}
	return out + "_(" + sub + ")", nil
}
