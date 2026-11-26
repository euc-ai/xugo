package xugofmt

import (
	"bytes"
	"go/ast"
	"go/format"
	"go/parser"
	"go/token"
	"slices"
	"strings"
)

// A line of code past LineWidth columns, counted from its indentation,
// is broken at a list that stands on it: the arguments of a call, the elements of a composite literal,
// the parameters of a function where it has two or more, the values of
// an assignment, of a declaration or of a return.
//
// The arguments of a call go to the line under its opening parenthesis,
// together where that line holds them and one to a line where it does
// not, and the closing parenthesis stays after the last:
//
//	polynomial_evaluation.EvalMul.Read(R).AsFact().At(
//		linearR, cofactor, a)
//
//	At(
//		ring_ideal.IdealMul,
//		ringRTerm,
//		d.TermAs[B]("ι(M.inv(h(0)))"),
//		d.TermAs[B]("ι(h(0))"))
//
// The values of an assignment or a declaration stand under its operator
// the same way; a return's first value stays after `return` and the
// others take a line each. The elements of a literal and the parameters
// of a function take a line each, and the literal's brace and the
// parameter list's parenthesis a line of their own after a comma:
//
//	}, func(
//		a *Argument,
//		R *Expr[RingOps[A]],
//		i, j *Expr[Nat],
//	) {
//
// The list broken is the outermost one with two or more elements on
// the line. A list of one element is broken after its opener where
// that brings the element's line inside the width, the outermost such
// list first, and otherwise the innermost one is, which leaves the
// element the widest line it can have:
//
//	restricted := a.TermAs[RingOps[A]](
//		"mk_ring(G.add, G.zero, G.neg, G.mul, G.one, G.sub, F.carrier)")
//
// An element that spans lines keeps its place, and so does every
// element before it: moving one would indent the lines it spans, and
// the list is broken after the last such element only. A text over
// several lines is no such element: its lines are its layout's. An
// abbreviation entry is not broken: its Text is laid out after its Name
// (fold.go).
//
// A comment that ends a line past the width stands on the line above,
// at the line's indentation.

// lineList is a list of a file whose elements a line break may part:
// its elements, the opener the first of them may leave for a line of
// its own, and the closer that takes a line of its own, after a comma,
// when the list is broken. A list of values has an opener only where
// an assignment or a declaration's `=` is one; a call's closing
// parenthesis is no closer. together says the elements stand on one
// line under the opener where that line holds them: a call's arguments,
// an assignment's or a declaration's values.
type lineList struct {
	elts          []ast.Node
	together      bool
	opener        int // the offset after the opener; -1 where the list has none
	closer        int // the closer's offset; -1 where it stays
	first, last   int // the lines the list spans
	edits         []_Edit
	onLine        map[int]bool // the lines its breakable gaps stand on
	eltLine       int          // a one-element list: the line of its opener gap
	gain, remains int          // a one-element list: the columns a break saves its element, and the element's line after it
}

// settleWideLines breaks each line of src past LineWidth at a list on
// it, or moves the comment that ends it to the line above, and reports
// settled when no line past the width has either to give. A line that a
// break of this pass changes waits for the next pass, which measures it
// as it then stands.
func settleWideLines(src []byte) (out []byte, settled bool, err error) {
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "", src, parser.ParseComments)
	if err != nil {
		return nil, false, err
	}
	lines := bytes.Split(src, []byte("\n"))
	var wide []int
	for i, line := range lines {
		if ContentWidth(string(line)) > LineWidth {
			wide = append(wide, i+1)
		}
	}
	if len(wide) == 0 {
		return src, true, nil
	}
	lists := lineLists(fset, file, src)
	trailing := trailingComments(fset, file, src)
	var edits []_Edit
	changed := map[int]bool{}
	for _, line := range wide {
		if changed[line] {
			continue
		}
		if move, moves := trailing[line]; moves {
			edits = append(edits, move...)
			changed[line] = true
			continue
		}
		list := listToBreak(lists, line, changed)
		if list == nil {
			continue
		}
		edits = append(edits, list.edits...)
		for l := list.first; l <= list.last; l++ {
			changed[l] = true
		}
	}
	if len(edits) == 0 {
		return src, true, nil
	}
	out, err = format.Source(applyEdits(src, edits))
	return out, false, err
}

// listToBreak is the list a wide line is broken at, of lists in the
// order a file opens them: the outermost list of several elements with
// a gap on the line, unless a list of one element outside it brings
// the element's line inside the width, and the innermost list of one
// element that a break narrows where the line has no other. A list on
// a line this pass has changed is none.
func listToBreak(lists []*lineList, line int, changed map[int]bool) *lineList {
	var fallback *lineList
	for _, list := range lists {
		if !list.onLine[line] {
			continue
		}
		free := true
		for l := list.first; l <= list.last && free; l++ {
			free = !changed[l]
		}
		if !free {
			continue
		}
		if len(list.elts) > 1 {
			return list
		}
		if list.eltLine != line || list.gain <= 0 {
			continue
		}
		if list.remains <= LineWidth {
			return list
		}
		fallback = list
	}
	return fallback
}

// lineLists are the lists of file that have a gap a line break may
// take, in the order the file opens them, each with the edits that
// break it.
func lineLists(fset *token.FileSet, file *ast.File, src []byte) []*lineList {
	offset := func(p token.Pos) int { return inSource(fset, p).Offset }
	var lists []*lineList
	add := func(elts []ast.Node, opener, closer int) *lineList {
		list := &lineList{elts: elts, opener: opener, closer: closer}
		lists = append(lists, list)
		return list
	}
	var stack []ast.Node
	ast.Inspect(file, func(n ast.Node) bool {
		if n == nil {
			stack = stack[:len(stack)-1]
			return true
		}
		stack = append(stack, n)
		switch n := n.(type) {
		case *ast.CallExpr:
			add(nodes(n.Args), offset(n.Lparen)+1, -1).together = true
		case *ast.CompositeLit:
			if !abbreviationEntry(stack) {
				add(nodes(n.Elts), offset(n.Lbrace)+1, offset(n.Rbrace))
			}
		case *ast.FuncType:
			if n.Params != nil && n.Params.Opening.IsValid() && len(n.Params.List) > 1 {
				add(nodes(n.Params.List), offset(n.Params.Opening)+1, offset(n.Params.Closing))
			}
		case *ast.AssignStmt:
			if len(n.Rhs) > 1 {
				add(nodes(n.Rhs), offset(n.TokPos)+len(n.Tok.String()), -1).together = true
			}
		case *ast.ValueSpec:
			if len(n.Values) > 1 {
				before := offset(n.Names[len(n.Names)-1].End())
				if n.Type != nil {
					before = offset(n.Type.End())
				}
				if eq := bytes.IndexByte(src[before:offset(n.Values[0].Pos())], '='); eq >= 0 {
					add(nodes(n.Values), before+eq+1, -1).together = true
				}
			}
		case *ast.ReturnStmt:
			if len(n.Results) > 1 {
				add(nodes(n.Results), -1, -1)
			}
		}
		return true
	})
	var broken []*lineList
	for _, list := range lists {
		if list.settle(fset, src) {
			broken = append(broken, list)
		}
	}
	return broken
}

// nodes are the elements of a list as nodes.
func nodes[T ast.Node](list []T) []ast.Node {
	out := make([]ast.Node, len(list))
	for i, n := range list {
		out[i] = n
	}
	return out
}

// settle computes the edits that break the list one element to a line
// and the lines its gaps stand on, and reports whether it has any. A
// gap is the blanks between the opener and the first element, between
// an element's comma and the next element, or between the last element
// and the closer, where the two stand on one line with no comment
// between them. The gaps before the last element that spans lines and
// is no text are not broken.
func (list *lineList) settle(fset *token.FileSet, src []byte) bool {
	if len(list.elts) == 0 {
		return false
	}
	offset := func(p token.Pos) int { return inSource(fset, p).Offset }
	tokens := fset.File(list.elts[0].Pos())
	lineOf := func(at int) int { return inSource(fset, tokens.Pos(at)).Line }
	spans := -1
	for i, elt := range list.elts {
		if !isText(elt) && bytes.IndexByte(src[offset(elt.Pos()):offset(elt.End())], '\n') >= 0 {
			spans = i
		}
	}
	list.first = lineOf(offset(list.elts[0].Pos()))
	if list.opener >= 0 {
		list.first = lineOf(list.opener)
	}
	end := offset(list.elts[len(list.elts)-1].End())
	if list.closer >= 0 {
		end = list.closer
	}
	list.last = lineOf(end)
	list.onLine = map[int]bool{}
	for i := spans + 1; i < len(list.elts); i++ {
		from, to := list.opener, offset(list.elts[i].Pos())
		if i > 0 {
			from = offset(list.elts[i-1].End())
			gap := string(src[from:to])
			afterComma := strings.TrimLeft(gap, " \t")
			if !strings.HasPrefix(afterComma, ",") {
				continue
			}
			from += len(gap) - len(afterComma) + 1
		}
		if from < 0 || strings.Trim(string(src[from:to]), " \t") != "" {
			continue
		}
		list.edits = append(list.edits, _Edit{from, to, "\n"})
		list.onLine[lineOf(to)] = true
		if i == 0 && len(list.elts) == 1 {
			list.eltLine = lineOf(to)
			list.gain, list.remains = lineUnder(src, to)
		}
	}
	if first := offset(list.elts[0].Pos()); list.together && len(list.edits) == len(list.elts) && len(list.onLine) == 1 {
		if _, remains := lineUnder(src, first); remains <= LineWidth {
			list.edits = list.edits[:1]
		}
	}
	if list.closer >= 0 && spans < len(list.elts)-1 && len(list.edits) > 0 {
		from := offset(list.elts[len(list.elts)-1].End())
		if gap := strings.Trim(string(src[from:list.closer]), " \t"); gap == "" || gap == "," {
			list.edits = append(list.edits, _Edit{from, list.closer, ",\n"})
		}
	}
	return len(list.edits) > 0
}

// lineUnder measures a break before offset at, which puts the rest of
// the line on a line of its own one tab in: the columns the break saves
// what stands at at, and the columns the line it then opens takes past
// its indentation.
func lineUnder(src []byte, at int) (gain, remains int) {
	lineStart := bytes.LastIndexByte(src[:at], '\n') + 1
	lineEnd := len(src)
	if next := bytes.IndexByte(src[at:], '\n'); next >= 0 {
		lineEnd = at + next
	}
	indent := lineStart
	for indent < len(src) && src[indent] == '\t' {
		indent++
	}
	under := Width(string(src[lineStart:indent])) + tabWidth
	return Width(string(src[lineStart:at])) - under, Width(string(src[at:lineEnd]))
}

// isText reports whether elt is a text, or a field holding one: a
// string literal or a chain of them, whose lines are its layout's
// (fold.go, prose.go) and move with it.
func isText(elt ast.Node) bool {
	if kv, isKV := elt.(*ast.KeyValueExpr); isKV {
		elt = kv.Value
	}
	e, isExpr := elt.(ast.Expr)
	return isExpr && literalChain(e) != nil
}

// trailingComments are, by line, the edits that move the `//` comment
// ending a line of code to the line above, at the line's indentation.
// A line that opens with a closing bracket keeps its comment: above it
// the comment would stand inside the brackets the line closes. So does
// a line that opens inside a chain of literals: above it the comment
// would stand inside the text, which keeps its lines while it holds one
// (textFolds).
func trailingComments(fset *token.FileSet, file *ast.File, src []byte) map[int][]_Edit {
	chains := literalChains(fset, file)
	moves := map[int][]_Edit{}
	for _, group := range file.Comments {
		for _, comment := range group.List {
			if !strings.HasPrefix(comment.Text, "//") {
				continue
			}
			at := inSource(fset, comment.Pos())
			lineStart := at.Offset - (at.Column - 1)
			code := strings.TrimRight(string(src[lineStart:at.Offset]), " \t")
			indent := code[:len(code)-len(strings.TrimLeft(code, "\t"))]
			if opening := strings.TrimLeft(code, "\t"); opening == "" || strings.IndexByte(")]}", opening[0]) >= 0 {
				continue
			}
			if slices.ContainsFunc(chains, func(chain _Span) bool { return chain.from < lineStart && lineStart < chain.to }) {
				continue
			}
			moves[at.Line] = []_Edit{
				{lineStart, lineStart, indent + comment.Text + "\n"},
				{lineStart + len(code), at.Offset + len(comment.Text), ""},
			}
		}
	}
	return moves
}

// _Span is the bytes from..to of a source.
type _Span struct{ from, to int }

// literalChains are the bytes each chain of string literals joined by
// `+` takes in file, from its first literal to its last.
func literalChains(fset *token.FileSet, file *ast.File) []_Span {
	var chains []_Span
	ast.Inspect(file, func(n ast.Node) bool {
		chain, isChain := n.(*ast.BinaryExpr)
		if !isChain || literalChain(chain) == nil {
			return true
		}
		chains = append(chains, _Span{inSource(fset, chain.Pos()).Offset, inSource(fset, chain.End()).Offset})
		return false
	})
	return chains
}
