// Package xugofmt formats a chapter's Go: gofmt's layout, with each
// argument of a narration verb on a line of its own, the arguments of a
// list verb on one line where they fit and one to a line where they do
// not, each other line of code past LineWidth columns broken at a list
// that stands on it (lines.go), and each text one literal where its
// line fits and a chain of literals, one line each, where it does not:
// a math text laid out by its structure (fold.go), a prose text by its
// words (prose.go). A line's columns are counted from its indentation
// (ContentWidth), so an argument nested deep has the columns the
// argument around it has.
//
// A narration verb is a verb of the proof language that takes a prose
// label beside the mathematics: Have, Show, Case, When, Leg and the
// rest of NarrationVerbs. On one line the label runs into its claim and
// its proof,
//
//	c.Show("i < j ≤ 1 is the pair (0, 1)", ByArith(bound, zero, faces, pair))
//
// and one argument to a line, the label is a line of the argument and
// the proof stands under it:
//
//	c.Show(
//		"i < j ≤ 1 is the pair (0, 1)",
//		ByArith(bound, zero, faces, pair))
//
// A narration call of two or more arguments takes a line break after
// its `(` and after each `,` between its arguments, wherever the source
// has only blanks there. A break the source already has stays, and so
// does a comment; the closing parenthesis stays where the source puts
// it.
//
// A list verb is a verb of the proof language whose arguments end in a
// list of premises, rules or facts: By, ByArith, BySets, ByElementarity,
// Simp, Simplified and the rest of listVerbs. Its arguments are one line while the line
// holding the call fits in LineWidth columns,
//
//	By(Normalized, scalarField, primeModule, h, carrierData)
//
// and are laid out as a narration call's, one argument to a line, when
// that line does not fit:
//
//	By(
//		Normalized,
//		scalarFieldDef,
//		field.SubfieldSubring.Read(k).At(C),
//		module.ModuleRestrictScalars.At(originalRing, V, C))
//
// The width is the line's with the call joined onto it (ContentWidth). A
// list call that holds a comment, a function literal, a string of
// several lines or a laid-out narration call does not join, and is
// laid out. List calls
// are settled from the outside in, so one inside a laid-out list call
// is measured on the line it then stands on.
//
// gofmt then indents. Outside the texts only line breaks change, and
// the comma before a closing bracket: gofmt drops it when a list call
// that ended on its own line is joined, and a literal's brace or a
// parameter list's parenthesis takes one with a line of its own. A math
// text keeps the DSL tokens it spells, its literals and the blanks
// between its tokens being its layout's; a prose text keeps its bytes.
// A comment keeps its place among the comments, one that ended a line
// past the width moving to the line above, and a text that holds one
// among its literals keeps the lines it stands on. So the file's other
// tokens are the source's, the result is a fixed point of gofmt, and
// Source is its own fixed point.
//
// A line stays past the width where nothing on it has a break to give:
// a name or a path longer than the line, a text with no blank.
//
// The command is library/cmd/xugo_fmt; the emitter formats what it
// renders here, and TestLintXugoFmt holds every chapter file to Source.
package xugofmt

import (
	"bytes"
	"go/ast"
	"go/format"
	"go/parser"
	"go/token"
	"sort"
	"strings"
)

// NarrationVerbs are the verbs of the proof language that take a prose
// label: the exported functions and methods of prover/proof with a
// parameter named label or labels, and library/authoring's names for
// them. TestNarrationVerbsAreTheLabelTakers derives the set from those
// sources and holds this table to it.
var NarrationVerbs = map[string]bool{
	"Assuming":     true,
	"Backward":     true,
	"Base":         true,
	"BothHold":     true,
	"Case":         true,
	"Conjuncts":    true,
	"DismissLeft":  true,
	"DismissRight": true,
	"EqLeg":        true,
	"FinalLeg":     true,
	"Forward":      true,
	"Have":         true,
	"LeLeg":        true,
	"Leg":          true,
	"LeftHolds":    true,
	"MakeCase":     true,
	"NeitherHolds": true,
	"Obtain":       true,
	"Obtain2":      true,
	"Obtain2As":    true,
	"Obtain3":      true,
	"Obtain3As":    true,
	"Obtain4":      true,
	"Obtain4As":    true,
	"Obtain5":      true,
	"Obtain5As":    true,
	"ObtainAs":     true,
	"ObtainChosen": true,
	"Otherwise":    true,
	"RightHolds":   true,
	"Show":         true,
	"Step":         true,
	"Unless":       true,
	"When":         true,
}

// listVerbs are the verbs of the proof language whose arguments end in
// a list of premises, rules or facts: the exported functions and
// methods of prover/proof whose last parameter is `premises ...`,
// `rules ...` or `facts ...` and that take no label, and
// library/authoring's names for them.
// TestListVerbsAreTheListTakers derives the set from those sources and
// holds this table to it.
var listVerbs = map[string]bool{
	"By":               true,
	"ByArith":          true,
	"ByChase":          true,
	"ByElementarity":   true,
	"BySets":           true,
	"Clear":            true,
	"Generalizing":     true,
	"RuleSet":          true,
	"Simp":             true,
	"SimpAll":          true,
	"SimpAt":           true,
	"SimpWith":         true,
	"SimpWithOriented": true,
	"Simplified":       true,
}

// LineWidth is the columns a line may take past its indentation
// (ContentWidth): a line of code, a line of a text, and the one string
// of a claim with a premise, which is written in parts past it
// (library/emit's claimArg).
const LineWidth = 100

// tabWidth is the columns a tab is counted as in a line's width.
const tabWidth = 4

// Width is the columns line takes, a tab counted as tabWidth columns and
// any other character as one.
func Width(line string) int {
	width := 0
	for _, r := range line {
		if r == '\t' {
			width += tabWidth
		} else {
			width++
		}
	}
	return width
}

// ContentWidth is the columns line takes past its indentation: its
// width less the tabs it opens with. It is what LineWidth bounds.
func ContentWidth(line string) int {
	return Width(strings.TrimLeft(line, "\t"))
}

// Source formats src, a whole Go file: a chapter's, or any other, which
// is laid out by the same rules. A file its generator marks as
// generated (`// Code generated … DO NOT EDIT.`) is the generator's to
// lay out, and is returned as it is. A `//line` directive is a comment
// as any other: the lines and columns a layout turns on are src's own
// (inSource), and the directive renumbers none of them. An error is
// src's not parsing.
func Source(src []byte) ([]byte, error) {
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "", src, parser.ParseComments)
	if err != nil {
		return nil, err
	}
	if ast.IsGenerated(file) {
		return src, nil
	}
	out, err := format.Source(applyEdits(src, narrationBreaks(fset, file, src)))
	seen := map[string]bool{}
	for settled := false; err == nil && !settled; {
		if seen[string(out)] {
			panic("xugofmt: the layout of a file does not settle; a pass returns to a layout it left")
		}
		seen[string(out)] = true
		out, settled, err = settleListCalls(out)
		if err == nil && settled {
			out, settled, err = settleWideLines(out)
		}
		if err == nil && settled {
			out, settled, err = settleTexts(out)
		}
	}
	if err != nil {
		return nil, err
	}
	return out, nil
}

// _Edit replaces the bytes from..to of a source with text.
type _Edit struct {
	from, to int
	text     string
}

// applyEdits makes edits, which do not overlap, on a copy of src.
func applyEdits(src []byte, edits []_Edit) []byte {
	sort.Slice(edits, func(i, j int) bool { return edits[i].from > edits[j].from })
	out := append([]byte(nil), src...)
	for _, e := range edits {
		out = append(out[:e.from], append([]byte(e.text), out[e.to:]...)...)
	}
	return out
}

// inSource is where p stands in the source as its bytes have it: its
// offset, its line and its column. fset.Position is where a compiler
// reports p, which past a `//line` directive is a line of the file the
// directive names, at a column the directive may leave unknown. A
// layout is of the source's own lines, so every position the package
// reads is read here, and TestPositionsAreReadInTheSource holds it to
// that.
func inSource(fset *token.FileSet, p token.Pos) token.Position {
	return fset.PositionFor(p, false)
}

// narrationBreaks are the line breaks of every narration call of two
// or more arguments.
func narrationBreaks(fset *token.FileSet, file *ast.File, src []byte) []_Edit {
	var breaks []_Edit
	ast.Inspect(file, func(n ast.Node) bool {
		if call, isCall := n.(*ast.CallExpr); isCall && len(call.Args) >= 2 && NarrationVerbs[calleeName(call)] {
			breaks = append(breaks, argumentBreaks(fset, call, src)...)
		}
		return true
	})
	return breaks
}

// argumentBreaks are the blanks before each argument of call that a
// line break replaces: those after the `(` and after each `,`. A gap
// holding a newline or a comment takes none.
func argumentBreaks(fset *token.FileSet, call *ast.CallExpr, src []byte) []_Edit {
	offset := func(p token.Pos) int { return inSource(fset, p).Offset }
	var breaks []_Edit
	from := offset(call.Lparen) + 1
	for i, arg := range call.Args {
		to := offset(arg.Pos())
		if i > 0 {
			// The gap after an argument opens with its comma, unless
			// a comment stands before the comma.
			gap := string(src[from:to])
			afterComma := strings.TrimLeft(gap, " \t\n")
			if !strings.HasPrefix(afterComma, ",") {
				from = offset(arg.End())
				continue
			}
			from += len(gap) - len(afterComma) + 1
		}
		if strings.Trim(string(src[from:to]), " \t") == "" {
			breaks = append(breaks, _Edit{from, to, "\n"})
		}
		from = offset(arg.End())
	}
	return breaks
}

// settleListCalls settles the outermost list calls src has not
// settled: it joins one that fits and spans lines, and lays out one
// that does not fit. A list call on a line that another changed in this
// pass waits for the next pass, which measures it against that call's
// new layout. It reports settled when it finds none to change.
func settleListCalls(src []byte) (out []byte, settled bool, err error) {
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "", src, parser.ParseComments)
	if err != nil {
		return nil, false, err
	}
	var edits []_Edit
	changed := map[int]bool{}
	ast.Inspect(file, func(n ast.Node) bool {
		call, isCall := n.(*ast.CallExpr)
		if !isCall || !listVerbs[calleeName(call)] {
			return true
		}
		first, last := inSource(fset, call.Pos()).Line, inSource(fset, call.End()).Line
		for line := first; line <= last; line++ {
			if changed[line] {
				return false
			}
		}
		var settle []_Edit
		if joins, joinable := oneLineJoins(fset, file, call, src); joinable && joinedWidth(fset, call, src, joins) <= LineWidth {
			settle = joins
		} else if len(call.Args) >= 2 {
			settle = argumentBreaks(fset, call, src)
		}
		if len(settle) == 0 {
			return true
		}
		edits = append(edits, settle...)
		for line := first; line <= last; line++ {
			changed[line] = true
		}
		return false
	})
	if len(edits) == 0 {
		return src, true, nil
	}
	out, err = format.Source(applyEdits(src, edits))
	return out, false, err
}

// oneLineJoins are the edits that put call on one line: each run of
// blanks holding a newline becomes the one space gofmt writes there, or
// nothing beside a bracket, and a comma before a closing bracket goes
// with the run. It reports false when call holds a comment, a function
// literal, a string of several lines or a narration call of two or
// more arguments, which do not join.
func oneLineJoins(fset *token.FileSet, file *ast.File, call *ast.CallExpr, src []byte) ([]_Edit, bool) {
	if holdsComment(file, call) {
		return nil, false
	}
	joinable := true
	ast.Inspect(call, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit:
			joinable = false
		case *ast.BasicLit:
			joinable = joinable && !strings.Contains(n.Value, "\n")
		case *ast.CallExpr:
			joinable = joinable && (len(n.Args) < 2 || !NarrationVerbs[calleeName(n)])
		}
		return joinable
	})
	if !joinable {
		return nil, false
	}
	var joins []_Edit
	end := inSource(fset, call.Rparen).Offset
	for i := inSource(fset, call.Pos()).Offset; i < end; i++ {
		if src[i] != '\n' {
			continue
		}
		from, to := i, i
		for from > 0 && (src[from-1] == ' ' || src[from-1] == '\t') {
			from--
		}
		for src[to] == ' ' || src[to] == '\t' || src[to] == '\n' {
			to++
		}
		text := " "
		if strings.IndexByte("([{", src[from-1]) >= 0 || strings.IndexByte(")]}", src[to]) >= 0 {
			text = ""
		}
		if src[from-1] == ',' && strings.IndexByte(")]}", src[to]) >= 0 {
			from--
		}
		joins = append(joins, _Edit{from, to, text})
		i = to - 1
	}
	return joins, true
}

// holdsComment reports whether a comment of file stands inside n.
func holdsComment(file *ast.File, n ast.Node) bool {
	for _, group := range file.Comments {
		if group.Pos() < n.End() && group.End() > n.Pos() {
			return true
		}
	}
	return false
}

// joinedWidth is the width of the line holding call once joins put it
// on one line.
func joinedWidth(fset *token.FileSet, call *ast.CallExpr, src []byte, joins []_Edit) int {
	start := inSource(fset, call.Pos()).Offset
	end := inSource(fset, call.End()).Offset
	lineStart := bytes.LastIndexByte(src[:start], '\n') + 1
	lineEnd := len(src)
	if next := bytes.IndexByte(src[end:], '\n'); next >= 0 {
		lineEnd = end + next
	}
	shifted := make([]_Edit, len(joins))
	for i, e := range joins {
		shifted[i] = _Edit{e.from - lineStart, e.to - lineStart, e.text}
	}
	return ContentWidth(string(applyEdits(src[lineStart:lineEnd], shifted)))
}

// calleeName is the name a call is made by: the function's, or the
// method's, with a generic instantiation's type arguments dropped.
func calleeName(call *ast.CallExpr) string {
	fun := call.Fun
	switch f := fun.(type) {
	case *ast.IndexExpr:
		fun = f.X
	case *ast.IndexListExpr:
		fun = f.X
	}
	switch f := fun.(type) {
	case *ast.Ident:
		return f.Name
	case *ast.SelectorExpr:
		return f.Sel.Name
	}
	return ""
}
