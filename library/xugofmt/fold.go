package xugofmt

import (
	"bytes"
	"go/ast"
	"go/format"
	"go/parser"
	"go/token"
	"strconv"
	"strings"

	"github.com/euc-ai/xugo/ext/dsl"
)

// A math text is a string the DSL reads: a statement's parts, a claim,
// a term, an abbreviation's text, a definition's type and equations
// (mathArguments, mathFields). It is written as one string literal
// where its line fits in LineWidth columns, and as a chain of literals
// joined by `+`, one to a line, where it does not:
//
//	Conclusion: "∃F:functor_ops(A, M, num → M, set(num → M)). " +
//		"    functor(C, homotopy_category(nerve(C)), F) ∧ " +
//		"    injective_on(C.objects, F.obj) ∧ " +
//		"    image(F.obj, C.objects) = nerve_simplices(C, 0)",
//
// The text is broken where it has a blank, which the lexer skips, so
// the pieces read as the one string does. A binder's names end a line
// and its scope stands under them four spaces in; an operator chain
// breaks at its loosest operator, one operand to a line with the
// operator ending it; a group breaks inside its brackets, at its commas
// where it has them, its later lines four spaces in. Each line but the
// last ends in a blank inside its literal, and a later line's spaces
// before its first token are its indentation inside the text, gofmt's
// tabs coming before the literal. The layout is computed from the text
// alone, so a chain that would fit is joined back into one literal and
// the blanks of a text that fits are single.

// mathParameters are the names a parameter of the proof language takes
// when it reads a DSL text. TestMathArgumentsAreTheTextReaders derives
// mathArguments from them.
var mathParameters = map[string]bool{
	"body":         true,
	"claim":        true,
	"content":      true,
	"equationText": true,
	"exists":       true,
	"fact":         true,
	"headline":     true,
	"law":          true,
	"membership":   true,
	"pred":         true,
	"predicate":    true,
	"raw":          true,
	"ruleText":     true,
	"specText":     true,
	"statement":    true,
	"text":         true,
	"typeText":     true,
}

// mathArguments are the arguments, by position, at which a call of the
// proof language reads a DSL text: the exported functions and methods
// of prover/proof and library/registry, by name, and library/
// authoring's names for them, at each parameter mathParameters names.
var mathArguments = map[string][]int{
	"Axiom":                   {0},
	"BigOpAs":                 {0},
	"Card":                    {0},
	"Conjunct":                {0},
	"Derived":                 {0},
	"FromResident":            {0},
	"GroundHyp":               {0},
	"GroundHypKeep":           {0},
	"Have":                    {1},
	"Hyp":                     {0},
	"Instance":                {1},
	"KeyOfText":               {0},
	"Law":                     {0},
	"Lemma":                   {0, 1},
	"LetAs":                   {1},
	"Lifted":                  {0},
	"MakePropText":            {0},
	"MatAs":                   {0},
	"MatAt":                   {2},
	"MemberOf":                {1},
	"Obtain":                  {1},
	"Obtain2":                 {1},
	"Obtain2As":               {1},
	"Obtain3":                 {1},
	"Obtain3As":               {1},
	"Obtain4":                 {1},
	"Obtain4As":               {1},
	"Obtain5":                 {1},
	"Obtain5As":               {1},
	"ObtainAs":                {1},
	"ObtainChosen":            {1},
	"Opening":                 {1},
	"ParseDefinitionEquation": {0, 2},
	"ParseInductiveRule":      {0, 2},
	"ParseQuotientRelation":   {0},
	"ParseSpecStatement":      {0},
	"Parts":                   {0},
	"Postulate":               {1},
	"Read":                    {0},
	"ResidentHyp":             {0},
	"SectionText":             {0},
	"Sections":                {0},
	"Statement":               {0},
	"StructureOf":             {0},
	"Term":                    {0},
	"TermAs":                  {0},
	"TermText":                {0, 1},
	"Theorem":                 {0, 1},
	"VecAs":                   {0},
	"VecAt":                   {1},
	"VecFunAs":                {0},
	"VecFunAt":                {2},
	"WithPredicate":           {0, 2},
}

// mathFields are the fields of a composite literal whose string, or
// whose list's strings, the DSL reads: a Statement's parts and a
// definition's type, equations and measure. An abbreviation's Text is
// one inside an abbreviation table (abbreviationEntry).
var mathFields = map[string]bool{
	"Binders":    true,
	"Conclusion": true,
	"Equations":  true,
	"Hypotheses": true,
	"Measure":    true,
	"Type":       true,
}

// abbreviationTables are the type names an abbreviation table is
// written under, and abbreviationEntries those an entry of one is: an
// entry's Text is a math text.
var (
	abbreviationTables  = map[string]bool{"Abbrev": true, "dsl.Abbrev": true, "[]dsl.Abbreviation": true}
	abbreviationEntries = map[string]bool{"Abbreviation": true, "dsl.Abbreviation": true}
)

// textSite is a text in a file: the expression that spells it, a string
// literal or a `+` chain of them, and the key it is the value of in a
// composite literal, if any. math says the DSL reads it; any other text
// is prose (prose.go).
type textSite struct {
	expr ast.Expr
	lits []*ast.BasicLit
	kv   *ast.KeyValueExpr
	lit  *ast.CompositeLit // the literal kv is an element of
	math bool
}

// mathSites are the math texts of file, in source order.
func mathSites(file *ast.File) []textSite {
	var sites []textSite
	add := func(e ast.Expr, kv *ast.KeyValueExpr, lit *ast.CompositeLit) {
		if lits := literalChain(e); lits != nil {
			sites = append(sites, textSite{expr: e, lits: lits, kv: kv, lit: lit, math: true})
		}
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
			for _, i := range mathArguments[calleeName(n)] {
				if i < len(n.Args) {
					add(n.Args[i], nil, nil)
				}
			}
		case *ast.KeyValueExpr:
			key, isIdent := n.Key.(*ast.Ident)
			if !isIdent || len(stack) < 2 {
				return true
			}
			lit, isLit := stack[len(stack)-2].(*ast.CompositeLit)
			if !isLit {
				return true
			}
			switch {
			case mathFields[key.Name]:
				if list, isList := n.Value.(*ast.CompositeLit); isList {
					for _, elt := range list.Elts {
						add(elt, nil, nil)
					}
				} else {
					add(n.Value, n, lit)
				}
			case key.Name == "Text" && abbreviationEntry(stack[:len(stack)-1]):
				add(n.Value, n, lit)
			}
		}
		return true
	})
	return sites
}

// abbreviationEntry reports whether the composite literal ending stack
// is an entry of an abbreviation table: typed as one, or an element
// with its type elided in a literal of a table's type.
func abbreviationEntry(stack []ast.Node) bool {
	lit := stack[len(stack)-1].(*ast.CompositeLit)
	if lit.Type != nil {
		return abbreviationEntries[typeName(lit.Type)]
	}
	if len(stack) < 2 {
		return false
	}
	outer, isLit := stack[len(stack)-2].(*ast.CompositeLit)
	return isLit && outer.Type != nil && abbreviationTables[typeName(outer.Type)]
}

// typeName is a composite literal's type as written: a name, a
// qualified name, or a slice of one.
func typeName(e ast.Expr) string {
	switch t := e.(type) {
	case *ast.Ident:
		return t.Name
	case *ast.SelectorExpr:
		return typeName(t.X) + "." + t.Sel.Name
	case *ast.ArrayType:
		if t.Len == nil {
			return "[]" + typeName(t.Elt)
		}
	}
	return ""
}

// StringValue is the string e spells where e is a string literal or a
// chain of them joined by `+`, as a text laid out over lines is
// written; false for any other expression.
func StringValue(e ast.Expr) (string, bool) {
	lits := literalChain(e)
	if lits == nil {
		return "", false
	}
	var b strings.Builder
	for _, lit := range lits {
		value, err := strconv.Unquote(lit.Value)
		if err != nil {
			return "", false
		}
		b.WriteString(value)
	}
	return b.String(), true
}

// literalChain is the string literals e joins: e itself, or the
// operands of a chain of `+` over string literals; nil for any other
// expression.
func literalChain(e ast.Expr) []*ast.BasicLit {
	switch e := e.(type) {
	case *ast.BasicLit:
		if e.Kind == token.STRING {
			return []*ast.BasicLit{e}
		}
	case *ast.BinaryExpr:
		if e.Op != token.ADD {
			return nil
		}
		left, right := literalChain(e.X), literalChain(e.Y)
		if left != nil && right != nil {
			return append(left, right...)
		}
	}
	return nil
}

// settleTexts writes each text of src as its layout, and reports
// settled when every one already is.
func settleTexts(src []byte) (out []byte, settled bool, err error) {
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "", src, parser.ParseComments)
	if err != nil {
		return nil, false, err
	}
	edits := textFolds(fset, file, src)
	if len(edits) == 0 {
		return src, true, nil
	}
	out, err = format.Source(applyEdits(src, edits))
	return out, false, err
}

// textFolds are the edits that write each text of file as its layout:
// one literal, or a chain of them one to a line. The lines of code are
// settled before the texts (Source), so a text still on a line of code
// past the width is one the code has no break for, and it is laid out
// after the code it follows. A layout is written over the text's chain
// from its first literal to its last, so a text that holds a comment
// among its literals has none written and keeps the lines it stands on.
func textFolds(fset *token.FileSet, file *ast.File, src []byte) []_Edit {
	var edits []_Edit
	offset := func(p token.Pos) int { return inSource(fset, p).Offset }
	sites := mathSites(file)
	sites = append(sites, proseSites(file, sites)...)
	for _, site := range sites {
		text, unquoted := StringValue(site.expr)
		if !unquoted || holdsComment(file, site.expr) {
			continue
		}
		start, end := offset(site.expr.Pos()), offset(site.expr.End())
		first, rest, tail := siteColumns(fset, file, src, site)
		var pieces []string
		if site.math {
			laid := false
			if pieces, laid = foldText(text, first, rest, tail); !laid {
				continue
			}
		} else {
			pieces = fillText(text, first, rest, tail)
			if strings.Join(pieces, "") != text {
				panic("xugofmt: the layout of the prose " + strconv.Quote(text) + " does not spell it")
			}
		}
		if sameLayout(site, pieces, fset) {
			continue
		}
		quoted := make([]string, len(pieces))
		for i, p := range pieces {
			quoted[i] = strconv.Quote(p)
		}
		edits = append(edits, _Edit{start, end, strings.Join(quoted, " +\n")})
	}
	return edits
}

// sameLayout reports whether site is already written as pieces, one
// literal to a line: a math text's literals in the quoting the layout
// writes, a prose text's spelling the pieces in any quoting.
func sameLayout(site textSite, pieces []string, fset *token.FileSet) bool {
	if len(site.lits) != len(pieces) {
		return false
	}
	for i, lit := range site.lits {
		if site.math && lit.Value != strconv.Quote(pieces[i]) {
			return false
		}
		if value, err := strconv.Unquote(lit.Value); err != nil || value != pieces[i] {
			return false
		}
		if i > 0 && inSource(fset, site.lits[i-1].End()).Line == inSource(fset, lit.Pos()).Line {
			return false
		}
	}
	return true
}

// siteColumns are the columns a text's lines may take, counted from
// the indentation of the line each stands on: first for its first
// line's content and rest for each later line's, both with the
// blank that ends a line inside its literal and the ` +` after it set
// aside, and tail for what the last line ends in past those three
// columns (negative where it ends in less): the code after the text, up
// to the next text on the line, which is laid out from where it starts.
// A field's value that opens its line is measured from the column gofmt
// aligns the literal's values to at the widest, the longest key of the
// literal set before it, so the layout does not turn on the alignment
// it changes.
func siteColumns(fset *token.FileSet, file *ast.File, src []byte, site textSite) (first, rest, tail int) {
	start := inSource(fset, site.expr.Pos()).Offset
	end := inSource(fset, site.expr.End()).Offset
	lineStart := bytes.LastIndexByte(src[:start], '\n') + 1
	indent := lineStart
	for indent < len(src) && src[indent] == '\t' {
		indent++
	}
	startCol := ContentWidth(string(src[lineStart:start]))
	if site.kv != nil && inSource(fset, site.kv.Pos()).Offset == indent {
		widest := 0
		for _, elt := range site.lit.Elts {
			if kv, isKV := elt.(*ast.KeyValueExpr); isKV {
				if key, isIdent := kv.Key.(*ast.Ident); isIdent && len(key.Name) > widest {
					widest = len(key.Name)
				}
			}
		}
		startCol = widest + len(": ")
	}
	lineEnd := len(src)
	if next := bytes.IndexByte(src[end:], '\n'); next >= 0 {
		lineEnd = end + next
	}
	for _, group := range file.Comments {
		if c := inSource(fset, group.Pos()).Offset; c >= end && c < lineEnd {
			lineEnd = c
		}
	}
	suffix := string(src[end:lineEnd])
	if next := strings.IndexAny(suffix, "\"`"); next >= 0 {
		suffix = suffix[:next]
	}
	suffix = strings.TrimRight(suffix, " \t")
	const quotes, lineEnding = 2, 3 // `""`, and ` +` after a line's closing blank
	first = LineWidth - startCol - quotes - lineEnding
	rest = LineWidth - quotes - lineEnding
	tail = Width(suffix) - lineEnding
	return first, rest, tail
}

// foldLine is a line of a laid-out text: its indentation in spaces and
// its tokens; the first line of a layout continues the line it starts
// on and its indent is unused.
type foldLine struct {
	indent int
	text   string
}

// folder lays out the tokens of one text.
type folder struct {
	spell []string // each token as the text spells it
	kind  []dsl.LayoutKind
	level []int
	blank []bool // blank[i]: the text has a blank between tokens i and i+1, neither an opener before it nor a closer after it
	match []int  // match[i]: the closer of the opener at i, the opener of the closer at i; -1 for any other token
	first int    // columns of the text's first line
	rest  int    // columns of each later line
}

// foldText lays out text over lines with first columns for the first
// line and rest for each later one, the last line ending in tail more
// (siteColumns). The pieces are the literals the text is written as:
// each line's indentation and tokens, and a closing blank on each but
// the last. It reports false where text does not lex, and is then left
// as it is written.
func foldText(text string, first, rest, tail int) ([]string, bool) {
	toks, err := dsl.LayoutTokens(text)
	if err != nil || len(toks) == 0 {
		return nil, false
	}
	f := &folder{first: first, rest: rest}
	var openers []int
	for i, t := range toks {
		f.spell = append(f.spell, text[t.Start:t.End])
		f.kind = append(f.kind, t.Kind)
		f.level = append(f.level, t.Level)
		f.blank = append(f.blank, i+1 < len(toks) && toks[i+1].Start > t.End &&
			t.Kind != dsl.LayoutOpen && toks[i+1].Kind != dsl.LayoutClose)
		f.match = append(f.match, -1)
		switch t.Kind {
		case dsl.LayoutOpen:
			openers = append(openers, i)
		case dsl.LayoutClose:
			if n := len(openers); n > 0 {
				f.match[i], f.match[openers[n-1]] = openers[n-1], i
				openers = openers[:n-1]
			}
		}
	}
	lines := f.lay(0, len(toks), 0, 0, tail, true, false)
	pieces := make([]string, len(lines))
	for i, line := range lines {
		if i > 0 {
			pieces[i] = strings.Repeat(" ", line.indent)
		}
		pieces[i] += line.text
		if i+1 < len(lines) {
			pieces[i] += " "
		}
	}
	f.check(text, strings.Join(pieces, ""))
	return pieces, true
}

// check panics unless laid, the joined layout of text, spells text's
// tokens in text's order: a layout that changed the text would change
// what it reads as.
func (f *folder) check(text, laid string) {
	toks, err := dsl.LayoutTokens(laid)
	if err != nil {
		panic("xugofmt: the layout of " + strconv.Quote(text) + " does not lex: " + err.Error())
	}
	if len(toks) != len(f.spell) {
		panic("xugofmt: the layout of " + strconv.Quote(text) + " changes its tokens: " + strconv.Quote(laid))
	}
	for i, t := range toks {
		if laid[t.Start:t.End] != f.spell[i] {
			panic("xugofmt: the layout of " + strconv.Quote(text) + " changes its tokens: " + strconv.Quote(laid))
		}
	}
}

// flat is tokens lo..hi on one line, a blank wherever the text has one
// (blank), none inside a group's brackets.
func (f *folder) flat(lo, hi int) string {
	var b strings.Builder
	for i := lo; i < hi; i++ {
		b.WriteString(f.spell[i])
		if i+1 < hi && f.blank[i] {
			b.WriteByte(' ')
		}
	}
	return b.String()
}

// lay lays out tokens lo..hi, starting col columns into a line and ended
// by tail more columns on their last line. A later line takes indent
// spaces; onFirst says the line is the text's first, inBraces that the
// tokens are a brace group's, whose bars separate.
func (f *folder) lay(lo, hi, col, indent, tail int, onFirst, inBraces bool) []foldLine {
	whole := []foldLine{{text: f.flat(lo, hi)}}
	if col+Width(whole[0].text)+tail <= f.width(onFirst) {
		return whole
	}
	if len(f.separators(lo, hi, inBraces)) == 0 {
		if lines, laid := f.layBinder(lo, hi, col, indent, tail, onFirst); laid {
			return lines
		}
	}
	if lines, laid := f.layChain(lo, hi, col, indent, tail, onFirst, inBraces); laid {
		return lines
	}
	if lines, laid := f.layGroup(lo, hi, col, indent, tail, onFirst); laid {
		return lines
	}
	return whole
}

// width is the columns a line takes: the text's first line's or a later
// one's.
func (f *folder) width(onFirst bool) int {
	if onFirst {
		return f.first
	}
	return f.rest
}

// binderEnd is the token after the binders of the binder at lo, its
// prefix operators skipped: after the first dot outside a group that
// the text follows with a blank. It is -1 where lo..hi does not open
// with a binder whose scope can stand on lines of its own.
func (f *folder) binderEnd(lo, hi int) int {
	i := lo
	for i < hi && f.kind[i] == dsl.LayoutPrefix {
		i++
	}
	if i == hi || f.kind[i] != dsl.LayoutBinder {
		return -1
	}
	for i++; i < hi; i++ {
		switch {
		case f.kind[i] == dsl.LayoutOpen && f.match[i] > i:
			i = f.match[i]
		case f.kind[i] == dsl.LayoutDot && f.blank[i]:
			if i+1 < hi {
				return i + 1
			}
			return -1
		}
	}
	return -1
}

// binderColon is the colon before the type of the binder that tokens
// lo..end spell, its dot last; -1 where the binder states no type.
func (f *folder) binderColon(lo, end int) int {
	for i := lo; i < end-1; i++ {
		if f.kind[i] == dsl.LayoutOpen && f.match[i] > i {
			i = f.match[i]
			continue
		}
		if f.spell[i] == ":" {
			return i
		}
	}
	return -1
}

// layBinder lays out tokens that open with binders: the binders end a
// line, consecutive ones on one line where they fit and one to a line
// where they do not, a binder's type laid out after its names where
// the binder alone does not fit, and the scope stands under them four
// spaces in. Binders the tokens end in, as a statement's Binders part
// is written, have no scope and stand one to a line.
func (f *folder) layBinder(lo, hi, col, indent, tail int, onFirst bool) ([]foldLine, bool) {
	ends := []int{}
	at := lo
	for end := f.binderEnd(at, hi); end >= 0; end = f.binderEnd(at, hi) {
		ends = append(ends, end)
		at = end
	}
	if f.endsInBinder(at, hi) {
		ends = append(ends, hi)
	}
	if len(ends) == 0 {
		return nil, false
	}
	scope := ends[len(ends)-1]
	var lines []foldLine
	if head := f.flat(lo, scope); scope < hi && col+Width(head) <= f.width(onFirst) {
		lines = append(lines, foldLine{text: head})
	} else {
		at := lo
		for i, end := range ends {
			c, first, after := indent, false, 0
			if i == 0 {
				c, first = col, onFirst
			}
			if end == hi {
				after = tail
			}
			part := []foldLine{{text: f.flat(at, end)}}
			if colon := f.binderColon(at, end); c+Width(part[0].text)+after > f.width(first) && colon > 0 {
				names := f.flat(at, colon+1)
				part = f.lay(colon+1, end-1, c+Width(names), indent+4, Width(f.spell[end-1])+after, first, false)
				part[0].text = names + part[0].text
				part[len(part)-1].text += f.spell[end-1]
			}
			part[0].indent = indent
			lines = append(lines, part...)
			at = end
		}
	}
	if scope == hi {
		return lines, true
	}
	body := f.lay(scope, hi, indent+4, indent+4, tail, false, false)
	body[0].indent = indent + 4
	return append(lines, body...), true
}

// endsInBinder reports whether tokens lo..hi are one binder and nothing
// after it: a binder symbol first and the dot that ends its names last.
func (f *folder) endsInBinder(lo, hi int) bool {
	return hi-lo >= 3 && f.kind[lo] == dsl.LayoutBinder && f.kind[hi-1] == dsl.LayoutDot
}

// separators are the commas of tokens lo..hi outside any group, and
// their bars where the tokens are a brace group's: the members of a
// group, each of which a binder inside it reaches to the end of and no
// further.
func (f *folder) separators(lo, hi int, inBraces bool) []int {
	var seps []int
	for i := lo; i+1 < hi; i++ {
		switch {
		case f.kind[i] == dsl.LayoutOpen && f.match[i] > i:
			i = f.match[i]
		case f.kind[i] == dsl.LayoutComma, f.kind[i] == dsl.LayoutPipe && inBraces:
			seps = append(seps, i)
		}
	}
	return seps
}

// layChain lays out tokens that are a chain of operands joined by
// operators outside any group, a binder's scope closing it: one operand
// to a line at the loosest layer the chain has, each ending in the
// operator after it. A group's members, its separators apart, are
// looser than any operator. It declines a chain whose loosest operators
// all lack the blank after them a line break takes.
func (f *folder) layChain(lo, hi, col, indent, tail int, onFirst, inBraces bool) ([]foldLine, bool) {
	layer := func(i int) int {
		switch f.kind[i] {
		case dsl.LayoutComma:
			return 0
		case dsl.LayoutPipe:
			if inBraces {
				return 0
			}
		case dsl.LayoutInfix:
			return f.level[i]
		}
		return -1
	}
	ops, loosest := f.separators(lo, hi, inBraces), 0
	if len(ops) == 0 {
		loosest = -1
		for i := lo; i < hi; i++ {
			if f.kind[i] == dsl.LayoutOpen && f.match[i] > i {
				i = f.match[i]
				continue
			}
			if f.binderEnd(i, hi) >= 0 {
				break
			}
			if l := layer(i); l > 0 && i > lo && i+1 < hi {
				ops = append(ops, i)
				if loosest < 0 || l < loosest {
					loosest = l
				}
			}
		}
	}
	var breaks []int
	for _, op := range ops {
		if layer(op) == loosest && f.blank[op] {
			breaks = append(breaks, op)
		}
	}
	if len(breaks) == 0 {
		return nil, false
	}
	var lines []foldLine
	at := lo
	for k := 0; k <= len(breaks); k++ {
		end, opText, after := hi, "", tail
		if k < len(breaks) {
			end = breaks[k]
			opText = f.spell[end]
			if f.blank[end-1] {
				opText = " " + opText
			}
			after = Width(opText)
		}
		var part []foldLine
		if k == 0 {
			part = f.lay(at, end, col, indent, after, onFirst, inBraces)
		} else {
			part = f.lay(at, end, indent, indent, after, false, inBraces)
			part[0].indent = indent
		}
		part[len(part)-1].text += opText
		lines = append(lines, part...)
		at = end + 1
	}
	return lines, true
}

// layGroup lays out tokens that end in a group, or in a group and its
// fields `(…).carrier`, a head before the opener with no blank outside
// its own groups: an application `f(…)`, a field's `x(…).f(…)`, a
// parenthesized term. The head is laid out
// where it does not fit, and the opener ends its last line. The group's
// content follows the opener where its first member fits there, or
// fits on no line and its first line does; it stands on the next line
// four spaces in where a line of its own holds the first member that
// the opener's line does not. The later lines are four spaces in either
// way; the closer ends the last line.
// Content that opens with a binder, inside parentheses alone, takes no
// further four spaces: the binder's scope is the one step in.
func (f *folder) layGroup(lo, hi, col, indent, tail int, onFirst bool) ([]foldLine, bool) {
	end := hi
	for end-3 >= lo && f.kind[end-1] == dsl.LayoutAtom && f.kind[end-2] == dsl.LayoutDot && !f.blank[end-2] && !f.blank[end-3] {
		end -= 2
	}
	fields := f.flat(end, hi)
	tail += Width(fields)
	closer := end - 1
	if f.kind[closer] != dsl.LayoutClose {
		return nil, false
	}
	opener := f.match[closer]
	if opener < lo || opener+1 >= closer {
		return nil, false
	}
	for i := lo; i < opener; i++ {
		if f.kind[i] == dsl.LayoutOpen && f.match[i] > i && f.match[i] < opener {
			i = f.match[i]
		}
		if f.blank[i] {
			return nil, false
		}
	}
	open, shut := f.spell[opener], f.spell[closer]
	var lines []foldLine
	if head := f.flat(lo, opener+1); opener == lo || col+Width(head) <= f.width(onFirst) {
		lines = []foldLine{{text: head}}
	} else {
		lines = f.lay(lo, opener, col, indent, Width(open), onFirst, false)
		lines[len(lines)-1].text += open
	}
	last := len(lines) - 1
	at, lastOnFirst := col, onFirst && last == 0
	if last > 0 {
		at = lines[last].indent
	}
	at += Width(lines[last].text)
	inner := indent + 4
	if opener == lo && f.binderEnd(opener+1, closer) >= 0 {
		inner = indent
	}
	inBraces := open == "{"
	content := f.lay(opener+1, closer, at, inner, tail+Width(shut), lastOnFirst, inBraces)
	if opener > lo && (at+Width(content[0].text) > f.width(lastOnFirst) || f.firstMemberWaits(opener, closer, at, indent+4, tail+Width(shut), lastOnFirst, inBraces)) {
		content = f.lay(opener+1, closer, indent+4, indent+4, tail+Width(shut), false, inBraces)
		content[0].indent = indent + 4
		lines = append(lines, content...)
	} else {
		lines[last].text += content[0].text
		lines = append(lines, content[1:]...)
	}
	lines[len(lines)-1].text += shut + fields
	return lines, true
}

// firstMemberWaits reports whether the first member of the group
// opener..closer does not fit at column at, after the opener, and fits
// on a line of its own indent spaces in: it then starts that line
// whole, where after the opener it would be broken inside. tail is what
// follows the content on its last line.
func (f *folder) firstMemberWaits(opener, closer, at, indent, tail int, onFirst, inBraces bool) bool {
	end, after := closer, tail
	if seps := f.separators(opener+1, closer, inBraces); len(seps) > 0 {
		end, after = seps[0], Width(f.spell[seps[0]])
	}
	member := Width(f.flat(opener+1, end)) + after
	return at+member > f.width(onFirst) && indent+member <= f.rest
}
