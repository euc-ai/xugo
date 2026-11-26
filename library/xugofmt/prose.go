package xugofmt

import (
	"go/ast"
	"strconv"
	"strings"
)

// A prose text is a string the DSL does not read: a step's label, a
// card's note, an entry's reading, any other string of a chapter file.
// It is written as one string literal where its line fits in LineWidth
// columns, and as a chain of literals joined by `+`, one to a line,
// where it does not:
//
//	Reading: "True because the composites are compared with the identities through the zigzag " +
//		"relation; a single homotopy step would fail off Kan complexes.",
//
// The lines are the fewest that hold the text and as even as that
// allows; each ends after a blank of the text, so the literals spell
// the text byte for byte. The layout is computed from the text alone:
// a chain that would fit is joined back into one literal, and a chain
// broken elsewhere is broken here.

// proseSites are the prose texts of file in source order: each string
// literal, and each chain of them joined by `+`, that is none of math.
// A raw literal and a text holding a line break keep the lines they are
// written on. An import path and a struct tag are no texts; a Name is
// one word however many blanks it has, an entry's or an abbreviation's;
// and neither is a literal that an operator other than the chain's `+`
// applies to a text: an operand of a chain with a name in it, a key, an
// indexed string.
func proseSites(file *ast.File, math []textSite) []textSite {
	isMath := map[ast.Expr]bool{}
	for _, site := range math {
		isMath[site.expr] = true
	}
	var sites []textSite
	var stack []ast.Node
	ast.Inspect(file, func(n ast.Node) bool {
		if n == nil {
			stack = stack[:len(stack)-1]
			return true
		}
		switch n := n.(type) {
		case *ast.ImportSpec, *ast.Field:
			return false
		case ast.Expr:
			if lits := literalChain(n); lits != nil {
				if site, isProse := proseSite(stack, n, lits); isProse && !isMath[n] {
					sites = append(sites, site)
				}
				return false
			}
		}
		stack = append(stack, n)
		return true
	})
	return sites
}

// proseSite is the text e spells with lits, under the nodes of stack,
// and whether it is one a layout may break.
func proseSite(stack []ast.Node, e ast.Expr, lits []*ast.BasicLit) (textSite, bool) {
	site := textSite{expr: e, lits: lits}
	for _, lit := range lits {
		value, err := strconv.Unquote(lit.Value)
		if err != nil || strings.HasPrefix(lit.Value, "`") || strings.Contains(value, "\n") {
			return site, false
		}
	}
	if len(stack) == 0 {
		return site, true
	}
	switch parent := stack[len(stack)-1].(type) {
	case *ast.BinaryExpr, *ast.ParenExpr, *ast.IndexExpr, *ast.SliceExpr, *ast.CaseClause:
		return site, false
	case *ast.KeyValueExpr:
		if key, isIdent := parent.Key.(*ast.Ident); parent.Key == e || isIdent && key.Name == "Name" {
			return site, false
		}
		if len(stack) >= 2 {
			if lit, isLit := stack[len(stack)-2].(*ast.CompositeLit); isLit {
				site.kv, site.lit = parent, lit
			}
		}
	}
	return site, true
}

// fillText lays a prose text out over lines of first columns for the
// first and rest for each later one, the last ending in tail more
// (siteColumns): the fewest lines that hold the text, and as even as
// that number allows, so a text just past the width is two halves and
// not a line and a word. The pieces are the literals the text is
// written as, and spell it byte for byte.
func fillText(text string, first, rest, tail int) []string {
	pieces := fillLines(text, first, rest, tail)
	for narrower, least := rest, 0; least < narrower; {
		by := (least + narrower + 1) / 2
		if even := fillLines(text, first-by, rest-by, tail); len(even) == len(pieces) {
			pieces, least = even, by
		} else {
			narrower = by - 1
		}
	}
	return pieces
}

// fillLines fills lines of first columns for the first and rest for
// each later one, the last ending in tail more: each line takes the
// words that fit and ends after the last blank of a run of them, and a
// word wider than a line stands on one alone.
func fillLines(text string, first, rest, tail int) []string {
	var pieces []string
	for avail := first; ; avail = rest {
		if quotedWidth(text)+tail <= avail {
			return append(pieces, text)
		}
		cut := -1
		for i := 0; i+1 < len(text); i++ {
			if text[i] != ' ' || text[i+1] == ' ' {
				continue
			}
			if cut >= 0 && quotedWidth(text[:i]) > avail {
				break
			}
			cut = i + 1
			if quotedWidth(text[:i]) > avail {
				break
			}
		}
		if cut < 0 {
			return append(pieces, text)
		}
		pieces = append(pieces, text[:cut])
		text = text[cut:]
	}
}

// quotedWidth is the columns text takes inside the quotes of the
// literal that spells it.
func quotedWidth(text string) int {
	return Width(strconv.Quote(text)) - len(`""`)
}
