// Package visualize draws the corpus: the graphs a reader looks at, as
// against the index (library/index), which says what the corpus holds.
// It reads the index and nothing reads it back, so how a graph is
// chosen and laid out is settled here and changes here.
//
// Two graphs are drawn. Families is the family graph whole, every
// family on the row of its height (familygraph.go); Proof is a member's
// graph — a theorem's proof as the results it stands on (proofgraph.go),
// a definition as what it is built from and who uses it
// (definitiongraph.go). Each is computed in full, coordinates and all,
// and printed by `xugo query graph` as JSON.
//
// Site is the corpus to browse (site.go): two pages, the family graph's
// and a member's, and the files they paint — a graph's layout, and what
// is said of a family and of each of its units, held once. A page's
// script asks for its data, paints the graph and answers the pointer:
// what a node stands on and what stands on it, a search, a zoom. The
// files are served as they are asked for, or written to a directory to
// be published as they are.
//
// Beside a node a page shows what its chapter says: a family's README
// as far as its first section (readme.go), a member's statement and its
// gloss. A formula those words write in LaTeX is typeset as MathML
// before it reaches the page (tex.go).
package visualize

import (
	_ "embed"
	"fmt"
	"strconv"
)

//go:embed familygraph.html.tmpl
var familyGraphTemplate string

//go:embed proofgraph.html.tmpl
var proofGraphTemplate string

// siteFragment is what the two pages share: the reading of the site's
// files, the links from a page to another, and the search, with its
// style.
//
//go:embed site.html.tmpl
var siteFragment string

// A page template's two slots: a comment line saying where the page
// comes from, and what the pages share (siteFragment).
const (
	pageNoticeSlot = "<!--NOTICE-->"
	pageSharedSlot = "<!--SHARED-->"
)

// round1 is the decimal of one place nearest x, a tie going to the even
// digit: the precision a drawing's coordinates are given in.
func round1(x float64) float64 {
	r, err := strconv.ParseFloat(strconv.FormatFloat(x, 'f', 1, 64), 64)
	if err != nil {
		panic(fmt.Sprintf("visualize: %v is no coordinate", x))
	}
	return r
}
