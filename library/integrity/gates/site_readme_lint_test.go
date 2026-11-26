package gates

import (
	"fmt"
	"html"
	"io/fs"
	"maps"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/library/landmarks"
)

// The site's pages, written by hand, and the README every page quoting
// it must quote.
const (
	siteTree     = "site"
	siteReadme   = "README.md"
	quoteFrom    = "<!-- from "
	quoteEnd     = "<!-- end "
	quoteMarkEnd = " -->"
)

// THE SITE QUOTES THE README WORD FOR WORD. A page under site/ marks
// what it says in a root README's words, between `<!-- from <file> -->`
// and `<!-- end <file> -->`: the front page quotes README.md's opening
// and its folded questions, and a page under site/zh/ quotes
// README.zh-CN.md once it is translated. Read in order, a page's spans
// from one file say what that file says after its first paragraph, the
// line that links the website and the other language, and after its
// title, which the page heads in its own markup. So nothing but
// this test keeps the README and the site one text, and it compares what
// a reader reads: the words, not the markup. Markdown's emphasis, inline
// code, list and quote markers, the arrows of a sequence and a link's
// address are not words, nor are the page's tags; a link's text is.
// The first word where the two part fails the test, with the words
// around it on each side; either text may be the one to change.
//
// The population is every .html file under site/, found by walking, and
// README.md must be quoted by one of them: the front page is its copy.
func TestLintSiteQuotesReadme(t *testing.T) {
	root := filepath.Join(moduleRoot, siteTree)
	quoted := map[string]bool{}
	err := filepath.WalkDir(root, func(file string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() || filepath.Ext(file) != ".html" {
			return err
		}
		src, err := os.ReadFile(file)
		if err != nil {
			return err
		}
		page, _ := filepath.Rel(moduleRoot, file)
		spans, err := siteQuotes(string(src))
		if err != nil {
			t.Errorf("%s: %v", page, err)
			return nil
		}
		for _, readme := range slices.Sorted(maps.Keys(spans)) {
			quoted[readme] = true
			text, err := os.ReadFile(filepath.Join(moduleRoot, readme))
			if err != nil {
				t.Errorf("%s quotes %s, which the tree does not hold: %v", page, readme, err)
				continue
			}
			want := markdownWords(readmeBody(string(text)))
			got := htmlWords(strings.Join(spans[readme], " "))
			if at, ok := firstDifference(want, got); !ok {
				t.Errorf("%s and %s part at word %d:\n    %s reads  %s\n    the page reads %s\n"+
					"    The page's spans marked `%s%s%s` say what %s says after its first paragraph and its title; "+
					"change the one that is behind.",
					page, readme, at+1, readme, around(want, at), around(got, at),
					quoteFrom, readme, quoteMarkEnd, readme)
			}
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	if !quoted[siteReadme] {
		t.Errorf("no page under %s/ quotes %s: the front page marks its opening and its questions "+
			"between `%s%s%s` and `%s%s%s`", siteTree, siteReadme,
			quoteFrom, siteReadme, quoteMarkEnd, quoteEnd, siteReadme, quoteMarkEnd)
	}
}

// THE LANDMARKS PAGES HOLD THE LIST AS WRITTEN. The list of landmarks is
// one file, site/landmarks.json; package landmarks writes it into
// landmarks.html and zh/landmarks.html between the marks of their table
// of contents and their topic sections, and each page keeps its own
// opening and navigation outside them. This test writes the list into
// each page in memory and fails on a page that would change: one whose
// list was edited by hand, or a list edited and not written. The list
// itself is read strictly (an unknown field, an empty one, an anchor used
// twice fail), and so are the marks (each pair once per page).
func TestLintSiteLandmarksCurrent(t *testing.T) {
	site := filepath.Join(moduleRoot, siteTree)
	stale, err := landmarks.Stale(site)
	if err != nil {
		t.Fatal(err)
	}
	for _, page := range stale {
		t.Errorf("stale %s/%s: its list is not %s/%s as written — edit the list there, never between the "+
			"page's marks, and run `go generate ./library/landmarks`", siteTree, page, siteTree, landmarks.ListFile)
	}
}

// siteQuotes are a page's spans by the file each quotes, in the page's
// order. A span opened and not closed, or closed by another file's
// mark, is a defect of the page.
func siteQuotes(page string) (map[string][]string, error) {
	spans := map[string][]string{}
	for rest := page; ; {
		open := strings.Index(rest, quoteFrom)
		if open < 0 {
			return spans, nil
		}
		rest = rest[open+len(quoteFrom):]
		name, after, ok := strings.Cut(rest, quoteMarkEnd)
		if !ok || strings.ContainsAny(name, " \n<>") {
			return nil, fmt.Errorf("a `%s` mark names no file", quoteFrom)
		}
		closing := quoteEnd + name + quoteMarkEnd
		body, tail, ok := strings.Cut(after, closing)
		if !ok {
			return nil, fmt.Errorf("the span quoting %s is not closed by `%s`", name, closing)
		}
		if strings.Contains(body, quoteFrom) {
			return nil, fmt.Errorf("the span quoting %s holds another span", name)
		}
		spans[name] = append(spans[name], body)
		rest = tail
	}
}

// readmeBody is a README after its first paragraph and its title: a
// heading line that opens what follows the paragraph is the page's own
// heading, not a quotation.
func readmeBody(text string) string {
	_, body, _ := strings.Cut(strings.TrimLeft(text, "\n"), "\n\n")
	if strings.HasPrefix(body, "# ") {
		_, body, _ = strings.Cut(body, "\n")
	}
	return body
}

var (
	mdFence    = regexp.MustCompile("^\\s*```")
	mdMarker   = regexp.MustCompile(`^\s*(?:[-*]|\d+\.|>|→)\s+`)
	mdLink     = regexp.MustCompile(`\[([^\]]+)\]\([^)\s]+\)`)
	mdAutolink = regexp.MustCompile(`<(https?://[^>\s]+)>`)
	mdTag      = regexp.MustCompile(`</?(?:details|summary)>`)
	mdItalic   = regexp.MustCompile(`(^|[^\w*])\*([^*\s][^*]*?)\*`)
	htmlTag    = regexp.MustCompile(`<!--.*?-->|<(/?)([a-zA-Z][a-zA-Z0-9]*)[^>]*>`)
)

// markdownWords are the words a reader of Markdown reads: a fenced block
// as it stands, inline code as it stands, and elsewhere a link's text, a
// bare address, the text inside emphasis, without the markers that open
// a list item, a quotation or a step of an arrowed sequence.
func markdownWords(text string) []string {
	var out strings.Builder
	fenced := false
	for _, line := range strings.Split(text, "\n") {
		if mdFence.MatchString(line) {
			fenced = !fenced
			out.WriteString(" ")
			continue
		}
		if fenced {
			out.WriteString(line + "\n")
			continue
		}
		line = mdMarker.ReplaceAllString(line, "")
		for i, part := range strings.Split(line, "`") {
			if i%2 == 1 {
				out.WriteString(part)
				continue
			}
			part = mdLink.ReplaceAllString(part, "$1")
			part = mdAutolink.ReplaceAllString(part, "$1")
			part = mdTag.ReplaceAllString(part, " ")
			part = strings.ReplaceAll(part, "**", "")
			part = mdItalic.ReplaceAllString(part, "$1$2")
			out.WriteString(part)
		}
		out.WriteString("\n")
	}
	return strings.Fields(out.String())
}

// htmlBlocks are the tags that stand between words; any other tag is
// inside a run of text and parts no word.
var htmlBlocks = map[string]bool{
	"p": true, "div": true, "ul": true, "ol": true, "li": true, "details": true, "summary": true,
	"h1": true, "h2": true, "h3": true, "h4": true, "h5": true, "h6": true, "pre": true,
	"blockquote": true, "br": true, "table": true, "tr": true, "td": true, "th": true, "section": true,
}

// htmlWords are the words a reader of a page reads: its text, its
// entities read, without its tags and comments.
func htmlWords(text string) []string {
	text = htmlTag.ReplaceAllStringFunc(text, func(tag string) string {
		m := htmlTag.FindStringSubmatch(tag)
		if m[2] != "" && htmlBlocks[strings.ToLower(m[2])] {
			return " "
		}
		return ""
	})
	return strings.Fields(html.UnescapeString(text))
}

// firstDifference is the first index at which two word sequences differ,
// and false; or true where they are one sequence.
func firstDifference(a, b []string) (int, bool) {
	for i := range min(len(a), len(b)) {
		if a[i] != b[i] {
			return i, false
		}
	}
	if len(a) != len(b) {
		return min(len(a), len(b)), false
	}
	return 0, true
}

// around is the words before and after an index, the word at it marked.
func around(words []string, at int) string {
	const span = 8
	from, to := max(0, at-span), min(len(words), at+span)
	var b strings.Builder
	b.WriteString("…")
	for i := from; i < to; i++ {
		if i == at {
			b.WriteString(" ⟦" + words[i] + "⟧")
		} else {
			b.WriteString(" " + words[i])
		}
	}
	if at >= len(words) {
		b.WriteString(" ⟦end⟧")
	}
	return b.String() + " …"
}
