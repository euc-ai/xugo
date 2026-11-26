package gates

import (
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
	"testing"
)

// A README FORMULA IN LATEX IS ONE GITHUB TYPESETS. A chapter README
// writes in LaTeX the formulas Unicode cannot set plainly
// (library/chapter_constitution.md, the paragraph on formulas in a
// README): inline as `$…$` on one line, a
// display as a `$$` line, the formula, and a closing `$$` line. GitHub
// reads the math out of the markdown, but it still applies markdown's
// backslash escapes inside it and still reads a table row's pipes, so a
// formula can render as something else with no error anywhere:
//
//   - a backslash before ASCII punctuation is markdown's escape, and
//     the backslash is gone before the math is typeset: `\,` reaches
//     the renderer as `,`, `\{` as `{`, `\|` as `|`;
//   - a `*` in inline math pairs with another as emphasis, and the
//     span is no longer math (`p^*` is `p^\ast`);
//   - a `|` in inline math ends a table cell, and is a hazard in prose
//     beside one (`\lvert x \rvert`, `\lVert u \rVert`);
//   - a `$` with no partner on its line, or a span opening or closing
//     on a space, is not math at all.
//
// A code span is the corpus's spelling or a quotation and is not read.
func TestLintReadmeMath(t *testing.T) {
	proofs := filepath.Join(moduleRoot, "library", "proofs")
	readmes := 0
	err := filepath.WalkDir(proofs, func(path string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() || d.Name() != "README.md" {
			return err
		}
		readmes++
		src, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		rel, _ := filepath.Rel(moduleRoot, path)
		for _, p := range readmeProblems(string(src)) {
			t.Errorf("%s:%d: %s", rel, p.line, p.text)
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	if readmes == 0 {
		t.Fatalf("found no README.md under %q", proofs)
	}
}

type readmeProblem struct {
	line int
	text string
}

var (
	readmeCodeSpan    = regexp.MustCompile("`[^`]*`")
	readmeInlineMath  = regexp.MustCompile(`\$([^$]*)\$`)
	readmeEscapedMark = regexp.MustCompile(`\\[!-/:-@\[-` + "`" + `{-~]`)
)

// readmeProblems lists what GitHub would not typeset as written:
// the formulas of a README's $$ blocks and its inline $…$ spans, fenced
// code and code spans passed over.
func readmeProblems(text string) []readmeProblem {
	var out []readmeProblem
	add := func(line int, text string) {
		out = append(out, readmeProblem{line, text})
	}
	escapes := func(line int, tex string) {
		if m := readmeEscapedMark.FindString(tex); m != "" {
			add(line, "`"+m+"` in math is markdown's escape, and GitHub drops the backslash before typesetting. "+
				"Write the command another way (`\\lbrace`, `\\lVert`), or leave the spacing out.")
		}
	}
	fenced, display, opened := false, false, 0
	for k, raw := range strings.Split(text, "\n") {
		line := strings.TrimRight(raw, " \t\r")
		n := k + 1
		switch {
		case strings.HasPrefix(strings.TrimLeft(line, " \t"), "```"):
			fenced = !fenced
			continue
		case fenced:
			continue
		case line == "$$":
			display = !display
			opened = n
			continue
		case display:
			escapes(n, line)
			continue
		}
		bare := readmeCodeSpan.ReplaceAllString(line, "``")
		if strings.Contains(bare, "$$") {
			add(n, "a display formula is a `$$` line, the formula, and a `$$` line; `$$` inside a line is not one.")
			continue
		}
		if strings.Count(bare, "$")%2 != 0 {
			add(n, "a `$` with no partner on its line: an inline formula opens and closes on one line.")
			continue
		}
		for _, m := range readmeInlineMath.FindAllStringSubmatch(bare, -1) {
			tex := m[1]
			switch {
			case tex == "" || strings.TrimSpace(tex) != tex:
				add(n, "`$"+tex+"$` opens or closes on a space, and GitHub reads it as text: put the `$` against the formula.")
			case strings.Contains(tex, "*"):
				add(n, "`*` in `$"+tex+"$` pairs as markdown emphasis and the formula is lost: write `\\ast` (or `\\cdot` for a product).")
			case strings.Contains(tex, "|"):
				add(n, "`|` in `$"+tex+"$` ends a table cell: write `\\lvert … \\rvert` (`\\lVert … \\rVert` for a norm, `\\mid` for a divider).")
			}
			escapes(n, tex)
		}
	}
	if display {
		add(opened, "this `$$` opens a display formula that no `$$` line closes.")
	}
	return out
}

// readmeProblems passes code and the safe spellings, and names each
// trap once.
func TestReadmeMathProblems(t *testing.T) {
	for _, c := range []struct {
		text  string
		lines []int
	}{
		{"Plain `$x$` code, and $\\frac{1}{s-1}$ with $\\lvert x \\rvert$ and $p^\\ast$.", nil},
		{"$$\n\\sum_{n \\ge 1} n^{-s}\n$$", nil},
		{"```\n$ unpaired in a fence\n```", nil},
		{"a $ alone", []int{1}},
		{"$ x$ opens on a space", []int{1}},
		{"$p^*$ and $q^*$", []int{1, 1}},
		{"| `A` | $|x|$ |", []int{1}},
		{"thin $a\\,b$ and set $\\{x\\}$", []int{1, 1}},
		{"$$x$$ on one line", []int{1}},
		{"$$\n(s-1)\\,n\n$$", []int{2}},
		{"text\n$$\nnever closed", []int{2}},
	} {
		var lines []int
		for _, p := range readmeProblems(c.text) {
			lines = append(lines, p.line)
		}
		if !slices.Equal(lines, c.lines) {
			t.Errorf("readmeProblems(%q) on lines %v; want %v", c.text, lines, c.lines)
		}
	}
}
