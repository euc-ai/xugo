package gates

import (
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"testing"
)

// A README TABLE ROW HAS ITS TABLE'S CELLS. GitHub splits a table row
// at every `|` that is not written `\|` — inside a code span too — and
// drops the cells past the header's count, so a member row whose
// statement holds `|x|` or `{x | P(x)}` loses the rest of its text
// without an error anywhere. A row is held to the cell count of its
// table's header row. A row standing after a blank line below its
// table is a paragraph on GitHub, not a row, and is refused too.
//
// What counts is GitHub's reading: a table is a header row followed by
// a delimiter row (`|---|---|`); its rows are the `|` lines that follow
// without a break; fenced code is passed over.
func TestLintReadmeTables(t *testing.T) {
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
		for _, p := range readmeTableProblems(string(src)) {
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

var readmeTableDelimiter = regexp.MustCompile(`^\|?\s*:?-+:?\s*(\|\s*:?-+:?\s*)*\|?$`)

// readmeTableCells is the number of cells GitHub reads in a table line:
// one more than its pipes not escaped by a backslash, the outer pipes
// left off.
func readmeTableCells(line string) int {
	s := strings.TrimSpace(line)
	s = strings.TrimPrefix(s, "|")
	if strings.HasSuffix(s, "|") && !strings.HasSuffix(s, `\|`) {
		s = s[:len(s)-1]
	}
	cells := 1
	for i := 0; i < len(s); i++ {
		switch s[i] {
		case '\\':
			i++
		case '|':
			cells++
		}
	}
	return cells
}

// readmeTableProblems lists the rows of a README's tables with more
// cells than their header — GitHub pads a shorter row with empty cells,
// and drops what a longer one holds past the header — and the rows cut
// off from their table by a blank line.
func readmeTableProblems(text string) []readmeProblem {
	var out []readmeProblem
	lines := strings.Split(text, "\n")
	fenced := false
	width := 0    // the header's cell count while inside a table, 0 outside
	lastRow := -2 // the index of the last header, delimiter or row line
	orphan := func(k int, line string) bool {
		return strings.HasPrefix(line, "|") && k >= 2 && lastRow == k-2 && strings.TrimSpace(lines[k-1]) == ""
	}
	for k, raw := range lines {
		line := strings.TrimSpace(raw)
		if strings.HasPrefix(line, "```") {
			fenced, width = !fenced, 0
			continue
		}
		if fenced {
			continue
		}
		if width > 0 {
			switch {
			case lastRow == k-1 && readmeTableDelimiter.MatchString(line):
				lastRow = k
				continue
			case strings.HasPrefix(line, "|"):
				if n := readmeTableCells(line); n > width {
					out = append(out, readmeProblem{k + 1, "this row has " + strconv.Itoa(n) + " cells and its table's header " +
						strconv.Itoa(width) + ": GitHub splits a row at every `|` not written `\\|`, a code span's included, " +
						"and drops the cells past the header's. Write a `|` inside a cell as `\\|`."})
				}
				lastRow = k
				continue
			}
			width = 0
		}
		switch {
		case strings.HasPrefix(line, "|") && k+1 < len(lines) && readmeTableDelimiter.MatchString(strings.TrimSpace(lines[k+1])):
			width, lastRow = readmeTableCells(line), k
		case orphan(k, line):
			out = append(out, readmeProblem{k + 1, "a blank line parts this row from the table above it, and " +
				"GitHub reads it as a paragraph: remove the blank line."})
		}
	}
	return out
}

// readmeTableProblems counts cells as GitHub does and finds a row parted
// from its table.
func TestReadmeTableProblems(t *testing.T) {
	const table = "| member | statement |\n|---|---|\n"
	for _, c := range []struct {
		text  string
		lines []int
	}{
		{table + "| `A` | `x ∈ s` |\n| `B` | `{x \\| P(x)}` and `\\|x\\|` |", nil},
		{table + "| `A` | `{x | P(x)}` |", []int{3}},
		{table + "| `A` | the size |x| |", []int{3}},
		{table + "| `A` | one |\n\n| `B` | parted |", []int{5}},
		{table + "| `A` | one |\n\nprose\n\n| not a table |", nil},
		{"```\n| a | b |\n|---|---|\n| c | d | e |\n```", nil},
		{"| a | b | c |\n|---|---|---|\n| `X` | two |", nil},
		{table + "| `A` | a\\|b and `||` |", []int{3}},
	} {
		var lines []int
		for _, p := range readmeTableProblems(c.text) {
			lines = append(lines, p.line)
		}
		if !slices.Equal(lines, c.lines) {
			t.Errorf("readmeTableProblems(%q) on lines %v; want %v", c.text, lines, c.lines)
		}
	}
}
