package gates

import (
	"io/fs"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
)

// A CHAPTER README OPENS WITH AN INTRODUCTION. Between the title line,
// `# <name> — <gloss>`, and the first `##` section stands prose saying
// what the chapter holds and how it is organized: the chapter's
// overview, what a reader who opens the family meets before any section
// and its member tables. The gloss is one line and a section is one
// part of the chapter, so neither stands in for it.
//
// What counts is a line of prose: outside a fenced code block, not
// blank, not a table row (opening with "|"), not a heading, and not
// indented four spaces (an indented code block). A paragraph or a list
// is an introduction; a table or a code block alone is not. Whether the
// prose is true of the chapter no lint reads.
//
// The population is every directory under library/proofs holding a
// family.go, found by walking and never listed, so a new family is
// inside the lint from its first file and its README is written with an
// introduction when it is scaffolded.
func TestLintReadmeIntroduction(t *testing.T) {
	proofs := filepath.Join(moduleRoot, "library", "proofs")
	families := 0
	err := filepath.WalkDir(proofs, func(path string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() || d.Name() != "family.go" {
			return err
		}
		families++
		readme := filepath.Join(filepath.Dir(path), "README.md")
		rel, _ := filepath.Rel(moduleRoot, readme)
		src, err := os.ReadFile(readme)
		if err != nil {
			t.Errorf("%s: %v.\n    Every family's README opens with its title line and an introduction.", rel, err)
			return nil
		}
		if end, line := readmeIntroductionGap(string(src)); line > 0 {
			t.Errorf("%s:%d: the README has no introduction: no prose stands between its title line and %s.\n"+
				"    Write the introduction there: prose saying what the chapter holds and how it is "+
				"organized, the overview read before any section (library/chapter_constitution.md, "+
				"the `README.md` item).",
				rel, line, end)
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	// A walk that found no family read the wrong tree.
	if families == 0 {
		t.Fatalf("found no family.go under %q", proofs)
	}
}

// readmeIntroductionGap finds prose in a paragraph or a list, and none
// in a table, a code block fenced or indented, or a heading; a `##`
// inside a fence is code, and "#word" is no heading.
func TestReadmeIntroductionGap(t *testing.T) {
	const title = "# a_family — its gloss\n"
	for _, c := range []struct {
		body string
		end  string
		line int
	}{
		{"\nA paragraph.\n\n## A section\n", "", 0},
		{"\n- an item\n\n## A section\n", "", 0},
		{"\n#word is prose\n", "", 0},
		{"\n## A section\n\nIts prose.\n", `the section "## A section"`, 3},
		{"\n| member | statement |\n|---|---|\n\n### A subsection\n", `the section "### A subsection"`, 6},
		{"\n```\n## fenced\nprose in a fence\n```\n\n    indented code\n\n## A section\n", `the section "## A section"`, 10},
		{"\n| a table, and no section |\n", "the end of the file", 4},
	} {
		end, line := readmeIntroductionGap(title + c.body)
		if end != c.end || line != c.line {
			t.Errorf("readmeIntroductionGap(%q) = %q, %d; want %q, %d", title+c.body, end, line, c.end, c.line)
		}
	}
}

// readmeIntroductionGap reads a README's introduction, the lines after
// the title and before the first heading below it. It returns line 0
// when a line of prose stands there; otherwise what ends the
// introduction — the first section, or the end of the file — and its
// 1-based line.
func readmeIntroductionGap(text string) (string, int) {
	lines := strings.Split(text, "\n")
	fenced := false
	for k := 1; k < len(lines); k++ {
		line := strings.TrimRight(lines[k], " \t\r")
		body := strings.TrimLeft(line, " \t")
		level := len(body) - len(strings.TrimLeft(body, "#"))
		heading := level > 0 && strings.HasPrefix(body[level:], " ")
		switch {
		case strings.HasPrefix(body, "```"):
			fenced = !fenced
		case fenced, body == "", strings.HasPrefix(body, "|"), strings.HasPrefix(line, "    "):
		case heading && level >= 2:
			return "the section " + strconv.Quote(body), k + 1
		case heading:
		default:
			return "", 0
		}
	}
	return "the end of the file", len(lines)
}
