package visualize

// A chapter's README read for the family graph's page: its
// introduction, the prose between the title and the first section,
// block by block. The title line is left out — it is the family's name
// and gloss, which the node carries — and so is a table. The text of a
// block is the README's markdown as written, its formulas typeset
// (typeset); `code`, **strong**, *emphasis* and [links](…) are the
// page's to render.

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"github.com/euc-ai/xugo/library/index"
)

// ReadmeBlock is one block of a README's prose. It is a list where
// Items holds its items, numbered where Ordered; a code block where
// Code is set, Text its lines; a formula set on its own line where
// Formula holds it, as MathML; and otherwise a paragraph, Text its
// lines joined.
type ReadmeBlock struct {
	Text    string   `json:"text,omitempty"`
	Items   []string `json:"items,omitempty"`
	Ordered bool     `json:"ordered,omitzero"`
	Code    bool     `json:"code,omitzero"`
	Formula string   `json:"formula,omitempty"`
}

// intro reads the introduction of a family's README: no block for a
// family that has no README, an error for a README that cannot be read
// or that holds a formula the page cannot typeset.
func intro(c *index.Corpus, f *index.Family) ([]ReadmeBlock, error) {
	if f.Readme == "" {
		return []ReadmeBlock{}, nil
	}
	text, err := os.ReadFile(filepath.Join(c.Root, filepath.FromSlash(f.Readme)))
	if err != nil {
		return nil, err
	}
	return readmeIntro(string(text))
}

// readmeIntro reads the introduction of a README's text as blocks: what
// stands before the first heading below the title. A line of "#"s and a
// space is a heading, the title's a single "#"; a line opening with "|"
// is a table's and is dropped; a line that is "$$" opens a formula set
// on its own line, the lines up to the next such line; a fence of backticks opens a
// code block that the next fence closes, and so does a line indented by
// four spaces where no paragraph or item is open — unless it is a
// further item of the list before it — closed by the first line
// indented less; a line opening with "- ", "* " or "1. " starts a list
// item, in the list before it where only blank lines lie between;
// any other line continues the paragraph or item open before it, or
// opens a paragraph. A blank line closes a paragraph. The formulas of a
// paragraph and of a list's items are typeset where they stand.
func readmeIntro(text string) ([]ReadmeBlock, error) {
	blocks := []ReadmeBlock{}
	// open is what a plain line would continue: a paragraph, the last
	// item of a list, or nothing. listed says the last block is a list
	// that an item may still join.
	const (
		nothing = iota
		paragraph
		item
	)
	open, listed := nothing, false
	lines := strings.Split(text, "\n")
	for k := 0; k < len(lines); k++ {
		line := strings.TrimRight(lines[k], " \t\r")
		body := strings.TrimLeft(line, " \t")
		_, _, marker := listItem(body)
		switch level := headingLevel(body); {
		case body == "":
			open = nothing
		case line == "$$":
			var tex []string
			for k++; k < len(lines) && strings.TrimRight(lines[k], " \t\r") != "$$"; k++ {
				tex = append(tex, strings.TrimSpace(lines[k]))
			}
			if k == len(lines) {
				return nil, fmt.Errorf("a $$ line opens a formula that no $$ line closes")
			}
			formula, err := texMathML(strings.Join(tex, " "), true)
			if err != nil {
				return nil, err
			}
			blocks = append(blocks, ReadmeBlock{Formula: formula})
			open, listed = nothing, false
		case strings.HasPrefix(body, "```"):
			var code []string
			for k++; k < len(lines) && !strings.HasPrefix(strings.TrimSpace(lines[k]), "```"); k++ {
				code = append(code, strings.TrimRight(lines[k], " \t\r"))
			}
			blocks = append(blocks, ReadmeBlock{Code: true, Text: strings.Join(code, "\n")})
			open, listed = nothing, false
		case open == nothing && strings.HasPrefix(line, "    ") && !(listed && marker):
			code := []string{line[4:]}
			for ; k+1 < len(lines) && strings.HasPrefix(lines[k+1], "    ") && strings.TrimSpace(lines[k+1]) != ""; k++ {
				code = append(code, strings.TrimRight(lines[k+1][4:], " \t\r"))
			}
			blocks = append(blocks, ReadmeBlock{Code: true, Text: strings.Join(code, "\n")})
			listed = false
		case strings.HasPrefix(line, "|"):
			open, listed = nothing, false
		case level > 1:
			return typesetBlocks(blocks)
		case level == 1:
			open, listed = nothing, false
		default:
			body, ordered, _ := listItem(body)
			switch {
			case marker:
				if !listed || blocks[len(blocks)-1].Ordered != ordered {
					blocks = append(blocks, ReadmeBlock{Ordered: ordered})
				}
				last := &blocks[len(blocks)-1]
				last.Items = append(last.Items, body)
				open, listed = item, true
			case open == item:
				last := &blocks[len(blocks)-1]
				last.Items[len(last.Items)-1] += " " + body
			case open == paragraph:
				blocks[len(blocks)-1].Text += " " + body
			default:
				blocks = append(blocks, ReadmeBlock{Text: body})
				open, listed = paragraph, false
			}
		}
	}
	return typesetBlocks(blocks)
}

// typesetBlocks typesets the formulas of the paragraphs and of the
// lists' items.
func typesetBlocks(blocks []ReadmeBlock) ([]ReadmeBlock, error) {
	for i := range blocks {
		if blocks[i].Code {
			continue
		}
		var err error
		if blocks[i].Text, err = typeset(blocks[i].Text); err != nil {
			return nil, err
		}
		for j := range blocks[i].Items {
			if blocks[i].Items[j], err = typeset(blocks[i].Items[j]); err != nil {
				return nil, err
			}
		}
	}
	return blocks, nil
}

// headingLevel is the number of "#"s a heading line opens with, 0 for a
// line that is no heading.
func headingLevel(line string) int {
	level := 0
	for level < len(line) && line[level] == '#' {
		level++
	}
	if level == 0 || level > 6 || level == len(line) || line[level] != ' ' {
		return 0
	}
	return level
}

// listItem reads a line that starts a list item: the item's text past
// the marker, and whether the marker is a number. A line with no marker
// is returned as it is.
func listItem(line string) (text string, ordered, marked bool) {
	if rest, ok := strings.CutPrefix(line, "- "); ok {
		return strings.TrimSpace(rest), false, true
	}
	if rest, ok := strings.CutPrefix(line, "* "); ok {
		return strings.TrimSpace(rest), false, true
	}
	digits := 0
	for digits < len(line) && line[digits] >= '0' && line[digits] <= '9' {
		digits++
	}
	if digits > 0 && strings.HasPrefix(line[digits:], ". ") {
		return strings.TrimSpace(line[digits+2:]), true, true
	}
	return line, false, false
}
