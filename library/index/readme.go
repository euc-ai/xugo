package index

import (
	"fmt"
	"strings"
	"sync"
)

// A chapter's README lists its members in tables, and the plain row is
// two cells: the member's bare name alone in backticks, and what the
// chapter says of it — a sentence for a theorem, the constant and its
// type for a definition. The row is read as text, once per README, for
// a member with no doc comment (Description). A row of
// another shape — several names in the first cell, a third column — is
// not a member's row and is not read.

// cardMark closes a card's row in its README's members table
// (chapter_constitution.md, "a chapter's README marks each card").
const cardMark = " — card"

// _ReadmeRows is one family README's member rows, by bare name.
type _ReadmeRows struct {
	once sync.Once
	rows map[string]string
	err  error
}

// readmeRow is what the family's README says of a member in its
// table: the second cell of the member's row as written, markdown and
// all, a card's mark left off. Empty where the README has no row for
// the member; a README that cannot be read is an error.
func (c *Corpus) readmeRow(m *Member) (string, error) {
	f := c.byFamily[m.Family]
	c.readmesMu.Lock()
	r := c.readmes[f.Name]
	if r == nil {
		r = &_ReadmeRows{}
		c.readmes[f.Name] = r
	}
	c.readmesMu.Unlock()
	r.once.Do(func() {
		text, err := readmeText(c.Root, f.Readme)
		if err != nil {
			r.err = fmt.Errorf("index: family %s: %v", f.Name, err)
			return
		}
		r.rows = memberRows(text)
	})
	return r.rows[m.bare()], r.err
}

// Description is what a member's chapter says it is, in words: the doc
// comment above the member in its chapter file, or, for a member the
// chapter leaves uncommented, its row in the chapter's README
// (readmeRow). Empty for a member with neither; a chapter file that
// declares nothing where the registry has the member is an error, and
// so is a README that cannot be read.
func (c *Corpus) Description(m *Member) (string, error) {
	decl, err := c.declaration(m)
	if err != nil {
		return "", err
	}
	if decl.gloss != "" {
		return decl.gloss, nil
	}
	return c.readmeRow(m)
}

// memberRows reads the member rows of a README's text: each table line
// of two cells whose first is one name in backticks, as name → second
// cell, the card mark dropped. A name's first row is the one kept.
func memberRows(text string) map[string]string {
	rows := map[string]string{}
	for _, line := range strings.Split(text, "\n") {
		if !strings.HasPrefix(line, "|") {
			continue
		}
		cells := tableCells(strings.TrimSpace(line))
		if len(cells) != 4 || cells[0] != "" || cells[3] != "" {
			continue
		}
		name, ticked := strings.CutPrefix(cells[1], "`")
		name, closed := strings.CutSuffix(name, "`")
		if !ticked || !closed || name == "" || strings.ContainsAny(name, "` ,") {
			continue
		}
		if _, seen := rows[name]; !seen {
			rows[name] = strings.TrimSuffix(cells[2], cardMark)
		}
	}
	return rows
}

// tableCells splits a markdown table line at its pipes, each cell
// trimmed: a row `| a | b |` is four cells, the first and last empty.
// An escaped pipe `\|` is the cell's own and is written `|`.
func tableCells(line string) []string {
	var cells []string
	var cell strings.Builder
	for i := 0; i < len(line); i++ {
		switch {
		case line[i] == '\\' && i+1 < len(line) && line[i+1] == '|':
			cell.WriteByte('|')
			i++
		case line[i] == '|':
			cells = append(cells, strings.TrimSpace(cell.String()))
			cell.Reset()
		default:
			cell.WriteByte(line[i])
		}
	}
	return append(cells, strings.TrimSpace(cell.String()))
}
