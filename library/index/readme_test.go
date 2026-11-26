package index

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

// A README's member rows are its two-cell table rows naming one member
// in backticks: the card mark is dropped and an escaped pipe is the
// cell's own. A row of several names or of a third cell is not read, a
// name's first row stands, and a text line that opens with a pipe is
// no row.
func TestMemberRows(t *testing.T) {
	text := strings.Join([]string{
		"# family — a title",
		"",
		"| member | statement |",
		"|---|---|",
		"| `Alpha` | The first law |",
		"| `Beta` | The second law, `f(x) = \\|x\\|` — card |",
		"| `Gamma`, `Delta` | two laws in one row |",
		"| `Epsilon` | `EpsilonOn` | a third cell |",
		"| `Alpha` | a later row of the same name |",
		"| Zeta | a name outside backticks |",
		"|x| < 1 opens a line of a paragraph",
	}, "\n")
	require.Equal(t, map[string]string{
		"Alpha": "The first law",
		"Beta":  "The second law, `f(x) = |x|`",
	}, memberRows(text))
}

// Over the corpus: a member's description is its doc comment where
// the chapter writes one and its README row otherwise, and a card's
// row is read without its mark.
func TestDescription(t *testing.T) {
	c := load(t)
	cardRows := 0
	for _, m := range c.Members {
		decl, err := c.declaration(m)
		require.NoError(t, err)
		row, err := c.readmeRow(m)
		require.NoError(t, err)
		require.False(t, strings.HasSuffix(row, cardMark), m.ID)
		if m.Card && row != "" {
			cardRows++
		}
		gloss, err := c.Description(m)
		require.NoError(t, err)
		if decl.gloss != "" {
			require.Equal(t, decl.gloss, gloss, m.ID)
		} else {
			require.Equal(t, row, gloss, m.ID)
		}
	}
	require.Positive(t, cardRows, "the corpus holds a card with a README row")
}
