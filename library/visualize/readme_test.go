package visualize

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

// readmeIntro keeps a README's prose up to its first section, in order
// — paragraphs with their lines joined, lists, code blocks fenced or
// indented, formulas typeset where they stand and on their own lines —
// and leaves out the title and a table.
func TestReadmeIntro(t *testing.T) {
	text := strings.Join([]string{
		"# finite_group — the order of a finite group",
		"",
		"A finite group is a group record `G`",
		"with `finite(G.carrier)`.",
		"",
		"A left coset is as large as `h`, of size $n$:",
		"$$",
		"\\sum_{k} a_k",
		"= n",
		"$$",
		"and no larger.",
		"",
		"    card(k) = card(h) * card(image(f, k))",
		"    card(h) ∣ card(k)",
		"",
		"| member | statement |",
		"|---|---|",
		"| `LagrangeOn` | `card(k) = …` |",
		"",
		"- the partition argument,",
		"  from the equivalence chapter;",
		"- the counting argument.",
		"",
		"    - a further item",
		"",
		"1. first",
		"2. second",
		"",
		"```",
		"| not a table |",
		"  two",
		"## not a heading",
		"```",
		"#not a heading",
		"",
		"## Lagrange's theorem",
		"",
		"A section's prose is no introduction.",
	}, "\n")
	blocks, err := readmeIntro(text)
	require.NoError(t, err)
	require.Equal(t, []ReadmeBlock{
		{Text: "A finite group is a group record `G` with `finite(G.carrier)`."},
		{Text: "A left coset is as large as `h`, of size " + mathOpen + "<math><mrow><mi>n</mi></mrow></math>" + mathClose + ":"},
		{Formula: `<math display="block"><mrow><munder><mo>∑</mo><mi>k</mi></munder><msub><mi>a</mi><mi>k</mi></msub><mo>=</mo><mi>n</mi></mrow></math>`},
		{Text: "and no larger."},
		{Code: true, Text: "card(k) = card(h) * card(image(f, k))\ncard(h) ∣ card(k)"},
		{Items: []string{"the partition argument, from the equivalence chapter;", "the counting argument.", "a further item"}},
		{Ordered: true, Items: []string{"first", "second"}},
		{Code: true, Text: "| not a table |\n  two\n## not a heading"},
		{Text: "#not a heading"},
	}, blocks)

	none, err := readmeIntro("# a_title — and its gloss\n\n## A section at once\n\nIts prose.\n")
	require.NoError(t, err)
	require.Equal(t, []ReadmeBlock{}, none)

	_, err = readmeIntro("# t — g\n\n$$\nx\n")
	require.ErrorContains(t, err, "no $$ line closes")
	_, err = readmeIntro("# t — g\n\nA formula $\\nosuch$ here.\n")
	require.ErrorContains(t, err, "is no command")
}
