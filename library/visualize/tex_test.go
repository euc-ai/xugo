package visualize

import (
	"encoding/xml"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

// texMathML reads a formula part by part: letters, numbers and
// operators, scripts and primes, groups, fractions and roots, fences
// that grow and fences that do not, named functions, ranges under a sum
// in a display and beside it in a line.
func TestTexMathML(t *testing.T) {
	for _, c := range []struct {
		tex     string
		display bool
		want    string
	}{
		{`x`, false, `<math><mrow><mi>x</mi></mrow></math>`},
		{`S^{n+1}`, false, `<math><mrow><msup><mi>S</mi><mrow><mi>n</mi><mo>+</mo><mn>1</mn></mrow></msup></mrow></math>`},
		{`\Omega_{S/R}`, false, `<math><mrow><msub><mi mathvariant="normal">Ω</mi><mrow><mi>S</mi><mo lspace="0" rspace="0">/</mo><mi>R</mi></mrow></msub></mrow></math>`},
		{`a_i^2 - 1.5`, false, `<math><mrow><msubsup><mi>a</mi><mi>i</mi><mn>2</mn></msubsup><mo>−</mo><mn>1.5</mn></mrow></math>`},
		{`g' < f''^2`, false, `<math><mrow><msup><mi>g</mi><mo>′</mo></msup><mo>&lt;</mo><msup><mi>f</mi><mrow><mo>′′</mo><mn>2</mn></mrow></msup></mrow></math>`},
		{`\frac{dx}{2y}`, false, `<math><mrow><mfrac><mrow><mi>d</mi><mi>x</mi></mrow><mrow><mn>2</mn><mi>y</mi></mrow></mfrac></mrow></math>`},
		{`\sqrt{x} + \sqrt[3]{y}`, false, `<math><mrow><msqrt><mi>x</mi></msqrt><mo>+</mo><mroot><mi>y</mi><mrow><mn>3</mn></mrow></mroot></mrow></math>`},
		{`\left(\frac{p}{q}\right)`, false, `<math><mrow><mrow><mo fence="true" stretchy="true" form="prefix">(</mo><mfrac><mi>p</mi><mi>q</mi></mfrac><mo fence="true" stretchy="true" form="postfix">)</mo></mrow></mrow></math>`},
		{`\bigl(x\bigr)`, false, `<math><mrow><mo fence="true" stretchy="true" minsize="1.2em" maxsize="1.2em">(</mo><mi>x</mi><mo fence="true" stretchy="true" minsize="1.2em" maxsize="1.2em">)</mo></mrow></math>`},
		{`\lvert y \rvert`, false, `<math><mrow><mo fence="true" form="prefix" stretchy="false">|</mo><mi>y</mi><mo fence="true" form="postfix" stretchy="false">|</mo></mrow></math>`},
		{`\operatorname{Re} s`, false, `<math><mrow><mi mathvariant="normal">Re</mi><mo>&#x2061;</mo><mspace width="0.1667em"/><mi>s</mi></mrow></math>`},
		{`\log_2 n + \exp(x)`, false, `<math><mrow><msub><mi>log</mi><mn>2</mn></msub><mo>&#x2061;</mo><mspace width="0.1667em"/><mi>n</mi><mo>+</mo><mi>exp</mi><mo>&#x2061;</mo><mo stretchy="false">(</mo><mi>x</mi><mo stretchy="false">)</mo></mrow></math>`},
		{`\sum_{n \ge 1} n^{-s}`, false, `<math><mrow><msub><mo>∑</mo><mrow><mi>n</mi><mo>≥</mo><mn>1</mn></mrow></msub><msup><mi>n</mi><mrow><mo>−</mo><mi>s</mi></mrow></msup></mrow></math>`},
		{`\sum_{n \ge 1} n^{-s}`, true, `<math display="block"><mrow><munder><mo>∑</mo><mrow><mi>n</mi><mo>≥</mo><mn>1</mn></mrow></munder><msup><mi>n</mi><mrow><mo>−</mo><mi>s</mi></mrow></msup></mrow></math>`},
		{`\frac{\sum_k a_k}{2}`, true, `<math display="block"><mrow><mfrac><mrow><msub><mo>∑</mo><mi>k</mi></msub><msub><mi>a</mi><mi>k</mi></msub></mrow><mn>2</mn></mfrac></mrow></math>`},
		{`\min_{x} f`, true, `<math display="block"><mrow><munder><mi>min</mi><mi>x</mi></munder><mo>&#x2061;</mo><mspace width="0.1667em"/><mi>f</mi></mrow></math>`},
		{`\int_0^1 f`, true, `<math display="block"><mrow><msubsup><mo>∫</mo><mn>0</mn><mn>1</mn></msubsup><mi>f</mi></mrow></math>`},
		{`a \equiv b \pmod{n}`, false, `<math><mrow><mi>a</mi><mo>≡</mo><mi>b</mi><mspace width="0.4444em"/><mo stretchy="false">(</mo><mi>mod</mi><mspace width="0.3333em"/><mi>n</mi><mo stretchy="false">)</mo></mrow></math>`},
		{`\mathbb{R} \to \text{a set}`, false, `<math><mrow><mi>ℝ</mi><mo>→</mo><mtext>a set</mtext></mrow></math>`},
		{`⟪u, v⟫ • w`, false, `<math><mrow><mo stretchy="false">⟪</mo><mi>u</mi><mo>,</mo><mi>v</mi><mo stretchy="false">⟫</mo><mo>•</mo><mi>w</mi></mrow></math>`},
		{`{}^n x`, false, `<math><mrow><msup><mrow></mrow><mi>n</mi></msup><mi>x</mi></mrow></math>`},
	} {
		got, err := texMathML(c.tex, c.display)
		require.NoError(t, err, c.tex)
		require.Equal(t, c.want, got, c.tex)
	}
}

// A formula the reader does not know whole is an error that names it.
func TestTexMathMLRefuses(t *testing.T) {
	for tex, part := range map[string]string{
		`\begin{matrix} a \end{matrix}`: `\begin is no command`,
		`a \, b`:                        `\, is no command`,
		`x^2^3`:                         "two superscripts",
		`x_1_2`:                         "two subscripts",
		`\frac{a}`:                      "an argument is due",
		`{a + b`:                        "no } closes",
		`a + b}`:                        "no { before",
		`\left( a`:                      `no \right closes`,
		`a \right)`:                     `no \left before`,
		`\left a b \right)`:             "is no delimiter",
		`\operatorname x`:               "a { is due",
		`a \`:                           "a backslash ends it",
	} {
		_, err := texMathML(tex, false)
		require.ErrorContains(t, err, part, tex)
		require.ErrorContains(t, err, "$"+tex+"$", tex)
	}
}

// typeset sets a text's formulas between the two marks and leaves a
// code span's dollars, and the rest, as written.
func TestTypeset(t *testing.T) {
	got, err := typeset("the unit `$x$` and $x^2$, then `a` and $y$.")
	require.NoError(t, err)
	require.Equal(t, "the unit `$x$` and "+mathOpen+"<math><mrow><msup><mi>x</mi><mn>2</mn></msup></mrow></math>"+mathClose+
		", then `a` and "+mathOpen+"<math><mrow><mi>y</mi></mrow></math>"+mathClose+".", got)

	plain, err := typeset("no formula, a lone $ and **strong** words")
	require.NoError(t, err)
	require.Equal(t, "no formula, a lone $ and **strong** words", plain)

	_, err = typeset(`fine $x$ and not $\nosuch$`)
	require.ErrorContains(t, err, `\nosuch is no command`)
}

// Every formula of every chapter README is one the reader knows, and
// reads into well-formed MathML: the lines between two "$$" lines, and
// each "$…$" outside a code span and a fence.
func TestReadmeFormulasTypeset(t *testing.T) {
	wellFormed := func(where, mathml string) {
		d := xml.NewDecoder(strings.NewReader(mathml))
		for {
			if _, err := d.Token(); err == io.EOF {
				return
			} else if err != nil {
				t.Errorf("%s: %s is not well formed: %v", where, mathml, err)
				return
			}
		}
	}
	readmes, formulas := 0, 0
	err := filepath.WalkDir(corpusRoot, func(path string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() || d.Name() != "README.md" {
			return err
		}
		readmes++
		text, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		lines := strings.Split(string(text), "\n")
		for k := 0; k < len(lines); k++ {
			line := strings.TrimRight(lines[k], " \t\r")
			switch {
			case strings.HasPrefix(strings.TrimLeft(line, " \t"), "```"):
				for k++; k < len(lines) && !strings.HasPrefix(strings.TrimSpace(lines[k]), "```"); k++ {
				}
			case line == "$$":
				var tex []string
				for k++; k < len(lines) && strings.TrimRight(lines[k], " \t\r") != "$$"; k++ {
					tex = append(tex, strings.TrimSpace(lines[k]))
				}
				mathml, err := texMathML(strings.Join(tex, " "), true)
				if err != nil {
					t.Errorf("%s:%d: %v", path, k+1, err)
					continue
				}
				formulas++
				wellFormed(path, mathml)
			default:
				set, err := typeset(line)
				if err != nil {
					t.Errorf("%s:%d: %v", path, k+1, err)
					continue
				}
				for _, part := range strings.Split(set, mathOpen)[1:] {
					formulas++
					wellFormed(path, part[:strings.Index(part, mathClose)])
				}
			}
		}
		return nil
	})
	require.NoError(t, err)
	require.Positive(t, readmes)
	require.Positive(t, formulas, "no README writes a formula in LaTeX")
	t.Logf("%d formulas in %d READMEs", formulas, readmes)
}
