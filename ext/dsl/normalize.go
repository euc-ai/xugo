// Surface-symbol normalization: NormalizeTextSymbols and the
// Unicode-subscript handling that let agents paste either ASCII
// or printed Unicode forms into DSL input.

package dsl

import (
	"strings"

	"github.com/euc-ai/xugo/utils"
)

// TextSymbol records a single symbol replacement applied to input text.
type TextSymbol struct {
	Position int    `json:"position"` // byte offset in the original string
	Length   int    `json:"length"`   // length of the original text replaced
	From     string `json:"from"`     // original text
	To       string `json:"to"`       // replacement text
}

// normRule is a single ASCII → Unicode replacement rule.
type normRule struct {
	from      string
	to        string
	wholeWord bool // only match when surrounded by non-alphanumeric chars
}

// normRules lists all replacements in priority order (longer matches first).
// Order matters: "<=>" must be tried before "=>" which must be tried before "->",
// and "<=>" must be tried before "<=" (otherwise "<=>" gets eaten as "<=" + ">").
var normRules = []normRule{
	// Multi-char operators (longest first)
	{"<=>", utils.IffStr, false},
	{"<=", "≤", false},
	{">=", "≥", false},
	{"!=", utils.NeqStr, false},
	{"=>", utils.ImplyStr, false},
	{"->", utils.FunStr, false},
	{`/\`, utils.AndStr, false},
	{`\/`, utils.OrStr, false},
	{"&&", utils.AndStr, false},
	// No `||` for ∨ and no `|-` for ⊢: `|` opens the `|x|` notation, so
	// `||x||` and `|-x|` are magnitudes; ∨'s ASCII spelling is `\/`, and
	// the turnstile has none.

	// Keywords (whole word only to avoid mangling variable names)
	{"forall", utils.ForAllStr, true},
	{"exists", utils.ForAllStr, false}, // handled specially below
	{"not", utils.NegStr, true},
	{"and", utils.AndStr, true},
	{"or", utils.OrStr, true},
	{"true", utils.TrueStr, true},
	{"false", utils.FalseStr, true},

	// Typographic twins of DSL symbols: the minus sign, and the n-ary
	// summation and product signs, which read as the DSL's `-`, `Σ`
	// and `Π`.
	{"−", "-", false},
	{"∑", "Σ", false},
	{"∏", "Π", false},

	// Single-char operators
	{"~", utils.NegStr, false},
	// "!" is special — only prefix negation, not inside identifiers.
}

func init() {
	// Fix the "exists" rule to use the correct symbol.
	for i := range normRules {
		if normRules[i].from == "exists" {
			normRules[i].to = utils.ExistsStr
			normRules[i].wholeWord = true
			break
		}
	}
}

// IdentifierName is the name a text spelling of an identifier reads as:
// a printed subscript (`x₀`) is the kernel's `x_0`, as the lexer reads
// it in any text, so a door that takes a bare NAME — a term_specialize
// table's binder — accepts the spelling every served statement prints.
func IdentifierName(name string) string { return denormalizeUnicodeSubscripts(name) }

// denormalizeUnicodeSubscripts rewrites every contiguous run of Unicode-
// subscript digits (U+2080..U+2089) as `_` followed by ASCII digits.
// The printer renders kernel variable names like `m_0`/`m_42`
// as Unicode-subscripted `m₀`/`m₄₂`; copying that printed form back into
// text-DSL input would otherwise hit the lexer's identifier rules,
// which only recognize ASCII letters/digits/underscore. Pre-normalizing
// here lets agents paste either form ("m₀" or "m_0") into lemma.text /
// assert.text / trans.const / case_split.const / etc. interchangeably.
//
// Conversion is per-run, not per-char: `m₀` → `m_0`, `m₄₂` → `m_42`,
// `f(m₀, n₀)` → `f(m_0, n_0)`. Subscripts in non-identifier positions
// (start of input, after punctuation) are still converted; downstream
// parser errors surface any genuinely ill-formed input.
func denormalizeUnicodeSubscripts(input string) string {
	if !strings.ContainsAny(input, "₀₁₂₃₄₅₆₇₈₉") {
		return input
	}
	var out strings.Builder
	out.Grow(len(input))
	inRun := false
	inAbbrev := false
	for _, r := range input {
		// An abbreviation's name is verbatim: `«R₀»` names the table's
		// entry R₀, and nothing inside the guillemets is a token.
		switch {
		case r == abbrevOpen:
			inAbbrev = true
		case r == abbrevClose:
			inAbbrev = false
		}
		if inAbbrev {
			out.WriteRune(r)
			inRun = false
			continue
		}
		if r >= '₀' && r <= '₉' {
			if !inRun {
				out.WriteByte('_')
				inRun = true
			}
			out.WriteRune('0' + (r - '₀'))
		} else {
			out.WriteRune(r)
			inRun = false
		}
	}
	return out.String()
}

// NormalizeTextSymbols replaces ASCII logic notation with canonical Unicode symbols.
// It returns the normalized string and a list of all replacements made.
// The input string is processed left-to-right; replacements do not overlap.
//
// Also pre-normalizes Unicode subscript digits (`m₀` → `m_0`) so the
// downstream lexer sees ASCII identifiers — see denormalizeUnicodeSubscripts.
// Subscript normalization is invisible to the TextSymbol diagnostic list
// (always-desired, never ambiguous), unlike logic-operator rewrites which
// agents may want to see surfaced.
func NormalizeTextSymbols(input string) (string, []TextSymbol) {
	if input == "" {
		return "", nil
	}
	input = denormalizeUnicodeSubscripts(input)

	var norms []TextSymbol
	var out strings.Builder
	out.Grow(len(input))

	i := 0
	for i < len(input) {
		// An abbreviation `«Name»` is verbatim: no keyword or operator
		// rewrite reaches inside it (an entry may be named «and»).
		if strings.HasPrefix(input[i:], string(abbrevOpen)) {
			if end := strings.Index(input[i:], string(abbrevClose)); end >= 0 {
				j := i + end + len(string(abbrevClose))
				out.WriteString(input[i:j])
				i = j
				continue
			}
		}
		// Skip if we're inside a string literal (double quotes).
		if input[i] == '"' {
			j := i + 1
			for j < len(input) && input[j] != '"' {
				if input[j] == '\\' {
					j++ // skip escaped char
				}
				j++
			}
			if j < len(input) {
				j++ // include closing quote
			}
			out.WriteString(input[i:j])
			i = j
			continue
		}

		// Try "!" as prefix negation: must be at start or after non-alnum.
		if input[i] == '!' && (i == 0 || !isAlphaNum(input[i-1])) {
			// `!=` normalizes to the inequality symbol ≠. This branch
			// has to run before the general `!` → ¬ rewrite below
			// because both consume the leading `!` (and the bare-`!`
			// case skips the rest of normRules).
			if i+1 < len(input) && input[i+1] == '=' {
				norms = append(norms, TextSymbol{
					Position: i,
					Length:   2,
					From:     "!=",
					To:       utils.NeqStr,
				})
				out.WriteString(utils.NeqStr)
				i += 2
				continue
			}
			// `∃!` (unique existential): the `!` is part of the quantifier,
			// not negation — pass it through so the lexer's ∃!-token rule
			// fires. Must precede the bare-`!` → ¬ rewrite below.
			if strings.HasSuffix(out.String(), utils.ExistsStr) {
				out.WriteByte('!')
				i++
				continue
			}
			norms = append(norms, TextSymbol{
				Position: i,
				Length:   1,
				From:     "!",
				To:       utils.NegStr,
			})
			out.WriteString(utils.NegStr)
			i++
			continue
		}

		matched := false
		for _, rule := range normRules {
			if i+len(rule.from) > len(input) {
				continue
			}
			candidate := input[i : i+len(rule.from)]

			// Case-insensitive match for keywords.
			if rule.wholeWord {
				if !strings.EqualFold(candidate, rule.from) {
					continue
				}
				// Check word boundaries.
				if i > 0 && isAlphaNum(input[i-1]) {
					continue
				}
				end := i + len(rule.from)
				if end < len(input) && isAlphaNum(input[end]) {
					continue
				}
			} else {
				if candidate != rule.from {
					continue
				}
			}

			norms = append(norms, TextSymbol{
				Position: i,
				Length:   len(rule.from),
				From:     rule.from,
				To:       rule.to,
			})
			out.WriteString(rule.to)
			i += len(rule.from)
			matched = true
			break
		}

		if !matched {
			// Copy the current byte (or full rune) as-is.
			r, size := runeAt(input, i)
			out.WriteRune(r)
			i += size
		}
	}

	return out.String(), norms
}

func isAlphaNum(b byte) bool {
	return (b >= 'a' && b <= 'z') || (b >= 'A' && b <= 'Z') || (b >= '0' && b <= '9') || b == '_'
}

func runeAt(s string, i int) (rune, int) {
	r := rune(s[i])
	if r < 0x80 {
		return r, 1
	}
	// Multi-byte UTF-8.
	var size int
	for size = 1; i+size < len(s) && (s[i+size]&0xC0) == 0x80; size++ {
	}
	runes := []rune(s[i : i+size])
	if len(runes) > 0 {
		return runes[0], size
	}
	return r, 1
}
