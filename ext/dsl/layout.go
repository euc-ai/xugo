package dsl

import (
	"fmt"
	"strings"
	"unicode/utf8"
)

// LayoutToken is one token of a text as a formatter that lays the text
// out over lines reads it: the span of the text as written that spells
// the token, and the part the token plays in the text's shape.
type LayoutToken struct {
	// Start and End are the token's byte span in the text as written,
	// before the symbol normalization the lexer reads (a subscript ₀ is
	// spelled there, not the `_0` the lexer sees).
	Start, End int
	Kind       LayoutKind
	// Level is a binary operator's layer, 1 the loosest and each next
	// one binding tighter, as the parser climbs them: ⇔, then ⇒ and →,
	// ∨, ∧, the relations, `..`, ∪ and ∖, ∩, + and -, •, * and /, ∘,
	// ^. It is zero for every other token.
	Level int
}

// LayoutKind is the part a token plays in the shape of a text.
type LayoutKind int

const (
	// LayoutAtom is a name, a numeral, an abbreviation, a constant
	// symbol, or any token the other kinds do not name.
	LayoutAtom LayoutKind = iota
	// LayoutOpen opens a group: ( { ⟨ ⟪ ⁅ ⟦ ⟬.
	LayoutOpen
	// LayoutClose closes one: ) } ⟩ ⟫ ⁆ ⟧ ⟭.
	LayoutClose
	// LayoutBinder is ∀, ∃, ∃!, λ or ε, which binds the names up to the
	// dot that ends its binders and reaches to the end of its scope.
	LayoutBinder
	// LayoutDot is a dot: the end of a binder's names, or a field's.
	LayoutDot
	// LayoutComma separates the members of a group.
	LayoutComma
	// LayoutPipe is a bar, a set-builder's separator inside braces.
	LayoutPipe
	// LayoutPrefix is a prefix operator: ¬, &, a prefix -.
	LayoutPrefix
	// LayoutInfix is a binary operator; Level is its layer.
	LayoutInfix
)

// LayoutTokens are the tokens of text in order, read as the lexer reads
// it. The error is the lexer's, or the text's normal form not lining up
// with the text word for word, which a normalization that adds or drops
// a blank would cause; the text is then not one a formatter may lay
// out.
func LayoutTokens(text string) ([]LayoutToken, error) {
	norm, _ := NormalizeTextSymbols(text)
	toks, diag := lex(norm)
	if diag != nil {
		return nil, fmt.Errorf("%s", diag.Message)
	}
	if n := len(toks); n > 0 && toks[n-1].kind == tokEOF {
		toks = toks[:n-1]
	}
	starts := make([]int, len(toks))
	for i, t := range toks {
		starts[i] = t.pos
	}
	starts, err := writtenOffsets(text, norm, starts)
	if err != nil {
		return nil, err
	}
	out := make([]LayoutToken, len(toks))
	for i, t := range toks {
		end := len(text)
		if i+1 < len(toks) {
			end = starts[i+1]
		}
		for end > starts[i] && isBlank(text[end-1]) {
			end--
		}
		out[i] = LayoutToken{Start: starts[i], End: end}
		out[i].Kind, out[i].Level = layoutRole(t.kind, i > 0 && operandEnds(out[i-1].Kind))
	}
	return out, nil
}

// OneLine is text on one line: its tokens with one space wherever text
// has blanks between two of them, and none after an opener or before a
// closer, as a text laid out over lines in source is read back for
// display. A text that does not lex is returned as it is.
func OneLine(text string) string {
	toks, err := LayoutTokens(text)
	if err != nil {
		return text
	}
	var b strings.Builder
	for i, t := range toks {
		if i > 0 && t.Start > toks[i-1].End && toks[i-1].Kind != LayoutOpen && t.Kind != LayoutClose {
			b.WriteByte(' ')
		}
		b.WriteString(text[t.Start:t.End])
	}
	return b.String()
}

// operandEnds reports whether a token of kind k can end an operand, so
// that a `-` after it is the binary minus and not the prefix one.
func operandEnds(k LayoutKind) bool {
	return k == LayoutAtom || k == LayoutClose
}

// layoutRole is the kind and layer of a token of kind k; afterOperand
// says the token before it ends an operand.
func layoutRole(k tokenKind, afterOperand bool) (LayoutKind, int) {
	switch k {
	case tokLParen, tokLBrace, tokLangle, tokLDAngle, tokLQuill, tokLDBracket, tokLShell:
		return LayoutOpen, 0
	case tokRParen, tokRBrace, tokRangle, tokRDAngle, tokRQuill, tokRDBracket, tokRShell:
		return LayoutClose, 0
	case tokForall, tokExists, tokUnique, tokLambda, tokHilbert:
		return LayoutBinder, 0
	case tokDot:
		return LayoutDot, 0
	case tokComma:
		return LayoutComma, 0
	case tokPipe:
		return LayoutPipe, 0
	case tokNot, tokAmp:
		return LayoutPrefix, 0
	case tokMinus:
		if !afterOperand {
			return LayoutPrefix, 0
		}
	}
	if level := operatorLayer(k); level > 0 {
		return LayoutInfix, level
	}
	return LayoutAtom, 0
}

// operatorLayer is the precedence layer of a binary operator token, in
// the order parseIff climbs them; zero for any other token.
func operatorLayer(k tokenKind) int {
	switch k {
	case tokIff:
		return 1
	case tokImply, tokArrow:
		return 2
	case tokOr:
		return 3
	case tokAnd:
		return 4
	case tokEquiv, tokTendsTo:
		return 5
	case tokDotDot:
		return 6
	case tokUnion, tokSetminus:
		return 7
	case tokInter:
		return 8
	case tokPlus, tokMinus:
		return 9
	case tokSmul:
		return 10
	case tokStar, tokSlash:
		return 11
	case tokCompose:
		return 12
	case tokCaret:
		return 13
	}
	if _, relational := relationalOp(k); relational {
		return 5
	}
	return 0
}

// writtenOffsets maps byte offsets of norm, text's normal form, to the
// offsets in text that begin the same tokens. Normalization rewrites
// inside the blank-separated words of a text and leaves its blanks as
// they are, so the two texts are the same words in normal form and
// text's, and an offset is found inside its word.
func writtenOffsets(text, norm string, offsets []int) ([]int, error) {
	if text == norm {
		return offsets, nil
	}
	written, normal := blankWords(text), blankWords(norm)
	if len(written) != len(normal) {
		return nil, fmt.Errorf("the normal form has %d words, the text %d", len(normal), len(written))
	}
	for i, w := range written {
		if n, _ := NormalizeTextSymbols(text[w[0]:w[1]]); n != norm[normal[i][0]:normal[i][1]] {
			return nil, fmt.Errorf("the word %q normalizes alone to %q, in its text to %q", text[w[0]:w[1]], n, norm[normal[i][0]:normal[i][1]])
		}
	}
	out := make([]int, len(offsets))
	w := 0
	for i, k := range offsets {
		for w < len(normal) && normal[w][1] <= k {
			w++
		}
		if w == len(normal) || k < normal[w][0] {
			return nil, fmt.Errorf("offset %d of the normal form is in no word", k)
		}
		word := text[written[w][0]:written[w][1]]
		j, found := writtenPrefix(word, norm[normal[w][0]:k])
		if !found {
			return nil, fmt.Errorf("no prefix of %q normalizes to %q", word, norm[normal[w][0]:k])
		}
		out[i] = written[w][0] + j
	}
	return out, nil
}

// writtenPrefix is the length of the prefix of word whose normal form is
// want.
func writtenPrefix(word, want string) (int, bool) {
	for j := 0; j <= len(word); {
		if n, _ := NormalizeTextSymbols(word[:j]); n == want {
			return j, true
		}
		if j == len(word) {
			break
		}
		_, size := utf8.DecodeRuneInString(word[j:])
		j += size
	}
	return 0, false
}

// blankWords are the byte spans of the runs of text between blanks.
func blankWords(text string) [][2]int {
	var words [][2]int
	start := -1
	for i := 0; i < len(text); i++ {
		switch {
		case isBlank(text[i]) && start >= 0:
			words = append(words, [2]int{start, i})
			start = -1
		case !isBlank(text[i]) && start < 0:
			start = i
		}
	}
	if start >= 0 {
		words = append(words, [2]int{start, len(text)})
	}
	return words
}

// isBlank reports whether b is a byte the lexer skips between tokens.
func isBlank(b byte) bool {
	return b == ' ' || b == '\t' || b == '\n' || b == '\r'
}
