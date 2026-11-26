package dsl

import (
	"strings"
	"unicode"
	"unicode/utf8"
)

// SurfaceForm is a printed statement in the chapter's surface spelling
// beyond what ChapterSpelling folds: a set binder spelled `set(τ)`, by
// the fold rule (RespellSets) — `∀s:(A → bool). … s ⊆ t` is
// `∀s:set(A). …` — and a constant's instance tie `⟨A:τ⟩` dropped where
// the constant's arguments fix the instance, as the statement door
// reads every occurrence with fresh letters (`finite⟨A:A⟩(s)` is
// `finite(s)` for s:set(A)). The printer writes both — the binder's
// type as the kernel holds it, a tie on every occurrence of a constant
// the statement holds at two instances — and a chapter writes neither.
//
// Each rewrite is kept only where reads accepts the text it makes: the
// caller's read-back check at the door the text is served for, so the
// result states what the input stated. Numeric embeddings are omitted
// where the reading restores them, with integer arithmetic and natural
// arithmetic kept distinct. An embedding needed to select the domain
// keeps its spelling, or takes `&` where that reads identically.
func SurfaceForm(text string, reads func(string) bool) string {
	if respelled, _ := RespellSets(text); respelled != text && reads(respelled) {
		text = respelled
	}
	ties := instanceTies(text)
	if len(ties) > 0 {
		if bare := dropSpans(text, ties); reads(bare) {
			text = bare
		} else {
			// Last first so the earlier spans keep their offsets.
			for i := len(ties) - 1; i >= 0; i-- {
				if bare := dropSpans(text, ties[i:i+1]); reads(bare) {
					text = bare
				}
			}
		}
	}
	return implicitNumericSurface(text, reads)
}

// implicitNumericSurface tries removing embeddings together, then one
// at a time from right to left, retaining the anchors the reading needs.
// The AST printer preserves precedence: dropping int_of_num(a - b)
// inside z + int_of_num(a - b) leaves z + (a - b), not z + a - b.
// Every candidate is checked at the caller's actual parse door; neither
// a successful parse alone nor a proposition's normalized key suffices.
func implicitNumericSurface(text string, reads func(string) bool) string {
	if !strings.Contains(text, integerLiteralHead) && !strings.Contains(text, "&") {
		return text
	}
	work, err := parseStmtAST(text)
	if err != nil {
		return text
	}
	type _EmbeddingCandidate struct{ node, operand astNode }
	var candidates []_EmbeddingCandidate
	collect := func(n astNode) {
		switch n := n.(type) {
		case *astApp:
			if isIntLiteral(n, func(string) bool { return false }) {
				candidates = append(candidates, _EmbeddingCandidate{n, n.args[0]})
			}
		case *astCoerce:
			candidates = append(candidates, _EmbeddingCandidate{n, n.operand})
		}
	}
	for _, d := range work.decls {
		walkAST(d.hyp, collect)
	}
	walkAST(work.body, collect)
	if len(candidates) == 0 {
		return text
	}
	pr := stmtPrinter{replacements: map[astNode]astNode{}}
	accept := func() bool {
		short, err := pr.prop(work)
		if err != nil || !reads(short) {
			return false
		}
		text = short
		return true
	}
	for _, c := range candidates {
		pr.replacements[c.node] = c.operand
	}
	if accept() {
		return text
	}
	clear(pr.replacements)
	for i := len(candidates) - 1; i >= 0; i-- {
		c := candidates[i]
		pr.replacements[c.node] = c.operand
		if accept() {
			continue
		}
		if _, explicit := c.node.(*astApp); explicit {
			pr.replacements[c.node] = &astCoerce{operand: c.operand, pos: c.node.nodePos()}
			if accept() {
				continue
			}
		}
		delete(pr.replacements, c.node)
	}
	return text
}

// instanceTies finds the `⟨V:τ, …⟩` ties a constant carries: a ⟨…⟩
// written against an identifier, whose content opens with a letter
// name and a colon. Spans are byte offsets [start, end), in order.
func instanceTies(text string) [][2]int {
	var spans [][2]int
	for i := 0; i < len(text); {
		open := strings.Index(text[i:], "⟨")
		if open < 0 {
			break
		}
		start := i + open
		i = start + len("⟨")
		before, _ := utf8.DecodeLastRuneInString(text[:start])
		if start == 0 || !(unicode.IsLetter(before) || unicode.IsDigit(before) || before == '_' || before == '\'') {
			continue
		}
		closing := strings.Index(text[i:], "⟩")
		if closing < 0 {
			break
		}
		body := text[i : i+closing]
		if strings.Contains(body, "⟨") || !opensWithLetterBinding(body) {
			continue
		}
		end := i + closing + len("⟩")
		spans = append(spans, [2]int{start, end})
		i = end
	}
	return spans
}

// opensWithLetterBinding reports whether a tie's content opens `V:`.
func opensWithLetterBinding(body string) bool {
	body = strings.TrimSpace(body)
	name := 0
	for name < len(body) {
		r, size := utf8.DecodeRuneInString(body[name:])
		if !(unicode.IsLetter(r) || unicode.IsDigit(r) || r == '_') {
			break
		}
		name += size
	}
	return name > 0 && strings.HasPrefix(strings.TrimSpace(body[name:]), ":")
}

// dropSpans removes the byte spans (in order, non-overlapping) from text.
func dropSpans(text string, spans [][2]int) string {
	var b strings.Builder
	last := 0
	for _, s := range spans {
		b.WriteString(text[last:s[0]])
		last = s[1]
	}
	b.WriteString(text[last:])
	return b.String()
}
