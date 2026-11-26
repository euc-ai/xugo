// Lexer for the text DSL: tokens, the symbol tables, and lex().

package dsl

import (
	"fmt"
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/euc-ai/xugo/utils"
)

// abbrevOpen and abbrevClose delimit an abbreviation, `«Name»`. They
// are the typographic guillemets U+00AB / U+00BB, not the relations
// `≪` / `≫`, which the lexer does not know.
const (
	abbrevOpen  = '«'
	abbrevClose = '»'
)

// abbrevName is the name a `«Name»` token spells: the span between the
// guillemets, trimmed.
func abbrevName(tokenText string) string {
	return strings.TrimSpace(strings.TrimSuffix(strings.TrimPrefix(tokenText, string(abbrevOpen)), string(abbrevClose)))
}

type tokenKind int

const (
	tokEOF tokenKind = iota
	tokIdent
	tokNumLit    // numeric literal: 0, 1, 42 — lowered to a bare bit-tree
	tokTurnstile // ⊢
	tokComma     // ,
	tokColon     // :
	tokDot       // .
	tokLParen    // (
	tokRParen    // )
	tokForall    // ∀
	tokExists    // ∃
	tokUnique    // ∃! (unique existential)
	tokLambda    // λ
	tokHilbert   // ε
	tokNot       // ¬
	tokAnd       // ∧
	tokOr        // ∨
	tokImply     // ⇒
	tokIff       // ⇔
	tokEq        // =
	tokArrow     // →
	tokTop       // ⊤
	tokBot       // ⊥
	// Nat-arith operator tokens. The text form is what appears in
	// astBinOp.op (and in natOperator's keys in arith.go), so ASCII
	// pre-normalized forms (≤, ≥) get their Unicode form stamped at
	// lex time via symbolTokens.
	tokPlus  // +
	tokMinus // -
	tokStar  // *
	// tokSlash is `/` — real division (`real_div`). Real only; see
	// isArithOperator in arith.go for why ℕ has no `/`.
	tokSlash // /
	tokLt    // <
	tokLe    // ≤
	tokGt    // >
	tokGe    // ≥
	tokNe    // ≠
	// tokDivides is U+2223 DIVIDES (`a ∣ b` — nat_divides / int_divides by
	// operand type), deliberately NOT the ASCII pipe U+007C: `|` is the
	// set-builder segment separator, and the three-part `{t | x | φ}`
	// disambiguation relies on tokPipe never being an operator inside φ
	// (where an expression begins it opens the `|x|` notation, which is
	// not an operator either — outfix.go).
	// Same codepoint choice as Lean/Mathlib's `∣`, for the same reason.
	tokDivides // ∣
	// tokEquiv is U+2261 IDENTICAL TO (`x ≡ y (mod m)` — congruence
	// sugar). The mixfix lowers by operand type: at num to ℕ's own
	// three-place `nat_cong(x, y, m)`, at int to ℤ's three-place
	// `int_cong(x, y, m)`. Real
	// congruence keeps the application form (real_mod is not
	// dispatched), and so does a congruence spelled
	// `==(x, y, num_mod(m))`. The `(mod …)` clause is part of the
	// production: a bare `x ≡ y` is a parse error, because the mixfix
	// always takes its modulus. `mod` is NOT a reserved word — parseSpine merely
	// declines to fold a `(mod …)` group into an application, so the
	// clause survives for parseRelational's ≡ arm.
	tokEquiv  // ≡
	tokAmp    // & — real-literal / num→real coercion prefix (`&n`)
	tokDotDot // .. — the numeric segment infix (`m..n`)
	// Polymorphic type-substitution annotation brackets. `Name⟨A:T⟩` after
	// an identifier binds the const's type-var A to T. The formatter emits
	// this suffix (see ext/formatConstTypeAnnotation) to disambiguate
	// polymorphic-const conflicts; the parser accepts it so
	// print→parse round-trips.
	tokLangle // ⟨
	tokRangle // ⟩
	// Set-theory surface. Infix binary ops span three precedence levels:
	// ∈/∉/⊆/⊊ are relational (non-assoc, alongside <, ≤); ∪/∖ are set-
	// additive (left-assoc, tighter than relational); ∩ is set-
	// multiplicative (left-assoc, tighter than ∪). ∅/𝕌 are polymorphic
	// nullary atoms; ⋃/⋂ are unary big-op prefixes (`⋃(s)`). `{`/`}`/`|`
	// bracket set enumerations (`{a,b,c}` — insert-chain over empty_set) and
	// set-builder (`{f(x) | φ(x)}` — set_comprehension/comprehension_spec). Each token has a
	// matching format-side symbol mapping in ext/format.go so the printer
	// round-trips exactly.
	tokIn       // ∈
	tokNotIn    // ∉ — `x ∉ s` reads ¬(x ∈ s), as `≠` reads ¬(a = b)
	tokSubset   // ⊆
	tokPSubset  // ⊊
	tokUnion    // ∪
	tokInter    // ∩
	tokSetminus // ∖
	tokEmpty    // ∅
	tokUniv     // 𝕌
	tokBigUnion // ⋃
	tokBigInter // ⋂
	tokLBrace   // {
	tokRBrace   // }
	tokPipe     // |
	// tokCompose is U+2218 RING OPERATOR — function composition.
	// Infix, right-associative, one level tighter than `*`. Its operands
	// are functions, on which no arithmetic operator has an instance, so
	// the level resolves no genuine ambiguity.
	tokCompose // ∘
	// Outfix notation delimiters (outfix.go): `‖` closes itself, `⟪`
	// pairs with `⟫`, `⁅` (U+2045 LEFT SQUARE BRACKET WITH QUILL) with
	// `⁆` (a quotient's class, ⁅x⁆), and `⟦` (U+27E6 MATHEMATICAL LEFT
	// WHITE SQUARE BRACKET) and `⟬` (U+27EC MATHEMATICAL LEFT WHITE
	// TORTOISE SHELL BRACKET) each close with `⟧` or `⟭`: the intervals
	// ⟦a, b⟧, ⟬a, b⟭, ⟦a, b⟭ and ⟬a, b⟧. The lexer knows only the
	// alphabet; which constant a pair spells is the scope's
	// (ParseScope.Syntax).
	tokNormBar   // ‖
	tokLDAngle   // ⟪
	tokRDAngle   // ⟫
	tokLQuill    // ⁅
	tokRQuill    // ⁆
	tokLDBracket // ⟦
	tokRDBracket // ⟧
	tokLShell    // ⟬
	tokRShell    // ⟭
	// Operator and big-operator symbols a chapter's constant declares
	// (operator.go, bigop.go): the scalar action's infix `•`, the
	// relation `⟶` (a limit's "tends to", at the comparison level, with
	// an optional `(at c)` point clause the parser reads like the
	// congruence's `(mod m)`), and the summation and product binders
	// `Σ`, `Π`. The lexer knows only the alphabet; which constant a
	// symbol spells is the scope's.
	tokSmul    // •
	tokTendsTo // ⟶
	tokBigSum  // Σ
	tokBigProd // Π
	// The power `x ^ n` a chapter's constant declares (operator.go): it
	// binds tighter than the prefix `-` and `¬`, looser than `&` and
	// application, and associates to the right (parser.go's parsePower).
	tokCaret // ^
	// An abbreviation `«Name»` (abbreviation.go): a name a statement's
	// table gives a term, spelled between guillemets in the statement
	// and in the texts of its proof. The token's text is the name,
	// verbatim; the lexer knows no table, the parse scope's expansion
	// does.
	tokAbbrev // «…»
)

type token struct {
	kind tokenKind
	text string
	pos  int // byte offset in normalized input
}

// asciiTokens maps single-rune ASCII punctuation to token kinds.
// `-` is safe to single-char tokenize because the ASCII multi-char
// forms involving `-` (`->`) are eliminated by NormalizeTextSymbols
// before lexing.
// multiCharIdents lists ASCII symbolic const names whose first char
// would otherwise be lexed as a single-char operator token. Lexed as
// tokIdent so the parser treats them as ordinary function names; the
// scope resolves them via ConstMetas (or Consts) at type-instantiation
// time. New entries land here when the corpus surfaces another
// symbolic const whose name would otherwise shadow a token.
var multiCharIdents = map[string]bool{
	"==": true, // modular equality (== A b c d)
	"<<": true, // well-founded relation (used by superadmissible, …)
}

// symbolicIdents lists single-char symbolic const names that aren't
// otherwise reserved tokens and should tokenize as identifiers so the
// parser treats them as ordinary function heads (`$(x, i)` becomes a
// two-arg application of the const named `$`). The name resolves
// through the regular scope-const path at build time. Single-char
// operators that ARE reserved tokens (`+`, `*`, `<`, `>`, `&`, `=`,
// `-`) already have dedicated tokens and bare-operator value-position
// support in parseAtom; entries here are ONLY the symbolic const names
// that have no other role. `$` is the cart-access combinator
// (`$(v, i)` reads the i-th component of a `cart(A, N)` vector); no
// other precedent uses it as a token, so lexing as ident is safe.
var symbolicIdents = map[rune]bool{
	'$': true,
}

var asciiTokens = map[rune]tokenKind{
	',': tokComma,
	':': tokColon,
	'.': tokDot,
	'(': tokLParen,
	')': tokRParen,
	'=': tokEq,
	'+': tokPlus,
	'-': tokMinus,
	'*': tokStar,
	'/': tokSlash,
	'<': tokLt,
	'>': tokGt,
	'&': tokAmp,
	'{': tokLBrace,
	'}': tokRBrace,
	'|': tokPipe,
	'^': tokCaret,
}

// symbolTokens maps Unicode logical symbols to token kinds.
var symbolTokens = map[string]tokenKind{
	utils.TurnstileStr: tokTurnstile,
	utils.ForAllStr:    tokForall,
	utils.ExistsStr:    tokExists,
	utils.LambdaStr:    tokLambda,
	utils.HilbertStr:   tokHilbert,
	utils.NegStr:       tokNot,
	utils.AndStr:       tokAnd,
	utils.OrStr:        tokOr,
	utils.ImplyStr:     tokImply,
	utils.IffStr:       tokIff,
	utils.FunStr:       tokArrow,
	utils.TrueStr:      tokTop,
	utils.FalseStr:     tokBot,
	"≤":                tokLe,
	"≥":                tokGe,
	"∣":                tokDivides,
	"≡":                tokEquiv,
	utils.NeqStr:       tokNe,
	"⟨":                tokLangle,
	"⟩":                tokRangle,
	// Set-theory surface — see the tok* declarations above.
	"∈": tokIn,
	"∉": tokNotIn,
	"⊆": tokSubset,
	"⊊": tokPSubset,
	"∪": tokUnion,
	"∩": tokInter,
	"∖": tokSetminus,
	"∅": tokEmpty,
	"𝕌": tokUniv,
	"⋃": tokBigUnion,
	"⋂": tokBigInter,
	// Function composition — see tokCompose above.
	"∘": tokCompose,
	// Outfix notation delimiters — see outfix.go.
	"‖": tokNormBar,
	"⟪": tokLDAngle,
	"⟫": tokRDAngle,
	"⁅": tokLQuill,
	"⁆": tokRQuill,
	"⟦": tokLDBracket,
	"⟧": tokRDBracket,
	"⟬": tokLShell,
	"⟭": tokRShell,
	// Declared operators and big operators — see operator.go, bigop.go.
	"•": tokSmul,
	"⟶": tokTendsTo,
	"Σ": tokBigSum,
	"Π": tokBigProd,
}

// intervalBracketHint is what the unknown-character refusal adds for a
// textbook interval bracket — `[`, `]`, `⟮`, `⟯` — which the DSL does
// not lex: it names the four interval spellings. Empty for any other
// character.
func intervalBracketHint(r rune) string {
	switch r {
	case '[', ']', '⟮', '⟯':
		return " — the intervals are written ⟦a, b⟧, ⟬a, b⟭, ⟦a, b⟭ and ⟬a, b⟧"
	}
	return ""
}

func lex(input string) ([]token, *InputDiagnostic) {
	var tokens []token
	i := 0

	for i < len(input) {
		// Skip whitespace.
		if input[i] == ' ' || input[i] == '\t' || input[i] == '\n' || input[i] == '\r' {
			i++
			continue
		}

		pos := i
		r, size := utf8.DecodeRuneInString(input[i:])

		// Multi-char ASCII const-name tokens. There is a small
		// set of symbolic const names that share leading chars with
		// single-char tokens (`==` modular eq vs `=` relational; `<<`
		// well-founded relation vs `<` lt). Check for these BEFORE
		// the single-char ASCII fall-through so the multi-char form
		// wins.
		if i+1 < len(input) {
			pair := input[i : i+2]
			if _, ok := multiCharIdents[pair]; ok {
				tokens = append(tokens, token{tokIdent, pair, pos})
				i += 2
				continue
			}
			// The `..` numeric-segment infix. Must lex BEFORE the
			// single-char `.` (which becomes tokDot — the ∀x. body
			// separator); otherwise `m..n` tokenizes as `m`, dot, dot, `n`
			// and the parser sees a stray dot in expression position.
			if pair == ".." {
				tokens = append(tokens, token{tokDotDot, "..", pos})
				i += 2
				continue
			}
		}

		// Single-char ASCII tokens.
		if kind, ok := asciiTokens[r]; ok {
			tokens = append(tokens, token{kind, string(r), pos})
			i += size
			continue
		}

		// An abbreviation `«Name»`: the name is everything up to the
		// closing guillemet, verbatim — a subscript, a space, a dotted
		// name are the author's. The closing guillemet on its own line
		// or missing is the one lexical error of the form.
		if r == abbrevOpen {
			end := strings.IndexRune(input[i+size:], abbrevClose)
			if end < 0 || strings.ContainsRune(input[i+size:i+size+end], '\n') {
				return nil, &InputDiagnostic{
					Position:   pos,
					Length:     size,
					Code:       CodeParseError,
					Message:    "unterminated abbreviation: « without a closing » on the same line",
					Suggestion: "write the abbreviation as «Name»",
				}
			}
			whole := input[i : i+size+end+utf8.RuneLen(abbrevClose)]
			if abbrevName(whole) == "" {
				return nil, &InputDiagnostic{
					Position:   pos,
					Length:     len(whole),
					Code:       CodeParseError,
					Message:    "empty abbreviation «»",
					Suggestion: "write the abbreviation as «Name»",
				}
			}
			// The token's text is the source span, guillemets included,
			// as every token's is — the parser reads the name off it.
			tokens = append(tokens, token{tokAbbrev, whole, pos})
			i += len(whole)
			continue
		}

		// Unicode logical symbols.
		sym := input[i : i+size]
		if kind, ok := symbolTokens[sym]; ok && !isHilbertAsIdent(sym, input[i+size:]) {
			// Special case: ∃! (unique existential) is one quantifier token.
			// normalize.go passes the `!` through unmangled when it follows ∃
			// (its bare-`!` → ¬ rule is suppressed there), so this fires.
			if sym == utils.ExistsStr && i+size < len(input) && input[i+size] == '!' {
				tokens = append(tokens, token{tokUnique, utils.UniqueStr, pos})
				i += size + 1
				continue
			}
			tokens = append(tokens, token{kind, sym, pos})
			i += size
			continue
		}

		// Numeric literal: decimal digits, no sign, no fractional part.
		// Captured before the identifier path so a bare `42` doesn't
		// fall through to isIdentStart (which doesn't allow leading
		// digits anyway, but the explicit branch keeps the diagnostic
		// clean if we ever extend identifier syntax). Lowered at
		// buildTerm time to a bare bit-tree over _0.
		if r >= '0' && r <= '9' {
			j := i + size
			for j < len(input) {
				r2, sz2 := utf8.DecodeRuneInString(input[j:])
				if r2 >= '0' && r2 <= '9' {
					j += sz2
				} else {
					break
				}
			}
			tokens = append(tokens, token{tokNumLit, input[i:j], pos})
			i = j
			continue
		}

		// Symbolic single-char idents (e.g. `$`). Handled BEFORE the
		// generic isIdentStart path because they aren't letters and
		// wouldn't be picked up there. Emitted as a one-rune tokIdent
		// so the parser's function-head resolution treats them like
		// any named const.
		if symbolicIdents[r] {
			tokens = append(tokens, token{tokIdent, string(r), pos})
			i += size
			continue
		}

		// Identifiers: letters, digits, _, '
		if isIdentStart(r) {
			j := i + size
			for j < len(input) {
				r2, sz2 := utf8.DecodeRuneInString(input[j:])
				if isIdentChar(r2) {
					j += sz2
				} else {
					break
				}
			}
			text := input[i:j]
			// Option D type-variable form: the literal prefix `var:`
			// followed by an identifier is lexed as a single ident
			// (so `var:Repty` is one token, not three). `resolveType`
			// then strips the prefix and produces a `VarType`. The
			// special-case is keyed off the literal text `"var"` —
			// other identifiers ending at a `:` (e.g. `x : bool` type
			// ascriptions) continue to lex as separate tokens.
			if text == "var" && j < len(input) && input[j] == ':' {
				k := j + 1
				// Allow a single leading `?` after `var:` as a Skolem-
				// type-var marker (prop.Normalize emits names like
				// `?94099` for fresh type variables). After the leading
				// `?`, identifier chars resume as usual. `?` is illegal
				// elsewhere in identifier syntax, so this stays a local
				// concession scoped to `var:`-prefixed type-var names.
				if k < len(input) && input[k] == '?' {
					k++
				}
				for k < len(input) {
					r2, sz2 := utf8.DecodeRuneInString(input[k:])
					if isIdentChar(r2) {
						k += sz2
					} else {
						break
					}
				}
				if k > j+1 {
					text = input[i:k]
					tokens = append(tokens, token{tokIdent, text, pos})
					i = k
					continue
				}
			}
			tokens = append(tokens, token{tokIdent, text, pos})
			i = j
			continue
		}

		// Bare type-variable shorthand: `?<ident-chars>` outside `var:`.
		// `prop.Normalize` emits fresh type-variable names like `?94099`,
		// and the printer surfaces them verbatim — so an agent reading a
		// goal copy-pastes `?94099` directly. Lexed as a synthesized
		// `var:?94099` ident so the existing `var:`-prefix path in
		// `resolveType` (infer.go) produces a `VarType` without further
		// changes. Bare `?` (no ident chars) is still an unknown char.
		if r == '?' {
			j := i + size
			for j < len(input) {
				r2, sz2 := utf8.DecodeRuneInString(input[j:])
				if isIdentChar(r2) {
					j += sz2
				} else {
					break
				}
			}
			if j > i+size {
				tokens = append(tokens, token{tokIdent, "var:" + input[i:j], pos})
				i = j
				continue
			}
		}

		// Unknown character.
		return nil, &InputDiagnostic{
			Position:   pos,
			Length:     size,
			Code:       CodeUnknownSymbol,
			Message:    fmt.Sprintf("unexpected character %q%s", string(r), intervalBracketHint(r)),
			Suggestion: "remove this character or replace with a valid symbol",
		}
	}

	tokens = append(tokens, token{tokEOF, "", len(input)})
	return tokens, nil
}

func isIdentStart(r rune) bool {
	return unicode.IsLetter(r) || r == '_'
}

// isHilbertAsIdent reports whether an `ε` at this position is the
// VARIABLE ε rather than the Hilbert binder: the binder is `ε` followed
// directly by its binder name (`εy:real. …`, the printers' spelling), so
// an `ε` that is not followed by a letter — `∀ε:real.`, `&0 < ε`,
// `… < ε)`, the Skolem `ε₀` — is an ordinary identifier, and the ε-δ
// vocabulary of analysis is written with the letters it uses.
func isHilbertAsIdent(sym, rest string) bool {
	if sym != utils.HilbertStr {
		return false
	}
	r, _ := utf8.DecodeRuneInString(rest)
	return !unicode.IsLetter(r)
}

func isIdentChar(r rune) bool {
	return unicode.IsLetter(r) || unicode.IsDigit(r) || r == '_' || r == '\'' || r == '%'
}

// ---------------------------------------------------------------------------
// AST
// ---------------------------------------------------------------------------
