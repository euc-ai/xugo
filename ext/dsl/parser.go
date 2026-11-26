// Recursive-descent parser for the text DSL: the operator-precedence
// grammar that turns a token stream into the AST.

package dsl

import (
	"fmt"
	"math/big"
	"strings"

	"github.com/euc-ai/xugo/utils"
)

type parser struct {
	tokens   []token
	pos      int
	warnings []InputDiagnostic
	// typeNames is every named type node the parse built, in source
	// order — the input of the type-vocabulary check (typenames.go),
	// which runs after the parse so one pass sees every type position
	// (binders, the declaration prefix, ⟨⟩ ties, set-builder binders).
	typeNames []*astTypeNamed
}

func (p *parser) warn(pos, length int, code, message, suggestion string) {
	p.warnings = append(p.warnings, InputDiagnostic{
		Position:   pos,
		Length:     length,
		Code:       code,
		Message:    message,
		Suggestion: suggestion,
	})
}

func (p *parser) peek() token {
	if p.pos >= len(p.tokens) {
		return token{tokEOF, "", -1}
	}
	return p.tokens[p.pos]
}

func (p *parser) advance() token {
	t := p.peek()
	if t.kind != tokEOF {
		p.pos++
	}
	return t
}

func (p *parser) expect(kind tokenKind) (token, *InputDiagnostic) {
	t := p.peek()
	if t.kind != kind {
		return t, &InputDiagnostic{
			Position:   t.pos,
			Length:     len(t.text),
			Code:       CodeParseError,
			Message:    fmt.Sprintf("expected %s, got %q", tokenName(kind), t.text),
			Suggestion: fmt.Sprintf("add %s here", tokenName(kind)),
		}
	}
	p.advance()
	return t, nil
}

func tokenName(k tokenKind) string {
	switch k {
	case tokEOF:
		return "end of input"
	case tokIdent:
		return "identifier"
	case tokTurnstile:
		return "⊢"
	case tokComma:
		return ","
	case tokColon:
		return ":"
	case tokDot:
		return "."
	case tokLParen:
		return "("
	case tokRParen:
		return ")"
	case tokForall:
		return "∀"
	case tokExists:
		return "∃"
	case tokUnique:
		return "∃!"
	case tokLambda:
		return "λ"
	case tokHilbert:
		return "ε"
	case tokNot:
		return "¬"
	case tokAnd:
		return "∧"
	case tokOr:
		return "∨"
	case tokImply:
		return "⇒"
	case tokIff:
		return "⇔"
	case tokEq:
		return "="
	case tokArrow:
		return "→"
	case tokTop:
		return "⊤"
	case tokBot:
		return "⊥"
	case tokAmp:
		return "&"
	case tokNormBar:
		return "‖"
	case tokLDAngle:
		return "⟪"
	case tokRDAngle:
		return "⟫"
	case tokLQuill:
		return "⁅"
	case tokRQuill:
		return "⁆"
	case tokLDBracket:
		return "⟦"
	case tokRDBracket:
		return "⟧"
	case tokLShell:
		return "⟬"
	case tokRShell:
		return "⟭"
	case tokLangle:
		return "⟨"
	case tokRangle:
		return "⟩"
	case tokDivides:
		return "∣"
	case tokIn:
		return "∈"
	case tokNotIn:
		return "∉"
	case tokSubset:
		return "⊆"
	case tokPSubset:
		return "⊊"
	case tokUnion:
		return "∪"
	case tokInter:
		return "∩"
	case tokSetminus:
		return "∖"
	case tokEmpty:
		return "∅"
	case tokUniv:
		return "𝕌"
	case tokBigUnion:
		return "⋃"
	case tokBigInter:
		return "⋂"
	case tokLBrace:
		return "{"
	case tokRBrace:
		return "}"
	case tokPipe:
		return "|"
	case tokCompose:
		return "∘"
	case tokSmul:
		return "•"
	case tokCaret:
		return "^"
	case tokTendsTo:
		return "⟶"
	case tokBigSum:
		return "Σ"
	case tokBigProd:
		return "Π"
	}
	return "?"
}

// parseProp parses a full proposition: [decls ⊢] expr
func (p *parser) parseProp() (*astProp, *InputDiagnostic) {
	pos := p.peek().pos

	// Look ahead for turnstile to determine if we have declarations.
	if hasTurnstile(p.tokens, p.pos) {
		decls, err := p.parseDecls()
		if err != nil {
			return nil, err
		}
		_, err = p.expect(tokTurnstile)
		if err != nil {
			return nil, err
		}
		body, err := p.parseExpr()
		if err != nil {
			return nil, err
		}
		return &astProp{decls: decls, body: body, pos: pos, hasTurn: true}, nil
	}

	// No turnstile: just an expression.
	body, err := p.parseExpr()
	if err != nil {
		return nil, err
	}
	return &astProp{body: body, pos: pos}, nil
}

// hasTurnstile scans tokens for a top-level ⊢ (not inside parens).
func hasTurnstile(tokens []token, start int) bool {
	depth := 0
	for i := start; i < len(tokens); i++ {
		switch tokens[i].kind {
		case tokLParen:
			depth++
		case tokRParen:
			depth--
		case tokTurnstile:
			if depth == 0 {
				return true
			}
		case tokEOF:
			return false
		}
	}
	return false
}

// parseDecls parses comma-separated declarations before ⊢.
// Each declaration is either "name : type" or a hypothesis expression.
func (p *parser) parseDecls() ([]astDecl, *InputDiagnostic) {
	var decls []astDecl

	for {
		decl, err := p.parseOneDecl()
		if err != nil {
			return nil, err
		}
		decls = append(decls, *decl)

		if p.peek().kind == tokComma {
			p.advance()
			continue
		}
		break
	}
	return decls, nil
}

// parseOneDecl tries "NAME : type" first, falls back to hypothesis expression.
func (p *parser) parseOneDecl() (*astDecl, *InputDiagnostic) {
	pos := p.peek().pos

	// Try "NAME : type" — look ahead for colon after identifier.
	if p.peek().kind == tokIdent {
		save := p.pos
		name := p.advance()
		if p.peek().kind == tokColon {
			p.advance() // consume ':'
			ty, err := p.parseType()
			if err != nil {
				return nil, err
			}
			return &astDecl{name: name.text, typeStr: ty, pos: pos}, nil
		}
		// Not a type declaration — backtrack.
		p.pos = save
	}

	// Parse as hypothesis expression.
	expr, err := p.parseExpr()
	if err != nil {
		return nil, err
	}
	return &astDecl{hyp: expr, pos: pos}, nil
}

// normalizeTypeVarName canonicalizes the spelling of a type-variable
// name in type position: `var:X` with X a single uppercase ASCII
// letter normalizes to the bare `X` — the canonical DSL spelling
// (both parse to the same VarType via resolveType; the statement
// formatter therefore prints the bare form). Everything else is
// returned verbatim: multi-letter forms (`var:Repty`) keep the
// prefix because a bare multi-letter name means a nullary composite
// type, and Skolem type-var idents (`var:?94099`, synthesized by the
// lexer for bare `?94099`) keep their spelling because `?` names are
// never single uppercase letters.
func normalizeTypeVarName(name string) string {
	if rest, ok := strings.CutPrefix(name, "var:"); ok {
		if len(rest) == 1 && rest[0] >= 'A' && rest[0] <= 'Z' {
			return rest
		}
	}
	return name
}

// parseType parses a type expression.
func (p *parser) parseType() (astType, *InputDiagnostic) {
	left, err := p.parseTypeAtom()
	if err != nil {
		return nil, err
	}

	// Check for → (function type, right-associative).
	if p.peek().kind == tokArrow {
		p.advance()
		right, err := p.parseType()
		if err != nil {
			return nil, err
		}
		return &astTypeFun{domain: left, codomain: right, pos: left.typePos(), end: right.typeEnd()}, nil
	}

	return left, nil
}

func (p *parser) parseTypeAtom() (astType, *InputDiagnostic) {
	tok := p.peek()

	if tok.kind == tokLParen {
		open := tok
		p.advance()
		// Could be tuple type "(A, B) → C" or parenthesized type.
		first, err := p.parseType()
		if err != nil {
			return nil, err
		}

		if p.peek().kind == tokComma {
			// Tuple type — collect all elements.
			types := []astType{first}
			for p.peek().kind == tokComma {
				p.advance()
				t, err := p.parseType()
				if err != nil {
					return nil, err
				}
				types = append(types, t)
			}
			_, err = p.expect(tokRParen)
			if err != nil {
				return nil, err
			}
			// Must be followed by → for multi-arg function type.
			if p.peek().kind != tokArrow {
				return nil, &InputDiagnostic{
					Position:   p.peek().pos,
					Code:       CodeParseError,
					Message:    "multi-element tuple type must be followed by →",
					Suggestion: "write (A, B) → C for a two-argument function",
				}
			}
			p.advance()
			codomain, err := p.parseType()
			if err != nil {
				return nil, err
			}
			// Build curried function type: (A, B) → C becomes A → B → C.
			// The synthesized nodes span the whole sugar (tuple) — no
			// subterm owns a contiguous text of its own.
			result := codomain
			for i := len(types) - 1; i >= 0; i-- {
				result = &astTypeFun{domain: types[i], codomain: result, pos: open.pos, end: codomain.typeEnd(), tuple: true}
			}
			return result, nil
		}

		closeTok, err := p.expect(tokRParen)
		if err != nil {
			return nil, err
		}
		// A parenthesized type spans its parens: the rewrite that
		// respells `(A → bool)` as `set(A)` replaces the parens too.
		first.setSpan(open.pos, closeTok.pos+len(closeTok.text))
		return first, nil
	}

	if tok.kind == tokIdent {
		p.advance()
		// Optional type-argument list `name(t1, t2, ...)` for n-ary
		// composite types (`list(A)`, `prod(A, B)`, …). Each arg is
		// itself a full type expression. The parens are required —
		// applying a 0-ary type is illegal (it's just the bare name).
		// The head name is a composite-type name position, never a
		// type variable, so it is stored verbatim (no
		// normalizeTypeVarName).
		if p.peek().kind == tokLParen {
			p.advance() // consume (
			var args []astType
			for {
				arg, err := p.parseType()
				if err != nil {
					return nil, err
				}
				args = append(args, arg)
				if p.peek().kind == tokComma {
					p.advance()
					continue
				}
				break
			}
			if p.peek().kind != tokRParen {
				return nil, &InputDiagnostic{
					Position: p.peek().pos,
					Length:   len(p.peek().text),
					Code:     CodeParseError,
					Message:  fmt.Sprintf("expected ')', got %q", p.peek().text),
				}
			}
			closeTok := p.peek()
			p.advance() // consume )
			node := &astTypeNamed{name: tok.text, args: args, pos: tok.pos, end: closeTok.pos + len(closeTok.text)}
			p.typeNames = append(p.typeNames, node)
			return node, nil
		}
		node := &astTypeNamed{name: normalizeTypeVarName(tok.text), pos: tok.pos, end: tok.pos + len(tok.text)}
		p.typeNames = append(p.typeNames, node)
		return node, nil
	}

	// The unit type is named `1` — a digit-only name that
	// the lexer tokenizes as tokNumLit, not tokIdent. Accept it as a
	// 0-ary type name here so emit's text form for unit-typed
	// propositions (`∀f:A → 1.…` etc.) round-trips. Other digit-only
	// names follow the same rule; alphanumeric-with-leading-digit
	// names are still illegal (lexer would split them).
	if tok.kind == tokNumLit {
		p.advance()
		node := &astTypeNamed{name: tok.text, pos: tok.pos, end: tok.pos + len(tok.text)}
		p.typeNames = append(p.typeNames, node)
		return node, nil
	}

	return nil, &InputDiagnostic{
		Position:   tok.pos,
		Length:     len(tok.text),
		Code:       CodeParseError,
		Message:    fmt.Sprintf("expected type, got %q", tok.text),
		Suggestion: "use a type name like bool, A, B, or nat",
	}
}

// parseTypeAnnotation consumes a `⟨V1:T1, V2:T2, ...⟩` polymorphic
// type-substitution suffix. The opening `⟨` must be the current token.
// Both `:` and `=` are accepted as the binding separator (the formatter
// emits `:`; earlier internal comments and JSON-shaped `A=T` sources use
// `=`). Each `Ti` is a full type expression (accepts `var:X`, `A → B`,
// `list(A)`, `?<skolem>` — anything `parseType` accepts).
func (p *parser) parseTypeAnnotation() ([]typeAnnotBinding, *InputDiagnostic) {
	if _, err := p.expect(tokLangle); err != nil {
		return nil, err
	}
	var bindings []typeAnnotBinding
	for {
		b, err := p.parseTypeBinding()
		if err != nil {
			return nil, err
		}
		bindings = append(bindings, b)
		if p.peek().kind == tokComma {
			p.advance()
			continue
		}
		break
	}
	if _, err := p.expect(tokRangle); err != nil {
		return nil, err
	}
	return bindings, nil
}

// parseTypeBinding consumes one `V:T` (or `V=T`) of a `⟨…⟩` suffix.
func (p *parser) parseTypeBinding() (typeAnnotBinding, *InputDiagnostic) {
	nameTok, err := p.expect(tokIdent)
	if err != nil {
		return typeAnnotBinding{}, err
	}
	// Skolem type-var names: prop.Normalize emits fresh type vars
	// named `?N`, and the printer's annotation surfaces them
	// verbatim (`has_size⟨?83621:var:A⟩`). The lexer's bare-`?`
	// concession tokenizes `?83621` as the synthesized ident
	// `var:?83621` (so it doubles as a type expression elsewhere);
	// in the annotation NAME position we want the raw type-var
	// name, so strip the synthesized prefix back off. A literal
	// `var:X` spelling in name position normalizes the same way.
	varName := strings.TrimPrefix(nameTok.text, "var:")
	sep := p.peek()
	if sep.kind != tokColon && sep.kind != tokEq {
		return typeAnnotBinding{}, &InputDiagnostic{
			Position:   sep.pos,
			Length:     len(sep.text),
			Code:       CodeParseError,
			Message:    fmt.Sprintf("expected ':' or '=' in type annotation, got %q", sep.text),
			Suggestion: "write ⟨A:T⟩ to bind type variable A to type T",
		}
	}
	p.advance()
	ty, err := p.parseType()
	if err != nil {
		return typeAnnotBinding{}, err
	}
	return typeAnnotBinding{varName: varName, ty: ty, pos: nameTok.pos}, nil
}

// ---------------------------------------------------------------------------
// Expression parsing (precedence climbing)
// ---------------------------------------------------------------------------

func (p *parser) parseExpr() (astNode, *InputDiagnostic) {
	return p.parseIff()
}

func (p *parser) parseQuant() (astNode, *InputDiagnostic) {
	tok := p.advance() // ∀, ∃, ∃!, or ε
	qStr := tok.text

	name, err := p.expect(tokIdent)
	if err != nil {
		return nil, err
	}

	// Grouped multi-binder form: `∀m n:num. body` / `∃x y. body`
	// desugars to nested single-binder quantifiers sharing one type
	// annotation (`∀m:num.∀n:num. body`). ∀/∃/∃! only — ε picks a
	// single witness, so a second binder name there is an error, not
	// a group.
	names := []token{name}
	for p.peek().kind == tokIdent {
		extra := p.advance()
		if qStr == utils.HilbertStr {
			return nil, &InputDiagnostic{
				Position:   extra.pos,
				Length:     len(extra.text),
				Code:       CodeParseError,
				Message:    fmt.Sprintf("ε binds a single variable; unexpected second binder %q", extra.text),
				Suggestion: "nest explicitly: εx. … (εy. …) …",
			}
		}
		names = append(names, extra)
	}

	// Type annotation is optional, mirroring the single-binder λ form
	// (see parseAbs). When omitted (`∀x. …`, `∃x. …`), the binder type
	// is inferred at build time from how the bound variable is used in
	// the body — same untypedAbsVars channel buildAbs uses. This lets
	// agents express ∃ over a goal-local type-variable they have no
	// concrete spelling for (e.g. `?71143`), as long as the body has
	// at least one use site that pins the type. On a grouped form the
	// annotation types every name in the group.
	var ty astType
	if p.peek().kind == tokColon {
		p.advance()
		ty, err = p.parseType()
		if err != nil {
			return nil, err
		}
	}

	_, err = p.expect(tokDot)
	if err != nil {
		return nil, err
	}

	// Wide binding: the body extends across binary
	// operators, so ∀x:A. P(x) ⇒ Q(x) parses as ∀x:A. (P(x) ⇒ Q(x)) and
	// the bound x is in scope for both sides. Use parens to narrow:
	// (∀x:A. P(x)) ⇒ Q.
	body, err := p.parseExpr()
	if err != nil {
		return nil, err
	}

	for i := len(names) - 1; i >= 0; i-- {
		body = &astQuantNode{
			quantifier: qStr,
			varName:    names[i].text,
			varType:    ty, // nil → infer from body usage at build time
			body:       body,
			pos:        names[i].pos,
		}
	}
	return body, nil
}

func (p *parser) parseIff() (astNode, *InputDiagnostic) {
	left, err := p.parseImpl()
	if err != nil {
		return nil, err
	}

	if p.peek().kind == tokIff {
		op := p.advance()
		right, err := p.parseImpl()
		if err != nil {
			return nil, err
		}
		left = &astBinOp{op: utils.IffStr, left: left, right: right, pos: op.pos}
		// Warn if another ⇔ follows (chained without parens).
		if p.peek().kind == tokIff {
			p.warn(p.peek().pos, len(utils.IffStr), "ambiguous_associativity",
				"chained ⇔ parsed left-associative; add parens if needed",
				"")
			for p.peek().kind == tokIff {
				op = p.advance()
				right, err = p.parseImpl()
				if err != nil {
					return nil, err
				}
				left = &astBinOp{op: utils.IffStr, left: left, right: right, pos: op.pos}
			}
		}
	}
	return left, nil
}

func (p *parser) parseImpl() (astNode, *InputDiagnostic) {
	left, err := p.parseDisj()
	if err != nil {
		return nil, err
	}

	// Right-associative: p ⇒ q ⇒ r = p ⇒ (q ⇒ r)
	// Also accept → (type arrow) as ⇒ in expression context — common mistake.
	isImply := p.peek().kind == tokImply
	isArrowAsImply := !isImply && p.peek().kind == tokArrow
	if isImply || isArrowAsImply {
		op := p.advance()
		if isArrowAsImply {
			p.warn(op.pos, len(op.text), "auto_corrected",
				"→ is the type arrow; interpreted as ⇒ (implication) here",
				"write => for implication")
		}
		right, err := p.parseImpl()
		if err != nil {
			return nil, err
		}
		// Warn if the right side is also an implication (chained without explicit parens).
		if bn, ok := right.(*astBinOp); ok && bn.op == utils.ImplyStr && !bn.parens {
			p.warn(op.pos, len(utils.ImplyStr), "ambiguous_associativity",
				"chained ⇒ parsed right-associative; add parens if left-associative intended",
				"")
		}
		return &astBinOp{op: utils.ImplyStr, left: left, right: right, pos: op.pos}, nil
	}
	return left, nil
}

func (p *parser) parseDisj() (astNode, *InputDiagnostic) {
	left, err := p.parseConj()
	if err != nil {
		return nil, err
	}

	for p.peek().kind == tokOr {
		op := p.advance()
		right, err := p.parseConj()
		if err != nil {
			return nil, err
		}
		// Warn if ∧ appears inside ∨ without explicit parentheses.
		if bn, ok := right.(*astBinOp); ok && bn.op == utils.AndStr && !bn.parens {
			p.warn(bn.pos, len(utils.AndStr), "ambiguous_precedence",
				"∧ binds tighter than ∨; add parens to clarify",
				"")
		}
		left = &astBinOp{op: utils.OrStr, left: left, right: right, pos: op.pos}
	}
	return left, nil
}

func (p *parser) parseConj() (astNode, *InputDiagnostic) {
	left, err := p.parseRelational()
	if err != nil {
		return nil, err
	}

	for p.peek().kind == tokAnd {
		op := p.advance()
		right, err := p.parseRelational()
		if err != nil {
			return nil, err
		}
		left = &astBinOp{op: utils.AndStr, left: left, right: right, pos: op.pos}
	}
	return left, nil
}

// parseRelational handles equality, inequality, and the nat comparison
// operators at one non-associative level. The arith operators (+, -, *)
// live below this in parseAdditive / parseMultiplicative.
//
// Precedence (low to high): … < ∧ < relational < segment (`..`) <
// additive < multiplicative < unary. So `a + b < c * d` parses as
// `(a + b) < (c * d)`, and `m+1..n` parses as `(m+1)..n` (additive
// binds tighter than the segment infix).
//
// Chained comparison `a < b < c` is not supported — only one operator
// is matched. A second comparison surfaces as "unexpected token" at
// the parser level, as a chained `=` does.
func (p *parser) parseRelational() (astNode, *InputDiagnostic) {
	left, err := p.parseSegment()
	if err != nil {
		return nil, err
	}

	// Congruence mixfix: `x ≡ y (mod m)`. The `(mod …)` clause is part
	// of the production — `==` always takes its modulus relation, so a
	// bare `x ≡ y` has nothing to lower to and errors here. The right
	// operand's parseSegment cannot have swallowed the clause:
	// parseSpine declines to fold a `(`-group whose first token is the
	// identifier `mod` (see the guard in its tokLParen arm).
	if p.peek().kind == tokEquiv {
		tok := p.advance()
		right, err := p.parseSegment()
		if err != nil {
			return nil, err
		}
		lp := p.peek()
		if lp.kind != tokLParen || !p.peekIsModClause() {
			return nil, &InputDiagnostic{
				Position:   lp.pos,
				Length:     len(lp.text),
				Code:       CodeParseError,
				Message:    "≡ requires a modulus clause",
				Suggestion: "write `x ≡ y (mod m)`; for a general relation use the application form `==(x, y, rel)`",
			}
		}
		p.advance() // (
		p.advance() // mod
		modulus, err := p.parseSegment()
		if err != nil {
			return nil, err
		}
		if _, rerr := p.expect(tokRParen); rerr != nil {
			return nil, rerr
		}
		return &astCong{left: left, right: right, modulus: modulus, pos: tok.pos}, nil
	}

	// The limit relation `⟶` (a chapter's declared operator, operator.go)
	// with its optional point clause: `a ⟶ l` is the two-operand infix,
	// `f ⟶ l (at c)` the three-operand mixfix — the congruence
	// production's shape, the clause word `at` in place of `mod`. The
	// right operand's parseSegment leaves the clause for the same reason
	// the modulus clause survives: parseSpine declines to fold a
	// `(`-group headed by the clause word.
	if p.peek().kind == tokTendsTo {
		tok := p.advance()
		right, err := p.parseSegment()
		if err != nil {
			return nil, err
		}
		if !p.peekIsClause(LimitPointClause) {
			return &astBinOp{op: "⟶", left: left, right: right, pos: tok.pos}, nil
		}
		p.advance() // (
		p.advance() // at
		point, err := p.parseSegment()
		if err != nil {
			return nil, err
		}
		if _, rerr := p.expect(tokRParen); rerr != nil {
			return nil, rerr
		}
		return &astTendsAt{fn: left, limit: right, point: point, pos: tok.pos}, nil
	}

	op, ok := relationalOp(p.peek().kind)
	if !ok {
		return left, nil
	}
	tok := p.advance()
	right, err := p.parseSegment()
	if err != nil {
		return nil, err
	}
	return &astBinOp{op: op, left: left, right: right, pos: tok.pos}, nil
}

// peekIsModClause reports whether the parser is looking at `( mod` —
// the head of a congruence-modulus clause. Used by parseRelational's ≡
// arm (which requires it) and parseSpine (which must NOT consume it as
// an application arg group: `x ≡ nat_mod(y, n) (mod n)` would otherwise
// curry `(mod n)` onto nat_mod(y, n)). `mod` is not a reserved word — no
// constant has that name, and outside this two-token
// shape it lexes and parses as an ordinary ident.
func (p *parser) peekIsModClause() bool { return p.peekIsClause("mod") }

// peekIsTie reports whether a `⟨A:T⟩` tie opens at the current token:
// a `⟨`, a name and a `:` or `=`, so an angle-bracket term after an
// abbreviation is never read as one.
func (p *parser) peekIsTie() bool {
	if p.pos+2 >= len(p.tokens) || p.tokens[p.pos].kind != tokLangle || p.tokens[p.pos+1].kind != tokIdent {
		return false
	}
	sep := p.tokens[p.pos+2].kind
	return sep == tokColon || sep == tokEq
}

// peekIsClause reports whether the parser is looking at `( word` — the
// head of a trailing clause of a mixfix production: `mod` for the
// congruence's modulus, `at` for the limit's point. The clause words
// are not reserved: outside the two-token shape each lexes and parses
// as an ordinary ident, and parseSpine merely declines to fold a group
// so headed into an application (`f(mod, x)` with a variable literally
// named `mod` or `at` is the price, and the corpus states none).
func (p *parser) peekIsClause(word string) bool {
	if p.peek().kind != tokLParen || p.pos+1 >= len(p.tokens) {
		return false
	}
	next := p.tokens[p.pos+1]
	return next.kind == tokIdent && next.text == word
}

// parseSegment parses the `m..n` numeric range constructor
// (closed interval, both endpoints inclusive). Sits between relational
// and set-additive precedence,
// which puts `..` tighter than `<` but looser than `+`. Result has set
// type (num → bool), so a downstream `(m..n) p` membership term parses
// as a curried application of the segment to its element. Non-chaining:
// `a..b..c` is not meaningful (set-typed result can't be the left
// operand of another `..`), so single-pass is enough.
func (p *parser) parseSegment() (astNode, *InputDiagnostic) {
	left, err := p.parseSetAdd()
	if err != nil {
		return nil, err
	}
	if p.peek().kind != tokDotDot {
		return left, nil
	}
	tok := p.advance()
	right, err := p.parseSetAdd()
	if err != nil {
		return nil, err
	}
	return &astBinOp{op: "..", left: left, right: right, pos: tok.pos}, nil
}

// parseSetAdd parses left-associative chains of ∪ / ∖. Sits between
// segment (`..`) and set-multiplicative (`∩`) — so `s ∪ t ∩ u` parses as
// `s ∪ (t ∩ u)` (∩ binds tighter, the standard math convention). Both
// operators dispatch through setOperator to their polymorphic const
// metas (UnionMeta, DiffMeta) in buildBinOp.
func (p *parser) parseSetAdd() (astNode, *InputDiagnostic) {
	left, err := p.parseSetMul()
	if err != nil {
		return nil, err
	}
	for {
		var op string
		switch p.peek().kind {
		case tokUnion:
			op = "∪"
		case tokSetminus:
			op = "∖"
		default:
			return left, nil
		}
		tok := p.advance()
		right, err := p.parseSetMul()
		if err != nil {
			return nil, err
		}
		left = &astBinOp{op: op, left: left, right: right, pos: tok.pos}
	}
}

// parseSetMul parses left-associative chains of ∩. Sits between set-
// additive (∪/∖) and arith-additive (+/-) — so `card(s) + card(t)` is
// `(card(s)) + (card(t))` and `s ∩ t ∩ u` folds left as
// `(s ∩ t) ∩ u`. Arith operators are never valid on set-typed operands
// (buildBinOp rejects), so the intermediate precedence layer causes no
// well-typed ambiguity.
func (p *parser) parseSetMul() (astNode, *InputDiagnostic) {
	left, err := p.parseAdditive()
	if err != nil {
		return nil, err
	}
	for p.peek().kind == tokInter {
		tok := p.advance()
		right, err := p.parseAdditive()
		if err != nil {
			return nil, err
		}
		left = &astBinOp{op: "∩", left: left, right: right, pos: tok.pos}
	}
	return left, nil
}

// relationalOp returns the canonical operator string for a relational
// token kind, or ("", false) if the kind is not relational. The
// canonical strings are what astBinOp.op carries and what natOperator
// (arith) / setOperator (setops) match against.
//
// Set-theory relationals ∈/∉/⊆/⊊ sit at the same non-associative level as
// =/<-family: `x ∈ s ∪ t` reads as `x ∈ (s ∪ t)` (set-op tighter), and
// `s ⊆ t ⊆ u` errors as a chained relational the same way `a < b < c`
// does. buildBinOp routes them to setOperator's polymorphic const metas,
// `∉` as the negation of its `∈`.
func relationalOp(k tokenKind) (string, bool) {
	switch k {
	case tokEq:
		return "=", true
	case tokLt:
		return "<", true
	case tokLe:
		return "≤", true
	case tokGt:
		return ">", true
	case tokGe:
		return "≥", true
	case tokNe:
		return "≠", true
	case tokDivides:
		// U+2223 — divisibility (nat_divides / int_divides by operand
		// type via arithOperator). Relational level like <-family:
		// `d ∣ m * n` reads as `d ∣ (m * n)`, and `a ∣ b ∣ c` errors as
		// a chained relational.
		return "∣", true
	case tokIn:
		return "∈", true
	case tokNotIn:
		return "∉", true
	case tokSubset:
		return "⊆", true
	case tokPSubset:
		return "⊊", true
	}
	// `⟶` (U+27F6) is relational too, but it has its own arm in
	// parseRelational for the optional point clause.
	return "", false
}

// parseAdditive parses left-associative chains of + / -.
//
//	a - b + c   parses as   (a - b) + c
func (p *parser) parseAdditive() (astNode, *InputDiagnostic) {
	left, err := p.parseSmul()
	if err != nil {
		return nil, err
	}
	for {
		var op string
		switch p.peek().kind {
		case tokPlus:
			op = "+"
		case tokMinus:
			op = "-"
		default:
			return left, nil
		}
		tok := p.advance()
		right, err := p.parseSmul()
		if err != nil {
			return nil, err
		}
		left = &astBinOp{op: op, left: left, right: right, pos: tok.pos}
	}
}

// parseSmul parses right-associative chains of `•`, the scalar
// action's infix — a symbol a chapter's constant declares (operator.go)
// and the build resolves by operand type. It sits between `+ -` and
// `* /`: `c * d • u` is `(c * d) • u`, the product of scalars acting
// once, and `c • d • u` is `c • (d • u)`, the one grouping that types.
// A big operator's body is read at this level (bigop.go), so
// `Σ_{i<m} x(i) • e(i)` sums the terms and `Σ_{i<m} a(i) + b` adds b
// to the sum.
func (p *parser) parseSmul() (astNode, *InputDiagnostic) {
	left, err := p.parseMultiplicative()
	if err != nil {
		return nil, err
	}
	if p.peek().kind != tokSmul {
		return left, nil
	}
	tok := p.advance()
	right, err := p.parseSmul()
	if err != nil {
		return nil, err
	}
	return &astBinOp{op: "•", left: left, right: right, pos: tok.pos}, nil
}

// parseMultiplicative parses left-associative chains of * and /.
//
// The two share one level, left-associative, so `x / y * z` is
// `(x / y) * z` — the ordinary reading. `/` is real division only; the
// build step reports the missing instance at any other operand domain.
func (p *parser) parseMultiplicative() (astNode, *InputDiagnostic) {
	left, err := p.parseCompose()
	if err != nil {
		return nil, err
	}
	for {
		var op string
		switch p.peek().kind {
		case tokStar:
			op = "*"
		case tokSlash:
			op = "/"
		default:
			return left, nil
		}
		tok := p.advance()
		right, err := p.parseCompose()
		if err != nil {
			return nil, err
		}
		left = &astBinOp{op: op, left: left, right: right, pos: tok.pos}
	}
}

// parseCompose parses right-associative chains of ∘ (function
// composition). It sits one level tighter than `*`;
// since a composition's operands
// are functions and no arithmetic operator has a function instance, the
// level resolves no genuine ambiguity.
//
// Right-associative because that is the source and the mathematical
// convention. `o` is associative, so the grouping is presentational —
// but `f ∘ g ∘ h` must round-trip to ONE term, and the printer's
// 2-arity infix template re-parses whatever this builds.
func (p *parser) parseCompose() (astNode, *InputDiagnostic) {
	left, err := p.parseUnary()
	if err != nil {
		return nil, err
	}
	if p.peek().kind != tokCompose {
		return left, nil
	}
	tok := p.advance()
	right, err := p.parseCompose()
	if err != nil {
		return nil, err
	}
	return &astBinOp{op: "∘", left: left, right: right, pos: tok.pos}, nil
}

// bareOperatorFollows reports whether the token after an operator
// symbol makes the symbol a first-class occurrence of its constant
// rather than an operator with a missing operand: a standalone
// argument or parenthesized value (`,` / `)`), or the whole text
// (the end of the input) — a layout's template that is the operator
// itself, as the printer spells the `+` of a resident
// `comm_monoid_on(𝕌, +, 0)`, is read back so. An operator before `(`
// heads a prefix call (parseAtom); `¬` before `(` is a negation.
func bareOperatorFollows(next tokenKind) bool {
	return next == tokComma || next == tokRParen || next == tokEOF
}

func (p *parser) parseUnary() (astNode, *InputDiagnostic) {
	if p.peek().kind == tokNot {
		// A bare `¬` standing as an argument, a parenthesized value or
		// the whole text (`word_bitwise_unary(n, ¬, x)`, `(¬)`) is the
		// negation constant itself, as a bare `+` is the addition
		// constant (parseAtom); `¬(…)` stays a negation, the two
		// readings of it being one term.
		if bareOperatorFollows(p.tokens[p.pos+1].kind) {
			tok := p.advance()
			return &astVar{name: utils.NegStr, pos: tok.pos}, nil
		}
		tok := p.advance()
		body, err := p.parseUnary()
		if err != nil {
			return nil, err
		}
		return &astNotNode{body: body, pos: tok.pos}, nil
	}
	// Unary `-x` is negation (real_neg | int_neg), resolved by the operand's
	// type at build time (astNeg). It binds like ¬ — tighter than `*`, so
	// `-x * y` is `(-x) * y`, and looser than `^` and `&` — and recurses through parseUnary so `--x` is a
	// double negation and `- &3` negates the coercion. (Binary `-` is handled
	// in parseAdditive, which only fires AFTER a left operand, so there is no
	// ambiguity: a `-` reaching parseUnary is always prefix.)
	if p.peek().kind == tokMinus {
		tok := p.advance()
		operand, err := p.parseUnary()
		if err != nil {
			return nil, err
		}
		return &astNeg{operand: operand, pos: tok.pos}, nil
	}
	// `&` is the numeric-literal coercion prefix (num → real|int). It binds
	// tightest (its operand is a single spine, so `&2 * x` is `(&2) * x` and
	// `&(a+b)` needs the parens). The target type is resolved at BUILD time by
	// context (astCoerce): default real_of_num, int_of_num when the context is
	// int. So `&n` is a real literal by default and an int literal under an
	// int operand/expected type.
	if p.peek().kind == tokAmp {
		tok := p.advance()
		operand, err := p.parseSpine()
		if err != nil {
			return nil, err
		}
		return p.parsePower(&astCoerce{operand: operand, pos: tok.pos})
	}
	// Wide-binding quantifiers: ∀x:A. P(x) ⇒ Q(x)
	// is parsed as ∀x:A. (P(x) ⇒ Q(x)). See parseQuant for details.
	// ε binds the same way — the body is a boolean predicate, and wide
	// binding lets `εx:A. P(x) ∧ Q(x)` read as the Hilbert pick over
	// the conjunction rather than as an application.
	if p.peek().kind == tokForall || p.peek().kind == tokExists ||
		p.peek().kind == tokUnique || p.peek().kind == tokHilbert {
		// A bare `∀` / `∃` standing as an argument or a parenthesized
		// value is the quantifier constant itself — `insert(s, ∃)`
		// names the set of non-empty sets — as a bare `+` is the
		// addition constant (parseAtom).
		if kind := p.peek().kind; kind == tokForall || kind == tokExists {
			if nxt := p.tokens[p.pos+1].kind; nxt == tokComma || nxt == tokRParen {
				tok := p.advance()
				return &astVar{name: tok.text, pos: tok.pos}, nil
			}
		}
		return p.parseQuant()
	}
	if p.peek().kind == tokLambda {
		return p.parseLambda()
	}
	// A big operator binds its index over a body read at the scalar
	// action's level (bigop.go).
	if p.peek().kind == tokBigSum || p.peek().kind == tokBigProd {
		return p.parseBigOp()
	}
	base, err := p.parseSpine()
	if err != nil {
		return nil, err
	}
	return p.parsePower(base)
}

// parsePower reads `base ^ exponent` after a base already parsed: an
// application spine or a coerced literal, `&` binding tighter than `^`.
// The power binds tighter than the prefix `-` and `¬`, so `-x ^ 2` is
// `-(x ^ 2)` and a negated base is written `(-x) ^ 2`; it associates to
// the right, the exponent being read at the prefix level, so
// `x ^ m ^ n` is `x ^ (m ^ n)`. At build time the BASE's domain picks
// the constant — nat_pow at num, real_pow at real, int_pow at int
// (arith.go's powDomainOperator) — and elsewhere the constant declaring
// `^` is picked by the operands (operator.go).
func (p *parser) parsePower(base astNode) (astNode, *InputDiagnostic) {
	if p.peek().kind != tokCaret {
		return base, nil
	}
	tok := p.advance()
	exponent, err := p.parseUnary()
	if err != nil {
		return nil, err
	}
	return &astBinOp{op: "^", left: base, right: exponent, pos: tok.pos}, nil
}

// parseSpine consumes one atom and then greedily applies it to any
// number of trailing atoms, supporting both:
//
//	f(x)(y)        — curried explicit application, where the
//	                 trailing groups are paren-arg lists. Each `(…)`
//	                 may carry multiple comma-separated args, which
//	                 desugar via the existing astApp shape.
//
//	f x y          — juxtaposition, the curried form.
//	                 Each trailing atom is a single-arg apply step.
//
// Mixed shapes work too: `f x (y, z) w`. Application binds tighter
// than every binary operator and ¬, so `f x ∧ g y` is `(f x) ∧ (g y)`.
// `f` itself must be an atom — quantifier-headed args (`f (∀x. P x)`,
// `f (λy. y)`) need explicit parens because parseUnary dispatches
// quantifiers/lambdas before parseSpine. parseAtom still handles the
// FIRST paren-arg list on a bare identifier (the legacy
// `tokIdent`-then-`tokLParen` fast path), so spine's job is just to
// keep extending the application past the first call site.
func (p *parser) parseSpine() (astNode, *InputDiagnostic) {
	head, err := p.parseAtom()
	if err != nil {
		return nil, err
	}
	for {
		next := p.peek()
		switch next.kind {
		case tokDot:
			before := p.pos
			head = p.parseFields(head)
			if p.pos == before {
				return head, nil
			}
		case tokLParen:
			// `( mod` heads a congruence-modulus clause and `( at` a
			// limit's point clause, not an arg group — leave them for
			// parseRelational's ≡ and ⟶ arms, their only consumers.
			if p.peekIsModClause() || p.peekIsClause(LimitPointClause) {
				return head, nil
			}
			p.advance() // (
			args, aerr := p.parseArgs()
			if aerr != nil {
				return nil, aerr
			}
			if _, rerr := p.expect(tokRParen); rerr != nil {
				return nil, rerr
			}
			// `vec⟨n⟩(u)` is one application: the group directly after
			// a head's dimensions joins them (dimension.go).
			if app, ok := head.(*astApp); ok && app.dims > 0 && app.dims == len(app.args) {
				app.args = append(app.args, args...)
				continue
			}
			head = &astApp{fun: head, args: args, pos: next.pos}
		case tokIdent, tokNumLit, tokTop, tokBot, tokLBrace, tokAbbrev:
			// Juxtaposition: head and a fresh atom both get
			// re-parsed as atoms; the comma separator is reserved
			// for paren-arg lists, so `f x y` is `(f x) y`, not
			// `f(x, y)`. Identifiers that happen to also be the
			// head of a `(…)` call still work — parseAtom on a
			// bare ident with a following `(` handles that, and
			// spine continues from the resulting astApp. An
			// abbreviation is an atom like an identifier.
			//
			// tokLBrace: brace atoms (`{a, b}` enumeration, `{x | φ}` /
			// `{t | x | φ}` set-builders) are self-delimiting, and the
			// printer's tight-prefix arity-1 templates emit them
			// unparenthesized (`⋃{x | φ}` — see the big_union/big_intersection
			// templates in ext/format.go). A `{` directly after an
			// application head had no other legal reading.
			arg, aerr := p.parseAtom()
			if aerr != nil {
				return nil, aerr
			}
			// A chain of fields belongs to the argument: f S.inner.zero
			// is f(S.inner.zero), not f(S.inner).zero.
			arg = p.parseFields(arg)
			head = &astApp{fun: head, args: []astNode{arg}, pos: next.pos}
		default:
			return head, nil
		}
	}
}

// parseFields consumes tightly attached postfix fields. It is shared
// by the application spine and its juxtaposed arguments so a field
// binds to its receiver before that receiver is passed to a function.
func (p *parser) parseFields(receiver astNode) astNode {
	for p.peek().kind == tokDot && p.pos+1 < len(p.tokens) {
		prev, dot, field := p.tokens[p.pos-1], p.tokens[p.pos], p.tokens[p.pos+1]
		if dot.pos != prev.pos+len(prev.text) || field.kind != tokIdent || field.pos != dot.pos+1 {
			break
		}
		p.advance()
		p.advance()
		receiver = fieldNode(receiver, field.text, dot.pos)
	}
	return receiver
}

// parseLambda parses bare lambda binders. Three accepted shapes:
//
//	λx:T. body         — typed single binder (canonical)
//	λx. body           — untyped single binder; type inferred from
//	                     enclosing expected codomain or body usage.
//	                     If neither pins it, defaults to a fresh
//	                     type variable in buildAbs.
//	λ(x:T1) (y:T2). body
//	                  — paren-grouped multi-binder; desugars to
//	                     chained `λx:T1. λy:T2. body`. Each group
//	                     MUST carry a type (the whole point of the
//	                     paren form is to scope a complex type like
//	                     `num→recspace(α)` to one binder).
//
// The body uses parseExpr (full expression) rather than parseRelational
// (what quantifiers take): lambdas almost always appear in argument
// position where `,` / `)` already bound the body, and the few
// standalone uses (`(λx:A. body) = (λx:A. body')` etc.) read naturally
// with a wide body. Chained lambdas / nested quantifiers in the body
// recurse via parseUnary's dispatch.
func (p *parser) parseLambda() (astNode, *InputDiagnostic) {
	tok := p.advance() // λ

	// Pair-pattern lambda: λ(u:T, x:T). body / λ((a, b), c). body.
	// Probed BEFORE the paren-grouped multi-binder form — the two are
	// disambiguated by the `,` inside the paren group (a multi-binder
	// group is always a single `(name:type)`). On a failed probe the
	// position is restored and the multi-binder path below reports its
	// own diagnostics.
	if p.peek().kind == tokLParen {
		save := p.pos
		if pat, ok := p.parsePatTree(); ok && p.peek().kind == tokDot {
			p.advance() // .
			body, err := p.parseExpr()
			if err != nil {
				return nil, err
			}
			return &astPatternAbs{pat: pat, body: body, pos: tok.pos}, nil
		}
		p.pos = save
	}

	// Paren-grouped multi-binder: λ(x:T1) (y:T2) ... . body
	if p.peek().kind == tokLParen {
		type binder struct {
			name string
			ty   astType
			pos  int
		}
		var binders []binder
		for p.peek().kind == tokLParen {
			lp := p.advance() // (
			name, err := p.expect(tokIdent)
			if err != nil {
				return nil, err
			}
			if _, err = p.expect(tokColon); err != nil {
				// Paren-grouped form requires a type in each group; an
				// untyped paren-grouped binder is ambiguous with function
				// application of a parenthesized expression.
				return nil, &InputDiagnostic{
					Position:   p.peek().pos,
					Length:     len(p.peek().text),
					Code:       CodeParseError,
					Message:    fmt.Sprintf("paren-grouped lambda binder must declare a type; got %q", p.peek().text),
					Suggestion: "write `λ(x:T) (y:T). body` with a type per group, or use chained `λx:T. λy:T. body`",
				}
			}
			ty, err := p.parseType()
			if err != nil {
				return nil, err
			}
			if _, err = p.expect(tokRParen); err != nil {
				return nil, err
			}
			binders = append(binders, binder{name: name.text, ty: ty, pos: lp.pos})
		}
		if _, err := p.expect(tokDot); err != nil {
			return nil, err
		}
		body, err := p.parseExpr()
		if err != nil {
			return nil, err
		}
		// Right-fold: λ(x:T1)(y:T2). body  →  λx:T1. (λy:T2. body)
		for i := len(binders) - 1; i >= 0; i-- {
			body = &astAbsNode{
				varName: binders[i].name,
				varType: binders[i].ty,
				body:    body,
				pos:     binders[i].pos,
			}
		}
		return body, nil
	}

	// Single-binder form (typed or untyped).
	name, err := p.expect(tokIdent)
	if err != nil {
		return nil, err
	}
	var ty astType
	if p.peek().kind == tokColon {
		p.advance()
		ty, err = p.parseType()
		if err != nil {
			return nil, err
		}
	}
	if _, err = p.expect(tokDot); err != nil {
		return nil, err
	}
	body, err := p.parseExpr()
	if err != nil {
		return nil, err
	}
	return &astAbsNode{
		varName: name.text,
		varType: ty, // nil = untyped, resolved at build time
		body:    body,
		pos:     tok.pos,
	}, nil
}

func (p *parser) parseAtom() (astNode, *InputDiagnostic) {
	tok := p.peek()

	switch tok.kind {
	case tokTop:
		p.advance()
		return &astConst{name: utils.TrueStr, pos: tok.pos}, nil

	case tokBot:
		p.advance()
		return &astConst{name: utils.FalseStr, pos: tok.pos}, nil

	case tokNormBar, tokLDAngle, tokLQuill, tokLDBracket, tokLShell, tokPipe:
		// A `|` where an expression begins opens a notation (`|x|`); the
		// set-builder's separator follows an expression and never
		// arrives here.
		return p.parseOutfix()

	case tokAbbrev:
		// An abbreviation is an atom: the scope's expansion puts the
		// entry's own AST here (abbreviation.go). A trailing `(...)`
		// and a field `«R».add` are parseSpine's, as for an identifier.
		// A trailing `⟨A:T⟩` is the use's tie: the type it takes for a
		// letter the entry is written at, as a constant's.
		p.advance()
		var ties []typeAnnotBinding
		if p.peekIsTie() {
			ann, err := p.parseTypeAnnotation()
			if err != nil {
				return nil, err
			}
			ties = ann
		}
		return &astAbbrev{name: abbrevName(tok.text), ties: ties, pos: tok.pos}, nil

	case tokNumLit:
		p.advance()
		v, ok := new(big.Int).SetString(tok.text, 10)
		if !ok {
			return nil, &InputDiagnostic{
				Position: tok.pos,
				Length:   len(tok.text),
				Code:     CodeParseError,
				Message:  fmt.Sprintf("invalid numeric literal %q", tok.text),
			}
		}
		return &astNumLit{value: v, pos: tok.pos}, nil

	case tokLParen:
		p.advance()
		expr, err := p.parseExpr()
		if err != nil {
			return nil, err
		}
		// Tuple literal: `(a, b)` / `(a, b, c)`. This is the printer-
		// emitted form for the pair constructor `,` (see format.go's
		// CommaConstMeta infix render). `,` is right-
		// associative, so `(a, b, c)` folds to `,(a, ,(b, c))`; the
		// prefix `,(...)` form (handled in the tokComma branch below)
		// is retained for backward compat with already-stored
		// assert.text payloads. A `(expr)` with no comma stays a plain
		// parenthesized grouping.
		if p.peek().kind == tokComma {
			comps := []astNode{expr}
			for p.peek().kind == tokComma {
				p.advance() // consume ","
				next, nerr := p.parseExpr()
				if nerr != nil {
					return nil, nerr
				}
				comps = append(comps, next)
			}
			if _, err = p.expect(tokRParen); err != nil {
				return nil, err
			}
			return makePairAST(comps, tok.pos), nil
		}
		_, err = p.expect(tokRParen)
		if err != nil {
			return nil, err
		}
		// Mark binary ops inside explicit parens so we can suppress
		// ambiguity warnings when the user already disambiguated.
		if bn, ok := expr.(*astBinOp); ok {
			bn.parens = true
		}
		return expr, nil

	case tokIdent:
		p.advance()
		// A FIELD, `N.add`: an identifier, a dot and an identifier with
		// nothing between them, in term position — a binder's dot is
		// never read here (bundle.go).
		if p.pos+1 < len(p.tokens) {
			dot, field := p.tokens[p.pos], p.tokens[p.pos+1]
			if dot.kind == tokDot && dot.pos == tok.pos+len(tok.text) &&
				field.kind == tokIdent && field.pos == dot.pos+1 {
				p.advance()
				p.advance()
				tok = token{kind: tokIdent, text: tok.text + "." + field.text, pos: tok.pos}
			}
		}
		// A trailing `(...)` is NOT consumed here — parseSpine is the
		// uniform owner of every application form (curried `f(x)(y)`,
		// juxtaposition `f x`, mixed `f x (y)`). Folding the `(...)`
		// into parseAtom would mis-bind `f x (y)` as `f (x(y))`,
		// because the juxtaposition arm of parseSpine would call
		// parseAtom on `x`, which would greedily eat the following
		// paren-arg group.
		//
		// A trailing `⟨V:T, ...⟩` polymorphic type-substitution
		// annotation IS consumed here — it binds tightly to the
		// identifier (like a suffix operator), and the annotation is
		// resolved against the const's meta at buildVarTerm / buildApp
		// time. If the identifier turns out not to be a scope-const,
		// build.go raises a clear error.
		//
		// The same suffix holds the dimensions of a constant that
		// declares them, `vec⟨n⟩` (dimension.go): the atom is then the
		// constant applied to them, and parseSpine reads a following
		// `(...)` into that one application.
		var annot []typeAnnotBinding
		var dims []astNode
		if p.peek().kind == tokLangle {
			ann, ds, err := p.parseHeadAnnotation()
			if err != nil {
				return nil, err
			}
			annot, dims = ann, ds
		}
		head := &astVar{name: tok.text, typeAnnot: annot, pos: tok.pos}
		if len(dims) > 0 {
			return &astApp{fun: head, args: dims, dims: len(dims), pos: tok.pos}, nil
		}
		return head, nil

	case tokDotDot:
		// `..` in atom position (no left operand) is the
		// segment const used as a function head — `..(m, n)` (prefix
		// call form) or even `..(m, n, p)` (curried membership). Lexer
		// emits tokDotDot uniformly; parseSegment consumes it after
		// it's the binary infix between two additive expressions, so
		// reaching parseAtom means we're in prefix position. Treat as
		// the ident ".." and let parseSpine handle any trailing arg
		// group like any other function name.
		p.advance()
		return &astVar{name: "..", pos: tok.pos}, nil

	case tokEmpty:
		// ∅ — the empty set, polymorphic nullary const. Lowered to a
		// bare astVar{"empty_set"} whose meta (EmptyMeta in setops.go) is
		// seeded into scopeConstMetas by registerSetScopeConsts. The
		// scopeConstMetas-only branch of buildVarTerm instantiates it
		// at its abstract polymorphic type, and subsequent inference
		// (e.g. `x ∈ ∅` or `s ∪ ∅`) pins A via unification. A trailing
		// `⟨A:T⟩` annotation is consumed here — polymorphic-conflict
		// printing surfaces `∅⟨A:num⟩` as the disambiguated form.
		return p.parseSetAtomConst("empty_set")

	case tokUniv:
		// 𝕌 — the universe set, polymorphic nullary const. Same lowering
		// discipline as ∅ — see tokEmpty above.
		return p.parseSetAtomConst("universe")

	case tokBigUnion:
		// ⋃ — big-union TIGHT PREFIX: the symbol (plus optional `⟨A:T⟩`
		// annotation) takes ONE spine as its operand, mirroring the `&`
		// coercion's binding (parseUnary's tokAmp branch). See
		// parseSetPrefixOp for why the old bare-var + spine-juxtaposition
		// lowering was wrong for ident-headed operands.
		return p.parseSetPrefixOp("big_union")

	case tokBigInter:
		// ⋂ — big-intersection tight prefix. Same as ⋃.
		return p.parseSetPrefixOp("big_intersection")

	case tokLBrace:
		// `{...}` — set enumeration `{a₁, a₂, …, aₙ}` (lowered to a right-
		// folded insert-chain over empty_set) or set-builder `{f(x) | φ(x)}`
		// (Task #5, TBD — flagged as an error until implemented). Empty
		// braces `{}` lower to bare empty_set. Distinguished by whether a
		// top-level `|` follows the first expression.
		return p.parseBrace()

	case tokPlus, tokStar, tokLt, tokGt, tokLe, tokGe, tokAnd, tokOr, tokImply:
		// Bare operator const in VALUE position: `monoidal_op(+)`,
		// `op_support(+, f, s)`, `neutral_elem(*)`,
		// `word_bitwise_binary(k, ∧, x, y)`, and the prefix-call form
		// of a partial application, `*(k)` for `λn. k * n`. The
		// nat operators are consts literally named "+", "*", "<", ">",
		// "<=", ">=", the connectives "∧", "∨", "⇒", and the printer
		// renders a first-class (unapplied or partially applied)
		// occurrence as the bare symbol. Restricted to occurrences
		// whose FOLLOWING token is "," or ")" or the end of the text —
		// manifestly a standalone argument / parenthesized value / the
		// whole text (bareOperatorFollows) — or "(" — the head of a
		// prefix call, as `..(m, n)` is read — never the start of an
		// operand expression, so mistyped infix chains (`x + + y`)
		// still error out instead of silently parsing as a partial
		// application (a trailing `x + +` reads its last `+` as the
		// constant and fails at its type). The name resolves through the regular
		// scope-const path at build time (Consts/ConstMetas, the
		// resolver); note the real/int siblings (real_add, int_mul, …)
		// print their own identifier in this position, not the
		// overloaded symbol, so the bare symbol uniquely denotes the
		// nat instance. Unary-capable `-` never reaches parseAtom
		// (parseUnary owns it), so the num monus const has no
		// bare-value spelling — a printed bare `-` fails here by
		// design and the caller's round-trip gate falls back; `=` and
		// `⇔` have none either, the builder making both by their
		// wrappers rather than by a named lookup.
		if next := p.tokens[p.pos+1].kind; bareOperatorFollows(next) || next == tokLParen {
			opName := map[tokenKind]string{
				tokPlus: "+", tokStar: "*", tokLt: "<",
				tokGt: ">", tokLe: "<=", tokGe: ">=",
				tokAnd: utils.AndStr, tokOr: utils.OrStr, tokImply: utils.ImplyStr,
			}[tok.kind]
			p.advance()
			return &astVar{name: opName, pos: tok.pos}, nil
		}
		return nil, &InputDiagnostic{
			Position:   tok.pos,
			Length:     len(tok.text),
			Code:       CodeParseError,
			Message:    fmt.Sprintf("expected expression, got %q", tok.text),
			Suggestion: "a bare operator is only valid as a standalone argument, e.g. monoidal_op(+)",
		}

	case tokComma:
		// Pair-constructor prefix literal: `,(a, b)`. The pair
		// const is named literally ",". The printer now emits the natural
		// infix tuple form `(a, b)` (handled in the tokLParen branch), but
		// this prefix branch is retained because already-stored assert.text
		// payloads from before that change still carry `,(...)`, and the
		// parser may only add surface syntax, never drop it.
		//
		// Resolution happens at buildApp time via
		// env.scopeConstMetas[","] (commaConstMeta from pairs.go,
		// registered in defaultNatScopeConstMetas).
		if p.pos+1 < len(p.tokens) && p.tokens[p.pos+1].kind == tokLParen {
			p.advance() // consume ","
			p.advance() // consume "("
			args, err := p.parseArgs()
			if err != nil {
				return nil, err
			}
			if _, err = p.expect(tokRParen); err != nil {
				return nil, err
			}
			return &astApp{
				fun:  &astVar{name: ",", pos: tok.pos},
				args: args,
				pos:  tok.pos,
			}, nil
		}
		// Bare "," with no following "(" — fall through to the default
		// error so misplaced separators (e.g., a stray "," at the start
		// of an arg list) still surface clearly.
		return nil, &InputDiagnostic{
			Position:   tok.pos,
			Length:     len(tok.text),
			Code:       CodeParseError,
			Message:    "expected expression, got \",\"",
			Suggestion: "for a pair literal, write (a, b); a bare \",\" is only valid as an arg/decl separator",
		}

	default:
		return nil, &InputDiagnostic{
			Position:   tok.pos,
			Length:     len(tok.text),
			Code:       CodeParseError,
			Message:    fmt.Sprintf("expected expression, got %q", tok.text),
			Suggestion: "write a variable name, ⊤, ⊥, or a parenthesized expression",
		}
	}
}

// makePairAST folds tuple components into a right-associative chain of
// binary pair-constructor applications: `(a, b, c)` → `,(a, ,(b, c))`.
// `,` is right-associative, so the result round-trips
// the printer's nested infix output and resolves through buildAppViaMeta
// (CommaConstMeta is binary, A → B → prod(A, B)). The single-component
// case never reaches here — the tokLParen caller only invokes this once
// it has seen a comma, so comps always has length ≥ 2.
func makePairAST(comps []astNode, pos int) astNode {
	result := comps[len(comps)-1]
	for i := len(comps) - 2; i >= 0; i-- {
		result = &astApp{
			fun:  &astVar{name: ",", pos: pos},
			args: []astNode{comps[i], result},
			pos:  pos,
		}
	}
	return result
}

// parsePatTree probes one λ-pattern paren group:
//
//	'(' elem (',' elem)+ ')'    elem := ident[:type] | nested group
//
// A group with NO top-level comma is not a pattern (it is the
// paren-grouped multi-binder form `λ(x:T). …`), so the probe declines
// and the caller restores the token position. Components fold
// right-associatively, mirroring makePairAST:
// `(a, b, c)` is the pattern `(a, (b, c))`.
func (p *parser) parsePatTree() (*astPat, bool) {
	if p.peek().kind != tokLParen {
		return nil, false
	}
	lp := p.advance() // (
	var elems []*astPat
	for {
		elem, ok := p.parsePatElem()
		if !ok {
			return nil, false
		}
		elems = append(elems, elem)
		if p.peek().kind != tokComma {
			break
		}
		p.advance() // ,
	}
	if len(elems) < 2 || p.peek().kind != tokRParen {
		return nil, false
	}
	p.advance() // )
	result := elems[len(elems)-1]
	for i := len(elems) - 2; i >= 0; i-- {
		result = &astPat{left: elems[i], right: result, pos: lp.pos}
	}
	return result, true
}

func (p *parser) parsePatElem() (*astPat, bool) {
	if p.peek().kind == tokLParen {
		return p.parsePatTree()
	}
	if p.peek().kind != tokIdent {
		return nil, false
	}
	name := p.advance()
	leaf := &astPat{name: name.text, pos: name.pos}
	if p.peek().kind == tokColon {
		p.advance()
		ty, err := p.parseType()
		if err != nil {
			return nil, false
		}
		leaf.ty = ty
	}
	return leaf, true
}

// parseSetAtomConst is shared machinery for the symbol-only set atoms
// (∅, 𝕌, ⋃, ⋂). It consumes the symbol token, optionally consumes the
// `⟨V:T, ...⟩` polymorphic type-substitution annotation that the printer
// emits under a poly-const type conflict, and returns an astVar under
// the given const name. buildVarTerm resolves the name via
// scopeConstMetas (registerSetScopeConsts in setops.go). The annotated
// build path (buildAnnotatedVarTerm) treats the meta identically to a
// tokIdent-carried annotation.
func (p *parser) parseSetAtomConst(name string) (astNode, *InputDiagnostic) {
	tok := p.advance()
	var annot []typeAnnotBinding
	if p.peek().kind == tokLangle {
		ann, err := p.parseTypeAnnotation()
		if err != nil {
			return nil, err
		}
		annot = ann
	}
	return &astVar{name: name, typeAnnot: annot, pos: tok.pos}, nil
}

// parseSetPrefixOp parses the big-op prefixes (⋃, ⋂) as TIGHT PREFIX
// operators: the symbol (with optional `⟨A:T⟩` annotation) followed by
// ONE spine operand — the same binding as the `&` numeric coercion
// (parseUnary's tokAmp branch): `⋃image(f, s)` is big_union(image(f, s)),
// `⋃s ∪ t` is (⋃s) ∪ t, `⋃f x` is ⋃(f x), `⋃⋃s` nests.
//
// The previous lowering (bare astVar handed to parseSpine's
// juxtaposition) MIS-BOUND ident-headed operands: parseAtom deliberately
// does not fold a trailing `(...)` into an ident (parseSpine owns every
// application form, so `f x (y)` stays `(f x)(y)`), which made
// `⋂image(f, s)` parse as (big_intersection image)(f, s) — a type error at best,
// a silently wrong term at worst (two
// round-trip failures on statements over ⋂image and ⋃). The emit text gate always caught the divergence
// and fell back to Go-expr, so the cost was text coverage, not
// soundness — but hand-written text had the same trap.
//
// A following paren group is deliberately NOT treated as the spine
// operand: returning the bare var lets parseSpine's tokLParen arm apply
// it as a plain ARGS group, preserving the call readings `⋃(s)`,
// `⋃(s, x)` (the 2-arg membership-unfold form) and `⋃(s)(x)` exactly as
// before. Likewise with no operand-starting token following (value
// position — `f(⋃)`, `⋃` before `,` / an infix), the bare astVar keeps
// unapplied uses working.
func (p *parser) parseSetPrefixOp(name string) (astNode, *InputDiagnostic) {
	v, err := p.parseSetAtomConst(name)
	if err != nil {
		return nil, err
	}
	switch p.peek().kind {
	case tokIdent, tokLBrace, tokEmpty, tokUniv, tokBigUnion, tokBigInter, tokAbbrev:
		operand, oerr := p.parseSpine()
		if oerr != nil {
			return nil, oerr
		}
		return &astApp{
			fun:  v,
			args: []astNode{operand},
			pos:  v.nodePos(),
		}, nil
	}
	return v, nil
}

// parseBrace dispatches the `{...}` bracket forms. Called from parseAtom
// after peeking tokLBrace. Three shapes:
//
//   - `{}`               → empty_set.
//   - `{a₁, …, aₙ}`      → right-folded insert-chain over empty_set.
//   - `{f | φ}`          → set-builder, lowered to set_comprehension(λv. ∃x. comprehension_spec(v, φ, f)).
//
// Distinguished by the token following the first inner expression: `,`
// or `}` → enumeration; `|` → set-builder. The empty case is detected up
// front by an immediate `}`.
func (p *parser) parseBrace() (astNode, *InputDiagnostic) {
	tok := p.advance() // consume `{`

	// Empty braces `{}` — a bare empty_set. Convenient for empty-set literals
	// in the surface; lowering keeps the polymorphic-instantiation path.
	if p.peek().kind == tokRBrace {
		p.advance()
		return &astVar{name: "empty_set", pos: tok.pos}, nil
	}

	first, err := p.parseExpr()
	if err != nil {
		return nil, err
	}

	// Typed set-builder head. In the two-part identity form `{x:T | φ}`, T
	// types the witness binder. In the three-part general form
	// `{f(x):U | x:T | φ}`, U types the output and therefore the hidden set_comprehension
	// λ-binder. parseSetBuilderCore distinguishes the forms by probing for the
	// second `|` after the first one.
	var headType astType
	if p.peek().kind == tokColon {
		p.advance()
		headType, err = p.parseType()
		if err != nil {
			return nil, err
		}
		if _, err := p.expect(tokPipe); err != nil {
			return nil, err
		}
		return p.parseSetBuilderCore(first, headType, tok.pos)
	}

	// Untyped set-builder `{f | φ}`. The bar sits at parser precedence lower
	// than every operator inside the braces (the lexer emits tokPipe only,
	// no fallthrough into any precedence layer), so parseExpr stops
	// naturally at the bar. Binder type is left nil — untyped-binder
	// inference in the build pass pins it via comprehension_spec's typing chain.
	if p.peek().kind == tokPipe {
		p.advance() // consume `|`
		return p.parseSetBuilderCore(first, nil, tok.pos)
	}

	// Enumeration form — collect the remaining comma-separated elements.
	elems := []astNode{first}
	for p.peek().kind == tokComma {
		p.advance()
		next, nerr := p.parseExpr()
		if nerr != nil {
			return nil, nerr
		}
		elems = append(elems, next)
	}
	if _, err := p.expect(tokRBrace); err != nil {
		return nil, err
	}
	return makeSetEnumAST(elems, tok.pos), nil
}

// setBuilderBinder is one entry of the general form's explicit binder
// list: a bare ident with an optional `:T` annotation.
type setBuilderBinder struct {
	name string
	typ  astType // nil → untyped inference
}

// probeSetBuilderBinderList tries to read the middle segment of the
// three-part general set-builder `{t | x₁, …, xₙ | φ}`: a comma-separated
// list of bare binder idents (each optionally `x:T`), terminated by a
// second `|`. On success the terminating `|` is consumed and the list is
// returned. On ANY mismatch it returns (nil, false) WITHOUT restoring
// p.pos — the caller owns the backtrack (a failed probe means the segment
// is the two-part identity form's φ and must be re-parsed as an
// expression).
func (p *parser) probeSetBuilderBinderList() ([]setBuilderBinder, bool) {
	var binders []setBuilderBinder
	for {
		if p.peek().kind != tokIdent {
			return nil, false
		}
		b := setBuilderBinder{name: p.advance().text}
		if p.peek().kind == tokColon {
			p.advance()
			ty, err := p.parseType()
			if err != nil {
				return nil, false
			}
			b.typ = ty
		}
		binders = append(binders, b)
		switch p.peek().kind {
		case tokComma:
			p.advance()
		case tokPipe:
			p.advance()
			return binders, true
		default:
			return nil, false
		}
	}
}

// parseSetBuilderCore is the shared desugar for the set-builder forms:
//
//   - identity two-part `{x | φ}` / `{x:T | φ}` (headType carries the
//     annotation): the output is a bare ident that doubles as the single
//     ∃-bound witness. Desugars to
//
//     set_comprehension(λv:T. ∃x:T. comprehension_spec(v, φ, x))
//
//   - general three-part `{t:U | x₁:T₁, …, xₙ:Tₙ | φ}` (the output type U
//     is optional on input; the parser-profile printer emits it): the explicit
//     binder list makes the bound-variable set, order and names entirely
//     surface-determined. The output t is an arbitrary expression over the
//     binders. Desugars to
//
//     set_comprehension(λv:U. ∃x₁:T₁. … ∃xₙ:Tₙ. comprehension_spec(v, φ, t))
//
// In both, `v` is a fresh outer binder (name `GEN%PVAR%<open-pos>` —
// safe because `%` is a legal ident char and the
// pos suffix is per-parse-site unique). Note the synthesized name is
// position-derived, so a print→parse round-trip preserves the term only
// up to α (the CNF cache absorbs the key drift via the goal-α-key
// fallback in tryCNFRefute). Untyped binders, and v when U is omitted, are
// pinned by the existing untyped-binder inference (buildQuant / buildAbs /
// buildAppViaMeta) via comprehension_spec's typing chain (its third arg = same type as
// its first).
//
// The two forms are disambiguated by probing the segment after the
// first `|` for a binder list terminated by a second `|` (backtracking
// on failure). φ can never itself contain a top-level `|` — tokPipe is
// not an operator, it only occurs inside a NESTED `{...}` — so the
// probe cannot misread a two-part φ as a binder list.
//
// A two-part form whose output is not a bare ident still errors: the
// binder list must be explicit. The printer stays consistent — it emits
// `{x | φ}` / `{t | x | φ}` ONLY for the exact shapes above (see
// matchIdentitySetBuilder / matchGeneralSetBuilder), and falls back to
// `set_comprehension(...)` otherwise.
func (p *parser) parseSetBuilderCore(output astNode, headType astType, openPos int) (astNode, *InputDiagnostic) {
	// General three-part probe. A head annotation belongs to the output in
	// this branch; if the probe fails, the same annotation belongs to the
	// identity binder below.
	save := p.pos
	if binders, ok := p.probeSetBuilderBinderList(); ok {
		return p.parseGeneralSetBuilder(output, headType, binders, openPos)
	}
	p.pos = save

	body, err := p.parseExpr()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(tokRBrace); err != nil {
		return nil, err
	}

	ov, ok := output.(*astVar)
	if !ok || len(ov.typeAnnot) > 0 {
		return nil, &InputDiagnostic{
			Position:   openPos,
			Length:     1,
			Code:       CodeParseError,
			Message:    "two-part set-builder supports only the identity form `{x | φ(x)}` (bare ident on the left)",
			Suggestion: "for a general output use the explicit binder list: `{f(x) | x | φ(x)}` (three-part, binders comma-separated)",
		}
	}
	binder := ov.name
	vName := fmt.Sprintf("GEN%%PVAR%%%d", openPos)

	// set_comprehension(λv:T. ∃x:T. comprehension_spec(v, φ, x))
	v := &astVar{name: vName, pos: openPos}
	x := &astVar{name: binder, pos: openPos}
	comprehensionSpec := &astApp{
		fun:  &astVar{name: "comprehension_spec", pos: openPos},
		args: []astNode{v, body, x},
		pos:  openPos,
	}
	exists := &astQuantNode{
		quantifier: utils.ExistsStr,
		varName:    binder,
		varType:    headType,
		body:       comprehensionSpec,
		pos:        openPos,
	}
	lambda := &astAbsNode{
		varName: vName,
		varType: headType,
		body:    exists,
		pos:     openPos,
	}
	return &astApp{
		fun:  &astVar{name: "set_comprehension", pos: openPos},
		args: []astNode{lambda},
		pos:  openPos,
	}, nil
}

// parseGeneralSetBuilder finishes the three-part form after
// probeSetBuilderBinderList consumed `x₁, …, xₙ |`: parses φ, expects
// `}`, and assembles set_comprehension(λv[:U]. ∃x₁…∃xₙ. comprehension_spec(v, φ, t)).
func (p *parser) parseGeneralSetBuilder(output astNode, outputType astType, binders []setBuilderBinder, openPos int) (astNode, *InputDiagnostic) {
	body, err := p.parseExpr()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(tokRBrace); err != nil {
		return nil, err
	}
	vName := fmt.Sprintf("GEN%%PVAR%%%d", openPos)
	v := &astVar{name: vName, pos: openPos}
	inner := astNode(&astApp{
		fun:  &astVar{name: "comprehension_spec", pos: openPos},
		args: []astNode{v, body, output},
		pos:  openPos,
	})
	for i := len(binders) - 1; i >= 0; i-- {
		inner = &astQuantNode{
			quantifier: utils.ExistsStr,
			varName:    binders[i].name,
			varType:    binders[i].typ,
			body:       inner,
			pos:        openPos,
		}
	}
	lambda := &astAbsNode{
		varName: vName,
		varType: outputType,
		body:    inner,
		pos:     openPos,
	}
	return &astApp{
		fun:  &astVar{name: "set_comprehension", pos: openPos},
		args: []astNode{lambda},
		pos:  openPos,
	}, nil
}

// makeSetEnumAST folds `{a₁, a₂, …, aₙ}` to the right-associative insert-
// chain `insert(a₁, insert(a₂, …, insert(aₙ, empty_set)))`, matching the
// canonical lowering. `insert` is polymorphic A → (A→bool) →
// (A→bool) and `empty_set` is polymorphic A → bool; buildAppViaMeta unifies A
// across the chain from the first element's type. Single-element `{a}`
// stays insert(a, empty_set) — the printer will still surface it as `{a}`
// when it detects the shape.
func makeSetEnumAST(elems []astNode, pos int) astNode {
	result := astNode(&astVar{name: "empty_set", pos: pos})
	for i := len(elems) - 1; i >= 0; i-- {
		result = &astApp{
			fun:  &astVar{name: "insert", pos: pos},
			args: []astNode{elems[i], result},
			pos:  pos,
		}
	}
	return result
}

func (p *parser) parseArgs() ([]astNode, *InputDiagnostic) {
	var args []astNode
	first, err := p.parseExpr()
	if err != nil {
		return nil, err
	}
	args = append(args, first)

	for p.peek().kind == tokComma {
		p.advance()
		arg, err := p.parseExpr()
		if err != nil {
			return nil, err
		}
		args = append(args, arg)
	}
	return args, nil
}

// ---------------------------------------------------------------------------
// AST → core.Prop builder with type inference
// ---------------------------------------------------------------------------
