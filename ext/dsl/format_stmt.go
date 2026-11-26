// format_stmt.go — the canonical statement-text formatter.
//
// FormatStmtText re-renders a DSL proposition text in the house
// statement style:
//
//   - minimal parentheses (exactly the precedence the grammar already
//     encodes, plus the parens that keep the parser's ambiguity
//     warnings silent);
//   - grouped quantifier binders — `∀m:num.∀n:num.` folds to
//     `∀m n:num.` (the parser's grouped multi-binder form);
//   - Unicode subscripts for `_N`-suffixed names (`m_0` → `m₀` — the
//     lexer pre-normalizes both spellings to the same identifier);
//   - one space after a binder dot and around binary operators.
//
// The transformation is SYNTACTIC and self-verifying: the input is
// parsed to the AST (no type resolution, no scope — this works on any
// statement text without knowing its consts), printed, re-parsed, and
// the two ASTs compared structurally. Any mismatch — including a parse
// warning on the output, which would put an ambiguity into blessed
// text — returns an error and the caller keeps the original spelling.
// Because binder names and structure are preserved exactly, a
// successful format is guaranteed to build the identical core.Prop in
// any scope, so CNF keys, statement keys and recorded pbs are
// untouched by re-spelling a statement through this formatter.
//
// Statement texts whose surface the printer does not cover (set
// enumeration braces, exotic atoms) fail the round-trip and are left
// alone — the formatter is conservative by construction.

package dsl

import (
	"fmt"
	"strings"
)

// FormatStmtText renders raw in the canonical statement style. It
// returns an error (and the caller should keep the original text) when
// the input does not parse cleanly, the printed form does not re-parse
// to the identical AST, or the printed form parses with warnings.
func FormatStmtText(raw string) (string, error) {
	orig, err := parseStmtAST(raw)
	if err != nil {
		return "", err
	}
	var pr stmtPrinter
	out, perr := pr.prop(orig)
	if perr != nil {
		return "", perr
	}
	back, err := parseStmtAST(out)
	if err != nil {
		return "", fmt.Errorf("formatted text does not re-parse (%q): %w", out, err)
	}
	// Compare with parser-minted set-builder λ-binders canonicalized:
	// their names are position-derived (`GEN%PVAR%<open-pos>`), so any
	// respelling that moves a `{` re-mints the suffix. parser.go
	// documents this class as round-trip-stable only up to α, with the
	// CNF cache absorbing the drift; every other binder name still
	// compares exactly.
	canonGenPVars(orig)
	canonGenPVars(back)
	if !astPropEqual(orig, back) {
		return "", fmt.Errorf("formatted text changes the AST (%q)", out)
	}
	return out, nil
}

// parseStmtAST runs normalize + lex + parseProp (the scope-free front
// half of ParsePropTextInScope) and refuses inputs that parse with
// warnings or trailing tokens.
func parseStmtAST(raw string) (*astProp, error) {
	normalized, _ := NormalizeTextSymbols(raw)
	tokens, lexErr := lex(normalized)
	if lexErr != nil {
		return nil, fmt.Errorf("lex: %s", lexErr.Message)
	}
	par := &parser{tokens: tokens}
	ast, parseErr := par.parseProp()
	if parseErr != nil {
		return nil, fmt.Errorf("parse: %s", parseErr.Message)
	}
	// A warning (a chained ⇒ read right-associative) is the parser
	// saying how it read the text, not a refusal: the AST is what it
	// read, and the printer writes that reading back.
	if par.pos < len(par.tokens) && par.tokens[par.pos].kind != tokEOF {
		return nil, fmt.Errorf("trailing tokens at %q", par.tokens[par.pos].text)
	}
	return ast, nil
}

// ---------------------------------------------------------------------------
// Printer
// ---------------------------------------------------------------------------

// Precedence levels, loosest to tightest, mirroring the parser's
// recursive-descent chain (parseIff → … → parseSpine). A child whose
// own level is LOWER than the level its context requires gets
// parenthesized.
const (
	levExpr = iota // root / inside parens
	levIff
	levImpl
	levDisj
	levConj
	levRel
	levSegment
	levSetAdd
	levSetMul
	levAdd
	levSmul
	levMul
	levCompose
	levUnary
	levPow
	levApp
)

// binOpLevel maps a canonical operator string to its precedence level
// and associativity. assoc: 'l' left, 'r' right, 'n' non-associative.
func binOpLevel(op string) (lev int, assoc byte, ok bool) {
	switch op {
	case "⇔":
		return levIff, 'n', true // chained ⇔ warns — print as non-assoc
	case "⇒":
		return levImpl, 'r', true
	case "∨":
		return levDisj, 'l', true
	case "∧":
		return levConj, 'l', true
	case "=", "<", "≤", ">", "≥", "≠", "∣", "∈", "∉", "⊆", "⊊", "⟶":
		return levRel, 'n', true
	case "..":
		return levSegment, 'n', true
	case "∪", "∖":
		return levSetAdd, 'l', true
	case "∩":
		return levSetMul, 'l', true
	case "+", "-":
		return levAdd, 'l', true
	case "•":
		// The scalar action: between `+ -` and `* /`, right-associative
		// (parseSmul).
		return levSmul, 'r', true
	case "*", "/":
		// One level, left-associative — parseMultiplicative reads both
		// in the same loop, so `x / y * z` is `(x / y) * z`.
		return levMul, 'l', true
	case "∘":
		// Function composition: one level tighter than `* /`,
		// right-associative (parseCompose).
		return levCompose, 'r', true
	case "^":
		// The power: tighter than the prefix `-` and `¬`, looser than `&`
		// and application, right-associative (parsePower).
		return levPow, 'r', true
	}
	return 0, 0, false
}

type stmtPrinter struct {
	// replacements are surface candidates checked by the caller's
	// typed read-back; the ordinary formatter leaves this nil.
	replacements map[astNode]astNode
}

func (p *stmtPrinter) prop(a *astProp) (string, error) {
	var parts []string
	for i := range a.decls {
		d := &a.decls[i]
		if d.hyp != nil {
			s, err := p.node(d.hyp, levExpr, true)
			if err != nil {
				return "", err
			}
			parts = append(parts, s)
			continue
		}
		ty, err := p.typ(d.typeStr, false)
		if err != nil {
			return "", err
		}
		parts = append(parts, prettyName(d.name)+" : "+ty)
	}
	body, err := p.node(a.body, levExpr, true)
	if err != nil {
		return "", err
	}
	if a.hasTurn || len(parts) > 0 {
		return strings.Join(parts, ", ") + " ⊢ " + body, nil
	}
	return body, nil
}

// isWideBinder reports whether n is one of the forms that bind to the
// right as far as they can — the ones `node` parenthesizes off tail
// position. Kept beside that switch so the two cannot drift.
func isWideBinder(n astNode) bool {
	switch n.(type) {
	case *astQuantNode, *astAbsNode, *astPatternAbs:
		return true
	}
	return false
}

// node prints one AST node. ctxLev is the loosest level the context
// accepts bare; tail reports whether everything to the right of this
// node's text, up to the enclosing paren or end of input, belongs to
// it — the condition under which a wide-binding form (quantifier, λ)
// may print without parens.
func (p *stmtPrinter) node(n astNode, ctxLev int, tail bool) (string, error) {
	if replacement, ok := p.replacements[n]; ok {
		return p.node(replacement, ctxLev, tail)
	}
	switch n := n.(type) {
	case *astQuantNode, *astAbsNode, *astPatternAbs:
		s, err := p.wideBinder(n)
		if err != nil {
			return "", err
		}
		if !tail {
			return "(" + s + ")", nil
		}
		return s, nil

	case *astBinOp:
		lev, assoc, ok := binOpLevel(n.op)
		if !ok {
			return "", fmt.Errorf("unsupported operator %q", n.op)
		}
		leftLev, rightLev := lev+1, lev+1
		switch assoc {
		case 'l':
			leftLev = lev
		case 'r':
			rightLev = lev
		}
		// Warning-avoidance parens, beyond pure precedence: the parser
		// warns on `a ⇒ b ⇒ c` (chained ⇒) and on an unparenthesized ∧
		// as the right operand of ∨. Blessed text stays warning-free.
		if n.op == "⇒" {
			if r, isBin := n.right.(*astBinOp); isBin && r.op == "⇒" {
				rightLev = levImpl + 1
			}
		}
		if n.op == "∨" {
			if r, isBin := n.right.(*astBinOp); isBin && r.op == "∧" {
				rightLev = levConj + 1
			}
		}
		left, err := p.node(n.left, leftLev, false)
		if err != nil {
			return "", err
		}
		// A prefix form prints bare at every level, but under `^` it
		// would read as negating the power: its base is `(-x) ^ 2`.
		if n.op == "^" {
			switch n.left.(type) {
			case *astNeg, *astNotNode:
				left = "(" + left + ")"
			}
		}
		// The right operand is in tail position when the whole binop is
		// (its text runs to the binop's end), and also when the binop is
		// about to be parenthesized (the operand then runs to the `)`).
		rightTail := tail || lev < ctxLev
		// ...EXCEPT under ∧/∨, where a bare trailing quantifier is
		// unambiguous to the parser and misleading to a reader. These
		// two connectives are the ones that CHAIN — `A ∧ B ∧ C` is read
		// as a list — so a quantifier silently swallowing the rest of
		// the list destroys the only cue that its binders belong to the
		// last operand and not to the whole conjunction. `⇒` and `⇔` are
		// directional, and "everything to the right" is already how a
		// reader takes their right-hand side, so a trailing quantifier
		// there stays bare.
		//
		// This is the one place the formatter spends a paren against
		// pure minimality, and it is spent where the corpus reasons
		// about the grouping: `finite(∅) ∧ (∀x s. finite(s) ⇒ …)` is
		// name-mapped by its insert conjunct's binders, and
		// proofs cite it on exactly that basis.
		if n.op == "∧" || n.op == "∨" {
			if isWideBinder(n.right) {
				rightTail = false
			}
		}
		right, err := p.node(n.right, rightLev, rightTail)
		if err != nil {
			return "", err
		}
		s := left + " " + n.op + " " + right
		if lev < ctxLev {
			return "(" + s + ")", nil
		}
		return s, nil

	case *astCong:
		// `x ≡ y (mod m)` — relational precedence, non-associative
		// (the operands print one level tighter, like `=`'s). The
		// trailing `(mod …)` clause is self-delimiting; the modulus
		// prints at the level its parse re-accepts (parseSegment).
		left, err := p.node(n.left, levRel+1, false)
		if err != nil {
			return "", err
		}
		right, err := p.node(n.right, levRel+1, false)
		if err != nil {
			return "", err
		}
		modulus, err := p.node(n.modulus, levSegment, true)
		if err != nil {
			return "", err
		}
		s := left + " ≡ " + right + " (mod " + modulus + ")"
		if levRel < ctxLev {
			return "(" + s + ")", nil
		}
		return s, nil

	case *astTendsAt:
		// `f ⟶ l (at c)` — the congruence's shape: relational
		// precedence, non-associative, the trailing `(at …)` clause
		// self-delimiting and its point printed at the level its parse
		// re-accepts (parseSegment).
		fn, err := p.node(n.fn, levRel+1, false)
		if err != nil {
			return "", err
		}
		limit, err := p.node(n.limit, levRel+1, false)
		if err != nil {
			return "", err
		}
		point, err := p.node(n.point, levSegment, true)
		if err != nil {
			return "", err
		}
		s := fn + " ⟶ " + limit + " (" + LimitPointClause + " " + point + ")"
		if levRel < ctxLev {
			return "(" + s + ")", nil
		}
		return s, nil

	case *astNotNode:
		body, err := p.node(n.body, levUnary, tail)
		if err != nil {
			return "", err
		}
		return "¬" + body, nil

	case *astNeg:
		body, err := p.node(n.operand, levUnary, tail)
		if err != nil {
			return "", err
		}
		return "-" + body, nil

	case *astTermLit:
		return "", fmt.Errorf("a completed implicit argument has no printed form")

	case *astOutfix:
		return p.printOutfix(n)

	case *astBigOp:
		return p.printBigOp(n, ctxLev, tail)

	case *astCoerce:
		body, err := p.node(n.operand, levApp, false)
		if err != nil {
			return "", err
		}
		// `&` takes a spine; a prefix form prints bare at every level,
		// and under `&` it is bracketed: `&(-x)`, `&(&n)` (bare, `&&`
		// reads as `∧`).
		switch n.operand.(type) {
		case *astNeg, *astNotNode, *astCoerce:
			body = "(" + body + ")"
		}
		return "&" + body, nil

	case *astField:
		receiver, err := p.node(n.receiver, levApp, false)
		if err != nil {
			return "", err
		}
		switch n.receiver.(type) {
		case *astNeg, *astCoerce, *astNotNode:
			receiver = "(" + receiver + ")"
		}
		return receiver + "." + prettyName(n.name), nil
	case *astApp:
		return p.app(n)

	case *astAbbrev:
		ties, err := p.ties(n.ties)
		if err != nil {
			return "", err
		}
		return string(abbrevOpen) + n.name + string(abbrevClose) + ties, nil

	case *astVar:
		s := prettyName(n.name)
		if sugar, ok := setAtomSugar[n.name]; ok {
			s = sugar
		}
		ties, err := p.ties(n.typeAnnot)
		if err != nil {
			return "", err
		}
		return s + ties, nil

	case *astNumLit:
		return n.value.String(), nil

	case *astConst:
		return n.name, nil
	}
	return "", fmt.Errorf("unsupported AST node %T", n)
}

// wideBinder prints a quantifier, λ, or pattern-λ with its body,
// folding runs of same-quantifier same-type binders into the grouped
// form (`∀m n:num. body`). The caller decides parenthesization.
func (p *stmtPrinter) wideBinder(n astNode) (string, error) {
	switch n := n.(type) {
	case *astQuantNode:
		names := []string{prettyName(n.varName)}
		seen := map[string]bool{n.varName: true}
		tyText := ""
		var err error
		if n.varType != nil {
			tyText, err = p.typ(n.varType, true)
			if err != nil {
				return "", err
			}
		}
		body := n.body
		// ε never groups (parser refuses a second binder name there).
		if n.quantifier != "ε" {
			for {
				next, isQ := body.(*astQuantNode)
				if !isQ || next.quantifier != n.quantifier || seen[next.varName] {
					break
				}
				nextTy := ""
				if next.varType != nil {
					nextTy, err = p.typ(next.varType, true)
					if err != nil {
						return "", err
					}
				}
				if (next.varType == nil) != (n.varType == nil) || nextTy != tyText {
					break
				}
				names = append(names, prettyName(next.varName))
				seen[next.varName] = true
				body = next.body
			}
		}
		s := n.quantifier + strings.Join(names, " ")
		if n.varType != nil {
			s += ":" + tyText
		}
		bodyText, err := p.node(body, levExpr, true)
		if err != nil {
			return "", err
		}
		return s + ". " + bodyText, nil

	case *astAbsNode:
		s := "λ" + prettyName(n.varName)
		if n.varType != nil {
			ty, err := p.typ(n.varType, true)
			if err != nil {
				return "", err
			}
			s += ":" + ty
		}
		body, err := p.node(n.body, levExpr, true)
		if err != nil {
			return "", err
		}
		return s + ". " + body, nil

	case *astPatternAbs:
		pat, err := p.pat(n.pat)
		if err != nil {
			return "", err
		}
		body, err := p.node(n.body, levExpr, true)
		if err != nil {
			return "", err
		}
		return "λ" + pat + ". " + body, nil
	}
	return "", fmt.Errorf("not a wide binder: %T", n)
}

func (p *stmtPrinter) pat(a *astPat) (string, error) {
	if a.isLeaf() {
		s := prettyName(a.name)
		if a.ty != nil {
			ty, err := p.typ(a.ty, true)
			if err != nil {
				return "", err
			}
			s += ":" + ty
		}
		return s, nil
	}
	l, err := p.pat(a.left)
	if err != nil {
		return "", err
	}
	r, err := p.pat(a.right)
	if err != nil {
		return "", err
	}
	return "(" + l + ", " + r + ")", nil
}

// setAtomSugar re-sugars the nullary set consts the PARSER lowers to
// bare names (`∅` → astVar{"empty_set"}, `𝕌` → astVar{"universe"}; parser.go's
// tokEmpty/tokUniv branches). Without it the formatter's "canonical"
// form spelled the lowered name, so re-formatting a set chapter turned
// its mathematics back into constant names — which is what kept the
// tool from being run on those families at all.
//
// The rewrite is safe in BOTH directions because the lowering is total:
// a source `empty_set` and a source `∅` parse to the identical node, so the
// resolver pre-seed and the surface fallback (setops.go) see the same
// name either way, and the two spellings build the same Prop in the
// same scope.
var setAtomSugar = map[string]string{
	"empty_set": "∅",
	"universe":  "𝕌",
}

// setPrefixSugar re-sugars the unary big-ops, which the parser lowers to
// a one-argument application (`⋃f` → big_union(f); parseSetPrefixOp).
var setPrefixSugar = map[string]string{
	"big_union":        "⋃",
	"big_intersection": "⋂",
}

// setPrefixOperandOK reports whether a printed operand can carry a
// big-op prefix. It mirrors parseSetPrefixOp's own token test — the
// prefix binds ONE SPINE and only when the next token is an identifier,
// `{`, or another set atom — so an operand that would need parens
// (an infix expression, a tuple, a numeral) keeps the call form
// instead. Getting this wrong is not a soundness risk (the round-trip
// gate rejects the output and the caller keeps the original text), but
// a declined format is a silent no-op, so the test is worth making
// exact rather than approximate.
func setPrefixOperandOK(s string) bool {
	if s == "" {
		return false
	}
	r := []rune(s)[0]
	switch r {
	case '{', '∅', '𝕌', '⋃', '⋂':
		return true
	}
	return r == '_' || (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z')
}

// app prints an application. Pairs — right-nested applications of the
// `,` constructor — print as tuple literals `(a, b, c)`; the unary
// big-ops print in their prefix sugar; everything else prints in the
// corpus's paren-call form `f(a, b)`.
func (p *stmtPrinter) app(n *astApp) (string, error) {
	if n.dims > 0 {
		return p.dimensioned(n)
	}
	if op, arg, ok := p.setPrefixApp(n); ok {
		operand, err := p.node(arg, levApp, false)
		if err != nil {
			return "", err
		}
		if setPrefixOperandOK(operand) {
			return op + operand, nil
		}
	}
	if s, ok, err := p.setBuilder(n); ok || err != nil {
		return s, err
	}
	if elems, isEnum := setEnumElements(n); isEnum {
		var parts []string
		for _, e := range elems {
			s, err := p.node(e, levExpr, true)
			if err != nil {
				return "", err
			}
			parts = append(parts, s)
		}
		return "{" + strings.Join(parts, ", ") + "}", nil
	}
	if comps, isPair := pairComponents(n); isPair {
		var parts []string
		for _, c := range comps {
			s, err := p.node(c, levExpr, true)
			if err != nil {
				return "", err
			}
			parts = append(parts, s)
		}
		return "(" + strings.Join(parts, ", ") + ")", nil
	}
	var fun string
	var err error
	switch f := n.fun.(type) {
	case *astVar, *astApp, *astField, *astAbbrev:
		fun, err = p.node(f, levApp, false)
	default:
		fun, err = p.node(f, levExpr, true)
		fun = "(" + fun + ")"
	}
	if err != nil {
		return "", err
	}
	var args []string
	for _, a := range n.args {
		s, err := p.node(a, levExpr, true)
		if err != nil {
			return "", err
		}
		args = append(args, s)
	}
	return fun + "(" + strings.Join(args, ", ") + ")", nil
}

// setPrefixApp recognizes a big-op application — an un-annotated
// big_union/big_intersection head applied to exactly one argument — and returns its
// sugar symbol and operand. A type annotation (`⋃⟨A:num⟩`) keeps the
// call form: the sugar carries its annotation on the SYMBOL, and
// re-sugaring that correctly is a spelling this corpus has never
// needed.
func (p *stmtPrinter) setPrefixApp(n *astApp) (op string, arg astNode, ok bool) {
	f, isVar := n.fun.(*astVar)
	if !isVar || len(f.typeAnnot) > 0 || len(n.args) != 1 {
		return "", nil, false
	}
	sym, isBigOp := setPrefixSugar[f.name]
	if !isBigOp {
		return "", nil, false
	}
	return sym, n.args[0], true
}

// setEnumElements recognizes the enumeration literal's lowering — a
// right-nested insert chain bottoming out in empty_set (makeSetEnumAST) —
// and returns its elements.
//
// The empty_set tail is the whole test, and it is what separates a LITERAL
// from the `insert(x, s)` idiom that adds an element to an arbitrary
// set. `insert(a, s)` is not `{a}` and must keep its call form; only a
// chain that terminates in the empty set is a brace literal.
func setEnumElements(n *astApp) ([]astNode, bool) {
	var elems []astNode
	cur := astNode(n)
	for {
		app, isApp := cur.(*astApp)
		if !isApp {
			break
		}
		f, isVar := app.fun.(*astVar)
		if !isVar || f.name != "insert" || len(f.typeAnnot) > 0 || len(app.args) != 2 {
			return nil, false
		}
		elems = append(elems, app.args[0])
		cur = app.args[1]
	}
	tail, isVar := cur.(*astVar)
	if !isVar || tail.name != "empty_set" || len(tail.typeAnnot) > 0 {
		return nil, false
	}
	return elems, len(elems) > 0
}

// pairComponents flattens a right-nested `,`-application chain into
// its component list; reports false when n is not a pair.
func pairComponents(n *astApp) ([]astNode, bool) {
	f, isVar := n.fun.(*astVar)
	if !isVar || f.name != "," || len(f.typeAnnot) > 0 || len(n.args) != 2 {
		return nil, false
	}
	if inner, isApp := n.args[1].(*astApp); isApp {
		if rest, isPair := pairComponents(inner); isPair {
			return append([]astNode{n.args[0]}, rest...), true
		}
	}
	return []astNode{n.args[0], n.args[1]}, true
}

// typ prints a type expression. In annotation position (after a binder
// or decl `:`), a function type keeps its enclosing parens — the
// corpus's `∀P:(num → num).` spelling — so the trailing binder dot
// never abuts a bare arrow chain.
// ties prints a `⟨A:T, …⟩` suffix — a constant's or an abbreviation's
// — or nothing for none.
func (p *stmtPrinter) ties(annot []typeAnnotBinding) (string, error) {
	if len(annot) == 0 {
		return "", nil
	}
	bs := make([]string, len(annot))
	for i := range annot {
		ty, err := p.typ(annot[i].ty, false)
		if err != nil {
			return "", err
		}
		bs[i] = annot[i].varName + ":" + ty
	}
	return "⟨" + strings.Join(bs, ", ") + "⟩", nil
}

func (p *stmtPrinter) typ(t astType, annotation bool) (string, error) {
	switch t := t.(type) {
	case *astTypeVar:
		return t.name, nil
	case *astTypeNamed:
		if len(t.args) == 0 {
			return t.name, nil
		}
		var args []string
		for _, a := range t.args {
			s, err := p.typ(a, false)
			if err != nil {
				return "", err
			}
			args = append(args, s)
		}
		return t.name + "(" + strings.Join(args, ", ") + ")", nil
	case *astTypeFun:
		dom, err := p.typ(t.domain, false)
		if err != nil {
			return "", err
		}
		if _, isFun := t.domain.(*astTypeFun); isFun {
			dom = "(" + dom + ")"
		}
		cod, err := p.typ(t.codomain, false)
		if err != nil {
			return "", err
		}
		s := dom + " → " + cod
		if annotation {
			s = "(" + s + ")"
		}
		return s, nil
	}
	return "", fmt.Errorf("unsupported type node %T", t)
}

// prettyName renders a trailing `_N` digit suffix as Unicode
// subscripts (`m_0` → `m₀`, `B_12` → `B₁₂`) — the display form the
// lexer pre-normalizes back, so both spellings are the same
// identifier. A field written on a name is one identifier whose
// segments the dots separate (`M_0.carrier`, parseAtom and fieldNode),
// and each segment is rendered: the receiver of a projection spells
// its subscript as the same name does on its own. The bare numeral
// const `_0` (no leading name) is left alone.
func prettyName(name string) string {
	if head, field, isField := strings.Cut(name, "."); isField {
		return prettyName(head) + "." + prettyName(field)
	}
	i := strings.LastIndex(name, "_")
	if i <= 0 {
		return name
	}
	suffix := name[i+1:]
	if suffix == "" {
		return name
	}
	for _, r := range suffix {
		if r < '0' || r > '9' {
			return name
		}
	}
	var sb strings.Builder
	sb.WriteString(name[:i])
	for _, r := range suffix {
		sb.WriteRune(rune(0x2080 + (r - '0')))
	}
	return sb.String()
}

// ---------------------------------------------------------------------------
// Structural AST equality (positions, paren flags and lazily-resolved
// type stashes ignored)
// ---------------------------------------------------------------------------

func astPropEqual(a, b *astProp) bool {
	if a.hasTurn != b.hasTurn || len(a.decls) != len(b.decls) {
		return false
	}
	for i := range a.decls {
		da, db := &a.decls[i], &b.decls[i]
		if da.name != db.name {
			return false
		}
		if (da.typeStr == nil) != (db.typeStr == nil) ||
			(da.typeStr != nil && !astTypeEqual(da.typeStr, db.typeStr)) {
			return false
		}
		if (da.hyp == nil) != (db.hyp == nil) ||
			(da.hyp != nil && !astNodeEqual(da.hyp, db.hyp)) {
			return false
		}
	}
	return astNodeEqual(a.body, b.body)
}

// tiesEqual reports whether two `⟨A:T, …⟩` suffixes bind the same
// letters to the same types, in order.
func tiesEqual(a, b []typeAnnotBinding) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i].varName != b[i].varName || !astTypeEqual(a[i].ty, b[i].ty) {
			return false
		}
	}
	return true
}

func astNodeEqual(a, b astNode) bool {
	switch a := a.(type) {
	case *astAbbrev:
		b, ok := b.(*astAbbrev)
		return ok && a.name == b.name && tiesEqual(a.ties, b.ties)
	case *astVar:
		b, ok := b.(*astVar)
		return ok && a.name == b.name && tiesEqual(a.typeAnnot, b.typeAnnot)
	case *astField:
		b, ok := b.(*astField)
		return ok && a.name == b.name && astNodeEqual(a.receiver, b.receiver)
	case *astApp:
		b, ok := b.(*astApp)
		if !ok || len(a.args) != len(b.args) || a.dims != b.dims || !astNodeEqual(a.fun, b.fun) {
			return false
		}
		for i := range a.args {
			if !astNodeEqual(a.args[i], b.args[i]) {
				return false
			}
		}
		return true
	case *astNumLit:
		b, ok := b.(*astNumLit)
		return ok && a.value.Cmp(b.value) == 0
	case *astBinOp:
		b, ok := b.(*astBinOp)
		return ok && a.op == b.op && astNodeEqual(a.left, b.left) && astNodeEqual(a.right, b.right)
	case *astCong:
		b, ok := b.(*astCong)
		return ok && astNodeEqual(a.left, b.left) && astNodeEqual(a.right, b.right) &&
			astNodeEqual(a.modulus, b.modulus)
	case *astTendsAt:
		b, ok := b.(*astTendsAt)
		return ok && astNodeEqual(a.fn, b.fn) && astNodeEqual(a.limit, b.limit) &&
			astNodeEqual(a.point, b.point)
	case *astNotNode:
		b, ok := b.(*astNotNode)
		return ok && astNodeEqual(a.body, b.body)
	case *astNeg:
		b, ok := b.(*astNeg)
		return ok && astNodeEqual(a.operand, b.operand)
	case *astCoerce:
		b, ok := b.(*astCoerce)
		return ok && astNodeEqual(a.operand, b.operand)
	case *astQuantNode:
		b, ok := b.(*astQuantNode)
		if !ok || a.quantifier != b.quantifier || a.varName != b.varName {
			return false
		}
		if (a.varType == nil) != (b.varType == nil) ||
			(a.varType != nil && !astTypeEqual(a.varType, b.varType)) {
			return false
		}
		return astNodeEqual(a.body, b.body)
	case *astAbsNode:
		b, ok := b.(*astAbsNode)
		if !ok || a.varName != b.varName {
			return false
		}
		if (a.varType == nil) != (b.varType == nil) ||
			(a.varType != nil && !astTypeEqual(a.varType, b.varType)) {
			return false
		}
		return astNodeEqual(a.body, b.body)
	case *astPatternAbs:
		b, ok := b.(*astPatternAbs)
		return ok && astPatEqual(a.pat, b.pat) && astNodeEqual(a.body, b.body)
	case *astConst:
		b, ok := b.(*astConst)
		return ok && a.name == b.name
	case *astTermLit:
		b, ok := b.(*astTermLit)
		return ok && a.term.Equals(b.term)
	case *astOutfix:
		b, ok := b.(*astOutfix)
		if !ok || a.open != b.open || a.close != b.close || len(a.args) != len(b.args) || (a.sub == nil) != (b.sub == nil) {
			return false
		}
		for i := range a.args {
			if !astNodeEqual(a.args[i], b.args[i]) {
				return false
			}
		}
		return a.sub == nil || astNodeEqual(a.sub, b.sub)
	case *astBigOp:
		b, ok := b.(*astBigOp)
		return ok && a.symbol == b.symbol && a.binder == b.binder && a.rel == b.rel &&
			astNodeEqual(a.bound, b.bound) && astNodeEqual(a.body, b.body)
	}
	return false
}

func astPatEqual(a, b *astPat) bool {
	if a.isLeaf() != b.isLeaf() {
		return false
	}
	if a.isLeaf() {
		if a.name != b.name {
			return false
		}
		if (a.ty == nil) != (b.ty == nil) {
			return false
		}
		return a.ty == nil || astTypeEqual(a.ty, b.ty)
	}
	return astPatEqual(a.left, b.left) && astPatEqual(a.right, b.right)
}

func astTypeEqual(a, b astType) bool {
	switch a := a.(type) {
	case *astTypeVar:
		b, ok := b.(*astTypeVar)
		return ok && a.name == b.name
	case *astTypeFun:
		b, ok := b.(*astTypeFun)
		return ok && astTypeEqual(a.domain, b.domain) && astTypeEqual(a.codomain, b.codomain)
	case *astTypeNamed:
		b, ok := b.(*astTypeNamed)
		if !ok || a.name != b.name || len(a.args) != len(b.args) {
			return false
		}
		for i := range a.args {
			if !astTypeEqual(a.args[i], b.args[i]) {
				return false
			}
		}
		return true
	}
	return false
}

// ---------------------------------------------------------------------------
// Set-builder re-sugaring + GEN%PVAR% canonicalization
// ---------------------------------------------------------------------------

// genPVarPrefix is the parser's synthesized set-builder λ-binder name
// class (parseSetBuilderCore): `GEN%PVAR%<open-pos>`, position-derived.
// Position-derived means SPELLING-derived:
// any respelling that moves the `{` mints a different suffix, so these
// names are stable only up to α — which parser.go documents as this
// class's round-trip contract (the CNF cache absorbs the drift via the
// goal-α-key fallback in tryCNFRefute). The formatter therefore (a)
// prints the sugar back for the exact lowered shapes, and (b) compares
// round-trip ASTs with this one name class canonicalized.
const genPVarPrefix = "GEN%PVAR%"

// setBuilder recognizes the two lowered set-builder shapes
// parseSetBuilderCore produces and prints their surface form back.
// Returns ok=false for anything else — including a set_comprehension whose λ-binder
// is not parser-synthesized (a hand-named binder is not in the α-free
// class, so re-sugaring it could not round-trip) — in which case the
// caller prints the raw application form.
//
//	set_comprehension(λv:T. ∃x:T. comprehension_spec(v, φ, x))          ↦  {x:T | φ}
//	set_comprehension(λv:U. ∃x₁:T₁…∃xₙ:Tₙ. comprehension_spec(v, φ, t)) ↦  {t:U | x₁:T₁, …, xₙ:Tₙ | φ}
//
// Types print exactly where the AST carries them (the parser puts the
// identity form's annotation on BOTH binders, and leaves both nil in
// the untyped form), so the printed text re-lowers to the same
// typed/untyped shape.
func (p *stmtPrinter) setBuilder(n *astApp) (string, bool, error) {
	f, isVar := n.fun.(*astVar)
	if !isVar || f.name != "set_comprehension" || len(f.typeAnnot) > 0 || len(n.args) != 1 {
		return "", false, nil
	}
	lam, isAbs := n.args[0].(*astAbsNode)
	if !isAbs || !strings.HasPrefix(lam.varName, genPVarPrefix) {
		return "", false, nil
	}
	var binders []*astQuantNode
	body := lam.body
	for {
		q, isQ := body.(*astQuantNode)
		if !isQ || q.quantifier != "∃" {
			break
		}
		binders = append(binders, q)
		body = q.body
	}
	if len(binders) == 0 {
		return "", false, nil
	}
	ss, isApp := body.(*astApp)
	if !isApp || len(ss.args) != 3 {
		return "", false, nil
	}
	sf, isVar := ss.fun.(*astVar)
	if !isVar || sf.name != "comprehension_spec" || len(sf.typeAnnot) > 0 {
		return "", false, nil
	}
	v0, isVar := ss.args[0].(*astVar)
	if !isVar || v0.name != lam.varName || len(v0.typeAnnot) > 0 {
		return "", false, nil
	}
	phi, out := ss.args[1], ss.args[2]

	sameType := func(a, b astType) bool {
		if (a == nil) != (b == nil) {
			return false
		}
		return a == nil || astTypeEqual(a, b)
	}

	// Identity form: one binder, the output is that binder bare, and the
	// λ carries the binder's own annotation (both nil in the untyped
	// form) — exactly what parseSetBuilderCore's two-part branch mints.
	if len(binders) == 1 {
		if ov, isv := out.(*astVar); isv && ov.name == binders[0].varName &&
			len(ov.typeAnnot) == 0 && sameType(lam.varType, binders[0].varType) {
			phiText, err := p.node(phi, levExpr, true)
			if err != nil {
				return "", false, err
			}
			s := "{" + prettyName(binders[0].varName)
			if binders[0].varType != nil {
				ty, err := p.typ(binders[0].varType, false)
				if err != nil {
					return "", false, err
				}
				s += ":" + ty
			}
			return s + " | " + phiText + "}", true, nil
		}
	}

	// General form: explicit binder list, arbitrary output expression.
	outText, err := p.node(out, levExpr, true)
	if err != nil {
		return "", false, err
	}
	head := "{" + outText
	if lam.varType != nil {
		ty, err := p.typ(lam.varType, false)
		if err != nil {
			return "", false, err
		}
		head += ":" + ty
	}
	var bs []string
	for _, q := range binders {
		b := prettyName(q.varName)
		if q.varType != nil {
			ty, err := p.typ(q.varType, false)
			if err != nil {
				return "", false, err
			}
			b += ":" + ty
		}
		bs = append(bs, b)
	}
	phiText, err := p.node(phi, levExpr, true)
	if err != nil {
		return "", false, err
	}
	return head + " | " + strings.Join(bs, ", ") + " | " + phiText + "}", true, nil
}

// canonGenPVars α-canonicalizes every BOUND binder whose name carries
// the parser-synthesized genPVarPrefix, renaming it (and its bound
// occurrences) to `GEN%PVAR%#<k>` in walk order. Binders outside the
// class are untouched, and a free occurrence of a prefixed name (never
// parser-produced, but writable by hand) is left alone — so two ASTs
// compare equal after canonicalization exactly when they are identical
// up to the spelling of parser-minted set-builder binders, the one
// name class parser.go documents as position-derived.
func canonGenPVars(pr *astProp) {
	c := &genPVarCanon{env: map[string]string{}}
	for i := range pr.decls {
		if pr.decls[i].hyp != nil {
			c.walk(pr.decls[i].hyp)
		}
	}
	c.walk(pr.body)
}

type genPVarCanon struct {
	env  map[string]string // in-scope renames, old → canonical
	next int
}

func (c *genPVarCanon) bind(name string) (string, func()) {
	if !strings.HasPrefix(name, genPVarPrefix) {
		// A non-class binder SHADOWS any outer class rename of the same
		// name for its scope.
		if old, had := c.env[name]; had {
			delete(c.env, name)
			return name, func() { c.env[name] = old }
		}
		return name, func() {}
	}
	canon := fmt.Sprintf("%s#%d", genPVarPrefix, c.next)
	c.next++
	old, had := c.env[name]
	c.env[name] = canon
	return canon, func() {
		if had {
			c.env[name] = old
		} else {
			delete(c.env, name)
		}
	}
}

func (c *genPVarCanon) walk(n astNode) {
	switch n := n.(type) {
	case *astVar:
		if canon, has := c.env[n.name]; has {
			n.name = canon
		}
	case *astOutfix:
		for _, a := range n.args {
			c.walk(a)
		}
		if n.sub != nil {
			c.walk(n.sub)
		}
	case *astField:
		c.walk(n.receiver)
	case *astApp:
		c.walk(n.fun)
		for _, a := range n.args {
			c.walk(a)
		}
	case *astBinOp:
		c.walk(n.left)
		c.walk(n.right)
	case *astCong:
		c.walk(n.left)
		c.walk(n.right)
		c.walk(n.modulus)
	case *astTendsAt:
		c.walk(n.fn)
		c.walk(n.limit)
		c.walk(n.point)
	case *astNotNode:
		c.walk(n.body)
	case *astNeg:
		c.walk(n.operand)
	case *astCoerce:
		c.walk(n.operand)
	case *astQuantNode:
		canon, restore := c.bind(n.varName)
		n.varName = canon
		c.walk(n.body)
		restore()
	case *astAbsNode:
		canon, restore := c.bind(n.varName)
		n.varName = canon
		c.walk(n.body)
		restore()
	case *astBigOp:
		c.walk(n.bound)
		canon, restore := c.bind(n.binder)
		n.binder = canon
		c.walk(n.body)
		restore()
	case *astPatternAbs:
		var restores []func()
		var bindPat func(p *astPat)
		bindPat = func(p *astPat) {
			if p == nil {
				return
			}
			if p.isLeaf() {
				canon, restore := c.bind(p.name)
				p.name = canon
				restores = append(restores, restore)
				return
			}
			bindPat(p.left)
			bindPat(p.right)
		}
		bindPat(n.pat)
		c.walk(n.body)
		for i := len(restores) - 1; i >= 0; i-- {
			restores[i]()
		}
	}
}
