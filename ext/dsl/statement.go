// statement.go — Statement, the structured spelling of a member's
// statement: its binders, its hypotheses one by one, its conclusion,
// and the abbreviations its texts spell.
//
// A member's statement is one closed proposition, `∀binders. H₁ ∧ … ∧
// Hₙ ⇒ C`, and the constructors (registry.Family.Theorem, Card,
// Sections) parse it from text. Written as one string, a statement
// with several premises is a long line; written as a Statement, the
// reader sees what is assumed and what is concluded without parsing
// it. Text assembles the one string the parser reads — the
// hypotheses ∧-joined into ONE antecedent, which a section's one
// `Fact` parameter binds (prover/proof/section.go) — and the registry
// keys the member by the proposition that string parses to, so the
// two spellings are one member.
//
// The assembly runs on the AST: each part is parsed, the parts are
// joined, and the statement printer prints the whole in the canonical
// style with the parentheses the grammar needs (a hypothesis whose
// root is a quantifier, an implication, a disjunction). SplitStatement
// is the inverse, for a text with a leading ∀-prefix and a top-level
// implication: the parts of the statement, printed canonically.

package dsl

import (
	"fmt"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/utils"
)

// Statement is a member's statement in parts. Binders is the leading
// ∀-prefix as the parser reads it (`∀L:field_on(A). ∀k:set(A). ∀t:A.`,
// possibly empty); Hypotheses the premises, one per entry, ∧-joined
// into the one antecedent (empty for a statement with none);
// Conclusion the conclusion; Abbrev the table the statement
// and its proof spell as «Name» (abbreviation.go).
//
// The binders are written out although a free variable reads as
// universal anyway, for three things the prefix carries and an implicit
// ∀ would leave to be recovered elsewhere. It declares each variable's
// type where the variable is used, not by inference or by one type per
// letter for a whole family. Its order is the order At takes witnesses
// in and a section's closure binds its parameters in, so moving a
// hypothesis never permutes a citation. And it closes the statement,
// so the statement door refuses every name it does not know, where an
// implicit ∀ would read a misspelt constant as a new variable.
//
// The hypotheses are joined to the left, as the parser joins `H₁ ∧ H₂ ∧
// H₃`, and read back along that spine: a hypothesis that is itself a
// conjunction stays one hypothesis where it stands second or later, and
// in first place reads as its conjuncts — written first, a conjunction
// is two hypotheses, and a proof binds it as two facts or as one fact
// it splits.
type Statement struct {
	Binders    string
	Hypotheses []string
	Conclusion string
	Abbrev     Abbrev
}

// Text is the one statement text the parts assemble to, in the
// canonical statement style: `Binders H₁ ∧ … ∧ Hₙ ⇒ C`, parenthesized
// as the grammar needs. The error names the part that does not parse.
func (s Statement) Text() (string, error) {
	ast, err := s.assemble()
	if err != nil {
		return "", err
	}
	var pr stmtPrinter
	out, err := pr.prop(ast)
	if err != nil {
		return "", fmt.Errorf("statement: %w", err)
	}
	back, err := parseStmtAST(out)
	if err != nil {
		return "", fmt.Errorf("statement: the assembled text does not re-parse (%q): %w", out, err)
	}
	canonGenPVars(ast)
	canonGenPVars(back)
	if !astPropEqual(ast, back) {
		return "", fmt.Errorf("statement: the assembled text changes the statement (%q)", out)
	}
	return out, nil
}

// assemble is the statement's AST: the binder prefix over the
// implication of the ∧-joined hypotheses and the conclusion.
func (s Statement) assemble() (*astProp, error) {
	if strings.TrimSpace(s.Conclusion) == "" {
		return nil, fmt.Errorf("statement: no Conclusion")
	}
	body, err := parsePartAST("Conclusion", s.Conclusion)
	if err != nil {
		return nil, err
	}
	if len(s.Hypotheses) > 0 {
		var ante astNode
		for i, h := range s.Hypotheses {
			node, err := parsePartAST(fmt.Sprintf("Hypotheses[%d]", i), h)
			if err != nil {
				return nil, err
			}
			if ante == nil {
				ante = node
				continue
			}
			ante = &astBinOp{op: utils.AndStr, left: ante, right: node, pos: node.nodePos()}
		}
		body = &astBinOp{op: utils.ImplyStr, left: ante, right: body, pos: body.nodePos()}
	}
	if strings.TrimSpace(s.Binders) != "" {
		prefix, err := parseBinderPrefix(s.Binders)
		if err != nil {
			return nil, err
		}
		innermost := prefix
		for {
			next, ok := innermost.body.(*astQuantNode)
			if !ok {
				break
			}
			innermost = next
		}
		innermost.body = body
		body = prefix
	}
	return &astProp{body: body}, nil
}

// parsePartAST reads one part of a statement — a hypothesis or the
// conclusion — as a proposition with no sequent prefix.
func parsePartAST(part, text string) (astNode, error) {
	ast, err := parseStmtAST(text)
	if err != nil {
		return nil, fmt.Errorf("statement: %s %q: %v", part, text, err)
	}
	if ast.hasTurn || len(ast.decls) > 0 {
		return nil, fmt.Errorf("statement: %s %q: a part of a statement has no ⊢", part, text)
	}
	return ast.body, nil
}

// parseBinderPrefix reads the Binders field: a chain of universal
// quantifiers and nothing else, returned as the outermost node of the
// chain, whose innermost body is ⊤ for the caller to replace.
func parseBinderPrefix(binders string) (*astQuantNode, error) {
	ast, err := parseStmtAST(binders + " " + utils.TrueStr)
	if err != nil {
		return nil, fmt.Errorf("statement: Binders %q: %v", binders, err)
	}
	outer, ok := ast.body.(*astQuantNode)
	if !ok || ast.hasTurn || len(ast.decls) > 0 {
		return nil, fmt.Errorf("statement: Binders %q is not a binder prefix — write the leading quantifiers, `∀x y:T. ∀s:set(T).`", binders)
	}
	for q := outer; ; {
		if q.quantifier != utils.ForAllStr {
			return nil, fmt.Errorf("statement: Binders %q binds with %s — a statement's leading binders are universal; an existential belongs to the conclusion", binders, q.quantifier)
		}
		next, isQ := q.body.(*astQuantNode)
		if !isQ {
			if c, isConst := q.body.(*astConst); !isConst || c.name != utils.TrueStr {
				return nil, fmt.Errorf("statement: Binders %q holds more than binders", binders)
			}
			return outer, nil
		}
		q = next
	}
}

// BinderNames is the names the statement's Binders bind, in order;
// nil when Binders is empty. The error is parseBinderPrefix's.
func (s Statement) BinderNames() ([]string, error) {
	if strings.TrimSpace(s.Binders) == "" {
		return nil, nil
	}
	prefix, err := parseBinderPrefix(s.Binders)
	if err != nil {
		return nil, err
	}
	var names []string
	for q := prefix; ; {
		names = append(names, q.varName)
		next, ok := q.body.(*astQuantNode)
		if !ok {
			return names, nil
		}
		q = next
	}
}

// AfterPrefix is the statement after prefix, where the statement opens
// as prefix does — its first binders prefix's, by name and in order,
// and its first hypotheses prefix's, in the canonical spelling
// SplitStatement prints — and false where it does not. It is the body
// a structure's door states a law from: the law's statement opens as
// the door's statement at ⊤ does (registry.Structure.Statement), and
// the body is what follows. A binder group the cut falls inside is
// split: `∀d s t:T.` after `d s` is `∀t:T.`.
func (s Statement) AfterPrefix(prefix Statement) (Statement, bool) {
	names, err := s.BinderNames()
	if err != nil {
		return Statement{}, false
	}
	first, err := prefix.BinderNames()
	if err != nil || len(first) > len(names) || !slices.Equal(names[:len(first)], first) {
		return Statement{}, false
	}
	if len(prefix.Hypotheses) > len(s.Hypotheses) || !slices.Equal(s.Hypotheses[:len(prefix.Hypotheses)], prefix.Hypotheses) {
		return Statement{}, false
	}
	rest := Statement{Hypotheses: s.Hypotheses[len(prefix.Hypotheses):], Conclusion: s.Conclusion, Abbrev: s.Abbrev}
	if len(first) == len(names) {
		return rest, true
	}
	q, err := parseBinderPrefix(s.Binders)
	if err != nil {
		return Statement{}, false
	}
	for range first {
		q = q.body.(*astQuantNode)
	}
	var pr stmtPrinter
	binders, err := pr.node(q, levExpr, true)
	if err != nil {
		return Statement{}, false
	}
	rest.Binders = strings.TrimSuffix(binders, " "+utils.TrueStr)
	return rest, true
}

// LeadingBinderNames is the names a statement text's leading ∀-prefix
// binds, in order — what the statement door exempts from the
// abbreviation capture check (ParseScope.AbbreviationBinders). nil for
// a text that does not parse or opens with no universal binder.
func LeadingBinderNames(text string) []string {
	ast, err := parseStmtAST(text)
	if err != nil {
		return nil
	}
	var names []string
	for body := ast.body; ; {
		q, isQ := body.(*astQuantNode)
		if !isQ || q.quantifier != utils.ForAllStr {
			return names
		}
		names = append(names, q.boundNames()...)
		body = q.body
	}
}

// SplitStatement reads a statement text into parts: the leading
// ∀-prefix as Binders, the top-level implication's antecedent split
// along its ∧-spine as Hypotheses, the consequent as Conclusion — each
// printed in the canonical style. A text that parses but has no
// top-level implication, or whose consequent implies again (a curried
// or interleaved statement), has no Hypotheses and its body as the
// Conclusion. The split is the inverse of Text: the parts assemble to
// the same statement (TestSplitStatementRoundTrip). ok is false for a
// text that does not parse, or one with a sequent prefix.
func SplitStatement(text string) (s Statement, ok bool) {
	ast, err := parseStmtAST(text)
	if err != nil || ast.hasTurn || len(ast.decls) > 0 {
		return Statement{}, false
	}
	return splitStatementAST(ast)
}

// CanonicalParts is text in parts (SplitStatement) where the parts
// assemble to the text's canonical spelling (FormatStmtText): the parts
// and the string are then one statement printed two ways, and either
// may stand where the other does. ok is false where they are not — the
// text does not parse or format, or its parts print otherwise — and the
// one string is the only rendering. A statement with no premise has
// parts too, with no Hypotheses.
func CanonicalParts(text string) (Statement, bool) {
	s, ok := SplitStatement(text)
	if !ok {
		return Statement{}, false
	}
	assembled, err := s.Text()
	if err != nil {
		return Statement{}, false
	}
	if canonical, err := FormatStmtText(text); err != nil || canonical != assembled {
		return Statement{}, false
	}
	return s, true
}

// StandardParts reads a statement text in the standard form, `∀xs.
// H₁ ∧ … ∧ Hₙ ⇒ C` with a conclusion that opens with neither ∀ nor ⇒,
// into its parts (SplitStatement). A text in any other form — a premise
// after the first, a binder after a premise — is refused, the error
// saying how to write it.
func StandardParts(text string) (Statement, error) {
	s, ok := SplitStatement(text)
	if !ok {
		return Statement{}, fmt.Errorf("%q does not read as a statement", text)
	}
	conclusion, err := parseStmtAST(s.Conclusion)
	if err != nil {
		return Statement{}, err
	}
	switch c := conclusion.body.(type) {
	case *astQuantNode:
		if c.quantifier == utils.ForAllStr {
			return Statement{}, fmt.Errorf("%q binds again after its premises — write every binder in front: ∀xs. H₁ ∧ … ∧ Hₙ ⇒ C", text)
		}
	case *astBinOp:
		if c.op == utils.ImplyStr {
			return Statement{}, fmt.Errorf("%q has a premise after its premises — write them as one ∧-joined antecedent: ∀xs. H₁ ∧ … ∧ Hₙ ⇒ C", text)
		}
	}
	return s, nil
}

// splitStatementAST is SplitStatement on a parsed text.
func splitStatementAST(ast *astProp) (s Statement, ok bool) {
	var pr stmtPrinter
	body := ast.body
	var binderNodes []*astQuantNode
	for {
		q, isQ := body.(*astQuantNode)
		if !isQ || q.quantifier != utils.ForAllStr {
			break
		}
		binderNodes = append(binderNodes, q)
		body = q.body
	}
	if len(binderNodes) > 0 {
		// The prefix prints as the chain over ⊤, the ⊤ dropped: the
		// printer groups `∀m n:num.` as the parser reads it back.
		last := binderNodes[len(binderNodes)-1]
		saved := last.body
		last.body = &astConst{name: utils.TrueStr, pos: last.pos}
		prefix, err := pr.node(binderNodes[0], levExpr, true)
		last.body = saved
		if err != nil {
			return Statement{}, false
		}
		s.Binders = strings.TrimSuffix(prefix, " "+utils.TrueStr)
	}
	// A curried or interleaved statement — `H₁ ⇒ H₂ ⇒ C`, `H ⇒ ∀y. H′ ⇒
	// C` — binds a Fact per premise, which the parts' one ∧-joined
	// antecedent cannot say: its premises stay in the conclusion, and
	// the parts list none.
	if imp, isImp := body.(*astBinOp); isImp && imp.op == utils.ImplyStr && !impliesAgain(imp.right) {
		for _, h := range conjunctionSpine(imp.left) {
			t, err := pr.node(h, levExpr, true)
			if err != nil {
				return Statement{}, false
			}
			s.Hypotheses = append(s.Hypotheses, t)
		}
		body = imp.right
	}
	concl, err := pr.node(body, levExpr, true)
	if err != nil {
		return Statement{}, false
	}
	s.Conclusion = concl
	return s, true
}

// impliesAgain reports whether n, its leading universal quantifiers
// stripped, is an implication: the tail of a curried or interleaved
// statement.
func impliesAgain(n astNode) bool {
	for {
		q, isQ := n.(*astQuantNode)
		if !isQ || q.quantifier != utils.ForAllStr {
			break
		}
		n = q.body
	}
	b, ok := n.(*astBinOp)
	return ok && b.op == utils.ImplyStr
}

// conjunctionSpine is the conjuncts of n along its left-associated
// ∧-spine, as the parser reads `a ∧ b ∧ c`: a parenthesized conjunct
// stays one conjunct.
func conjunctionSpine(n astNode) []astNode {
	if b, ok := n.(*astBinOp); ok && b.op == utils.AndStr && !b.parens {
		return append(conjunctionSpine(b.left), b.right)
	}
	return []astNode{n}
}
