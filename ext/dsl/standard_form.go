// standard_form.go — StandardStatement, a statement text restated in
// the standard form `∀x₁ … xₙ. H₁ ∧ … ∧ Hₘ ⇒ C`: every universal
// binder of the leading telescope in front, every antecedent's
// conjuncts one hypothesis each, and a conclusion that opens with
// neither ∀ nor ⇒.

package dsl

import (
	"fmt"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/utils"
)

// StandardStatement reads a statement text's telescope — ∀ blocks and
// ⇒ antecedents in any alternation, `∀x. H ⇒ ∀y. H′ ⇒ C` — into the
// parts of the standard form: the binders in the order the telescope
// meets them, each antecedent split along its ∧-spine into
// hypotheses in order, and what follows the telescope as the
// conclusion, each printed in the canonical style. Moving a binder in
// front of a hypothesis met before it is refused where that could
// capture: when the binder's name is already bound in front of it, or
// free in a hypothesis met before it. An abbreviation counts as
// spelling no name here: its entry may spell only the statement's
// leading binders, which the telescope binds in front of every
// hypothesis already.
func StandardStatement(text string) (Statement, error) {
	s, _, err := StandardStatementSources(text)
	return s, err
}

// StandardStatementSources is StandardStatement reporting besides, for
// each hypothesis, the index of the telescope's antecedent it came from
// — the premise a curried statement's section bound it with.
func StandardStatementSources(text string) (Statement, []int, error) {
	ast, err := parseStmtAST(text)
	if err != nil {
		return Statement{}, nil, err
	}
	if ast.hasTurn || len(ast.decls) > 0 {
		return Statement{}, nil, fmt.Errorf("a statement with a sequent prefix has no standard form")
	}
	var binders []*astQuantNode
	var hypotheses []astNode
	var sources []int
	antecedent := 0
	bound := map[string]bool{}
	body := ast.body
	for {
		if q, isQ := body.(*astQuantNode); isQ && q.quantifier == utils.ForAllStr {
			for _, name := range q.boundNames() {
				if bound[name] {
					return Statement{}, nil, fmt.Errorf("the binder %s rebinds a name the telescope binds before it", name)
				}
				for _, h := range hypotheses {
					if slices.Contains(noTable.freeNamesOf(h), name) {
						return Statement{}, nil, fmt.Errorf("the binder %s would move in front of a hypothesis where %s is free", name, name)
					}
				}
				bound[name] = true
			}
			binders = append(binders, q)
			body = q.body
			continue
		}
		if imp, isImp := body.(*astBinOp); isImp && imp.op == utils.ImplyStr {
			for _, h := range conjunctionSpine(imp.left) {
				hypotheses = append(hypotheses, h)
				sources = append(sources, antecedent)
			}
			antecedent++
			body = imp.right
			continue
		}
		break
	}
	var pr stmtPrinter
	var s Statement
	if len(binders) > 0 {
		for i := 0; i+1 < len(binders); i++ {
			binders[i].body = binders[i+1]
		}
		last := binders[len(binders)-1]
		last.body = &astConst{name: utils.TrueStr, pos: last.pos}
		prefix, err := pr.node(binders[0], levExpr, true)
		if err != nil {
			return Statement{}, nil, err
		}
		s.Binders = strings.TrimSuffix(prefix, " "+utils.TrueStr)
	}
	for _, h := range hypotheses {
		t, err := pr.node(h, levExpr, true)
		if err != nil {
			return Statement{}, nil, err
		}
		s.Hypotheses = append(s.Hypotheses, t)
	}
	conclusion, err := pr.node(body, levExpr, true)
	if err != nil {
		return Statement{}, nil, err
	}
	s.Conclusion = conclusion
	return s, sources, nil
}

// noTable reads an abbreviation as spelling no name (StandardStatement).
var noTable = &AbbreviationTable{}
