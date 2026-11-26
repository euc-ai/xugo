package reify

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// Equation is a definition stated as a proposition
// ∀x₁ … xₖ. c(x₁, …, xₖ) = body, or ⇔ body, with the name of the
// member that states it.
type Equation struct {
	Lemma     string
	Statement core.Term
}

// _UnfoldRule is an equation read for unfolding: the constant at its
// stated type, the distinct bound variables its left side applies it
// to, and the body.
type _UnfoldRule struct {
	lemma     string
	constant  core.ConstTerm
	variables []core.VarTerm
	body      core.Term
}

type _EquationUnfolder struct {
	rules []_UnfoldRule
}

// EquationUnfolder is an Unfolder over the given equations: an
// application of one of their constants to as many arguments as the
// equation binds unfolds to the body at those arguments, the
// equation's type variables instantiated as the application's
// constant is. An equation whose left side is not a constant applied
// to distinct bound variables is no unfolding rule and is refused.
func EquationUnfolder(equations ...Equation) Unfolder {
	u := &_EquationUnfolder{}
	for _, e := range equations {
		u.rules = append(u.rules, readUnfoldRule(e))
	}
	return u
}

func readUnfoldRule(e Equation) _UnfoldRule {
	list, body := ext.DecomposesFORALL(e.Statement)
	left, right, ok := core.MatchesEQ(body)
	if !ok {
		panic(fmt.Sprintf("reify: the equation of %s is not an equation: %s", e.Lemma, ext.PrintTerm(e.Statement)))
	}
	head, args := ext.MatchesApply(left)
	constant, isConst := head.AsConst()
	if !isConst {
		panic(fmt.Sprintf("reify: the equation of %s applies no constant: %s", e.Lemma, ext.PrintTerm(e.Statement)))
	}
	variables := make([]core.VarTerm, len(args))
	for i, a := range args {
		v, isVar := a.AsVar()
		if !isVar || !list.Has(v) {
			panic(fmt.Sprintf("reify: the equation of %s is not applied to its bound variables: %s", e.Lemma, ext.PrintTerm(e.Statement)))
		}
		for _, earlier := range variables[:i] {
			if earlier.EqualsVar(v) {
				panic(fmt.Sprintf("reify: the equation of %s repeats a variable: %s", e.Lemma, ext.PrintTerm(e.Statement)))
			}
		}
		variables[i] = v
	}
	return _UnfoldRule{lemma: e.Lemma, constant: constant, variables: variables, body: right}
}

func (u *_EquationUnfolder) Unfold(t core.Term) (core.Term, string, bool) {
	head, args := ext.MatchesApply(t)
	c, isConst := head.AsConst()
	if !isConst {
		return nil, "", false
	}
	for _, rule := range u.rules {
		if rule.constant.Name() != c.Name() || len(args) != len(rule.variables) {
			continue
		}
		var substs []core.TypeSubst
		if !rule.constant.Type().Equals(c.Type()) {
			var ok bool
			substs, ok = rule.constant.Type().Matches(c.Type(), utils.FullPredicate)
			if !ok {
				continue
			}
		}
		body := rule.body.TypeSubstitute(substs...)
		termSubsts := make([]core.TermSubst, len(args))
		for i, v := range rule.variables {
			instance, _ := v.TypeSubstitute(substs...).AsVar()
			termSubsts[i] = core.MakeTermSubst(instance, args[i])
		}
		return body.Substitute(termSubsts...), rule.lemma, true
	}
	return nil, "", false
}
