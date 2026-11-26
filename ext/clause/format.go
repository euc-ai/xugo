package clause

import (
	"fmt"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

func FormatClause(c *Clause) string {
	s := ""
	for v := range c.univBoundVars.Iter() {
		s += fmt.Sprintf("∀%s.", ext.PrintTerm(v))
	}
	if c.univBoundVars.Size() > 0 {
		s += "\n"
	}
	if c.EffectiveNumLits() > 0 {
		var pos, neg []string
		for _, t := range c.Lits() {
			if MatchesNOT(t) != nil {
				neg = append(neg, ext.PrintTerm(t))
			} else {
				pos = append(pos, ext.PrintTerm(t))
			}
		}
		connected := strings.Join(append(neg, pos...), " | ")
		if c.univBoundVars.Size() > 0 {
			connected = prop.AddTab(connected)
		}
		s += connected
	}
	return s
}

func (c *Clause) String() string { return FormatClause(c) }

func FormatClauseThm(conclusion *Clause, hypClauses []*Clause) string {
	s := ""
	hyps := make([]string, len(hypClauses))
	for i, c := range hypClauses {
		hyps[i] = c.String()
	}
	if len(hypClauses) > 0 {
		slices.Sort(hyps)
		s = strings.Join(hyps, ",\n")
		s = s + "\n"
	}

	c := utils.TurnstileStr + " " + conclusion.String()

	if len(hypClauses) > 0 {
		c = prop.AddTab(c)
	}
	s += c
	return s
}

func (t *ClauseThm) String() string {
	return FormatClauseThm(t.conclusion, t.hypClauses)
}

func FormatConjunctiveClauses(
	groundVars *VarList,
	clauses []*Clause) string {
	s := ""
	for v := range groundVars.Iter() {
		s += fmt.Sprintf("%s:%s, ", ext.PrintTerm(v), ext.FormatType(v.Type()))
	}
	if groundVars.Size() > 0 {
		s = strings.TrimSuffix(s, " ")
		s += "\n"
	}
	for _, ci := range clauses {
		ciString := ci.String()
		if groundVars.Size() > 0 {
			ciString = prop.AddTab(ciString)
		}
		s += ciString + "\n"
	}
	s = strings.TrimSuffix(s, "\n")
	return s
}

func (c *CNFClauses) String() string {
	return FormatConjunctiveClauses(&c.groundVars, c.clauses)
}
