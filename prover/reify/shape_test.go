package reify

import (
	"fmt"
	"slices"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

func sortStrings(s []string) { sort.Strings(s) }

// expandAll unfolds every application the unfolder knows, everywhere
// in the term, until none is left: the hand-written formula families
// are nests of defined constants over the four constructors.
func expandAll(t core.Term, u Unfolder) core.Term {
	for {
		body, _, ok := u.Unfold(t)
		if !ok {
			break
		}
		t = body
	}
	switch s := t.(type) {
	case core.AppliedTerm:
		return core.Apply(expandAll(s.Fun(), u), expandAll(s.Arg(), u))
	case core.AbsTerm:
		return core.Abs(s.Var(), expandAll(s.Body(), u))
	}
	return t
}

// _NatPolynomial is a polynomial over num terms with integer
// coefficients, keyed by its monomials: a sorted product of symbols
// joined by "·", "" for the constant. Variables and applications the
// arithmetic does not read are symbols.
type _NatPolynomial map[string]int64

func natPolynomial(t core.Term) _NatPolynomial {
	if value, ok := ext.NumeralValue(t); ok {
		return _NatPolynomial{"": value.Int64()}
	}
	head, args := ext.MatchesApply(t)
	if c, ok := head.AsConst(); ok && len(args) == 2 {
		switch c.Name() {
		case "+":
			return natPolynomial(args[0]).add(natPolynomial(args[1]))
		case "*":
			return natPolynomial(args[0]).mul(natPolynomial(args[1]))
		}
	}
	return _NatPolynomial{ext.FormatTermForParser(t): 1}
}

func (p _NatPolynomial) add(q _NatPolynomial) _NatPolynomial {
	out := _NatPolynomial{}
	for m, c := range p {
		out[m] += c
	}
	for m, c := range q {
		out[m] += c
	}
	return out
}

func (p _NatPolynomial) mul(q _NatPolynomial) _NatPolynomial {
	out := _NatPolynomial{}
	for m1, c1 := range p {
		for m2, c2 := range q {
			factors := slices.DeleteFunc(append(strings.Split(m1, "·"), strings.Split(m2, "·")...), func(s string) bool { return s == "" })
			sort.Strings(factors)
			out[strings.Join(factors, "·")] += c1 * c2
		}
	}
	return out
}

func (p _NatPolynomial) String() string {
	var terms []string
	for m, c := range p {
		if c == 0 {
			continue
		}
		switch {
		case m == "":
			terms = append(terms, fmt.Sprint(c))
		case c == 1:
			terms = append(terms, m)
		default:
			terms = append(terms, fmt.Sprintf("%d·%s", c, m))
		}
	}
	sort.Strings(terms)
	if len(terms) == 0 {
		return "0"
	}
	return strings.Join(terms, " + ")
}

// skeleton renders a formula's shape with its names erased: every
// atom "a", the theories' true formulas "⊤", adjacent quantifier
// blocks of one kind merged into one block whose length is written as
// a normalized polynomial, conjunctions flattened and sorted with ⊤
// dropped, and a finite conjunction as "⋀[length]" over its body. Two
// formulas with one skeleton have the same block structure, quantifier
// prefix and atom count.
func skeleton(t core.Term) string {
	head, args := ext.MatchesApply(t)
	c, ok := head.AsConst()
	if !ok {
		return "?" + ext.FormatTermForParser(t)
	}
	switch c.Name() {
	case "fo_atom", "ring_equality_formula":
		return "a"
	case "polynomial_weak_inequality_formula":
		return "¬a"
	case "ordered_ring_equality_formula":
		return "∧[¬a ¬a]"
	case "ring_true_formula", "ordered_ring_true_formula":
		return "⊤"
	case "fo_not":
		inner := skeleton(args[0])
		if inner == "⊤" {
			return "⊥"
		}
		return "¬" + inner
	case "fo_and", "fo_or":
		var parts []string
		for _, conjunct := range flattenBinary(t, c.Name()) {
			if s := skeleton(conjunct); s != "⊤" || c.Name() == "fo_or" {
				parts = append(parts, s)
			}
		}
		sort.Strings(parts)
		switch {
		case len(parts) == 0:
			return "⊤"
		case len(parts) == 1:
			return parts[0]
		}
		symbol := "∧"
		if c.Name() == "fo_or" {
			symbol = "∨"
		}
		return symbol + "[" + strings.Join(parts, " ") + "]"
	case "fo_implies":
		return "(" + skeleton(args[0]) + " ⇒ " + skeleton(args[1]) + ")"
	case "fo_iff":
		return "(" + skeleton(args[0]) + " ⇔ " + skeleton(args[1]) + ")"
	case "fo_forall", "fo_all_range", "fo_exists", "fo_exists_range":
		symbol, body, length := quantifierBlock(t)
		return symbol + "[" + length.String() + "]" + skeleton(body)
	case "fo_conjoin":
		abs, isAbs := args[2].AsAbsTerm()
		if !isAbs {
			return "?conjoin"
		}
		return "⋀[" + natPolynomial(args[1]).String() + "]" + skeleton(abs.Body())
	}
	return "?" + string(c.Name())
}

func flattenBinary(t core.Term, name core.TermName) []core.Term {
	head, args := ext.MatchesApply(t)
	if c, ok := head.AsConst(); ok && c.Name() == name && len(args) == 2 {
		return append(flattenBinary(args[0], name), flattenBinary(args[1], name)...)
	}
	return []core.Term{t}
}

// quantifierBlock merges the quantifiers of one kind at the head of t
// into one block: the symbol, the body under them, and the total
// length.
func quantifierBlock(t core.Term) (string, core.Term, _NatPolynomial) {
	symbolOf := func(name core.TermName) string {
		switch name {
		case "fo_forall", "fo_all_range":
			return "∀"
		case "fo_exists", "fo_exists_range":
			return "∃"
		}
		return ""
	}
	head, args := ext.MatchesApply(t)
	c, _ := head.AsConst()
	symbol := symbolOf(c.Name())
	total := _NatPolynomial{}
	for {
		head, args = ext.MatchesApply(t)
		c, ok := head.AsConst()
		if !ok || symbolOf(c.Name()) != symbol {
			return symbol, t, total
		}
		switch c.Name() {
		case "fo_forall", "fo_exists":
			total = total.add(_NatPolynomial{"": 1})
			t = args[1]
		default:
			total = total.add(natPolynomial(args[1]))
			t = args[2]
		}
	}
}

// atomCount counts the atoms of a skeleton, outside its length brackets.
func atomCount(skeleton string) int {
	count, depth := 0, 0
	for _, r := range skeleton {
		switch {
		case r == '[':
			depth++
		case r == ']':
			depth--
		case r == 'a' && depth == 0:
			count++
		}
	}
	return count
}
