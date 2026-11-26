package omega

import (
	"slices"

	"github.com/euc-ai/xugo/ext/prop"
)

// The equation a pair of comparisons makes.
//
// Two hypotheses that bound one difference from both sides — `x ≤ y` beside
// `y ≤ x`, `t ≤ &0` beside `&0 ≤ t` — are the equation of the two sides.
// The linear core holds the pair as the two inequalities it is, and they
// reach a variable where it stands alone in a linear form and nowhere
// else: beside them `t * A` is still an unknown, and `f(x)` and `f(y)` are
// two atoms. So the pair is read as the equation it would be if stated
// (variable_subst.go): where a side of it is a variable the equation is a
// rule, and the two comparisons are the rule's own hypotheses, left out of
// a context read at the definitions as a stated definition's equation is.
//
// Which pairs. Two hypotheses, each one comparison at a number carrier the
// policy admits, read as the linear layer reads a hypothesis
// (Domain.hypConstraintsOf: a `≥` turned, a negated comparison un-negated,
// a subtraction moved across): `a ≤ b` and `c ≤ d` with `a + c` and
// `b + d` one linear form. Then `b − a` and `d − c` are each other's
// negation, and each is zero. At ℕ and ℤ a strict `c < d` is the non-strict
// `c + 1 ≤ d`. The equation read off a pair is that of a non-strict member
// with a variable side.
//
// The pairing is the untrusted model's. The equation is proved by the
// carrier's linear prover from the two hypotheses, so a pair misread proves
// nothing and is no rule; and since the prover's lemmas are the carrier's
// bundle's, a pair is read only at a carrier the policy admits, where a
// stated equation, which cites no lemma, is read at every carrier.

// pairedEquation is `{hyps[at[0]], hyps[at[1]]} ⊢ l = r`, the equation the
// two hypotheses make.
type pairedEquation struct {
	l, r Term
	eq   *prop.PropWrapper
	at   []int
}

// comparisonCarrier is a number carrier as the pairing reads it: its
// domain, its `a ≤ b`, its linear prover, and whether its order is
// discrete.
type comparisonCarrier struct {
	d        *Domain
	le       func(a, b Term) Term
	prove    func(hyps []Term, goal Term) (*prop.PropWrapper, bool)
	discrete bool
}

// comparisonCarriers lists the carriers policy admits.
func comparisonCarriers(policy ArithPolicy) []comparisonCarrier {
	var out []comparisonCarrier
	if policy.Nat {
		out = append(out, comparisonCarrier{d: natDomain, le: le, discrete: true,
			prove: func(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
				return proveLinThenInt(slices.Values(hyps), goal)
			}})
	}
	if intLemmaBundle != nil && policy.Int {
		out = append(out, comparisonCarrier{d: intDomain, le: intLeT, discrete: true, prove: intLinProveSigned})
	}
	if realLemmaBundle != nil && policy.Real {
		out = append(out, comparisonCarrier{d: realDomain, le: realLeT, prove: realLinProveSigned})
	}
	return out
}

// bound is hypothesis at read as `lo ≤ hi`: the two sides as the linear
// layer holds them, and their forms — the lower's with one added where the
// hypothesis is strict.
type bound struct {
	at       int
	lo, hi   Term
	lof, hif linForm
	strict   bool
}

// boundOf reads h, hypothesis at, as a bound; ok=false where h is not one
// comparison of the carrier with linear sides, or is strict at a carrier
// whose order is dense.
func (c comparisonCarrier) boundOf(at int, h Term) (bound, bool) {
	if _, _, isAnd := prop.MatchesAND(h); isAnd {
		return bound{}, false
	}
	cs := c.d.hypConstraintsOf(h)
	if len(cs) != 1 || cs[0].Op == opEQ || (cs[0].Op == opLT && !c.discrete) {
		return bound{}, false
	}
	lof, ok := c.d.linOf(cs[0].Lhs)
	if !ok {
		return bound{}, false
	}
	hif, ok := c.d.linOf(cs[0].Rhs)
	if !ok {
		return bound{}, false
	}
	b := bound{at: at, lo: cs[0].Lhs, hi: cs[0].Rhs, lof: lof, hif: hif, strict: cs[0].Op == opLT}
	if b.strict {
		b.lof = linAdd(b.lof, linConst(integerOne))
	}
	return b, true
}

// opposite reports whether p and q bound one difference from both sides:
// the lower sides and the upper sides sum to one form.
func opposite(p, q bound) bool {
	if !p.lof.konst.add(q.lof.konst).equal(p.hif.konst.add(q.hif.konst)) {
		return false
	}
	return sameLinForm(linAdd(p.lof, q.lof), linAdd(p.hif, q.hif))
}

// pairedEquations lists the equations the pairs among hyps make, each the
// equation of a non-strict member whose sides sided accepts. A hypothesis
// is in one pair at most. With only ≥ 0 the pairs are those hypothesis
// only is a member of.
func pairedEquations(hyps []Term, policy ArithPolicy, sided func(l, r Term) bool, only int) []pairedEquation {
	var out []pairedEquation
	for _, c := range comparisonCarriers(policy) {
		var bounds []bound
		for at, h := range hyps {
			if b, ok := c.boundOf(at, h); ok {
				bounds = append(bounds, b)
			}
		}
		paired := make([]bool, len(bounds))
		for i, p := range bounds {
			if paired[i] || p.strict || !sided(p.lo, p.hi) {
				continue
			}
			for j, q := range bounds {
				if j == i || paired[j] || (only >= 0 && p.at != only && q.at != only) || !opposite(p, q) {
					continue
				}
				eq, ok := c.equation(hyps[p.at], hyps[q.at], eqT(p.lo, p.hi))
				if !ok {
					continue
				}
				paired[i], paired[j] = true, true
				out = append(out, pairedEquation{l: p.lo, r: p.hi, eq: eq, at: []int{p.at, q.at}})
				break
			}
		}
	}
	return out
}

// pairedEquationMemo keeps the prover's answer per pair and equation: the
// rules are read off a context once for each decision made in it.
var pairedEquationMemo linProveMemo

// equation proves `{h, k} ⊢ goal`, goal the equation the pair h, k makes.
func (c comparisonCarrier) equation(h, k, goal Term) (*prop.PropWrapper, bool) {
	hyps := []Term{h, k}
	key := c.d.name + "|" + linQuestionKey(hyps, goal)
	if e, ok := pairedEquationMemo.lookup(key, hyps, goal); ok {
		return e.proof, e.proof != nil
	}
	proof, ok := c.prove(hyps, goal)
	if !ok {
		proof = nil
	}
	pairedEquationMemo.store(key, linAnswer{hyps: hyps, goal: goal, proof: proof})
	return proof, ok
}
