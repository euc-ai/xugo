package omega

// numeral_reading.go — the numeral reading: a statement read at its
// numerals. A term with no variable, built from natural-number literals
// by +, ·, − and suc, is its value (`2 + 1` is `3`), and so is a sum or a
// product of `&` literals in ℝ and ℤ (`&2 * &3` is `&6`); a comparison
// with no variable on either side, its sides built from literals by +,
// −, · and ℝ's /, is ⊤ or ⊥ (`0 < 2`, `&1 / &2 < &1`, `1 + 1 = 2`); and
// the truth constants that leaves are folded out of the connectives, the
// CONDs and the quantifiers around them (`0 < 2 ⇒ Q` is `Q`). Nothing that names a
// variable is read — `0 ≤ n`, `u ≤ u` and `n + 1 + 1` are the arithmetic
// closer's or a cited law's — and no factorial, power, quotient of
// naturals, root or absolute value: those are that closer's too.
//
// The reading is what the apply rung compares statements in, beside the
// membership reading and the record reading (prover/proof, rungReader):
// a guard `x ∈ X(2 + 1)` is supplied by a resident `x ∈ X(3)`, a guard
// that reads ⊤ asks for no supplier, a goal that reads ⊤ is closed.
// It is not a rewrite of the leaf a closer is handed: the refuter does
// not compute, and a numeral fact its author listed is a fact it uses.
//
// One function has two faces. numeralValue is the value a term has by
// Go's arithmetic, which says what the reading reads: where it is silent
// nothing is rewritten. NumeralReading is the kernel's `⊢ t = t'`, built
// from the evaluators of the arithmetic closer (the bit recursions of
// nat_norm.go, the OfNum bridges, the hypothesis-free decision of a
// ground comparison). A verdict of the kernel's that is not the value's
// is an engine invariant broken, and panics. A comparison the decision
// leaves undecided is left as written.

import (
	"fmt"
	"math/big"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// numeralLiteral is the value of t where t is a literal of ℕ, ℝ or ℤ: a
// canonical bit tower, or `&` of one.
func numeralLiteral(t Term) (*big.Int, bool) {
	if x, ok := MatchesRealOfNum(t); ok {
		t = x
	} else if x, ok := MatchesIntOfNum(t); ok {
		t = x
	}
	if !ext.IsCanonicalNumeral(t) {
		return nil, false
	}
	return ext.NumeralValue(t)
}

// numeralValue is the value of t where t is a numeral term of the
// reading: a literal, or numeral terms under +, ·, − and, in ℕ, suc;
// under the negation of ℝ and ℤ; under ℝ's quotient by a value that is
// not zero. ℕ's − is truncated. False for every other term, a variable
// among them.
func numeralValue(t Term) (*big.Rat, bool) {
	if v, ok := numeralLiteral(t); ok {
		return new(big.Rat).SetInt(v), true
	}
	binary := func(l, r Term, op func(z, x, y *big.Rat) *big.Rat) (*big.Rat, bool) {
		x, ok := numeralValue(l)
		if !ok {
			return nil, false
		}
		y, ok := numeralValue(r)
		if !ok {
			return nil, false
		}
		return op(new(big.Rat), x, y), true
	}
	switch {
	case isNat(t):
		if l, r, ok := MatchesPlus(t); ok {
			return binary(l, r, (*big.Rat).Add)
		}
		if l, r, ok := MatchesStar(t); ok {
			return binary(l, r, (*big.Rat).Mul)
		}
		if l, r, ok := MatchesMinus(t); ok {
			return binary(l, r, func(z, x, y *big.Rat) *big.Rat {
				if x.Cmp(y) <= 0 {
					return z
				}
				return z.Sub(x, y)
			})
		}
		if x, ok := MatchesSuc(t); ok {
			v, ok := numeralValue(x)
			if !ok {
				return nil, false
			}
			return new(big.Rat).Add(v, big.NewRat(1, 1)), true
		}
	case isRealTerm(t), isIntTerm(t):
		d := realDomain
		if isIntTerm(t) {
			d = intDomain
		}
		if l, r, ok := d.matchPlus(t); ok {
			return binary(l, r, (*big.Rat).Add)
		}
		if l, r, ok := d.matchStar(t); ok {
			return binary(l, r, (*big.Rat).Mul)
		}
		if l, r, ok := d.matchSub(t); ok {
			return binary(l, r, (*big.Rat).Sub)
		}
		if x, ok := d.matchNeg(t); ok {
			v, ok := numeralValue(x)
			if !ok {
				return nil, false
			}
			return new(big.Rat).Neg(v), true
		}
		if l, r, ok := MatchesRealDiv(t); ok && isRealTerm(t) {
			y, ok := numeralValue(r)
			if !ok || y.Sign() == 0 {
				return nil, false
			}
			x, ok := numeralValue(l)
			if !ok {
				return nil, false
			}
			return new(big.Rat).Quo(x, y), true
		}
	}
	return nil, false
}

// numeralComparison is the truth of t where t compares two numeral
// terms of one of the three types: `=`, `<`, `≤`, `>` or `≥`.
func numeralComparison(t Term) (holds, ok bool) {
	sides := func(l, r Term, holds func(cmp int) bool) (bool, bool) {
		x, ok := numeralValue(l)
		if !ok {
			return false, false
		}
		y, ok := numeralValue(r)
		if !ok {
			return false, false
		}
		return holds(x.Cmp(y)), true
	}
	for _, d := range []*Domain{natDomain, realDomain, intDomain} {
		if l, r, ok := d.matchLt(t); ok {
			return sides(l, r, func(c int) bool { return c < 0 })
		}
		if l, r, ok := d.matchLe(t); ok {
			return sides(l, r, func(c int) bool { return c <= 0 })
		}
		if l, r, ok := d.matchGt(t); ok {
			return sides(l, r, func(c int) bool { return c > 0 })
		}
		if l, r, ok := d.matchGe(t); ok {
			return sides(l, r, func(c int) bool { return c >= 0 })
		}
	}
	if l, r, ok := prop.MatchesEQ(t); ok && (isNat(l) || isRealTerm(l) || isIntTerm(l)) {
		return sides(l, r, func(c int) bool { return c == 0 })
	}
	return false, false
}

// numeralFold is the reading of one numeral term that is no literal and
// whose operands are literals, as the kernel's `⊢ t = literal`: a sum, a
// product, a truncated difference or a successor in ℕ, a sum or a
// product of `&` literals in ℝ and ℤ. nil for every other term. The
// deep rewrite reaches a nested term operands first, so `(1 + 1) + 1`
// is read in two steps.
// ℝ's and ℤ's literals are read through ℕ's evaluators, so they are read
// only where the policy admits ℕ's bundle as well.
func numeralFold(policy ArithPolicy) prop.Rewrite {
	literals := func(l, r Term) bool {
		_, okL := numeralLiteral(l)
		_, okR := numeralLiteral(r)
		return okL && okR
	}
	return func(t Term) *prop.PropWrapper {
		switch {
		case isNat(t) && policy.Nat:
			if l, r, ok := MatchesPlus(t); ok && literals(l, r) {
				w, _ := NormNatAdd(l, r)
				return w
			}
			if l, r, ok := MatchesStar(t); ok && literals(l, r) {
				w, _ := NormNatMul(l, r)
				return w
			}
			if l, r, ok := MatchesMinus(t); ok && literals(l, r) {
				if w := subCancel(l, r); w != nil {
					return w
				}
				return subTrunc(l, r)
			}
			if x, ok := MatchesSuc(t); ok {
				if _, lit := numeralLiteral(x); lit {
					return sucBits(x)
				}
			}
		case isRealTerm(t) && policy.Nat && policy.Real && realLemmaBundle != nil:
			if l, r, ok := realDomain.matchPlus(t); ok && literals(l, r) {
				w, _ := realNormNatAdd(l, r)
				return w
			}
			if l, r, ok := realDomain.matchStar(t); ok && literals(l, r) {
				w, _ := realNormNatMul(l, r)
				return w
			}
		case isIntTerm(t) && policy.Nat && policy.Int && intLemmaBundle != nil:
			if l, r, ok := intDomain.matchPlus(t); ok && literals(l, r) {
				w, _ := intNormNatAdd(l, r)
				return w
			}
			if l, r, ok := intDomain.matchStar(t); ok && literals(l, r) {
				w, _ := intNormNatMul(l, r)
				return w
			}
		}
		return nil
	}
}

// numeralDecide is the reading of one comparison between numeral terms,
// as the kernel's `⊢ t ⇔ ⊤` or `⊢ t ⇔ ⊥` — the arithmetic closer's
// simplification of a hypothesis (NewArithCtxWithPolicy: the identity
// and numeral folds, a literal divisor cleared, a difference moved
// across, the decision of a ground comparison), which consults no
// hypothesis, run on the one comparison and asked only where the value
// says t is one. nil where it leaves the comparison undecided.
func numeralDecide(policy ArithPolicy) prop.Rewrite {
	var leaves []prop.Rewrite
	if policy.Nat {
		leaves = append(leaves, arithSimpStep)
	}
	if realLemmaBundle != nil && policy.Real {
		leaves = append(leaves, realArithSimpStep, realMoveAcrossLeaf)
	}
	if intLemmaBundle != nil && policy.Int {
		leaves = append(leaves, intArithSimpStep)
	}
	decide := prop.BasicRewritesWith(append(leaves, groundComparisonDecide(policy))...)
	return func(t Term) *prop.PropWrapper {
		holds, ok := numeralComparison(t)
		if !ok || !policy.Nat {
			return nil
		}
		w := decide(t)
		if !decides(w) {
			return nil
		}
		if prop.Rhs(w).Equals(prop.T) != holds {
			panic(fmt.Sprintf("numeral reading: the arithmetic decision of %s is %s and its value says %t (engine invariant)",
				ext.PrintTerm(t), ext.PrintTerm(prop.Rhs(w)), holds))
		}
		return w
	}
}

// truthConstant reports whether t is ⊤ or ⊥.
func truthConstant(t Term) bool { return t.Equals(prop.T) || t.Equals(prop.F) }

// truthConstantFold folds a truth constant out of the connective, the
// COND or the quantifier it is an operand of: `¬⊤`, `⊤ ∧ A`, `A ∨ ⊥`,
// `⊤ ⇒ A`, `A ⇔ ⊥`, `COND(⊥, a, b)`, `∀x. ⊤`. It is the boolean rewrite,
// the COND clauses and the moot quantifier, taken only at a node one of
// whose operands is a truth constant: a statement that holds none is
// not touched.
func truthConstantFold(t Term) *prop.PropWrapper {
	if abs := ext.MatchesFORALL(t); !abs.IsZero() {
		if truthConstant(abs.Body()) {
			return prop.MootForAll(abs.Var(), abs.Body())
		}
		return nil
	}
	if abs := ext.MatchesEXISTS(t); !abs.IsZero() {
		if truthConstant(abs.Body()) {
			return prop.MootExists(abs.Var(), abs.Body())
		}
		return nil
	}
	if p, x, y, ok := ext.MatchesCond(t); ok {
		switch {
		case p.Equals(prop.T):
			return prop.CondClauseT(x, y)
		case p.Equals(prop.F):
			return prop.CondClauseF(x, y)
		}
		return nil
	}
	if inner := ext.MatchesNOT(t); inner != nil {
		if truthConstant(inner) {
			return prop.BoolRewrite(t)
		}
		return nil
	}
	for _, match := range []func(Term) (Term, Term, bool){ext.MatchesAND, ext.MatchesOR, ext.MatchesIMPLY, ext.MatchesIFF} {
		if l, r, ok := match(t); ok {
			if truthConstant(l) || truthConstant(r) {
				return prop.BoolRewrite(t)
			}
			return nil
		}
	}
	return nil
}

// NumeralReading is the numeral reading as a rewrite: `⊢ t = t'` with t'
// the reading of t, nil where t spells nothing the reading reads. It
// runs under policy, the bundles a proof may use: a type whose bundle
// the policy withholds is not read.
func NumeralReading(policy ArithPolicy) prop.Rewrite {
	return func(t Term) *prop.PropWrapper {
		if !policy.readsNumerals() || !SpellsNumeralStatement(t) {
			return nil
		}
		return numeralRewrite(policy)(t)
	}
}

// numeralRewrites holds the reading's deep rewrite, built once for each
// policy and each set of installed bundles it was built over.
var numeralRewrites sync.Map

type numeralRewriteKey struct {
	policy  ArithPolicy
	real    *RealLemmaBundle
	integer *IntLemmaBundle
}

func numeralRewrite(policy ArithPolicy) prop.Rewrite {
	key := numeralRewriteKey{policy: policy, real: realLemmaBundle, integer: intLemmaBundle}
	if r, ok := numeralRewrites.Load(key); ok {
		return r.(prop.Rewrite)
	}
	r := prop.DeepRewrite(numeralFold(policy), numeralDecide(policy), truthConstantFold)
	numeralRewrites.Store(key, r)
	return r
}

// NumeralNormal is t read at its numerals under policy: the right side
// of NumeralReading, t itself where nothing is read.
func NumeralNormal(policy ArithPolicy, t Term) Term {
	if w := NumeralReading(policy)(t); w != nil {
		return prop.Rhs(w)
	}
	return t
}

// readsNumerals reports whether the reading has what every evaluation
// of it stands on: ℕ's bundle, admitted by the policy and installed —
// or, in a test, the stand-in for it. The reading is the rung's at every
// comparison, so with no bundle to evaluate with it reads nothing, where
// an Arith step asked for by name fails loudly on the first leaf.
func (p ArithPolicy) readsNumerals() bool {
	return p.Nat && (natLemmaBundle != nil || fabricatePlaceholder != nil)
}

// ReadsNumerals reports whether the reading reads anything under
// policy: whether it admits ℕ's bundle and there is one to evaluate
// with.
func ReadsNumerals(policy ArithPolicy) bool { return policy.readsNumerals() }

// NumeralDomains reports which of the three types t spells a numeral
// statement at — a numeral term that is no literal, or a comparison
// between numeral terms: the bundles a reading of t evaluates with,
// beside ℕ's, which every reading does.
func NumeralDomains(t Term) (real, integer bool) {
	var walk func(Term)
	walk = func(t Term) {
		if _, lit := numeralLiteral(t); lit {
			return
		}
		at := t
		if l, _, ok := prop.MatchesEQ(t); ok {
			at = l
		} else {
			for _, d := range []*Domain{realDomain, intDomain} {
				for _, match := range []func(Term) (Term, Term, bool){d.matchLt, d.matchLe, d.matchGt, d.matchGe} {
					if l, _, ok := match(t); ok {
						at = l
					}
				}
			}
		}
		_, value := numeralValue(t)
		_, comparison := numeralComparison(t)
		if value || comparison {
			real = real || isRealTerm(at)
			integer = integer || isIntTerm(at)
			return
		}
		switch x := t.Core().(type) {
		case core.AppliedTerm:
			walk(x.Fun())
			walk(x.Arg())
		case core.AbsTerm:
			walk(x.Body())
		}
	}
	walk(t)
	return real, integer
}

// SpellsNumeralStatement reports whether t holds what the reading
// reads: a numeral term that is no literal, or a comparison between
// numeral terms. It is the reading's test of whether there is anything
// to do, made without the kernel.
func SpellsNumeralStatement(t Term) bool {
	if _, lit := numeralLiteral(t); lit {
		return false
	}
	if _, ok := numeralValue(t); ok {
		return true
	}
	if _, ok := numeralComparison(t); ok {
		return true
	}
	switch x := t.Core().(type) {
	case core.AppliedTerm:
		return SpellsNumeralStatement(x.Fun()) || SpellsNumeralStatement(x.Arg())
	case core.AbsTerm:
		return SpellsNumeralStatement(x.Body())
	}
	return false
}
