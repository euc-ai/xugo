package omega

import (
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A target that denies a variable a value.
//
// A hypothesis `v = e` defines v, and a decision reads the definition into
// the places the linear core does not reach: under a product, inside an
// opaque atom (variable_subst.go). A target `¬(v = e)` asks for the same
// equation's refutation, and the linear core refutes it as two inequalities
// beside the hypotheses, which reaches v where it stands alone in a linear
// form and nowhere else. `0 < r ∧ r = g * v ∧ v = 0 ⊢ ⊥` and
// `0 < r ∧ r = g * v ⊢ ¬(v = 0)` are one fact on the two sides of the
// turnstile, and the definition's reading decides the first.
//
// So a target that denies a value is decided by the value's own reading. The
// equation joins the hypotheses; where it is then a rule, every hypothesis
// whose reading it changes is decided under the others at the definitions,
// and one that reads ⊥ refutes the equation:
//
//	{hyps, v = e} ⊢ ⊥    hence    {hyps} ⊢ ¬(v = e)
//
// Only the hypotheses the value is read into are asked. A contradiction among
// the others is the hypotheses' own, found without the value.
//
// What denies a value. A disequation with a variable side, at a carrier of
// the rule, as it is written. On ℕ a comparison in one variable that
// `0 < v` implies linearly — `0 < v` itself, `1 ≤ v`, `v > 0` — since there
// a variable is positive exactly where it is not zero (PosIffNonzero). And a
// strict comparison at a number carrier, `a < b` in any spelling: it denies
// `b ≤ a`, which is half of an equation, and beside a resident `a ≤ b` the
// two are the pair that makes one (paired_equation.go). So
// `x ≤ y ∧ ¬(f(x) = f(y)) ⊢ x < y` is `x ≤ y ∧ y ≤ x ∧ ¬(f(x) = f(y)) ⊢ ⊥`
// from the other side of the turnstile, as the disequation is the stated
// value's.
//
// The reading decides a target; it rewrites none. It is asked last, of a
// target the hypotheses as written and at their definitions leave open.

// denial is one reading of a target as the denial of a hypothesis: value,
// the hypothesis denied, and from, which gives the `{¬value} ⊢ t` that
// carries the denial to the target — nil where the target is `¬value`
// itself. paired marks a value that is a comparison, a rule only as one of
// a pair.
type denial struct {
	value  Term
	from   func() *prop.PropWrapper
	paired bool
}

// denials lists the readings of t as a denial, in the order they are
// tried; none where t denies nothing.
func denials(t Term, elem func(Term) bool, policy ArithPolicy) []denial {
	if inner := ext.MatchesNOT(t); inner != nil {
		if l, r, isEq := ext.MatchesEQ(inner); isEq {
			if !elem(l) || !(isVar(l) || isVar(r)) || l.AlphaEquals(r) {
				return nil
			}
			return []denial{{value: inner}}
		}
	}
	var out []denial
	if d, ok := deniedNatZero(t, policy); ok {
		out = append(out, d)
	}
	for _, c := range comparisonCarriers(policy) {
		if d, ok := c.deniedBound(t); ok {
			out = append(out, d)
		}
	}
	return out
}

// deniedNatZero reads a comparison of ℕ in one variable v that `0 < v`
// implies linearly as the denial of `v = 0`.
func deniedNatZero(t Term, policy ArithPolicy) (denial, bool) {
	if !policy.Nat || !IsLinComparisonGoal(t) {
		return denial{}, false
	}
	if _, _, isEq := ext.MatchesEQ(t); isEq {
		return denial{}, false
	}
	frees := t.Frees(func(core.VarTerm) bool { return true })
	if len(frees) != 1 || !isNat(frees[0]) || posIffNonzeroThm() == nil {
		return denial{}, false
	}
	v := frees[0]
	value := eqT(v, natZero)
	linear, ok := proveLinThenInt(slices.Values([]Term{lt(natZero, v)}), t) // {0 < v} ⊢ t
	if !ok {
		return denial{}, false
	}
	return denial{value: value, from: func() *prop.PropWrapper {
		positive := natPosIffNonzero(v).EqMP(prop.Assume(not(value))) // {¬(v = 0)} ⊢ 0 < v
		return prop.WrapProp(positive.MaybeDeriveTrans(linear))
	}}, true
}

// deniedBound reads a strict comparison of the carrier as the denial of
// the non-strict one it negates: `a < b`, or `b > a`, of `b ≤ a`, and a
// negated `a ≤ b` of that comparison as written.
func (c comparisonCarrier) deniedBound(t Term) (denial, bool) {
	if inner := ext.MatchesNOT(t); inner != nil {
		_, _, isLe := c.d.matchLe(inner)
		_, _, isGe := c.d.matchGe(inner)
		if !isLe && !isGe {
			return denial{}, false
		}
		return denial{value: inner, paired: true}, true
	}
	a, b, ok := c.d.matchLt(t)
	if !ok {
		if b, a, ok = c.d.matchGt(t); !ok {
			return denial{}, false
		}
	}
	value := c.le(b, a)
	return denial{value: value, paired: true, from: func() *prop.PropWrapper {
		w, ok := c.prove([]Term{not(value)}, t) // {¬(b ≤ a)} ⊢ a < b
		if !ok {
			return nil
		}
		return w
	}}, true
}

// withHyp is the context of c's hypotheses and h after them. The pre-simp
// of a hypothesis reads that hypothesis alone, so c's is kept.
func (c *ArithCtx) withHyp(h Term) *ArithCtx {
	simplified, bridges := preSimpHyps([]Term{h}, c.hypFreeSimp)
	hyps := append(slices.Clone(c.hyps), h)
	return &ArithCtx{
		hyps:           hyps,
		simplifiedHyps: append(slices.Clone(c.simplifiedHyps), simplified...),
		bridges:        append(slices.Clone(c.bridges), bridges...),
		defs:           readAtDefinitions(hyps, c.policy),
		hypFreeSimp:    c.hypFreeSimp,
		policy:         c.policy,
		reader:         c.reader,
	}
}

// decideDeniedValue decides a target that denies a value to ⊤ by refuting
// the value read into the hypotheses: `{hyps} ⊢ t = ⊤`, or nil.
func (c *ArithCtx) decideDeniedValue(t Term) *prop.PropWrapper {
	elem, _ := ruleScopeUnder(c.hyps)
	for _, d := range denials(t, elem, c.policy) {
		if w := c.refuteDenied(d); w != nil {
			return w
		}
	}
	return nil
}

// refuteDenied is `{hyps} ⊢ t = ⊤` for the target d reads, where d's value
// joined to the hypotheses is a rule that reads one of them ⊥; nil
// otherwise.
func (c *ArithCtx) refuteDenied(d denial) *prop.PropWrapper {
	joined := len(c.hyps)
	if d.paired {
		// A comparison is a rule only beside its opposite: the pairs it
		// would be a member of are asked before the context is built.
		anySide := func(l, r Term) bool { return isVar(l) || isVar(r) }
		if len(pairedEquations(append(slices.Clone(c.hyps), d.value), c.policy, anySide, joined)) == 0 {
			return nil
		}
	}
	with := c.withHyp(d.value)
	if with.defs == nil || !with.defs.defines[joined] {
		return nil // v is fixed, or defined already: the value is no rule
	}
	for j, h := range c.hyps {
		if with.defs.defines[j] || !c.readsDifferently(with, j) {
			continue
		}
		at := with.decideAtDefinitions(j, h) // {hyps∖j, value} ⊢ h = ⊥
		if at == nil || !prop.Rhs(at).Equals(prop.F) {
			continue
		}
		denied := at.EqMP(prop.Assume(h)).NegHyp(d.value) // {hyps} ⊢ ¬value
		if d.from == nil {
			return eqtIntro(denied)
		}
		from := d.from() // {¬value} ⊢ t
		if from == nil {
			return nil
		}
		return eqtIntro(prop.WrapProp(denied.MaybeDeriveTrans(from)))
	}
	return nil
}

// readsDifferently reports whether hypothesis j reads otherwise at with's
// definitions than at c's: the reading names a variable with defines and c
// does not, or j was a definition of c's that with's displaced.
func (c *ArithCtx) readsDifferently(with *ArithCtx, j int) bool {
	if c.defs == nil {
		return !with.defs.read[j].AlphaEquals(c.hyps[j])
	}
	return c.defs.defines[j] || !with.defs.read[j].AlphaEquals(c.defs.read[j])
}
