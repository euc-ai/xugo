package omega

import (
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Ground congruence for the arith path.
//
// A hypothesis equation between two COMPOUND terms of one carrier —
// `pi / &2 = &2`, `x + y = &3` — is substituted, bigger side to smaller,
// into the term the decider is about to read, so that an atom whose
// argument is spelled one way (`real_cos(pi / &2)`) meets the same atom
// spelled the other way (`real_cos(&2)`) as one unknown. This is what the
// refuter's clause layer already does with such an equation (the
// order-gated demodulation of ext/clause/deduce.go), brought to the arith
// path; the variable-sided case (`a = &0` into `f(a)`) was already the
// substitution leaf's (eqHypSubst / intEqHypSubst), and stays its own.
//
// The carriers are the three number carriers and every carrier the
// structure ring reads (structure_ring.go): a type at which a comm_ring
// or field fact stands among the hypotheses, or an instance is installed.
// At a carrier set the ring reads an atom only with its membership
// resident, so an equation between two spellings of a term is its one
// way from the spelling the goal has to the spelling the memberships
// name — determinant's `A′·B′ = −(A·B)` from `A′ = −A`, `B′ = B`, the
// τ·q-side atoms A′, B′ without a membership. The pass reads the equation
// and nothing of the ring, so it needs no law and no policy.
//
// Three conditions make an equation a rule:
//   - neither side is a bare variable (that shape belongs to the
//     variable-sided rule, whose orientation is by variable rank, not size,
//     and the two must not compete over one equation);
//   - the sides differ in size (congSize: a literal counts 0, an
//     abstraction its body), and the bigger rewrites to the smaller (equal
//     sizes — a permutation equation `x·z = z·x` — are skipped, the
//     oscillation the variable rule's rank guard exists to prevent);
//   - the smaller side names no FREE carrier variable the bigger side
//     lacks (the substitution never creates a redex for the variable-sided
//     rule); a bound variable is nobody's target, and its name is the
//     binder's.
//
// The pass runs to its own fixpoint BEFORE the composed leaves, not as one
// more leaf among them: every fire strictly shrinks the term, so the pass
// terminates on its own, while interleaved with the variable rule — which
// may grow a term as it lowers variable ranks — the union of the two would
// have no such argument. The price is a redex the variable rule exposes
// afterwards, which stays; the variable rule substitutes literals almost
// always, which expose none.
//
// The rules are read from the hypotheses AS WRITTEN and applied to the
// target as written, before the hypothesis pre-simp: that pre-simp folds
// `x / &2 = &2` into `x = &4`, a true equation in a spelling the goal's
// `real_cos(x / &2)` no longer carries, while the author's spelling is the
// one the atoms share — the spelling the refuter's demodulation reads too.
// Like the variable-sided rule, the pass rewrites the TARGET of a Decide /
// DecideExcept call under that call's hypotheses; a hypothesis is rewritten
// when the arith tactic decides it under the others, and the closer's
// rounds carry the result back to the conclusion.

// compoundSubst is one oriented rule: `{h} ⊢ from = to`, from the bigger side.
type compoundSubst struct {
	from Term
	eq   *prop.PropWrapper
}

// compoundEqSubsts reads the rules off the hypothesis set.
func compoundEqSubsts(hyps []Term) []compoundSubst {
	elem := carrierElemUnder(hyps)
	var subs []compoundSubst
	for _, h := range hyps {
		l, r, ok := ext.MatchesEQ(h)
		if !ok || !elem(l) || isVar(l) || isVar(r) || l.AlphaEquals(r) {
			continue
		}
		switch {
		case congSize(l) > congSize(r) && freeVarsWithin(r, l, elem):
			subs = append(subs, compoundSubst{from: l, eq: prop.Assume(h)}) // l → r
		case congSize(r) > congSize(l) && freeVarsWithin(l, r, elem):
			subs = append(subs, compoundSubst{from: r, eq: prop.Assume(h).EqSym()}) // r → l
		}
	}
	return subs
}

// congSize is the size the orientation compares: a literal — a canonical
// numeral, or a carrier's embedding `&n` of one — counts 0, every other node
// 1, an abstraction's body with it. A literal is the most reduced spelling
// there is and must come out the smaller side whatever its encoding's node
// count (`&3` is real_of_num over a three-node bit string, and would
// otherwise outweigh `x + y`).
func congSize(t Term) int {
	if isLiteral(t) {
		return 0
	}
	if a, ok := t.AsAppliedTerm(); ok {
		return 1 + congSize(a.Fun()) + congSize(a.Arg())
	}
	if abs, ok := t.AsAbsTerm(); ok {
		return 1 + congSize(abs.Body())
	}
	return 1
}

func isLiteral(t Term) bool {
	if ext.IsCanonicalNumeral(t) {
		return true
	}
	if n, ok := MatchesRealOfNum(t); ok {
		return ext.IsCanonicalNumeral(n)
	}
	if n, ok := MatchesIntOfNum(t); ok {
		return ext.IsCanonicalNumeral(n)
	}
	return false
}

// carrierElem reports whether t is an element of one of the three arithmetic
// carriers (the pass is kernel rewriting by assumption — bundle-free, so it
// is not gated by the arith policy).
func carrierElem(t Term) bool {
	return natDomain.isElem(t) || realDomain.isElem(t) || intDomain.isElem(t)
}

// carrierElemUnder is carrierElem widened by the structure rings' carriers
// under hyps: the type of a comm_ring or field fact among them, or of an
// installed instance.
func carrierElemUnder(hyps []Term) func(Term) bool {
	carriers := structureCarriers(hyps)
	return func(t Term) bool {
		return carrierElem(t) || slices.ContainsFunc(carriers, t.Type().Equals)
	}
}

// structureCarriers lists the carriers of the structure facts among hyps
// and of the installed instances (structureCarrierOf, structure_ring.go),
// the number carriers left out as carrierElem's.
func structureCarriers(hyps []Term) []core.HolType {
	if structureLaws == nil {
		return nil
	}
	var out []core.HolType
	add := func(fact Term) {
		if carrier, ok := structureCarrierOf(fact, structureLaws); ok && !isNumberCarrier(carrier) {
			out = append(out, carrier)
		}
	}
	for _, h := range hyps {
		add(h)
	}
	for i := range structureInstances {
		add(structureInstances[i].Fact.Conclusion())
	}
	return out
}

// freeVarsWithin reports whether every free carrier variable of small
// occurs free in big, elem naming the carriers. A function-typed variable
// — an atom's head, `f` in `f(x)` — is not a substitution target of any
// rule and does not count, as the variable-sided rule's own freeNumVars
// does not count it; a bound variable is no target either.
func freeVarsWithin(small, big Term, elem func(Term) bool) bool {
	frees := func(t Term) []core.VarTerm {
		return t.Frees(func(v core.VarTerm) bool { return elem(v) })
	}
	inBig := frees(big)
	for _, v := range frees(small) {
		if !slices.ContainsFunc(inBig, v.EqualsVar) {
			return false
		}
	}
	return true
}

// compoundEqSubstRewrite is the deep rewrite by the hypothesis set's
// compound rules; nil when the set has none.
func compoundEqSubstRewrite(hyps []Term) prop.Rewrite {
	subs := compoundEqSubsts(hyps)
	if len(subs) == 0 {
		return nil
	}
	anyHyp := func(pred func(prop.Term) bool) bool { return slices.ContainsFunc(hyps, pred) }
	leaf := func(s Term) *prop.PropWrapper {
		for _, sb := range subs {
			if s.AlphaEquals(sb.from) {
				return sb.eq
			}
		}
		return nil
	}
	deep := prop.DeepRewriteWithEnv(anyHyp, leaf)
	// The deep rewrite fires at each position once and goes on into what it
	// produced, but does not re-match the node it just produced against the
	// rules — so a chain (`f(x) + f(x) → g(x)`, then `g(x) → &2`) needs the
	// pass run again on its own result. Every round strictly shrinks the
	// term, so the rounds end on their own; the cap is a fuse against a rule
	// set no measure was meant for, never the termination argument.
	return func(t Term) *prop.PropWrapper {
		var acc *prop.PropWrapper
		for round := 0; round < congruenceRounds; round++ {
			w := deep(t)
			if w == nil || prop.Rhs(w).AlphaEquals(t) {
				break
			}
			if acc == nil {
				acc = w
			} else {
				acc = acc.EqTrans(w)
			}
			t = prop.Rhs(w)
		}
		return acc
	}
}

// congruenceRounds caps the pass's rounds (see compoundEqSubstRewrite).
const congruenceRounds = 32

// withCompoundEqSubst runs the congruence pass on a target, then inner on
// what it leaves, composing the two certificates; the pass alone is
// progress when inner then declines (the rewritten target is a simpler
// goal, as a hypothesis fold is). Where inner carries the pass's result
// back to the target the composition is no rewrite, and answers nil as a
// rewrite that does not fire: a rule is oriented by size and inner by its
// normal form, and the two disagree on an equation between a term and a
// bigger normal form of it — `&2 ^ n = &(2 ^ n)`, which the arith tactic
// itself leaves beside a leaf it normalized (emitArithBridges).
func withCompoundEqSubst(hyps []Term, inner prop.Rewrite) prop.Rewrite {
	pre := compoundEqSubstRewrite(hyps)
	if pre == nil {
		return inner
	}
	return func(t Term) *prop.PropWrapper {
		cong := pre(t) // {eqs} ⊢ t = t'
		if cong == nil {
			return inner(t)
		}
		w := inner(prop.Rhs(cong))
		if w == nil {
			return cong
		}
		if prop.Rhs(w).AlphaEquals(t) {
			return nil
		}
		return cong.EqTrans(w)
	}
}
