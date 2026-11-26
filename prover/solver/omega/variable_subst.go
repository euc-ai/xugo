package omega

import (
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// The variable-sided rule of the arith path.
//
// A hypothesis equation with a variable on one side, `v = e`, defines v,
// and the decider reads its target with v replaced by e. The linear core
// uses such an equation as two inequalities, which reaches v where it
// stands alone in a linear form and nowhere else: not under a product
// (`t = &0` beside `t * A`), not inside an opaque atom (`n = 2` beside
// `nat_mod(7, n)`). Substituted, `t * A` is `&0 * A` and folds, an atom on
// n becomes an atom on a literal and evaluates, two atoms that differ by
// which of two equal variables they name are one, and `a = b + c` turns
// `a * x = b * x + c * x` into a ring identity.
//
// The rule is one at every carrier the ground-congruence pass reads
// (congruence_subst.go): the three number carriers and the structure
// rings' carriers. It reads the equation and cites no lemma, so no bundle
// and no policy gates it. An equation between two compound terms is that
// pass's, oriented by size; the two do not compete over one equation.
//
// An equation need not be stated to be one. Two comparisons that bound one
// difference from both sides, `t ≤ &0` beside `&0 ≤ t`, are the equation
// of the sides, and are read as the rule it would be (paired_equation.go)
// — at the number carriers the policy admits, the equation being the
// linear prover's to show.
//
// Which variables a rule may define. An unknown of the problem, and not a
// constant of the theory the deciders work in. At a number carrier the
// constants are literals and every variable is an unknown. At a structure
// ring's carrier the ring's own elements are constants even where they
// are variables — the zero and the one of `comm_ring(add, zero, neg, mul,
// one)` stated over variable components: `p - r = zero` pins the
// difference of p and r and does not define zero. So a variable free in a
// structure fact of the context is fixed: no rule defines it, and a
// definition that names it names a constant.
//
// A function is defined as a number is. `F = λx. e` with F a variable of
// the problem defines F, whatever F's type: the decider's carriers are
// where e is read, and F stands for the λ at them. The reading of the
// rule is the reading of any other with its applications reduced — `F(s)`
// reads as e at s, and F standing unapplied, as an argument, reads as the
// λ — so a leaf read at the rule names F nowhere. It is read where target
// and context are read together (definitionReading) and by no leaf of the
// deciders' own rewrite: a target read at the body beside hypotheses that
// still spell `F(s)` would be two unknowns, and no linear fact joins them
// as `v = 2` joins a number to its value.
//
// Which equations are rules. Each variable gets at most one, and the rules
// together are acyclic: no variable is reached from its own definition
// through the definitions of the variables that definition names. That is
// the termination argument, and the whole of it. A rewrite `v → e` leaves
// only variables defined, if at all, strictly later in a fixed order of
// the rules, so the deep rewrite's fixpoint cannot cycle, whatever e
// repeats. `v = v + 1` and the pair `a = b + 1`, `b = a - 1` are the
// cycles the check refuses.
//
// The equations are taken in two passes over the hypotheses, in their
// order:
//   - a value first: `v = e` with no carrier variable free in e — a
//     literal, a constant, a term over other types' variables. It needs
//     no check, and no definition taken later can displace it, so a
//     branch's pin `x = 3` wins over a resident `x = y + z`;
//   - then every other equation with a variable side, the left side
//     tried before the right. Between two variables the one later in
//     core's variable order goes to the earlier, so an equation and its
//     symmetric make the same rule.
//
// Where the rule is read. A definition gives a decision two readings, and
// a decider that searches to a bound is the stronger in neither: a name
// for a compound term keeps it one unknown, which a product of two
// hypotheses may need, and the definition read in exposes what the name
// hides, which an identity may need. So a decision of the arith tactic
// (ArithCtx.Decide) is tried as the hypotheses spell it and then with
// every defined variable eliminated: the target and each hypothesis of
// its context read at the definitions together (definitionReading), a
// definition's own equation, which then reads `e = e`, left out. Target
// and context so spell one term one way — read on the target alone,
// `ρ = |c| + δ` would turn the goal's `ρ ^ n` into `(|c| + δ) ^ n` beside
// hypotheses that still say `ρ ^ n`, two unknowns to the linear prover.
// What that reading decides is carried back to the hypotheses as written;
// a target it does not decide is not rewritten by it.
//
// The leaf itself is read in the rounds of a close, last (prover/tactic,
// leafAtDefinitions over LeafAtDefinitions here): where a round has no
// other firing, one firing rewrites every hypothesis and the conclusion at
// the definitions and drops the definitions' own equations. The rounds'
// simplifier then meets one spelling, and no later firing has a
// hypothesis left to respell.
//
// Inside the deciders a VALUE is also read by a leaf of the deep rewrite
// (eqHypValues): a variable a hypothesis pins to a term of no carrier
// variable — a resident `n = 2`, a split branch's `s = 1`, an enumerated
// value — reads as that term in the goal it is decided against. The
// dedicated ℤ stack and the ℕ split's leaf read every rule of their
// hypotheses that way (eqHypSubst).
//
// A target that denies a rule's equation, `¬(v = e)`, is decided by the
// same reading from the other side of the turnstile: the equation joins
// the hypotheses as the rule it would be there, and a hypothesis it then
// reads ⊥ refutes it (denied_value.go).
//
// Capture: a rewrite carries its equation as a hypothesis, and the walk
// renames a binder of the target that collides with a variable free in it
// (prop.DeepRewriteWithEnv).

// varSubst is one rule: `{hyps[at…]} ⊢ from = to`, from a variable, at
// the hypotheses the rule is read off — an equation, or the two
// comparisons of a pair. value marks a rule whose definition names no
// carrier variable.
type varSubst struct {
	from, to Term
	eq       *prop.PropWrapper
	at       []int
	value    bool
}

// varEqSubsts reads the rules off the hypothesis set, elem naming the
// carriers and fixed the variables the context fixes (nil for none). The
// equations are the stated ones, in the hypotheses' order, and after them
// those the pairs of comparisons make at the carriers policy admits
// (paired_equation.go).
func varEqSubsts(hyps []Term, elem, fixed func(Term) bool, policy ArithPolicy) []varSubst {
	unknown := func(t Term) bool { return isVar(t) && (fixed == nil || !fixed(t)) }
	carrierVar := func(v core.VarTerm) bool { return elem(v) && unknown(v) }
	var subs []varSubst
	rule := func(v Term) (varSubst, bool) {
		i := slices.IndexFunc(subs, func(s varSubst) bool { return s.from.AlphaEquals(v) })
		if i < 0 {
			return varSubst{}, false
		}
		return subs[i], true
	}
	// reaches reports whether v is free in e, or in the definition of a
	// variable free in e, and so on down the rules taken so far. The
	// rules are acyclic, so the descent ends.
	var reaches func(e, v Term) bool
	reaches = func(e, v Term) bool {
		for _, w := range e.Frees(carrierVar) {
			if w.AlphaEquals(v) {
				return true
			}
			if s, ok := rule(w); ok && reaches(s.to, v) {
				return true
			}
		}
		return false
	}
	// orientations lists the readings of eq, `{hyps[at…]} ⊢ l = r`, as
	// a definition, in the order they are tried.
	orientations := func(at []int, eq *prop.PropWrapper, l, r Term) []varSubst {
		lToR := varSubst{from: l, to: r, eq: eq, at: at}
		rToL := varSubst{from: r, to: l, eq: eq.EqSym(), at: at}
		switch {
		case unknown(l) && unknown(r):
			if l.Compare(r) > 0 {
				return []varSubst{lToR}
			}
			return []varSubst{rToL}
		case unknown(l):
			return []varSubst{lToR}
		case unknown(r):
			return []varSubst{rToL}
		}
		return nil
	}
	type equation struct {
		readings []varSubst
		taken    bool
	}
	var eqs []equation
	for at, h := range hyps {
		l, r, ok := ext.MatchesEQ(h)
		if !ok || !(isVar(l) || isVar(r)) || !elem(l) || l.AlphaEquals(r) {
			continue
		}
		if readings := orientations([]int{at}, prop.Assume(h), l, r); len(readings) > 0 {
			eqs = append(eqs, equation{readings: readings})
		}
	}
	sided := func(l, r Term) bool { return elem(l) && !l.AlphaEquals(r) && (unknown(l) || unknown(r)) }
	for _, p := range pairedEquations(hyps, policy, sided, -1) {
		if readings := orientations(p.at, p.eq, p.l, p.r); len(readings) > 0 {
			eqs = append(eqs, equation{readings: readings})
		}
	}
	for i := range eqs {
		for _, s := range eqs[i].readings {
			if _, defined := rule(s.from); defined || len(s.to.Frees(carrierVar)) > 0 {
				continue
			}
			s.value = true
			subs, eqs[i].taken = append(subs, s), true
			break
		}
	}
	for i := range eqs {
		if eqs[i].taken {
			continue
		}
		for _, s := range eqs[i].readings {
			if _, defined := rule(s.from); defined || reaches(s.to, s.from) {
				continue
			}
			subs = append(subs, s)
			break
		}
	}
	return subs
}

// eqHypSubst is the variable-sided rule as a rewrite leaf at the number
// carriers elem names: a variable a rule defines reads as its definition,
// `{h} ⊢ v = e`, or `{h, k} ⊢ v = e` for a pair read under policy.
func eqHypSubst(hyps []Term, elem func(Term) bool, policy ArithPolicy) prop.Rewrite {
	return varSubstLeaf(varEqSubsts(hyps, elem, nil, policy))
}

// eqHypValues is the leaf of the values alone: a variable the hypotheses
// give a value reads as the value.
func eqHypValues(hyps []Term, elem func(Term) bool, policy ArithPolicy) prop.Rewrite {
	return varSubstLeaf(valuesOf(varEqSubsts(hyps, elem, nil, policy)))
}

// eqHypValuesUnder is eqHypValues at every carrier the context reads, the
// structure rings' among them.
func eqHypValuesUnder(hyps []Term, policy ArithPolicy) prop.Rewrite {
	elem, fixed := ruleScopeUnder(hyps)
	return varSubstLeaf(valuesOf(varEqSubsts(hyps, elem, fixed, policy)))
}

func valuesOf(subs []varSubst) []varSubst {
	return slices.DeleteFunc(subs, func(s varSubst) bool { return !s.value })
}

// varSubstLeaf is the leaf of a rule set.
func varSubstLeaf(subs []varSubst) prop.Rewrite {
	if len(subs) == 0 {
		return func(Term) *prop.PropWrapper { return nil }
	}
	return func(s Term) *prop.PropWrapper {
		if !isVar(s) {
			return nil
		}
		for _, sb := range subs {
			if s.AlphaEquals(sb.from) {
				return sb.eq
			}
		}
		return nil
	}
}

// fnEqSubsts reads the function definitions off the hypothesis set, in
// the hypotheses' order: an equation between a variable and a
// λ-abstraction, either way round, the variable one the context does not
// fix and no rule of taken or of the result defines. taken is the rules
// already read off hyps; a definition that reaches its own variable
// through them and the function rules before it is no rule.
func fnEqSubsts(hyps []Term, fixed func(Term) bool, taken []varSubst) []varSubst {
	isLambda := func(t Term) bool { _, ok := t.AsAbsTerm(); return ok }
	anyVar := func(core.VarTerm) bool { return true }
	rules := slices.Clone(taken)
	rule := func(v Term) (varSubst, bool) {
		i := slices.IndexFunc(rules, func(s varSubst) bool { return s.from.AlphaEquals(v) })
		if i < 0 {
			return varSubst{}, false
		}
		return rules[i], true
	}
	var reaches func(e, v Term) bool
	reaches = func(e, v Term) bool {
		for _, w := range e.Frees(anyVar) {
			if w.AlphaEquals(v) {
				return true
			}
			if s, ok := rule(w); ok && reaches(s.to, v) {
				return true
			}
		}
		return false
	}
	var fns []varSubst
	for at, h := range hyps {
		l, r, ok := ext.MatchesEQ(h)
		if !ok {
			continue
		}
		eq := prop.Assume(h)
		if isLambda(l) {
			l, r, eq = r, l, eq.EqSym()
		}
		if !isVar(l) || !isLambda(r) || fixed(l) {
			continue
		}
		if _, defined := rule(l); defined || reaches(r, l) {
			continue
		}
		s := varSubst{from: l, to: r, eq: eq, at: []int{at}}
		fns, rules = append(fns, s), append(rules, s)
	}
	return fns
}

// fnSubstLeaf is the leaf of the function rules: an application of a
// defined function reads as the definition's body at the arguments, and
// the function standing unapplied as the λ.
func fnSubstLeaf(fns []varSubst) prop.Rewrite {
	if len(fns) == 0 {
		return func(Term) *prop.PropWrapper { return nil }
	}
	return func(s Term) *prop.PropWrapper {
		head, args := ext.MatchesApply(s)
		if !isVar(head) {
			return nil
		}
		for _, f := range fns {
			if !head.AlphaEquals(f.from) {
				continue
			}
			w := f.eq // {h} ⊢ F = λx. e
			for _, arg := range args {
				w = w.RightApply(arg).RewriteConclRhs(prop.BetaRewrite)
			}
			return w
		}
		return nil
	}
}

// definitionReading is a hypothesis set read at its own definitions: the
// elimination a decision of the arith tactic is made under.
type definitionReading struct {
	// read[j] is hyps[j] with every defined variable replaced, and
	// bridges[j] its `{hyps[j], definitions} ⊢ read[j]`, nil where
	// hyps[j] names none.
	read    []Term
	bridges []*prop.PropWrapper
	// defines[j] marks a hypothesis a rule was read off: its equation,
	// which read is `e = e`, or a comparison of its pair, which read is
	// `e ≤ e`. It is no hypothesis of the context.
	defines []bool
	// target reads a target: `{definitions} ⊢ t = t′`, nil where t names
	// no defined variable.
	target prop.Rewrite
}

// readAtDefinitions reads hyps at the rules they hold under policy, the
// function definitions among them; nil where they hold none.
func readAtDefinitions(hyps []Term, policy ArithPolicy) *definitionReading {
	elem, fixed := ruleScopeUnder(hyps)
	subs := varEqSubsts(hyps, elem, fixed, policy)
	fns := fnEqSubsts(hyps, fixed, subs)
	if len(subs) == 0 && len(fns) == 0 {
		return nil
	}
	anyHyp := func(pred func(prop.Term) bool) bool { return slices.ContainsFunc(hyps, pred) }
	d := &definitionReading{
		read:    make([]Term, len(hyps)),
		bridges: make([]*prop.PropWrapper, len(hyps)),
		defines: make([]bool, len(hyps)),
		target:  prop.DeepRewriteWithEnv(anyHyp, fnSubstLeaf(fns), varSubstLeaf(subs)),
	}
	for _, s := range slices.Concat(subs, fns) {
		for _, at := range s.at {
			d.defines[at] = true
		}
	}
	for j, h := range hyps {
		d.read[j] = h
		if d.defines[j] {
			continue
		}
		if w := d.target(h); w != nil {
			d.read[j] = prop.Rhs(w)
			d.bridges[j] = w.EqMP(prop.Assume(h)) // {h, definitions} ⊢ read[j]
		}
	}
	return d
}

// ruleScopeUnder is the rule's scope under hyps: elem, the carriers — the
// number carriers and the structure rings' (carrierElemUnder) — and fixed,
// the variables free in a structure fact among hyps. The structure facts
// are read off hyps once, and only when a term of no number carrier, or a
// variable, is asked about.
func ruleScopeUnder(hyps []Term) (elem, fixed func(Term) bool) {
	var carriers []core.HolType
	var constants []core.VarTerm
	read := false
	load := func() {
		if read {
			return
		}
		read = true
		carriers = structureCarriers(hyps)
		if structureLaws == nil {
			return
		}
		for _, h := range hyps {
			if _, ok := structureCarrierOf(h, structureLaws); ok {
				constants = append(constants, h.Frees(func(core.VarTerm) bool { return true })...)
			}
		}
	}
	elem = func(t Term) bool {
		if carrierElem(t) {
			return true
		}
		load()
		return slices.ContainsFunc(carriers, t.Type().Equals)
	}
	fixed = func(v Term) bool {
		load()
		return slices.ContainsFunc(constants, func(c core.VarTerm) bool { return c.AlphaEquals(v) })
	}
	return elem, fixed
}
