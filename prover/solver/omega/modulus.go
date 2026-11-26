package omega

import (
	"fmt"
	"iter"
	"reflect"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// The modulus: a carrier's absolute value into ℝ, read by the real layer.
//
// A modulus is a real number, so it stands in ℝ's rows as an atom keyed
// by its spelled argument. Two things about it are read here, from the
// laws its chapter states (ModulusLaws, installed by library/serve):
//
//   - its laws across the carrier's operations, as rewrites toward the
//     leaves (modulusSimpStep): `|x·y| = |x|·|y|`, `|x/y| = |x|/|y|`,
//     `|xⁿ| = |x|ⁿ`, `|−x| = |x|` and the like. Every law is an
//     unconditional equation whose left side is the modulus of a compound
//     term and whose right side applies the modulus to the law's
//     variables only, so the rewrite pushes the modulus strictly inward
//     and terminates. A sum or a difference under a modulus matches no
//     law and stays one unknown, as spelled: `|z − w|` and `|w − z|` are
//     two atoms, and the law that relates them is cited.
//   - its sign (modulusProver): `&0 ≤ |t|` for every modulus a decision's
//     hypotheses and goal spell outside a binder, held beside the
//     hypotheses for that decision, as ℝ's rows hold `&0 ≤ &n` for a
//     cast.
//
//   - its zero test (modulus_zero.go): a term and its modulus vanish
//     together, so what the carrier's ring shows of a modulus's argument
//     — zero, or not zero — is a fact about the modulus for ℝ's rows, and
//     what ℝ's rows show of a modulus is a fact about its argument for
//     the ring.
//
// All three read a hypothesis as they read the goal: the rewrite is a
// leaf of the hypothesis pre-simp and of every decided target, and the
// sign and zero-test facts join the hypotheses of every decision,
// whichever target it decides. The triangle inequality and every other
// estimate of a sum is an inequality with a point to choose, no rewrite,
// and is not read.

// ModulusLaws are a carrier's modulus as its chapter states it. Nonneg
// names the modulus; every other field is one equation read left to
// right, and a nil one is a law the carrier does not state.
type ModulusLaws struct {
	// Nonneg: ∀z. &0 ≤ |z|.
	Nonneg *prop.PropWrapper

	Mul  *prop.PropWrapper // ∀z w. |z·w| = |z|·|w|
	Inv  *prop.PropWrapper // ∀z. |inv z| = inv |z|
	Div  *prop.PropWrapper // ∀z w. |z/w| = |z|/|w|
	Pow  *prop.PropWrapper // ∀z n. |zⁿ| = |z|ⁿ
	Neg  *prop.PropWrapper // ∀z. |−z| = |z|
	Conj *prop.PropWrapper // ∀z. |conj z| = |z|
	// OfReal: ∀x. |embed x| = real_abs(x), at the carrier's copy of ℝ.
	OfReal *prop.PropWrapper
	// Unit: |i| = &1, the modulus of a named element.
	Unit *prop.PropWrapper

	// The zero test, read as facts and never as rewrites (modulus_zero.go).
	// EqZero: ∀z. |z| = &0 ⇔ z = zero, and PosIffNonzero: ∀z. &0 < |z| ⇔
	// ¬(z = zero), zero the carrier's. Stated together or not at all.
	EqZero, PosIffNonzero *prop.PropWrapper
}

// modulusRule is one law ready to fire: its binders in order, and the
// pattern its left side applies the modulus to.
type modulusRule struct {
	field   string
	law     *prop.PropWrapper
	binders []core.VarTerm
	pattern Term
}

// modulusReading is the installed modulus: the map, its sign law, its
// rules and its zero test (nil where the carrier states none).
type modulusReading struct {
	fn     Term
	nonneg *prop.PropWrapper
	rules  []modulusRule
	zero   *modulusZeroTest
}

var (
	installedModulus      *modulusReading
	modulusFoundationKeys map[core.PropKey]bool
)

// SetModulusLaws installs a carrier's modulus (nil uninstalls). A law
// that is not an equation of the shape the rewrite reads panics here:
// one that put the modulus back on a compound term would not terminate.
func SetModulusLaws(l *ModulusLaws) {
	resetConstraintMemos()
	if l == nil {
		installedModulus = nil
		return
	}
	if l.Nonneg == nil {
		panic("omega.SetModulusLaws: no Nonneg law, which names the modulus")
	}
	z, body := forallBinders(l.Nonneg.Conclusion())
	zero, at, ok := realDomain.matchLe(body)
	var fn Term
	if ok && len(z) == 1 && isRealZero(zero) {
		if app, isApp := at.AsAppliedTerm(); isApp && app.Arg().AlphaEquals(z[0]) {
			fn = app.Fun()
		}
	}
	if fn == nil || l.Nonneg.NumHyps() > 0 || len(fn.Frees(func(core.VarTerm) bool { return true })) > 0 {
		panic(fmt.Sprintf("omega.SetModulusLaws: Nonneg is not `∀z. &0 ≤ m(z)` for a closed m: %s",
			ext.PrintTerm(l.Nonneg.Conclusion())))
	}
	if want := core.MakeFun(z[0].Type(), dsl.RealType); !fn.Type().Equals(want) {
		panic(fmt.Sprintf("omega.SetModulusLaws: the modulus %s is not a map into real", ext.PrintTerm(fn)))
	}
	m := &modulusReading{fn: fn, nonneg: l.Nonneg}
	v := reflect.ValueOf(l).Elem()
	for i := range v.NumField() {
		name := v.Type().Field(i).Name
		law, _ := v.Field(i).Interface().(*prop.PropWrapper)
		if name == "Nonneg" || name == "EqZero" || name == "PosIffNonzero" || law == nil {
			continue
		}
		m.rules = append(m.rules, m.rule(name, law))
	}
	m.zero = m.zeroTest(l.EqZero, l.PosIffNonzero)
	installedModulus = m
}

// forallBinders peels the leading ∀-binders of t: the bound variables in
// order and the body they are free in.
func forallBinders(t Term) (binders []core.VarTerm, body Term) {
	for {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			return binders, t
		}
		binders = append(binders, abs.Var())
		t = abs.Body()
	}
}

// rule reads law as `∀xs. m(p) = r` and checks what the rewrite relies
// on: p is no bare variable and holds every binder, so a match grounds
// the law; p holds no modulus, and r applies the modulus to binders
// only, so every firing moves the modulus strictly inward.
func (m *modulusReading) rule(field string, law *prop.PropWrapper) modulusRule {
	refuse := func(why string) {
		panic(fmt.Sprintf("omega.SetModulusLaws: %s is not a law the modulus rewrite reads (%s): %s",
			field, why, ext.PrintTerm(law.Conclusion())))
	}
	if law.NumHyps() > 0 {
		refuse("it has hypotheses")
	}
	binders, body := forallBinders(law.Conclusion())
	lhs, rhs, ok := ext.MatchesEQ(body)
	if !ok {
		refuse("not an equation")
	}
	pattern, ok := m.argument(lhs)
	if !ok {
		refuse("its left side is not the modulus of a term")
	}
	isBinder := func(t Term) bool {
		return slices.ContainsFunc(binders, func(b core.VarTerm) bool { return t.AlphaEquals(b) })
	}
	if isBinder(pattern) {
		refuse("its left side is the modulus of a variable")
	}
	for _, b := range binders {
		if !pattern.HasFree(b) {
			refuse(fmt.Sprintf("the binder %s is not in its left side", ext.PrintTerm(b)))
		}
	}
	inward := func(side Term, allow func(Term) bool) bool {
		return walkTerm(side, func(s Term) bool {
			arg, isModulus := m.argument(s)
			return !isModulus || allow(arg)
		})
	}
	if !inward(pattern, func(Term) bool { return false }) {
		refuse("a modulus stands inside its left side")
	}
	if !inward(rhs, isBinder) {
		refuse("its right side applies the modulus to a compound term")
	}
	return modulusRule{field: field, law: law, binders: binders, pattern: pattern}
}

// argument reports whether t is the modulus applied, and to what.
func (m *modulusReading) argument(t Term) (Term, bool) {
	app, ok := t.AsAppliedTerm()
	if !ok || !app.Fun().AlphaEquals(m.fn) {
		return nil, false
	}
	return app.Arg(), true
}

// match binds the rule's binders so that its pattern is t, first order:
// a binder takes the subterm it meets, the same one at every occurrence.
func (r modulusRule) match(pattern, t Term, bound []Term) bool {
	if i := slices.IndexFunc(r.binders, func(b core.VarTerm) bool { return pattern.AlphaEquals(b) }); i >= 0 {
		if !pattern.Type().Equals(t.Type()) {
			return false
		}
		if bound[i] == nil {
			bound[i] = t
			return true
		}
		return bound[i].AlphaEquals(t)
	}
	if p, ok := pattern.AsAppliedTerm(); ok {
		u, ok := t.AsAppliedTerm()
		return ok && r.match(p.Fun(), u.Fun(), bound) && r.match(p.Arg(), u.Arg(), bound)
	}
	return pattern.AlphaEquals(t)
}

// modulusSimpStep rewrites a modulus by the first law whose left side
// it is: ⊢ m(p[xs]) = r[xs]; nil when t is no modulus, or the modulus of
// a term no law reads.
func modulusSimpStep(t Term) *prop.PropWrapper {
	m := installedModulus
	if m == nil {
		return nil
	}
	arg, ok := m.argument(t)
	if !ok {
		return nil
	}
	for _, r := range m.rules {
		bound := make([]Term, len(r.binders))
		if !r.match(r.pattern, arg, bound) {
			continue
		}
		w := r.law.ConclForAllInsts(bound...)
		if !prop.Lhs(w).AlphaEquals(t) {
			panic(fmt.Sprintf("omega: the modulus law %s matched %s and instantiated to %s",
				r.field, ext.PrintTerm(t), ext.PrintTerm(w.Conclusion())))
		}
		return w
	}
	return nil
}

// moduli appends to atoms the moduli t spells outside every binder,
// each once: the terms a sign fact can be stated about with no variable
// to generalize.
func (m *modulusReading) moduli(t Term, atoms []Term) []Term {
	if _, isAbs := t.AsAbsTerm(); isAbs {
		return atoms
	}
	app, ok := t.AsAppliedTerm()
	if !ok {
		return atoms
	}
	if _, isModulus := m.argument(t); isModulus && !slices.ContainsFunc(atoms, t.AlphaEquals) {
		atoms = append(atoms, t)
	}
	return m.moduli(app.Arg(), m.moduli(app.Fun(), atoms))
}

// facts are, for the moduli the terms spell outside a binder, what a
// decision under resident holds of each: `|u| = &0` where carrier shows
// its argument zero, `&0 < |u|` where it shows it not zero, and `&0 ≤ |u|`
// otherwise — less the ones resident already states. carrier is the zero
// test's evidence (modulus_zero.go), nil where the policy reads none.
func (m *modulusReading) facts(resident []Term, carrier modulusEvidence, terms ...Term) []*prop.PropWrapper {
	var atoms []Term
	for _, t := range terms {
		atoms = m.moduli(t, atoms)
	}
	stated := func(t Term) bool { return slices.ContainsFunc(resident, t.AlphaEquals) }
	// What the carrier's ring reads of resident, found at the first
	// modulus that asks: every modulus has the one carrier.
	var read []Term
	asked := false
	var facts []*prop.PropWrapper
	for _, a := range atoms {
		// A strict sign the context states is the strongest fact a
		// modulus that is not zero has.
		if stated(realLtT(realLit(0), a)) {
			continue
		}
		arg, _ := m.argument(a)
		if m.zero != nil && carrier != nil && !asked {
			read, asked = carrierHyps(resident, arg.Type()), true
		}
		if fact := m.zeroTestFact(read, carrier, a, arg); fact != nil {
			if !stated(fact.Conclusion()) {
				facts = append(facts, fact)
			}
			continue
		}
		// A sign the context states, `&0 ≤ |u|`, is the one the decision
		// reads: the fact beside it would be a second sign for the same
		// unknown.
		if stated(realLeT(realLit(0), a)) {
			continue
		}
		facts = append(facts, m.nonneg.ConclForAllInsts(arg))
	}
	return facts
}

// modulusProver is prove with what is known of every modulus in sight:
// the facts of the moduli of the hypotheses and the goal join the
// hypotheses, and are cut from the proof. A decision that re-enters
// finds them resident and adds nothing.
func modulusProver(prove proveFn, carrier modulusEvidence) proveFn {
	return func(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
		m := installedModulus
		if m == nil {
			return prove(hyps, goal)
		}
		hs := slices.Collect(hyps)
		facts := m.facts(hs, carrier, append(slices.Clone(hs), goal)...)
		if len(facts) == 0 {
			return prove(slices.Values(hs), goal)
		}
		return enrichAndCut(func(h []Term) (*prop.PropWrapper, bool) {
			return prove(slices.Values(h), goal)
		}, hs, facts)
	}
}

// ModulusInstalled reports whether a modulus is installed.
func ModulusInstalled() bool { return installedModulus != nil }

// ModulusContent reports whether p spells the installed modulus, in its
// conclusion or a hypothesis, under a binder or not — the capability
// classifier's question for this reading.
func ModulusContent(p core.Prop) bool {
	m := installedModulus
	if m == nil {
		return false
	}
	spells := func(root Term) bool {
		return !walkTerm(root, func(s Term) bool { return !s.AlphaEquals(m.fn) })
	}
	if spells(p.Conclusion()) {
		return true
	}
	for h := range p.HypIter() {
		if spells(h) {
			return true
		}
	}
	return false
}

// SetModulusFoundation installs the modulus laws' capability foundation
// closure for the scope-less gate (the twin of SetStructureBundleFoundation).
func SetModulusFoundation(keys map[core.PropKey]bool) { modulusFoundationKeys = keys }

// ModulusAllowsTarget — the gate for the installed modulus: a proof its
// laws rest on may not read the modulus through them.
func ModulusAllowsTarget(target core.PropKey) bool {
	if target == "" || modulusFoundationKeys == nil {
		return true
	}
	return !modulusFoundationKeys[target]
}
