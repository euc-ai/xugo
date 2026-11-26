package omega

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// The zero test of the modulus: a term and its modulus vanish together.
//
// The modulus is a real number and its argument an element of the
// carrier's ring, so a statement that one of them is zero, or is not, is
// read by one layer and is about a term the other layer reads. The two
// laws of the test (ModulusLaws.EqZero, PosIffNonzero) carry it across,
// each way:
//
//   - to ℝ's rows (modulusReading.zeroTestFact): for a modulus `|s|` a
//     decision spells, `|s| = &0` where the carrier's ring shows s zero —
//     by a ring identity, `|c − c|`, or from the context's equations — and
//     `&0 < |s|` where it shows s not zero, in place of the sign `&0 ≤ |s|`;
//   - to the carrier's ring (modulusCarrierFacts): for a modulus `|s|` the
//     hypotheses spell, `¬(s = zero)` where ℝ's rows show `&0 < |s|` and
//     `s = zero` where they show `|s| ≤ &0`, beside the hypotheses of the
//     ring's decision.
//
// So `z ≠ c ⊢ &0 < |z − c|` and `&0 < |z − c| ⊢ z ≠ c` close alike, a
// divisor `z − c` has its evidence from a punctured disc's `&0 < |z − c|`,
// and `|c − c| < r` is `&0 < r`.
//
// Each layer asks the other's evidence as that layer holds it without the
// test: the ring's identity, combination and nonzero evidence over the
// hypotheses as written, and ℝ's linear prover over the hypotheses and the
// moduli's signs. Neither asks the test in turn, so the two do not
// re-enter each other.

// modulusZeroTest is the zero test of an installed modulus: the carrier's
// zero and the two laws.
type modulusZeroTest struct {
	zero                  Term
	eqZero, posIffNonzero *prop.PropWrapper
}

// zeroTest reads the two laws of the test, nil where the carrier states
// neither. One without the other, or a law of another shape, panics: a
// test read one way round is the asymmetry the pair exists to close.
func (m *modulusReading) zeroTest(eqZero, posIffNonzero *prop.PropWrapper) *modulusZeroTest {
	if eqZero == nil && posIffNonzero == nil {
		return nil
	}
	if eqZero == nil || posIffNonzero == nil {
		panic("omega.SetModulusLaws: EqZero and PosIffNonzero are stated together or not at all")
	}
	refuse := func(field string, law *prop.PropWrapper, want string) {
		panic(fmt.Sprintf("omega.SetModulusLaws: %s is not `%s`: %s", field, want, ext.PrintTerm(law.Conclusion())))
	}
	// vanishes reads law as `∀z. lhs(m(z)) ⇔ rhs` and returns rhs.
	vanishes := func(field string, law *prop.PropWrapper, want string, lhs func(modulus Term) Term) (core.VarTerm, Term) {
		binders, body := forallBinders(law.Conclusion())
		l, r, ok := ext.MatchesEQ(body)
		if !ok || len(binders) != 1 || law.NumHyps() > 0 || !l.AlphaEquals(lhs(ext.Apply(m.fn, binders[0]))) {
			refuse(field, law, want)
		}
		return binders[0], r
	}
	z, isZero := vanishes("EqZero", eqZero, "∀z. |z| = &0 ⇔ z = zero",
		func(modulus Term) Term { return eqT(modulus, realLit(0)) })
	arg, zero, ok := ext.MatchesEQ(isZero)
	if !ok || !arg.AlphaEquals(z) || len(zero.Frees(func(core.VarTerm) bool { return true })) > 0 {
		refuse("EqZero", eqZero, "∀z. |z| = &0 ⇔ z = zero")
	}
	w, notZero := vanishes("PosIffNonzero", posIffNonzero, "∀z. &0 < |z| ⇔ ¬(z = zero)",
		func(modulus Term) Term { return realLtT(realLit(0), modulus) })
	if !notZero.AlphaEquals(not(eqT(w, zero))) {
		refuse("PosIffNonzero", posIffNonzero, "∀z. &0 < |z| ⇔ ¬(z = zero)")
	}
	return &modulusZeroTest{zero: zero, eqZero: eqZero, posIffNonzero: posIffNonzero}
}

// modulusEvidence is what the carrier's ring shows of a term s under
// hyps: zero, `Γ ⊢ s = zero`, or nonzero, `Γ ⊢ ¬(s = zero)`, Γ ⊆ hyps; both
// nil where it shows neither.
type modulusEvidence func(hyps []Term, s Term) (zero, nonzero *prop.PropWrapper)

// modulusEvidence is the carrier's evidence under the policy: the
// structure ring's at the carrier of the installed modulus. nil where the
// modulus states no zero test or the policy withholds the structure ring.
//
// The ring is asked under the hypotheses it reads and no others
// (carrierHyps): its equations, its disequalities and its structure
// facts. A real decision is asked over one context many times, and over
// that context with a split's guards and pins added at every branch;
// none of those adds a hypothesis the ring reads, so the ring's answer
// for a modulus is found once for all of them (modulusZeroMemo). ℝ's
// arithmetic is not asked for the evidence of an embedded real: the
// modulus of one is rewritten to ℝ's absolute value before a decision
// sees it.
func (p ArithPolicy) modulusEvidence(reader *LibraryReader) modulusEvidence {
	m := installedModulus
	if m == nil || m.zero == nil || !p.Structure || structureLaws == nil {
		return nil
	}
	zero := m.zero.zero
	return func(hyps []Term, s Term) (isZero, nonzero *prop.PropWrapper) {
		for _, sr := range structureFactsAt(hyps, s.Type(), p.StructureInstances, reader) {
			if !sr.comps.zero.AlphaEquals(zero) {
				continue
			}
			b := sr.bind(hyps)
			if !b.members.proveAtoms(s) {
				continue
			}
			if w, ok := b.proveEqWithoutUnitsSigned(hyps, s, zero); ok {
				return w, nil
			}
			if w := b.proveNonzero(hyps, s); w != nil {
				return nil, w
			}
		}
		return nil, nil
	}
}

// carrierHyps lists the hypotheses a structure ring at the carrier τ
// reads: an equation or a disequation between elements of τ, as a
// hypothesis or a conjunct of one, a membership, and a structure fact.
func carrierHyps(hyps []Term, τ core.HolType) []Term {
	reads := func(part Term) bool {
		if inner := ext.MatchesNOT(part); inner != nil {
			part = inner
		}
		if l, _, ok := ext.MatchesEQ(part); ok {
			return l.Type().Equals(τ)
		}
		head, args := ext.MatchesApply(part)
		c, isConst := head.AsConst()
		return isConst && c.Meta() == structureLaws.member && len(args) == 2 && args[0].Type().Equals(τ)
	}
	var out []Term
	for _, h := range hyps {
		if _, ok := structureCarrierOf(h, structureLaws); ok {
			out = append(out, h)
			continue
		}
		if _, _, isConj := prop.MatchesAND(h); isConj {
			if slices.ContainsFunc(conjunctTerms(h), reads) {
				out = append(out, h)
			}
			continue
		}
		if reads(h) {
			out = append(out, h)
		}
	}
	return out
}

// conjunctTerms lists the conjuncts of t, the leaves of its tree of ∧.
func conjunctTerms(t Term) []Term {
	if a, b, ok := prop.MatchesAND(t); ok {
		return append(conjunctTerms(a), conjunctTerms(b)...)
	}
	return []Term{t}
}

// modulusZeroMemo holds what the carrier's ring shows of a modulus's
// argument under the hypotheses the ring reads, for the arith step that
// asked (ReleaseStepMemos).
var modulusZeroMemo linProveMemo

// zeroTestFact is the fact the zero test gives ℝ's rows about the modulus
// a = |arg| under read, the hypotheses the carrier's ring reads
// (carrierHyps): `Γ ⊢ a = &0` where carrier shows arg zero, `Γ ⊢ &0 < a`
// where it shows arg not zero, nil where it shows neither or the modulus
// has no test.
func (m *modulusReading) zeroTestFact(read []Term, carrier modulusEvidence, a, arg Term) *prop.PropWrapper {
	if m.zero == nil || carrier == nil {
		return nil
	}
	key := linQuestionKey(read, a)
	if e, ok := modulusZeroMemo.lookup(key, read, a); ok {
		return e.proof
	}
	var fact *prop.PropWrapper
	isZero, nonzero := carrier(read, arg)
	switch {
	case isZero != nil:
		fact = m.zero.eqZero.ConclForAllInsts(arg).EqSym().EqMP(isZero) // Γ ⊢ |arg| = &0
	case nonzero != nil:
		fact = m.zero.posIffNonzero.ConclForAllInsts(arg).EqSym().EqMP(nonzero) // Γ ⊢ &0 < |arg|
	}
	modulusZeroMemo.store(key, linAnswer{hyps: read, goal: a, proof: fact})
	return fact
}

// modulusCarrierIs reports whether τ is the carrier of an installed
// modulus that states a zero test.
func modulusCarrierIs(τ core.HolType) bool {
	m := installedModulus
	return m != nil && m.zero != nil && m.zero.zero.Type().Equals(τ)
}

// modulusCarrierFacts lists what ℝ's rows show of the arguments of the
// moduli hyps spell outside a binder: `Γ ⊢ ¬(s = zero)` where they show
// `&0 < |s|`, `Γ ⊢ s = zero` where they show `|s| ≤ &0`, Γ ⊆ hyps — less
// the ones hyps already states. The rows are the hypotheses and the sign
// `&0 ≤ |u|` of every modulus in sight, read by the linear prover.
func modulusCarrierFacts(hyps []Term) []*prop.PropWrapper {
	m := installedModulus
	if m == nil || m.zero == nil {
		return nil
	}
	var atoms []Term
	for _, h := range hyps {
		atoms = m.moduli(h, atoms)
	}
	if len(atoms) == 0 {
		return nil
	}
	signs := m.facts(hyps, nil, hyps...)
	shown := func(goal Term) *prop.PropWrapper {
		w, ok := enrichAndCut(func(h []Term) (*prop.PropWrapper, bool) {
			return realLinProveSigned(h, goal)
		}, hyps, signs)
		if !ok {
			return nil
		}
		return w
	}
	stated := func(t Term) bool { return slices.ContainsFunc(hyps, t.AlphaEquals) }
	zero := m.zero.zero
	var facts []*prop.PropWrapper
	for _, a := range atoms {
		arg, _ := m.argument(a)
		if positive := shown(realLtT(realLit(0), a)); positive != nil {
			if fact := m.zero.posIffNonzero.ConclForAllInsts(arg).EqMP(positive); !stated(fact.Conclusion()) {
				facts = append(facts, fact) // Γ ⊢ ¬(arg = zero)
			}
			continue
		}
		if vanishes := shown(eqT(a, realLit(0))); vanishes != nil {
			if fact := m.zero.eqZero.ConclForAllInsts(arg).EqMP(vanishes); !stated(fact.Conclusion()) && !arg.AlphaEquals(zero) {
				facts = append(facts, fact) // Γ ⊢ arg = zero
			}
		}
	}
	return facts
}
