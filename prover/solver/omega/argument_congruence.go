package omega

import (
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Two applications that differ in their arguments.
//
// The layers decide comparisons of numbers and the equations of the
// carriers they read. An application of a function or a predicate they do
// not read is an atom to them, and two atoms meet only where they are one
// term: `f(n + 1 + 1)` and `f(n + 2)` are two unknowns, and so are
// `x ∈ S(n - i)` and a hypothesis `x ∈ S(q + 1)` beside `q = n - 1 - i`.
// But an application is determined by its head and its arguments, and
// whether two arguments are equal is a question the decider answers. So
// two applications of one head are compared argument by argument, each
// pair that is not one term asked as an equation of the whole decider
// under the same hypotheses; where every pair is decided equal the two
// applications are equal by congruence (core.PropApply). An argument
// that is itself an application of one head on both sides is compared the
// same way, and two abstractions by their bodies at one variable, so the
// comparison reaches an index inside a set-builder.
//
// Where it is read, on the target of a decision:
//   - an equation between two applications of one head is ⊤ — at a carrier
//     a ring reads (a number carrier, a structure ring's) only between two
//     applications that ring does not read, an equation of its sums and
//     products being the ring's own;
//   - an equation is ⊤ where a hypothesis states it up to the arguments of
//     its two sides, either way round;
//   - a formula no layer reads is ⊤ where a hypothesis is the same
//     application up to its arguments, ⊥ where the negation of one is:
//     the reading prop.FormulaDecideByHyps gives a formula a hypothesis
//     states exactly.
//
// A comparison of two atoms at a number carrier, `g(n + 1 + 1) ≤
// g(n + 2)`, is the layers' formula and is not read here.
//
// Every step is the kernel's: the argument equations are the decider's
// theorems, and the congruence, the abstraction and the transitivity
// through a hypothesis are core rules. An argument equation asked while
// the same equation is being asked further up is declined, so the
// comparison ends: the equations it can ask are between subterms of the
// target and of the hypotheses, finitely many. The answers are kept for
// the leaf's hypotheses (_ArgumentQuestions), so the comparison costs one
// decision per equation and not one per way of reaching it.

// argumentCongruence is the leaf over decide, the decider the argument
// equations are asked of: the rewrite this leaf is one leaf of. policy
// and reader find the structure rings that read a carrier.
func argumentCongruence(hyps []Term, policy ArithPolicy, reader *LibraryReader, decide func() prop.Rewrite) prop.Rewrite {
	questions := newArgumentQuestions()
	read := ringReading(hyps, policy, reader)
	var equal, decided func(s, t Term) *prop.PropWrapper
	// equal is `{…} ⊢ s = t` for two applications of one head whose
	// arguments decide equal pair by pair, or two abstractions whose
	// bodies do; nil otherwise.
	equal = func(s, t Term) *prop.PropWrapper {
		if s.AlphaEquals(t) {
			return prop.WrapProp(core.Refl(s))
		}
		if sa, ok := s.AsAbsTerm(); ok {
			// The bodies at s's variable, where neither t nor a
			// hypothesis names it, so the abstraction rule applies.
			ta, ok := t.AsAbsTerm()
			x := sa.Var()
			named := func(u Term) bool { return len(u.Frees(func(v core.VarTerm) bool { return v.Equals(x) })) > 0 }
			if !ok || !x.Type().Equals(ta.Var().Type()) || named(t) || slices.ContainsFunc(hyps, named) {
				return nil
			}
			eq := decided(sa.Body(), ta.Body().Substitute(core.MakeTermSubst(ta.Var(), x)))
			if eq == nil || slices.ContainsFunc(eq.Hyps(), named) {
				return nil
			}
			return eq.Abs(x) // ⊢ (λx. sb) = (λx. tb)
		}
		sh, sargs := ext.MatchesApply(s)
		th, targs := ext.MatchesApply(t)
		if len(sargs) == 0 || len(sargs) != len(targs) || !sh.Equals(th) {
			return nil
		}
		acc := prop.WrapProp(core.Refl(sh)) // ⊢ h = h
		for i := range sargs {
			eq := decided(sargs[i], targs[i])
			if eq == nil {
				return nil
			}
			acc = acc.Apply(eq) // ⊢ h a₁…aᵢ = h b₁…bᵢ
		}
		return acc
	}
	// decided is `{…} ⊢ a = b`: one term, the equation decided ⊤, or the
	// two equal by their own arguments.
	decided = func(a, b Term) *prop.PropWrapper {
		if a.AlphaEquals(b) {
			return prop.WrapProp(core.Refl(a))
		}
		if !a.Type().Equals(b.Type()) {
			return nil
		}
		question := eqT(a, b)
		return questions.ask(question.AlphaKey(), func() *prop.PropWrapper {
			if d := decide()(question); d != nil && prop.Rhs(d).Equals(prop.T) {
				return d.EqSym().EqMP(prop.DerivesTrue)
			}
			return equal(a, b)
		})
	}
	// stated is `{…, h} ⊢ l = r` for an equation h that states it up to
	// the arguments of its sides, either way round; nil where none does.
	stated := func(t, l, r Term) *prop.PropWrapper {
		for _, h := range hyps {
			hl, hr, ok := ext.MatchesEQ(h)
			if !ok || !hl.Type().Equals(l.Type()) || h.AlphaEquals(t) {
				continue
			}
			for _, sides := range [][2]Term{{hl, hr}, {hr, hl}} {
				left := equal(l, sides[0])
				if left == nil {
					continue
				}
				right := equal(sides[1], r)
				if right == nil {
					continue
				}
				given := prop.Assume(h) // {h} ⊢ hl = hr
				if !sides[0].AlphaEquals(hl) {
					given = given.EqSym()
				}
				return left.EqTrans(given).EqTrans(right)
			}
		}
		return nil
	}
	return func(t Term) *prop.PropWrapper {
		if !t.Type().Equals(core.TypeBool()) {
			return nil
		}
		if l, r, ok := ext.MatchesEQ(t); ok {
			if l.AlphaEquals(r) || read.carrier(l) && !(read.unread(l) && read.unread(r)) {
				return nil
			}
			if w := equal(l, r); w != nil {
				return eqtIntro(w)
			}
			if w := stated(t, l, r); w != nil {
				return eqtIntro(w)
			}
			return nil
		}
		head, args := ext.MatchesApply(t)
		if len(args) == 0 || readByItsParts(t) || isPureArithFormula(t) {
			return nil
		}
		for _, h := range hyps {
			positive := h
			negated := ext.MatchesNOT(h)
			if negated != nil {
				positive = negated
			}
			ph, pargs := ext.MatchesApply(positive)
			if len(pargs) != len(args) || !ph.Equals(head) || positive.AlphaEquals(t) {
				continue
			}
			w := equal(t, positive) // {…} ⊢ t = positive
			if w == nil {
				continue
			}
			if negated == nil {
				return w.EqTrans(eqtIntro(prop.Assume(h))) // {…, h} ⊢ t = ⊤
			}
			return w.EqTrans(prop.BooleanThms["p ⇔ ⊥"](positive).EqSym().EqMP(prop.Assume(h))) // {…, ¬p} ⊢ t = ⊥
		}
		return nil
	}
}

// _ArgumentQuestions keeps the answers to the argument equations one leaf
// asks, each keyed by its equation up to bound names. An answer is the
// equation's theorem under the leaf's hypotheses, or nil where the
// decider has none.
//
// A question asked while it is open, being worked out further up, is
// declined: it answers nil there, and the answer being worked out
// directly above rests on that decline. A theorem is the question's
// answer wherever it is asked again, whatever was declined on the way to
// it. A nil is kept where working the question out again would go the
// same way and end in nil again:
//
//   - settled, where no decline went into it, or where the declines that
//     did are of itself and of questions it reached, which it would meet
//     again;
//   - held, where it rests on the decline of questions open above it.
//     Asked again while they are open it answers nil, and the asker's
//     answer rests on the same questions.
//
// A held nil follows the questions it rests on as they close. One that
// closes with a settled nil answers nil from then on as its decline did,
// so the nils held on it rest on one question fewer, and one left
// resting on none is settled. One that closes with a held nil hands the
// nils held on it what it rests on itself.
//
// A theorem is what a nil reached under a decline may have lacked. So a
// theorem found ends every held nil, and a nil a decline went into is
// not kept where a theorem was found while it was worked out, nor are
// the nils held on it: part of that work was done without the theorem.
//
// So a question is worked out again only after a theorem is found: once,
// and once more as each question that was open at the theorem closes.
// Keeping only the answers no decline went into works a question out
// once for every path that reaches it through the others.
type _ArgumentQuestions struct {
	settled map[core.TermKey]*prop.PropWrapper
	open    map[core.TermKey]*_OpenQuestion
	asking  []*_OpenQuestion // the open questions, outermost first
	held    map[core.TermKey]map[*_OpenQuestion]bool
	found   int // theorems found so far
}

// _OpenQuestion is a question being worked out.
type _OpenQuestion struct {
	// found is the table's count of theorems when the question was asked.
	found int
	// declined reports whether a decline went into the answer so far, of
	// this question or of any other.
	declined bool
	// rests is the open questions whose decline went into the answer so
	// far: this one or one above it, and so open for as long as it is.
	rests map[*_OpenQuestion]bool
}

func newArgumentQuestions() *_ArgumentQuestions {
	return &_ArgumentQuestions{
		settled: map[core.TermKey]*prop.PropWrapper{},
		open:    map[core.TermKey]*_OpenQuestion{},
		held:    map[core.TermKey]map[*_OpenQuestion]bool{},
	}
}

// ask answers the question at key, working it out with work where no
// answer is kept. work may ask further questions of the table.
func (q *_ArgumentQuestions) ask(key core.TermKey, work func() *prop.PropWrapper) *prop.PropWrapper {
	if w, ok := q.settled[key]; ok {
		return w
	}
	if o, ok := q.open[key]; ok {
		q.restOn(map[*_OpenQuestion]bool{o: true})
		return nil
	}
	if rests, ok := q.held[key]; ok {
		q.restOn(rests)
		return nil
	}
	o := &_OpenQuestion{found: q.found, rests: map[*_OpenQuestion]bool{}}
	q.open[key] = o
	q.asking = append(q.asking, o)
	w := work()
	q.asking = q.asking[:len(q.asking)-1]
	delete(q.open, key)
	delete(o.rests, o)
	if w != nil {
		q.settled[key] = w
		q.found++
		clear(q.held)
		return w
	}
	switch theoremSince := o.found != q.found; {
	case len(o.rests) == 0 && !(o.declined && theoremSince):
		q.settled[key] = nil
		q.closed(o, nil)
		return nil
	case theoremSince:
		for k, rests := range q.held {
			if rests[o] {
				delete(q.held, k)
			}
		}
	default:
		q.closed(o, o.rests)
		q.held[key] = o.rests
	}
	q.restOn(o.rests)
	return nil
}

// restOn records that the answer being worked out directly has been
// given a nil that is not settled, one that rests on the decline of the
// questions in rests.
func (q *_ArgumentQuestions) restOn(rests map[*_OpenQuestion]bool) {
	n := len(q.asking)
	if n == 0 {
		return
	}
	asker := q.asking[n-1]
	asker.declined = true
	for o := range rests {
		asker.rests[o] = true
	}
}

// closed moves the nils held on o, which has closed with a nil that is
// kept, onto the questions that nil rests on, and settles those left
// resting on none.
func (q *_ArgumentQuestions) closed(o *_OpenQuestion, rests map[*_OpenQuestion]bool) {
	for k, held := range q.held {
		if !held[o] {
			continue
		}
		delete(held, o)
		for above := range rests {
			held[above] = true
		}
		if len(held) == 0 {
			q.settled[k] = nil
			delete(q.held, k)
		}
	}
}

// readByItsParts reports whether t is a connective's or a quantifier's
// formula, which the rewrites around this leaf read by its parts.
func readByItsParts(t Term) bool {
	if ext.MatchesNOT(t) != nil {
		return true
	}
	if _, _, ok := prop.MatchesAND(t); ok {
		return true
	}
	if _, _, ok := prop.MatchesOR(t); ok {
		return true
	}
	if _, _, ok := prop.MatchesIMPLY(t); ok {
		return true
	}
	if _, _, ok := ext.MatchesIFF(t); ok {
		return true
	}
	return !ext.MatchesFORALL(t).IsZero() || !ext.MatchesEXISTS(t).IsZero()
}

// ringRead is what the rings under a context read: the carriers, and
// the operations at each.
type ringRead struct {
	domains func(Term) []*Domain
}

// ringReading is the rings under hyps: the number carriers' and the
// structure rings' at the carriers hyps or the installed instances give
// (structureFactsAt), found once per carrier.
func ringReading(hyps []Term, policy ArithPolicy, reader *LibraryReader) ringRead {
	byType := map[core.TypeKey][]*Domain{}
	return ringRead{domains: func(t Term) []*Domain {
		for _, d := range []*Domain{natDomain, intDomain, realDomain} {
			if d.isElem(t) {
				return []*Domain{d}
			}
		}
		key := t.Type().Key()
		if ds, ok := byType[key]; ok {
			return ds
		}
		var ds []*Domain
		if policy.Structure {
			for _, sr := range structureFactsAt(hyps, t.Type(), policy.StructureInstances, reader) {
				ds = append(ds, sr.dom)
			}
		}
		byType[key] = ds
		return ds
	}}
}

// carrier reports whether a ring reads t's type.
func (r ringRead) carrier(t Term) bool { return len(r.domains(t)) > 0 }

// unread reports whether t is an application no ring at its carrier
// reads: no sum, product, difference, negation, successor, power or
// literal of one.
func (r ringRead) unread(t Term) bool {
	if _, args := ext.MatchesApply(t); len(args) == 0 {
		return false
	}
	for _, d := range r.domains(t) {
		if d.readsOperation(t) {
			return false
		}
	}
	return true
}

// readsOperation reports whether t is one of d's operations or literals.
func (d *Domain) readsOperation(t Term) bool {
	if _, shaped, _ := d.asLiteral(t); shaped {
		return true
	}
	if _, _, ok := d.matchPlus(t); ok {
		return true
	}
	if _, _, ok := d.matchStar(t); ok {
		return true
	}
	if d.matchSuc != nil {
		if _, ok := d.matchSuc(t); ok {
			return true
		}
	}
	if d.matchSub != nil {
		if _, _, ok := d.matchSub(t); ok {
			return true
		}
	}
	if d.matchNeg != nil {
		if _, ok := d.matchNeg(t); ok {
			return true
		}
	}
	if d.matchPow != nil {
		if _, _, ok := d.matchPow(t); ok {
			return true
		}
	}
	return false
}
