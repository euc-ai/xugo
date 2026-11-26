package proof

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// ---------------------------------------------------------------------------
// Calc — first-class equation / relation chains
// ---------------------------------------------------------------------------
//
// The estimate chain is the native shape of hard-analysis mathematics:
//
//	a  =  t₁  [why]   =  t₂  [why]   =  b  [why]
//	a  ≤  t₁  [why]   ≤  t₂  [why]   ≤  b  [why]
//
// The corpus spells the = form as nested Expect(Trans(bridge), Case,
// Case) trees — two bridges already indent two levels, the pyramid in
// miniature — and the ≤ form as Have/Have/Show blocks whose
// transitivity groundings (CiteSpecialize(trans, a, b, c)) are
// hand-computed plumbing. Calc is the flat spelling of both. Each leg
// names its target term, carries its justification label and proof,
// and the combinator supplies the connective structure:
//
//   - CalcEq desugars to the EXACT nested Trans tree the handwritten
//     spelling produces — same kernel steps, same subgoals, same
//     order, so converting a hand-nested chain keeps recorded .cnf.pb
//     blobs hitting (the Expect / Deduce contract, action.go).
//   - CalcRel.Calc runs as a Deduce-item fact producer: it asserts
//     each pairwise link and folds the running chain through the
//     kit's transitivity certificate, COMPUTING the grounding tuples
//     the hand spelling wrote out. The chained fact ends resident;
//     exactly one unsolved leaf remains (Deduce linearity). Each
//     chained fact closes PREMISE-SCOPED — its two links and the
//     certificate at the computed tuple, everything else cleared
//     (_CalcChainClose) — so a chain is usable inside a context full
//     of resident ∀-facts; the same fold serves CalcOrder. The
//     certificate is any fact a By takes as a premise: a law named by
//     its entry, a certificate, or a resident hypothesis — the
//     transitivity rule of an inductive relation, read out of its
//     rules — bare or already at its leading parameters.
//
// Contracts shared with Have: every leg's proof must CLOSE its leg —
// failure panics immediately with the leg's label — and labels are
// mandatory; folding the chain's plumbing never folds its narrative.

// CalcLeg is one step of a Calc chain: the term the chain reaches,
// the justification label, and the proof of this leg. Construct with
// Leg / FinalLeg for the single-relation chains (CalcEq, CalcRel), or
// with LeLeg / EqLeg for the mixed chain (CalcOrder).
type CalcLeg struct {
	to    Term // nil ⇔ FinalLeg (CalcEq only: the goal's own RHS)
	label string
	body  []Action
	rel   calcRelKind // relUntagged for Leg/FinalLeg; set by LeLeg/EqLeg
	// fold marks the chain-fold's own synthetic leg (the chained fact,
	// proved by _CalcChainClose) as opposed to an author's leg: its
	// failure carries a complete diagnostic of its own, so runLegBody
	// passes it through instead of appending the author-leg advice.
	fold bool
}

// calcRelKind tags which of a CalcOrder chain's two relations a leg
// travels. The single-relation combinators take untagged legs only —
// a tag there names a relation they have no certificate for, which is
// the author reaching for CalcOrder.
type calcRelKind uint8

const (
	relUntagged calcRelKind = iota
	relEq
	relLe
)

func (r calcRelKind) String() string {
	switch r {
	case relEq:
		return "≈"
	case relLe:
		return "≤"
	}
	return "untagged"
}

// Leg is a calc step "… reaches `to`, because label: body". In CalcEq
// the leg proves ⟨previous term⟩ = to; in CalcRel.Calc it proves
// rel(⟨previous term⟩, to).
func Leg(to TermLike, label string, body ...Action) CalcLeg {
	return CalcLeg{to: ext.CoreOf(to), label: label, body: body}
}

// FinalLeg is CalcEq's last step: it proves ⟨previous term⟩ = ⟨the
// goal's RHS⟩, closing the chain without naming the RHS again.
func FinalLeg(label string, body ...Action) CalcLeg {
	return CalcLeg{label: label, body: body}
}

// CalcEq proves the current equational goal L = R as a chain
//
//	L = t₁ = t₂ = … = R
//
// via one Trans bridge per intermediate term. Legs name t₁ … tₖ (the
// last leg is FinalLeg, closing tₖ = R). Desugar: the identical
// right-nested Trans tree the handwritten Expect(Trans(t), Case,
// Case) spelling produces — leg i's proof runs on the subgoal
// ⟨tᵢ₋₁ = tᵢ⟩ and must close it.
func CalcEq(legs ...CalcLeg) Action {
	if len(legs) < 2 {
		panic("CalcEq: a chain needs at least two legs (one bridge + the final leg)")
	}
	requireUntagged("CalcEq", legs)
	for i, leg := range legs[:len(legs)-1] {
		if leg.to == nil {
			panic(fmt.Sprintf("CalcEq: leg %d (%q) has no target term — only the last leg may be FinalLeg", i+1, leg.label))
		}
	}
	if last := legs[len(legs)-1]; last.to != nil {
		panic(fmt.Sprintf("CalcEq: the last leg (%q) must be FinalLeg — the chain closes onto the goal's own RHS", last.label))
	}
	return _CalcEqAction{legs: legs}
}

type _CalcEqAction struct{ legs []CalcLeg }

func (c _CalcEqAction) applyAction(s *Script, root *GoalStackNode) {
	cur := root.unsolvedLeaf(0)
	if cur == nil {
		panic("CalcEq: focus has no unsolved leaves remaining " +
			"(section already proved — extra Step in chain?)" + closedLeafNote(root))
	}
	for _, leg := range c.legs {
		if leg.to == nil { // FinalLeg: the residual leaf IS ⟨prev = R⟩
			runLegBody(s, cur, "CalcEq", leg)
			return
		}
		s.Do(cur, Trans(leg.to.Core()))
		Assert(len(cur.children) == 2)
		left, right := cur.children[0], cur.children[1] // ⟨prev = to⟩, ⟨to = R⟩
		runLegBody(s, left, "CalcEq", leg)
		cur = right
	}
}

// runLegBody applies a leg's proof to its subgoal and enforces the
// eager-close contract with the leg's label in the panic. A leaf the
// proof leaves proved and open is closed first (closeProvedLeaves).
func runLegBody(s *Script, leaf *GoalStackNode, combinator string, leg CalcLeg) {
	// Attribute a failure INSIDE the body to its leg. Without this the
	// author gets a bare engine panic with no way to tell which of a
	// chain's legs raised it — and the most common one here has a
	// standard fix, so it is worth naming.
	func() {
		defer func() {
			if r := recover(); r != nil {
				if leg.fold {
					// The chain-fold's close names the chained fact, its
					// premises and the defect class itself; the author-leg
					// advice below would misdirect (there is no CnfRefute
					// to drop and no cite to swap).
					panic(r)
				}
				panic(fmt.Sprintf("%s: leg %q failed: %v\n"+
					"  (a calc leg is a far smaller goal than the blob it was carved out of, so a cite that "+
					"needed grounding + a refute in the flat spelling often closes the leg on its own. If the "+
					"message above is \"no unsolved leaves\" or \"cite ... closed the section; witnesses are "+
					"unused\", this leg's proof is one step too long: drop its CnfRefute, or swap "+
					"CiteSpecialize for UseLemmaExact.)", combinator, leg.label, r))
			}
		}()
		for _, a := range leg.body {
			a.applyAction(s, leaf)
		}
	}()
	closeProvedLeaves(s, leaf)
	if leaves := leaf.UnsolvedLeaves(); len(leaves) != 0 {
		msg := fmt.Sprintf("%s: leg %q did not close (%d unsolved leaf(ves))",
			combinator, leg.label, len(leaves))
		for _, l := range leaves {
			msg += "\n  leaf: " + prop.PrintProp(l.Goal)
		}
		panic(msg)
	}
}

// closeProvedLeaves closes what a leg's proof leaves proved and open
// under leaf: a leaf whose conclusion is ⊤, and one whose conclusion is
// an equation of a term with itself. A rewrite that brings the two
// sides of a leg to one term ends on the second, and a rewrite after it
// that folds that equation ends on the first; neither closes the goal
// it rewrote.
func closeProvedLeaves(s *Script, leaf *GoalStackNode) {
	for _, l := range leaf.UnsolvedLeaves() {
		concl := l.Goal.Conclusion()
		if concl.Equals(T) {
			s.Do(l, _TrivialSimplify{})
			continue
		}
		if a, b, ok := ext.MatchesEQ(concl); ok && a.AlphaEquals(b) {
			s.Do(l, _Refl{})
		}
	}
}

// CalcRel is the kit for relation chains: the relation as a Prop
// builder plus the transitivity certificate the chain folds through —
// a fact whose open binders are the three terms of a composition, in
// the order (a, b, c) of `Rel(a, b) ∧ Rel(b, c) ⇒ Rel(a, c)`: an entry
// (nat_order.LessEqTrans), a resident rule (the transitivity conjunct
// of an inductive relation's rules), or either at the relation's own
// parameters (DerivableTransitive.At(E, O)). The legs' `to` terms are
// handed back to Rel exactly as passed, so a vocabulary closure may
// type-assert them to its own term-wrapper type.
type CalcRel struct {
	Rel   func(a, b Term) Prop
	Trans CiteTarget
}

// Calc runs as a Deduce-item fact producer: starting from `from`, each
// leg asserts the pairwise link rel(prev, to) (proved by the leg's
// body), and from the second leg on the running chain rel(from, to) is
// asserted alongside, proved by the kit's transitivity certificate
// grounded at the COMPUTED tuple (from, prev, to) — the plumbing the
// hand spelling wrote by hand. All links and the chained fact end
// resident; exactly one unsolved leaf remains.
//
// The chain-fold proof closes PREMISE-SCOPED: over exactly the running
// chained fact, this leg's link and the certificate at the computed
// tuple, with every other resident hypothesis cleared first
// (_CalcChainClose — the By executor's clear-first close). The chained
// leaf is a three-step resolution over those premises, so it closes
// the same in an empty context and in one full of wide ∀-facts; a
// failure there is a defect in the chain, never a missing premise.
//
// Terminal chains. As in CalcOrder.Calc: when a fact the chain would
// assert is α-equal to the goal, the chain has ARRIVED — it is proved
// against the goal instead of asserted beside it, and the block CLOSES
// rather than leaving a leaf. Without this a chain whose endpoint IS
// the section goal cannot be spelled as one Calc at all: AssertTactic
// refuses a claim α-equal to the goal, so the last chain-fold dies with
// "ministep Assert … failed", and the author has to run the Calc across
// the interior waypoints and hand-write the terminal leg as a Show with
// its own ground cites — splitting one chain into two spellings and
// hand-grounding the very transitivity instance Calc exists to compute.
// A terminal chain must be its Deduce block's FINAL item or stand alone
// in the enclosing Chain; legs after the arrival panic.
//
// Grounding ceiling, mid-chain. A leg body may hit "cite … closed the
// section; witnesses are unused — use UseLemmaExact instead". That is
// not a sign the chain is wrong: it means the cited lemma's conclusion
// matched THIS leg exactly, so the install closed the leg before any
// witness was consumed. A calc leg is a much smaller goal than the
// blob it was carved out of, so this happens more often than in the
// hand spelling — the fix is the unground verb for that leg
// (UseLemmaExact), and any CnfRefute after it becomes unnecessary.
func (k CalcRel) Calc(from TermLike, legs ...CalcLeg) Action {
	if len(legs) < 2 {
		panic("CalcRel.Calc: a chain needs at least two legs — a single link is just Have")
	}
	requireUntagged("CalcRel.Calc", legs)
	for i, leg := range legs {
		if leg.to == nil {
			panic(fmt.Sprintf("CalcRel.Calc: leg %d (%q) has no target term — FinalLeg is CalcEq-only", i+1, leg.label))
		}
	}
	return _CalcRelAction{kit: k, from: ext.CoreOf(from), legs: legs}
}

type _CalcRelAction struct {
	kit  CalcRel
	from Term
	legs []CalcLeg
}

func (c _CalcRelAction) applyAction(s *Script, root *GoalStackNode) {
	cur := root.unsolvedLeaf(0)
	if cur == nil {
		panic("CalcRel.Calc: focus has no unsolved leaves remaining " +
			"(section already proved — extra Step in chain?)" + closedLeafNote(root))
	}
	arrived := "" // non-empty once the chain has closed the goal itself
	assertFact := func(claim Prop, leg CalcLeg) {
		if cur.Goal.Conclusion().AlphaEquals(claim.Conclusion()) {
			// Terminal chain — see CalcOrder.Calc's doc for the contract.
			runLegBody(s, cur, "CalcRel.Calc", leg)
			arrived = leg.label
			return
		}
		s.Do(cur, AssertStep(claim))
		Assert(len(cur.children) == 2)
		runLegBody(s, cur.children[0], "CalcRel.Calc", leg)
		cur = cur.children[1]
	}
	prev := c.from
	for i, leg := range c.legs {
		if arrived != "" {
			panic(fmt.Sprintf("CalcRel.Calc: the chain closed the goal at %q, but leg %d (%q) follows — a chain that reaches the goal must end there",
				arrived, i+1, leg.label))
		}
		link := c.kit.Rel(prev, leg.to)
		assertFact(link, leg)
		if i > 0 && arrived == "" {
			label := fmt.Sprintf("calc: chain to leg %d by transitivity", i+1)
			chained := CalcLeg{
				label: label,
				fold:  true,
				body: []Action{_CalcChainClose{
					combinator: "CalcRel.Calc",
					label:      label,
					chained:    c.kit.Rel(c.from, leg.to),
					running:    c.kit.Rel(c.from, prev),
					link:       link,
					instances:  []Fact{foldInstance("CalcRel.Calc", c.kit.Trans, c.from, prev, leg.to)},
				}},
			}
			assertFact(c.kit.Rel(c.from, leg.to), chained)
		}
		prev = leg.to
	}
}

// _CalcChainClose proves one chained fact of a relation chain — the
// fold's own leg, shared by CalcRel.Calc and both CalcOrder branches.
// It closes PREMISE-SCOPED: the leaf is handed to the By executor with
// exactly the running chained fact and this leg's link as resident
// premises and the fold's instances — the kit certificates at the
// tuples the fold computed — as the premises after them, so every
// other ambient hypothesis is cleared before the close (step_by.go,
// phases 1–2 and 4). The running fact and the link are located by
// α-equality against the props the fold asserted, never by index.
//
// Why scoped: the chained leaf is a three-step resolution — the two
// links plus the transitivity instance entail the chained fact — and
// an ambient refute over an analysis context (a dozen resident hyps, a
// ∀∃ coverage fact, a set-builder membership) runs to its budget and
// fails on it, where the hand-written By(link₁, link₂, trans.At(…))
// closes the identical leaf instantly because By clears what it was
// not handed. The chain does what the hand spelling does: its close IS
// that By, the instances the same `cert.At(…)` premises, which is why
// a certificate may be whatever a By takes — an entry, a certificate,
// a resident rule.
//
// Recorded shape: ONE `by` composite per chained fact, its premises
// the two resident facts and the instances.
type _CalcChainClose struct {
	combinator string // for the panic: which Calc verb
	label      string // the fold leg's label ("calc: chain to leg N …")
	chained    Prop   // the fact being proved: Rel(from, to)
	running    Prop   // Rel(from, prev) — resident (previous fold, or the first link)
	link       Prop   // Rel(prev, to) — resident (asserted by this leg)
	// instances are the kit certificates at the tuples the fold
	// computed, in the order the close installs them: the lifts, then
	// the transitivity. Empty on a Leibniz step that touches `=`.
	instances []Fact
}

func (c _CalcChainClose) applyAction(s *Script, root *GoalStackNode) {
	Assert(root.unsolvedLeaf(0) != nil) // assertFact just carved this leaf out
	// Normalized: the chained leaf — two links and the transitivity
	// instance resident, the chained fact the goal — is decided by Basic
	// once the premises are in (split the instance's implication,
	// discharge its antecedent, assume), so the recorder's audit would
	// flag a bare refute here as avoidable at every chain. Shape the
	// close by construction; the refuter is the fallback, not the plan.
	premises := []any{Normalized, ResidentHyp(c.running), ResidentHyp(c.link)}
	for _, inst := range c.instances {
		premises = append(premises, inst)
	}
	defer func() {
		if r := recover(); r != nil {
			panic(c.diagnostic(s, r))
		}
	}()
	closeBy := By(premises...).(_ByAction)
	closeBy.engineShape = true
	closeBy.applyAction(s, root)
}

// diagnostic is the scoped close's failure text. The premise set is
// fixed by the fold and every other hypothesis was cleared, so the
// leaf is fully determined by the premises printed — there is no
// missing premise to look for and no key to record: the chain itself
// is wrong. (Under strict replay the cause is a CNF cache MISS for the
// scoped leaf's key, which is the re-record case; the cause text says
// so.)
func (c _CalcChainClose) diagnostic(s *Script, cause any) string {
	show := func(p Prop) string { return ext.PrintTerm(p.AsProp().Conclusion()) }
	var b strings.Builder
	fmt.Fprintf(&b, "%s: %s — the chained fact could not be closed from its two links and the transitivity instance:\n",
		c.combinator, c.label)
	fmt.Fprintf(&b, "  chained fact:  %s\n", show(c.chained))
	fmt.Fprintf(&b, "  running fact:  %s   (resident: the chain so far)\n", show(c.running))
	fmt.Fprintf(&b, "  link:          %s   (resident: this leg's link)\n", show(c.link))
	switch len(c.instances) {
	case 0:
		b.WriteString("  transitivity:  none cited — the = link rewrites the running fact (Leibniz chain)\n")
	default:
		for _, inst := range c.instances {
			fmt.Fprintf(&b, "  instance:      %s   (the kit's certificate at the tuple the fold computed: lift(s), then transitivity)\n", foldInstanceText(s, inst))
		}
	}
	b.WriteString("The close is premise-scoped — every other hypothesis was cleared first — so the leaf is a " +
		"resolution over exactly these premises and the premise list is complete by construction. " +
		"The failure is a defect in the chain: a mis-tagged leg (the link is not the relation this " +
		"leg claims) or a kit certificate that does not compose these two links — one whose open " +
		"binders are not the composition's own terms in order, a certificate of a parameterized " +
		"relation left off its parameters among them. It is not a missing premise and not a key " +
		"to record.")
	fmt.Fprintf(&b, "\ncause: %v", cause)
	return b.String()
}

// foldInstanceText spells a fold instance for the diagnostic: the
// certificate's statement at its tuple, where the statement is in hand
// and its leading ∀-binders take the tuple; otherwise the fact as a By
// names it.
func foldInstanceText(s *Script, inst Fact) string {
	var stated core.Term
	switch {
	case inst.handle != nil && inst.handle.term != nil:
		stated = inst.handle.content()
	case inst.target != nil:
		if ref := citeReferenceProp(s, inst.target); ref != nil && ref.NumHyps() == 0 {
			stated = ref.Conclusion()
		}
	}
	if stated == nil {
		return inst.describe()
	}
	subst := make([]core.TermSubst, 0, len(inst.witnesses))
	for _, w := range inst.witnesses {
		abs := ext.MatchesFORALL(stated)
		if abs.IsZero() || !abs.Var().Type().Equals(w.Type()) {
			return inst.describe()
		}
		subst = append(subst, core.MakeTermSubst(abs.Var(), w.Core()))
		stated = abs.Body()
	}
	return ext.PrintTerm(stated.Substitute(subst...))
}

// foldInstance is a kit certificate at a tuple the fold computed, as
// the premise the fold's close takes: the certificate's own grounding,
// if it carries one (a rule already at its relation's parameters),
// then the tuple.
func foldInstance(combinator string, cert CiteTarget, tuple ...Term) Fact {
	witnesses := make([]TermLike, len(tuple))
	for i, t := range tuple {
		witnesses[i] = t
	}
	return targetFact(combinator, cert).At(witnesses...)
}

// requireUntagged rejects LeLeg/EqLeg legs in a single-relation chain.
func requireUntagged(combinator string, legs []CalcLeg) {
	for i, leg := range legs {
		if leg.rel != relUntagged {
			panic(fmt.Sprintf("%s: leg %d (%q) is tagged %s — %s is a SINGLE-relation chain and holds no certificate for a second relation; a chain that mixes ≤ with ≈ is CalcOrder",
				combinator, i+1, leg.label, leg.rel, combinator))
		}
	}
}

// ---------------------------------------------------------------------------
// CalcOrder — mixed-relation chains (an order interleaved with an equivalence)
// ---------------------------------------------------------------------------
//
// The estimate chains above are homogeneous, but the working shape of
// order mathematics is MIXED: one bounds, the rest rewrite.
//
//	x·y  ≤  x·y + x·d   [self-add]
//	     ≈  x·(y + d)   [distributivity, flipped]
//	     ≈  x·z         [well-definedness transports z ≈ y + d]
//	                    ⟹  x·y ≤ x·z
//
// CalcRel cannot express this — it is single-relation with a single
// Trans certificate — so the corpus spells such arguments as a pile of
// consecutive unground UseLemmaExact installs plus one CnfRefute, and
// the chain survives only in the doc comment while the refuter
// reconstructs it invisibly. CalcOrder makes the narrated chain the
// checked structure: every link is an asserted, independently closed
// leg carrying its own justification label.
//
// The combinator is theory-FREE. Both relations and all three
// composition laws arrive as parameters, exactly as CalcRel's Rel /
// Trans do; nothing here knows what ≤ or ≈ mean.
//
// The fold, per leg, from the running fact rel(from, prev) and the new
// link rel(prev, to):
//
//	≤ ∘ ≤ → ≤   LeTrans
//	≈ ∘ ≈ → ≈   EqTrans
//	≤ ∘ ≈ → ≤   EqToLe lifts the LINK,  then LeTrans
//	≈ ∘ ≤ → ≤   EqToLe lifts the CHAIN, then LeTrans
//
// so the running relation is ≤ as soon as any leg is ≤ and ≈ only
// while every leg has been ≈. Every grounding tuple is COMPUTED from
// the leg terms — (from, prev, to) for a transitivity, (prev, to) or
// (from, prev) for a lift — never spelled by the author.
//
// An all-LeLeg CalcOrder produces the same tree as the CalcRel it
// generalizes: no lift fires, and each chaining leg closes from the
// same LeTrans instance. CalcRel stays the right tool for a
// homogeneous chain; CalcOrder is what a second relation costs.

// LeLeg is a CalcOrder step that travels the ORDER: it proves
// Le(⟨previous term⟩, to).
func LeLeg(to TermLike, label string, body ...Action) CalcLeg {
	return CalcLeg{to: ext.CoreOf(to), label: label, body: body, rel: relLe}
}

// EqLeg is a CalcOrder step that travels the EQUIVALENCE: it proves
// Eq(⟨previous term⟩, to).
func EqLeg(to TermLike, label string, body ...Action) CalcLeg {
	return CalcLeg{to: ext.CoreOf(to), label: label, body: body, rel: relEq}
}

// CalcOrder is the kit for a chain that mixes an order with an
// equivalence: the two relations as Prop builders plus the three
// composition certificates, each a fact a By takes as a premise, its
// open binders the composition's own terms in order (as CalcRel's
// Trans).
//
// Certificate shapes, up to the propositional spelling the refuter
// sees through (⇒-form and ∨-form both work):
//
//	LeTrans   ∀a b c.  Le(a,b) ∧ Le(b,c) ⇒ Le(a,c)
//	EqTrans   ∀a b c.  Eq(a,b) ∧ Eq(b,c) ⇒ Eq(a,c)
//	EqToLe    ∀a b.    Eq(a,b) ⇒ Le(a,b)
//
// Only the certificates a given chain's leg tags actually reach are
// required; leaving out one the chain needs panics at construction,
// naming the composition that wanted it. As with CalcRel, legs' `to`
// terms reach the Prop builders exactly as passed, so a vocabulary
// closure may type-assert them to its own term-wrapper type.
//
// A theory whose equivalence IS the kernel's `=` leaves Eq (and
// EqTrans, EqToLe) nil and folds through CalcLeibniz: CalcLeibniz
// refuses a kit that supplies Eq, while .Calc's requireCerts names Eq
// the moment an EqLeg appears — one kit value cannot serve both verbs,
// the verb is chosen by the theory (measured on ℝ's instance).
type CalcOrder struct {
	Le, Eq  func(a, b Term) Prop
	LeTrans CiteTarget
	EqTrans CiteTarget
	EqToLe  CiteTarget
}

// Calc runs as a Deduce-item fact producer, like CalcRel.Calc:
// starting from `from`, each leg asserts its pairwise link (proved by
// the leg's body, which must CLOSE it), and from the second leg on the
// running chain fact is asserted alongside and proved by the
// composition the two relations select. All links and the chained
// facts end resident; exactly one unsolved leaf remains, so the
// enclosing Deduce continues at the same level.
//
// The chain's final fact is Le(from, last) if any leg was an LeLeg,
// else Eq(from, last) — that is the fact the block leaves for the
// closing Show to use.
//
// Terminal chains. When a fact the chain would assert is α-equal to
// the goal, the chain has ARRIVED: the fact is proved against the goal
// instead of asserted beside it, and the block closes rather than
// leaving a leaf. (Asserting it is not an option — tactic.AssertTactic
// refuses a claim α-equal to the goal — and it is not a loss: nothing
// remains to assert it for. This is CalcEq's mode, reached by a chain
// whose endpoint is what was to be proved: "…≈ x·z, hence x·y ≤ x·z ∎".)
// A terminal chain must therefore be its Deduce block's FINAL item, or
// stand alone in the enclosing Chain — Deduce's own leaf-count contract
// enforces that, and legs after the arrival panic.
func (k CalcOrder) Calc(from TermLike, legs ...CalcLeg) Action {
	if len(legs) < 2 {
		panic("CalcOrder.Calc: a chain needs at least two legs — a single link is just Have")
	}
	for i, leg := range legs {
		if leg.rel == relUntagged {
			panic(fmt.Sprintf("CalcOrder.Calc: leg %d (%q) is untagged — a mixed chain cannot guess which relation a link travels; spell it LeLeg(...) or EqLeg(...)", i+1, leg.label))
		}
	}
	for i, leg := range legs {
		if leg.to == nil {
			panic(fmt.Sprintf("CalcOrder.Calc: leg %d (%q) has no target term — FinalLeg is CalcEq-only", i+1, leg.label))
		}
	}
	k.requireCerts(legs)
	return _CalcOrderAction{kit: k, from: ext.CoreOf(from), legs: legs}
}

// CalcLeibniz folds a mixed chain whose ≈ side is the KERNEL'S OWN
// equality rather than a defined relation — `m = m * 1` next to
// `P(m,n) ≤ A·(m+n)+B`, the shape most of the corpus's order chains
// actually have.
//
// Same legs, same tagging, same fold table, same terminal-chain
// semantics as .Calc — what changes is which compositions have to be
// CITED. For a defined ≈, `a ≈ b` is an opaque atom: to use it under ≤
// the chain must lift it (EqToLe) and then chain (LeTrans). The
// kernel's `=` is not opaque — the refuter rewrites WITH it — so from
// the running fact and the link, all three ≈-involving compositions
// close by paramodulation with nothing cited:
//
//	≤ ∘ ≤ → ≤   LeTrans          (the only certificate a Leibniz chain needs)
//	= ∘ = → =   —  `=` is transitive in the kernel
//	≤ ∘ = → ≤   —  the link rewrites `to` for `prev` in the running bound
//	= ∘ ≤ → ≤   —  the running fact rewrites `from` for `prev` in the link
//
// So the kit carries Le and LeTrans and NOTHING else: supplying Eq,
// EqTrans or EqToLe is a category error and panics, because there is
// no ≈ theory here to certify. That is also why this is a second verb
// rather than a nil-certificate convention on .Calc — inferring the
// mode from three absent fields would turn "you forgot EqToLe" from a
// precise construction-time panic into a silent reinterpretation that
// fails much later, inside the refuter.
//
// Only LeTrans is required, and only if some step is pureOrder; an
// all-EqLeg Leibniz chain needs no certificates at all.
func (k CalcOrder) CalcLeibniz(from TermLike, legs ...CalcLeg) Action {
	if len(legs) < 2 {
		panic("CalcOrder.CalcLeibniz: a chain needs at least two legs — a single link is just Have")
	}
	// Kit shape first: "you called the wrong verb" outranks any
	// complaint about the legs.
	k.rejectEquivalenceCerts()
	for i, leg := range legs {
		if leg.rel == relUntagged {
			panic(fmt.Sprintf("CalcOrder.CalcLeibniz: leg %d (%q) is untagged — a mixed chain cannot guess which relation a link travels; spell it LeLeg(...) or EqLeg(...)", i+1, leg.label))
		}
	}
	for i, leg := range legs {
		if leg.to == nil {
			panic(fmt.Sprintf("CalcOrder.CalcLeibniz: leg %d (%q) has no target term — FinalLeg is CalcEq-only", i+1, leg.label))
		}
	}
	k.requireLeibnizCerts(legs)
	k.Eq = leibnizEq
	return _CalcOrderAction{kit: k, from: ext.CoreOf(from), legs: legs, leibniz: true}
}

// leibnizEq builds the link/chain proposition of a Leibniz chain's ≈
// side: the kernel's own equality, which needs no family vocabulary.
func leibnizEq(a, b Term) Prop { return prop.MakeProp(core.Eq(a, b)) }

// rejectEquivalenceCerts refuses a kit that carries ≈ theory into a
// Leibniz chain — there is none to carry.
func (k CalcOrder) rejectEquivalenceCerts() {
	// `supplied` is computed against the typed field — see requireCerts on
	// why a nil func must not be routed through an `any` parameter.
	reject := func(supplied bool, name string) {
		if supplied {
			panic(fmt.Sprintf("CalcOrder.CalcLeibniz: the kit supplies %s, but a Leibniz chain's ≈ side is the kernel's own equality — the refuter rewrites with it directly, so %s has nothing to justify. Drop it; if ≈ is a DEFINED relation, this chain wants .Calc instead.", name, name))
		}
	}
	reject(k.Eq != nil, "Eq")
	reject(k.EqTrans != nil, "EqTrans")
	reject(k.EqToLe != nil, "EqToLe")
}

// requireLeibnizCerts checks — before any kernel work — that the kit
// carries the certificates this chain of leg tags actually reaches.
// Only pureOrder steps reach one.
func (k CalcOrder) requireLeibnizCerts(legs []CalcLeg) {
	need := func(missing bool, name, why string) {
		if missing {
			panic(fmt.Sprintf("CalcOrder.CalcLeibniz: this chain needs the %s certificate (%s), but the kit leaves it nil", name, why))
		}
	}
	for _, leg := range legs {
		if leg.rel == relLe {
			need(k.Le == nil, "Le", "a leg travels the order")
		}
	}
	for _, st := range calcOrderPlan(legs) {
		if st.rel == relLe {
			need(k.Le == nil, "Le", "the chained fact is an order fact")
		}
		if st.pureOrder() {
			need(k.LeTrans == nil, "LeTrans", "the chain composes ≤ with ≤")
		}
	}
}

// calcOrderStep is one chaining move, determined by the leg tags
// alone: which lifts fire, which transitivity certificate chains the
// two facts, and what the running relation becomes.
type calcOrderStep struct {
	liftChain bool        // running fact ≈ → ≤ before chaining
	liftLink  bool        // this leg's link ≈ → ≤ before chaining
	rel       calcRelKind // transitivity used, and the resulting relation
}

// pureOrder reports whether this step composes two ORDER facts — no ≈
// anywhere, so LeTrans alone chains it. It is the one composition a
// Leibniz chain still has to CITE (see CalcLeibniz): the other three
// all touch an `=` link or an `=` running fact, and when that `=` is
// the kernel's own equality the refuter rewrites with it directly.
func (st calcOrderStep) pureOrder() bool {
	return st.rel == relLe && !st.liftChain && !st.liftLink
}

// calcOrderPlan simulates the fold over the leg tags, returning one
// step per chaining leg (legs[1:]).
func calcOrderPlan(legs []CalcLeg) []calcOrderStep {
	run := legs[0].rel
	steps := make([]calcOrderStep, 0, len(legs)-1)
	for _, leg := range legs[1:] {
		res := run
		if leg.rel == relLe {
			res = relLe
		}
		steps = append(steps, calcOrderStep{
			liftChain: run == relEq && res == relLe,
			liftLink:  leg.rel == relEq && res == relLe,
			rel:       res,
		})
		run = res
	}
	return steps
}

// requireCerts checks — before any kernel work — that the kit carries
// every certificate this particular chain of leg tags will reach.
func (k CalcOrder) requireCerts(legs []CalcLeg) {
	// `missing` is computed by the CALLER against the typed field: Le and
	// Eq are func-typed, and a nil func handed to an `any` parameter
	// arrives as a non-nil interface, so a `cert any` check would silently
	// never fire for them.
	need := func(missing bool, name, why string) {
		if missing {
			panic(fmt.Sprintf("CalcOrder.Calc: this chain needs the %s certificate (%s), but the kit leaves it nil", name, why))
		}
	}
	for _, leg := range legs {
		if leg.rel == relLe {
			need(k.Le == nil, "Le", "a leg travels the order")
		} else {
			need(k.Eq == nil, "Eq", "a leg travels the equivalence")
		}
	}
	for _, st := range calcOrderPlan(legs) {
		if st.rel == relLe {
			need(k.Le == nil, "Le", "the chained fact is an order fact")
			need(k.LeTrans == nil, "LeTrans", "the chain composes into ≤")
		} else {
			need(k.EqTrans == nil, "EqTrans", "the chain composes ≈ with ≈")
		}
		if st.liftChain || st.liftLink {
			need(k.EqToLe == nil, "EqToLe", "the chain mixes ≈ into ≤ and an ≈ fact must be lifted")
		}
	}
}

func (k CalcOrder) rel(r calcRelKind) func(a, b Term) Prop {
	if r == relLe {
		return k.Le
	}
	return k.Eq
}

func (k CalcOrder) trans(r calcRelKind) CiteTarget {
	if r == relLe {
		return k.LeTrans
	}
	return k.EqTrans
}

type _CalcOrderAction struct {
	kit     CalcOrder
	from    Term
	legs    []CalcLeg
	leibniz bool // ≈ is the kernel's `=` — see CalcLeibniz
}

// name is the combinator as it should appear in a panic.
func (c _CalcOrderAction) name() string {
	if c.leibniz {
		return "CalcOrder.CalcLeibniz"
	}
	return "CalcOrder.Calc"
}

func (c _CalcOrderAction) applyAction(s *Script, root *GoalStackNode) {
	cur := root.unsolvedLeaf(0)
	if cur == nil {
		panic(c.name() + ": focus has no unsolved leaves remaining " +
			"(section already proved — extra Step in chain?)" + closedLeafNote(root))
	}
	arrived := "" // non-empty once the chain has closed the goal itself
	assertFact := func(claim Prop, leg CalcLeg) {
		if cur.Goal.Conclusion().AlphaEquals(claim.Conclusion()) {
			// The chain has arrived AT the goal. Asserting it is both
			// impossible (tactic.AssertTactic refuses a claim α-equal to
			// the goal) and pointless — there is nothing left to assert it
			// for. The chain IS the proof here, exactly as in CalcEq: run
			// this leg's proof on the goal and require it to close.
			runLegBody(s, cur, c.name(), leg)
			arrived = leg.label
			return
		}
		s.Do(cur, AssertStep(claim))
		Assert(len(cur.children) == 2)
		runLegBody(s, cur.children[0], c.name(), leg)
		cur = cur.children[1]
	}
	steps := calcOrderPlan(c.legs)
	prev := c.from
	runRel := c.legs[0].rel // the running fact's relation before each fold
	for i, leg := range c.legs {
		if arrived != "" {
			panic(fmt.Sprintf("%s: the chain closed the goal at %q, but leg %d (%q) follows — a chain that reaches the goal must end there",
				c.name(), arrived, i+1, leg.label))
		}
		link := c.kit.rel(leg.rel)(prev, leg.to)
		assertFact(link, leg)
		if i > 0 && arrived == "" {
			st := steps[i-1]
			var instances []Fact
			label := fmt.Sprintf("calc: chain to leg %d by %s-transitivity", i+1, st.rel)
			if c.leibniz && !st.pureOrder() {
				// The composition touches the kernel's own `=`, which the
				// refuter rewrites with: the running fact and the link are
				// both resident, and one paramodulation closes the chained
				// fact. No instance — the scoped close runs over the two
				// facts alone.
				label = fmt.Sprintf("calc: chain to leg %d — the = link rewrites the running fact", i+1)
			} else {
				if st.liftChain {
					instances = append(instances, foldInstance(c.name(), c.kit.EqToLe, c.from, prev))
				}
				if st.liftLink {
					instances = append(instances, foldInstance(c.name(), c.kit.EqToLe, prev, leg.to))
				}
				instances = append(instances, foldInstance(c.name(), c.kit.trans(st.rel), c.from, prev, leg.to))
			}
			chained := c.kit.rel(st.rel)(c.from, leg.to)
			assertFact(chained, CalcLeg{
				label: label,
				fold:  true,
				body: []Action{_CalcChainClose{
					combinator: c.name(),
					label:      label,
					chained:    chained,
					running:    c.kit.rel(runRel)(c.from, prev),
					link:       link,
					instances:  instances,
				}},
			})
			runRel = st.rel
		}
		prev = leg.to
	}
}
