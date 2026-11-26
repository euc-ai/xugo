// fact.go — the fact layer of the proof surface: the first-class fact
// VALUE (`Fact`, the noun), the justification closers that consume it
// (By / ByArith), and the cite VERBS that bring a fact to bear on the
// goal state directly (Cite / CiteKeep / CiteACRegroup).
//
// The split that organizes this file is imperative vs functional. A
// cite verb is a STATEMENT — run now, against the current leaf, its
// result an anonymous resident hyp. A Fact is an EXPRESSION — a lazy,
// passable description, materialized only when a justification verb
// consumes it. Derive (derive.go) is where facts become named values
// and the Go variable graph becomes the proof DAG.
//
// Sections:
//   - Fact and the By closers
//   - Cite, the consolidated cite verb
//   - CiteACRegroup, the AC-rearrangement cite
//

package proof

import (
	"context"
	"fmt"
	"runtime"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/ac"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/prover/typematch"
)

// =======================================================================
// Fact — the first-class fact value, and the By closers
// =======================================================================
//
// fact.go — the first-class fact VALUE (`Fact`, the noun) and the
// explicit-premise justification closers By / ByArith that consume it.
//
// Naming: verb = Cite — run against the goal state now, the
// result an anonymous resident hyp. Value = Fact — a lazy, passable
// DESCRIPTION of a fact, materialized only when a justification verb
// consumes it. The split is the imperative / functional boundary of
// the proof surface: Cite is a statement, Fact is an expression.
//
// What a Fact denotes, by flavor:
//
//   - a NAMED or CERTIFIED fact — registry entry var (NamedDep),
//     ThmCert, Prop, or sibling section *GoalStackNode:
//     the resolveLemmaTarget universe, resolved at consumption;
//   - a RESIDENT HYPOTHESIS of the in-progress proof — returned by the
//     Argument verbs (Have / Obtain / Assume / SupposeNot / Hyp, derive.go),
//     carried as a lazily tracked HypHandle;
//   - either of the above AT WITNESSES: `f.At(w…)` / `At(target, w…)`
//     — grounding as function application, a pure value operation; the
//     ground instance materializes only inside the consuming By.
//   - a DERIVED fact — a claim plus the proof of it — handed over by a
//     solver kit through the SelfProvingPremise outlet below. The
//     consuming By materializes it as a Have moved inside its own leaf.
//
// By(premises…) is the lexical-scope close: it brings EXACTLY the
// listed premises to bear — installs the ones not already resident,
// grounds the witnessed ones, asserts-and-proves the self-proving ones
// (a Have moved inside the leaf), CLEARS every other ambient hypothesis,
// and runs one refutation. What is not listed does not exist for the
// refuter, so refute-poisoning (wide-∀ residue, spent bridges) is
// impossible by construction instead of by Clear() discipline, and the
// premise list doubles as the readable justification — the checked
// counterpart of a paper's "by A, B and C".
//
// The spine/leaf contract — what makes lexical premises compatible
// with a mutable goal context: By only ever prunes the LEAF IT CLOSES
// (a Have's claim branch, a Show terminal, a Case body). The deduction
// SPINE — the running residual a Derive block advances along — is
// never pruned, so spine-resident facts stay resolvable for later
// premise lists, and grounding a spine fact inside a By consumes it
// only inside that By's leaf: the spine's copy is untouched, and the
// same fact grounds again at different witnesses in a later By.
//
// By's contracts, all loud:
//
//   - a premise that neither is resident nor installs panics (the
//     Cite verb's no-op contract);
//   - a premise that closes the leaf BEFORE the list is exhausted
//     panics as over-specified, naming the premises left unused — the
//     argument is claiming more than it needs. A premise that closes
//     on the LAST element is fine: `By(p₁, …, pₙ)` where pₙ finishes
//     is the normal shape, and needs no trailing refutation;
//   - the terminal refutation failing panics with the premise list AND
//     the cleared-hyp list — the missing premise is usually in there.
//
// By runs the CNF refuter; ByArith runs the gated arithmetic closer
// instead. Both are facts-as-parameters in the solver
// trust sense: every materialized step cites what the caller passed.

// Fact is a first-class fact value: a lazy description of a named /
// certified fact, of a resident hypothesis, or of a solver kit's
// self-proving claim, optionally grounded at witnesses. Zero value is
// unusable; a CiteTarget reads as one (AsFact), At and MakeFact
// construct one, and the Argument verbs return one (derive.go). Facts are pure values —
// copying, storing and passing them has no goal-state effect.
type Fact struct {
	target    any        // resolveLemmaTarget universe; nil for hyp flavor
	handle    *HypHandle // non-nil for the resident-hyp flavor
	witnesses []Term     // pending grounding, applied at consumption
	// named pins binders of the stated form by name (Where): the fact
	// enters the consuming By as the apply rung's seeded head.
	named []NamedWitness
	claim Prop     // non-nil for the derived flavor: what it asserts
	proof []Action // the derived flavor's own proof of claim
	// derivedCert is the derived flavor's kernel certificate (the kit's
	// SelfProof) — what the By composite closes the claim branch with.
	// Set alongside claim/proof by adoptSelfProving.
	derivedCert Prop
	// residentContent — the resident-by-CONTENT flavor (ResidentHyp):
	// the hyp is located by α-match against this Prop/Term at
	// consumption, no handle involved. The machine-rendered spelling of
	// a resident premise (emit's By rendering); hand-written proofs
	// prefer the lexical Fact (a closure param, a.Hyp, a handle).
	residentContent any
	// coefficient — the SCALED flavor (Scaled): once the fact, an
	// equation l = r, is installed and grounded, the consuming By adds
	// its congruence c·l = c·r under the carrier's multiplication as a
	// hypothesis, proved from the equation. Lean's linear_combination
	// coefficient: a polynomial multiplier the arithmetic closer's
	// equality deciders cannot search for (they combine equations by
	// integers), supplied by the author.
	coefficient Term
	// members are the evidence carriers At took as witnesses whose
	// evidence nothing has carried with the fact yet: the consuming By
	// reads them against the instance's guards (member_evidence.go).
	members []memberWitness
	// listed are the facts this one travels with (GroupPremises): in a
	// By list they stand before it; a verb taking the fact in hand
	// materializes them first and discharges the instance's guards from
	// them (residentHandleListing).
	listed []any
}

// CiteTarget is what a cite verb names: a fact, under whichever Go
// type holds it. The verbs that take a target — Cite, CiteSpecialize,
// At, Where, Scaled, and a simp rule's Fwd and Rev — take a CiteTarget
// and read the Fact through AsFact, so the compiler refuses a value
// that names no fact. The implementers are the universe:
//
//   - Fact itself;
//   - a registry entry and a family's generated theorem wrapper, the
//     named fact (NamedFact);
//   - a generated wrapper's reading (`dot.AddLeft.Read(inst)`), which
//     holds its Fact as a field, and any type that embeds a Fact;
//   - *GoalStackNode, a local section's theorem;
//   - *TypedThm, a dep at an explicit type instance (ctx.AtTypes);
//   - *HypHandle, a resident hypothesis.
//
// A kernel statement or certificate — `ctx.Dep(x)`,
// `ctx.DepNormalized(x)` — is in package core and carries no method of
// this package: MakeFact names it as a fact. A registered name is not
// a target: a dep is its entry.
type CiteTarget interface {
	AsFact() Fact
}

// AsFact is the CiteTarget reading of a Fact: itself.
func (f Fact) AsFact() Fact { return f }

// AsFact is a local section as a fact: its theorem, cited once the
// section is proved.
func (n *GoalStackNode) AsFact() Fact { return Fact{target: n} }

// AsFact is a dep at an explicit type instance as a fact.
func (t *TypedThm) AsFact() Fact { return Fact{target: t} }

// AsFact is the resident hypothesis the handle names, as a fact.
func (h *HypHandle) AsFact() Fact { return residentFact(h) }

// SelfProvingPremise is the solver-kit outlet: a premise that carries
// its own proof. A value satisfying it is accepted anywhere a Fact is
// (`By(…, kit.Thing(…), …)`), and the consuming By materializes it as a
// Have moved inside its own leaf — the claim is asserted there, the
// claim branch is closed from the kernel-derived certificate, and the
// deduction continues with the fact resident.
//
// The interface is stated over kernel Props alone so that a kit BELOW
// package proof (prover/solver/ac is the motivating one — it
// manufactures certificates and cannot depend on the proof calculus,
// see its package doc) can satisfy it without an import cycle.
//
// The boundary is deliberate, and it is why there is no exported
// constructor for this flavor: it is a solver-kit outlet, not a
// hand-authoring verb. Every step a kit emits cites what the consumer
// passed it (the facts-as-parameters trust regime prover/solver runs
// on), so the premise list stays an honest account of the argument. A
// HAND-written intermediate fact that needs a proof of its own is
// `a.Have(label, claim, By(…))`, where claim and justification are both
// on the page; a premise list that hides an arbitrary proof inside
// itself is the case-split pyramid smuggled back in.
type SelfProvingPremise interface {
	// SelfProof returns the premise as a CLOSED, kernel-proved Prop:
	// hyp-free, and Proved (or promised). It is both the claim the
	// consuming By asserts and the certificate that closes it.
	SelfProof() Prop
}

// derivedFact is the DERIVED flavor's constructor — deliberately
// unexported (see SelfProvingPremise).
func derivedFact(claim Prop, proof ...Action) Fact {
	return Fact{claim: claim, proof: proof}
}

// adoptSelfProving turns a kit's certificate into the derived Fact:
// the claim is the certificate's statement (hyp-free, as a goal), and
// the proof is the certificate itself.
func adoptSelfProving(p SelfProvingPremise) Fact {
	cert := p.SelfProof()
	if cert == nil {
		panic(fmt.Sprintf("a self-proving premise: %T returned a nil self-proof", p))
	}
	if cert.NumHyps() != 0 {
		panic(fmt.Sprintf("a self-proving premise: %T's self-proof carries hypotheses — it "+
			"must be a CLOSED fact:\n%s", p, prop.PrintProp(cert)))
	}
	if !cert.Proved() && !core.IsPromised(cert) {
		panic(fmt.Sprintf("a self-proving premise: %T's self-proof is not kernel-proved — a premise that carries "+
			"its own proof must carry a certificate:\n%s", p, prop.PrintProp(cert)))
	}
	f := derivedFact(core.MakeProp(cert.Conclusion()), CiteKnown(cert))
	f.derivedCert = cert
	return f
}

// MakeFact names a kernel statement as a fact: a certificate
// (`ctx.Dep(x)`, `ctx.DepNormalized(x)`) or an explicit Prop, which a
// cite verb then uses verbatim — the explicit form keeps full control
// over what is installed. Every other cite target is a CiteTarget
// already and is passed as itself. (The constructor is `MakeFact`
// because plain `Fact` is the type, as MakeCase is named for Case.)
func MakeFact(stated Prop) Fact {
	if stated == nil {
		panic("MakeFact: nil statement")
	}
	return Fact{target: stated}
}

// NamedFact is the fact a registry dep names — what an entry and a
// generated theorem wrapper read as (CiteTarget).
func NamedFact(dep NamedDep) Fact {
	if dep == nil {
		panic("NamedFact: nil dep")
	}
	return Fact{target: dep}
}

// premiseFact is the Fact a premise list's element reads as: a
// CiteTarget through AsFact, a solver kit's SelfProvingPremise adopted
// as the derived flavor, and a kernel statement as the fact naming it.
func premiseFact(premise any) Fact {
	switch t := premise.(type) {
	case nil:
		panic("nil where a fact is expected")
	case CiteTarget:
		return t.AsFact()
	case SelfProvingPremise:
		return adoptSelfProving(t)
	}
	return Fact{target: premise}
}

// targetFact is the Fact a verb's target reads as; who names the verb
// for the refusal of a nil target.
func targetFact(who string, target CiteTarget) Fact {
	if target == nil {
		panic(who + ": nil target")
	}
	return target.AsFact()
}

// ResidentHyp names a RESIDENT hypothesis of the consuming leaf as a
// premise, located by content (α-match against a Prop's conclusion or
// a bare Term) — the machine-rendered spelling of the resident flavor:
// a session `by`'s by_hyps premise emits as ResidentHyp(<stmt>), and
// replay re-locates the hyp index-free. Hand-written proofs prefer the
// lexical Fact (a binder-closure param, a.Hyp, a bound handle) — reach
// for this only where no lexical name exists.
func ResidentHyp(content any) Fact {
	if content == nil {
		panic("ResidentHyp: nil content")
	}
	return Fact{residentContent: content}
}

// At is the ground-instance expression: the fact `target` taken at the
// given witnesses — "LessEqTrans at (a, b, c)". A pure value operation;
// nothing materializes until a justification verb consumes the result.
func At(target CiteTarget, witnesses ...TermLike) Fact {
	if len(witnesses) == 0 {
		panic("At: witnesses required (a bare fact is the target itself)")
	}
	return targetFact("At", target).At(witnesses...)
}

// At appends witnesses to the fact's pending grounding (pure copy).
func (f Fact) At(witnesses ...TermLike) Fact {
	if len(witnesses) == 0 {
		panic("Fact.At: witnesses required")
	}
	if f.claim != nil {
		panic(fmt.Sprintf("Fact.At: a self-proving premise is already the ground fact it claims — "+
			"there is no ∀-source to instantiate:\n%s", prop.PrintProp(f.claim)))
	}
	if len(f.named) > 0 {
		panic("Fact.At: this fact already pins a binder by name (Where) — a positional tuple " +
			"grounds a prefix and a named table seeds the apply rung; one fact takes one or the other")
	}
	g := f
	g.witnesses = append(append([]Term{}, f.witnesses...), ext.CoreTerms(witnesses)...)
	for _, w := range witnesses {
		if c, ok := w.(_EvidenceCarrier); ok {
			g.members = append(append([]memberWitness(nil), g.members...), memberWitness{carrier: c, point: w.Core()})
		}
	}
	return g
}

// Scaled is the fact `target` — an equation once installed and
// grounded, or read bare at a resident fact and so materialized as the
// Have it replaces — with a COEFFICIENT: the consuming By adds the congruence
// `c·l = c·r` beside the fact `l = r`, under the multiplication of the
// equation's carrier (num, real, int, or a ring by a comm_ring / field
// fact resident in the leaf or installed), proved from the fact and
// keyless. This is Lean's `linear_combination c * h`: the arithmetic
// closer combines the context's equations by INTEGER coefficients over
// the monomial basis, and a polynomial coefficient — `e` in
// `a = b·c, d = c·e ⊢ a·e = b·d`, where a·e − b·d = e·(a − b·c) − b·(d −
// c·e) — is the author's to supply:
//
//	ByArith(Scaled(a.Term("e"), h1), Scaled(a.Term("b"), h2))
//
// The target may be witnessed (`Scaled(c, At(law, w…))`) — the tuple
// grounds first, the instance is what is scaled. A fact pinned by name
// (Where) or a self-proving premise takes no coefficient.
func Scaled(coefficient TermLike, target CiteTarget) Fact {
	if coefficient == nil {
		panic("Scaled: a coefficient term is required")
	}
	f := targetFact("Scaled", target)
	if f.claim != nil {
		panic(fmt.Sprintf("Scaled: a self-proving premise is the ground fact it claims and is not scaled:\n%s",
			prop.PrintProp(f.claim)))
	}
	if len(f.named) > 0 {
		panic("Scaled: this fact pins a binder by name (Where) — the apply rung's head is not scaled; " +
			"ground it with At and scale the instance")
	}
	if f.coefficient != nil {
		panic("Scaled: this fact already carries a coefficient")
	}
	f.coefficient = coefficient.Core()
	return f
}

// NamedWitness pins one ∀-binder of a stated form by its stated name.
type NamedWitness struct {
	Binder  string
	Witness Term
}

// Where pins one ∀-binder of the fact's STATED form by name — Lean's
// `apply law (R := r)`, on a binder the goal cannot
// determine. The fact then enters the consuming By as the apply rung's
// head with that binder seeded: the remaining binders are read off the
// goal's conclusion and the context (apply_close.go), every antecedent
// must be resident, and the leaf closes by kernel apply — keyless,
// nothing recorded. A named fact MUST apply: it is an instruction, not
// a candidate the closer may ignore, and a By whose named premise does
// not fire fails naming the nearest miss. Contrast At, which GROUNDS a
// positional prefix and leaves the rest to the closer; a fact takes one
// or the other. The binder may sit anywhere in the stated ∀-prefix —
// that is the point: a positional tuple cannot skip to it.
func (f Fact) Where(binder string, witness TermLike) Fact {
	if binder == "" || witness == nil {
		panic("Fact.Where: a binder name and a witness term are both required")
	}
	if f.claim != nil {
		panic(fmt.Sprintf("Fact.Where: a self-proving premise has no binders to pin:\n%s",
			prop.PrintProp(f.claim)))
	}
	if len(f.witnesses) > 0 {
		panic("Fact.Where: this fact already grounds a positional tuple (At) — a named table seeds " +
			"the apply rung instead; one fact takes one or the other")
	}
	for _, nw := range f.named {
		if nw.Binder == binder {
			panic(fmt.Sprintf("Fact.Where: binder %q is already pinned", binder))
		}
	}
	g := f
	g.named = append(append([]NamedWitness{}, f.named...), NamedWitness{Binder: binder, Witness: witness.Core()})
	return g
}

// Where is the function form of Fact.Where: the fact `target` with its
// stated binder pinned — "Related where R is scalesBy".
func Where(target CiteTarget, binder string, witness TermLike) Fact {
	return targetFact("Where", target).Where(binder, witness)
}

// BoundContent reports what a RESIDENT fact said when its handle was
// bound — the antecedent an a.Assume moved into the hyps, the claim an
// a.Have proved — and false for every other flavor (named and certified
// targets resolve at consumption and carry no authoring-time content,
// and a ground instance f.At(w…) states its instance, which no handle
// bound until a verb materializes it).
//
// This is an AUTHORING-time reading, for surfaces that refuse to build
// a value around a fact that does not say what the caller asserts (the
// dimension-refined membership gate in proofs/cartesian/carrier is the
// tenant). It is a tripwire, not a soundness boundary: the content is
// the BIND-time form (a verb that later transforms the hyp moves the
// resident content, not this reading), and what a By ultimately
// consumes is checked by the prover as always.
func (f Fact) BoundContent() (core.Term, bool) {
	if f.handle == nil || f.handle.term == nil || len(f.witnesses) > 0 || len(f.named) > 0 {
		return nil, false
	}
	return f.handle.content(), true
}

// Rw rewrites the goal (and the other hyps) with this fact's equation
// in its written direction (l → r). The fact is one in hand — a
// resident hypothesis, its ground instance f.At(w…), or a law read under
// a resident hypothesis — and a ground instance is first materialized on
// the spine (residentHandle); the handle's tracking follows the result.
//
// This is the one place a Fact drives a goal-surface move rather than
// serving as a premise — the bridge for an argument that mixes a
// premise-list close with a rewrite (without it, converting the
// introduction to a Argument verb would strand the later rewrite).
func (f Fact) Rw() Action { return f.rw("Rw", false) }

// RwRev rewrites with this fact's equation REVERSED (r → l).
// Direction is spelled by the verb, not by an argument — the
// same Fwd / Rev orientation vocabulary a simp rule uses.
func (f Fact) RwRev() Action { return f.rw("RwRev", true) }

// rw is the shared bottom of the pair; verb names the caller's spelling
// so a panic points at the line the author wrote.
func (f Fact) rw(verb string, flip bool) Action {
	return f.inHandStep(verb, "a named lemma cited as a rewrite is Cite(dep), or a rule: Simp(Fwd(dep))", true,
		func(h *HypHandle) Action { return h.rw(flip) })
}

// Simp rewrites this fact, in its place, with the rules — Lean's `simp at
// h`: the conclusion is untouched, the rules' side conditions discharge
// against the other hypotheses, and the fact goes on naming the rewritten
// hypothesis. A fact in hand is rewritten; a ground instance is first
// materialized on the spine, and the rewrite is of the instance.
func (f Fact) Simp(rules ...SimpRule) Action {
	return f.inHandStep("Simp", "a named lemma is a rule: Simp(Fwd(dep)), or rewritten as a.Simplified(dep, rules…)", false,
		func(h *HypHandle) Action { return h.Simp(rules...) })
}

// Subst substitutes with this fact's equation (variable = term).
func (f Fact) Subst() Action {
	return f.inHandStep("Subst", "only a fact in hand substitutes", true,
		func(h *HypHandle) Action { return h.Subst() })
}

// CongrArg applies forward congruence on this fact's equation under fn.
func (f Fact) CongrArg(fn Term) Action {
	return f.inHandStep("CongrArg", "only a fact in hand drives congruence", true,
		func(h *HypHandle) Action { return h.CongrArg(fn) })
}

// inHandStep is a goal-surface verb on a fact in hand: on a bare
// resident fact the handle's own step; on any other fact in hand the
// instance is materialized first (residentHandle) and the step is taken
// on it — an equation verb's on an instance whose guards the context
// discharged, the guard it does not hold named. A named law is not in
// hand: it rewrites as a cite or a rule, and the verb refuses it,
// naming that spelling.
func (f Fact) inHandStep(verb, named string, equation bool, run func(*HypHandle) Action) Action {
	if f.handle != nil && len(f.witnesses) == 0 && len(f.named) == 0 && f.coefficient == nil {
		return run(f.handle)
	}
	if !f.inHand() {
		panic(fmt.Sprintf("Fact.%s: %s is not a fact in hand — %s", verb, f.describe(), named))
	}
	return _FactContextAction{f: f, verb: verb, run: func(h *HypHandle) Action {
		if note := unsuppliedGuardNote(h.bindNode, h.term); equation && note != "" {
			panic(fmt.Sprintf("Fact.%s: the instance of %s is no equation%s", verb, f.describe(), note))
		}
		return run(h)
	}}
}

// inHand reports a fact of the proof in progress: a resident hypothesis,
// named by a handle or by content, bare or at witnesses, or a law read
// under one.
func (f Fact) inHand() bool {
	if f.handle != nil || f.residentContent != nil {
		return true
	}
	r, ok := f.target.(readingInst)
	return ok && r.resident()
}

// residentFact wraps a bound HypHandle as a Fact — the Argument verbs'
// return path (derive.go).
func residentFact(h *HypHandle) Fact { return Fact{handle: h} }

// =======================================================================
// Fact — the context verbs: branch splitting, and Clear
// =======================================================================
//
// Rw / Subst / CongrArg above drive the goal SURFACE from a fact's
// equation. The verbs below want something else: a fact's ADDRESS — the
// hypothesis slot it occupies — because splitting a ∨/⇔/⇒-shaped
// hypothesis and dropping one are operations on the CONTEXT, not on the
// goal.
//
// Needing an address is exactly why these are not the pure forwards onto
// *HypHandle they look like. A handle is by construction bound to a
// resident hypothesis; a Fact may still be a DESCRIPTION of a fact that
// was never installed, and naming a description does not give it a slot.
// residentHandle is where that difference is resolved, per flavor, and
// it is the one thing to read before adding another verb here.

// residentHandle materializes f as a hypothesis of the current leaf and
// returns the handle naming it — the one step behind every verb that
// acts on a fact as a hypothesis (the splits here, Rw and Simp above,
// Unpack, Conjuncts, Unfolded and Simplified in derive.go, MemberOf in
// member.go).
//
//   - RESIDENT (an Argument verb's return value, or a *HypHandle read
//     as its fact): already bound — returned unchanged. The caller then
//     records exactly what the handle spelling records, ministep for
//     ministep.
//   - RESIDENT AT WITNESSES (`f.At(w…)`, or ResidentHyp(…).At(w…)):
//     grounded on the spine as `a.Do(f.At(w…))` grounds it
//     (groundResident) — the ∀-source stays, the instance's guards are
//     discharged from the facts listed with it — and the instance is
//     bound. A guard nothing supplies stays on the instance, where the
//     verb's own shape check meets it: nothing is assumed.
//   - RESIDENT BY CONTENT (ResidentHyp): located by α-match at the
//     current leaf, as a By premise locates it, and bound — the
//     machine-rendered spelling emit gives a verb's fact where no
//     handle names it; at witnesses it is grounded as above.
//   - NAMED or CERTIFIED: not resident, so it is installed here, through
//     the Cite verb's own path — the preserving lemma chain plus its
//     reproduction close for a bare fact, the cite-at-use ground
//     instance for `At(dep, w…)` (its guards discharged as above) — and
//     the arrival is bound. So `At(dep, w…).SplitDisj(…)` records
//     install-then-split: the same two moves, in the same order, as
//     `h.From(Cite(dep, w…))` followed by `h.SplitDisj(…)`.
//   - DERIVED (a solver kit's self-proving premise): rejected. It carries
//     a proof, not a position; it belongs in a By premise list. So is a
//     Scaled fact (its coefficient is a By's) and a resident fact pinned
//     by name (Where reads a NAMED fact's stated form).
//
// An instance's guards are discharged from the facts listed with it —
// the facts of the group it travels in, which residentHandleListing is
// handed, and its own source — and a guard the context supplies through
// any other fact is refused (listed_suppliers.go).
func (f Fact) residentHandle(verb string, s *Script, root *GoalStackNode) *HypHandle {
	return f.residentHandleListing(verb, s, root, nil)
}

// residentHandleListing is residentHandle with facts listed for the
// instance's guards beyond the ones f travels with. A resident fact
// taken as it stands has no instance whose guards a listed fact could
// discharge, so any fact listed with it is refused (refuseSurplus).
func (f Fact) residentHandleListing(verb string, s *Script, root *GoalStackNode, listed []_ListedTerm) *HypHandle {
	f, listed = f.materializeListed(verb, s, root, listed)
	switch {
	case f.claim != nil:
		panic(fmt.Sprintf("Fact.%s: a self-proving premise is not a hypothesis of this proof — "+
			"it carries a proof, not a position, and belongs in a By premise list:\n%s",
			verb, prop.PrintProp(f.claim)))
	case f.coefficient != nil:
		panic(fmt.Sprintf("Fact.%s: %s carries a coefficient — Scaled is a By premise, whose close adds "+
			"the scaled congruence; act on the fact itself", verb, f.describe()))
	case len(f.named) > 0 && (f.handle != nil || f.residentContent != nil):
		panic(fmt.Sprintf("Fact.%s: %s pins a binder by name (Where), which reads the stated form of a "+
			"NAMED fact — a resident hypothesis is grounded positionally (At)", verb, f.describe()))
	case f.handle != nil && len(f.witnesses) == 0:
		listedSuppliers("Fact."+verb, f.describe(), listed).refuseSurplus()
		return f.handle
	case f.handle != nil || f.residentContent != nil:
		leaf := root.unsolvedLeaf(0)
		if leaf == nil {
			panic(fmt.Sprintf("Fact.%s: no unsolved leaves remaining (section already proved?) — %s",
				verb, f.describe()) + closedLeafNote(root))
		}
		idx := f.residentIndex("Fact."+verb, leaf)
		node, held := leaf, leaf.Goal.Hyp(idx)
		if len(f.witnesses) > 0 {
			node, held = groundResident("Fact."+verb, s, leaf, idx, f.witnesses, f.describe(), listed)
		}
		h := NewHypHandle(f.describe())
		h.bindTo(node, held)
		return h
	}
	return installFactResident("Fact."+verb, s, root, f, listed).handle
}

// materializeListed brings the facts f travels with into the context,
// each as a fact in hand — a member as every fact of its evidence — and
// returns f without them and listed extended by what they state at the
// leaf, a member's evidence marked carried. A premise of a member's
// evidence is installed with the evidence materialized before it listed
// (a closure member's reading at a point finds the point's membership
// there), and with nothing else: a fact the author listed is the
// instance's, not the evidence's.
func (f Fact) materializeListed(verb string, s *Script, root *GoalStackNode, listed []_ListedTerm) (Fact, []_ListedTerm) {
	var evidence []_ListedTerm
	for _, m := range f.listed {
		facts, carried := []any{m}, false
		if c, ok := m.(_Carried); ok {
			facts, carried = []any{c.premise}, true
		}
		if c, ok := facts[0].(_EvidenceCarrier); ok {
			facts, carried = c.evidencePremises(), true
		}
		for _, e := range facts {
			var with []_ListedTerm
			if carried {
				with = slices.Clip(evidence)
			}
			h := inHandHandleListing(verb, s, root, e, with)
			t := _ListedTerm{term: h.contentAt(root.unsolvedLeaf(0)), name: h.name, carried: carried}
			listed = append(listed, t)
			if carried {
				evidence = append(evidence, t)
			}
		}
	}
	f.listed = nil
	return f, listed
}

// residentIndex locates a resident fact's hypothesis in leaf: by its
// handle, or by content for ResidentHyp.
func (f Fact) residentIndex(who string, leaf *GoalStackNode) int {
	if f.handle != nil {
		return f.handle.resolveOrPanic(who, leaf)
	}
	idx, err := findHypIndex(leaf.Goal, contentHypTerm(who, f.residentContent))
	if err != nil {
		panic(fmt.Sprintf("%s: %s: %v\n(goal: %s)", who, f.describe(), err, prop.PrintProp(leaf.Goal)))
	}
	return idx
}

// groundResident grounds the resident hypothesis at idx of leaf at the
// witnesses, on the spine — the one grounding a fact in hand takes
// (residentHandle) and `a.Do(f.At(w…))` records. The tuple is read
// against the fact's guarded binders, by type where its positional order
// is ill-typed and the types settle it (witness_order.go); the ∀-source
// is KEPT, so a spine fact grounds again at other witnesses; and the
// instance's guards are discharged from the facts listed with it — the
// group it is handed in (listed) and the source itself — where they
// supply them (Lean's `h w ‹A›`), so a fact resident as `∀n. N₀ ≤ n ⇒ …`
// grounds at n₀ to its consequent when the assumption N₀ ≤ n₀ is listed
// beside it; a guard the context supplies through an unlisted fact is
// refused (listed_suppliers.go). An instance already resident is taken
// as it stands, with nothing recorded for the grounding. Returns the
// leaf the deduction continues on and the instance as a hypothesis of
// it.
func groundResident(who string, s *Script, leaf *GoalStackNode, idx int, witnesses []Term, desc string, listed []_ListedTerm) (*GoalStackNode, core.Term) {
	source := leaf.Goal.Hyp(idx)
	wits := witnesses
	if binders, _ := guardedPrefixBinders(source); len(wits) <= len(binders) {
		wits = permuteByTypeIfIllTyped(binders[:len(wits)], wits)
	}
	instance := residentInstance(leaf, source, wits)
	if instance == nil {
		ws := make([]string, len(wits))
		for i, w := range wits {
			ws[i] = ext.PrintTerm(w)
		}
		panic(fmt.Sprintf("%s: %s does not ground at its witness tuple\n  hyp: %s\n  witness tuple: (%s)%s",
			who, desc, ext.PrintTerm(source), strings.Join(ws, ", "), witnessOrderNote(nil, source, wits)))
	}
	node := leaf
	if !goalHasHypAlpha(leaf.Goal, instance) {
		s.Do(leaf, SpecializeKeep(InstHyp(idx, wits...)))
		node = leaf.unsolvedLeaf(0)
	}
	at, err := findHypIndex(node.Goal, instance)
	if err != nil {
		panic(fmt.Sprintf("%s: the ground instance of %s is not a hypothesis after grounding (engine invariant): %v\n  instance: %s",
			who, desc, err, ext.PrintTerm(instance)))
	}
	suppliers := listedSuppliers(who, desc, listed, source)
	node, instance = dischargeGuards(node, node.Goal.Hyp(at), false, rungOpts{}, suppliers)
	suppliers.refuseSurplus()
	return node, instance
}

// residentInstance is the hypothesis SpecializeKeep at wits adds beside
// source — the same tactic, in the leaf's reading, run on the sequent
// that holds source alone — or nil when the tuple does not ground it.
func residentInstance(leaf *GoalStackNode, source core.Term, wits []Term) core.Term {
	alone := core.MakeProp(leaf.Goal.Conclusion(), source)
	sub := tactic.SpecializeTacticReading([]SpecializeHyp{InstHyp(0, wits...)}, true,
		libraryRead(leaf.ProofScope()))(alone)
	if sub == nil || sub.Size() != 1 {
		return nil
	}
	child := sub.ChildGoal(0)
	for i := 0; i < child.NumHyps(); i++ {
		if h := child.Hyp(i); !h.AlphaEquals(source) {
			return h
		}
	}
	return nil
}

// inHandHandle is residentHandle for every value a fact verb takes. A
// member — its evidence, the membership last — has each fact before the
// last materialized first, by this same function, each with the
// evidence before it listed (a closure member read at a closure member
// holds the inner reading, whose guard is the inner point's
// membership), and the last takes them all as the facts its guards are
// discharged from (residentHandleListing). Any other value is the Fact
// it reads as (premiseFact), which lists what it travels with
// (GroupPremises).
func inHandHandle(verb string, s *Script, root *GoalStackNode, x any) *HypHandle {
	return inHandHandleListing(verb, s, root, x, nil)
}

// inHandHandleListing is inHandHandle with facts already listed for the
// instance. Those reach the member's membership, its last premise, and
// never the premises of its evidence before it, which list the evidence
// alone.
func inHandHandleListing(verb string, s *Script, root *GoalStackNode, x any, listed []_ListedTerm) *HypHandle {
	c, ok := x.(_EvidenceCarrier)
	if !ok {
		return premiseFact(x).residentHandleListing(verb, s, root, listed)
	}
	members := c.evidencePremises()
	var evidence []_ListedTerm
	for _, m := range members[:len(members)-1] {
		h := inHandHandleListing(verb, s, root, m, slices.Clip(evidence))
		evidence = append(evidence, _ListedTerm{term: h.contentAt(root.unsolvedLeaf(0)), name: h.name, carried: true})
	}
	return inHandHandleListing(verb, s, root, members[len(members)-1], slices.Concat(listed, evidence))
}

// installFactResident brings a NAMED fact into the context at the
// current leaf and returns it bound as a resident Fact — the shared
// install behind Argument.Unpack's named form (derive.go) and the Fact
// context verbs above.
//
// A witnessed fact takes the Cite verb's cite-at-use ground instance,
// its witness tuple read in the TARGET'S stated binder order
// (witness_order.go), so `At(dep, w…)` denotes the same ground fact
// wherever it appears — as a By premise, as an Unpack source, as a fact
// about to be split. A bare fact is the PLAIN ADD of its stated form —
// one hypothesis, as the By executor installs a witnessed premise — and
// its guards are then discharged from the facts listed with it, as the
// witnessed path discharges them (dischargeGuards): the facts handed in
// its group (listed) and the fact its law is read at, so a law read at
// a resident structure fact, `S(c) ⊢ G ⇒ A ∧ B`, stands as `A ∧ B` with
// G stated by a listed fact, as written or as a conjunct of one. A
// guard the context supplies through an unlisted fact is refused
// (listed_suppliers.go). A law read under a resident hypothesis is
// derived at the leaf, the hypothesis as the leaf spells it
// (resolveTargetAt).
func installFactResident(who string, s *Script, root *GoalStackNode, f Fact, listed []_ListedTerm) Fact {
	name := f.describe()
	anchor := root.unsolvedLeaf(0)
	if anchor == nil {
		panic(fmt.Sprintf("%s: no unsolved leaves remaining (section already proved?) — %s", who, name) + closedLeafNote(root))
	}
	L, reading := resolveTargetAt(who, s, anchor, f.target)
	suppliers := listedSuppliers(who, name, listed, readingSuppliers(f.target, anchor)...)
	before := anchor.Goal
	// A witnessed fact is followed from its install to its instance by a
	// handle (the grounding records the source's successor), so an
	// instance that was already resident, and merged with it, is found
	// as surely as a new one.
	var source *HypHandle
	if len(f.witnesses) > 0 {
		ref, witnesses := L, f.witnesses
		if reading {
			L, witnesses = witnessedReadingForm(who, name, L, f.witnesses)
			ref = L
		} else {
			ref = citeReferenceProp(s, f.target)
		}
		if node, installed := anchor.citeSpecializeRef(L, ref, false, isExplicitInstance(f.target), suppliers, witnesses...); node != nil {
			source = NewHypHandle(name)
			source.bindTo(node, installed)
		}
	} else {
		if IsStronger(L, anchor.Goal) {
			panic(fmt.Sprintf("%s: %s closes the goal outright — there is nothing left to bring it to bear on "+
				"(cite it instead: Show(…, Cite(dep)) / By(dep))", who, name))
		}
		if !addStatedHypothesis(anchor, L) {
			panic(fmt.Sprintf("%s: %s does not install (already resident?)\n  on leaf goal: %s",
				who, name, prop.PrintProp(anchor.Goal)))
		}
		closeReproductionObligation(s, anchor, L)
	}
	leaves := anchor.UnsolvedLeaves()
	if len(leaves) == 0 {
		panic(fmt.Sprintf("%s: %s closed the goal outright — there is nothing left to bring it to bear on "+
			"(cite it instead: Show(…, Cite(dep)) / By(dep))", who, name))
	}
	if len(leaves) != 1 {
		panic(fmt.Sprintf("%s: installing %s left %d unsolved leaves — exactly 1 is required to "+
			"locate the installed hypothesis unambiguously", who, name, len(leaves)))
	}
	leaf := leaves[0]
	var idx int
	var err error
	if source != nil {
		idx, err = source.resolve(leaf)
	} else {
		idx, err = locateInstalled(before, leaf.Goal, L)
	}
	if err != nil {
		panic(fmt.Sprintf("%s: cannot locate the installed fact %s: %v\n(goal: %s)",
			who, name, err, prop.PrintProp(leaf.Goal)))
	}
	h := NewHypHandle(name)
	node, installed := leaf, leaf.Goal.Hyp(idx)
	if source == nil {
		node, installed = dischargeGuards(leaf, installed, false, rungOpts{}, suppliers)
	}
	suppliers.refuseSurplus()
	h.bindTo(node, installed)
	return residentFact(h)
}

// readingSuppliers is the facts a reading target is read at, as leaf
// states them: the resident structure fact of each reading in the
// chain. Empty for any other target.
func readingSuppliers(target any, leaf *GoalStackNode) []core.Term {
	r, ok := readingTarget(target)
	if !ok {
		return nil
	}
	var out []core.Term
	for cur := &r; cur != nil; cur = cur.prior {
		if cur.resident() {
			out = append(out, cur.hypothesis(leaf))
		}
	}
	return out
}

// addStatedHypothesis installs L's stated form as ONE hypothesis of the
// leaf: the plain add (tactic.LemmaAddHypTactic), at the goal's types
// where L is polymorphic and an adaptation to them is found
// (typematch.TryAdaptLemmaTypes — the preserving chain's choice on a
// tie), committed as the preserving step with the claim child the
// install leaves, as the By executor commits a witnessed premise's
// install. False where nothing installs: the stated form is resident.
func addStatedHypothesis(leaf *GoalStackNode, L Prop) bool {
	candidates := []Prop{L}
	if ext.PropHasTypeVars(L) {
		if adapted := typematch.TryAdaptLemmaTypes(L, leaf.Goal); adapted != nil {
			candidates = []Prop{adapted, L}
		}
	}
	for _, lemma := range candidates {
		sg := tactic.LemmaAddHypTactic(lemma)(leaf.Goal)
		if sg == nil {
			continue
		}
		key := core.PropKey("")
		if !lemma.AlphaEquals(L) {
			key = lemmaSourceKey(L)
		}
		return leaf.commitStep(_LemmaPreserveTactic{lemma: lemma, polymorphicSourceKey: key}, sg)
	}
	return false
}

// SplitDisj splits this fact's disjunction into its two branches, each
// claimed by the disjunct it assumes (disjunction_branches.go).
func (f Fact) SplitDisj(left DisjLeftHolds, right DisjRightHolds) Action {
	return _FactContextAction{f: f, verb: "SplitDisj",
		run: func(h *HypHandle) Action { return h.SplitDisj(left, right) }}
}

// SplitIff splits this fact's ⇔-shaped statement into the branch where
// both sides hold and the branch where neither does. A RESIDENT ⇔ is
// not a pair of directions — that is the goal-side split (SplitIff on
// the conclusion) — so the halves are named for truth, not for arrows.
func (f Fact) SplitIff(both IffBothHold, neither IffNeitherHolds) Action {
	return _FactContextAction{f: f, verb: "SplitIff",
		run: func(h *HypHandle) Action { return h.SplitIff(both, neither) }}
}

// SplitImply splits this fact's ⇒-shaped statement — one Case for the
// antecedent's failure, one for the consequent.
func (f Fact) SplitImply(cases ...Case) Action {
	return _FactContextAction{f: f, verb: "SplitImply",
		run: func(h *HypHandle) Action { return h.SplitImply(cases...) }}
}

// DismissLeft is the linearizing spelling of a BINARY disjunctive split:
// discharge the LEFT disjunct's branch inline with the labeled proof and
// continue the enclosing chain on the surviving branch, with the right
// disjunct resident. Same ministeps, same subgoals, same tree as the
// Case-nested SplitDisj spelling; the side proof must close its branch.
//
// The Fact keeps tracking across the split, so the same value names the
// surviving disjunct afterwards — `f.DismissLeft(…)` then `By(…, f, …)`
// is the shape, with no re-binding in between.
func (f Fact) DismissLeft(label string, body ...Action) Action {
	return _FactContextAction{f: f, verb: "DismissLeft",
		run: func(h *HypHandle) Action { return h.DismissLeft(label, body...) }}
}

// DismissRight discharges the RIGHT disjunct's branch; the proof
// continues with the left disjunct resident. See DismissLeft.
func (f Fact) DismissRight(label string, body ...Action) Action {
	return _FactContextAction{f: f, verb: "DismissRight",
		run: func(h *HypHandle) Action { return h.DismissRight(label, body...) }}
}

type _FactContextAction struct {
	f    Fact
	verb string
	run  func(*HypHandle) Action
}

func (a _FactContextAction) applyAction(s *Script, root *GoalStackNode) {
	a.run(a.f.residentHandle(a.verb, s, root)).applyAction(s, root)
}

// Clear drops the hypotheses the given facts name — one ClearHyps step
// with every index resolved against the same goal snapshot (the
// batch-step contract). Lean's `clear h₁ h₂`. Arguments are Fact values
// or anything that reads as one (CiteTarget), so a proof still holding
// *HypHandles passes them unchanged.
//
// Every argument must be RESIDENT. Clear drops a hypothesis of the proof
// in progress; a named fact that was never installed has none to drop,
// and installing one in order to drop it is not an argument anyone means
// to make. Both that and a fact carrying pending witnesses are loud.
//
// On the discipline — Clear is NOT the general context manager it could
// be read as. `By` clears every ambient hypothesis its premise list does
// not name, and that clear-first rule, not this verb, is what makes a
// close's premises an honest account of the argument. Clear exists for
// the ladders that do NOT end in a By: a terminal CnfRefute, a
// multi-closer Finally — each of which meets the whole
// context. There, dropping a spent ∀-source is load-bearing mathematics
// ("this source has done its work, and left resident it poisons the
// refutation"), and saying so lexically beats both alternatives, leaving
// the poison or restating the argument to fit a By. Reaching for Clear
// AHEAD of a By is the misuse: name the premises and let the close clear.
func Clear(facts ...any) Action { return _ClearAction{facts: facts} }

type _ClearAction struct{ facts []any }

func (a _ClearAction) applyAction(s *Script, root *GoalStackNode) {
	if len(a.facts) == 0 {
		panic("Clear: no facts given")
	}
	handles := make([]*HypHandle, len(a.facts))
	for i, p := range a.facts {
		f := premiseFact(p)
		switch {
		case f.claim != nil:
			panic("Clear: a self-proving premise is not a hypothesis of this proof — nothing to drop")
		case f.handle == nil:
			panic(fmt.Sprintf("Clear: %s is not resident — Clear drops a hypothesis of the proof in "+
				"progress, and a named fact was never installed. If it IS installed, name the "+
				"resident fact (an Argument verb's return value, or a.Hyp(…)).", f.describe()))
		case len(f.witnesses) > 0:
			panic(fmt.Sprintf("Clear: %s carries pending witnesses — a ground instance that was never "+
				"materialized has nothing to drop. Clear the fact itself (the instance, once "+
				"materialized, is a separate hypothesis).", f.describe()))
		}
		handles[i] = f.handle
	}
	leaf := handles[0].mustLeaf("Clear", root)
	idxs := make([]int, len(handles))
	for i, h := range handles {
		idxs[i] = h.resolveOrPanic("Clear", leaf)
	}
	s.Do(leaf, ClearHyps(idxs...))
}

// describe renders the fact for panic messages.
func (f Fact) describe() string {
	var base string
	switch {
	case f.claim != nil:
		base = "self-proving premise " + prop.PrintProp(f.claim)
	case f.residentContent != nil:
		base = "resident hyp " + ext.PrintTerm(contentHypTerm("By", f.residentContent))
	case f.handle != nil:
		base = fmt.Sprintf("hyp %q", f.handle.Name())
	default:
		switch t := f.target.(type) {
		case NamedDep:
			base = fmt.Sprintf("dep %q", t.DepName())
		case *GoalStackNode:
			base = "sibling section"
		case *TypedThm:
			stmt := ext.PrintTerm(t.Reference().Conclusion())
			if len(stmt) > 60 {
				stmt = stmt[:57] + "…"
			}
			base = "typed instance " + stmt
		case typedInst:
			ts := make([]string, len(t.bind))
			for i, b := range t.bind {
				ts[i] = fmt.Sprintf("%s:=%s", b.name, ext.FormatType(b.to))
			}
			base = fmt.Sprintf("dep %q at (%s)", t.dep.DepName(), strings.Join(ts, ", "))
		case _TypedSoleInst:
			base = fmt.Sprintf("dep %q at %s", t.dep.DepName(), ext.FormatType(t.to))
		case readingInst:
			base = t.describe()
		case Prop:
			// A certificate or an explicit statement — `ctx.Dep(name)`,
			// a typed instance's reference, the form ByInduction hands
			// its principle on in.
			base = "fact " + clipRunes(ext.PrintTerm(t.AsProp().Conclusion()), 60)
		default:
			base = fmt.Sprintf("%T", f.target)
		}
	}
	if len(f.witnesses) > 0 {
		ws := make([]string, len(f.witnesses))
		for i, w := range f.witnesses {
			ws[i] = ext.PrintTerm(w.Core())
		}
		base += " at (" + strings.Join(ws, ", ") + ")"
	}
	if len(f.named) > 0 {
		base += " where " + describeNamedWitnesses(f.named)
	}
	return base
}

// describeNamedWitnesses renders a named table as `R := r, op := ⊕`.
func describeNamedWitnesses(named []NamedWitness) string {
	parts := make([]string, len(named))
	for i, nw := range named {
		parts[i] = nw.Binder + " := " + clipRunes(ext.PrintTerm(nw.Witness), 60)
	}
	return strings.Join(parts, ", ")
}

// PremiseGroup is a fact travelling with the facts its guard
// antecedents consume: the value GroupPremises and a typed reading's At
// return, a Fact whose listed facts stand before it. In a By list the
// group is its members listed in place, in order — same
// materialization, same recorded step, same over-specification
// accounting per member; the group buys the SPELLING, a guarded
// citation reading as one item (`Extensionality.AtVec(x, w, xIn, wIn)`)
// instead of the cite and its evidence drifting apart in the list.
// Handed to a verb that takes a fact in hand (Conjuncts, Simplified,
// Unpack, a.Do, Rw), the listed facts are what the instance's guards are
// discharged from (residentHandleListing): there the group is the
// premise list the verb has.
//
// The typed evidence-carrying cite surfaces (a theorem wrapper's AtVec)
// are the intended constructors; hand-grouping is legal wherever a
// premise genuinely travels with its evidence.
type PremiseGroup = Fact

// _Carried is a premise a group lists as a member's evidence rather than
// as a fact the author named: it travels with the member whether a guard
// reads it or not, so the surplus check (refuseSurplus) never reports
// it. A By list reads it as the premise it carries.
type _Carried struct{ premise any }

// carried marks each premise of ps as a member's evidence.
func carried(ps []any) []any {
	out := make([]any, len(ps))
	for i, p := range ps {
		if _, ok := p.(_Carried); ok {
			out[i] = p
		} else {
			out[i] = _Carried{p}
		}
	}
	return out
}

// GroupPremises is the last member with the members before it listed.
// Members are premises only — shaping options are list-level structure
// and panic here. A member that is itself a group, the value a typed
// reading's At returns, is spliced in place, so a fact can travel with a
// cite that carries evidence of its own; a member carrying evidence (a
// Member, an Inhabited vector) stands for it, its evidence carried.
func GroupPremises(members ...any) PremiseGroup {
	if len(members) == 0 {
		panic("GroupPremises: empty group")
	}
	var listed []any
	for _, m := range members[:len(members)-1] {
		listed = append(listed, groupMember(m)...)
	}
	last := members[len(members)-1]
	switch v := last.(type) {
	case ByShape, byBroadcast:
		panic("GroupPremises: a group holds premises only — shaping options stay in the By list itself")
	case _EvidenceCarrier:
		evidence := v.evidencePremises()
		for _, e := range evidence[:len(evidence)-1] {
			listed = append(listed, carried(groupMember(e))...)
		}
		last = evidence[len(evidence)-1]
	}
	f := premiseFact(last)
	f.listed = append(listed, f.listed...)
	return f
}

// groupMember is what one member before the last contributes to the
// list: a fact with its own listed facts first, a member (a Member, an
// inhabited vector) as its evidence, carried, any other value as it is.
func groupMember(m any) []any {
	switch v := m.(type) {
	case ByShape, byBroadcast:
		panic("GroupPremises: a group holds premises only — shaping options stay in the By list itself")
	case Fact:
		f := v
		out := append([]any(nil), f.listed...)
		f.listed = nil
		return append(out, f)
	case _EvidenceCarrier:
		if fv, ok := v.(CiteTarget); ok {
			return carried(groupMember(fv.AsFact()))
		}
		return []any{_Carried{m}}
	case CiteTarget:
		f := v.AsFact()
		out := append([]any(nil), f.listed...)
		f.listed = nil
		return append(out, f)
	}
	return []any{m}
}

// expandPremiseGroup flattens a group into its members — the listed
// facts, each expanded, then the fact itself — and a value that carries
// evidence (a Member) into the premises establishing it; every other
// premise passes through as itself.
func expandPremiseGroup(p any) []any {
	if c, ok := p.(_Carried); ok {
		return expandPremiseGroup(c.premise)
	}
	if c, ok := p.(_EvidenceCarrier); ok {
		return c.evidencePremises()
	}
	var f Fact
	switch v := p.(type) {
	case CiteTarget:
		f = v.AsFact()
	default:
		return []any{p}
	}
	if len(f.listed) == 0 {
		return []any{p}
	}
	var out []any
	for _, m := range f.listed {
		out = append(out, expandPremiseGroup(m)...)
	}
	f.listed = nil
	return append(out, f)
}

// By closes the current leaf from EXACTLY the given premises: each
// premise is materialized as a resident hypothesis (installed, located,
// or grounded per its flavor), every OTHER ambient hypothesis is
// cleared, and one CNF refutation finishes the leaf. A premise is a
// CiteTarget (a Fact, an entry var, a section, a handle), a kernel
// certificate or statement, a solver kit's self-proving premise, or a
// PremiseGroup standing for several. A
// premise reading a law under a resident hypothesis (Read) brings the
// premise locating that hypothesis with it (reading.go). See the file
// header for the semantics and the spine/leaf contract.
func By(premises ...any) Action { return _ByAction{premises: premises, site: authorCallSite()} }

// ByArith is By with the gated arithmetic closer as the terminal step
// instead of the CNF refuter: Arith decides the leaf, the trivial
// simplification discharges what it leaves behind. A fact of
// arithmetic alone closes as a bare ByArith() — every ambient
// hypothesis is cleared and the decision procedure reads the goal
// alone; a close that needs a hypothesis names it.
func ByArith(premises ...any) Action {
	return _ByAction{premises: premises, arith: true, site: authorCallSite()}
}

// BySets is By with the membership-mode set driver (SetTacMembership)
// as the terminal step instead of the CNF refuter: definitional
// unfolding of the standard set vocabulary down to a first-order
// membership residual, then the kernel-checked refute — with By's
// premise discipline in front (clear-first, install exactly the listed
// premises). A goal the set vocabulary settles alone closes as a bare
// BySets(); a close that needs outside facts lists them, and an
// ambient hypothesis the list omits is cleared before the driver runs.
//
// The driver always uses StandardSetVocabulary — the vocabulary is the
// driver's own fixed notion, not a per-call choice (a name the goal
// does not mention is inert). The full-expansion mode (SetTac's LEGACY
// λ-level computation) is deliberately NOT on this surface: the six
// goals that need it are measured exceptions that keep their explicit
// .Do(...) spelling.
func BySets(premises ...any) Action {
	return _ByAction{premises: premises, settac: true, site: authorCallSite()}
}

// ByChase is By with the diagram-chase closer (prover/solver/chase) as
// the terminal step instead of the CNF refuter: the named premises are
// read as an abelian diagram — the modules (module_on facts), the
// homomorphisms between them, the commuting squares and other equation
// laws, exactness, onto and one-to-one maps, the submodules a coset
// equation is reduced through — and the leaf is decided by the
// integer-linear algebra of the diagram, pulling preimages back for
// Depth(k) rounds. The list carries Depth(k), the number of pull-back
// rounds, as its one parameter; a premise the closer cannot read is
// named in the failure and never guessed at. Deterministic and bounded:
// the composite records the call and no key.
//
//	ByChase(Depth(3), complexes, chainMap, exactness, a.Hyp("u ∈ P(n + 1)"), …)
func ByChase(premises ...any) Action {
	return _ByAction{premises: premises, chase: true, site: authorCallSite()}
}

// ByShape is a shaping option that may appear anywhere in a By premise
// list. It is not a premise — it selects a normalization the accumulated
// premises pass through before the terminal close, for the arguments
// whose facts do not meet the refuter in clause form. Two exist:
//
//	By(Normalized, a, b)   — Basic() between the installs and the refute
//	By(Denoted(8), a, b)   — Denote(n) + Basic() likewise
//
// These are engine shaping, not mathematics: they carry no premise and
// state nothing about the argument, so they are values in the list
// rather than verbs of their own (the alternative — one By-variant per
// shaping — is the tactic zoo this layer exists to avoid).
//
// Two triggers, and the second is not a failure diagnosis at all:
//
//  1. The close fails WITHOUT cleared hyps to blame — the signature of
//     a shape problem rather than a missing premise.
//  2. The close would REACH THE REFUTER on a leaf that Basic() settles.
//     Nothing is wrong with the premise list; the cost is that the
//     refuter mints a CNF key, and a corpus practising zero recorded
//     keys does not want one. Cleared hyps say nothing either way here
//     — the sites that found this had cleared several. By's own MISS
//     message now decides this case for the author (see
//     byClosesUnderBasic, step_by.go).
//
// Shaping options MERGE: `By(Denoted(8), HilbertDenoted, …)` runs
// Denote(8) + HilbertDenote() + Basic() — the ε-heavy arguments whose
// large gap terms must become stable atoms before the ε is realized
// need both, in that order. Conflicting denote sizes stay a loud
// authoring error.
type ByShape struct {
	pre bool // run Basic() BEFORE the denote/realize stage
	raw bool // suppress the conditioning stage for this call
	// chaseDepth is ByChase's parameter, the number of pull-back rounds
	// (Depth); depthSet tells Depth(0) from no Depth at all. The By macro
	// takes it out of the list before the shapes merge: it is no shaping.
	chaseDepth int
	depthSet   bool
	denote     int  // >0 ⇒ run Denote(denote) first  (SEARCH form)
	hilbert    bool // run HilbertDenote() first      (SEARCH form)
	// denoteTerm / denoteName are the EXPLICIT shaping (DenotedAs /
	// HilbertDenotedAs): name THIS term, not whatever the heuristic
	// finds. denoteHilbert routes to the ε transform.
	denoteTerm    Term
	denoteName    string
	denoteHilbert bool
}

// Depth is ByChase's parameter: the number of pull-back rounds the
// chase runs after reading the premises (0 reads and decides without
// pulling anything back). It appears anywhere in a ByChase list, as a
// shaping value does, and is refused by every other By.
func Depth(rounds int) ByShape {
	if rounds < 0 {
		panic("Depth: a negative number of rounds")
	}
	return ByShape{chaseDepth: rounds, depthSet: true}
}

// Raw suppresses By's conditioning stage for this one call — the
// escape hatch the author's hand is promised: premises install and the
// goal reaches the closer exactly as spelled (no ∧-premise splitting,
// no goal ∀/⇒ strip). For the argument whose bare spelling IS the
// intent.
var Raw = ByShape{raw: true}

// PreNormalized runs Basic() BEFORE the denote/realize stage — for the
// ε-heavy argument whose installs must reach clause form before its
// large terms are denoted into stable atoms (the atom vocabulary the
// close then works on is timing-sensitive). Merge it with Denoted /
// HilbertDenoted; on its own it is Normalized.
var PreNormalized = ByShape{pre: true}

// Normalized shapes a By's context with Basic() before the close.
var Normalized = ByShape{}

// HilbertDenoted shapes a By's context with HilbertDenote() + Basic()
// before the close — for arguments whose facts are stated over ε-terms
// that must be denoted before the refuter meets them. A DIFFERENT
// tactic from Denoted's size-threshold denote, hence its own value.
var HilbertDenoted = ByShape{hilbert: true}

// Denoted shapes a By's context with Denote(size) + Basic() — the
// SEARCH form of the shaping. Like Denote itself it is excluded from
// the bare-name surface, library/authoring (a proof file's `Denoted()`
// does not compile); the authoring form is DenotedAs, which says what
// is being named.
func Denoted(size ...int) ByShape { return ByShape{denote: denoteSize(size)} }

// DenotedAs is the EXPLICIT shaping: it names `term` by `name` (then
// Basic()) before the close, instead of letting a size threshold decide.
//
//	By(DenotedAs("d", sumOfGaps), eqX, eqY)
//
// Under Broadcast the shaping runs ONCE PER LEAF, and a leaf it does not
// apply to simply skips it — either because the leaf does not contain
// the term, or because `name` is already free there (the shaping fired
// on the branch this leaf was split from; a BOOLEAN denote's defining
// equation is an ⇔ that the intervening Basic() clause-decomposes, so
// "already denoted" is not always visible as a resident equation). A
// term NO leaf takes is still a loud By failure — the drift this form
// exists to catch.
func DenotedAs(name string, term TermLike) ByShape {
	if term == nil {
		panic("DenotedAs: nil term")
	}
	return ByShape{denoteTerm: term.Core(), denoteName: name}
}

// HilbertDenotedAs is DenotedAs for an ε-term: the explicit twin of
// HilbertDenoted (see HilbertDenoteTerm for the transform).
func HilbertDenotedAs(name string, term TermLike) ByShape {
	if term == nil {
		panic("HilbertDenotedAs: nil term")
	}
	return ByShape{denoteTerm: term.Core(), denoteName: name, denoteHilbert: true}
}

// Broadcast is a premise-list option (like a ByShape, it is not a
// premise): the terminal closer runs over EVERY leaf that is open when
// the premises are down, instead of demanding a single one. It exists
// for the argument whose shaping FANS the leaf — a `Normalized` /
// `Denoted(n)` normalization that splits a conjunction-shaped residual
// into clause leaves, each closed by the SAME refutation from the same
// premises. Without it such a close cannot be a By at all ("CnfRefute
// returned but the goal is still open"), and the site regresses to an
// install pile with hand-paired closers.
//
//	By(Normalized, Broadcast, a, b)   — normalize, then refute each leaf
//
// Opt-in by design: the single-leaf contract stays the default (a fan
// the author did not expect should stay loud), and Broadcast composes
// with a shaping option rather than replacing it — the fan is the
// shaping's doing, the broadcast is the closer's response.
//
// The composition is PER LEAF ("install → normalize → per-leaf {shape,
// close}"): the pre-stage (PreNormalized) runs once on the anchor — the
// fan-producing normalize — and the denote/realize stage (Denoted /
// HilbertDenoted, with its trailing Basic) runs as each leaf's own
// preamble before that leaf's close. A leaf whose preamble has no work
// to do skips it silently (every shaping pass is recover-wrapped), so
// the same-closer fan and the fan whose leaves each need their own
// denote are one option, not two phase models.
type byBroadcast struct{}

// Broadcast — see the type doc.
var Broadcast byBroadcast

type _ByAction struct {
	premises []any
	arith    bool
	settac   bool
	chase    bool
	// site is where the author wrote this By — the source file and line
	// of the call, captured at construction (authorCallSite). Runtime only:
	// never serialized, never part of a key. The recorder's economy audit
	// names it, so that a finding reaches exactly one site even where a
	// member holds several Bys with the same premises.
	site string
	// engineShape marks a By whose shape element the prover inserted
	// itself (a Calc chain's close, ObtainChosen's choice): no author
	// text carries it, so the economy audit does not advise dropping it.
	engineShape bool
}

// moduleSourceRoot is the prefix every source file of this module is
// compiled under, read off this file's own path
// (`<root>/prover/proof/fact.go`): the checkout directory in an
// ordinary build, the module path under -trimpath, the module cache
// when another module imports this one.
var moduleSourceRoot = func() string {
	_, file, _, _ := runtime.Caller(0)
	return strings.TrimSuffix(file, "prover/proof/fact.go")
}()

// authorCallSite returns the file:line of the call to the constructor
// that calls it (By, ByArith, BySets, ByChase, ByInduction, Unfold) in
// the author's source — the frame two above this one — with the path
// cut at the module's source root (`library/proofs/...`). A call in
// another module keeps its path as compiled.
func authorCallSite() string {
	_, file, line, ok := runtime.Caller(2)
	if !ok {
		return ""
	}
	return fmt.Sprintf("%s:%d", strings.TrimPrefix(file, moduleSourceRoot), line)
}

// The execution order is CLEAR-FIRST: resident premises are located,
// every other ambient hyp is cleared, and only then are the named
// premises installed and grounded. Clear-first makes the lexical
// guarantee airtight — an install that absorbs the goal on injection
// (the eqSimplify install-rewrite class) can only have used listed
// premises, never an ambient hyp the list omitted. It also hands the
// refuter a minimal context.
//
// A premise whose materialization closes the goal is accepted when it
// is the LAST premise (whether the close lands at install or at the
// refute is an engine-simplification detail — the calc chain-fold's
// cite-then-close precedent, _CalcChainClose); premises left over
// after an early close panic as over-specification, naming the unused
// tail.
func (b _ByAction) applyAction(s *Script, root *GoalStackNode) {
	anchor := root.unsolvedLeaf(0)
	if anchor == nil {
		panic("By: no unsolved leaves remaining (section already proved — extra By call?)" + closedLeafNote(root))
	}
	if len(b.premises) == 0 && !b.arith && !b.settac {
		panic("By: empty premise list (a bare refutation is CnfRefute())")
	}

	// Shaping options merge (Denoted + HilbertDenoted is the ε-heavy
	// combination); only a denote-size conflict is an error
	// (MergeByShapes, shared with the engine's `by` dispatch).
	var shapes []ByShape
	broadcast := false
	var facts []Fact
	var described []string
	listedHandles := map[*HypHandle]bool{}
	listedCarriers := map[_EvidenceCarrier]bool{}
	depth, depthSet := 0, false
	for _, p := range b.premises {
		if sh, ok := p.(ByShape); ok {
			// Depth(k) rides in the list as a ByShape value, but it is the
			// chase's parameter and no shaping: kept out of the merged shape,
			// so it neither runs Basic() ahead of the close nor records a
			// shape element.
			if sh.depthSet {
				if depthSet && depth != sh.chaseDepth {
					panic(fmt.Sprintf("By: two Depth values in one premise list (%d and %d) — pick one", depth, sh.chaseDepth))
				}
				depth, depthSet = sh.chaseDepth, true
				continue
			}
			shapes = append(shapes, sh)
			continue
		}
		if _, ok := p.(byBroadcast); ok {
			broadcast = true
			continue
		}
		carrier, carriesEvidence := p.(_EvidenceCarrier)
		if carriesEvidence {
			listedCarriers[carrier] = true
		}
		for _, m := range expandPremiseGroup(p) {
			f := premiseFact(m)
			// A member stands for its evidence, and the points a structure
			// door binds in one run share one guard conjunction: listed
			// once, as the list that names the conjunction lists it.
			if h := residentHandleOf(f); h != nil {
				if carriesEvidence && listedHandles[h] {
					continue
				}
				listedHandles[h] = true
			}
			facts = append(facts, f)
			described = append(described, f.describe())
		}
	}
	facts, described = expandLooseReadings(s, anchor, facts, described)
	shape := MergeByShapes(shapes)
	switch {
	case depthSet && !b.chase:
		panic("By: Depth(k) is ByChase's parameter — the number of pull-back rounds; no other closer reads it")
	case !depthSet && b.chase:
		panic("ByChase: the list carries no Depth(k) — the number of pull-back rounds is the author's to write")
	}
	if b.chase && len(facts) == 0 {
		panic("ByChase: the list holds no premises — the closer reads its diagram from the named module, homomorphism, exactness and element facts")
	}
	if len(facts) == 0 && !b.arith && !b.settac {
		// A premise-free BySets or ByArith is legal: the set driver's
		// vocabulary unfolding and the arithmetic decision procedure ARE
		// the content, so "clear everything, run the closer" is a
		// complete statement. The refuter has a premise-free spelling of
		// its own, and an empty By would just obscure it.
		panic("By: premise list holds no premises (a bare refutation is CnfRefute())")
	}

	// Resolve every premise to the composite's descriptor. Named facts
	// resolve here (the Script holds the dep universe); resident facts
	// record their statement so the executor re-locates them by α-match;
	// a kit's derived premise carries its certificate as a runtime input
	// and is asserted AT ITS LIST POSITION inside the executor (order is
	// behavior: an equation resident earlier changes what a later
	// install absorbs).
	premises := make([]byPremise, len(facts))
	var claimCerts []Prop
	for i, f := range facts {
		switch {
		case f.claim != nil:
			if f.derivedCert == nil {
				panic(fmt.Sprintf("By: premise %s is a derived premise without a certificate "+
					"(SelfProvingPremise contract break)", described[i]))
			}
			premises[i] = byPremise{
				install:     f.claim,
				derivedCert: f.derivedCert,
				describe:    described[i],
			}
		case f.residentContent != nil:
			if len(f.named) > 0 {
				panic(fmt.Sprintf("By: premise %s pins a binder by name (Where), which reads the stated "+
					"form of a NAMED fact — a resident hypothesis is grounded positionally (At)", described[i]))
			}
			premises[i] = byPremise{
				install:     prop.MakeProp(contentHypTerm("By", f.residentContent)),
				witnesses:   f.witnesses,
				resident:    true,
				coefficient: f.coefficient,
				describe:    described[i],
			}
		case f.handle != nil:
			if len(f.named) > 0 {
				panic(fmt.Sprintf("By: premise %s pins a binder by name (Where), which reads the stated "+
					"form of a NAMED fact — a resident hypothesis is grounded positionally (At)", described[i]))
			}
			idx := f.handle.resolveOrPanic("By", anchor)
			premises[i] = byPremise{
				install:     prop.MakeProp(anchor.Goal.Hyp(idx)),
				witnesses:   f.witnesses,
				resident:    true,
				coefficient: f.coefficient,
				describe:    described[i],
			}
		default:
			if r, ok := f.target.(readingInst); ok && r.resident() && len(f.witnesses) == 0 && len(f.named) == 0 {
				// A law read under a RESIDENT hypothesis is a fact in
				// context, and it materializes exactly as the Have it
				// replaces: asserted before every install, whatever its
				// list position (withReadingsFirst below), the claim branch
				// closed from the kernel-derived sequent (whose one
				// hypothesis is kept resident beside it —
				// readingHypothesisPremises), the deduction continuing with
				// the fact resident. Not an install: the preserving chain
				// would rewrite the goal with an equation-shaped reading,
				// and a plain add would simplify it — either moves the leaf
				// a Have of the same fact leaves where it is.
				thm := r.resolve(s, anchor)
				premises[i] = byPremise{
					install:      core.MakeProp(thm.Conclusion()),
					derivedCert:  thm,
					readingUnder: true,
					coefficient:  f.coefficient,
					describe:     described[i],
				}
				continue
			}
			// A law read under a resident hypothesis is derived at this
			// leaf, the hypothesis as the leaf spells it, and the derived
			// statement is its own reference form (resolveTargetAt).
			L, reading := resolveTargetAt("By", s, anchor, f.target)
			ref := L
			if !reading {
				ref = citeReferenceProp(s, f.target)
				if len(f.named) > 0 {
					ref = namedCiteReferenceProp(s, f.target)
				}
			}
			witnesses := f.witnesses
			if reading && len(f.witnesses) > 0 {
				L, witnesses = witnessedReadingForm("By", "premise "+described[i], L, f.witnesses)
				ref = L
			}
			pr := byPremise{
				install:     L,
				witnesses:   witnesses,
				named:       f.named,
				coefficient: f.coefficient,
				describe:    described[i],
			}
			// A NAMED premise carries its clause form — the normalized
			// dep, a typed instance's install half. Bare, it installs
			// that form (the closer alone consumes it) with the stated
			// form as the apply rung's head; witnessed, it is a plain add
			// of the stated form the tuple grounds. An explicit Prop, cert
			// or section (no clause form) installs verbatim. The
			// obligation a clause install leaves certifies from its
			// registered normalized cert.
			if clause := premiseClauseForm(s, f.target); clause != nil {
				pr.clause = clause
				if !clause.AlphaEquals(L) {
					claimCerts = append(claimCerts, clause)
				}
			}
			// The STATED form rides along with the install: the witness
			// reorder reads its binder order, and the executor's apply
			// rung reads its telescope (apply_close.go) — the clause form
			// has none. Named pins also distinguish alpha-equal forms
			// whose binder names differ; bare and positional installs
			// retain the certificate's spelling.
			if ref != nil && (!ref.AlphaEquals(L) ||
				len(f.named) > 0 && !ref.Conclusion().Equals(L.Conclusion())) {
				pr.reference = ref
				// A stated-form install the apply rung makes on demand
				// leaves a claim obligation in the stated form; its
				// certificate is the reference itself.
				claimCerts = append(claimCerts, ref)
			}
			if isExplicitInstance(f.target) {
				// An AtTypes instance is an EXPLICIT type instantiation:
				// install it exactly, or chooseTypeAdaptedStep's speculative
				// σ against the goal context overrides the author's choice
				// (the materialize failure of cardinality.CardSubsetEq at B).
				pr.exact = true
			}
			premises[i] = pr
			claimCerts = append(claimCerts, L)
		}
	}

	checkMemberEvidence(readerOf(anchor.proofScope), anchor.Goal, facts, premises, described, listedHandles, listedCarriers)

	// A premise reading a law under a resident hypothesis brings the
	// premise locating that hypothesis with it (reading.go).
	hypotheses := make([][]Term, len(facts))
	for i, f := range facts {
		if f.claim != nil || f.residentContent != nil || f.handle != nil {
			continue
		}
		if r, ok := f.target.(readingInst); ok && r.resident() {
			hypotheses[i] = r.resolve(s, anchor).Hyps()
		}
	}
	premises = withHypothesisPremises(anchor.Goal, premises, hypotheses, described)
	premises = withReadingsFirst(premises)

	// A goal its one premise states as it is closes from that premise's
	// certificate, as the premise's claim obligation would: the composite
	// would leave the goal itself as that obligation.
	if len(premises) == 1 {
		for _, L := range claimCerts {
			if IsStronger(L, anchor.Goal) {
				s.ClaimProvedThm(L)
				if !anchor.runStep(CiteKnown(L).(_KnownThmStep)) {
					panic(fmt.Sprintf("By: the premise states the goal but CiteKnown failed to close it\n  %s", prop.PrintProp(anchor.Goal)))
				}
				return
			}
		}
	}

	// The composite executor (step_by.go): clear-first, install, ground,
	// shape, one refutation — recorded as ONE `by` ministep. The claim
	// obligations of the named premises come back as open children;
	// certify each from the resolved facts (the resolved L IS the cert
	// on the path — resolveLemmaTarget returns proved/promised
	// props), with the cache tiers covering type-adapted obligations.
	s.Do(anchor, _ByStep{
		premises:    premises,
		shape:       shape,
		spine:       anchor,
		arith:       b.arith,
		settac:      b.settac,
		chase:       b.chase,
		chaseDepth:  depth,
		broadcast:   broadcast,
		site:        b.site,
		engineShape: b.engineShape,
		ctx:         context.Background(),
	})
	for _, child := range anchor.Children() {
		if child.Proved() {
			continue
		}
		closed := false
		for _, L := range claimCerts {
			if IsStronger(L, child.Goal) {
				// Certify WITHOUT Script.Do: Do would consume an expected-
				// goal key, but the claim obligations are regenerated by
				// this replayed By in the forms its FACTS resolve to —
				// not the session's recorded install forms — and emit's
				// ledger (sectionExpectedGoalKeys) correspondingly skips
				// the By subtree. The TryMatchKnownThm fallback below is
				// consume-free for the same reason.
				s.ClaimProvedThm(L)
				if !child.runStep(CiteKnown(L).(_KnownThmStep)) {
					panic(fmt.Sprintf("By: certificate covers the premise obligation "+
						"but CiteKnown failed to close it\n  %s", prop.PrintProp(child.Goal)))
				}
				closed = true
				break
			}
		}
		// Type-adapted obligation: installing a POLYMORPHIC fact into a
		// monomorphic goal type-adapts the hyp, so the claim obligation
		// is a TYPE INSTANCE of the resolved fact — IsStronger (no type
		// substitution) misses it, and the cache tiers only see forced
		// thms under their own keys. Certify through _TypeInstStep from
		// the fact itself, exactly the shape the session's tier-3
		// auto-match recorded (source + derivation, never the instance).
		// Live instance: LibraryThm-backed nat_sum.Clauses (type vars
		// ?110063/?110102) cited by the B₀=0 branch of a digit-sum proof.
		if !closed {
			for _, L := range claimCerts {
				if !ext.PropHasTypeVars(L) {
					continue
				}
				if child.runStep(_TypeInstStep{source: L}) {
					s.ClaimProvedThm(L)
					closed = true
					break
				}
			}
		}
		if !closed && !TryMatchKnownThm(s.LocalThmCache, child) &&
			!TryMatchKnownThm(&s.Env.ThmCache, child) {
			panic(fmt.Sprintf("By: no certificate covers the premise obligation\n  %s\n  premises: %s%s",
				prop.PrintProp(child.Goal), strings.Join(described, ", "),
				witnessedInstanceNote(premises, described)))
		}
	}
	Assert(anchor.Proved())
}

// witnessedInstanceNote names, under a refused claim obligation, the
// type instance each witnessed polymorphic premise's tuple forces — the
// instance its obligation stands at — and the spelling that cites the
// entry there outright: the explicit instance's certificate is the
// obligation's own statement, which no type matching has to recover.
func witnessedInstanceNote(premises []byPremise, described []string) string {
	var b strings.Builder
	for i, pr := range premises {
		if len(pr.witnesses) == 0 || pr.exact || pr.resident || pr.install == nil {
			continue
		}
		ref := pr.reference
		if ref == nil {
			ref = pr.install
		}
		if !ext.PropHasTypeVars(ref) {
			continue
		}
		env, _, ok := witnessTypeReading(ref, pr.witnesses)
		if !ok {
			continue
		}
		subst := nonIdentityTypeSubst(env)
		if len(subst) == 0 {
			continue
		}
		letters := make([]string, len(subst))
		types := make([]string, len(subst))
		for j, e := range subst {
			letters[j] = fmt.Sprintf("%s := %s", e.VarType.Name(), ext.FormatType(e.HolType))
			types[j] = ext.FormatType(e.HolType)
		}
		fmt.Fprintf(&b, "\n  premise %s is cited at the instance %s (the types of its tuple); "+
			"an obligation at that instance is covered by citing the entry there: .Inst[%s]()",
			described[i], strings.Join(letters, ", "), strings.Join(types, ", "))
	}
	return b.String()
}

// applyAction makes a GROUNDED RESIDENT fact consumable as a spine
// STEP — `a.Do(f.At(w…))` — for the argument whose ground instance is
// consumed downstream by a step rather than by a close: a rewrite
// ladder, an `Arith`, a `Simp`. Inside a By the same expression is a
// premise and materializes only in that By's leaf; here it
// materializes on the spine itself (groundResident), and the ∀-source
// is KEPT (spine facts stay re-groundable at other witnesses — the
// spine/leaf contract's value side). The verbs that act on the instance
// (Rw, Unpack, Conjuncts, …) take `f.At(w…)` directly and ground it the
// same way.
//
// Deliberately narrow: only the resident flavor with witnesses runs as
// a step. A NAMED fact brought to bear on the goal state is the Cite
// verb's job (`Cite(dep)` / `Cite(dep, w…)`), and a bare resident fact
// is already on the spine — both panic here, pointing at the right
// spelling. Parking ground instances for a later CLOSE remains
// structurally pointless: a later By clears every hyp its premise list
// does not name, so a spine grounding can only serve steps.
func (f Fact) applyAction(s *Script, root *GoalStackNode) {
	f, listed := f.materializeListed("At", s, root, nil)
	switch {
	case f.claim != nil:
		panic("Fact: a self-proving premise runs inside a By premise list, not as a step")
	case f.handle == nil && f.residentContent == nil:
		panic("Fact: a named fact brought to bear on the goal state is Cite(dep) / Cite(dep, w…); " +
			"only a resident fact's ground instance (f.At(w…)) runs as a step")
	case len(f.witnesses) == 0:
		panic(fmt.Sprintf("Fact: %s is already resident — a bare resident fact is not a step "+
			"(ground it: f.At(w…))", f.describe()))
	}
	leaf := root.unsolvedLeaf(0)
	if leaf == nil {
		panic(fmt.Sprintf("Fact.At: no unsolved leaves remaining (section already proved?) — %s",
			f.describe()) + closedLeafNote(root))
	}
	groundResident("Fact.At", s, leaf, f.residentIndex("Fact.At", leaf), f.witnesses, f.describe(), listed)
}

// closeReproductionObligation discharges the leaf a preserving install
// leaves behind — but ONLY when that leaf IS the obligation.
//
// The install has two outcomes. Normally it adds L as a hypothesis and
// leaves the obligation to reproduce, which CiteKnown closes from the
// cache. But when L's equation fires as a goal REWRITE (eqSimplify
// consuming it at injection), the leaf that remains is the REWRITTEN
// GOAL, not an obligation, and CiteKnown then misses with an anonymous
// "no matching cached thm".
//
// Separating the two takes BOTH tests below, because a polymorphic L
// type-adapts on install (chooseTypeAdaptedStep), so the obligation
// leaf carries the INSTANTIATED statement — same printed form, α-unequal
// types — which IsStronger alone cannot equate with the schematic L.
// The cache matcher CiteKnown itself falls back to (TryMatchKnownThm:
// exact / normalized / type-instance tiers, the last recording the
// replay-stable _TypeInstStep) sees through the instantiation. Only
// when IsStronger fails AND both caches miss is the leaf not an
// obligation at all.
func closeReproductionObligation(s *Script, anchor *GoalStackNode, L Prop) {
	leaf := anchor.unsolvedLeaf(0)
	if leaf == nil {
		return // the install absorbed the whole subtree
	}
	if IsStronger(L, leaf.Goal) {
		s.Do(leaf, CiteKnown(L))
		return
	}
	// Type-instantiated obligation, or rewritten goal: the cache
	// matcher decides (same lookup order as Script.Do's CiteKnown
	// fallback). A hit closes the obligation; a double miss means the
	// install was consumed as a rewrite and there is nothing to close.
	if TryMatchKnownThm(s.LocalThmCache, leaf) {
		return
	}
	_ = TryMatchKnownThm(&s.Env.ThmCache, leaf)
}

// locateInstalled finds the hyp index of a just-installed premise so it
// can be grounded.
//
// The before/after hyp diff is the general mechanism, but it is
// ambiguous when the install ALSO rewrites an already-resident premise
// — two hyps are then net-new and grounding dies with "install added
// more than one hyp". So try the exact identification first: the hyp
// alpha-equal to L's own conclusion. Fall back to the diff when the
// install normalized the statement on injection (no exact match), which
// is the case the diff handles correctly.
func locateInstalled(before, after Prop, L Prop) (int, error) {
	if idx, err := findHypIndex(after, L.AsProp().Conclusion()); err == nil {
		return idx, nil
	}
	return newHypIndex(before, after)
}

// =======================================================================
// Cite — the consolidated cite verb
// =======================================================================
//
// The consolidated cite verb for hand-written proofs.
//
// Naming: `Cite` is the VERB (bring a fact to bear on the goal state,
// now); `Fact` is the NOUN — the first-class fact value (fact.go) that
// By/Derive consume; `CiteKnown` (script.go) is the internal bare
// cache-close Step.
//
// The raw cite surface has one verb per plumbing decision: UseLemma vs
// UseLemmaExact picks the install tactic, the bare cache-close
// (CiteKnown) stands alone, CiteSpecialize adds grounding, and a dep
// cite chooses its install FORM by wrapping
// (`ctx.NormalizedThm(ctx.Dep(N))` / `ctx.DepNormalized(N)` / raw
// `ctx.Dep(N)`). Each of those choices is a function of the goal state
// and the dep's shape, not of the mathematics. `Cite` folds the
// decisions into one verb:
//
//	Cite(nat_arith.AddClauses)              // bring the fact to bear
//	Cite("nat_order.LessEqTrans")        // cross-family dep, by name
//	Cite(leTrans, sucM, sucN, p0)       // ground instance at witnesses
//	CiteKeep(leExists, p0, n0)          // … keeping the ∀-source
//
// Semantics of the bare form, decided per call from the goal state:
//
//  1. If the resolved fact already closes the current leaf (the
//     known-thm cache-close — bare `CiteKnown`), close it. Two tiers:
//     the strict stronger-fact match (concl α-equal, hyps ⊆), and the
//     normalize-tier match — the leaf IS the fact modulo Normalize
//     (citeNormalizedClose; the same match the session's auto-match
//     closes such leaves with). The second tier is what keeps the
//     close-vs-install choice a function of the GOAL STATE rather than
//     of the resolved install form: a ⇒-guarded law whose named target
//     resolves to the packed clause form must still close the sequent
//     leaf that states it.
//  2. Otherwise install it as a hypothesis via the PRESERVING lemma
//     chain (ApplyLemmaPreserve — the same dispatch the session-facing
//     `lemma` RPC runs; hyp-preserving, type-adaptation-aware; for a
//     ground lemma the recorded ministep is identical to
//     UseLemmaExact's _LemmaPreserveTactic), then close the lemma-
//     reproduction obligation by cache lookup. If the install closed
//     the whole section, the trailing close is skipped — the class of
//     siteless "no unsolved leaves" panics that forced authors to
//     predict whether a cite would close or install is absorbed here.
//  3. If the fact neither closes nor installs, panic loudly — a no-op
//     Cite is always an authoring error, never silently absorbed.
//
// The witness form is grounding-intent: it never tries the bare close
// (unused witnesses are an authoring error) and runs the established
// cite-at-use mechanics (replay-exact preserve install + cache close +
// content-located Specialize — GoalStackNode.citeSpecialize, the same
// tree CiteSpecialize records).
//
// The target is a CiteTarget, read as its Fact and resolved by the
// dispatch the CiteSpecialize family shares (resolveLemmaTarget): a
// certificate or explicit Prop named through MakeFact is used VERBATIM —
// explicit certs keep full control over the install form; a
// *GoalStackNode contributes its certificate without forcing a deferred
// proof; its stated goal supplies the reference for named binders. A
// registry entry var names its dep, claimed at use via Script.Dep. A
// named dep resolves to the dep's STATED form (the
// entry's headline), the same form the
// session installs: normalization is the closer's business, last, and
// the apply rung reads the telescope only the stated form has. A
// proof that wants a row's normalized form for its own reasons spells
// it — `Cite(MakeFact(ctx.DepNormalized(name)))` — and that
// spelling is the marked minority, not a default anyone re-derives.

// NamedDep is anything that names a registry dep — satisfied by
// *registry.ProofEntry (entry vars) and a family's generated wrappers,
// which are CiteTargets through NamedFact, so cite verbs accept the
// entry var directly: Cite(nat_arith.AddSym). Structural interface: prover
// must not import the registry package.
type NamedDep interface {
	DepName() string
}

// Cite brings a known fact to bear on the current leaf: bare, it
// closes the leaf outright when the fact is stronger, else installs it
// as a hypothesis (preserving chain) and closes the reproduction
// obligation; with witnesses, it installs the fact's ground instance
// at those witnesses (the cite-at-use CiteSpecialize mechanics),
// dropping the ∀-source. See the file header for the full contract.
func Cite(target CiteTarget, witnesses ...TermLike) Action {
	return _CiteAction{target: targetFact("Cite", target), witnesses: ext.CoreTerms(witnesses)}
}

// CiteKeep is the witness form of Cite keeping the cited ∀-source
// resident after grounding (SpecializeKeep semantics). Witnesses are
// required — a bare install always keeps its source, so a bare
// CiteKeep would be Cite.
func CiteKeep(target CiteTarget, witnesses ...TermLike) Action {
	if len(witnesses) == 0 {
		panic("CiteKeep: witnesses required (a bare install keeps its source — use Cite)")
	}
	return _CiteAction{target: targetFact("CiteKeep", target), witnesses: ext.CoreTerms(witnesses), keep: true}
}

type _CiteAction struct {
	target    Fact
	witnesses []Term
	keep      bool
}

// factTarget is what a fact names, its Fact wrapping read through: a
// Fact names its own target (proof.Inst, a wrapper's exact cite), so
// what the target IS — an explicit instance, a reading — does not
// depend on the spelling that reached the verb (resolveLemmaTarget's
// Fact case, the same doctrine).
func factTarget(target any) any {
	if f, ok := target.(Fact); ok {
		return factTarget(f.target)
	}
	return target
}

func (c _CiteAction) applyAction(s *Script, root *GoalStackNode) {
	L := resolveLemmaTarget("Cite", s, c.target)

	// Witness form: grounding intent — the established cite-at-use
	// tree (replay-exact preserve install + cache close + content-
	// located Specialize). The witness tuple is read in the TARGET'S
	// OWN stated binder order (witness_order.go); unused witnesses
	// stay an authoring error (citeSpecialize panics when the cite
	// closes the section).
	if len(c.witnesses) > 0 {
		target := factTarget(c.target)
		ref, witnesses := L, c.witnesses
		if r, ok := readingTarget(target); ok && r.resident() {
			L, witnesses = witnessedReadingForm("Cite", r.describe(), L, c.witnesses)
		} else {
			ref = citeReferenceProp(s, c.target)
		}
		root.citeSpecializeRef(L, ref, c.keep, isExplicitInstance(target), nil, witnesses...)
		return
	}

	leaf := root.unsolvedLeaf(0)
	if leaf == nil {
		panic(fmt.Sprintf("Cite: no unsolved leaves remaining "+
			"(section already proved — extra Cite call?). Cite: %s",
			prop.PrintProp(L)) + closedLeafNote(root))
	}
	// Stage 1 — the fact closes the leaf outright (CiteKnown parity:
	// Script.Do's _KnownThmStep primary path).
	if (L.Proved() || core.IsPromised(L)) && IsStronger(L, leaf.Goal) {
		s.ClaimProvedThm(L)
		if !leaf.runStep(_KnownThmStep{strongerGoal: L}) {
			panic(fmt.Sprintf("Cite: known-thm close failed for %s on goal %s",
				prop.PrintProp(L), prop.PrintProp(leaf.Goal)))
		}
		return
	}

	// Stage 1.5 — the normalize-tier close: the leaf IS the cited fact
	// modulo Normalize (engine normal form). This is the tier the
	// session's auto-match closes such leaves with (a normalized-key
	// match — engine applyAutoMatchOnRoots), and Script.Do's KnownThm
	// arm has it too (TryMatchKnownThm); bare Cite lacked it, so the
	// close-vs-install choice fell to whether the RESOLVED INSTALL FORM
	// happened to be usable by the lemma tactics — a ⇒-guarded law
	// resolved to its packed clause form INSTALLED at a leaf the session
	// had closed (real_field.MulRightInverse; measured: IsStronger is
	// false for BOTH forms there, and the raw form closed only via
	// eqLemma's conditional rewrite, which the clause shape cannot drive).
	//
	// Targeted at L, deliberately NOT a cache-wide TryMatchKnownThm: the
	// recorded step's thm is what emit resolves the cite through, so the close
	// must consume the fact the author cited — a cache-wide scan could
	// close via an unrelated resident and silently re-attribute the dep.
	if citeNormalizedClose(s, leaf, L) {
		return
	}

	// Stage 2 — preserving install (the session `lemma` dispatch:
	// hyp-preserving, type-adaptation-aware; ground lemmas record the
	// same _LemmaPreserveTactic ministep UseLemmaExact does).
	if !ApplyLemmaPreserve(leaf, L) {
		panic(fmt.Sprintf("Cite: %s neither closes the leaf nor installs "+
			"(already resident, or nothing to rewrite?)\n  on leaf goal: %s",
			prop.PrintProp(L), prop.PrintProp(leaf.Goal)))
	}
	// Close the lemma-reproduction obligation — unless the install
	// already closed the whole subtree (the absorbed siteless-panic
	// class: no leaf left means nothing to close, not an error).
	if leaf.unsolvedLeaf(0) != nil {
		s.Do(leaf, CiteKnown(L))
	}
}

// citeNormalizedClose is Cite's stage 1.5: close the leaf with the
// cited fact when the two are the same proposition modulo Normalize.
// Both sides normalize through the SAME engine normal form, so the
// derivation is Normalize's own reconstruction thread — kernel work
// only, promise-transparent (an unforced L yields a derived unforced
// closer, exactly as ThmCache.LoadNormalizedThm's reconstruction does).
//
// The recorded step is _KnownThmStep{reconstructed, equivalentThm: L} —
// the same shape ThmCache tier-2 hits record (commitFoundThmStep), and
// the proto backstop's invariant (equivalentThm normalize-equal to
// strongerGoal) holds by the very key equality that admitted the close.
//
// False (no state change) when the fact is unproved/unpromised, the
// leaf normalizes to ⊤ (the trivial-⊤ guard every normalize-keyed
// close carries — LoadNormalizedThm's rationale), or the normal forms
// differ — the caller falls through to the install stage.
// premiseClauseForm is the closer's form of a named By premise, by
// target kind: a dep named by entry or string resolves to its
// registered NormalizedThm; a typed instance to its install half (the
// normalized dep at the instance types — Normalize and type
// instantiation do not commute, so the half computed at registration
// is the one recorded against); a wrapper to its wrapped target's. An
// explicit Prop, a cert and a section install verbatim (nil).
func premiseClauseForm(s *Script, target any) Prop {
	switch t := target.(type) {
	case NamedDep:
		return s.NormalizedThm(s.Dep(t))
	case *TypedThm:
		return t.Thm
	case typedInst:
		return t.resolve(s).Thm
	case _TypedSoleInst:
		return t.resolve(s).Thm
	case readingInst:
		if t.resident() {
			// A law under a resident hypothesis has no clause form:
			// bare, it is the derived flavor (a Have moved inside the
			// leaf); witnessed, the sequent installs verbatim and grounds.
			return nil
		}
		return s.NormalizedThm(t.resolve(s, nil))
	case Fact:
		if t.claim == nil && t.handle == nil {
			return premiseClauseForm(s, t.target)
		}
	}
	return nil
}

func citeNormalizedClose(s *Script, leaf *GoalStackNode, L Prop) bool {
	stronger := normalizeTierCloser(leaf.Goal, L)
	if stronger == nil {
		return false
	}
	s.ClaimProvedThm(L)
	return leaf.runStep(_KnownThmStep{strongerGoal: stronger, equivalentThm: L})
}

// normalizeTierCloser is the closer citeNormalizedClose records on goal
// for the cited L: Normalize's reconstruction of L's normal form at
// goal, stronger than goal. nil when L is neither proved nor promised,
// goal normalizes to ⊤, or the two normal forms differ.
func normalizeTierCloser(goal, L Prop) Prop {
	if !(L.Proved() || core.IsPromised(L)) {
		return nil
	}
	normLeaf, reconstruct := Normalize(goal)
	if normLeaf.Conclusion().Equals(T) {
		return nil
	}
	normL, _ := Normalize(L)
	if normLeaf.AlphaKey() != normL.AlphaKey() {
		return nil
	}
	stronger := reconstruct(normL)
	Assert(IsStronger(stronger, goal))
	return stronger
}

// =======================================================================
// CiteACRegroup — permute-and-reassociate as one cite
// =======================================================================
//
// ac_regroup — "permute and re-associate a sum" as a first-class
// Action: install ⊢ lhs = rhs for two ground sums that are
// AC-rearrangements of each other through the same surface Cite /
// CiteSpecialize use.
//
// This file is the ACTION SHELL only — the goal-state plumbing that
// cannot live outside package prover, since it inspects the current
// leaf at apply time. The mathematics (parsing the assoc/sym certs,
// flatten/reorder, the kernel composition that produces the equation)
// is prover/solver/ac, a leaf package below proof: see its doc for
// why the split falls here.
//
// The corpus hand-spells this walk today as 5-6 consecutive
// CiteSpecialize(addAssoc, …) / CiteSpecialize(addSym, …) ground
// instances whose only purpose is to let the CNF refuter paramodulate
// one regrouped sum into another (the arith Phase C fresh-eye's
// [kernel-wishlist] item). CiteACRegroup replaces each walk with ONE
// call: the assoc/sym instances still happen, but at the Prop layer
// (kernel-checked Refl / Apply / EqSym / EqTrans composition — never a
// recorded tactic chain per instance), and only the FINAL equation
// touches the goal tree.
//
// Record/replay: the recorded ministeps are the cite-then-ground shape
// CiteSpecialize produces — one `lemma_preserve` carrying the derived
// equation, one `known_thm` closing its reproduction child, and (when
// the equation has free variables, which the LemmaPreserve surface
// ∀-closes on install) one composite `specialize` grounding the
// closure back at its own variables. The derivation is a pure function
// of (assoc, sym, lhs, rhs) — no CNF refute, no search, no cache
// state — so a Build re-run replays it byte-for-byte.

// CiteACRegroup derives ⊢ lhs = rhs — lhs and rhs being ground sums
// over one associative-commutative binary op ⊕ that flatten to the
// same leaf multiset — and installs the equation on the current leaf
// through the same surface Cite / CiteSpecialize use: replay-exact
// LemmaPreserve + Cite (UseLemmaExact), followed by one composite
// Specialize that grounds the surface's ∀-closure back to the literal
// equation, which then sits as a resident hypothesis for a downstream
// CnfRefute to paramodulate. When the current leaf's goal IS the
// regroup equation, the Action closes it outright with a direct Cite.
//
// assoc must be a certificate of the shape ∀m n p. (m⊕n)⊕p = m⊕(n⊕p)
// (either orientation), sym of the shape ∀m n. m⊕n = n⊕m, both over
// the SAME op ⊕, which is read off the assoc statement — the Action
// works for any AC op whose certs are supplied (callers pass e.g.
// ctx.Dep(AddAssoc) / ctx.Dep(AddSym); nothing is
// hardcoded to a particular entry). See ac.New / ac.Validate for the
// certificate and input contracts, and ac.Deriver.RegroupEq for the
// derivation.
//
// Panics (soundness-first — every misuse is loud, nothing degrades) on
// nil arguments, on any ac-level certificate or input violation, and
// when the section has no unsolved leaf at apply time.
func CiteACRegroup(assoc, sym Thm, lhs, rhs *ext.TermWrapper) Action {
	if assoc == nil || sym == nil {
		panic("CiteACRegroup: nil assoc/sym certificate")
	}
	if lhs == nil || rhs == nil {
		panic("CiteACRegroup: nil lhs/rhs term")
	}
	d := ac.New(assoc, sym)
	l, r := lhs.Core(), rhs.Core()
	d.Validate(l, r)
	return _CiteACRegroupAction{d: d, lhs: l, rhs: r}
}

// ACRegroup is CiteACRegroup with the endpoints READ OFF THE GOAL: the
// current leaf must itself be the equation `lhs = rhs` between two
// ⊕-sums over the same leaf multiset, and the derived certificate
// closes it.
//
// This is the shape a rearrangement LEMMA wants. Spelling the endpoints
// at such a site means writing the equation twice — once as the
// section's statement, once as a pair of hand-built terms — and the
// second copy is exactly what the section header already says. The
// leaf's own goal is the honest source, and it costs nothing: the
// derivation is the same pure function of (assoc, sym, lhs, rhs).
//
// The binders are the caller's business: strip them (a section closure
// parameter, or StripQuant) so the goal is the bare equation, and the
// frees stand in for the ground terms the derivation needs — AC
// rearrangement never looks inside a leaf.
//
// Panics (soundness-first) when the section has no unsolved leaf, when
// the leaf's goal is not an equation, and — via ac.Validate — when the
// two sides are not AC-equal.
func ACRegroup(assoc, sym Thm) Action {
	if assoc == nil || sym == nil {
		panic("ACRegroup: nil assoc/sym certificate")
	}
	return _CiteACRegroupAction{d: ac.New(assoc, sym), fromGoal: true}
}

// ACRegroupWith is ACRegroup over a Deriver the caller already holds —
// for the family that states its ⊕ assoc/sym pair ONCE (an `ac.New`
// wrapped in a `family.go` helper) and wants both of the kit's faces
// from that single statement.
//
// The kit's premise face is `d.Eq(lhs, rhs)`, consumed by `By`; this is
// its goal face. Without it a member whose GOAL is the rearrangement
// cannot reach the family helper at all — `ACRegroup` takes the raw
// certificate pair — so it re-spells the two `DepNormalized` locals
// inline, which is the second copy of the pair the helper exists to
// prevent.
//
// It lives here rather than as `(*ac.Deriver).Regroup()`, which is the
// shape everyone proposes first: `proof` imports the solver kits, so a
// kit cannot name `Action`. Same layering that makes a kit's premise
// reach `By` through `SelfProvingPremise` rather than by returning a
// `Fact`.
func ACRegroupWith(d *ac.Deriver) Action {
	if d == nil {
		panic("ACRegroupWith: nil deriver")
	}
	return _CiteACRegroupAction{d: d, fromGoal: true}
}

// ApplyACRegroup is the Script-free twin of the ACRegroup Action — the
// engine-facing entry for the session `ac_regroup` tactic. The focused
// leaf's goal must be the bare equation `lhs = rhs` between two ⊕-sums
// over one leaf multiset (strip the binders first); the composite
// (step_ac.go) closes it from the derived certificate, or — when the
// goal is not itself the regroup equation — installs the certificate as
// a resident hypothesis for a downstream refute, grounded back to the
// literal equation. One executor with the Action: the recorded step is
// the same composite either way, so emit renders it 1:1.
//
// Panics (recovered by the engine dispatch into the RPC error channel)
// carry the ac kit's own contract diagnostics — nil certs, shape
// violations, sides that are not AC-equal.
func ApplyACRegroup(n *GoalStackNode, assoc, sym Thm) bool {
	if assoc == nil || sym == nil {
		panic("ac_regroup: nil assoc/sym certificate")
	}
	leaf := n.unsolvedLeaf(0)
	if leaf == nil {
		return false
	}
	return leaf.runStep(_ACRegroupStep{assoc: assoc, sym: sym})
}

type _CiteACRegroupAction struct {
	d        *ac.Deriver
	lhs, rhs Term
	fromGoal bool // read the endpoints off the leaf instead of lhs/rhs
}

func (a _CiteACRegroupAction) applyAction(s *Script, root *GoalStackNode) {
	who := "CiteACRegroup"
	if a.fromGoal {
		who = "ACRegroup"
	}
	leaf := root.unsolvedLeaf(0)
	if leaf == nil {
		panic(who + ": section has no unsolved leaves remaining " +
			"(already proved — extra Step in chain?)" + closedLeafNote(root))
	}
	if a.fromGoal {
		// The goal face records the ONE composite (step_ac.go) — the
		// session's `ac_regroup` and this Action are one executor, and
		// emit renders the step back as ACRegroup(<assoc>, <sym>).
		assoc, sym := a.d.Certs()
		s.Do(leaf, _ACRegroupStep{assoc: assoc, sym: sym})
		return
	}
	eq := a.d.RegroupEq(a.lhs, a.rhs)
	if IsStronger(eq, leaf.Goal) {
		// The leaf IS the regroup equation — the degenerate install.
		// Close it with a direct Cite (recorded `known_thm`, resolved
		// against the derived cert): the LemmaPreserve surface would
		// refuse a lemma α-equal to the goal as circular, a guard the
		// tactic layer cannot waive because it sees only the Prop, not
		// the fact that the equation is independently kernel-derived.
		s.Do(leaf, CiteKnown(eq))
		return
	}
	before := leaf.Goal
	root.UseLemmaExact(eq)
	// The LemmaPreserve forward-load installs the equation in "general
	// form" — ∀-closed over its free variables (hypMatching's closure).
	// Ground it back to the literal equation by instantiating each
	// binder at its own variable, exactly the cite-then-ground shape
	// CiteSpecialize records (one composite `specialize` ministep).
	res := root.unsolvedLeaf(0)
	if res == nil {
		return // the install closed the section outright
	}
	idx, err := newHypIndex(before, res.Goal)
	if err != nil {
		// No single new hyp: the hyp-preserving lemma chain consumed
		// the equation another way (e.g. a conclusion rewrite). That
		// is a deterministic, recorded outcome — accept it.
		return
	}
	vars, body := ac.StripForallBinders(res.Goal.Hyp(idx))
	if len(vars) == 0 {
		return // installed ground already (no free vars to close over)
	}
	if !body.AlphaEquals(eq.Conclusion()) {
		panic(fmt.Sprintf("CiteACRegroup: installed hyp is not a ∀-closure of the derived "+
			"equation — unexpected install shape\n  installed: %s\n  derived:   %s",
			ext.PrintTerm(res.Goal.Hyp(idx)), PrintProp(eq)))
	}
	witnesses := make([]Term, len(vars))
	for i, v := range vars {
		witnesses[i] = v
	}
	s.Do(res, Specialize(InstHyp(idx, witnesses...)))
}

// withHypothesisPremises inserts, before each premise reading a law
// under a resident hypothesis, the premise locating that hypothesis
// (readingHypothesisPremise) — one per hypothesis not already listed
// (α-keyed on the located hypothesis). hypotheses is parallel to
// premises: every hypothesis premise i is read under, nil where it is
// read under none. Before, not after: a premise listed after one that
// closes the goal on contact is reported unused.
func withHypothesisPremises(leaf Prop, premises []byPremise, hypotheses [][]Term, described []string) []byPremise {
	listed := map[core.TermKey]bool{}
	for _, pr := range premises {
		if pr.resident {
			listed[pr.install.AsProp().Conclusion().AlphaKey()] = true
		}
	}
	out := make([]byPremise, 0, len(premises))
	for i, pr := range premises {
		for _, h := range hypotheses[i] {
			cp := readingHypothesisPremise(leaf, h, described[i])
			if key := cp.install.AsProp().Conclusion().AlphaKey(); !listed[key] {
				listed[key] = true
				out = append(out, cp)
			}
		}
		out = append(out, pr)
	}
	return out
}
