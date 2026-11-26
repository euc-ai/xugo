package proof

// reading.go — a law read at an instance: Read(law, instance).
//
// A structure's law is a Horn theorem `∀comps. S(comps) ⇒ body`, and a
// consumer at a carrier cites it beside the carrier's instance theorem
// `S(c₁, …, cₙ)` — `By(dot.AddLeft, real_ring.CommRing)` — the apply
// rung reading the components off the goal and the hypothesis off the
// instance. Where the law is wanted as a VALUE rather than at a goal —
// a Simp rule, a typed ground cite, a premise a calc leg names — the
// same two facts make one theorem: the law type- and term-instantiated
// at the instance's components, its hypothesis discharged by the
// instance, `⊢ body[comps := c]`. Read is that theorem as a cite
// target. The kernel derives it when a verb consumes the value (instantiation
// at the components, modus ponens against the instance); it is served
// in its stated form like any named dep, closes keyless, records
// nothing, and its deps are the two entries it is read from, both
// claimed at use like any cite.
//
// The law may also be a proved LOCAL section of the member — the node
// `ctx.Lemma` returns, stated over the structure binder — read as an
// entry's law is: its statement is the section's root goal, its theorem
// the section's, and it adds no dep of its own.
//
// The instance is one of two things. A registered instance ENTRY —
// the carrier's `S(c)` theorem, `real_ring.CommRing` — gives a closed
// reading. A RESIDENT structure fact of the proof in progress — the
// hypothesis a Law's closure receives (`ring`), a Have's
// `monoidal_op(vadd)` — gives the reading UNDER that hypothesis,
// `S(c) ⊢ body[comps := c]`, the instance being the fact assumed as the
// leaf consuming the reading spells it (hypothesis). That is the one
// hop a chapter stated over a structure otherwise writes as a Have per
// use — `monoidal_op(vadd)` from `vec_space.MonoidalVecAdd` and the
// ring — and the hop is the kernel's:
// where the value is consumed the hypothesis is resident, so a By
// keeps it beside the reading and materializes the reading exactly as
// the Have it replaces — asserted at its list position, the claim
// branch closed from the derived sequent, the fact then resident —
// the form the apply rung and the closer both read, and the leaf the
// Have left. Its deps are the law alone.
//
// The instance's statement must be the law's antecedent applied to
// concrete components: the predicate with each leading ∀-binder in one component slot;
// other components remain fixed by prior readings.
// Anything else refuses at consumption naming both statements. The
// type letters the components' types carry are fixed by the instance;
// a letter the law binds elsewhere stays a variable of the reading.
//
// A reading materialized as a fact of the leaf has rigid type letters.
// A By can instead cite a loose law beside its resident instance, any
// witness tuple grounding the law at the components as well, each at
// its own binder (expandLooseReadings).
// An unwitnessed nested reading uses the law beside the inner
// reading's derived structure fact. Witnessed nested readings retain
// their derived sequent: the tuple fixes its loose letters while every
// type letter in the resident hypotheses stays fixed (ReadingAtWitnessTypes).

import (
	"fmt"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/ematch"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/prover/typematch"
)

// readingInst is Read's deferred value — resolved at a Script, like a
// typed instance, so the value is pure and may sit at package level.
// Exactly one of the two instance fields is set: the instance entry,
// or the resident fact the reading is taken under.
type readingInst struct {
	law      NamedDep
	instance NamedDep // an instance entry
	at       Fact     // a resident structure fact, when instance is nil
	// inner is set when the instance is itself a READING — a projection
	// law read at an instance, `abelian_group.Monoid.Read(group)`, whose
	// conclusion is the sub-structure at its components: the outer law
	// is read at that derived instance, under whatever the inner one is
	// under. Exactly one of instance, at and inner is set.
	inner *readingInst
	// prior is the law after an earlier bundle has already been read.
	prior *readingInst
}

// resident reports the form under a hypothesis of the proof in
// progress: a reading at a resident fact, or at a reading that is.
func (r readingInst) resident() bool {
	if r.prior != nil && r.prior.resident() {
		return true
	}
	if r.inner != nil {
		return r.inner.resident()
	}
	return r.instance == nil
}

// Read is `law` read at `instance`: the structure law's statement with
// its components pinned to the instance's and its hypothesis
// discharged — as a Fact, for By, Simp (`Fwd(Read(law, inst))`) and
// ground cites (`At(Read(law, inst), w…)`). Further instances read successive
// structure binders: `Read(law, source, target).At(f)` supplies each
// bundle once and retains the hypotheses of every resident instance.
// The law is a registry entry, or a PROVED local section — the node
// `ctx.Lemma` returns, its statement opening with the structure binder
// (`∀L:field_on(A). …`): `Read(chart, L).At(…)` reads it at the bundle
// fact as a member's reading is read, the section's theorem in place of
// the entry's. The instance is a registry
// entry (the carrier's instance theorem) or a resident structure fact
// of the proof in progress (the hypothesis a Law's closure receives, a
// Have's fact), bare — neither grounded nor pinned, since the reading
// is derived from its content. A family's generated wrapper spells the
// same value typed, `dot.AddLeft.Read(inst).At(u, v, w)`, with the
// component slots gone.
func Read(law any, instance any, further ...any) Fact {
	dep := lawDep(law)
	r := readOne(dep, instance)
	for _, next := range further {
		previous := r
		r = readOne(dep, next)
		r.prior = &previous
	}
	return Fact{target: r}
}

// lawDep is the law of a reading as a NamedDep: an entry as it is, a
// local section as a _SectionLaw.
func lawDep(law any) NamedDep {
	switch l := law.(type) {
	case nil:
		panic("Read: the law and the instance are both required")
	case *GoalStackNode:
		if l == nil {
			panic("Read: the law and the instance are both required")
		}
		return _SectionLaw{node: l}
	case NamedDep:
		return l
	}
	panic(fmt.Sprintf("Read: the law is a registry entry or a proved local section (the node ctx.Lemma returns); got %T", law))
}

// _SectionLaw is a local section read as a law. Its statement is the
// section's root goal, known before the proof runs; its theorem is the
// section's, once the section is proved (lawProp).
type _SectionLaw struct{ node *GoalStackNode }

// DepName names the section by its statement, for a refusal.
func (l _SectionLaw) DepName() string {
	return "the local section " + clipRunes(ext.PrintTerm(l.node.Goal.Conclusion()), 60)
}

// StatementProp is the section's statement.
func (l _SectionLaw) StatementProp() core.Prop { return l.node.Goal }

// lawProp is the law's theorem at s: an entry's through the Script,
// which claims it; a section's own, which the section's Qed already
// registered.
func (r readingInst) lawProp(s *Script) Prop {
	if sec, ok := r.law.(_SectionLaw); ok {
		if !sec.node.Proved() {
			panic(fmt.Sprintf("Read(%s): the section is not proved — a section is read once its proof is closed", sec.DepName()))
		}
		// In the statement's spelling: a binder pinned by name is named
		// as the section states it.
		thm := prop.WeakenTo(sec.node.PromisedThm(), sec.node.Goal)
		if thm == nil {
			panic(fmt.Sprintf("Read(%s): the section's theorem does not state its goal (engine invariant)", sec.DepName()))
		}
		return thm
	}
	return s.Dep(r.law)
}

// lawCiteTarget is the law as a cite target, for the loose expansion:
// the entry, or the section's node.
func (r readingInst) lawCiteTarget() any {
	if sec, ok := r.law.(_SectionLaw); ok {
		return sec.node
	}
	return r.law
}

// lawDescribe names the law in a description: an entry by its name, a
// section by its statement.
func (r readingInst) lawDescribe() string {
	if _, ok := r.law.(_SectionLaw); ok {
		return r.law.DepName()
	}
	return fmt.Sprintf("dep %q", r.law.DepName())
}

func readOne(law NamedDep, instance any) readingInst {
	if law == nil || instance == nil {
		panic("Read: the law and the instance are both required")
	}
	switch inst := instance.(type) {
	case CiteTarget:
		return readingAt(law, inst.AsFact())
	case NamedDep:
		return readingInst{law: law, instance: inst}
	}
	panic(fmt.Sprintf("Read(%s): the instance is a registry entry (the carrier's instance theorem) or a "+
		"resident fact of the proof in progress (the structure hypothesis a Law's closure receives, a "+
		"Have's fact); got %T", law.DepName(), instance))
}

// readingAt is the constructor behind a Fact instance: a resident fact
// gives the reading under its hypothesis; a fact that merely names an
// entry is that entry's reading; anything grounded, pinned or
// self-proving is refused — a reading pins nothing of its instance.
func readingAt(law NamedDep, at Fact) readingInst {
	if at.claim != nil {
		panic(fmt.Sprintf("Read(%s): a self-proving premise is not a resident hypothesis", law.DepName()))
	}
	if len(at.witnesses) > 0 || len(at.named) > 0 {
		if _, ok := at.target.(readingInst); ok {
			// A reading grounded at its witnesses is a structure fact at
			// concrete components, which no entry states and no hypothesis
			// holds: the fact a Have names.
			panic(fmt.Sprintf("Read(%s): %s is a reading grounded at its witnesses — a law is read at an "+
				"instance entry, a resident fact or a reading, bare; state the ground fact as a Have proved "+
				"by that grounded reading, and read the law at the Have", law.DepName(), at.describe()))
		}
		panic(fmt.Sprintf("Read(%s): the instance is the structure fact itself, not %s — a reading pins "+
			"nothing of it", law.DepName(), at.describe()))
	}
	if at.handle == nil && at.residentContent == nil {
		if dep, ok := at.target.(NamedDep); ok {
			return readingInst{law: law, instance: dep}
		}
		if inner, ok := at.target.(readingInst); ok {
			// A reading at a reading: the inner one's conclusion is the
			// structure at its components, which is what the outer law's
			// hypothesis is discharged against.
			return readingInst{law: law, inner: &inner}
		}
		panic(fmt.Sprintf("Read(%s): %s is neither a registry entry, a resident hypothesis nor a reading",
			law.DepName(), at.describe()))
	}
	return readingInst{law: law, at: at}
}

// _StatedDep is a dep whose statement is known before the proof runs: a
// registry entry.
type _StatedDep interface {
	NamedDep
	StatementProp() core.Prop
}

// content is what the reading says where that is known before the
// proof runs — the law's statement read at what its instance says: a
// resident fact's bound content, an instance entry's statement, an
// inner reading's own content — and false where the law or the
// instance states nothing at this time. It is the reading's statement
// in the instance normal form, what a closure law read at the reading
// names its member from (instanceContent); the proof derives the same
// statement when the reading is consumed (resolve).
func (r readingInst) content() (core.Term, bool) {
	stated, ok := r.law.(_StatedDep)
	if !ok {
		return nil, false
	}
	law := stated.StatementProp()
	if r.prior != nil {
		prior, known := r.prior.content()
		if !known {
			return nil, false
		}
		law = core.MakeProp(prior)
	}
	var instance core.Term
	switch {
	case r.inner != nil:
		instance, ok = r.inner.content()
	case r.instance != nil:
		entry, isStated := r.instance.(_StatedDep)
		if !isStated {
			return nil, false
		}
		statement := entry.StatementProp()
		if statement.NumHyps() > 0 {
			return nil, false
		}
		instance, ok = statement.Conclusion(), true
	default:
		instance, ok = instanceContent(r.at)
	}
	if !ok {
		return nil, false
	}
	read, err := readLawStatementAt(law, core.Assume(instance))
	if err != nil {
		panic(fmt.Sprintf("Read(%s): %v", r.describe(), err))
	}
	return read.Conclusion(), true
}

// hypothesis is the resident form's hypothesis, what a By keeps
// resident beside the reading (readingHypothesisPremises): the
// hypothesis as leaf spells it, the handle followed from its binding
// down to the leaf as a premise handle is (HypHandle.resolve), so a Let
// or a Simp that respelled it since the fact was taken is read at the
// current text, and a hypothesis the leaf no longer carries is refused
// naming the step that consumed it. With no leaf in hand it is the
// content the fact was bound to. nil for a closed reading.
func (r readingInst) hypothesis(leaf *GoalStackNode) core.Term {
	if !r.resident() {
		return nil
	}
	if r.inner != nil {
		return r.inner.hypothesis(leaf)
	}
	if r.at.handle != nil {
		if leaf != nil {
			idx, err := r.at.handle.resolve(leaf)
			if err != nil {
				panic(fmt.Sprintf("Read(%s): the law is read under hyp %q, which is not a hypothesis of this leaf — "+
					"HypHandle %q: %v\n(current goal: %s)",
					r.law.DepName(), r.at.handle.Name(), r.at.handle.Name(), err, prop.PrintProp(leaf.Goal)))
			}
			return leaf.Goal.Hyp(idx)
		}
		t, bound := r.at.BoundContent()
		if !bound {
			panic(fmt.Sprintf("Read(%s): hyp %q is not bound", r.law.DepName(), r.at.handle.Name()))
		}
		return t
	}
	return contentHypTerm("Read", r.at.residentContent)
}

// instanceProp is what the law's hypothesis is discharged against: the
// entry's served theorem, or the resident fact ASSUMED — `S(c) ⊢ S(c)`
// — so the reading carries that hypothesis to where it is resident.
func (r readingInst) instanceProp(s *Script, leaf *GoalStackNode) Prop {
	if r.inner != nil {
		return r.inner.resolve(s, leaf)
	}
	if r.instance != nil {
		return s.Dep(r.instance)
	}
	return core.Assume(r.hypothesis(leaf))
}

// resolve derives the reading at s, for a consumer at leaf — nil where
// none is in hand (hypothesis). A closed reading (at an entry) is
// registered as a known theorem, so every cite of it closes by
// known-thm lookup; one under a hypothesis is the derived sequent
// itself, consumed where the hypothesis is resident. The theorem is
// handed on as derived: a certificate, or a promise where the law is a
// section whose own certificate is still one (a derivation goes lazy
// at an unforced dependency, core.deriveProp), settled with the
// consumer's. Nothing forces at the read, as no cite of a section does
// (GoalStackNode.PromisedThm).
func (r readingInst) resolve(s *Script, leaf *GoalStackNode) Thm {
	lawCert := r.lawProp(s)
	if r.prior != nil {
		lawCert = r.prior.resolve(s, leaf)
	}
	thm, err := readLawAt(lawCert, r.instanceProp(s, leaf), libraryRead(s.Scope))
	if err != nil {
		panic(fmt.Sprintf("Read(%s): %v", r.describe(), err))
	}
	if r.resident() {
		return core.AsThm(thm)
	}
	return s.registerKnownThm(thm)
}

// resolveTargetAt is resolveLemmaTarget for a verb consuming its target
// at leaf: a law read under a resident hypothesis — bare, or the target
// of a Fact that names nothing else — is derived there, its hypothesis
// as the leaf spells it (hypothesis), and the result reports that it
// was: the derived statement is then its own reference form, where a
// caller needs one (citeReferenceProp). Any other target resolves as it
// does with no leaf in hand.
func resolveTargetAt(who string, s *Script, leaf *GoalStackNode, target any) (resolved Prop, residentReading bool) {
	if r, ok := readingTarget(target); ok && r.resident() {
		return r.resolve(s, leaf), true
	}
	return resolveLemmaTarget(who, s, target), false
}

// readingTarget is the reading a cite target is: bare, or the target of
// a Fact that names nothing else — neither a hypothesis nor a claim,
// no witnesses, no pins.
func readingTarget(target any) (readingInst, bool) {
	switch t := target.(type) {
	case readingInst:
		return t, true
	case Fact:
		if t.claim == nil && t.handle == nil && t.residentContent == nil && len(t.witnesses) == 0 && len(t.named) == 0 {
			return readingTarget(t.target)
		}
	}
	return readingInst{}, false
}

func (r readingInst) describe() string {
	if r.prior != nil {
		current := r
		current.prior = nil
		return r.prior.describe() + "; then " + current.describe()
	}
	if r.inner != nil {
		return fmt.Sprintf("%s read at (%s)", r.lawDescribe(), r.inner.describe())
	}
	if r.resident() {
		return fmt.Sprintf("%s read at %s", r.lawDescribe(), r.at.describe())
	}
	return fmt.Sprintf("%s read at %q", r.lawDescribe(), r.instance.DepName())
}

// readingHypothesisPremise is the premise that goes with a By premise
// reading a law under the RESIDENT hypothesis h (the resident form of
// Read): the resident premise locating h among the leaf's, kept beside
// the reading so that the derived sequent's hypothesis is in the goal
// where its certificate closes the claim branch (fact.go). A
// hypothesis the leaf no longer carries (bound, then rewritten away) is
// an authoring error, named.
func readingHypothesisPremise(leaf Prop, h Term, described string) byPremise {
	idx, err := findHypIndex(leaf, h)
	if err != nil {
		panic(fmt.Sprintf("By: %s reads its law under %s, which is not a hypothesis of this leaf\n  leaf: %s",
			described, ext.PrintTerm(h), prop.PrintProp(leaf)))
	}
	return byPremise{
		install:  prop.MakeProp(leaf.Hyp(idx)),
		resident: true,
		kept:     true,
		describe: "the hypothesis the reading is under, " + clipRunes(ext.PrintTerm(h), 60),
	}
}

// ReadingRecord says what a reading was read from: the law, and the
// instance it was read at. A session's premise or rule carries it to
// the wire (ReadingProto), where emit spells `law.Read(instance)` from
// it; no executor consults it.
type ReadingRecord struct {
	// Law is the law's stated form.
	Law Prop
	// Exactly one of the three is set: Instance, an instance entry's
	// stated form; Under, the resident hypothesis the reading is taken
	// under; Inner, the reading the law is read at.
	Instance Prop
	Under    Term
	Inner    *ReadingRecord
}

func (r *ReadingRecord) proto(b *ext.PoolBuilder) *ReadingProto {
	if r == nil {
		return nil
	}
	p := &ReadingProto{Law: b.PropRef(r.Law)}
	switch {
	case r.Instance != nil:
		p.Instance = b.PropRef(r.Instance)
	case r.Under != nil:
		p.Under = b.PropRef(prop.MakeProp(r.Under))
	case r.Inner != nil:
		p.Inner = r.Inner.proto(b)
	default:
		panic("ReadingRecord: no instance, hypothesis or inner reading")
	}
	return p
}

// ReadingRecordFromProto decodes a recorded reading; nil for an absent
// or empty message (a rule that is no reading).
func ReadingRecordFromProto(r *ext.PoolReader, p *ReadingProto) *ReadingRecord {
	if p == nil || p.GetLaw() == nil {
		return nil
	}
	law, _ := r.Prop(p.GetLaw())
	rec := &ReadingRecord{Law: law}
	switch {
	case p.GetInstance() != nil:
		rec.Instance, _ = r.Prop(p.GetInstance())
	case p.GetUnder() != nil:
		under, _ := r.Prop(p.GetUnder())
		rec.Under = under.Conclusion()
	case p.GetInner() != nil:
		rec.Inner = ReadingRecordFromProto(r, p.GetInner())
	}
	return rec
}

// Hypothesis is the resident hypothesis the reading is taken under —
// its own, or its inner reading's — and nil for a reading at an entry.
func (r *ReadingRecord) Hypothesis() Term {
	switch {
	case r == nil:
		return nil
	case r.Inner != nil:
		return r.Inner.Hypothesis()
	}
	return r.Under
}

// ReadLawAt is the reading's derivation for a caller that holds the two
// theorems rather than a Script — the serve bundles bind a structure
// law read at a carrier's instance entry (`field.InvMul` at
// `real_field.Field`) exactly as a proof's cite of the reading does.
func ReadLawAt(law, instance Prop) (Prop, error) { return readLawAt(law, instance, nil) }

// ReadLawStated is the reading's derivation for a law given as its
// statement: the registry's readings view, which states what a cite
// hands over and proves nothing. The derivation yields a statement, so
// the instance normal form reads its record equations as statements
// too (tactic.StatedRead) instead of building their proofs.
func ReadLawStated(law, instance Prop) (Prop, error) {
	return readLawAt(law, instance, tactic.StatedRead)
}

// ReadingAtWitnessTypes instantiates only the reading's loose type
// letters forced by its witness tuple. Every letter in a hypothesis
// stays rigid, so the derived certificate is under the same resident
// facts. Unwitnessed letters stay as stated; the goal supplies no types.
// A witness is read at its binder's type first (FitWitness: a bare
// polymorphic constant's fresh letters take the binder's), and the
// tuple is returned so retyped. A witness that fits its binder no way
// is refused naming the two types and, where the witness carries a
// letter nothing pinned, the tie that pins it.
func ReadingAtWitnessTypes(reading Prop, witnesses []Term) (Prop, []Term, error) {
	if len(witnesses) == 0 {
		return reading, witnesses, nil
	}
	fixed := ReadingFixedLetters(reading)
	loose := func(v core.VarType) bool { return !fixed(v) }
	subst, fitted, _, ok := witnessTypeReadingWith(reading, witnesses, loose)
	if !ok {
		return nil, nil, fmt.Errorf("the witness tuple does not fit the reading's binders with its resident hypothesis types fixed%s",
			witnessMisfit(reading, witnesses, loose))
	}
	return core.PropTypeInst(reading, nonIdentityTypeSubst(subst)...), fitted, nil
}

// witnessedReadingForm is a law read under a RESIDENT hypothesis taken
// at a witness tuple, as the By builder and the fact verbs install it:
// its loose letters read from the tuple with every letter a hypothesis
// spells fixed (ReadingAtWitnessTypes), the tuple typed at the binders,
// and the goal consulted for no type — the instance is then explicit
// (isExplicitInstance), and installs as it is. A tuple that fits the
// binders no way is refused, naming the verb and the premise.
func witnessedReadingForm(who, described string, reading Prop, witnesses []Term) (Prop, []Term) {
	typed, fitted, err := ReadingAtWitnessTypes(reading, witnesses)
	if err != nil {
		panic(fmt.Sprintf("%s: %s: %v", who, described, err))
	}
	return typed, fitted
}

// ReadingAtGoalTypes instantiates the reading's loose type letters at
// the types the goal pins them to: the goal-anchored adaptation the
// plain `lemma` and the bare Cite run on any lemma
// (typematch.TryAdaptLemmaTypes), applied to the derived certificate.
// It types a BARE cite of a reading at a polymorphic instance entry
// (`symmetric_group.SymmetricGroup` is `group⟨A:permutation(A)⟩(…)`,
// its A the reading's own), as ReadingAtWitnessTypes types a witnessed
// one off its tuple. Every letter a hypothesis spells stays rigid, and
// a reading the goal pins no letter of comes back as stated.
func ReadingAtGoalTypes(reading, goal Prop) Prop {
	if !ext.PropHasTypeVars(reading) {
		return reading
	}
	fixed := ReadingFixedLetters(reading)
	loose := func(v core.VarType) bool { return !fixed(v) }
	stated := core.MakeProp(reading.Conclusion())
	adapted := typematch.TryAdaptLemmaTypes(stated, goal)
	if adapted == nil {
		return reading
	}
	subst, ok := prop.IsTypeMatchOf(stated, adapted, loose)
	if !ok {
		return reading
	}
	return core.PropTypeInst(reading, nonIdentityTypeSubst(subst)...)
}

// readLawAt derives `Γ, Δ ⊢ body[comps := c]` from a law `Δ ⊢ ∀comps.
// S(comps) ⇒ body` and an instance `Γ ⊢ S(c)`: the law's type letters
// are matched against the instance's component types, the leading
// binders are specialized at the components in binder order, and the
// antecedent is discharged against the instance by cut — the
// instance's own hypotheses (none at an entry; the fact itself at a
// resident one) are the reading's. The body is handed over in the
// instance normal form (prover/tactic, InstanceNormal), its record
// equations read through read: a law read at a packed record value states
// the value's parts.
func readLawAt(law, instance Prop, read tactic.LibraryRead) (Prop, error) {
	derived, err := readLawDerived(law, instance)
	if err != nil {
		return nil, err
	}
	return prop.WrapProp(derived).RewriteConcl(tactic.InstanceNormal(read)).Core(), nil
}

// readLawDerived is readLawAt's derivation before the instance normal
// form.
func readLawDerived(law, instance Prop) (Prop, error) {
	law = prop.LawTelescopeAt(law, instance.Conclusion())
	binders, atBinder, err := readingComponents(law, instance.Conclusion())
	if err != nil {
		return nil, err
	}

	// The letters the components' types carry, read off the instance.
	var env []core.TypeSubst
	rigid := fixedReadingLetters(law, binders)
	for _, hyp := range law.Hyps() {
		_ = ext.TermAnyTypeVar(hyp, func(v core.VarType) bool { rigid[v.Name()] = true; return false })
	}
	anyLetter := func(v core.VarType) bool { return !rigid[v.Name()] }
	for j, b := range binders {
		if !core.MatchTypeInto(b.Type(), atBinder[j].Type(), anyLetter, &env) {
			return nil, fmt.Errorf("the component %s of type %s does not fit the binder %s:%s",
				ext.PrintTerm(atBinder[j]), ext.FormatType(atBinder[j].Type()), b.Name(), ext.FormatType(b.Type()))
		}
	}
	// The law's loose letters are held apart from the instance's in the
	// same substitution: a letter the components fix is replaced by the
	// instance's type, and the instance's letters inside that type are
	// not renamed in turn.
	w := prop.WrapProp(law).TypeInst(append(looseLettersApart(law, binders, instance), nonIdentityTypeSubst(env)...)...).ConclForAllInsts(atBinder...)
	discharged, _, ok := ext.MatchesIMPLY(w.Conclusion())
	if !ok || !discharged.AlphaEquals(instance.Conclusion()) {
		return nil, fmt.Errorf("at the components the law's hypothesis reads %s, not the instance %s",
			ext.PrintTerm(discharged), ext.PrintTerm(instance.Conclusion()))
	}
	return core.DeriveTrans(instance, w.DemoteHyp()), nil
}

// readLawStatementAt is readLawAt's statement, for a caller that reads
// what a reading says rather than proving it: the body in the instance
// normal form computed from the record equations' statements
// (tactic.InstanceNormalTerm), nothing read.
func readLawStatementAt(law, instance Prop) (Prop, error) {
	derived, err := readLawDerived(law, instance)
	if err != nil {
		return nil, err
	}
	return core.MakeProp(tactic.InstanceNormalTerm(derived.Conclusion()), derived.Hyps()...), nil
}

// fixedReadingLetters keeps already chosen components rigid across later reads.
func fixedReadingLetters(law Prop, binders []core.VarTerm) map[core.TypeName]bool {
	law = prop.LawTelescope(law)
	fixed := map[core.TypeName]bool{}
	_, body := ext.DecomposesFORALL(law.Conclusion())
	antecedent, _, ok := ext.MatchesIMPLY(body)
	if !ok {
		return fixed
	}
	_, args := ext.MatchesApply(antecedent)
	for _, arg := range args {
		bound := false
		for _, b := range binders {
			if b.Equals(arg) {
				bound = true
				break
			}
		}
		if !bound {
			_ = ext.TermAnyTypeVar(arg, func(v core.VarType) bool { fixed[v.Name()] = true; return false })
		}
	}
	return fixed
}

// looseLettersApart is the substitution that holds a law's LOOSE type
// letters — the ones no component binder's type carries, so the
// instance fixes nothing about them — apart from the instance's own
// letters where the two spell one name: module.ModuleSumIn's index
// letter D, read at the chains, a free module on the carrier D → A,
// is the law's D and not the carrier's, and a sum indexed by num
// grounds the one without touching the other. The law's letter takes
// the prefix ♭, the session's mark for a lemma's letter held apart
// from the goal's (a character no identifier can carry), doubled until
// it is free of both statements. A loose letter the instance does not
// spell is left as the law states it.
func looseLettersApart(law Prop, binders []core.VarTerm, instance Prop) []core.TypeSubst {
	fixed := fixedReadingLetters(law, binders)
	for _, b := range binders {
		for _, v := range b.Type().TypeVars() {
			fixed[v.Name()] = true
		}
	}
	// A prior reading's hypotheses fix their letters for every later bundle.
	for _, hyp := range law.Hyps() {
		_ = ext.TermAnyTypeVar(hyp, func(v core.VarType) bool { fixed[v.Name()] = true; return false })
	}
	spelled := map[core.TypeName]bool{}
	note := func(v core.VarType) bool { spelled[v.Name()] = true; return false }
	_ = ext.TermAnyTypeVar(instance.Conclusion(), note)
	for i := range instance.NumHyps() {
		_ = ext.TermAnyTypeVar(instance.Hyp(i), note)
	}
	taken := map[core.TypeName]bool{}
	for name := range spelled {
		taken[name] = true
	}
	_ = ext.TermAnyTypeVar(law.Conclusion(), func(v core.VarType) bool { taken[v.Name()] = true; return false })

	var apart []core.TypeSubst
	renamed := map[core.TypeName]bool{}
	_ = ext.TermAnyTypeVar(law.Conclusion(), func(v core.VarType) bool {
		name := v.Name()
		if fixed[name] || renamed[name] || !spelled[name] {
			return false
		}
		fresh := core.TypeName("♭" + string(name))
		for taken[fresh] {
			fresh = core.TypeName("♭" + string(fresh))
		}
		taken[fresh], renamed[name] = true, true
		apart = append(apart, core.MakeTypeSubst(v, core.MakeVarType(fresh)))
		return false
	})
	return apart
}

// StructureLaw reads the shape a reading reads a law in — `∀comps.
// S(comps) ⇒ body`, a constant applied to exactly the leading binders,
// each once — and returns the hypothesis `S(comps)`, the body and the
// binders in binder order, a law in the standard form read through its
// LawTelescope. ok is false for a sequent and for any other shape: a law
// with a guard or a second antecedent before its body has that
// antecedent in its body, which is where a reading leaves it.
func StructureLaw(law core.Prop) (hypothesis, body core.Term, binders []core.VarTerm, ok bool) {
	law = prop.LawTelescope(law)
	if law.NumHyps() != 0 {
		return nil, nil, nil, false
	}
	t := law.Conclusion()
	for {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			break
		}
		binders = append(binders, abs.Var())
		t = abs.Body()
	}
	hypothesis, body, isImply := ext.MatchesIMPLY(t)
	if !isImply || len(binders) == 0 {
		return nil, nil, nil, false
	}
	head, args := ext.MatchesApply(hypothesis)
	if _, isConst := head.AsConst(); !isConst || len(args) != len(binders) {
		return nil, nil, nil, false
	}
	placed := make([]bool, len(binders))
	for _, arg := range args {
		v, isVar := arg.AsVar()
		if !isVar {
			return nil, nil, nil, false
		}
		found := false
		for j, b := range binders {
			if b.Equals(v) && !placed[j] {
				placed[j], found = true, true
				break
			}
		}
		if !found {
			return nil, nil, nil, false
		}
	}
	return hypothesis, body, binders, true
}

// readingComponents matches a Horn law `∀comps. S(comps) ⇒ body` against
// an instance `S(c)`: the law's leading binders, and for each the
// component of the instance it stands for — the instance's argument at
// the position the binder takes in the law's antecedent. A law in the
// standard form is read through its prop.LawTelescope.
func readingComponents(law Prop, instConcl Term) ([]core.VarTerm, []Term, error) {
	law = prop.LawTelescopeAt(law, instConcl)
	instHead, instArgs := ext.MatchesApply(instConcl)
	instPred, ok := instHead.AsConst()
	if !ok || len(instArgs) == 0 {
		return nil, nil, fmt.Errorf("the instance does not state a predicate at its components: %s",
			ext.PrintTerm(instConcl))
	}

	var binders []core.VarTerm
	body := law.Conclusion()
	for {
		abs := ext.MatchesFORALL(body)
		if abs.IsZero() {
			break
		}
		binders = append(binders, abs.Var())
		body = abs.Body()
	}
	antecedent, _, ok := ext.MatchesIMPLY(body)
	if !ok {
		return nil, nil, fmt.Errorf("the law is not a Horn theorem ∀comps. S(comps) ⇒ body: %s",
			ext.PrintTerm(law.Conclusion()))
	}
	lawHead, lawArgs := ext.MatchesApply(antecedent)
	lawPred, ok := lawHead.AsConst()
	if !ok || lawPred.Meta().Name() != instPred.Meta().Name() || len(lawArgs) != len(instArgs) {
		return nil, nil, fmt.Errorf("the instance states %s, the law's hypothesis is %s",
			ext.PrintTerm(instConcl), ext.PrintTerm(antecedent))
	}
	// The component each leading binder stands for: the instance's
	// argument at the position the binder takes in the antecedent.
	atBinder := make([]Term, len(binders))
	for i, arg := range lawArgs {
		v, isVar := arg.AsVar()
		if !isVar {
			continue
		} // a component fixed by a previous reading
		placed := false
		for j, b := range binders {
			if b.Equals(v) {
				if atBinder[j] != nil {
					return nil, nil, fmt.Errorf("the law's hypothesis names the binder %s twice", v.Name())
				}
				atBinder[j] = instArgs[i]
				placed = true
				break
			}
		}
		// Unbound components belong to an earlier reading. The full
		// specialized antecedent is checked against the instance below.
		_ = placed
	}
	for j, b := range binders {
		if atBinder[j] == nil {
			return nil, nil, fmt.Errorf("the law's leading binder %s is not a component of its hypothesis", b.Name())
		}
	}
	return binders, atBinder, nil
}

// expandLooseReadings replaces, in a By's premise list, each law read
// under a RESIDENT hypothesis whose statement carries a loose type
// letter (see the file header) by the law itself beside that
// instance; a direct resident hypothesis is added unless the list
// already names it, and a nested instance keeps its derived certificate.
// A direct witnessed reading's tuple grounds the law at the components
// the hypothesis applies the structure to, each at the binder the law
// states it at, beside the witnesses (looseCiteTuple), so the law is
// grounded at the same instance; so is an unwitnessed one's when a
// component is a packed record value, whose parts the grounding's
// normal form states (prover/tactic, InstanceNormal) and no goal spells
// back as the law's projections. Every other premise passes through
// unchanged. leaf is the By's, where each hypothesis is read as it
// stands (hypothesis).
func expandLooseReadings(s *Script, leaf *GoalStackNode, facts []Fact, described []string) ([]Fact, []string) {
	listed := func(h *HypHandle) bool {
		for _, f := range facts {
			if h != nil && f.handle == h {
				return true
			}
		}
		return false
	}
	var outFacts []Fact
	var outDescribed []string
	for i, f := range facts {
		r, isReading := f.target.(readingInst)
		// A witnessed nested reading fixes its loose letters from the
		// tuple. Without witnesses, cite the outer law beside the inner
		// reading's structure fact so the law remains polymorphic.
		if !isReading || !r.resident() || (r.inner != nil && len(f.witnesses) > 0) || r.prior != nil || f.claim != nil || len(f.named) > 0 {
			outFacts = append(outFacts, f)
			outDescribed = append(outDescribed, described[i])
			continue
		}
		law := r.lawProp(s)
		var instance Term
		var companion Fact
		if r.inner != nil {
			instance = r.inner.resolve(s, leaf).Conclusion()
			companion = Fact{target: *r.inner}
		} else {
			instance, companion = r.hypothesis(leaf), r.at
		}
		binders, components, err := readingComponents(law, instance)
		if err != nil || !hasLooseLetter(law, binders) {
			// A malformed reading refuses where it is resolved, naming
			// both statements; one without a loose letter is read as is.
			outFacts = append(outFacts, f)
			outDescribed = append(outDescribed, described[i])
			continue
		}
		if r.inner != nil && r.inner.prior == nil {
			if err := CheckLooseReadingCompanion(r.inner.lawProp(s), r.inner.instanceProp(s, leaf).Conclusion()); err != nil {
				panic(err.Error())
			}
		}
		cited := Fact{target: r.lawCiteTarget()}
		if len(f.witnesses) > 0 || slices.ContainsFunc(components, tactic.IsRecordValue) {
			tuple, err := looseCiteTuple(law, binders, components, f.witnesses)
			if err != nil {
				panic(fmt.Sprintf("By: %s is cited as its law beside the hypothesis it is read under: %v", described[i], err))
			}
			cited.witnesses = tuple
		}
		outFacts = append(outFacts, cited)
		outDescribed = append(outDescribed, cited.describe())
		if r.inner != nil || !listed(r.at.handle) {
			outFacts = append(outFacts, companion)
			outDescribed = append(outDescribed, companion.describe())
		}
	}
	return outFacts, outDescribed
}

// ReadingIsLoose reads a law against the resident hypothesis it would
// be read under and reports whether the law carries a LOOSE type letter
// — one no component's type fixes. A By reads a loose reading as the
// law cited beside the hypothesis, a witnessed one's tuple grounding
// the law at the hypothesis's components and the witnesses together
// (expandLooseReadings, LooseCiteTuple); a session expands its premise
// the same way.
func ReadingIsLoose(law Prop, hypothesis Term) (bool, error) {
	binders, _, err := readingComponents(law, hypothesis)
	if err != nil {
		return false, err
	}
	return hasLooseLetter(law, binders), nil
}

// looseCiteSlots reads the binders a tuple on law grounds — its spine,
// in the order the statement gives them (ematch.StripGuardedForalls) —
// against a reading of it: fixed[i] is the component the hypothesis
// fixes spine[i] at, nil at a binder the reading keeps. binders and
// components are readingComponents'. The reading's own binders are the
// spine's without the fixed ones, in the same order, so a tuple on the
// reading fills the nil slots in turn.
func looseCiteSlots(law Prop, binders []core.VarTerm, components []Term) (spine []core.VarTerm, fixed []Term) {
	spine, _ = ematch.StripGuardedForalls(law.Conclusion())
	fixed = make([]Term, len(spine))
	placed := make([]bool, len(binders))
	for i, b := range spine {
		for j, c := range binders {
			if !placed[j] && c.Equals(b) {
				fixed[i], placed[j] = components[j], true
				break
			}
		}
	}
	for j, c := range binders {
		if !placed[j] {
			panic(fmt.Sprintf("a reading fixes the binder %s, which the law does not bind on its spine: %s",
				ext.PrintTerm(c), prop.PrintProp(law)))
		}
	}
	return spine, fixed
}

// ReadingLawBinders are the binders of law that a reading of it at
// instance keeps: the law's spine without the binders the instance
// fixes, in the order the law states them. The reading's own binders
// are these, one for one, under the names the kernel holds them by.
func ReadingLawBinders(law Prop, instance Term) ([]core.VarTerm, error) {
	binders, components, err := readingComponents(law, instance)
	if err != nil {
		return nil, err
	}
	spine, fixed := looseCiteSlots(law, binders, components)
	var kept []core.VarTerm
	for i, b := range spine {
		if fixed[i] == nil {
			kept = append(kept, b)
		}
	}
	return kept, nil
}

// looseCiteTuple is the tuple a loose reading's law is grounded at,
// beside the hypothesis the reading is under: the law's binders in the
// order its statement gives them, each one the hypothesis fixes at its
// component and the others at the reading's witnesses in turn, through
// the last binder either names. A tuple grounds a prefix of the law's
// binders, so every component must lie inside it: a binder the tuple
// does not reach, stated before a component, is refused by name. A
// witness past the law's last binder follows in order, for the
// grounding to judge.
func looseCiteTuple(law Prop, binders []core.VarTerm, components, witnesses []Term) ([]Term, error) {
	spine, fixed := looseCiteSlots(law, binders, components)
	var tuple []Term
	next := 0
	for i := range spine {
		switch {
		case fixed[i] != nil:
			tuple = append(tuple, fixed[i])
		case next < len(witnesses):
			tuple = append(tuple, witnesses[next])
			next++
		default:
			lastFixed := -1
			for j := i + 1; j < len(spine); j++ {
				if fixed[j] != nil {
					lastFixed = j
				}
			}
			if lastFixed < 0 {
				return tuple, nil
			}
			through := i
			for j := i + 1; j < lastFixed; j++ {
				if fixed[j] == nil {
					through = j
				}
			}
			var all, held []string
			for j, b := range spine {
				all = append(all, ext.PrintTerm(b))
				if fixed[j] != nil {
					held = append(held, ext.PrintTerm(b))
				}
			}
			return nil, fmt.Errorf("the law binds %s and the hypothesis fixes %s; a tuple grounds a prefix of the law's binders, "+
				"and this one stops at %s, stated before %s — give the reading's binders through %s",
				strings.Join(all, ", "), strings.Join(held, ", "),
				ext.PrintTerm(spine[i]), ext.PrintTerm(spine[lastFixed]), ext.PrintTerm(spine[through]))
		}
	}
	return append(tuple, witnesses[next:]...), nil
}

// LooseCiteTuple is the tuple a loose reading's law is grounded at
// beside the hypothesis it is read under, from the witnesses given on
// the reading's own binders (looseCiteTuple): what a session's premise
// carries where the Go macro expands `law.Read(fact).At(w…)`.
func LooseCiteTuple(law Prop, hypothesis Term, witnesses []Term) ([]Term, error) {
	binders, components, err := readingComponents(law, hypothesis)
	if err != nil {
		return nil, err
	}
	return looseCiteTuple(law, binders, components, witnesses)
}

// LooseCiteWitnesses reads a loose cite's tuple back: the positions in
// tuple of the witnesses given on the reading's binders, the others
// being the components the hypothesis fixes, each checked at its own
// binder. A tuple that does not hold every component where the law
// binds it is no record of the expansion LooseCiteTuple makes.
func LooseCiteWitnesses(law Prop, hypothesis Term, tuple []Term) ([]int, error) {
	binders, components, err := readingComponents(law, hypothesis)
	if err != nil {
		return nil, err
	}
	spine, fixed := looseCiteSlots(law, binders, components)
	var given []int
	for i, t := range tuple {
		if i >= len(spine) || fixed[i] == nil {
			given = append(given, i)
			continue
		}
		if !t.AlphaEquals(fixed[i]) {
			return nil, fmt.Errorf("position %d holds %s where the hypothesis fixes %s at %s",
				i, ext.PrintTerm(t), ext.PrintTerm(spine[i]), ext.PrintTerm(fixed[i]))
		}
	}
	for i := len(tuple); i < len(spine); i++ {
		if fixed[i] != nil {
			return nil, fmt.Errorf("the tuple holds %d terms and does not reach %s, which the hypothesis fixes at %s",
				len(tuple), ext.PrintTerm(spine[i]), ext.PrintTerm(fixed[i]))
		}
	}
	return given, nil
}

// CheckLooseReadingCompanion checks an intermediate reading before a
// bare outer loose law is detached from it. The intermediate structure
// must keep the same types when emitted as a standalone By premise;
// another loose expansion would change that fixed instance on replay.
func CheckLooseReadingCompanion(law Prop, instance Term) error {
	loose, err := ReadingIsLoose(law, instance)
	if err != nil {
		return err
	}
	if loose {
		return fmt.Errorf("By: a bare nested loose reading has an intermediate structure with unfixed type letters; materialize that structure as a resident fact before reading the outer law")
	}
	return nil
}

// hasLooseLetter reports whether the law's statement carries a type
// letter that no component binder's type carries — one the instance
// cannot fix.
func hasLooseLetter(law Prop, binders []core.VarTerm) bool {
	law = prop.LawTelescope(law)
	fixed := map[core.TypeName]bool{}
	for _, b := range binders {
		for _, v := range b.Type().TypeVars() {
			fixed[v.Name()] = true
		}
	}
	return ext.TermAnyTypeVar(law.Conclusion(), func(v core.VarType) bool { return !fixed[v.Name()] })
}

// withReadingsFirst moves the premises that are laws read under a
// resident hypothesis (byPremise.readingUnder) ahead of every other
// premise, stably. Such a reading is a fact of the context, and the
// Have it replaces was resident before the By began; an install's own
// strategies read the context — an equation resident earlier changes
// what a later install absorbs — so the reading's position in the
// author's list must not decide the leaf.
func withReadingsFirst(premises []byPremise) []byPremise {
	var first, rest []byPremise
	for _, pr := range premises {
		if pr.readingUnder {
			first = append(first, pr)
		} else {
			rest = append(rest, pr)
		}
	}
	if len(first) == 0 {
		return premises
	}
	return append(first, rest...)
}
