// emit_by.go — rendering the `by` composite ministep (StepProto_By)
// back as the math layer's By(...) / ByArith(...) / BySets(...)
// expression.
//
// The payload IS the call (premise list + shaping + closer choice), so
// rendering is a straight read-out — no shape recognition, no fusion
// heuristics, nothing to verify: the emitted expression re-runs the
// same shared executor (_ByStep.apply) that produced the record, which
// is the whole point of the composite tag (record/emit/replay code
// reuse; see prover/proof/step_by.go).
//
// The node's children are the premise CLAIM obligations, closed at
// record time by auto-match / certs. They are implied by the premise
// list — the replayed By(...) regenerates and certifies them itself —
// so the renderers skip them entirely.

package emit

import (
	"fmt"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/ematch"
)

// renderByExpr renders one recorded ByProto as the By/ByArith call
// expression.
//
// Premise spellings:
// - named → `At("NAME", w…)` / the bare cite-target expr
// (byNamedPremiseExpr — the same tiers as the Cite verb rendering);
// - resident → the Go name of the Have that states the hypothesis,
// where a Derive block bound one (`fact1`, haveHandleIdents), else
// `ResidentHyp(<stmt>)`; either is wrapped in At for a grounded
// resident premise (witnesses in the recorded stated order — emit
// prints them in that order, the executor reorders);
// - a reading → `law.Read(instance)` (readingExpr), under At when
// grounded. The hypothesis a reading is under is kept beside it by
// the By itself, so the resident premise the record carries for it
// is not printed a second time (byPremisesPrinted);
// - derived, with no reading → unreachable from session records
// (kit premises are hand-written); rendered as a marked TODO so a
// surprise is loud in review rather than silent at replay.
//
// A witness is a Go local where it is a variable and the text a chapter
// writes where that text reads back (witnessExpr).
func (e *_Emitter) renderByExpr(by *proof.ByProto) string {
	var args []string
	if sh := by.GetShape(); sh != nil {
		args = append(args, e.byShapeArgs(sh)...)
	}
	if by.GetBroadcast() {
		args = append(args, "Broadcast")
	}
	for _, p := range e.byPremisesPrinted(by) {
		args = append(args, e.byPremiseExpr(p))
	}
	name := "By"
	switch {
	case by.GetArith():
		name = "ByArith"
	case by.GetSettac():
		name = "BySets"
	case by.GetChase():
		// The depth is the closer's parameter, written first.
		name = "ByChase"
		args = append([]string{fmt.Sprintf("Depth(%d)", by.GetChaseDepth())}, args...)
	}
	return fmt.Sprintf("%s(%s)", name, strings.Join(args, ", "))
}

// byPremisesPrinted are the premises of a recorded `by` that its
// rendering prints, in list order: the authored premises
// (authoredByPremises) but the companions of a loose cite — the bare
// resident premise for the hypothesis it is read under, the derived
// reading it is read at — which the Go macro of the printed
// `Law.Read(fact)` adds itself (proof.expandLooseReadings).
func (e *_Emitter) byPremisesPrinted(by *proof.ByProto) []*proof.ByPremiseProto {
	under := map[core.TermKey]bool{}
	var inner []*proof.ReadingProto
	for _, p := range by.GetPremises() {
		if !readingCitedLoose(e.reader, p) {
			continue
		}
		if hypothesis := recordedReadingHypothesis(e.reader, p.GetReading()); hypothesis != nil {
			under[hypothesis.Conclusion().AlphaKey()] = true
		}
		if p.GetReading().GetInner().GetLaw() != nil {
			inner = append(inner, p.GetReading().GetInner())
		}
	}
	var printed []*proof.ByPremiseProto
	for _, p := range authoredByPremises(e.reader, by) {
		if namesResidentHypothesis(p) && len(p.GetWitnesses()) == 0 && !p.GetScaled() {
			if install, _ := e.reader.Prop(p.GetInstall()); install != nil && under[install.Conclusion().AlphaKey()] {
				continue
			}
		}
		if p.GetDerived() && slices.ContainsFunc(inner, func(r *proof.ReadingProto) bool { return readingProtoEquals(e.reader, p.GetReading(), r) }) {
			continue
		}
		printed = append(printed, p)
	}
	return printed
}

// authoredByPremises omits a reading's automatically kept hypothesis.
// Both rendering and CNF collection reconstruct the authored call from
// this list; ApplyByStep restores the kept premise with its audit flag.
// A loose cite's hypothesis stays: the executor keeps nothing beside a
// law cited as itself, so the record's own resident premise for it is
// the one the call has.
func authoredByPremises(reader *ext.PoolReader, by *proof.ByProto) []*proof.ByPremiseProto {
	readUnder := map[core.TermKey]bool{}
	for _, p := range by.GetPremises() {
		if readingCitedLoose(reader, p) {
			continue
		}
		if under := recordedReadingHypothesis(reader, p.GetReading()); under != nil {
			readUnder[under.Conclusion().AlphaKey()] = true
		}
	}
	printed := make([]*proof.ByPremiseProto, 0, len(by.GetPremises()))
	for _, p := range by.GetPremises() {
		if p.GetResident() && len(p.GetWitnesses()) == 0 && !p.GetScaled() {
			if install, _ := reader.Prop(p.GetInstall()); install != nil && readUnder[install.Conclusion().AlphaKey()] {
				continue
			}
		}
		printed = append(printed, p)
	}
	return printed
}

// readingCitedLoose reports whether p cites a law read under a resident
// hypothesis as the law itself beside that hypothesis — the expansion
// the session's `by` and the Go macro make of a reading whose law
// carries a type letter its instance does not fix
// (proof.ReadingIsLoose): the install is the law's own
// statement, and the reading says what it was read at.
func readingCitedLoose(reader *ext.PoolReader, p *proof.ByPremiseProto) bool {
	r := p.GetReading()
	if r.GetLaw() == nil || recordedReadingHypothesis(reader, r) == nil {
		return false
	}
	law, _ := reader.Prop(r.GetLaw())
	install, _ := reader.Prop(p.GetInstall())
	return law != nil && install != nil && install.AlphaEquals(law)
}

// readingProtoEquals reports whether two recorded readings read one law
// at one instance: the same law, and the same entry, hypothesis or
// inner reading, up to α.
func readingProtoEquals(reader *ext.PoolReader, a, b *proof.ReadingProto) bool {
	if a.GetLaw() == nil || b.GetLaw() == nil {
		return false
	}
	lawA, _ := reader.Prop(a.GetLaw())
	lawB, _ := reader.Prop(b.GetLaw())
	if lawA == nil || lawB == nil || !lawA.AlphaEquals(lawB) {
		return false
	}
	switch {
	case a.GetInner().GetLaw() != nil || b.GetInner().GetLaw() != nil:
		return readingProtoEquals(reader, a.GetInner(), b.GetInner())
	case a.GetUnder() != nil || b.GetUnder() != nil:
		underA, _ := reader.Prop(a.GetUnder())
		underB, _ := reader.Prop(b.GetUnder())
		return underA != nil && underB != nil && underA.AlphaEquals(underB)
	}
	instanceA, _ := reader.Prop(a.GetInstance())
	instanceB, _ := reader.Prop(b.GetInstance())
	return instanceA != nil && instanceB != nil && instanceA.AlphaEquals(instanceB)
}

// namesResidentHypothesis reports whether p names a resident hypothesis
// by that hypothesis's own statement — no reading, no kit certificate:
// the premise byPremiseExpr renders as a Have's handle or as
// `ResidentHyp(<stmt>)`.
func namesResidentHypothesis(p *proof.ByPremiseProto) bool {
	return p.GetResident() && !p.GetDerived() && p.GetReading().GetLaw() == nil
}

// residentPremiseOf reports whether p names the resident hypothesis
// content states: its statement is that content, up to bound names.
func (e *_Emitter) residentPremiseOf(p *proof.ByPremiseProto, content core.Term) bool {
	if !namesResidentHypothesis(p) {
		return false
	}
	install, _ := e.reader.Prop(p.GetInstall())
	return install != nil && install.Conclusion().AlphaEquals(content)
}

// readingUnderPremiseOf reports whether p reads a law under the resident
// hypothesis content states — the fact its `Law.Read(fact)` names.
func (e *_Emitter) readingUnderPremiseOf(p *proof.ByPremiseProto, content core.Term) bool {
	under := e.readingHypothesis(p.GetReading())
	return under != nil && under.Conclusion().AlphaEquals(content)
}

func (e *_Emitter) byShapeArgs(sh *proof.ByShapeProto) []string {
	var args []string
	if sh.GetRaw() {
		args = append(args, "Raw")
	}
	if sh.GetPre() {
		args = append(args, "PreNormalized")
	}
	if n := sh.GetDenoteSize(); n > 0 {
		// The SEARCH form — off the bare-name surface by design; a
		// landing converts it to DenotedAs (naming the term), exactly as
		// with a recorded Denote(size) step.
		args = append(args, fmt.Sprintf("Denoted(%d)", n))
	}
	if t := sh.GetDenoteTerm(); t != 0 {
		term := e.reader.Term(t)
		ctor := "DenotedAs"
		if sh.GetDenoteHilbert() {
			ctor = "HilbertDenotedAs"
		}
		args = append(args, fmt.Sprintf("%s(%q, %s)", ctor, sh.GetDenoteName(), e.witnessExpr(term)))
	}
	if sh.GetHilbert() {
		args = append(args, "HilbertDenoted")
	}
	if len(args) == 0 {
		// A present-but-empty shape is the macro's Normalized value
		// (ByShape zero struct): Basic() between the installs and the
		// close.
		args = append(args, "Normalized")
	}
	return args
}

// byPremiseInstallPrinted reports whether byPremiseExpr will spell the
// premise's recorded install statement in the output — the predicate
// the symbol walk (walkMiniStep's By arm) and the Go-used marking pass
// read before registering that statement's consts and free vars, so a
// statement the rendering never prints declares nothing.
//
// A derived premise always prints it (`ResidentHyp(<stmt>)`), and so
// does a resident one unless a Have's handle stands for it — which is
// decided as its Derive block renders, after both passes. So the walk
// registers a resident statement's vocabulary either way (the Have's
// claim is the same statement and registers the same), and its Go-used
// marks are made where it is printed (byPremiseExpr), not by the pass.
// A reading prints the entries it was read from, and the hypothesis it
// is under when it is under one (readingHypothesis), never its install.
// A named premise prints nothing of it when a reference resolves the
// install (an earlier section's node, a classified dep); an unresolved
// one renders the placeholder, which prints nothing either — but it is
// counted as printed, conservatively, so a declaration is never missing
// from a file that already fails to compile for another reason.
func (e *_Emitter) byPremiseInstallPrinted(p *proof.ByPremiseProto, install core.Prop) bool {
	if p.GetReading().GetLaw() != nil {
		return false
	}
	if p.GetResident() || p.GetDerived() {
		return true
	}
	if _, ok := e.resolveLemmaRef(install); ok {
		return false
	}
	if _, _, ok := e.bySectionInstanceExpr(install); ok {
		return false
	}
	if _, ok := e.resolveExternalLeafProp(install); ok {
		return false
	}
	return true
}

func (e *_Emitter) byPremiseExpr(p *proof.ByPremiseProto) string {
	install, _ := e.reader.Prop(p.GetInstall())
	var base string
	var stated core.Prop
	witnesses := p.GetWitnesses()
	switch {
	case p.GetReading().GetLaw() != nil:
		base = e.readingExpr(p.GetReading(), e.hypHandleByUse[_HypUse{premise: p}])
		if readingCitedLoose(e.reader, p) {
			witnesses = e.looseCiteWitnesses(p)
		}
	case p.GetDerived():
		base = fmt.Sprintf("/* TODO: kit self-proving premise — restore the kit value (ac.New(…).Eq(…)) */ ResidentHyp(%s)",
			e.miniStepPropExpr(install))
	case p.GetResident():
		if handle, named := e.hypHandleByUse[_HypUse{premise: p}]; named {
			base = handle
			break
		}
		if handle := e.lawHandleFor(install); handle != "" {
			base = handle
			break
		}
		// The statement is printed inline, its identifiers marked used
		// where it prints: a resident premise a Have's handle stands for
		// prints none of them.
		base = e.residentHypExpr(install)
	default:
		base, stated = e.byNamedPremiseExpr(install, p.GetExact())
	}
	if named := p.GetNamed(); len(named) > 0 {
		// A premise pinned by name renders as the Where chain — one
		// binder per link, in recorded order — the apply rung's seeded
		// head (fact.go Where).
		// Alpha-renamed text pins the same slots in the section's
		// declaration; the emitted target reads those declared names.
		binders := map[string]string{}
		if stated != nil {
			reference := install
			if p.GetReference() != nil {
				reference, _ = e.reader.Prop(p.GetReference())
			}
			if !reference.AlphaEquals(stated) {
				panic("local section instance: named reference differs from its stated telescope")
			}
			from, _ := ematch.StripGuardedForalls(reference.Conclusion())
			to, _ := ematch.StripGuardedForalls(stated.Conclusion())
			for i, binder := range from {
				binders[string(binder.Name())] = string(to[i].Name())
			}
		}
		expr := base
		for i, nw := range named {
			binder := nw.GetBinder()
			if declared, ok := binders[binder]; ok {
				binder = declared
			}
			if i == 0 {
				expr = fmt.Sprintf("Where(%s, %q, %s)", base, binder, e.printer.PrintTerm(e.reader.Term(nw.GetTerm())))
				continue
			}
			expr = fmt.Sprintf("%s.Where(%q, %s)", expr, binder, e.printer.PrintTerm(e.reader.Term(nw.GetTerm())))
		}
		return expr
	}
	expr := base
	if len(witnesses) > 0 {
		wits := make([]string, 0, len(witnesses)+1)
		wits = append(wits, base)
		for _, w := range witnesses {
			wits = append(wits, e.witnessExpr(e.reader.Term(w)))
		}
		expr = fmt.Sprintf("At(%s)", strings.Join(wits, ", "))
	}
	if p.GetScaled() {
		// A scaled premise renders as the Scaled wrapper around the
		// fact (fact.go Scaled): the coefficient first, as written.
		expr = fmt.Sprintf("Scaled(%s, %s)", e.goTermExpr(e.reader.Term(p.GetCoefficient())), expr)
	}
	return expr
}

// byNamedPremiseExpr renders a named premise's cite-target expression:
// an earlier section's node, or the dep the leaf resolver classifies
// (`ctx.Dep(name)`, the entry at its instance, the registered name —
// renderExternalLeaf's lemma-applied spellings, which already carry a
// type instance's σ as `ctx.AtTypes(…)`). An unresolved install renders
// the TODO placeholder, which does not compile.
func (e *_Emitter) byNamedPremiseExpr(install core.Prop, exact bool) (string, core.Prop) {
	if exact {
		if expr, stated, ok := e.byIdentityInstanceExpr(install); ok {
			return expr, stated
		}
	}
	if base, ok := e.tryLemmaRefExprCtx(install, leafCite, false); ok {
		return base, nil
	}
	if instance, stated, ok := e.bySectionInstanceExpr(install); ok {
		return instance, stated
	}
	return e.externalLeafExprCtx(install, leafCite), nil
}

// byIdentityInstanceExpr preserves an explicit identity type binding.
// The statement alone cannot distinguish it from a bare cite: the typed
// instance keeps the recorded exact flag and disables speculative type
// adaptation. It is spelled as a proper instance is — an earlier
// section by its letters (sectionInstExpr), a landed entry by its typed
// wrapper's Inst (wrapperInstAt), `ctx.AtTypes(ctx.Dep(X), τ…)` where
// the entry has no wrapper to call. Proper instances continue through
// the ordinary instance renderers.
func (e *_Emitter) byIdentityInstanceExpr(install core.Prop) (string, core.Prop, bool) {
	for _, section := range e.citableSections() {
		if section.goal.AlphaEquals(install) {
			if identity, ok := identityInstance(section.goal, install); ok {
				return e.sectionInstExpr(e.citeSection(section), identity), section.goal, true
			}
		}
	}
	if leaf, ok := e.resolveExternalLeafProp(install); ok && leaf.Kind == LeafLibraryThm && leaf.Stated != nil {
		if identity, ok := identityInstance(leaf.Stated, install); ok {
			if expr, ok := e.wrapperInstAt(leaf.ThmName, leaf.Key, identity); ok {
				return expr, nil, true
			}
			e.markDepName(leaf.ThmName, leaf.Key)
			var args strings.Builder
			for _, s := range identity {
				fmt.Fprintf(&args, ", %s", e.printer.PrintType(s.HolType))
			}
			return fmt.Sprintf("ctx.AtTypes(ctx.Dep(%s)%s)", e.depNameExpr(leaf.ThmName, leaf.Key), args.String()), nil, true
		}
	}
	return "", nil, false
}

// identityInstance reads the unchanged type instance of source that
// install records: each type variable at itself, in AtTypes order. A
// monomorphic source has no type adaptation to disable and takes no
// instance. A changed instance belongs to atTypesInstance.
func identityInstance(source, install core.Prop) ([]core.TypeSubst, bool) {
	norm, _ := proof.Normalize(source)
	if !source.AlphaEquals(install) && !norm.AlphaEquals(install) {
		return nil, false
	}
	vars := proof.OrderedPropTypeVars(norm)
	if len(vars) == 0 {
		return nil, false
	}
	identity := make([]core.TypeSubst, len(vars))
	for i, v := range vars {
		identity[i] = core.MakeTypeSubst(v, v)
	}
	return identity, true
}

// bySectionInstanceExpr resolves a proper type instance of a local
// section the reading section may cite (citableSections). The target
// stays a node, so the instance reads its stated binders.
func (e *_Emitter) bySectionInstanceExpr(install core.Prop) (string, core.Prop, bool) {
	for _, section := range e.citableSections() {
		_, substitution, ok := atTypesInstance(section.goal, install)
		if !ok || !core.PropTypeInst(section.goal, substitution...).AlphaEquals(install) {
			continue
		}
		return e.sectionInstExpr(e.citeSection(section), substitution), core.PropTypeInst(section.goal, substitution...), true
	}
	return "", nil, false
}

// readingExpr spells a recorded reading as the Go value it is,
// `Law.Read(instance)` (prover/proof/reading.go): the law by its entry
// variable, the instance by an entry variable, by the Go name of the
// hypothesis the reading is under — handle, the Have's that states it,
// else the Law door's — or by `ResidentHyp(<statement>)` for that
// hypothesis, or by the reading it is read at. A hypothesis printed
// inline has its identifiers marked used here, as a resident premise's
// are.
func (e *_Emitter) readingExpr(r *proof.ReadingProto, handle string) string {
	law, _ := e.reader.Prop(r.GetLaw())
	var instance string
	switch {
	case r.GetInner().GetLaw() != nil:
		instance = e.readingExpr(r.GetInner(), handle)
	case r.GetUnder() != nil:
		under, _ := e.reader.Prop(r.GetUnder())
		if handle == "" {
			handle = e.lawHandleFor(under)
		}
		if handle != "" {
			instance = handle
			break
		}
		instance = e.residentHypExpr(under)
	default:
		entry, _ := e.reader.Prop(r.GetInstance())
		instance = e.readingEntryExpr(entry)
	}
	if section := e.priorSectionStating(law); section != "" {
		// A law that is an earlier section of the member is read by the
		// free function: a section has no typed wrapper.
		return fmt.Sprintf("Read(%s, %s)", section, instance)
	}
	return fmt.Sprintf("%s.Read(%s)", e.readingEntryExpr(law), instance)
}

// priorSectionStating is the variable of the section the reading
// section may cite (citableSections) whose statement is stated, up to
// α; "" when none is.
func (e *_Emitter) priorSectionStating(stated core.Prop) string {
	for _, section := range e.citableSections() {
		if section.goal.AlphaEquals(stated) {
			return e.citeSection(section)
		}
	}
	return ""
}

// looseCiteWitnesses are the witnesses a loose cite's `At(Law.Read(fact),
// w…)` spells: the recorded tuple is the law's, the components of the
// hypothesis placed at the binders the law states them at among what
// the author gave (by_tactic.go, proof.LooseCiteTuple), and the Go macro
// places them again, so the rendering takes them out. A tuple that does
// not hold the components there is no record of that expansion.
func (e *_Emitter) looseCiteWitnesses(p *proof.ByPremiseProto) []uint32 {
	recorded := p.GetWitnesses()
	if len(recorded) == 0 {
		return nil
	}
	law, _ := e.reader.Prop(p.GetReading().GetLaw())
	under := e.readingHypothesis(p.GetReading())
	tuple := make([]core.Term, len(recorded))
	for i, ref := range recorded {
		tuple[i] = e.reader.Term(ref)
	}
	given, err := proof.LooseCiteWitnesses(law, under.Conclusion(), tuple)
	if err != nil {
		panic(fmt.Sprintf("emit: a loose cite's tuple does not ground its law at the hypothesis's components: %v", err))
	}
	witnesses := make([]uint32, len(given))
	for i, at := range given {
		witnesses[i] = recorded[at]
	}
	return witnesses
}

// readingEntryExpr is the entry variable a reading names its law, or
// its instance entry, by. The variable is the only spelling there is:
// `Read` is a method of the law's typed wrapper, and it takes the
// instance entry as a value. A statement no landed entry's variable
// serves renders a TODO placeholder that does not compile.
func (e *_Emitter) readingEntryExpr(stated core.Prop) string {
	leaf, ok := e.resolveExternalLeafProp(stated)
	if !ok || leaf.Kind != LeafLibraryThm {
		return fmt.Sprintf("/* TODO: unresolved entry %q — a reading is read from landed entries */ ThmCert{}",
			stated.AlphaKey())
	}
	e.markDepName(leaf.ThmName, leaf.Key)
	if id, ok := e.depIdent(leaf.ThmName, leaf.Key); ok {
		return id
	}
	return fmt.Sprintf("/* TODO: %s has no entry variable in reach — a reading is read from the entry's typed wrapper */ ThmCert{}",
		leaf.ThmName)
}

// readingHypothesis is the resident hypothesis a recorded reading is
// taken under — its own, or the reading's it is read at — as a hyp-free
// prop; nil for no reading and for a reading at an entry.
func (e *_Emitter) readingHypothesis(r *proof.ReadingProto) core.Prop {
	return recordedReadingHypothesis(e.reader, r)
}

func recordedReadingHypothesis(reader *ext.PoolReader, r *proof.ReadingProto) core.Prop {
	switch {
	case r.GetLaw() == nil:
		return nil
	case r.GetInner().GetLaw() != nil:
		return recordedReadingHypothesis(reader, r.GetInner())
	case r.GetUnder() != nil:
		under, _ := reader.Prop(r.GetUnder())
		return under
	}
	return nil
}

// simpRuleReading is what rule i of a recorded simp_with was read from,
// nil for a rule that is no reading.
func simpRuleReading(sw *proof.SimpWithProto, i int) *proof.ReadingProto {
	if readings := sw.GetRuleReading(); i < len(readings) && readings[i].GetLaw() != nil {
		return readings[i]
	}
	return nil
}
