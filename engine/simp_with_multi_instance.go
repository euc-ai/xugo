// The simp rule set: resolution of a `simp_with` call's entries and of
// the bare `simp`'s installed set into the ordered rule list the driver
// runs, and the adaptation of its polymorphic rules to the goal.
//
// Three things the set does beyond listing the rules as given.
//
// The session's INSTALLED simp set — the bound family's and its
// imports' definitions and the session's own defines — is the bare
// `simp`'s rule set and rides behind the named rules of `simp_all`
// (addInstalled). A `simp_with` call's set is its entries alone, as the
// Go Simp(Fwd(…), Rev(…)) it renders to fires only the rules it names:
// a chapter definition the step needs is listed beside the cited law,
// or fired by a bare `simp` after it. The emit prunes a step to the
// rules that fired.
//
// A polymorphic rule WITHOUT an explicit per-entry σ (type_specialize /
// term_specialize) expands to one resolved rule copy per DISTINCT
// full-lemma instantiation the goal exhibits, the rule at its own
// letters kept beside them (the enumeration drops that instance as the
// identity; a goal carrying the constant at the rule's own instance
// beside another has a redex only the unadapted rule matches)
// (typematch.EnumerateLemmaTypeAdaptations — same informative-anchor
// gating as the single-instance adapter, dedup by instantiated-lemma
// AlphaKey), the finite anchor-pin set complete. On goals
// where the same const occurs at several type instances
// (`list_length⟨?A⟩(l1)` and `list_length⟨?B⟩(l2)` in one goal — the
// zip / two-list-map class) every instance fires in one call.
//
// The instances are read off the goal AND off what the rewrite exposes
// (expandToFixpoint): a rule whose constant does not occur in the goal
// until an earlier rule's unfold puts it there (fst under
// letter_inverse, list_append under list_reverse) adapts to nothing at
// resolution, so the set is run, every adaptable rule is re-adapted
// against the residual, and the loop repeats while a round adds a
// copy, bounded by proof.MaxSimpAdaptRounds.
//
// All of this is engine-DISPATCH: SimpWithProto.rules is a repeated
// list of RESOLVED props recorded verbatim, the driver prunes to USED
// rules with per-rule children, and replay re-runs the recorded
// resolved rules on the recorded goal — the driver is a pure function
// of (goal, rules), so the one recorded run over the final set
// reproduces what the adaptation rounds discovered. No proto change,
// no replay change, no CNF cache impact (simp_with participates in no
// CNF cache). Each adapted copy's rule child closes through the
// type-instance channel (applyAutoMatchTypeInstanceOnRoots) against the
// polymorphic source — the entry, or an installed definition's own
// certificate — so deps dedup to one entry (closeSimpRuleChildren).
//
// Entries WITH an explicit σ keep exact single-instance semantics (the
// Exact-bypass contract of lemma_type_specialize_override_test.go): an
// explicit type_specialize is honored verbatim and never re-adapted or
// multi-expanded.
//
// Multi-instance expansion, newly exposed instances and cross-entry
// deduplication produce DiagAutoTypeInstances diagnostics on StepResult.
// A copy added at the round bound that rewrites the residual further is
// an error naming it (expandToFixpoint), the diagnostics surfaced beside
// it. Rule children closed on the clone are reported through
// StepResult.AutoMatched.

package engine

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/prover/typematch"
	"github.com/euc-ai/xugo/utils"
)

// simpRuleSrc carries a resolved rule's polymorphic source for the
// post-step close pass: a type-ADAPTED (or explicitly specialized) rule
// child has a unique alpha-key the generic runAutoMatch can't close, and
// must be recorded as a _TypeInstStep against the POLYMORPHIC entry (see
// the Bug-A rationale in type_specialize_recording_test.go). key names
// the registry entry the agent cited ("" for a session define and for a
// rule given by text); prop is the polymorphic statement; cert, when
// non-nil, is the source's own certificate — a session define's section
// promise or an import's replay promise — the bare `simp`'s installed
// rules carry one, an agent's cited entry does not (its close goes
// through the corpus-backed injection by key). A rule given by text has
// neither, so it is no source: its child — the rule as stated, or an
// adapted or specialized instance of it — closes only on a proved
// section of the session or an entry that states it, and a step that
// leaves it open is refused (openTextRule). The injection by key would
// close that child on a promise no entry backs, and a false rule would
// then complete the section.
type simpRuleSrc struct {
	key  core.PropKey
	prop core.Prop
	cert core.Prop
	// reading says what the rule was read from when it is a structure
	// law read at an instance (reading.go); its cert is then the derived
	// theorem. Recorded beside the rule, for emit.
	reading *proof.ReadingRecord
	// resident marks a resident hypothesis assumed (hyp_index): its
	// child closes on the hypothesis, before any entry is consulted.
	resident bool
	// text marks a rule given by text.
	text bool
}

// simpTextRule is a rule of the set given by text, as the driver runs
// it: the entry's own statement, or a copy adapted to the goal. entry
// is its index in the request.
type simpTextRule struct {
	entry int
	rule  core.Prop
}

// simpAdaptable is a polymorphic rule the set may adapt to the goal's
// type instances: every rule without an explicit per-entry σ. label
// names it in diagnostics.
type simpAdaptable struct {
	entryIdx int
	label    string
	src      simpRuleSrc
	poly     core.Prop
	flip     bool
}

// simpRuleSet is the ordered rule set handed to the driver, built up by
// resolveSimpWithRules (the agent's entries), addInstalled (the
// session's simp set) and the adaptation passes. Dedup is by the
// resolved rule's AlphaKey: an ordered rewrite set gains nothing from
// an identical duplicate, and the duplicate's rule child would just be
// a second α-equal leaf to close; the first copy's flip decision wins.
type simpRuleSet struct {
	rules []core.Prop
	flips []bool
	// readings is parallel to rules: what rule i was read from, nil for
	// a rule that is no reading.
	readings []*proof.ReadingRecord
	srcs     []simpRuleSrc
	// texts are the rules given by text, each copy the set holds.
	texts       []simpTextRule
	adaptables  []*simpAdaptable
	diags       []Diagnostic
	seenRules   map[core.PropKey]int // rule AlphaKey → entry index that first added it
	seenSrcKeys map[core.PropKey]struct{}
	nextEntry   int // entry index for rules added after the agent's list
}

func newSimpRuleSet() *simpRuleSet {
	return &simpRuleSet{seenRules: map[core.PropKey]int{}, seenSrcKeys: map[core.PropKey]struct{}{}}
}

// apply runs the set on node as ONE simp_with ministep: on the
// conclusion, or on hypothesis *hyp in its place when hyp is non-nil.
func (rs *simpRuleSet) apply(node *proof.GoalStackNode, hyp *int) bool {
	return proof.ApplySimpWithRead(node, hyp, rs.rules, rs.flips, rs.readings)
}

// refusal is tactic.SimpRefusal over the set as the last sentence of a
// no-progress message, and nothing when no rule was refused at targets.
func (rs *simpRuleSet) refusal(goal core.Prop, targets ...core.Term) string {
	if note := tactic.SimpRefusal(goal, rs.rules, rs.flips, targets...); note != "" {
		return " " + note
	}
	return ""
}

// cut is tactic.SimpCut over the set: what a step says when the
// divergence whistle ended its rewrite of one of targets, and nothing
// when it cut none.
func (rs *simpRuleSet) cut(goal core.Prop, targets ...core.Term) string {
	return tactic.SimpCut(goal, rs.rules, rs.flips, targets...)
}

// hypIndexInRange refuses a hyp_index past the goal's hypotheses by
// name: the index is the request's, read from outside. nil for an
// absent index.
func hypIndexInRange(verb string, goal core.Prop, hyp *int) error {
	if hyp == nil || *hyp >= 0 && *hyp < goal.NumHyps() {
		return nil
	}
	return fmt.Errorf("%s hyp_index %d out of range [0, %d): the goal has %d hypotheses", verb, *hyp, goal.NumHyps(), goal.NumHyps())
}

// simpTarget is the term apply rewrites: hypothesis *hyp when hyp is
// non-nil, else the conclusion; the index is in range
// (hypIndexInRange).
func simpTarget(goal core.Prop, hyp *int) core.Term {
	if hyp != nil {
		return goal.Hyp(*hyp)
	}
	return goal.Conclusion()
}

// add records one resolved rule with its source. Returns false when
// the rule was already in the set (a diagnostic names the collision
// when it came from a different entry).
func (rs *simpRuleSet) add(entryIdx int, src simpRuleSrc, rule core.Prop, flip bool) bool {
	k := rule.AlphaKey()
	if firstIdx, dup := rs.seenRules[k]; dup {
		if firstIdx != entryIdx {
			rs.diags = append(rs.diags, Diagnostic{
				Type: DiagAutoTypeInstances,
				Message: fmt.Sprintf(
					"simp_with: rule #%d resolves to the same instance as rule #%d (%s) — deduplicated, one copy kept",
					entryIdx, firstIdx, prop.PrintProp(rule)),
			})
		}
		return false
	}
	rs.seenRules[k] = entryIdx
	rs.rules = append(rs.rules, rule.AsProp())
	rs.flips = append(rs.flips, flip)
	rs.readings = append(rs.readings, src.reading)
	if src.text {
		rs.texts = append(rs.texts, simpTextRule{entry: entryIdx, rule: rule.AsProp()})
	}
	if src.key != "" || src.cert != nil || src.resident {
		// One close-pass source per distinct entry: the pass iterates
		// all leaves to fixpoint, so N instance children of the same
		// entry close through one source. A session define has no key;
		// its certificate is the identity; a resident rule has neither,
		// and closes on its hypothesis.
		id := src.key
		if id == "" {
			id = src.prop.AlphaKey()
		}
		if _, dup := rs.seenSrcKeys[id]; !dup {
			rs.seenSrcKeys[id] = struct{}{}
			rs.srcs = append(rs.srcs, src)
		}
	}
	return true
}

// addAdaptable enters a polymorphic rule at its own letters and marks it
// for adaptation against the goal. The rule at its OWN letters stays in
// the set beside the adapted copies: the enumeration returns the goal's
// OTHER instances — it drops the identity by contract — and a goal
// carrying the constant at the rule's own instance beside another has a
// redex only the unadapted rule matches (measured on list_append at A
// and B in one goal: the B copy alone fires nothing, since the redex it
// needs is the A copy's to expose). An unfired copy costs no child and
// no rendering.
func (rs *simpRuleSet) addAdaptable(entryIdx int, label string, src simpRuleSrc, poly core.Prop, flip bool) {
	rs.add(entryIdx, src, poly, flip)
	if poly.NumHyps() == 0 && ext.PropHasTypeVars(poly) {
		rs.adaptables = append(rs.adaptables, &simpAdaptable{entryIdx: entryIdx, label: label, src: src, poly: poly, flip: flip})
	}
}

// addInstalled appends the session's installed simp set — the bound
// family's and its imports' definitions, and the session's own defines
// — behind the rules already in the set, each a source backed by its
// certificate and adaptable to the goal's instances. The bare `simp`
// runs this set alone and `simp_all` runs it behind its named rules;
// `simp_with` never adds it.
func (rs *simpRuleSet) addInstalled(s *Session) {
	if s == nil {
		return
	}
	for _, r := range s.simpRules {
		idx := rs.nextEntry
		rs.nextEntry++
		src := simpRuleSrc{prop: r.rule, cert: r.cert}
		label := "installed rule " + prop.PrintProp(r.rule)
		if r.entry != nil {
			src.key = core.PropKey(r.entry.Key)
			label = "installed " + r.entry.Name
		}
		rs.addAdaptable(idx, label, src, r.rule, false)
	}
}

// adaptAgainst adds, for every adaptable rule, one copy per distinct
// type instance `target` exhibits beyond the copies already in the set
// (typematch.EnumerateLemmaTypeAdaptations — same informative-anchor
// gating as the single-instance adapter, dedup by instantiated-lemma
// AlphaKey), completing every finite anchor pin. Returns the number
// of copies added.
func (rs *simpRuleSet) adaptAgainst(target core.Prop, exposed bool) int {
	added := 0
	for _, a := range rs.adaptables {
		adaptations := typematch.EnumerateLemmaTypeAdaptations(a.poly, target)
		if len(adaptations) == 0 {
			continue
		}
		var names []string
		for _, adapted := range adaptations {
			if _, dup := rs.seenRules[adapted.AlphaKey()]; dup {
				continue
			}
			// Every adapted copy of one entry carries the same flip
			// bit — type-adaptation is a type substitution, so a rule
			// that was ∀xs. l = r before adaptation stays ∀xs. l = r
			// after (with a different type instance), still flippable.
			if rs.add(a.entryIdx, a.src, adapted, a.flip) {
				added++
				names = append(names, prop.PrintProp(adapted))
			}
		}
		// Name each instance whenever the expansion did anything
		// beyond a single-instance adaptation, or the
		// instance was exposed by the rewrite itself.
		if len(names) > 1 || (exposed && len(names) > 0) {
			where := "distinct goal type-instance(s) beside the rule's own"
			if exposed {
				where = "type-instance(s) the rewrite itself exposed"
			}
			msg := fmt.Sprintf(
				"simp_with: rule #%d (%s) is polymorphic without explicit type_specialize — auto-adapted to %d %s: %s",
				a.entryIdx, a.label, len(names), where, strings.Join(names, " ; "))

			rs.diags = append(rs.diags, Diagnostic{Type: DiagAutoTypeInstances, Message: msg})
		}
	}
	return added
}

// expandToFixpoint re-reads the goal's type instances AFTER the rules
// have rewritten it: a rule whose constant does not occur in the goal
// until an earlier rule's unfold exposes it (fst under letter_inverse,
// list_append under list_reverse) adapts to nothing at resolution and
// fires nowhere; here the driver runs on the set so far, every
// adaptable rule is adapted against the residual, and the loop repeats
// while a round adds a copy. The recorded step is still ONE driver run
// over the final set — the driver is a pure function of (goal, rules),
// so with every needed instance present it reaches the full rewrite in
// that one run, and replay re-runs exactly it.
func (rs *simpRuleSet) expandToFixpoint(goal core.Prop, hyp *int) error {
	rs.adaptAgainst(goal, false)
	for round := 0; ; round++ {
		residual := proof.SimpResidual(goal, hyp, rs.rules, rs.flips)
		if residual == nil {
			return nil
		}
		added := rs.adaptAgainst(residual, true)
		if added == 0 {
			return nil
		}
		if round < proof.MaxSimpAdaptRounds {
			continue
		}
		// At the bound, as the Go Simp decides it (proof.MaxSimpAdaptRounds):
		// a copy this round added that rewrites the residual on its own is
		// named; copies with no redex are inert, the set complete as it
		// stands.
		var exposed []string
		for j := len(rs.rules) - added; j < len(rs.rules); j++ {
			if proof.SimpResidual(residual, hyp, rs.rules[j:j+1], rs.flips[j:j+1]) != nil {
				entry := rs.seenRules[rs.rules[j].AlphaKey()]
				exposed = append(exposed, fmt.Sprintf("rule #%d (%s) at %s", entry, rs.entryLabel(entry), prop.PrintProp(rs.rules[j])))
			}
		}
		if len(exposed) == 0 {
			return nil
		}
		return fmt.Errorf("simp_with: the rewrite keeps exposing rule instances that rewrite further, %d residual rounds deep — "+
			"the last round exposed %s. A rule restating its constant at a larger type reaches no fixpoint, and a chain of "+
			"unfolds deeper than the bound is not followed: pass the instance meant with an explicit type_specialize "+
			"(an explicit instance is not re-adapted), or drop the rule",
			proof.MaxSimpAdaptRounds, strings.Join(exposed, " ; "))
	}
}

// entryLabel is the diagnostics' name of entry idx: its adaptable's
// label (a copy only ever comes from an adaptable).
func (rs *simpRuleSet) entryLabel(idx int) string {
	for _, a := range rs.adaptables {
		if a.entryIdx == idx {
			return a.label
		}
	}
	panic(fmt.Sprintf("simp_with: entry %d added a copy without being adaptable", idx))
}

// resolveSimpWithRules resolves the agent's with_lemmas entries into the
// ordered rule set handed to proof.ApplySimpWith, each polymorphic
// no-σ entry adapted to the goal's instances, plus the per-source
// close-pass list and any informational diagnostics. See the package
// comment for the multi-instance expansion contract. `simp_all` adds
// the session's installed set behind them (addInstalled); every caller
// adapts to the instances the rewrite exposes (expandToFixpoint)
// before applying.
func (e *Engine) resolveSimpWithRules(
	s *Session,
	goal core.Prop,
	entries []LemmaWithSpec,
) (*simpRuleSet, error) {
	rs := newSimpRuleSet()
	rs.nextEntry = len(entries)
	for i, l := range entries {
		if l.HypIndex != nil {
			if rerr := addSimpResident(goal, rs, i, l); rerr != nil {
				return nil, fmt.Errorf("simp_with: lemma #%d (%s): %w", i, describeSimpWithEntry(l), rerr)
			}
			continue
		}
		if l.ReadAt != nil {
			// A structure law read at an instance (reading.go): the
			// rule is the derived theorem — under a resident hypothesis
			// the sequent, whose hypothesis the goal holds — at its own
			// letters, as the Go `Fwd(law.Read(instance))` serves it.
			if rerr := e.addSimpReading(s, goal, rs, i, l); rerr != nil {
				return nil, fmt.Errorf("simp_with: lemma #%d (%s): %w", i, describeSimpWithEntry(l), rerr)
			}
			continue
		}
		lemmaReq := TacticReq{
			Type:           "lemma",
			LemmaKey:       l.Key,
			LemmaText:      l.Text,
			TypeSpecialize: l.TypeSpecialize,
			TermSpecialize: l.TermSpecialize,
		}
		lemmaProp, lerr := e.resolveLemma(s, lemmaReq, goal)
		if lerr != nil {
			return nil, fmt.Errorf("simp_with: lemma #%d: %w", i, lerr)
		}
		if lemmaProp == nil {
			return nil, fmt.Errorf("simp_with: lemma #%d: missing key or text", i)
		}
		if l.Coefficient != "" {
			return nil, fmt.Errorf(
				"simp_with: lemma #%d (%s): coefficient scales a `by` premise (Lean's linear_combination) — a rewrite rule is not scaled",
				i, describeSimpWithEntry(l))
		}
		if l.Normalized && (len(l.TypeSpecialize) > 0 || len(l.TermSpecialize) > 0) {
			return nil, fmt.Errorf(
				"simp_with: lemma #%d (%s): normalized:true beside type_specialize / term_specialize — a specialized instance is served in its STATED form (as ctx.AtTypes serves it); drop one of the two",
				i, describeSimpWithEntry(l))
		}
		if l.Flip {
			// Reject flip on rule shapes with no equation UPFRONT so the
			// agent gets a clean typed error (naming the entry and its
			// resolved shape) instead of a silent no-progress failure
			// from the driver. Flip is well-defined on a rule whose
			// ∀-stripped body is `l = r` / `l ⇔ r` (bool =) and on the
			// equation matrix of a conditional rule (Horn or clause
			// form) — the driver turns that equation around in place
			// (tactic.RuleFlippable / flipRuleLemma).
			if !tactic.RuleFlippable(lemmaProp) {
				return nil, fmt.Errorf(
					"simp_with: lemma #%d (%s): flip:true needs an equation to turn around — a plain `∀xs. l = r` / `l ⇔ r`, or the equation matrix of a conditional rule (`C ⇒ … ⇒ ∀ys. l = r`, `¬C ∨ … ∨ l = r`) with l and r distinct; the resolved form carries none — drop flip",
					i, describeSimpWithEntry(l))
			}
		}
		// A clause the driver reads as a CLOSURE rule — an atom under a
		// Horn antecedent — is named HERE, once per entry, so a
		// no-progress failure does not send the author down the
		// exposed-redex / side-condition ladder for a rule that
		// rewrites nothing (tactic.ClosureSimpClauses).
		if closures := tactic.ClosureSimpClauses(lemmaProp); len(closures) > 0 {
			rs.diags = append(rs.diags, Diagnostic{
				Type: DiagRuleShape,
				Message: fmt.Sprintf(
					"simp_with: rule #%d (%s) has %d clause(s) whose matrix under the antecedent is an ATOM, not an equation — a closure rule: it discharges a side condition of the set's conditional rewrites and rewrites nothing itself: %s",
					i, describeSimpWithEntry(l), len(closures), strings.Join(closures, " ; ")),
			})
		}
		// Capture the source BEFORE any specialization replaces
		// lemmaProp: the post-step type-instance close pass must
		// receive the POLYMORPHIC form so a specialized rule child
		// records a _TypeInstStep against the entry.
		// Handing it the specialized instance instead takes the
		// identical-α-key branch, which closes the child with a
		// _KnownThmStep whose payload is the per-session instance — a
		// statement naming nothing, detonating only at emit. Mirrors
		// auto_with's pre-specialization srcs capture.
		src := simpRuleSrc{key: core.PropKey(l.Key), prop: lemmaProp, text: l.Key == ""}
		if l.Normalized {
			// The normalizer's orientation of the served statement —
			// the form ctx.DepNormalized(name) resolves to at replay
			// (proof.NormalizedForm: Normalize, stated prefix order).
			// The flip check above read the stated form; a normalized
			// rule that has no equation to turn around is refused the
			// same way, on the form the driver will actually see.
			lemmaProp = proof.NormalizedForm(lemmaProp)
			if l.Flip && !tactic.RuleFlippable(lemmaProp) {
				return nil, fmt.Errorf(
					"simp_with: lemma #%d (%s): flip:true on the normalized form %s, which carries no equation to turn around — drop flip",
					i, describeSimpWithEntry(l), prop.PrintProp(lemmaProp))
			}
		}
		var fixed core.VarTypePredicate = utils.EmptyPredicate[core.VarType]
		if len(l.TypeSpecialize) > 0 {
			specialized, goalLetters, sErr := buildSpecializedLemma(lemmaProp, l.TypeSpecialize, goal)
			if sErr != nil {
				return nil, fmt.Errorf("simp_with: lemma #%d: %w", i, sErr)
			}
			lemmaProp, fixed = specialized, goalLetters
		}
		if len(l.TermSpecialize) > 0 {
			specialized, sErr := e.buildTermSpecializedLemma(lemmaProp, l.TermSpecialize, goal, s.familyScope(), fixed)
			if sErr != nil {
				return nil, fmt.Errorf("simp_with: lemma #%d: %w", i, sErr)
			}
			lemmaProp = specialized
		}
		// Polymorphic rules adapt against the goal unless the agent's
		// explicit σ already pinned the instance (same skip-adapt
		// rationale as lean_rw's term_specialize fork — Exact-bypass:
		// an explicit σ is honored verbatim, single instance, never
		// re-adapted). Without an explicit σ the rule expands to one
		// copy per distinct instance found by the finite anchor walk,
		// against the goal and the residuals in expandToFixpoint.
		if len(l.TypeSpecialize) == 0 && len(l.TermSpecialize) == 0 {
			rs.addAdaptable(i, describeSimpWithEntry(l), src, lemmaProp, l.Flip)
			continue
		}
		rs.add(i, src, lemmaProp, l.Flip)
	}
	if len(rs.rules) == 0 {
		// Unreachable in practice (the first entry always adds), but a
		// rewrite set that deduplicated to nothing must fail loudly, not
		// hand the driver an empty set.
		return nil, fmt.Errorf("simp_with: rule set is empty after deduplication")
	}
	return rs, nil
}

// addSimpReading enters one rule that is a law read at an instance
// (LemmaWithSpec.ReadAt). The rule is a single statement, entered once
// and never adapted: a reading's type letters are its instance's, and a
// letter the instance leaves loose is not re-read against the goal, as
// Go's Simp does not re-read it.
func (e *Engine) addSimpReading(s *Session, goal core.Prop, rs *simpRuleSet, entryIdx int, l LemmaWithSpec) error {
	switch {
	case l.Text != "":
		return fmt.Errorf("read_at reads a law at an instance — name the law by its key, or a proved section of this session by its id, not by text")
	case len(l.TypeSpecialize) > 0:
		return fmt.Errorf("read_at with type_specialize: the reading's type letters are the instance's, fixed by its components or pinned off the goal or the tuple — drop type_specialize")
	case len(l.TermSpecialize) > 0:
		return fmt.Errorf("read_at with term_specialize: a rewrite rule matches its own instances — a reading is a rule as it stands; ground one in a `by` premise")
	case l.Normalized:
		return fmt.Errorf("read_at with normalized:true: a reading is served in its stated form — drop normalized")
	case l.Coefficient != "":
		return fmt.Errorf("coefficient scales a `by` premise (Lean's linear_combination) — a rewrite rule is not scaled")
	}
	reading, err := e.resolveReading(s, goal, l.Key, l.ReadAt)
	if err != nil {
		return err
	}
	rule := reading.theorem
	if l.Flip && !tactic.RuleFlippable(rule) {
		return fmt.Errorf("flip:true needs an equation to turn around, and %s carries none — drop flip: %s",
			reading.describe, prop.PrintProp(rule))
	}
	if closures := tactic.ClosureSimpClauses(rule); len(closures) > 0 {
		rs.diags = append(rs.diags, Diagnostic{
			Type: DiagRuleShape,
			Message: fmt.Sprintf(
				"simp_with: rule #%d (%s) has %d clause(s) whose matrix under the antecedent is an ATOM, not an equation — a closure rule: it discharges a side condition of the set's conditional rewrites and rewrites nothing itself: %s",
				entryIdx, reading.describe, len(closures), strings.Join(closures, " ; ")),
		})
	}
	rs.add(entryIdx, simpRuleSrc{prop: rule, cert: rule, reading: reading.record}, rule, l.Flip)
	return nil
}

// addSimpResident adds a resident hypothesis of the goal as a rule:
// the hypothesis assumed, `h ⊢ h`, at its own types (never adapted) —
// the rule the Go `Simp(Fwd(fact))` resolves to (proof.residentRule).
func addSimpResident(goal core.Prop, rs *simpRuleSet, entryIdx int, l LemmaWithSpec) error {
	switch {
	case l.Key != "" || l.Text != "" || l.ReadAt != nil:
		return fmt.Errorf("hyp_index names the rule by itself — a resident hypothesis, with no key, text or read_at beside it")
	case len(l.TypeSpecialize) > 0 || len(l.TermSpecialize) > 0:
		return fmt.Errorf("hyp_index with a specialization: a resident hypothesis is a rule at its own types, matching its own instances")
	case l.Normalized:
		return fmt.Errorf("hyp_index with normalized:true: a resident hypothesis is served as it stands")
	case l.Coefficient != "":
		return fmt.Errorf("coefficient scales a `by` premise (Lean's linear_combination) — a rewrite rule is not scaled")
	}
	idx := *l.HypIndex
	if idx < 0 || idx >= goal.NumHyps() {
		return fmt.Errorf("hyp_index %d out of range [0, %d)", idx, goal.NumHyps())
	}
	rule := core.Prop(core.Assume(goal.Hyp(idx)))
	if l.Flip && !tactic.RuleFlippable(rule) {
		return fmt.Errorf("flip:true needs an equation to turn around, and hypothesis %d carries none — drop flip: %s",
			idx, prop.PrintProp(rule))
	}
	if closures := tactic.ClosureSimpClauses(rule); len(closures) > 0 {
		rs.diags = append(rs.diags, Diagnostic{
			Type: DiagRuleShape,
			Message: fmt.Sprintf(
				"simp_with: rule #%d (hyp_index %d) has %d clause(s) whose matrix under the antecedent is an ATOM, not an equation — a closure rule: it discharges a side condition of the set's conditional rewrites and rewrites nothing itself: %s",
				entryIdx, idx, len(closures), strings.Join(closures, " ; ")),
		})
	}
	rs.add(entryIdx, simpRuleSrc{prop: rule, resident: true}, rule, l.Flip)
	return nil
}

// residentRuleIndices are the hypothesis indices the entries name as
// rules.
func residentRuleIndices(entries []LemmaWithSpec) []int {
	var out []int
	for _, l := range entries {
		if l.HypIndex != nil {
			out = append(out, *l.HypIndex)
		}
	}
	return out
}

// closeSimpRuleChildren closes the rule children a fired simp step left
// open on roots, through the three channels in order: a PROVED sibling
// section stating the rule; a source's own certificate at an α-equal
// child (the installed definitions — the define section's promise, an
// import's replay promise — in a scratch cache, so session-authored
// facts never enter the dep-bounded pool); and the type-instance pass
// per source for an adapted or specialized copy's child (a
// _TypeInstStep against the polymorphic entry, the channel `lemma`'s
// claim child uses, so deps record the entry). Returns every closed
// child for StepResult.AutoMatched.
func (s *Session) closeSimpRuleChildren(roots []*proof.GoalStackNode, rs *simpRuleSet) []AutoMatchedGoal {
	// A resident hypothesis's rule closes on the hypothesis first, so
	// no entry the auto-match finds stands in for it.
	for _, src := range rs.srcs {
		if !src.resident {
			continue
		}
		for _, root := range roots {
			for _, leaf := range root.UnsolvedLeaves() {
				if src.prop.AlphaEquals(leaf.Goal) && !proof.ApplyAssumption(leaf) {
					panic(fmt.Sprintf("simp_with: the obligation of a resident rule does not close on its hypothesis (engine invariant): %s",
						prop.PrintProp(leaf.Goal)))
				}
			}
		}
	}
	matched := s.applyAutoMatchOnRoots(roots, s.autoMatchCache)
	certCache := &proof.ThmCache{}
	var certSrcs []simpRuleSrc
	for _, src := range rs.srcs {
		if src.cert == nil {
			continue
		}
		certSrcs = append(certSrcs, src)
		normalized, _ := prop.Normalize(src.cert)
		certCache.SaveThm(src.cert, normalized)
	}
	if len(certSrcs) > 0 {
		for _, root := range roots {
			for _, leaf := range root.UnsolvedLeaves() {
				for _, src := range certSrcs {
					if src.prop.AlphaEquals(leaf.Goal) {
						proof.ApplyKnown(leaf, certCache)
						break
					}
				}
			}
		}
	}
	for _, src := range rs.srcs {
		if src.resident {
			continue
		}
		source, cache := src.prop, s.autoMatchCache
		if src.cert != nil {
			source, cache = src.cert, certCache
		}
		matched = append(matched, s.applyAutoMatchTypeInstanceOnRoots(roots, src.key, source, nil, cache)...)
	}
	return matched
}

// openTextRule is the refusal of a step on goal that leaves a text
// rule's obligation open on roots once the close pass has run
// (closeSimpRuleChildren), and nil when it leaves none. A rule given by
// text is certified by a proved section of the session or an entry
// that states it, as a `by` premise given by text is. Its obligation is
// the rule with no hypotheses, so a conditional rule the goal holds is
// not certified by the hypothesis, and the refusal names the
// hypothesis to cite in its place. A rule whose normal form is ⊤ closes
// on no section either: the pass that reads the proved sections passes
// over a leaf the normalizer decides (applyAutoMatchOnRoots), so the
// refusal names the one route such a rule has, asserted and then cited
// as a hypothesis. The step is run on a clone, so a refused one leaves
// the session as it was.
func (rs *simpRuleSet) openTextRule(verb string, goal core.Prop, roots []*proof.GoalStackNode, entries []LemmaWithSpec) error {
	for _, root := range roots {
		for _, leaf := range root.UnsolvedLeaves() {
			for _, text := range rs.texts {
				if !text.rule.AlphaEquals(leaf.Goal) {
					continue
				}
				who := fmt.Sprintf("%s: lemma #%d (%s) is a rule given by text", verb, text.entry, describeSimpWithEntry(entries[text.entry]))
				if text.rule.NumHyps() == 0 {
					for i, h := range goal.Hyps() {
						if h.AlphaEquals(text.rule.Conclusion()) {
							return fmt.Errorf("%s, and its obligation is the rule under no hypothesis, which nothing "+
								"certifies. The goal holds the rule as hypothesis %d: name it by `hyp_index: %d` in place "+
								"of the text, and it is read under that hypothesis. The session is unchanged.", who, i, i)
						}
					}
				}
				if normal, _ := prop.Normalize(text.rule); normal.Conclusion().Equals(ext.T) {
					return fmt.Errorf("%s, and nothing certifies it. The rule is one the normalizer decides — its "+
						"normal form is ⊤ — and such a statement closes on no section that states it, so proving it "+
						"as a section does not serve. `assert` it with the same text, close the claim (`auto`), and "+
						"name the hypothesis it leaves by `hyp_index` in place of the text. The session is unchanged.\n"+
						"  the rule: %s", who, prop.PrintProp(text.rule))
				}
				return fmt.Errorf("%s, and nothing certifies it: no proved section of this session and no entry "+
					"states it. A text rule is proved before it is used. A law is a section of its own (add-goal), or "+
					"an entry cited by `key`; a fact about this goal's own variables is an `assert` of the same text, "+
					"which leaves it a hypothesis to name by `hyp_index`. The session is unchanged.\n  the rule: %s",
					who, prop.PrintProp(text.rule))
			}
		}
	}
	return nil
}

// describeSimpWithEntry names a with_lemmas entry for diagnostics: its
// key when key-loaded, otherwise a shortened text form
// (rune-safe — the label lands in strict-UTF-8 RPC diagnostics).
func describeSimpWithEntry(l LemmaWithSpec) string {
	if l.Key != "" {
		return "key " + l.Key
	}
	if l.HypIndex != nil {
		return fmt.Sprintf("hyp_index %d", *l.HypIndex)
	}
	return "text " + abbreviateString(l.Text, 60)
}
