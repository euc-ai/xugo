// defer.go — the `defer` move: an open leaf becomes a CARD — a member of
// the session's family stated without a proof — and the leaf closes by
// citing it. The card is minted in the session as the axiom
// `⊢ <statement>` (the leaf's conclusion ∀-closed over its free
// variables), named `<family>.<Name>`, and the leaf closes by the
// `lemma` move naming it, recorded like any cite. `emit-section`
// renders the card as a family.Add entry built by family.Card beside
// the member, so the landed file carries both and the member's proof
// cites the card; replay serves the card as its axiom
// (library/serve, the harness's trust frontier) until a proof lands in
// place of the Card build. Nothing is threaded through the section and
// nothing is restated later: filling the card is local to the card.
//
// A defer may name the card's Deps: the members its proof will cite,
// the narrative a hand-laid card's Deps carry, which orders the fill
// and which nothing replays. Each is a registered name, as a `lemma`
// cite spells it — a registry entry the family's package can name in
// Go, or a card this session minted — and the rendered card entry
// lists them as its Deps.
//
// A card is identified by its STATEMENT — the normalized key — so the
// same lemma deferred twice in one session is one card, standing on the
// deps either defer named, and a card an entry already states is not
// minted: the result says so and names the entry to cite. The lineage
// records each defer that mints a card, attaches one to a section or
// adds to its deps; resume re-issues it, and the recorded cite that
// follows re-closes the leaf.

package engine

import (
	"context"
	"errors"
	"fmt"
	"path"
	"regexp"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
)

// DeferRequest names the open leaf to defer and the card's name, note
// and deps. Name is the card's bare member name in the chapter (the Go
// variable the entry lands as); Note is the agent's account of why it
// deserves to be a member and what its proof must establish — the
// brief the next prover reads; Deps are the registered names of the
// members that proof will cite (file comment), none when omitted.
type DeferRequest struct {
	SessionID string   `json:"session_id"`
	GoalID    string   `json:"goal_id"`
	Name      string   `json:"name"`
	Note      string   `json:"note,omitempty"`
	Deps      []string `json:"deps,omitempty"`
}

// DeferredCard is a card as the session carries it: the closed
// statement (its Key is the card's identity), the bare name and the
// registered name it lands under — the spelling a cite uses — the
// note, the deps by registered name, and the section whose leaf
// deferred it.
type DeferredCard struct {
	Key       string   `json:"key"`
	Name      string   `json:"name"`
	Entry     string   `json:"entry"`
	Note      string   `json:"note,omitempty"`
	Deps      []string `json:"deps,omitempty"`
	Statement string   `json:"statement"`
	// StatementTyped is the parse-faithful spelling — paste it into
	// `add-goal {text}` to attack the card. Absent when the print does
	// not round-trip (see FormatStatementTyped).
	StatementTyped string `json:"statement_typed,omitempty"`
	Section        int    `json:"section"`
}

// SectionStatus is a section as the deferral views report it: its
// statement, whether it is proved, and the cards it cites.
type SectionStatus struct {
	Section   int            `json:"section"`
	Statement string         `json:"statement"`
	Proved    bool           `json:"proved"`
	Cards     []DeferredCard `json:"cards,omitempty"`
}

// DeferResult reports a defer. Status is "deferred" (the card is
// minted and the leaf closed by it), "proved" (a proved entry already
// states the card — nothing was minted; cite it by the name in
// StatedBy) or "card" (a landed card states it — cite that card). A
// replayed defer never reports the latter two: it re-mints what the
// transcript recorded.
type DeferResult struct {
	Status   string   `json:"status"`
	StatedBy []string `json:"stated_by,omitempty"`
	// OpenElsewhere lists the other lineages that minted this card —
	// the same lemma deferred twice is one card.
	OpenElsewhere []string       `json:"open_elsewhere,omitempty"`
	Card          *DeferredCard  `json:"card,omitempty"`
	Section       *SectionStatus `json:"section,omitempty"`
	State         *StateView     `json:"state,omitempty"`
}

// sessionCard is a card the session minted: its statement, closed,
// its key, the names it goes by, its deps, and the axiom it is served
// as in this session — `⊢ <statement>`, a realized certificate.
type sessionCard struct {
	key       core.PropKey
	statement core.Prop
	name      string // bare: the Go variable the entry lands as
	entry     string // registered: <family>.<name>, the cite spelling
	note      string
	// deps are the registered names every defer of the card named, in
	// the order first named: the same lemma deferred twice is one card,
	// standing on what either defer said it stands on.
	deps  []string
	axiom core.ThmCert
}

// view is the card as served, through the session's output door.
func (c *sessionCard) view(section int, door *Spelling) DeferredCard {
	typed, _ := door.Typed(c.statement)
	return DeferredCard{
		Key:            string(c.key),
		Name:           c.name,
		Entry:          c.entry,
		Note:           c.note,
		Deps:           slices.Clone(c.deps),
		Statement:      door.Prop(c.statement),
		StatementTyped: typed,
		Section:        section,
	}
}

// status is the section as served, through the session's output door.
func (sec *sectionState) status(idx int, door *Spelling) *SectionStatus {
	st := &SectionStatus{Section: idx, Statement: door.Prop(sec.root.Goal), Proved: sec.root.Proved()}
	for _, c := range sec.deferred {
		st.Cards = append(st.Cards, c.view(idx, door))
	}
	return st
}

// cardStatement is the card a leaf conclusion states: the conclusion
// closed over every free variable, so the lemma stands on its own.
func cardStatement(concl core.Term) core.Prop {
	return prop.ForAllConclFreeVars(prop.MakeProp(concl))
}

// statementKey is a goal's identity among cards and members: a
// hyp-free goal is read as the closed statement it states (so a target
// stated with free variables and one stated with binders are one), a
// sequent goal is keyed as itself.
func statementKey(g core.Prop) core.PropKey {
	if g.NumHyps() == 0 {
		return registry.KeyOf(cardStatement(g.Conclusion()))
	}
	return registry.KeyOf(g)
}

// sectionLocalFrees lists the variables free in t that are not free in
// the section's own statement — the Skolems the proof introduced. A
// card may not mention them: it is a theorem of the chapter, and the
// section's replay mints those names afresh.
func sectionLocalFrees(root core.Prop, t core.Term) []string {
	var names []string
	for _, v := range t.Frees(func(core.VarTerm) bool { return true }) {
		if root.Conclusion().HasFree(v) || root.AnyHyp(func(h core.Term) bool { return h.HasFree(v) }) {
			continue
		}
		names = append(names, ext.PrintTerm(v))
	}
	return names
}

// cardName is the shape a card's name must have: the exported Go
// identifier its entry var is declared as (entry lint E0).
var cardName = regexp.MustCompile(`^[A-Z][A-Za-z0-9]*$`)

// cardFor resolves a session card by its registered name or its key;
// nil when the session minted none such. The card channel every cite
// path consults after the registry: resolveLemmaProp (the served
// statement), the cited-entry certification (the claim child), and
// corpusBackedInjection (the certificate).
func (s *Session) cardFor(keyOrName string) *sessionCard {
	if s == nil || keyOrName == "" {
		return nil
	}
	if c, ok := s.cards[keyOrName]; ok {
		return c
	}
	for _, c := range s.cards {
		if string(c.key) == keyOrName {
			return c
		}
	}
	return nil
}

// cardDeps reads a defer's deps: trimmed, in the order given, each
// once, every one a member the card may stand on (cardDepRefusal).
func (s *Session) cardDeps(names []string) ([]string, error) {
	var out []string
	for i, raw := range names {
		name := strings.TrimSpace(raw)
		if name == "" {
			return nil, fmt.Errorf("defer: deps[%d] is empty — each dep is a member's registered name, <family>.<Name>", i)
		}
		if slices.Contains(out, name) {
			continue
		}
		if err := s.cardDepRefusal(name); err != nil {
			return nil, err
		}
		out = append(out, name)
	}
	return out, nil
}

// cardDepRefusal says why a card of the session's family cannot stand
// on the member registered as name, and is nil when it can: name is a
// card this session minted, or a registry entry the family's package
// can name in Go (citeRefusal) — a dep is spelled as a `lemma` cite
// spells an entry, and the card entry emit-section renders names it.
func (s *Session) cardDepRefusal(name string) error {
	if _, ok := s.cards[name]; ok {
		return nil
	}
	if entry, ok := registry.ByName(name); ok {
		if err := s.citeRefusal(entry); err != nil {
			return fmt.Errorf("defer: the dep %s — %w", name, err)
		}
		return nil
	}
	hint := ""
	if !strings.Contains(name, ".") {
		qualified := path.Base(s.family.Name) + "." + name
		_, minted := s.cards[qualified]
		_, registered := registry.ByName(qualified)
		if minted || registered {
			hint = fmt.Sprintf("; a member of this family is qualified too: %s", qualified)
		}
	}
	return fmt.Errorf("defer: the dep %q is no registered member and no card this session minted — "+
		"name each dep by its registered name, <family>.<Name>, as a `lemma` cite does%s", name, hint)
}

// cardDepCycle refuses deps that would make the card registered as own
// stand on itself: own among them, or a card of the session among them
// whose deps reach own. The rendered card entries name their deps as
// Go variables, so a cycle among them is a Go initialization cycle.
func (s *Session) cardDepCycle(own string, deps []string) error {
	for _, d := range deps {
		if d == own {
			return fmt.Errorf("defer: the deps name the card itself, %s — a card does not stand on itself; drop it from deps", own)
		}
		if chain := s.cardDepChain(d, own, map[string]bool{}); chain != nil {
			return fmt.Errorf("defer: the dep %s stands on the card %s (%s) — a card cannot stand on what stands on it; drop %s from deps",
				d, own, strings.Join(chain, " → "), d)
		}
	}
	return nil
}

// cardDepChain is the path from the session card registered as from
// to the one registered as to through the session cards' deps, from
// first; nil when there is none.
func (s *Session) cardDepChain(from, to string, seen map[string]bool) []string {
	c, ok := s.cards[from]
	if !ok || seen[from] {
		return nil
	}
	seen[from] = true
	for _, d := range c.deps {
		if d == to {
			return []string{from, to}
		}
		if rest := s.cardDepChain(d, to, seen); rest != nil {
			return append([]string{from}, rest...)
		}
	}
	return nil
}

// unionNames is have followed by the names of more it lacks, in order;
// have itself is never extended in place.
func unionNames(have, more []string) []string {
	out := slices.Clone(have)
	for _, n := range more {
		if !slices.Contains(out, n) {
			out = append(out, n)
		}
	}
	return out
}

// Defer makes the open leaf a card and closes the leaf by it — see the
// file comment. The lineage records the mint and the closing cite;
// resume replays both.
func (e *Engine) Defer(ctx context.Context, req *DeferRequest) (*DeferResult, error) {
	if req == nil {
		return nil, errors.New("defer: nil request")
	}
	s, err := e.getSession(req.SessionID)
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if err := s.faultRefusal(); err != nil {
		return nil, err
	}
	return e.deferLocked(ctx, s, req.GoalID, req.Name, req.Note, req.Deps, true)
}

// deferLocked is Defer under the session lock. closeLeaf says whether
// to close the leaf by the minted card (the live move); a resume
// re-mints only, the recorded cite that follows closes the leaf.
func (e *Engine) deferLocked(ctx context.Context, s *Session, goalID, name, note string, deps []string, closeLeaf bool) (*DeferResult, error) {
	name = strings.TrimSpace(name)
	note = strings.TrimSpace(note)
	if name == "" {
		return nil, errors.New("defer: name is required — the card's member name in the chapter, the Go variable its entry lands as")
	}
	if !cardName.MatchString(name) {
		return nil, fmt.Errorf("defer: %q is not a member name — an exported Go identifier (MulOne, DividesAntisym)", name)
	}
	if note == "" && !s.replaying {
		return nil, errors.New("defer: note is required — why the card is a member and what its proof must establish, the brief its prover reads")
	}
	if s.family == nil {
		return nil, errors.New("defer: the session is bound to no family — a card is a member of a chapter; create the session with {family: …}")
	}
	deps, err := s.cardDeps(deps)
	if err != nil {
		return nil, err
	}
	entry, ok := s.goalIndex[goalID]
	if !ok {
		return nil, fmt.Errorf("goal %s not found in session %s", goalID, s.ID)
	}
	sec := s.sections[entry.sectionID]
	leaf := entry.node
	concl := leaf.Goal.Conclusion()
	if locals := sectionLocalFrees(sec.root.Goal, concl); len(locals) > 0 {
		return nil, fmt.Errorf("defer: the leaf mentions the section-local variable(s) %s — "+
			"assert the ∀-closed statement first, then defer its claim leaf",
			strings.Join(locals, ", "))
	}
	statement := cardStatement(concl)
	key := registry.KeyOf(statement)
	if trivial, _ := prop.Normalize(prop.MakeProp(sec.root.Goal.Conclusion(), append(sec.root.Goal.Hyps(), concl)...)); trivial.Conclusion().Equals(ext.T) {
		return nil, errors.New("defer: the card states the section's own conclusion — " +
			"this leaf is the theorem itself, not a lemma of it")
	}
	door := s.Spelling()
	if !s.replaying {
		if stated, ok := registry.ByKey(string(key)); ok {
			status := "proved"
			if stated.IsCard() {
				status = "card"
			}
			c := sessionCard{key: key, statement: statement, name: name, entry: stated.Name, note: note, deps: deps}
			v := c.view(entry.sectionID, door)
			return &DeferResult{Status: status, StatedBy: []string{stated.Name}, Card: &v}, nil
		}
	}

	registered := path.Base(s.family.Name) + "." + name
	card := s.cards[registered]
	if card != nil && card.key != key {
		return nil, fmt.Errorf("defer: the name %s is taken in this session by the card stating %s — name this lemma otherwise",
			registered, strings.TrimPrefix(door.Prop(card.statement), "⊢ "))
	}
	if card == nil {
		if same := s.cardFor(string(key)); same != nil {
			card = same // the same lemma deferred twice is one card, under its first name
		}
	}
	own := registered
	if card != nil {
		own = card.entry
	}
	if err := s.cardDepCycle(own, deps); err != nil {
		return nil, err
	}
	// The lineage records a defer that changes what the session holds —
	// a card minted, a card a section newly stands on, deps a card
	// gains — so that a resume, which re-issues it, holds the same.
	changed := false
	if card == nil {
		card = &sessionCard{
			key:       key,
			statement: statement,
			name:      name,
			entry:     registered,
			note:      note,
			deps:      deps,
			axiom:     core.NewAxiom(statement.Conclusion()),
		}
		s.cards[registered] = card
		changed = true
	} else if grown := unionNames(card.deps, deps); len(grown) > len(card.deps) {
		card.deps = grown
		changed = true
	}
	if !slices.Contains(sec.deferred, card) {
		sec.deferred = append(sec.deferred, card)
		changed = true
	}
	if changed {
		s.recordDefer(goalID, entry.sectionID, card, deps)
	}

	if closeLeaf {
		if _, err := e.applyOnGoalLocked(ctx, s, goalID, TacticReq{Type: "lemma", LemmaKey: card.entry}); err != nil {
			return nil, fmt.Errorf("defer: citing the card %s did not close the leaf: %w — "+
				"assert the ∀-closed statement first and defer its claim leaf", card.entry, err)
		}
		if _, open := s.goalIndex[goalID]; open {
			return nil, fmt.Errorf("defer: ENGINE FAULT — citing the card %s left the leaf %s open; the card states the leaf's closure",
				card.entry, goalID)
		}
	}

	v := card.view(entry.sectionID, door)
	return &DeferResult{
		Status:        "deferred",
		OpenElsewhere: e.cardOpenElsewhere(s.ID, key),
		Card:          &v,
		Section:       sec.status(entry.sectionID, door),
		State:         s.buildStateView(),
	}, nil
}

// applyOnGoalLocked applies one tactic to an open goal as ApplyStep
// does — plan on a clone, commit, certify a cited entry's claim child,
// auto-pipeline, re-index, record — under the session lock, without
// the RPC's diagnostics and checkpoint. Returns the produced subgoals.
func (e *Engine) applyOnGoalLocked(ctx context.Context, s *Session, goalID string, tactic TacticReq) ([]ProducedSubgoal, error) {
	entry, ok := s.goalIndex[goalID]
	if !ok {
		return nil, fmt.Errorf("goal %s not found", goalID)
	}
	plan, err := e.applyTacticOnClone(ctx, s, entry.node.Goal, tactic)
	s.pendingApplyDiagnostics, s.pendingAutoMatched = nil, nil
	if err != nil {
		return nil, err
	}
	inputGoal := entry.node.Goal
	if !entry.node.Commit(plan) {
		return nil, fmt.Errorf("goal %s is not an open leaf", goalID)
	}
	s.certifyCitedEntry(tactic)
	s.runAutoPipeline()
	s.pendingApplyDiagnostics = nil
	s.rebuildGoalIndex()
	produced := s.collectProducedSubgoals(entry.node, entry.sectionID, inputGoal)
	s.recordApply(&ApplyStepRequest{GoalID: goalID, Tactic: tactic}, entry.sectionID, classifyEffect(produced), false, "", "")
	s.recordProvedSections()
	return produced, nil
}

// certifyCitedEntry closes the claim child a `lemma` / `lean_rw` cite
// leaves: `⊢ <the cited statement>` (at the instance the install
// adapted to) closes through the type-instance channel against what
// the author named — a registry entry by its own key or registered
// name, or a card this session minted — whichever spelling named it.
func (s *Session) certifyCitedEntry(tactic TacticReq) []AutoMatchedGoal {
	if tactic.LemmaKey == "" || (tactic.Type != "lemma" && tactic.Type != "lean_rw") {
		return nil
	}
	if lemmaEntry, ok := registryEntry(tactic.LemmaKey); ok {
		return s.runAutoMatchTypeInstance(core.PropKey(tactic.LemmaKey), lemmaEntry.Statement().Prop, []string{lemmaEntry.Name})
	}
	if card := s.cardFor(tactic.LemmaKey); card != nil {
		return s.runAutoMatchTypeInstance(card.key, card.statement, []string{card.entry})
	}
	return nil
}
