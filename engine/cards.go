// cards.go — the `cards` view: the cards the session store knows of,
// a card being a member stated without a proof (registry.Family.Card),
// served as an axiom until its proof lands. A lineage knows a card two
// ways: it minted the card with `defer` (its parent), or its target
// states the card (its attacker). The corpus's own cards — who stands
// on each, the cheap order to fill them in — are `query cards`
// (library/index); this view reads the registry only to tell a landed
// card from one minted and emitted nowhere yet, and carddata for a
// landed card's generated spellings.
//
// A card's identity is its statement's normalized key, so a lemma
// deferred from two lineages, or minted in one and landed from
// another, is one card. A card an entry PROVES is no card any more and
// leaves the view by itself: filling a card is replacing its Card
// build by a proof, in place, and nothing downstream changes.

package engine

import (
	"fmt"
	"os"
	"path"
	"path/filepath"
	"slices"
	"sort"
	"sync"

	json "encoding/json/v2"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/carddata"
	"github.com/euc-ai/xugo/library/registry"
)

// CardsRequest filters the view: Lineage restricts to the cards one
// lineage minted or attacks; Key to one card. Both empty: every card
// the session store knows of.
type CardsRequest struct {
	Lineage string `json:"lineage,omitempty"`
	Key     string `json:"key,omitempty"`
}

// CardsResult is the view: the cards, by registered name, and the
// declarations the view could not read.
type CardsResult struct {
	Cards    []CardView `json:"cards"`
	Problems []string   `json:"problems,omitempty"`
}

// CardView is one card.
type CardView struct {
	Key string `json:"key"`
	// Name is the bare member name; Entry the registered name — the
	// spelling a cite uses and the entry var the card lands as.
	Name   string `json:"name"`
	Entry  string `json:"entry"`
	Family string `json:"family,omitempty"`
	Note   string `json:"note,omitempty"`
	// Deps are the registered names of the members the card says it
	// stands on — what its proof will cite: a landed card's Deps, or
	// every name the defers that minted it gave.
	Deps      []string `json:"deps,omitempty"`
	Statement string   `json:"statement"`
	// StatementTyped is the parse-faithful spelling — paste it into
	// `add-goal {text}` to attack the card. Present when the print →
	// parse → key round-trip closes (FormatStatementTyped); absent
	// means the card must be restated by hand from Statement.
	StatementTyped string `json:"statement_typed,omitempty"`
	// Abbreviations are the names Statement spells as «Name», each
	// with the term it stands for, as the card's author declared them.
	// A landed card is attacked with them: `add-goal {entry: <Entry>}`
	// states it as its author did, abbreviations included.
	Abbreviations dsl.Abbrev `json:"abbreviations,omitempty"`
	// Landed says the card is a registry entry; a card not landed was
	// minted by a lineage (Parents) and emitted nowhere yet.
	Landed bool `json:"landed"`
	// Parents are the lineage sections that minted the card and are
	// not landed.
	Parents    []CardParentView `json:"parents,omitempty"`
	AttackedBy []CardAttackView `json:"attacked_by,omitempty"`
}

// CardParentView is a lineage section standing on a card it minted.
type CardParentView struct {
	Lineage   string `json:"lineage"`
	Section   int    `json:"section"`
	Statement string `json:"statement"`
}

// CardAttackView is a lineage whose target states the card.
type CardAttackView struct {
	Lineage string `json:"lineage"`
	Section int    `json:"section"`
}

// --- the index ---

type cardParent struct {
	lineage   string
	section   int
	statement string
}

type cardAttack struct {
	lineage string
	section int
}

type cardRecord struct {
	key            core.PropKey
	name, entry    string
	family         string
	note           string
	deps           []string
	statement      string
	statementTyped string
	abbreviations  dsl.Abbrev
	landed         *registry.ProofEntry
	parents        []cardParent
	attackers      []cardAttack
}

type cardIndex struct {
	cards    map[core.PropKey]*cardRecord
	problems []string
}

func (ix *cardIndex) card(key core.PropKey) *cardRecord {
	c, ok := ix.cards[key]
	if !ok {
		c = &cardRecord{key: key}
		ix.cards[key] = c
	}
	return c
}

// sectionSim is a section as the transcript walk sees it.
type sectionSim struct {
	statement string
	key       core.PropKey
	deferred  []LineageDefer
}

func cloneSections(secs []sectionSim) []sectionSim {
	out := make([]sectionSim, len(secs))
	for i, s := range secs {
		out[i] = sectionSim{statement: s.statement, key: s.key, deferred: append([]LineageDefer(nil), s.deferred...)}
	}
	return out
}

// walkLineage replays a transcript's section bookkeeping: add-goals
// open sections, checkpoints snapshot the list, restores roll it back,
// defers attach the cards the section minted. Also returns the family
// the lineage bound.
func walkLineage(l *sessionLineage) ([]sectionSim, string) {
	var secs []sectionSim
	family := ""
	snapshots := map[string][]sectionSim{}
	for _, ev := range l.Events {
		switch ev.Kind {
		case kindFamily:
			if ev.Family != nil {
				family = ev.Family.Name
			}
		case kindAddGoal:
			if ev.Goal == nil {
				continue
			}
			// The section's identity is its statement's normalized key
			// — what a landed member's own key is, and what a card is
			// keyed by.
			key := core.PropKey(ev.Goal.NormKey)
			for len(secs) < ev.Goal.Section {
				secs = append(secs, sectionSim{})
			}
			secs = append(secs, sectionSim{statement: ev.Goal.Statement, key: key})
		case kindApply:
			if ev.Apply != nil && ev.Apply.AutoCheckpoint != "" {
				snapshots[ev.Apply.AutoCheckpoint] = cloneSections(secs)
			}
		case kindCheckpoint:
			if ev.Checkpoint != nil {
				snapshots[ev.Checkpoint.ID] = cloneSections(secs)
			}
		case kindRestore:
			if ev.Restore != nil {
				if snap, ok := snapshots[ev.Restore.CheckpointID]; ok {
					secs = cloneSections(snap)
				}
			}
		case kindDefer:
			if ev.Defer != nil && ev.Defer.Section >= 0 && ev.Defer.Section < len(secs) {
				secs[ev.Defer.Section].deferred = append(secs[ev.Defer.Section].deferred, *ev.Defer)
			}
		}
	}
	return secs, family
}

// lineageCardDeps is, per card, every dep the lineage's defers of it
// named, a restore notwithstanding: a session's cards outlive a
// restore, and so do the deps they stand on.
func lineageCardDeps(l *sessionLineage) map[core.PropKey][]string {
	out := map[core.PropKey][]string{}
	for _, ev := range l.Events {
		if ev.Kind == kindDefer && ev.Defer != nil {
			key := core.PropKey(ev.Defer.Key)
			out[key] = unionNames(out[key], ev.Defer.Deps)
		}
	}
	return out
}

// readLineages loads every persisted transcript.
func readLineages(sessionStore string) ([]*sessionLineage, error) {
	if sessionStore == "" {
		return nil, nil
	}
	dirs, err := os.ReadDir(sessionStore)
	if err != nil {
		if os.IsNotExist(err) {
			return nil, nil
		}
		return nil, fmt.Errorf("cards: %w", err)
	}
	var out []*sessionLineage
	for _, dir := range dirs {
		if !dir.IsDir() {
			continue
		}
		data, rerr := os.ReadFile(filepath.Join(sessionStore, dir.Name(), lineageFileName))
		if rerr != nil {
			continue
		}
		var l sessionLineage
		if json.Unmarshal(data, &l) != nil || l.ID == "" {
			continue
		}
		out = append(out, &l)
	}
	return out, nil
}

// indexLandedCards reads the registry's cards. A card with no generated
// text whose statement cannot be read is reported, not indexed.
func indexLandedCards(ix *cardIndex) {
	for _, entry := range registry.All() {
		if !entry.IsCard() {
			continue
		}
		if err := readCard(ix, entry); err != nil {
			ix.problems = append(ix.problems, err.Error())
		}
	}
}

func readCard(ix *cardIndex, entry *registry.ProofEntry) error {
	r := landedCardOf(entry)
	if r.err != nil {
		return r.err
	}
	c := ix.card(r.key)
	c.landed = entry
	c.name, c.entry, c.family, c.note = entry.BareName(), entry.Name, entry.Family().Name, entry.CardNote()
	var deps []string
	for _, d := range entry.DepEntries() {
		deps = append(deps, d.Name)
	}
	c.deps = deps
	c.statement, c.statementTyped = r.statement, r.statementTyped
	c.abbreviations = entry.Abbreviations()
	return nil
}

// _LandedCard is what reading a registry card computes: its key and
// its two spellings, or why it could not be read.
type _LandedCard struct {
	key                       core.PropKey
	statement, statementTyped string
	err                       error
}

// landedCards memoizes readings for cards with no matching generated
// text, including cards registered during a session or a test. Corpus
// cards read carddata directly; TestCardDataCurrent holds it current.
var landedCards sync.Map // *registry.ProofEntry → _LandedCard

func landedCardOf(entry *registry.ProofEntry) (r _LandedCard) {
	if text, ok := carddata.Lookup(entry.Name, entry.Key); ok {
		return _LandedCard{key: core.PropKey(entry.Key), statement: text.Statement, statementTyped: text.StatementTyped}
	}
	if v, ok := landedCards.Load(entry); ok {
		return v.(_LandedCard)
	}
	defer func() {
		if p := recover(); p != nil {
			r = _LandedCard{err: fmt.Errorf("%s: %v", entry.Name, p)}
		}
		landedCards.Store(entry, r)
	}()
	st := entry.Statement()
	r.key = st.Key()
	r.statement = entry.StatementText()
	r.statementTyped = EntryStatementTyped(entry)
	return r
}

// CardStatementTyped is a landed card's parse-faithful spelling: its
// generated text while that is current, computed otherwise; empty where
// the print does not round-trip (FormatStatementTyped). A card whose
// statement cannot be read panics, as reading it anywhere else does.
func CardStatementTyped(entry *registry.ProofEntry) string {
	r := landedCardOf(entry)
	if r.err != nil {
		panic(r.err.Error())
	}
	return r.statementTyped
}

// readCardIndex builds the index: the registry's cards, then the
// session store's minted cards and attackers.
func readCardIndex(sessionStore string) (*cardIndex, error) {
	ix := &cardIndex{cards: map[core.PropKey]*cardRecord{}}
	indexLandedCards(ix)
	if err := indexLineageCards(sessionStore, ix); err != nil {
		return nil, err
	}
	return ix, nil
}

// indexLineageCards reads the session store into the index: the cards
// each lineage minted, with the lineage as a parent, and the attackers
// of every card the index holds.
func indexLineageCards(sessionStore string, ix *cardIndex) error {
	lineages, err := readLineages(sessionStore)
	if err != nil {
		return err
	}
	walked := make([][]sectionSim, len(lineages))
	for i, l := range lineages {
		var family string
		walked[i], family = walkLineage(l)
		deps := lineageCardDeps(l)
		for s, sec := range walked[i] {
			for _, d := range sec.deferred {
				key := core.PropKey(d.Key)
				// A card a proved entry states is discharged: the lineage
				// cites the member now, there is nothing open.
				if stated, ok := registry.ByKey(string(key)); ok && !stated.IsCard() {
					continue
				}
				c := ix.card(key)
				if c.landed == nil && c.name == "" {
					c.name, c.note, c.statement, c.statementTyped, c.family = d.Name, d.Note, d.Statement, d.StatementTyped, family
					c.entry = d.Entry
					if c.entry == "" && family != "" {
						c.entry = path.Base(family) + "." + d.Name
					}
				}
				if c.landed == nil {
					c.deps = unionNames(c.deps, deps[key])
				}
				parent := cardParent{lineage: l.ID, section: s, statement: sec.statement}
				if !slices.Contains(c.parents, parent) {
					c.parents = append(c.parents, parent)
				}
			}
		}
	}
	// Attackers: every section whose target states a card.
	for i, l := range lineages {
		for s, sec := range walked[i] {
			if sec.key == "" {
				continue
			}
			if c, ok := ix.cards[sec.key]; ok {
				c.attackers = append(c.attackers, cardAttack{lineage: l.ID, section: s})
			}
		}
	}
	return nil
}

// cardOpenElsewhere lists the other lineages that minted the card and
// have not landed it. It reads the session store alone: a card's
// parents are the lineages that minted it, and the registry adds none.
func (e *Engine) cardOpenElsewhere(selfID string, key core.PropKey) []string {
	ix := &cardIndex{cards: map[core.PropKey]*cardRecord{}}
	if err := indexLineageCards(e.sessionStore, ix); err != nil {
		return nil
	}
	c, ok := ix.cards[key]
	if !ok {
		return nil
	}
	var ids []string
	seen := map[string]bool{}
	for _, p := range c.parents {
		if p.lineage != selfID && !seen[p.lineage] {
			seen[p.lineage] = true
			ids = append(ids, p.lineage)
		}
	}
	return ids
}

// Cards renders the cards with the engine's persisted session lineages.
func (e *Engine) Cards(req *CardsRequest) (*CardsResult, error) {
	return ViewCards(e.sessionStore, req)
}

// ViewCards reads the persisted lineages under sessionStore, and the
// registry for the cards they name, without constructing a proof
// engine. An empty store knows of no card. Session transcripts are
// read afresh on each call; generated corpus texts are shared by the
// CLI and the server.
func ViewCards(sessionStore string, req *CardsRequest) (*CardsResult, error) {
	if req == nil {
		req = &CardsRequest{}
	}
	ix, err := readCardIndex(sessionStore)
	if err != nil {
		return nil, err
	}
	result := &CardsResult{Cards: []CardView{}, Problems: ix.problems}

	for key, c := range ix.cards {
		if len(c.parents) == 0 && len(c.attackers) == 0 {
			continue
		}
		if req.Key != "" && req.Key != string(key) {
			continue
		}
		if req.Lineage != "" {
			touches := false
			for _, p := range c.parents {
				if p.lineage == req.Lineage {
					touches = true
				}
			}
			for _, a := range c.attackers {
				if a.lineage == req.Lineage {
					touches = true
				}
			}
			if !touches {
				continue
			}
		}
		cv := CardView{Key: string(key), Name: c.name, Entry: c.entry, Family: c.family, Note: c.note, Deps: c.deps,
			Statement: c.statement, StatementTyped: c.statementTyped, Abbreviations: c.abbreviations, Landed: c.landed != nil}
		for _, p := range c.parents {
			cv.Parents = append(cv.Parents, CardParentView{Lineage: p.lineage, Section: p.section, Statement: p.statement})
		}
		for _, a := range c.attackers {
			cv.AttackedBy = append(cv.AttackedBy, CardAttackView{Lineage: a.lineage, Section: a.section})
		}
		result.Cards = append(result.Cards, cv)
	}
	sort.Slice(result.Cards, func(i, j int) bool {
		a, b := result.Cards[i], result.Cards[j]
		if a.Entry != b.Entry {
			return a.Entry < b.Entry
		}
		return a.Key < b.Key
	})
	return result, nil
}
