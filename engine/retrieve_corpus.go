package engine

// retrieve_corpus.go — the proof registry read as a lemma index.
//
// `retrieve` answers from the corpus: every member reachable by name
// from `by` / `lemma` / `known` is reachable by discovery too. By goal,
// the members that APPLY: read by the apply rung's own plan
// (proof.StatedHead.Read), so a member listed here is one `by` fires as a
// named premise up to the kernel's spelling of the instance, reported
// with the witnesses the goal pins and each premise's status (resident
// in the context, stated by a proved entry, stated by a card — a
// member without a proof yet — or open, to be supplied before the
// by); and the members whose
// statement IS the goal — exact, by key, through the entry's own key.
// By constants, by name and by dependency the registry answers
// directly.
//
// No index over the members. The registry is scanned, deadline-bounded,
// and the reading of one member is a first-order match over its
// statement as read (registry.Statement — read once per process, every
// member's at engine construction, the constants it spells with it)
// and never over its key: normalizing is the expensive half of a
// member's elaboration, and a scan that asked each member's key would
// normalize the whole corpus on the first request. A key is asked of
// the hits alone. A path index could not do this work anyway: a
// schema-skeleton walker reads a normalized clause (`¬A ∨ B` — every
// structure law) as ONE atom, and a bare-variable side of any equation
// covers every equality goal, so the true hit ties with unrelated
// statements. Matching is exact where path coverage is a heuristic;
// a scan earns an index when it stops being cheap, which the readings
// below have: they are many times the members, so the view keeps them
// by the rigid heads of the conclusions the plan reads them at, and a
// goal reads the ones at its own head and the wild ones
// (registry.ReadablesFor) — the rest the plan declines before anything
// else. Members and readings alike
// are read from a form prepared once, off the request path
// (proof.StatedHead: the statement's at construction, the reading's in
// the walk), which declines, before any instance is enumerated, a
// conclusion whose typed skeleton the goal's does not carry and a form
// whose binders neither the goal's hypotheses nor the corpus's facts
// could pin. A law stated at a structure record (`∀R:comm_ring(A).
// R.zero * x = R.zero`) meets a goal at an instance (`&0 * x = &0` on
// ℝ) through the record the instance's fact supplies
// (`real_ring.CommRing`): the pre-read reads its projections at the
// record values the facts and the hypotheses offer, and the plan pins
// the record from that fact before it matches the conclusion, read at
// the record in the instance normal form.
//
// A second group answers by goal from what no member states: the laws
// readable through a PROJECTION (registry.Readables — a law of one
// structure whose body states another, read at a fact of the first).
// "A ring homomorphism keeps zero" is `group_homomorphism.MapOne` read
// at `ring_homomorphism.AdditiveHomomorphism`, which the constitution's
// §Readings says is cited where it is used and never written as a
// member; the kernel-derived statement of every such reading is
// scanned by the same plan, after the members, the candidates the
// view's head index serves at the goal, and a hit is reported as the
// law with the chain and both spellings of the value.

import (
	"fmt"
	"slices"
	"sort"
	"strings"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/unify"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// The corpus group's vocabulary on the wire.
const (
	retrieveCorpus           = "corpus"
	retrieveCorpusReadings   = "corpus_readings"
	retrieveCorpusDeps       = "corpus_deps"
	retrieveCorpusDependents = "corpus_dependents"

	corpusMatchExact = "exact"
	corpusMatchApply = "apply"

	premiseResident = "resident"
	premiseEntry    = "entry"
	premiseCard     = "card"
	premiseOpen     = "open"
)

// goalScan is what the two goal groups read a goal through: the goal
// itself, the goal opened as `by`'s conditioning opens it before the
// rung and prepared to be read against the heads with the corpus's
// bare facts (proof.HeadGoalOf), and those facts; truncated says the
// facts were gathered under a deadline that ran out.
type goalScan struct {
	goal, opened core.Prop
	facts        *proof.FactSource
	headGoal     *proof.HeadGoal
	truncated    bool
}

// scanGoal opens the goal and gathers the facts once for both groups.
func scanGoal(goal core.Prop, deadline time.Time) goalScan {
	facts, truncated := corpusFacts(deadline)
	opened := openGoal(goal)
	return goalScan{goal: goal, opened: opened, facts: facts, headGoal: proof.HeadGoalOf(opened, facts), truncated: truncated}
}

// corpusByGoal is the corpus group of `retrieve goal`: the members
// whose statement is the goal (by key, over the goal's stronger
// variants), then the members that apply to it. Ranked exact first,
// then by unsupplied premises (open, or stated only by a card)
// ascending, then by name; capped at limit.
func corpusByGoal(scan goalScan, limit int, deadline time.Time) (RetrieveGroup, bool) {
	goal := scan.goal
	g := RetrieveGroup{MatchedVia: retrieveCorpus}
	seen := map[*registry.ProofEntry]bool{}
	var hits []RetrieveEntry

	cache := &prop.PreCNFCache{}
	for _, v := range proof.StrongerGoals(goal) {
		normalized, _ := cache.Normalize(v)
		// A variant the normalizer absorbs to ⊤ is closed by normalization,
		// not by any member: an entry that happens to carry the ⊤ key (a
		// tautological statement) is no exact hit for it.
		if normalized.NumHyps() == 0 && normalized.Conclusion().Equals(ext.T) {
			continue
		}
		entry, ok := entryByKey(string(normalized.AlphaKey()))
		if !ok || seen[entry] {
			continue
		}
		seen[entry] = true
		re := corpusEntry(entry)
		re.Match = corpusMatchExact
		hits = append(hits, re)
	}

	// The rung reads a bare conclusion over split hypotheses: the goal
	// is opened first, as `by`'s conditioning opens it before the rung.
	g.Truncated = scan.truncated
	for _, entry := range registry.All() {
		if time.Now().After(deadline) {
			g.Truncated = true
			break
		}
		if seen[entry] {
			continue
		}
		reading, ok := entry.Statement().Head().Read(scan.headGoal)
		if !ok {
			continue
		}
		seen[entry] = true
		re := corpusEntry(entry)
		re.Match = corpusMatchApply
		fillHeadReading(&re, reading)
		hits = append(hits, re)
	}

	sort.SliceStable(hits, func(a, b int) bool {
		if (hits[a].Match == corpusMatchExact) != (hits[b].Match == corpusMatchExact) {
			return hits[a].Match == corpusMatchExact
		}
		if ua, ub := unsupplied(hits[a]), unsupplied(hits[b]); ua != ub {
			return ua < ub
		}
		return hits[a].Entry < hits[b].Entry
	})
	if len(hits) > limit {
		hits, g.Truncated = hits[:limit], true
	}
	g.Entries = hits
	return g, len(hits) > 0
}

// fillHeadReading reports what the rung's plan read: the binders it
// pinned and each antecedent at them with its status.
func fillHeadReading(re *RetrieveEntry, reading *proof.HeadReading) {
	for _, w := range reading.Witnesses {
		re.Witnesses = append(re.Witnesses, RetrieveWitness{Binder: w.Binder, Term: ext.PrintTerm(w.Witness)})
	}
	for _, p := range reading.Premises {
		re.Premises = append(re.Premises, corpusPremise(p.Term, p.Resident))
	}
}

// unsupplied counts the premises the rung would need supplied: the
// open ones and the ones only a card states.
func unsupplied(re RetrieveEntry) int {
	n := 0
	for _, p := range re.Premises {
		if p.Status == premiseOpen || p.Status == premiseCard {
			n++
		}
	}
	return n
}

// corpusReadings is the readings group of `retrieve goal`: the laws
// readable through a projection whose derived statement applies to
// the goal, read by the same plan as a member's. Each hit is the law,
// what the reading states, the premises — the first the structure
// fact the chain is read at — and the chain with both spellings of
// the value. Ranked by unsupplied premises ascending, then by chain
// length, then by the law's name; capped at limit. The derived
// statements are the registry's view, computed once per process in
// the background from the engine's construction and read at the
// opened goal's head; a request that arrives before the view is there
// does not wait for it, and reports the group truncated and empty.
func corpusReadings(scan goalScan, limit int, deadline time.Time) (RetrieveGroup, bool) {
	g := RetrieveGroup{MatchedVia: retrieveCorpusReadings, Truncated: scan.truncated}
	readables, ready := registry.ReadablesForIfReady(scan.opened.Conclusion())
	if !ready {
		g.Truncated = true
		return g, true
	}
	type hit struct {
		entry RetrieveEntry
		depth int
	}
	var hits []hit
	for _, r := range readables {
		if time.Now().After(deadline) {
			g.Truncated = true
			break
		}
		reading, ok := r.Head().Read(scan.headGoal)
		if !ok {
			continue
		}
		re := corpusEntry(r.Law)
		re.Match = corpusMatchApply
		re.Card = r.StandsOnCard()
		re.Statement = r.Root().Family().SpellStatement(r.Statement)
		fillHeadReading(&re, reading)
		re.Reading = readingSpellings(scan.goal, r, reading)
		hits = append(hits, hit{re, r.Depth()})
	}
	sort.SliceStable(hits, func(a, b int) bool {
		if ua, ub := unsupplied(hits[a].entry), unsupplied(hits[b].entry); ua != ub {
			return ua < ub
		}
		if hits[a].depth != hits[b].depth {
			return hits[a].depth < hits[b].depth
		}
		return hits[a].entry.Entry < hits[b].entry.Entry
	})
	if len(hits) > limit {
		hits, g.Truncated = hits[:limit], true
	}
	for _, h := range hits {
		g.Entries = append(g.Entries, h.entry)
	}
	return g, len(g.Entries) > 0
}

// readingSpellings spells a readable law's value at the goal: the
// chain, the Go `Law.Read(Pₙ.Read(… P₁.Read(instance)))` and the
// session `read_at`. The instance is the premise the rung read for
// the root structure's fact: a hypothesis of the goal is named by
// index, a bare fact a member states by that entry, and a fact the
// goal holds only opened, or not at all, leaves the session spelling
// out and is written `ResidentHyp(<fact>)` in Go.
func readingSpellings(goal core.Prop, r registry.Readable, reading *proof.HeadReading) *RetrieveReading {
	root, _ := registry.ProjectionOf(r.Root())
	spelled := &RetrieveReading{}
	for _, p := range r.Through {
		spelled.Through = append(spelled.Through, p.Name)
	}
	var fact core.Term
	for _, p := range reading.Premises {
		if head, ok := unify.SpineHeadConst(p.Term); ok && string(head) == root.From {
			fact = p.Term
			break
		}
	}
	if fact == nil {
		panic(fmt.Sprintf("retrieve: the reading of %s through %v read no premise stating %s", r.Law.Name, spelled.Through, root.From))
	}
	instance := fmt.Sprintf("ResidentHyp(%s)", ext.PrintTerm(fact))
	var at *ReadAtSpec
	if idx, ok := hypIndex(goal, fact); ok {
		at = &ReadAtSpec{HypIndex: &idx}
	} else if premise := corpusPremise(fact, false); premise.Entry != "" {
		at, instance = &ReadAtSpec{Key: premise.Entry}, premise.Entry
	}
	value := instance
	for _, p := range r.Through {
		value = p.Name + ".Read(" + value + ")"
		if at != nil {
			at = &ReadAtSpec{Key: p.Name, ReadAt: at}
		}
	}
	spelled.Go = r.Law.Name + ".Read(" + value + ")"
	spelled.ReadAt = at
	return spelled
}

// hypIndex finds a term among the goal's hypotheses, up to α.
func hypIndex(goal core.Prop, t core.Term) (int, bool) {
	for i, h := range goal.Hyps() {
		if h.AlphaEquals(t) {
			return i, true
		}
	}
	return 0, false
}

// corpusPremise reports one instantiated antecedent as the rung would
// need it: resident in the context; else, when closed, stated by an
// entry found by key — the `by` premise that supplies it, a card when
// that entry has no proof yet; else open.
func corpusPremise(a core.Term, resident bool) RetrievePremise {
	p := RetrievePremise{Statement: ext.PrintTerm(a), Status: premiseOpen}
	if resident {
		p.Status = premiseResident
		return p
	}
	if len(a.Frees(nil)) == 0 {
		normalized, _ := prop.Normalize(prop.MakeProp(a))
		if entry, ok := entryByKey(string(normalized.AlphaKey())); ok {
			p.Status, p.Entry = premiseEntry, entry.Name
			if entry.IsCard() {
				p.Status = premiseCard
			}
		}
	}
	return p
}

// corpusEntry is the wire view of a member: its registered name (what
// the key slot takes), its chapter, its own key, its statement, and
// whether it is a card.
func corpusEntry(entry *registry.ProofEntry) RetrieveEntry {
	st := entry.Statement()
	re := RetrieveEntry{
		Key:           string(st.Key()),
		Entry:         entry.Name,
		Family:        entry.Family().Name,
		Card:          entry.IsCard(),
		Statement:     entry.StatementText(),
		Abbreviations: entry.Abbreviations(),
	}
	return re
}

// dependentsOf is the registry's dependency graph reversed: for each
// entry, the entries whose dependencies (DepEntries) include it.
func dependentsOf() map[*registry.ProofEntry][]*registry.ProofEntry {
	dependents := map[*registry.ProofEntry][]*registry.ProofEntry{}
	for _, entry := range registry.All() {
		for _, d := range entry.DepEntries() {
			dependents[d] = append(dependents[d], entry)
		}
	}
	return dependents
}

// corpusFacts is the FactSource the reading is handed: the corpus's
// bare facts — hyp-free members whose statement has no leading ∀ and
// no free variable (the structure instances above all), by head
// constant, with the heads that are structure predicates marked — each
// matched against an antecedent piece at the bindings so far, and a
// structure fact offering the type instance a head's antecedent takes
// at it. A member stated over declared free variables is not a fact:
// its variables are nobody's witnesses. The member that supplied a binding is not remembered here:
// the instantiated premise finds it again by key (corpusPremise),
// which is also what reports it. Deadline-bounded like the pass it
// feeds: past the deadline the facts gathered so far are the source,
// and the scan reports itself truncated.
func corpusFacts(deadline time.Time) (*proof.FactSource, bool) {
	facts := &proof.FactSource{ByHead: map[core.TermName][]core.Term{}, Structures: map[core.TermName]bool{}}
	truncated := false
	for _, entry := range registry.All() {
		if time.Now().After(deadline) {
			truncated = true
			break
		}
		st := entry.Statement().Prop
		c := st.Conclusion()
		if st.NumHyps() > 0 || !ext.MatchesFORALL(c).IsZero() || len(c.Frees(nil)) > 0 {
			continue
		}
		head, ok := unify.SpineHeadConst(c)
		if !ok {
			continue
		}
		facts.ByHead[head] = append(facts.ByHead[head], c)
		if registry.IsStructurePredicate(string(head)) {
			facts.Structures[head] = true
		}
	}
	return facts, truncated
}

// openGoal opens a goal the way `by`'s conditioning opens it before
// the rung: leading ∀-binders freed, leading antecedents made
// hypotheses, conjunctive hypotheses split, repeatedly.
func openGoal(goal core.Prop) core.Prop {
	w, _ := prop.WrapProp(goal).StripConclForAll()
	for {
		ante, rest, ok := ext.MatchesIMPLY(w.Conclusion())
		if !ok {
			break
		}
		hyps := append([]core.Term{}, w.Hyps()...)
		w = prop.MakeProp(rest, append(hyps, ante)...)
		w, _ = w.StripConclForAll()
	}
	var split []core.Term
	for _, h := range w.Hyps() {
		split = append(split, conjuncts(h)...)
	}
	if len(split) == w.NumHyps() {
		return w
	}
	return prop.MakeProp(w.Conclusion(), split...)
}

// conjuncts flattens a ∧-spine.
func conjuncts(t core.Term) []core.Term {
	if a, b, ok := ext.MatchesAND(t); ok {
		return append(conjuncts(a), conjuncts(b)...)
	}
	return []core.Term{t}
}

// corpusByConsts lists the members whose statement spells every named
// constant (registry.Statement.Constants — read with the statement, no
// key asked), the ones spelling the fewest others first.
func corpusByConsts(consts []string, limit int) (RetrieveGroup, bool) {
	g := RetrieveGroup{MatchedVia: retrieveCorpus}
	type scored struct {
		entry *registry.ProofEntry
		extra int
	}
	var hits []scored
	for _, entry := range registry.All() {
		spelled := entry.Statement().Constants()
		all := true
		for _, c := range consts {
			if !slices.Contains(spelled, core.TermName(c)) {
				all = false
				break
			}
		}
		if !all {
			continue
		}
		hits = append(hits, scored{entry, len(spelled) - len(consts)})
	}
	sort.Slice(hits, func(a, b int) bool {
		if hits[a].extra != hits[b].extra {
			return hits[a].extra < hits[b].extra
		}
		return hits[a].entry.Name < hits[b].entry.Name
	})
	for _, h := range hits {
		if len(g.Entries) >= limit {
			g.Truncated = true
			break
		}
		g.Entries = append(g.Entries, corpusEntry(h.entry))
	}
	return g, len(g.Entries) > 0
}

// corpusByName lists the members whose registered name contains the
// pattern, case-insensitively, in name order.
func corpusByName(pattern string, limit int) (RetrieveGroup, bool) {
	g := RetrieveGroup{MatchedVia: retrieveCorpus}
	needle := strings.ToLower(pattern)
	var matched []*registry.ProofEntry
	for _, entry := range registry.All() {
		if strings.Contains(strings.ToLower(entry.Name), needle) {
			matched = append(matched, entry)
		}
	}
	sort.Slice(matched, func(a, b int) bool { return matched[a].Name < matched[b].Name })
	for _, entry := range matched {
		if len(g.Entries) >= limit {
			g.Truncated = true
			break
		}
		g.Entries = append(g.Entries, corpusEntry(entry))
	}
	return g, len(g.Entries) > 0
}

// corpusRelated answers `related_to` for a member named by entry name
// or key: the entries it cites and the entries citing it, one hop
// each, from the registry's own dependency graph.
func corpusRelated(keyOrName string, limit int) []RetrieveGroup {
	entry, ok := registryEntry(keyOrName)
	if !ok {
		return nil
	}
	var groups []RetrieveGroup
	list := func(via string, entries []*registry.ProofEntry) {
		g := RetrieveGroup{MatchedVia: via}
		for _, e := range entries {
			if len(g.Entries) >= limit {
				g.Truncated = true
				break
			}
			g.Entries = append(g.Entries, corpusEntry(e))
		}
		if len(g.Entries) > 0 {
			groups = append(groups, g)
		}
	}
	list(retrieveCorpusDeps, entry.DepEntries())
	list(retrieveCorpusDependents, dependentsOf()[entry])
	return groups
}
