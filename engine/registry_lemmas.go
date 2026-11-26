// Registry lemma resolution: the proof registry (library/registry) is
// the ONLY source a session cites.
//
// The registry is an in-process, package-init-populated lookup
// surface: every family member registers a parse-only Stmt alongside
// its Build. A key slot resolves an entry by its own key (the
// statement's normalized key) or by its registered name. A registry
// hit is extractable by the replay harness (a cite of the entry, which
// its recording observes / registry-first name resolution); the served statement is the entry's own statement
// — the same form the harness's resolveDep and serve.EntryThm serve,
// so session and replay agree about a name's form (see registryLemma).
//
// Nothing else is admitted: a cite of a statement no member states
// would record a dep the corpus cannot replay. Nor is an entry a member
// of the session's family cannot name in Go (citeRefusal): its cite
// would export as a reference that does not compile.
//
// Registry population is a LINK-TIME property: the serve binary links
// the chapter aggregator (via library/integrity/manifest's blank
// import), and the engine test binary blank-imports it from the test
// file. An engine embedded without the corpus simply sees an empty
// registry — every lookup misses.

package engine

import (
	"errors"
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/registry"
)

// entryByKey resolves a key to the entry that answers for it: the
// entry's own key (registry.ProofEntry.Key — the statement's
// normalized key, what a session's key for the same statement
// coincides with for a monomorphic statement).
func entryByKey(key string) (*registry.ProofEntry, bool) {
	return registry.ByKey(key)
}

// registryEntry resolves keyOrName against the proof registry: by its
// own key first (see entryByKey), then by registered name (so an agent
// that knows the entry as nat_order.LessEqRefl cites it without the
// key). The library-theorem name an entry serves as (ProofEntry.ServesAs,
// the engine's by-name bootstrap convention) is not a cite spelling.
func registryEntry(keyOrName string) (*registry.ProofEntry, bool) {
	if e, ok := entryByKey(keyOrName); ok {
		return e, true
	}
	return registry.ByName(keyOrName)
}

// registryLemma is resolveLemma's registry channel. Returns ok=false
// when keyOrName is not a registry entry (the caller owns the miss
// diagnostic). On a hit it returns the entry's served statement, or the
// refusal of an entry the session's family cannot cite (citeRefusal).
//
// Served form: the entry's statement (registry ProofEntry.Statement)
// — the same form the replay harness's resolveDep and serve.EntryThm
// serve, so the session READS the form the entry's own file signs —
// binder names and order included. NOTE a BARE `by` premise installs in
// the closer's clause form — proof.ApplyByStep normalizes the statement
// for it, as the Go macro does for a named dep — while the SERVED form
// stays the headline (reading, σ/witness maps).
func (e *Engine) registryLemma(s *Session, keyOrName string) (core.Prop, error, bool) {
	entry, ok := registryEntry(keyOrName)
	if !ok {
		return nil, nil, false
	}
	if err := s.citeRefusal(entry); err != nil {
		return nil, err, true
	}
	return entry.Statement().Prop, nil, true
}

// citeRefusal refuses an entry a member of the session's family cannot
// cite (unreachableCite). nil for an unbound session, whose family is
// the export's: familyDepEntryForEmit refuses there.
func (s *Session) citeRefusal(entry *registry.ProofEntry) error {
	if s == nil || s.family == nil {
		return nil
	}
	if why := unreachableCite(entry, s.family.PackageDir(), s.family.Name); why != "" {
		return errors.New(why)
	}
	return nil
}

// unreachableCite says why a member of family, whose package is at dir,
// cannot cite entry, and is "" when it can. A member names each cite by
// its entry's Go reference, so an entry its package cannot reach
// (registry.ProofEntry.UnreachableFrom) is cited by no member that
// compiles. The text names the entries within the family's reach that
// entry stands on (reachableFoundation).
func unreachableCite(entry *registry.ProofEntry, dir, family string) string {
	why := entry.UnreachableFrom(dir)
	if why == "" {
		return ""
	}
	remedy := fmt.Sprintf("If other chapters need the fact, make it API of %s (chapter_constitution.md §\"Entries and dependencies\").",
		entry.Family().Name)
	if foundation := reachableFoundation(entry, dir); len(foundation) > 0 {
		remedy = fmt.Sprintf("It stands on %s, which %s can cite: cite that instead, or, if other chapters need the fact, "+
			"make it API of %s (chapter_constitution.md §\"Entries and dependencies\").",
			strings.Join(foundation, ", "), family, entry.Family().Name)
	}
	return fmt.Sprintf("%s: a member of %s cannot name it in Go, so no cite of it can be exported. %s", why, family, remedy)
}

// reachableFoundation lists, by registered name, the entries Go code at
// dir can cite that entry stands on: the entries its build reads, each
// one dir cannot cite replaced by the entries it reads in turn, in the
// order first reached.
func reachableFoundation(entry *registry.ProofEntry, dir string) []string {
	var out []string
	seen := map[*registry.ProofEntry]bool{entry: true}
	queue := entry.ServedDeps()
	for len(queue) > 0 {
		d := queue[0]
		queue = queue[1:]
		if seen[d] {
			continue
		}
		seen[d] = true
		if d.UnreachableFrom(dir) == "" {
			out = append(out, d.Name)
			continue
		}
		queue = append(queue, d.ServedDeps()...)
	}
	return out
}
