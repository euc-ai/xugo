// dag_test.go — structural integrity check for the registry dependency
// graph (built from the registry entries).
//
// Verifies the DAG is well-formed without running any proof's kernel
// verification:
//
// - no two entries claim the same key (no duplicate identity) or the
// same name
// - the graph has no cycles
//
// A dep is a typed entry reference, so a dangling dep is a compile
// error rather than a finding here.
//
// What this catches that TestReplayAll doesn't:
//
// - A cycle introduced by a careless re-prove (X cites Y while Y still
// cites X) — TestReplayAll's bounded force breaks at the trust
// frontier so a cycle there might not surface as a hang.
// - Two entries accidentally registered with the same key (e.g. a
// re-emit collision that didn't get noticed) — they would
// alias in the trust set and confuse downstream lookups.
//
// What this does NOT catch (out of scope, intentionally):
//
// - A proof body shortcuited with TestThm — TestThm is a documented
// kernel trust escape; auditing it belongs to `grep TestThm` review,
// not to an automatic check.
// - A broken proof body that compiles — its OWN t.Run catches it.
//
// Reads STATICALLY from the registry — every entry exposes its
// dependencies (DepEntries).
// No kernel work, no env setup, no Build calls; cheap.
package gates

import (
	"sort"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/library/registry"
)

func TestRegistryDAGIntegrity(t *testing.T) {
	// Index every entry by its own key and by its display name.
	type entry struct {
		id   string // "entry:NAME"
		name string
	}
	allEntries := registry.All()
	keyIndex := make(map[string]entry, len(allEntries))
	nameIndex := make(map[string]entry, len(allEntries))
	for _, e := range allEntries {
		ent := entry{id: "entry:" + e.Name, name: e.Name}
		if existing, dup := keyIndex[e.Key]; dup {
			t.Errorf("duplicate entry key %q: %s clashes with %s (two entries with the same key)", e.Key, ent.id, existing.id)
		}
		keyIndex[e.Key] = ent
		if existing, dup := nameIndex[e.Name]; dup {
			t.Errorf("duplicate entry name %q: %s clashes with %s", e.Name, ent.id, existing.id)
		}
		nameIndex[e.Name] = ent
	}
	// adj: entry id → list of dep entry ids.
	adj := make(map[string][]string, len(keyIndex))
	addEdge := func(from string, to entry) {
		adj[from] = append(adj[from], to.id)
	}

	// Entries: every edge is a dependency — a declared Dep, or an entry
	// a proof was recorded reading. A typed cite is compiler-checked
	// (import cycles across families, var-init cycles within one); a
	// read by a conventional name an entry serves (ServesAs) is not, so
	// the cycle scan below is the one check over the whole graph.
	for _, e := range allEntries {
		fromID := "entry:" + e.Name
		for _, dep := range e.DepEntries() {
			addEdge(fromID, nameIndex[dep.Name])
		}
	}

	// Cycle detection: iterative DFS with white/gray/black coloring.
	// A back-edge to a gray node closes a cycle; the stack reconstructs
	// the path for the error message.
	const (
		white = 0
		gray  = 1
		black = 2
	)
	color := make(map[string]int, len(adj))
	type frame struct {
		id  string
		idx int
	}
	dfs := func(start string) {
		color[start] = gray
		st := []frame{{id: start, idx: 0}}
		for len(st) > 0 {
			f := &st[len(st)-1]
			deps := adj[f.id]
			if f.idx >= len(deps) {
				color[f.id] = black
				st = st[:len(st)-1]
				continue
			}
			next := deps[f.idx]
			f.idx++
			switch color[next] {
			case white:
				color[next] = gray
				st = append(st, frame{id: next, idx: 0})
			case gray:
				// Reconstruct the cycle: walk the stack from `next` down,
				// then close with `next` again.
				var path []string
				start := false
				for _, sf := range st {
					if !start && sf.id != next {
						continue
					}
					start = true
					path = append(path, sf.id)
				}
				path = append(path, next)
				t.Errorf("dependency cycle: %s", strings.Join(path, " → "))
				// Keep scanning — there may be more cycles to surface.
			}
		}
	}
	roots := make([]string, 0, len(keyIndex))
	for _, e := range keyIndex {
		roots = append(roots, e.id)
	}
	sort.Strings(roots)
	for _, id := range roots {
		if color[id] == white {
			dfs(id)
		}
	}

	totalEdges := 0
	for _, deps := range adj {
		totalEdges += len(deps)
	}
	t.Logf("registry DAG: %d nodes, %d edges, acyclic ✓", len(keyIndex), totalEdges)
}
