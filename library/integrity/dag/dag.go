// Package dag is the corpus dependency graph: every chapter member under
// its own-key identity, one graph over which the circularity instruments
// ask "what does this reach". Its readers are omega's bundle foundations
// (library/serve), the complete capability manifest
// (library/integrity/manifest), and the DAG gate. Read-only; built once,
// on first use, after every chapter's init has run; runs no proof.
//
// # Key space
//
// A node's key is its statement's own normalized key
// (registry.ProofEntry.Key).
//
// # Edges
//
// A member's dependencies (DepEntries — declared, or recorded from what
// its proof reads), each edge the dep's own key. Every edge resolves by
// construction, since a dep is an entry.
package dag

import (
	"sort"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/registry"
)

// Node is one proof in the corpus graph.
type Node struct {
	// Key is the node's canonical identity: the member's own key.
	Key core.PropKey
	// Name is the member's registered name.
	Name string
	// Source labels where the node came from. One value today; it is a
	// field rather than a constant because manifest.Digest hashes it and
	// its error messages print it.
	Source string
	// Deps are the node's direct dependencies, canonical keys, sorted
	// and deduplicated.
	Deps []core.PropKey
	// Capabilities are the compound-mechanism capabilities the proof was
	// RECORDED using (registry.RecordedCapabilities — the family blob's
	// per-member record plus what the Build constructor itself makes).
	Capabilities []string
	// Card says the member is stated without a proof (registry
	// ProofEntry.IsCard): an axiom until its proof lands. A node's
	// Deps reach its card frontier through the same edges.
	Card bool
}

const SourceChapter = "chapter"

var (
	once  sync.Once
	nodes map[core.PropKey]*Node
	order []core.PropKey
)

func ensure() {
	once.Do(build)
}

func build() {
	nodes = make(map[core.PropKey]*Node, len(registry.All()))
	for _, e := range registry.All() {
		k := core.PropKey(e.Key)
		n := &Node{Key: k, Name: e.Name, Source: SourceChapter,
			Capabilities: registry.RecordedCapabilities(e), Card: e.IsCard()}
		nodes[k] = n
		order = append(order, k)
	}
	for _, e := range registry.All() {
		n := nodes[core.PropKey(e.Key)]
		for _, dep := range e.DepEntries() {
			n.Deps = append(n.Deps, core.PropKey(dep.Key))
		}
		n.Deps = sortedUnique(n.Deps)
	}
}

// Has reports whether k names a node.
func Has(k core.PropKey) bool {
	ensure()
	_, ok := nodes[k]
	return ok
}

// Lookup returns the node k names.
func Lookup(k core.PropKey) (Node, bool) {
	ensure()
	n, ok := nodes[k]
	if !ok {
		return Node{}, false
	}
	return *n, true
}

// DepsOf returns the direct canonical deps of the node k names, or nil
// when k names no node. The slice is shared with the index — do not
// mutate it.
func DepsOf(k core.PropKey) []core.PropKey {
	ensure()
	if n := nodes[k]; n != nil {
		return n.Deps
	}
	return nil
}

// Nodes returns every node, in registration order.
func Nodes() []Node {
	ensure()
	out := make([]Node, 0, len(order))
	for _, k := range order {
		out = append(out, *nodes[k])
	}
	return out
}

// Closure returns the transitive reach of seeds over Deps, INCLUDING
// the seeds. A seed that names no node is kept as a leaf (an
// external axiom or const def a bundle field may rest on). BFS with one
// shared visited set, so duplicate seeds cost nothing extra.
//
// Soundness contract for omega's self-circularity gate: target ∈
// Closure(bundleFieldKeys) ⇔ the bundle, fully unfolded, relies on
// target as a sub-proof — exactly when the bundle proving target would
// be circular, transitive reach included.
func Closure(seeds []core.PropKey) map[core.PropKey]bool {
	ensure()
	out := make(map[core.PropKey]bool, len(seeds))
	queue := make([]core.PropKey, 0, len(seeds))
	visit := func(k core.PropKey) {
		if out[k] {
			return
		}
		out[k] = true
		queue = append(queue, k)
	}
	for _, s := range seeds {
		visit(s)
	}
	for len(queue) > 0 {
		k := queue[0]
		queue = queue[1:]
		if n := nodes[k]; n != nil {
			for _, d := range n.Deps {
				visit(d)
			}
		}
	}
	return out
}

func sortedUnique(in []core.PropKey) []core.PropKey {
	seen := make(map[core.PropKey]bool, len(in))
	out := in[:0]
	for _, k := range in {
		if k != "" && !seen[k] {
			seen[k] = true
			out = append(out, k)
		}
	}
	sortKeys(out)
	return out
}

func sortKeys(ks []core.PropKey) {
	sort.Slice(ks, func(i, j int) bool { return ks[i] < ks[j] })
}
