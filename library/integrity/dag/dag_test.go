package dag

import (
	"testing"

	"github.com/euc-ai/xugo/core"

	// The graph is built from whatever families are linked; this
	// test wants the whole corpus, so it links the aggregator.
	_ "github.com/euc-ai/xugo/library/proofs"
)

// Every edge points at a node.
func TestEdgesResolve(t *testing.T) {
	byKey := map[core.PropKey]Node{}
	for _, n := range Nodes() {
		byKey[n.Key] = n
	}
	for _, n := range Nodes() {
		for _, d := range n.Deps {
			if _, ok := byKey[d]; !ok {
				t.Errorf("%s %s depends on %s, which is no node", n.Source, n.Name, d)
			}
		}
	}
}

// Closure basics: empty seeds, a leaf, an external key, transitivity.
func TestClosure(t *testing.T) {
	if c := Closure(nil); len(c) != 0 {
		t.Errorf("empty seeds: |closure| = %d, want 0", len(c))
	}
	const external = core.PropKey("prop_not_an_entry_key")
	if c := Closure([]core.PropKey{external}); len(c) != 1 || !c[external] {
		t.Errorf("external seed: got %v, want just the seed", c)
	}
	var leaf, parent Node
	for _, n := range Nodes() {
		if len(n.Deps) == 0 && leaf.Key == "" {
			leaf = n
		}
		if len(n.Deps) > 0 && parent.Key == "" {
			parent = n
		}
	}
	if leaf.Key == "" || parent.Key == "" {
		t.Skip("corpus too small")
	}
	if c := Closure([]core.PropKey{leaf.Key}); !c[leaf.Key] || len(c) != 1 {
		t.Errorf("leaf %s: closure %v", leaf.Name, c)
	}
	c := Closure([]core.PropKey{parent.Key})
	for _, d := range parent.Deps {
		if !c[d] {
			t.Errorf("closure of %s misses its direct dep %s", parent.Name, d)
		}
		for _, dd := range DepsOf(d) {
			if !c[dd] {
				t.Errorf("closure of %s misses the transitive dep %s", parent.Name, dd)
			}
		}
	}
}
