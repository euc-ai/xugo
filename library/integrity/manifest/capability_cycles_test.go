package manifest

import (
	"maps"
	"slices"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/prover/proof"
)

// Recorded capability uses are proof dependencies even when several
// capabilities supply one another's foundations.
func TestCapabilityCyclesRejected(t *testing.T) {
	const a, b, c core.PropKey = "prop_a", "prop_b", "prop_c"
	specs := map[string]proof.CapabilitySpec{
		"tool:a": {Roots: []core.PropKey{a}},
		"tool:b": {Roots: []core.PropKey{b}},
		"tool:c": {Roots: []core.PropKey{c}},
	}
	for _, tc := range []struct {
		name  string
		nodes []Node
		cycle string
	}{
		{
			name:  "self",
			nodes: []Node{{Key: a, Name: "A", Capabilities: []string{"tool:a"}}},
			cycle: "chapter:A[prop_a] -> chapter:A[prop_a]",
		},
		{
			name: "mutual_capabilities",
			nodes: []Node{
				{Key: a, Name: "A", Capabilities: []string{"tool:b"}},
				{Key: b, Name: "B", Capabilities: []string{"tool:a"}},
			},
			cycle: "chapter:A[prop_a] -> chapter:B[prop_b] -> chapter:A[prop_a]",
		},
		{
			name: "three_capabilities",
			nodes: []Node{
				{Key: a, Name: "A", Capabilities: []string{"tool:b"}},
				{Key: b, Name: "B", Capabilities: []string{"tool:c"}},
				{Key: c, Name: "C", Capabilities: []string{"tool:a"}},
			},
			cycle: "chapter:A[prop_a] -> chapter:B[prop_b] -> chapter:C[prop_c] -> chapter:A[prop_a]",
		},
		{
			name: "capabilities_and_citation",
			nodes: []Node{
				{Key: a, Name: "A", Capabilities: []string{"tool:b"}},
				{Key: b, Name: "B", Deps: []core.PropKey{c}},
				{Key: c, Name: "C", Capabilities: []string{"tool:a"}},
			},
			cycle: "chapter:A[prop_a] -> chapter:B[prop_b] -> chapter:C[prop_c] -> chapter:A[prop_a]",
		},
		{
			name: "citations",
			nodes: []Node{
				{Key: a, Name: "A", Deps: []core.PropKey{b}},
				{Key: b, Name: "B", Deps: []core.PropKey{a}},
			},
			cycle: "chapter:A[prop_a] -> chapter:B[prop_b] -> chapter:A[prop_a]",
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			g := &Graph{Nodes: make(map[core.PropKey]Node)}
			for _, n := range tc.nodes {
				n.Source = "chapter"
				g.Nodes[n.Key] = n
			}
			err := g.addCapabilities(specs)
			if err == nil || !strings.Contains(err.Error(), "canonical proof dependency cycle: "+tc.cycle) {
				t.Fatalf("want the complete cycle %s refused, got %v", tc.cycle, err)
			}
		})
	}
}

// Acyclic capability chains remain in the graph that supplies runtime
// foundations, including a capability used by another capability's root.
func TestCapabilityChainPreserved(t *testing.T) {
	const a, b, c, d core.PropKey = "prop_a", "prop_b", "prop_c", "prop_d"
	g := &Graph{Nodes: map[core.PropKey]Node{
		a: {Key: a, Name: "A", Deps: []core.PropKey{d}, Capabilities: []string{"tool:b", "tool:b"}},
		b: {Key: b, Name: "B", Capabilities: []string{"tool:c"}},
		c: {Key: c, Name: "C"},
		d: {Key: d, Name: "D"},
	}}
	specs := map[string]proof.CapabilitySpec{
		"tool:a": {Roots: []core.PropKey{a}},
		"tool:b": {Roots: []core.PropKey{b}},
		"tool:c": {Roots: []core.PropKey{c}},
	}
	if err := g.addCapabilities(specs); err != nil {
		t.Fatal(err)
	}
	if want := []core.PropKey{b, d}; !slices.Equal(g.Nodes[a].Deps, want) {
		t.Fatalf("A dependencies: got %v, want %v", g.Nodes[a].Deps, want)
	}
	if want := []core.PropKey{c}; !slices.Equal(g.Nodes[b].Deps, want) {
		t.Fatalf("B dependencies: got %v, want %v", g.Nodes[b].Deps, want)
	}
	closure := make(map[core.PropKey]bool)
	g.collectReachable(a, closure)
	if want := map[core.PropKey]bool{a: true, b: true, c: true, d: true}; !maps.Equal(closure, want) {
		t.Fatalf("tool:a foundation: got %v, want %v", closure, want)
	}
}
