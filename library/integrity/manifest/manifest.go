//go:generate go run ../../cmd/policy_gen -policy-output ../policy/policy_gen.go

// Package manifest builds the one canonical dependency graph used for proof
// integrity. Its base is the corpus DAG (library/integrity/dag):
// entries under their own keys, dep edges resolved there. Build models
// every compound-mechanism capability a proof's recorded build USED
// (the family blob's per-member record —
// nobody declares one) as edges to the capability's theorem roots, and
// checks dangling references and cycles.
//
// Two integrity properties exist ONLY here, so the manifest test must
// stay in every landing's gates:
//
// - Capability circularity: the raw install-time foundations are
// closures over the DAG's dep edges alone. Build adds the capability
// edges and rejects cycles in the complete graph. A cycle may run
// through OTHER proofs' capability uses, which no dep closure sees.
// The accepted graph supplies the policy witness's Denied sets:
// prover/proof.NewProofScope refuses a capability whose roots reach
// the target, on top of the raw foundation gate.
// - The refined foundations themselves: Build recomputes each
// capability's closure over the complete graph and installs it via
// RefineDependencyCapabilityFoundations — its sole caller.
package manifest

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/serve"

	// The corpus registers into registry at package-init
	// time: the blank import pulls in (via its proofs.go) every
	// family sub-package, so the DAG below sees the whole corpus.
	"github.com/euc-ai/xugo/library/integrity/dag"
	_ "github.com/euc-ai/xugo/library/proofs"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

type Node struct {
	Key          core.PropKey
	Name         string
	Source       string
	Deps         []core.PropKey
	Capabilities []string
	// Card says the member is stated without a proof (dag.Node.Card).
	// Not part of the digest: a card's proof landing changes no edge.
	Card bool
}

type Graph struct {
	Nodes map[core.PropKey]Node
	Order []core.PropKey
}

// ProofPolicy is one target's verdict: the capabilities its recorded
// proof used, and the capabilities the refined foundations deny it —
// every installed capability whose bundle roots reach the target.
type ProofPolicy struct {
	Target core.PropKey
	Name   string
	Used   []string
	Denied []string
}

func Build() (g *Graph, err error) {
	defer func() {
		if r := recover(); r != nil {
			g = nil
			err = fmt.Errorf("initialize proof dependency capabilities: %v", r)
		}
	}()
	serve.InstallNatBundle()
	serve.InstallRealBundle()
	serve.InstallIntBundle()
	// Structure ring: the algebra chapters' general laws and the
	// carrier instances (ℂ) the ring at a comm_ring / field fact reads.
	serve.InstallStructureRingBundle()
	// Diagram chase: the algebra and set chapters' carrier laws the
	// chase closer reads at a module diagram.
	serve.InstallChaseBundle()
	// Record normal form: the record equations an instance is computed
	// with where it is handed over (prover/tactic, InstanceNormal).
	serve.InstallRecordNormal()

	g = &Graph{Nodes: make(map[core.PropKey]Node)}
	// The base graph is the corpus DAG: every edge is a typed dep, so
	// every edge resolves.
	for _, n := range dag.Nodes() {
		g.Nodes[n.Key] = Node{Key: n.Key, Name: n.Name, Source: n.Source,
			Deps: n.Deps, Capabilities: n.Capabilities, Card: n.Card}
	}

	specs := proof.DependencyCapabilitySnapshot()
	if err := g.addCapabilities(specs); err != nil {
		return nil, err
	}

	// The complete, acyclic graph supplies the foundations for lexical
	// runtime gating. No recorded capability edge is omitted.
	foundations := make(map[string]map[core.PropKey]bool, len(specs))
	for name, spec := range specs {
		closure := make(map[core.PropKey]bool)
		for _, root := range spec.Roots {
			g.collectReachable(root, closure)
		}
		foundations[name] = closure
		// A capability's foundation is what every close by that
		// capability stands on; a card in it would put an axiom under
		// every arithmetic close in the corpus. A card may be cited
		// anywhere but there: prove it, or cut the edge.
		for key := range closure {
			if g.Nodes[key].Card {
				return nil, fmt.Errorf("capability %q: its foundation reaches the card %s (%s) — a card is an axiom until "+
					"its proof lands, and a capability's foundation admits none; prove the card or cut the edge", name, g.Nodes[key].Name, key)
			}
		}
	}
	proof.RefineDependencyCapabilityFoundations(foundations)
	return g, nil
}

// addCapabilities expands every recorded use into its theorem roots and
// rejects cycles before the graph can supply a policy or refined foundation.
func (g *Graph) addCapabilities(specs map[string]proof.CapabilitySpec) error {
	for key, n := range g.Nodes {
		n.Deps = canonicalDeps(n.Deps)
		for _, dep := range n.Deps {
			if _, ok := g.Nodes[dep]; !ok {
				return fmt.Errorf("%s (%s) has dangling dependency key %s", n.Name, n.Source, dep)
			}
		}
		for _, capability := range expandCapabilityNames(n.Capabilities) {
			spec, ok := specs[capability]
			if !ok {
				return fmt.Errorf("%s capability manifest: dependency capability %q is not installed", n.Name, capability)
			}
			for _, root := range spec.Roots {
				if _, ok := g.Nodes[root]; !ok {
					return fmt.Errorf("%s capability %q has dangling root %s", n.Name, capability, root)
				}
			}
			n.Deps = append(n.Deps, spec.Roots...)
		}
		n.Deps = canonicalDeps(n.Deps)
		g.Nodes[key] = n
		g.Order = append(g.Order, key)
	}
	sort.Slice(g.Order, func(i, j int) bool { return g.Order[i] < g.Order[j] })

	if cycle := g.FindCycle(); len(cycle) > 0 {
		return fmt.Errorf("canonical proof dependency cycle: %s", g.formatPath(cycle))
	}
	return nil
}

func expandCapabilityNames(capabilities []string) []string {
	seen := make(map[string]bool)
	var out []string
	for _, name := range capabilities {
		if !seen[name] {
			seen[name] = true
			out = append(out, name)
		}
	}
	sort.Strings(out)
	return out
}

// collectReachable marks the reach of key over the graph.
func (g *Graph) collectReachable(key core.PropKey, seen map[core.PropKey]bool) {
	if seen[key] {
		return
	}
	seen[key] = true
	n := g.Nodes[key]
	for _, dep := range n.Deps {
		g.collectReachable(dep, seen)
	}
}

func canonicalDeps(in []core.PropKey) []core.PropKey {
	seen := map[core.PropKey]bool{}
	out := make([]core.PropKey, 0, len(in))
	for _, k := range in {
		if k != "" && !seen[k] {
			seen[k] = true
			out = append(out, k)
		}
	}
	sort.Slice(out, func(i, j int) bool { return out[i] < out[j] })
	return out
}

func (g *Graph) FindCycle() []core.PropKey {
	color := make(map[core.PropKey]uint8, len(g.Nodes))
	stack := make([]core.PropKey, 0)
	position := make(map[core.PropKey]int)
	var visit func(core.PropKey) []core.PropKey
	visit = func(key core.PropKey) []core.PropKey {
		color[key] = 1
		position[key] = len(stack)
		stack = append(stack, key)
		for _, dep := range g.Nodes[key].Deps {
			switch color[dep] {
			case 0:
				if cycle := visit(dep); cycle != nil {
					return cycle
				}
			case 1:
				cycle := append([]core.PropKey(nil), stack[position[dep]:]...)
				return append(cycle, dep)
			}
		}
		stack = stack[:len(stack)-1]
		delete(position, key)
		color[key] = 2
		return nil
	}
	for _, key := range g.Order {
		if color[key] == 0 {
			if cycle := visit(key); cycle != nil {
				return cycle
			}
		}
	}
	return nil
}

func (g *Graph) formatPath(path []core.PropKey) string {
	parts := make([]string, len(path))
	for i, key := range path {
		n := g.Nodes[key]
		parts[i] = n.Source + ":" + n.Name + "[" + string(key) + "]"
	}
	return strings.Join(parts, " -> ")
}

// Digest is a stable certificate of the exact canonical graph. The generated
// Go initialization witness embeds it; tests reject a stale witness.
func (g *Graph) Digest() string {
	h := sha256.New()
	for _, key := range g.Order {
		fmt.Fprintf(h, "%s\n", key)
		n := g.Nodes[key]
		capabilities := append([]string(nil), n.Capabilities...)
		sort.Strings(capabilities)
		for _, capability := range capabilities {
			fmt.Fprintf(h, "  capability:%s\n", capability)
		}
		for _, dep := range n.Deps {
			fmt.Fprintf(h, "  %s\n", dep)
		}
	}
	return hex.EncodeToString(h.Sum(nil))
}

// CanonicalProofPolicies projects the complete graph's capability
// closures onto every entry: the capabilities its recorded proof
// uses (the node's capability edges) and the capabilities the refined
// foundations DENY it — a capability whose bundle roots reach the
// entry's node. Denial is recorded for the capabilities a proof of the
// target could reach for: the arithmetic domains (any proof may) and
// the capabilities its own record uses (a lift's int_of_real source —
// nothing else ever asks for it). Only an entry that uses or is denied
// something gets a row; the rest are gated by the raw foundation alone,
// which agrees with the refined one on them (they lie in no foundation).
func CanonicalProofPolicies(g *Graph) []ProofPolicy {
	specs := proof.DependencyCapabilitySnapshot()
	var out []ProofPolicy
	for _, entry := range registry.All() {
		target := core.PropKey(entry.Key)
		n, ok := g.Nodes[target]
		if !ok {
			panic(fmt.Sprintf("proof policy target %s (%s) is absent from canonical graph", target, entry.Name))
		}
		used := append([]string(nil), n.Capabilities...)
		sort.Strings(used)
		candidates := append([]string{proof.CapabilityArithNat, proof.CapabilityArithReal, proof.CapabilityArithInt,
			proof.CapabilityArithStructure, proof.CapabilityArithStructureInstances, proof.CapabilityArithModulus,
			proof.CapabilityChase}, used...)
		sort.Strings(candidates)
		var denied []string
		for i, name := range candidates {
			if i > 0 && name == candidates[i-1] {
				continue
			}
			if spec, ok := specs[name]; ok && spec.Foundation[target] {
				denied = append(denied, name)
			}
		}
		if len(used) == 0 && len(denied) == 0 {
			continue
		}
		out = append(out, ProofPolicy{Target: target, Name: entry.Name, Used: used, Denied: denied})
	}
	sort.Slice(out, func(i, j int) bool { return out[i].Target < out[j].Target })
	return out
}

// PolicyDigest covers the per-target verdicts as well as the canonical
// graph, so a re-recorded use or a moved foundation makes the static
// policy witness stale.
func PolicyDigest(g *Graph) string {
	h := sha256.New()
	fmt.Fprintln(h, g.Digest())
	for _, policy := range CanonicalProofPolicies(g) {
		fmt.Fprintf(h, "%s\n", policy.Target)
		for _, capability := range policy.Used {
			fmt.Fprintf(h, "  used:%s\n", capability)
		}
		for _, capability := range policy.Denied {
			fmt.Fprintf(h, "  denied:%s\n", capability)
		}
	}
	return hex.EncodeToString(h.Sum(nil))
}
