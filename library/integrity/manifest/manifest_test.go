package manifest_test

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/integrity/manifest"
	"github.com/euc-ai/xugo/library/integrity/policy"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_div_rem"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

func TestCanonicalDependencyGraph(t *testing.T) {
	g, err := manifest.Build()
	if err != nil {
		t.Fatal(err)
	}
	// PolicyDigest covers both the raw graph and the per-target policy table
	// projected off it, so this one comparison catches every drift the runtime
	// lookup cares about.
	if got, want := policy.Digest, manifest.PolicyDigest(g); got != want {
		t.Fatalf("stale canonical proof policy: got %s, want %s; run go generate ./library/integrity/manifest", got, want)
	}
	t.Logf("canonical proof graph: %d nodes, digest %s", len(g.Nodes), g.Digest())
	intFoundation := proof.DependencyCapabilitySnapshot()[proof.CapabilityArithInt].Foundation
	for _, e := range []registry.EntryLike{int_div_rem.DivByOne, int_div_rem.RemByOne} {
		if key := core.PropKey(e.Entry().Key); !intFoundation[key] {
			t.Errorf("int arithmetic foundation is missing %s (%s)", key, e.Entry().Name)
		}
	}
}

// TestNoDeniedUse holds the policy projection to the acyclic graph:
// no recorded use may be denied by its capability's refined foundation.
// Build rejects circular uses before any policy can be generated.
func TestNoDeniedUse(t *testing.T) {
	g, err := manifest.Build()
	if err != nil {
		t.Fatal(err)
	}
	rows := 0
	for _, p := range manifest.CanonicalProofPolicies(g) {
		rows++
		denied := map[string]bool{}
		for _, capability := range p.Denied {
			denied[capability] = true
		}
		for _, capability := range p.Used {
			if denied[capability] {
				t.Errorf("%s (%s) uses %q but the canonical graph reaches it from that "+
					"capability's roots: the proof cannot replay. Find the dep edge that "+
					"dragged the target into the bundle's foundation and cut it, or re-prove "+
					"the step without the capability. Do not exempt the proof.",
					p.Name, p.Target, capability)
			}
		}
	}
	t.Logf("capability uses checked against the complete graph; %d target(s) use or are denied something", rows)
}
