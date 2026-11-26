package serve

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/tactic"
)

// TestInductionBackedByCorpus forces the production induction-principle
// promises the bootstrap serves from entries (num_induction,
// list_induction, option_induction) and verifies the chapter proof is
// what ran.
//
// The bootstrap is lazy, so a green build proves only that the promise
// DECLARES correctly — this test is the half that actually runs
// peano.Induction's Build (plus its transitive family deps, each on its
// own fresh env) at force time. Two assertions, both load-bearing:
//
// 1. the forced cert is kernel-proved and in the shape the induction
// tactic's analyzer reads;
// 2. the entry path is what produced it — the entryPromises memo
// holds settled promises for the entry and its transitive typed-dep
// closure, which only a force through the promise.go seam creates.
// Without this check a silent fallback to any other binding of the
// name would pass assertion 1 identically.
//
// The closure is READ OFF THE REGISTRY (typedDepClosure), never listed
// by hand: a hand census names the deps of one day, and goes stale the
// day a chapter replaces one dep by another (peano.Induction's Deps,
// say) while the path it guards stays intact.
func TestInductionBackedByCorpus(t *testing.T) {
	corpEnv := env()
	for _, tc := range []struct {
		name  string
		entry string // the entry the bootstrap serves under name
	}{
		{"num_induction", "peano.Induction"},
		// The datatype principles are derived by the datatype door
		// from the minted type over the recspace universe, so each
		// closure is the derived entry and the universe's rows below it.
		{"list_induction", "list.Induction"},
		{"option_induction", "option.Induction"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			thm, ok := corpEnv.LibraryThms[tc.name]
			if !ok {
				t.Fatalf("%s not bound on the corpus env", tc.name)
			}
			cert := core.Force(context.Background(), core.AsThm(thm))
			if cert.IsZero() || !cert.Proved() {
				t.Fatalf("%s forced but not proved", tc.name)
			}
			// The binding is the BRIDGED form — the shape the tactic's
			// analyzer parses.
			if _, aerr := tactic.AnalyzeInductionPrinciple(prop.WrapProp(cert)); aerr != nil {
				t.Fatalf("forced %s does not parse as an induction principle: %v", tc.name, aerr)
			}
			requirePromisedClosure(t, tc.entry)
		})
	}
}

// typedDepClosure is the transitive closure of an entry's typed deps
// as the registry holds them today — the entry first, then every
// entry reachable through ServedDeps, each once. What EntryThm forces
// on the way to the root (promise.go step (1) realizes every dep
// before a Build runs), so every name here must hold a settled promise
// after the root is forced.
func typedDepClosure(t *testing.T, root string) []string {
	t.Helper()
	entry, ok := registry.ByName(root)
	if !ok {
		t.Fatalf("%s is not registered", root)
	}
	seen := map[string]bool{entry.Name: true}
	out := []string{entry.Name}
	for i := 0; i < len(out); i++ {
		cur, _ := registry.ByName(out[i])
		for _, dep := range cur.ServedDeps() {
			if seen[dep.Name] {
				continue
			}
			seen[dep.Name] = true
			out = append(out, dep.Name)
		}
	}
	return out
}

// requirePromisedClosure is the provenance check: forcing through
// promise.go memoizes a promise per entry it built, so the root and
// its whole typed-dep closure must be there, settled. A datatype door's
// principle has no typed deps — the door derives it from the minted
// type alone — so its closure is the entry itself, and the check is
// that the entry's own promise ran.
func requirePromisedClosure(t *testing.T, root string) {
	t.Helper()
	closure := typedDepClosure(t, root)
	t.Logf("%s: typed-dep closure of %d entries", root, len(closure))
	entryMu.Lock()
	defer entryMu.Unlock()
	for _, name := range closure {
		p, ok := entryPromises[name]
		if !ok {
			t.Fatalf("promise for %s was never created — the force did not run the path (closure of %s: %v)", name, root, closure)
		}
		if !p.Proved() {
			t.Errorf("promise for %s exists but is not settled", name)
		}
	}
}

// TestRecursionBackedByCorpus is TestInductionBackedByCorpus for the
// two datatype RECURSION schemas: the define door's equation compiler
// looks them up by name, and they are served from the chapters. It
// checks the same two things — that the name forces to a real theorem
// the schema analyzer parses, and that the force ran through the seam,
// entry and typed-dep closure alike.
func TestRecursionBackedByCorpus(t *testing.T) {
	corpEnv := env()
	for _, tc := range []struct {
		name  string
		entry string
	}{
		// The universe below the datatype door's derivation — the
		// recursion theorem the schema is read off, the family
		// constructor whose clauses resolve the constructor tag, and
		// what those stand on — is the closure the registry reads.
		{"list_recursion", "list.Recursion"},
		{"option_recursion", "option.Recursion"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			thm, ok := corpEnv.LibraryThms[tc.name]
			if !ok {
				t.Fatalf("%s not bound on the corpus env", tc.name)
			}
			cert := core.Force(context.Background(), core.AsThm(thm))
			if cert.IsZero() || !cert.Proved() {
				t.Fatalf("%s forced but not proved", tc.name)
			}
			if _, aerr := tactic.AnalyzeRecursionPrinciple(prop.WrapProp(cert)); aerr != nil {
				t.Fatalf("forced %s does not parse as a recursion principle: %v", tc.name, aerr)
			}
			requirePromisedClosure(t, tc.entry)
		})
	}
}
