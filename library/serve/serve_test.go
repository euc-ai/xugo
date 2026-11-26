package serve

import (
	"context"
	"iter"
	"regexp"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// TestRegisterAllPromiseByKey is the C mechanism: after RegisterAll, the engine
// can ask for a proved-earlier dep by its own key and get a real,
// UNFORCED, forceable promise (an honest IOU) instead of a fabricated
// TestThm — and forcing it runs the chapter proof to a kernel
// certificate bridged into the requested statement's shape (the settle
// gate). The requested statement is spelled by hand rather than read
// off the entry, so this also exercises the BridgeNormalize step
// PromiseByKey performs when a builder settles at a shape other than
// the caller's.
func TestRegisterAllPromiseByKey(t *testing.T) {
	regEnv := &proof.ProverEnv{}
	RegisterAll(regEnv)
	penv := env()

	addSymKey := core.PropKey(nat_arith.AddSym.Entry().Key)
	// The law spelled by hand; the check below is that this statement
	// really keys to the entry.
	stmt := proof.NewScript(penv).MakePropText("∀m:num. ∀n:num. m + n = n + m")
	if got, _ := prop.Normalize(stmt); got.AlphaKey() != addSymKey {
		t.Fatalf("the hand-built statement keys to %s, not nat_arith.AddSym's own key %s", got.AlphaKey(), addSymKey)
	}

	p := regEnv.PromiseByKey(addSymKey, stmt)
	if p == nil {
		t.Fatal("PromiseByKey returned nil — RegisterAll did not register nat_arith.AddSym's own key")
	}
	if p.Proved() {
		t.Fatal("promise is already forced — must be a lazy IOU")
	}

	cert := core.Force(context.Background(), core.AsThm(p))
	if cert.IsZero() {
		t.Fatal("forced promise yielded nil cert")
	}
	if !cert.Conclusion().AlphaEquals(stmt.Conclusion()) {
		t.Fatalf("forced cert does not α-match requested statement\n got=%v\nwant=%v",
			cert.Conclusion(), stmt.Conclusion())
	}
	// Provenance: the seam built it.
	entry := nat_arith.AddSym.Entry()
	entryMu.Lock()
	memo, memoed := entryPromises[entry.Name]
	entryMu.Unlock()
	if !memoed || !memo.Proved() {
		t.Fatalf("key %s resolved, but the entry %s was not the builder", addSymKey, entry.Name)
	}

	// An unregistered key yields nil (engine then falls back to TestThm).
	if regEnv.PromiseByKey(core.PropKey("prop_deadbeef"), stmt) != nil {
		t.Fatal("PromiseByKey on an unregistered key should be nil")
	}
}

// TestRegisterAllOwnKey: an entry's own key resolves after
// RegisterAll, and forcing it runs the chapter proof (promise.go) to a
// kernel cert of the entry's statement. Provenance is checked the way
// TestInductionBackedByCorpus checks it: the memo holds the
// settled promise, which no generated path would create.
func TestRegisterAllOwnKey(t *testing.T) {
	regEnv := &proof.ProverEnv{}
	RegisterAll(regEnv)

	var entry *registry.ProofEntry
	for _, e := range registry.All() {
		if len(e.Build.Capabilities) == 0 {
			entry = e
			break
		}
	}
	if entry == nil {
		t.Skip("no capability-free entry is linked")
	}
	stmt := entry.Statement().Prop
	p := regEnv.PromiseByKey(core.PropKey(entry.Key), stmt)
	if p == nil {
		t.Fatalf("PromiseByKey(%s) is nil — RegisterAll did not register %s under its own key", entry.Key, entry.Name)
	}
	if p.Proved() {
		t.Fatal("promise is already forced — must be a lazy IOU")
	}
	cert := core.Force(context.Background(), core.AsThm(p))
	if cert.IsZero() || !cert.Proved() {
		t.Fatalf("forcing %s yielded no proved cert", entry.Name)
	}
	if !cert.Conclusion().AlphaEquals(stmt.Conclusion()) {
		t.Fatalf("forced cert does not α-match the entry's statement\n got=%v\nwant=%v", cert.Conclusion(), stmt.Conclusion())
	}
	entryMu.Lock()
	defer entryMu.Unlock()
	if prom, ok := entryPromises[entry.Name]; !ok || !prom.Proved() {
		t.Fatalf("%s was not forced through the promise seam (memo present=%v)", entry.Name, ok)
	}
}

// TestCorpusForcesRealCert: a single corpus theorem builds against the dedicated
// corpus env and forces to a real kernel certificate — validating the non-test
// corpus env end to end.
// The subject is nat_arith.AddSym: the chapter proof
// and its whole cone force, so the gate means what its name says.
func TestCorpusForcesRealCert(t *testing.T) {
	thm := EntryThm(env(), nat_arith.AddSym)
	if thm == nil {
		t.Fatal("EntryThm(nat_arith.AddSym) returned nil")
	}
	cert := core.Force(context.Background(), core.AsThm(thm))
	if cert.IsZero() {
		t.Fatal("forced nat_arith.AddSym cert is nil")
	}
}

// TestCorpusEnvNamedPromiseForce covers the shared corpus env's
// promise-resolution seam by NAME: env() binds names in
// corpEnv.LibraryThms — the resolution surface for a session's
// `ctx.LibraryThm("NAME")` witness-boundary cites, and for the schema
// names the define door reads — and forcing one runs the deferred build
// ON corpEnv, settling the cell at its declared statement via the
// α-gate. The standing named bindings are the corpus-served schemas.
func TestCorpusEnvNamedPromiseForce(t *testing.T) {
	for _, name := range []string{"list_recursion", "option_recursion"} {
		thm, ok := env().LibraryThms[name]
		if !ok {
			t.Fatalf("%s not bound in corpus env LibraryThms", name)
		}
		cert := core.Force(context.Background(), core.AsThm(thm))
		if cert.IsZero() {
			t.Fatalf("forced %s cert is nil", name)
		}
		if !cert.Proved() {
			t.Fatalf("%s forced but not proved", name)
		}
	}
}

var rIdentRE = regexp.MustCompile(`[A-Za-z_][A-Za-z0-9_]*`)

// rScope assigns RealType to every identifier in s (mirrors omega's test helper).
func rScope(s string) map[string]core.HolType {
	ctx := map[string]core.HolType{}
	for _, id := range rIdentRE.FindAllString(s, -1) {
		ctx[id] = dsl.RealType
	}
	return ctx
}

func rParse(t *testing.T, s string, expected core.HolType) core.Term {
	t.Helper()
	r := dsl.ParseTermTextInScope(s, rScope(s), &dsl.ParseScope{}, expected)
	if len(r.Errors) > 0 {
		t.Fatalf("dsl parse %q: %v", s, r.Errors)
	}
	return r.Term
}

func seqOfTerms(ts ...core.Term) iter.Seq[core.Term] {
	return func(yield func(core.Term) bool) {
		for _, t := range ts {
			if !yield(t) {
				return
			}
		}
	}
}
