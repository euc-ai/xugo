// promise.go — the consumption seam: serving an
// entry as a promise. serve.go's env binds the promise of an entry that
// ServesAs a library-convention name under that name (the by-NAME
// surface the induction/recursion schema lookups and the define door
// read), RegisterAll registers every entry under its own key (the
// by-KEY channel), and the bundles bind their fields through fromEntry
// below; all of them hand out the one promise this file makes.
//
// Consumers import the LEAF CHAPTER whose entry they serve, never the
// chapter aggregator: `serve → proofs/nat_num/peano → registry` is
// acyclic, while importing package proofs would cycle back through
// this package.
//
// Isolation contract, mirroring the replay harness's per-member build:
// a Build runs on a FRESH env — its typed deps pre-forced to
// certs (a forced ThmCert is a kernel object valid in any env), its
// family's CNF store installed strict — so the shared corpus env is
// never mutated (no map writes concurrent readers could race on, no
// RequireCNFCacheHit leakage) and the build replays exactly as the
// harness verified it.
//
// A CARD — a member stated without a proof (registry.Family.Card) —
// has no Build to run: it is served as the axiom `⊢ <statement>`,
// minted here with core.NewAxiom (EntryAxiom). So is the POSTULATE
// (registry.Family.Postulate), the axiom of infinity, at the term its
// chapter builds. This is the one production site that mints an axiom
// for a member: the corpus is sound relative to its postulate and its
// cards, `xugo cards` lists the cards, and a card's proof landing in
// place of its Card build retires its axiom with no change downstream.

package serve

import (
	"fmt"
	"sync"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

var (
	entryMu       sync.Mutex
	entryPromises = map[string]core.Thm{}
	// builtEntries names every entry whose Build this process has run
	// through EntryThm — the proofs the corpus env ran for real, as
	// against the promises a bounded force settled from trust.
	builtEntries = map[string]bool{}
)

func noteEntryBuilt(e *registry.ProofEntry) {
	entryMu.Lock()
	defer entryMu.Unlock()
	builtEntries[e.Name] = true
}

// entriesBuilt is a snapshot of the entries built so far.
func entriesBuilt() map[string]bool {
	entryMu.Lock()
	defer entryMu.Unlock()
	out := make(map[string]bool, len(builtEntries))
	for n := range builtEntries {
		out[n] = true
	}
	return out
}

// EntryThm returns the lazy statement-promise serving entry e.
// Cheap to call (the proof runs only at force time), memoized per
// entry so diamond deps share one build. penv is the corpus env
// (possibly mid-init: this is called from env()'s bootstrap, so it
// must not call env() itself).
//
// The promise is declared at the entry's statement — the form the
// entry's own file signs — and the force closure bridges the built
// theorem to it where the two α-differ (a Derived member's ε-derived
// top).
func EntryThm(penv *proof.ProverEnv, entry registry.EntryLike) core.Thm {
	e := entry.Entry()
	entryMu.Lock()
	defer entryMu.Unlock()
	if t, ok := entryPromises[e.Name]; ok {
		return t
	}
	if e.ServedAsAxiom() {
		t := EntryAxiom(e)
		entryPromises[e.Name] = t
		return t
	}
	stmt := e.Statement().Prop
	t := core.Promise(stmt, func(f core.Forcer) core.ThmCert {
		// (1) Realize the deps first — sibling entries recurse through
		// their own promises (the registry DAG is compiler-checked
		// acyclic; core's promise dependency graph backstops).
		deps := e.ServedDeps()
		certs := make([]core.ThmCert, len(deps))
		for i, dep := range deps {
			certs[i] = f.Force(core.AsThm(EntryThm(penv, dep)))
		}
		// (2) Fresh build env (the isolation contract above).
		noteEntryBuilt(e)
		benv := newEntryBuildEnv(e, deps, certs)
		benv.Forcer = &f
		// (3) Run the Build under the entry's identity — Builds
		// read env.Scope via NewScriptForEntry; the proof file never
		// spells its own key.
		benv.Scope = proof.NewProofScope(core.PropKey(e.Key))
		built, _ := e.Build.Fn(benv)
		cert := f.Force(core.AsThm(built))
		// (4) Bridge to the declared statement where the built top's
		// α-form differs from it (the Sections/Derived machine-form
		// fallback). BridgeNormalize is kernel-faithful; nil means the
		// entry's recorded statement and its proof have genuinely
		// diverged — a defect, not a shape to route around.
		if cert.AlphaEquals(stmt) {
			return cert
		}
		bridged := prop.BridgeNormalize(stmt, cert)
		if bridged == nil {
			panic(fmt.Sprintf("EntryThm %s: built theorem does not normalize-coincide with the declared statement (%s)",
				e.Name, stmt.AlphaKey()))
		}
		return f.Force(core.AsThm(bridged))
	})
	entryPromises[e.Name] = t
	return t
}

// EntryAxiom mints the axiom a member with no proof is served as: a
// card's `⊢ <statement>`, its closed statement verbatim
// (registry.CardStatement refuses a sequent), or the postulate's
// `⊢ <term>`, the term its chapter builds (registry.PostulateTerm
// checks it against the statement). A realized certificate, not a
// promise — there is no proof to run at force time. The one mint for
// both consumers: the session (EntryThm) and the replay harness (its
// dep resolver).
func EntryAxiom(e *registry.ProofEntry) core.ThmCert {
	if e.IsPostulate() {
		return core.NewAxiom(e.PostulateTerm().Conclusion())
	}
	return core.NewAxiom(e.CardStatement().Conclusion())
}

// newEntryBuildEnv constructs the fresh env one Build runs
// on: const-meta wiring as NewSeedEnv, the entry's dep certs as its
// whole named library, and the family CNF store installed strict — the
// same regime the replay harness verified the proof under.
func newEntryBuildEnv(e *registry.ProofEntry, deps []*registry.ProofEntry, certs []core.ThmCert) *proof.ProverEnv {
	mgr := registry.GetConstMetaManager()
	var cnfCache ext.TermKeyPropMap
	benv := &proof.ProverEnv{
		ProofService: &proof.ProofService{
			LoadConstMeta:        mgr.LoadConstMeta,
			LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
			Syntax:               mgr,
			TypeArity:            mgr.TypeArity,
		},
		CnfRefuterTimeout:     5 * time.Second,
		CnfNormalizationCache: &cnfCache,
		CnfNormalizeCache:     proof.NewCNFNormalizeCache(),
		LibraryThms:           make(map[string]core.Thm, 2*len(deps)),
	}
	for i, dep := range deps {
		registry.InstallLibraryDep(benv, dep, certs[i])
	}
	if store := e.Family().CNFStore(); store != nil {
		benv.InstallCNFStore(store)
	}
	return benv
}

// fromEntry binds an omega bundle field to an entry in its NORMAL
// form: the statement's Normalize form, the canonical spelling the
// entry's key names — so an omega leaf written against that form reads
// one fixed binder order and orientation, whatever binder order and
// orientation the entry itself states.
// Statement-level and promise-transparent: nothing is forced here. Also
// the IntBridges binding (normalize-first, the principle
// Script.IntOfRealDerive's source canonicalization follows — the
// bridges are consumed as pattern rewrites, binder-order-insensitive).
func fromEntry(entry registry.EntryLike) *prop.PropWrapper {
	norm, _ := prop.Normalize(prop.WrapProp(EntryThm(env(), entry)))
	return prop.WrapProp(norm)
}

// fromReading binds a structure law read at a carrier's instance entry
// — `field.InvMul` at `real_field.Field` is ℝ's `real_inv(x * y) =
// real_inv(x) * real_inv(y)` — the theorem the kernel derives from the
// two (proof.ReadLawAt, the derivation a proof's `law.Read(instance)`
// cite makes), normalized as fromEntry normalizes an entry's. Its
// statement is no entry's, so the field binding it names its two
// sources as capability roots (entryKeys(law, instance)).
func fromReading(law, instance registry.EntryLike) *prop.PropWrapper {
	read, err := proof.ReadLawAt(EntryThm(env(), law), EntryThm(env(), instance))
	if err != nil {
		panic(fmt.Sprintf("fromReading(%s at %s): %v", law.Entry().Name, instance.Entry().Name, err))
	}
	norm, _ := prop.Normalize(prop.WrapProp(read))
	return prop.WrapProp(norm)
}

// fromEntryAsStated binds an entry in the form its file STATES,
// ∀-closed (forallCloseFrees) — for the statements omega consumes in
// their stated spelling rather than their normal form: the definitional
// equation packs (Sub, nat_pow, factorial, real_pow — conjunctions of
// ∀-clauses a leaf projects), nat_order.LessEqOfEq, and the ℤ lifts
// AbsEven, AbsIdempotent and SgnOdd, whose leaves instantiate the
// stated equation positionally.
func fromEntryAsStated(entry registry.EntryLike) *prop.PropWrapper {
	return forallCloseFrees(prop.WrapProp(EntryThm(env(), entry)))
}

// entryKeys spells capability roots as the entries' own keys — the
// corpus DAG's node keys for entries. It takes the entries themselves
// (typed references), so there is nothing to look up.
func entryKeys(entries ...registry.EntryLike) []core.PropKey {
	out := make([]core.PropKey, len(entries))
	for i, e := range entries {
		out[i] = core.PropKey(e.Entry().Key)
	}
	return out
}
