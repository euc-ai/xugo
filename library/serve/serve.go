// Package serve is the library's export surface: how a proved chapter
// reaches a consumer that must not import the chapters. Omega and the
// engine's auto-match both need named library theorems, and neither may
// depend on library/proofs — so the dependency is inverted here, and
// this package hands them what they need at startup.
//
// It builds a self-contained ProverEnv (const-meta from the process-global
// ConstMetaManager — the engine's built-ins and the chapters' mints, the
// only constants the corpus knows) and exposes the corpus through four
// seams:
//
// - InstallNatBundle / InstallRealBundle / InstallIntBundle — fill omega's
// per-domain *LemmaBundle from the corpus, so each ring / norm_num /
// order leaf reads a real, lazily-built Thm rather than a fabricated
// placeholder. InstallIntBundle also installs the IntBridges (the
// homomorphism theorems IntOfRealThm consumes) and chains into
// InstallIntLemmaBundle.
// - RegisterAll — registers every entry on a live env as a lazy builder
// under its own key, so the engine's auto-match settles a proved-earlier
// leaf with the dep's real promise (PromiseByKey) instead of a
// placeholder.
// - EntryThm — serves one entry as a promise; the single-entry form the
// other two are built on (promise.go).
// - PromiseForGeneral — the shape adapter each bundle's `fromGeneral(...)`
// field routes through: it takes a leaf-wanted general shape, normalizes
// it to a key, resolves that key to the entry answering for it, and
// reconstructs the result back to the general shape on the way out.
//
// Bundle fields are TYPED entry references (`fromEntry(nat_arith.AddSym)` in
// promise.go), and the served form is the entry's own recorded form.
//
// foundation.go computes the self-circularity gate's bundle-foundation
// closure.
//
// Why a DEDICATED env, not the live engine env: an entry's build replays
// under its family's CNF store installed strict (env.InstallCNFStore sets
// env.RequireCNFCacheHit = true) — installing the corpus's CNF stores into a
// live session env would make the agent's own non-cache-backed Auto/refute
// steps panic on a miss. Builds run on fresh envs seeded from this one
// (promise.go), never on a session's. A forced ThmCert is a kernel object
// valid in any env, so certificates built here compose into session
// derivations freely.
//
// num_induction is this env's num-induction principle (LibraryThms), read by
// the induction tactic when the arithmetic theorems proved BY induction
// replay. It is proved NON-circularly (from is_num / mk_num, no induction
// step) and served by the chapter's own proof — peano.Induction, through the
// promise.go seam.
package serve

import (
	"sync"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	// The datatype principles (list_induction, list_recursion and option's
	// twins) reach this env by name alone, through the ServesAs loop
	// over the registered corpus: the domain is imported for its
	// registration, not for a typed reference.
	_ "github.com/euc-ai/xugo/library/proofs/datatypes"
	"github.com/euc-ai/xugo/library/proofs/relations/well_founded"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"

	"fmt"
)

var (
	envOnce sync.Once
	corpEnv *proof.ProverEnv
)

// env returns the shared dedicated corpus env, constructed once. Mirrors
// testenv.MakeT's construction (global const-meta + CNF normalization
// caches + the induction principles) but with no testing dependency, and
// with every principle served by its chapter proof rather than trusted.
func env() *proof.ProverEnv {
	envOnce.Do(func() {
		// A type a chapter minted at init on the promise of its
		// inhabitation entry forces that promise through here — the
		// entry's own proof, never a trust.
		registry.ForceEntry = func(f core.Forcer, e *registry.ProofEntry) core.ThmCert {
			return f.Force(core.AsThm(EntryThm(corpEnv, e)))
		}
		mgr := registry.GetConstMetaManager()
		var cnfCache ext.TermKeyPropMap
		corpEnv = &proof.ProverEnv{
			ProofService: &proof.ProofService{
				LoadConstMeta:        mgr.LoadConstMeta,
				LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
				Syntax:               mgr,
				TypeArity:            mgr.TypeArity,
			},
			CnfRefuterTimeout:     5 * time.Second,
			CnfNormalizationCache: &cnfCache,
			CnfNormalizeCache:     proof.NewCNFNormalizeCache(),
			LibraryThms:           map[string]core.Thm{},
		}
		// Register the corpus by key so PromiseByKey can resolve a
		// Normalize-produced key. Cheap — closures only; no proof runs
		// until a key is forced (and nothing below forces: the entry
		// builders call env() at force time, which would deadlock inside
		// this Once). This is what PromiseForGeneral relies on.
		RegisterAll(corpEnv)
		// The corpus is the name surface: an entry that ServesAs a
		// library-convention name (num_induction, num_recursion,
		// wellfounded_recursion, fst, family_cons, …) is
		// bound under it, so the induction/recursion schema lookups and
		// the define door resolve to a hand-authored proof. A name no
		// entry serves is simply not bound, and a consumer of one gets
		// `no library theorem … is bound in this env`. Lazy: the
		// statement now, the proof at force (EntryThm's promise), and NO
		// ThmCache deposit. Every principle is bound as stated: the
		// induction tactic reads the standard form `∀P x. cases ⇒ P(x)`
		// (tactic.AnalyzeInductionPrinciple), which peano.Induction states
		// for num and the datatype door derives for a datatype
		// (list_induction, list_recursion, option's twins).
		//
		// EntryThm takes the in-progress env as an argument and never
		// calls env() itself, which would re-enter envOnce.Do and deadlock
		// if forced during init.
		for _, e := range registry.All() {
			if e.ServesAs == "" {
				continue
			}
			// The entry's statement AS STATED — not its Normalize form:
			// the consumers read the shape rather than the key (the
			// define door's datatype kit projects family_cons's two clauses
			// positionally and reads recspace_recursion's binders), and
			// normalizing would hoist inner ∀s and re-orient equations.
			// Promise-transparent: nothing forces here.
			corpEnv.LibraryThms[e.ServesAs] = EntryThm(corpEnv, e)
		}
		// The datatype RECURSION schemas (`<base>_RECURSION`, which the
		// define door's equation compiler looks up by name —
		// tactic.RecursionPrincipleNameCandidates) are bound by the
		// ServesAs loop above: the datatype door derives each in the
		// shape AnalyzeRecursionPrinciple parses (∀-prefix over the
		// parameters, ∃fn, one equation per constructor).
		//
		// The WF schema rows serve from the wellfounded chapter: the WF
		// equation compiler consumes these names (CompileWFExistence — it
		// accepts both arrangements, so the chapter's spelling is drop-in),
		// and the imported rows it replaced could not force their own cones
		// (the list_recursion class of corpus condition — a promise
		// dependency cycle), while this cone does.
		// No bridge: the compiler reads the served form directly.
		for _, spec := range []struct {
			name  string
			entry registry.EntryLike
		}{
			{proof.WFRecName, well_founded.Recursion},
			{proof.WFMeasureName, well_founded.Measure},
		} {
			corpEnv.LibraryThms[spec.name] = EntryThm(corpEnv, spec.entry)
		}
	})
	return corpEnv
}

// InductionPrinciples returns the corpus-backed induction principles as
// the analyzer reads them (LibraryThms name → promise-backed Thm; the
// real kernel proof is deferred to first force). Engine/serve envs overlay
// these over their core.TestThm fallbacks so the `induction` tactic runs on
// honest theorems for every type the corpus covers (num, list, option, …).
// A name no corpus entry proves is absent — the caller keeps its own
// fallback for those.
func InductionPrinciples() map[string]core.Thm {
	shared := env()
	out := make(map[string]core.Thm, len(shared.LibraryThms))
	for name, thm := range shared.LibraryThms {
		if thm != nil {
			out[name] = thm
		}
	}
	return out
}

// NewSeedEnv returns a FRESH ProverEnv wired like the shared corpus env
// (const-meta, CNF caches, induction principles) — one Build per env,
// the replay-harness contract, for tests and probes that run a single
// entry's Build. The induction-principle entries are shared from the
// corpus env: a promise/cert is a kernel object valid in any env.
func NewSeedEnv() *proof.ProverEnv {
	shared := env() // ensures once-init: the principle bootstrap
	mgr := registry.GetConstMetaManager()
	var cnfCache ext.TermKeyPropMap
	libraryThms := make(map[string]core.Thm, len(shared.LibraryThms))
	for name, thm := range shared.LibraryThms {
		libraryThms[name] = thm
	}
	return &proof.ProverEnv{
		ProofService: &proof.ProofService{
			LoadConstMeta:        mgr.LoadConstMeta,
			LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
			Syntax:               mgr,
			TypeArity:            mgr.TypeArity,
		},
		CnfRefuterTimeout:     5 * time.Second,
		CnfNormalizationCache: &cnfCache,
		CnfNormalizeCache:     proof.NewCNFNormalizeCache(),
		LibraryThms:           libraryThms,
	}
}

// RegisterAll registers the corpus on liveEnv as lazy by-key builders, so
// the engine's auto-match / `known` paths can settle a proved-earlier leaf
// with the dep's real (lazy, kernel-gated) promise via
// liveEnv.PromiseByKey(key, stmt) instead of a fabricated core.TestThm. A
// builder runs against the dedicated corpus env; the realized ThmCert is
// a kernel object valid in liveEnv. (Auto-match gap "C".)
//
// Registration is cheap — it only stores closures; no proof is defined or
// forced until a key is actually required.
//
// The population is the proof registry, each entry under its own key
// (registry.ProofEntry.Key — the statement's normalized key, what
// PromiseForGeneral's Normalize-then-look-up, a session citing a
// member by key, and the engine's corpusBackedInjection hand in). No
// statement is parsed: every key is a literal. The builder forces the entry
// through promise.go's EntryThm on the corpus env — which must
// be initialized by force time; the env bootstrap registers but never
// forces. A key no entry answers for resolves to nothing: the
// engine's channel treats a nil promise as "no corpus theorem", and
// PromiseForGeneral panics — the right failure for a statement the
// corpus does not have. Only the entries' own keys are registered; the
// by-NAME channel — the induction and recursion principles and the WF
// schemas the env bootstrap binds into LibraryThms — is separate.
//
// A requested shape is served through the identity relation, not
// α-equality: a builder settles at the entry's own headline, and
// PromiseByKey bridges it to the caller's statement with
// BridgeNormalize, which panics loudly when the two are not
// normalize-coincident.
//
// One `_BuilderEntry.once` cell per key.
func RegisterAll(liveEnv *proof.ProverEnv) {
	for _, ce := range registry.All() {
		ce := ce
		builder := func(f core.Forcer) core.ThmCert {
			return f.Force(core.AsThm(EntryThm(env(), ce)))
		}
		liveEnv.RegisterBuilder(core.PropKey(ce.Key), builder)
	}
}

// forallCloseFrees ∀-closes the free term variables of a statement's
// conclusion via real generalization steps (prop.ConclForAll) over
// the wrapped promise — a DERIVED wrapper, never a re-statement, so the
// underlying core.Promise's settle gate still checks the FREE-VAR-form cert
// against the FREE-VAR-form Stmt it was declared with.
//
// Why: a statement in free-var sequent form (`x:int, y:int ⊢ int_abs(x * y)
// = …` — declared variables, no term-level ∀) cannot serve a leaf as-is.
// Omega's leaf macro layer (macroEq/macroThm → instAll = ConclForAllInsts)
// no-ops on a non-∀-headed conclusion, so a bundle field bound to such a Stmt
// as-is can NEVER α-match its concrete instantiation — the leaf then dies at
// the production placeholder-panic seam. fromEntryAsStated therefore closes
// the statement here at bind time.
//
// Binder order: Frees enumerates first occurrence left-to-right (fun before
// arg) — the order each omega leaf passes its instAll args in.
// ConclForAllList makes the first var outermost. Vars free in a hypothesis are
// skipped (the ConclForAll guard); a ∀-closed or var-free conclusion is a
// no-op, so wrapping every fromEntryAsStated binding is safe.
func forallCloseFrees(w *prop.PropWrapper) *prop.PropWrapper {
	frees := w.Conclusion().Frees(func(v core.VarTerm) bool {
		return prop.NotFreeInHyps(w, v)
	})
	if len(frees) == 0 {
		return w
	}
	return w.ConclForAllList(frees...)
}

// PromiseForGeneral is the unified shape-adapter seam. Given a Prop in the
// caller's preferred (GENERAL) shape, it returns a lazy Prop in that same
// shape, sourced from the corpus entry its NORMALIZED form's key names.
//
// Construction-time work is ZERO — this is a graph constructor: it stores a
// closure but runs nothing. All work happens on force:
//
// 1. Normalize(general) — pure term work — yields the normalized prop + its
// reconstruct callback.
// 2. Look up the normalized key in the corpus (RegisterAll's registration).
// 3. Force the corpus promise to a kernel cert (the entry's Build runs once,
// memoized per entry in EntryThm).
// 4. Apply reconstruct → cert of the general shape.
// 5. Assert IsStronger(out, general) as the soundness gate.
//
// A bundle field that is never consumed pays nothing — not even Normalize.
// Replaces hand-rolled per-leaf adapters (CurryDisj2/CurryIffConj/
// SwapPremises2/ReorderForall/MulCancelToScale/DeriveLessEqOfEqSwapped in omega). Any
// consumer that wants a corpus theorem in a specific non-normalized shape
// just declares that shape and calls this.
func PromiseForGeneral(general core.Prop) core.Prop {
	return promiseForGeneralOn(env(), general)
}

// promiseForGeneralOn is the internal variant taking an explicit env, used
// inside envOnce.Do to avoid re-entering env() (which would deadlock the
// sync.Once). Identical semantics to PromiseForGeneral.
func promiseForGeneralOn(e *proof.ProverEnv, general core.Prop) core.Prop {
	return core.Promise(general, func(f core.Forcer) core.ThmCert {
		// All work — including Normalize — fires here at force time. Graph
		// constructor discipline: a field never consumed pays nothing.
		normalized, reconstruct := prop.Normalize(general)
		key := normalized.AlphaKey()
		// The entry whose own key this is first, through the seam rather
		// than the env's builder registry: the seam's promise is bridged
		// to the normalized form here and never memoized into the env's
		// ThmCache, so a caller asking the same key in another spelling
		// still reaches the entry rather than a cached bridge. The env's
		// by-key channel (PromiseByKey) is the fallback.
		normPromise := entryNormalizedPromise(e, key, normalized)
		if normPromise == nil {
			normPromise = e.PromiseByKey(key, normalized)
		}
		if normPromise == nil {
			panic(fmt.Sprintf("PromiseForGeneral: no corpus theorem registered for "+
				"normalized key %s (from general %v)", key, general))
		}
		normCert := f.Force(core.AsThm(normPromise))
		out := reconstruct(prop.WrapProp(normCert))
		if !prop.IsStronger(out, general) {
			panic(fmt.Sprintf("PromiseForGeneral: reconstruct produced %v, not stronger "+
				"than requested general %v", out, general))
		}
		return out.AsThmCert()
	})
}

// entryNormalizedPromise returns a promise of `normalized` backed by
// the entry that answers for key — the entry's own key — or nil when
// no linked entry does. penv is the stmt-capable corpus env the seam
// parses against.
func entryNormalizedPromise(penv *proof.ProverEnv, key core.PropKey, normalized core.Prop) core.Prop {
	ce, ok := registry.ByKey(string(key))
	if !ok {
		return nil
	}
	return core.Promise(normalized, func(f core.Forcer) core.ThmCert {
		cert := f.Force(core.AsThm(EntryThm(penv, ce)))
		if cert.AlphaEquals(normalized) {
			return cert
		}
		bridged := prop.BridgeNormalize(normalized, prop.WrapProp(cert))
		if bridged == nil {
			panic(fmt.Sprintf("PromiseForGeneral: entry %s does not normalize-coincide with the requested form %s",
				ce.Name, key))
		}
		return f.Force(core.AsThm(bridged))
	})
}
