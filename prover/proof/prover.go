package proof

import (
	"fmt"
	"maps"
	"slices"
	"sync"
	"time"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/clause"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/euc-ai/xugo/utils"
)

type ProofService struct {
	LoadConstMeta        func(name core.TermName) (core.ConstTermMeta, bool)
	LoadOrStoreConstMeta func(meta core.ConstTermMeta) (core.ConstTermMeta, bool)

	// CNFStore is the certificate + plan store a recorded refute-closing
	// step reads back at replay (cnf_store.go). nil = no store: live
	// refutes and conditioning searches run and persist nothing, so
	// nothing recorded under such an env replays strictly — the shape
	// of a white-box test engine, never of a session that emits.
	CNFStore CNFStore

	// RangeConstMeta enumerates every registered const meta, stopping
	// early when yield returns false. Optional (nil = enumeration
	// unavailable); backs the datatype kit's type-name-in-use probe
	// (TypeNameInUseProbe) — type identity is structural, so freshness
	// of a new type name can only be checked by scanning what the
	// registered constants' types mention. Wired from the process
	// ConstMetaManager wherever that is the backing store.
	RangeConstMeta func(yield func(core.ConstTermMeta) bool)

	// TypeArity is the corpus's type vocabulary — the arity of a type
	// constructor some registered constant's type mentions — for the
	// text parser's type-name check (dsl.ParseScope.TypeResolver).
	// Wired from the process ConstMetaManager beside Syntax; nil
	// leaves type names unchecked.
	TypeArity func(name string) (arity int, ok bool)

	// Syntax is the corpus's constant syntax — implicit leading binders
	// and outfix notations declared at the chapters' definitions
	// (registry.DefEntry.Implicit / Notation) — for the text parser
	// (ext/dsl/implicit.go, outfix.go). Wired from the process
	// ConstMetaManager wherever that is the backing store; nil means no
	// constant declares any.
	Syntax dsl.SyntaxTable
}

// MockConstMetaService creates a minimal ProofService for const meta.
func MockConstMetaService() *ProofService {
	constMetaMap := ext.InitConstMetaMap()
	return &ProofService{
		LoadConstMeta: constMetaMap.Load,
		LoadOrStoreConstMeta: func(meta core.ConstTermMeta) (core.ConstTermMeta, bool) {
			return constMetaMap.LoadOrStore(meta.Name(), meta)
		},
	}
}

type ProverEnv struct {
	ProofService *ProofService

	// Scope, when non-nil, is harness-armed proof identity: the replay /
	// recorder / probe harness constructs it from the registry entry
	// (NewStaticProofScope(entry.Key, entry.Capabilities...)) before
	// invoking Build, and the proof body picks it up via
	// NewScriptForEntry(env). This keeps the target key and capability
	// declaration out of proof text entirely — identity lives in
	// the ProofEntry, and the arming site is the layer that already owns
	// it. One env = one Build: an env with an armed Scope must not be
	// reused to build a DIFFERENT entry (deps are preloaded
	// certs, never nested Builds, so this holds by construction in the
	// harnesses; resolveDep-style lazy dep builders re-arm around their
	// Build call).
	Scope *ProofScope

	// Forcer binds synchronous forced reads during a promise's Build to
	// that builder. Nil means the env is being used outside a promise build.
	Forcer *core.Forcer

	// amortizes proof replay cost by holding kernel certificates across proof scopes
	// within one ProverEnv.
	ThmCache ThmCache

	// LibraryThms holds preloaded template theorems needed by compound tactics.
	// Keyed by theorem name (e.g. "num_induction"). Each tactic that depends on
	// a library theorem looks it up here; if absent, the tactic is unavailable.
	// Populated lazily from the DB by the caller (e.g. Searcher).
	//
	// Values are core.Thm (proven-or-provable), not realized ThmCert: a
	// promise-backed principle (e.g. the corpus's lazily-built num_induction)
	// stays UNFORCED here. The only consumer, AnalyzeInductionPrinciple, reads
	// just the statement, and the induction reconstruct threads the principle
	// through promise-transparent kernel ops — so the cone forces only when an
	// induction-using proof is itself forced, not at env bootstrap.
	LibraryThms map[string]Thm

	// LibraryResolver, when set, answers a library-theorem read that
	// neither LibraryThms nor the runtime overlay binds. The replay
	// harness and the CNF recorder serve a chapter member's corpus deps
	// through it instead of preloading them, so every name the member's
	// proof reads passes here and its dependencies are observed, not
	// declared. It is asked on every such read; ok=false is a miss,
	// exactly as an unbound name.
	LibraryResolver func(name string) (Thm, bool)

	// RequireCNFCacheHit, when true, forbids tryCNFRefute from running the
	// live refuter: a CNF refute that reaches the resolution stage MUST be
	// served from the stored cache (the family blob at replay, the
	// session's store in emit's CollectCNFCache). A cache MISS — or a
	// stored proof that fails to reconstruct — panics instead of silently
	// re-proving.
	//
	// The silent live-refute fallback it disables was actively harmful: it
	// masked the real signal (a recording/replay divergence, a stale
	// cnf_proofs row) by making every cache failure look identical to a
	// cache success, so a "passing" replay could secretly be re-deriving the
	// proof live (and flakily, under the per-call timeout). Set by
	// InstallCNFStore (replay) and on the env CNFCaptureEnv builds for
	// emit's CollectCNFCache. It stays false on the live prover / session
	// paths, where running the refuter IS the intended primary behavior,
	// not a fallback.
	RequireCNFCacheHit bool

	// CNFCacheCaptureOnly, when true, makes tryCNFRefute confirm-and-return
	// on a cache HIT WITHOUT reconstructing the stored proof: it reads the
	// blob (so a CapturingCNFStore in front of the store can capture it) and closes the step
	// with a reconstruct-at-force promise (captureOnlyClosePromise) — an
	// honest IOU that stays unforced on the capture pass's throwaway goal
	// stacks, never a fabricated cert. Set ONLY on the env CNFCaptureEnv
	// builds for emit's CollectCNFCache, alongside RequireCNFCacheHit.
	//
	// Rationale: the collection answers which certificates a member's
	// replay reads — obtained from the reads alone. Reconstruction
	// (replaying the stored clause certificate) is the replay's
	// responsibility, which is where a reconstruction failure is correctly
	// located and meaningful. Doing it at emit would (a) needlessly run the
	// refuter on every cache hit and (b) turn any nondeterminism in
	// reconstruction into a misleading emit failure. A genuine MISS is
	// unaffected: it still trips the RequireCNFCacheHit panic.
	CNFCacheCaptureOnly bool

	// ByAuditReport, when non-nil, arms the economy audit
	// in the By executor: after each successful By close it probes
	// downward — refute → Basic(), shaped → each shape element
	// removed — and reports what closes cheaper as a lint-style
	// finding naming the honest spelling. The recorder harness is the
	// ONLY wirer (recording is the live run, which is what the probes
	// re-run against); sessions and every replay path leave it nil,
	// at zero cost — a session's `by` asks for the first probe alone,
	// per call (BySpec.Report). Findings are messages — the recording
	// and the member text are untouched.
	ByAuditReport func(finding string)

	CnfRefuterTimeout time.Duration
	// CnfNormalizationCache is the legacy single-level cache used by
	// refuter.CreateRefuter (full pipeline). Keyed on raw-hyp alpha key,
	// stores the whole cnfNormalizeWorkFlow output.
	CnfNormalizationCache *ext.TermKeyPropMap
	// CnfNormalizeCache is the two-level cache used by
	// refuter.CreateRefuterFromPreNormalized (the prelude/middle/tail
	// split). PreCNF level is keyed on raw-hyp alpha key (term-level
	// PreCNFNormalize result, sharable with prop.Normalize); Tail level is
	// keyed on the pre-CNF alpha key (Skolem + tail rewrite). May be nil to
	// let tryCNFRefute initialize it lazily.
	CnfNormalizeCache *clause.CNFNormalizeCache

	cnfNormalizeCacheMu sync.Mutex

	// theorems is the lazy namespace of buildable named theorems (key → root
	// promise). Accessed via Theorems(); lazily created so the many
	// struct-literal ProverEnv construction sites need not initialize it.
	theorems   *TheoremRegistry
	theoremsMu sync.Mutex

	// dynLibraryThms is the RUNTIME overlay over LibraryThms: named
	// principles installed AFTER env construction — the session
	// `define` move's derived datatype principles (<T>_INDUCT /
	// <T>_RECURSION), since a session mint is process-global ("LibraryThms
	// writes under the engine lock" — this map carries its own lock so
	// a session's install cannot race another session's principle
	// lookup on the shared engine env; the LibraryThms map itself
	// stays construction-time-immutable). Read through
	// LookupLibraryThm; written through InstallLibraryThm. LibraryThms
	// wins on a name collision — the overlay refuses to shadow a
	// construction-time binding.
	dynLibraryThms   map[string]Thm
	dynLibraryThmsMu sync.Mutex
}

// LookupLibraryThm resolves a named library theorem: the
// construction-time LibraryThms map first, then the runtime overlay
// (InstallLibraryThm), then LibraryResolver. It is the one read of a
// library theorem — a cite of a corpus entry (Script.LibraryThm), the
// induction dispatch, Script.Induct replay and the recursion-schema
// compile all read through it — so a session-defined datatype's
// principles resolve exactly like the corpus-served ones, and a
// resolver sees every name a proof reads that nothing preloaded.
func (env *ProverEnv) LookupLibraryThm(name string) (Thm, bool) {
	if thm, ok := env.LibraryThms[name]; ok && thm != nil {
		return thm, true
	}
	env.dynLibraryThmsMu.Lock()
	thm, ok := env.dynLibraryThms[name]
	env.dynLibraryThmsMu.Unlock()
	if ok && thm != nil {
		return thm, true
	}
	if env.LibraryResolver != nil {
		thm, ok := env.LibraryResolver(name)
		return thm, ok && thm != nil
	}
	return nil, false
}

// InstallLibraryThm installs a named theorem into the runtime overlay
// (see LookupLibraryThm). Exclusive against both the overlay and the
// construction-time map: a name already bound errors — the
// session-mint ruling's collision-errors-never-shadows discipline.
func (env *ProverEnv) InstallLibraryThm(name string, thm Thm) error {
	if thm == nil {
		return fmt.Errorf("InstallLibraryThm(%q): nil theorem", name)
	}
	if existing, ok := env.LibraryThms[name]; ok && existing != nil {
		return fmt.Errorf("library theorem %q is already bound in this env", name)
	}
	env.dynLibraryThmsMu.Lock()
	defer env.dynLibraryThmsMu.Unlock()
	if _, ok := env.dynLibraryThms[name]; ok {
		return fmt.Errorf("library theorem %q is already installed in this env", name)
	}
	if env.dynLibraryThms == nil {
		env.dynLibraryThms = map[string]Thm{}
	}
	env.dynLibraryThms[name] = thm
	return nil
}

func NewCNFNormalizeCache() *clause.CNFNormalizeCache {
	var preCNFCache clause.PreCNFCache
	var cnfTailCache ext.TermKeyPropMap
	return &clause.CNFNormalizeCache{
		PreCNF: &preCNFCache,
		Tail:   &cnfTailCache,
	}
}

// InstallCNFCache decodes a recorded CNF blob into a store in front of
// env.ProofService.CNFStore and sets env.RequireCNFCacheHit — the
// raw-bytes form of InstallCNFStore. After this call, Auto /
// tryCNFRefute / the By conditioning stage resolve via the in-memory
// tables (both certificates and plans, decoded from blob) before falling
// back to whatever store the env already held (engine.SessionCNFStore,
// a test store, or nothing at all) — and a
// refute that finds NOTHING in either panics rather than re-proving
// live.
//
// The blob is a family's shared recording, <family>.cnf.pb, written by
// the family CNF recorder and //go:embed'd as registry.Family.CNF. The
// replay harness installs it through InstallCNFStore (Family.CNFStore
// decodes it once per process); this form serves a caller holding only
// the bytes.
//
// Layering: missed lookups fall through to the prior store before the
// strict miss-panic fires — so an unrelated caller's DB-backed CNF read
// still works; the embedded blob is the fast path on top. Writes go to
// the prior store; the blob is never written at replay.
//
// Strictness (RequireCNFCacheHit): installing a cache asserts the proof
// is fully cache-backed, so a genuine miss (or a stored proof that fails
// to reconstruct) is a bug — a recording/replay divergence or a stale
// recording — and panics with a descriptive message instead of being
// masked by a silent, flaky live re-proof. The strict gate does NOT
// extend to plans — a By leaf recorded before the grounding stage
// existed has no plan entry, and its conditioning replays as the
// deterministic stages alone (a plan MISS in strict mode is a no-op,
// never a panic; the certificate lookup downstream is where strictness
// bites). The live prover and session paths install no cache, so they
// keep the live refuter.
//
// Panics on unmarshal failure (DecodeCNFCache).
func (env *ProverEnv) InstallCNFCache(blob []byte) {
	env.InstallCNFStore(NewMemoryCNFStoreFrom(DecodeCNFCache(blob)))
}

// DecodeCNFCache unmarshals a recorded CNF blob. Panics on failure —
// a blob is a build-tree artifact (//go:embed'd from a file the
// recorder controls), so a corrupt one is a tree inconsistency, not a
// runtime input.
func DecodeCNFCache(blob []byte) *CNFCache {
	var cache CNFCache
	if err := proto.Unmarshal(blob, &cache); err != nil {
		panic(fmt.Sprintf("DecodeCNFCache: unmarshal: %v", err))
	}
	return &cache
}

// InstallCNFStore is InstallCNFCache for a blob already decoded into
// a store: a family's recorded certificates are decoded ONCE per
// process (registry Family.CNFStore) and every env that
// replays one of its members installs that same store. Sound to share
// because the installed store is only ever read — writes go to the
// env's own store behind it (embeddedCNFStore) — and MemoryCNFStore
// serializes its reads.
func (env *ProverEnv) InstallCNFStore(front *MemoryCNFStore) {
	if env.ProofService == nil {
		env.ProofService = &ProofService{}
	}
	env.ProofService.CNFStore = embeddedCNFStore{front: front, back: env.ProofService.CNFStore}
	// Installing an embedded cache asserts the proof is fully cache-backed:
	// every CNF refute the Build reaches must resolve from this blob.
	// Enforce that — a miss now panics instead of silently (and flakily)
	// re-proving live. See ProverEnv.RequireCNFCacheHit.
	env.RequireCNFCacheHit = true
}

// CNFCaptureEnv is the env emit's CollectCNFCache walks a recorded proof
// under: this env's proof service with store in the CNFStore slot,
// strict (RequireCNFCacheHit) and capture-only (CNFCacheCaptureOnly).
// The receiver is read and never written — the engine's one env serves
// every session of a serve, and a collection's mode is the collection's
// alone, so a session refuting live on this env while a collection runs
// keeps its own store and its live refuter.
//
// The derived env shares what the closers read: the scope, the Forcer, the named
// library and its resolver, the theorem registry (whose cache stays this
// env's), the normalization caches, the audit hook and the refuter
// timeout. The runtime library overlay is copied under its lock, since
// each env guards its overlay with a lock of its own. The ThmCache
// starts empty: the By, SetTac and refute executors read theorems
// through the registry, never from the env's cache.
//
// Built by field, not copied: ProverEnv holds locks and sync maps, so a
// copy of the value is not a well-formed env. ProofService is a value of
// its own because the slot store replaces lives behind that shared
// pointer, where a copy of the env alone would still write through.
func (env *ProverEnv) CNFCaptureEnv(store CNFStore) *ProverEnv {
	service := *env.ProofService
	service.CNFStore = store
	env.dynLibraryThmsMu.Lock()
	overlay := maps.Clone(env.dynLibraryThms)
	env.dynLibraryThmsMu.Unlock()
	return &ProverEnv{
		ProofService:          &service,
		Scope:                 env.Scope,
		Forcer:                env.Forcer,
		LibraryThms:           env.LibraryThms,
		LibraryResolver:       env.LibraryResolver,
		RequireCNFCacheHit:    true,
		CNFCacheCaptureOnly:   true,
		ByAuditReport:         env.ByAuditReport,
		CnfRefuterTimeout:     env.CnfRefuterTimeout,
		CnfNormalizationCache: env.CnfNormalizationCache,
		CnfNormalizeCache:     env.cnfNormalizeCache(),
		theorems:              env.Theorems(),
		dynLibraryThms:        overlay,
	}
}

func (env *ProverEnv) cnfNormalizeCache() *clause.CNFNormalizeCache {
	env.cnfNormalizeCacheMu.Lock()
	defer env.cnfNormalizeCacheMu.Unlock()
	if env.CnfNormalizeCache == nil {
		env.CnfNormalizeCache = NewCNFNormalizeCache()
	}
	return env.CnfNormalizeCache
}

// asRealizedThm collapses a node certificate Prop to its realized kernel
// ThmCert. It accepts a ThmCert (identity) or an already-FORCED ThmPromise
// (returns its settled cert) — but panics on an UNFORCED promise, since there
// is no certificate to give. Use it only at boundaries that legitimately need
// the concrete cert NOW (ProvedThm(), the ThmCert-returning cache accessor); a
// boundary that should stay lazy must thread the Prop / Thm instead (see
// PromisedThm, AsThm). p.Core().(ThmCert) would NOT see through a realized
// promise — ThmPromise.Core() preserves promise identity — so we go through
// AsThmCert, which both concretes implement.
func asRealizedThm(p Prop) ThmCert {
	return p.AsThmCert()
}

// ClaimProved registers `n`'s proved Thm into both the per-section
// (`localThmCache`) and shared (`env.ThmCache`) caches under both raw
// and normalized AlphaKey. Idempotent: a second claim of an already-
// cached thm is a no-op fast-path. Per-leaf assertion checks each
// thmLeaf-produced Thm is also already in one of the two caches —
// the bottom-up invariant that downstream sections relied on.
func (env *ProverEnv) ClaimProved(
	n *GoalStackNode,
	localThmCache *ThmCache) {
	if !n.Proved() {
		panic(fmt.Sprintf("ClaimProved: section is not fully proved — "+
			"%d unsolved leaf/leaves remain (the step chain closed early or "+
			"a closing step is missing):\n%s",
			len(n.UnsolvedLeaves()), n.String()))
	}
	// PromisedThm(), not ProvedThm(): register the section's certificate Prop —
	// a Thm when eager, or a ThmPromise (statement now, proof deferred) in the
	// define-then-run corpus — so the namespace stays a promise graph, unforced.
	provedThm := n.PromisedThm()
	normalized, held := heldThm(provedThm, localThmCache, &env.ThmCache)
	if held {
		return
	}
	for thmNode := range n.thmLeavesIter() {
		// The leaf's own prop, not the section's: a leaf is consumed as
		// proved only against a prior Cite/UseLemma/UseThm of that prop.
		knownThm := thmNode.PromisedThm()
		if _, held := heldThm(knownThm, localThmCache, &env.ThmCache); !held {
			panic(fmt.Sprintf("ClaimProved: a KnownThm leaf's claimed prop is not in "+
				"either thm cache — it was consumed as proved without a matching "+
				"prior Cite/UseLemma/UseThm on the same prop. Leaf prop:\n%s",
				PrintProp(knownThm)))
		}
	}
	if normalized.Conclusion().Equals(T) {
		panic(fmt.Sprintf("ClaimProved: section's conclusion normalizes to ⊤ — a "+
			"section can't be trivially true (its promised cert carries no proof "+
			"content). Common causes: (a) the SectionText's conclusion is literally "+
			"⊤ (a stub / placeholder — use a real proposition or omit the section), "+
			"(b) the conclusion α-equals one of the section's own hypotheses (drop "+
			"the redundant hyp or restate the goal), (c) an intended nontrivial "+
			"claim was accidentally simplified to ⊤ by an earlier tactic. Section prop:\n%s",
			PrintProp(provedThm)))
	}
	localThmCache.SaveThm(provedThm, normalized)
	env.ThmCache.SaveThm(provedThm, normalized)
}

// ThmCache is the prover's proved-prop namespace. Its values are Prop, not
// Thm: a stored entry is a realized Thm in the eager case, or a ThmPromise
// (statement now, certificate deferred) once the corpus is define-then-run. The
// Load* accessors still collapse to Thm at their boundary via asRealizedThm
// (panic on a promise — the marker for the next caller to convert to Prop);
// SaveThm/HasThm already deal in Prop so promises can be registered.
type ThmCache struct {
	// thms and normalizedThms index the same (thm, normalizedThm) pair,
	// by thm's raw key and by its normal form's key: a raw-key hit
	// answers both "is thm held" and "what is thm's normal form".
	thms           utils.Map[core.PropKey, struct{ thm, normalizedThm Prop }]
	normalizedThms utils.Map[core.PropKey, struct{ thm, normalizedThm Prop }]

	// skeletonBuckets indexes proved thms by SkeletonKey(normalized) for
	// TypeMatch lookup — the third FindProvedThm tier after AlphaKey and
	// NormalizedKey. Each bucket holds the same (thm, normalizedThm)
	// pair as normalizedThms (the original thm is needed to surface as
	// `equivalentThm`; the normalized form is what we run
	// NormalizedPropTypeMatch against).
	//
	// Bucket value is a slice (not a sync.Map) because cap-bounded
	// append is the only mutation we do and bucket scans iterate
	// sequentially. The mutex serializes Save vs Save and Save vs Load
	// reads; Load releases the lock before scanning the bucket so the
	// per-candidate NormalizedPropTypeMatch work doesn't block parallel
	// Save callers. The lazy init pattern handles the composite-literal
	// construction sites (e.g. `&ThmCache{}` and `var c ThmCache`).
	skeletonMu      sync.Mutex
	skeletonBuckets map[core.PropKey][]struct{ thm, normalizedThm Prop }
}

// Reads a proved prop in the db (if any) — a Thm or a ThmPromise.
func (thmCache *ThmCache) LoadThm(goal Prop) Prop {
	if held, ok := thmCache.thms.Load(goal.AlphaKey()); ok {
		return held.thm
	}
	return nil
}

// LoadByNormalizedKeyProp is the promise-preserving form of LoadByNormalizedKey:
// returns the stored cert as the Thm interface (a realized ThmCert or an
// unforced ThmPromise) without forcing, or nil on a miss. Used by
// TheoremRegistry.PromiseByKey / RequireThm so an already-registered
// theorem's promise is returned (and threaded) rather than forced.
func (thmCache *ThmCache) LoadByNormalizedKeyProp(normalizedKey core.PropKey) Thm {
	if pair, ok := thmCache.normalizedThms.Load(normalizedKey); ok {
		return core.AsThm(pair.thm)
	}
	return nil
}

// Reads a proved thm which is equivalent to a proved thm in the cache (if
// any). Also returns the equivalent thm.
//
// Trivial-true guard: refuse normalize-keyed matches when the goal collapses
// to ⊢⊤. Every cached tautology shares that normalized key, so a hit there
// would be successful but semantically empty. The raw-key path (LoadThm) is
// intentionally not guarded — retrieval-style callers need to find a stored
// Thm by its prop, even
// when that prop is a tautology like `⊢ ∀x. x = x`.
func (thmCache *ThmCache) LoadNormalizedThm(goal Prop) (Prop, Prop) {
	normalized, reconstruct := Normalize(goal)
	if normalized.Conclusion().Equals(T) {
		return nil, nil
	}
	if normalized, ok := thmCache.normalizedThms.Load(normalized.AlphaKey()); ok {
		// reconstruct threads a Prop: a promise-backed normalizedThm yields a
		// derived promise reconstructed back to goal shape, unforced.
		reconstructed := reconstruct(normalized.normalizedThm)
		Assert(IsStronger(reconstructed, goal))
		return reconstructed, normalized.thm
	}
	return nil, nil
}

// heldThm reports whether any of caches holds thm — under its raw key,
// or under the key of its normal form — and returns thm's normal form,
// so a caller that goes on to save thm does not normalize it a second
// time. A raw-key hit normalizes nothing and returns nil for the form.
func heldThm(thm Prop, caches ...*ThmCache) (normalized Prop, held bool) {
	key := thm.AlphaKey()
	for _, cache := range caches {
		if _, ok := cache.thms.Load(key); ok {
			return nil, true
		}
	}
	normalized, _ = Normalize(thm)
	normalizedKey := normalized.AlphaKey()
	for _, cache := range caches {
		if _, ok := cache.normalizedThms.Load(normalizedKey); ok {
			return normalized, true
		}
	}
	return normalized, false
}

// HasThm reports whether the cache holds thm, by its raw key or by the
// key of its normal form.
func (thmCache *ThmCache) HasThm(thm Prop) bool {
	_, held := heldThm(thm, thmCache)
	return held
}

// normalForm is a theorem stating what Normalize(thm) states, names
// included: the normal form saved in any of caches with a thm of the
// same statement, else Normalize's. It promises the statement, not the
// object — a saved form's proof rests on the thm it was saved with — and
// relies only on Normalize's statement being a function of its input's.
// An α-variant does not share it: Normalize keeps its input's binder
// names, and the install forms read their prefix back by name
// (statedPrefixOrder, the ground cite's witness map). A miss saves
// nothing — saving registers thm as a known theorem, which is the
// caller's call.
func normalForm(thm Prop, caches ...*ThmCache) Prop {
	key := thm.AlphaKey()
	for _, cache := range caches {
		if held, ok := cache.thms.Load(key); ok && sameStatement(held.thm, thm) {
			return held.normalizedThm
		}
	}
	normalized, _ := Normalize(thm)
	return normalized
}

// sameStatement reports whether a and b are the same sequent, names
// included.
func sameStatement(a, b Prop) bool {
	if a.NumHyps() != b.NumHyps() || !a.Conclusion().Equals(b.Conclusion()) {
		return false
	}
	return slices.EqualFunc(slices.Collect(a.HypIter()), slices.Collect(b.HypIter()),
		func(x, y Term) bool { return x.Equals(y) })
}

// SaveThm registers a proved prop (a Thm or a ThmPromise) under its raw,
// normalized, and skeleton keys. thm and normalized are Props so a promise can
// be cached without forcing. normalized must be thm's normal form: a later
// normal-form query for a thm of the same statement is answered with it.
func (thmCache *ThmCache) SaveThm(thm, normalized Prop) {
	pair := struct{ thm, normalizedThm Prop }{thm, normalized}
	thmCache.thms.Store(thm.AlphaKey(), pair)
	thmCache.normalizedThms.Store(normalized.AlphaKey(), pair)

	// Index the (already-normalized) thm under its SkeletonKey for the
	// TypeMatch fallthrough tier. Lazy-init the map under the mutex —
	// ThmCache is constructed via composite literal in several call
	// sites (script.go:78, proof.go:125, proof.go:189, etc.).
	skelKey := skeleton.SkeletonKey(normalized)
	thmCache.skeletonMu.Lock()
	if thmCache.skeletonBuckets == nil {
		thmCache.skeletonBuckets =
			make(map[core.PropKey][]struct{ thm, normalizedThm Prop })
	}
	thmCache.skeletonBuckets[skelKey] = append(thmCache.skeletonBuckets[skelKey], pair)
	thmCache.skeletonMu.Unlock()
}

// LoadMatchThm is the third FindProvedThm tier — a SkeletonKey bucket
// scan that catches type-instantiation hits the AlphaKey and
// NormalizedKey tiers miss. Used when the goal is a (possibly
// concrete) type-instantiation of a polymorphic stored thm, including
// the simpler variant case where the bijection is var↔var only.
//
// Mechanism: normalize the goal, compute SkeletonKey of the normalized
// form, fetch the bucket. For each candidate, run
// NormalizedPropTypeMatch against the goal's normalized form; on hit,
// apply the substitution via PropTypeInst and run the goal's
// reconstruct closure to produce a goal-shape Thm.
//
// Trivial-true guard: same as LoadNormalizedThm — refuse matches when
// the goal normalizes to ⊢⊤, since a cached tautology's ⊢⊤ form would
// match anything via the empty substitution branch.
func (thmCache *ThmCache) LoadMatchThm(goal Prop) (Prop, Prop) {
	stronger, src, _ := thmCache.LoadMatchThmWithSource(goal)
	return stronger, src
}

// LoadMatchThmWithSource is LoadMatchThm surfacing the matched entry's
// NORMALIZED polymorphic form as a third return. The commit layer
// (commitFoundThmStep) records tier-3 hits as _TypeInstStep with that
// normalized source — the stable identity replay/emit can resolve —
// instead of a _KnownThmStep carrying the per-goal type instance
// (which has no registry/section identity and panics emit; the fst/snd
// shape in cardinality.HasSizeProduct was the live instance).
func (thmCache *ThmCache) LoadMatchThmWithSource(goal Prop) (Prop, Prop, Prop) {
	normalized, reconstruct := Normalize(goal)
	if normalized.Conclusion().Equals(T) {
		return nil, nil, nil
	}
	skelKey := skeleton.SkeletonKey(normalized)

	// Lock just long enough to read the slice header. The backing array
	// is append-only, so iterating with the captured len after release
	// is race-free (new appends either reuse the existing backing array
	// past our captured len, or allocate a fresh one — either way our
	// view is consistent).
	thmCache.skeletonMu.Lock()
	bucket := thmCache.skeletonBuckets[skelKey]
	thmCache.skeletonMu.Unlock()

	for _, entry := range bucket {
		substs, ok := NormalizedPropTypeMatch(entry.normalizedThm, normalized)
		if !ok {
			continue
		}
		// entry.normalizedThm has the stored thm's type-var names; apply
		// σ to align with goal's normalized form, then reconstruct
		// un-normalizes back to goal-shape.
		instantiated := core.PropTypeInst(entry.normalizedThm, substs...)
		reconstructed := reconstruct(instantiated)
		Assert(IsStronger(reconstructed, goal))
		return reconstructed, entry.thm, entry.normalizedThm
	}
	return nil, nil, nil
}

func (thmCache *ThmCache) FindProvedThm(goal Prop) (Prop, Prop) {
	Assert(!goal.Proved())
	goals := StrongerGoals(goal)

	// Tier 1 — exact AlphaKey lookup.
	for _, g := range goals {
		if strongerGoal := thmCache.LoadThm(g); strongerGoal != nil {
			return strongerGoal, nil
		}
	}

	// Tier 2 — normalized-form AlphaKey lookup (catches α-equivalent
	// rewordings after Normalize).
	for _, g := range goals {
		if strongerGoal, equivalentThm :=
			thmCache.LoadNormalizedThm(g); strongerGoal != nil {
			return strongerGoal, equivalentThm
		}
	}

	// Tier 3 — TypeMatch via SkeletonKey bucket scan. Catches the case
	// where the goal is a type-instantiation of a polymorphic stored
	// thm; subsumes the type-variant subcase (same theorem restated
	// with renamed type vars).
	for _, g := range goals {
		if strongerGoal, equivalentThm :=
			thmCache.LoadMatchThm(g); strongerGoal != nil {
			return strongerGoal, equivalentThm
		}
	}

	return nil, nil
}
