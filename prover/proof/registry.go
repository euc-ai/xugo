package proof

import (
	"context"
	"fmt"
	"sync"

	"github.com/euc-ai/xugo/core"
)

// TheoremRegistry is the env's by-key namespace of buildable theorems: it maps
// a PropKey to a builder that produces the theorem's certificate on demand
// (serve.RegisterAll registers one per corpus entry, building the entry's
// proof). A cited theorem is an honest IOU whose certificate is produced by a
// real builder and gated by the kernel, never fabricated.
//
// PromiseByKey hands out an unforced, forceable Prop at the caller's statement;
// forcing it runs the builder once (sync.Once per key) and memoizes the
// realized Thm into the env's ThmCache. The registry deliberately knows about
// ThmCache (it writes realized thms back), but core.ThmPromise does not — the
// cache write lives here, never in core.
//
// Key space. Both the ThmCache short-circuit (LoadByNormalizedKey) and the
// memo write key on the ENGINE-NORMALIZED space the cache uses, so a key
// should be the theorem's engine-normalized key. A key in another spelling
// still works functionally — the builder map is keyed by whatever key was
// registered — but the ThmCache fast path then misses by construction and
// every force pays the once round-trip instead of a cache hit.
type TheoremRegistry struct {
	env *ProverEnv

	mu       sync.Mutex
	builders map[core.PropKey]*_BuilderEntry
}

// _BuilderEntry is a by-key builder with no pre-declared statement (see
// RegisterBuilder). sync.Once dedups concurrent forces so the builder runs
// exactly once. A builder that cannot produce its theorem panics; there is no
// error to record.
type _BuilderEntry struct {
	once  sync.Once
	build func(core.Forcer) core.ThmCert
	thm   core.ThmCert
}

// _ReqKeyChain is the set of theorem keys currently being forced on the active
// RequireThm path, carried by the Forcer's context. RequireThm panics on a
// by-key citation cycle (X requires Y requires X): without this guard a
// builder-entry's sync.Once would deadlock on re-entry. Builders use the
// supplied Forcer for nested forces, retaining both this chain and the
// kernel's promise dependencies.
type _ReqKeyChain struct {
	key  core.PropKey
	prev *_ReqKeyChain
}

func (c *_ReqKeyChain) contains(k core.PropKey) bool {
	for n := c; n != nil; n = n.prev {
		if n.key == k {
			return true
		}
	}
	return false
}

type _ReqKeyChainKey struct{}

func reqKeyChainFrom(ctx context.Context) *_ReqKeyChain {
	c, _ := ctx.Value(_ReqKeyChainKey{}).(*_ReqKeyChain)
	return c
}

func withReqKey(ctx context.Context, k core.PropKey) context.Context {
	return context.WithValue(ctx, _ReqKeyChainKey{}, &_ReqKeyChain{key: k, prev: reqKeyChainFrom(ctx)})
}

// Theorems returns the env's theorem registry, lazily creating it.
func (env *ProverEnv) Theorems() *TheoremRegistry {
	env.theoremsMu.Lock()
	defer env.theoremsMu.Unlock()
	if env.theorems == nil {
		env.theorems = &TheoremRegistry{env: env}
	}
	return env.theorems
}

// PromiseByKey returns an UNFORCED, forceable Prop for a registered theorem,
// declared at the caller-supplied `stmt` (the shape the caller needs it in —
// e.g. an engine-normalized goal). Returns the realized ThmCert if already in
// the ThmCache; else a core.Promise(stmt, …) over the registered builder, whose
// force runs the real proof and is α-gated against `stmt` (a shape mismatch
// fails loudly at force, never silently); else nil if key is unregistered.
// The engine's auto-match uses it to inject a real, forceable IOU for a
// proved-earlier leaf instead of a fabricated TestThm.
func (env *ProverEnv) PromiseByKey(key core.PropKey, stmt core.Prop) core.Prop {
	return env.Theorems().PromiseByKey(key, stmt)
}

// RegisterBuilder registers a by-key builder WITHOUT a pre-declared statement:
// the theorem is reachable through PromiseByKey (and RequireThm), which force
// the builder.
//
// Trust boundary. A builder-only entry has NO statement to gate against, so
// RequireThm returns whatever Thm the builder produced under `key`, unchecked.
// This is sound at the kernel level — the builder kernel-derives its result —
// but it does NOT verify that result matches `key`. A key↔builder mismatch is
// caught downstream: PromiseByKey's settle gate bridges the cert to the
// caller's statement with BridgeNormalize and panics when the two do not
// normalize-coincide.
func (env *ProverEnv) RegisterBuilder(
	key core.PropKey, builder func(core.Forcer) core.ThmCert) {
	env.Theorems().RegisterBuilder(key, builder)
}

func (r *TheoremRegistry) RegisterBuilder(
	key core.PropKey, builder func(core.Forcer) core.ThmCert) {
	r.mu.Lock()
	defer r.mu.Unlock()
	if r.builders == nil {
		r.builders = make(map[core.PropKey]*_BuilderEntry)
	}
	if _, ok := r.builders[key]; ok {
		return
	}
	r.builders[key] = &_BuilderEntry{build: builder}
}

func (r *TheoremRegistry) PromiseByKey(key core.PropKey, stmt core.Prop) core.Prop {
	// Promise-preserving, as the name says: return a cached entry as its (possibly
	// unforced) Prop rather than forcing/asserting it here. Forcing is the
	// caller's job, or the returned promise's builder via RequireThm.
	if thm := r.env.ThmCache.LoadByNormalizedKeyProp(key); thm != nil {
		// The cache stores the entry at ITS OWN recorded shape (for an
		// entry whose statement is NOT in engine-normalized form), while
		// this function's contract is the
		// caller-supplied `stmt` shape. Returning the raw cached thm on
		// divergence hands the caller a prop whose spelling it never asked
		// for — measured as the finalize-reconstruct EqMP assert in
		// serve.promiseForGeneralOn, reachable only when an EARLIER force
		// in the same env realized the row into the cache (a shared-env
		// multi-member run; per-member subprocess envs never see it). So:
		// α-equal → as-is; else the same lazy force-then-bridge the
		// cache-miss promise below performs.
		if thm.AlphaKey() == stmt.AlphaKey() {
			return thm
		}
		return core.Promise(stmt, func(f core.Forcer) core.ThmCert {
			cert := f.Force(core.AsThm(thm))
			if cert.AlphaKey() == stmt.AlphaKey() {
				return cert
			}
			bridged := BridgeNormalize(stmt, WrapProp(cert))
			if bridged == nil {
				panic(fmt.Sprintf("PromiseByKey(%s): cached entry settled at %s, "+
					"which does not normalize-coincide with the requested "+
					"statement — key↔cache mismatch", key, cert.AlphaKey()))
			}
			return f.Force(core.AsThm(bridged))
		})
	}
	r.mu.Lock()
	_, ok := r.builders[key]
	r.mu.Unlock()
	if !ok {
		return nil
	}
	return core.Promise(stmt, func(f core.Forcer) core.ThmCert {
		cert := r.RequireThm(f, key)
		// The registered entry settles at ITS OWN recorded shape — for an
		// entry stated in pre-normalized form (e.g. list_induction's
		// implication form) that is NOT the normalized statement the
		// caller promised. This promise's settle gate α-checks against
		// `stmt`, so bridge the cert into stmt's α-form when they differ.
		// BridgeNormalize is kernel-faithful and returns nil only when the
		// two forms do NOT normalize-coincide — a genuine key↔builder
		// mismatch, worth the loud stop (the settle gate would panic on
		// it in any case; the bridge adds shape adaptation and no
		// trust).
		if cert.AlphaKey() == stmt.AlphaKey() {
			return cert
		}
		bridged := BridgeNormalize(stmt, WrapProp(cert))
		if bridged == nil {
			panic(fmt.Sprintf("PromiseByKey(%s): registered entry settled at %s, "+
				"which does not normalize-coincide with the requested statement — "+
				"key↔builder mismatch", key, cert.AlphaKey()))
		}
		return f.Force(core.AsThm(bridged))
	})
}

// RequireThm forces a registered theorem to a real kernel certificate and
// memoizes it into the ThmCache. Panics if key is unregistered, on a by-key
// citation cycle, or when the build fails — there is no error path.
func (r *TheoremRegistry) RequireThm(f core.Forcer, key core.PropKey) core.ThmCert {
	// A cached entry may be an unforced promise, so force it to a realized
	// cert here rather than asserting it is already proved.
	if thm := r.env.ThmCache.LoadByNormalizedKeyProp(key); thm != nil {
		return f.Force(core.AsThm(thm))
	}
	// Cycle guard: a builder-entry's sync.Once would deadlock if its build
	// (transitively) forced the same key, and a mutual cycle X→Y→X likewise.
	// Abort before re-entering the Once, then push
	// key so nested forces using this Forcer can see it.
	ctx := f.Context()
	if reqKeyChainFrom(ctx).contains(key) {
		panic(fmt.Sprintf("theorem citation cycle: %q", key))
	}
	f = f.WithContext(withReqKey(ctx, key))

	r.mu.Lock()
	b, ok := r.builders[key]
	r.mu.Unlock()
	if !ok {
		panic(fmt.Sprintf("theorem %q not registered", key))
	}
	b.once.Do(func() { b.thm = b.build(f) })
	thm := b.thm
	Assert(!thm.IsZero())

	// Memoize for tactic / normalized-match lookups. The builder usually
	// SaveThm's its own result via ClaimProved, so guard against a duplicate
	// skeleton-bucket append.
	if normalized, held := heldThm(thm, &r.env.ThmCache); !held {
		r.env.ThmCache.SaveThm(thm, normalized.AsThmCert())
	}
	return thm
}
