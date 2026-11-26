package clause

import (
	"sync"
	"sync/atomic"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// Diagnostic counters for the deserializeClauseCache. Read snapshot via
// ClauseCacheStats; reset via ClauseCacheStatsReset. Hot-path increments are
// plain atomic adds (single uncontended atomic op).
var (
	clauseCacheHits   atomic.Uint64
	clauseCacheMisses atomic.Uint64
	clauseCacheStores atomic.Uint64
)

// ClauseCacheStats returns (hits, misses, stores) since program start (or last
// reset). Cache size is the number of stores minus any evictions (we never
// evict, so == number of unique keys stored).
func ClauseCacheStats() (hits, misses, stores uint64) {
	return clauseCacheHits.Load(), clauseCacheMisses.Load(), clauseCacheStores.Load()
}

// ClauseCacheStatsReset zeros the counters (for per-batch deltas in tests).
func ClauseCacheStatsReset() {
	clauseCacheHits.Store(0)
	clauseCacheMisses.Store(0)
	clauseCacheStores.Store(0)
}

// Clauses serialize into the shared ext.PoolProto owned by the enclosing
// CNFRefuteProofProto: a clause's lits/univ (and a recipe's terms) are node
// indices into that pool, so a term recurring across a certificate's clauses is
// stored once. Serialization threads an *ext.PoolBuilder; deserialization an
// *ext.PoolReader (which already built every node once, bottom-up).

func SerializeClause(d *Clause, b *ext.PoolBuilder) *DisjunctClauseProto {
	lits := make([]uint32, len(d.literals))
	for i, l := range d.literals {
		lits[i] = b.TermRef(l)
	}
	univ := make([]uint32, 0, d.univBoundVars.Size())
	for v := range d.univBoundVars.Iter() {
		univ = append(univ, b.TermRef(v))
	}
	return &DisjunctClauseProto{Lits: lits, Univ: univ}
}

// deserializeClauseCache memoizes MakeClause by an EXACT, pool-independent
// content hash of the clause, process-globally. DeserializeClause -> MakeClause
// re-runs full clause normalization (component split, division/simplification
// theorems) — ~1/3 of replay CPU — and the same clause recurs heavily, both
// within a certificate's steps and ACROSS the whole corpus (so the cache must
// outlive any single pool/reader).
//
// The key (PoolReader.ClauseContentKey) is a uint64 computed straight from the
// proto pool WITHOUT building any term and WITHOUT allocating (memoized node
// content hashes, no Digest) — so a clause already in the cache is resolved
// without constructing its core terms, and the per-lookup cost matches the
// legacy uint64 proto-hash. It is exact, distinguishing bound-variable names
// (recipe substs reference them by name). Sharing the *Clause is safe: a Clause
// is immutable after construction (the only mutator, rename, always clones
// first — see AvoidVarsCollision). The clause is fully determined by its terms,
// independent of loadConstMeta, so a process-global cache is consistent with
// the repo's process-global const metadata.
var (
	deserializeClauseCacheMu sync.RWMutex
	deserializeClauseCache   = make(map[uint64]*Clause, 4096)
)

func DeserializeClause(p *DisjunctClauseProto, r *ext.PoolReader) *Clause {
	key := r.ClauseContentKey(p.Lits, p.Univ)
	deserializeClauseCacheMu.RLock()
	c, ok := deserializeClauseCache[key]
	deserializeClauseCacheMu.RUnlock()
	if ok {
		clauseCacheHits.Add(1)
		return c
	}
	clauseCacheMisses.Add(1)
	// Miss: build the terms (lazily, via the reader) and normalize.
	lits := make([]core.Term, len(p.Lits))
	for i, idx := range p.Lits {
		lits[i] = r.Term(idx)
	}
	t := Or(lits...)
	for i := len(p.Univ) - 1; i >= 0; i-- {
		v, ok := r.Term(p.Univ[i]).AsVar()
		Assert(ok)
		t = ForAll(v)(t)
	}
	c = MakeClause(t)
	deserializeClauseCacheMu.Lock()
	deserializeClauseCache[key] = c
	deserializeClauseCacheMu.Unlock()
	clauseCacheStores.Add(1)
	return c
}

// SerializeClauseThm serializes a ClauseThm into a ClauseThmProto.
// Since we cannot simply claim a proposition is true, we need to reconstruct
// the theorem by essentially re-proving it, so this serialization is only
// reconstructable if the theorem can be proved by clause factoring or resolution.
func SerializeClauseThm(t *ClauseThm, b *ext.PoolBuilder) *ClauseThmProto {
	Assert(len(t.hypClauses) == 1 || len(t.hypClauses) == 2)
	recipe := serializeRecipe(t.recipe, b)
	// Every serialized clause thm must carry its inference recipe — the recipe is
	// how reconstruction reproduces it. A recipe-less thm here is a producer
	// bug, not data to tolerate.
	Assert(recipe != nil)
	if t.IsRefuted() {
		return &ClauseThmProto{Recipe: recipe}
	}
	return &ClauseThmProto{
		Concl:  SerializeClause(t.ConclClause(), b),
		Recipe: recipe}
}

// deserializeConcl reads the conclusion clause of a clause thm proto (⊥ when
// absent).
func deserializeConcl(p *ClauseThmProto, r *ext.PoolReader) *Clause {
	if p.Concl == nil {
		return FClause
	}
	return DeserializeClause(p.Concl, r)
}

// DeserializeClauseThm reconstructs a ClauseThm from its recorded inference
// recipe, replaying the exact unifier deterministically and search-free.
//
// Every stored certificate is recipe-bearing. A proto without a recipe is
// corrupt or stale (pre-recipe) data: rather than papering over it, this PANICS
// so the inconsistency surfaces immediately.
func DeserializeClauseThm(p *ClauseThmProto, r *ext.PoolReader) *ClauseThm {
	rec := deserializeRecipe(p.Recipe, r)
	if rec == nil {
		panic("clause.DeserializeClauseThm: clause thm proto has no inference recipe — " +
			"corrupt or pre-recipe data; recipe-less protos are not supported")
	}
	return reconstructFromRecipe(deserializeConcl(p, r), rec)
}

func serializeTermSubst(s TermSubst, b *ext.PoolBuilder) *TermSubstProto {
	return &TermSubstProto{
		Var:  b.TermRef(s.VarTerm),
		Term: b.TermRef(s.Term),
	}
}

func deserializeTermSubst(p *TermSubstProto, r *ext.PoolReader) TermSubst {
	v, ok := r.Term(p.Var).AsVar()
	Assert(ok)
	return ext.MakeTermSubst(v, r.Term(p.Term))
}

func serializeRecipe(rec *deduceRecipe, b *ext.PoolBuilder) *DeduceRecipeProto {
	if rec == nil {
		return nil
	}
	var rule DeduceRecipeProto_Rule
	switch rec.rule {
	case _RuleFactor:
		rule = DeduceRecipeProto_FACTOR
	case _RuleResolve:
		rule = DeduceRecipeProto_RESOLVE
	case _RuleDiffResolve:
		rule = DeduceRecipeProto_DIFF_RESOLVE
	case _RuleContradicts:
		rule = DeduceRecipeProto_CONTRADICTS
	case _RuleSelfContradict:
		rule = DeduceRecipeProto_SELF_CONTRADICT
	case _RuleSimplifies:
		rule = DeduceRecipeProto_SIMPLIFIES
	case _RuleBoolSpecialize:
		rule = DeduceRecipeProto_BOOL_SPECIALIZE
	case _RuleSimplifyBridge:
		rule = DeduceRecipeProto_SIMPLIFY_BRIDGE
	case _RuleFunext:
		rule = DeduceRecipeProto_FUNEXT
	case _RuleEqApply:
		rule = DeduceRecipeProto_EQ_APPLY
	default:
		panic("unknown deduce rule")
	}
	out := &DeduceRecipeProto{
		Rule:        rule,
		Inputs:      utils.MapSlice(rec.inputs, func(c *Clause) *DisjunctClauseProto { return SerializeClause(c, b) }),
		LitIndex:    int32(rec.litIndex),
		RewriteType: int32(rec.rewriteType),
		Substs:      utils.MapSlice(rec.substs, func(s TermSubst) *TermSubstProto { return serializeTermSubst(s, b) }),
		SwitchSide:  rec.switchSide,
	}
	if rec.c1Subterm != nil {
		idx := b.TermRef(rec.c1Subterm)
		out.C1Subterm = &idx
	}
	return out
}

func deserializeRecipe(p *DeduceRecipeProto, r *ext.PoolReader) *deduceRecipe {
	if p == nil {
		return nil
	}
	var rule _DeduceRule
	switch p.Rule {
	case DeduceRecipeProto_FACTOR:
		rule = _RuleFactor
	case DeduceRecipeProto_RESOLVE:
		rule = _RuleResolve
	case DeduceRecipeProto_DIFF_RESOLVE:
		rule = _RuleDiffResolve
	case DeduceRecipeProto_CONTRADICTS:
		rule = _RuleContradicts
	case DeduceRecipeProto_SELF_CONTRADICT:
		rule = _RuleSelfContradict
	case DeduceRecipeProto_SIMPLIFIES:
		rule = _RuleSimplifies
	case DeduceRecipeProto_BOOL_SPECIALIZE:
		rule = _RuleBoolSpecialize
	case DeduceRecipeProto_SIMPLIFY_BRIDGE:
		rule = _RuleSimplifyBridge
	case DeduceRecipeProto_FUNEXT:
		rule = _RuleFunext
	case DeduceRecipeProto_EQ_APPLY:
		rule = _RuleEqApply
	default:
		panic("unknown deduce rule proto")
	}
	rec := &deduceRecipe{
		rule:        rule,
		inputs:      utils.MapSlice(p.Inputs, func(c *DisjunctClauseProto) *Clause { return DeserializeClause(c, r) }),
		litIndex:    int(p.LitIndex),
		rewriteType: _EqRewriteType(p.RewriteType),
		substs:      utils.MapSlice(p.Substs, func(s *TermSubstProto) TermSubst { return deserializeTermSubst(s, r) }),
		switchSide:  p.SwitchSide,
	}
	if p.C1Subterm != nil {
		rec.c1Subterm = r.Term(*p.C1Subterm)
	}
	return rec
}
