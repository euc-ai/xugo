package engine

import (
	"container/list"
	"regexp"
	"sync"
	"time"

	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// DerivationPool — engine-global closed-derivation pool for cross-session
// proof grafting.
// ---------------------------------------------------------------------------
//
// The pool is the ephemeral merge layer for parallel divide-and-conquer
// proving: each sub-agent proves its phase in its OWN session, and any
// sequent a session closes becomes citable from every other session of the
// same engine via the existing `cite-node` tactic. `serve` builds exactly
// one Engine per process (engine/cmd/xugo/main.go), so engine-global
// == serve-process-global.
//
// Deliberately NOT package-global: a Prop's AlphaKey identifies constants
// by name + type only (core/const_term.go AlphaKey), not by definition
// identity. Two envs in one test process may define same-named constants
// differently; a package-global pool could then graft a derivation of an
// α-identical-LOOKING but semantically different statement. Scoping the
// pool to the engine (whose sessions all share e.env) removes that class
// entirely.
//
// Key: the FULL AlphaKey of the closed node's sequent — an α-invariant
// content hash over the conclusion AND every hypothesis (core/thm.go
// a statement's AlphaKey). Session goal ids (`s<sec>_c<AlphaKey[:16]>`) carry
// a session-local section index, but that prefix is presentation-only; the
// hash part is pure sequent content, which is why two sessions producing
// the same sequent produce the same id suffix.
//
// Replay self-containment: the pool changes only WHERE cite-node finds its
// target at live time. What gets recorded is unchanged — ApplyCiteNode
// materializes a clone of the cited subtree into the assert's first child,
// so the recorded DetailedProofProto is a regular assert with a fully-proven
// first branch (prover/proof/tactic_apply.go ApplyCiteNode). A fresh replay
// process with an empty pool replays those inlined ministeps through the
// kernel like any other assert; the pool is never consulted at replay.
//
// Soundness: entries are published only for Proved() nodes (kernel-backed
// certificate already attached; Publish panics otherwise — soundness over
// availability). Consumption goes through the exact same engine-enforced
// gate as same-session cite-node: the cited sequent's hyp context must be
// an (α-equiv) subset of the citing focus's hyps. Dependency acyclicity is
// not the pool's concern: an inlined ministep's cite resolves at emit to a
// typed dep of the consuming member, and the corpus DAG is checked there.
//
// NO disk persistence by design: durability comes from the session lineage
// and the emitted member; the pool only merges live sessions. An evicted or
// missing entry just means the consumer re-proves — never an error.

// DefaultDerivationPoolCap is the default max entry count. Entries hold
// pointers into (immutable, already-allocated) session proof subtrees, so
// the pool's own footprint is small; the cap mainly bounds how much
// otherwise-dead session memory pooled entries keep alive after their
// sessions close.
const DefaultDerivationPoolCap = 10000

// poolEntry is one published closed derivation.
type poolEntry struct {
	// node is the closed (Proved()) goal-stack node. Immutable once
	// closed — a node's miniStep/children/provedThm are never mutated
	// after provedThm is set (see GoalStackNode.Clone's sharing
	// invariant) — so sharing the pointer across sessions is safe.
	node *proof.GoalStackNode

	key         string // full AlphaKey of node.Goal (primary key)
	short       string // shortKey(node.Goal) — the 16-char id suffix agents see
	sessionID   string // publishing session (stats/debugging only)
	publishedAt time.Time

	elem *list.Element // position in the LRU list
}

// DerivationPool is a bounded, LRU-evicting map from a closed sequent's
// canonical content key to the session subtree that proved it. All methods
// are safe for concurrent use and tolerate a nil receiver (no-op / empty
// results), so callers never need a nil guard.
//
// A single Mutex (not RWMutex) is used: both publishes (per session
// mutation) and reads (per cite-node call) are low-frequency relative to
// proof search, and reads touch LRU recency anyway.
type DerivationPool struct {
	mu  sync.Mutex
	cap int

	entries map[string]*poolEntry   // full AlphaKey → entry
	byShort map[string][]*poolEntry // 16-char key prefix → entries (collision-tolerant)
	lru     *list.List              // of *poolEntry; front = most recently used

	published uint64
	hits      uint64
	misses    uint64
	evictions uint64
}

// NewDerivationPool builds a pool holding at most capEntries closed
// derivations (LRU eviction beyond that). capEntries <= 0 selects
// DefaultDerivationPoolCap.
func NewDerivationPool(capEntries int) *DerivationPool {
	if capEntries <= 0 {
		capEntries = DefaultDerivationPoolCap
	}
	return &DerivationPool{
		cap:     capEntries,
		entries: make(map[string]*poolEntry),
		byShort: make(map[string][]*poolEntry),
		lru:     list.New(),
	}
}

// Publish registers a closed derivation under its sequent's canonical
// content key. Returns true when a new entry was added; false on a
// duplicate key (first publication wins — both prove the same sequent, so
// keeping either is correct; recency is refreshed) or a nil pool/node.
//
// Panics if node is not closed: publishing an unproved derivation would
// let a later cite-node graft an unverified subtree — an inconsistency,
// not a recoverable condition. (Unreachable from the session publish hook,
// which only walks Proved() nodes; the panic guards other callers.)
func (p *DerivationPool) Publish(node *proof.GoalStackNode, sessionID string) bool {
	if p == nil || node == nil {
		return false
	}
	if !node.Proved() {
		panic("DerivationPool.Publish: node is not closed — publishing an " +
			"unproved derivation would let cite-node graft an unverified subtree")
	}
	key := string(node.Goal.AlphaKey())
	p.mu.Lock()
	defer p.mu.Unlock()
	if e, ok := p.entries[key]; ok {
		p.lru.MoveToFront(e.elem)
		return false
	}
	e := &poolEntry{
		node:        node,
		key:         key,
		short:       shortKey(node.Goal),
		sessionID:   sessionID,
		publishedAt: time.Now(),
	}
	e.elem = p.lru.PushFront(e)
	p.entries[key] = e
	p.byShort[e.short] = append(p.byShort[e.short], e)
	p.published++
	for len(p.entries) > p.cap {
		p.evictOldestLocked()
	}
	return true
}

// evictOldestLocked drops the least-recently-used entry. Caller holds p.mu.
func (p *DerivationPool) evictOldestLocked() {
	back := p.lru.Back()
	if back == nil {
		return
	}
	e := back.Value.(*poolEntry)
	p.lru.Remove(back)
	delete(p.entries, e.key)
	peers := p.byShort[e.short]
	for i, x := range peers {
		if x == e {
			peers = append(peers[:i], peers[i+1:]...)
			break
		}
	}
	if len(peers) == 0 {
		delete(p.byShort, e.short)
	} else {
		p.byShort[e.short] = peers
	}
	p.evictions++
}

// nodeIDPrefixRe matches the session-local presentation prefix of a goal /
// closed-subtree id: `s<sectionIdx>_` plus the open ("g") / closed ("c")
// marker. Everything after it is the sequent's AlphaKey prefix — the
// canonical, session-independent part.
var nodeIDPrefixRe = regexp.MustCompile(`^s\d+_[cg]`)

// CandidatesForNodeID resolves the id an agent passes to cite-node
// (`s<N>_c<key16>` — or a bare full/16-char AlphaKey) against the pool and
// returns every closed node whose sequent key matches, in publish order.
// The section index in the id is ignored: it is meaningless outside the
// publishing session. Multiple candidates only occur on a 16-char key
// prefix collision; the caller disambiguates by applying the cite-node
// soundness gate to each (any candidate that passes proves an acceptable
// sequent — grafting it is sound).
//
// Touches LRU recency on hit. Nil-safe (returns nil).
func (p *DerivationPool) CandidatesForNodeID(nodeID string) []*proof.GoalStackNode {
	if p == nil || nodeID == "" {
		return nil
	}
	key := nodeIDPrefixRe.ReplaceAllString(nodeID, "")
	p.mu.Lock()
	defer p.mu.Unlock()
	var out []*proof.GoalStackNode
	if e, ok := p.entries[key]; ok {
		// Full-key form (programmatic callers).
		p.lru.MoveToFront(e.elem)
		out = append(out, e.node)
	} else {
		for _, e := range p.byShort[key] {
			p.lru.MoveToFront(e.elem)
			out = append(out, e.node)
		}
	}
	if len(out) == 0 {
		p.misses++
	} else {
		p.hits++
	}
	return out
}

// DerivationPoolStats is a point-in-time snapshot of pool counters.
type DerivationPoolStats struct {
	Entries   int    `json:"entries"`
	Cap       int    `json:"cap"`
	Published uint64 `json:"published"`
	Hits      uint64 `json:"hits"`
	Misses    uint64 `json:"misses"`
	Evictions uint64 `json:"evictions"`
}

// Stats returns current counters. Nil-safe (zero value).
func (p *DerivationPool) Stats() DerivationPoolStats {
	if p == nil {
		return DerivationPoolStats{}
	}
	p.mu.Lock()
	defer p.mu.Unlock()
	return DerivationPoolStats{
		Entries:   len(p.entries),
		Cap:       p.cap,
		Published: p.published,
		Hits:      p.hits,
		Misses:    p.misses,
		Evictions: p.evictions,
	}
}

// publishClosedSubtrees pushes every top-level closed sub-derivation of
// this session into the engine-global DerivationPool. Invoked from
// rebuildGoalIndex — the single post-mutation choke point ("Rebuilt after
// any mutation", see Session.goalIndex) — so any node that transitioned to
// CLOSED since the last mutation is published promptly. Publish dedupes by
// canonical sequent key, making the re-walk idempotent; cost is the same
// O(open frontier + top-level closed nodes) walk indexNode already pays.
func (s *Session) publishClosedSubtrees() {
	if s.derivPool == nil {
		return
	}
	s.walkClosedSubtrees(func(id string, secIdx, depth int, n *proof.GoalStackNode) {
		s.derivPool.Publish(n, s.ID)
	})
}
