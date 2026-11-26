// cnf_store.go — the CNF store: the two tables a recorded refute-closing
// step reads back at replay, held as ONE value.
//
// A By that closes on its conditioned leaf is recorded as TWO artifacts:
// the certificate, under the CONDITIONED leaf's CNF key, and the
// conditioning plan, under the BARE leaf's plan key (planKey: the goal's
// AlphaKey with its free variables under canonical names, its terms
// stored under the same names, so a member whose binders were renamed
// reads the same plan). Strict replay
// never searches — it reads the plan, reproduces the conditioned leaf
// mechanically, then reads the certificate — so a certificate whose plan
// was not kept is an unreplayable recording, and a plan without its
// certificate is a leaf nothing closes. The two tables therefore travel
// together or not at all: an env holds a CNFStore or holds none, and no
// env can keep certificates while dropping plans. (Three session envs
// did exactly that, as four independently-optional hooks allowed, and
// the recording looked whole until emit's strict re-run MISSed on the
// bare key.)
//
// Beside the certificates stands the exact-key table: a certificate's
// key is the key of a normal form, seconds to compute on a wide leaf,
// and the table says under which key the certificate of a refute prop
// is stored, by the refute prop's own AlphaKey. It is an index of the
// certificate table and travels with it.

package proof

import (
	"context"
	"maps"
	"slices"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/refuter"
)

// planKey is the plan table's key for a leaf: its AlphaKey under
// canonical free names (prop.CanonicalFreeKey) in β-normal form — one
// key for the leaf of a member and for the same leaf with its free
// variables renamed, and one for a leaf that spells a redex and the
// same leaf reduced: an instance taken at a λ-witness, a motive applied
// by an induction principle, state what their reduction states.
func planKey(goal Prop) core.PropKey { return prop.CanonicalFreeKey(betaNormalProp(goal)) }

// betaNormalProp is goal with its conclusion and hypotheses β-collapsed;
// goal itself where none spells a redex.
func betaNormalProp(goal Prop) Prop {
	ctx := context.Background()
	changed := false
	hyps := make([]core.Term, 0, goal.NumHyps())
	for h := range goal.HypIter() {
		c := ext.BetaCollapse(ctx, h)
		changed = changed || !c.Equals(h)
		hyps = append(hyps, c)
	}
	concl := ext.BetaCollapse(ctx, goal.Conclusion())
	if !changed && concl.Equals(goal.Conclusion()) {
		return goal
	}
	return core.MakeProp(concl, hyps...)
}

// CNFStore is the certificate table (cnf_proofs; key = the refute's
// normalized CNF prop AlphaKey, written by tryCNFRefute on a live
// success) and the plan table (cnf_plans; key = the bare By working
// leaf's planKey, written by the conditioning stage on a
// successful conditioned close). Backed by files for live sessions
// (engine.SessionCNFStore, <data-dir>/cnf_cache/), by the
// embedded family blob for replay (InstallCNFStore), by
// MemoryCNFStore in tests and the recorder harness.
//
// Write policies are the store's own: the session store's certificate table
// keeps the smaller of two proofs for a key, its plan table keeps the
// latest (a plan must stay in step with the certificate its own run
// wrote); the in-memory stores overwrite.
//
// ScanProofs enumerates the stored certificates (key + blob), stopping
// early when yield returns false. It backs tryCNFRefute's α-variant
// fallback: the primary cnf_proofs key is name-sensitive through the
// CNF pipeline (Skolem naming, name-ordered sorting), so a goal whose
// bound-variable names differ from the recording session's — e.g.
// re-parsed `{x | φ}` set-builder text, which synthesizes
// position-derived GEN%PVAR% binders — computes a different key for
// the SAME proposition; the fallback finds the row by the goal's own
// AlphaKey instead. Enumeration must be deterministic (the fallback
// takes the first reconstructing match). The in-memory stores
// enumerate in sorted key order; the session store enumerates NOTHING —
// a full-table decode scan is not an inline lookup path, and the
// DB-backed callers (live prover, emit) run name-faithful to their
// recorded goals.
//
// ReadExactKey and WriteExactKey are the exact-key table (cnf_exact_keys):
// exact is the AlphaKey of a refute prop as the CNF conversion builds
// it, and the row is the key its certificate is stored under in the
// certificate table. tryCNFRefute writes the row with the certificate
// and asks it before it computes a certificate's key; ReadExactKey
// answers "" where the table holds no row, and a row whose certificate
// is gone is a miss to the reader, which then computes the key.
type CNFStore interface {
	ReadProof(key core.PropKey) *refuter.CNFRefuteProofProto
	WriteProof(key core.PropKey, proof *refuter.CNFRefuteProofProto)
	ReadPlan(key core.PropKey) *ByConditionPlanProto
	WritePlan(key core.PropKey, plan *ByConditionPlanProto)
	ReadExactKey(exact core.PropKey) core.PropKey
	WriteExactKey(exact, key core.PropKey)
	ScanProofs(yield func(key core.PropKey, proof *refuter.CNFRefuteProofProto) bool)
}

// MemoryCNFStore is the in-memory CNFStore: the test envs' store, the
// captured set inside CapturingCNFStore, the front of the embedded
// replay store. Overwrite on write; concurrency-safe (the refuter's
// racer goroutines write through it).
type MemoryCNFStore struct {
	mu     sync.Mutex
	proofs map[core.PropKey]*refuter.CNFRefuteProofProto
	plans  map[core.PropKey]*ByConditionPlanProto
	exact  map[core.PropKey]core.PropKey
}

func NewMemoryCNFStore() *MemoryCNFStore {
	return &MemoryCNFStore{
		proofs: map[core.PropKey]*refuter.CNFRefuteProofProto{},
		plans:  map[core.PropKey]*ByConditionPlanProto{},
		exact:  map[core.PropKey]core.PropKey{},
	}
}

// NewMemoryCNFStoreFrom returns a store holding a decoded blob's
// certificates, plans and exact keys (an empty store for a nil blob).
func NewMemoryCNFStoreFrom(cache *CNFCache) *MemoryCNFStore {
	s := NewMemoryCNFStore()
	for k, p := range cache.GetEntries() {
		s.proofs[core.PropKey(k)] = p
	}
	for k, p := range cache.GetPlans() {
		s.plans[core.PropKey(k)] = p
	}
	for exact, key := range cache.GetExactKeys() {
		s.exact[core.PropKey(exact)] = core.PropKey(key)
	}
	return s
}

func (s *MemoryCNFStore) ReadProof(key core.PropKey) *refuter.CNFRefuteProofProto {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.proofs[key]
}

func (s *MemoryCNFStore) WriteProof(key core.PropKey, proof *refuter.CNFRefuteProofProto) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.proofs[key] = proof
}

func (s *MemoryCNFStore) ReadPlan(key core.PropKey) *ByConditionPlanProto {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.plans[key]
}

func (s *MemoryCNFStore) WritePlan(key core.PropKey, plan *ByConditionPlanProto) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.plans[key] = plan
}

func (s *MemoryCNFStore) ReadExactKey(exact core.PropKey) core.PropKey {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.exact[exact]
}

func (s *MemoryCNFStore) WriteExactKey(exact, key core.PropKey) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.exact[exact] = key
}

// ScanProofs enumerates in sorted key order over a snapshot, so the
// yield may itself read or write the store.
func (s *MemoryCNFStore) ScanProofs(yield func(core.PropKey, *refuter.CNFRefuteProofProto) bool) {
	proofs := s.Proofs()
	for _, k := range slices.Sorted(maps.Keys(proofs)) {
		if !yield(k, proofs[k]) {
			return
		}
	}
}

// Proofs and Plans return snapshots of the two tables.
func (s *MemoryCNFStore) Proofs() map[core.PropKey]*refuter.CNFRefuteProofProto {
	s.mu.Lock()
	defer s.mu.Unlock()
	return maps.Clone(s.proofs)
}

func (s *MemoryCNFStore) Plans() map[core.PropKey]*ByConditionPlanProto {
	s.mu.Lock()
	defer s.mu.Unlock()
	return maps.Clone(s.plans)
}

// ExactKeys returns a snapshot of the exact-key table.
func (s *MemoryCNFStore) ExactKeys() map[core.PropKey]core.PropKey {
	s.mu.Lock()
	defer s.mu.Unlock()
	return maps.Clone(s.exact)
}

// Len is the number of rows across the certificate and plan tables.
func (s *MemoryCNFStore) Len() int {
	s.mu.Lock()
	defer s.mu.Unlock()
	return len(s.proofs) + len(s.plans)
}

// Cache is the tables as the embeddable CNFCache proto (Plans and
// ExactKeys left nil when their table is empty — the marshalled bytes
// are the same, and a pre-conditioning blob stays byte-identical).
func (s *MemoryCNFStore) Cache() *CNFCache {
	s.mu.Lock()
	defer s.mu.Unlock()
	cache := &CNFCache{
		Entries: make(map[string]*refuter.CNFRefuteProofProto, len(s.proofs)),
	}
	for k, p := range s.proofs {
		cache.Entries[string(k)] = p
	}
	if len(s.plans) > 0 {
		cache.Plans = make(map[string]*ByConditionPlanProto, len(s.plans))
		for k, p := range s.plans {
			cache.Plans[string(k)] = p
		}
	}
	if len(s.exact) > 0 {
		cache.ExactKeys = make(map[string]string, len(s.exact))
		for exact, key := range s.exact {
			cache.ExactKeys[string(exact)] = string(key)
		}
	}
	return cache
}

// IsEmpty reports whether the cache carries no row in either table — the
// question emit asks before wiring an embed. A By whose conditioned leaf
// closes α-directly records a plan and NO certificate, so a blob with an
// empty certificate table can still be load-bearing.
func (c *CNFCache) IsEmpty() bool {
	return c == nil || (len(c.Entries) == 0 && len(c.Plans) == 0)
}

// CapturingCNFStore records every row a run touches — each read that
// HIT and each write — into its own MemoryCNFStore while delegating to
// the inner store (nil = no store beneath: reads miss, writes are kept
// only in the capture). It is the one capture the recorder and emit's
// CollectCNFCache share: what a proof's replay will read is exactly what
// its recording read or wrote.
type CapturingCNFStore struct {
	inner    CNFStore
	captured *MemoryCNFStore
	mu       sync.Mutex
	goals    map[core.PropKey]Prop
}

func NewCapturingCNFStore(inner CNFStore) *CapturingCNFStore {
	return &CapturingCNFStore{inner: inner, captured: NewMemoryCNFStore(), goals: map[core.PropKey]Prop{}}
}

// Captured is the store of touched rows.
func (c *CapturingCNFStore) Captured() *MemoryCNFStore { return c.captured }

// CNFGoalNoter is the optional face of a CNFStore that wants to know
// WHICH LEAF a row stands for. The store keys rows by AlphaKey alone —
// a key names a proposition, never the place in a proof that needed
// it — so the recorder's report had nothing but keys to print, and an
// author reading "+2 new" found the two leaves by diffing the blob's
// strings. The sites that serve or receive a row (tryCNFRefute for a
// certificate, the conditioning stage for a plan) hand the leaf goal
// to a store that implements this; the capturing store keeps it
// beside the key, and the recorder prints it. The persisted stores do
// not implement it: nothing about a stored row changes.
type CNFGoalNoter interface {
	NoteCNFGoal(key core.PropKey, goal Prop)
}

// noteCNFGoal names the leaf a key stands for, to a store that listens.
func noteCNFGoal(store CNFStore, key core.PropKey, goal Prop) {
	if n, ok := store.(CNFGoalNoter); ok {
		n.NoteCNFGoal(key, goal)
	}
}

// NoteCNFGoal keeps the leaf goal beside the key (the first noted goal
// wins: a key several leaves reach is named by the first).
func (c *CapturingCNFStore) NoteCNFGoal(key core.PropKey, goal Prop) {
	c.mu.Lock()
	defer c.mu.Unlock()
	if _, seen := c.goals[key]; !seen {
		c.goals[key] = goal
	}
}

// Goals is the leaf goal noted for each touched key — the certificate
// keys at the sequent that reached resolution, the plan keys at the
// bare working leaf.
func (c *CapturingCNFStore) Goals() map[core.PropKey]Prop {
	c.mu.Lock()
	defer c.mu.Unlock()
	return maps.Clone(c.goals)
}

// CNFRowHolder is the optional face of a CNFStore whose reads are
// recorded: it says whether a row is held without serving it, a look
// the record does not count. The economy audit asks through it what a
// recording of another spelling would be served (auditReplayProbeKey),
// and the asking must leave the member's record as the member's own
// reads made it. A store that records no read does not implement it and
// is asked by a read (cnfStoreHoldsProof).
type CNFRowHolder interface {
	HoldsProof(key core.PropKey) bool
	HoldsPlan(key core.PropKey) bool
}

// cnfStoreHoldsProof / cnfStoreHoldsPlan report whether store holds the
// row, by a look no capture records.
func cnfStoreHoldsProof(store CNFStore, key core.PropKey) bool {
	if h, ok := store.(CNFRowHolder); ok {
		return h.HoldsProof(key)
	}
	return store.ReadProof(key) != nil
}

func cnfStoreHoldsPlan(store CNFStore, key core.PropKey) bool {
	if h, ok := store.(CNFRowHolder); ok {
		return h.HoldsPlan(key)
	}
	return store.ReadPlan(key) != nil
}

// HoldsProof / HoldsPlan look beneath the capture and record nothing.
func (c *CapturingCNFStore) HoldsProof(key core.PropKey) bool {
	return c.inner != nil && cnfStoreHoldsProof(c.inner, key)
}

func (c *CapturingCNFStore) HoldsPlan(key core.PropKey) bool {
	return c.inner != nil && cnfStoreHoldsPlan(c.inner, key)
}

func (c *CapturingCNFStore) ReadProof(key core.PropKey) *refuter.CNFRefuteProofProto {
	if c.inner == nil {
		return nil
	}
	p := c.inner.ReadProof(key)
	if p != nil {
		c.captured.WriteProof(key, p)
	}
	return p
}

func (c *CapturingCNFStore) WriteProof(key core.PropKey, proof *refuter.CNFRefuteProofProto) {
	c.captured.WriteProof(key, proof)
	if c.inner != nil {
		c.inner.WriteProof(key, proof)
	}
}

func (c *CapturingCNFStore) ReadPlan(key core.PropKey) *ByConditionPlanProto {
	if c.inner == nil {
		return nil
	}
	p := c.inner.ReadPlan(key)
	if p != nil {
		c.captured.WritePlan(key, p)
	}
	return p
}

func (c *CapturingCNFStore) WritePlan(key core.PropKey, plan *ByConditionPlanProto) {
	c.captured.WritePlan(key, plan)
	if c.inner != nil {
		c.inner.WritePlan(key, plan)
	}
}

// ReadExactKey captures a row it serves, WriteExactKey the row it is
// given: the capture holds the exact key of every certificate the run
// reached by one or wrote, beside the certificate.
func (c *CapturingCNFStore) ReadExactKey(exact core.PropKey) core.PropKey {
	if c.inner == nil {
		return ""
	}
	key := c.inner.ReadExactKey(exact)
	if key != "" {
		c.captured.WriteExactKey(exact, key)
	}
	return key
}

func (c *CapturingCNFStore) WriteExactKey(exact, key core.PropKey) {
	c.captured.WriteExactKey(exact, key)
	if c.inner != nil {
		c.inner.WriteExactKey(exact, key)
	}
}

// ScanProofs enumerates the inner store; a hit the α-variant fallback
// takes is routed back through ReadProof under its stored key
// (tryCNFRefute), which is where it lands in the capture.
func (c *CapturingCNFStore) ScanProofs(yield func(core.PropKey, *refuter.CNFRefuteProofProto) bool) {
	if c.inner != nil {
		c.inner.ScanProofs(yield)
	}
}

// embeddedCNFStore is the replay store InstallCNFStore builds: a
// decoded blob in front (both tables, read-only, enumerable), the
// store the env already held behind it (engine.SessionCNFStore, a test
// store, or nothing). Reads try
// the blob first and fall through; writes go to the store behind, if
// any — the blob is a build-tree artifact, never written at replay.
type embeddedCNFStore struct {
	front *MemoryCNFStore
	back  CNFStore
}

func (s embeddedCNFStore) ReadProof(key core.PropKey) *refuter.CNFRefuteProofProto {
	if p := s.front.ReadProof(key); p != nil {
		return p
	}
	if s.back != nil {
		return s.back.ReadProof(key)
	}
	return nil
}

func (s embeddedCNFStore) WriteProof(key core.PropKey, proof *refuter.CNFRefuteProofProto) {
	if s.back != nil {
		s.back.WriteProof(key, proof)
	}
}

func (s embeddedCNFStore) ReadPlan(key core.PropKey) *ByConditionPlanProto {
	if p := s.front.ReadPlan(key); p != nil {
		return p
	}
	if s.back != nil {
		return s.back.ReadPlan(key)
	}
	return nil
}

func (s embeddedCNFStore) WritePlan(key core.PropKey, plan *ByConditionPlanProto) {
	if s.back != nil {
		s.back.WritePlan(key, plan)
	}
}

func (s embeddedCNFStore) ReadExactKey(exact core.PropKey) core.PropKey {
	if key := s.front.ReadExactKey(exact); key != "" {
		return key
	}
	if s.back != nil {
		return s.back.ReadExactKey(exact)
	}
	return ""
}

func (s embeddedCNFStore) WriteExactKey(exact, key core.PropKey) {
	if s.back != nil {
		s.back.WriteExactKey(exact, key)
	}
}

// ScanProofs walks the blob's certificates in sorted key order, then the
// store behind — the blob is the fast path on top, for enumeration as
// for lookup.
func (s embeddedCNFStore) ScanProofs(yield func(core.PropKey, *refuter.CNFRefuteProofProto) bool) {
	stop := false
	s.front.ScanProofs(func(k core.PropKey, p *refuter.CNFRefuteProofProto) bool {
		if !yield(k, p) {
			stop = true
			return false
		}
		return true
	})
	if !stop && s.back != nil {
		s.back.ScanProofs(yield)
	}
}
