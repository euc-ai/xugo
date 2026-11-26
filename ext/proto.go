package ext

import (
	"fmt"
	"log"
	"sync/atomic"

	"github.com/cespare/xxhash/v2"
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
	"google.golang.org/protobuf/proto"
)

type LoadConstMeta = func(TermName) (core.ConstTermMeta, bool)

// makeConstFromMeta builds a core.ConstTerm from a const name, its abstract
// type (as serialized) and its instance type, resolving the meta via
// loadConstMeta. Used by the pooled ConstTermProto deserialization path.
func makeConstFromMeta(
	name string, absType, instType core.HolType, loadConstMeta LoadConstMeta) core.ConstTerm {
	Assert(loadConstMeta != nil)
	if meta, ok := loadConstMeta(TermName(name)); ok {
		if !meta.AbsType().Equals(absType) {
			// The DB's absType and the proto's absType may use different
			// type variable names but must be structurally identical.
			mapping, ok := absType.Matches(meta.AbsType(), utils.FullPredicate)
			if !ok || !utils.All(mapping, func(s core.TypeSubst) bool {
				_, isVar := s.HolType.(core.VarType)
				return isVar
			}) {
				log.Panicf(
					"const %q: absType not alpha-equivalent — proto=%s db=%s",
					name, absType.Key(), meta.AbsType().Key())
			}
		}
		return core.MakeConstTerm(meta, instType)
	}
	switch name {
	case utils.EqStr:
		return core.MakeConstTerm(core.MetaEq(), instType)
	case utils.HilbertStr:
		return core.MakeConstTerm(core.MetaHilbert(), instType)
	}
	// Const not found in metadata map. This should not happen after proper
	// initialization — it means the const-meta registration is incomplete.
	panic(fmt.Sprintf("const %q not found in the const-meta registry (the registration is incomplete)", name))
}

// ===========================================================================
// Pooled (content-addressed DAG) encoding — the canonical term serialization.
//
// A term is a DAG; the pool stores each distinct string / type-node / term-node
// once and refers to children by index. PoolBuilder interns core.Term/HolType
// into a shared PoolProto (deduping by structure AND by pointer, so DAG input
// is walked in O(distinct nodes)); PoolReader rebuilds core objects from a
// PoolProto in one linear bottom-up pass, restoring in-memory sharing.
//
// A blob that holds terms carries ONE PoolProto and references its entries by
// index (uint32 for a term/type, HolPropProto for a prop) — every shared
// subterm in the blob is stored once. Standalone term/type/prop blobs use the
// TermBlobProto / PropBlobProto wrappers; containers (CNF
// proofs, detailed proofs) embed a PoolProto at the top.
// ===========================================================================

// --- PoolBuilder: core.Term / core.HolType -> shared PoolProto ---

// PoolBuilder accumulates a shared PoolProto. Nodes are interned by a
// structural signature over children's already-assigned indices, so equal
// subterms collapse to one node and the pool stays topologically sorted.
//
// NOT SAFE FOR CONCURRENT USE. A PoolBuilder mutates its intern maps/slices on
// every Ref call — use exactly ONE builder per goroutine (to build many pools in
// parallel, give each goroutine its own builder). Misuse is caught
// deterministically: a second goroutine entering a public Ref/Pool while one is
// in flight panics, rather than triggering Go's nondeterministic "concurrent map
// writes" fatal.
//
// ONE-SHOT. Pool() SEALS the builder: it returns the builder's live slices (not
// a copy), so interning anything after Pool() would mutate the pool a consumer
// already holds. Such a post-Pool() Ref panics instead. Finish all
// TermRef/TypeRef/PropRef first, call Pool() once, then discard the builder.
type PoolBuilder struct {
	strings []string
	strIdx  map[string]uint32
	// types/nodes are deduped by a structural hash over (kind, child indices) —
	// children are interned first, so equal subterms share a canonical index and
	// hence an equal hash. The map buckets candidate indices per hash; a verify
	// (typeNodeEqual / termNodeEqual) confirms an exact match before reuse, so a
	// hash collision never merges distinct nodes. No string keys / delimiters.
	types   []*HolTypeProto
	typeIdx map[uint64][]uint32
	nodes   []*HolTermProto
	nodeIdx map[uint64][]uint32

	// Pointer memos: when the input is a shared-pointer DAG (e.g. anything from
	// PoolReader, or built by the prover with sharing) these collapse the walk
	// to O(distinct nodes). For tree input every pointer is distinct so they
	// never hit (one extra map probe per node).
	termMemo map[core.Term]uint32
	typeMemo map[core.HolType]uint32

	inUse  int32 // concurrent-use guard: CAS 0<->1 brackets every public entry
	sealed bool  // set by Pool(); any later intern panics (live-slice aliasing)
}

func NewPoolBuilder() *PoolBuilder {
	return &PoolBuilder{
		strIdx:   map[string]uint32{},
		typeIdx:  map[uint64][]uint32{},
		nodeIdx:  map[uint64][]uint32{},
		termMemo: map[core.Term]uint32{},
		typeMemo: map[core.HolType]uint32{},
	}
}

// NewPoolBuilderExtending returns a PoolBuilder pre-seeded with `pool`'s
// entries, so subsequent TermRef/TypeRef/PropRef list_append to it. Existing
// indices are preserved (the slices are only ever appended to), so any
// HolPropProto / term / type ref already minted against `pool` stays valid
// against the returned builder's Pool(). Newly-interned nodes dedup against the
// seeded entries (the intern maps are rebuilt by re-hashing), so a new prop
// that shares subterms with the pool reuses them rather than duplicating.
//
// Use this to splice a few synthesized nodes into an already-serialized pool
// (e.g. adding a node to a stored proof tree) without re-serializing every
// existing ref into a fresh pool. `pool` is read, never mutated; the builder
// copies its slice headers — the node/type pointers are shared, which is safe
// because pooled nodes are immutable.
func NewPoolBuilderExtending(pool *PoolProto) *PoolBuilder {
	b := NewPoolBuilder()
	if pool == nil {
		return b
	}
	b.strings = append(b.strings, pool.Strings...)
	for i, s := range pool.Strings {
		if _, ok := b.strIdx[s]; !ok {
			b.strIdx[s] = uint32(i)
		}
	}
	b.types = append(b.types, pool.Types...)
	for i, n := range pool.Types {
		h := hashTypeNode(n)
		b.typeIdx[h] = append(b.typeIdx[h], uint32(i))
	}
	b.nodes = append(b.nodes, pool.Nodes...)
	for i, n := range pool.Nodes {
		h := hashTermNode(n)
		b.nodeIdx[h] = append(b.nodeIdx[h], uint32(i))
	}
	return b
}

// lock/unlock bracket every PUBLIC entry point. The CAS makes concurrent use
// fail loudly and deterministically instead of corrupting the intern maps.
// Internal recursion goes through the unexported typeRef/termRef/varRef helpers,
// which do NOT lock, so same-goroutine recursion is fine.
func (b *PoolBuilder) lock() {
	if !atomic.CompareAndSwapInt32(&b.inUse, 0, 1) {
		panic("ext.PoolBuilder is not safe for concurrent use — use one builder per goroutine")
	}
}

func (b *PoolBuilder) unlock() { atomic.StoreInt32(&b.inUse, 0) }

func (b *PoolBuilder) assertUnsealed() {
	if b.sealed {
		panic("ext.PoolBuilder: interned after Pool() — Pool() returns the " +
			"builder's live slices; finish all TermRef/TypeRef/PropRef before " +
			"Pool(), then discard the builder")
	}
}

// Pool returns the accumulated shared pool and SEALS the builder. The returned
// PoolProto aliases the builder's internal slices (no copy); the builder must
// not be mutated afterward, and isn't — a subsequent Ref panics. The pool is
// immutable from here and safe to read / share concurrently.
func (b *PoolBuilder) Pool() *PoolProto {
	b.lock()
	defer b.unlock()
	b.sealed = true
	return &PoolProto{Strings: b.strings, Types: b.types, Nodes: b.nodes}
}

func (b *PoolBuilder) NumNodes() int   { b.lock(); defer b.unlock(); return len(b.nodes) }
func (b *PoolBuilder) NumTypes() int   { b.lock(); defer b.unlock(); return len(b.types) }
func (b *PoolBuilder) NumStrings() int { b.lock(); defer b.unlock(); return len(b.strings) }

func (b *PoolBuilder) internStr(s string) uint32 {
	if i, ok := b.strIdx[s]; ok {
		return i
	}
	i := uint32(len(b.strings))
	b.strings = append(b.strings, s)
	b.strIdx[s] = i
	return i
}

// internTypeNode returns the index of a structurally-equal existing type node,
// or appends node and returns its new index. Dedup is by structural hash with a
// verify against bucket candidates (a hash collision never merges distinct
// nodes).
func (b *PoolBuilder) internTypeNode(node *HolTypeProto) uint32 {
	h := hashTypeNode(node)
	for _, c := range b.typeIdx[h] {
		if typeNodeEqual(b.types[c], node) {
			return c
		}
	}
	i := uint32(len(b.types))
	b.types = append(b.types, node)
	b.typeIdx[h] = append(b.typeIdx[h], i)
	return i
}

func (b *PoolBuilder) internNode(node *HolTermProto) uint32 {
	h := hashTermNode(node)
	for _, c := range b.nodeIdx[h] {
		if termNodeEqual(b.nodes[c], node) {
			return c
		}
	}
	i := uint32(len(b.nodes))
	b.nodes = append(b.nodes, node)
	b.nodeIdx[h] = append(b.nodeIdx[h], i)
	return i
}

// hashTypeNode / hashTermNode mix the node kind and its already-canonical child
// indices into a structural hash (mixHash is the same mixer the reader's content
// hashing uses). Equal nodes have equal child indices, hence equal hashes.

func hashTypeNode(n *HolTypeProto) uint64 {
	switch x := n.Node.(type) {
	case *HolTypeProto_Var:
		return mixHash('V', uint64(x.Var))
	case *HolTypeProto_Comp:
		h := mixHash('C', uint64(x.Comp.MetaName))
		for _, a := range x.Comp.Args {
			h = mixHash(h, uint64(a))
		}
		return h
	}
	panic("hashTypeNode: empty type node")
}

func hashTermNode(n *HolTermProto) uint64 {
	switch x := n.Node.(type) {
	case *HolTermProto_Var:
		return mixHash(mixHash('v', uint64(x.Var.Name)), uint64(x.Var.Type))
	case *HolTermProto_Cnst:
		return mixHash(mixHash(mixHash('c', uint64(x.Cnst.Name)), uint64(x.Cnst.AbsType)), uint64(x.Cnst.Type))
	case *HolTermProto_App:
		return mixHash(mixHash('a', uint64(x.App.Fun)), uint64(x.App.Arg))
	case *HolTermProto_Abs:
		return mixHash(mixHash('l', uint64(x.Abs.Var)), uint64(x.Abs.Body))
	}
	panic("hashTermNode: empty term node")
}

// typeNodeEqual / termNodeEqual are the exact structural equality the hash
// buckets verify with — comparing kind + child indices (all uint32). They are
// the dedup criterion, not deep core equality.

func typeNodeEqual(a, b *HolTypeProto) bool {
	switch x := a.Node.(type) {
	case *HolTypeProto_Var:
		y, ok := b.Node.(*HolTypeProto_Var)
		return ok && x.Var == y.Var
	case *HolTypeProto_Comp:
		y, ok := b.Node.(*HolTypeProto_Comp)
		if !ok || x.Comp.MetaName != y.Comp.MetaName || len(x.Comp.Args) != len(y.Comp.Args) {
			return false
		}
		for i, a := range x.Comp.Args {
			if a != y.Comp.Args[i] {
				return false
			}
		}
		return true
	}
	return false
}

func termNodeEqual(a, b *HolTermProto) bool {
	switch x := a.Node.(type) {
	case *HolTermProto_Var:
		y, ok := b.Node.(*HolTermProto_Var)
		return ok && x.Var.Name == y.Var.Name && x.Var.Type == y.Var.Type
	case *HolTermProto_Cnst:
		y, ok := b.Node.(*HolTermProto_Cnst)
		return ok && x.Cnst.Name == y.Cnst.Name && x.Cnst.AbsType == y.Cnst.AbsType && x.Cnst.Type == y.Cnst.Type
	case *HolTermProto_App:
		y, ok := b.Node.(*HolTermProto_App)
		return ok && x.App.Fun == y.App.Fun && x.App.Arg == y.App.Arg
	case *HolTermProto_Abs:
		y, ok := b.Node.(*HolTermProto_Abs)
		return ok && x.Abs.Var == y.Abs.Var && x.Abs.Body == y.Abs.Body
	}
	return false
}

// TypeRef interns a core.HolType, returning its index into pool.types.
func (b *PoolBuilder) TypeRef(s core.HolType) uint32 {
	b.lock()
	defer b.unlock()
	b.assertUnsealed()
	return b.typeRef(s)
}

// typeRef is the unlocked recursive body of TypeRef (internal recursion must not
// re-take the lock).
func (b *PoolBuilder) typeRef(s core.HolType) uint32 {
	if i, ok := b.typeMemo[s]; ok {
		return i
	}
	var idx uint32
	switch t := s.(type) {
	case core.VarType:
		nameIdx := b.internStr(string(t.Name()))
		idx = b.internTypeNode(&HolTypeProto{Node: &HolTypeProto_Var{Var: nameIdx}})
	case core.CompositeType:
		metaIdx := b.internStr(string(t.Meta().Name()))
		args := make([]uint32, t.Meta().Arity())
		for i := range args {
			args[i] = b.typeRef(t.SubType(i))
		}
		idx = b.internTypeNode(
			&HolTypeProto{Node: &HolTypeProto_Comp{
				Comp: &CompositeTypeProto{MetaName: metaIdx, Args: args}}})
	default:
		panic("TypeRef: wrong HolType")
	}
	b.typeMemo[s] = idx
	return idx
}

func (b *PoolBuilder) varRef(v core.VarTerm) uint32 {
	if i, ok := b.termMemo[v]; ok {
		return i
	}
	nameIdx := b.internStr(string(v.Name()))
	typeIdx := b.typeRef(v.Type())
	idx := b.internNode(&HolTermProto{Node: &HolTermProto_Var{
		Var: &VarTermProto{Name: nameIdx, Type: typeIdx}}})
	b.termMemo[v] = idx
	return idx
}

// TermRef interns a core.Term, returning its index into pool.nodes.
func (b *PoolBuilder) TermRef(s core.Term) uint32 {
	b.lock()
	defer b.unlock()
	b.assertUnsealed()
	return b.termRef(s)
}

// termRef is the unlocked recursive body of TermRef.
func (b *PoolBuilder) termRef(s core.Term) uint32 {
	c := s.Core()
	if i, ok := b.termMemo[c]; ok {
		return i
	}
	var idx uint32
	switch t := c.(type) {
	case core.VarTerm:
		return b.varRef(t) // memoized inside, keyed by the same pointer
	case core.ConstTerm:
		nameIdx := b.internStr(string(t.Meta().Name()))
		absT := b.typeRef(t.Meta().AbsType())
		instT := absT
		if !t.Type().Equals(t.Meta().AbsType()) {
			instT = b.typeRef(t.Type())
		}
		idx = b.internNode(&HolTermProto{Node: &HolTermProto_Cnst{
			Cnst: &ConstTermProto{Name: nameIdx, AbsType: absT, Type: instT}}})
	case core.AppliedTerm:
		fun := b.termRef(t.Fun())
		arg := b.termRef(t.Arg())
		idx = b.internNode(&HolTermProto{Node: &HolTermProto_App{
			App: &AppliedTermProto{Fun: fun, Arg: arg}}})
	case core.AbsTerm:
		varIdx := b.varRef(t.Var())
		body := b.termRef(t.Body())
		idx = b.internNode(&HolTermProto{Node: &HolTermProto_Abs{
			Abs: &AbsTermProto{Var: varIdx, Body: body}}})
	default:
		panic("TermRef: wrong term type")
	}
	b.termMemo[c] = idx
	return idx
}

// PropRef interns a prop's conclusion and hyps into the pool, returning a
// HolPropProto that points at them (it carries no pool of its own — the pool is
// the container's). Use for a prop embedded in a pooled container.
func (b *PoolBuilder) PropRef(p core.Prop) *HolPropProto {
	b.lock()
	defer b.unlock()
	b.assertUnsealed()
	concl := b.termRef(p.Conclusion())
	hyps := make([]uint32, p.NumHyps())
	for i := range hyps {
		hyps[i] = b.termRef(p.Hyp(i))
	}
	return &HolPropProto{Concl: concl, Hyps: hyps, ClaimProved: p.Proved()}
}

// --- PoolReader: PoolProto -> core.Term / core.HolType (lazy, memoized) ---

// PoolReader builds core terms/types from a pool ON DEMAND, memoizing each node
// the first time it is requested. Lazy (rather than building the whole pool up
// front) is load-bearing for replay: a clause whose content is already in the
// process-global clause cache is resolved by NodeContentHash WITHOUT building
// any of its terms — exactly as the legacy reader skipped DeserializeHolTerm on
// a cache hit. Equal subterms still build once and share by pointer (the result
// is a DAG) because every node is memoized in r.nodes/r.types.
//
// NOT SAFE FOR CONCURRENT USE. Memoization writes r.nodes/r.types/r.*Hash on
// every read, so a single PoolReader must stay within ONE goroutine. For shared
// / concurrent reads of one pool — query, render, parallel replay — give each
// goroutine its own reader built from the (immutable, read-only) *PoolProto; do
// not share a reader. The laziness here is load-bearing for the refute/clause-
// cache path that skips building terms via NodeContentHash, which is always
// single-goroutine.
type PoolReader struct {
	pool          *PoolProto
	loadConstMeta LoadConstMeta
	types         []core.HolType // lazy: nil = not yet built
	nodes         []core.Term    // lazy: nil = not yet built
	typeHash      []uint64       // lazy content-hash memo
	typeHashed    []bool
	nodeHash      []uint64
	nodeHashed    []bool
}

func NewPoolReader(pool *PoolProto, loadConstMeta LoadConstMeta) *PoolReader {
	return &PoolReader{
		pool:          pool,
		loadConstMeta: loadConstMeta,
		types:         make([]core.HolType, len(pool.Types)),
		nodes:         make([]core.Term, len(pool.Nodes)),
		typeHash:      make([]uint64, len(pool.Types)),
		typeHashed:    make([]bool, len(pool.Types)),
		nodeHash:      make([]uint64, len(pool.Nodes)),
		nodeHashed:    make([]bool, len(pool.Nodes)),
	}
}

func (r *PoolReader) Type(i uint32) core.HolType {
	if r.types[i] != nil {
		return r.types[i]
	}
	var out core.HolType
	switch x := r.pool.Types[i].Node.(type) {
	case *HolTypeProto_Var:
		out = core.MakeVarType(r.pool.Strings[x.Var])
	case *HolTypeProto_Comp:
		args := make([]core.HolType, len(x.Comp.Args))
		for k, a := range x.Comp.Args {
			args[k] = r.Type(a)
		}
		out = core.MakeCompositeType(
			core.MakeMetaType(r.pool.Strings[x.Comp.MetaName], len(args)), args...)
	default:
		panic("PoolReader: empty type node")
	}
	r.types[i] = out
	return out
}

func (r *PoolReader) Term(i uint32) core.Term {
	if r.nodes[i] != nil {
		return r.nodes[i]
	}
	var out core.Term
	switch x := r.pool.Nodes[i].Node.(type) {
	case *HolTermProto_Var:
		out = core.Var(r.pool.Strings[x.Var.Name], r.Type(x.Var.Type))
	case *HolTermProto_Cnst:
		out = makeConstFromMeta(
			r.pool.Strings[x.Cnst.Name], r.Type(x.Cnst.AbsType), r.Type(x.Cnst.Type), r.loadConstMeta)
	case *HolTermProto_App:
		out = core.Apply(r.Term(x.App.Fun), r.Term(x.App.Arg))
	case *HolTermProto_Abs:
		v, ok := r.Term(x.Abs.Var).AsVar()
		Assert(ok)
		out = core.Abs(v, r.Term(x.Abs.Body))
	default:
		panic("PoolReader: empty term node")
	}
	r.nodes[i] = out
	return out
}

// ConstNameAt returns the name of the const node at index i in pool, without
// building the term or needing const metadata (the name is a pooled string).
// ok is false if node i is not a const node.
func ConstNameAt(pool *PoolProto, i uint32) (string, bool) {
	if c, ok := pool.Nodes[i].Node.(*HolTermProto_Cnst); ok {
		return pool.Strings[c.Cnst.Name], true
	}
	return "", false
}

// Prop deserializes ref against the pool. The second return is the
// proto's ClaimProved bit — NOT a success flag (deserialization either
// succeeds or panics). Callers walking payloads regardless of proof
// status must ignore it; gating on it silently skips every unproved
// claim (the emit By-premise walk bug).
func (r *PoolReader) Prop(ref *HolPropProto) (core.Prop, bool) {
	hyps := make([]core.Term, len(ref.Hyps))
	for i, h := range ref.Hyps {
		hyps[i] = r.Term(h)
	}
	return core.MakeProp(r.Term(ref.Concl), hyps...), ref.ClaimProved
}

// --- Pool-structural content hashing (no core.Term building) ---
//
// These produce a pool-INDEPENDENT exact content hash: equal terms/types hash
// equally regardless of which pool (and which indices) they live in, computed
// straight from the proto pool with zero allocation (no Digest, no buffers — a
// streaming mix of xxhash string hashes and child hashes). This lets the
// clause cache be consulted before any term is built.

func mixHash(h, v uint64) uint64 {
	h ^= v
	h *= 0x9e3779b97f4a7c15
	h ^= h >> 29
	return h
}

func (r *PoolReader) typeContentHash(i uint32) uint64 {
	if r.typeHashed[i] {
		return r.typeHash[i]
	}
	var v uint64
	switch x := r.pool.Types[i].Node.(type) {
	case *HolTypeProto_Var:
		v = mixHash('t', xxhash.Sum64String(r.pool.Strings[x.Var]))
	case *HolTypeProto_Comp:
		v = mixHash('c', xxhash.Sum64String(r.pool.Strings[x.Comp.MetaName]))
		for _, a := range x.Comp.Args {
			v = mixHash(v, r.typeContentHash(a))
		}
	default:
		panic("PoolReader: empty type node")
	}
	r.typeHash[i] = v
	r.typeHashed[i] = true
	return v
}

// NodeContentHash returns the exact, pool-independent content hash of node i
// (var/const names+types, app/abs structure), memoized per reader.
func (r *PoolReader) NodeContentHash(i uint32) uint64 {
	if r.nodeHashed[i] {
		return r.nodeHash[i]
	}
	var v uint64
	switch x := r.pool.Nodes[i].Node.(type) {
	case *HolTermProto_Var:
		v = mixHash('V', xxhash.Sum64String(r.pool.Strings[x.Var.Name]))
		v = mixHash(v, r.typeContentHash(x.Var.Type))
	case *HolTermProto_Cnst:
		v = mixHash('C', xxhash.Sum64String(r.pool.Strings[x.Cnst.Name]))
		v = mixHash(v, r.typeContentHash(x.Cnst.Type))
	case *HolTermProto_App:
		v = mixHash('A', r.NodeContentHash(x.App.Fun))
		v = mixHash(v, r.NodeContentHash(x.App.Arg))
	case *HolTermProto_Abs:
		v = mixHash('L', r.NodeContentHash(x.Abs.Var))
		v = mixHash(v, r.NodeContentHash(x.Abs.Body))
	default:
		panic("PoolReader: empty term node")
	}
	r.nodeHash[i] = v
	r.nodeHashed[i] = true
	return v
}

// ClauseContentKey is the pool-independent exact key for a clause (its lit and
// univ node indices), used by the global clause cache. Computed without
// building any term.
func (r *PoolReader) ClauseContentKey(lits, univ []uint32) uint64 {
	v := uint64(0x436c6175736500) // "Clause\0"
	for _, l := range lits {
		v = mixHash(v, r.NodeContentHash(l))
	}
	v = mixHash(v, '|')
	for _, u := range univ {
		v = mixHash(v, r.NodeContentHash(u))
	}
	return v
}

// --- Standalone prop blob: core.Prop <-> *PropBlobProto ---

// SerializePropPool serializes a core.Prop into a self-contained pooled blob.
func SerializePropPool(p core.Prop) *PropBlobProto {
	b := NewPoolBuilder()
	ref := b.PropRef(p)
	return &PropBlobProto{Pool: b.Pool(), Concl: ref.Concl, Hyps: ref.Hyps, ClaimProved: ref.ClaimProved}
}

// DeserializePropPool rebuilds a core.Prop from a pooled blob (a DAG in memory).
// A nil pool means absent/empty data (or a non-pooled blob) — returns nil rather
// than panicking, so callers can treat it as "no prop".
func DeserializePropPool(p *PropBlobProto, loadConstMeta LoadConstMeta) (core.Prop, bool) {
	if p == nil || p.Pool == nil {
		return nil, false
	}
	r := NewPoolReader(p.Pool, loadConstMeta)
	return r.Prop(&HolPropProto{Concl: p.Concl, Hyps: p.Hyps, ClaimProved: p.ClaimProved})
}

// MarshalPropBlob / UnmarshalPropBlob are the standalone-prop codec (a
// session lineage's recorded lemma, claim and goal blobs).
//
// UnmarshalPropBlob's bool is the blob's claim-proved flag — whether
// the prop was serialized as a proved one — and not a success report:
// a blob with no pool decodes to (nil, false, nil), so a caller tests
// the prop for nil and the error, and reads the bool only as the
// claim it records.
func MarshalPropBlob(p core.Prop) ([]byte, error) {
	return proto.Marshal(SerializePropPool(p))
}

func UnmarshalPropBlob(b []byte, loadConstMeta LoadConstMeta) (core.Prop, bool, error) {
	var pp PropBlobProto
	if err := proto.Unmarshal(b, &pp); err != nil {
		return nil, false, fmt.Errorf("unmarshal pooled prop blob: %w", err)
	}
	prop, proved := DeserializePropPool(&pp, loadConstMeta)
	return prop, proved, nil
}
