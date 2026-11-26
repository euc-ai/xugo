package registry

import (
	"runtime"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// ConstDefKind classifies how a const's "definitional thm" is derived
// from its ConstTermMeta. The emit layer dispatches an external leaf
// back to the right Script helper by it at emit / replay time.
type ConstDefKind int

const (
	// ConstDefThm: the const was introduced by NewConstDef (or
	// a define door, which mints through it). The leaf thm is meta.def — the c = body equation,
	// possibly a conjunction of clauses.
	ConstDefThm ConstDefKind = iota
	// TypeDefAbsRepEq: the const is one half of a NewTypeDef pair. The
	// leaf thm is `⊢ abs(rep a) = a`, the first output of TypeDefExpand
	// applied to meta.defSource.
	TypeDefAbsRepEq
	// TypeDefPredRepEq: same NewTypeDef pair as TypeDefAbsRepEq but the
	// other output: `⊢ P(r) ⇔ rep(abs r) = r`.
	TypeDefPredRepEq
)

// ConstDefRef identifies which const a normalized prop key is the
// "definitional thm" of, and which form (NewConstDef def, type-def
// abs/rep eq, type-def pred/rep eq).
//
// ConstName is the actual const's name (e.g. `+`), never a theorem
// name. For NewTypeDef pairs the abs-half's name is stored; either
// half works as an argument to the Script.TypeDefAxiom helper because
// meta.TypeDefExpand recovers orientation from the pair pointer.
type ConstDefRef struct {
	ConstName string
	Kind      ConstDefKind
}

// ConstDefIndex maps the normalized key of a constant's definitional
// theorem to the constant — the reverse index the emit layer reads to
// label a definitional external leaf (LeafConstDef / LeafTypeDefAxiom).
type ConstDefIndex map[core.PropKey]ConstDefRef

// BuildConstDefIndex walks the given constants once, hashing each
// const's "definitional thm" payload(s) by the AlphaKey of the
// Normalize-d form (a session's leaf keys are normalized keys, so the
// lookup compares on the same canonical form).
//
// For NewConstDef consts: one entry, keyed on Normalize(meta.def).
// For NewTypeDef pairs: two entries, keyed on the two outputs of
// meta.TypeDefExpand(meta.defSource). Indexed under the abs-half's
// name only — IsTypeDefAbs() gates the work to avoid double-walking
// each pair.
//
// The ⊤ bucket is excluded: every tautology Normalizes to ⊢ ⊤ and
// collapses onto one key, and a handful of logical-primitive consts
// have definitional thms that are themselves tautologies (`∀ = (λP. P
// = λx.⊤)`, `¬ = (λp. p ⇔ ⊥)`, `∃ = (λP. P(ε P))`, ⊤/⊥ themselves).
// Indexing those would let the ⊤ key resolve to an arbitrary
// connective (last writer over a non-deterministic Range) and
// mis-label ANY ⊤-normalizing external leaf.
//
// Each constant's rows are computed once per process (constDefRowsOf),
// spread over every processor, and the index is assembled in the order
// the walk visits the constants.
func BuildConstDefIndex(rangeMetas func(yield func(core.ConstTermMeta) bool)) ConstDefIndex {
	var metas []core.ConstTermMeta
	rangeMetas(func(meta core.ConstTermMeta) bool {
		metas = append(metas, meta)
		return true
	})
	rows := make([][]_ConstDefRow, len(metas))
	next := make(chan int)
	var wg sync.WaitGroup
	for range runtime.GOMAXPROCS(0) {
		wg.Go(func() {
			for i := range next {
				rows[i] = constDefRowsOf(metas[i])
			}
		})
	}
	for i := range metas {
		next <- i
	}
	close(next)
	wg.Wait()

	idx := make(ConstDefIndex)
	topKey := trivialTrueKey()
	for _, rs := range rows {
		for _, r := range rs {
			if r.key != topKey {
				idx[r.key] = r.ref
			}
		}
	}
	return idx
}

// _ConstDefRow is one row a constant contributes to the index.
type _ConstDefRow struct {
	key core.PropKey
	ref ConstDefRef
}

// constDefRows holds each constant's rows by its meta. A meta's
// definitional theorem is fixed when the constant is minted and
// prop.Normalize is a function of the statement alone (the keys
// spelled in source rest on the same fact), so a constant's rows
// never change once computed.
var constDefRows sync.Map // core.ConstTermMeta → []_ConstDefRow

// constDefRowsOf is the constant's rows: one for a NewConstDef
// constant, two for the abs-half of a NewTypeDef pair, none otherwise.
func constDefRowsOf(meta core.ConstTermMeta) []_ConstDefRow {
	if rs, ok := constDefRows.Load(meta); ok {
		return rs.([]_ConstDefRow)
	}
	var rs []_ConstDefRow
	name := string(meta.Name())
	if def := meta.DefThm(); !def.IsZero() {
		normalized, _ := prop.Normalize(def)
		rs = append(rs, _ConstDefRow{normalized.AlphaKey(), ConstDefRef{ConstName: name, Kind: ConstDefThm}})
	}
	if meta.DefSource() != nil && meta.IsTypeDefAbs() {
		out1, out2 := meta.TypeDefExpand(meta.DefSource())
		n1, _ := prop.Normalize(out1)
		n2, _ := prop.Normalize(out2)
		rs = append(rs,
			_ConstDefRow{n1.AlphaKey(), ConstDefRef{ConstName: name, Kind: TypeDefAbsRepEq}},
			_ConstDefRow{n2.AlphaKey(), ConstDefRef{ConstName: name, Kind: TypeDefPredRepEq}})
	}
	constDefRows.Store(meta, rs)
	return rs
}

// trivialTrueKey is the AlphaKey of the normalized ⊢ ⊤ prop — the
// shared bucket every tautology collapses into under prop.Normalize.
func trivialTrueKey() core.PropKey {
	n, _ := prop.Normalize(prop.MakeProp(ext.T))
	return n.AlphaKey()
}
