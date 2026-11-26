package ext

import (
	"sync/atomic"
	"testing"

	"github.com/euc-ai/xugo/core"

	"github.com/stretchr/testify/assert"
)

func TestPropPoolRoundTrip(t *testing.T) {
	loadConstMeta := InitConstMetaMap().Load

	x := Var("x", core.TypeA())
	y := Var("y", core.TypeA())
	q := Var("q", core.TypeBool())
	P := Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	s := P.To((Unique(q)(ForAll(x)(P.Apply(x.SuchThat(P.Apply(x))).Imply(q)).Imply(q))).
		Or(Exists(x)(ForAll(y)((P.Apply(x)).And(P.Apply(y)).Imply(
			x.SuchThat(P.Apply(x).Imply(q)).Neq(y))))))

	cases := []struct {
		name string
		prop core.Prop
	}{
		{"axiom", core.NewAxiom(Exists(x)(ForAll(y)(P.Apply(y).Imply(Not(x.Eq(y))))).Core())},
		{"hyps-prop", core.MakeProp(s.Eq(P.To(q)), s.Apply(P), P.Apply(y))},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			pool := SerializePropPool(tc.prop)

			// 1. core-level round-trip preserves the prop (and its PK, AlphaKey).
			got, proved := DeserializePropPool(pool, loadConstMeta)
			assert.Equal(t, tc.prop.Proved(), proved)
			assert.True(t, tc.prop.AlphaEquals(got))
			assert.Equal(t, tc.prop.AlphaKey(), got.AlphaKey(), "AlphaKey (theorems PK) must survive")
			assert.Equal(t, tc.prop.NumHyps(), got.NumHyps())

			// 2. The pointer-memo path: serializing a shared-pointer DAG (as
			//    produced by DeserializePropPool) reaches the same dedup level
			//    and round-trips to the same prop. (Byte-identical proto is NOT
			//    guaranteed — index-assignment order may permute harmlessly
			//    between tree-shaped and DAG-shaped input.)
			dag, _ := DeserializePropPool(pool, loadConstMeta)
			poolFromDag := SerializePropPool(dag)
			assert.Equal(t, len(pool.Pool.Nodes), len(poolFromDag.Pool.Nodes))
			assert.Equal(t, len(pool.Pool.Types), len(poolFromDag.Pool.Types))
			redag, _ := DeserializePropPool(poolFromDag, loadConstMeta)
			assert.Equal(t, tc.prop.AlphaKey(), redag.AlphaKey())

			// 4. Blob round-trip through the production marshal/unmarshal.
			blob, err := MarshalPropBlob(tc.prop)
			assert.NoError(t, err)
			fromBlob, _, err := UnmarshalPropBlob(blob, loadConstMeta)
			assert.NoError(t, err)
			assert.True(t, tc.prop.AlphaEquals(fromBlob))
			assert.Equal(t, tc.prop.AlphaKey(), fromBlob.AlphaKey())
		})
	}
}

// TestPoolBuilder_SealAfterPool: Pool() returns the builder's live slices, so
// interning after Pool() is a footgun — it must panic, not silently mutate the
// pool a consumer already holds.
func TestPoolBuilder_SealAfterPool(t *testing.T) {
	prop := core.MakeProp(Var("x", core.TypeA()).Eq(Var("y", core.TypeA())))

	b := NewPoolBuilder()
	_ = b.PropRef(prop)
	_ = b.Pool() // seals

	assert.Panics(t, func() { b.TermRef(prop.Conclusion()) }, "TermRef after Pool() must panic")
	assert.Panics(t, func() { b.PropRef(prop) }, "PropRef after Pool() must panic")
	assert.Panics(t, func() { b.TypeRef(core.TypeA()) }, "TypeRef after Pool() must panic")
	// Pool() itself stays idempotent (no mutation), so it must NOT panic.
	assert.NotPanics(t, func() { _ = b.Pool() }, "repeated Pool() is allowed")
}

// TestPoolBuilder_ConcurrentUsePanics deterministically exercises the
// concurrent-use guard: with inUse already set (simulating an in-flight call on
// another goroutine), any public Ref must panic rather than corrupt the maps.
func TestPoolBuilder_ConcurrentUsePanics(t *testing.T) {
	prop := core.MakeProp(Var("x", core.TypeA()).Eq(Var("y", core.TypeA())))

	b := NewPoolBuilder()
	atomic.StoreInt32(&b.inUse, 1) // pretend another goroutine is inside

	assert.Panics(t, func() { b.PropRef(prop) }, "concurrent PropRef must panic")
	assert.Panics(t, func() { b.TermRef(prop.Conclusion()) }, "concurrent TermRef must panic")
	assert.Panics(t, func() { b.TypeRef(core.TypeA()) }, "concurrent TypeRef must panic")
}
