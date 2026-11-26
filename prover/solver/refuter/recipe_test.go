package refuter

import (
	"sync"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"google.golang.org/protobuf/proto"
)

// countRecipes walks a serialized refutation certificate and counts how many
// deduce/derive clause-thm steps carry an inference recipe. Used to assert that
// the determinism test actually exercises the recipe replay path rather than a
// recipe-less fallback.
func countRecipes(node *RefuteStepProto) int {
	n := 0
	for _, rs := range node.GetReplay() {
		if d := rs.GetDerive(); d != nil && d.GetRecipe() != nil {
			n++
		}
	}
	switch step := node.Step.(type) {
	case *RefuteStepProto_Deduce:
		if step.Deduce.GetLocalStep().GetRecipe() != nil {
			n++
		}
	case *RefuteStepProto_Merge:
		for _, child := range step.Merge.GetChildren() {
			n += countRecipes(child)
		}
	}
	return n
}

// TestReconstructDeterministicViaRecipe proves a resolution-heavy goal (so the
// certificate contains recorded factor/resolution recipes) and then reconstructs
// the refutation theorem many times concurrently. Before recipes, reconstruction
// re-ran the wall-clock-bounded unification search, which under load could time
// out and return nil non-deterministically. With recipes the replay is
// search-free and must succeed every time.
//
// Run with -race to amplify scheduling pressure; the old search path panicked
// ~100% under -race, the recipe path stays clean.
func TestReconstructDeterministicViaRecipe(t *testing.T) {
	ctx := t.Context()

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := Var("P", core.MakeFun(TypeA, TypeA, TypeA))
	I := Var("Inv", core.MakeFun(TypeA, TypeA))
	One := Var("One", TypeA)

	// Group axioms ⊢ right inverse — the same resolution-heavy goal as
	// TestProofPersist1.
	g0 := ForAll(x, y, z)(P.Apply(x, P.Apply(y, z)).Eq(P.Apply(P.Apply(x, y), z)))
	g1 := ForAll(x)(P.Apply(One, x).Eq(x))
	g2 := ForAll(x)(P.Apply(I.Apply(x), x).Eq(One))
	g := ForAll(x)(P.Apply(x, I.Apply(x)).Eq(One))
	goal := TestProp(g, g0, g1, g2)

	refuter := CreateRefuter(ctx, goal, nil)
	proof := refuter.Prove(ctx)
	assert.True(t, refuter.Refuted())

	// Round-trip through the wire so we exercise the deserialized recipe path,
	// exactly as replay does.
	buf, err := proto.Marshal(proof)
	assert.Nil(t, err)
	wire := &CNFRefuteProofProto{}
	assert.Nil(t, proto.Unmarshal(buf, wire))

	recipes := countRecipes(wire.Root)
	t.Logf("certificate carries %d inference recipes", recipes)
	assert.Greater(t, recipes, 0,
		"expected at least one factor/resolution recipe; the determinism test "+
			"would otherwise not be exercising the recipe replay path")

	want := refuter.refutedCNFClauseThm.Thm

	const N = 64
	var wg sync.WaitGroup
	var mu sync.Mutex
	failures := 0
	for i := 0; i < N; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			defer func() {
				if r := recover(); r != nil {
					mu.Lock()
					failures++
					mu.Unlock()
				}
			}()
			ct := ReconstructCNFProofNode(wire.Root, ext.NewPoolReader(wire.Pool, loadConstMeta))
			if ct == nil || !ct.Thm.AlphaEquals(want) {
				mu.Lock()
				failures++
				mu.Unlock()
			}
		}()
	}
	wg.Wait()
	assert.Equal(t, 0, failures,
		"recipe replay must reconstruct deterministically on every run")
}
