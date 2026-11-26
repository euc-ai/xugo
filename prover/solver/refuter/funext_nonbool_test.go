package refuter

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
	"google.golang.org/protobuf/proto"
)

// funEqArgumentGoal builds `f = g ⊢ K(f) = K(g)` for f, g : A → codomain
// and an opaque head K : (A → codomain) → A. Pre-CNF normalization reads
// the hypothesis pointwise (∀x. f(x) = g(x); at bool, the iff pair),
// which reaches f only applied; the goal has f in ARGUMENT position of
// K, which only the unit equality f = g reaches, through Simplifies.
// FUNEXT derives that equality at init (ext/clause/funext.go).
func funEqArgumentGoal(codomain core.HolType) Prop {
	fun := MakeFun(TypeA, codomain)
	f := Var("f", fun)
	g := Var("g", fun)
	K := Var("K", MakeFun(fun, TypeA))
	return TestProp(K.Apply(f).Eq(K.Apply(g)), f.Eq(g))
}

// TestFunextArgumentPosition: a function equality reaches argument
// position whatever its codomain. The bool codomain (the set case,
// recovered from the pointwise iff pair) and the pointwise-reachable
// `f = g ⊢ f(a) = g(a)` are the controls.
func TestFunextArgumentPosition(t *testing.T) {
	defer goleak.VerifyNone(t)
	var cache utils.Map[core.TermKey, Prop]

	a := Var("a", TypeA)
	f := Var("f", MakeFun(TypeA, TypeB))
	g := Var("g", MakeFun(TypeA, TypeB))
	cases := []struct {
		name string
		goal Prop
	}{
		{"control: pointwise reach, non-bool codomain",
			TestProp(f.Apply(a).Eq(g.Apply(a)), f.Eq(g))},
		{"control: argument position, bool codomain", funEqArgumentGoal(TypeBool)},
		{"argument position, non-bool codomain", funEqArgumentGoal(TypeB)},
	}
	ctx, cancel := context.WithTimeout(t.Context(), _PROVE_BUDGET)
	defer cancel()
	for _, tc := range cases {
		p := CreateRefuter(t.Context(), tc.goal, &cache)
		p.Prove(ctx)
		assert.True(t, p.Refuted(), tc.name)
	}
}

// TestFunextArgumentPositionReplayRoundTrip: the certificate of the
// non-bool goal — the FUNEXT step and the Simplifies it feeds —
// round-trips through the wire and reconstructs deterministically.
func TestFunextArgumentPositionReplayRoundTrip(t *testing.T) {
	defer goleak.VerifyNone(t)
	var cache utils.Map[core.TermKey, Prop]
	ctx, cancel := context.WithTimeout(t.Context(), _PROVE_BUDGET)
	defer cancel()

	refuter := CreateRefuter(t.Context(), funEqArgumentGoal(TypeB), &cache)
	proof := refuter.Prove(ctx)
	require.True(t, refuter.Refuted())
	require.NotNil(t, proof)

	buf, err := proto.Marshal(proof)
	require.NoError(t, err)
	wire := &CNFRefuteProofProto{}
	require.NoError(t, proto.Unmarshal(buf, wire))
	assert.Greater(t, countRecipes(wire.Root), 0,
		"the certificate must carry its inference recipes")

	want := refuter.refutedCNFClauseThm.Thm
	for range 4 {
		ct := ReconstructCNFProofNode(
			wire.Root, ext.NewPoolReader(wire.Pool, loadConstMeta))
		require.NotNil(t, ct, "recipe replay must reconstruct")
		assert.True(t, ct.Thm.AlphaEquals(want))
	}
}
