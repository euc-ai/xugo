package refuter

import (
	"context"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
	"google.golang.org/protobuf/proto"
)

// recipeRules lists the inference rules a certificate records, replay
// steps first, then the closing step, merges flattened in child order.
func recipeRules(node *RefuteStepProto) []string {
	var rules []string
	for _, rs := range node.GetReplay() {
		if d := rs.GetDerive(); d != nil && d.GetRecipe() != nil {
			rules = append(rules, d.GetRecipe().GetRule().String())
		}
	}
	switch step := node.Step.(type) {
	case *RefuteStepProto_Deduce:
		if r := step.Deduce.GetLocalStep().GetRecipe(); r != nil {
			rules = append(rules, r.GetRule().String())
		}
	case *RefuteStepProto_Merge:
		for _, child := range step.Merge.GetChildren() {
			rules = append(rules, recipeRules(child)...)
		}
	}
	return rules
}

// etaShortArgumentGoals are one goal shape, a function f standing bare as
// an argument of an opaque head, K(f) = K(e), with the equation f = e
// supplied in the ways that reach the refuter differently. Normalization
// reads f = e pointwise, ∀x. f(x) = e(x), and that unit reaches the
// argument occurrence of f only through Simplifies' η-aware rewrite. With
// e = λx. h(x, c) the FUNEXT recombination leaves a λ-sided equality the
// init pass filters, and a ground guard makes the clause divisible, so
// the unit is assumed by divide-and-conquer; every row closes only if a
// given or assumed clause meets the rewrite check a derived one does
// (refutesByRewrite).
func etaShortArgumentGoals() []struct {
	name string
	goal Prop
} {
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	c := Var("c", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	f := Var("f", MakeFun(TypeA, TypeB))
	g := Var("g", MakeFun(TypeA, TypeB))
	h := Var("h", MakeFun(TypeA, TypeA, TypeB))
	K := Var("K", MakeFun(MakeFun(TypeA, TypeB), TypeA))
	L := Var("L", MakeFun(TypeA, TypeA))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	lam := x.To(h.Apply(x, c))
	goalLam := K.Apply(f).Eq(K.Apply(lam))
	return []struct {
		name string
		goal Prop
	}{
		{"control, element type: a = b ⊢ L(a) = L(b)",
			TestProp(L.Apply(a).Eq(L.Apply(b)), a.Eq(b))},
		{"control, recombined: f = g ⊢ K(f) = K(g)",
			TestProp(K.Apply(f).Eq(K.Apply(g)), f.Eq(g))},
		{"given, λ-sided: f = λx.h(x,c) ⊢ K(f) = K(λx.h(x,c))",
			TestProp(goalLam, f.Eq(lam))},
		{"assumed by division: Q(c) ⇒ f = λx.h(x,c), Q(c) ⊢ K(f) = K(λx.h(x,c))",
			TestProp(goalLam, Q.Apply(c).Imply(f.Eq(lam)), Q.Apply(c))},
		{"derived by resolution: ∀y. Q(y) ⇒ f = λx.h(x,y), Q(c) ⊢ K(f) = K(λx.h(x,c))",
			TestProp(goalLam,
				ForAll(y)(Q.Apply(y).Imply(f.Eq(x.To(h.Apply(x, y))))),
				Q.Apply(c))},
	}
}

// TestInitClausesMeetSimplifies: every row of etaShortArgumentGoals
// closes, and the certificate names the rule that closed it.
func TestInitClausesMeetSimplifies(t *testing.T) {
	defer goleak.VerifyNone(t)
	for _, tc := range etaShortArgumentGoals() {
		t.Run(tc.name, func(t *testing.T) {
			var cache utils.Map[core.TermKey, Prop]
			ctx, cancel := context.WithTimeout(t.Context(), 5*time.Second)
			defer cancel()
			refuter := CreateRefuter(t.Context(), tc.goal, &cache)
			started := time.Now()
			proof := refuter.Prove(ctx)
			require.NoError(t, ctx.Err(), "the search must close or saturate, not time out")
			require.True(t, refuter.Refuted())
			t.Logf("closed in %v by %v", time.Since(started), recipeRules(proof.Root))
		})
	}
}

// TestInitClausesMeetSimplifiesReplayRoundTrip: a Simplifies step whose
// two hypotheses are both initial clauses round-trips through the wire
// and reconstructs.
func TestInitClausesMeetSimplifiesReplayRoundTrip(t *testing.T) {
	defer goleak.VerifyNone(t)
	goal := etaShortArgumentGoals()[2].goal
	var cache utils.Map[core.TermKey, Prop]
	ctx, cancel := context.WithTimeout(t.Context(), 5*time.Second)
	defer cancel()
	refuter := CreateRefuter(t.Context(), goal, &cache)
	proof := refuter.Prove(ctx)
	require.True(t, refuter.Refuted())
	require.NotNil(t, proof)
	assert.Equal(t, []string{"SIMPLIFIES"}, recipeRules(proof.Root))

	buf, err := proto.Marshal(proof)
	require.NoError(t, err)
	wire := &CNFRefuteProofProto{}
	require.NoError(t, proto.Unmarshal(buf, wire))
	want := refuter.refutedCNFClauseThm.Thm
	ct := ReconstructCNFProofNode(
		wire.Root, ext.NewPoolReader(wire.Pool, loadConstMeta))
	require.NotNil(t, ct, "recipe replay must reconstruct")
	assert.True(t, ct.Thm.AlphaEquals(want))
}
