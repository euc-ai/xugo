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

// conditionalSetEqGoal is the shape of a leaf on a prime spectrum's
// identity map: a set equality stated under a condition,
//
//	q ∈ P ⇒ preimage_on(c, f, q) = q,  q ∉ V  ⊢  ¬(q ∈ P ∧ preimage_on(c, f, q) ∈ V)
//
// with f the identity λa.a when lambdaArg is set and a plain variable
// otherwise. FunEqRewrite extensionalizes the equality into two
// pointwise clauses that each carry the condition's literal, so the
// equality never stands alone and `preimage_on(c, f, q) ∈ V`, where the
// set sits in argument position, is unreachable by resolution; the
// contextual FUNEXT recombination (ext/clause/funext.go) restores
// `q ∉ P ∨ preimage_on(c, f, q) = q` at init.
func conditionalSetEqGoal(lambdaArg bool) Prop {
	setA := MakeFun(TypeA, TypeBool)
	setSetA := MakeFun(setA, TypeBool)
	a := Var("a", TypeA)
	q := Var("q", setA)
	c := Var("c", setA)
	P := Var("P", setSetA)
	V := Var("V", setSetA)
	in := Var("set_member", core.MakeFun(setA, setSetA, TypeBool))
	pre := Var("preimage_on", core.MakeFun(setA, MakeFun(TypeA, TypeA), setA, setA))
	var f ext.TermLike = Var("f", MakeFun(TypeA, TypeA))
	if lambdaArg {
		f = a.To(a)
	}
	preQ := pre.Apply(c, f, q)
	qInP := in.Apply(q, P)
	return TestProp(
		Not(qInP.And(in.Apply(preQ, V))),
		qInP.Imply(preQ.Eq(q)),
		Not(in.Apply(q, V)))
}

// TestRefuteConditionalSetEquality: the conditional set equality closes
// at init, with the λ argument and without — the λ plays no part — and
// its certificate round-trips through the wire and reconstructs: the
// FUNEXT recipe replays the contextual recombination from its two input
// clauses.
func TestRefuteConditionalSetEquality(t *testing.T) {
	defer goleak.VerifyNone(t)
	for _, lambdaArg := range []bool{true, false} {
		var cache utils.Map[core.TermKey, Prop]
		ctx, cancel := context.WithTimeout(t.Context(), 5*time.Second)
		refuter := CreateRefuter(t.Context(), conditionalSetEqGoal(lambdaArg), &cache)
		proof := refuter.Prove(ctx)
		cancel()
		require.True(t, refuter.Refuted(), "lambdaArg=%v", lambdaArg)
		require.NotNil(t, proof)

		buf, err := proto.Marshal(proof)
		require.NoError(t, err)
		wire := &CNFRefuteProofProto{}
		require.NoError(t, proto.Unmarshal(buf, wire))
		assert.Greater(t, countRecipes(wire.Root), 0,
			"the certificate must carry the chain's recipes")
		want := refuter.refutedCNFClauseThm.Thm
		ct := ReconstructCNFProofNode(
			wire.Root, ext.NewPoolReader(wire.Pool, loadConstMeta))
		require.NotNil(t, ct, "recipe replay must reconstruct")
		assert.True(t, ct.Thm.AlphaEquals(want))
	}
}

// TestRefuteQuantifiedConditionalSetEquality: the condition's binder is
// not contracted over — `∀U. U ∈ S ⇒ preimage_on(c, f, U) = g(U)`
// recombines to `∀U. U ∉ S ∨ preimage_on(c, f, U) = g(U)`, which
// resolves against `U₀ ∈ S` into the unit equality the argument
// position needs.
func TestRefuteQuantifiedConditionalSetEquality(t *testing.T) {
	defer goleak.VerifyNone(t)
	setA := MakeFun(TypeA, TypeBool)
	setSetA := MakeFun(setA, TypeBool)
	U := Var("U", setA)
	U0 := Var("U₀", setA)
	c := Var("c", setA)
	f := Var("f", MakeFun(TypeA, TypeA))
	g := Var("g", MakeFun(setA, setA))
	S := Var("S", setSetA)
	V := Var("V", setSetA)
	in := Var("set_member", core.MakeFun(setA, setSetA, TypeBool))
	pre := Var("preimage_on", core.MakeFun(setA, MakeFun(TypeA, TypeA), setA, setA))
	goal := TestProp(
		Not(in.Apply(pre.Apply(c, f, U0), V)),
		ForAll(U)(in.Apply(U, S).Imply(pre.Apply(c, f, U).Eq(g.Apply(U)))),
		in.Apply(U0, S),
		Not(in.Apply(g.Apply(U0), V)))

	var cache utils.Map[core.TermKey, Prop]
	ctx, cancel := context.WithTimeout(t.Context(), 5*time.Second)
	defer cancel()
	refuter := CreateRefuter(t.Context(), goal, &cache)
	refuter.Prove(ctx)
	assert.True(t, refuter.Refuted())
}
