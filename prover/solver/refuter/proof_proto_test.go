package refuter

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	ext "github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
	"google.golang.org/protobuf/proto"
)

var loadConstMeta = ext.InitConstMetaMap().Load

func TestProofPersist0(t *testing.T) {
	defer goleak.VerifyNone(t)
	ctx := t.Context()

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))

	// ∃x.∀y.(t(y) ⇔ (x = y)) = ∃x.t ∧ ∀x.∀y.((t(x) ∧ t(y)) ⇒ (x = y))
	g0 := Exists(x)(P.Apply(x)).And(ForAll(x, y)(P.Apply(x).And(P.Apply(y)).Imply(x.Eq(y))))
	g1 := Exists(x)(ForAll(y)(P.Apply(y).Eq(x.Eq(y))))

	goal := TestProp(g0.And(g1).Or(Not(g0).And(Not(g1))))
	refuter := CreateRefuter(ctx, goal, nil)
	proof := refuter.Prove(ctx)
	assert.True(t, refuter.Refuted())
	assert.True(t, ReconstructCNFProofNode(proof.Root, ext.NewPoolReader(proof.Pool, loadConstMeta)).Thm.
		AlphaEquals(refuter.refutedCNFClauseThm.Thm))
	buf, err := proto.Marshal(proof)
	assert.Nil(t, err)
	message := &CNFRefuteProofProto{}
	err = proto.Unmarshal(buf, message)
	assert.Nil(t, err)
	assert.True(t, proto.Equal(proof, message))
}

func TestProofPersist1(t *testing.T) {
	defer goleak.VerifyNone(t)
	ctx := t.Context()

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := Var("P", core.MakeFun(TypeA, TypeA, TypeA))
	I := Var("Inv", core.MakeFun(TypeA, TypeA))
	One := Var("One", TypeA)

	g0 := ForAll(x, y, z)(P.Apply(x, P.Apply(y, z)).Eq(P.Apply(P.Apply(x, y), z)))
	g1 := ForAll(x)(P.Apply(One, x).Eq(x))
	g2 := ForAll(x)(P.Apply(I.Apply(x), x).Eq(One))
	g := ForAll(x)(P.Apply(x, I.Apply(x)).Eq(One))
	goal := TestProp(g, g0, g1, g2)
	refuter := CreateRefuter(ctx, goal, nil)
	proof := refuter.Prove(ctx)
	assert.True(t, refuter.Refuted())
	assert.True(t, ReconstructCNFProofNode(proof.Root, ext.NewPoolReader(proof.Pool, loadConstMeta)).Thm.
		AlphaEquals(refuter.refutedCNFClauseThm.Thm))
	buf, err := proto.Marshal(proof)
	assert.Nil(t, err)
	message := &CNFRefuteProofProto{}
	err = proto.Unmarshal(buf, message)
	assert.Nil(t, err)
	assert.True(t, proto.Equal(proof, message))
}
