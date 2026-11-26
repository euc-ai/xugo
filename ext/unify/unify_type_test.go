package unify

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

func TestUnifyType(t *testing.T) {
	defer goleak.VerifyNone(t)

	allowed := func(t ...core.TypeName) VarTypePredicate {
		if len(t) == 0 {
			return utils.FullPredicate
		}
		return func(v VarType) bool {
			return utils.Any(t, func(s core.TypeName) bool { return v.Name() == s })
		}
	}

	TypeC := core.MakeVarType("C")

	substs, ok := unifyTypePair(TypeA, TypeA, allowed())
	assert.True(t, ok)
	assert.Empty(t, substs)

	substs, ok = unifyTypePair(TypeA, TypeB, allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs, MakeTypeSubst(TypeA, TypeB))

	substs, ok = unifyTypePair(TypeA, TypeB, allowed("B"))
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs, MakeTypeSubst(TypeB, TypeA))

	substs, ok = unifyTypePair(TypeA, TypeB, allowed("A", "B"))
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs, MakeTypeSubst(TypeA, TypeB))

	_, ok = unifyTypePair(TypeA, TypeB, allowed("C"))
	assert.False(t, ok)

	substs, ok = unifyTypePair(TypeA, TypeBool, allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs, MakeTypeSubst(TypeA, TypeBool))

	substs, ok = unifyTypePair(TypeBool, TypeA, allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs, MakeTypeSubst(TypeA, TypeBool))

	_, ok = unifyTypePair(TypeBool, TypeInd, allowed())
	assert.False(t, ok)

	_, ok = unifyTypePair(
		MakeFun(TypeA, TypeA, TypeA),
		MakeFun(MakeFun(TypeB, TypeB), TypeB), allowed())
	assert.False(t, ok)

	substs, ok = unifyTypePair(
		TypeA,
		MakeFun(TypeBool, TypeBool), allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs,
		MakeTypeSubst(TypeA,
			MakeFun(TypeBool, TypeBool)))

	_, ok = unifyTypePair(
		TypeA,
		MakeFun(TypeA, TypeBool), allowed())
	assert.False(t, ok)

	_, ok = unifyTypePair(
		MakeFun(TypeA, TypeBool),
		TypeA, allowed())
	assert.False(t, ok)

	substs, ok = unifyTypePair(
		MakeFun(MakeFun(TypeA, TypeBool), TypeB),
		MakeFun(TypeB, MakeFun(TypeA, TypeBool)), allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs,
		MakeTypeSubst(TypeB, MakeFun(TypeA, TypeBool)))

	_, ok = unifyTypePair(
		MakeFun(MakeFun(TypeA, TypeBool), TypeB),
		MakeFun(TypeA, MakeFun(TypeB, TypeBool)), allowed())
	assert.False(t, ok)

	_, ok = unifyTypePair(
		MakeFun(MakeFun(TypeB, TypeBool), TypeB),
		MakeFun(TypeA, MakeFun(TypeB, TypeBool)), allowed())
	assert.False(t, ok)

	substs, ok = unifyTypePair(
		MakeFun(TypeA, TypeBool),
		MakeFun(TypeA, TypeBool), allowed())
	assert.True(t, ok)
	assert.Empty(t, substs)

	substs, ok = unifyTypePair(
		MakeFun(TypeA, TypeBool),
		MakeFun(TypeBool, TypeA), allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs, MakeTypeSubst(TypeA, TypeBool))

	substs, ok = unifyTypePair(
		MakeFun(TypeA, TypeBool),
		MakeFun(TypeBool, TypeB), allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs,
		MakeTypeSubst(TypeA, TypeBool),
		MakeTypeSubst(TypeB, TypeBool))

	_, ok = unifyTypePair(
		MakeFun(TypeBool, TypeInd),
		MakeFun(TypeInd, TypeBool), allowed())
	assert.False(t, ok)

	substs, ok = unifyTypePair(
		MakeFun(TypeA, TypeB),
		MakeFun(TypeB, TypeA), allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs,
		MakeTypeSubst(TypeA, TypeB))

	substs, ok = unifyTypePair(
		MakeFun(TypeA, TypeB),
		MakeFun(TypeB, TypeA), allowed("B"))
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs,
		MakeTypeSubst(TypeB, TypeA))

	substs, ok = unifyTypePair(
		MakeFun(TypeA, TypeB),
		MakeFun(TypeA, TypeC), allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs, MakeTypeSubst(TypeB, TypeC))

	substs, ok = unifyTypePair(
		MakeFun(TypeA, TypeB),
		MakeFun(TypeA, TypeC), allowed("A", "C"))
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs, MakeTypeSubst(TypeC, TypeB))

	substs, ok = unifyTypePair(
		MakeFun(TypeA, TypeB),
		MakeFun(TypeB, TypeC), allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs,
		MakeTypeSubst(TypeA, TypeC),
		MakeTypeSubst(TypeB, TypeC))

	substs, ok = unifyTypePair(
		MakeFun(TypeA, TypeB),
		MakeFun(TypeB, TypeC), allowed("B", "C"))
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs,
		MakeTypeSubst(TypeB, TypeA),
		MakeTypeSubst(TypeC, TypeA))

	substs, ok = unifyTypePair(
		MakeFun(TypeA, TypeB),
		MakeFun(TypeB, TypeC), allowed("A", "C"))
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs,
		MakeTypeSubst(TypeA, TypeB),
		MakeTypeSubst(TypeC, TypeB))

	_, ok = unifyTypePair(
		MakeFun(TypeA, TypeB),
		MakeFun(TypeB, MakeFun(TypeA, TypeA)), allowed())
	assert.False(t, ok)

	substs, ok = unifyTypePair(
		MakeFun(TypeA, TypeA),
		MakeFun(MakeFun(TypeB, TypeC), TypeA), allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs,
		MakeTypeSubst(TypeA, MakeFun(TypeB, TypeC)))

	substs, ok = unifyTypePair(
		MakeFun(TypeA, TypeB),
		MakeFun(MakeFun(TypeInd, TypeInd), TypeInd), allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs,
		MakeTypeSubst(TypeA, MakeFun(TypeInd, TypeInd)),
		MakeTypeSubst(TypeB, TypeInd))

	_, ok = unifyTypePair(
		MakeFun(TypeA, TypeA),
		MakeFun(MakeFun(TypeInd, TypeInd), TypeInd), allowed())
	assert.False(t, ok)

	substs, ok = unifyTypePair(
		MakeFun(TypeA, TypeA),
		MakeFun(TypeB, TypeInd), allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs,
		MakeTypeSubst(TypeA, TypeInd),
		MakeTypeSubst(TypeB, TypeInd))

	_, ok = unifyTypePair(
		MakeFun(TypeA, TypeA),
		MakeFun(TypeB, TypeInd), allowed("A"))
	assert.False(t, ok)

	_, ok = unifyTypePair(
		MakeFun(TypeA, TypeA),
		MakeFun(TypeB, TypeInd), allowed("B"))
	assert.False(t, ok)

	substs, ok = unifyTypePair(
		MakeFun(TypeB, TypeA),
		MakeFun(TypeA, TypeInd), allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs,
		MakeTypeSubst(TypeA, TypeInd),
		MakeTypeSubst(TypeB, TypeInd))

	substs, ok = unifyTypePair(
		MakeFun(TypeInd, TypeA),
		MakeFun(TypeA, TypeInd), allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs, MakeTypeSubst(TypeA, TypeInd))

	substs, ok = unifyTypePair(
		MakeFun(TypeC, TypeC, TypeBool),
		MakeFun(MakeFun(TypeA, TypeB), MakeFun(TypeB, TypeA), TypeA), allowed())
	assert.True(t, ok)
	assertTypeSubstEqual(t, substs,
		MakeTypeSubst(TypeA, TypeBool),
		MakeTypeSubst(TypeB, TypeBool),
		MakeTypeSubst(TypeC, MakeFun(TypeBool, TypeBool)))
}
