package skeleton

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
)

func TestSkeletonKey_VariantsCollide(t *testing.T) {
	// Variant case: x:A=x:A and x:B=x:B share SkeletonKey since their
	// path encodings are identical (types are erased entirely).
	TypeB := core.MakeVarType("B")
	xA := ext.Var("x", core.TypeA())
	xB := ext.Var("x", TypeB)
	pA := core.MakeProp(core.Eq(xA, xA))
	pB := core.MakeProp(core.Eq(xB, xB))
	assert.Equal(t, SkeletonKey(pA), SkeletonKey(pB),
		"type-variants must share SkeletonKey")
}

func TestSkeletonKey_ConcreteInstantiationCollides(t *testing.T) {
	// Concrete-instantiation case: polymorphic source x:A=x:A and its
	// concrete instance x:bool=x:bool share SkeletonKey. This is the
	// key property — SkeletonKey erases ALL type info (vars AND
	// concrete), making it a necessary condition for NormalizedPropTypeMatch.
	xA := ext.Var("x", core.TypeA())
	xBool := ext.Var("x", core.TypeBool())
	pPoly := core.MakeProp(core.Eq(xA, xA))
	pConcrete := core.MakeProp(core.Eq(xBool, xBool))
	assert.Equal(t, SkeletonKey(pPoly), SkeletonKey(pConcrete),
		"polymorphic source and concrete instance must share SkeletonKey")
}

func TestSkeletonKey_ErasesConcreteTypes(t *testing.T) {
	// (A,A)→bool and (bool,bool)→bool: SkeletonKey erases the concrete
	// type bool as well as the type variables — one bucket.
	hAA := ext.Var("h", core.MakeFun(core.TypeA(), core.TypeA(), core.TypeBool()))
	hBoolBool := ext.Var("h", core.MakeFun(core.TypeBool(), core.TypeBool(), core.TypeBool()))
	pPoly := core.MakeProp(core.Eq(hAA, hAA))
	pConcrete := core.MakeProp(core.Eq(hBoolBool, hBoolBool))

	assert.Equal(t, SkeletonKey(pPoly), SkeletonKey(pConcrete))
}

func TestSkeletonKey_FreeVarNamesCollapse(t *testing.T) {
	// The skeleton encoding treats all free vars as `*F/0` wildcards
	// (only constants are distinguished by name). So props that differ
	// only in free-var identity share the SkeletonKey. This is
	// intentional over-approximation — bucket-internal
	// NormalizedPropTypeMatch then disambiguates (it rejects e.g.
	// x=x vs x=y since term-var names must α-match after type subst).
	xA := ext.Var("x", core.TypeA())
	yA := ext.Var("y", core.TypeA())
	assert.Equal(t,
		SkeletonKey(core.MakeProp(core.Eq(xA, xA))),
		SkeletonKey(core.MakeProp(core.Eq(xA, yA))),
		"free-var pattern differences are collapsed in skeleton encoding")
}

func TestSkeletonKey_DifferentConstantHeadsDiffer(t *testing.T) {
	// Constants ARE tracked by name. Two props with structurally similar
	// shape but different constant heads produce different keys.
	xA := ext.Var("x", core.TypeA())
	pBool := ext.Var("p", core.TypeBool())
	notP := ext.Not(pBool)
	xEqX := core.Eq(xA, xA)
	assert.NotEqual(t,
		SkeletonKey(core.MakeProp(notP)),
		SkeletonKey(core.MakeProp(xEqX)),
		"different constant heads must yield different SkeletonKeys")
}

func TestSkeletonKey_BoundVarRenamingTransparent(t *testing.T) {
	// λx:A.x and λy:A.y are α-equivalent; their SkeletonKeys agree.
	xA := ext.Var("x", core.TypeA()).AssertVar()
	yA := ext.Var("y", core.TypeA()).AssertVar()
	p := core.MakeProp(core.Eq(core.Abs(xA, xA), core.Abs(xA, xA)))
	q := core.MakeProp(core.Eq(core.Abs(yA, yA), core.Abs(yA, yA)))
	assert.Equal(t, SkeletonKey(p), SkeletonKey(q))
}

func TestSkeletonKey_HasPrefix(t *testing.T) {
	// Sanity: the SkeletonKey uses a distinct prefix from AlphaKey so
	// the two can't accidentally collide if shared by a single map.
	xA := ext.Var("x", core.TypeA())
	p := core.MakeProp(core.Eq(xA, xA))
	k := string(SkeletonKey(p))
	assert.True(t, len(k) > len(_SKELETON_KEY_PREFIX))
	assert.Equal(t, _SKELETON_KEY_PREFIX, k[:len(_SKELETON_KEY_PREFIX)])
}
