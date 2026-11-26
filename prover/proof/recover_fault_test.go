package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// raisedBy runs f and returns what it panicked with, nil when it
// returned.
func raisedBy(f func()) (r any) {
	defer func() { r = recover() }()
	f()
	return nil
}

// TestTypedForMembers_AFaultInTheTypingIsRaisedAgain: the member check
// types a polymorphic premise by its tuple and falls back to the stated
// form where the typing reports a failure. A fault in the typing is no
// such report: it is raised, not answered with the stated form. The
// fixture is a tuple holding no term, which the typing cannot read.
func TestTypedForMembers_AFaultInTheTypingIsRaisedAgain(t *testing.T) {
	A := core.MakeVarType("A")
	x := ext.Var("x", A)
	law := prop.MakeProp(ext.ForAll(x)(x.Eq(x)).Core())
	x0 := ext.Var("x_0", TypeInd)
	goal := prop.MakeProp(x0.Eq(x0).Core())

	require.NotPanics(t, func() { typedForMembers(law, []Term{x0.Core()}, goal) },
		"fixture: the typing reads a well-formed tuple")
	r := raisedBy(func() { typedForMembers(law, []Term{nil}, goal) })
	require.NotNil(t, r, "the fault is raised, not answered with the stated form")
	assert.True(t, utils.IsFault(r), "raised as it is, got %v", r)
}

// TestInstantiateLambdaPair_AFaultInTheChainIsRaisedAgain: the site
// instantiation answers "not instantiable" where its chain of
// instantiations reports a failure. A source whose body is no equation
// has drifted from the form the chain assumes; the kernel refuses the
// chain's last step by a failed assertion, which is raised.
func TestInstantiateLambdaPair_AFaultInTheChainIsRaisedAgain(t *testing.T) {
	A, B, C := core.MakeVarType("A"), core.MakeVarType("B"), core.MakeVarType("C")
	p := ext.Var("p", core.MakeVarType("P"))
	g := ext.Var("g", core.MakeFun(A, B, C))
	q := ext.Var("q", core.TypeBool())
	drifted := prop.MakeProp(ext.ForAll(p)(ext.ForAll(g)(q)).Core())

	x, y := core.Var("x", TypeInd), core.Var("y", TypeInd)
	site := &PairedBetaSite{XVar: x, YVar: y, Body: x, Pair: core.Var("pair", TypeInd)}

	r := raisedBy(func() { InstantiateLambdaPair(drifted, site) })
	require.NotNil(t, r, "the fault is raised, not answered with \"not instantiable\"")
	assert.True(t, utils.IsFault(r), "raised as it is, got %v", r)
}
