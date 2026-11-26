package core_test

// The kernel's trust gate, probed from outside: this is an external test
// package, so it holds exactly what any importing package holds.
//
// Prop and Thm are interfaces of exported methods, so a type outside core
// satisfies them by embedding a core value and may override any exported
// method. The kernel reads every Prop through the unexported kernel()
// method, which promotion resolves to the embedded core value, so an
// embedder's own Conclusion, Proved, Core or AlphaEquals are never what a
// door sees. Each test feeds such an embedder to a door and checks that
// the door saw the embedded value and nothing else.
//
// Forcing is held the same way. It is a function of the package, which
// reads the kernel value, and no method of Thm: a Force an embedder
// declares is a method no door calls.

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/require"
)

// claimsProved embeds an unproved statement and claims it is proved.
type claimsProved struct{ core.Prop }

func (c claimsProved) Proved() bool    { return true }
func (c claimsProved) Core() core.Prop { return c }

// claimsForceable embeds an unproved statement, reports it unproved, and
// declares a Force that delivers nothing.
type claimsForceable struct{ claimsProved }

func (c claimsForceable) Proved() bool                       { return false }
func (c claimsForceable) Core() core.Prop                    { return c }
func (c claimsForceable) Force(context.Context) core.ThmCert { return core.ThmCert{} }

// relabels keeps a genuine certificate behind Core() and reports another
// statement through every other method.
type relabels struct {
	core.Prop
	real core.ThmCert
}

func (r relabels) Core() core.Prop { return r.real }

// conforms answers AlphaEquals with yes to anything and hides a genuine
// certificate behind Core().
type conforms struct {
	core.Prop
	real core.ThmCert
}

func (c conforms) AlphaEquals(core.Prop) bool { return true }
func (c conforms) Core() core.Prop            { return c.real }

// carries embeds a genuine certificate: the one legitimate shape of an
// outside Prop, which the doors must keep reading as the certificate.
type carries struct{ core.ThmCert }

// carriesThm embeds a Thm, the shape generated proof code traffics in.
type carriesThm struct{ core.Thm }

// _OverridesForce embeds a genuine theorem and declares forces of its
// own: one that fails, and a bounded one that hands back a genuine
// certificate of another statement.
type _OverridesForce struct{ core.Thm }

func (_OverridesForce) Force(context.Context) core.ThmCert {
	panic("an embedder's Force is not a kernel proof")
}

func (_OverridesForce) ForceWithBoundary(context.Context, core.PropPredicate) (core.ThmCert, []core.Prop) {
	return core.Refl(core.Var("y", core.TypeBool())), nil
}

// Every way of forcing realizes the embedded promise and never asks the
// embedder: a promise with no proof runs its own builder and fails, and
// a proved one yields the certificate of its own statement.
func TestAForceReadsTheKernelValue(t *testing.T) {
	ctx := context.Background()
	x := core.Var("x", core.TypeBool())
	forces := map[string]func(core.Thm) core.ThmCert{
		"Force": func(t core.Thm) core.ThmCert { return core.Force(ctx, t) },
		"ForceWithBoundary": func(t core.Thm) core.ThmCert {
			cert, _ := core.ForceWithBoundary(ctx, t, func(core.Prop) bool { return false })
			return cert
		},
		"Forcer.Force": func(t core.Thm) core.ThmCert { return core.NewForcer(ctx).Force(t) },
	}
	for name, force := range forces {
		built := false
		unproved := core.Promise(core.MakeProp(x), func(core.Forcer) core.ThmCert {
			built = true
			panic("no proof")
		})
		require.Panics(t, func() { force(_OverridesForce{unproved}) }, name)
		require.True(t, built, "%s did not run the promise's own builder", name)
		require.False(t, unproved.Proved(), "%s proved a promise whose builder failed", name)

		proved := core.Promise(core.MakeProp(core.Eq(x, x)), func(core.Forcer) core.ThmCert {
			return core.Refl(x)
		})
		require.True(t, force(_OverridesForce{proved}).AlphaEquals(proved),
			"%s returned a certificate of another statement", name)
	}
}

func TestEveryDoorReadsAPropThroughItsKernelValue(t *testing.T) {
	A := core.TypeA()
	x, y := core.Var("x", core.TypeBool()), core.Var("y", core.TypeBool())
	xa, ya := core.Var("x", A), core.Var("y", A)
	boolToBool := core.MakeFun(core.TypeBool(), core.TypeBool())
	f, g := core.Var("f", boolToBool), core.Var("g", boolToBool)
	z := core.Var("z", A)
	claim := func(concl core.Term) core.Prop { return claimsProved{core.MakeProp(concl)} }
	xEqY, yEqX := claim(core.Eq(x, y)), claim(core.Eq(y, x))
	fEqG := claim(core.Eq(f, g))
	justX, justY := claim(x), claim(y)
	xaEqYa := claim(core.Eq(xa, ya))

	doors := map[string]func() core.Prop{
		"EqSym":          func() core.Prop { return core.EqSym(xEqY) },
		"EqTrans":        func() core.Prop { return core.EqTrans(xEqY, yEqX) },
		"EqMP":           func() core.Prop { return core.EqMP(xEqY, justX) },
		"Deduct":         func() core.Prop { return core.Deduct(justX, justY) },
		"DeriveTrans":    func() core.Prop { return core.DeriveTrans(justX, justY) },
		"PropApply":      func() core.Prop { return core.PropApply(fEqG, xEqY) },
		"PropLeftApply":  func() core.Prop { return core.PropLeftApply(f, xEqY) },
		"PropRightApply": func() core.Prop { return core.PropRightApply(fEqG, x) },
		"PropAbs":        func() core.Prop { return core.PropAbs(z, xEqY) },
		"PropTypeInst": func() core.Prop {
			return core.PropTypeInst(xaEqYa, core.MakeTypeSubst(core.TypeA(), core.TypeBool()))
		},
		"PropTermInst": func() core.Prop { return core.PropTermInst(xEqY, core.MakeTermSubst(x, y)) },
	}
	for name, door := range doors {
		got := door()
		require.False(t, got.Proved(), "%s minted a certificate over an unproved statement", name)
		require.False(t, core.IsPromised(got), "%s minted a promise over an unproved statement", name)
	}
}

func TestADoorIgnoresAnEmbedderOwnCoreAndProved(t *testing.T) {
	x, y := core.Var("x", core.TypeBool()), core.Var("y", core.TypeBool())
	lie := core.MakeProp(core.Eq(x, y))

	// Core() returning a genuine theorem of another statement changes
	// nothing: the door reads the embedded (unproved) statement.
	got := core.EqSym(relabels{lie, core.Refl(x)})
	require.False(t, got.Proved())
	require.True(t, got.AlphaEquals(core.MakeProp(core.Eq(y, x))))

	// A Force that delivers nothing is never asked: no promise is derived
	// over a bare statement.
	got = core.EqSym(claimsForceable{claimsProved{lie}})
	require.False(t, got.Proved())
	require.False(t, core.IsPromised(got))

	// The narrowing door and the type test see the same value.
	require.Panics(t, func() { core.AsThm(claimsProved{lie}) })
	require.False(t, core.IsPromised(claimsProved{lie}))
}

func TestTypeDefExpandReadsItsSourceThroughItsKernelValue(t *testing.T) {
	z := core.Var("z", core.TypeBool())
	identity := core.Abs(z, z)
	src := core.Refl(identity) // ⊢ identity = identity, the form P(w) with P = (=) identity
	_, mk, _ := core.NewTypeDef(src, "zz_trust_one", "zz_trust_mk", "zz_trust_dest")

	// Another predicate of the same type, offered by an embedder whose
	// AlphaEquals says yes and whose Core() is the genuine source.
	f := core.Var("f", core.MakeFun(core.TypeBool(), core.TypeBool()))
	constTrue := core.Abs(z, core.Eq(z, z))
	other := core.Abs(f, core.Eq(f, constTrue))
	require.Panics(t, func() {
		mk.Meta().TypeDefExpand(conforms{core.MakeProp(core.Apply(other, identity)), src})
	})

	// The genuine source expands, embedded or not.
	_, membership := mk.Meta().TypeDefExpand(carries{src})
	require.True(t, membership.Proved())
}

func TestAnEmbeddedKernelValueIsReadAsItself(t *testing.T) {
	x := core.Var("x", core.TypeBool())

	cert := core.EqSym(carries{core.Refl(x)})
	_, isCert := cert.(core.ThmCert)
	require.True(t, isCert)

	stmt := core.MakeProp(core.Eq(x, x))
	promise := core.Promise(stmt, func(core.Forcer) core.ThmCert { return core.Refl(x) })
	derived := core.EqSym(carriesThm{promise})
	require.True(t, core.IsPromised(derived))
	require.True(t, core.Force(context.Background(), core.AsThm(derived)).AlphaEquals(stmt))
}

// AlphaKey is the α-class: a binder restored from its de Bruijn form takes
// a name the body does not mention, so a free variable spelled with the
// macron is never captured on the way to the key.
func TestAlphaKeyIsCanonicalWhenARestoredBinderMeetsAMacronName(t *testing.T) {
	A := core.TypeA()
	x, w := core.Var("x", A), core.Var("w", A)
	g := core.Var("g", core.MakeFun(A, A, A, core.TypeBool()))
	macron := core.Var("%2", A)                                                  // spelled ˍ2: a legal free variable
	deBruijn1 := core.Abs(x, x).DeBruijn(0).(core.AbsTerm).Body().(core.VarTerm) // the free de Bruijn var %1
	app := func(a, b, c core.Term) core.Term { return core.Apply(core.Apply(core.Apply(g, a), b), c) }

	shifted := core.Abs(x, app(x, macron, deBruijn1)).DeBruijn(0) // λ%2. g %2 ˍ2 %1
	s := shifted.Substitute(core.MakeTermSubst(deBruijn1, w))     // λ%2. g %2 ˍ2 w, with ˍ2 free
	same := core.Abs(x, app(x, macron, w))                        // λx. g x ˍ2 w
	differs := core.Abs(x, app(x, x, w))                          // λx. g x x w

	require.True(t, s.AlphaEquals(same))
	require.False(t, s.AlphaEquals(differs))
	require.Equal(t, same.AlphaKey(), s.AlphaKey())
	require.NotEqual(t, differs.AlphaKey(), s.AlphaKey())

	// ChangeAbsVar refuses a capturing name on a de Bruijn binder as on any other.
	require.Panics(t, func() { s.(core.AbsTerm).ChangeAbsVar(macron.Name()) })
}

// The zero value of the certificate type, core.ThmCert{}, is a
// composite literal Go allows anywhere, unexported fields or not. It
// holds no proposition, so it proves nothing: it is not Proved, reading its statement
// panics, and a door handed it either panics or hands back a value
// whose statement cannot be read either — a substitution that touches
// nothing returns its input, and the input is still the zero value.
// What is held here is that no door turns it into a theorem of
// anything.
func TestTheZeroCertificateProvesNothing(t *testing.T) {
	zero := core.ThmCert{}
	require.False(t, zero.Proved(), "the zero certificate is proved")
	x, y := core.Var("x", core.TypeBool()), core.Var("y", core.TypeBool())
	f := core.Var("f", core.MakeFun(core.TypeBool(), core.TypeBool()))
	require.Panics(t, func() { zero.Conclusion() }, "the zero certificate has a conclusion")
	require.Panics(t, func() { zero.Hyps() }, "the zero certificate has hypotheses")
	require.Panics(t, func() { zero.AlphaKey() }, "the zero certificate has a key")

	doors := map[string]func() core.Prop{
		"EqSym":          func() core.Prop { return core.EqSym(zero) },
		"EqTrans":        func() core.Prop { return core.EqTrans(zero, zero) },
		"EqMP":           func() core.Prop { return core.EqMP(zero, zero) },
		"Deduct":         func() core.Prop { return core.Deduct(zero, zero) },
		"DeriveTrans":    func() core.Prop { return core.DeriveTrans(zero, zero) },
		"PropApply":      func() core.Prop { return core.PropApply(zero, zero) },
		"PropLeftApply":  func() core.Prop { return core.PropLeftApply(f, zero) },
		"PropRightApply": func() core.Prop { return core.PropRightApply(zero, x) },
		"PropAbs":        func() core.Prop { return core.PropAbs(x, zero) },
		"PropTypeInst": func() core.Prop {
			return core.PropTypeInst(zero, core.MakeTypeSubst(core.TypeA(), core.TypeBool()))
		},
		"PropTermInst": func() core.Prop { return core.PropTermInst(zero, core.MakeTermSubst(x, y)) },
	}
	for name, door := range doors {
		require.Panics(t, func() { door().Conclusion() }, "%s made a theorem of the zero certificate", name)
	}
}
