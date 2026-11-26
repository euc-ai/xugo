package core_test

// What a certificate assumes, read from outside the package: every
// statement that entered it through a door other than a rule, carried
// by every rule and every settle to whatever is derived from it.

import (
	"context"
	"sort"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/require"
)

// assumes spells a certificate's assumptions as "door key", sorted.
func assumes(p core.Prop) []string {
	var out []string
	for _, a := range p.AsThmCert().Assumes() {
		out = append(out, a.Door.String()+" "+string(a.Statement.AlphaKey()))
	}
	sort.Strings(out)
	return out
}

// together is several such lists as one, sorted.
func together(lists ...[]string) []string {
	var out []string
	for _, l := range lists {
		out = append(out, l...)
	}
	sort.Strings(out)
	return out
}

func by(door core.AssumptionDoor, statements ...core.Prop) []string {
	var out []string
	for _, s := range statements {
		out = append(out, door.String()+" "+string(s.AlphaKey()))
	}
	sort.Strings(out)
	return out
}

func TestACertificateOfTheRulesAssumesNothing(t *testing.T) {
	boolType := core.TypeBool()
	x, y := core.Var("x", boolType), core.Var("y", boolType)
	f := core.Var("f", core.MakeFun(boolType, boolType))

	refl := core.Refl(x)
	assume := core.Assume(x)
	beta := core.Beta(core.Apply(core.Abs(x, x), x))
	eta := core.Eta(core.Apply(f, x))
	choice := core.Select(core.Apply(f, x))
	definition := core.NewConstDef(core.Abs(x, x), "zz_assumption_identity").DefThm()
	for name, cert := range map[string]core.ThmCert{
		"Refl": refl, "Assume": assume, "Beta": beta, "Eta": eta, "Select": choice, "NewConstDef": definition,
	} {
		require.Empty(t, cert.Assumes(), "%s assumes something", name)
	}
	require.Empty(t, assumes(core.EqTrans(core.EqSym(refl), refl)))
	require.Empty(t, assumes(core.PropTermInst(refl, core.MakeTermSubst(x, y))))
	require.Empty(t, assumes(core.Deduct(assume, assume)))
}

func TestEveryDoorMarksItsCertificate(t *testing.T) {
	boolType := core.TypeBool()
	x, y := core.Var("x", boolType), core.Var("y", boolType)

	axiom := core.NewAxiom(core.Eq(x, y))
	require.Equal(t, by(core.AxiomDoor, axiom), assumes(axiom))

	fabricated := core.TestThm(core.Eq(y, x))
	require.Equal(t, by(core.TestDoor, fabricated), assumes(fabricated))

	statement := core.MakeProp(x)
	promise := core.Promise(statement, func(core.Forcer) core.ThmCert { panic("no proof") })
	trusted, settled := core.ForceWithBoundary(context.Background(), promise, func(core.Prop) bool { return true })
	require.Len(t, settled, 1)
	require.Equal(t, by(core.BoundaryDoor, statement), assumes(trusted))

	// The mark is the certificate's: a later force of the settled cell,
	// plain or bounded by a predicate that trusts nothing, returns it.
	require.Equal(t, by(core.BoundaryDoor, statement), assumes(core.Force(context.Background(), promise)))
	again, settledAgain := core.ForceWithBoundary(context.Background(), promise, func(core.Prop) bool { return false })
	require.Empty(t, settledAgain)
	require.Equal(t, by(core.BoundaryDoor, statement), assumes(again))

	// One statement through one door is one assumption, and the same
	// statement through two doors is two.
	twice := core.EqTrans(core.NewAxiom(core.Eq(x, y)), core.EqSym(core.NewAxiom(core.Eq(x, y))))
	require.Equal(t, by(core.AxiomDoor, axiom), assumes(twice))
	both := core.EqTrans(core.NewAxiom(core.Eq(x, y)), core.EqSym(core.TestThm(core.Eq(x, y))))
	require.Equal(t,
		together(by(core.AxiomDoor, axiom), by(core.TestDoor, axiom)), assumes(both))
}

func TestEveryRuleCarriesWhatItsPremisesAssume(t *testing.T) {
	A := core.TypeA()
	boolType := core.TypeBool()
	x, y, z := core.Var("x", boolType), core.Var("y", boolType), core.Var("z", boolType)
	boolToBool := core.MakeFun(boolType, boolType)
	f, g := core.Var("f", boolToBool), core.Var("g", boolToBool)
	xa, ya := core.Var("x", A), core.Var("y", A)

	xEqY := core.NewAxiom(core.Eq(x, y))
	yEqZ := core.NewAxiom(core.Eq(y, z))
	fEqG := core.NewAxiom(core.Eq(f, g))
	justX := core.TestThm(x)
	justY := core.TestThm(y, x)
	xaEqYa := core.NewAxiom(core.Eq(xa, ya))
	both := func(a, b core.Prop) []string { return together(assumes(a), assumes(b)) }

	rules := map[string]struct {
		got  core.Prop
		want []string
	}{
		"EqSym":          {core.EqSym(xEqY), assumes(xEqY)},
		"EqTrans":        {core.EqTrans(xEqY, yEqZ), both(xEqY, yEqZ)},
		"EqMP":           {core.EqMP(xEqY, justX), both(xEqY, justX)},
		"Deduct":         {core.Deduct(justX, justY), both(justX, justY)},
		"DeriveTrans":    {core.DeriveTrans(justX, justY), both(justX, justY)},
		"PropApply":      {core.PropApply(fEqG, xEqY), both(fEqG, xEqY)},
		"PropLeftApply":  {core.PropLeftApply(f, xEqY), assumes(xEqY)},
		"PropRightApply": {core.PropRightApply(fEqG, x), assumes(fEqG)},
		"PropAbs":        {core.PropAbs(z, xEqY), assumes(xEqY)},
		"PropTypeInst":   {core.PropTypeInst(xaEqYa, core.MakeTypeSubst(A, boolType)), assumes(xaEqYa)},
		"PropTermInst":   {core.PropTermInst(xEqY, core.MakeTermSubst(x, z)), assumes(xEqY)},
	}
	for name, rule := range rules {
		require.NotEmpty(t, rule.want, name)
		require.Equal(t, rule.want, assumes(rule.got), "%s dropped or added an assumption", name)
	}

	// The type definition's two theorems stand on its source.
	identity := core.Abs(z, z)
	source := core.TestThm(core.Eq(identity, identity))
	_, mk, _ := core.NewTypeDef(source, "zz_assumption_one", "zz_assumption_mk", "zz_assumption_dest")
	retraction, membership := mk.Meta().TypeDefExpand(source)
	require.Equal(t, assumes(source), assumes(retraction))
	require.Equal(t, assumes(source), assumes(membership))
}

func TestAPromiseSettlesWithWhatItsProofAssumes(t *testing.T) {
	boolType := core.TypeBool()
	x, y, z := core.Var("x", boolType), core.Var("y", boolType), core.Var("z", boolType)
	ctx := context.Background()

	// A builder's certificate keeps its own assumptions.
	axiom := core.NewAxiom(core.Eq(x, y))
	built := core.Promise(core.MakeProp(core.Eq(y, x)), func(core.Forcer) core.ThmCert {
		return core.EqSym(axiom).AsThmCert()
	})
	// A rule over an unforced promise is a derived promise; forced, it
	// assumes what its dependencies turn out to assume.
	lazy := core.EqSym(built)
	require.True(t, core.IsPromised(lazy))
	require.Equal(t, assumes(axiom), assumes(core.Force(ctx, core.AsThm(lazy))))
	require.Equal(t, assumes(axiom), assumes(core.Force(ctx, built)))

	// The same over a dependency a bounded force settles from trust, and
	// over one a readiness check realizes.
	leaf := core.MakeProp(core.Eq(y, z))
	unbuilt := core.Promise(leaf, func(core.Forcer) core.ThmCert { panic("no proof") })
	chain := core.EqTrans(axiom, unbuilt)
	cert, _ := core.ForceWithBoundary(ctx, core.AsThm(chain), func(p core.Prop) bool { return p.AlphaEquals(leaf) })
	require.Equal(t, together(by(core.AxiomDoor, axiom), by(core.BoundaryDoor, leaf)), assumes(cert))
	onceSettled := core.EqSym(core.EqTrans(axiom, unbuilt))
	require.True(t, onceSettled.Proved())
	require.Equal(t, assumes(cert), assumes(onceSettled))

	// A promise declared at a certificate's statement promises the
	// statement, not what that certificate assumed.
	restated := core.Promise(axiom, func(core.Forcer) core.ThmCert { return core.TestThm(core.Eq(x, y)) })
	require.Equal(t, by(core.TestDoor, axiom), assumes(core.Force(ctx, restated)))

	// What Assumes hands out is the caller's.
	list := cert.Assumes()
	list[0] = core.Assumption{}
	require.Equal(t, together(by(core.AxiomDoor, axiom), by(core.BoundaryDoor, leaf)), assumes(cert))
}

// A bounded force settles a root promise from trust and never a derived
// one: a derivation whose result is a trusted statement is still
// derived, and stands on what it was derived over.
func TestOnlyARootPromiseIsSettledFromTrust(t *testing.T) {
	boolType := core.TypeBool()
	x, y := core.Var("x", boolType), core.Var("y", boolType)
	ctx := context.Background()
	leaf, result := core.MakeProp(core.Eq(x, y)), core.MakeProp(core.Eq(y, x))
	unbuilt := func() core.ThmPromise {
		return core.Promise(leaf, func(core.Forcer) core.ThmCert { panic("no proof") })
	}

	// Trusting the derived cell's statement alone does not settle it: its
	// dependency is forced, and that one has no proof.
	derived := core.AsThm(core.EqSym(unbuilt()))
	require.True(t, derived.AlphaEquals(result))
	require.Panics(t, func() {
		core.ForceWithBoundary(ctx, derived, func(p core.Prop) bool { return p.AlphaEquals(result) })
	})

	// Trusting both, the certificate assumes the root's statement and not
	// its own.
	derived = core.AsThm(core.EqSym(unbuilt()))
	cert, settled := core.ForceWithBoundary(ctx, derived, func(core.Prop) bool { return true })
	require.Len(t, settled, 1)
	require.True(t, settled[0].AlphaEquals(leaf))
	require.Equal(t, by(core.BoundaryDoor, leaf), assumes(cert))
}

// sharingAKey is two statements that are not α-equal and have one key:
// p ⊢ p, which the rule Assume derives, and ⊢ x for a variable x whose
// name spells where the first statement's two keys meet (TermKey).
func sharingAKey(t *testing.T) (derived core.ThmCert, x core.VarTerm, trusted core.Prop) {
	boolType := core.TypeBool()
	derived = core.Assume(core.Var("p", boolType))
	x = core.Var("p_"+string(boolType.Key())+"var_p", boolType)
	trusted = core.MakeProp(x)
	require.Equal(t, derived.AlphaKey(), trusted.AlphaKey(),
		"the two statements have two keys: this pair no longer shows what a shared key does")
	require.False(t, derived.AlphaEquals(trusted))
	return derived, x, trusted
}

func neverBuilt(core.Forcer) core.ThmCert {
	panic("a statement settled from trust is not built")
}

// A certificate lists the statement it was minted over, not another
// statement with that statement's key: here the other one is derived by
// a rule, and a list naming it would hide what was taken on trust.
func TestAnAssumptionIsItsStatementWhateverSharesItsKey(t *testing.T) {
	ctx := context.Background()
	derived, x, trusted := sharingAKey(t)
	everything := func(core.Prop) bool { return true }

	first, _ := core.ForceWithBoundary(ctx, core.Promise(derived.AsProp(), neverBuilt), everything)
	second, _ := core.ForceWithBoundary(ctx, core.Promise(trusted, neverBuilt), everything)
	anything := core.PropTermInst(second, core.MakeTermSubst(x, core.Var("q", core.TypeBool()))).AsThmCert()

	for name, c := range map[string]struct {
		cert core.ThmCert
		over core.Prop
	}{
		"the first settled":  {first, derived},
		"the second settled": {second, trusted},
		"an instance of it":  {anything, trusted},
	} {
		assumptions := c.cert.Assumes()
		require.Len(t, assumptions, 1, name)
		require.Equal(t, core.BoundaryDoor, assumptions[0].Door, name)
		require.True(t, assumptions[0].Statement.AlphaEquals(c.over), "%s lists another statement", name)
	}
	require.Len(t, core.Deduct(first, second).AsThmCert().Assumes(), 2,
		"a certificate standing on both lists one of them")

	again, _ := core.ForceWithBoundary(ctx, core.Promise(core.MakeProp(x), neverBuilt), everything)
	require.Len(t, core.Deduct(second, again).AsThmCert().Assumes(), 1,
		"two mints of one statement are two assumptions")
}

// The same through NewAxiom, over two terms with one key: g applied to
// a variable whose name runs on into the next key, and a function whose
// name does applied to x.
func TestAnAxiomIsItsStatementWhateverSharesItsKey(t *testing.T) {
	boolType := core.TypeBool()
	unary := core.MakeFun(boolType, boolType)
	one := core.Apply(core.Var("g_"+string(unary.Key())+"var_h", unary), core.Var("x", boolType))
	other := core.Apply(core.Var("g", unary), core.Var("h_"+string(unary.Key())+"var_x", boolType))
	require.Equal(t, one.AlphaKey(), other.AlphaKey(),
		"the two terms have two keys: this pair no longer shows what a shared key does")
	require.False(t, one.AlphaEquals(other))

	first, second := core.NewAxiom(one), core.NewAxiom(other)
	for name, cert := range map[string]core.ThmCert{"the first axiom": first, "the second axiom": second} {
		assumptions := cert.Assumes()
		require.Len(t, assumptions, 1, name)
		require.Equal(t, core.AxiomDoor, assumptions[0].Door, name)
		require.True(t, assumptions[0].Statement.AlphaEquals(cert), "%s lists another statement", name)
	}
	require.Len(t, core.Deduct(first, second).AsThmCert().Assumes(), 2)
	require.Len(t, core.Deduct(second, core.NewAxiom(other)).AsThmCert().Assumes(), 1)
}
