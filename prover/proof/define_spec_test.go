package proof

// define_spec.go units: the analysis grammar, the fresh nested mint,
// and the spec existence compiler run to REAL kernel certificates at
// test-local constants — including the imported specification
// twin shape (name-tag binders, inner function-form existential, the
// two-constant bridge chain) that the nat_div/nat_mod claim rides.

import (
	"math/big"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// specTestMatrix builds the toy specification matrix
// (qv = m) ∧ (rv = n) at the given value terms.
func specTestMatrix(qv, rv, m, n *ext.TermWrapper) *ext.TermWrapper {
	return qv.Eq(m).And(rv.Eq(n))
}

// specTestObligation derives ⊢ ∀m n. ∃u v. (u = m) ∧ (v = n) — the
// pointwise obligation of the toy specification — from first
// principles.
func specTestObligation(t *testing.T) Prop {
	t.Helper()
	m := Var("m", ext.NumType)
	n := Var("n", ext.NumType)
	u := Var("u", ext.NumType)
	v := Var("v", ext.NumType)

	reflM := prop.WrapProp(core.Refl(m.Core()))
	reflN := prop.WrapProp(core.Refl(n.Core()))
	pair := prop.ConclAND(reflM.Conclusion(), reflN.Conclusion())
	both := reflN.DeriveTrans(reflM.DeriveTrans(pair))

	inner := ext.Exists(v)(specTestMatrix(m, v, m, n)).Core()
	both = both.DeriveTrans(prop.InstExists(inner, n.Core()))
	outer := ext.Exists(u)(ext.Exists(v)(specTestMatrix(u, v, m, n))).Core()
	both = both.DeriveTrans(prop.InstExists(outer, m.Core()))
	closed := both.ConclForAllList(m.Core().(core.VarTerm), n.Core().(core.VarTerm))
	require.True(t, closed.Proved(), "obligation fixture must be a real theorem")
	return closed.Prop
}

func specTestFun3() core.HolType {
	return MakeFun(ext.NumType, MakeFun(ext.NumType, MakeFun(ext.NumType, ext.NumType)))
}

func specTestFun2() core.HolType {
	return MakeFun(ext.NumType, MakeFun(ext.NumType, ext.NumType))
}

// mintTaggedSpecTwins mints the imported-specification twin pair
// at fresh names — the nat_div/nat_mod shape at a toy matrix:
//
//	c1 := (εq. ∀tag. ∃r. ∀m n. (q(tag,m,n) = m) ∧ (r(m,n) = n))(42)
//	c2 := (εr. ∀tag. ∀m n. (c1(m,n) = m) ∧ (r(tag,m,n) = n))(7)
func mintTaggedSpecTwins(t *testing.T, name1, name2 string) (c1, c2 core.ConstTerm) {
	t.Helper()
	m := Var("m", ext.NumType)
	n := Var("n", ext.NumType)
	tag := Var("tag", ext.NumType)
	q := Var("q", specTestFun3())
	r2 := Var("r", specTestFun2())

	tagValue := ext.MakeNumeral(big.NewInt(42))

	inner := ext.ForAll(m, n)(specTestMatrix(q.Apply(tag, m, n), r2.Apply(m, n), m, n))
	payload1 := q.SuchThat(ext.ForAll(tag)(ext.Exists(r2)(inner)))
	c1w := ext.ConstDef(payload1.Apply(tagValue).Core(), ext.TermName(name1))
	c1 = c1w.AssertConst()

	r3 := Var("r", specTestFun3())
	body2 := ext.ForAll(m, n)(specTestMatrix(
		ext.WrapTerm(c1).Apply(m, n), r3.Apply(tag, m, n), m, n))
	payload2 := r3.SuchThat(ext.ForAll(tag)(body2))
	c2w := ext.ConstDef(payload2.Apply(tagValue).Core(), ext.TermName(name2))
	c2 = c2w.AssertConst()
	return c1, c2
}

func TestAnalyzeSpecGoal_TwoConst(t *testing.T) {
	c1, c2 := mintTaggedSpecTwins(t, "zz_spec_an1", "zz_spec_an2")
	m := Var("m", ext.NumType)
	n := Var("n", ext.NumType)
	goal := prop.MakeProp(ext.ForAll(m, n)(specTestMatrix(
		ext.WrapTerm(c1).Apply(m, n), ext.WrapTerm(c2).Apply(m, n), m, n)).Core())

	sd, err := AnalyzeSpecGoal(goal, []core.ConstTerm{c1, c2})
	require.NoError(t, err)
	require.Len(t, sd.Binders, 2)
	require.Len(t, sd.AppArgs, 2)
	require.Len(t, sd.AppArgs[0], 2)

	// The obligation: ∀m n. ∃v1 v2. (v1 = m) ∧ (v2 = n).
	u := Var("u", ext.NumType)
	v := Var("v", ext.NumType)
	want := ext.ForAll(m, n)(ext.Exists(u)(ext.Exists(v)(
		specTestMatrix(u, v, m, n)))).Core()
	require.True(t, sd.Obligation.Conclusion().AlphaEquals(want),
		"obligation = %s\nwant %s", ext.PrintTerm(sd.Obligation.Conclusion()),
		ext.PrintTerm(want))
}

func TestCompileSpecExistence_TaggedChain(t *testing.T) {
	c1, c2 := mintTaggedSpecTwins(t, "zz_spec_tc1", "zz_spec_tc2")
	m := Var("m", ext.NumType)
	n := Var("n", ext.NumType)
	goal := prop.MakeProp(ext.ForAll(m, n)(specTestMatrix(
		ext.WrapTerm(c1).Apply(m, n), ext.WrapTerm(c2).Apply(m, n), m, n)).Core())

	sd, err := AnalyzeSpecGoal(goal, []core.ConstTerm{c1, c2})
	require.NoError(t, err)

	obligation := specTestObligation(t)
	derived, err := CompileSpecExistence(nil, sd, obligation)
	require.NoError(t, err)
	out := prop.BridgeNormalize(goal, derived)
	require.NotNil(t, out, "derived %s does not bridge onto goal %s",
		prop.PrintProp(derived), prop.PrintProp(goal))
	require.True(t, out.Proved() || core.IsPromised(out),
		"the derived characterizing statement must carry a certificate")
}

func TestCompileSpecExistence_FreshTwoConst(t *testing.T) {
	env := &ProverEnv{ProofService: MockConstMetaService()}
	m := Var("m", ext.NumType)
	n := Var("n", ext.NumType)
	q := Var("zz_spec_fresh_q", specTestFun2())
	r := Var("zz_spec_fresh_r", specTestFun2())
	stmt := prop.MakeProp(ext.ForAll(m, n)(specTestMatrix(
		q.Apply(m, n), r.Apply(m, n), m, n)).Core())

	consts, characterizing, err := MintSpecDefinition(env, stmt,
		[]core.VarTerm{q.Core().(core.VarTerm), r.Core().(core.VarTerm)})
	require.NoError(t, err)
	require.Len(t, consts, 2)

	sd, err := AnalyzeSpecGoal(characterizing, consts)
	require.NoError(t, err)

	obligation := specTestObligation(t)
	derived, err := CompileSpecExistence(nil, sd, obligation)
	require.NoError(t, err)
	out := prop.BridgeNormalize(characterizing, derived)
	require.NotNil(t, out)
	require.True(t, out.Proved() || core.IsPromised(out))
}

// TestDefineSpecStep_Composite runs the ministep end-to-end on a
// Script section: the obligation surfaces as the one child, closes by
// witness actions, and the reconstruct lands the characterizing goal.
func TestDefineSpecStep_Composite(t *testing.T) {
	c1, c2 := mintTaggedSpecTwins(t, "zz_spec_st1", "zz_spec_st2")
	m := Var("m", ext.NumType)
	n := Var("n", ext.NumType)
	goal := prop.MakeProp(ext.ForAll(m, n)(specTestMatrix(
		ext.WrapTerm(c1).Apply(m, n), ext.WrapTerm(c2).Apply(m, n), m, n)).Core())

	sd, err := AnalyzeSpecGoal(goal, []core.ConstTerm{c1, c2})
	require.NoError(t, err)

	step := DefineSpecStep([]core.Term{c1, c2}).(_DefineSpecStep)
	sub := step.apply(goal)
	require.NotNil(t, sub, "the composite must apply to the characterizing goal")
	require.Equal(t, 1, sub.Size(), "one obligation child")
	require.True(t, sub.ChildGoal(0).Conclusion().AlphaEquals(sd.Obligation.Conclusion()),
		"child = %s\nwant %s", prop.PrintProp(sub.ChildGoal(0)),
		prop.PrintProp(sd.Obligation))

	closed := sub.Reconstruct(specTestObligation(t))
	require.NotNil(t, closed)
	require.True(t, closed.Conclusion().AlphaEquals(goal.Conclusion()))
}
