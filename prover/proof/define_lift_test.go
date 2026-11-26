package proof

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// liftTestEnv is the quotient test env with the quotient's Sound and
// Exact served under their conventional names, as the quotient door
// binds them.
func liftTestEnv(t *testing.T) (*ProverEnv, *MintedQuotient) {
	t.Helper()
	env, mq, equivalence := quotientTestEnv(t)
	for _, k := range []QuotientTheoremKind{QuotientSound, QuotientExact} {
		require.NoError(t, env.InstallLibraryThm(mq.PrincipleName(k), core.AsThm(mq.Derive(k, equivalence))))
	}
	return env, mq
}

func TestLift_AnalyzeAndObligation(t *testing.T) {
	env, mq := liftTestEnv(t)
	resolve := envConstMetaResolver(env)
	a := Var("a", NumType).Core().(VarTerm)
	b := Var("b", NumType).Core().(VarTerm)
	n := Var("n", NumType).Core().(VarTerm)
	Q := mq.QType

	// A class-valued binary operation: the first argument's class.
	first := Var("zz_qfirst", MakeFun(Q, MakeFun(Q, Q))).Core().(VarTerm)
	firstEq := core.MakeProp(ForAll(a, b)(ext.Eq(Apply(first, mq.class(a), mq.class(b)), mq.class(a))).Core())
	require.True(t, IsQuotientLiftEquation(firstEq, first))
	ld, err := AnalyzeLiftDefinition([]Prop{firstEq}, first, resolve)
	require.NoError(t, err)
	require.Len(t, ld.Args, 2)
	require.NotNil(t, ld.Args[0].Quotient)
	require.NotNil(t, ld.Codomain)
	require.Equal(t, "∀a.∀a'.∀b.∀b'.((zz_qeq(a, a') ∧ zz_qeq(b, b')) ⇒ zz_qeq(a, a'))", PrintTerm(ld.Obligation.Conclusion()))

	// A relation with an external argument beside the class.
	mem := Var("zz_qmem", MakeFun(NumType, MakeFun(Q, TypeBool))).Core().(VarTerm)
	memEq := core.MakeProp(ForAll(n, a)(ext.Eq(Apply(mem, n, mq.class(a)), ext.Eq(n, a))).Core())
	ld2, err := AnalyzeLiftDefinition([]Prop{memEq}, mem, resolve)
	require.NoError(t, err)
	require.Nil(t, ld2.Codomain)
	require.Nil(t, ld2.Args[0].Quotient)
	require.Equal(t, "∀n.∀a.∀a'.(zz_qeq(a, a') ⇒ ((n = a) ⇔ (n = a')))", PrintTerm(ld2.Obligation.Conclusion()))

	// Refusals name the repair.
	plain := Var("zz_qplain", MakeFun(NumType, NumType)).Core().(VarTerm)
	plainEq := core.MakeProp(ForAll(a)(ext.Eq(Apply(plain, a), a)).Core())
	require.False(t, IsQuotientLiftEquation(plainEq, plain))
	_, err = AnalyzeLiftDefinition([]Prop{plainEq}, plain, resolve)
	require.ErrorContains(t, err, "no argument is a class pattern")

	recur := Var("zz_qrecur", MakeFun(Q, Q)).Core().(VarTerm)
	recurEq := core.MakeProp(ForAll(a)(ext.Eq(Apply(recur, mq.class(a)), Apply(recur, mq.class(a)))).Core())
	_, err = AnalyzeLiftDefinition([]Prop{recurEq}, recur, resolve)
	require.ErrorContains(t, err, "recurs")

	unbound := Var("zz_qunbound", MakeFun(Q, Q)).Core().(VarTerm)
	unboundEq := core.MakeProp(ForAll(a)(ext.Eq(Apply(unbound, mq.class(n)), mq.class(a))).Core())
	_, err = AnalyzeLiftDefinition([]Prop{unboundEq}, unbound, resolve)
	require.ErrorContains(t, err, "not ∀-bound")
}

// TestLift_DefineStep runs the define composite on lifts: the one child
// is the respectfulness, and the closed obligation compiles to the
// characterizing theorem by kernel rules.
func TestLift_DefineStep(t *testing.T) {
	env, mq := liftTestEnv(t)
	resolve := envConstMetaResolver(env)
	a := Var("a", NumType).Core().(VarTerm)
	b := Var("b", NumType).Core().(VarTerm)
	n := Var("n", NumType).Core().(VarTerm)
	Q := mq.QType

	run := func(name string, defVar VarTerm, equation Prop) {
		t.Helper()
		ld, err := AnalyzeLiftDefinition([]Prop{equation}, defVar, resolve)
		require.NoError(t, err, name)
		c, characterizing, err := MintLiftDefinition(env, ld)
		require.NoError(t, err, name)
		require.True(t, IsQuotientLiftConst(c, resolve), name)
		node := CreateGoalStack(characterizing)
		require.True(t, ApplyDefineStep(node, env, c), "%s: the composite applies", name)
		leaves := node.UnsolvedLeaves()
		require.Len(t, leaves, 1, "%s: one child, the respectfulness", name)
		require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(ld.Obligation.Conclusion()), name)
		require.True(t, ApplyCiteKnown(leaves[0], core.TestThm(ld.Obligation.Conclusion())), name)
		require.True(t, node.Proved(), name)
		cert := core.Force(context.Background(), core.AsThm(node.PromisedThm()))
		require.True(t, cert.AlphaEquals(characterizing), "%s: the forced certificate proves the stated rule:\n  %s", name, PrintProp(cert))
	}

	first := Var("zz_qfirst", MakeFun(Q, MakeFun(Q, Q))).Core().(VarTerm)
	run("first", first, core.MakeProp(ForAll(a, b)(ext.Eq(Apply(first, mq.class(a), mq.class(b)), mq.class(a))).Core()))

	mem := Var("zz_qmem", MakeFun(NumType, MakeFun(Q, TypeBool))).Core().(VarTerm)
	run("mem", mem, core.MakeProp(ForAll(n, a)(ext.Eq(Apply(mem, n, mq.class(a)), ext.Eq(n, a))).Core()))

	same := Var("zz_qsame", MakeFun(Q, Q)).Core().(VarTerm)
	run("same", same, core.MakeProp(ForAll(a)(ext.Eq(Apply(same, mq.class(a)), mq.class(a))).Core()))

	// Without the quotient's laws served, the compile fails by name.
	bare := &ProverEnv{ProofService: env.ProofService, LibraryThms: map[string]Thm{}}
	ld, err := AnalyzeLiftDefinition([]Prop{core.MakeProp(ForAll(a)(ext.Eq(Apply(same, mq.class(a)), mq.class(a))).Core())}, same, resolve)
	require.NoError(t, err)
	_, err = CompileLiftExistence(bare, ld, core.TestThm(ld.Obligation.Conclusion()))
	require.ErrorContains(t, err, "zz_qnum_exact")
}
