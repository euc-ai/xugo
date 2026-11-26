package proof

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/stretchr/testify/require"
)

// registerEquivalenceVocab mints the relations chapter's four
// predicates into a test env with the chapter's own definitions —
// what the quotient spine unfolds — so the package test needs no
// corpus.
func registerEquivalenceVocab(t *testing.T, env *ProverEnv) {
	t.Helper()
	A := TypeA
	relT := MakeFun(A, MakeFun(A, TypeBool))
	R := Var("R", relT).Core().(VarTerm)
	x := Var("x", A).Core().(VarTerm)
	y := Var("y", A).Core().(VarTerm)
	z := Var("z", A).Core().(VarTerm)
	rel := func(a, b Term) Term { return Apply(R, a, b).Core() }
	mint := func(name string, body Term) ConstTerm {
		if meta, ok := env.ProofService.LoadConstMeta(TermName(name)); ok {
			return MakeConstTerm(meta, meta.AbsType())
		}
		c := core.NewConstDef(body, TermName(name))
		env.ProofService.LoadOrStoreConstMeta(c.Meta())
		return c
	}
	reflexive := mint(reflexiveConstName, Abs(R, ForAll(x)(rel(x, x)).Core()))
	symmetric := mint(symmetricConstName, Abs(R, ForAll(x, y)(WrapTerm(rel(x, y)).Imply(rel(y, x))).Core()))
	transitive := mint(transitiveConstName, Abs(R, ForAll(x, y, z)(WrapTerm(WrapTerm(rel(x, y)).And(rel(y, z))).Imply(rel(x, z))).Core()))
	conj := WrapTerm(Apply(reflexive, R)).And(Apply(symmetric, R)).And(Apply(transitive, R))
	mint(EquivalenceConstName, Abs(R, conj.Core()))
}

// quotientTestEnv is a mock env with the equivalence vocabulary and the
// quotient of num by equality minted: the mechanics exercised at the
// simplest relation, the laws' input a trusted test theorem.
func quotientTestEnv(t *testing.T) (*ProverEnv, *MintedQuotient, Prop) {
	t.Helper()
	env := &ProverEnv{ProofService: MockConstMetaService(), LibraryThms: map[string]Thm{}}
	registerEquivalenceVocab(t, env)
	x := Var("x", NumType).Core().(VarTerm)
	y := Var("y", NumType).Core().(VarTerm)
	rel := core.NewConstDef(Abs(x, Abs(y, ext.Eq(x, y))), "zz_qeq")
	env.ProofService.LoadOrStoreConstMeta(rel.Meta())
	qd, err := AnalyzeQuotientDefinition(rel, envConstMetaResolver(env))
	require.NoError(t, err)
	require.True(t, qd.Typedef.Trivial, "the class shape is inhabited by normalization")
	mq, err := MintQuotientDefinition(env, qd, "zz_qnum", "zz_qnum_abs", "zz_qnum_rep", "zz_qnum_class")
	require.NoError(t, err)
	equivalence := core.TestThm(qd.Equivalence.Conclusion())
	return env, mq, equivalence
}

func TestQuotient_StatementsAndNames(t *testing.T) {
	_, mq, _ := quotientTestEnv(t)
	require.Equal(t, "zz_qnum", mq.TypeText())
	require.Equal(t, "zz_qnum_induction", mq.PrincipleName(QuotientInduct))
	require.Equal(t, "zz_qnum_sound", mq.PrincipleName(QuotientSound))
	require.Equal(t, "zz_qnum_exact", mq.PrincipleName(QuotientExact))
	require.Equal(t, "", mq.PrincipleName(QuotientEq))
	require.Equal(t, "∀q.∃x.(q = zz_qnum_class(x))", PrintTerm(mq.Stmt(QuotientSurjectivity).Conclusion()))
	require.Equal(t, "∀x.∀y.((zz_qnum_class(x) = zz_qnum_class(y)) ⇔ zz_qeq(x, y))", PrintTerm(mq.Stmt(QuotientEq).Conclusion()))
	for _, k := range QuotientTheoremKinds {
		kind, ok := mq.KindOf(mq.Stmt(k))
		require.True(t, ok)
		require.Equal(t, k, kind)
	}

	// The induction principle is in the standard form the analyzer
	// reads: one case, the class map as its constructor, no inductive
	// hypothesis.
	tmpl, err := tactic.AnalyzeInductionPrinciple(mq.Stmt(QuotientInduct))
	require.NoError(t, err)
	require.Len(t, tmpl.Cases, 1)
	require.Empty(t, tmpl.Cases[0].RecArgIndices)
	require.Equal(t, "zz_qnum_class(x)", PrintTerm(tmpl.Cases[0].Constructor))
}

func TestQuotient_DeriveAllKinds(t *testing.T) {
	_, mq, equivalence := quotientTestEnv(t)
	for _, k := range QuotientTheoremKinds {
		thm := mq.Derive(k, equivalence)
		require.True(t, thm.Proved(), "%v derives to a proved theorem", k)
		cert := core.Force(context.Background(), core.AsThm(thm))
		require.True(t, cert.AlphaEquals(mq.Stmt(k)), "%v proves its statement:\n  %s", k, PrintProp(cert))
	}
	require.Panics(t, func() { mq.Derive(QuotientEq, core.TestThm(T)) }, "a wrong equivalence input is refused")
}

func TestQuotient_Recover(t *testing.T) {
	env, mq, _ := quotientTestEnv(t)
	require.True(t, IsQuotientClassMap(mq.Mk))
	require.False(t, IsQuotientClassMap(mq.Abs), "the typedef abs is not the class map")
	back, err := RecoverMintedQuotient(mq.Mk, envConstMetaResolver(env))
	require.NoError(t, err)
	require.True(t, back.Def.Rel.AlphaEquals(mq.Def.Rel))
	require.Equal(t, mq.Meta.Name(), back.Meta.Name())
	for _, k := range QuotientTheoremKinds {
		require.True(t, back.Stmt(k).AlphaEquals(mq.Stmt(k)), "%v recovers", k)
	}
}

func TestQuotient_Refusals(t *testing.T) {
	env := &ProverEnv{ProofService: MockConstMetaService(), LibraryThms: map[string]Thm{}}
	x := Var("x", NumType).Core().(VarTerm)
	y := Var("y", NumType).Core().(VarTerm)
	n := Var("n", NumType).Core().(VarTerm)
	resolve := envConstMetaResolver(env)

	_, err := AnalyzeQuotientDefinition(Abs(x, Abs(y, ext.Eq(x, n))), resolve)
	require.ErrorContains(t, err, "closed")

	_, err = AnalyzeQuotientDefinition(Abs(x, Abs(y, ext.Eq(x, y))), resolve)
	require.ErrorContains(t, err, "define it as a constant", "a bare λ is refused")

	unary := core.NewConstDef(Abs(x, ext.Eq(x, x)), "zz_qunary")
	env.ProofService.LoadOrStoreConstMeta(unary.Meta())
	_, err = AnalyzeQuotientDefinition(unary, resolve)
	require.ErrorContains(t, err, "binary relation")

	rel := core.NewConstDef(Abs(x, Abs(y, ext.Eq(x, y))), "zz_qeq2")
	env.ProofService.LoadOrStoreConstMeta(rel.Meta())
	_, err = AnalyzeQuotientDefinition(rel, resolve)
	require.ErrorContains(t, err, "relations/equivalence", "the equivalence predicate must be registered")
}

// TestDefineQuotientStep_AllKinds runs the composite executor over each
// derived-theorem section goal — the record/emit/replay shared path —
// closing the equivalence child by a cite.
func TestDefineQuotientStep_AllKinds(t *testing.T) {
	env, mq, equivalence := quotientTestEnv(t)
	for _, k := range QuotientTheoremKinds {
		stmt := mq.Stmt(k)
		node := CreateGoalStack(stmt)
		require.True(t, ApplyDefineQuotientStep(node, env, mq.Mk), "composite must apply to the %v section", k)
		leaves := node.UnsolvedLeaves()
		require.Len(t, leaves, 1, "%v: the one child is the equivalence", k)
		require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(mq.Def.Equivalence.Conclusion()))
		require.True(t, ApplyCiteKnown(leaves[0], equivalence))
		require.True(t, node.Proved(), "%v section proved", k)
		cert := core.Force(context.Background(), core.AsThm(node.PromisedThm()))
		require.True(t, cert.AlphaEquals(stmt), "%v's forced certificate proves the statement", k)
	}

	// A goal that is none of the seven fails the apply, agent-visibly.
	bogus := CreateGoalStack(core.MakeProp(T))
	require.False(t, ApplyDefineQuotientStep(bogus, env, mq.Mk))
}

// TestParseQuotientRelation_ReadsLettersBack: a polymorphic relation
// spelled bare reads at its constant's own letters — the parameters of
// a quotient over a polymorphic carrier are the carrier's letters
// (free_group(A)), never the parser's occurrence-local stand-ins.
func TestParseQuotientRelation_ReadsLettersBack(t *testing.T) {
	A := core.MakeVarType("A")
	relT := MakeFun(ext.MakeType("list", A), MakeFun(ext.MakeType("list", A), TypeBool))
	rel := MakeConstTerm(MakeConstMeta("zz_prel", relT), relT)
	base := &dsl.ParseScope{ConstMetas: map[string]ConstTermMeta{"zz_prel": rel.Meta()}}
	parsed, err := ParseQuotientRelation("zz_prel", base)
	require.NoError(t, err)
	require.True(t, parsed.Type().Equals(relT), "read at the constant's own letter: %s", ext.FormatType(parsed.Type()))
	env := &ProverEnv{ProofService: MockConstMetaService(), LibraryThms: map[string]Thm{}}
	registerEquivalenceVocab(t, env)
	qd, err := AnalyzeQuotientDefinition(parsed, envConstMetaResolver(env))
	require.NoError(t, err)
	require.Equal(t, "A", string(qd.Rho.TypeVars()[0].Name()))
}
