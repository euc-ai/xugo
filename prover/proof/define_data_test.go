package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/stretchr/testify/require"
)

// registerRecspaceVocab registers the recspace-layer const metas the
// kit's encodings need into a (fresh, test-local) ProofService. Types
// are at their usual polymorphic letters.
func registerRecspaceVocab(t *testing.T, env *ProverEnv) {
	t.Helper()
	A := MakeVarType("A")
	recA := MakeCompositeType(MakeMetaType("recspace", 1), A)
	numToRecA := MakeFun(NumType, recA)
	for _, meta := range []ConstTermMeta{
		MakeConstMeta("recspace_node",
			MakeFun(NumType, MakeFun(A, MakeFun(numToRecA, recA)))),
		MakeConstMeta("recspace_bottom", recA),
		MakeConstMeta("family_cons",
			MakeFun(A, MakeFun(MakeFun(NumType, A),
				MakeFun(NumType, A)))),
		MakeConstMeta("family_nil", MakeFun(NumType, A)),
		MakeConstMeta("suc", MakeFun(NumType, NumType)),
		ext.ZeroMeta,
	} {
		if _, ok := env.ProofService.LoadConstMeta(meta.Name()); !ok {
			env.ProofService.LoadOrStoreConstMeta(meta)
		}
	}
}

// analyzeBtree is the shared btree(A) fixture: bleaf(A) | bnode(btree,
// btree) — transcript B's datatype.
func analyzeBtree(t *testing.T, env *ProverEnv) *DataDefinition {
	t.Helper()
	lookup := func(name TermName) ConstTermMeta {
		if meta, ok := env.ProofService.LoadConstMeta(name); ok {
			return meta
		}
		return ConstTermMeta{}
	}
	dd, err := AnalyzeDataDefinition("btree", []string{"A"}, []DataConstructorSpec{
		{Name: "bleaf", Args: []string{"A"}},
		{Name: "bnode", Args: []string{"btree(A)", "btree(A)"}},
	}, lookup, nil)
	require.NoError(t, err)
	return dd
}

func TestAnalyzeDataDefinition_Shapes(t *testing.T) {
	env := &ProverEnv{ProofService: MockConstMetaService()}
	registerRecspaceVocab(t, env)
	dd := analyzeBtree(t, env)
	require.Equal(t, TypeName("btree"), dd.TypeName)
	require.Len(t, dd.PayloadSlots, 1, "one external type: A")
	require.Equal(t, []bool{false}, dd.Ctors[0].IsRec)
	require.Equal(t, []bool{true, true}, dd.Ctors[1].IsRec)
	require.Equal(t, []int{0}, dd.Ctors[0].PayloadSlot)
	require.Equal(t, []int{-1, -1}, dd.Ctors[1].PayloadSlot)

	// Repair-naming rejections.
	lookup := func(name TermName) ConstTermMeta {
		if meta, ok := env.ProofService.LoadConstMeta(name); ok {
			return meta
		}
		return ConstTermMeta{}
	}
	_, err := AnalyzeDataDefinition("stream", []string{"A"}, []DataConstructorSpec{
		{Name: "scons", Args: []string{"A", "stream(A)"}},
	}, lookup, nil)
	require.ErrorContains(t, err, "base constructor")

	_, err = AnalyzeDataDefinition("rosetree", []string{"A"}, []DataConstructorSpec{
		{Name: "rnode", Args: []string{"list(rosetree(A))"}},
	}, lookup, nil)
	require.ErrorContains(t, err, "nested")

	_, err = AnalyzeDataDefinition("pair2", []string{"B", "A"}, []DataConstructorSpec{
		{Name: "p2", Args: []string{"A", "B"}},
	}, lookup, nil)
	require.ErrorContains(t, err, "ascending")

	_, err = AnalyzeDataDefinition("phantomty", []string{"A", "B"}, []DataConstructorSpec{
		{Name: "ph", Args: []string{"A"}},
	}, lookup, nil)
	require.ErrorContains(t, err, "not used")

	_, err = AnalyzeDataDefinition("leaky", []string{"A"}, []DataConstructorSpec{
		{Name: "lk", Args: []string{"B"}},
	}, lookup, nil)
	require.ErrorContains(t, err, "not a declared param")
}

func TestMintDataDefinition_BtreeInduct(t *testing.T) {
	env := &ProverEnv{ProofService: MockConstMetaService()}
	registerRecspaceVocab(t, env)
	dd := analyzeBtree(t, env)

	md, err := MintDataDefinition(env, dd)
	require.NoError(t, err)
	require.Equal(t, TermName("mk_btree"), md.Mk.Name())
	require.Len(t, md.Ctors, 2)

	// The statements print sanely.
	t.Logf("INDUCT:    %s", PrintProp(md.InductStmt()))
	t.Logf("RECURSION: %s", PrintProp(md.RecursionStmt()))
	t.Logf("INJ:       %s", PrintProp(md.InjStmt()))
	t.Logf("DISTINCT:  %s", PrintProp(md.DistinctStmt()))

	// The INDUCT statement parses into an induction template —
	// transcript B5's dispatch shape.
	tmpl, err := tactic.AnalyzeInductionPrinciple(md.InductStmt())
	require.NoError(t, err)
	require.Len(t, tmpl.Cases, 2)
	require.Empty(t, tmpl.Cases[0].RecArgIndices)
	require.Equal(t, []int{0, 1}, tmpl.Cases[1].RecArgIndices)

	// And the RECURSION statement into a recursion template (the
	// equation compiler's dispatch shape for B2/B3).
	rt, err := tactic.AnalyzeRecursionPrinciple(md.RecursionStmt())
	require.NoError(t, err)
	require.Len(t, rt.Cases, 2)
	require.False(t, rt.Unique)
	require.Len(t, rt.OuterParams, 2)

	// INDUCT derives, env-free, and lands exactly on the statement.
	induct, err := DeriveDataInduct(env, md)
	require.NoError(t, err)
	require.True(t, core.AsThm(induct).Proved(), "induction derivation must be a real theorem")
	require.True(t, induct.AlphaEquals(md.InductStmt()))

	// The recovery round-trip: the composite's replay entry rebuilds
	// the same datatype from the minted consts alone.
	recovered, err := RecoverMintedDatatype(md.Mk, md.Ctors)
	require.NoError(t, err)
	require.True(t, recovered.InductStmt().AlphaEquals(md.InductStmt()))
	require.True(t, recovered.RecursionStmt().AlphaEquals(md.RecursionStmt()))
	require.True(t, recovered.InjStmt().AlphaEquals(md.InjStmt()))
	require.True(t, recovered.DistinctStmt().AlphaEquals(md.DistinctStmt()))

	// Second mint of the same names refuses (exclusive registration).
	_, err = MintDataDefinition(env, dd)
	require.ErrorContains(t, err, "already registered")
}

// installTestRecspaceRows binds test-trust versions of the recspace
// corpus rows into env.LibraryThms, in the corpus's own statement
// arrangements (kit-correctness tests only; the engine battery runs
// against the real corpus rows).
func installTestRecspaceRows(t *testing.T, env *ProverEnv) {
	t.Helper()
	A, B, Z := MakeVarType("A"), MakeVarType("B"), MakeVarType("Z")
	recA := MakeCompositeType(MakeMetaType("recspace", 1), A)
	numT := NumType
	numToRecA := MakeFun(numT, recA)

	meta := func(name string) ConstTermMeta {
		m, ok := env.ProofService.LoadConstMeta(TermName(name))
		require.True(t, ok, "test vocab %s", name)
		return m
	}
	constr := meta("recspace_node").Term()
	if constr.IsZero() {
		constr = MakeConstTerm(meta("recspace_node"), meta("recspace_node").AbsType())
	}
	suc := MakeConstTerm(meta("suc"), meta("suc").AbsType())
	zero := MakeConstTerm(meta("_0"), meta("_0").AbsType())
	fcons := MakeConstTerm(meta("family_cons"), meta("family_cons").AbsType())

	// recspace_recursion: ⊢ ∃f. ∀c i r. f(recspace_node(c,i,r)) = Fn(c,i,r,λn.f(r n)), Fn free.
	fVar := Var("f", MakeFun(recA, Z)).Core().(VarTerm)
	FnVar := Var("Fn", MakeFun(numT, MakeFun(A, MakeFun(numToRecA,
		MakeFun(MakeFun(numT, Z), Z))))).Core().(VarTerm)
	cV := Var("c", numT).Core().(VarTerm)
	iV := Var("i", A).Core().(VarTerm)
	rV := Var("r", numToRecA).Core().(VarTerm)
	nV := Var("n", numT).Core().(VarTerm)
	recBody := WrapTerm(Apply(fVar, Apply(constr, cV, iV, rV).Core()).Core()).
		Eq(Apply(FnVar, cV, iV, rV,
			Abs(nV, Apply(fVar, Apply(rV, nV).Core()).Core())).Core()).Core()
	constrRec := Exists(fVar)(
		ForAll(cV)(ForAll(iV)(ForAll(rV)(recBody)))).Core()
	env.LibraryThms["recspace_recursion"] = core.TestThm(constrRec)

	// recspace_node_injective: (recspace_node(c1,i1,r1) = recspace_node(c2,i2,r2)) ⇔ (c1=c2 ∧ (i1=i2 ∧ r1=r2)).
	c1 := Var("c1", numT).Core().(VarTerm)
	i1 := Var("i1", A).Core().(VarTerm)
	r1 := Var("r1", numToRecA).Core().(VarTerm)
	c2 := Var("c2", numT).Core().(VarTerm)
	i2 := Var("i2", A).Core().(VarTerm)
	r2 := Var("r2", numToRecA).Core().(VarTerm)
	constrInj := WrapTerm(
		WrapTerm(Apply(constr, c1, i1, r1).Core()).
			Eq(Apply(constr, c2, i2, r2).Core()).Core()).
		Eq(WrapTerm(WrapTerm(Term(c1)).Eq(c2).Core()).
			And(WrapTerm(WrapTerm(Term(i1)).Eq(i2).Core()).
				And(WrapTerm(Term(r1)).Eq(r2).Core()).Core()).Core()).Core()
	env.LibraryThms["recspace_node_injective"] = core.TestThm(constrInj)

	// family_cons: (∀a f. family_cons(a,f,0) = a) ∧ (∀a f n. family_cons(a,f,suc n) = f(n)).
	aV := Var("a", A).Core().(VarTerm)
	fV2 := Var("f", MakeFun(numT, A)).Core().(VarTerm)
	fc1 := ForAll(aV)(ForAll(fV2)(
		WrapTerm(Apply(fcons, aV, fV2, zero).Core()).Eq(aV))).Core()
	fc2 := ForAll(aV)(ForAll(fV2)(ForAll(nV)(
		WrapTerm(Apply(fcons, aV, fV2, Apply(suc, nV).Core()).Core()).
			Eq(Apply(fV2, nV).Core())))).Core()
	env.LibraryThms["family_cons_definition"] = core.TestThm(WrapTerm(fc1).And(fc2).Core())

	// suc_not_zero / suc_injective in the corpus's SERVED arrangements
	// (∀-closed; suc_injective with the bare equation on the LEFT).
	env.LibraryThms["suc_not_zero"] = core.TestThm(ForAll(nV)(
		Not(WrapTerm(Term(zero)).Eq(Apply(suc, nV).Core()).Core())).Core())
	mV := Var("m", numT).Core().(VarTerm)
	env.LibraryThms["suc_injective"] = core.TestThm(ForAll(nV)(ForAll(mV)(
		WrapTerm(WrapTerm(Term(nV)).Eq(mV).Core()).
			Eq(WrapTerm(Apply(suc, nV).Core()).
				Eq(Apply(suc, mV).Core()).Core()))).Core())

	// pair_injective / fst / snd at (A, B).
	comma := MakeConstTerm(ext.CommaConstMeta,
		MakeFun(A, MakeFun(B, MakeProdType(A, B))))
	xV := Var("x", A).Core().(VarTerm)
	yV := Var("y", B).Core().(VarTerm)
	aV2 := Var("a", A).Core().(VarTerm)
	bV2 := Var("b", B).Core().(VarTerm)
	pairEq := ForAll(bV2)(ForAll(yV)(ForAll(aV2)(ForAll(xV)(
		WrapTerm(
			WrapTerm(Apply(comma, aV2, bV2).Core()).
				Eq(Apply(comma, xV, yV).Core()).Core()).
			Eq(WrapTerm(WrapTerm(Term(aV2)).Eq(xV).Core()).
				And(WrapTerm(Term(bV2)).Eq(yV).Core()).Core()))))).Core()
	env.LibraryThms["pair_injective"] = core.TestThm(pairEq)
	fstC := MakeConstTerm(MakeConstMeta("fst",
		MakeFun(MakeProdType(TypeA, B), TypeA)),
		MakeFun(MakeProdType(A, B), A))
	sndC := MakeConstTerm(MakeConstMeta("snd",
		MakeFun(MakeProdType(TypeA, B), B)),
		MakeFun(MakeProdType(A, B), B))
	env.LibraryThms["fst_of_pair"] = core.TestThm(ForAll(yV)(ForAll(xV)(
		WrapTerm(Term(xV)).
			Eq(Apply(fstC, Apply(comma, xV, yV).Core()).Core()))).Core())
	env.LibraryThms["snd_of_pair"] = core.TestThm(ForAll(yV)(ForAll(xV)(
		WrapTerm(Term(yV)).
			Eq(Apply(sndC, Apply(comma, xV, yV).Core()).Core()))).Core())
}

func TestDeriveDataRecursion_Btree(t *testing.T) {
	env := &ProverEnv{
		ProofService: MockConstMetaService(),
		LibraryThms:  map[string]Thm{},
	}
	registerRecspaceVocab(t, env)
	installTestRecspaceRows(t, env)
	dd := analyzeBtree(t, env)
	md, err := MintDataDefinition(env, dd)
	require.NoError(t, err)

	rec, err := DeriveDataRecursion(env, md)
	require.NoError(t, err)
	require.True(t, rec.AlphaEquals(md.RecursionStmt()))
	require.True(t, core.AsThm(rec).Proved())
}

func TestDeriveDataInjDistinct_Btree(t *testing.T) {
	env := &ProverEnv{
		ProofService: MockConstMetaService(),
		LibraryThms:  map[string]Thm{},
	}
	registerRecspaceVocab(t, env)
	installTestRecspaceRows(t, env)
	dd := analyzeBtree(t, env)
	md, err := MintDataDefinition(env, dd)
	require.NoError(t, err)

	inj, err := DeriveDataInj(env, md)
	require.NoError(t, err)
	require.True(t, inj.AlphaEquals(md.InjStmt()))

	distinct, err := DeriveDataDistinct(env, md)
	require.NoError(t, err)
	require.True(t, distinct.AlphaEquals(md.DistinctStmt()))
}

// TestDeriveData_MixedShape stresses the general encoding: three
// constructors (suc_injective chains in DISTINCT), multi-slot payload with a
// repeated external type (pair_injective/fst/snd chains, ε-filled unused
// slots), and a constructor mixing external and recursive arguments.
func TestDeriveData_MixedShape(t *testing.T) {
	env := &ProverEnv{
		ProofService: MockConstMetaService(),
		LibraryThms:  map[string]Thm{},
	}
	registerRecspaceVocab(t, env)
	installTestRecspaceRows(t, env)
	lookup := func(name TermName) ConstTermMeta {
		if meta, ok := env.ProofService.LoadConstMeta(name); ok {
			return meta
		}
		return ConstTermMeta{}
	}
	dd, err := AnalyzeDataDefinition("zmix", []string{"A"}, []DataConstructorSpec{
		{Name: "znil", Args: nil},
		{Name: "zpair", Args: []string{"A", "num", "A"}},
		{Name: "zmixc", Args: []string{"A", "zmix(A)", "num", "zmix(A)"}},
	}, lookup, nil)
	require.NoError(t, err)
	require.Len(t, dd.PayloadSlots, 3, "payload slots: A, num, A")
	require.Equal(t, []int{0, 1, 2}, dd.Ctors[1].PayloadSlot)
	require.Equal(t, []int{0, -1, 1, -1}, dd.Ctors[2].PayloadSlot)

	md, err := MintDataDefinition(env, dd)
	require.NoError(t, err)
	t.Logf("INDUCT:    %s", PrintProp(md.InductStmt()))
	t.Logf("RECURSION: %s", PrintProp(md.RecursionStmt()))

	induct, err := DeriveDataInduct(env, md)
	require.NoError(t, err)
	require.True(t, induct.AlphaEquals(md.InductStmt()))

	rec, err := DeriveDataRecursion(env, md)
	require.NoError(t, err)
	require.True(t, rec.AlphaEquals(md.RecursionStmt()))

	inj, err := DeriveDataInj(env, md)
	require.NoError(t, err)
	require.True(t, inj.AlphaEquals(md.InjStmt()))

	distinct, err := DeriveDataDistinct(env, md)
	require.NoError(t, err)
	require.True(t, distinct.AlphaEquals(md.DistinctStmt()))
}

// TestDeriveData_EnumShape: a parameterless enumeration — bool payload,
// no INJ clauses for the nullary constructors, three DISTINCT pairs.
func TestDeriveData_EnumShape(t *testing.T) {
	env := &ProverEnv{
		ProofService: MockConstMetaService(),
		LibraryThms:  map[string]Thm{},
	}
	registerRecspaceVocab(t, env)
	installTestRecspaceRows(t, env)
	lookup := func(name TermName) ConstTermMeta {
		if meta, ok := env.ProofService.LoadConstMeta(name); ok {
			return meta
		}
		return ConstTermMeta{}
	}
	dd, err := AnalyzeDataDefinition("zenum", nil, []DataConstructorSpec{
		{Name: "zred", Args: nil},
		{Name: "zgreen", Args: nil},
		{Name: "zblue", Args: nil},
	}, lookup, nil)
	require.NoError(t, err)
	require.Empty(t, dd.PayloadSlots)

	md, err := MintDataDefinition(env, dd)
	require.NoError(t, err)
	require.Nil(t, md.InjStmt(), "no argumented constructor — no INJ")
	require.Equal(t,
		[]DataTheoremKind{DataInduct, DataRecursion, DataDistinct}, md.Kinds())

	induct, err := DeriveDataInduct(env, md)
	require.NoError(t, err)
	require.True(t, induct.AlphaEquals(md.InductStmt()))

	rec, err := DeriveDataRecursion(env, md)
	require.NoError(t, err)
	require.True(t, rec.AlphaEquals(md.RecursionStmt()))

	distinct, err := DeriveDataDistinct(env, md)
	require.NoError(t, err)
	require.True(t, distinct.AlphaEquals(md.DistinctStmt()))
}

// TestDefineDataStep_AllKinds runs the composite executor over each
// derived-theorem section goal — the record/emit/replay shared path.
func TestDefineDataStep_AllKinds(t *testing.T) {
	env := &ProverEnv{
		ProofService: MockConstMetaService(),
		LibraryThms:  map[string]Thm{},
	}
	registerRecspaceVocab(t, env)
	installTestRecspaceRows(t, env)
	dd := analyzeBtree(t, env)
	md, err := MintDataDefinition(env, dd)
	require.NoError(t, err)

	ctorTerms := make([]Term, len(md.Ctors))
	for i, c := range md.Ctors {
		ctorTerms[i] = c
	}
	for _, k := range md.Kinds() {
		stmt := md.Stmt(k)
		node := CreateGoalStack(stmt)
		require.True(t, ApplyDefineDataStep(node, env, md.Mk, ctorTerms),
			"composite must close the %v section", k)
		require.True(t, node.Proved(), "%v section proved", k)
	}

	// A goal that is none of the four fails the apply, agent-visibly.
	bogus := CreateGoalStack(core.MakeProp(T))
	require.False(t, ApplyDefineDataStep(bogus, env, md.Mk, ctorTerms))
}

// TestDeriveData_WrapperShape: a single-constructor datatype — no
// DISTINCT theorem, one-disjunct rule closure, INJ over the lone
// constructor.
func TestDeriveData_WrapperShape(t *testing.T) {
	env := &ProverEnv{
		ProofService: MockConstMetaService(),
		LibraryThms:  map[string]Thm{},
	}
	registerRecspaceVocab(t, env)
	installTestRecspaceRows(t, env)
	lookup := func(name TermName) ConstTermMeta {
		if meta, ok := env.ProofService.LoadConstMeta(name); ok {
			return meta
		}
		return ConstTermMeta{}
	}
	dd, err := AnalyzeDataDefinition("zwrap", []string{"A"}, []DataConstructorSpec{
		{Name: "zw", Args: []string{"A"}},
	}, lookup, nil)
	require.NoError(t, err)
	md, err := MintDataDefinition(env, dd)
	require.NoError(t, err)
	require.Nil(t, md.DistinctStmt())
	require.Equal(t, []DataTheoremKind{DataInduct, DataRecursion, DataInj}, md.Kinds())

	for _, k := range md.Kinds() {
		derived, derr := DeriveDataTheorem(env, md, k)
		require.NoError(t, derr, "%v derives", k)
		require.True(t, derived.AlphaEquals(md.Stmt(k)), "%v lands on its statement", k)
	}
}
