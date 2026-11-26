// step_by_apply_test.go — the apply rung's contract (apply_close.go):
//
//  1. KEYLESS: a leaf that is an instance of a resident guarded law
//     whose antecedents are in the context closes with NO certificate
//     and NO plan written — the refuter never runs.
//  2. STRICT REPLAY FROM NOTHING: the same By closes under
//     RequireCNFCacheHit with an EMPTY store — the move is a pure
//     function of the leaf, recorded nowhere.
//  3. The premise split's shape: a conjunctive antecedent whose
//     conjuncts are resident separately still discharges (the
//     assert-then-split path).
//  4. HONEST LIMITS, named in the diagnostic: a conclusion match that
//     leaves a binder unpinned, and a resident law whose antecedent is
//     missing,
//     both DECLINE — the closers run as before — and the failure text
//     carries the apply rung's nearest miss.
package proof

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestByApply_GuardedLawClosesKeyless(t *testing.T) {
	goal := guardedFixture(t)
	st := newGroundByStore()

	live := groundTestEnv(t)
	st.wire(live, true)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, live, t.Context(), guardedBySpec(goal)), "live By must close")
	require.True(t, n.Proved())
	assert.Empty(t, st.Proofs(), "the apply rung closes with no refutation, so no certificate")
	assert.Empty(t, st.Plans(), "and before the grounding stage, so no plan entry")

	strict := groundTestEnv(t)
	newGroundByStore().wire(strict, true)
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n2, strict, t.Context(), guardedBySpec(goal)),
		"strict replay must close from an EMPTY store — the move records nothing")
	require.True(t, n2.Proved())
}

// conjAnteFixture states the law's guard as a conjunction and leaves
// the conjuncts resident SEPARATELY — what the premise split makes of a
// conjunctive hypothesis:
//
//	∀x. P(x) ∧ Q(x) ⇒ ∀y. zk(y) = g(x, y),  P(a),  Q(a)  ⊢  zk(b) = g(a, b)
func conjAnteFixture(t *testing.T) Prop {
	t.Helper()
	ind2 := core.MakeFun(TypeInd, core.MakeFun(TypeInd, TypeInd))
	pred := core.MakeFun(TypeInd, core.TypeBool())
	g := ext.Var("g", ind2)
	P := ext.Var("P", pred)
	Q := ext.Var("Q", pred)
	a := ext.Var("a", TypeInd)
	b := ext.Var("b", TypeInd)
	x := ext.Var("x", TypeInd)
	y := ext.Var("y", TypeInd)
	zk := ext.WrapTerm(zkConst)

	law := ext.ForAll(x)(P.Apply(x).And(Q.Apply(x)).Imply(ext.ForAll(y)(zk.Apply(y).Eq(g.Apply(x, y)))))
	concl := zk.Apply(b).Eq(g.Apply(a, b))
	return prop.MakeProp(concl.Core(), law.Core(), P.Apply(a).Core(), Q.Apply(a).Core())
}

func TestByApply_ConjunctiveAntecedentFromSplitConjuncts(t *testing.T) {
	goal := conjAnteFixture(t)
	st := newGroundByStore()
	live := groundTestEnv(t)
	st.wire(live, true)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, live, t.Context(), guardedBySpec(goal)))
	require.True(t, n.Proved())
	assert.Empty(t, st.Proofs(), "asserting the conjunction and splitting it is keyless")
}

// unpinnedFixture: the law's conclusion mentions only one of its two
// binders, so no goal can pin the other —
//
//	∀x z. P(z) ⇒ zk(x) = g(x, x)  ⊢  zk(b) = g(b, b)
//
// — and nothing supplies P at any point, so the refuter cannot close it
// either: the failure must name the apply rung's miss.
func unpinnedFixture(t *testing.T) Prop {
	t.Helper()
	ind2 := core.MakeFun(TypeInd, core.MakeFun(TypeInd, TypeInd))
	g := ext.Var("g", ind2)
	P := ext.Var("P", core.MakeFun(TypeInd, core.TypeBool()))
	b := ext.Var("b", TypeInd)
	x := ext.Var("x", TypeInd)
	z := ext.Var("z", TypeInd)
	zk := ext.WrapTerm(zkConst)
	law := ext.ForAll(x)(ext.ForAll(z)(P.Apply(z).Imply(zk.Apply(x).Eq(g.Apply(x, x)))))
	concl := zk.Apply(b).Eq(g.Apply(b, b))
	return prop.MakeProp(concl.Core(), law.Core())
}

func mustPanicContaining(t *testing.T, want string, run func()) {
	t.Helper()
	defer func() {
		r := recover()
		require.NotNil(t, r, "expected a failure")
		msg := anyToString(r)
		assert.Contains(t, msg, want, "the failure text names the apply rung's nearest miss")
	}()
	run()
}

func TestByApply_DeclinesAndNamesTheMiss(t *testing.T) {
	t.Run("binder the conclusion does not pin", func(t *testing.T) {
		goal := unpinnedFixture(t)
		env := groundTestEnv(t)
		newGroundByStore().wire(env, true)
		spec := BySpec{Premises: []ByPremiseSpec{
			{Install: prop.MakeProp(goal.Hyp(0)), Resident: true, Describe: "law"}}}
		mustPanicContaining(t, "every binder", func() {
			ApplyByStep(CreateGoalStack(goal), env, t.Context(), spec)
		})
	})
	t.Run("antecedent missing from the context", func(t *testing.T) {
		// The guarded fixture with its guard P(a) withheld from the leaf
		// (hyps are stored sorted, so the law is located by shape).
		full := guardedFixture(t)
		var law core.Term
		for i := range full.NumHyps() {
			if !ext.MatchesFORALL(full.Hyp(i)).IsZero() {
				law = full.Hyp(i)
			}
		}
		require.NotNil(t, law)
		goal := prop.MakeProp(full.Conclusion(), law)
		env := groundTestEnv(t)
		newGroundByStore().wire(env, true)
		spec := BySpec{Premises: []ByPremiseSpec{
			{Install: prop.MakeProp(law), Resident: true, Describe: "guarded law"}}}
		mustPanicContaining(t, "is not in the context", func() {
			ApplyByStep(CreateGoalStack(goal), env, t.Context(), spec)
		})
	})
}

// TestByApply_NamedPremiseStatedForm is the shape every chapter `By`
// over a typed dep has: the law arrives as a NAMED premise whose
// canonical install is its NORMALIZED form (a prenex clause with the
// guard negated — no telescope) and whose stated form rides along as
// the reference. The apply rung must read the reference, install it on
// demand, and close keylessly; the install's claim obligation is a
// child of the composite (certified by the macro from the reference).
func TestByApply_NamedPremiseStatedForm(t *testing.T) {
	full := guardedFixture(t)
	var law core.Term
	for i := range full.NumHyps() {
		if !ext.MatchesFORALL(full.Hyp(i)).IsZero() {
			law = full.Hyp(i)
		}
	}
	require.NotNil(t, law)
	// The leaf carries only the guard P(a); the law is a named premise.
	guard := full.Hyp(0)
	if guard.AlphaEquals(law) {
		guard = full.Hyp(1)
	}
	goal := prop.MakeProp(full.Conclusion(), guard)
	stated := prop.MakeProp(law)
	normalized, _ := prop.Normalize(stated)
	require.NotNil(t, normalized)
	require.False(t, normalized.AlphaEquals(stated), "the fixture's law must normalize to a different form")

	spec := BySpec{Premises: []ByPremiseSpec{
		{Install: prop.MakeProp(guard), Resident: true, Describe: "guard"},
		{Install: normalized, Reference: stated, Describe: "guarded law (named)"},
	}}
	st := newGroundByStore()
	live := groundTestEnv(t)
	st.wire(live, true)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, live, t.Context(), spec), "live By must close through the stated form")
	assert.Empty(t, st.Proofs(), "keyless: the apply rung closed it, not the refuter")
	// The composite's open children are the claim obligations: the
	// normalized install's, and the stated form's on-demand install.
	open := 0
	for _, c := range n.Children() {
		if !c.Proved() {
			open++
		}
	}
	assert.Equal(t, 2, open, "two claim obligations — the normalized install and the stated-form install")
}

// TestByApply_FunctionWitnessIsEtaReduced pins the witness spelling for
// a FUNCTION-typed binder: the matcher binds a head applied under a
// binder as an abstraction (`λy. q(y)`), and the instance must be taken
// at the η-reduced `q` — the kernel's `P(λy. q(y))` is not the resident
// `P(q)`, and `zk((λy. q(y))(b))` is not the goal's `zk(q(b))`.
//
//	∀h:ind→ind. P(h) ⇒ ∀y. zk(h(y)) = g(y),  P(q)  ⊢  zk(q(b)) = g(b)
func TestByApply_FunctionWitnessIsEtaReduced(t *testing.T) {
	indFun := core.MakeFun(TypeInd, TypeInd)
	g := ext.Var("g", indFun)
	q := ext.Var("q", indFun)
	P := ext.Var("P", core.MakeFun(indFun, core.TypeBool()))
	b := ext.Var("b", TypeInd)
	h := ext.Var("h", indFun)
	y := ext.Var("y", TypeInd)
	zk := ext.WrapTerm(zkConst)

	law := ext.ForAll(h)(P.Apply(h).Imply(ext.ForAll(y)(zk.Apply(h.Apply(y)).Eq(g.Apply(y)))))
	guard := P.Apply(q)
	concl := zk.Apply(q.Apply(b)).Eq(g.Apply(b))
	goal := prop.MakeProp(concl.Core(), law.Core(), guard.Core())

	st := newGroundByStore()
	live := groundTestEnv(t)
	st.wire(live, true)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, live, t.Context(), guardedBySpec(goal)), "live By must close")
	require.True(t, n.Proved())
	assert.Empty(t, st.Proofs(), "the apply rung closes it at the η-reduced witness, keyless")
}

// TestByApply_ConclusionModuloEta: the witnesses are η-reduced along
// their spine, so a goal spelled at the expanded function meets the
// kernel instance at the bare one; the two are one statement, and the
// rung closes it keyless through the assumption step's conversion.
//
//	∀h:ind→ind. P(h) ⇒ R(h),  P(q)  ⊢  R(λy. q(y))
func TestByApply_ConclusionModuloEta(t *testing.T) {
	indFun := core.MakeFun(TypeInd, TypeInd)
	q := ext.Var("q", indFun)
	P := ext.Var("P", core.MakeFun(indFun, core.TypeBool()))
	R := ext.Var("R", core.MakeFun(indFun, core.TypeBool()))
	h := ext.Var("h", indFun)
	y := core.Var(core.TermName("y"), TypeInd)

	law := ext.ForAll(h)(P.Apply(h).Imply(R.Apply(h)))
	guard := P.Apply(q)
	concl := R.Apply(ext.WrapTerm(ext.Abs(y, q.Apply(ext.WrapTerm(y)).Core())))
	goal := prop.MakeProp(concl.Core(), law.Core(), guard.Core())

	st := newGroundByStore()
	live := groundTestEnv(t)
	st.wire(live, true)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, live, t.Context(), guardedBySpec(goal)), "live By must close")
	require.True(t, n.Proved())
	assert.Empty(t, st.Proofs(), "the apply rung closes the η-expanded goal keyless")
}

// TestByApply_NamedPremiseAtItsOwnTypeVariable pins the polymorphic-
// carrier case: a structure law stated over a type variable A, applied
// at a leaf that is itself over A — every leaf of an abstract chapter,
// where the law's hypothesis is the resident structure fact. The type
// adaptation enumerator drops the identity instance by contract, so
// the rung must try the stated form itself; otherwise the exact
// instance falls to the refuter and records a key it never needed.
//
//	∀op:(A→A→A). ∀e:A. S(op, e) ⇒ ∀x:A. op(e, x) = x,  S(op₀, e₀)  ⊢  op₀(e₀, x₀) = x₀
func TestByApply_NamedPremiseAtItsOwnTypeVariable(t *testing.T) {
	A := core.MakeVarType("A")
	opType := core.MakeFun(A, core.MakeFun(A, A))
	S := ext.Var("S", core.MakeFun(opType, core.MakeFun(A, core.TypeBool())))
	op := ext.Var("op", opType)
	e := ext.Var("e", A)
	x := ext.Var("x", A)
	op0 := ext.Var("op_0", opType)
	e0 := ext.Var("e_0", A)
	x0 := ext.Var("x_0", A)

	law := ext.ForAll(op)(ext.ForAll(e)(S.Apply(op, e).Imply(ext.ForAll(x)(op.Apply(e, x).Eq(x)))))
	instance := S.Apply(op0, e0)
	goal := prop.MakeProp(op0.Apply(e0, x0).Eq(x0).Core(), instance.Core())

	stated := prop.MakeProp(law.Core())
	normalized, _ := prop.Normalize(stated)
	require.NotNil(t, normalized)
	spec := BySpec{Premises: []ByPremiseSpec{
		{Install: prop.MakeProp(instance.Core()), Resident: true, Describe: "the structure hypothesis"},
		{Install: normalized, Reference: stated, Describe: "structure law (named)"},
	}}
	st := newGroundByStore()
	live := groundTestEnv(t)
	st.wire(live, true)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, live, t.Context(), spec), "live By must close through the stated form at the goal's own type variable")
	assert.Empty(t, st.Proofs(), "keyless: the apply rung closed it at the identity type instance, not the refuter")
}

// A projection law `∀add zero neg. G(add, zero, neg) ⇒ S(add, zero)` at
// the hypothesis G(add₀, zero₀, neg₀), goal S(add₀, zero₀): the
// conclusion pins add and zero, the antecedent pins neg off the
// context, and the leaf closes keyless — a structure chapter's
// `Have("comm_monoid(add, zero)", By(Monoid, group))`. The install must
// be the plain hyp-add: the preserving chain's conclusion match would
// apply the law backwards and leave `G(add₀, zero₀, neg)` with neg free.
func TestByApply_ProjectionLawPinsComponentOffContext(t *testing.T) {
	A := core.MakeVarType("A")
	opType := core.MakeFun(A, core.MakeFun(A, A))
	unType := core.MakeFun(A, A)
	G := ext.Var("G", core.MakeFun(opType, core.MakeFun(A, core.MakeFun(unType, core.TypeBool()))))
	S := ext.Var("S", core.MakeFun(opType, core.MakeFun(A, core.TypeBool())))
	add := ext.Var("add", opType)
	zero := ext.Var("zero", A)
	neg := ext.Var("neg", unType)
	add0 := ext.Var("add_0", opType)
	zero0 := ext.Var("zero_0", A)
	neg0 := ext.Var("neg_0", unType)
	x0 := ext.Var("x_0", A)
	y0 := ext.Var("y_0", A)
	z0 := ext.Var("z_0", A)

	law := ext.ForAll(add)(ext.ForAll(zero)(ext.ForAll(neg)(G.Apply(add, zero, neg).Imply(S.Apply(add, zero)))))
	instance := G.Apply(add0, zero0, neg0)
	sum := add0.Apply(x0, y0).Eq(add0.Apply(x0, z0))
	goal := prop.MakeProp(S.Apply(add0, zero0).Core(), sum.Core(), instance.Core())

	stated := prop.MakeProp(law.Core())
	normalized, _ := prop.Normalize(stated)
	require.NotNil(t, normalized)
	spec := BySpec{Premises: []ByPremiseSpec{
		{Install: normalized, Reference: stated, Describe: "projection law (named)"},
		{Install: prop.MakeProp(instance.Core()), Resident: true, Describe: "the structure hypothesis"},
	}}
	st := newGroundByStore()
	live := groundTestEnv(t)
	st.wire(live, true)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, live, t.Context(), spec), "live By must close through the projection law")
	assert.Empty(t, st.Proofs(), "keyless: the apply rung pins neg off the context and fires")
}

// TestByApply_ConjunctiveAntecedentAtItsOwnTypeVariable: a Horn law
// with a CONJUNCTIVE antecedent, stated over a type variable A and
// cited at a leaf over A — the identity type instance, which the
// enumerator drops — with the antecedent resident whole and as its
// conjuncts beside the premise's normalized clause:
//
//	∀s t:set(A). F(t) ∧ Sub(s, t) ⇒ F(s),  F(t₀),  Sub(s₀, t₀),  F(t₀) ∧ Sub(s₀, t₀)  ⊢  F(s₀)
//
// closes through the stated form, keyless.
func TestByApply_ConjunctiveAntecedentAtItsOwnTypeVariable(t *testing.T) {
	A := core.MakeVarType("A")
	setA := core.MakeFun(A, core.TypeBool())
	F := ext.Var("F", core.MakeFun(setA, core.TypeBool()))
	Sub := ext.Var("Sub", core.MakeFun(setA, core.MakeFun(setA, core.TypeBool())))
	s := ext.Var("s", setA)
	tt := ext.Var("t", setA)
	s0 := ext.Var("s_0", setA)
	t0 := ext.Var("t_0", setA)

	law := ext.ForAll(s)(ext.ForAll(tt)(F.Apply(tt).And(Sub.Apply(s, tt)).Imply(F.Apply(s))))
	finiteT := F.Apply(t0)
	contained := Sub.Apply(s0, t0)
	whole := finiteT.And(contained)
	for _, shape := range []struct {
		name string
		hyps []core.Term
	}{
		{"conjuncts only", []core.Term{finiteT.Core(), contained.Core()}},
		{"whole only", []core.Term{whole.Core()}},
		{"whole and conjuncts", []core.Term{finiteT.Core(), contained.Core(), whole.Core()}},
	} {
		t.Run(shape.name, func(t *testing.T) {
			goal := prop.MakeProp(F.Apply(s0).Core(), shape.hyps...)
			stated := prop.MakeProp(law.Core())
			normalized, _ := prop.Normalize(stated)
			require.NotNil(t, normalized)
			var premises []ByPremiseSpec
			for i, h := range shape.hyps {
				premises = append(premises, ByPremiseSpec{Install: prop.MakeProp(h), Resident: true, Describe: fmt.Sprintf("fact %d", i)})
			}
			premises = append(premises, ByPremiseSpec{Install: normalized, Reference: stated, Describe: "finite subset (named)"})
			spec := BySpec{Premises: premises}
			st := newGroundByStore()
			live := groundTestEnv(t)
			st.wire(live, true)
			n := CreateGoalStack(goal)
			require.True(t, ApplyByStep(n, live, t.Context(), spec), "live By must close through the stated form at the goal's own type variable")
			assert.Empty(t, st.Proofs(), "keyless: the apply rung closed it at the identity type instance, not the refuter")
		})
	}
}

// A conjunctive goal is closed conjunct by conjunct, each conditioned
// in its own round, and a round the apply rung closed is told by the
// working leaves left. Where the rung closes a conjunct through a
// premise's stated form installed on demand — an ⇔ law cited at its
// witnesses, whose stated instance is not resident — that install's
// claim obligation joins the executor's claim set mid-round, and it is
// not a working leaf: each later conjunct still gets its round. Read
// as one, the rung's close looked like none, and the next conjunct
// reached the refuter unconditioned (a key the bare cite never paid).
//
//	∀s n m f. s(n, m, f) ⇔ C₁ ∧ C₂ ∧ C₃  at (s, n, m, f),  s(n, m, f)  ⊢  C₁ ∧ C₂ ∧ C₃
func TestByApply_WitnessedIffClosesEveryConjunctOfTheGoal(t *testing.T) {
	stated := core.TestThm(parseFor(t, "∀s:(num → num → (num → num) → bool). ∀n m:num. ∀f:(num → num). s(n, m, f) ⇔ "+
		"(∀a b:num. a ≤ b ∧ b ≤ m ⇒ f(a) ≤ f(b)) ∧ (∀a:num. a ≤ m ⇒ f(a) ≤ n) ∧ (∀a:num. m < a ⇒ f(a) = 0)").Conclusion())
	sec := CreateGoalStack(parseFor(t, "s:(num → num → (num → num) → bool), n:num, m:num, f:(num → num) ⊢ s(n, m + 1, f) ⇒ "+
		"(∀j k:num. j ≤ k ∧ k ≤ m + 1 ⇒ f(j) ≤ f(k)) ∧ (∀k:num. k ≤ m + 1 ⇒ f(k) ≤ n) ∧ (∀k:num. m + 1 < k ⇒ f(k) = 0)"))
	require.True(t, sec.runStep(StripImp()))
	leaf := sec.UnsolvedLeaves()[0]
	member := leaf.Goal.Hyp(leaf.Goal.NumHyps() - 1)
	predicate, components := ext.MatchesApply(member)
	for _, witnessed := range []bool{false, true} {
		cite := ByPremiseSpec{Install: stated, Describe: "the law"}
		if witnessed {
			cite.Witnesses = append([]core.Term{predicate}, components...)
		}
		spec := BySpec{Premises: []ByPremiseSpec{{Install: prop.MakeProp(member), Resident: true, Describe: "s(n, m + 1, f)"}, cite}}
		strict := groundTestEnv(t)
		st := newGroundByStore()
		st.wire(strict, true)
		strict.RequireCNFCacheHit = true
		n := CreateGoalStack(leaf.Goal)
		closed := false
		require.NotPanics(t, func() { closed = ApplyByStep(n, strict, t.Context(), spec) },
			"witnessed=%v: strict replay from an EMPTY store closes every conjunct on the rung", witnessed)
		require.True(t, closed, "witnessed=%v", witnessed)
		assert.Empty(t, st.Proofs(), "witnessed=%v: keyless", witnessed)
	}
}

// A normalized clause may need its stated Horn form on the apply rung.
// That alternate form keeps an explicit compound instance's remaining
// letters fixed, just as the installed clause does.
func TestByApply_ExplicitCompoundInstanceKeepsItsLetters(t *testing.T) {
	for _, frontend := range []string{"Go", "session"} {
		for _, mode := range []string{"plain", "named", "antecedent"} {
			for _, test := range []struct {
				name, letter string
				exact        bool
			}{
				{"fixed_same_type", "B", true}, {"fixed_other_type", "C", true}, {"unpinned_other_type", "C", false},
			} {
				t.Run(frontend+"/"+mode+"/"+test.name, func(t *testing.T) {
					env := groundTestEnv(t)
					st := newGroundByStore()
					st.wire(env, true)
					env.RequireCNFCacheHit = true
					script := NewScript(env)
					predTy := core.MakeFun(core.TypeA(), core.TypeBool())
					pm := core.MakeConstMeta("exactHeadP", predTy)
					qm := core.MakeConstMeta("exactHeadQ", predTy)
					rm := core.MakeConstMeta("exactHeadR", predTy)
					for _, meta := range []core.ConstTermMeta{pm, qm, rm} {
						env.ProofService.LoadOrStoreConstMeta(meta)
					}
					x := core.Var("x", core.TypeA())
					p := ext.WrapTerm(core.MakeConstTerm(pm, predTy))
					q := ext.WrapTerm(core.MakeConstTerm(qm, predTy))
					law := core.TestThm(ext.ForAll(x)(p.Apply(x).Imply(q.Apply(x))).Core())
					serveThm(script, "zz_exact_head", law)
					chosen := NamedFact(depName("zz_exact_head"))
					if test.exact {
						chosen = Inst(depName("zz_exact_head"), TypeBinder.BindA[ext.Set[ext.B]]())
					}
					targetTy := core.MakeFun(core.MakeVarType(core.TypeName(test.letter)), core.TypeBool())
					a := core.Var("a", targetTy)
					at := func(meta core.ConstTermMeta) core.Term {
						return core.Apply(core.MakeConstTerm(meta, core.MakeFun(targetTy, core.TypeBool())), a)
					}
					conclusion, hyps := at(qm), []core.Term{at(pm)}
					if mode == "antecedent" {
						conclusion = at(rm)
						hyps = append(hyps, ext.WrapTerm(at(qm)).Imply(at(rm)).Core())
					}
					goal := core.MakeProp(conclusion, hyps...)
					section := script.Section(goal)
					apply := func() {
						if frontend == "Go" {
							cite := chosen
							if mode == "named" {
								cite = cite.Where("x", a)
							}
							premises := []any{cite}
							for _, h := range hyps {
								premises = append(premises, ResidentHyp(h))
							}
							section.Do(Derive(func(arg *Argument) { arg.Show("the law at the chosen type", By(premises...)) }))
							require.True(t, section.Proved())
							return
						}
						cite := ByPremiseSpec{Install: law, Reference: law, Describe: "the polymorphic law"}
						if test.exact {
							typed := chosen.target.(typedInst).resolve(script)
							cite = ByPremiseSpec{Install: typed.Thm, Reference: typed.Reference(), Exact: true, Describe: "the law at Set[B]"}
						}
						if mode == "named" {
							cite.Named = []NamedWitness{{Binder: "x", Witness: a}}
						}
						premises := []ByPremiseSpec{cite}
						for _, h := range hyps {
							premises = append(premises, ByPremiseSpec{Install: core.MakeProp(h), Resident: true, Describe: "the premise"})
						}
						require.True(t, ApplyByStep(section, env, t.Context(), BySpec{Premises: premises}))
					}
					if test.exact && test.letter == "C" {
						var refused any
						func() { defer func() { refused = recover() }(); apply() }()
						require.NotNil(t, refused, "an explicit Set[B] law cannot become a Set[C] head")
						if mode == "named" {
							require.Contains(t, fmt.Sprint(refused), "pinned by name did not apply")
						} else {
							require.Contains(t, fmt.Sprint(refused), "CNF cache MISS")
						}
						return
					}
					require.NotPanics(t, apply)
					assert.Empty(t, st.Proofs())
				})
			}
		}
	}
}
