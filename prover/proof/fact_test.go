// fact_test.go — the fact/cite surface (fact.go).

package proof

import (
	"fmt"
	"runtime"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/ac"
	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"
)

// =======================================================================
// CiteACRegroup
// =======================================================================

// acRegroupTestEnv is the synthetic AC setup shared by the
// CiteACRegroup tests: an uninterpreted binary const ⊕ on ind with
// TestThm assoc/sym certificates (acceptable inside _test.go only) —
// the Action never looks the op up anywhere, it reads it off the
// assoc cert, so an uninterpreted const exercises exactly the
// any-AC-op contract.
type acRegroupTestEnv struct {
	ctx        *Script
	plus       *ext.TermWrapper
	assoc, sym Thm
	a, b, c, d *ext.TermWrapper
	m, n, p    *ext.TermWrapper // the certs' own binder vars
}

// makeACRegroupTestEnv builds the env. reversedAssoc stores the assoc
// cert as ∀m n p. m⊕(n⊕p) = (m⊕n)⊕p — the nat_arith.AddAssoc orientation —
// instead of the reading direction.
func makeACRegroupTestEnv(reversedAssoc bool) *acRegroupTestEnv {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	opTy := MakeFun(TypeInd, MakeFun(TypeInd, TypeInd))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("acplus", opTy))
	e := &acRegroupTestEnv{ctx: ctx}
	e.plus = ctx.Const("acplus", opTy)
	e.m, e.n, e.p = Var("m", TypeInd), Var("n", TypeInd), Var("p", TypeInd)
	left := e.plus.Apply(e.plus.Apply(e.m, e.n), e.p)
	right := e.plus.Apply(e.m, e.plus.Apply(e.n, e.p))
	eq := left.Eq(right)
	if reversedAssoc {
		eq = right.Eq(left)
	}
	e.assoc = core.TestThm(ext.ForAll(e.m)(ext.ForAll(e.n)(ext.ForAll(e.p)(eq))))
	e.sym = core.TestThm(ext.ForAll(e.m)(ext.ForAll(e.n)(
		e.plus.Apply(e.m, e.n).Eq(e.plus.Apply(e.n, e.m)))))
	e.a, e.b = Var("a", TypeInd), Var("b", TypeInd)
	e.c, e.d = Var("c", TypeInd), Var("d", TypeInd)
	return e
}

// proveEqGoal poses ⊢ lhs = rhs as a section and closes it with a
// single CiteACRegroup (the derived equation matches the goal exactly,
// so the install surface's Cite closes the section outright).
func (e *acRegroupTestEnv) proveEqGoal(t *testing.T, lhs, rhs *ext.TermWrapper) *GoalStackNode {
	t.Helper()
	sec := e.ctx.Section(prop.MakeProp(lhs.Eq(rhs)))
	sec.Do(CiteACRegroup(e.assoc, e.sym, lhs, rhs))
	require.True(t, sec.Proved(), "CiteACRegroup did not close ⊢ %s = %s",
		lhs, rhs)
	sec.Qed()
	return sec
}

// TestCiteACRegroup_InterchangeLaw: the motivating 4-leaf instance —
// the interchange law (a⊕b)⊕(c⊕d) = (a⊕c)⊕(b⊕d), the shape the
// corpus hand-spells as a 5-6-cite AddAssoc/AddSym walk.
func TestCiteACRegroup_InterchangeLaw(t *testing.T) {
	e := makeACRegroupTestEnv(false)
	lhs := e.plus.Apply(e.plus.Apply(e.a, e.b), e.plus.Apply(e.c, e.d))
	rhs := e.plus.Apply(e.plus.Apply(e.a, e.c), e.plus.Apply(e.b, e.d))
	e.proveEqGoal(t, lhs, rhs)
}

// TestCiteACRegroup_ThreeLeafRotation: (a⊕b)⊕c = b⊕(c⊕a) — a full
// 3-cycle plus re-association.
func TestCiteACRegroup_ThreeLeafRotation(t *testing.T) {
	e := makeACRegroupTestEnv(false)
	lhs := e.plus.Apply(e.plus.Apply(e.a, e.b), e.c)
	rhs := e.plus.Apply(e.b, e.plus.Apply(e.c, e.a))
	e.proveEqGoal(t, lhs, rhs)
}

// TestCiteACRegroup_ReversedAssocOrientation: the assoc cert stored as
// ∀m n p. m⊕(n⊕p) = (m⊕n)⊕p — the actual nat_arith.AddAssoc orientation —
// is detected and EqSym'd internally; same interchange goal closes.
func TestCiteACRegroup_ReversedAssocOrientation(t *testing.T) {
	e := makeACRegroupTestEnv(true)
	lhs := e.plus.Apply(e.plus.Apply(e.a, e.b), e.plus.Apply(e.c, e.d))
	rhs := e.plus.Apply(e.plus.Apply(e.a, e.c), e.plus.Apply(e.b, e.d))
	e.proveEqGoal(t, lhs, rhs)
}

// TestCiteACRegroup_DuplicateLeaves: multiset (not set) semantics —
// (a⊕a)⊕b = a⊕(b⊕a) keeps both a-occurrences distinct.
func TestCiteACRegroup_DuplicateLeaves(t *testing.T) {
	e := makeACRegroupTestEnv(false)
	lhs := e.plus.Apply(e.plus.Apply(e.a, e.a), e.b)
	rhs := e.plus.Apply(e.a, e.plus.Apply(e.b, e.a))
	e.proveEqGoal(t, lhs, rhs)
}

// TestCiteACRegroup_InstallsResidentHyp: on a goal that does not
// mention the sum, the install surface forward-loads the derived
// equation as a resident hypothesis — the "regroup then CnfRefute"
// consumption shape of the walks.
func TestCiteACRegroup_InstallsResidentHyp(t *testing.T) {
	e := makeACRegroupTestEnv(false)
	q := Var("q", MakeFun(TypeInd, TypeBool))
	lhs := e.plus.Apply(e.plus.Apply(e.a, e.b), e.c)
	rhs := e.plus.Apply(e.c, e.plus.Apply(e.b, e.a))

	sec := e.ctx.Section(prop.MakeProp(q.Apply(e.d)))
	sec.Do(CiteACRegroup(e.assoc, e.sym, lhs, rhs))

	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1, "install must leave exactly the residual goal open")
	require.True(t, leaves[0].Goal.HasHyp(lhs.Eq(rhs)),
		"derived equation is not resident as a hypothesis:\n%s",
		prop.PrintProp(leaves[0].Goal))
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(q.Apply(e.d)),
		"residual conclusion changed:\n%s", prop.PrintProp(leaves[0].Goal))
}

// requirePanicContains runs f and requires it panics with a message
// containing want.
func requirePanicContains(t *testing.T, want string, f func()) {
	t.Helper()
	defer func() {
		r := recover()
		require.NotNil(t, r, "expected a panic containing %q", want)
		require.Contains(t, fmt.Sprint(r), want)
	}()
	f()
}

// TestCiteACRegroup_MultisetMismatchPanics: sides that are not
// AC-rearrangements of the same sum panic at Action construction,
// printing both flattened leaf lists.
func TestCiteACRegroup_MultisetMismatchPanics(t *testing.T) {
	e := makeACRegroupTestEnv(false)
	lhs := e.plus.Apply(e.plus.Apply(e.a, e.b), e.c)
	rhs := e.plus.Apply(e.plus.Apply(e.a, e.b), e.d)
	requirePanicContains(t, "leaf multisets differ", func() {
		CiteACRegroup(e.assoc, e.sym, lhs, rhs)
	})

	// Multiplicity mismatch too — {a,a,b} vs {a,b,b}.
	lhs = e.plus.Apply(e.plus.Apply(e.a, e.a), e.b)
	rhs = e.plus.Apply(e.plus.Apply(e.a, e.b), e.b)
	requirePanicContains(t, "leaf multisets differ", func() {
		CiteACRegroup(e.assoc, e.sym, lhs, rhs)
	})
}

// TestCiteACRegroup_AlphaEqualSidesPanic: lhs α-equal to rhs is an
// authoring error (the equation would normalize to ⊤).
func TestCiteACRegroup_AlphaEqualSidesPanic(t *testing.T) {
	e := makeACRegroupTestEnv(false)
	lhs := e.plus.Apply(e.a, e.b)
	requirePanicContains(t, "nothing to regroup", func() {
		CiteACRegroup(e.assoc, e.sym, lhs, lhs)
	})
}

// TestCiteACRegroup_CertPatternPanics: passing a cert's OWN equation
// side where a concrete sum belongs is the authoring error the
// ground-only guard exists for — the two sides of the assoc cert are
// each other's AC-rearrangement, so nothing else would catch it.
func TestCiteACRegroup_CertPatternPanics(t *testing.T) {
	e := makeACRegroupTestEnv(false)
	lhs := e.plus.Apply(e.plus.Apply(e.m, e.n), e.p) // (m⊕n)⊕p — the cert's own lhs
	rhs := e.plus.Apply(e.m, e.plus.Apply(e.n, e.p)) // m⊕(n⊕p) — the cert's own rhs
	requirePanicContains(t, "one of the certs' own equation sides", func() {
		CiteACRegroup(e.assoc, e.sym, lhs, rhs)
	})
}

// TestCiteACRegroup_LeafNamedLikeBinderIsAccepted: a concrete sum one of
// whose LEAVES merely shares a name with a cert binder is a legitimate
// input, not a pattern.
//
// This pins the fix for the guard's original name-based test, which
// rejected exactly this shape. The names the assoc/sym certs bind are
// the commonest variable names in the corpus — nat_arith's AddAssoc and
// MulAssoc bind ∀m n p — so under the old test every AC regroup inside
// an induction over m, n or p was refused on spelling alone, and a
// member had to work around it. Instantiation runs through the
// kernel's capture-avoiding ConclForAllInsts, so the collision was
// never a soundness question.
func TestCiteACRegroup_LeafNamedLikeBinderIsAccepted(t *testing.T) {
	e := makeACRegroupTestEnv(false)
	lhs := e.plus.Apply(e.plus.Apply(e.m, e.a), e.b) // (m⊕a)⊕b — three distinct leaves
	rhs := e.plus.Apply(e.b, e.plus.Apply(e.a, e.m)) // b⊕(a⊕m)
	e.proveEqGoal(t, lhs, rhs)
}

// TestCiteACRegroup_OpMismatchPanics: assoc and sym certs over
// different ops are rejected at construction.
func TestCiteACRegroup_OpMismatchPanics(t *testing.T) {
	e := makeACRegroupTestEnv(false)
	opTy := MakeFun(TypeInd, MakeFun(TypeInd, TypeInd))
	e.ctx.Env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("acmul", opTy))
	mul := e.ctx.Const("acmul", opTy)
	otherSym := core.TestThm(ext.ForAll(e.m)(ext.ForAll(e.n)(
		mul.Apply(e.m, e.n).Eq(mul.Apply(e.n, e.m)))))

	lhs := e.plus.Apply(e.plus.Apply(e.a, e.b), e.c)
	rhs := e.plus.Apply(e.c, e.plus.Apply(e.a, e.b))
	requirePanicContains(t, "different ops", func() {
		CiteACRegroup(e.assoc, otherSym, lhs, rhs)
	})
}

// TestCiteACRegroup_WrongOperandTypePanics: a side that is not of the
// certs' operand type is rejected with the type-specialize hint.
func TestCiteACRegroup_WrongOperandTypePanics(t *testing.T) {
	e := makeACRegroupTestEnv(false)
	q := Var("q", TypeBool)
	requirePanicContains(t, "operand type", func() {
		CiteACRegroup(e.assoc, e.sym, ext.WrapTerm(q), ext.WrapTerm(q))
	})
}

// TestCiteACRegroup_DeterministicRecordRoundTrip: two fresh-env runs
// of the same regroup record identical DetailedProofProto trees — the
// replay contract for a Build is deterministic re-execution,
// so wire-level equality of the recorded ministeps is the round trip.
func TestCiteACRegroup_DeterministicRecordRoundTrip(t *testing.T) {
	record := func() *DetailedProofProto {
		e := makeACRegroupTestEnv(false)
		lhs := e.plus.Apply(e.plus.Apply(e.a, e.b), e.plus.Apply(e.c, e.d))
		rhs := e.plus.Apply(e.plus.Apply(e.a, e.c), e.plus.Apply(e.b, e.d))
		sec := e.proveEqGoal(t, lhs, rhs)
		p := sec.DetailedProofProto()
		require.NotNil(t, p, "proved section must serialize")
		return p
	}
	p1, p2 := record(), record()
	require.True(t, proto.Equal(p1, p2),
		"two fresh runs recorded different proofs:\n--- run 1:\n%v\n--- run 2:\n%v", p1, p2)
}

// =======================================================================
// Cite — absorption-site hyp location
// =======================================================================

// TestCite_AbsorptionSiteLocatesInstalledHyp pins installedHypIndex's
// content branch: a cite into a CLAUSE-shaped goal absorbs the goal's
// own negated disjuncts as hyps alongside the lemma's, so the install
// nets more than one hyp and the before/after diff cannot say which one
// the lemma contributed. Content addressing can — and must, because the
// fused witness form is the corpus-default first move at nonneg_real_formal_diff/real_construction.
//
//	lemma: ⊢ ∀x. p(x)      goal: ⊢ ¬A ∨ ¬B ∨ q(c)
//
// The install folds the goal's disjuncts into hyps AND adds p's ∀-form,
// so several hyps appear at once. Before the content refinement this
// panicked with "install added more than one hyp".
func TestCite_AbsorptionSiteLocatesInstalledHyp(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	pTy := core.MakeFun(TypeA, core.TypeBool())
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("pc_absorb_test", pTy))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("qc_absorb_test", pTy))
	pc := ctx.Const("pc_absorb_test", pTy)
	qc := ctx.Const("qc_absorb_test", pTy)
	x := Var("x", TypeA)
	c := Var("c", TypeA)
	A := Var("A", core.TypeBool())
	B := Var("B", core.TypeBool())

	allP := core.NewAxiom(ext.ForAll(x)(pc.Apply(x)))

	// Clause-shaped goal: the cite's install absorbs ¬A and ¬B.
	clause := ctx.Section(prop.MakeProp(
		ext.Or(ext.Not(A), ext.Or(ext.Not(B), qc.Apply(c)))))
	before := clause.Goal.NumHyps()
	clause.Do(Cite(MakeFact(allP), c))
	leaves := clause.UnsolvedLeaves()
	require.Len(t, leaves, 1, "the cite leaves one residual leaf")
	require.Greater(t, leaves[0].Goal.NumHyps(), before+1,
		"this fixture must be an ABSORPTION site — the install nets "+
			"more than the lemma's own hyp, else it tests nothing")
	// The grounded instance p(c) is resident: that is what locating the
	// right hyp bought us.
	require.True(t, leaves[0].Goal.AnyHyp(pc.Apply(c).AlphaEquals),
		"the ground instance p(c) must be resident after the fused cite")
}

// TestCite_SingleHypInstallUnchanged is the control: at a NON-absorption
// site (one net-new hyp, so the α-match and the diff agree) the fused
// cite behaves exactly as it did before content addressing.
//
//	lemma: ⊢ ∀x. p(x)      goal: hyp S ⊢ R
func TestCite_SingleHypInstallUnchanged(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	pTy := core.MakeFun(TypeA, core.TypeBool())
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("pc_single_test", pTy))
	pc := ctx.Const("pc_single_test", pTy)
	x := Var("x", TypeA)
	c := Var("c", TypeA)
	R := Var("R", core.TypeBool())
	S := Var("S", core.TypeBool())

	allP := core.NewAxiom(ext.ForAll(x)(pc.Apply(x)))

	sec := ctx.Section(prop.MakeProp(R, S))
	sec.Do(Cite(MakeFact(allP), c))
	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	require.Equal(t, 2, leaves[0].Goal.NumHyps(),
		"non-absorption control: S plus the ground instance")
	require.True(t, leaves[0].Goal.AnyHyp(pc.Apply(c).AlphaEquals),
		"the ground instance p(c) must be resident")
	require.False(t, leaves[0].Goal.AnyHyp(ext.ForAll(x)(pc.Apply(x)).AlphaEquals),
		"the non-keep form drops the ∀-source")
}

// =======================================================================
// By over a self-proving premise (the DERIVED Fact flavor)
// =======================================================================

// TestBy_ACEquationPremise: `ac.New(assoc, sym).Eq(lhs, rhs)` is a
// premise that proves itself when the By consumes it. The equation
// appears ONCE, as its two endpoints — no Have restating it as a claim
// — and the refuter meets it as a resident hypothesis of the By-leaf.
//
//	q((a⊕b)⊕c) ⊢ q(c⊕(b⊕a))
func TestBy_ACEquationPremise(t *testing.T) {
	e := makeACRegroupTestEnv(false)
	q := Var("q", MakeFun(TypeInd, TypeBool))
	lhs := e.plus.Apply(e.plus.Apply(e.a, e.b), e.c)
	rhs := e.plus.Apply(e.c, e.plus.Apply(e.b, e.a))

	sec := e.ctx.Section(prop.MakeProp(q.Apply(rhs), q.Apply(lhs)))
	sec.Do(Derive(func(a *Argument) {
		known := a.Hyp(q.Apply(lhs).Core())
		a.Show("the two sums are the same leaves in a different order",
			By(known, ac.New(e.assoc, e.sym).Eq(lhs, rhs)))
	}))
	require.True(t, sec.Proved(),
		"By over an ac.Eq premise did not close the section")
}

// TestBy_ACEquationPremise_AssertsInsideTheLeaf: the materialization is
// a Have moved INSIDE the By-leaf — interior to the recorded `by`
// composite, never a step on the deduction spine. The spine node the
// Derive block advances along keeps exactly the children its own verbs
// created, and the leaf By closes carries ONE `by` ministep with no
// assert anywhere in the RECORDED tree (the assert runs in the
// composite's private execution).
func TestBy_ACEquationPremise_AssertsInsideTheLeaf(t *testing.T) {
	e := makeACRegroupTestEnv(false)
	q := Var("q", MakeFun(TypeInd, TypeBool))
	lhs := e.plus.Apply(e.plus.Apply(e.a, e.b), e.c)
	rhs := e.plus.Apply(e.c, e.plus.Apply(e.b, e.a))

	sec := e.ctx.Section(prop.MakeProp(q.Apply(rhs), q.Apply(lhs)))
	sec.Do(Derive(func(a *Argument) {
		a.Show("regroup", By(a.Hyp(q.Apply(lhs).Core()),
			ac.New(e.assoc, e.sym).Eq(lhs, rhs)))
	}))
	require.True(t, sec.Proved())

	var asserts, bySteps int
	var walk func(n *GoalStackNode)
	walk = func(n *GoalStackNode) {
		switch n.miniStep.(type) {
		case _AssertStep:
			asserts++
		case _ByStep:
			bySteps++
		}
		for _, c := range n.children {
			walk(c)
		}
	}
	walk(sec)
	require.Equal(t, 0, asserts,
		"the self-proving premise's assert must stay interior to the composite — never on the recorded tree")
	require.Equal(t, 1, bySteps,
		"the close must record exactly one `by` composite ministep")
}

// TestFact_SelfProvingPremiseTakesNoWitnesses: a derived premise IS the
// ground fact it claims — there is no ∀-source to instantiate.
func TestFact_SelfProvingPremiseTakesNoWitnesses(t *testing.T) {
	e := makeACRegroupTestEnv(false)
	lhs := e.plus.Apply(e.plus.Apply(e.a, e.b), e.c)
	rhs := e.plus.Apply(e.c, e.plus.Apply(e.b, e.a))
	f := premiseFact(ac.New(e.assoc, e.sym).Eq(lhs, rhs))

	requirePanicContains(t, "Fact.At: a self-proving premise is already the ground fact", func() {
		f.At(e.d)
	})
}

// unprovedPremise is a malformed SelfProvingPremise: it hands over a
// statement with no certificate behind it.
type unprovedPremise struct{ p Prop }

func (u unprovedPremise) SelfProof() Prop { return u.p }

// TestMakeFact_SelfProvingContract: the outlet is soundness-first — a
// kit handing over an unproved or hypothesis-carrying statement is
// rejected loudly at adoption, not silently asserted.
func TestPremiseFact_SelfProvingContract(t *testing.T) {
	R := Var("R", core.TypeBool())
	S := Var("S", core.TypeBool())

	requirePanicContains(t, "is not kernel-proved", func() {
		premiseFact(unprovedPremise{prop.MakeProp(R)})
	})
	requirePanicContains(t, "carries hypotheses", func() {
		premiseFact(unprovedPremise{prop.MakeProp(core.TestThm(R, S).Conclusion(), S)})
	})
}

// =======================================================================
// The call site a By records
// =======================================================================

// TestByCallSite_IsCutAtTheModuleRoot: a By names the file and line of
// its own call, the path cut at the module's source root — the same
// text wherever the module is checked out, and under -trimpath.
func TestByCallSite_IsCutAtTheModuleRoot(t *testing.T) {
	_, _, line, _ := runtime.Caller(0)
	by := By().(_ByAction) // the call the site names: one line below the Caller above
	require.Equal(t, fmt.Sprintf("prover/proof/fact_test.go:%d", line+1), by.site)

	_, _, line, _ = runtime.Caller(0)
	arith := ByArith().(_ByAction)
	require.Equal(t, fmt.Sprintf("prover/proof/fact_test.go:%d", line+1), arith.site)
}
