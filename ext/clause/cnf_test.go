package clause

import (
	"context"
	"math"
	"math/rand"
	"slices"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// mustMakeCNF is the test-side wrapper for inputs known to be legal CNF.
func mustMakeCNF(t Term) *CNFClauses {
	c, err := makeCNF(t)
	Assert(err == nil)
	return c
}

func TestIsCNF(t *testing.T) {
	a := Var("a", TypeInd)
	b := Var("b", TypeA)
	D := Var("D", MakeFun(TypeInd, TypeBool))
	h := Var("h_0", TypeBool)
	P := Var("P", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeBool, TypeBool))

	term := ForAll(D, a, b)(Not(D.Apply(a)).Or(P.Apply(b))).
		And(ForAll(D, a)((R.Apply(h)).Or(D.Apply(a))))
	c := mustMakeCNF(term)
	assert.Equal(t, len(c.clauses), 2)
	assertTermAlphaEqual(t,
		c.clauses[0].Term(),
		ForAll(D, a)((R.Apply(h)).Or(D.Apply(a))))
	assertTermAlphaEqual(t,
		c.clauses[1].Term(),
		ForAll(D, a, b)(Not(D.Apply(a)).Or(P.Apply(b))))

	term = D.Apply(a).And(P.Apply(b))
	assert.True(t, isCNF(term))

	term = D.Apply(a).Or(P.Apply(b))
	assert.True(t, isCNF(term))

	term = D.Apply(a).And(P.Apply(b).Or(R.Apply(h)))
	assert.True(t, isCNF(term))

	term = D.Apply(a).And(P.Apply(b).And(R.Apply(h)))
	assert.True(t, isCNF(term))

	term = D.Apply(a).Or(P.Apply(b).And(R.Apply(h)))
	assert.False(t, isCNF(term))

	term = D.Apply(a).Or(P.Apply(b).Or(R.Apply(h)))
	assert.True(t, isCNF(term))

	term = ForAll(P, R, h)(
		Not(D.Apply(a)).Or(P.Apply(b)).
			And((R.Apply(h)).Or(D.Apply(a))))
	assert.False(t, isCNF(term))

	term = ForAll(P, R, h)(
		Not(D.Apply(a)).Or(P.Apply(b)).
			Or((R.Apply(h)).Or(D.Apply(a))))
	assert.True(t, isCNF(term))

	term = ForAll(P, R, h)(
		Exists(D, a, b)(Not(D.Apply(a)).Or(P.Apply(b))).
			Or(Exists(D, a)((R.Apply(h)).Or(D.Apply(a)))))
	assert.False(t, isCNF(term))
}

func TestPreCNFGapShape(t *testing.T) {
	x := Var("x", TypeBool)
	y := Var("y", TypeBool)
	a := Var("a", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))

	// This is intentionally not a raw TrivialNormalize no-op detector.
	assert.False(t, hasPreCNFGapShape(Not(Not(x))))
	assert.NotNil(t, prop.TrivialNormalize(Not(Not(x))))

	assert.True(t, hasPreCNFGapShape(x.Eq(y)))            // IFF
	assert.True(t, hasPreCNFGapShape(Unique(a)(a.Eq(a)))) // ∃!
	assert.True(t, hasPreCNFGapShape(ext.Cond(x, a, a)))  // COND
	assert.True(t, hasPreCNFGapShape(f.Eq(f)))            // FunEq
	assert.False(t, hasPreCNFGapShape(x.Or(Not(y))))      // ordinary pre-CNF shape
	assert.False(t, hasPreCNFGapShape(x.Imply(y).Or(Not(y))))
}

func TestCNFNormalizeCacheCollapsesPreCNFEquivalentHyps(t *testing.T) {
	defer goleak.VerifyNone(t)

	p := Var("p", TypeBool)
	q := Var("q", TypeBool)

	var preCNFCache PreCNFCache
	var tailCache ext.TermKeyPropMap
	cache := &CNFNormalizeCache{
		PreCNF: &preCNFCache,
		Tail:   &tailCache,
	}

	// Raw-distinct hypotheses that share one pre-CNF representative. The
	// prelude cache is raw-keyed, so both inputs get entries; the tail cache is
	// keyed by the pre-CNF form, so the expensive middle/tail work should share
	// one entry.
	goal := MakeProp(F, p.Imply(q), Not(p).Or(q))
	_, err := NegateGoalCNFFromPreNormalized(t.Context(), goal, cache)
	assert.NoError(t, err)
	assert.Equal(t, 2, preCNFCache.TermCacheSize(), "raw-keyed pre-CNF cache should see both hyps")
	assert.Equal(t, 1, tailCache.Size(), "pre-CNF-keyed tail cache should collapse equivalent hyps")

	_, err = NegateGoalCNFFromPreNormalized(t.Context(), goal, cache)
	assert.NoError(t, err)
	assert.Equal(t, 2, preCNFCache.TermCacheSize(), "second run should reuse pre-CNF entries")
	assert.Equal(t, 1, tailCache.Size(), "second run should reuse the shared tail entry")
}

func TestCNFRewrite(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	c := Var("c", TypeBool)
	d := Var("d", TypeBool)

	// Helper function to run CNF rewrite with timeout and check for errors
	rewrite := func(s Term) *PropWrapper {
		w, err := cnfRewriteWithTimeout(t.Context(), s)
		assert.Nil(t, err)
		return w
	}

	// Test case: a ∨ b
	// This is already in CNF, so no rewrite needed
	s := a.Or(b)
	assert.Nil(t, rewrite(s))

	// Test case: a ∧ b
	// This is already in CNF, so no rewrite needed
	s = a.And(b)
	assert.Nil(t, rewrite(s))

	// Test case: a ∨ (b ∨ a)
	// This should be rewritten to a ∨ b using OR simplification
	s = a.Or(b.Or(a))
	assertPropAlphaEqual(t, rewrite(s),
		testThm(s.Eq(a.Or(b))))

	// Test case: a ∨ (b ∧ a)
	// This should be rewritten to just a using absorption law
	// Since (a ∨ (b ∧ a)) ≡ a
	s = a.Or(b.And(a))
	assertPropAlphaEqual(t, rewrite(s),
		testThm(s.Eq(a)))

	// Test case: (a ∨ b) ∧ c
	// This is already in CNF, so no rewrite needed
	s = a.Or(b).And(c)
	assert.Nil(t, rewrite(s))

	// Test case: (a ∧ b) ∨ c
	// This should be rewritten to (c ∨ a) ∧ (c ∨ b) using distributive law
	s = a.And(b).Or(c)
	assertPropAlphaEqual(t, rewrite(s),
		testThm(s.Eq(c.Or(a).And(c.Or(b)))))

	// Test case: a ∧ (b ∨ a)
	// This should be rewritten to just a using absorption law
	// Since a ∧ (b ∨ a) ≡ a
	s = a.And(b.Or(a))
	assertPropAlphaEqual(t,
		rewrite(s),
		testThm(s.Eq(a)))

	// Test case: a ∧ (b ∨ ¬a)
	// This should be rewritten to a ∧ b since a ∧ (b ∨ ¬a) ≡ a ∧ b
	s = a.And(b.Or(Not(a)))
	assertPropAlphaEqual(t,
		rewrite(s),
		testThm(s.Eq(a.And(b))))

	// Test case: (b ∨ a) ∧ ¬a
	// This should be rewritten to ¬a ∧ b since (b ∨ a) ∧ ¬a ≡ ¬a ∧ b
	s = (b.Or(a)).And(Not(a))
	assertPropAlphaEqual(t,
		rewrite(s),
		testThm(s.Eq(Not(a).And(b))))

	// Test case: (c ∧ a) ∨ (c ∧ b) ∨ ((d ∧ a) ∨ (d ∧ b))
	// This should be rewritten to (c ∨ d) ∧ (a ∨ b) using distributive laws
	// and factoring out common terms
	s = (c.And(a)).Or(c.And(b)).Or((d.And(a)).Or(d.And(b)))
	assertPropAlphaEqual(t,
		rewrite(s),
		testThm(s.Eq((c.Or(d)).And(a.Or(b)))))

	// Test case: ∃c.∀a.((c ∧ a) ∨ (c ∧ b) ∨ ((d ∧ a) ∨ (d ∧ b)))
	// This should be rewritten to ∃c.∀a.((c ∨ d) ∧ (a ∨ b))
	// applying CNF rewrite under quantifiers
	s = Exists(c)(ForAll(a)((c.And(a)).Or(c.And(b)).Or((d.And(a)).Or(d.And(b)))))
	assertPropAlphaEqual(t,
		rewrite(s),
		testThm(s.Eq(Exists(c)(ForAll(a)((c.Or(d)).And(a.Or(b)))))))

	// The following tests check for size limits in CNF conversion
	// Create conjunctions of increasing size to test the size threshold behavior
	s0, s1 := Var("x_0", TypeBool), Var("y_0", TypeBool)

	// Test with formula below the size threshold
	// Creates s0 = x_0 ∧ x_1 ∧ ... and s1 = y_0 ∧ y_1 ∧ ...
	// Then tests s0 ∨ s1, which should succeed
	for i := 1; i < int(math.Sqrt(_CNF_SIZE_THRES)); i++ {
		s0 = s0.And(Var("x_"+TermName(strconv.Itoa(i)), TypeBool))
		s1 = s1.And(Var("y_"+TermName(strconv.Itoa(i)), TypeBool))
	}
	s = s0.Or(s1)
	_, err := cnfRewrite(context.Background(), s)
	assert.Nil(t, err)

	// Test with formula above the size threshold
	// Creates larger conjunctions that exceed the size limit
	// The conversion should fail with an error
	s0, s1 = Var("x_0", TypeBool), Var("y_0", TypeBool)
	for i := 1; i < _CNF_SIZE_THRES; i++ {
		s0 = s0.And(Var("x_"+TermName(strconv.Itoa(i)), TypeBool))
		s1 = s1.And(Var("y_"+TermName(strconv.Itoa(i)), TypeBool))
	}
	s = s0.Or(s1)
	_, err = cnfRewrite(context.Background(), s)
	assert.NotNil(t, err)

	// Test timeout functionality
	// Should terminate within reasonable time even for large formulas
	now := time.Now()
	w, err := cnfRewriteWithTimeout(t.Context(), s)
	assert.Nil(t, w)
	assert.NotNil(t, err)
	assert.Less(t, time.Since(now), 2*_CNF_REWRITE_TIMEOUT)
}

func TestInsideDenoteRewrite(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeA, TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeBool, TypeBool, TypeBool))

	// Test case: ∀z.Q(∃x.∃y.R(x, y, z), P(z))
	// This formula has a quantifier inside an argument (∃x.∃y.R(x, y, z))
	// Regular workflow cannot handle it directly
	s := ForAll(z)(Q.Apply(Exists(x, y)(R.Apply(x, y, z)), P.Apply(z)))
	w := prop.NormalizeRewriteWorkflow(s)
	assert.Nil(t, w)

	// Using insideDenoteRewrite should extract the inner quantifier:
	// ∃α_0.((α_0 = λz.∃x.∃y.R(x, y, z)) ∧ ∀z.Q(α_0(z), P(z)))
	w = insideDenoteRewrite(context.Background())(s)
	alpha0 := Var("α_0", MakeFun(TypeA, TypeBool))
	assertTermAlphaEqual(t, Rhs(w),
		Exists(alpha0)(alpha0.Eq(z.To(Exists(x, y)(R.Apply(x, y, z)))).
			And(ForAll(z)(Q.Apply(alpha0.Apply(z), P.Apply(z))))))

	// Test case with nested quantifiers: ∀z.Q(∃x.∀y.R(x, y, z), ∃y.P(y))
	// Contains inner quantified terms in both arguments of Q
	s = ForAll(z)(Q.Apply(Exists(x)(ForAll(y)(R.Apply(x, y, z))), Exists(y)(P.Apply(y))))
	w = prop.NormalizeRewriteWorkflow(s)
	assert.Nil(t, w)

	// First denote rewrite extracts the left nested quantifier
	// ∃α_0.((α_0 = λz.∃x.∀y.R(x, y, z)) ∧ ∀z.Q(α_0(z), ∃y.P(y)))
	w = insideDenoteRewrite(context.Background())(s)
	alpha0 = Var("α_0", MakeFun(TypeA, TypeBool))
	assertTermAlphaEqual(t, Rhs(w),
		Exists(alpha0)(alpha0.Eq(z.To(Exists(x)(ForAll(y)(R.Apply(x, y, z))))).
			And(ForAll(z)(Q.Apply(alpha0.Apply(z), Exists(y)(P.Apply(y)))))))

	// ∃α_0.∃ƒ_1.∃ƒ_2.∀z.∀y.∀x.
	// (((α_0(z) ∧ R(ƒ_1(z), y, z)) ∨ (¬α_0(z) ∧ ¬R(x, ƒ_2(z, x), z))) ∧ Q(α_0(z), ∃y.P(y)))
	u := prop.NormalizeRewriteWorkflow(Rhs(w))
	assert.NotNil(t, u)
	uRhs := Rhs(u)
	w = w.EqTrans(u)

	// ∃α_1.((α_1 = (∃y.P(y))) ∧
	// (∃α_0.∃ƒ_1.∃ƒ_2.∀z.∀y.∀x.
	// (((α_0(z) ∧ R(ƒ_1(z), y, z)) ∨ (¬α_0(z) ∧ ¬R(x, ƒ_2(z, x), z))) ∧ Q(α_0(z), α_1))))
	u = insideDenoteRewrite(context.Background())(Rhs(w))
	assert.NotNil(t, u)
	w = w.EqTrans(u)
	alpha1 := Var("α_1", TypeBool)
	assertTermAlphaEqual(t, Rhs(w),
		Exists(alpha1)(alpha1.Eq(Exists(y)(P.Apply(y))).
			And(Rhs(prop.EqRewrite(prop.Assume(Exists(y)(P.Apply(y)).Eq(alpha1)))(uRhs)))))

	// Continue applying workflow for further normalization
	u = prop.NormalizeRewriteWorkflow(Rhs(w))
	assert.NotNil(t, u)
	w = w.EqTrans(u)

	// Check that no more nested quantifiers remain to extract
	u = insideDenoteRewrite(context.Background())(Rhs(w))
	assert.Nil(t, u)

	// Check that no more regular rewrites are applicable
	u = prop.NormalizeRewriteWorkflow(Rhs(w))
	assert.Nil(t, u)

	///////////////////////////////////////////////////

	x = Var("x", TypeBool)
	y = Var("y", TypeBool)
	z = Var("z", TypeBool)
	Q = Var("Q", MakeFun(TypeBool, TypeBool))
	R = Var("R", MakeFun(TypeBool, TypeBool))

	// Test boolean term with nested conjunction: ∀x.∀y.¬R(x ∧ (y ∨ z))
	// Contains boolean operation nesting that needs to be extracted
	s = ForAll(x, y)(Not(R.Apply(x.And(y.Or(z)))))
	w = prop.NormalizeRewriteWorkflow(s)
	assert.Nil(t, w)

	// Extract the nested term x ∧ (y ∨ z)
	w = insideDenoteRewrite(context.Background())(s)
	alpha0 = Var("α_0", MakeFun(TypeBool, TypeBool, TypeBool))
	assertTermAlphaEqual(t, Rhs(w),
		Exists(alpha0)(alpha0.Eq(x.To(y.To(x.And(y.Or(z))))).
			And(ForAll(x, y)(Not(R.Apply(alpha0.Apply(x, y)))))))

	s = ForAll(x, y)(R.Apply(Q.Apply(x).And(Q.Apply(y.Or(z)))))
	w = prop.NormalizeRewriteWorkflow(s)
	assert.Nil(t, w)

	w = insideDenoteRewrite(context.Background())(s)
	alpha0 = Var("α_0", MakeFun(TypeBool, TypeBool, TypeBool))
	assertTermAlphaEqual(t, Rhs(w),
		Exists(alpha0)(alpha0.Eq(x.To(y.To(Q.Apply(x).And(Q.Apply(y.Or(z)))))).
			And(ForAll(x, y)(R.Apply(alpha0.Apply(x, y))))))

	// ∃α_0.∀x.∀y.
	// (((α_0(x, y) ∧ (Q(x) ∧ Q(y ∨ z))) ∨
	// (¬α_0(x, y) ∧ (¬Q(x) ∨ ¬Q(y ∨ z)))) ∧ R(α_0(x, y)))
	u = prop.NormalizeRewriteWorkflow(Rhs(w))
	assert.NotNil(t, u)
	uRhs = Rhs(u)
	w = w.EqTrans(u)

	u = insideDenoteRewrite(context.Background())(Rhs(w))
	assert.NotNil(t, u)
	w = w.EqTrans(u)
	alpha1 = Var("α_1", MakeFun(TypeBool, TypeBool))
	// (∃α_1.((α_1 = (λy.(y ∨ z))) ∧
	// (∃α_0.∀x.∀y.
	// (((α_0(x, y) ∧ (Q(x) ∧ Q(α_1(y)))) ∨
	// (¬α_0(x, y) ∧ (¬Q(x) ∨ ¬Q(α_1(y))))) ∧ R(α_0(x, y))))))
	assertTermAlphaEqual(t, Rhs(w),
		Exists(alpha1)(alpha1.Eq(y.To(y.Or(z))).
			And(Rhs(prop.EqRewrite(prop.Assume(y.To(y.Or(z)).Eq(alpha1)))(uRhs)))))

	// Continue normalization process
	u = prop.NormalizeRewriteWorkflow(Rhs(w))
	assert.NotNil(t, u)
	w = w.EqTrans(u)

	// Verify no more denote rewrites are needed
	u = insideDenoteRewrite(context.Background())(Rhs(w))
	assert.Nil(t, u)

	// Verify no more regular rewrites are needed
	u = prop.NormalizeRewriteWorkflow(Rhs(w))
	assert.Nil(t, u)

	///////////////////////////////////////////////////

	// Test denote rewrite with mixed types
	x = Var("x", TypeA)
	y = Var("y", TypeBool)
	z = Var("z", TypeBool)
	P = Var("P", MakeFun(TypeA, TypeBool))
	Q = Var("Q", MakeFun(TypeBool, TypeBool, TypeBool))

	// Term with nested quantifier in first argument: ∀z.Q(∃x.P(x), y ∧ z)
	s = ForAll(z)(Q.Apply(Exists(x)(P.Apply(x)), y.And(z)))
	w = insideDenoteRewrite(context.Background())(s)
	alpha0 = Var("α_0", TypeBool)
	assertTermAlphaEqual(t, Rhs(w),
		Exists(alpha0)(alpha0.Eq(Exists(x)(P.Apply(x))).
			And(ForAll(z)(Q.Apply(alpha0, y.And(z))))))

	// Continue normalization process
	u = prop.NormalizeRewriteWorkflow(Rhs(w))
	assert.NotNil(t, u)
	uRhs = Rhs(u)
	w = w.EqTrans(u)

	// Extract y ∧ z from the second argument
	u = insideDenoteRewrite(context.Background())(Rhs(w))
	assert.NotNil(t, u)
	w = w.EqTrans(u)

	alpha1 = Var("α_1", MakeFun(TypeBool, TypeBool))
	// ∃α_1.((α_1 = (λz.(y ∧ z))) ∧
	// (∃α_0.∃x.∀z.∀y.(((α_0 ∧ P(x)) ∨ (¬α_0 ∧ ¬P(y))) ∧
	// Q(α_0, α_1(z)))))
	assertTermAlphaEqual(t, Rhs(w),
		Exists(alpha1)(alpha1.Eq(z.To(y.And(z))).
			And(Rhs(prop.EqRewrite(prop.Assume(z.To(y.And(z)).Eq(alpha1)))(uRhs)))))

	// Complete normalization
	u = prop.NormalizeRewriteWorkflow(Rhs(w))
	assert.NotNil(t, u)
	w = w.EqTrans(u)

	// Verify no more transformations are needed
	u = insideDenoteRewrite(context.Background())(Rhs(w))
	assert.Nil(t, u)

	u = prop.NormalizeRewriteWorkflow(Rhs(w))
	assert.Nil(t, u)
}

func TestNegateGoalCNF(t *testing.T) {
	defer goleak.VerifyNone(t)
	var cnfNormalizationCache utils.Map[core.TermKey, Prop]

	// Helper function to test the negation of a goal and verify the result
	// Checks that the reconstructed theorem from the CNF is equivalent to the original goal
	verify := func(goal Prop) {
		res, err := NegateGoalCNF(t.Context(), goal, &cnfNormalizationCache)
		assert.Nil(t, err)

		hyps := make([]Term, len(res.CNF.Clauses()))
		for i, c := range res.CNF.Clauses() {
			hyps[i] = c.Term()
		}
		if res.Reconstruct == nil {
			assert.False(t, res.Thm.IsZero())
			assert.True(t, IsStronger(res.Thm, goal))
			return
		}
		assert.True(t, IsStronger(res.Reconstruct(res.CNF.RefuteProp()), goal))
		assert.NotPanics(t, func() { res.Reconstruct(testThm(F, hyps...)).AsThmCert() })

		// Check that negating the CNF clauses gives back an equivalent CNF
		res1, err := NegateGoalCNF(t.Context(), res.CNF.RefuteProp(), &cnfNormalizationCache)
		assert.Nil(t, err)
		assert.True(t, slices.EqualFunc(res.CNF.Clauses(), res1.CNF.Clauses(), (*Clause).Equivalent))

		// Test with random subsets of the hypotheses to ensure reconstruction works correctly
		if len(hyps) > 1 {
			for range 10 {
				subLen := rand.Intn(len(hyps)-1) + 1
				selectedIndices := make(utils.Set[int])
				_hyps := make([]Term, 0, subLen)
				for len(_hyps) < subLen {
					index := rand.Intn(len(hyps))
					if !selectedIndices.Has(index) {
						_hyps = append(_hyps, hyps[index])
						selectedIndices.Add(index)
					}
				}
				assert.True(t, IsStronger(res.Reconstruct(testProp(F, _hyps...)), goal))
				assert.NotPanics(t, func() { res.Reconstruct(testThm(F, _hyps...)).AsThmCert() })
			}
		}
	}

	// Helper function for cases where the goal is expected to be directly proven
	// without needing CNF refutation
	directlyProve := func(goal Prop) {
		res, err := NegateGoalCNF(t.Context(), goal, &cnfNormalizationCache)
		assert.NotNil(t, res.CNF)
		assert.Equal(t, len(res.CNF.Clauses()), 1)
		assert.True(t, res.CNF.Clauses()[0].Term().Equals(F))
		assert.Nil(t, res.Reconstruct)
		assert.Nil(t, err)
		assert.False(t, res.Thm.IsZero())
		assert.True(t, IsStronger(res.Thm, goal))
	}

	var p, q, x, y, z, P, Q, R *ext.TermWrapper
	var g, g0, g1, g2, g3 *ext.TermWrapper

	// Test direct proof of simple propositional logic goals
	p = Var("p", TypeBool)
	q = Var("q", TypeBool)
	directlyProve(testProp(F, p, q, Not(p)))
	directlyProve(testProp(F, p.Eq(Not(p)), p.Eq(F)))
	directlyProve(testProp(p.Eq(p)))
	directlyProve(testProp(p.Eq(p), p))

	// Test with first-order logic terms
	x = Var("x", TypeA)
	y = Var("y", TypeA)
	z = Var("z", TypeA)
	P = Var("P", MakeFun(TypeA, TypeBool))
	Q = Var("Q", MakeFun(TypeA, TypeBool))

	// Test various first-order logic goals
	directlyProve(testProp(P.Apply(x), P.Apply(x)))                                       // P(x) ⊢ P(x) (identity)
	directlyProve(testProp(ForAll(y)(x.Eq(y).Eq(y.Eq(x)))))                               // ⊢ ∀y.(x ≡ y) ≡ (y ≡ x) (symmetry of equality)
	directlyProve(testProp(F, Not(Q.Apply(y)), p.And(P.Apply(y)), Not(p).Or(Q.Apply(y)))) // ¬Q(y), p ∧ P(y), ¬p ∨ Q(y) ⊢ ⊥ (complex contradiction)

	// Test CNF conversion and reconstruction for more complex formulas
	verify(testProp(P.Apply(x), Not(P.Apply(x))))                                            // ¬P(x) ⊢ P(x)
	verify(testProp(P.Apply(x), Q.Apply(x), Q.Apply(y), Not(Q.Apply(x)).Or(Q.Apply(z))))     // Q(x), Q(y), ¬Q(x) ∨ Q(z) ⊢ P(x),
	verify(testProp(P.Apply(x), ForAll(x)(P.Apply(x)).And(ForAll(x)(Q.Apply(x)))))           // ∀x.P(x) ∧ ∀x.Q(x) ⊢ P(x)
	verify(testProp(ForAll(p)(ForAll(x)(P.Apply(x).Or(p)).Eq(ForAll(x)(P.Apply(x)).Or(p))))) // ⊢ ∀p.(∀x.(P(x) ∨ p) ≡ (∀x.P(x) ∨ p)) (quantifier distribution)
	verify(testProp(ForAll(x)(P.Apply(x)), Exists(x)(Not(P.Apply(x)))))
	verify(testProp(F, Exists(x)(P.Apply(x)), P.Apply(x)))                                        // ∃x.P(x), P(x) ⊢ ⊥
	verify(testProp(F, Exists(x)(P.Apply(x)), Exists(x)(Q.Apply(x))))                             // ∃x.P(x), ∃x.Q(x) ⊢ ⊥
	verify(testProp(P.Apply(x), Exists(x)(P.Apply(x)), Exists(x)(Q.Apply(x))))                    // ∃x.P(x), ∃x.Q(x) ⊢ P(x)
	verify(testProp(P.Apply(x), Exists(x)(P.Apply(x).And(Q.Apply(x))), Exists(x)(Q.Apply(x))))    // ∃x.(P(x) ∧ Q(x)), ∃x.Q(x) ⊢ P(x)
	verify(testProp(P.Apply(x), Exists(x, y)(P.Apply(x).And(Q.Apply(y))), Exists(x)(Q.Apply(x)))) // ∃x,y.(P(x) ∧ Q(y)), ∃x.Q(x) ⊢ P(x)
	verify(testProp(P.Apply(y), Exists(x)(P.Apply(x).And(Q.Apply(x).And(P.Apply(y))))))           // ∃x.(P(x) ∧ Q(x) ∧ P(y)) ⊢ P(y)

	// Test uniqueness quantifier and function properties
	g0 = Exists(x)(P.Apply(x)).And(ForAll(x, y)(P.Apply(x).And(P.Apply(y)).Imply(x.Eq(y))))
	g1 = Exists(x)(ForAll(y)(P.Apply(y).Eq(x.Eq(y))))

	verify(testProp(g0, g1))
	verify(testProp(g1, g0))
	verify(testProp(g0.Eq(g1)))

	// Test transitivity, symmetry and other properties in relations
	x = Var("x", TypeA)
	y = Var("y", TypeA)
	z = Var("z", TypeA)
	P = Var("P", MakeFun(TypeA, TypeA, TypeBool))
	Q = Var("Q", MakeFun(TypeA, TypeA, TypeBool))

	g0 = ForAll(x, y, z)(P.Apply(x, y).And(P.Apply(y, z)).Imply(P.Apply(x, z)))
	g1 = ForAll(x, y, z)(Q.Apply(x, y).And(Q.Apply(y, z)).Imply(Q.Apply(x, z)))
	g2 = ForAll(x, y)(Q.Apply(x, y).Imply(Q.Apply(y, x)))
	g3 = ForAll(x, y)(P.Apply(x, y).Or(Q.Apply(x, y)))
	g = ForAll(x, y)(P.Apply(x, y)).Or(ForAll(x, y)(Q.Apply(x, y)))
	verify(testProp(g, g0, g1, g2, g3))

	// Test functional properties and existential instantiation
	x = Var("x", TypeA)
	y = Var("y", TypeA)
	z = Var("z", TypeA)
	P = Var("P", MakeFun(TypeA, TypeA, TypeA))
	Q = Var("Q", MakeFun(TypeA, TypeA, TypeBool))

	g0 = ForAll(x, y, z)(P.Apply(x, P.Apply(y, z)).Eq(P.Apply(P.Apply(x, y), z)))
	g1 = ForAll(x, y)(P.Apply(x, y).Eq(P.Apply(y, x)))
	g2 = ForAll(x, y)(Q.Apply(x, y).Eq(Exists(z)(y.Eq(P.Apply(z, x)))))
	g = ForAll(x, y, z)(Q.Apply(x, y).Imply(Q.Apply(x, P.Apply(z, y))))
	verify(testProp(g, g0, g1, g2))

	// Test with complex quantifiers and function applications
	x = Var("x", TypeA)
	y = Var("y", TypeA)
	P = Var("P", MakeFun(TypeA, TypeBool))
	R = Var("R", MakeFun(TypeA, TypeA, TypeBool))
	Q = Var("Q", MakeFun(TypeBool, TypeBool, TypeBool))

	g = Q.Apply(ForAll(x, y)(R.Apply(x, y)), Exists(y)(P.Apply(y)))
	verify(testProp(F, g))
}

// TestNegateGoalCNF_ExistsUnderLambdaAlphaDuplication guards a CNF-pipeline
// invariant: for any bool-typed atom H, the sequent `H, ¬H ⊢ ⊥` must collapse
// to the single-clause CNF `[⊥]` regardless of H's internal structure — that
// is the `directlyProve` invariant elsewhere in this file. Unit resolution on
// `H` and `¬H` should fire before any Skolem-abstraction pass has a chance to
// rewrite the two occurrences into non-complementary literals.
//
// This test isolates the class of H that breaks this invariant AT THE CNF
// LEVEL: an ∃ under a λ that appears inside an argument to an outer function
// (`set_comprehension` here — but the wrapper is a plain `Var`, so the test doesn't depend
// on the actual set_comprehension constant's definition; any bool-returning applied-λ
// argument reproduces the pattern).
//
// Root cause: `insideDenoteRewrite` (this file, line ~295) calls
// `prop.ExistsDenoteRewrite(s)(t)` at each `InsideQuantifierBoolOp` site, minting
// a fresh α Skolem-abstraction symbol per occurrence via `RenameToAvoid(s, t)`
// — no memoization across sites in the same term. When `λg. ∃y. R(g, y)` appears
// both positively and negatively, the positive occurrence gets `α₁` and the
// negative gets `α₀` (both hyps mint α₀ independently; the goal-level merge
// renames the second apart via SubscriptExistsVars), plus independent Skolem
// functions `ƒ₀`, `ƒ₁` for the ∃y itself. α₀ and α₁ are logically identical
// (both `⇔ ∃y. R(g, y)`) but syntactically distinct Skolem constants, so unit
// resolution can't derive ⊥ from the CNF alone.
//
// The fix deliberately does NOT touch the CNF (that would shift the
// cnf_proofs cache key of every stored certificate carrying such hyps):
// the ALPHA-MERGE chain (alpha_merge.go) derives the missing symbol
// equality at refuter init and the goal closes there.
//
// Corpus impact: an image of an image and an insert over a union both hit this via
// `def_expand image` / `set_tac` unfolding union into `λ. ∃y. comprehension_spec(...)`
// shape. Their NESTED denote structure is only partially covered by the v1
// merge (see TestDeriveAlphaMergeChain_Nested); the navigation workaround
// (keep the set-application constructor symbolic + load the membership lemma as ⇔-hyp,
// then `def_expand set_member`) remains valid for those.
//
// Test structure: baseline shapes (collapse to [⊥]) + the α-duplication
// shape (pinned to its 8-clause CNF form, closed at the refuter level).
func TestNegateGoalCNF_ExistsUnderLambdaAlphaDuplication(t *testing.T) {
	defer goleak.VerifyNone(t)
	var cache utils.Map[core.TermKey, Prop]

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	g := Var("g", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeA, TypeBool))
	// set_comprehension : (A→bool) → (A→bool). A plain Var — the test does not depend on
	// the actual set_comprehension constant's definition, only on the CNF pipeline's
	// treatment of `V(λ, x)`-shaped applied terms.
	setComprehension := Var("set_comprehension",
		MakeFun(MakeFun(TypeA, TypeBool), MakeFun(TypeA, TypeBool)))

	// mustCollapseToBottom asserts the `directlyProve` invariant: for the
	// sequent `hyp1 ⊢ ⊥` (concl = F), `NegateGoalCNF` produces a single-clause
	// CNF whose sole clause is `⊥` — i.e. the pipeline pre-detects the
	// contradiction before refutation search.
	mustCollapseToBottom := func(t *testing.T, atom Term) {
		t.Helper()
		goal := MakeProp(F, atom, Not(atom))
		res, err := NegateGoalCNF(t.Context(), goal, &cache)
		assert.NoError(t, err)
		assert.NotNil(t, res.CNF)
		assert.Equal(t, 1, len(res.CNF.Clauses()),
			"expected single-clause CNF (the ⊥ collapse), got %d clauses:\n%s",
			len(res.CNF.Clauses()), res.CNF)
		if len(res.CNF.Clauses()) == 1 {
			assert.True(t, res.CNF.Clauses()[0].Term().Equals(F),
				"expected sole clause to be ⊥, got: %s", res.CNF.Clauses()[0])
		}
	}

	// (A) Baseline: opaque atom, no λ. Must collapse.
	//     H = set_comprehension(P, x) where P is a plain Var. This is the classical
	//     `V(P, x), ¬V(P, x) ⊢ ⊥` shape — first-order unit resolution.
	t.Run("baseline_opaque_atom", func(t *testing.T) {
		H := setComprehension.Apply(P).Apply(x)
		mustCollapseToBottom(t, H)
	})

	// (B) Shared λ, no ∃. Must collapse. This variant establishes that the
	//     mere presence of a λ under the outer function does not trigger the
	//     bug — the CNF pipeline handles `V(λg. g = y, x)` cleanly.
	t.Run("shared_lambda_no_exists", func(t *testing.T) {
		body := g.Eq(y) // λg. g = y
		Plambda := g.To(body)
		H := setComprehension.Apply(Plambda).Apply(x)
		mustCollapseToBottom(t, H)
	})

	// (C) Two distinctly-built α-equivalent λ terms. Must collapse. This
	//     variant falsifies the "distinct-internal-var-with-same-
	//     display-name" hypothesis: even when the λ-terms are constructed
	//     from independently-created `VarTerm` pointers under the same name,
	//     α-equivalence holds and the CNF pipeline resolves them.
	t.Run("distinctly_built_alpha_identical_lambdas", func(t *testing.T) {
		g0 := Var("g", TypeA)
		body0 := g0.Eq(y)
		P0 := g0.To(body0)

		g1 := Var("g", TypeA) // same name, different VarTerm identity
		body1 := g1.Eq(y)
		P1 := g1.To(body1)

		// Sanity — confirm α-equivalence at the term level before probing CNF.
		assert.True(t, P0.Core().AlphaEquals(P1.Core()),
			"independently-built λg. g = y terms must be α-equal")

		Hpos := setComprehension.Apply(P0).Apply(x)
		Hneg := setComprehension.Apply(P1).Apply(x)
		goal := MakeProp(F, Hpos, Not(Hneg))
		res, err := NegateGoalCNF(t.Context(), goal, &cache)
		assert.NoError(t, err)
		assert.Equal(t, 1, len(res.CNF.Clauses()),
			"expected single-clause CNF for α-equiv λ atoms, got %d clauses:\n%s",
			len(res.CNF.Clauses()), res.CNF)
		if len(res.CNF.Clauses()) == 1 {
			assert.True(t, res.CNF.Clauses()[0].Term().Equals(F),
				"expected sole clause to be ⊥, got: %s", res.CNF.Clauses()[0])
		}
	})

	// (D) The α-duplication shape: `λg. ∃y. R(g, y)` under an outer
	//     application, appearing both positively and negatively.
	//     `insideDenoteRewrite` mints α₀ for one occurrence and α₁ for the
	//     other, so the CNF does NOT collapse to [⊥] — and that is BY DESIGN
	//     permanent: fixing it at the CNF level would change the clause-set
	//     identity of every stored certificate carrying such hyps (the
	//     cnf_proofs cache key), the exact trap the FUNEXT history warns
	//     about. Instead the ALPHA-MERGE init chain (alpha_merge.go) derives
	//     the missing symbol equality at REFUTER init from the clauses
	//     below, so the goal closes there — see TestDeriveAlphaMergeChain
	//     (this package) for the chain and TestAlphaMergeRefutesGoal
	//     (prover/solver/refuter) for the end-to-end refutation.
	//
	//     This subtest pins the CNF-level shape the chain consumes: 8
	//     clauses, two α families. If the pipeline ever changes this shape,
	//     the merge detection must be revalidated.
	t.Run("lambda_with_exists_alpha_duplication_shape", func(t *testing.T) {
		body := Exists(y)(R.Apply(g).Apply(y)) // λ-body = ∃y. R(g, y)
		Plambda := g.To(body)
		H := setComprehension.Apply(Plambda).Apply(x)
		goal := MakeProp(F, H, Not(H))
		res, err := NegateGoalCNF(t.Context(), goal, &cache)
		assert.NoError(t, err)
		assert.NotNil(t, res.CNF)
		assert.Equal(t, 8, len(res.CNF.Clauses()),
			"α-duplication CNF shape drifted — revalidate the ALPHA-MERGE "+
				"detection (alpha_merge.go) against the new shape:\n%s", res.CNF)
	})
}

// TestSelfConsistentGoal guards the cnfNormalizeCache order-dependence fix.
// A CNF-refute proof must store its goal in self-consistent form, so re-normalizing it WITHOUT a
// cache reproduces the same refutation regardless of how the shared cache was
// warmed. Without this, an existential hyp's Skolem-witness naming follows
// whichever alpha-variant first populated the cache, and a cold replay diverges
// from the stored cert (a replay false-fail on the numeral-product clauses).
func TestSelfConsistentGoal(t *testing.T) {
	defer goleak.VerifyNone(t)
	ctx := t.Context()

	R := Var("R", MakeFun(TypeA, TypeA, TypeBool))
	a, b := Var("a", TypeA), Var("b", TypeA)
	m, n := Var("m", TypeA), Var("n", TypeA)
	x, y := Var("x", TypeA), Var("y", TypeA)

	univ := ForAll(x, y)(R.Apply(x, y))                                  // ∀x.∀y.R(x,y)
	goalA := MakeProp(F, Exists(a)(Exists(b)(Not(R.Apply(a, b)))), univ) // ∃a.∃b.¬R(a,b), ∀… ⊢ ⊥
	goalM := MakeProp(F, Exists(m)(Exists(n)(Not(R.Apply(m, n)))), univ) // alpha-variant ∃m.∃n.…

	// Warm a shared cache with the m-variant so its representative naming is m,n;
	// then normalize the a-variant goal through the SAME (now warm) cache.
	var pre PreCNFCache
	var tail ext.TermKeyPropMap
	warm := &CNFNormalizeCache{PreCNF: &pre, Tail: &tail}
	_, err := NegateGoalCNFFromPreNormalized(ctx, goalM, warm)
	assert.NoError(t, err)
	res, err := NegateGoalCNFFromPreNormalized(ctx, goalA, warm)
	assert.NoError(t, err)

	// (1) The stored self-consistent goal is alpha-equal to the input goal (so the cnfKey
	// lookup and the final IsStronger check are unaffected).
	assert.True(t, res.SelfConsistentGoal.AlphaEquals(goalA),
		"SelfConsistentGoal must be alpha-equal to the input goal")

	// (2) Self-consistency: re-normalizing SelfConsistentGoal with NO cache reproduces the
	// warm refutation — this is what makes replay cache-order-independent.
	fresh, err := NegateGoalCNFFromPreNormalized(ctx, res.SelfConsistentGoal, nil)
	assert.NoError(t, err)
	assert.True(t, fresh.CNF.RefuteProp().AlphaEquals(res.CNF.RefuteProp()),
		"no-cache normalization of SelfConsistentGoal must reproduce the warm CNF")

	// (3) Name-faithfulness of the cache itself: the warm-cache result for the
	// α-variant must EQUAL its cold result. Historically the α-keyed cache hit
	// spliced in the m-variant's representative naming (warm ≠ cold — the
	// divergence SelfConsistentGoal papered over at the goal level, and the
	// residual LHS/RHS naming split inside the per-hyp equation that still
	// broke stored-proof self-consistency: the ẋ₀/ẋʹ₀ row of real_construction.AddSym). The
	// name-faithful hit guards (NormalizeTermNameFaithful + the tail-cache
	// Lhs-Equals check) eliminate the divergence at the source: an α-variant
	// recomputes with its OWN naming instead of inheriting the resident
	// entry's.
	raw, err := NegateGoalCNFFromPreNormalized(ctx, goalA, nil)
	assert.NoError(t, err)
	assert.True(t, raw.CNF.RefuteProp().AlphaEquals(res.CNF.RefuteProp()),
		"name-faithful cache: warm-cache CNF of an α-variant must match its cold CNF")

	// (4) Exact-name reuse still shares: the m-variant itself re-normalized
	// through the warm cache reproduces its own warm result (the cache's
	// raison d'être is unchanged for verbatim-equal hyps).
	resM, err := NegateGoalCNFFromPreNormalized(ctx, goalM, warm)
	assert.NoError(t, err)
	coldM, err := NegateGoalCNFFromPreNormalized(ctx, goalM, nil)
	assert.NoError(t, err)
	assert.True(t, resM.CNF.RefuteProp().AlphaEquals(coldM.CNF.RefuteProp()),
		"exact-name warm hit must agree with the cold result")
}

// TestNegateGoalCNFFromPreNormalized_IndependentWitnessIsAConstant: the
// prelude-split pipeline on `∀x.(M(x) ⇒ M'(x)), ∀x.(N(x) ⇒ N'(x)) ⊢
// ∀x.((∃m n. M(m) ∧ N(n) ∧ x = h(m, n)) ⇒ ∃m n. M'(m) ∧ N'(n) ∧ x =
// h(m, n))` gives the antecedent's witnesses as Skolem constants. The
// prelude's prenex puts the consequent's ∀m.∀n above the antecedent's
// ∃m.∃n in the negated conclusion; Skolemized there, the witnesses were
// functions ƒ(m, n) of universals they never meet, and the refuter
// nested them without end (the set driver's product-set inclusion
// under a record projection).
func TestNegateGoalCNFFromPreNormalized_IndependentWitnessIsAConstant(t *testing.T) {
	defer goleak.VerifyNone(t)

	x, m, n := Var("x", TypeA), Var("m", TypeA), Var("n", TypeA)
	M, M1 := Var("M", MakeFun(TypeA, TypeBool)), Var("M'", MakeFun(TypeA, TypeBool))
	N, N1 := Var("N", MakeFun(TypeA, TypeBool)), Var("N'", MakeFun(TypeA, TypeBool))
	h := Var("h", MakeFun(TypeA, TypeA, TypeA))
	products := func(P, Q *ext.TermWrapper) *ext.TermWrapper {
		return Exists(m, n)(P.Apply(m).And(Q.Apply(n)).And(x.Eq(h.Apply(m, n))))
	}
	goal := MakeProp(
		ForAll(x)(products(M, N).Imply(products(M1, N1))),
		ForAll(x)(M.Apply(x).Imply(M1.Apply(x))),
		ForAll(x)(N.Apply(x).Imply(N1.Apply(x))))

	var pre PreCNFCache
	var tail ext.TermKeyPropMap
	res, err := NegateGoalCNFFromPreNormalized(t.Context(), goal, &CNFNormalizeCache{PreCNF: &pre, Tail: &tail})
	require.NoError(t, err)
	require.NotNil(t, res.CNF)
	for v := range res.CNF.GroundVars().Iter() {
		assert.False(t, strings.HasPrefix(string(v.Name()), utils.F_HOOK),
			"the antecedent's witness %s is a Skolem function; the CNF:\n%s", v.Name(), res.CNF)
	}
	// The antecedent's three clauses are ground: M(m₀), N(n₀), x₀ = h(m₀, n₀).
	ground := 0
	for _, c := range res.CNF.Clauses() {
		if vars, _ := DecomposesFORALL(c.Term()); vars.Empty() {
			ground++
		}
	}
	assert.Equal(t, 3, ground, "the CNF:\n%s", res.CNF)
}

// The denoting stage reads its context before each round, not only once
// they have all run: a context that ends during the second round stops
// the stage there, with nothing returned, though the third round has a
// rewrite to make.
func TestDenoteRoundsStopsBetweenRounds(t *testing.T) {
	a := Var("a", TypeBool)
	nested := func(depth int) *ext.TermWrapper {
		s := a
		for range depth {
			s = Not(Not(s))
		}
		return s
	}
	// One round strips one double negation.
	strip := func(calls *int, after func()) prop.Rewrite {
		return func(s Term) *PropWrapper {
			*calls++
			if after != nil {
				after()
			}
			return prop.DoubleNegRewrite(s)
		}
	}

	calls := 0
	w := denoteRounds(context.Background(), prop.Refl(nested(4)), strip(&calls, nil))
	require.NotNil(t, w)
	assertTermAlphaEqual(t, Rhs(w), a)
	assert.Equal(t, 5, calls, "four rounds that rewrite, and the one that finds nothing left")

	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	calls = 0
	w = denoteRounds(ctx, prop.Refl(nested(4)), strip(&calls, func() {
		if calls == 2 {
			cancel()
		}
	}))
	assert.Nil(t, w, "a stage its context ended has produced nothing to keep")
	assert.Equal(t, 2, calls, "no round starts once the context is done")

	// The last round's "nothing left" is no verdict once the context is
	// done: a round the context ended has not read its whole term.
	ctx, cancel = context.WithCancel(context.Background())
	defer cancel()
	calls = 0
	w = denoteRounds(ctx, prop.Refl(nested(1)), strip(&calls, func() {
		if calls == 2 {
			cancel()
		}
	}))
	assert.Nil(t, w)
	assert.Equal(t, 2, calls)
}
