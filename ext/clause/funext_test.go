package clause

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// TestFunextFromUnitEq: ∀x. f(x) = g(x)  →  ⊢ f = g (non-bool result type).
func TestFunextFromUnitEq(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	f := Var("f", MakeFun(TypeA, TypeB))
	g := Var("g", MakeFun(TypeA, TypeB))

	c := MakeClause(ForAll(x)(f.Apply(x).Eq(g.Apply(x))))
	thm := FunextFromUnitEq(c)
	require.NotNil(t, thm)
	assert.True(t, thm.Conclusion().AlphaEquals(Eq(f, g)),
		"conclusion must be the contracted equality, got %s",
		ext.PrintTerm(thm.Conclusion()))
	require.Equal(t, 1, thm.NumHyps())
	assert.True(t, thm.Hyp(0).AlphaEquals(c.Term()))
}

// TestFunextFromUnitEq_MultiArg: two binders contract iteratively.
func TestFunextFromUnitEq_MultiArg(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeB)
	f := Var("f", MakeFun(TypeA, TypeB, TypeInd))
	g := Var("g", MakeFun(TypeA, TypeB, TypeInd))

	c := MakeClause(ForAll(x, y)(f.Apply(x, y).Eq(g.Apply(x, y))))
	thm := FunextFromUnitEq(c)
	require.NotNil(t, thm)
	assert.True(t, thm.Conclusion().AlphaEquals(Eq(f, g)))
}

// TestFunextFromUnitEq_Declines: shapes the rule must not fire on, and
// shapes where the builder returns a PARTIALLY contracted (λ-sided)
// equality — funextContract's partial contraction, which the
// alpha-bridge extension uses — that the LambdaFreeEqSides caller
// filter rejects.
// deriveInitFunext's enrichment scope is the builder+filter composition,
// so both halves are pinned here.
func TestFunextFromUnitEq_Declines(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	f := Var("f", MakeFun(TypeA, TypeB))
	g := Var("g", MakeFun(TypeA, TypeA, TypeB))
	h := Var("h", TypeB)

	// Ground unit equality (no ∀ prefix): nothing to contract.
	assert.Nil(t, FunextFromUnitEq(MakeClause(f.Apply(x).Eq(h))))

	// Binder not the trailing argument on the right side: the left side
	// η-contracts, the right keeps its λ — a partial form the init-funext
	// filter rejects (only the alpha-bridge consumes those).
	partial := FunextFromUnitEq(
		MakeClause(ForAll(x)(f.Apply(x).Eq(g.Apply(x, x)))))
	require.NotNil(t, partial)
	assert.False(t, LambdaFreeEqSides(partial.ConclClause()),
		"partially contracted result must be rejected by the caller filter")
	l, r, ok := MatchesEQ(partial.ConclClause().EffectiveBody())
	require.True(t, ok)
	assert.True(t, l.AlphaEquals(Term(f)) || r.AlphaEquals(Term(f)),
		"the contractible side must have η-contracted to f, got %s = %s",
		ext.PrintTerm(l), ext.PrintTerm(r))

	// Binder free in the function part on both sides: Abs-only on both —
	// λ-sided, filter-rejected (when the trivial identity doesn't collapse
	// the clause entirely first).
	noEta := FunextFromUnitEq(
		MakeClause(ForAll(x)(g.Apply(x, x).Eq(g.Apply(x, x)))))
	if noEta != nil {
		assert.False(t, LambdaFreeEqSides(noEta.ConclClause()))
	}
}

// TestFunextFromIffPair: the set-typed case — the two pointwise implication
// clauses FunEqRewrite+IffToOr leave for `s = e : A→bool` recombine to the
// unit equality clause.
func TestFunextFromIffPair(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	s := Var("s", MakeFun(TypeA, TypeBool))
	e := Var("e", MakeFun(TypeA, TypeBool))

	// The exact shapes observed in the CNF debug probe:
	//   ∀ẋ.(e(ẋ) ∨ ¬s(ẋ)) and ∀ẋ.(s(ẋ) ∨ ¬e(ẋ))
	c0 := MakeClause(ForAll(x)(e.Apply(x).Or(Not(s.Apply(x)))))
	c1 := MakeClause(ForAll(x)(s.Apply(x).Or(Not(e.Apply(x)))))

	thm := FunextFromIffPair(c0, c1)
	require.NotNil(t, thm)
	got := thm.Conclusion()
	assert.True(t,
		got.AlphaEquals(Eq(e, s)) || got.AlphaEquals(Eq(s, e)),
		"conclusion must be the contracted set equality, got %s",
		ext.PrintTerm(got))
	assert.Equal(t, 2, thm.NumHyps())

	// Symmetric argument order must also fire.
	assert.NotNil(t, FunextFromIffPair(c1, c0))
}

// TestFunextFromIffPair_Declines: non-complementary pairs must not fire.
func TestFunextFromIffPair_Declines(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	s := Var("s", MakeFun(TypeA, TypeBool))
	e := Var("e", MakeFun(TypeA, TypeBool))
	q := Var("q", MakeFun(TypeA, TypeBool))

	c0 := MakeClause(ForAll(x)(e.Apply(x).Or(Not(s.Apply(x)))))
	// Wrong partner: mentions q, not the complement of c0.
	cq := MakeClause(ForAll(x)(q.Apply(x).Or(Not(e.Apply(x)))))
	assert.Nil(t, FunextFromIffPair(c0, cq))

	// Same clause twice.
	assert.Nil(t, FunextFromIffPair(c0, c0))

	// Both literals positive.
	cp := MakeClause(ForAll(x)(s.Apply(x).Or(e.Apply(x))))
	assert.Nil(t, FunextFromIffPair(c0, cp))
}

// TestFunextFromIffPair_BinderOrder: contraction follows the application
// spine, not the ∀-prefix order. ForAllConclFreeVars orders the prefix by
// naming, so a resolvent like ∀g.∀f.(a(f,g) ∨ ¬b(f,g)) arrives with the
// binder order reversed w.r.t. the spine a(f)(g); the recombine must still
// contract to a = b. (This is the shape the ALPHA-MERGE chain feeds it for
// nested, function-parameterized denote symbols — see alpha_merge.go.)
func TestFunextFromIffPair_BinderOrder(t *testing.T) {
	defer goleak.VerifyNone(t)

	g := Var("g", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	a := Var("a", MakeFun(MakeFun(TypeA, TypeA), TypeA, TypeBool))
	b := Var("b", MakeFun(MakeFun(TypeA, TypeA), TypeA, TypeBool))

	A := a.Apply(f, g)
	B := b.Apply(f, g)
	for _, order := range [][]*ext.TermWrapper{{g, f}, {f, g}} {
		quantify := func(body *ext.TermWrapper) Term {
			t := Term(body)
			for i := len(order) - 1; i >= 0; i-- {
				t = ForAll(order[i])(t)
			}
			return t
		}
		c0 := MakeClause(quantify(B.Or(Not(A))))
		c1 := MakeClause(quantify(A.Or(Not(B))))
		thm := FunextFromIffPair(c0, c1)
		require.NotNil(t, thm, "binder order %v must recombine", order)
		got := thm.Conclusion()
		assert.True(t,
			got.AlphaEquals(Eq(a, b)) || got.AlphaEquals(Eq(b, a)),
			"conclusion must be the contracted equality, got %s",
			ext.PrintTerm(got))
	}
}

// TestFunextRecipeRoundtrip: the FUNEXT recipe serializes, deserializes, and
// reconstructs the same clause thm (the replay path stored certificates use).
func TestFunextRecipeRoundtrip(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	s := Var("s", MakeFun(TypeA, TypeBool))
	e := Var("e", MakeFun(TypeA, TypeBool))

	c0 := MakeClause(ForAll(x)(e.Apply(x).Or(Not(s.Apply(x)))))
	c1 := MakeClause(ForAll(x)(s.Apply(x).Or(Not(e.Apply(x)))))
	thm := FunextFromIffPair(c0, c1)
	require.NotNil(t, thm)

	b := ext.NewPoolBuilder()
	pb := SerializeClauseThm(thm, b)
	r := ext.NewPoolReader(b.Pool(), loadConstMeta)
	back := DeserializeClauseThm(pb, r)
	require.NotNil(t, back)
	assert.True(t, back.Conclusion().AlphaEquals(thm.Conclusion()))
	assert.Equal(t, thm.NumHyps(), back.NumHyps())
}

// TestFunextFromIffPair_Context: the pointwise pair of a set equality
// under a condition — the two clauses FunEqRewrite + IffToOr leave for
// `C ⇒ s = e : A→bool`, each carrying the condition's literal — recombines
// to the equality under that literal, `(e = s) ∨ ¬C`, which stays a
// 2-literal clause (the bool ∀-iff the normalizer would re-extensionalize
// it to is not disjunctive). A positive context literal exercises the
// double-negation step of restoring it.
func TestFunextFromIffPair_Context(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	s := Var("s", MakeFun(TypeA, TypeBool))
	e := Var("e", MakeFun(TypeA, TypeBool))
	C := Var("C", TypeBool)
	D := Var("D", TypeBool)

	for _, context := range []Term{Not(C), D} {
		c0 := MakeClause(ForAll(x)(Or(context, e.Apply(x), Not(s.Apply(x)))))
		c1 := MakeClause(ForAll(x)(Or(context, s.Apply(x), Not(e.Apply(x)))))
		thm := FunextFromIffPair(c0, c1)
		require.NotNil(t, thm, "context %s", ext.PrintTerm(context))
		got := thm.Conclusion()
		assert.True(t,
			got.AlphaEquals(Or(Eq(e, s), context)) || got.AlphaEquals(Or(Eq(s, e), context)),
			"conclusion must be the equality under the context literal, got %s",
			ext.PrintTerm(got))
		assert.Equal(t, 2, thm.NumHyps())
		assert.Equal(t, 2, thm.ConclClause().EffectiveNumLits())
		assert.True(t, LambdaFreeEqSides(thm.ConclClause()))
		assert.NotNil(t, FunextFromIffPair(c1, c0))
	}
}

// TestFunextFromIffPair_QuantifiedContext: a binder the context mentions
// is not contracted over — `∀y x. ¬R(y) ∨ e(y, x) ∨ ¬s(y, x)` and its
// complement recombine to `∀y. (e(y) = s(y)) ∨ ¬R(y)`.
func TestFunextFromIffPair_QuantifiedContext(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeB)
	s := Var("s", MakeFun(TypeB, TypeA, TypeBool))
	e := Var("e", MakeFun(TypeB, TypeA, TypeBool))
	R := Var("R", MakeFun(TypeB, TypeBool))

	c0 := MakeClause(ForAll(y, x)(Or(Not(R.Apply(y)), e.Apply(y, x), Not(s.Apply(y, x)))))
	c1 := MakeClause(ForAll(y, x)(Or(Not(R.Apply(y)), s.Apply(y, x), Not(e.Apply(y, x)))))
	thm := FunextFromIffPair(c0, c1)
	require.NotNil(t, thm)
	got := thm.Conclusion()
	es := Or(e.Apply(y).Eq(s.Apply(y)), Not(R.Apply(y)))
	se := Or(s.Apply(y).Eq(e.Apply(y)), Not(R.Apply(y)))
	assert.True(t,
		got.AlphaEquals(ForAll(y)(es)) || got.AlphaEquals(ForAll(y)(se)),
		"conclusion must keep the context's binder, got %s", ext.PrintTerm(got))
	assert.True(t, LambdaFreeEqSides(thm.ConclClause()))
}

// TestFunextFromIffPair_ContextDeclines: a context literal that mentions
// the only binder is no condition on a function equality, and two
// clauses under different conditions are no pair.
func TestFunextFromIffPair_ContextDeclines(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	s := Var("s", MakeFun(TypeA, TypeBool))
	e := Var("e", MakeFun(TypeA, TypeBool))
	D := Var("D", MakeFun(TypeA, TypeBool))
	C := Var("C", TypeBool)
	C1 := Var("C₁", TypeBool)

	// ∀x. ¬D(x) ∨ e(x) ∨ ¬s(x): the context's binder is the pair's.
	c0 := MakeClause(ForAll(x)(Or(Not(D.Apply(x)), e.Apply(x), Not(s.Apply(x)))))
	c1 := MakeClause(ForAll(x)(Or(Not(D.Apply(x)), s.Apply(x), Not(e.Apply(x)))))
	assert.Nil(t, FunextFromIffPair(c0, c1))

	// Different conditions.
	c0 = MakeClause(ForAll(x)(Or(Not(C), e.Apply(x), Not(s.Apply(x)))))
	c1 = MakeClause(ForAll(x)(Or(Not(C1), s.Apply(x), Not(e.Apply(x)))))
	assert.Nil(t, FunextFromIffPair(c0, c1))
}

// TestFunextFromUnitEq_Context: the one pointwise clause of a function
// equality under a condition, `∀x. ¬C ∨ f(x) = g(x)`, recombines to
// `(f = g) ∨ ¬C`.
func TestFunextFromUnitEq_Context(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	f := Var("f", MakeFun(TypeA, TypeB))
	g := Var("g", MakeFun(TypeA, TypeB))
	C := Var("C", TypeBool)

	c := MakeClause(ForAll(x)(Not(C).Or(f.Apply(x).Eq(g.Apply(x)))))
	thm := FunextFromUnitEq(c)
	require.NotNil(t, thm)
	assert.True(t, thm.Conclusion().AlphaEquals(Or(Eq(f, g), Not(C))),
		"conclusion must be the equality under the context literal, got %s",
		ext.PrintTerm(thm.Conclusion()))
	require.Equal(t, 1, thm.NumHyps())
	assert.True(t, thm.Hyp(0).AlphaEquals(c.Term()))

	// The equality's binder free in the context: nothing to contract over.
	D := Var("D", MakeFun(TypeA, TypeBool))
	assert.Nil(t, FunextFromUnitEq(
		MakeClause(ForAll(x)(Not(D.Apply(x)).Or(f.Apply(x).Eq(g.Apply(x)))))))
}

// TestFunextDerivedClauseIsNotItsInput: the derived `f = g` is a clause of
// its own. Clause identity does not extensionalize — FunEqRewrite is the
// pre-CNF pipeline's step — so at a non-bool codomain the unit equality
// and the pointwise clause it came from have different keys. Were they
// one key, the refuter would skip the derivation as an initial clause,
// and FUNEXT would be dead for functions into a non-bool type (a
// bool-valued function's pointwise form is an iff pair, which no single
// clause can be, so the set case was never at risk).
func TestFunextDerivedClauseIsNotItsInput(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	f := Var("f", MakeFun(TypeA, TypeB))
	g := Var("g", MakeFun(TypeA, TypeB))

	pointwise := MakeClause(ForAll(x)(f.Apply(x).Eq(g.Apply(x))))
	thm := FunextFromUnitEq(pointwise)
	require.NotNil(t, thm)
	derived := thm.ConclClause()
	assert.False(t, derived.Equivalent(pointwise),
		"the derived equality must not share its input's key")
	require.Len(t, derived.components, 1)
	component := derived.components[0]
	assert.True(t, component.AlphaEquals(Eq(f, g)) || component.AlphaEquals(Eq(g, f)),
		"the component is the equality itself, not its pointwise form: %s",
		ext.PrintTerm(component))
}

// TestNamingEqSides: the naming shape is a λ-abstraction against a
// VARIABLE, the contracted form of a hypothesis that names a function
// value. A constant against a λ-abstraction is a definition: the set
// driver's residence rule `∀s x. set_comprehension(s, x) ⇔ s(x)`
// contracts to `set_comprehension = λs. s`, which recorded as a unit
// equality unfolds the constant wherever the search spells it. A
// variable standing in its own value — commutativity `∀x y. q(x, y) =
// q(y, x)` contracted to `q = λx y. q(y, x)` — is a rewrite that makes
// its own redexes. A λ-free equality is LambdaFreeEqSides's shape and
// replaces its sources.
func TestNamingEqSides(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	e := Var("e", MakeFun(TypeA, TypeB))
	f := Var("f", MakeFun(TypeA, TypeB))
	g := Var("g", MakeFun(TypeB, TypeB))

	// ∀x. e(x) = g(f(x)) contracts to e = λx. g(f(x)): a variable names a value.
	naming := FunextFromUnitEq(MakeClause(ForAll(x)(e.Apply(x).Eq(g.Apply(f.Apply(x))))))
	require.NotNil(t, naming)
	assert.True(t, NamingEqSides(naming.ConclClause()), "got %s", ext.PrintTerm(naming.Conclusion()))
	assert.False(t, LambdaFreeEqSides(naming.ConclClause()))

	// ∀x w. q(x, w) = q(w, x) contracts to q = λx w. q(w, x): q stands in
	// its own value, not a naming.
	q := Var("q", MakeFun(TypeA, TypeA, TypeA))
	w := Var("w", TypeA)
	commute := FunextFromUnitEq(MakeClause(ForAll(x, w)(q.Apply(x, w).Eq(q.Apply(w, x)))))
	require.NotNil(t, commute)
	assert.False(t, NamingEqSides(commute.ConclClause()), "got %s", ext.PrintTerm(commute.Conclusion()))
	assert.False(t, LambdaFreeEqSides(commute.ConclClause()))

	// ∀x. e(x) = f(x) contracts to e = f: λ-free, not a naming.
	plain := FunextFromUnitEq(MakeClause(ForAll(x)(e.Apply(x).Eq(f.Apply(x)))))
	require.NotNil(t, plain)
	assert.True(t, LambdaFreeEqSides(plain.ConclClause()))
	assert.False(t, NamingEqSides(plain.ConclClause()))

	// The residence rule of set_comprehension as the two clauses of its
	// ⇔ contracts to set_comprehension = λs. s: a constant's definition.
	setT := MakeFun(TypeA, TypeBool)
	scT := MakeFun(setT, TypeA, TypeBool)
	sc := ext.WrapTerm(core.MakeConstTerm(core.MakeConstMeta("zz_set_comprehension", scT), scT))
	s := Var("s", setT)
	c0 := MakeClause(ForAll(s, x)(sc.Apply(s, x).Or(Not(s.Apply(x)))))
	c1 := MakeClause(ForAll(s, x)(s.Apply(x).Or(Not(sc.Apply(s, x)))))
	definition := FunextFromIffPair(c0, c1)
	require.NotNil(t, definition)
	l, r, ok := MatchesEQ(definition.Conclusion())
	require.True(t, ok)
	_, lAbs := l.AsAbsTerm()
	_, rAbs := r.AsAbsTerm()
	assert.True(t, lAbs || rAbs, "contracts to a λ-sided equality, got %s", ext.PrintTerm(definition.Conclusion()))
	assert.False(t, NamingEqSides(definition.ConclClause()))
	assert.False(t, LambdaFreeEqSides(definition.ConclClause()))
}
