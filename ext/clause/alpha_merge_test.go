package clause

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

// alphaDupCNF normalizes the sequent `H, ¬H ⊢ ⊥` and returns its clauses.
func alphaDupCNF(t *testing.T, H Term) []*Clause {
	t.Helper()
	var cache utils.Map[core.TermKey, Prop]
	goal := MakeProp(F, H, Not(H))
	res, err := NegateGoalCNF(t.Context(), goal, &cache)
	assert.NoError(t, err)
	assert.NotNil(t, res.CNF)
	return res.CNF.Clauses()
}

// TestDeriveAlphaMergeChain exercises the ALPHA-MERGE chain on the minimal
// α-duplication CNF (see TestNegateGoalCNF_ExistsUnderLambdaAlphaDuplication
// in cnf_test.go for the pipeline-level shape): from the 8-clause set with
// duplicated α₀/α₁ families, the chain must derive the two pointwise
// bridges, the symbol equality, and a twin that complements one of the two
// set_comprehension unit clauses.
func TestDeriveAlphaMergeChain(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	g := Var("g", TypeA)
	R := Var("R", MakeFun(TypeA, TypeA, TypeBool))
	setComprehension := Var("set_comprehension",
		MakeFun(MakeFun(TypeA, TypeBool), MakeFun(TypeA, TypeBool)))

	H := setComprehension.Apply(g.To(Exists(y)(R.Apply(g).Apply(y)))).Apply(x)
	clauses := alphaDupCNF(t, H)
	assert.Equal(t, 8, len(clauses),
		"the α-duplication CNF shape changed; update this test and "+
			"re-validate the merge chain")

	chain := DeriveAlphaMergeChain(clauses)
	assert.Equal(t, 4, len(chain),
		"expected [bridge, bridge, equality, twin], got %d steps", len(chain))
	if len(chain) != 4 {
		return
	}

	// Step c is a var=var equality (the merged symbols).
	l, r, ok := MatchesEQ(chain[2].ConclClause().EffectiveBody())
	assert.True(t, ok, "step c must be an equality, got %s", chain[2].ConclClause())
	_, lok := l.AsVar()
	_, rok := r.AsVar()
	assert.True(t, lok && rok, "step c must equate two vars, got %s = %s",
		WrapTerm(l), WrapTerm(r))
	assert.True(t, isVarEqVarClause(chain[2].ConclClause()),
		"step c must pass the Simplifies var=var size-gate exception")

	// The twin must be the exact complement of one of the input unit clauses
	// (this is what lets findContradicts close the goal at refuter init).
	twin := chain[3].ConclClause().Term()
	complemented := false
	for _, c := range clauses {
		if n := MatchesNOT(twin); n != nil && n.AlphaEquals(c.Term()) {
			complemented = true
		}
		if n := MatchesNOT(c.Term()); n != nil && n.AlphaEquals(twin) {
			complemented = true
		}
	}
	assert.True(t, complemented,
		"twin %s must complement an initial clause", WrapTerm(twin))

	// Every step obeys the binary proof DAG contract and dependency order:
	// hyps are input clauses or earlier steps' conclusions. Keyed by
	// Clause.Key() — the identity the refuter's deduction records and
	// proof builder use — because a direction chain renames the intro
	// apart from the wits before resolving it (here the intro's binder g
	// collides with the wit's), and the renamed form shares the original's
	// key.
	known := map[ClauseKey]bool{}
	for _, c := range clauses {
		known[c.Key()] = true
	}
	for i, s := range chain {
		assert.LessOrEqual(t, s.NumHyps(), 2,
			"step %d has %d hyps; makeDeduceStep requires ≤2", i, s.NumHyps())
		for h := range s.HypClauseIter() {
			assert.True(t, known[h.Key()],
				"step %d hyp %s is neither an input clause nor an earlier "+
					"step's conclusion", i, h)
		}
		known[s.ConclClause().Key()] = true
	}

	// Idempotence: the chain is derived from initial clauses only; feeding
	// the enriched set back must not re-merge the same pair.
	enriched := append(append([]*Clause{}, clauses...),
		chain[0].ConclClause(), chain[1].ConclClause(),
		chain[2].ConclClause(), chain[3].ConclClause())
	again := DeriveAlphaMergeChain(enriched)
	for _, s := range again {
		assert.False(t, isVarEqVarClause(s.ConclClause()),
			"re-running on the enriched set must not derive a duplicate "+
				"symbol equality, got %s", s.ConclClause())
	}
}

// TestDeriveAlphaMergeChain_Nested exercises the NESTED denote case (the
// corpus shape of an image of an image, or an insert over a union): the λ-body's ∃ contains
// another ∃ under an opaque head, so the pipeline mints a second-level α
// parameterized over the enclosing Skolem function (αᵢ(ƒ, g)).
//
// The INNER pair merges in round 1 (the spine-order funextContract
// generalization). The OUTER pair's wit/intro sides carry β-distinct
// instantiations of the inner α (α(ƒ₀, g) vs α(λg.g, y)) — bridged by
// the alpha-bridge extension (alpha_bridge.go): the inner
// symbol's canonicalization equality (a partial funext contraction +
// EQ_APPLY paramodulation) rewrites the outer wits into the intros'
// canonical instance form, and the outer pair merges on the next round.
func TestDeriveAlphaMergeChain_Nested(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	g := Var("g", TypeA)
	w := Var("w", TypeA)
	Q := Var("Q", MakeFun(TypeA, TypeA, TypeBool))
	comprehensionSpec := Var("comprehension_spec", MakeFun(TypeA, TypeBool, TypeA, TypeBool))
	setComprehension := Var("set_comprehension",
		MakeFun(MakeFun(TypeA, TypeBool), MakeFun(TypeA, TypeBool)))

	// H = set_comprehension(λg. ∃y. comprehension_spec(g, ∃w. Q(w, y), y), x)
	inner := Exists(w)(Q.Apply(w).Apply(y))
	H := setComprehension.Apply(
		g.To(Exists(y)(comprehensionSpec.Apply(g).Apply(inner).Apply(y)))).Apply(x)
	clauses := alphaDupCNF(t, H)

	chain := DeriveAlphaMergeChain(clauses)

	// Round 1: the inner (2-ary, function-parameterized) pair must merge.
	innerMerged := false
	outerMerged := false
	for _, s := range chain {
		c := s.ConclClause()
		if !isVarEqVarClause(c) {
			continue
		}
		l, _, _ := MatchesEQ(c.EffectiveBody())
		if v, ok := l.AsVar(); ok {
			// Arity distinguishes the levels: inner α is (A→A)→A→bool
			// (2 args), outer α is A→bool (1 arg).
			switch len(ext.MatchesFun(v.Type())) - 1 {
			case 2:
				innerMerged = true
			case 1:
				outerMerged = true
			}
		}
	}
	assert.True(t, innerMerged,
		"the inner fun-parameterized α pair must merge (round 1); if this "+
			"broke, check the funextContract spine-order generalization")
	assert.True(t, outerMerged,
		"the outer α pair must merge through the alpha-bridge "+
			"canonicalization (alpha_bridge.go); its refuter-level sibling "+
			"is TestAlphaMergeNestedRefutesGoal in prover/solver/refuter")

	// The chain must also produce a twin complementing one of the two
	// set_comprehension unit clauses — the step findContradicts closes the goal on.
	complemented := false
	for _, s := range chain {
		twin := s.ConclClause().Term()
		for _, c := range clauses {
			if n := MatchesNOT(twin); n != nil && n.AlphaEquals(c.Term()) {
				complemented = true
			}
			if n := MatchesNOT(c.Term()); n != nil && n.AlphaEquals(twin) {
				complemented = true
			}
		}
	}
	assert.True(t, complemented,
		"a twin must complement one of the set_comprehension unit clauses")

	// Binary-DAG + dependency-order contract. Keyed by Clause.Key()
	// (α-key derived) — the identity the refuter's deduction records and
	// proof builder use — because the bridge derivation collision-renames
	// β's defining clauses before resolving them (r1/r2 record the renamed
	// forms, which share the original clauses' keys).
	known := map[ClauseKey]bool{}
	for _, c := range clauses {
		known[c.Key()] = true
	}
	for i, s := range chain {
		assert.LessOrEqual(t, s.NumHyps(), 2,
			"step %d has %d hyps; makeDeduceStep requires ≤2", i, s.NumHyps())
		for h := range s.HypClauseIter() {
			assert.True(t, known[h.Key()],
				"step %d hyp %s is neither an input clause nor an earlier "+
					"step's conclusion", i, h)
		}
		known[s.ConclClause().Key()] = true
	}
}

// TestOnePointWitElimination: direct unit for chain moves e/f (the
// ONE-POINT SHAPE section of alpha_merge.go's header). The hand-built clauses
// are exactly what the CNF pipeline leaves for a one-point λ-body
// `λG. ∃x. P(x) ∧ G = x`:
//
//	wit1:  ∀G. P(ƒ(G)) ∨ ¬α(G)
//	wit2:  ∀G. ¬α(G) ∨ (G = ƒ(G))
//	intro: ∀x. α(x) ∨ ¬P(x)
//
// The recombine must decline pre-elimination (the ƒ(G) argument), the
// elimination must derive the ƒ-free wit via a native _RuleResolve step,
// and the enriched group must recombine to the defining fn-equality
// ⊢ α = P within deriveInitFunext's LambdaFreeEqSides scope.
func TestOnePointWitElimination(t *testing.T) {
	defer goleak.VerifyNone(t)

	G := Var("G", TypeA)
	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	alpha := Var("a0", MakeFun(TypeA, TypeBool)).AssertVar()
	sk := Var("f0", MakeFun(TypeA, TypeA))
	alphaW := ext.WrapTerm(alpha)

	wit1 := MakeClause(ForAll(G)(P.Apply(sk.Apply(G)).Or(Not(alphaW.Apply(G)))))
	wit2 := MakeClause(ForAll(G)(Not(alphaW.Apply(G)).Or(G.Eq(sk.Apply(G)))))
	intro := MakeClause(ForAll(x)(alphaW.Apply(x).Or(Not(P.Apply(x)))))

	// Pre-elimination the recombine declines — the wit body's arg is ƒ(G).
	assert.Nil(t, FunextFromIffPair(wit1, intro))

	findGroup := func(clauses []*Clause) *_alphaGroup {
		for _, g := range detectAlphaGroups(clauses) {
			if g.sym.Equals(alpha) {
				return g
			}
		}
		return nil
	}
	g := findGroup([]*Clause{wit1, wit2, intro})
	assert.NotNil(t, g)
	assert.Equal(t, 2, len(g.wits))
	assert.Equal(t, 1, len(g.intros))

	// ...and so does the whole-group merge.
	assert.Nil(t, mergeSymbolDefinition(g))

	// Chain move e: the elimination derives the ƒ-free wit.
	elims := eliminateOnePointWits(g)
	assert.Equal(t, 1, len(elims))
	want := ForAll(G)(P.Apply(G).Or(Not(alphaW.Apply(G))))
	assert.True(t, elims[0].ConclClause().Term().AlphaEquals(want.Core()),
		"eliminated wit must be ∀G. P(G) ∨ ¬α(G), got %s",
		elims[0].ConclClause())

	// Chain move f: the group enriched with the eliminated wit recombines
	// to the defining fn-equality, in LambdaFreeEqSides scope.
	enriched := findGroup([]*Clause{
		wit1, wit2, intro, elims[0].ConclClause()})
	eq := mergeSymbolDefinition(enriched)
	assert.NotNil(t, eq, "the enriched group must recombine")
	assert.True(t, LambdaFreeEqSides(eq.ConclClause()))
	l, r, ok := MatchesEQ(eq.ConclClause().EffectiveBody())
	assert.True(t, ok)
	assert.True(t,
		(l.AlphaEquals(alpha) && r.AlphaEquals(P)) ||
			(l.AlphaEquals(P.Core()) && r.AlphaEquals(alpha)),
		"expected ⊢ α = P, got %s", eq.ConclClause())
}

// TestDeriveAlphaMergeChain_OnePoint exercises the full chain on the
// pipeline-produced one-point CNF — the `H, ¬H ⊢ ⊥` face of the shape
// (the refuter-level end-to-end siblings, including the K(f) ⊢ K(g)
// single-symbol faces, live in
// prover/solver/refuter/alpha_merge_test.go TestAlphaMergeOnePointRefutesGoal).
func TestDeriveAlphaMergeChain_OnePoint(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	G := Var("G", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	K := Var("K", MakeFun(MakeFun(TypeA, TypeBool), TypeBool))

	H := K.Apply(G.To(Exists(x)(P.Apply(x).And(G.Eq(x))))).Core()
	clauses := alphaDupCNF(t, H)
	assert.Equal(t, 12, len(clauses),
		"the one-point α-duplication CNF shape changed; update this test "+
			"and re-validate the chain")

	chain := DeriveAlphaMergeChain(clauses)

	// The chain must derive at least one defining equality (α = P) and the
	// α-pair equality — all var=var, Simplifies-usable.
	eqCount := 0
	for _, s := range chain {
		if isVarEqVarClause(s.ConclClause()) {
			eqCount++
		}
	}
	assert.GreaterOrEqual(t, eqCount, 2,
		"expected the defining equalities and the pair equality, got %d "+
			"in %d steps", eqCount, len(chain))

	// A twin must complement one of the two K unit clauses — the step
	// findContradicts closes the goal on.
	complemented := false
	for _, s := range chain {
		twin := s.ConclClause().Term()
		for _, c := range clauses {
			if n := MatchesNOT(twin); n != nil && n.AlphaEquals(c.Term()) {
				complemented = true
			}
			if n := MatchesNOT(c.Term()); n != nil && n.AlphaEquals(twin) {
				complemented = true
			}
		}
	}
	assert.True(t, complemented,
		"a twin must complement one of the K unit clauses")

	// Binary-DAG + dependency-order contract (keyed by Clause.Key, see
	// TestDeriveAlphaMergeChain_Nested).
	known := map[ClauseKey]bool{}
	for _, c := range clauses {
		known[c.Key()] = true
	}
	for i, s := range chain {
		assert.LessOrEqual(t, s.NumHyps(), 2,
			"step %d has %d hyps; makeDeduceStep requires ≤2", i, s.NumHyps())
		for h := range s.HypClauseIter() {
			assert.True(t, known[h.Key()],
				"step %d hyp %s is neither an input clause nor an earlier "+
					"step's conclusion", i, h)
		}
		known[s.ConclClause().Key()] = true
	}

	// Idempotence: feeding the enriched set back must not re-derive any
	// equality (elimination re-derivations are key-gated; single-symbol
	// merges are blocked by the pre-existing equality clauses; pairs by
	// mergedPairs pre-seeding).
	enriched := slices.Clone(clauses)
	for _, s := range chain {
		enriched = append(enriched, s.ConclClause())
	}
	for _, s := range DeriveAlphaMergeChain(enriched) {
		assert.False(t, isVarEqVarClause(s.ConclClause()),
			"re-running on the enriched set must not re-derive an equality, "+
				"got %s", s.ConclClause())
	}
}

// assertChainClosesKPair checks the chain-level contract shared by every
// α-duplication face under an opaque K: at least one var=var equality
// (the merged symbols, Simplifies-usable), a twin complementing one of the
// two K unit clauses (the step findContradicts closes the goal on), the
// binary-DAG + dependency-order contract keyed by Clause.Key (the chain
// collision-renames clauses before resolving them; renamed forms share
// the original's key), and idempotence on the enriched set.
func assertChainClosesKPair(t *testing.T, clauses []*Clause, chain []*ClauseThm) {
	t.Helper()
	eqCount := 0
	for _, s := range chain {
		if isVarEqVarClause(s.ConclClause()) {
			eqCount++
		}
	}
	assert.GreaterOrEqual(t, eqCount, 1,
		"expected a var=var symbol equality, got %d in %d steps",
		eqCount, len(chain))

	complemented := false
	for _, s := range chain {
		twin := s.ConclClause().Term()
		for _, c := range clauses {
			if n := MatchesNOT(twin); n != nil && n.AlphaEquals(c.Term()) {
				complemented = true
			}
			if n := MatchesNOT(c.Term()); n != nil && n.AlphaEquals(twin) {
				complemented = true
			}
		}
	}
	assert.True(t, complemented,
		"a twin must complement one of the K unit clauses")

	known := map[ClauseKey]bool{}
	for _, c := range clauses {
		known[c.Key()] = true
	}
	for i, s := range chain {
		assert.LessOrEqual(t, s.NumHyps(), 2,
			"step %d has %d hyps; makeDeduceStep requires ≤2", i, s.NumHyps())
		for h := range s.HypClauseIter() {
			assert.True(t, known[h.Key()],
				"step %d hyp %s is neither an input clause nor an earlier "+
					"step's conclusion", i, h)
		}
		known[s.ConclClause().Key()] = true
	}

	enriched := slices.Clone(clauses)
	for _, s := range chain {
		enriched = append(enriched, s.ConclClause())
	}
	for _, s := range DeriveAlphaMergeChain(enriched) {
		assert.False(t, isVarEqVarClause(s.ConclClause()),
			"re-running on the enriched set must not re-derive an equality, "+
				"got %s", s.ConclClause())
	}
}

// kPairCNF normalizes `K(S) ⊢ K(S′)` and returns its clauses.
func kPairCNF(t *testing.T, S, S2 Term) []*Clause {
	t.Helper()
	K := Var("K", MakeFun(MakeFun(TypeA, TypeBool), TypeBool))
	var cache utils.Map[core.TermKey, Prop]
	goal := MakeProp(K.Apply(S2).Core(), K.Apply(S).Core())
	res, err := NegateGoalCNF(t.Context(), goal, &cache)
	assert.NoError(t, err)
	assert.NotNil(t, res.CNF)
	return res.CNF.Clauses()
}

// TestDeriveAlphaMergeChain_CompoundWitness exercises the COMPOUND-WITNESS
// face (the §"THE COMPOUND-WITNESS SHAPE" section of alpha_merge.go's
// header) on the pipeline-produced CNF of the product-set comprehension
// body `λg. ∃x y. M(x) ∧ N(y) ∧ g = mul(x, y)`: three wit clauses per
// symbol and a three-literal intro whose symbol is applied to the compound
// mul(x, y). The pair must merge through the multi-step direction chain —
// an equality paramodulation at the compound position followed by one
// resolution per conjunct — and twin a K unit clause.
func TestDeriveAlphaMergeChain_CompoundWitness(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	g := Var("g", TypeA)
	u := Var("u", TypeA)
	v := Var("v", TypeA)
	h := Var("h", TypeA)
	M := Var("M", MakeFun(TypeA, TypeBool))
	N := Var("N", MakeFun(TypeA, TypeBool))
	mul := Var("mul", MakeFun(TypeA, TypeA, TypeA))
	S := g.To(Exists(x, y)(M.Apply(x).And(N.Apply(y)).And(g.Eq(mul.Apply(x, y))))).Core()
	S2 := h.To(Exists(u, v)(M.Apply(u).And(N.Apply(v)).And(h.Eq(mul.Apply(u, v))))).Core()

	clauses := kPairCNF(t, S, S2)
	assert.Equal(t, 16, len(clauses),
		"the compound-witness CNF shape changed; update this test and "+
			"re-validate the chain")
	chain := DeriveAlphaMergeChain(clauses)
	assertChainClosesKPair(t, clauses, chain)

	// Spelled identically: the renaming is not what the chain bridges.
	clauses = kPairCNF(t, S, S)
	assertChainClosesKPair(t, clauses, DeriveAlphaMergeChain(clauses))
}

// TestDeriveAlphaMergeChain_MultiConjunct covers the rest of the class
// the compound-witness move exists for — a multi-literal intro whatever
// its symbol argument:
//
//   - a bare-variable argument with two conjuncts, `λg. ∃y. P(g) ∧ R(g, y)`
//     (two wits, a three-literal intro at a binder);
//   - a conjunct that mentions the outer binder beside a compound witness,
//     `λg. ∃x. M(x) ∧ R(g, x) ∧ g = f(x)` (one-point contraction leaves the
//     intro conjunct at R(f(x), x) while the wit reads R(g, ƒ(g)));
//   - a conjunct that contains the witness term itself,
//     `λg. ∃x. M(x) ∧ N(f(x)) ∧ g = f(x)` (the wit reads N(f(ƒ(g))), which
//     the equality wit normalizes to N(g) before the pair can align).
func TestDeriveAlphaMergeChain_MultiConjunct(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	g := Var("g", TypeA)
	u := Var("u", TypeA)
	h := Var("h", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	M := Var("M", MakeFun(TypeA, TypeBool))
	N := Var("N", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeA, TypeBool))
	f := Var("f", MakeFun(TypeA, TypeA))

	cases := []struct {
		name  string
		S, S2 Term
	}{
		{"bare argument, two conjuncts",
			g.To(Exists(y)(P.Apply(g).And(R.Apply(g, y)))).Core(),
			h.To(Exists(u)(P.Apply(h).And(R.Apply(h, u)))).Core()},
		{"conjunct mentions the outer binder",
			g.To(Exists(x)(M.Apply(x).And(R.Apply(g, x)).And(g.Eq(f.Apply(x))))).Core(),
			h.To(Exists(u)(M.Apply(u).And(R.Apply(h, u)).And(h.Eq(f.Apply(u))))).Core()},
		{"conjunct contains the witness term",
			g.To(Exists(x)(M.Apply(x).And(N.Apply(f.Apply(x))).And(g.Eq(f.Apply(x))))).Core(),
			h.To(Exists(u)(M.Apply(u).And(N.Apply(f.Apply(u))).And(h.Eq(f.Apply(u))))).Core()},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			clauses := kPairCNF(t, tc.S, tc.S2)
			assertChainClosesKPair(t, clauses, DeriveAlphaMergeChain(clauses))
		})
	}
}
