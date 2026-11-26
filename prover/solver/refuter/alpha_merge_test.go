package refuter

import (
	"context"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
	"google.golang.org/protobuf/proto"
)

// alphaDupGoal builds `H, ¬H ⊢ ⊥` for H = set_comprehension(λg. ∃y. R(g, y), x) — the
// minimal α-duplication shape (see ext/clause/alpha_merge.go and
// TestNegateGoalCNF_ExistsUnderLambdaAlphaDuplication in ext/clause). The
// CNF denotes the ∃-under-λ apart per hyp (α₀ vs α₁), so without the
// ALPHA-MERGE init chain the refuter saturates without finding ⊥.
func alphaDupGoal() Prop {
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	g := Var("g", TypeA)
	R := Var("R", core.MakeFun(TypeA, TypeA, TypeBool))
	setComprehension := Var("set_comprehension",
		core.MakeFun(core.MakeFun(TypeA, TypeBool), core.MakeFun(TypeA, TypeBool)))
	H := setComprehension.Apply(g.To(Exists(y)(R.Apply(g).Apply(y)))).Apply(x)
	return TestProp(ext.F, H, Not(H))
}

// TestAlphaMergeRefutesGoal: the α-duplication goal must refute — and at
// init (search-free), so no generous timeout is needed. The λ-free control
// establishes that the harness itself is sound.
func TestAlphaMergeRefutesGoal(t *testing.T) {
	defer goleak.VerifyNone(t)
	var cache utils.Map[core.TermKey, Prop]

	// Control: same wrapper, λ-body without ∃ — collapses at the CNF level.
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	g := Var("g", TypeA)
	setComprehension := Var("set_comprehension",
		core.MakeFun(core.MakeFun(TypeA, TypeBool), core.MakeFun(TypeA, TypeBool)))
	Hc := setComprehension.Apply(g.To(g.Eq(y).Core())).Apply(x)
	control := TestProp(ext.F, Hc, Not(Hc))

	pc := CreateRefuter(t.Context(), control, &cache)
	pc.Prove(t.Context())
	assert.True(t, pc.Refuted(), "λ-free control must refute")

	p := CreateRefuter(t.Context(), alphaDupGoal(), &cache)
	p.Prove(t.Context())
	assert.True(t, p.Refuted(),
		"the α-duplication goal must refute via the ALPHA-MERGE init chain")
}

// TestAlphaMergeReplayRoundTrip: the refutation certificate of the
// α-duplication goal round-trips through the wire and reconstructs
// deterministically. This pins the replay path of the chain's recipes — the
// hand-computed _RuleResolve unifiers of the pointwise bridges, the FUNEXT
// recombine, and the Simplifies twin (which needs the var=var size-gate
// exception at replay time too).
func TestAlphaMergeReplayRoundTrip(t *testing.T) {
	defer goleak.VerifyNone(t)
	var cache utils.Map[core.TermKey, Prop]

	refuter := CreateRefuter(t.Context(), alphaDupGoal(), &cache)
	proof := refuter.Prove(t.Context())
	require.True(t, refuter.Refuted())
	require.NotNil(t, proof)

	buf, err := proto.Marshal(proof)
	require.NoError(t, err)
	wire := &CNFRefuteProofProto{}
	require.NoError(t, proto.Unmarshal(buf, wire))

	recipes := countRecipes(wire.Root)
	t.Logf("certificate carries %d inference recipes", recipes)
	assert.Greater(t, recipes, 0,
		"the certificate must carry the chain's recipes")

	want := refuter.refutedCNFClauseThm.Thm
	for range 8 {
		ct := ReconstructCNFProofNode(
			wire.Root, ext.NewPoolReader(wire.Pool, loadConstMeta))
		require.NotNil(t, ct, "recipe replay must reconstruct")
		assert.True(t, ct.Thm.AlphaEquals(want))
	}
}

// nestedAlphaDupGoal builds the NESTED α-duplication shape (the
// corpus class of an image of an image, or an insert over a union): the λ-body's ∃ contains
// another ∃ under an opaque head, so the CNF mints a second-level α
// parameterized over the enclosing Skolem function, and the wit/intro
// sides of one symbol carry β-distinct instantiations (α(ƒ₀,g) vs
// α(λg.g,y)).
func nestedAlphaDupGoal() Prop {
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	g := Var("g", TypeA)
	w := Var("w", TypeA)
	Q := Var("Q", core.MakeFun(TypeA, TypeA, TypeBool))
	comprehensionSpec := Var("comprehension_spec", core.MakeFun(TypeA, TypeBool, TypeA, TypeBool))
	setComprehension := Var("set_comprehension",
		core.MakeFun(core.MakeFun(TypeA, TypeBool), core.MakeFun(TypeA, TypeBool)))

	inner := Exists(w)(Q.Apply(w).Apply(y))
	H := setComprehension.Apply(
		g.To(Exists(y)(comprehensionSpec.Apply(g).Apply(inner).Apply(y)))).Apply(x)
	return TestProp(ext.F, H, Not(H))
}

// TestAlphaMergeNestedRefutesGoal: the NESTED α-duplication goal refutes
// at init via the alpha-bridge extension (ext/clause/alpha_bridge.go): the
// inner pair merges (round 1), the inner symbol's canonicalization bridge
// aligns the outer wits with the outer intros (round 2), and the outer
// pair merges (round 3), search-free.
func TestAlphaMergeNestedRefutesGoal(t *testing.T) {
	defer goleak.VerifyNone(t)
	var cache utils.Map[core.TermKey, Prop]

	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()
	p := CreateRefuter(ctx, nestedAlphaDupGoal(), &cache)
	p.Prove(ctx)
	assert.True(t, p.Refuted(),
		"the nested α-duplication goal must refute via the alpha-bridge "+
			"extension of the ALPHA-MERGE init chain")
}

// TestAlphaMergeNestedReplayRoundTrip pins the wire path of the nested
// chain's recipes — in particular the EQ_APPLY partial-application
// paramodulation (clause.proto rule 10), which only this chain produces.
func TestAlphaMergeNestedReplayRoundTrip(t *testing.T) {
	defer goleak.VerifyNone(t)
	var cache utils.Map[core.TermKey, Prop]

	refuter := CreateRefuter(t.Context(), nestedAlphaDupGoal(), &cache)
	proof := refuter.Prove(t.Context())
	require.True(t, refuter.Refuted())
	require.NotNil(t, proof)

	buf, err := proto.Marshal(proof)
	require.NoError(t, err)
	wire := &CNFRefuteProofProto{}
	require.NoError(t, proto.Unmarshal(buf, wire))

	recipes := countRecipes(wire.Root)
	t.Logf("certificate carries %d inference recipes", recipes)
	assert.Greater(t, recipes, 0,
		"the certificate must carry the chain's recipes")

	want := refuter.refutedCNFClauseThm.Thm
	for range 8 {
		ct := ReconstructCNFProofNode(
			wire.Root, ext.NewPoolReader(wire.Pool, loadConstMeta))
		require.NotNil(t, ct, "recipe replay must reconstruct")
		assert.True(t, ct.Thm.AlphaEquals(want))
	}
}

// onePointParts builds the ONE-POINT α-duplication material (the third
// shape — see ext/clause/alpha_merge.go §"THE ONE-POINT SHAPE"):
//
//	f = λG. ∃x. P(x) ∧ G = x     (the comprehension_spec normal form)
//	g = λu. P(u)                 (its one-point contraction)
//
// f and g are extensionally equal but only bridgeable through the
// eliminateOnePointWits + mergeSymbolDefinition chain moves: the λs sit in
// argument position of the opaque K, and f's wit clauses go through the
// ∃-witness Skolem.
func onePointParts() (kf, kg Term) {
	x := Var("x", TypeA)
	G := Var("G", TypeA)
	u := Var("u", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	K := Var("K", core.MakeFun(core.MakeFun(TypeA, TypeBool), TypeBool))
	f := G.To(Exists(x)(P.Apply(x).And(G.Eq(x))))
	g := u.To(P.Apply(u))
	return K.Apply(f).Core(), K.Apply(g).Core()
}

// TestAlphaMergeOnePointRefutesGoal: the three failing faces of the
// one-point gap must refute at init (search-free), plus the
// compound-parameter variant faithful to a corpus shape, finiteness of a vector type
// (λG. ∃x. P(i,x) ∧ G = x — the defining equality contracts to a
// compound-vs-symbol form, exercising the size-gated Simplifies twin).
func TestAlphaMergeOnePointRefutesGoal(t *testing.T) {
	defer goleak.VerifyNone(t)
	var cache utils.Map[core.TermKey, Prop]

	kf, kg := onePointParts()

	// V2 — argument position, no equality hyp anywhere: K(f) ⊢ K(g).
	p := CreateRefuter(t.Context(), TestProp(kg, kf), &cache)
	p.Prove(t.Context())
	assert.True(t, p.Refuted(), "K(f) ⊢ K(g) must refute via the "+
		"one-point defining-equality merge")

	// V4 — the `H, ¬H ⊢ ⊥` face: K(f) ⊢ K(f).
	p = CreateRefuter(t.Context(), TestProp(kf, kf), &cache)
	p.Prove(t.Context())
	assert.True(t, p.Refuted(), "K(f) ⊢ K(f) (one-point α-duplication) "+
		"must refute")

	// Compound-parameter variant (the vector-finiteness shape).
	x := Var("x", TypeA)
	G := Var("G", TypeA)
	u := Var("u", TypeA)
	i := Var("i", TypeA)
	P2 := Var("P2", core.MakeFun(TypeA, TypeA, TypeBool))
	K := Var("K", core.MakeFun(core.MakeFun(TypeA, TypeBool), TypeBool))
	fi := G.To(Exists(x)(P2.Apply(i, x).And(G.Eq(x))))
	gi := u.To(P2.Apply(i, u))
	p = CreateRefuter(t.Context(),
		TestProp(K.Apply(gi).Core(), K.Apply(fi).Core()), &cache)
	p.Prove(t.Context())
	assert.True(t, p.Refuted(), "the compound-parameter one-point goal "+
		"(the vector-finiteness shape) must refute")
}

// TestAlphaMergeOnePointEqualityHypRefutesGoal: the stated-equality face —
// K(f), f = g ⊢ K(g). Before the one-point chain moves this failed too
// (the extensionalized f = g hyp leaves only Skolem-threaded pointwise
// clauses; nothing recombined them back to a unit equality).
func TestAlphaMergeOnePointEqualityHypRefutesGoal(t *testing.T) {
	defer goleak.VerifyNone(t)
	var cache utils.Map[core.TermKey, Prop]

	x := Var("x", TypeA)
	G := Var("G", TypeA)
	u := Var("u", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	K := Var("K", core.MakeFun(core.MakeFun(TypeA, TypeBool), TypeBool))
	f := G.To(Exists(x)(P.Apply(x).And(G.Eq(x))))
	g := u.To(P.Apply(u))

	goal := TestProp(K.Apply(g).Core(), K.Apply(f).Core(),
		ext.WrapTerm(f.Core()).Eq(g).Core())
	p := CreateRefuter(t.Context(), goal, &cache)
	p.Prove(t.Context())
	assert.True(t, p.Refuted(),
		"K(f), f=g ⊢ K(g) must refute via the one-point chain moves")
}

// TestAlphaMergeOnePointReplayRoundTrip pins the wire path of the
// one-point chain's recipes: the eliminateOnePointWits _RuleResolve step
// (an equality-literal paramodulation at a recorded positional unifier)
// and the mergeSymbolDefinition FUNEXT recombine.
func TestAlphaMergeOnePointReplayRoundTrip(t *testing.T) {
	defer goleak.VerifyNone(t)
	var cache utils.Map[core.TermKey, Prop]

	kf, kg := onePointParts()
	refuter := CreateRefuter(t.Context(), TestProp(kg, kf), &cache)
	proof := refuter.Prove(t.Context())
	require.True(t, refuter.Refuted())
	require.NotNil(t, proof)

	buf, err := proto.Marshal(proof)
	require.NoError(t, err)
	wire := &CNFRefuteProofProto{}
	require.NoError(t, proto.Unmarshal(buf, wire))

	recipes := countRecipes(wire.Root)
	t.Logf("certificate carries %d inference recipes", recipes)
	assert.Greater(t, recipes, 0,
		"the certificate must carry the chain's recipes")

	want := refuter.refutedCNFClauseThm.Thm
	for range 8 {
		ct := ReconstructCNFProofNode(
			wire.Root, ext.NewPoolReader(wire.Pool, loadConstMeta))
		require.NotNil(t, ct, "recipe replay must reconstruct")
		assert.True(t, ct.Thm.AlphaEquals(want))
	}
}

// compoundWitnessParts builds the COMPOUND-WITNESS α-duplication material
// (see ext/clause/alpha_merge.go §"THE COMPOUND-WITNESS SHAPE"): the
// λ-body of a product-set comprehension `{x · y | x, y | x ∈ M ∧ y ∈ N}`,
//
//	S  = λg. ∃x y. M(x) ∧ N(y) ∧ g = mul(x, y)
//	S′ = S with every binder renamed
//
// each under the opaque K. The CNF denotes the ∃-under-λ apart per hyp
// (α₀ vs α₁) with THREE witness clauses per symbol and an intro of three
// literals whose symbol is applied to the compound mul(x, y).
func compoundWitnessParts() (ks, ksRenamed Term) {
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	g := Var("g", TypeA)
	u := Var("u", TypeA)
	v := Var("v", TypeA)
	h := Var("h", TypeA)
	M := Var("M", MakeFun(TypeA, TypeBool))
	N := Var("N", MakeFun(TypeA, TypeBool))
	mul := Var("mul", core.MakeFun(TypeA, TypeA, TypeA))
	K := Var("K", core.MakeFun(core.MakeFun(TypeA, TypeBool), TypeBool))
	S := g.To(Exists(x, y)(M.Apply(x).And(N.Apply(y)).And(g.Eq(mul.Apply(x, y)))))
	S2 := h.To(Exists(u, v)(M.Apply(u).And(N.Apply(v)).And(h.Eq(mul.Apply(u, v)))))
	return K.Apply(S).Core(), K.Apply(S2).Core()
}

// TestAlphaMergeCompoundWitnessRefutesGoal: K(S) ⊢ K(S′) for the
// compound-witness body must refute at init (search-free) — with the
// binders renamed and spelled identically alike — through the
// compound-witness direction chain. The control (a one-conjunct body,
// `λg. ∃y. R(g, y)`) closes through the single-step bridge and pins the
// harness.
func TestAlphaMergeCompoundWitnessRefutesGoal(t *testing.T) {
	defer goleak.VerifyNone(t)
	var cache utils.Map[core.TermKey, Prop]

	run := func(name string, goal Prop) {
		ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
		defer cancel()
		p := CreateRefuter(ctx, goal, &cache)
		p.Prove(ctx)
		assert.True(t, p.Refuted(), "%s must refute via the compound-witness "+
			"ALPHA-MERGE chain", name)
	}

	// Control: one conjunct, bare-variable body — the existing chain.
	g := Var("g", TypeA)
	y := Var("y", TypeA)
	h := Var("h", TypeA)
	z := Var("z", TypeA)
	R := Var("R", core.MakeFun(TypeA, TypeA, TypeBool))
	K := Var("K", core.MakeFun(core.MakeFun(TypeA, TypeBool), TypeBool))
	kc := K.Apply(g.To(Exists(y)(R.Apply(g, y)))).Core()
	kcRenamed := K.Apply(h.To(Exists(z)(R.Apply(h, z)))).Core()
	run("control K(λg.∃y.R(g,y)) ⊢ K(renamed)", TestProp(kcRenamed, kc))

	ks, ksRenamed := compoundWitnessParts()
	run("K(S) ⊢ K(S′) with renamed binders", TestProp(ksRenamed, ks))
	run("K(S) ⊢ K(S) spelled identically", TestProp(ks, ks))
}

// TestAlphaMergeCompoundWitnessReplayRoundTrip pins the wire path of the
// compound-witness chain's recipes: the equality paramodulation at the
// compound argument position and the per-conjunct resolutions, each a
// native _RuleResolve at a recorded unifier over a collision-renamed
// intro clause.
func TestAlphaMergeCompoundWitnessReplayRoundTrip(t *testing.T) {
	defer goleak.VerifyNone(t)
	var cache utils.Map[core.TermKey, Prop]

	ks, ksRenamed := compoundWitnessParts()
	refuter := CreateRefuter(t.Context(), TestProp(ksRenamed, ks), &cache)
	proof := refuter.Prove(t.Context())
	require.True(t, refuter.Refuted())
	require.NotNil(t, proof)

	buf, err := proto.Marshal(proof)
	require.NoError(t, err)
	wire := &CNFRefuteProofProto{}
	require.NoError(t, proto.Unmarshal(buf, wire))

	recipes := countRecipes(wire.Root)
	t.Logf("certificate carries %d inference recipes", recipes)
	assert.Greater(t, recipes, 0,
		"the certificate must carry the chain's recipes")

	want := refuter.refutedCNFClauseThm.Thm
	for range 8 {
		ct := ReconstructCNFProofNode(
			wire.Root, ext.NewPoolReader(wire.Pool, loadConstMeta))
		require.NotNil(t, ct, "recipe replay must reconstruct")
		assert.True(t, ct.Thm.AlphaEquals(want))
	}
}
