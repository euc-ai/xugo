package gates

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/bridge"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// The elementarity step on linear algebra of symbolic size: finite sums
// of scalar terms, existential indices and indices computed from index
// binders, each read in the sentence mode's bridge, through the
// equivalence mode from a family of models by prime, and through the
// embedding mode.

// A finite sum, spelled with the field's addition and with its ring's:
// the sum of the squares of a tuple's coordinates, a sum of shifted
// coordinates, and a sum of coordinates in the carrier.
func TestElementarityBridge_FiniteSum(t *testing.T) {
	lib, _ := buildSentence(t, "∀F:field_ops(A). ∀n:num. ∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ module_sum(F.add, F.zero, {j:num | j < n}, λj:num. F.mul(x(j), x(j))) = module_sum(field_ring(F).add, field_ring(F).zero, {i:num | i < n}, λi:num. F.add(x(i), F.one)) ∨ module_sum(F.add, F.zero, {j:num | j < n}, λj:num. x(j)) ∈ F.carrier", 2)
	require.Contains(t, lib.read(), "ring_homomorphism.MapSum")
	require.Contains(t, lib.read(), "polynomial_formula.ParameterPolynomialsSumIn")
}

// An existential index: a tuple is a normalized projective point, its
// leading coordinate one and every coordinate before it zero, the inner
// index bounded by the existential one, which the arithmetic keeps below
// the tuple's length.
func TestElementarityBridge_ExistentialIndex(t *testing.T) {
	lib, _ := buildSentence(t, "∀F:field_ops(A). ∀n:num. ∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ (∃j:num. j < n ∧ x(j) = F.one ∧ (∀i:num. i < j ⇒ x(i) = F.zero)) ∨ (∀j:num. j < n ⇒ x(j) = F.zero)", 2)
	require.Contains(t, lib.read(), "first_order.ConjoinSemantics")
}

// Computed indices: a family of r·N polynomials read as r rows of N,
// each row against a tuple a — the null-space condition of a flattened
// double-indexed family — and a tuple of length r·N read at j·N + c.
func TestElementarityBridge_ComputedIndex(t *testing.T) {
	lib, _ := buildSentence(t, "∀F:field_ops(A). ∀n N r d:num. ∀Q:(num → (num → num) → A). (∀j:num. j < r * N ⇒ polynomial_bound(field_ring(F), n, d, Q(j))) ⇒ ∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ ∀a:(num → A). ring_tuple(field_ring(F), N, a) ⇒ ∀j:num. j < r ⇒ module_sum(F.add, F.zero, {c:num | c < N}, λc:num. F.mul(polynomial_value(field_ring(F), Q(j * N + c), x), a(c))) = F.zero", 5)
	t.Logf("arithmetic goals: %d", lib.arith)
	buildSentence(t, "∀F:field_ops(A). ∀N r:num. ∀y:(num → A). ring_tuple(field_ring(F), r * N, y) ⇒ ∀j:num. j < r ⇒ ∀c:num. c < N ⇒ y(j * N + c) = y(j * N + c)", 3)
}

// The equivalence mode: a sentence with a sum, an existential index and
// a computed index, transferred from a family of models by prime. The
// executor proves both bridges and the sentence's closedness.
func TestElementarity_LinearAlgebraFromPrimeFamily(t *testing.T) {
	installBundles()
	const property = "∀Q:(num → (num → num) → A). (∀j:num. j < r * N ⇒ polynomial_bound(field_ring(F), n, d, Q(j))) ⇒ ∃a:(num → A). ring_tuple(field_ring(F), N, a) ∧ (∃c:num. c < N ∧ ¬(a(c) = F.zero)) ∧ (∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ ∀j:num. j < r ⇒ module_sum(F.add, F.zero, {c:num | c < N}, λc:num. F.mul(polynomial_value(field_ring(F), Q(j * N + c), x), a(c))) = F.zero)"
	Φ, _ := bridgeSentence(t, "∀F:field_ops(A). ∀n N r d:num. "+property, 5)
	modelProperty := "∀Q:(num → (num → num) → B). (∀j:num. j < r * N ⇒ polynomial_bound(field_ring(G), n, d, Q(j))) ⇒ ∃a:(num → B). ring_tuple(field_ring(G), N, a) ∧ (∃c:num. c < N ∧ ¬(a(c) = G.zero)) ∧ (∀x:(num → B). ring_tuple(field_ring(G), n, x) ⇒ ∀j:num. j < r ⇒ module_sum(G.add, G.zero, {c:num | c < N}, λc:num. G.mul(polynomial_value(field_ring(G), Q(j * N + c), x), a(c))) = G.zero)"
	family, _ := bridgeSentence(t, "∀F:field_ops(A). ∀n N r d:num. ∀p:num. nat_prime(p) ⇒ ∃G:field_ops(B). algebraically_closed_field_on(G) ∧ field_characteristic(G, p) ∧ ("+modelProperty+")", 5)
	closedF, _ := bridgeSentence(t, "∀F:field_ops(A). algebraically_closed_field_on(F)", 1)
	lib := newBridgeLibrary(t)
	call := bridge.Call{Goal: Φ, Facts: []core.Prop{core.Assume(closedF)}, Source: bridge.Source{Family: core.Assume(family)}}
	outcome, err := bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.NoError(t, err)
	require.Equal(t, bridge.EquivalenceMode, outcome.Mode)
	cert := core.Force(context.Background(), core.AsThm(outcome.Theorem))
	require.True(t, cert.Conclusion().AlphaEquals(Φ), "conclusion %s", ext.PrintTerm(cert.Conclusion()))
	require.Equal(t, 2, cert.NumHyps(), "hypotheses: %s", prop.PrintProp(cert))
	t.Logf("arithmetic goals: %d", lib.arith)
}

// The embedding mode on the three propositions a smooth projective
// curve's transfer between algebraically closed fields reads: degree-
// bounded membership of f in the ideal of P, pointwise; a normalized
// common projective zero of P; and a nonzero vector in the null space
// of the flattened family Q. Each is an iff across i: F → G with its
// parameters' images on G's side.
func TestElementarity_LinearAlgebraEmbedding(t *testing.T) {
	installBundles()
	const binders = "∀F:field_ops(A). ∀G:field_ops(B). ∀i:(A → B). ∀n N r d D:num. ∀f:((num → num) → A). ∀P Q:(num → (num → num) → A). "
	sentence := func(text string) core.Term {
		term, _ := bridgeSentence(t, binders+text, 11)
		return term
	}
	const fImage, pImage, qImage = "(λm:(num → num). i(f(m)))", "(λj:num. λm:(num → num). i(P(j, m)))", "(λj:num. λm:(num → num). i(Q(j, m)))"
	cases := []struct {
		name, overF, overG string
		bounds             []string
	}{
		{"membership in the ideal of P with degree-bounded cofactors",
			"∃H:(num → (num → num) → A). (∀j:num. j < r ⇒ polynomial_bound(field_ring(F), n, D, H(j))) ∧ (∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ polynomial_value(field_ring(F), f, x) = module_sum(F.add, F.zero, {j:num | j < r}, λj:num. F.mul(polynomial_value(field_ring(F), P(j), x), polynomial_value(field_ring(F), H(j), x))))",
			"∃H:(num → (num → num) → B). (∀j:num. j < r ⇒ polynomial_bound(field_ring(G), n, D, H(j))) ∧ (∀x:(num → B). ring_tuple(field_ring(G), n, x) ⇒ polynomial_value(field_ring(G), " + fImage + ", x) = module_sum(G.add, G.zero, {j:num | j < r}, λj:num. G.mul(polynomial_value(field_ring(G), " + pImage + "(j), x), polynomial_value(field_ring(G), H(j), x))))",
			[]string{"polynomial_bound(field_ring(F), n, d, f)", "∀j:num. j < r ⇒ polynomial_bound(field_ring(F), n, d, P(j))"}},
		{"a normalized common projective zero of P",
			"∃x:(num → A). ring_tuple(field_ring(F), n, x) ∧ (∃j:num. j < n ∧ x(j) = F.one ∧ (∀k:num. k < j ⇒ x(k) = F.zero)) ∧ (∀j:num. j < r ⇒ polynomial_value(field_ring(F), P(j), x) = F.zero)",
			"∃x:(num → B). ring_tuple(field_ring(G), n, x) ∧ (∃j:num. j < n ∧ x(j) = G.one ∧ (∀k:num. k < j ⇒ x(k) = G.zero)) ∧ (∀j:num. j < r ⇒ polynomial_value(field_ring(G), " + pImage + "(j), x) = G.zero)",
			[]string{"∀j:num. j < r ⇒ polynomial_bound(field_ring(F), n, d, P(j))"}},
		{"a nonzero vector in the null space of the flattened family Q",
			"∃a:(num → A). ring_tuple(field_ring(F), N, a) ∧ (∃c:num. c < N ∧ ¬(a(c) = F.zero)) ∧ (∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ ∀j:num. j < r ⇒ module_sum(F.add, F.zero, {c:num | c < N}, λc:num. F.mul(polynomial_value(field_ring(F), Q(j * N + c), x), a(c))) = F.zero)",
			"∃a:(num → B). ring_tuple(field_ring(G), N, a) ∧ (∃c:num. c < N ∧ ¬(a(c) = G.zero)) ∧ (∀x:(num → B). ring_tuple(field_ring(G), n, x) ⇒ ∀j:num. j < r ⇒ module_sum(G.add, G.zero, {c:num | c < N}, λc:num. G.mul(polynomial_value(field_ring(G), " + qImage + "(j * N + c), x), a(c))) = G.zero)",
			[]string{"∀j:num. j < r * N ⇒ polynomial_bound(field_ring(F), n, d, Q(j))"}},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			Φ := sentence("(" + c.overF + ") ⇔ (" + c.overG + ")")
			facts := []core.Prop{
				core.Assume(sentence("algebraically_closed_field_on(F)")),
				core.Assume(sentence("algebraically_closed_field_on(G)")),
				core.Assume(sentence("ring_homomorphism(field_ring(F), field_ring(G), i)")),
			}
			for _, b := range c.bounds {
				facts = append(facts, core.Assume(sentence(b)))
			}
			lib := newBridgeLibrary(t)
			outcome, err := bridge.Elementarity(bridge.Call{Goal: Φ, Facts: facts}, bridgeVocabulary(t), lib)
			require.NoError(t, err)
			require.Equal(t, bridge.EmbeddingMode, outcome.Mode)
			require.Equal(t, bridge.AlgebraicallyClosedTheory, outcome.Theory)
			requireOnFacts(t, outcome.Theorem, Φ, facts)
			t.Logf("arithmetic goals: %d", lib.arith)
		})
	}
}

// The step on the null-space proposition: ByElementarity with no source,
// as a chapter's Go writes it, and the session's entry on the same leaf,
// both close the iff along the embedding; the step's arithmetic is the
// arith closer under the proof's scope.
func TestByElementarity_NullSpaceEmbedding(t *testing.T) {
	installBundles()
	const binders = "∀F:field_ops(A). ∀G:field_ops(B). ∀i:(A → B). ∀n N r d:num. ∀Q:(num → (num → num) → A). "
	sentence := func(text string) core.Term {
		term, _ := bridgeSentence(t, binders+text, 8)
		return term
	}
	Φ := sentence("(∃a:(num → A). ring_tuple(field_ring(F), N, a) ∧ (∃c:num. c < N ∧ ¬(a(c) = F.zero)) ∧ (∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ ∀j:num. j < r ⇒ module_sum(F.add, F.zero, {c:num | c < N}, λc:num. F.mul(polynomial_value(field_ring(F), Q(j * N + c), x), a(c))) = F.zero)) ⇔ (∃a:(num → B). ring_tuple(field_ring(G), N, a) ∧ (∃c:num. c < N ∧ ¬(a(c) = G.zero)) ∧ (∀x:(num → B). ring_tuple(field_ring(G), n, x) ⇒ ∀j:num. j < r ⇒ module_sum(G.add, G.zero, {c:num | c < N}, λc:num. G.mul(polynomial_value(field_ring(G), (λj:num. λm:(num → num). i(Q(j, m)))(j * N + c), x), a(c))) = G.zero))")
	facts := []core.Term{
		sentence("algebraically_closed_field_on(F)"),
		sentence("algebraically_closed_field_on(G)"),
		sentence("ring_homomorphism(field_ring(F), field_ring(G), i)"),
		sentence("∀j:num. j < r * N ⇒ Q(j) ∈ polynomial_algebra(field_ring(F), {v:num | v < n})"),
	}
	goal := core.MakeProp(Φ, facts...)

	s := proof.NewScript(bridgeEnv(t))
	root := s.Section(goal)
	var cited []any
	for _, f := range facts {
		cited = append(cited, proof.ResidentHyp(f))
	}
	root.Do(proof.ByElementarity(nil, cited...))
	require.True(t, root.Proved(), "the Go verb leaves the leaf open")

	session := proof.CreateGoalStack(goal)
	require.NoError(t, proof.ApplyElementarityStep(session, bridgeEnv(t), context.Background(), proof.ElementaritySpec{Facts: facts}))
	require.True(t, session.Proved(), "the session entry leaves the leaf open")
}
