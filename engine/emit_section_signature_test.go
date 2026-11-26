package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// The signature, headline, entry form and claim texts emit-section
// renders a section in: each test states a chapter's shape in a bound
// session, proves it as the chapter's member was proved, reads the
// emitted Go for the chapter's spelling, and — under
// XUGO_EMIT_REPLAY=1 — lands the member through a build overlay and
// replays it with the gates harness (replayEmittedInFamily).

// addDoorGoal states a goal at the session's statement door — the door
// the chapter's texts read at, with the family's notations and
// implicit bindings — and adds it.
func addDoorGoal(t *testing.T, s *Session, text string) string {
	t.Helper()
	parsed := dsl.ParsePropTextInScope(text, s.StatementDoorScope())
	require.Empty(t, parsed.Errors, "goal %q", text)
	return s.AddGoal(parsed.Prop)
}

// applyOnGoalWhere applies a tactic to the one open goal whose printed
// conclusion pick accepts.
func applyOnGoalWhere(t *testing.T, e *Engine, s *Session, pick func(conclusion string) bool, tactic TacticReq) {
	t.Helper()
	ctx := context.Background()
	state, err := e.InspectState(ctx, s.ID)
	require.NoError(t, err)
	var picked []string
	var goalID string
	for _, g := range state.Goals {
		printed := ext.PrintTerm(g.Statement.Conclusion())
		if pick(printed) {
			picked = append(picked, printed)
			goalID = g.ID
		}
	}
	require.Len(t, picked, 1, "one open goal's conclusion is picked; picked %v", picked)
	res, err := e.ApplyStep(ctx, s.ID, &ApplyStepRequest{GoalID: goalID, Tactic: tactic})
	require.NoError(t, err)
	require.True(t, res.Success, "%s failed; diagnostics: %v", tactic.Type, res.Diagnostics)
}

// holds picks a conclusion that contains fragment.
func holds(fragment string) func(string) bool {
	return func(conclusion string) bool { return strings.Contains(conclusion, fragment) }
}

// lacks picks a conclusion that does not contain fragment.
func lacks(fragment string) func(string) bool {
	return func(conclusion string) bool { return !strings.Contains(conclusion, fragment) }
}

// hypHolding is the index, among the hypotheses of the open goal pick
// accepts as the kernel orders them, of the one whose print contains
// fragment.
func hypHolding(t *testing.T, e *Engine, s *Session, pick func(string) bool, fragment string) int {
	t.Helper()
	state, err := e.InspectState(context.Background(), s.ID)
	require.NoError(t, err)
	found := -1
	picked := 0
	for _, g := range state.Goals {
		if !pick(ext.PrintTerm(g.Statement.Conclusion())) {
			continue
		}
		picked++
		for i := range g.Statement.NumHyps() {
			if strings.Contains(ext.PrintTerm(g.Statement.Hyp(i)), fragment) {
				require.Equal(t, -1, found, "one hypothesis holds %q", fragment)
				found = i
			}
		}
	}
	require.Equal(t, 1, picked, "one open goal is picked")
	require.NotEqual(t, -1, found, "a hypothesis holds %q", fragment)
	return found
}

// every picks every conclusion.
func every(string) bool { return true }

// emitSoleResult is emitSole with the whole result, for the replay.
func emitSoleResult(t *testing.T, e *Engine, s *Session, funcName string) *EmitSectionResult {
	t.Helper()
	require.True(t, s.sections[0].root.Proved())
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0, IncludePrior: []int{}, FuncName: funcName})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	return out
}

// TestEmitSection_TheHeadlineIsTheChapterSpellingAndTheStripsTheSignature:
// a statement over a module record, whose chapter writes the record's
// operations as `+` and `•`, is emitted in that spelling — not the
// kernel's `mod_add(V, …)` with `var:` type letters — and its opening
// strip is the closure's typed parameters, the claim texts spelling
// the binders' own names: no `ctx.Var("p_0", …)` wall, no
// `StripQuant()` (chain_complex.DoubleBoundaryCoordinate is landed so).
func TestEmitSection_TheHeadlineIsTheChapterSpellingAndTheStripsTheSignature(t *testing.T) {
	e, s := boundSession(t, "algebra/module/chain_complex")
	// The landed member's statement with its degree written p + (q + 1):
	// another key, the same proof.
	const statement = "∀V:module_ops(A, B). ∀h v:(num → num → B → B). ∀s:(num → A). ∀p q:num. ∀u:(num → B). " +
		"double_boundary(V, h, v, s, p + (q + 1), u, p) = h(p + 1, q, u(p + 1)) + s(p) • v(p, q + 1, u(p))"
	addDoorGoal(t, s, statement)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: "p₀ < p₀ + (q₀ + 1) ∧ p₀ + (q₀ + 1) - (p₀ + 1) = q₀ ∧ p₀ + (q₀ + 1) - p₀ = q₀ + 1"})
	applyOnGoalWhere(t, e, s, holds("<"), TacticReq{Type: "by", Arith: true})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{Key: "chain_complex.DoubleBoundaryDef"}}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0)}, ByShape: &ByShapeReq{Normalized: true}})
	out := emitSoleResult(t, e, s, "Build_ZzDoubleBoundaryCoordinateProbe")
	src := out.Go
	assert.Equal(t, statement, headlineOf(t, src), "--- source: ---\n%s", src)
	// One assert is the binary branch the chapter's rule keeps
	// (deriveStaircaseMin): its claim is the Script's text, in the minted
	// spelling that door reads; the labels spell the binders' names.
	for _, want := range []string{
		"\t\tfunc(\n\t\t\ta *Argument,\n\t\t\tV *Expr[ModuleOps[A, B]],\n\t\t\th, v *Expr[Fun3[Nat, Nat, B, B]],\n\t\t\ts *Arrow[Nat, A],\n\t\t\tp, q *Expr[Nat],\n\t\t\tu *Arrow[Nat, B],\n\t\t) {\n",
		"\t\t\t\tAssertStep(ctx.MakePropText(\n\t\t\t\t\t\"p₀ < p₀ + (q₀ + 1) ∧ p₀ + (q₀ + 1) - (p₀ + 1) = q₀ ∧ p₀ + (q₀ + 1) - p₀ = q₀ + 1\"),\n",
		"\t\t\t\t\tCase(\n\t\t\t\t\t\t\"claim: p < p + (q + 1) ∧ p + (q + 1) - (p + 1) = q ∧ p + (q + 1) - p = q + 1\",\n",
		"\t\t\t\t\tCase(\n\t\t\t\t\t\t\"after: double_boundary(V, h, v, s, p + (q + 1), u, \"+\n",
		"\t\t\t\t\t\tSimp(Fwd(DoubleBoundaryDef)),\n\t\t\t\t\t\tBy(\n\t\t\t\t\t\t\tNormalized,\n\t\t\t\t\t\t\tResidentHyp(",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	for _, banned := range []string{"var:", "ctx.Var(", "StripQuant()", "V₀", "V_0"} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
	replayEmittedInFamily(t, "algebra/module/chain_complex", "ZzDoubleBoundaryCoordinateProbe", out)
}

// TestEmitSection_ABundleBinderIsOneTypedFactParameter: a statement
// opening with a bundle binder — `∀φ:ring_homomorphism(A, B).`, the
// structure's two ring records and its map and the antecedent that
// applies it to them — binds the run and its antecedent as ONE
// structure-fact parameter named after the bundle, typed at the
// records' letters, and a law read at the bundle reads at that
// parameter (ring_localization.FractionMapClass is landed so). The
// family states its bundles in the text, so the Law door is not its
// door. The two rings' operations are spelled as fields: `*` is bound
// on both records, so the headline folds neither.
func TestEmitSection_ABundleBinderIsOneTypedFactParameter(t *testing.T) {
	e, s := boundSession(t, "algebra/ring/ring_localization")
	const statement = "∀φ:ring_homomorphism(A, B). ∀a u:A. a ∈ R.carrier ∧ u ∈ R.carrier ⇒ φ(R.mul(a, u)) = S.mul(φ(a), φ(u)) ∧ φ(R.add(a, u)) = S.add(φ(a), φ(u))"
	addDoorGoal(t, s, statement)
	for _, step := range []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	hom, members := hypHolding(t, e, s, every, "ring_homomorphism("), hypHolding(t, e, s, every, "∧")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(members)}, WithLemmas: []LemmaWithSpec{
		{Key: "ring_homomorphism.MapMul", ReadAt: &ReadAtSpec{HypIndex: &hom}},
		{Key: "ring_homomorphism.MapAdd", ReadAt: &ReadAtSpec{HypIndex: &hom}},
	}})
	out := emitSoleResult(t, e, s, "Build_ZzHomPreservesProbe")
	src := out.Go
	assert.Equal(t, statement, headlineOf(t, src), "--- source: ---\n%s", src)
	for _, want := range []string{
		// A binder named a takes the receiver's name: the receiver is arg.
		"\t\tfunc(arg *Argument, φ ring_homomorphism.RingHomomorphismFact[on.R, on.S], a, u *Expr[A], h Fact) {\n",
		"\t\t\targ.Do(\n\t\t\t\tBy(ring_homomorphism.MapMul.Read(φ), ring_homomorphism.MapAdd.Read(φ), h),\n",
		"\t\"github.com/euc-ai/xugo/ext/on\"\n",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	for _, banned := range []string{"Term", "ResidentHyp(", "StripQuant()", "RingOps[", ".Law("} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
	replayEmittedInFamily(t, "algebra/ring/ring_localization", "ZzHomPreservesProbe", out)
}

// TestEmitSection_AStructureAntecedentIsItsTypedFact: an antecedent
// applying a structure on its components' carriers — `module_on(R, M)`
// over two records — binds as that structure's typed fact at the
// carriers' letters, in a family that writes such statements as
// family.Theorem (resolution.CanonicalBoundaryHom is landed so), and a
// law of the structure reads at it. The headline is the session's
// curried goal in the standard form: every binder in front, the
// premises one antecedent, the typed fact's hypothesis among them.
func TestEmitSection_AStructureAntecedentIsItsTypedFact(t *testing.T) {
	e, s := boundSession(t, "algebra/module/resolution")
	const statement = "∀R:ring_ops(A). ∀M:module_ops(A, B). module_on(R, M) ⇒ ∀u v:B. u ∈ M.carrier ∧ v ∈ M.carrier ⇒ R.zero • u = R.zero • v"
	const standard = "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀u v:B. module_on(R, M) ∧ u ∈ M.carrier ∧ v ∈ M.carrier ⇒ R.zero • u = R.zero • v"
	addDoorGoal(t, s, statement)
	for _, step := range []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	module, member := hypHolding(t, e, s, every, "module_on("), hypHolding(t, e, s, every, "v₀ ∈")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(member)}, WithLemmas: []LemmaWithSpec{
		{Key: "module.ZeroSmul", ReadAt: &ReadAtSpec{HypIndex: &module}},
	}})
	out := emitSoleResult(t, e, s, "Build_ZzProbeZeroSmulMember")
	src := out.Go
	assert.Equal(t, standard, headlineOf(t, src), "--- source: ---\n%s", src)
	for _, want := range []string{
		"\t\tfunc(\n\t\t\ta *Argument,\n\t\t\tR *Expr[RingOps[A]],\n\t\t\tM *Expr[ModuleOps[A, B]],\n\t\t\th module.ModuleFact[on.R, on.M],\n\t\t\tu, v *Expr[B],\n\t\t\th2 Fact,\n\t\t) {\n",
		"module.ZeroSmul.Read(h)",
		"\t\"github.com/euc-ai/xugo/library/proofs/algebra/module/module\"\n",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	for _, banned := range []string{"ResidentHyp(", "StripQuant()", "StripImp()", "ctx.Var(", ".Law("} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
	replayEmittedInFamily(t, "algebra/module/resolution", "ZzProbeZeroSmulMember", out)
}

// TestEmitSection_AStructureLawWithItsCardsIsTheDoor: in a family that
// states its members through a structure's door — polynomial's laws
// are `comm_ring.CommRingOn.Law(…)`, its cards
// `family.Card(comm_ring.CommRingOn.Statement(…))` — a section whose
// statement is a law of that structure renders through the door, the
// hypothesis the typed fact, the body's own binders the closure's
// further parameters, and a card the proof deferred renders at the
// door's statement (polynomial_evaluation.EvalHomomorphism and its cards
// EvalAdd, EvalMul are landed so).
func TestEmitSection_AStructureLawWithItsCardsIsTheDoor(t *testing.T) {
	e, s := boundSession(t, "algebra/ring/polynomial/polynomial")
	const statement = "∀R:comm_ring_on(A). ∀x:A. x ∈ R.carrier ⇒ x * (R.one + R.one) = x + x"
	// The card — the distributed product — is asserted ∀-closed, its
	// fields spelled: under the resident ring a second record's `+`
	// would be ambiguous.
	const card = "∀R:ring_ops(A). comm_ring_on(R) ⇒ ∀x:A. x ∈ R.carrier ⇒ " +
		"R.mul(x, R.add(R.one, R.one)) = R.add(R.mul(x, R.one), R.mul(x, R.one))"
	addDoorGoal(t, s, statement)
	for _, step := range []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: card})
	ctx := context.Background()
	state, err := e.InspectState(ctx, s.ID)
	require.NoError(t, err)
	var claim string
	for _, g := range state.Goals {
		if !ext.MatchesFORALL(g.Statement.Conclusion()).IsZero() {
			claim = g.ID
		}
	}
	require.NotEmpty(t, claim, "the asserted law is an open goal")
	deferred, err := e.Defer(ctx, &DeferRequest{SessionID: s.ID, GoalID: claim, Name: "ZzProbeDistrib",
		Note: "a probe card: the product with one + one distributes"})
	require.NoError(t, err)
	require.Equal(t, "deferred", deferred.Status)
	ring := hypHolding(t, e, s, every, "comm_ring_on(R₀")
	member, lemma := hypHolding(t, e, s, every, "x₀ ∈ ring_carrier(R₀)"), hypHolding(t, e, s, every, "∀R")
	// x * one = x is the multiplicative monoid's right identity, read at
	// the ring's monoid read at the hypothesis.
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(member), hyp(lemma)}, WithLemmas: []LemmaWithSpec{
		{Key: "comm_monoid.RightIdentityOn", ReadAt: &ReadAtSpec{Key: "comm_ring.MulMonoidOn", ReadAt: &ReadAtSpec{HypIndex: &ring}}},
	}})
	out := emitSoleResult(t, e, s, "Build_ZzProbeEvalLaw")
	src := out.Go
	for _, want := range []string{
		"\tBuild: comm_ring.CommRingOn.Law(Statement{\n\t\tBinders: \"∀x:A.\",\n\t\tHypotheses: []string{\n\t\t\t\"x ∈ R.carrier\",\n\t\t},\n\t\tConclusion: \"x * (R.one + R.one) = x + x\",\n\t},\n",
		"\t\tfunc(a *Argument, h comm_ring.CommRingFact[on.R], x *Expr[A], h2 Fact) {\n",
		"\tBuild: family.Card(comm_ring.CommRingOn.Statement(Statement{\n\t\tBinders: \"∀x:A.\",\n\t\tHypotheses: []string{\n\t\t\t\"x ∈ R.carrier\",\n\t\t},\n\t\tConclusion: \"x * (R.one + R.one) = x * R.one + x * R.one\",\n\t}),\n",
		"comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(h))",
		"\n\t\t\t\t\t\t\th2,\n",
		"Cite(ZzProbeDistrib)",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	for _, banned := range []string{"family.Theorem(", "family.Card(\"", "ctx.Var(", "StripQuant()", "StripImp()"} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
	replayEmittedInFamily(t, "algebra/ring/polynomial/polynomial", "ZzProbeEvalLaw", out)
}

// TestEmitSection_AClaimKeepsTheTieItsReadBackNeeds: an asserted claim
// over a constant whose type letter no term of the claim fixes —
// `carrier_embedding : B → set(prod(num, prod(A, B)))` applied to a
// vector of B — keeps the `⟨A:A, B:B⟩` tie the session wrote: without
// it the text leaves the letter unpinned, which the Have door refuses
// (resolution.CarrierPreimageEmbedding, session 20d2e157).
func TestEmitSection_AClaimKeepsTheTieItsReadBackNeeds(t *testing.T) {
	e, s := boundSession(t, "algebra/module/resolution")
	const statement = "∀M:module_ops(A, B). ∀b:B. b ∈ M.carrier ⇒ carrier_preimage(M, carrier_embedding(b)) = b ∧ " +
		"carrier_embedding⟨A:A, B:B⟩(carrier_preimage(M, carrier_embedding(b))) = carrier_embedding(b)"
	addDoorGoal(t, s, statement)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: "carrier_preimage(M₀, carrier_embedding(b₀)) = b₀"})
	applyOnGoalWhere(t, e, s, lacks("∧"), TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0)},
		WithLemmas: []LemmaWithSpec{{Key: "resolution.CarrierPreimageEmbedding"}}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert",
		ClaimText: "carrier_embedding⟨A:A, B:B⟩(carrier_preimage(M₀, carrier_embedding(b₀))) = carrier_embedding(b₀)"})
	decoded := hypHolding(t, e, s, lacks("∧"), "= b₀")
	applyOnGoalWhere(t, e, s, lacks("∧"), TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(decoded)}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{
		hyp(hypHolding(t, e, s, every, "= b₀")), hyp(hypHolding(t, e, s, every, "carrier_embedding⟨A:var:A,B:var:B⟩(carrier_preimage"))}})
	out := emitSoleResult(t, e, s, "Build_ZzProbeEmbeddingPin")
	src := out.Go
	assert.Equal(t, statement, headlineOf(t, src), "--- source: ---\n%s", src)
	for _, want := range []string{
		"\t\tfunc(a *Argument, M *Expr[ModuleOps[A, B]], b *Expr[B], h Fact) {\n",
		"\t\t\t\t\"carrier_embedding⟨A:A, B:B⟩(carrier_preimage(M, carrier_embedding(b))) = carrier_embedding(b)\",\n",
		"fact1 := a.Have(\n\t\t\t\t\"carrier_preimage(M, carrier_embedding⟨A:A, B:B⟩(b)) = b\",\n\t\t\t\t\"carrier_preimage(M, carrier_embedding(b)) = b\",\n\t\t\t\tBy(h, CarrierPreimageEmbedding),\n",
		"\t\t\t\tBy(fact1),\n",
		"\t\t\ta.Show(",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	for _, banned := range []string{`"carrier_embedding(carrier_preimage(`, "ctx.Var(", "StripQuant()", "MakePropText("} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
	replayEmittedInFamily(t, "algebra/module/resolution", "ZzProbeEmbeddingPin", out)
}

// TestEmitSection_ALandedStatementKeepsItsAuthoredText: a section
// stating what a landed entry states — a card being filled — is
// emitted under the entry's own text, a set-valued binder spelled
// `set(I)` and a tie on the atom the author tied, where the printer
// spells `(num → I → bool)` and moves the ties onto the head
// (tor_ext.HomComplex, cardinal.ScalarIntoPowerSet). The entry's
// statement_typed types its binders as the author typed a set:
// TensorComplex's is its authored text.
func TestEmitSection_ALandedStatementKeepsItsAuthoredText(t *testing.T) {
	for _, tc := range []struct {
		family, entry, text string
		typedIsText         bool
	}{
		{"algebra/module/tor_ext", "tor_ext.TensorComplex",
			"∀R:ring_ops(A). ∀N:module_ops(A, C). ∀S:(num → set(I)). ∀d:(num → (I → A) → I → A). " +
				"module_on(R, N) ∧ chain_complex(R, free_complex(R, S, d)) ⇒ chain_complex(R, tensor_complex(R, S, d, N))", true},
		{"sets/cardinal", "cardinal.LeftFactorIntoPowerSet", "card_le(𝕌⟨A:A⟩, 𝕌⟨A:set(prod(num, prod(A, B)))⟩)", false},
	} {
		t.Run(tc.entry, func(t *testing.T) {
			entry, ok := registry.ByName(tc.entry)
			require.True(t, ok)
			if tc.typedIsText {
				assert.Equal(t, tc.text, EntryStatementTyped(entry), "the entry's statement_typed")
			}
			e, s := boundSession(t, tc.family)
			addDoorGoal(t, s, tc.text)
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "lemma", LemmaKey: tc.entry})
			src := emitSole(t, e, s, "Build_ZzRestated")
			assert.Equal(t, tc.text, headlineOf(t, src), "--- source: ---\n%s", src)
		})
	}
}

// TestEmitSection_SubscriptedBindersKeepTheirPositions: binders of one
// type whose subscripts the parser spells `x_0`, `x_1`, `x_01` — the
// renamer's own suffix spelling — each lift to their own parameter,
// read off where they occur in the stripped goal, applied under a
// function binder as well as bare.
func TestEmitSection_SubscriptedBindersKeepTheirPositions(t *testing.T) {
	for _, tc := range []struct{ name, statement string }{
		{"terms", "∀x₀ x₁ x₀₁:num. x₀ ≤ x₁ ∧ x₁ ≤ x₀₁ ⇒ x₀ ≤ x₀₁ + 1"},
		{"function applications", "∀f:num → num. ∀x₀ x₁ x₀₁:num. f(x₀) ≤ f(x₁) ∧ f(x₁) ≤ f(x₀₁) ⇒ f(x₀) ≤ f(x₀₁) + 1"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			e, s := boundSession(t, "nat_num/nat_order")
			addDoorGoal(t, s, tc.statement)
			for _, step := range []string{"strip_quant", "strip_imp"} {
				applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
			}
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Arith: true, ByHyps: []ByHypSpec{hyp(0)}})
			out := emitSoleResult(t, e, s, "Build_ZzSubscriptedBoundaryProbe")
			assert.Contains(t, out.Go, "x0, x1, x01 *Expr[Nat], h Fact")
			assert.NotContains(t, out.Go, "ctx.Var(")
			assert.NotContains(t, out.Go, "StripQuant()")
			assert.NotContains(t, out.Go, "StripImp()")
			replayEmittedInFamily(t, "nat_num/nat_order", "ZzSubscriptedBoundaryProbe", out)
		})
	}
}

// A structure fact owned by the output family needs its local alias and
// carrier letters, with no self import or empty package path. The goal
// binds a row q besides the structure's components, so it renders as a
// theorem whose closure takes the typed fact rather than through the
// structure's Law door, and no member of the family states it, so the
// replayed fixture takes no registered key.
func TestEmitSection_SameFamilyStructureFactImports(t *testing.T) {
	e, s := boundSession(t, "simplicial/simplicial_module")
	addDoorGoal(t, s, "∀R:ring_ops(A). ∀V:module_ops(A, B). ∀D:bisimplicial_ops(B). ∀q:num. bisimplicial_module(R, V, D) ⇒ bisimplicial_set(D) ∧ simplicial_module(R, V, bisimplicial_row(D, q))")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0)}, WithLemmas: []LemmaWithSpec{{Key: "simplicial_module.BisimplicialModule", TermSpecialize: map[string]string{"R": "R₀", "V": "V₀", "D": "D₀"}}}})
	out := emitSoleResult(t, e, s, "Build_ZzSameFamilyStructureFact")
	assert.Contains(t, out.Go, "BisimplicialModuleFact[on.R, on.V]")
	assert.Contains(t, out.Go, `"github.com/euc-ai/xugo/ext/on"`)
	assert.NotContains(t, out.Go, "\n\t\"\"\n")
	assert.NotContains(t, out.Go, `"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"`)
	replayEmittedInFamily(t, "simplicial/simplicial_module", "ZzSameFamilyStructureFact", out)
}

// A local typed bundle still uses carrier letters when its fact alias is
// unqualified in the member's own family.
func TestEmitSection_SameFamilyBundleImportsCarrierLetters(t *testing.T) {
	e, s := boundSession(t, "algebra/ring/comm_ring")
	lemmaID := addDoorGoal(t, s, "∀R:comm_ring_on(A). R.one ∈ R.carrier")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	ring := hypHolding(t, e, s, every, "comm_ring_on(")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: "comm_ring.OneIn", ReadAt: &ReadAtSpec{HypIndex: &ring}}}})
	addDoorGoal(t, s, "(∃R:ring_ops(A). comm_ring_on(R)) ⇒ ∃R:ring_ops(A). R.one ∈ R.carrier")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "cite-node", NodeID: lemmaID})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0), hyp(1)}})
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 1, IncludePrior: []int{0}, Family: "algebra/ring/comm_ring", FuncName: "Build_ZzSameFamilyBundle"})
	require.NoError(t, err)
	assert.Contains(t, out.Go, "CommRingFact[on.R]")
	assert.Contains(t, out.Go, `"github.com/euc-ai/xugo/ext/on"`)
	assert.NotContains(t, out.Go, "\n\t\"\"\n")
	assert.NotContains(t, out.Go, `"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"`)
	replayEmittedInFamily(t, "algebra/ring/comm_ring", "ZzSameFamilyBundle", out)
}

// TestEmitSection_ALaterSectionsInnerSkolemLeavesTheLiftsBound: a lemma
// binds `∀h x`, and the theorem that cites it binds `∀h a` and strips a
// `∀x` of its own further down, minting the variable the lemma's strip
// minted. Each section's opening strips are still its closure's typed
// parameters: x₀ is the lemma's parameter x inside the lemma, and the
// script's declaration in the theorem, whose inner strip mints it. No
// closure falls back to `StripQuant()` over a wall of `ctx.Var` lines,
// and no comment suggests a signature.
func TestEmitSection_ALaterSectionsInnerSkolemLeavesTheLiftsBound(t *testing.T) {
	e, s := boundSession(t, "nat_num/nat_order")
	addDoorGoal(t, s, "∀h:(num → num). ∀x:num. h(x) ≤ h(x) + 1")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "arith"})
	require.True(t, s.sections[0].root.Proved(), "the lemma closes")
	lemma := closedNodeID(0, s.sections[0].root.Goal)

	addDoorGoal(t, s, "∀h:(num → num). ∀a:num. a ≤ a + 1 ∧ (∀x:num. h(x) ≤ h(x) + 1 + 1)")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "split_conj"})
	applyOnGoalWhere(t, e, s, lacks("∀"), TacticReq{Type: "arith"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "cite-node", NodeID: lemma, TermSpecialize: map[string]string{"h": "h₀", "x": "x₀"}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "arith"})
	require.True(t, s.sections[1].root.Proved(), "the theorem closes")

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 1, FuncName: "Build_ZzInnerSkolemProbe"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	src := out.Go
	for _, want := range []string{
		"func(a *Argument, h *Arrow[Nat, Nat], x *Expr[Nat]) {",
		"func(arg *Argument, h *Arrow[Nat, Nat], a *Expr[Nat]) {",
		"x_0 := ctx.Var(\"x_0\", NumType)",
		"Cite(lemma1, h, x_0),",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	assert.Equal(t, 1, strings.Count(src, "StripQuant()"), "the theorem's inner strip alone is a step\n--- source: ---\n%s", src)
	for _, banned := range []string{"h_0", "a_0", "can bind them with"} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
	replayEmittedInFamily(t, "nat_num/nat_order", "ZzInnerSkolemProbe", out)
}

// TestEmitSection_AWitnessNoPhantomSpellsIsItsUntypedText: a witness
// whose type no phantom in the family's scope spells — here a term at
// the type letter K, which the family declares no phantom for — is the
// text the Argument's untyped door reads, `a.Term("g(c)")`, and no Go
// expression over declared constants and locals. The member replays.
func TestEmitSection_AWitnessNoPhantomSpellsIsItsUntypedText(t *testing.T) {
	e, s := boundSession(t, "sets/set_order")
	addDoorGoal(t, s, "∀s:set(K). ∀x:K. x ∈ s ⇒ x ∈ s ∪ s")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, ByHyps: []ByHypSpec{hyp(0)}})
	require.True(t, s.sections[0].root.Proved(), "the lemma closes")

	addDoorGoal(t, s, "∀t:set(K). ∀g:(K → K). ∀c:K. g(c) ∈ t ⇒ g(c) ∈ t ∪ t")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0)}, WithLemmas: []LemmaWithSpec{
		{Text: "∀s:set(K). ∀x:K. x ∈ s ⇒ x ∈ s ∪ s", TermSpecialize: map[string]string{"s": "t₀", "x": "g₀(c₀)"}}}})
	require.True(t, s.sections[1].root.Proved(), "the theorem closes")

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 1, FuncName: "Build_ZzUntypedWitnessProbe"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	src := out.Go
	assert.Contains(t, src, `a.Term("g(c)")`, "--- source: ---\n%s", src)
	for _, banned := range []string{".Apply(", "TermAs[", "ctx.Const("} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
	replayEmittedInFamily(t, "sets/set_order", "ZzUntypedWitnessProbe", out)
}

// TestEmitSection_ASectionAtATypeInstanceIsBoundByItsLetters: a lemma
// of the member stated over the letter A and cited at num is the
// section at its letters, `ctx.AtTypeVars(lemma1,
// TypeBinder.BindA[Nat]())`, which names the letter the statement
// spells where `ctx.AtTypes(lemma1, NumType)` counts positions of the
// normalized form. The member replays.
func TestEmitSection_ASectionAtATypeInstanceIsBoundByItsLetters(t *testing.T) {
	e, s := boundSession(t, "sets/set_order")
	const lemma = "∀s:set(A). ∀x:A. x ∈ s ⇒ x ∈ s ∪ s"
	addDoorGoal(t, s, lemma)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, ByHyps: []ByHypSpec{hyp(0)}})
	require.True(t, s.sections[0].root.Proved(), "the lemma closes")

	addDoorGoal(t, s, "∀t:set(num). ∀n:num. n + 1 ∈ t ⇒ n + 1 ∈ t ∪ t")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0)}, WithLemmas: []LemmaWithSpec{{
		Text: lemma, TypeSpecialize: map[string]string{"A": "num"}, TermSpecialize: map[string]string{"s": "t₀", "x": "n₀ + 1"},
	}}})
	require.True(t, s.sections[1].root.Proved(), "the theorem closes")

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 1, FuncName: "Build_ZzSectionAtLettersProbe"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	assert.Contains(t, out.Go, `At(ctx.AtTypeVars(lemma1, TypeBinder.BindA[Nat]()), t, a.TermAs[Nat]("n + 1"))`, "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "ctx.AtTypes(", "--- source: ---\n%s", out.Go)
	replayEmittedInFamily(t, "sets/set_order", "ZzSectionAtLettersProbe", out)
}
