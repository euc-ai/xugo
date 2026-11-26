package engine

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// stripCurried strips a curried statement `∀…. H ⇒ ∀…. H′ ⇒ C` down to
// C, as a session does: two strip_quant / strip_imp pairs.
func stripCurried(t *testing.T, e *Engine, sid string) {
	t.Helper()
	for _, tactic := range []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"} {
		applyOnSoleGoal(t, e, sid, TacticReq{Type: tactic})
	}
}

// sectionOf is the rendering of the section opened by `open` in a
// family.Sections member: from that line to the next section's.
func sectionOf(t *testing.T, src, open string) string {
	t.Helper()
	at := strings.Index(src, open)
	require.GreaterOrEqual(t, at, 0, "the member opens %q:\n%s", open, src)
	rest := src[at+len(open):]
	if end := strings.Index(rest, "ctx.Theorem("); end >= 0 && !strings.Contains(open, "ctx.Theorem(") {
		rest = rest[:end]
	}
	return rest
}

// A local lemma's interleaved binders and guards are the strips its
// section opens with: they are its closure's parameters, and its
// statement is the standard form, as a member of one section binds
// them.
func TestEmitSection_LocalCurriedTelescope(t *testing.T) {
	e, s := boundSession(t, "sets/set_order")
	addTextGoal(t, s, "∀s t:set(A). s ⊆ t ⇒ ∀x:A. x ∈ s ⇒ x ∈ t")
	stripCurried(t, e, s.ID)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, ByHyps: []ByHypSpec{hyp(0), hyp(1)}})
	addTextGoal(t, s, "∀s t:set(prod(num, bool)). s ⊆ t ⇒ ∀x:prod(num, bool). x ∈ s ⇒ x ∈ t")
	require.True(t, proof.ApplyTypeInst(s.sections[1].root, s.sections[0].root.PromisedThm()))
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 1, IncludePrior: []int{0}, Family: "sets/set_order", FuncName: "Build_ZzCurriedSection"})
	require.NoError(t, err)
	lemma := sectionOf(t, out.Go, "lemma1 := ctx.Lemma(")
	require.Contains(t, lemma, `Binders: "∀s t:set(A). ∀x:A.",`)
	require.Contains(t, lemma, "func(a *Argument, s, t *Expr[Set[A]], h Fact, x *Expr[A], h2 Fact)")
	require.NotContains(t, lemma, "StripQuant()")
	replayEmittedInFamily(t, "sets/set_order", "ZzCurriedSection", out)
}

// A new public member keeps a standard headline while its proof opens
// the session's interleaved telescope: the strips are its closure's
// parameters.
func TestEmitSection_PublicCurriedTelescope(t *testing.T) {
	e, s := boundSession(t, "sets/set_order")
	addTextGoal(t, s, "∀s t:set(A). s ⊆ t ⇒ ∀x:A. x ∈ s ⇒ x ∈ t ∧ s ⊆ t")
	stripCurried(t, e, s.ID)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, ByHyps: []ByHypSpec{hyp(0), hyp(1)}})
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0, Family: "sets/set_order", FuncName: "Build_ZzCurriedTarget"})
	require.NoError(t, err)
	require.Contains(t, out.Go, `Binders: "∀s t:set(A). ∀x:A.",`)
	require.Contains(t, out.Go, "func(a *Argument, s, t *Expr[Set[A]], h Fact, x *Expr[A], h2 Fact)")
	require.NotContains(t, out.Go, "StripQuant()")
	replayEmittedInFamily(t, "sets/set_order", "ZzCurriedTarget", out)
}

// A member of several sections whose TARGET is curried: the target's
// interleaved strips are its closure's parameters as a lemma's are, so
// its standard headline binds the telescope its proof runs against.
func TestEmitSection_CurriedTargetSections(t *testing.T) {
	e, s := boundSession(t, "sets/set_order")
	const flat = "∀s t:set(A). ∀x:A. s ⊆ t ∧ x ∈ s ⇒ x ∈ t"
	addTextGoal(t, s, flat)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, ByHyps: []ByHypSpec{hyp(0)}})
	addTextGoal(t, s, "∀s t u:set(A). s ⊆ t ∧ t ⊆ u ⇒ ∀x:A. x ∈ s ⇒ x ∈ u")
	stripCurried(t, e, s.ID)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0), hyp(1)}, WithLemmas: []LemmaWithSpec{{Text: flat}}})
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 1, IncludePrior: []int{0}, Family: "sets/set_order", FuncName: "Build_ZzCurriedTargetSections"})
	require.NoError(t, err)
	require.Contains(t, out.Go, `Binders: "∀s t u:set(A). ∀x:A.",`)
	target := sectionOf(t, out.Go, "return ctx.Theorem(headline,")
	require.Contains(t, target, "func(a *Argument, s, t, u *Expr[Set[A]], h Fact, x *Expr[A], h2 Fact)")
	require.NotContains(t, out.Go, "StripQuant()")
	replayEmittedInFamily(t, "sets/set_order", "ZzCurriedTargetSections", out)
}

// A section whose opening strips the lift cannot bind — a binder named
// as the member's scaffold binds a Go name — runs them as steps against
// its statement as the session states it, and keeps that text; in a
// member of several sections that is the one section's, whatever its
// place: the target beside it, whose Skolems it does not mention, is
// still lifted and restated.
func TestEmitSection_UnliftedStripsKeepSessionText(t *testing.T) {
	const unliftable = "∀s t:set(A). s ⊆ t ⇒ ∀env:A. env ∈ s ⇒ env ∈ t"
	t.Run("one_section", func(t *testing.T) {
		e, s := boundSession(t, "sets/set_order")
		addTextGoal(t, s, unliftable)
		stripCurried(t, e, s.ID)
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, ByHyps: []ByHypSpec{hyp(0), hyp(1)}})
		out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0, Family: "sets/set_order", FuncName: "Build_ZzUnliftedTarget"})
		require.NoError(t, err)
		require.Contains(t, out.Go, `family.Theorem("∀s t:set(A). s ⊆ t ⇒ ∀env:A. env ∈ s ⇒ env ∈ t"`)
		require.Contains(t, out.Go, "StripQuant()")
		replayEmittedInFamily(t, "sets/set_order", "ZzUnliftedTarget", out)
	})
	t.Run("lemma_section", func(t *testing.T) {
		e, s := boundSession(t, "sets/set_order")
		addTextGoal(t, s, unliftable)
		stripCurried(t, e, s.ID)
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, ByHyps: []ByHypSpec{hyp(0), hyp(1)}})
		addTextGoal(t, s, "∀p q r:set(A). p ⊆ q ∧ q ⊆ r ⇒ ∀y:A. y ∈ p ⇒ y ∈ r")
		stripCurried(t, e, s.ID)
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0), hyp(1)}, WithLemmas: []LemmaWithSpec{{Text: unliftable}}})
		out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 1, IncludePrior: []int{0}, Family: "sets/set_order", FuncName: "Build_ZzUnliftedLemma"})
		require.NoError(t, err)
		lemma := sectionOf(t, out.Go, "lemma1 := ctx.Lemma(")
		require.Contains(t, lemma, `"∀s t:set(A). s ⊆ t ⇒ ∀env:A. env ∈ s ⇒ env ∈ t"`)
		require.Contains(t, lemma, "func(a *Argument) {")
		require.Contains(t, lemma, "StripQuant()")
		require.Contains(t, out.Go, `Binders: "∀p q r:set(A). ∀y:A.",`)
		target := sectionOf(t, out.Go, "return ctx.Theorem(headline,")
		require.Contains(t, target, "func(a *Argument, p, q, r *Expr[Set[A]], h Fact, y *Expr[A], h2 Fact)")
		replayEmittedInFamily(t, "sets/set_order", "ZzUnliftedLemma", out)
	})
}

// A Skolem two sections mint is the parameter of the closure that binds
// it and the script's declaration elsewhere: a lemma that cannot lift
// its strips — a binder named `env` — runs them as steps over the
// declared s₀ and t₀, and the target, whose strips mint the same two,
// still binds them as its parameters.
func TestEmitSection_SharedSkolemsLiftAlike(t *testing.T) {
	e, s := boundSession(t, "sets/set_order")
	const unliftable = "∀s t:set(A). s ⊆ t ⇒ ∀env:A. env ∈ s ⇒ env ∈ t"
	addTextGoal(t, s, unliftable)
	stripCurried(t, e, s.ID)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, ByHyps: []ByHypSpec{hyp(0), hyp(1)}})
	addTextGoal(t, s, "∀s t u:set(A). s ⊆ t ∧ t ⊆ u ⇒ ∀y:A. y ∈ s ⇒ y ∈ u")
	stripCurried(t, e, s.ID)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0), hyp(1)}, WithLemmas: []LemmaWithSpec{{Text: unliftable}}})
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 1, IncludePrior: []int{0}, Family: "sets/set_order", FuncName: "Build_ZzSharedSkolems"})
	require.NoError(t, err)
	lemma := sectionOf(t, out.Go, "lemma1 := ctx.Lemma(")
	require.Contains(t, lemma, "func(a *Argument) {")
	require.Contains(t, lemma, "StripQuant()")
	target := sectionOf(t, out.Go, "return ctx.Theorem(headline,")
	require.Contains(t, target, "func(a *Argument, s, t, u *Expr[Set[A]], h Fact, y *Expr[A], h2 Fact) {")
	require.NotContains(t, target, "StripQuant()")
	require.Contains(t, out.Go, `Binders: "∀s t u:set(A). ∀y:A.",`)
	replayEmittedInFamily(t, "sets/set_order", "ZzSharedSkolems", out)
}

// An intermediate fact can precede the remaining guarded binders. The
// standard headline and partial callback bind the same dependencies.
func TestEmitSection_AHaveBeforeCurriedTailReplays(t *testing.T) {
	e, s := boundSession(t, "sets/set_order")
	const statement = "∀s t u:set(A). s ⊆ t ∧ t ⊆ u ⇒ ∀x:A. x ∈ s ⇒ x ∈ u ∧ s ⊆ u"
	addTextGoal(t, s, statement)
	for _, step := range []string{"strip_quant", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: "s₀ ⊆ u₀"})
	applyOnGoalWhere(t, e, s, lacks("∀"), TacticReq{Type: "by", Settac: true, ByHyps: []ByHypSpec{hyp(0)}})
	for _, step := range []string{"strip_quant", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	transitive := hypHolding(t, e, s, every, "s₀ ⊆ u₀")
	member := hypHolding(t, e, s, every, "x₀ ∈ s₀")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, ByHyps: []ByHypSpec{hyp(transitive), hyp(member)}})
	out := emitSoleResult(t, e, s, "Build_ZzHaveBeforeCurriedTail")
	require.Contains(t, out.Go, `Binders: "∀s t u:set(A). ∀x:A.",`)
	require.Contains(t, out.Go, "func(a *Argument, s, t, u *Expr[Set[A]], h Fact)")
	require.Contains(t, out.Go, "StripQuant()")
	replayEmittedInFamily(t, "sets/set_order", "ZzHaveBeforeCurriedTail", out)
}
