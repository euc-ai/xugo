// unique.go — ∃!-elimination: the one derived rule the equation
// compiler needs that the wrapper toolbox did not already spell.
//
// The primitive definitions make it purely definitional work:
//
//	∃  := λP. P(εP)                          (basic_defs defExists)
//	∃! := λP. ∃x.∀y.(P(y) ⇔ (x = y))         (basic_defs defUnique)
//
// so ⊢ ∃!(P₀) unfolds to a chosen h with ∀y.(P₀(y) ⇔ (h = y)),
// instantiating y := h gives ⊢ P₀(h), and the ε-axiom (core.Select)
// re-introduces the ∃ at P₀'s own choice term. Every step is a
// statement-level wrapper op, so a promise-backed input threads
// through as a derived promise — nothing forces here.

package prop

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// UniqueImpliesExists derives ⊢ ∃x.Φ(x) from ⊢ ∃!x.Φ(x).
//
// Returns nil when the input is not a hyp-free ∃!-headed theorem.
// Every intermediate is β-normalized (DeepBeta) so the definitional
// unfolds, the ε-axiom's redex forms, and the final ∃-refold all meet
// on one α-form; the caller aligns the result to its own target
// arrangement (BridgeNormalize) as usual.
func UniqueImpliesExists(unique Prop) *PropWrapper {
	if unique == nil || unique.NumHyps() != 0 {
		return nil
	}
	app, ok := unique.Conclusion().AsAppliedTerm()
	if !ok {
		return nil
	}
	uniqueC, ok := app.Fun().AsConst()
	if !ok || string(uniqueC.Name()) != utils.UniqueStr {
		return nil
	}
	p0 := app.Arg()

	// ⊢ ∃!(P₀) = ∃x.∀y.(P₀(y) ⇔ (x = y)), then MP: ⊢ ∃(Φ).
	w := ExpandDef(uniqueC, p0).Rewrite(DeepBeta).
		EqMP(WrapProp(unique).Rewrite(DeepBeta))

	exApp, ok := w.Conclusion().AsAppliedTerm()
	if !ok {
		return nil
	}
	existsC, ok := exApp.Fun().AsConst()
	if !ok || string(existsC.Name()) != utils.ExistsStr {
		return nil
	}
	phi := exApp.Arg()

	// Unfold ∃ at Φ: ⊢ ∀y.(P₀(y) ⇔ (h = y)) with h the chosen point.
	w = ExpandDef(existsC, phi).Rewrite(DeepBeta).EqMP(w)
	forAll := ext.MatchesFORALL(w.Conclusion())
	if forAll.IsZero() {
		return nil
	}
	_, rhs, ok := core.MatchesEQ(forAll.Body())
	if !ok {
		return nil
	}
	h, _, ok := core.MatchesEQ(rhs)
	if !ok {
		return nil
	}

	// y := h: ⊢ P₀(h) ⇔ (h = h), so ⊢ P₀(h).
	atH := w.ConclForAllInsts(h).EqSym().EqMP(Refl(h))

	// ε re-introduction: P₀(h) ⊢ P₀(εP₀) (core.Select), discharge the
	// hyp, and fold the ∃ definition backwards.
	selApp, ok := ext.Apply(p0, h).AsAppliedTerm()
	if !ok {
		return nil
	}
	body := WrapProp(core.Select(selApp)).Rewrite(DeepBeta).DeriveHypFrom(atH)

	// The ∃ const at P₀'s own instance: Φ and P₀ share the domain τ
	// (the ∃!-definition binds x : τ), so the earlier occurrence IS
	// the right instance.
	refold := ExpandDef(existsC, p0).Rewrite(DeepBeta)
	return refold.EqSym().EqMP(body)
}
