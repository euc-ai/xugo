// canonical_free.go — a sequent's free variables under canonical names.
//
// A recorded artifact that must be found again for any renaming of the
// goal's free variables (the By conditioning plan: its key, and the
// hypothesis and witness terms it stores) is written under names that
// are a function of the goal's α-class alone: the free variables in
// canonicalBinderOrder over the sequent read as the one disjunction
// φ ∨ ¬h₁ ∨ … ∨ ¬hₙ, named %plan0, %plan1, … in that order. Two
// symmetric variables may take either label; the forms they give are
// the same term, so the key and the stored terms agree either way.

package prop

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// canonicalFreePrefix heads the canonical names; `%` keeps them apart
// from every name a text can spell.
const canonicalFreePrefix = "%plan"

// CanonicalFreeRenaming is the substitution that takes p's free
// variables to their canonical names, and the one that takes them back.
func CanonicalFreeRenaming(p Prop) (to, back []core.TermSubst) {
	body := ext.WrapTerm(p.Conclusion())
	for h := range p.HypIter() {
		body = body.Or(ext.Not(h))
	}
	var frees []core.VarTerm
	seen := map[core.TermKey]bool{}
	for _, v := range body.Core().Frees(func(core.VarTerm) bool { return true }) {
		if k := v.AlphaKey(); !seen[k] {
			seen[k] = true
			frees = append(frees, v)
		}
	}
	for i, v := range canonicalBinderOrder(frees, body.Core()) {
		c := ext.Var(core.TermName(fmt.Sprintf("%s%d", canonicalFreePrefix, i)), v.Type()).Core().(core.VarTerm)
		to = append(to, core.MakeTermSubst(v, c))
		back = append(back, core.MakeTermSubst(c, v))
	}
	return to, back
}

// CanonicalFreeKey is p's AlphaKey under its canonical free names: the
// same for p and for p with its free variables renamed.
func CanonicalFreeKey(p Prop) core.PropKey {
	to, _ := CanonicalFreeRenaming(p)
	hyps := make([]core.Term, 0, p.NumHyps())
	for h := range p.HypIter() {
		hyps = append(hyps, h.Substitute(to...))
	}
	return core.MakeProp(p.Conclusion().Substitute(to...), hyps...).AlphaKey()
}
