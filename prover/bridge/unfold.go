package bridge

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/reify"
)

// unfoldTheorem is ⊢ c(a₁, …, aₖ) = body[x₁ := a₁, …, xₖ := aₖ] for a
// constant c whose kernel definition is c = λx₁ … xₖ. body: the
// definition applied to the arguments, each head redex β-reduced and
// nothing further, so an argument that is an abstraction stays applied
// where the body applies its variable. Nil for a term that is not such
// an application: no constant at its head, no definition, or a
// definition that is not an abstraction over as many binders.
func unfoldTheorem(t core.Term) *prop.PropWrapper {
	head, args := ext.MatchesApply(t)
	c, ok := head.AsConst()
	if !ok || len(args) == 0 || isLogical(c) {
		return nil
	}
	def := c.DefThm()
	if def.IsZero() {
		return nil
	}
	l, r, ok := core.MatchesEQ(def.Conclusion())
	if !ok || !l.AlphaEquals(c) {
		return nil
	}
	body := r
	for range args {
		abs, ok := body.AsAbsTerm()
		if !ok {
			return nil
		}
		body = abs.Body()
	}
	w := wrap(def)
	for _, a := range args {
		w = w.RightApply(a)
		_, redex, _ := core.MatchesEQ(w.Conclusion())
		w = w.EqTrans(prop.BetaRewrite(redex))
	}
	return w
}

// isLogical tells whether c is one of the logic's own constants, whose
// definitions the kernel builds its connectives and quantifiers from:
// a proposition reads them as written, never unfolded.
func isLogical(c core.ConstTerm) bool {
	for _, l := range []core.ConstTerm{ext.T, ext.F, ext.NOT, ext.AND, ext.OR, ext.IMPLY, ext.COND, ext.FORALL, ext.EXISTS, ext.UNIQUE} {
		if c.Meta().Equals(l.Meta()) {
			return true
		}
	}
	return false
}

type _DefinitionUnfolder struct{}

// DefinitionUnfolder is the reifier's Unfolder over the kernel's
// definitions: an application of a defined constant unfolds to its
// definition's body at the arguments, as unfoldTheorem reads it, and
// the lemma it names is the constant. It reads the definition the way
// the proof calculus's Unfold does, so it records no dependency; the
// builder proves the node by the same theorem.
func DefinitionUnfolder() reify.Unfolder { return _DefinitionUnfolder{} }

func (_DefinitionUnfolder) Unfold(t core.Term) (core.Term, string, bool) {
	w := unfoldTheorem(t)
	if w == nil {
		return nil, "", false
	}
	head, _ := ext.MatchesApply(t)
	c, _ := head.AsConst()
	_, body, _ := core.MatchesEQ(w.Conclusion())
	return body, string(c.Name()), true
}
