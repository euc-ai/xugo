package bridge

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

// The kernel moves the builder composes, each one rule or a short
// fixed chain of them.

func wrap(p core.Prop) *prop.PropWrapper { return prop.WrapProp(p) }

// assume is h ⊢ h.
func assume(h core.Term) *prop.PropWrapper { return prop.Assume(h) }

// conjoin is Γ ∪ Δ ⊢ l ∧ r from Γ ⊢ l and Δ ⊢ r; where l and r are one
// proposition, ConclAND holds it once and r's proof discharges it.
func conjoin(l, r *prop.PropWrapper) *prop.PropWrapper {
	both := wrap(r.MaybeDeriveTrans(prop.ConclAND(l.Conclusion(), r.Conclusion())))
	return wrap(l.MaybeDeriveTrans(both))
}

// modusPonens is Γ ∪ Δ ⊢ c from Γ ⊢ h ⇒ c and Δ ⊢ h.
func modusPonens(implication, antecedent *prop.PropWrapper) *prop.PropWrapper {
	return antecedent.DeriveTrans(implication.DemoteHyp())
}

// truthOf is ⊢ (h ⇔ ⊤) from ⊢ h.
func truthOf(fact *prop.PropWrapper) *prop.PropWrapper {
	return fact.Deduct(wrap(prop.DerivesTrue))
}

// conjunctionPieces is each conjunct of h, flattened, with its
// derivation h ⊢ piece.
func conjunctionPieces(h core.Term) []*prop.PropWrapper {
	var out []*prop.PropWrapper
	var walk func(t core.Term, from *prop.PropWrapper)
	walk = func(t core.Term, from *prop.PropWrapper) {
		if l, r, ok := ext.MatchesAND(t); ok {
			walk(l, from.DeriveTrans(prop.HypAND0(l, r)))
			walk(r, from.DeriveTrans(prop.HypAND1(l, r)))
			return
		}
		out = append(out, from)
	}
	walk(h, assume(h))
	return out
}

// absorb replaces the hypotheses of t that are conjuncts of h by h
// itself: each conjunct derived from h is cut against t.
func absorb(t *prop.PropWrapper, h core.Term) *prop.PropWrapper {
	for _, piece := range conjunctionPieces(h) {
		if t.HasHyp(piece.Conclusion()) {
			t = piece.DeriveTrans(t)
		}
	}
	return t
}

// discharge is Γ ⊢ h ⇒ c from Γ, h's conjuncts ⊢ c.
func discharge(t *prop.PropWrapper, h core.Term) *prop.PropWrapper {
	return absorb(t, h).PromoteHyp(h)
}

// unary is ⊢ f(a) = f(a') from ⊢ a = a', f read off t = f(a).
func unary(t core.Term, arg *prop.PropWrapper) *prop.PropWrapper {
	app, ok := t.AsAppliedTerm()
	utils.Assert(ok)
	return arg.LeftApply(app.Fun())
}

// binary is ⊢ op(a, b) = op(a', b') from ⊢ a = a' and ⊢ b = b', op
// read off t = op(a, b).
func binary(t core.Term, left, right *prop.PropWrapper) *prop.PropWrapper {
	app, ok := t.AsAppliedTerm()
	utils.Assert(ok)
	inner, ok := app.Fun().AsAppliedTerm()
	utils.Assert(ok)
	return prop.Refl(inner.Fun()).Apply(left).Apply(right)
}

// implicationUnder is Γ ⊢ (g ⇒ a) = (g ⇒ b) from Γ, g ⊢ a = b.
func implicationUnder(g core.Term, eq *prop.PropWrapper) *prop.PropWrapper {
	a, b, ok := core.MatchesEQ(eq.Conclusion())
	utils.Assert(ok)
	forward := eq.EqMP(assume(ext.WrapTerm(g).Imply(a).Core()).DemoteHyp()).PromoteHyp(g)
	backward := eq.EqSym().EqMP(assume(ext.WrapTerm(g).Imply(b).Core()).DemoteHyp()).PromoteHyp(g)
	return backward.Deduct(forward)
}

// forallUnder is Γ ⊢ (∀x. g ⇒ a) = (∀x. g ⇒ b) from Γ, g ⊢ a = b, the
// quantifier read off t = ∀x. g ⇒ a.
func forallUnder(t core.Term, x core.VarTerm, g core.Term, eq *prop.PropWrapper) *prop.PropWrapper {
	app, ok := t.AsAppliedTerm()
	utils.Assert(ok)
	return implicationUnder(g, eq).Abs(x).LeftApply(app.Fun())
}

// instantiate is the theorem at its leading binders' witnesses: its type
// variables matched against the witnesses' types, then its ∀s
// instantiated in order.
func instantiate(t *prop.PropWrapper, witnesses ...core.Term) *prop.PropWrapper {
	t = apart(t, witnesses...)
	list, _ := ext.DecomposesFORALL(t.Conclusion())
	vars := slices.Collect(list.Iter())
	if len(witnesses) > len(vars) {
		panic(fmt.Sprintf("bridge: %d witnesses for a theorem with %d binders: %s", len(witnesses), len(vars), prop.PrintProp(t)))
	}
	var env []core.TypeSubst
	for i, w := range witnesses {
		if !core.MatchTypeInto(vars[i].Type(), w.Type(), utils.FullPredicate, &env) {
			panic(fmt.Sprintf("bridge: witness %s of type %s does not fit binder %s of type %s in %s",
				ext.PrintTerm(w), ext.FormatType(w.Type()), vars[i].Name(), ext.FormatType(vars[i].Type()), prop.PrintProp(t)))
		}
	}
	substs := slices.DeleteFunc(env, func(s core.TypeSubst) bool { return s.HolType.Equals(s.VarType) })
	if len(substs) > 0 {
		t = t.TypeInst(substs...)
	}
	return t.ConclForAllInsts(witnesses...)
}

// typeVarsOf is the type variables of the terms, each once, in the
// order they are met.
func typeVarsOf(terms ...core.Term) []core.VarType {
	var out []core.VarType
	for _, t := range terms {
		ext.TermAnyTypeVar(t, func(v core.VarType) bool {
			if !slices.ContainsFunc(out, func(w core.VarType) bool { return w.Name() == v.Name() }) {
				out = append(out, v)
			}
			return false
		})
	}
	return out
}

// apart renames each type variable of t that the witnesses' types also
// name, so matching t's binders against the witnesses never confuses a
// letter of t with the goal's letter of the same name.
func apart(t *prop.PropWrapper, witnesses ...core.Term) *prop.PropWrapper {
	taken := typeVarsOf(witnesses...)
	own := typeVarsOf(t.Conclusion())
	used := map[core.TypeName]bool{}
	for _, v := range append(slices.Clone(taken), own...) {
		used[v.Name()] = true
	}
	var substs []core.TypeSubst
	for _, v := range own {
		if !slices.ContainsFunc(taken, func(w core.VarType) bool { return w.Name() == v.Name() }) {
			continue
		}
		name := v.Name()
		for used[name] {
			name += "ʹ"
		}
		used[name] = true
		substs = append(substs, core.MakeTypeSubst(v, core.MakeVarType(name)))
	}
	if len(substs) == 0 {
		return t
	}
	return t.TypeInst(substs...)
}

// oriented is ⊢ l = r from a fact whose conclusion is that equation, or
// its symmetric.
func oriented(eq *prop.PropWrapper, l core.Term) *prop.PropWrapper {
	left, right, ok := core.MatchesEQ(eq.Conclusion())
	utils.Assert(ok)
	switch {
	case left.AlphaEquals(l):
		return eq
	case right.AlphaEquals(l):
		return eq.EqSym()
	}
	panic(fmt.Sprintf("bridge: the equation %s has no side %s", prop.PrintProp(eq), ext.PrintTerm(l)))
}

// replace is ⊢ t = t' where t' is t with every outermost subterm α-equal
// to an equation's left side replaced by its right side, the equations
// tried in order at each subterm, once: a replaced subterm is not read
// again, so an equation whose right side holds its left still ends.
func replace(t core.Term, eqs ...*prop.PropWrapper) *prop.PropWrapper {
	if eq := substitute(t, eqs); eq != nil {
		return eq
	}
	return prop.Refl(t)
}

func substitute(t core.Term, eqs []*prop.PropWrapper) *prop.PropWrapper {
	for _, eq := range eqs {
		if l, _, ok := core.MatchesEQ(eq.Conclusion()); ok && l.AlphaEquals(t) {
			return eq
		}
	}
	switch s := t.(type) {
	case core.AppliedTerm:
		f, a := substitute(s.Fun(), eqs), substitute(s.Arg(), eqs)
		if f == nil && a == nil {
			return nil
		}
		if f == nil {
			f = prop.Refl(s.Fun())
		}
		if a == nil {
			a = prop.Refl(s.Arg())
		}
		return f.Apply(a)
	case core.AbsTerm:
		for _, eq := range eqs {
			if !prop.NotFreeInHyps(eq, s.Var()) {
				return nil
			}
		}
		if body := substitute(s.Body(), eqs); body != nil {
			return body.Abs(s.Var())
		}
	}
	return nil
}

// rewriteBy rewrites the conclusion of t by the equations (replace).
func rewriteBy(t *prop.PropWrapper, eqs ...*prop.PropWrapper) *prop.PropWrapper {
	return replace(t.Conclusion(), eqs...).EqMP(t)
}

// reduceRedexes is ⊢ t = t' where every application of the abstraction
// lam in t is β-reduced, and nothing else.
func reduceRedexes(t core.Term, lam core.Term) *prop.PropWrapper {
	return prop.RewriteOrRefl(prop.DeepRewrite(func(s core.Term) *prop.PropWrapper {
		app, ok := s.AsAppliedTerm()
		if !ok || !app.Fun().AlphaEquals(lam) {
			return nil
		}
		return prop.BetaRewrite(s)
	}), t)
}

// sameConclusion asserts that t concludes the expected term up to α,
// naming the node.
func sameConclusion(t *prop.PropWrapper, expected core.Term, what string) {
	if !t.Conclusion().AlphaEquals(expected) {
		panic(fmt.Sprintf("bridge: %s concludes\n  %s\nwhere the plan expects\n  %s", what, ext.PrintTerm(t.Conclusion()), ext.PrintTerm(expected)))
	}
}
