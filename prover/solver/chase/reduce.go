package chase

// reduce.go — the goals the closer decides by reducing them to chases
// of its own shapes, the same facts it reads when they stand as
// hypotheses: a goal injective_on(A, g) is x = y under fresh x, y and
// the definition's antecedents; a goal exact_at(e, A, B, g, f) is its
// definition's set equation; and a goal S = T between two sets of
// module elements (a module's carrier, an image, a kernel) is, by
// extensionality, the two memberships z ∈ T under z ∈ S and z ∈ S
// under z ∈ T for a fresh z, each its own chase at the same depth. So
// a fact the closer reads in a hypothesis it decides in the goal (the
// manual's Design rules, "A closer's capability is symmetric or
// absent"): onto as image(p, A) = B, exactness, one-to-one.

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// _Reduction is a goal split into sub-goals and the derivation of the
// goal from their theorems.
type _Reduction struct {
	what    string
	subs    []core.Prop
	rebuild func(thms []*prop.PropWrapper) *prop.PropWrapper
}

// freshVar is a variable of type ty named after base, used nowhere in
// the goal and distinct from the variables in also.
func freshVar(goal core.Prop, base string, ty core.HolType, also ...core.VarTerm) core.VarTerm {
	taken := func(name core.TermName) bool {
		for _, v := range also {
			if v.Name() == name {
				return true
			}
		}
		return goal.Conclusion().HasName(name) || goal.AnyHyp(func(h core.Term) bool { return h.HasName(name) })
	}
	name := core.TermName(base)
	for i := 1; taken(name); i++ {
		name = core.TermName(fmt.Sprintf("%s%d", base, i))
	}
	return core.Var(name, ty)
}

// moduleSet reports whether s is a set the closer reads as a set of
// module elements: an image, a kernel, or a term that is not a coset —
// whether it is a module of the diagram is the sub-chase's to read.
func moduleSet(s core.Term) bool {
	if _, ok := headNamed(s, leftCosetName, leftCosetArity); ok {
		return false
	}
	return isSetType(s.Type())
}

// reduceGoal is the goal's reduction, nil for a goal the chase decides
// as it stands.
func reduceGoal(laws *Laws, goal core.Prop) *_Reduction {
	c := goal.Conclusion()
	if args, ok := headNamed(c, injectiveOnName, injectiveOnArity); ok {
		def := lawAt(laws.InjectiveOnDef, args, nil) // injective_on(A, g) ⇔ ∀x y. ante ⇒ x = y
		abs := ext.MatchesFORALL(prop.Rhs(def))
		inner := ext.MatchesFORALL(abs.Body())
		x := freshVar(goal, "x", abs.Var().Type())
		y := freshVar(goal, "y", inner.Var().Type(), x)
		body := inner.Body().Substitute(core.MakeTermSubst(abs.Var(), x), core.MakeTermSubst(inner.Var(), y))
		ante, concl, _ := ext.MatchesIMPLY(body)
		sub := core.MakeProp(concl, append(goal.Hyps(), ante)...)
		return &_Reduction{what: "injectivity on " + ext.PrintTerm(args[0]), subs: []core.Prop{sub},
			rebuild: func(thms []*prop.PropWrapper) *prop.PropWrapper {
				w := thms[0].PromoteHyp(ante).ConclForAll(y).ConclForAll(x)
				return def.EqSym().EqMP(w)
			}}
	}
	if args, ok := headNamed(c, exactAtName, exactAtArity); ok {
		def := lawAt(laws.ExactAtDef, args, nil) // exact_at(…) ⇔ image(g, A) = group_kernel(e, B, f)
		sub := core.MakeProp(prop.Rhs(def), goal.Hyps()...)
		return &_Reduction{what: "exactness at " + ext.PrintTerm(args[2]), subs: []core.Prop{sub},
			rebuild: func(thms []*prop.PropWrapper) *prop.PropWrapper { return def.EqSym().EqMP(thms[0]) }}
	}
	if l, r, ok := core.MatchesEQ(c); ok && moduleSet(l) && moduleSet(r) {
		flat := ext.MatchesFun(l.Type())
		ext_ := lawAt(laws.Extension, []core.Term{l, r}, nil) // l = r ⇔ ∀x. x ∈ l ⇔ x ∈ r
		abs := ext.MatchesFORALL(prop.Rhs(ext_))
		z := freshVar(goal, "z", flat[0])
		inL, inR, _ := core.MatchesEQ(abs.Body().Substitute(core.MakeTermSubst(abs.Var(), z)))
		forward := core.MakeProp(inR, append(goal.Hyps(), inL)...)  // z ∈ l ⊢ z ∈ r
		backward := core.MakeProp(inL, append(goal.Hyps(), inR)...) // z ∈ r ⊢ z ∈ l
		return &_Reduction{what: "the set equation " + ext.PrintTerm(c), subs: []core.Prop{forward, backward},
			rebuild: func(thms []*prop.PropWrapper) *prop.PropWrapper {
				both := thms[1].Deduct(thms[0]) // (z ∈ l) = (z ∈ r)
				return ext_.EqSym().EqMP(both.ConclForAll(z))
			}}
	}
	return nil
}
