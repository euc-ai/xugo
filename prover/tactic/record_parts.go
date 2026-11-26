package tactic

// record_parts.go — the record reading at the refuter's own
// instantiations.
//
// The instance normal form (instance_normal.go) is computed at every
// instantiation boundary the proof calculus owns: a specialize, a read,
// an unfold, a Simp rewrite. The refuter instantiates on its own — a
// clause with a variable of a record type is instantiated at whatever
// record value unification offers — and a projection of the variable,
// `X.s` at X := simplicial_fiber(…), becomes a redex the refuter has no
// equation for. RecordPartsTactic hands it those equations ahead of the
// search: for every projection the leaf applies to a bound variable and
// every record value of that variable's type the leaf spells — a
// constructor or a definition a projection reads through, applied in
// full, ground in the leaf — the part equation `p(v) = part`, as a
// hypothesis of the leaf. The result is a function of the leaf and the
// installed table, so the By stage runs it on every path and records
// nothing. An equation is read through the record equations as the
// proof's own cite only where the close used it: the reconstruction
// reads the ones the child's theorem still assumes, so the recorded
// dependencies hold no equation the refutation did not need.

import (
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// RecordPartsTactic installs the part equations of the record values a
// leaf spells (above); read is the proof's read of a record equation,
// and a nil read reads through the installed fallback. One child, the
// leaf with the equations among its hypotheses; nil where no equation
// is new to it.
func RecordPartsTactic(read LibraryRead) Tactic {
	tb := installedRecords.Load()
	if tb == nil || len(tb.projections) == 0 || tb.fallback == nil {
		return func(Prop) *SubGoals { return nil }
	}
	if read == nil {
		read = tb.fallback
	}
	// The equations are found through the fallback, which reads each
	// entry as stated and records nothing; the reconstruction reads the
	// ones the close used through read.
	find := InstanceNormal(tb.fallback)
	return func(goal Prop) *SubGoals {
		values, projections := tb.recordParts(goal)
		var parts []core.Term
		var equations []core.Term
		for _, v := range values {
			for _, p := range projections {
				var env []core.TypeSubst
				if !core.MatchTypeInto(ext.MatchesFun(p.Type())[0], v.Type(), everyLetter, &env) {
					continue
				}
				applied := core.Apply(p.TypeSubstitute(env...), v)
				bridge := find(applied)
				if bridge == nil || prop.Rhs(bridge).AlphaEquals(applied) {
					continue
				}
				equation := bridge.Conclusion()
				if goal.AnyHyp(equation.AlphaEquals) || slices.ContainsFunc(equations, equation.AlphaEquals) {
					continue
				}
				parts = append(parts, applied)
				equations = append(equations, equation)
			}
		}
		if len(equations) == 0 {
			return nil
		}
		child := MakeProp(goal.Conclusion(), append(goal.Hyps(), equations...)...)
		reconstruct := func(thms ...Prop) Prop {
			result := prop.WrapProp(thms[0])
			for i, equation := range equations {
				if result.HasHyp(equation) {
					result = InstanceNormal(read)(parts[i]).DeriveTrans(result)
				}
			}
			return result
		}
		return MakeTrackedSubGoals(goal, reconstruct, [][]int{keptSuccessors(goal, child)}, child)
	}
}

// everyLetter instantiates every type variable of a projection's type.
func everyLetter(core.VarType) bool { return true }

// recordParts is the record values and the projections of a leaf the
// tactic pairs: the projections the leaf applies to a bound variable,
// each at its type instance; and the values, ground in the leaf, whose
// head is a constructor or a definition a projection reads through,
// applied in full, of the type one of those projections reads. Both in
// the kernel's term order, without repetition.
func (tb *recordTable) recordParts(goal Prop) (values []core.Term, projections []core.ConstTerm) {
	frees := map[core.TermName]bool{}
	forEachTerm(goal, func(t core.Term) {
		for _, v := range t.Frees(nil) {
			frees[v.Name()] = true
		}
	})
	ground := func(t core.Term) bool {
		return t.AllFree(func(v core.VarTerm) bool { return frees[v.Name()] })
	}
	named := tb.namedValues(goal)
	forEachTerm(goal, func(t core.Term) {
		walkBound(t, nil, func(s core.Term, bound []core.TermName) {
			head, args := ext.MatchesApply(s)
			c, ok := head.AsConst()
			if !ok {
				return
			}
			if len(tb.projections[string(c.Name())]) > 0 && len(args) > 0 {
				if x, isVar := args[0].AsVar(); isVar && (slices.Contains(bound, x.Name()) || named[x.Name()]) {
					projections = append(projections, c)
				}
				return
			}
			if arity, isValue := tb.arity[string(c.Name())]; isValue && len(args) == arity && ground(s) {
				values = append(values, s)
			}
		})
	})
	slices.SortFunc(projections, func(a, b core.ConstTerm) int { return a.Compare(b) })
	projections = slices.CompactFunc(projections, func(a, b core.ConstTerm) bool { return a.Equals(b) })
	values = slices.DeleteFunc(values, func(v core.Term) bool {
		return !slices.ContainsFunc(projections, func(p core.ConstTerm) bool {
			var env []core.TypeSubst
			return core.MatchTypeInto(ext.MatchesFun(p.Type())[0], v.Type(), everyLetter, &env)
		})
	})
	slices.SortFunc(values, core.Term.Compare)
	values = slices.CompactFunc(values, core.Term.Equals)
	return values, projections
}

// namedValues is the free variables a hypothesis of the leaf equates
// with a record value applied in full: the names a Let gives such a
// value, `Zn = free_module_record(R, S)`. A projection of one is a
// projection of the value, which the refuter reaches by the equation
// once it holds the value's part.
func (tb *recordTable) namedValues(goal Prop) map[core.TermName]bool {
	named := map[core.TermName]bool{}
	isValue := func(t core.Term) bool {
		head, args := ext.MatchesApply(t)
		c, ok := head.AsConst()
		if !ok {
			return false
		}
		arity, valued := tb.arity[string(c.Name())]
		return valued && len(args) == arity
	}
	for i := range goal.NumHyps() {
		l, r, ok := ext.MatchesEQ(goal.Hyp(i))
		if !ok {
			continue
		}
		if x, isVar := l.AsVar(); isVar && isValue(r) {
			named[x.Name()] = true
		}
		if x, isVar := r.AsVar(); isVar && isValue(l) {
			named[x.Name()] = true
		}
	}
	return named
}

// forEachTerm visits a proposition's conclusion and hypotheses.
func forEachTerm(goal Prop, visit func(core.Term)) {
	visit(goal.Conclusion())
	for i := range goal.NumHyps() {
		visit(goal.Hyp(i))
	}
}

// walkBound visits every subterm of t, t first, under abstractions
// included, with the names the abstractions around it bind.
func walkBound(t core.Term, bound []core.TermName, visit func(core.Term, []core.TermName)) {
	visit(t, bound)
	if app, ok := t.AsAppliedTerm(); ok {
		walkBound(app.Fun(), bound, visit)
		walkBound(app.Arg(), bound, visit)
	} else if abs, ok := t.AsAbsTerm(); ok {
		walkBound(abs.Body(), append(slices.Clip(bound), abs.Var().Name()), visit)
	}
}
