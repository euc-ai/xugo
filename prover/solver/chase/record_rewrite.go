package chase

import (
	"fmt"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// RecordRewrites holds proved, universally quantified defining equations in
// their forward direction. Every field is optional. Named fields preserve the
// individual theorem roots when the serve layer computes the capability.
type RecordRewrites struct {
	RingAdd, RingZero, RingNeg, RingMul, RingOne, RingSub, RingCarrier                  *prop.PropWrapper
	ModuleAdd, ModuleZero, ModuleNeg, ModuleSmul, ModuleCarrier                         *prop.PropWrapper
	ComplexAdd, ComplexZero, ComplexNeg, ComplexSmul, ComplexTerms, ComplexDifferential *prop.PropWrapper
	RestrictModule, QuotientModule, ComplexModule, HomologyModule, HomologyCarrier      *prop.PropWrapper
	CohomologyModule, CohomologyCarrier                                                 *prop.PropWrapper
}

func (r RecordRewrites) rewrite() prop.Rewrite {
	rules := map[core.ConstTermMeta][]prop.Rewrite{}
	for _, law := range []*prop.PropWrapper{
		r.RingAdd, r.RingZero, r.RingNeg, r.RingMul, r.RingOne, r.RingSub, r.RingCarrier,
		r.ModuleAdd, r.ModuleZero, r.ModuleNeg, r.ModuleSmul, r.ModuleCarrier,
		r.ComplexAdd, r.ComplexZero, r.ComplexNeg, r.ComplexSmul, r.ComplexTerms, r.ComplexDifferential,
		r.RestrictModule, r.QuotientModule, r.ComplexModule, r.HomologyModule, r.HomologyCarrier,
		r.CohomologyModule, r.CohomologyCarrier,
	} {
		if law != nil {
			rewrite := recordDefinition(law)
			_, body := stripForalls(law.Conclusion())
			lhs, _, _ := core.MatchesEQ(body)
			head, _ := ext.MatchesApply(lhs)
			c, ok := head.AsConst()
			if !ok {
				panic("chase: a record definition must have a constant head")
			}
			rules[c.Meta()] = append(rules[c.Meta()], rewrite)
		}
	}
	return prop.DeepRewrite(func(t core.Term) *prop.PropWrapper {
		head, _ := ext.MatchesApply(t)
		c, ok := head.AsConst()
		if !ok {
			return nil
		}
		for _, rule := range rules[c.Meta()] {
			if eq := rule(t); eq != nil {
				return eq
			}
		}
		return nil
	})
}

// recordDefinition matches a defining equation's left side structurally,
// instantiates its quantified variables and types, and returns that theorem.
// It never computes a projection without its supplied equation.
func recordDefinition(law *prop.PropWrapper) prop.Rewrite {
	vars, body := stripForalls(law.Conclusion())
	lhs, _, ok := core.MatchesEQ(body)
	if !ok || len(law.Hyps()) != 0 {
		panic("chase: a record rewrite must be a closed defining equation")
	}
	return func(t core.Term) *prop.PropWrapper {
		values := make([]core.Term, len(vars))
		var types []core.TypeSubst
		var match func(core.Term, core.Term) bool
		match = func(p, q core.Term) bool {
			if !core.MatchTypeInto(p.Type(), q.Type(), func(core.VarType) bool { return true }, &types) {
				return false
			}
			if v, ok := p.AsVar(); ok {
				for i, binder := range vars {
					if !v.EqualsVar(binder) {
						continue
					}
					if values[i] == nil {
						values[i] = q
						return true
					}
					return values[i].AlphaEquals(q)
				}
				return p.AlphaEquals(q)
			}
			if c, ok := p.AsConst(); ok {
				other, ok := q.AsConst()
				return ok && c.Meta() == other.Meta()
			}
			if a, ok := p.AsAppliedTerm(); ok {
				other, ok := q.AsAppliedTerm()
				return ok && match(a.Fun(), other.Fun()) && match(a.Arg(), other.Arg())
			}
			return false
		}
		if !match(lhs, t) {
			return nil
		}
		for _, value := range values {
			if value == nil {
				panic("chase: a record definition has a binder absent from its left side")
			}
		}
		types = slices.DeleteFunc(types, func(s core.TypeSubst) bool { return s.HolType.Equals(s.VarType) })
		w := law
		if len(types) > 0 {
			w = w.TypeInst(types...)
		}
		w = w.ConclForAllInsts(values...)
		if !prop.Lhs(w).AlphaEquals(t) {
			panic(fmt.Sprintf("chase: record rewrite instance does not match %v", t))
		}
		if prop.Rhs(w).AlphaEquals(t) {
			return nil
		}
		return w
	}
}

// RewriteRecords is a term's normal form as the closer reads the leaf:
// the supplied record definitions reduced, its record projections
// computed through reader, every application of a λ computed
// (Laws.reading). The caller must authorize the chase capability before
// using its theorem.
func RewriteRecords(t core.Term, reader *omega.LibraryReader) *prop.PropWrapper {
	laws := Installed()
	if laws == nil {
		return nil
	}
	return laws.reading(reader).leaf(t)
}
