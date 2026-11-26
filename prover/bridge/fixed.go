package bridge

import (
	"math/big"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/unify"
)

// The degree-bound lemmas the fixed-parameter form cites, as
// family.Member.
const (
	lemmaCommonBound      = "polynomial_encoding.CommonDegreeBound"
	lemmaBoundMono        = "polynomial_encoding.PolynomialBoundMono"
	lemmaTupleOfPolynomal = "polynomial_encoding.TupleOfPolynomial"
)

// fixed is the fixed-parameter form .At: the property the source
// states, at the goal's structure, unfolds to ∀ binders. guards ⇒
// consequent; at the call's parameters the consequent is the goal,
// which settles every argument of the property but the degree bound.
// Each guard bounding a parameter's degree by it is met by
// CommonDegreeBound from the parameter's membership in the polynomial
// algebra, the bounds pooled as their sum; the property is transferred
// at that bound as a sentence, unfolded, and instantiated at the
// parameters, the other guards met by the call's facts.
//
// The source is an entry, ∀ data. Φ(S, data), or a family of models by
// prime with the property's data bound ahead of the prime, ∀ data. ∀p.
// nat_prime(p) ⇒ ∃G. algebraically_closed_field_on(G) ∧
// field_characteristic(G, p) ∧ Φ(G, data); the family is instantiated
// at the data the goal and the bound settle and transfers the property
// at them (family).
func (x *_Executor) fixed(target _Structure) (*prop.PropWrapper, error) {
	var list ext.VarList
	var body core.Term
	var models *prop.PropWrapper
	if x.call.Source.Family != nil {
		models = wrap(x.call.Source.Family)
		var ok bool
		if list, body, ok = familyData(models.Conclusion()); !ok {
			return nil, refuse("the source is not a family of models by prime, ∀data. ∀p. nat_prime(p) ⇒ ∃G. algebraically_closed_field_on(G) ∧ field_characteristic(G, p) ∧ Φ(G, data): %s", ext.PrintTerm(models.Conclusion()))
		}
	} else {
		list, body = ext.DecomposesFORALL(wrap(x.lib.Theorem(x.call.Source.Entry)).Conclusion())
	}
	property, open, data, err := x.propertyPattern(list, body, target)
	if err != nil {
		return nil, err
	}
	def := unfoldTheorem(property)
	if def == nil {
		return nil, refuse("the source's property %s has no definition .At can unfold", ext.PrintTerm(property))
	}
	_, unfolded, _ := core.MatchesEQ(def.Conclusion())
	guards, consequent, err := x.atParams(unfolded)
	if err != nil {
		return nil, err
	}
	names := unify.TermNameSet{}
	for _, v := range open {
		names.Add(v.Name())
	}
	bindings, ok := unify.TermMatch(consequent, x.call.Goal, names)
	if !ok {
		return nil, refuse("at the parameters the property concludes another proposition than the goal:\n  goal:     %s\n  property: %s", ext.PrintTerm(x.call.Goal), ext.PrintTerm(consequent))
	}
	var substs []core.TermSubst
	var bound core.VarTerm
	for _, v := range open {
		if w, hit := bindings[v.Name()]; hit {
			substs = append(substs, core.MakeTermSubst(v, w))
			continue
		}
		if !bound.IsZero() {
			return nil, refuse("the goal leaves two arguments of the property open, %s and %s; .At settles one, the degree bound", bound.Name(), v.Name())
		}
		bound = v
	}
	property = property.Substitute(substs...)
	if guards != nil {
		guards = guards.Substitute(substs...)
	}

	var degrees []*prop.PropWrapper
	var witnesses []_Witness
	if !bound.IsZero() {
		if guards == nil {
			return nil, refuse("the goal leaves the property's argument %s open, and the property has no guard bounding a parameter's degree by it", bound.Name())
		}
		var dg []_DegreeGuard
		for _, piece := range conjunctionPieces(guards) {
			g := piece.Conclusion()
			if !g.HasFree(bound) {
				continue
			}
			parsed, ok := degreeGuard(g, bound)
			if !ok {
				return nil, refuse("the guard %s names the degree bound %s other than as a parameter's degree bound", ext.PrintTerm(g), bound.Name())
			}
			dg = append(dg, parsed)
		}
		if len(dg) == 0 {
			return nil, refuse("the goal leaves the property's argument %s open, and no guard bounds a parameter's degree by it", bound.Name())
		}
		for _, g := range dg {
			if g.tuple && len(dg) > 1 {
				return nil, refuse("the property bounds the length of %s and another parameter by its argument %s; .At pools degree bounds, not a polynomial's length", ext.PrintTerm(g.family), bound.Name())
			}
		}
		for _, g := range dg {
			w, err := x.commonBound(g, witnesses)
			if err != nil {
				return nil, err
			}
			witnesses = append(witnesses, w)
		}
		var d core.Term = witnesses[0].bound
		for _, w := range witnesses[1:] {
			d = constantCall(x.lib, "+", d, w.bound)
		}
		at := core.MakeTermSubst(bound, d)
		substs = append(substs, at)
		for i, g := range dg {
			degrees = append(degrees, x.degreeAt(g, witnesses[i], d, len(dg) > 1, g.statement.Substitute(at)))
		}
		property = property.Substitute(at)
		if guards != nil {
			guards = guards.Substitute(at)
		}
	}

	var transferred *prop.PropWrapper
	if models != nil {
		var values []core.Term
		for v := range list.Iter() {
			i := slices.IndexFunc(data, v.EqualsVar)
			if i < 0 {
				return nil, refuse("the family's datum %s is not an argument of the property", v.Name())
			}
			values = append(values, core.Term(open[i]).Substitute(substs...))
		}
		transferred, err = x.family(target.F, wrap(models.ConclForAllInsts(values...)), property)
	} else {
		transferred, err = x.entry(target, property)
	}
	if err != nil {
		return nil, err
	}
	opened := unfoldTheorem(property).EqMP(transferred).ConclForAllInsts(x.call.Params...).RewriteConcl(prop.DeepBeta)
	if guards != nil {
		available := append(degrees, x.facts...)
		met := fromPieces(guards, available)
		if met == nil {
			return nil, refuse("no fact meets the property's guard at the parameters: %s", ext.PrintTerm(firstUnmet(guards, available)))
		}
		opened = modusPonens(opened, met)
	}
	sameConclusion(opened, x.call.Goal, "the property at the parameters")
	for i := len(witnesses) - 1; i >= 0; i-- {
		w := witnesses[i]
		opened = w.exists.DeriveTrans(opened.HypExists(w.bound, w.body))
	}
	return opened, nil
}

// propertyPattern is the source's property, body under the source's
// leading binders list, at the goal's structure, each argument the
// source quantifies a fresh variable of its own: the open variables, in
// the property's argument order, beside the binder each stands for.
func (x *_Executor) propertyPattern(list ext.VarList, body core.Term, target _Structure) (core.Term, []core.VarTerm, []core.VarTerm, error) {
	head, sArgs := ext.MatchesApply(body)
	c, ok := head.AsConst()
	if !ok || len(sArgs) == 0 {
		return nil, nil, nil, refuse("the source states no property of its structure: %s", ext.PrintTerm(body))
	}
	structure := []core.Term{target.F}
	if target.lt != nil {
		structure = append(structure, target.lt)
	}
	avoid := append([]core.Term{x.call.Goal}, x.call.Params...)
	for _, f := range x.facts {
		avoid = append(avoid, f.Conclusion())
	}
	var args []core.Term
	var open, data []core.VarTerm
	next := 0
	for i, a := range sArgs {
		if v, isVar := a.AsVar(); isVar && list.Has(v) {
			if !v.Type().Equals(ext.NumType) {
				return nil, nil, nil, refuse("the source quantifies %s of type %s; a source's binders are its property's numeric data", v.Name(), ext.FormatType(v.Type()))
			}
			w := core.Var(v.Name(), v.Type()).RenameToAvoid(avoid...)
			avoid = append(avoid, w)
			open = append(open, w)
			data = append(data, v)
			args = append(args, w)
			continue
		}
		if next == len(structure) {
			return nil, nil, nil, refuse("the source fixes argument %d of its property, %s, which is neither its structure nor a binder", i, ext.PrintTerm(a))
		}
		args = append(args, structure[next])
		next++
	}
	if next < len(structure) {
		return nil, nil, nil, refuse("the source's property %s does not take the goal's structure", c.Name())
	}
	return constantCall(x.lib, c.Name(), args...), open, data, nil
}

// atParams reads the unfolded property at the call's parameters, in
// the order of its ∀ binders: its guards, nil when it has none, and
// its consequent.
func (x *_Executor) atParams(unfolded core.Term) (guards, consequent core.Term, err error) {
	list, body := ext.DecomposesFORALL(unfolded)
	var binders []core.VarTerm
	for v := range list.Iter() {
		binders = append(binders, v)
	}
	if len(x.call.Params) != len(binders) {
		return nil, nil, refuse("the property quantifies %d binders; .At gives %d parameters", len(binders), len(x.call.Params))
	}
	var substs []core.TermSubst
	for i, p := range x.call.Params {
		if !p.Type().Equals(binders[i].Type()) {
			return nil, nil, refuse(".At's parameter %d, %s of type %s, does not fit the property's binder %s of type %s",
				i+1, ext.PrintTerm(p), ext.FormatType(p.Type()), binders[i].Name(), ext.FormatType(binders[i].Type()))
		}
		substs = append(substs, core.MakeTermSubst(binders[i], p))
	}
	body = wrap(core.Assume(body.Substitute(substs...))).RewriteConcl(prop.DeepBeta).Conclusion()
	if h, c, ok := ext.MatchesIMPLY(body); ok {
		return h, c, nil
	}
	return nil, body, nil
}

// _DegreeGuard is a guard bounding a parameter's degree by the open
// bound: polynomial_bound(R, n, d, p) for a polynomial, ∀j. j < k ⇒
// polynomial_bound(R, n, d, P(j)) for a family, ring_tuple(R, d, p) for
// a polynomial in one variable, its coefficients a tuple of length d
// (tuple, family the polynomial).
type _DegreeGuard struct {
	statement core.Term
	ring      core.Term
	dimension core.Term
	count     core.Term
	family    core.Term
	scalar    bool
	tuple     bool
}

func degreeGuard(g core.Term, bound core.VarTerm) (_DegreeGuard, bool) {
	boundAt := func(t core.Term) (ring, dimension, p core.Term, ok bool) {
		if !isApplicationOf(t, "polynomial_bound") {
			return nil, nil, nil, false
		}
		_, args := ext.MatchesApply(t)
		if len(args) != 4 || !args[2].AlphaEquals(bound) || args[0].HasFree(bound) || args[1].HasFree(bound) || args[3].HasFree(bound) {
			return nil, nil, nil, false
		}
		return args[0], args[1], args[3], true
	}
	if R, n, p, ok := boundAt(g); ok {
		j := core.Var("j", ext.NumType).RenameToAvoid(p)
		return _DegreeGuard{statement: g, ring: R, dimension: n, count: numeral(1), family: core.Abs(j, p), scalar: true}, true
	}
	if isApplicationOf(g, "ring_tuple") {
		_, args := ext.MatchesApply(g)
		if len(args) == 3 && args[1].AlphaEquals(bound) && !args[0].HasFree(bound) && !args[2].HasFree(bound) {
			return _DegreeGuard{statement: g, ring: args[0], family: args[2], tuple: true}, true
		}
	}
	all := ext.MatchesFORALL(g)
	if all.IsZero() {
		return _DegreeGuard{}, false
	}
	j := all.Var()
	below, inner, ok := ext.MatchesIMPLY(all.Body())
	if !ok || !isApplicationOf(below, "<") {
		return _DegreeGuard{}, false
	}
	_, lt := ext.MatchesApply(below)
	if len(lt) != 2 || !lt[0].AlphaEquals(j) || lt[1].HasFree(j) || lt[1].HasFree(bound) {
		return _DegreeGuard{}, false
	}
	R, n, member, ok := boundAt(inner)
	if !ok {
		return _DegreeGuard{}, false
	}
	app, isApp := member.AsAppliedTerm()
	if !isApp || !app.Arg().AlphaEquals(j) || app.Fun().HasFree(j) || R.HasFree(j) || n.HasFree(j) {
		return _DegreeGuard{}, false
	}
	return _DegreeGuard{statement: g, ring: R, dimension: n, count: lt[1], family: app.Fun()}, true
}

// _Witness is a parameter's common degree bound: ⊢ ∃d. B(d) from
// CommonDegreeBound, the bound's fresh variable and B at it.
type _Witness struct {
	exists *prop.PropWrapper
	bound  core.VarTerm
	body   core.Term
}

// commonBound is CommonDegreeBound at the guard's parameter, its
// membership discharged by the call's facts: the family's own, or a
// polynomial's read as the one-member family's. Its bound is a variable
// apart from the bounds taken before it.
func (x *_Executor) commonBound(g _DegreeGuard, taken []_Witness) (_Witness, error) {
	if g.tuple {
		lemma := instantiate(wrap(x.lib.Theorem(lemmaTupleOfPolynomal)), g.ring, g.family).RewriteConcl(fieldRingProjections(x.lib))
		h, _, ok := ext.MatchesIMPLY(lemma.Conclusion())
		if !ok {
			panic("bridge: TupleOfPolynomial has no antecedent")
		}
		member := x.fact(h)
		if member == nil {
			return _Witness{}, refuse("no fact gives the polynomial in one variable over the carrier, which its length is taken from: %s", ext.PrintTerm(h))
		}
		return x.witness(modusPonens(lemma, member), taken), nil
	}
	lemma := instantiate(wrap(x.lib.Theorem(lemmaCommonBound)), g.ring, g.dimension, g.count, g.family).RewriteConcl(prop.DeepBeta)
	h, _, ok := ext.MatchesIMPLY(lemma.Conclusion())
	if !ok {
		panic("bridge: CommonDegreeBound has no antecedent")
	}
	member := x.fact(h)
	if member == nil && g.scalar {
		all := ext.MatchesFORALL(h)
		below, inner, _ := ext.MatchesIMPLY(all.Body())
		if f := x.fact(inner); f != nil {
			member = f.PromoteHyp(below).ConclForAll(all.Var())
		}
	}
	if member == nil {
		what := h
		if g.scalar {
			all := ext.MatchesFORALL(h)
			_, what, _ = ext.MatchesIMPLY(all.Body())
		}
		return _Witness{}, refuse("no fact gives the parameter's membership in the polynomial algebra, which its degree bound is taken from: %s", ext.PrintTerm(what))
	}
	return x.witness(modusPonens(lemma, member), taken), nil
}

// witness is the bound ⊢ ∃d. B(d) gives, at a variable apart from the
// bounds taken before it.
func (x *_Executor) witness(exists *prop.PropWrapper, taken []_Witness) _Witness {
	abs := ext.MatchesEXISTS(exists.Conclusion())
	avoid := []core.Term{x.call.Goal, exists.Conclusion()}
	avoid = append(avoid, x.call.Params...)
	for _, f := range x.facts {
		avoid = append(avoid, f.Conclusion())
	}
	for _, w := range taken {
		avoid = append(avoid, w.bound)
	}
	d := core.Var(abs.Var().Name(), abs.Var().Type()).RenameToAvoid(avoid...)
	return _Witness{exists: exists, bound: d, body: abs.Body().Substitute(core.MakeTermSubst(abs.Var(), d))}
}

// degreeAt proves the guard at the pooled bound d from the witness's
// bound: the witness's own statement for a family alone, its instance
// at 0 for a polynomial, and through PolynomialBoundMono, the
// witness's bound below the sum, when several are pooled.
func (x *_Executor) degreeAt(g _DegreeGuard, w _Witness, d core.Term, pooled bool, statement core.Term) *prop.PropWrapper {
	given := assume(w.body)
	raise := func(t *prop.PropWrapper) *prop.PropWrapper {
		if !pooled {
			return t
		}
		_, args := ext.MatchesApply(t.Conclusion())
		le := derivedArith(x.lib, constantCall(x.lib, "<=", w.bound, d), nil)
		mono := instantiate(wrap(x.lib.Theorem(lemmaBoundMono)), args[0], args[1], w.bound, d, args[3])
		for {
			h, _, ok := ext.MatchesIMPLY(mono.Conclusion())
			if !ok {
				return mono
			}
			met := fromPieces(h, []*prop.PropWrapper{t, le})
			if met == nil {
				panic("bridge: PolynomialBoundMono's antecedent is not the bound and the order: " + ext.PrintTerm(h))
			}
			mono = modusPonens(mono, met)
		}
	}
	var t *prop.PropWrapper
	if g.tuple {
		t = given
	} else if g.scalar {
		zero := numeral(0)
		below := derivedArith(x.lib, constantCall(x.lib, "<", zero, numeral(1)), nil)
		t = raise(modusPonens(given.ConclForAllInst(zero), below))
	} else if !pooled {
		t = given
	} else {
		all := ext.MatchesFORALL(w.body)
		j := all.Var()
		below, _, _ := ext.MatchesIMPLY(all.Body())
		t = raise(modusPonens(given.ConclForAllInst(j), assume(below))).PromoteHyp(below).ConclForAll(j)
	}
	sameConclusion(t, statement, "a parameter's degree bound")
	return t
}

// fromPieces proves h from the theorems at hand: one that states it,
// or, for a conjunction, its conjuncts' proofs conjoined; nil when a
// conjunct has none.
func fromPieces(h core.Term, available []*prop.PropWrapper) *prop.PropWrapper {
	for _, a := range available {
		if a.Conclusion().AlphaEquals(h) {
			return a
		}
	}
	l, r, ok := ext.MatchesAND(h)
	if !ok {
		return nil
	}
	left := fromPieces(l, available)
	if left == nil {
		return nil
	}
	right := fromPieces(r, available)
	if right == nil {
		return nil
	}
	return conjoin(left, right)
}

// firstUnmet is the first conjunct of h no theorem at hand states.
func firstUnmet(h core.Term, available []*prop.PropWrapper) core.Term {
	if fromPieces(h, available) != nil {
		return nil
	}
	if l, r, ok := ext.MatchesAND(h); ok {
		if u := firstUnmet(l, available); u != nil {
			return u
		}
		return firstUnmet(r, available)
	}
	return h
}

func numeral(k int64) core.Term { return ext.MakeNumeral(big.NewInt(k)) }
