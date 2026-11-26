package omega

// The structure ring over a FABRICATED algebra: the structure predicates
// and monoid_pow are test constants, every law a statement-correct
// stand-in (core.TestThm, the package's fabricator convention). What is
// under test is the composition — the leaves read the general laws at
// the fact, the ring and signed normalizers compose them, the equality
// decider finds integer combinations — not the laws themselves, which
// the serve binding test checks against the corpus.

import (
	"math/big"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

type fakeAlgebra struct {
	A, ringType, fieldType, groupType                  core.HolType
	commRing, commMonoid, abGroup, grp                 core.ConstTerm // the carrier forms: comm_ring_on, …
	field, wholeCommRing, wholeField, monoidPow        core.ConstTerm
	mkRing, mkField, mkGroup, fieldRing, additiveGroup core.ConstTerm
	restrictRing, restrictField                        core.ConstTerm
	member, univ, empty                                core.ConstTerm // `∈`, 𝕌 and ∅
	laws                                               *StructureRingLaws
}

// newFakeAlgebra mints the predicates and the power over a type variable
// A and fabricates the laws in the stated shapes the corpus chapters
// register them in.
func newFakeAlgebra() *fakeAlgebra {
	A := core.MakeVarType("A")
	AA := core.MakeFun(A, A)
	AAA := core.MakeFun(A, AA)
	num := dsl.NumType
	v := func(name string, ty core.HolType) *ext.TermWrapper { return ext.Var(ext.TermName(name), ty) }
	T := ext.WrapTerm(ext.T)
	// λ-bodies for the predicates: constantly true; for the power: x.
	add, zero, neg, mul, one, sub := v("add", AAA), v("zero", A), v("neg", AA), v("mul", AAA), v("one", A), v("sub", AAA)
	inv, div := v("inv", AA), v("div", AAA)
	op, e, x, y, z, n, m := v("op", AAA), v("e", A), v("x", A), v("y", A), v("z", A), v("n", num), v("m", num)
	set := core.MakeFun(A, core.TypeBool())
	c := v("c", set)
	constant := func(name string, ty core.HolType) core.ConstTerm {
		return core.MakeConstTerm(core.MakeConstMeta(name, ty), ty)
	}
	fun := func(result core.HolType, args ...core.HolType) core.HolType {
		for i := len(args) - 1; i >= 0; i-- {
			result = core.MakeFun(args[i], result)
		}
		return result
	}
	ringType := core.MakeCompositeType(core.MakeMetaType("zz_ring_ops", 1), A)
	fieldType := core.MakeCompositeType(core.MakeMetaType("zz_field_ops", 1), A)
	groupType := core.MakeCompositeType(core.MakeMetaType("zz_group_ops", 1), A)
	r, f, g := v("R", ringType), v("F", fieldType), v("G", groupType)
	commRing := constant("comm_ring_on", core.MakeFun(ringType, core.TypeBool()))
	commMonoid := core.NewConstDef(c.To(op.To(e.To(T))).Core(), "zz_comm_monoid_on_test")
	abGroup := constant("zz_abelian_group_on_test", core.MakeFun(groupType, core.TypeBool()))
	grp := constant("zz_group_on_test", core.MakeFun(groupType, core.TypeBool()))
	field := constant("field_on", core.MakeFun(fieldType, core.TypeBool()))
	monoidPow := core.NewConstDef(op.To(e.To(x.To(n.To(x)))).Core(), "zz_monoid_pow_test")
	member := core.NewConstDef(x.To(c.To(T)).Core(), "zz_member_test")
	univ := core.NewConstDef(x.To(T).Core(), "zz_univ_test")
	empty := core.NewConstDef(x.To(ext.WrapTerm(ext.F)).Core(), "zz_empty_test")
	fa := &fakeAlgebra{A: A, ringType: ringType, fieldType: fieldType, groupType: groupType,
		commRing: commRing, commMonoid: commMonoid, abGroup: abGroup, grp: grp,
		field: field, wholeCommRing: constant("comm_ring", core.MakeFun(ringType, core.TypeBool())),
		wholeField: constant("field", core.MakeFun(fieldType, core.TypeBool())),
		monoidPow:  monoidPow, member: member, univ: univ, empty: empty,
		mkRing:        constant("zz_mk_ring", fun(ringType, AAA, A, AA, AAA, A, AAA, set)),
		mkField:       constant("zz_mk_field", fun(fieldType, AAA, A, AA, AAA, A, AAA, AA, AAA, set)),
		mkGroup:       constant("zz_mk_group", fun(groupType, AAA, A, AA, set)),
		fieldRing:     constant("zz_field_ring", fun(ringType, fieldType)),
		additiveGroup: constant("zz_additive_group", fun(groupType, ringType)),
		restrictRing:  constant("zz_restrict_ring", fun(ringType, ringType, set)),
		restrictField: constant("zz_restrict_field", fun(fieldType, fieldType, set)),
	}
	type projection struct {
		constructor core.ConstTerm
		index       int
	}
	projections := map[core.ConstTermMeta]projection{}
	fields := func(prefix string, record core.HolType, constructor core.ConstTerm, types ...core.HolType) []*ext.TermWrapper {
		out := make([]*ext.TermWrapper, len(types))
		var value *ext.TermWrapper
		switch record {
		case ringType:
			value = r
		case fieldType:
			value = f
		case groupType:
			value = g
		}
		for i, ty := range types {
			selector := constant(prefix+string(rune('a'+i)), core.MakeFun(record, ty))
			projections[selector.Meta()] = projection{constructor, i}
			out[i] = ext.WrapTerm(ext.Apply(selector, value.Core()))
		}
		return out
	}
	rf := fields("zz_ring_", ringType, fa.mkRing, AAA, A, AA, AAA, A, AAA, set)
	ff := fields("zz_field_", fieldType, fa.mkField, AAA, A, AA, AAA, A, AAA, AA, AAA, set)
	gf := fields("zz_group_", groupType, fa.mkGroup, AAA, A, AA, set)
	// Stand-in record equations exercise the same normalization boundary as
	// the corpus equations; the composition tests fabricate their leaves.
	normalize := prop.DeepRewrite(func(t core.Term) *prop.PropWrapper {
		h, args := ext.MatchesApply(t)
		selector, ok := h.AsConst()
		if !ok || len(args) != 1 {
			return nil
		}
		p, ok := projections[selector.Meta()]
		if !ok {
			return nil
		}
		record := args[0]
		rh, values := ext.MatchesApply(record)
		if rh.Equals(fa.fieldRing) && len(values) == 1 {
			parts := make([]core.Term, 7)
			for i, j := range []int{0, 1, 2, 3, 4, 5, 8} {
				projectionHead, _ := ext.MatchesApply(ff[j].Core())
				parts[i] = ext.Apply(projectionHead, values[0])
			}
			record = ext.Apply(fa.mkRing, parts...)
		} else if rh.Equals(fa.additiveGroup) && len(values) == 1 {
			// Its argument can itself be a field's ring projection.
			parts := make([]core.Term, 4)
			for i, j := range []int{0, 1, 2, 6} {
				projectionHead, _ := ext.MatchesApply(rf[j].Core())
				parts[i] = ext.Apply(projectionHead, values[0])
			}
			record = ext.Apply(fa.mkGroup, parts...)
		}
		if rh.Equals(fa.restrictRing) || rh.Equals(fa.restrictField) {
			if len(values) != 2 {
				return nil
			}
			source, carrier := values[0], values[1]
			fields, constructor := rf, fa.mkRing
			if rh.Equals(fa.restrictField) {
				fields, constructor = ff, fa.mkField
			}
			parts := make([]core.Term, len(fields))
			for i, field := range fields {
				selector, _ := ext.MatchesApply(field.Core())
				parts[i] = ext.Apply(selector, source)
			}
			parts[len(parts)-1] = carrier
			record = ext.Apply(constructor, parts...)
		}
		rh, values = ext.MatchesApply(record)
		if !rh.Equals(p.constructor) || len(values) <= p.index {
			return nil
		}
		return prop.WrapProp(core.TestThm(core.Eq(t, values[p.index])))
	})

	ap := func(f core.Term, args ...*ext.TermWrapper) *ext.TermWrapper {
		ts := make([]core.Term, len(args))
		for i, a := range args {
			ts[i] = a.Core()
		}
		return ext.WrapTerm(ext.Apply(f, ts...))
	}
	thm := func(t *ext.TermWrapper) *prop.PropWrapper { return prop.WrapProp(core.TestThm(t.Core())) }
	ForAll := ext.ForAll
	in := func(t *ext.TermWrapper) *ext.TermWrapper { return ap(member, t, c) }
	// guarded(xs…)(body) is `∀xs. x₁ ∈ c ∧ … ⇒ body`, the carrier laws' shape.
	guarded := func(vars ...*ext.TermWrapper) func(body *ext.TermWrapper) *ext.TermWrapper {
		return func(body *ext.TermWrapper) *ext.TermWrapper {
			guard := in(vars[len(vars)-1])
			for i := len(vars) - 2; i >= 0; i-- {
				guard = in(vars[i]).And(guard.Core())
			}
			binders := make([]ext.Term, len(vars))
			for i, v := range vars {
				binders[i] = v
			}
			return ForAll(binders...)(guard.Imply(body.Core()))
		}
	}
	substitute := func(body *ext.TermWrapper, from, to []*ext.TermWrapper) *ext.TermWrapper {
		substs := make([]core.TermSubst, len(from))
		for i := range from {
			variable, _ := from[i].Core().AsVar()
			substs[i] = core.MakeTermSubst(variable, to[i].Core())
		}
		return ext.WrapTerm(body.Core().Substitute(substs...))
	}
	ring := ap(commRing, r)
	ringLaw := func(body *ext.TermWrapper) *prop.PropWrapper {
		body = substitute(body, []*ext.TermWrapper{add, zero, neg, mul, one, sub, c}, rf)
		return thm(ForAll(r)(ring.Imply(body.Core())))
	}
	monoid := ap(commMonoid, c, op, e)
	monoidLaw := func(body *ext.TermWrapper) *prop.PropWrapper {
		return thm(ForAll(c, op, e)(monoid.Imply(body.Core())))
	}
	group := ap(grp, g)
	groupLaw := func(body *ext.TermWrapper) *prop.PropWrapper {
		body = substitute(body, []*ext.TermWrapper{op, e, inv, c}, gf)
		return thm(ForAll(g)(group.Imply(body.Core())))
	}
	abelian := ap(abGroup, g)
	abelianLaw := func(body *ext.TermWrapper) *prop.PropWrapper {
		body = substitute(body, []*ext.TermWrapper{add, zero, neg, c}, gf)
		return thm(ForAll(g)(abelian.Imply(body.Core())))
	}
	fld := ap(field, f)
	fieldLaw := func(body *ext.TermWrapper) *prop.PropWrapper {
		body = substitute(body, []*ext.TermWrapper{add, zero, neg, mul, one, sub, inv, div, c}, ff)
		return thm(ForAll(f)(fld.Imply(body.Core())))
	}
	pow := func(o, id, b, k *ext.TermWrapper) *ext.TermWrapper { return ap(monoidPow, o, id, b, k) }
	nplus := func(a, b *ext.TermWrapper) *ext.TermWrapper { return ext.WrapTerm(plus(a.Core(), b.Core())) }
	nstar := func(a, b *ext.TermWrapper) *ext.TermWrapper { return ext.WrapTerm(star(a.Core(), b.Core())) }
	suc := func(a *ext.TermWrapper) *ext.TermWrapper { return ext.WrapTerm(ext.Apply(natSuc, a.Core())) }
	lit := func(k uint64) *ext.TermWrapper { return ext.WrapTerm(Numeral(k)) }

	fa.laws = &StructureRingLaws{
		MulMonoid: ringLaw(ap(commMonoid, c, mul, one)),
		AddMonoid: ringLaw(ap(commMonoid, c, add, zero)),
		AddGroup:  ringLaw(ap(abGroup, ap(fa.additiveGroup, r))),
		Group:     abelianLaw(ap(grp, g)),
		NegAdd:    abelianLaw(guarded(x, y)(ap(neg, ap(add, x, y)).Eq(ap(add, ap(neg, x), ap(neg, y))))),

		Comm:          monoidLaw(guarded(x, y)(ap(op, x, y).Eq(ap(op, y, x)))),
		Assoc:         monoidLaw(guarded(x, y, z)(ap(op, x, ap(op, y, z)).Eq(ap(op, ap(op, x, y), z)))),
		LeftIdentity:  monoidLaw(guarded(x)(ap(op, e, x).Eq(x))),
		RightIdentity: monoidLaw(guarded(x)(ap(op, x, e).Eq(x))),
		PowOne:        monoidLaw(guarded(x)(pow(op, e, x, lit(1)).Eq(x))),
		PowAdd:        monoidLaw(ForAll(x, m, n)(in(x).Imply(pow(op, e, x, nplus(m, n)).Eq(ap(op, pow(op, e, x, m), pow(op, e, x, n))).Core()))),
		PowIn:         monoidLaw(ForAll(x, n)(in(x).Imply(in(pow(op, e, x, n)).Core()))),
		PowZeroClause: thm(ForAll(op, e, x)(pow(op, e, x, lit(0)).Eq(e))),
		PowSucClause:  thm(ForAll(op, e, x, n)(pow(op, e, x, suc(n)).Eq(ap(op, x, pow(op, e, x, n))))),

		InvInv:      groupLaw(guarded(x)(ap(inv, ap(inv, x)).Eq(x))),
		InvOne:      groupLaw(ap(inv, e).Eq(e)),
		LeftInverse: groupLaw(guarded(x)(ap(op, ap(inv, x), x).Eq(e))),
		RightCancel: groupLaw(guarded(x, y, z)(ap(op, y, x).Eq(ap(op, z, x)).Eq(y.Eq(z)))),

		LeftDistrib:  ringLaw(guarded(x, y, z)(ap(mul, x, ap(add, y, z)).Eq(ap(add, ap(mul, x, y), ap(mul, x, z))))),
		RightDistrib: ringLaw(guarded(x, y, z)(ap(mul, ap(add, x, y), z).Eq(ap(add, ap(mul, x, z), ap(mul, y, z))))),
		MulLeftZero:  ringLaw(guarded(x)(ap(mul, zero, x).Eq(zero))),
		MulRightZero: ringLaw(guarded(x)(ap(mul, x, zero).Eq(zero))),
		SubAddNeg:    ringLaw(guarded(x, y)(ap(sub, x, y).Eq(ap(add, x, ap(neg, y))))),
		MulRightNeg:  ringLaw(guarded(x, y)(ap(mul, x, ap(neg, y)).Eq(ap(neg, ap(mul, x, y))))),
		AddPowMul:    ringLaw(ForAll(m, n)(pow(add, zero, one, nstar(m, n)).Eq(ap(mul, pow(add, zero, one, m), pow(add, zero, one, n))))),

		ZeroIn: ringLaw(in(zero)),
		OneIn:  ringLaw(in(one)),
		AddIn:  ringLaw(guarded(x, y)(in(ap(add, x, y)))),
		NegIn:  ringLaw(guarded(x)(in(ap(neg, x)))),
		MulIn:  ringLaw(guarded(x, y)(in(ap(mul, x, y)))),
		SubIn:  ringLaw(guarded(x, y)(in(ap(sub, x, y)))),

		RingOnUniverse:  thm(ForAll(r)(ap(fa.wholeCommRing, r).Eq(ap(commRing, ap(fa.restrictRing, r, ext.WrapTerm(univ)))))),
		FieldOnUniverse: thm(ForAll(f)(ap(fa.wholeField, f).Eq(ap(field, ap(fa.restrictField, f, ext.WrapTerm(univ)))))),
		InUniv:          thm(ForAll(x)(ap(member, x, ext.WrapTerm(univ)))),

		FieldRing:     fieldLaw(ap(commRing, ap(fa.fieldRing, f))),
		InvIn:         fieldLaw(guarded(x)(in(ap(inv, x)))),
		DivIn:         fieldLaw(guarded(x, y)(in(ap(div, x, y)))),
		NormalizeWith: func(LibraryRead) prop.Rewrite { return normalize },
		NormalizeTerm: func(t core.Term) core.Term {
			if w := normalize(t); w != nil {
				return prop.Rhs(w)
			}
			return t
		},
		DivMulInv: fieldLaw(guarded(x, y)(ap(div, x, y).Eq(ap(mul, x, ap(inv, y))))),
		InvMul:    fieldLaw(guarded(x, y)(ap(inv, ap(mul, x, y)).Eq(ap(mul, ap(inv, x), ap(inv, y))))),
		MulLeftInverse: fieldLaw(ForAll(x)(in(x).And(not(x.Eq(zero).Core())).
			Imply(ap(mul, ap(inv, x), x).Eq(one).Core()))),
	}
	return fa
}

// abstractWorld is a chapter's view: variable components and the fact
// resident as a hypothesis.
type abstractWorld struct {
	fa                            *fakeAlgebra
	add, zero, neg, mul, one, sub core.Term
	S                             core.Term // comm_ring at a record whose carrier field is empty
	c                             core.Term // a carrier set
	SOn                           core.Term // comm_ring_on at a record with carrier c
}

func (fa *fakeAlgebra) abstract() *abstractWorld {
	A := fa.A
	AA := core.MakeFun(A, A)
	AAA := core.MakeFun(A, AA)
	v := func(name string, ty core.HolType) core.Term { return ext.Var(ext.TermName(name), ty).Core() }
	w := &abstractWorld{fa: fa, add: v("add₀", AAA), zero: v("zero₀", A), neg: v("neg₀", AA), mul: v("mul₀", AAA), one: v("one₀", A), sub: v("sub₀", AAA),
		c: v("c₀", core.MakeFun(A, core.TypeBool()))}
	w.S = ext.Apply(fa.wholeCommRing, ext.Apply(fa.mkRing, w.add, w.zero, w.neg, w.mul, w.one, w.sub, fa.empty))
	w.SOn = ext.Apply(fa.commRing, ext.Apply(fa.mkRing, w.add, w.zero, w.neg, w.mul, w.one, w.sub, w.c))
	return w
}

// in is `t ∈ c₀`.
func (w *abstractWorld) in(t core.Term) core.Term { return ext.Apply(w.fa.member, t, w.c) }

func (w *abstractWorld) x(name string) core.Term    { return ext.Var(ext.TermName(name), w.fa.A).Core() }
func (w *abstractWorld) p(a, b core.Term) core.Term { return ext.Apply(w.add, a, b) }
func (w *abstractWorld) t(a, b core.Term) core.Term { return ext.Apply(w.mul, a, b) }
func (w *abstractWorld) d(a, b core.Term) core.Term { return ext.Apply(w.sub, a, b) }
func (w *abstractWorld) ng(a core.Term) core.Term   { return ext.Apply(w.neg, a) }
func (w *abstractWorld) pw(a core.Term, k uint64) core.Term {
	return ext.Apply(w.fa.monoidPow, w.mul, w.one, a, Numeral(k))
}

func installFakeStructureRing(t *testing.T) *fakeAlgebra {
	t.Helper()
	fa := newFakeAlgebra()
	SetStructureRingLaws(fa.laws)
	SetStructureInstances(nil)
	t.Cleanup(func() { SetStructureRingLaws(nil); SetStructureInstances(nil) })
	return fa
}

// decides runs the hyp-aware decider with the structure policy on and
// reports whether goal decided to ⊤ with hyps ⊆ hyps.
func structureDecides(t *testing.T, hyps []Term, goal Term) bool {
	t.Helper()
	policy := ArithPolicy{Nat: true, Structure: true, StructureInstances: true}
	w := NewArithCtxWithPolicy(hyps, policy, nil).Decide(goal)
	if w == nil || !prop.Rhs(w).Equals(prop.T) {
		return false
	}
	closed := w.EqSym().EqMP(prop.DerivesTrue)
	require.True(t, prop.IsStronger(closed, core.MakeProp(goal, hyps...)),
		"the closing theorem carries a hypothesis the goal lacks: %v", closed.Hyps())
	return true
}

func TestStructureRing_AbstractIdentities(t *testing.T) {
	fa := installFakeStructureRing(t)
	w := fa.abstract()
	x, y, z := w.x("x"), w.x("y"), w.x("z")
	xy := w.p(x, y)
	rows := []struct {
		name string
		l, r Term
	}{
		{"binomial square", w.t(xy, xy), w.p(w.p(w.t(x, x), w.t(w.p(w.one, w.one), w.t(x, y))), w.t(y, y))},
		{"commute and associate", w.t(w.p(x, y), z), w.p(w.t(z, y), w.t(x, z))},
		{"difference of squares", w.t(w.d(x, y), w.p(x, y)), w.d(w.t(x, x), w.t(y, y))},
		{"negation through a product", w.ng(w.t(x, y)), w.t(x, w.ng(y))},
		{"negated square", w.t(w.ng(x), w.ng(x)), w.t(x, x)},
		{"opposite differences squared", w.t(w.d(x, y), w.d(x, y)), w.t(w.d(y, x), w.d(y, x))},
		{"zero annihilates", w.t(w.zero, w.p(x, y)), w.zero},
		{"one is neutral", w.t(w.one, x), w.p(x, w.zero)},
		{"the square as a power", w.pw(x, 2), w.t(x, x)},
		{"the cube of a sum", w.pw(xy, 3), w.p(w.p(w.pw(x, 3), w.t(w.p(w.one, w.p(w.one, w.one)), w.p(w.t(w.t(x, x), y), w.t(x, w.t(y, y))))), w.pw(y, 3))},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			goal := core.Eq(r.l, r.r)
			require.True(t, structureDecides(t, []Term{w.S}, goal), "declined %s", ext.PrintTerm(goal))
			// Without the fact nothing fires: the ring has no laws to read.
			require.Nil(t, NewArithCtxWithPolicy(nil, ArithPolicy{Nat: true, Structure: true}, nil).Decide(goal),
				"decided %s with no structure fact in the context", ext.PrintTerm(goal))
		})
	}
	// A non-identity is left alone.
	require.False(t, structureDecides(t, []Term{w.S}, core.Eq(w.t(x, y), w.p(x, y))))
}

func TestStructureRing_IntegerCombinations(t *testing.T) {
	fa := installFakeStructureRing(t)
	w := fa.abstract()
	a, b, c, d, e := w.x("a"), w.x("b"), w.x("c"), w.x("d"), w.x("e")
	x, y, u, v := w.x("x"), w.x("y"), w.x("u"), w.x("v")
	// x = y, u = v ⊢ x + u = y + v   (coefficients 1, 1)
	require.True(t, structureDecides(t, []Term{w.S, core.Eq(x, y), core.Eq(u, v)}, core.Eq(w.p(x, u), w.p(y, v))))
	// x + x = y ⊢ x + x + x + x = y + y   (coefficient 2)
	twoX := w.p(x, x)
	require.True(t, structureDecides(t, []Term{w.S, core.Eq(twoX, y)}, core.Eq(w.p(twoX, twoX), w.p(y, y))))
	// x = y + z ⊢ x − z = y   (sub on the goal side, coefficient 1)
	require.True(t, structureDecides(t, []Term{w.S, core.Eq(x, w.p(y, w.zTerm()))}, core.Eq(w.d(x, w.zTerm()), y)))
	// a = b·c, d = c·e ⊢ a·e = b·d: each equation defines its variable,
	// and read at the definitions the goal is a ring identity
	// (variable_subst.go).
	h1, h2 := core.Eq(a, w.t(b, c)), core.Eq(d, w.t(c, e))
	require.True(t, structureDecides(t, []Term{w.S, h1, h2}, core.Eq(w.t(a, e), w.t(b, d))))
	// a + b = c·d ⊢ (a + b)·e = c·d·e needs the POLYNOMIAL coefficient e,
	// and its equation defines no variable: declined …
	h3 := core.Eq(w.p(a, b), w.t(c, d))
	scaled := core.Eq(w.t(w.p(a, b), e), w.t(w.t(c, d), e))
	require.False(t, structureDecides(t, []Term{w.S, h3}, scaled))
	// … and closes once the context carries the scaled equation — what a
	// Scaled(e, h) premise installs.
	s3 := core.Eq(w.t(e, w.p(a, b)), w.t(e, w.t(c, d)))
	require.True(t, structureDecides(t, []Term{w.S, s3}, scaled))
	// x + x = y + y ⊢ x = y would need the coefficient ½: declined (false in characteristic 2).
	require.False(t, structureDecides(t, []Term{w.S, core.Eq(twoX, w.p(y, y))}, core.Eq(x, y)))
}

func (w *abstractWorld) zTerm() core.Term { return w.x("z") }

func TestStructureRing_InstanceAndField(t *testing.T) {
	fa := installFakeStructureRing(t)
	A := fa.A
	// A concrete carrier: constants for the components, the fact a theorem.
	cadd := core.NewConstDef(ext.Var("p", A).To(ext.Var("q", A).To(ext.Var("p", A))).Core(), "zz_cadd")
	cmul := core.NewConstDef(ext.Var("p", A).To(ext.Var("q", A).To(ext.Var("q", A))).Core(), "zz_cmul")
	csub := core.NewConstDef(ext.Var("p", A).To(ext.Var("q", A).To(ext.Var("p", A))).Core(), "zz_csub")
	cdiv := core.NewConstDef(ext.Var("p", A).To(ext.Var("q", A).To(ext.Var("p", A))).Core(), "zz_cdiv")
	cneg := core.NewConstDef(ext.Var("p", A).To(ext.Var("p", A)).Core(), "zz_cneg")
	cinv := core.NewConstDef(ext.Var("p", A).To(ext.Var("p", A)).Core(), "zz_cinv")
	czero := ext.Var("czero", A).Core() // a free variable stands in for the distinguished elements
	cone := ext.Var("cone", A).Core()
	fact := prop.WrapProp(core.TestThm(ext.Apply(fa.wholeField, ext.Apply(fa.mkField, cadd, czero, cneg, cmul, cone, csub, cinv, cdiv, fa.empty))))
	SetStructureInstances([]StructureInstance{{Fact: fact}})

	x, y := ext.Var("x", A).Core(), ext.Var("y", A).Core()
	add := func(a, b Term) Term { return ext.Apply(cadd, a, b) }
	mul := func(a, b Term) Term { return ext.Apply(cmul, a, b) }
	div := func(a, b Term) Term { return ext.Apply(cdiv, a, b) }
	inv := func(a Term) Term { return ext.Apply(cinv, a) }
	// No resident fact: the installed instance serves, and the close is hyp-free.
	goal := core.Eq(mul(add(x, y), add(x, y)), add(add(mul(x, x), mul(add(cone, cone), mul(x, y))), mul(y, y)))
	w := NewArithCtxWithPolicy(nil, ArithPolicy{Nat: true, Structure: true, StructureInstances: true}, nil).Decide(goal)
	require.NotNil(t, w)
	require.True(t, prop.Rhs(w).Equals(prop.T))
	require.Equal(t, 0, w.NumHyps(), "an instance fact is a theorem: the close carries no hypothesis")
	// The field's quotient reads as a product with the inverse.
	require.True(t, structureDecides(t, nil, core.Eq(div(add(x, y), y), add(mul(x, inv(y)), mul(y, inv(y))))))
	// Content predicates.
	require.True(t, IsStructureRingContent(nil, goal))
	require.False(t, IsStructureRingContent(nil, core.Eq(x, y)), "two bare atoms mention no component")
	content, _ := StructureRingContent(core.MakeProp(ext.ForAll(ext.Var("q", A))(ext.WrapTerm(core.Eq(mul(x, ext.Var("q", A).Core()), mul(ext.Var("q", A).Core(), x)))).Core()))
	require.True(t, content)
}

// TestStructureRing_WholeTypeFactReadsThroughTheBridge observes that a
// whole fact is read at 𝕌 even when its record carries another set.
func TestStructureRing_WholeTypeFactReadsThroughTheBridge(t *testing.T) {
	fa := installFakeStructureRing(t)
	w := fa.abstract()
	sr := fallbackReader.ringFor(prop.Assume(w.S), nil)
	require.NotNil(t, sr)
	head, args := ext.MatchesApply(sr.ringFact.Conclusion())
	headConst, _ := head.AsConst()
	require.Equal(t, commRingOnConstName, string(headConst.Name()), "the ring fact is the carrier form")
	require.Len(t, args, 1)
	require.True(t, sr.set.Equals(fa.univ), "the bridge replaces the record's carrier by 𝕌")
	require.True(t, sr.universe)
	// The ring fact still rests on the resident fact alone.
	require.Equal(t, 1, sr.ringFact.NumHyps())
	require.True(t, sr.ringFact.HasHyp(w.S))
}

// TestStructureRing_CarrierSet: a resident comm_ring_on fact decides
// identities whose atoms' memberships the context holds — as
// hypotheses, or as conjuncts of one — and the close rests on exactly
// those memberships and the fact.
func TestStructureRing_CarrierSet(t *testing.T) {
	fa := installFakeStructureRing(t)
	w := fa.abstract()
	x, y, z := w.x("x"), w.x("y"), w.x("z")
	xy := w.p(x, y)
	memberships := []Term{w.in(x), w.in(y), w.in(z)}
	conj := ext.WrapTerm(w.in(x)).And(ext.WrapTerm(w.in(y)).And(w.in(z)).Core()).Core()
	rows := []struct {
		name string
		l, r Term
	}{
		{"binomial square", w.t(xy, xy), w.p(w.p(w.t(x, x), w.t(w.p(w.one, w.one), w.t(x, y))), w.t(y, y))},
		{"commute and associate", w.t(w.p(x, y), z), w.p(w.t(z, y), w.t(x, z))},
		{"difference of squares", w.t(w.d(x, y), w.p(x, y)), w.d(w.t(x, x), w.t(y, y))},
		{"negation through a product", w.ng(w.t(x, y)), w.t(x, w.ng(y))},
		{"zero annihilates", w.t(w.zero, w.p(x, y)), w.zero},
		{"one is neutral", w.t(w.one, x), w.p(x, w.zero)},
		{"the square as a power", w.pw(x, 2), w.t(x, x)},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			goal := core.Eq(r.l, r.r)
			require.True(t, structureDecides(t, append([]Term{w.SOn}, memberships...), goal), "declined %s", ext.PrintTerm(goal))
			require.True(t, structureDecides(t, []Term{w.SOn, conj}, goal), "declined %s with the memberships as one conjunction", ext.PrintTerm(goal))
		})
	}
	// Without a membership the ring declines, and names the atom.
	goal := core.Eq(w.t(xy, xy), w.p(w.p(w.t(x, x), w.t(w.p(w.one, w.one), w.t(x, y))), w.t(y, y)))
	hyps := []Term{w.SOn, w.in(x)}
	require.False(t, structureDecides(t, hyps, goal))
	set, atoms := StructureRingMissingMemberships(hyps, goal)
	require.True(t, set.Equals(w.c))
	require.Len(t, atoms, 1)
	require.True(t, atoms[0].Equals(y), "the missing atom is y, got %s", ext.PrintTerm(atoms[0]))
	// `y ∈ s` with `s ⊆ c₀` is not inferred: the membership must be resident.
	s := ext.Var("s", core.MakeFun(fa.A, core.TypeBool())).Core()
	require.False(t, structureDecides(t, []Term{w.SOn, w.in(x), ext.Apply(fa.member, y, s)}, goal))
	// Nothing is missing on the universal carrier.
	set, atoms = StructureRingMissingMemberships([]Term{w.S}, goal)
	require.Nil(t, set)
	require.Nil(t, atoms)
	// A context equation over the carrier combines, its atoms' memberships held.
	u, v := w.x("u"), w.x("v")
	require.True(t, structureDecides(t, []Term{w.SOn, w.in(x), w.in(y), w.in(u), w.in(v), core.Eq(x, y), core.Eq(u, v)},
		core.Eq(w.p(x, u), w.p(y, v))))
	// Two equations between variables are read into the goal whatever
	// the memberships: the goal is then one term on both sides, and no
	// law of the ring is asked for.
	require.True(t, structureDecides(t, []Term{w.SOn, w.in(x), w.in(y), w.in(u), core.Eq(x, y), core.Eq(u, v)},
		core.Eq(w.p(x, u), w.p(y, v))))
	// A context equation the ring has to combine is read only with its
	// atoms' memberships held: x + u = y + v, v outside.
	sum := core.Eq(w.p(x, u), w.p(y, v))
	shifted := core.Eq(w.p(w.p(x, u), x), w.p(w.p(y, v), x))
	require.True(t, structureDecides(t, []Term{w.SOn, w.in(x), w.in(y), w.in(u), w.in(v), sum}, shifted))
	require.False(t, structureDecides(t, []Term{w.SOn, w.in(x), w.in(y), w.in(u), sum}, shifted))
	// A left-nested membership conjunction reads as well.
	leftNested := ext.WrapTerm(w.in(x)).And(w.in(y)).And(w.in(z)).Core()
	require.True(t, structureDecides(t, []Term{w.SOn, leftNested}, core.Eq(w.t(w.p(x, y), z), w.p(w.t(z, y), w.t(x, z)))))
}

// TestStructureRing_SeveralFactsAtOneCarrier: an atom is tried at every
// fact at its carrier whose components it mentions, the rings on 𝕌
// first; a ring on a set whose memberships the context lacks does not
// stand in the way of one that decides, in either hypothesis order.
func TestStructureRing_SeveralFactsAtOneCarrier(t *testing.T) {
	fa := installFakeStructureRing(t)
	w := fa.abstract()
	x, y := w.x("x"), w.x("y")
	xy := w.p(x, y)
	square := core.Eq(w.t(xy, xy), w.p(w.p(w.t(x, x), w.t(w.p(w.one, w.one), w.t(x, y))), w.t(y, y)))
	// The record with carrier 𝕌 beside the ring on a set, no membership held.
	require.True(t, structureDecides(t, []Term{w.SOn, w.S}, square))
	require.True(t, structureDecides(t, []Term{w.S, w.SOn}, square))
	// Two rings on sets: the one holding the memberships decides.
	s := ext.Var("s", core.MakeFun(fa.A, core.TypeBool())).Core()
	onS := ext.Apply(fa.commRing, ext.Apply(fa.mkRing, w.add, w.zero, w.neg, w.mul, w.one, w.sub, s))
	inS := func(t core.Term) core.Term { return ext.Apply(fa.member, t, s) }
	require.True(t, structureDecides(t, []Term{w.SOn, onS, inS(x), inS(y)}, square))
	require.True(t, structureDecides(t, []Term{onS, w.SOn, w.in(x), w.in(y)}, square))
	// Neither holds them: declined, and the first ring's atoms are named.
	require.False(t, structureDecides(t, []Term{w.SOn, onS, inS(x)}, square))
	set, atoms := StructureRingMissingMemberships([]Term{w.SOn, onS, inS(x)}, square)
	require.NotNil(t, set)
	require.Len(t, atoms, 2)
	// An installed instance on 𝕌 beside a resident ring on a set.
	SetStructureInstances([]StructureInstance{{Fact: prop.WrapProp(core.TestThm(w.S))}})
	require.True(t, structureDecides(t, []Term{w.SOn}, square))
	set, atoms = StructureRingMissingMemberships([]Term{w.SOn}, square)
	require.Nil(t, set)
	require.Nil(t, atoms)
}

// TestStructureRing_ResidentFieldRecord: a resident
// field fact is read at its record, its quotient as a product with inverse.
func TestStructureRing_ResidentFieldRecord(t *testing.T) {
	fa := installFakeStructureRing(t)
	w := fa.abstract()
	A := fa.A
	inv := ext.Var("inv₀", core.MakeFun(A, A)).Core()
	div := ext.Var("div₀", core.MakeFun(A, core.MakeFun(A, A))).Core()
	for _, whole := range []bool{false, true} {
		predicate, carrier := fa.field, core.Term(fa.univ)
		if whole {
			predicate, carrier = fa.wholeField, fa.empty
		}
		field := ext.Apply(predicate, ext.Apply(fa.mkField, w.add, w.zero, w.neg, w.mul, w.one, w.sub, inv, div, carrier))
		x, y := w.x("x"), w.x("y")
		quotient := func(a, b core.Term) core.Term { return ext.Apply(div, a, b) }
		require.True(t, structureDecides(t, []Term{field},
			core.Eq(quotient(w.p(x, y), y), w.p(w.t(x, ext.Apply(inv, y)), w.t(y, ext.Apply(inv, y))))))
		require.True(t, structureDecides(t, []Term{field}, core.Eq(w.t(w.d(x, y), w.p(x, y)), w.d(w.t(x, x), w.t(y, y)))))
	}
}

// TestStructureRing_InstanceOnCarrierRefusesLiteral: an instance that
// is a ring on a carrier set may not spell a literal of its own — the
// leaves would reach it with no closure law to place it in the set.
func TestStructureRing_InstanceOnCarrierRefusesLiteral(t *testing.T) {
	fa := installFakeStructureRing(t)
	w := fa.abstract()
	two := ext.Var("two", fa.A).Core()
	require.Panics(t, func() {
		SetStructureInstances([]StructureInstance{{
			Fact:          prop.WrapProp(core.TestThm(w.SOn)),
			Literal:       func(t Term) (*big.Int, bool, bool) { return big.NewInt(2), t.Equals(two), t.Equals(two) },
			LiteralBridge: func(t Term, n *big.Int) *prop.PropWrapper { return prop.Refl(t) },
		}})
	})
}

// TestStructureRing_ContentNamesTheInstanceUse: the capability
// classifier says an atom is the structure ring's, and separately
// whether an installed instance reads it — a resident ring alone uses
// the laws, an instance at the atom's carrier the instances too, and the
// leaves read an instance only when the policy admits instances.
func TestStructureRing_ContentNamesTheInstanceUse(t *testing.T) {
	fa := installFakeStructureRing(t)
	w := fa.abstract()
	x, y := w.x("x"), w.x("y")
	square := core.Eq(w.t(w.p(x, y), w.p(x, y)), w.p(w.p(w.t(x, x), w.t(w.p(w.one, w.one), w.t(x, y))), w.t(y, y)))
	content, viaInstance := StructureRingContent(core.MakeProp(square, w.SOn, w.in(x), w.in(y)))
	require.True(t, content)
	require.False(t, viaInstance, "a resident ring on a set uses no instance")
	SetStructureInstances([]StructureInstance{{Fact: prop.WrapProp(core.TestThm(w.S))}})
	content, viaInstance = StructureRingContent(core.MakeProp(square))
	require.True(t, content)
	require.True(t, viaInstance, "the installed instance reads the atom")
	// The leaves read the instance only under StructureInstances.
	withInstances := NewArithCtxWithPolicy(nil, ArithPolicy{Nat: true, Structure: true, StructureInstances: true}, nil).Decide(square)
	require.NotNil(t, withInstances)
	require.Nil(t, NewArithCtxWithPolicy(nil, ArithPolicy{Nat: true, Structure: true}, nil).Decide(square),
		"without StructureInstances the instance is not read")
}

// Distinguished zero and one need the same literal bridges when they
// multiply a signed expression as when they normalize on their own.
func TestStructureRing_SignedLiteralCoefficients(t *testing.T) {
	fa := installFakeStructureRing(t)
	w := fa.abstract()
	x, z, d, v := w.x("x"), w.x("z"), w.x("d"), w.x("v")
	difference := w.d(x, z)
	for _, carrier := range []bool{false, true} {
		name := "universe"
		hyps := []Term{w.S}
		if carrier {
			name = "carrier"
			hyps = []Term{w.SOn, w.in(x), w.in(z), w.in(d), w.in(v)}
		}
		t.Run(name, func(t *testing.T) {
			rows := []struct {
				name        string
				left, right Term
			}{
				{"one on left", w.t(w.one, difference), difference},
				{"one on right", w.t(difference, w.one), difference},
				{"zero on left", w.t(w.zero, difference), w.zero},
				{"zero on right", w.t(difference, w.zero), w.zero},
			}
			for _, row := range rows {
				t.Run(row.name, func(t *testing.T) {
					require.True(t, structureDecides(t, hyps, core.Eq(row.left, row.right)))
				})
			}
			t.Run("unit cancellation", func(t *testing.T) {
				product := core.Eq(w.t(x, d), w.t(z, d))
				inverse := core.Eq(w.t(d, v), w.one)
				premises := append(append([]Term{}, hyps...), product, inverse)
				scaledProduct, productProof, ok := ScaleEquation(premises, v, product, nil)
				require.True(t, ok)
				require.True(t, productProof.Conclusion().AlphaEquals(scaledProduct))
				scaledInverse, inverseProof, ok := ScaleEquation(premises, difference, inverse, nil)
				require.True(t, ok)
				require.True(t, inverseProof.Conclusion().AlphaEquals(scaledInverse))
				require.True(t, structureDecides(t, append(premises, scaledProduct, scaledInverse), core.Eq(difference, w.zero)))
			})
		})
	}
}

func TestStructureRing_ExplicitContextPreservesProvenance(t *testing.T) {
	fa := installFakeStructureRing(t)
	w := fa.abstract()
	x := w.x("x")
	goal := core.Eq(w.t(w.one, x), x)
	for _, tag := range []Term{core.Eq(x, x), core.Eq(w.zero, w.zero)} {
		hypothesis := ext.WrapTerm(w.S).And(tag).Core()
		fact := prop.Assume(hypothesis).DeriveTrans(prop.HypAND0(w.S, tag))
		bound := BindStructureRing(fa.laws, nil, fact)
		proof, ok := bound.Identity(w.t(w.one, x), x)
		require.True(t, ok)
		require.True(t, prop.IsStronger(proof, core.MakeProp(goal, hypothesis)), "a context inherited a different proof's hypotheses")
	}
	// Carrier closure uses the supplied membership proof, with all original
	// assumptions restored rather than left as new bare memberships.
	hypothesis := ext.WrapTerm(w.SOn).And(w.in(x)).Core()
	premise := prop.Assume(hypothesis)
	ring := premise.DeriveTrans(prop.HypAND0(w.SOn, w.in(x)))
	member := premise.DeriveTrans(prop.HypAND1(w.SOn, w.in(x)))
	bound := BindStructureRing(fa.laws, nil, ring, member)
	proof, ok := bound.Member(w.t(x, x))
	require.True(t, ok)
	require.True(t, prop.IsStronger(proof, core.MakeProp(w.in(w.t(x, x)), hypothesis)))
	_, ok = bound.Member(w.x("outside"))
	require.False(t, ok)
}

func TestStructureRing_FieldCarrierGuards(t *testing.T) {
	fa := installFakeStructureRing(t)
	w := fa.abstract()
	inv := ext.Var("inv₀", core.MakeFun(fa.A, fa.A)).Core()
	div := ext.Var("div₀", core.MakeFun(fa.A, core.MakeFun(fa.A, fa.A))).Core()
	field := ext.Apply(fa.field, ext.Apply(fa.mkField, w.add, w.zero, w.neg, w.mul, w.one, w.sub, inv, div, w.c))
	x, y, z := w.x("x"), w.x("y"), w.x("z")
	quotient := func(a, b core.Term) core.Term { return ext.Apply(div, a, b) }
	goal := core.Eq(quotient(w.p(x, y), z), w.p(w.t(x, ext.Apply(inv, z)), w.t(y, ext.Apply(inv, z))))
	require.True(t, structureDecides(t, []Term{field, w.in(x), w.in(y), w.in(z)}, goal))
	require.False(t, structureDecides(t, []Term{field, w.in(x), w.in(y)}, goal))
	// Knowing the inverse's membership does not establish the original
	// denominator guard of the division law.
	require.False(t, structureDecides(t, []Term{field, w.in(x), w.in(y), w.in(ext.Apply(inv, z))}, goal))
	bound := BindStructureRing(fa.laws, nil, prop.Assume(field), prop.Assume(w.in(x)), prop.Assume(w.in(z)))
	member, ok := bound.Member(quotient(x, z))
	require.True(t, ok)
	require.True(t, member.Conclusion().AlphaEquals(w.in(quotient(x, z))))
}

func TestStructureRing_VariableRecord(t *testing.T) {
	fa := installFakeStructureRing(t)
	for _, whole := range []bool{false, true} {
		for _, record := range []core.Term{ext.Var("R", fa.ringType).Core(), ext.Var("F", fa.fieldType).Core()} {
			predicate := fa.commRing
			if record.Type().Equals(fa.fieldType) {
				predicate = fa.field
			}
			if whole {
				predicate = fa.wholeCommRing
				if record.Type().Equals(fa.fieldType) {
					predicate = fa.wholeField
				}
			}
			fact := ext.Apply(predicate, record)
			sr := fallbackReader.ringFor(prop.Assume(fact), nil)
			require.NotNil(t, sr)
			x, y := ext.Var("x", fa.A).Core(), ext.Var("y", fa.A).Core()
			goal := core.Eq(ext.Apply(sr.comps.add, x, y), ext.Apply(sr.comps.add, y, x))
			hyps := []Term{fact}
			if !whole {
				members := sr.members(nil)
				hyps = append(hyps, members.membership(x), members.membership(y))
			} else {
				require.True(t, sr.universe)
			}
			require.True(t, structureDecides(t, hyps, goal))
			negX := ext.Apply(sr.comps.neg, x)
			negatedSquare := core.Eq(ext.Apply(sr.comps.mul, negX, negX), ext.Apply(sr.comps.mul, x, x))
			require.True(t, structureDecides(t, hyps, negatedSquare), "declined %s", ext.PrintTerm(negatedSquare))
		}
	}
}

// TestStructureRing_AtomEquationFromTheContext: an equation between two
// ATOMS, `p = r`, mentions no component of the ring and is decided from
// the context's equations like any other — here a hypothesis pinning
// their difference, `p − r = zero`, resident as a hypothesis of its own
// or as a conjunct beside the memberships (the shape a carrier law's
// guards arrive in) — at every ring on its carrier, once the context
// holds an equation there; with none it is not the ring's content. On
// a carrier set an equation over an atom without a membership is not
// read, and the decline names that atom as it names the goal's.
func TestStructureRing_AtomEquationFromTheContext(t *testing.T) {
	fa := installFakeStructureRing(t)
	w := fa.abstract()
	p, r, u := w.x("p"), w.x("r"), w.x("u")
	goal := core.Eq(p, r)
	diff := core.Eq(w.d(p, r), w.zero)
	t.Run("on 𝕌", func(t *testing.T) {
		require.True(t, structureDecides(t, []Term{w.S, diff}, goal))
		require.True(t, IsStructureRingContent([]Term{w.S, diff}, goal))
	})
	t.Run("two bare equations chain", func(t *testing.T) {
		require.True(t, structureDecides(t, []Term{w.S, core.Eq(p, u), core.Eq(u, r)}, goal))
	})
	t.Run("without an equation in the context the atom is not the ring's", func(t *testing.T) {
		require.False(t, IsStructureRingContent([]Term{w.S}, goal))
		require.False(t, IsStructureRingContent([]Term{w.S, w.in(p), goal}, goal), "the atom itself is no equation to combine with")
		require.Nil(t, NewArithCtxWithPolicy([]Term{w.S}, ArithPolicy{Nat: true, Structure: true}, nil).Decide(goal))
	})
	t.Run("on a carrier set, the memberships beside the equation", func(t *testing.T) {
		require.True(t, structureDecides(t, []Term{w.SOn, w.in(p), w.in(r), diff}, goal))
	})
	t.Run("on a carrier set, the equation a conjunct of the memberships", func(t *testing.T) {
		conj := ext.WrapTerm(w.in(p)).And(ext.WrapTerm(w.in(r)).And(diff).Core()).Core()
		require.True(t, structureDecides(t, []Term{w.SOn, conj}, goal))
		set, atoms := StructureRingMissingMemberships([]Term{w.SOn, conj}, goal)
		require.Nil(t, set)
		require.Nil(t, atoms)
	})
	t.Run("an equation over an atom without a membership is not read, and the atom is named", func(t *testing.T) {
		// p + u = r + u ⊢ p = r is the combination with coefficient 1 …
		shifted := core.Eq(w.p(p, u), w.p(r, u))
		require.True(t, structureDecides(t, []Term{w.SOn, w.in(p), w.in(r), w.in(u), shifted}, goal))
		// … and declines, naming u, when u's membership is not resident:
		// the goal's own atoms are held, so the name comes from the equation.
		hyps := []Term{w.SOn, w.in(p), w.in(r), shifted}
		require.False(t, structureDecides(t, hyps, goal))
		set, atoms := StructureRingMissingMemberships(hyps, goal)
		require.True(t, set.Equals(w.c))
		require.Len(t, atoms, 1)
		require.True(t, atoms[0].Equals(u), "the missing atom is u, got %s", ext.PrintTerm(atoms[0]))
	})
}
