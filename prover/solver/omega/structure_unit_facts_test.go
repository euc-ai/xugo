package omega

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// fieldWorld is an abstract field over the fake algebra: its inverse and
// division beside the abstract ring's components, and the fact `field_on`
// at the record on the carrier set c₀ (onSet) or `field` on 𝕌.
type fieldWorld struct {
	*abstractWorld
	inv, div core.Term
	fact     core.Term
	onSet    bool
}

func (fa *fakeAlgebra) fieldWorld(onSet bool) *fieldWorld {
	w := fa.abstract()
	inv := ext.Var("inv₀", core.MakeFun(fa.A, fa.A)).Core()
	div := ext.Var("div₀", core.MakeFun(fa.A, core.MakeFun(fa.A, fa.A))).Core()
	f := &fieldWorld{abstractWorld: w, inv: inv, div: div, onSet: onSet}
	if onSet {
		f.fact = ext.Apply(fa.field, ext.Apply(fa.mkField, w.add, w.zero, w.neg, w.mul, w.one, w.sub, inv, div, w.c))
	} else {
		f.fact = ext.Apply(fa.wholeField, ext.Apply(fa.mkField, w.add, w.zero, w.neg, w.mul, w.one, w.sub, inv, div, fa.empty))
	}
	return f
}

func (f *fieldWorld) i(a core.Term) core.Term    { return ext.Apply(f.inv, a) }
func (f *fieldWorld) q(a, b core.Term) core.Term { return ext.Apply(f.div, a, b) }
func (f *fieldWorld) nonzero(a core.Term) core.Term {
	return not(core.Eq(a, f.zero))
}

// numeral is the ring's canonical numeral n, monoid_pow(add, zero, one, n).
func (f *fieldWorld) numeral(n uint64) core.Term {
	return ext.Apply(f.fa.monoidPow, f.add, f.zero, f.one, Numeral(n))
}

// hyps is the field fact, the given hypotheses and, on the carrier set,
// the memberships of the atoms.
func (f *fieldWorld) hyps(atoms []core.Term, given ...core.Term) []Term {
	out := append([]Term{f.fact}, given...)
	if f.onSet {
		for _, a := range atoms {
			out = append(out, f.in(a))
		}
	}
	return out
}

// TestStructureRing_UnitFacts: at a field, a factor and its inverse
// cancel wherever they stand in a monomial (structure_unit_facts.go) —
// split across a product, behind a quotient, only after the product is
// multiplied out, or inside a context equation — on the context's
// evidence that the factor is not zero, at a field on 𝕌 and on a carrier
// set alike; with no evidence nothing cancels.
func TestStructureRing_UnitFacts(t *testing.T) {
	fa := installFakeStructureRing(t)
	for _, onSet := range []bool{false, true} {
		f := fa.fieldWorld(onSet)
		a, b, v, u, l := f.x("a"), f.x("b"), f.x("v"), f.x("u"), f.x("l")
		x, c, fx, p, h := f.x("x"), f.x("c"), f.x("fx"), f.x("p"), f.x("h")
		two := f.numeral(2)
		rows := []struct {
			name  string
			atoms []core.Term
			given []core.Term
			goal  core.Term
		}{
			{"the pair split across a product", []core.Term{a, v}, []core.Term{f.nonzero(v)},
				core.Eq(f.t(f.t(a, f.i(v)), v), a)},
			{"behind a quotient", []core.Term{a, v}, []core.Term{f.nonzero(v)},
				core.Eq(f.t(f.q(a, v), v), a)},
			{"the evidence spelled the other way round", []core.Term{a, v}, []core.Term{not(core.Eq(f.zero, v))},
				core.Eq(f.t(f.q(a, v), v), a)},
			{"a difference quotient times its offset, from x ≠ c", []core.Term{fx, p, x, c}, []core.Term{not(core.Eq(x, c))},
				core.Eq(f.t(f.q(f.d(fx, p), f.d(x, c)), f.d(x, c)), f.d(fx, p))},
			{"two pairs, after multiplying out", []core.Term{u, l}, []core.Term{f.nonzero(u), f.nonzero(l)},
				core.Eq(f.t(f.d(f.i(u), f.i(l)), f.t(u, l)), f.d(l, u))},
			{"a literal divisor, its evidence resident", []core.Term{b, u}, []core.Term{f.nonzero(two)},
				core.Eq(f.t(f.q(b, two), f.p(u, u)), f.t(b, u))},
			{"a pair inside a context equation", []core.Term{h, a, v, b}, []core.Term{f.nonzero(v), core.Eq(h, f.p(f.t(f.q(a, v), v), b))},
				core.Eq(h, f.p(a, b))},
			// Several pairs in ONE monomial: the second pair's cancellation
			// is read off the monomial the first pair's fact reduces it to.
			{"two pairs in one monomial", []core.Term{a, b, u, l}, []core.Term{f.nonzero(u), f.nonzero(l)},
				core.Eq(f.t(f.t(f.q(a, u), f.q(b, l)), f.t(u, l)), f.t(a, b))},
			{"three pairs in one monomial", []core.Term{a, b, x, u, l, v}, []core.Term{f.nonzero(u), f.nonzero(l), f.nonzero(v)},
				core.Eq(f.t(f.t(f.t(f.q(a, u), f.q(b, l)), f.q(x, v)), f.t(f.t(u, l), v)), f.t(f.t(a, b), x))},
			// The inverse of a product is the product of the inverses: a
			// divisor that is a product cancels factor by factor, on each
			// factor's evidence or on the product's.
			{"a quotient by a product", []core.Term{a, u, l}, []core.Term{f.nonzero(u), f.nonzero(l)},
				core.Eq(f.t(f.t(f.q(a, f.t(u, l)), u), l), a)},
			{"the inverse of a product, written out", []core.Term{a, u, l}, []core.Term{f.nonzero(u), f.nonzero(l)},
				core.Eq(f.t(f.t(f.t(a, f.i(f.t(u, l))), u), l), a)},
			{"a quotient by a product, the product nonzero the evidence", []core.Term{a, u, l}, []core.Term{f.nonzero(f.t(u, l))},
				core.Eq(f.t(f.q(a, f.t(u, l)), f.t(u, l)), a)},
			{"the product nonzero, its factors cancelled apart", []core.Term{a, u, l}, []core.Term{f.nonzero(f.t(u, l))},
				core.Eq(f.t(f.t(f.q(a, f.t(u, l)), l), u), a)},
			{"a product of quotients is the quotient of the products, on no evidence", []core.Term{a, b, u, l}, nil,
				core.Eq(f.t(f.q(a, u), f.q(b, l)), f.q(f.t(a, b), f.t(u, l)))},
		}
		for _, r := range rows {
			require.True(t, structureDecides(t, f.hyps(r.atoms, r.given...), r.goal), "onSet=%v: %s declined", onSet, r.name)
		}
		if onSet {
			// The evidence as a conjunct beside the membership, the shape a
			// carrier law's guards arrive in.
			conj := ext.WrapTerm(f.in(v)).And(f.nonzero(v)).Core()
			require.True(t, structureDecides(t, []Term{f.fact, f.in(a), conj}, core.Eq(f.t(f.q(a, v), v), a)),
				"the evidence as a conjunct was not read")
			// No membership for the divisor: declined, not a panic.
			require.False(t, structureDecides(t, []Term{f.fact, f.in(a), f.nonzero(v)}, core.Eq(f.t(f.q(a, v), v), a)))
		}

		quotient := core.Eq(f.t(f.q(a, v), v), a)
		// No evidence, no fact: inv(v)·v is not one at v = zero.
		require.False(t, structureDecides(t, f.hyps([]core.Term{a, v}), quotient), "cancelled v with no evidence")
		require.False(t, structureDecides(t, f.hyps([]core.Term{a, v, u}, f.nonzero(u)), quotient),
			"cancelled v on another divisor's evidence")
		// Two pairs, one divisor without evidence: its pair stays.
		require.False(t, structureDecides(t, f.hyps([]core.Term{a, b, u, l}, f.nonzero(u)),
			core.Eq(f.t(f.t(f.q(a, u), f.q(b, l)), f.t(u, l)), f.t(a, b))), "cancelled l with no evidence")
		// A literal is not nonzero by itself: a field may have characteristic 2.
		require.False(t, structureDecides(t, f.hyps([]core.Term{b, u}), core.Eq(f.t(f.q(b, two), f.p(u, u)), f.t(b, u))),
			"cancelled the literal 2 with no evidence")

		// A goal the context's equations decide alone does not read the
		// unit facts: its close carries no evidence.
		hyps := f.hyps([]core.Term{a, b, v}, f.nonzero(v))
		w := NewArithCtxWithPolicy(hyps, ArithPolicy{Nat: true, Structure: true}, nil).
			Decide(core.Eq(f.p(f.q(a, v), b), f.p(b, f.q(a, v))))
		require.NotNil(t, w)
		require.True(t, prop.Rhs(w).Equals(prop.T))
		require.False(t, w.HasHyp(f.nonzero(v)), "an identity closed through a unit fact")

		// One fact per pair and cofactor in sight; none without evidence.
		sr := fallbackReader.ringFor(prop.Assume(f.fact), nil)
		require.NotNil(t, sr)
		bound := sr.bind(hyps)
		lhs := f.t(f.q(a, v), v)
		units := bound.unitEquations(hyps, bound.equationHyps(hyps), lhs, a)
		require.Len(t, units, 1)
		require.True(t, units[0].proof.HasHyp(f.nonzero(v)), "the unit fact does not rest on the evidence")
		bare := f.hyps([]core.Term{a, b, v})
		bareBound := sr.bind(bare)
		require.Empty(t, bareBound.unitEquations(bare, bareBound.equationHyps(bare), lhs, a))

		// The zero is no divisor: zero put for zero changes nothing, so a
		// resident disequality is no evidence for it and the search ends.
		require.Nil(t, bound.proveNonzero(hyps, f.zero), "read v ≠ zero as evidence that zero is nonzero")
		require.False(t, structureDecides(t, hyps, core.Eq(f.t(f.q(a, f.zero), f.zero), a)), "cancelled a division by zero")
	}
}

// TestStructureRing_RealEmbedding: at an instance that names an injective
// embedding of ℝ sending &0 to its zero, an embedded real is not zero
// wherever ℝ's arithmetic shows the real is not — a literal by itself, a
// negative literal, a variable from a resident sign — so its inverse
// cancels with no premise at the carrier, and the close of a literal is a
// theorem. With ℝ's arithmetic withheld by the policy, with no evidence
// for the real, at the embedded zero, and at an abstract field, which
// names no embedding, nothing cancels.
func TestStructureRing_RealEmbedding(t *testing.T) {
	fa := installFakeStructureRing(t)
	SetRealLemmaBundle(&RealLemmaBundle{})
	t.Cleanup(func() { SetRealLemmaBundle(nil) })
	A := fa.A
	p, q := ext.Var("p", A), ext.Var("q", A)
	cadd := core.NewConstDef(p.To(q.To(p)).Core(), "zz_eadd")
	cmul := core.NewConstDef(p.To(q.To(q)).Core(), "zz_emul")
	csub := core.NewConstDef(p.To(q.To(p)).Core(), "zz_esub")
	cdiv := core.NewConstDef(p.To(q.To(p)).Core(), "zz_ediv")
	cneg := core.NewConstDef(p.To(p).Core(), "zz_eneg")
	cinv := core.NewConstDef(p.To(p).Core(), "zz_einv")
	embType := core.MakeFun(dsl.RealType, A)
	emb := core.MakeConstTerm(core.MakeConstMeta("zz_eemb", embType), embType)
	embed := func(r Term) Term { return ext.Apply(emb, r) }
	czero, cone := embed(realLit(0)), ext.Var("cone", A).Core()
	fact := prop.WrapProp(core.TestThm(ext.Apply(fa.wholeField, ext.Apply(fa.mkField, cadd, czero, cneg, cmul, cone, csub, cinv, cdiv, fa.empty))))
	rx, ry := ext.Var("x", dsl.RealType), ext.Var("y", dsl.RealType)
	injective := prop.WrapProp(core.TestThm(ext.ForAll(rx)(ext.ForAll(ry)(ext.WrapTerm(
		core.Eq(core.Eq(embed(rx.Core()), embed(ry.Core())), core.Eq(rx.Core(), ry.Core()))))).Core()))
	SetStructureInstances([]StructureInstance{{Fact: fact, RealEmbedding: &RealEmbedding{Map: emb, Injective: injective}}})

	x := ext.Var("x", A).Core()
	r := ext.Var("r", dsl.RealType).Core()
	cancels := func(d Term) Term { // x / d · d = x
		return core.Eq(ext.Apply(cmul, ext.Apply(cdiv, x, d), d), x)
	}
	with := ArithPolicy{Nat: true, Real: true, Structure: true, StructureInstances: true}
	without := ArithPolicy{Nat: true, Structure: true, StructureInstances: true}
	decides := func(policy ArithPolicy, hyps []Term, goal Term) *prop.PropWrapper {
		w := NewArithCtxWithPolicy(hyps, policy, nil).Decide(goal)
		if w == nil || !prop.Rhs(w).Equals(prop.T) {
			return nil
		}
		closed := w.EqSym().EqMP(prop.DerivesTrue)
		require.True(t, prop.IsStronger(closed, core.MakeProp(goal, hyps...)),
			"the closing theorem carries a hypothesis the goal lacks: %v", closed.Hyps())
		return w
	}
	two := embed(realLit(2))
	w := decides(with, nil, cancels(two))
	require.NotNil(t, w, "the embedded literal 2 did not cancel")
	require.Equal(t, 0, w.NumHyps(), "an embedded literal's evidence is ℝ's: the close carries no hypothesis")
	require.NotNil(t, decides(with, nil, cancels(embed(realNegT(realLit(2))))), "the embedded −2 did not cancel")
	sign := realLtT(realLit(0), r)
	require.NotNil(t, decides(with, []Term{sign}, cancels(embed(r))), "an embedded real of resident sign did not cancel")

	require.Nil(t, decides(without, nil, cancels(two)), "cancelled the embedded 2 with ℝ's arithmetic withheld")
	require.Nil(t, decides(with, nil, cancels(embed(r))), "cancelled an embedded real with no evidence")
	require.Nil(t, decides(with, nil, cancels(czero)), "cancelled the embedded zero")

	// An abstract field names no embedding: its literal stays a premise to
	// name, ℝ's arithmetic admitted or not.
	f := fa.fieldWorld(false)
	b, u := f.x("b"), f.x("u")
	literal := core.Eq(f.t(f.q(b, f.numeral(2)), f.p(u, u)), f.t(b, u))
	require.Nil(t, decides(with, f.hyps([]core.Term{b, u}), literal), "an abstract field cancelled the literal 2 with no evidence")
}
