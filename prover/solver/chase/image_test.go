package chase

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/stretchr/testify/require"
)

// argumentOf reads the argument of a λ's value off the value: where the
// body spells the binder the value spells the argument, at every place
// the same one, and never a variable the body binds.
func TestArgumentOf(t *testing.T) {
	w := newFakeWorldBase()
	v := w.elem("v").(core.VarTerm)
	a, b := w.elem("a"), w.elem("b")
	g, h := w.fn("g"), w.fn("h")
	u, z := w.elem("u").(core.VarTerm), w.elem("z").(core.VarTerm)
	p := core.Var("p", core.MakeFun(w.T, core.MakeFun(w.T, w.T)))
	other := core.Var("s", w.S)
	for _, row := range []struct {
		name  string
		body  core.Term
		value core.Term
		arg   core.Term
	}{
		{"one place", w.ap(g, v), w.ap(g, a), a},
		{"the binder alone", v, w.ap(g, a), w.ap(g, a)},
		{"a compound argument", w.ap(g, w.ap(h, v)), w.ap(g, w.ap(h, w.plus(a, b))), w.plus(a, b)},
		{"two places, one argument", w.plus(w.ap(g, v), w.ap(h, v)), w.plus(w.ap(g, a), w.ap(h, a)), a},
		{"two places, two arguments", w.plus(w.ap(g, v), w.ap(h, v)), w.plus(w.ap(g, a), w.ap(h, b)), nil},
		{"another head", w.ap(g, v), w.ap(h, a), nil},
		{"a body without the binder", w.ap(g, a), w.ap(g, a), nil},
		{"under a binder", core.Abs(u, w.ap(p, v, u)), core.Abs(z, w.ap(p, a, z)), a},
		{"an argument that would name the bound variable", core.Abs(u, w.ap(p, v, u)), core.Abs(z, w.ap(p, z, z)), nil},
		{"a value of another type", w.ap(g, v), other, nil},
	} {
		arg, ok := argumentOf(core.Abs(v, row.body), row.value)
		if row.arg == nil {
			require.False(t, ok, row.name)
			continue
		}
		require.True(t, ok, row.name)
		require.True(t, arg.AlphaEquals(row.arg), "%s: read %v", row.name, arg)
	}
}

// A homomorphism given by a λ is linear on the values a leaf spells
// computed: `g(k(x + y))` is the value of `λv. g(k(v))` at the sum, read
// off the body, where no application of the λ stands in the leaf.
func TestChase_LambdaHomomorphismValueIsReadByItsBody(t *testing.T) {
	w := installFake(t)
	M, N := w.set("M"), w.set("N")
	g, k := w.fn("g"), w.fn("k")
	v := w.elem("v").(core.VarTerm)
	value := func(x core.Term) core.Term { return w.ap(g, w.ap(k, x)) }
	lambda := core.Abs(v, value(v))
	x, y := w.elem("x"), w.elem("y")
	hyps := []core.Term{w.module(M), w.module(N), w.homOf(lambda, M, N), w.in(x, M), w.in(y, M)}
	closes(t, core.MakeProp(eq(value(w.plus(x, w.minus(y))), w.plus(value(x), w.minus(value(y)))), hyps...), 0)
	closes(t, core.MakeProp(eq(value(w.zero), w.zero), hyps...), 0)
	closes(t, core.MakeProp(w.in(value(w.plus(x, y)), N), hyps...), 0)
}

// The facts and the goal that state a map's value at a variable they
// bind — one-to-one, a preimage asked, onto pointwise — name a map given
// by a λ through that value, `g(k(u))` for `λv. g(k(v))`.
func TestChase_LambdaHomomorphismShapesAreReadByItsBody(t *testing.T) {
	w := installFake(t)
	M, N := w.set("M"), w.set("N")
	g, k := w.fn("g"), w.fn("k")
	v := w.elem("v").(core.VarTerm)
	value := func(x core.Term) core.Term { return w.ap(g, w.ap(k, x)) }
	lambda := core.Abs(v, value(v))
	x, y, b := w.elem("x"), w.elem("y"), w.elem("b")
	hyps := []core.Term{w.module(M), w.module(N), w.homOf(lambda, M, N), w.in(x, M), w.in(y, M)}
	// One-to-one, the fact spelling the map's values: equal values, equal elements.
	injective := append([]core.Term{w.oneToOne(lambda, M), eq(value(x), value(y))}, hyps...)
	closes(t, core.MakeProp(eq(x, y), injective...), 1)
	// A preimage of a value the leaf names.
	closes(t, core.MakeProp(preimage(w, lambda, M, value(w.plus(x, y))), hyps...), 0)
	// Onto, stated pointwise: every element of N is a value.
	z, q := w.elem("z"), w.elem("q")
	pointwise := all([]core.Term{z}, imp(w.in(z, N), ext.Exists(q)(and(w.in(q, M), eq(value(q), z))).Core()))
	onto := append([]core.Term{pointwise, w.in(b, N)}, hyps...)
	closes(t, core.MakeProp(preimage(w, lambda, M, b), onto...), 1)
}

// packedFamilies installs a packed pair of families over degrees, sets
// and maps, with the two projections that read them back, and returns
// the packing and the projections.
func (w *_FakeWorld) packedFamilies() (pack, terms, maps core.Term) {
	sets, fns := core.MakeFun(dslNum(), w.setT), core.MakeFun(dslNum(), core.MakeFun(w.T, w.T))
	packedType := core.MakeCompositeType(core.MakeMetaType("zz_families_chase", 1), w.T)
	pack = opaqueRecordConst("zz_mk_families_chase", []core.HolType{sets, fns}, packedType)
	terms = opaqueRecordConst("zz_families_terms_chase", []core.HolType{packedType}, sets)
	maps = opaqueRecordConst("zz_families_maps_chase", []core.HolType{packedType}, fns)
	parts := []core.Term{core.Var("F", sets), core.Var("D", fns)}
	packed := w.ap(pack, parts...)
	read := []prop.Rewrite{
		recordDefinition(thm(all(parts, eq(w.ap(terms, packed), parts[0])))),
		recordDefinition(thm(all(parts, eq(w.ap(maps, packed), parts[1])))),
	}
	previous := w.laws.NormalizeWith
	w.laws.NormalizeWith = func(r omega.LibraryRead) prop.Rewrite {
		return prop.DeepRewrite(append([]prop.Rewrite{previous(r)}, read...)...)
	}
	SetLaws(w.laws)
	return pack, terms, maps
}

// A packed value holds its families over degrees as λs, terms
// `λk. P(nxt(k))` and maps `λk. λv. d(nxt(k))(v)`, and a projection
// computed at it leaves the λ applied at the degree. In the normal form
// the carrier a projection gives at n is the `P(nxt(n))` a membership
// spells, whichever of the homomorphism and the memberships spells
// which, and the map a projection gives there, itself a λ, carries the
// sum the leaf applies it to.
func TestChase_ProjectedFamilyIsReadAtItsDegree(t *testing.T) {
	w := installFake(t)
	pack, terms, maps := w.packedFamilies()
	P, D, N := w.family("P"), w.mapFamily("d"), w.set("N")
	nxt := nxtOf()
	n, k := numVar("n"), numVar("k").(core.VarTerm)
	v := w.elem("v").(core.VarTerm)
	packed := w.ap(pack,
		core.Abs(k, w.ap(P, w.ap(nxt, k))),
		core.Abs(k, core.Abs(v, w.ap(w.ap(D, w.ap(nxt, k)), v))))
	member, projected := w.ap(P, w.ap(nxt, n)), w.ap(w.ap(terms, packed), n)
	f, x, y := w.fn("f"), w.elem("x"), w.elem("y")
	linear := func(f core.Term) core.Term { return eq(w.ap(f, w.plus(x, y)), w.plus(w.ap(f, x), w.ap(f, y))) }
	for _, row := range []struct{ hom, elements core.Term }{
		{member, member}, {projected, member}, {member, projected}, {projected, projected},
	} {
		closes(t, core.MakeProp(linear(f), w.homOf(f, row.hom, N), w.in(x, row.elements), w.in(y, row.elements)), 0)
	}
	// A preimage through an onto map whose source is the projected family.
	b := w.elem("b")
	onto := []core.Term{w.homOf(f, projected, N), w.onto(f, projected, N), w.in(b, N)}
	closes(t, core.MakeProp(preimage(w, f, member, b), onto...), 1)
	// The projected map at the degree, applied to a sum, against its
	// values spelled out.
	mapMember, mapProjected := w.ap(D, w.ap(nxt, n)), w.ap(w.ap(maps, packed), n)
	closes(t, core.MakeProp(linear(mapProjected), w.homOf(mapProjected, member, N), w.in(x, projected), w.in(y, projected)), 0)
	closes(t, core.MakeProp(linear(mapMember), w.homOf(mapProjected, member, N), w.in(x, member), w.in(y, member)), 0)
}
