package omega

import (
	"iter"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// fakeModulus is a modulus over a carrier of its own: a map into ℝ with
// a product and a negation it is stated across, the laws fabricated.
type fakeModulus struct {
	m, mul, neg core.ConstTerm
	z, w        *ext.TermWrapper
}

func newFakeModulus() *fakeModulus {
	A := core.MakeVarType("A")
	constant := func(name string, ty core.HolType) core.ConstTerm {
		return core.MakeConstTerm(core.MakeConstMeta(core.TermName(name), ty), ty)
	}
	return &fakeModulus{
		m:   constant("zz_modulus_test", core.MakeFun(A, dsl.RealType)),
		mul: constant("zz_modulus_mul_test", core.MakeFun(A, core.MakeFun(A, A))),
		neg: constant("zz_modulus_neg_test", core.MakeFun(A, A)),
		z:   ext.Var("z", A),
		w:   ext.Var("w", A),
	}
}

func (f *fakeModulus) of(x Term) Term       { return ext.Apply(f.m, x) }
func (f *fakeModulus) times(x, y Term) Term { return ext.Apply(f.mul, x, y) }
func (f *fakeModulus) minus(x Term) Term    { return ext.Apply(f.neg, x) }

func (f *fakeModulus) law(body Term, binders ...Term) *prop.PropWrapper {
	return prop.WrapProp(core.TestThm(ext.ForAll(binders...)(body).Core()))
}

// laws are the sign, the product law and the negation law.
func (f *fakeModulus) laws() *ModulusLaws {
	z, w := f.z.Core(), f.w.Core()
	return &ModulusLaws{
		Nonneg: f.law(realLeT(realLit(0), f.of(z)), f.z),
		Mul:    f.law(core.Eq(f.of(f.times(z, w)), realStarT(f.of(z), f.of(w))), f.z, f.w),
		Neg:    f.law(core.Eq(f.of(f.minus(z)), f.of(z)), f.z),
	}
}

func installFakeModulus(t *testing.T) *fakeModulus {
	t.Helper()
	f := newFakeModulus()
	SetModulusLaws(f.laws())
	t.Cleanup(func() { SetModulusLaws(nil) })
	return f
}

// TestModulus_LawsRewriteTowardTheLeaves: a modulus of a compound term a
// law reads is rewritten by it, to the fixpoint under the deep rewrite,
// and a modulus of a term no law reads is left as it is.
func TestModulus_LawsRewriteTowardTheLeaves(t *testing.T) {
	f := installFakeModulus(t)
	a, b := f.z.Core(), f.w.Core()
	nested := f.of(f.times(a, f.minus(f.times(b, a))))
	w := prop.DeepRewrite(modulusSimpStep)(nested)
	require.NotNil(t, w)
	want := realStarT(f.of(a), realStarT(f.of(b), f.of(a)))
	require.True(t, prop.Rhs(w).AlphaEquals(want), "pushed to %s", ext.PrintTerm(prop.Rhs(w)))
	require.Nil(t, modulusSimpStep(f.of(a)), "a modulus of a variable is a leaf")
	require.Nil(t, modulusSimpStep(f.times(a, b)), "a term that is no modulus is not the leaf's")
}

// TestModulus_SignFacts: the sign facts are one per modulus the terms
// spell outside a binder, less those whose sign, strict or not, is
// resident.
func TestModulus_SignFacts(t *testing.T) {
	f := installFakeModulus(t)
	a, b := f.z.Core(), f.w.Core()
	sum := realDomain.plus(f.of(a), f.of(f.times(a, b)))
	facts := installedModulus.facts(nil, nil, sum, f.of(a))
	require.Len(t, facts, 2)
	require.True(t, facts[0].Conclusion().AlphaEquals(realLeT(realLit(0), f.of(a))))
	require.True(t, facts[1].Conclusion().AlphaEquals(realLeT(realLit(0), f.of(f.times(a, b)))))
	for _, fact := range facts {
		require.Zero(t, fact.NumHyps())
	}

	strict := realLtT(realLit(0), f.of(a))
	require.Len(t, installedModulus.facts([]Term{strict}, nil, sum), 1, "a resident strict sign stands for the fact")
	weak := realLeT(realLit(0), f.of(a))
	require.Len(t, installedModulus.facts([]Term{weak}, nil, sum), 1, "a resident sign is not stated twice")

	bound := ext.ForAll(f.z)(realLeT(f.of(a), realLit(1))).Core()
	require.Empty(t, installedModulus.facts(nil, nil, bound), "a modulus under a binder has no closed sign fact")
}

// TestModulus_ProverReadsTheSign: the real atom prover wrapped by
// modulusProver decides with `&0 ≤ |u|` in hand and returns a proof that
// stands on the given hypotheses alone.
func TestModulus_ProverReadsTheSign(t *testing.T) {
	f := installFakeModulus(t)
	a := f.z.Core()
	var seen []Term
	inner := func(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
		for h := range hyps {
			seen = append(seen, h)
		}
		return prop.Assume(realLeT(realLit(0), f.of(a))), true
	}
	w, ok := modulusProver(inner, nil)(func(yield func(Term) bool) {}, realLeT(realLit(0), f.of(a)))
	require.True(t, ok)
	require.Len(t, seen, 1, "the sign fact joins the hypotheses")
	require.Zero(t, w.NumHyps(), "and is cut from the proof")
}

// TestModulus_InstallRefusesALawThatDoesNotMoveInward: the rewrite
// terminates because every law moves the modulus strictly inward, so the
// install refuses a law that does not — the modulus put back on a
// compound term, the modulus of a bare variable on the left, a law with a
// hypothesis — and an install with no sign law, which names the modulus.
func TestModulus_InstallRefusesALawThatDoesNotMoveInward(t *testing.T) {
	f := newFakeModulus()
	t.Cleanup(func() { SetModulusLaws(nil) })
	z, w := f.z.Core(), f.w.Core()
	bad := map[string]*prop.PropWrapper{
		"the modulus on a compound term again": f.law(core.Eq(f.of(f.times(z, w)), f.of(f.times(w, z))), f.z, f.w),
		"the modulus of a variable":            f.law(core.Eq(f.of(z), f.of(f.minus(z))), f.z),
		"a binder the left side lacks":         f.law(core.Eq(f.of(f.minus(z)), realStarT(f.of(z), f.of(w))), f.z, f.w),
		"no equation":                          f.law(realLeT(f.of(f.minus(z)), f.of(z)), f.z),
		"a hypothesis":                         prop.Assume(core.Eq(f.of(f.minus(z)), f.of(z))),
	}
	for name, law := range bad {
		laws := f.laws()
		laws.Neg = law
		require.Panics(t, func() { SetModulusLaws(laws) }, name)
	}
	noSign := f.laws()
	noSign.Nonneg = nil
	require.Panics(t, func() { SetModulusLaws(noSign) })
}

// TestModulus_Content: a statement spells the modulus when the constant
// stands anywhere in it, a hypothesis and a binder included.
func TestModulus_Content(t *testing.T) {
	f := installFakeModulus(t)
	a := f.z.Core()
	plain := realLeT(realLit(0), realLit(1))
	require.False(t, ModulusContent(core.MakeProp(plain)))
	require.True(t, ModulusContent(core.MakeProp(realLeT(realLit(0), f.of(a)))))
	require.True(t, ModulusContent(core.MakeProp(plain, realLeT(f.of(a), realLit(1)))))
	bound := ext.ForAll(f.z)(realLeT(f.of(a), realLit(1))).Core()
	require.True(t, ModulusContent(core.MakeProp(bound)))
	SetModulusLaws(nil)
	require.False(t, ModulusContent(core.MakeProp(bound)))
}
