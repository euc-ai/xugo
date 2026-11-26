package omega

// The monomial-basis extraction over ℤ (domain.go polyMul, wired to
// intRing.polyMul in int_lemmas.go): the int twin of real_poly_basis_test.go.
// A product of atoms is one monomial unknown to the int linear layer; a
// product of integers is an integer, so the integer layer (discreteness, the
// rounding cut) treats it as any other unknown. The enumeration gate keeps
// its meaning through genuinelyLinear (TestIntBoundedEnum pins the rows).

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
)

// TestIntPolyBasisCanonicalForms pins linOf's expansion over ℤ against
// hand-built canonical forms via the buildTerm rendering.
func TestIntPolyBasisCanonicalForms(t *testing.T) {
	a, b, c := intVar("a"), intVar("b"), intVar("c")
	m := func(c int64, a Term) Term { return intMonoTerm(integerOf(c), a) }
	cases := []struct {
		name      string
		in, canon Term
	}{
		{"commutation", intStarT(a, b), intStarT(b, a)},
		{"association", intStarT(intStarT(a, b), c), intStarT(a, intStarT(b, c))},
		{"cross terms", intStarT(intPlusT(a, intLit(1)), intPlusT(b, intLit(2))),
			intPlusT(intPlusT(intPlusT(intStarT(a, b), m(2, a)), b), intLit(2))},
		{"like monomials merge", intPlusT(m(2, intStarT(a, b)), m(3, intStarT(b, a))), m(5, intStarT(a, b))},
		{"scaled factors", intStarT(m(2, a), m(3, b)), m(6, intStarT(a, b))},
	}
	for _, tc := range cases {
		lfIn, ok1 := intDomain.linOf(tc.in)
		lfCanon, ok2 := intDomain.linOf(tc.canon)
		if !ok1 || !ok2 {
			t.Errorf("%s: linOf declined %v or %v", tc.name, tc.in, tc.canon)
			continue
		}
		if !intDomain.buildTerm(lfIn).AlphaEquals(intDomain.buildTerm(lfCanon)) {
			t.Errorf("%s: linOf(%v) = %v; want the form of %v = %v",
				tc.name, tc.in, intDomain.buildTerm(lfIn), tc.canon, intDomain.buildTerm(lfCanon))
		}
	}
}

// TestIntPolyBasisNormalizeProofLockstep: the proof side (intRing.
// normalizeProof) produces the model's exact form on polynomial terms.
func TestIntPolyBasisNormalizeProofLockstep(t *testing.T) {
	a, b, c := intVar("a"), intVar("b"), intVar("c")
	m := func(c int64, a Term) Term { return intMonoTerm(integerOf(c), a) }
	for _, e := range []Term{
		intStarT(a, b), intStarT(b, a), intStarT(intStarT(a, b), c),
		intStarT(intPlusT(a, intLit(1)), intPlusT(b, intLit(2))),
		intStarT(intPlusT(a, b), intPlusT(a, b)),
		intPlusT(m(2, intStarT(a, b)), m(3, intStarT(b, a))),
		intStarT(m(2, a), m(3, b)),
	} {
		checkIntNormalize(t, e)
	}
}

// TestIntPolyBasisGenuinelyLinear pins the enumeration gate's test: a
// product atom makes a side NOT genuinely linear although linOf accepts it.
func TestIntPolyBasisGenuinelyLinear(t *testing.T) {
	x := intVar("x")
	xx := intStarT(x, x)
	if !intDomain.isLinear(xx) || intDomain.genuinelyLinear(xx) {
		t.Errorf("x·x: isLinear=%v genuinelyLinear=%v; want true, false",
			intDomain.isLinear(xx), intDomain.genuinelyLinear(xx))
	}
	if !intGoalHasNonlinearSide(intLeT(xx, intLit(4))) {
		t.Error("x·x ≤ &4 must still count as having a nonlinear side (the enumeration gate)")
	}
	if intGoalHasNonlinearSide(intLeT(intMonoTerm(integerOf(2), x), intLit(4))) {
		t.Error("2·x ≤ &4 has no nonlinear side")
	}
}

// TestIntPolyBasisLinProve: the ℤ twins of the wave's ℝ leaves through the
// int forward prover, and the fragment boundary (a monomial's sign is not a
// row).
func TestIntPolyBasisLinProve(t *testing.T) {
	a, b, d, x, y := intVar("a"), intVar("b"), intVar("d"), intVar("x"), intVar("y")
	m := func(c int64, a Term) Term { return intMonoTerm(integerOf(c), a) }
	abd := intStarT(intStarT(a, b), d)
	aabb := intStarT(intStarT(intStarT(a, a), b), b)
	abab := intStarT(intStarT(a, b), intStarT(a, b))
	rows := []struct {
		name  string
		hyps  []Term
		goal  Term
		close bool
	}{
		{"halving over a product", []Term{intLeT(m(2, abd), m(2, aabb))}, intLeT(abd, aabb), true},
		{"both sides respelled: association, and the square as (ab)·(ab)",
			[]Term{intLeT(m(2, abd), m(2, aabb))}, intLeT(intStarT(a, intStarT(b, d)), abab), true},
		{"a genuinely different monomial", []Term{intLeT(m(2, abd), m(2, aabb))},
			intLeT(intStarT(a, intStarT(b, d)), intStarT(intStarT(a, b), intStarT(b, b))), false},
		{"scaling a product hypothesis", []Term{intLtT(intLit(0), intStarT(a, b))}, intLtT(intLit(0), m(2, intStarT(a, b))), true},
		{"a square hypothesis spelled x·x",
			[]Term{intLtT(intLit(0), y), intLeT(intLit(0), x), intLeT(intStarT(x, x), y),
				intLeT(m(2, x), intPlusT(intStarT(x, x), intLit(1)))},
			intLeT(x, intPlusT(y, intLit(1))), true},
		{"boundary: a factor of unknown sign", []Term{intLtT(intLit(0), a)}, intLtT(intLit(0), m(2, intStarT(a, b))), false},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			_, ok := IntLinProve(slices.Values(r.hyps), r.goal)
			if ok != r.close {
				t.Errorf("IntLinProve closed=%v, want %v", ok, r.close)
			}
		})
	}
	_ = prop.T
}
