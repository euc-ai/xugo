package omega

// The monomial sign rows over ℤ (int_sign_rows.go) — the twin of
// real_sign_rows_test.go. Over ℤ a product atom is an unknown with no sign, so
// the refutation needs a row saying `&0 ≤ a·b`: from the factors' stated signs,
// unconditionally when the monomial is a square, or because the atom is an `&n`
// coercion.

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

func intDecides(t *testing.T, hyps []Term, goal Term) bool {
	t.Helper()
	w := IntArithDecideWithHyps(hyps)(goal)
	return w != nil && prop.Rhs(w).Equals(prop.T)
}

func TestIntSignRows_FromFactorSigns(t *testing.T) {
	installTestBundle(t)
	a, b, c, d := intVar("a"), intVar("b"), intVar("c"), intVar("d")
	z := intLit(0)
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"two positive factors",
			[]Term{intLtT(z, a), intLtT(z, b), intLeT(intStarT(a, b), c)}, intLtT(z, c)},
		{"three positive factors",
			[]Term{intLtT(z, a), intLtT(z, b), intLtT(z, c), intLeT(intStarT(intStarT(a, b), c), d)}, intLtT(z, d)},
		{"two nonneg factors",
			[]Term{intLeT(z, a), intLeT(z, b), intLeT(intStarT(a, b), c)}, intLeT(z, c)},
		{"mixed signs make the product nonpositive",
			[]Term{intLeT(a, z), intLeT(z, b), intLtT(z, intPlusT(intStarT(a, b), c))}, intLtT(z, c)},
		{"two negative factors make it nonnegative",
			[]Term{intLeT(a, z), intLeT(b, z), intLeT(intStarT(a, b), c)}, intLeT(z, c)},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if !intDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
}

func TestIntSignRows_SquareAndCoercion(t *testing.T) {
	installTestBundle(t)
	n := ext.Var(ext.TermName("n"), dsl.NumType)
	a, b, x, y, z0 := intVar("a"), intVar("b"), intVar("x"), intVar("y"), intVar("z")
	z := intLit(0)
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"a bare square", []Term{intLeT(intStarT(x, x), y)}, intLeT(z, y)},
		{"a square in an equation", []Term{eqT(intPlusT(intStarT(x, x), intStarT(y, y)), z)}, eqT(intStarT(x, x), z)},
		{"a regrouped even monomial",
			[]Term{intLeT(intStarT(intStarT(a, a), intStarT(b, b)), z0)}, intLeT(z, z0)},
		{"a square written with a subtraction",
			[]Term{intLeT(intStarT(intSubT(a, b), intSubT(a, b)), z0)}, intLeT(z, z0)},
		{"an `&n` coercion is nonnegative", []Term{intLeT(intOfNumT(n), x)}, intLeT(z, x)},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if !intDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
}

// TestIntSignRows_Declines pins the boundary, the same one the ℝ pass keeps.
func TestIntSignRows_Declines(t *testing.T) {
	installTestBundle(t)
	a, b, c, x, y := intVar("a"), intVar("b"), intVar("c"), intVar("x"), intVar("y")
	z := intLit(0)
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"no factor sign is stated", []Term{intLeT(intStarT(a, b), c)}, intLtT(z, c)},
		{"only one factor is signed", []Term{intLtT(z, a), intLeT(intStarT(a, b), c)}, intLtT(z, c)},
		{"nonneg factors give no strict bound",
			[]Term{intLeT(z, a), intLeT(z, b), intLeT(intStarT(a, b), c)}, intLtT(z, c)},
		{"an odd monomial is not a square",
			[]Term{intLeT(intStarT(intStarT(x, x), x), y)}, intLeT(z, y)},
	}
	// The converse direction — a factor's sign off the monomial's — is
	// not a sign row; it closes through the products pass instead
	// (int_products.go, TestIntProducts_NlinarithShapes).
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if intDecides(t, r.hyps, r.goal) {
				t.Errorf("closed %v under %v — the pass must decline this", r.goal, r.hyps)
			}
		})
	}
}

// TestIntSignRows_MixedStrictnessFolds: `&0 < a` beside `&0 ≤ b` prices a·b
// non-strictly, the strict fact weakened first. The ℝ twin carries the same
// row.
func TestIntSignRows_MixedStrictnessFolds(t *testing.T) {
	installTestBundle(t)
	a, b, c := intVar("a"), intVar("b"), intVar("c")
	z := intLit(0)
	hyps := []Term{intLtT(z, a), intLeT(z, b), intLeT(intStarT(a, b), c)}
	cs := intDomain.hypConstraints(slices.Values(hyps))
	var saw bool
	for _, row := range intMonomialSignConstraints(cs) {
		if isIntZero(row.Lhs) && row.Op == opLE && row.Rhs.AlphaEquals(intStarT(a, b)) {
			saw = true
		}
	}
	if !saw {
		t.Error("no non-strict sign row for a·b")
	}
	if !intDecides(t, hyps, intLeT(z, c)) {
		t.Error("mixed strictness must close")
	}
}

// TestIntSignRows_HypSubset is the provenance contract: the sign facts are
// projected out of ONE conjunctive hypothesis, so a derived row's proof must
// carry that conjunction and not the conjuncts.
func TestIntSignRows_HypSubset(t *testing.T) {
	installTestBundle(t)
	a, b, c := intVar("a"), intVar("b"), intVar("c")
	z := intLit(0)
	conj := ext.Apply(prop.AND, intLtT(z, a), intLtT(z, b))
	bound := intLeT(intStarT(a, b), c)
	goal := intLtT(z, c)
	w, ok := IntLinProve(slices.Values([]Term{conj, bound}), goal)
	if !ok {
		t.Fatal("IntLinProve declined the conjunctive spelling")
	}
	for h := range w.HypIter() {
		if !h.AlphaEquals(conj) && !h.AlphaEquals(bound) {
			t.Errorf("stray hypothesis %v — a projected conjunct escaped as its own hypothesis", h)
		}
	}
}

// TestIntSignRows_LinearGoalsUntouched: the pass costs one linOf sweep and
// returns nothing when no sign-bearing atom is present.
func TestIntSignRows_LinearGoalsUntouched(t *testing.T) {
	installTestBundle(t)
	a, b := intVar("a"), intVar("b")
	cs := intDomain.hypConstraints(slices.Values([]Term{intLtT(intLit(0), a), intLeT(a, b)}))
	if extra := intMonomialSignConstraints(cs); len(extra) != 0 {
		t.Errorf("a linear constraint set produced %d sign rows; want none", len(extra))
	}
}
