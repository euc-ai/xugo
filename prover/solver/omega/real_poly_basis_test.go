package omega

// The monomial-basis extraction over ℝ (domain.go polyMul, wired to
// realRing.polyMul in real_lemmas.go): the ℝ linear layer reads a product of
// atoms as one monomial unknown, exactly as num does, so a hypothesis
// carrying a product combines with the goal under Farkas and an ordering
// leaf whose reasoning is linear over a product closes without the product
// being named first. Over ℝ this is a pure change of basis — realBuildAll
// injects no sign rows — so the fragment gains nothing about a monomial's
// SIGN: `&0 < a·b` still comes only from the sign-known handlers.
//
// The rows in TestRealPolyBasisWaveLeaves are the leaves the vector /
// real_sqrt chapters met failing under `by {arith:true}`, verbatim;
// the last row pins the boundary.

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// pb parses a real comparison whose text may mention real_pow (its exponent
// is a nat numeral); every other identifier is a real variable.
func pb(s string) Term {
	scope := realScope(s)
	delete(scope, "real_pow")
	r := dsl.ParseTermTextInScope(s, scope,
		&dsl.ParseScope{Consts: map[string]core.ConstTerm{"real_pow": dsl.RealPowMeta.Term()}}, core.TypeBool())
	if len(r.Errors) > 0 {
		panic(fmt.Sprintf("dsl parse %q: %v", s, r.Errors))
	}
	return r.Term
}

// TestRealPolyBasisCanonicalForms pins linOf's expansion over ℝ against
// hand-computed canonical forms via the buildTerm rendering.
func TestRealPolyBasisCanonicalForms(t *testing.T) {
	cases := []struct{ in, canon string }{
		{"a * b", "b * a"},
		{"(a * b) * c", "a * (b * c)"},
		{"(a + &1) * (b + &2)", "a * b + &2 * a + b + &2"},
		{"(a + b) * (a + b)", "a * a + &2 * (a * b) + b * b"},
		{"&2 * (a * b) + &3 * (b * a)", "&5 * (a * b)"},
		{"(&2 * a) * (&3 * b)", "&6 * (a * b)"},
	}
	for _, tc := range cases {
		lfIn, ok1 := realDomain.linOf(rr(tc.in))
		lfCanon, ok2 := realDomain.linOf(rr(tc.canon))
		if !ok1 || !ok2 {
			t.Errorf("linOf declined %q or %q", tc.in, tc.canon)
			continue
		}
		if !realDomain.buildTerm(lfIn).AlphaEquals(realDomain.buildTerm(lfCanon)) {
			t.Errorf("linOf(%q) = %v; want the form of %q = %v",
				tc.in, realDomain.buildTerm(lfIn), tc.canon, realDomain.buildTerm(lfCanon))
		}
	}
}

// TestRealPolyBasisRoundTrip: the rendering of an extracted form re-extracts
// to the same form (the canonicality invariant).
func TestRealPolyBasisRoundTrip(t *testing.T) {
	for _, s := range []string{"a * b", "(a + b) * (c + &1)", "&2 * (a * b) + &3 * c + &7"} {
		lf, ok := realDomain.linOf(rr(s))
		if !ok {
			t.Fatalf("linOf declined %q", s)
		}
		lf2, ok := realDomain.linOf(realDomain.buildTerm(lf))
		if !ok || !realDomain.buildTerm(lf).AlphaEquals(realDomain.buildTerm(lf2)) {
			t.Errorf("round trip moved %q: %v → %v", s, realDomain.buildTerm(lf), realDomain.buildTerm(lf2))
		}
	}
}

// TestRealPolyBasisNormalizeProofLockstep: the proof side (realRing.
// normalizeProof) produces the model's exact form on polynomial terms — the
// replay's cancel step depends on the two coinciding.
func TestRealPolyBasisNormalizeProofLockstep(t *testing.T) {
	for _, s := range []string{
		"a * b", "b * a", "(a + &1) * (b + &2)", "(a + b) * (a + b)", "(a * b) * c",
		"&2 * (a * b) + &3 * (b * a)", "(&2 * a) * (&3 * b)",
	} {
		checkRealNormalize(t, rr(s))
	}
}

// TestRealPolyBasisWideCoefficients: a coefficient past the int64 range
// expands exactly on both sides.
func TestRealPolyBasisWideCoefficients(t *testing.T) {
	product := rr("(&4000000000 * a) * (&4000000000 * b)")
	lf, ok := realDomain.linOf(product)
	if !ok || len(lf.monos) != 1 || !lf.monos[0].coeff.equal(integerOfUint(16000000000000000000)) {
		t.Errorf("wide-coefficient product = %+v ok=%v; want 16000000000000000000·(a·b)", lf, ok)
	}
	checkRealNormalize(t, product)
}

// TestRealPolyBasisWaveLeaves: the wave's ordering leaves through the ℝ
// decider (hyps ⊢ goal rewrites to ⊤), and the fragment boundary.
func TestRealPolyBasisWaveLeaves(t *testing.T) {
	rows := []struct {
		name  string
		hyps  []string
		goal  string
		close bool
	}{
		{"halving over a product (CauchySchwarz)",
			[]string{"&2 * ((a * b) * d) <= &2 * (((a * a) * b) * b)"}, "(a * b) * d <= ((a * a) * b) * b", true},
		{"a nonneg difference read as an ordering (CauchySchwarz)",
			[]string{"&0 <= (b * ((b * (a * a)) - (a * d))) - (a * ((b * d) - (a * (b * b))))"},
			"&2 * ((a * b) * d) <= &2 * ((a * b) * (a * b))", true},
		{"scaling a product hypothesis",
			[]string{"&0 < a * b"}, "&0 < &2 * (a * b)", true},
		{"a square hypothesis spelled x * x (SquareRootExists)",
			[]string{"&0 < y", "&0 <= x", "x * x <= y", "&2 * x <= x * x + &1"}, "x <= y + &1", true},
		{"the same with the pow atom",
			[]string{"&0 < y", "&0 <= x", "real_pow(x, 2) <= y", "&2 * x <= real_pow(x, 2) + &1"}, "x <= y + &1", true},
		{"linear over a cross term (ApproachFromAbove)",
			[]string{"&2 * (w * x) <= q - y", "p = (q - &2 * (w * x)) + s", "&0 < s"}, "y < p", true},
		{"an equation with a product, under a hypothesis",
			[]string{"x * y = z"}, "y * x + &0 = z", true},
		// A monomial's sign is not a row: `&0 < &2·(a·b)` from the factors'
		// signs is the sign-of-product handler's (realProveFactorSign
		// descending the product tree), not the linear layer's.
		{"the sign of a scaled product from its factors",
			[]string{"&0 < a", "&0 < b"}, "&0 < &2 * (a * b)", true},
		// Boundary: a sign fact the hypotheses do not carry.
		{"boundary: a factor of unknown sign",
			[]string{"&0 < a"}, "&0 < &2 * (a * b)", false},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			var hyps []Term
			for _, h := range r.hyps {
				hyps = append(hyps, pb(h))
			}
			w := RealArithDecideWithHyps(hyps)(pb(r.goal))
			closed := w != nil && prop.Rhs(w).Equals(prop.T)
			if closed != r.close {
				t.Errorf("%s: closed=%v, want %v (rewrite %v)", r.name, closed, r.close, w)
			}
		})
	}
}
