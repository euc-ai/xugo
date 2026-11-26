package omega

// The ring normal form as a rewrite (ring_nf.go): the pretty spelling, the
// fixpoint on a term already in it, every arithmetic subterm reached, and
// the policy gate.

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// nb parses a num term of the test DSL.
func nb(s string) Term { return tParse(s, dsl.NumType) }

// allCarriers is the policy of a proof outside every foundation: the
// unscoped policy reads the corpus's foundation closures, which the test
// bundles do not install.
var allCarriers = ArithPolicy{Nat: true, Real: true, Int: true}

func TestRingNf_PrettyForms(t *testing.T) {
	installTestBundle(t)
	rw := RingNormalizeRewriteWithPolicy(allCarriers)
	rows := []struct {
		name string
		in   Term
		want Term
	}{
		{"a sum is sorted and merged", nb("b + a + a"), nb("2 * a + b")},
		{"a product distributes", nb("(a + b) * (a + b)"), nb("a * a + 2 * (a * b) + b * b")},
		{"a constant comes last", nb("3 + a + 1"), nb("a + 4")},
		{"a unit coefficient and a zero constant are elided", nb("1 * a + 0"), nb("a")},
		{"real: the same spelling", rr("(x + y) * &2"), rr("&2 * x + &2 * y")},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			w := rw(r.in)
			if w == nil {
				t.Fatalf("ring_nf declined %v", r.in)
			}
			if !prop.Rhs(w).AlphaEquals(r.want) {
				t.Errorf("ring_nf(%v) = %v, want %v", r.in, prop.Rhs(w), r.want)
			}
			if !prop.Lhs(w).AlphaEquals(r.in) {
				t.Errorf("the rewrite proves about %v", prop.Lhs(w))
			}
			if rw(prop.Rhs(w)) != nil {
				t.Errorf("the normal form %v is not a fixpoint", prop.Rhs(w))
			}
		})
	}
}

// TestRingNf_ReachesSubterms: the rewrite is deep — a polynomial under a
// comparison, under a function and under a binder is normalized where it
// stands — and leaves a term already in normal form alone.
func TestRingNf_ReachesSubterms(t *testing.T) {
	installTestBundle(t)
	rw := RingNormalizeRewriteWithPolicy(allCarriers)
	w := rw(tb("(b + a) * 2 <= c ∧ c <= a + a"))
	if w == nil {
		t.Fatal("ring_nf declined a conjunction of comparisons with polynomial sides")
	}
	if !prop.Rhs(w).AlphaEquals(tb("2 * a + 2 * b <= c ∧ c <= 2 * a")) {
		t.Errorf("got %v", prop.Rhs(w))
	}
	if rw(tb("2 * a + b <= c")) != nil {
		t.Error("a comparison already in normal form must be left alone")
	}
	under := ext.ForAll(numVar("k"))(tb("k + k <= c"))
	if w := rw(under); w == nil || !prop.Rhs(w).AlphaEquals(ext.ForAll(numVar("k"))(tb("2 * k <= c"))) {
		t.Errorf("under a binder: got %v", func() any {
			if w == nil {
				return nil
			}
			return prop.Rhs(w)
		}())
	}
}

// TestRingNf_PolicyGate: a carrier the policy withholds is left as written.
func TestRingNf_PolicyGate(t *testing.T) {
	installTestBundle(t)
	noNat := ArithPolicy{Nat: false, Real: true, Int: true}
	if RingNormalizeRewriteWithPolicy(noNat)(nb("b + a + a")) != nil {
		t.Error("the num carrier must stay as written under a policy that withholds it")
	}
	if RingNormalizeRewriteWithPolicy(noNat)(rr("(x + y) * &2")) == nil {
		t.Error("the real carrier, which the policy allows, must still be rewritten")
	}
}
