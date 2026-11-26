package dsl

import (
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
)

// The three-part set-builder `{t | x̄ | φ}` with an output that is no
// bare binder: the comprehension's point takes its type from the
// output, built after it (buildArgsAgainstFunType's ordering), whether
// the binders are typed by annotation or by φ — a binder's bare use at
// `∈` is built after the set it is a member of (buildSetOperands).
func TestGeneralSetBuilder_OutputTypesThePoint(t *testing.T) {
	scope := absOutfixTestScope(t)
	same := func(sugar, plain string) {
		t.Helper()
		a, b := parseImplicit(t, scope, sugar), parseImplicit(t, scope, plain)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", sugar, plain, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	same("{ x + x | x | x ∈ s } = s",
		"set_comprehension(λv:real. ∃x:real. comprehension_spec(v, x ∈ s, x + x)) = s")
	same("{ x + x | x:real | x ∈ s } = s",
		"set_comprehension(λv:real. ∃x:real. comprehension_spec(v, x ∈ s, x + x)) = s")
	same("{ zz_abs(x) | x:real | x ∈ s } = s",
		"set_comprehension(λv:real. ∃x:real. comprehension_spec(v, x ∈ s, zz_rabs(x))) = s")
	same("{ |x| | x | x ∈ s } = s",
		"set_comprehension(λv:real. ∃x:real. comprehension_spec(v, x ∈ s, zz_rabs(x))) = s")
	same("{ x + y | x, y | x ∈ s ∧ y ∈ s } = s",
		"set_comprehension(λv:real. ∃x:real. ∃y:real. comprehension_spec(v, x ∈ s ∧ y ∈ s, x + y)) = s")
	// Binders typed by φ alone, two of them, and the word or the bars
	// as the output.
	same("{ w + v | w, v | w ∈ s ∧ v ∈ s } = s",
		"set_comprehension(λu:real. ∃w:real. ∃v:real. comprehension_spec(u, w ∈ s ∧ v ∈ s, w + v)) = s")
	same("{ zz_abs(w) | w | w ∈ s } = s",
		"set_comprehension(λv:real. ∃w:real. comprehension_spec(v, w ∈ s, zz_rabs(w))) = s")
	same("{ |w| | w | w ∈ s } = s",
		"set_comprehension(λv:real. ∃w:real. comprehension_spec(v, w ∈ s, zz_rabs(w))) = s")
	// A binder named like no declared variable, and one named like the
	// declared x — the binder shadows it.
	same("{ w + w | w | w ∈ s } = s",
		"set_comprehension(λv:real. ∃w:real. comprehension_spec(v, w ∈ s, w + w)) = s")
	same("{ x + x | x | x ∈ s } = {w + w | w | w ∈ s}",
		"set_comprehension(λv:real. ∃w:real. comprehension_spec(v, w ∈ s, w + w)) = set_comprehension(λv:real. ∃w:real. comprehension_spec(v, w ∈ s, w + w))")
	// The identity form, its binder typed by `∈` alone.
	same("{x | x ∈ s} = s", "set_comprehension(λv:real. ∃x:real. comprehension_spec(v, x ∈ s, x)) = s")
	same("{w | w ∈ s} = s", "set_comprehension(λv:real. ∃w:real. comprehension_spec(v, w ∈ s, w)) = s")
	same("|x| ∈ {w | w ∈ s ∧ |w| < &1}", "zz_rabs(x) ∈ {w | w ∈ s ∧ zz_rabs(w) < &1}")
}
