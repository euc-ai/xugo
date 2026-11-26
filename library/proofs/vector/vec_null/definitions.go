package vec_null

import (
	_ "github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/registry"
)

// NullSetDef — arbitrarily small countable cube covers of a set of
// n-vectors, with only the empty set null in dimension zero.
var NullSetDef = nullSetDefThm{family.Define(registry.DefEntry{
	Name:  "NullSetDef",
	Key:   "prop_eca050cefd618d9e",
	Const: "vec_null_set",
	Type:  "num → set(num → real) → bool",
	Dim:   "n",
	Equations: []string{
		"∀n:num. ∀S:set(num → real). " +
			"    vec_null_set⟨n⟩(S) ⇔ " +
			"    (n = 0 ∧ S = ∅) ∨ " +
			"    (0 < n ∧ " +
			"        S ⊆ {x:num → real | vec⟨n⟩(x)} ∧ " +
			"        ∀ε:real. " +
			"            &0 < ε ⇒ " +
			"            ∃c:(num → num → real). ∃r:(num → real). ∃s:real. " +
			"                (∀j:num. vec⟨n⟩(c(j)) ∧ &0 ≤ r(j)) ∧ " +
			"                (∀x:(num → real). x ∈ S ⇒ ∃j:num. ∀i:num. i < n ⇒ |x(i) - c(j)(i)| < r(j)) ∧ " +
			"                real_sums(λj:num. (&2 * r(j)) ^ n, s) ∧ " +
			"                s < ε)",
	},
	Reading: "A null set lies in the zero-padded n-vector carrier. In positive dimension a " +
		"radius-zero cube is empty and has volume zero, so finite and empty covers can be padded " +
		"to sequences; the separate n = 0 clause avoids 0^0 and makes exactly the empty set null.",
})}
