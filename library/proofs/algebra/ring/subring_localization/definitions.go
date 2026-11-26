// definitions.go — the localization of a subring S of a field at a set p:
// the fractions a/b of S with b off p.

package subring_localization

import (
	"github.com/euc-ai/xugo/library/registry"
	// The chapter minting int_of_num and num_of_int, which the signed powers'
	// definition spells, initialized before it.
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
)

// SubringLocalizationDef — `subring_localization(L, S, p)`, written S_p:
// the members of L that are fractions a/b of members of S with b off p. For
// a prime p of S it is the localization of S at p, a subring of L.
var SubringLocalizationDef = subringLocalizationDefThm{family.Define(registry.DefEntry{
	Name:  "SubringLocalizationDef",
	Key:   "prop_d93c3ebd4655f9a5",
	Const: "subring_localization",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S p:set(A). " +
			"    subring_localization(R, S, p) = " +
			"    {f:A | f ∈ R.carrier ∧ (∃a b:A. a ∈ S ∧ b ∈ S ∧ b ∉ p ∧ R.mul(f, b) = a)}",
	},
})}
