package finite_field

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// FiniteFieldDef — `finite_field(F)`: F is a field on a finite carrier.
var FiniteFieldDef = finiteFieldDefThm{family.Define(registry.DefEntry{
	Name:      "FiniteFieldDef",
	Key:       "prop_23f5c9870a966c35",
	Const:     "finite_field",
	Type:      "field_ops(A) → bool",
	Equations: []string{"∀F:field_ops(A). finite_field(F) ⇔ field_on(F) ∧ finite(F.carrier)"},
	Reading: "The carrier is a finite set; inverse and division are quantified operations " +
		"on the ambient type. No condition is imposed on their values outside the carrier.",
})}

// FieldSizeDef — `field_size(F)`: the number of elements of F's carrier.
var FieldSizeDef = fieldSizeDefThm{family.Define(registry.DefEntry{
	Name:      "FieldSizeDef",
	Key:       "prop_2456ef530c269bd6",
	Const:     "field_size",
	Type:      "field_ops(A) → num",
	Equations: []string{"∀F:field_ops(A). field_size(F) = card(F.carrier)"},
})}

// PrimeCharacteristicDef — `ring_prime_characteristic(R, p)`: p is a prime
// and the p-fold sum of one is zero in R.
var PrimeCharacteristicDef = primeCharacteristicDefThm{family.Define(registry.DefEntry{
	Name:  "PrimeCharacteristicDef",
	Key:   "prop_7410608b714714b8",
	Const: "ring_prime_characteristic",
	Type:  "ring_ops(A) → num → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀p:num. " +
			"    ring_prime_characteristic(R, p) ⇔ nat_prime(p) ∧ monoid_pow(R.add, R.zero, R.one, p) = R.zero",
	},
	Reading: "This predicate asserts a prime annihilator of one. For a nonzero " +
		"ring it is its characteristic; the zero ring satisfies it at every prime.",
})}

// FieldCharacteristicDef — characteristic zero or prime characteristic p; field axioms are stated
// separately.
var FieldCharacteristicDef = fieldCharacteristicDefThm{family.Define(registry.DefEntry{
	Name: "FieldCharacteristicDef", Const: "field_characteristic", Type: "field_ops(A) → num → bool",
	Key: "prop_932483db0acd3fa4",
	Equations: []string{
		"∀F:field_ops(A). ∀p:num. " +
			"    field_characteristic(F, p) ⇔ " +
			"    (p = 0 ∧ characteristic_zero(field_ring(F))) ∨ " +
			"    (0 < p ∧ ring_prime_characteristic(field_ring(F), p))",
	},
	Deps: []registry.EntryLike{PrimeCharacteristicDef},
})}

// SameCharacteristicDef — the integer maps of the two fields have the same kernel.
var SameCharacteristicDef = sameCharacteristicDefThm{family.Define(registry.DefEntry{
	Name:  "SameCharacteristicDef",
	Const: "same_characteristic",
	Type:  "field_ops(A) → field_ops(B) → bool",
	Key:   "prop_994543d05f4c420f",
	Equations: []string{
		"∀F:field_ops(A). ∀G:field_ops(B). " +
			"    same_characteristic(F, G) ⇔ " +
			"    ∀z:int. (integer_map(field_ring(F), z) = F.zero ⇔ integer_map(field_ring(G), z) = G.zero)",
	},
})}

// FrobeniusPowerDef — `frobenius_power(R, Q, z)`: z raised to the Q-th power
// in R.
var FrobeniusPowerDef = frobeniusPowerDefThm{family.Define(registry.DefEntry{
	Name:  "FrobeniusPowerDef",
	Key:   "prop_df7b3e6c08c4e51b",
	Const: "frobenius_power",
	Type:  "ring_ops(A) → num → A → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀Q:num. ∀z:A. frobenius_power(R, Q, z) = monoid_pow(R.mul, R.one, z, Q)",
	},
	Reading: "The exponent Q is a natural term, not required to be a prime power " +
		"in the definition. Ring and characteristic hypotheses belong to the laws.",
})}

// FiniteConstantsDef — `finite_constants(R, q, m)`: the members of the
// carrier fixed by the q^m-th power map.
var FiniteConstantsDef = finiteConstantsDefThm{family.Define(registry.DefEntry{
	Name:  "FiniteConstantsDef",
	Key:   "prop_caadb3f1ee9a04df",
	Const: "finite_constants",
	Type:  "ring_ops(A) → num → num → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀q m:num. " +
			"    finite_constants(R, q, m) = {x:A | x ∈ R.carrier ∧ monoid_pow(R.mul, R.one, x, q ^ m) = x}",
	},
	Reading: "At m = 0, or at q = 1, the power is the first and the set is the whole " +
		"carrier; inside an algebraically closed field, for q the size of a finite " +
		"subfield and m > 0, it is the subfield with q^m elements (FiniteConstantsSubfield).",
})}

// LocallyFiniteFieldDef — `locally_finite_field(F)`: F is a field in which
// every finite set of elements lies in a finite subfield.
var LocallyFiniteFieldDef = locallyFiniteFieldDefThm{family.Define(registry.DefEntry{
	Name:  "LocallyFiniteFieldDef",
	Key:   "prop_941b68b604237619",
	Const: "locally_finite_field",
	Type:  "field_ops(A) → bool",
	Equations: []string{
		"∀F:field_ops(A). " +
			"    locally_finite_field(F) ⇔ " +
			"    field_on(F) ∧ " +
			"    (∀S:set(A). finite(S) ∧ S ⊆ F.carrier ⇒ ∃K:set(A). subfield(F, K) ∧ finite(K) ∧ S ⊆ K)",
	},
})}
