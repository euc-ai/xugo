// localization_primes.go — extension and contraction of prime ideals in a localization.

package ring_localization

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/registry"
)

// LocalizationPrimeCorrespondence — Extend p by fractions with numerator in p.
var LocalizationPrimeCorrespondence = localizationPrimeCorrespondenceThm{family.Add(registry.ProofEntry{
	Name: "LocalizationPrimeCorrespondence",
	Key:  "prop_22fe644c2cb6dd6",
	Deps: []registry.EntryLike{
		FractionClassEq,
		FractionAddClass,
		FractionMulClass,
		FractionNegClass,
		LocalizationRing,
		ToFractionDef,
		ring_ideal.PrimeIdealDef,
	},
	Build: family.Card(Statement{
		Binders: "∀c:comm_ring_on(A). ∀s p:set(A).",
		Hypotheses: []string{
			"multiplicative_set(c.carrier, s)",
			"prime_ideal(c, p)",
			"p ∩ s = ∅",
		},
		Conclusion: "prime_ideal(localized_ring(c, s), " +
			"    {X:set(prod(A, A)) | ∃a u:A. a ∈ p ∧ u ∈ s ∧ X = fraction_class(c.carrier, s, a, u)}) ∧ " +
			"{a:A | " +
			"    a ∈ c.carrier ∧ " +
			"    to_fraction(c.carrier, s, a) ∈ " +
			"    {X:set(prod(A, A)) | ∃a u:A. a ∈ p ∧ u ∈ s ∧ X = fraction_class(c.carrier, s, a, u)}} = " +
			"p",
	},
		"Extend p by fractions with numerator in p. FractionClassEq and disjointness "+
			"from s make numerator membership independent of representatives; the class "+
			"laws give an ideal and primality. Contracting along a ↦ a/one returns p."),
})}

// LocalizationPrimeCorrespondenceInverse — Contract Q along ToFractionHomomorphism; the ring laws make the contraction prime.
var LocalizationPrimeCorrespondenceInverse = localizationPrimeCorrespondenceInverseThm{family.Add(registry.ProofEntry{
	Name: "LocalizationPrimeCorrespondenceInverse",
	Key:  "prop_453d41dc786c1f4f",
	Deps: []registry.EntryLike{
		ToFractionHomomorphism,
		DenominatorUnit,
		FractionMulClass,
		FractionClassEq,
		ring_ideal.UnitNotInProperIdeal,
		ring_ideal.PrimeIdealDef,
	},
	Build: family.Card(Statement{
		Binders: "∀c:comm_ring_on(A). ∀s:set(A). ∀Q:set(set(prod(A, A))).",
		Hypotheses: []string{
			"multiplicative_set(c.carrier, s)",
			"prime_ideal(localized_ring(c, s), Q)",
		},
		Conclusion: "prime_ideal(c, preimage_on(c.carrier, to_fraction(c.carrier, s), Q)) ∧ " +
			"preimage_on(c.carrier, to_fraction(c.carrier, s), Q) ∩ s = ∅ ∧ " +
			"{X:set(prod(A, A)) | " +
			"    ∃a u:A. " +
			"        a ∈ preimage_on(c.carrier, to_fraction(c.carrier, s), Q) ∧ " +
			"        u ∈ s ∧ " +
			"        X = fraction_class(c.carrier, s, a, u)} = " +
			"Q",
	},
		"Contract Q along ToFractionHomomorphism; the ring laws make the contraction prime. "+
			"DenominatorUnit and properness make it disjoint from s. Multiplication by a denominator "+
			"unit shows that a/u belongs to Q exactly when a/one does, proving the extension equation."),
})}
