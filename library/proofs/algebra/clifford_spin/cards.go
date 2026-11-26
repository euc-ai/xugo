package clifford_spin

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/exterior_basis"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/words/word_bits"
	"github.com/euc-ai/xugo/library/registry"
)

// CliffordSignCocycle — The sign of the binary-basis product is a cocycle on finite sets of generators.
var CliffordSignCocycle = cliffordSignCocycleThm{family.Add(registry.ProofEntry{
	Name: "CliffordSignCocycle",
	Key:  "prop_b17c8afb0c7b1b28",
	Deps: []registry.EntryLike{cardinality.CardUnionMinusOverlap, cardinality.CardDiff},
	Build: family.Card(Statement{
		Binders:    "∀X Y Z:set(num).",
		Hypotheses: []string{"finite(X)", "finite(Y)", "finite(Z)"},
		Conclusion: "real_pow(-&1, «exponent»(X, Y) + «exponent»(«Δ»(X, Y), Z)) = " +
			"real_pow(-&1, «exponent»(X, «Δ»(Y, Z)) + «exponent»(Y, Z))",
		Abbrev: Abbrev{
			{Name: "Δ", Text: "λU:set(num). λV:set(num). {i:num | ¬(i ∈ U ⇔ i ∈ V)}"},
			{Name: "exponent", Text: "λU:set(num). λV:set(num). " +
				"    card({p:prod(num, num) | fst(p) ∈ U ∧ snd(p) ∈ V ∧ snd(p) < fst(p)}) + card(U ∩ V)"},
		},
	},
		"The exponent is additive mod 2 in each argument: the crossed pairs of X Δ Y against Z are "+
			"the symmetric difference of those of X and of Y, the overlaps likewise, and card(S Δ T) "+
			"has the parity of card(S) + card(T) for finite S and T (CardUnionMinusOverlap, and "+
			"CardDiff on (S ∪ T) ∖ (S ∩ T)). Both exponents are then e(X, Y) + e(X, Z) + e(Y, Z) mod 2."),
	Reading: "The exponent is the one clifford_product spells, the crossed pairs and the repeated " +
		"generators of two masks. Finiteness is load-bearing: the parity count reads card on each set.",
})}

var CliffordAssociative = cliffordAssociativeThm{family.Add(registry.ProofEntry{
	Name: "CliffordAssociative",
	Key:  "prop_4d0339c68dd168a4",
	Deps: []registry.EntryLike{
		CliffordSignCocycle,
		exterior_basis.MaskWordBits,
		word_bits.BitsEqBounded,
		word_bits.BitXor,
		word_bits.BitwiseBinaryBound,
		word_bits.ClearBitsBound,
		real_sum.Swap,
		real_sum.Delta,
	},
	Build: family.Card(
		"∀n:num. ∀a b c:(num → real). "+
			"    clifford_product(n, clifford_product(n, a, b), c) = "+
			"    clifford_product(n, a, clifford_product(n, b, c))",
		"Distribute the finite sums. For a and b below 2^n the one index below 2^n whose mask is the "+
			"symmetric difference of theirs is word_xor(a, b): its bits are the places below n where "+
			"exactly one of a, b has one (MaskWordBits, BitXor), it lies below 2^n (BitwiseBinaryBound, "+
			"ClearBitsBound), and it is the only such index (BitsEqBounded). So Delta collapses the inner "+
			"sum on each side; CliffordSignCocycle then compares the signs for each triple of basis masks."),
})}

var CliffordRelation = cliffordRelationThm{family.Add(registry.ProofEntry{
	Name: "CliffordRelation",
	Key:  "prop_ab04d80fa5d3c933",
	Deps: []registry.EntryLike{
		exterior_basis.MaskWordBits,
		word_bits.BitPowTwo,
		word_bits.BitsEqBounded,
		real_sum.Swap,
		real_sum.Delta,
	},
	Build: family.Card(
		"∀n:num. ∀u v:(num → real). ∀a:num. "+
			"    clifford_product(n, clifford_vector(n, u), clifford_vector(n, v), a) + "+
			"    clifford_product(n, clifford_vector(n, v), clifford_vector(n, u), a) = "+
			"    COND(a = 0, -&2 * real_sum({i:num | i < n}, λi:num. u(i) * v(i)), &0)",
		"A vector lives on the indices whose mask has one element, the numbers 2^i for "+
			"i < n (MaskWordBits, BitPowTwo, BitsEqBounded). At 2^i and 2^j the crossed "+
			"pair counts one exactly when j < i and the overlap one exactly when i = j: "+
			"distinct generators anticommute and a repeated generator squares to minus one."),
})}

var SpinGroup = spinGroupThm{family.Add(registry.ProofEntry{
	Name: "SpinGroup",
	Key:  "prop_f37d79d9ce4eae0d",
	Deps: []registry.EntryLike{CliffordAssociative, CliffordRelation},
	Build: family.Card("∀n:num. group_on(spin_group(n))",
		"An even word is closed under multiplication; reversing its unit "+
			"vectors and changing their signs gives its Clifford conjugate inverse."),
})}

var SpinOrthogonal = spinOrthogonalThm{family.Add(registry.ProofEntry{
	Name: "SpinOrthogonal",
	Key:  "prop_3e2c23a8d45b7fe7",
	Deps: []registry.EntryLike{CliffordRelation},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀a:(num → real).",
		Hypotheses: []string{"spin_element(n, a)"},
		Conclusion: "determinant(real_ring, n, spin_vector_action(n, a)) = &1 ∧ " +
			"(∀i j:num. " +
			"    i < n ∧ j < n ⇒ " +
			"    real_sum({k:num | k < n}, " +
			"        λk:num. spin_vector_action(n, a, k, i) * spin_vector_action(n, a, k, j)) = " +
			"    COND(i = j, &1, &0))",
	},
		"Conjugation by a unit vector induces a signed reflection. "+
			"An even product acts orthogonally with determinant one."),
})}

var SpinCover = spinCoverThm{family.Add(registry.ProofEntry{
	Name: "SpinCover",
	Key:  "prop_5d3f925b4611688d",
	Deps: []registry.EntryLike{SpinOrthogonal},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀O:(num → num → real).",
		Hypotheses: []string{
			"determinant(real_ring, n, O) = &1",
			"∀i j:num. O(i, j) = COND(i < n ∧ j < n, O(i, j), &0)",
			"∀i j:num. " +
				"    i < n ∧ j < n ⇒ real_sum({k:num | k < n}, λk:num. O(k, i) * O(k, j)) = COND(i = j, &1, &0)",
		},
		Conclusion: "∃a:(num → real). spin_element(n, a) ∧ spin_vector_action(n, a) = O",
	},
		"Express an orientation-preserving orthogonal map as an even product of "+
			"reflections, and lift the reflecting unit vectors to the Clifford algebra."),
})}

var RepresentationProduct = representationProductThm{family.Add(registry.ProofEntry{
	Name: "RepresentationProduct",
	Key:  "prop_71f68825b1cfd34d",
	Deps: []registry.EntryLike{CliffordRelation},
	Build: family.Card(
		"∀m:num. ∀a b:(num → real). "+
			"    spinor_representation(m, clifford_product(2 * m, a, b)) = "+
			"    matrix_mul(complex_add, "+
			"        complex_mul, "+
			"        nat_pow(2, m), "+
			"        spinor_representation(m, a), "+
			"        spinor_representation(m, b))",
		"Wedge and contraction satisfy the negative Clifford relations. The ordered blade "+
			"matrices therefore carry the binary-basis multiplication to matrix multiplication."),
})}

var SpinRepresentationUnitary = spinRepresentationUnitaryThm{family.Add(registry.ProofEntry{
	Name: "SpinRepresentationUnitary",
	Key:  "prop_7802b4cab3c6a8b",
	Deps: []registry.EntryLike{RepresentationProduct},
	Build: family.Card(Statement{
		Binders:    "∀m:num. ∀a:(num → real). ∀i j:num.",
		Hypotheses: []string{"spin_element(2 * m, a)", "i < nat_pow(2, m)", "j < nat_pow(2, m)"},
		Conclusion: "module_sum(complex_add, " +
			"    complex_of_real(&0), " +
			"    {k:num | k < nat_pow(2, m)}, " +
			"    λk:num. " +
			"        complex_conj(spinor_representation(m, a, k, i)) * spinor_representation(m, a, k, j)) = " +
			"COND(i = j, complex_of_real(&1), complex_of_real(&0)) ∧ " +
			"(nat_mod(card(exterior_mask(m, i)), 2) ≠ nat_mod(card(exterior_mask(m, j)), 2) ⇒ " +
			"    spinor_representation(m, a, i, j) = complex_of_real(&0))",
	},
		"Real unit vectors act by skew-Hermitian unitary Clifford "+
			"matrices. Even products are unitary and preserve exterior parity."),
})}
