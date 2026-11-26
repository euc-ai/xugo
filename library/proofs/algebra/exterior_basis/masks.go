// masks.go — the binary digits of a number below 2ʳ as a subset of
// {0, …, r − 1}: the mask read as the word bits below r, adding or
// removing one digit, the empty mask, the bijection with the subsets, the
// sign of passing a generator over the digits below it, and the k-th digit
// in increasing order.

package exterior_basis

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/words/bit_arith"
	"github.com/euc-ai/xugo/library/proofs/words/machine_word"
	"github.com/euc-ai/xugo/library/proofs/words/word_bits"
	"github.com/euc-ai/xugo/library/registry"
)

// MaskWordBits — the mask contains exactly the set bits of a at positions below r.
var MaskWordBits = maskWordBitsThm{family.Add(registry.ProofEntry{
	Name: "MaskWordBits",
	Key:  "prop_156cf2d13d29cc11",
	Build: family.Theorem("∀r a:num. exterior_mask(r, a) = {i:num | i < r ∧ word_bit(i, a)}",
		func(arg *Argument, r, a *Expr[Nat]) {
			arg.Do(
				Simp(Fwd(MaskDef), Fwd(machine_word.WordBitDef), Fwd(nat_parity.OddIffModTwoOne)),
				Basic(),
			)
		}),
	Reading: "Places at or above r are cut off on both sides, so " +
		"a ≥ 2^r is allowed: its mask is that of its remainder mod 2^r.",
})}

// MaskInsert — adding 2ⁱ to a number whose digit i is 0 inserts i into its
// mask.
var MaskInsert = maskInsertThm{family.Add(registry.ProofEntry{
	Name: "MaskInsert",
	Key:  "prop_e13adaf34339f10c",
	Reading: "i < r is load-bearing: for i ≥ r adding 2ⁱ leaves the digits below r " +
		"alone, and the mask does not gain i. So is i ∉ mask(r, a), for the carry. The " +
		"mask equation holds for every a, a ≥ 2ʳ included; only the bound reads a < 2ʳ.",
	Deps: []registry.EntryLike{
		MaskWordBits,
		bit_arith.AddAndOr,
		word_bits.BitOfAnd,
		word_bits.BitOfOr,
		word_bits.BitPowTwo,
	},
	Build: family.Card(Statement{
		Binders:    "∀r a i:num.",
		Hypotheses: []string{"i < r", "i ∉ exterior_mask(r, a)"},
		Conclusion: "exterior_mask(r, a + nat_pow(2, i)) = insert(i, exterior_mask(r, a)) ∧ " +
			"(a < nat_pow(2, r) ⇒ a + nat_pow(2, i) < nat_pow(2, r))",
	},
		"read the mask as the word bits below r (MaskWordBits). Bit i of a is 0, so "+
			"word_and(a, 2ⁱ) = 0 (word_bits.BitOfAnd, BitPowTwo) and a + 2ⁱ = word_or(a, 2ⁱ) "+
			"(bit_arith.AddAndOr), whose bits are those of a with bit i added (BitOfOr, "+
			"BitPowTwo). For the bound, a < 2ʳ with digit i equal to 0 is at most 2ʳ − 1 − 2ⁱ"),
})}

// MaskDelete — subtracting 2ⁱ from a number whose digit i is 1 removes i
// from its mask.
var MaskDelete = maskDeleteThm{family.Add(registry.ProofEntry{
	Name: "MaskDelete",
	Key:  "prop_4d8dc34c5b900422",
	Reading: "No bound on a is asked: i < r and 2ⁱ ≤ a both follow " +
		"from i being a digit of a below r, and the card holds for a ≥ 2ʳ.",
	Deps: []registry.EntryLike{
		MaskWordBits,
		bit_arith.OrAndXor,
		word_bits.BitOfXor,
		word_bits.BitOfAnd,
		word_bits.BitPowTwo,
	},
	Build: family.Card(Statement{
		Binders:    "∀r a i:num.",
		Hypotheses: []string{"i ∈ exterior_mask(r, a)"},
		Conclusion: "nat_pow(2, i) ≤ a ∧ " +
			"exterior_mask(r, a - nat_pow(2, i)) = delete(exterior_mask(r, a), i)",
	},
		"bit i of a is 1 (MaskWordBits), so word_and(a, 2ⁱ) = 2ⁱ and word_or(a, 2ⁱ) = a "+
			"(word_bits.BitOfAnd, BitPowTwo), and a = 2ⁱ + word_xor(a, 2ⁱ) (bit_arith.OrAndXor): "+
			"2ⁱ ≤ a, and b = a − 2ⁱ is word_xor(a, 2ⁱ), the bits of a with bit i removed (BitOfXor)"),
})}

// MaskEmpty — below 2ʳ only 0 has no binary digit.
var MaskEmpty = maskEmptyThm{family.Add(registry.ProofEntry{
	Name: "MaskEmpty",
	Key:  "prop_5d5a14e77e15c93c",
	Reading: "a < 2ʳ is load-bearing for ⇒: 2ʳ itself has " +
		"no digit below r. The direction ⇐ holds for every a.",
	Deps: []registry.EntryLike{MaskWordBits, word_bits.BitsEqBounded},
	Build: family.Card(Statement{
		Binders:    "∀r a:num.",
		Hypotheses: []string{"a < nat_pow(2, r)"},
		Conclusion: "exterior_mask(r, a) = ∅ ⇔ a = 0",
	},
		"the mask is the word bits below r (MaskWordBits), and two numbers below 2ʳ with the "+
			"same bits below r are equal (word_bits.BitsEqBounded), 0 being the number with none"),
})}

// MaskBijective — the masks of the numbers below 2ʳ are the subsets of
// {0, …, r − 1}, each exactly once.
var MaskBijective = maskBijectiveThm{family.Add(registry.ProofEntry{
	Name: "MaskBijective",
	Key:  "prop_1553bf62bbbefb99",
	Deps: []registry.EntryLike{
		MaskWordBits,
		word_bits.BitsEqBounded,
		word_bits.BitOfBitSet,
		word_bits.WordOfBitsBound,
	},
	Build: family.Card(
		"∀r:num. "+
			"    (∀a b:num. "+
			"        a < nat_pow(2, r) ∧ b < nat_pow(2, r) ∧ exterior_mask(r, a) = exterior_mask(r, b) ⇒ "+
			"        a = b) ∧ "+
			"    (∀s:set(num). s ⊆ {i:num | i < r} ⇒ ∃a:num. a < nat_pow(2, r) ∧ exterior_mask(r, a) = s)",
		"injective: masks are the word bits below r (MaskWordBits), and two numbers below 2ʳ "+
			"with the same bits below r are equal (word_bits.BitsEqBounded). Onto: word_of_bits(r, "+
			"s) is below 2ʳ (WordOfBitsBound) and its bits below r are those of s (BitOfBitSet)"),
})}

// SignToggle — inserting the digit i into a mask adds one to the count of
// its digits below j exactly when i < j.
var SignToggle = signToggleThm{family.Add(registry.ProofEntry{
	Name: "SignToggle",
	Key:  "prop_33f828c730e5e934",
	Reading: "The sign rule of the exterior basis: the generator i passes over the digits " +
		"below it. For i ≠ j, inserting i then j and inserting j then i pass over counts " +
		"whose sums differ by [i < j] + [j < i] = 1, so wedges with two distinct generators " +
		"anticommute, and so do a wedge and a contraction. At j = i the counts are equal.",
	Deps: []registry.EntryLike{MaskInsert, cardinality.InsertCountsOneMore},
	Build: family.Card(Statement{
		Binders:    "∀r a i j:num.",
		Hypotheses: []string{"i < r", "i ∉ exterior_mask(r, a)"},
		Conclusion: "card({k:num | k ∈ exterior_mask(r, a + nat_pow(2, i)) ∧ k < j}) = " +
			"card({k:num | k ∈ exterior_mask(r, a) ∧ k < j}) + COND(i < j, 1, 0)",
	},
		"by MaskInsert the left set is {k ∈ mask(r, a) | k < j} with i inserted when "+
			"i < j and the same set otherwise; it is finite, a subset of {k | k < r}, "+
			"and does not hold i, so cardinality.InsertCountsOneMore counts the insertion"),
})}

// SlotSpec — the k-th slot is the digit of the mask with exactly k digits
// below it.
var SlotSpec = slotSpecThm{family.Add(registry.ProofEntry{
	Name: "SlotSpec",
	Key:  "prop_ca365b0ff238ec02",
	Reading: "For k at least the mask's size the slot is the choice's arbitrary value " +
		"and nothing is claimed. The card gives existence only: that the slots below the " +
		"size are distinct (their counts differ) and exhaust the mask (an injection of " +
		"{0, …, k − 1} into a set of size k is onto) is a counting step its citers take.",
	Deps: []registry.EntryLike{cardinality.FiniteHasSize, cardinality.CardSubset},
	Build: family.Card(Statement{
		Binders:    "∀r a k:num.",
		Hypotheses: []string{"k < card(exterior_mask(r, a))"},
		Conclusion: "exterior_slot(r, a, k) ∈ exterior_mask(r, a) ∧ " +
			"card({j:num | j ∈ exterior_mask(r, a) ∧ j < exterior_slot(r, a, k)}) = k",
	},
		"the choice is met once some digit of the mask has exactly k digits below it; the mask "+
			"is a finite set of numbers, and listing it in increasing order (induction on its size, "+
			"removing the largest element) puts at place k a digit with exactly k smaller ones"),
})}
