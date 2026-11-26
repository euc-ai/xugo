// iword.go — the ℤ→word constructor, the ℤ↔word correspondence it
// makes with the signed reading, and the constructor as a ring map:
// what `word_of_int` builds, what it destroys, the two round trips, the one
// test for whether an integer and a word correspond, and how building
// carries ℤ's ring operations to the word ones.
//
// `word_of_int` reduces before it builds — `int_rem` is Euclidean, so
// the remainder it takes is already the reduced value — and the first
// part's members are the faces of that reduction. A number carries no
// sign to destroy, so on `&m` the reduction is ℕ's own nat_mod; on an
// arbitrary integer the reduction destroys exactly the multiple of
// the range, which is what a congruence modulo the range cannot see;
// and a second reduction finds nothing left to do. The second part
// turns those faces into the correspondence with `int_of_word`.
//
// The range never vanishes — `int_pow(&2, n) ≠ &0` — and that is the
// standing premise of the whole file: it is what makes each remainder
// nonnegative, hence able to cross into ℕ and back as itself, hence
// the crossing faithful. `WordOfIntImage` spends it once, and every other
// member reaches the crossing through that equation.

package signed_word

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_congruence"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_div_rem"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/words/machine_word"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The constructor's basics
// ---------------------------------------------------------------------------

// WordOfIntOfNum — on ℕ's image `word_of_int` IS the unsigned reduction: a
// word built from an embedded number is that number modulo the range.
// Fully strong — at n = 0 both sides are 0.
//
// Unfolding `word_of_int` leaves the ℕ→ℤ→ℕ round trip on the argument, and
// nothing is deduced about it — the ℤ side is COMPUTED away: the
// modulus becomes ℕ's range, the remainder of two images becomes the
// image of ℕ's nat_mod, and the retraction cancels the image it is
// applied to. What is left is the two sides spelled alike.
var WordOfIntOfNum = wordOfIntOfNumThm{family.Add(registry.ProofEntry{
	Name: "WordOfIntOfNum",
	Key:  "prop_30408d5a6062aaf4",
	Build: family.Theorem(
		"∀n m:num. word_of_int(n, m) = rem(m, nat_pow(2, n))",
		func(a *Argument, n, m Term) {
			// ↦ num_of_int(int_rem(int_of_num(m), int_pow(int_of_num(2), n))) = nat_mod(m, nat_pow(2, n))
			a.Do(Unfold(WordOfIntDef))

			a.Show(
				"the ℤ detour is computed away, and the two sides spell alike",
				Simp(
					Rev(int_pow.OfNumPow),       // int_pow(&2, n) ↦ &(nat_pow(2, n))
					Rev(int_div_rem.OfNumRem),   // int_rem(&m, &(nat_pow(…))) ↦ &(nat_mod(m, nat_pow(…)))
					Fwd(int_embed.OfNumRetract), // num_of_int(&(nat_mod(…))) ↦ nat_mod(…)
				),
				TrivialNormalized())
		}),
})}

// IntRoundTripCong — an integer built into a word and read back is
// congruent to itself modulo the range. Fully strong — at width zero
// everything is congruent mod 1.
//
// The proof puts one named quantity between the two maps: the
// remainder of x by the range. `IntOfWordValCong` reads the built word
// congruent to its own image; that image IS the remainder — the
// crossing into ℕ and back changes nothing on a nonnegative integer,
// and the Euclidean remainder is nonnegative because the range never
// vanishes (`int_pow.PowTwoNonzero`); and modulo the range a
// remainder by the range is what it came from.
var IntRoundTripCong = intRoundTripCongThm{family.Add(registry.ProofEntry{
	Name: "IntRoundTripCong",
	Key:  "prop_71be97d41284ea8",
	Build: family.Theorem(
		"∀n:num. ∀x:int. int_of_word(n, word_of_int(n, x)) ≡ x (mod int_pow(2, n))",
		func(a *Argument, n, x Term) {
			// The range in ℤ; the built word and its reading.
			modulus := a.Term("int_pow(2, n)")
			built := a.Term("word_of_int(n, x)")
			reading := a.Term("int_of_word(n, word_of_int(n, x))")

			a.Show(
				"the built word's image is the source's remainder, the reading is "+
					"congruent to that, and modulo the range a remainder is what it came from",
				By(
					WordOfIntImage,
					// int_of_word(n, built) ≡ &(built) (mod modulus)
					At(IntOfWordValCong, n, built),
					// reading ≡ remainder (mod modulus) ⇔ reading ≡ x (mod modulus)
					At(int_congruence.RemRight, reading, x, modulus)))
		}),
})}

// WordOfIntRem — reducing before building changes nothing, because
// building reduces anyway: `word_of_int` cannot tell an integer from its
// remainder by the range. It is what makes the constructor well
// defined on remainders, so a value computed in ℤ may be brought into
// range at any point, or not at all, and the word is the same either
// way.
//
// Unfolded, both sides are `num_of_int` of a remainder by the range —
// the right one taken twice — and a remainder taken twice is taken
// once.
var WordOfIntRem = wordOfIntRemThm{family.Add(registry.ProofEntry{
	Name: "WordOfIntRem",
	Key:  "prop_c32201e62a9989bb",
	Build: family.Theorem(
		"∀n:num. ∀m:int. word_of_int(n, m) = word_of_int(n, rem(m, int_pow(2, n)))",
		func(a *Argument, n, m Term) {
			// ↦ num_of_int(int_rem(m, R)) = num_of_int(int_rem(int_rem(m, R), R)),
			// with R the range int_pow(&2, n) on both sides.
			a.Do(Unfold(WordOfIntDef))

			// The law goes in bare: its ∀-form already rewrites the
			// doubled reduction away, closing the goal at the install.
			a.Show(
				"both sides reduce by one and the same range, so the "+
					"doubled reduction collapses and the two sides spell alike",
				By(int_div_rem.RemRem))
		}),
})}

// WordOfIntImage — a built word's image is its source's remainder by the
// range: the one equation through which every claim about `word_of_int`
// crosses back into ℤ, and the fact the part banner promises. The
// remainder is nonnegative because the range never vanishes, and a
// nonnegative integer crosses into ℕ and back as itself — so
// unfolding the constructor leaves exactly that round trip.
var WordOfIntImage = wordOfIntImageThm{family.Add(registry.ProofEntry{
	Name: "WordOfIntImage",
	Key:  "prop_f445e6790ba34f7b",
	Build: family.Theorem(
		"∀n:num. ∀x:int. word_of_int(n, x) = rem(x, int_pow(2, n))",
		func(a *Argument, n, x Term) {
			modulus := a.Term("int_pow(2, n)")
			remainder := a.Term("rem(x, int_pow(2, n))")

			// Left unbound: consumed ambiently — unfolding `word_of_int`
			// exposes exactly this round trip, and the resident equation
			// closes it as part of the expansion's own simplify.
			a.Have(
				"the remainder of x by the never-vanishing range is not "+
					"negative, and therefore crosses into ℕ and back as itself",
				"int_of_num(num_of_int(rem(x, int_pow(2, n)))) = rem(x, int_pow(2, n))",
				By(
					// int_pow(&2, n) ≠ &0
					At(int_pow.PowTwoNonzero, n),
					// modulus ≠ &0 ⇒ &0 ≤ remainder
					At(int_div_rem.RemNonneg, x, modulus),
					// &0 ≤ remainder ⇒ &(num_of_int(remainder)) = remainder
					At(int_embed.NumOfIntSection, remainder)))

			// ↦ &(num_of_int(remainder)) = remainder — the resident fact,
			// absorbed by the expansion's own simplify.
			a.Show(
				"unfolding the constructor leaves exactly the round trip the fact above closes",
				Unfold(WordOfIntDef))
		}),
})}

// ---------------------------------------------------------------------------
// The ℤ↔word correspondence
// ---------------------------------------------------------------------------
//
// `word_of_int` is exactly the quotient of ℤ by the range — two integers
// build one word precisely when they are congruent — and `int_of_word` is
// its section on the window ⟦−2ⁿ⁻¹, 2ⁿ⁻¹⟭: a word read and rebuilt is
// that word, an integer of the window built and read back is that
// integer. Together the two maps are a bijection between the words and
// the window's integers, which is what a fixed-width signed integer
// type IS; the last member states the bijection as one equivalence.

// WordOfIntEq — two integers build one word exactly when they are
// congruent modulo the range: the precise statement of what the
// constructor destroys, and with it the map is completely described —
// the quotient of ℤ by the range, no coarser and no finer. Fully
// strong: at width zero everything is congruent mod 1 and both builds
// are the zero word.
//
// The two builds' images are the two remainders, a congruence modulo
// the range IS an equality of remainders by it, and the embedding's
// injectivity carries that equality between the images and the words.
var WordOfIntEq = wordOfIntEqThm{family.Add(registry.ProofEntry{
	Name: "WordOfIntEq",
	Key:  "prop_62cfc39977ddde2d",
	Build: family.Theorem(
		"∀n:num. ∀x y:int. (word_of_int(n, x) = word_of_int(n, y)) ⇔ x ≡ y (mod int_pow(2, n))",
		func(a *Argument, n, x, y Term) {
			modulus := a.Term("int_pow(2, n)")

			a.Show(
				"a congruence modulo the range equates the remainders, the builds' "+
					"images, and the embedding's injectivity descends that to the built words",
				By(
					WordOfIntImage,
					// x ≡ y (mod R) ⇔ int_rem(x, R) = int_rem(y, R)
					At(int_congruence.CongruentIffSameRem, x, y, modulus),
					// left bare: &a = &b ⇔ a = b is the rewrite that
					// descends the crossed equality to ℕ's own.
					int_embed.OfNumEq))
		}),
})}

// WordRoundTrip — read a word and build it back, and you have the word:
// the round trip in the order that owes only the range guard every
// val-face statement carries. A reading is not just any integer — it
// is congruent to the word's own image, so the remainder the
// constructor takes from it is the image's remainder, and an in-range
// image is its own remainder. It is what makes `word_of_int` onto and
// `int_of_word` one-to-one.
//
// One close does it: unfolding the constructor leaves the retraction
// of the reading's remainder, and the premises — the congruence read
// as an equality of remainders, the ℕ↔ℤ crossings, and the residue
// collapse — meet it in a single step (the stations are marked inline,
// not deduced separately: none names anything the next would reuse).
var WordRoundTrip = wordRoundTripThm{family.Add(registry.ProofEntry{
	Name: "WordRoundTrip",
	Key:  "prop_f58a4ae3f5a78ce9",
	Build: family.Theorem(
		Statement{
			Binders: "∀n w:num.",
			Hypotheses: []string{
				"w < nat_pow(2, n)",
			},
			Conclusion: "w = word_of_int(n, int_of_word(n, w))",
		},
		func(a *Argument, n, w Term, wBound Fact) {
			two := a.Ctx().Numeral(2)
			width := a.Term("nat_pow(2, n)")
			reading := a.Term("int_of_word(n, w)")
			image := a.TermAs[Int]("w")
			modulus := a.Term("int_pow(2, n)")

			// ↦ w = num_of_int(int_rem(int_of_word(n, w), int_pow(int_of_num(2), n)))
			a.Do(Unfold(WordOfIntDef))

			a.Show(
				"the reading's remainder is the image's remainder, which in "+
					"range is the image itself — and its retraction is the word",
				By(
					Normalized,
					wBound,
					// int_of_word(n, w) ≡ int_of_num(w) (mod modulus)
					At(IntOfWordValCong, n, w),
					// so int_rem(reading, modulus) = int_rem(image, modulus)
					At(int_congruence.CongruentIffSameRem, reading, image, modulus),
					// int_rem(&w, &(nat_pow(2, n))) = &(nat_mod(w, nat_pow(2, n)))
					At(int_div_rem.OfNumRem, w, width),
					// with the modulus one range, raised in ℕ and then
					// embedded or embedded and then raised
					At(int_pow.OfNumPow, two, n),
					// below the width, nat_mod(w, nat_pow(2, n)) = w
					At(nat_div_mod.ModLessThan, w, width),
					// and num_of_int(&w) = w
					At(int_embed.OfNumRetract, w)))
		}),
})}

// IntRoundTripInRange — in the other order the round trip is exact
// exactly where the reading can reach: an integer of the half-open
// window built into a word reads back as itself. This is the sharp
// form of the congruence the constructor leaves, and — with
// `WordRoundTrip` above — what makes the two maps a bijection between
// the words and the window's integers.
//
// Three sentences and no case split. The round trip is congruent to
// what it started from, so the two differ by a multiple of the range.
// Both lie in the window of half-width 2ⁿ⁻¹ — m by hypothesis, the
// reading by its own bound — so they differ by less than the window's
// full width. And the full width IS the range: a power is doubled by
// raising the exponent one place, and the width guard is what gives it
// a place to be raised from. A congruence over a gap smaller than its
// modulus is an equality.
var IntRoundTripInRange = intRoundTripInRangeThm{family.Add(registry.ProofEntry{
	Name: "IntRoundTripInRange",
	Key:  "prop_aceaf58d3874c17e",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num. ∀m:int.",
			Hypotheses: []string{
				"1 ≤ n",
				"-int_pow(2, n - 1) ≤ m",
				"m < int_pow(2, n - 1)",
			},
			Conclusion: "m = int_of_word(n, word_of_int(n, m))",
		},
		func(a *Argument, n, m Term, widthPos, lower, upper Fact) {
			one := a.Ctx().Numeral(1)

			// The top place; the half range on the ℕ side, where the
			// doubling is settled; the half range and the whole range
			// in ℤ, where every bound below is compared; the word m
			// builds; and its reading, the argument's one quantity.
			topPlace := a.Term("n - 1")
			halfNat := a.Term("nat_pow(2, n - 1)")
			halfRange := a.Term("int_pow(2, n - 1)")
			wholeRange := a.Term("int_pow(2, n)")
			built := a.Term("word_of_int(n, m)")
			reading := a.Term("int_of_word(n, word_of_int(n, m))")

			doublingNat := a.Have(
				"the whole range is the half range twice over — the width has a place to raise the power from",
				"nat_pow(2, n) = nat_pow(2, n - 1) + nat_pow(2, n - 1)",
				ByArith(
					Normalized,
					widthPos,
					At(nat_monus.SubAddCancel, n, one), // (n - 1) + 1 = n
					At(nat_arith.Add1, topPlace),       // suc(n - 1) = (n - 1) + 1
					// Bare — its ∀-form closes the goal at the install.
					nat_arith.PowTwoSuc)) // 2ᵏ + 2ᵏ = 2^suc(k), at the top place

			// Only the SUM needs citing across: `&(nat_pow(2, k))` and
			// `int_pow(&2, k)` are one normal form to the ℤ closer,
			// which lowers the power even at a symbolic exponent.
			doubling := a.Have(
				"and the embedding carries the doubling across, the powers crossing by themselves",
				"int_pow(2, n) = int_pow(2, n - 1) + int_pow(2, n - 1)",
				ByArith(doublingNat, At(int_embed.OfNumAdd, halfNat, halfNat)))

			// The half range is NAMED for the close: the linear closer
			// works over opaque quantities and a power is not one of
			// them — named, the four bounds become four ordinary
			// inequalities.
			span := a.Have(
				"m and the reading of its word share one half-open window, so neither "+
					"stands a full width from the other, and that width is positive",
				"m - (int_pow(2, n - 1) + int_pow(2, n - 1)) < int_of_word(n, word_of_int(n, m)) ∧ "+
					"int_of_word(n, word_of_int(n, m)) < m + (int_pow(2, n - 1) + int_pow(2, n - 1)) ∧ "+
					"0 < int_pow(2, n - 1) + int_pow(2, n - 1)",
				ByArith(
					DenotedAs("halfRange", halfRange),
					lower,
					upper,
					// -halfRange ≤ reading ∧ reading < halfRange
					At(IntOfWordBound, n, built)))

			// The doubling enters here and only here, to read the
			// window's width back as the range: the equivalence names
			// the goal and the two facts fill in its other side.
			gap := a.Have(
				"so their difference is smaller than the whole range",
				"|int_of_word(n, word_of_int(n, m)) - m| < int_pow(2, n)",
				By(
					doubling,
					span,
					// int_abs(reading - m) < wholeRange
					// ⇔ m - wholeRange < reading ∧ reading < m + wholeRange ∧ &0 < wholeRange
					At(int_real_lift.AbsBetween, m, reading, wholeRange)))

			a.Show(
				"and a congruence over a gap smaller than its modulus is an equality",
				By(
					gap,
					// reading ≡ m (mod wholeRange)
					At(IntRoundTripCong, n, m),
					// int_abs(reading - m) < wholeRange ∧ reading ≡ m (mod wholeRange)
					// ⇒ reading = m
					At(int_congruence.EqOfSmallDifference, reading, m, wholeRange)))
		}),
})}

// IntOfWordEqByWordOfIntInRange — the correspondence itself: m is w's reading
// exactly when w is the word m builds and m lies in the window. Read
// left to right it extracts — hold the reading and you have the word
// back and where m lies; read right to left it constructs. It is the
// two round trips above as ONE sentence, with the window inside it
// instead of three facts to assemble.
//
// So nothing is proved a second time; each direction is an already
// member above with the hypotheses put to work. Building then reading
// is exact inside the window (`IntRoundTripInRange` — the equivalence's
// own conjuncts are the range it asks for); and a reading keeps to the
// window (`IntOfWordBound`) and rebuilds its word (`WordRoundTrip`), with the
// hypothesis carrying each of the two across to m.
var IntOfWordEqByWordOfIntInRange = intOfWordEqByWordOfIntInRangeThm{family.Add(registry.ProofEntry{
	Name: "IntOfWordEqByWordOfIntInRange",
	Key:  "prop_c2f5b87d72c4790d",
	Build: family.Theorem(
		Statement{
			Binders: "∀n w:num. ∀m:int.",
			Hypotheses: []string{
				"1 ≤ n",
				"w < nat_pow(2, n)",
			},
			Conclusion: "m = int_of_word(n, w) ⇔ " +
				"w = word_of_int(n, m) ∧ -int_pow(2, n - 1) ≤ m ∧ m < int_pow(2, n - 1)",
		},
		func(a *Argument, n, w, m Term, widthPos, wBound Fact) {
			// Both arms close by simplification: each is one cited
			// instance met by the hypothesis — a substitution, plus the
			// discharge of guards the hypotheses already carry.
			a.Iff()
			a.Forward(
				"a reading keeps to the window and rebuilds the word it came from, and m is that reading",
				func(a *Argument, reads Fact) {
					a.Show(
						"both facts are about int_of_word(n, w), and the hypothesis carries each across to m",
						By(
							wBound,
							reads,
							// -half ≤ int_of_word(n, w) ∧ int_of_word(n, w) < half
							At(IntOfWordBound, n, w),
							// w < nat_pow(2, n) ⇒ w = word_of_int(n, int_of_word(n, w))
							At(WordRoundTrip, n, w)))
				})
			a.Backward(
				"m is in the window and w is the word it builds, so reading w can only give m back",
				func(a *Argument, builtInWindow Fact) {
					a.Show(
						"the first conjunct makes the claim that round trip, "+
							"and the other two are the window that makes it exact",
						By(
							widthPos,
							builtInWindow,
							// 1 ≤ n ⇒ -half ≤ m ⇒ m < half ⇒ m = int_of_word(n, word_of_int(n, m))
							At(IntRoundTripInRange, n, m)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The constructor as a ring map
// ---------------------------------------------------------------------------
//
// Building a word commutes with the ring: `word_of_int` carries sums,
// negations, differences and products of integers to the val-face
// operations on the words they build. Every member is fully strong —
// at width zero every word is the zero word, so both sides agree with
// nothing asked.
//
// One argument serves all four. Each val-face operation IS a build:
// its reduction is what `word_of_int` makes of the embedded ℕ result —
// `WordOfIntOfNum` read backwards — so by `WordOfIntEq` each member is
// ONE CONGRUENCE between integers. And that congruence is remainder
// algebra: a built word's image is its source's remainder by the range
// (`WordOfIntImage`), and modulo the range the sum,
// negation or product of remainders is the sum, negation or product of
// the sources. The difference member alone needs no remainders — it is
// the sum and negation members composed.

// WordOfIntSum — the constructor carries a sum of integers to the word
// sum of the words they build.
//
// The word sum reduces the ℕ-sum of the two built words, which is what
// `word_of_int` builds from that sum's embedding — so the claim is the
// congruence of x + y with the embedded sum. Each built word's image
// is its source's remainder by the range, and a sum of remainders
// leaves the remainder of the sum (int_congruence.RemOfSum), which is
// that congruence read as an equality of remainders.
var WordOfIntSum = wordOfIntSumThm{family.Add(registry.ProofEntry{
	Name: "WordOfIntSum",
	Key:  "prop_bdb41537cfedac10",
	Build: family.Theorem(
		"∀n:num. ∀x y:int. word_of_int(n, x + y) = word_add(n, word_of_int(n, x), word_of_int(n, y))",
		func(a *Argument, n, x, y Term) {
			modulus := a.Term("int_pow(2, n)")
			builtX := a.Term("word_of_int(n, x)")
			builtY := a.Term("word_of_int(n, y)")
			sumSrc := a.Term("x + y")
			embSum := a.Term("int_of_num(word_of_int(n, x) + word_of_int(n, y))")

			cong := a.Have(
				"x + y is congruent to the embedded sum of the built words, whose "+
					"images are remainders: both leave what a sum of remainders leaves",
				"x + y ≡ word_of_int(n, x) + word_of_int(n, y) (mod int_pow(2, n))",
				By(
					WordOfIntImage,
					// &(word_of_int(n, x) + word_of_int(n, y)) = &word_of_int(n, x) + &word_of_int(n, y)
					At(int_embed.OfNumAdd, builtX, builtY),
					// the claim, as an equality of remainders by the range
					At(int_congruence.CongruentIffSameRem, sumSrc, embSum, modulus),
					// int_rem(x + y, R) = int_rem(int_rem(x, R) + int_rem(y, R), R)
					At(int_congruence.RemOfSum, x, y, modulus)))

			a.Show(
				"the word sum is what the constructor builds from the "+
					"embedded sum, and congruent sources build one word",
				// ↦ word_of_int(n, x + y) = nat_mod(word_of_int(n, x) + word_of_int(n, y), nat_pow(2, n))
				Unfold(machine_word.WordAddDef),
				// Both laws go in bare and land as rewrites: WordOfIntOfNum
				// folds the exposed reduction back into the build of the
				// embedded sum, and WordOfIntEq exchanges the resulting
				// equality of builds for the congruence `cong` supplies.
				By(cong, WordOfIntOfNum, WordOfIntEq))
		}),
})}

// WordOfIntNeg — the constructor carries a negation to the word
// negation of the built word.
//
// The val-face negation reduces the complement, and the complement law
// machine_word.CongNeg says what that means modulo the range: the negated
// word and the word it negates sum to nothing. Crossed into ℤ and with
// the built word's image known to be the source's remainder, one
// congruence subtraction turns "the images sum to nothing" into "the
// negated word's image is congruent to -x" — and congruent sources
// build one word.
var WordOfIntNeg = wordOfIntNegThm{family.Add(registry.ProofEntry{
	Name: "WordOfIntNeg",
	Key:  "prop_6bc054bced73efdb",
	Build: family.Theorem(
		"∀n:num. ∀x:int. word_of_int(n, -x) = word_neg(n, word_of_int(n, x))",
		func(a *Argument, n, x Term) {
			two := a.Ctx().Numeral(2)
			zero := a.Ctx().Numeral(0)
			modulus := a.Term("int_pow(2, n)")
			width := a.Term("nat_pow(2, n)")
			built := a.Term("word_of_int(n, x)")
			negated := a.Term("word_neg(n, word_of_int(n, x))")
			sumNat := a.Term("word_neg(n, word_of_int(n, x)) + word_of_int(n, x)")
			embA := a.Term("int_of_num(word_of_int(n, x))")
			embW := a.Term("int_of_num(word_neg(n, word_of_int(n, x)))")
			sumInt := a.Term("word_neg(n, word_of_int(n, x)) + int_of_num(word_of_int(n, x))")
			zeroInt := a.TermAs[Int]("0")
			negX := a.Term("-x")

			reduced := a.Have(
				"the negated word is already reduced: unfolded, it is a "+
					"remainder by the range, and a remainder taken twice is taken once",
				"rem(word_neg(n, word_of_int(n, x)), nat_pow(2, n)) = word_neg(n, word_of_int(n, x))",
				Unfold(machine_word.WordNegDef),
				// nat_mod(nat_mod(C, nat_pow(2, n)), nat_pow(2, n)) = nat_mod(C, nat_pow(2, n)),
				// with C the complement the unfolding exposes — the law
				// lands bare as the rewrite collapsing the doubled
				// reduction.
				By(nat_div_mod.ModModRefl))

			// A and W abbreviate the two words in the comments below —
			// A the word x builds (`built`), W its val-face negation
			// (`negated`) — so that a cite's shape stays on one line.
			// The embeddings are named for them: embA = &A, embW = &W.
			crossed := a.Have(
				"the value face's complement law, crossed into ℤ: the negated word's "+
					"image and the word's own image sum to nothing modulo the range",
				"word_neg(n, word_of_int(n, x)) + &word_of_int(n, x) ≡ 0 (mod int_pow(2, n))",
				By(
					// ==(word_neg(n, A) + A, 0, num_mod(nat_pow(2, n))) — ℕ's own
					// complement congruence, at the built word
					At(machine_word.CongNeg, n, built),
					// which read in ℤ is &(word_neg(n, A) + A) ≡ &0 at &(nat_pow(2, n))
					At(int_congruence.OfNumCongruent, sumNat, zero, width),
					// with the modulus one range, raised in ℕ and then
					// embedded or embedded and then raised
					At(int_pow.OfNumPow, two, n),
					// and the embedded sum split across the crossing
					At(int_embed.OfNumAdd, negated, built)))

			negCong := a.Have(
				"subtracting the word's image — congruent to the source — from "+
					"both sides leaves the negated word's image congruent to -x",
				"-x ≡ word_neg(n, word_of_int(n, x)) (mod int_pow(2, n))",
				By(
					Normalized,
					crossed,
					WordOfIntImage,
					// int_rem(x, R) ≡ x (mod R): the image is congruent to its source
					At(int_congruence.RemCongruent, x, modulus),
					// (&W + &A) - &A ≡ &0 - x, congruents less congruents
					At(int_congruence.SubCongruent, sumInt, zeroInt, embA, x, modulus),
					// (&W + &A) - &A = &W ⇔ &W + &A = &W + &A — the left side computed
					At(int_real_lift.EqSubRightAdd, sumInt, embA, embW),
					// &0 - x = -x
					At(int_real_lift.SubLeftZero, x),
					// and the congruence flipped through its remainder
					// reading, once in each direction
					At(int_congruence.CongruentIffSameRem, negX, embW, modulus),
					At(int_congruence.CongruentIffSameRem, embW, negX, modulus)))

			a.Show(
				"the val-face negation — already reduced — is what the constructor "+
					"builds from its own embedding, and congruent sources build one word",
				// WordOfIntOfNum and WordOfIntEq go in bare and land as
				// rewrites, as in WordOfIntSum's close.
				By(reduced, negCong, WordOfIntOfNum, WordOfIntEq))
		}),
})}

// WordOfIntDiff — the constructor carries a difference to the word
// difference of the built words: nothing about words is at stake — ℤ
// reads subtraction as adding the negation, and the sum and negation
// members carry each piece across.
var WordOfIntDiff = wordOfIntDiffThm{family.Add(registry.ProofEntry{
	Name: "WordOfIntDiff",
	Key:  "prop_8820264390abfe28",
	Build: family.Theorem(
		"∀n:num. ∀x y:int. word_of_int(n, x - y) = word_sub(n, word_of_int(n, x), word_of_int(n, y))",
		func(a *Argument, n, x, y Term) {
			negY := a.Term("-y")

			a.Show(
				"ℤ reads the difference as x + -y, and the constructor carries the negation and then the sum",
				// ↦ word_of_int(n, x - y) = word_add(n, word_of_int(n, x), word_neg(n, word_of_int(n, y)))
				Unfold(machine_word.WordSubDef),
				By(
					// Both ring-map members go in bare and land as rewrites,
					// folding the val-face operations back into builds:
					// word_neg(n, word_of_int(n, y)) ↦ word_of_int(n, -y), then
					// word_add(n, word_of_int(n, x), word_of_int(n, -y)) ↦ word_of_int(n, x + -y).
					WordOfIntNeg,
					WordOfIntSum,
					// x - int_neg(-y) = x + -y
					At(int_real_lift.SubRightNeg, x, negY),
					// bare, the rewrite int_neg(int_neg(y)) ↦ y that reads
					// the instance above as x - y = x + -y
					int_real_lift.NegNeg))
		}),
})}

// WordOfIntProduct — the constructor carries a product of integers to
// the word product of the words they build: WordOfIntSum's argument with
// the sum replaced by the product at every step — the embedding
// carries products, and a product of remainders leaves the remainder
// of the product.
var WordOfIntProduct = wordOfIntProductThm{family.Add(registry.ProofEntry{
	Name: "WordOfIntProduct",
	Key:  "prop_522796bced7fa10",
	Build: family.Theorem(
		"∀n:num. ∀x y:int. word_of_int(n, x * y) = word_mul(n, word_of_int(n, x), word_of_int(n, y))",
		func(a *Argument, n, x, y Term) {
			modulus := a.Term("int_pow(2, n)")
			builtX := a.Term("word_of_int(n, x)")
			builtY := a.Term("word_of_int(n, y)")
			prodSrc := a.Term("x * y")
			embProd := a.Term("int_of_num(word_of_int(n, x) * word_of_int(n, y))")

			cong := a.Have(
				"x * y is congruent to the embedded product of the built words, whose "+
					"images are remainders: both leave what a product of remainders leaves",
				"x * y ≡ word_of_int(n, x) * word_of_int(n, y) (mod int_pow(2, n))",
				By(
					WordOfIntImage,
					// &(word_of_int(n, x) * word_of_int(n, y)) = &word_of_int(n, x) * &word_of_int(n, y)
					At(int_embed.OfNumMul, builtX, builtY),
					// the claim, as an equality of remainders by the range
					At(int_congruence.CongruentIffSameRem, prodSrc, embProd, modulus),
					// int_rem(x * y, R) = int_rem(int_rem(x, R) * int_rem(y, R), R)
					At(int_congruence.RemOfProduct, x, y, modulus)))

			a.Show(
				"the word product is what the constructor builds from the "+
					"embedded product, and congruent sources build one word",
				// ↦ word_of_int(n, x * y) = nat_mod(word_of_int(n, x) * word_of_int(n, y), nat_pow(2, n))
				Unfold(machine_word.WordMulDef),
				// WordOfIntOfNum and WordOfIntEq go in bare and land as
				// rewrites, as in WordOfIntSum's close.
				By(cong, WordOfIntOfNum, WordOfIntEq))
		}),
})}
