// countable.go — the countable number sets: the integers and the
// rationals.

package real_cardinality

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/real/rational"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// CountableInteger — every integer is &n or -&n for a natural n, so the
// integers lie inside the image of ℕ under n ↦ &n together with its
// image under n ↦ -&n. Each image of the countable ℕ is countable, so is
// their union, and so is any subset of it.
var CountableInteger = countableIntegerThm{family.Add(registry.ProofEntry{
	Name: "CountableInteger",
	Key:  "prop_a980464202093b10",
	Build: family.Theorem("countable({x:real | integer(x)})",
		func(a *Argument) {
			naturals := a.TermAs[Set[Nat]]("𝕌⟨A:num⟩")
			plus := a.TermAs[Fun[Nat, Real]]("λn:num. &n")
			minus := a.TermAs[Fun[Nat, Real]]("λn:num. -&n")
			integers := a.TermAs[Set[Real]]("{x:real | integer(x)}")
			plusImage := a.TermAs[Set[Real]]("image(λn:num. &n, 𝕌⟨A:num⟩)")
			minusImage := a.TermAs[Set[Real]]("image(λn:num. -&n, 𝕌⟨A:num⟩)")
			cover := a.TermAs[Set[Real]]("image(λn:num. &n, 𝕌⟨A:num⟩) ∪ image(λn:num. -&n, 𝕌⟨A:num⟩)")
			inside := a.Have(
				"every integer is &n or -&n for some natural n",
				"{x:real | integer(x)} ⊆ image(λn:num. &n, 𝕌⟨A:num⟩) ∪ image(λn:num. -&n, 𝕌⟨A:num⟩)",
				BySets(int_construction.IntegerIffPlusMinusNat))
			a.Show(
				"each image of the countable ℕ is countable, so is their union, and the integers lie inside it",
				By(
					inside,
					cardinal.NumCountable,
					cardinal.CountableImage.At(plus, naturals),
					cardinal.CountableImage.At(minus, naturals),
					cardinal.CountableUnion.At(plusImage, minusImage),
					cardinal.CountableSubset.At(integers, cover)))
		}),
})}

// CountableRational — a rational is m / n with m and n integers, the
// value of the quotient map p ↦ fst(p) / snd(p) at the pair (m, n); so
// the rationals lie inside the quotient map's image of ℤ × ℤ. The pairs
// of integers are countable because the integers are, so is their image,
// and so is any subset of it.
var CountableRational = countableRationalThm{family.Add(registry.ProofEntry{
	Name: "CountableRational",
	Key:  "prop_1048f23f5e2ef166",
	Build: family.Theorem(Statement{
		Conclusion: "countable({x:real | rational(x)})",
		Abbrev: Abbrev{
			{Name: "integerSet", Text: "{x:real | integer(x)}"},
			{Name: "integerPairs", Text: "set_cross(«integerSet», «integerSet»)"},
			{Name: "quotientValues", Text: "image(λp:prod(real, real). fst(p) / snd(p), «integerPairs»)"},
		},
	},
		func(a *Argument) {
			integers := a.TermAs[Set[Real]]("«integerSet»")
			rationals := a.TermAs[Set[Real]]("{x:real | rational(x)}")
			quotientMap := a.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). fst(p) / snd(p)")
			pairsOfIntegers := a.TermAs[Set[Prod[Real, Real]]]("«integerPairs»")
			quotients := a.TermAs[Set[Real]]("«quotientValues»")
			each := a.Have(
				"every rational is the quotient of a pair of integers",
				"∀x:real. rational(x) ⇒ x ∈ «quotientValues»",
				Derive(func(b *Argument) {
					b.FixAs[Real]()
					m, n, isQuotient := b.Unpack2As[Real, Real](b.Unfolded(b.Assume(), rational.RationalDef), "m", "n")
					b.Show(
						"x is m / n for integers m and n; the pair (m, n) lies in "+
							"ℤ × ℤ, its components being integers, and is sent to m / n",
						BySets(
							isQuotient,
							pairs.Fst.At(m, n),
							pairs.Snd.At(m, n),
							set_product.InCross.At(integers, integers, m, n)))
				}))
			inside := a.Have(
				"so the rationals lie among the quotients of pairs of integers",
				"{x:real | rational(x)} ⊆ «quotientValues»",
				BySets(each))
			a.Show(
				"ℤ × ℤ is countable as ℤ is, so is its image under "+
					"the quotient map, and the rationals lie inside it",
				By(
					inside,
					CountableInteger,
					cardinal.CountableProduct.At(integers, integers),
					cardinal.CountableImage.At(quotientMap, pairsOfIntegers),
					cardinal.CountableSubset.At(rationals, quotients)))
		}),
})}

// RationalCardEqNum — there are exactly as many rationals as naturals.
// The rationals are no more than the naturals, being countable, and no
// fewer: n ↦ &n sends the naturals among the rationals and identifies no
// two of them. Schröder–Bernstein joins the two comparisons.
var RationalCardEqNum = rationalCardEqNumThm{family.Add(registry.ProofEntry{
	Name: "RationalCardEqNum",
	Key:  "prop_6845506823db55",
	Build: family.Theorem("card_eq({x:real | rational(x)}, 𝕌⟨A:num⟩)",
		func(a *Argument) {
			rationals := a.TermAs[Set[Real]]("{x:real | rational(x)}")
			naturals := a.TermAs[Set[Nat]]("𝕌⟨A:num⟩")
			noMore := a.Have(
				"the rationals are countable",
				"card_le({x:real | rational(x)}, 𝕌⟨A:num⟩)",
				By(CountableRational, cardinal.CountableDef.At(rationals)))
			noFewer := a.Have(
				"n ↦ &n sends the naturals among the rationals, identifying no two",
				"card_le(𝕌⟨A:num⟩, {x:real | rational(x)})",
				Unfold(cardinal.CardLeDef),
				Unfold(functions.InjectiveOnDef),
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Fun[Nat, Real]]("λn:num. &n"))
					b.Show(
						"&n is rational, and &m = &n only when m = n",
						BySets(rational.OfNumRational, real_construction.OfNumEq))
				}))
			a.Show(
				"no more and no fewer: by Schröder–Bernstein, the same size",
				By(noMore, noFewer, cardinal.SchroederBernstein.At(rationals, naturals)))
		}),
})}
