// liminf.go — the lower limit of a sequence in ⟦0, ∞⟧, the
// eventual lower bound it gives for a nonnegative real sequence, and the
// bound the limit of a convergent real sequence gives it.

package extended_nonneg_real

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// ExtendedLiminfDef — the lower limit of a sequence is the supremum
// of the infima of its tails.
var ExtendedLiminfDef = extendedLiminfDefThm{family.Define(registry.DefEntry{
	Name:  "ExtendedLiminfDef",
	Key:   "prop_d33c31f4da0d209c",
	Const: "extended_liminf",
	Type:  "(num → extended_nonneg_real) → extended_nonneg_real",
	Equations: []string{
		"∀a:(num → extended_nonneg_real). " +
			"    extended_liminf(a) = extended_sup(image(λk:num. extended_inf(image(λn:num. a(k + n), 𝕌)), 𝕌))",
	},
	Deps: []registry.EntryLike{ExtendedSupDef, ExtendedInfDef},
})}

// LowerLimitEventually — a fact of ⟦0, ∞⟧ read back on the reals: where l
// lies below the lower limit, taken in ⟦0, ∞⟧, of a nonnegative real
// sequence, the terms eventually exceed l − ε. Below 0 every term does.
// Otherwise l − ε lies strictly below the lower limit, so below the
// infimum of some tail, and so below every term of that tail.
var LowerLimitEventually = lowerLimitEventuallyThm{family.Add(registry.ProofEntry{
	Name: "LowerLimitEventually",
	Reading: "The displayed supremum of tail infima is extended_liminf " +
		"applied to the sequence embedded by extended_of_real.",
	Key: "prop_8e137cc2bd3f7b",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀l ε:real.",
		Hypotheses: []string{
			"∀n:num. &0 ≤ a(n)",
			"extended_of_real(l) ≤ «liminf»",
			"&0 < ε",
		},
		Conclusion: "∃N:num. ∀n:num. N ≤ n ⇒ l - ε < a(n)",
		Abbrev: Abbrev{
			{Name: "liminf", Text: "extended_sup( " +
				"    image(λk:num. extended_inf(image(λn:num. extended_of_real(a(k + n)), 𝕌)), 𝕌))"},
		},
	}, func(arg *Argument, a *Arrow[Nat, Real], l, ε *Expr[Real], nonneg, below, positive Fact) {
		reached := arg.Assuming(
			arg.Term("&0 ≤ l - ε"),
			"below 0 every term lies above l − ε",
			Given(func(b *Argument, negative Fact) {
				b.Take(b.TermAs[Nat]("0"))
				n := b.FixAs[Nat]("n")
				b.Assume()
				b.Show(
					"a(n) is nonnegative",
					ByArith(negative, nonneg.At(n)))
			}))
		lower := arg.TermAs[ExtendedNonnegReal]("extended_of_real(l - ε)")
		liminf := arg.TermAs[ExtendedNonnegReal]("«liminf»")
		strictly := arg.Have(
			"l − ε lies strictly below the lower limit, l lying below it",
			"extended_of_real(l - ε) < «liminf»",
			ByArith(
				reached,
				below,
				positive,
				OfRealLe.At(l, arg.TermAs[Real]("l - ε")),
				LtIffNotLe.At(lower, liminf),
				LeTrans.At(
					arg.TermAs[ExtendedNonnegReal]("extended_of_real(l)"), liminf, lower)))
		k, tail := arg.ObtainAs[Nat](
			"so below the infimum of some tail",
			"∃k:num. extended_of_real(l - ε) < extended_inf(image(λj:num. extended_of_real(a(k + j)), 𝕌))",
			By(
				strictly,
				SupApprox.At(
					arg.TermAs[Set[ExtendedNonnegReal]](
						"image(λk:num. extended_inf(image(λj:num. extended_of_real(a(k + j)), 𝕌)), 𝕌)"),
					lower),
				set_image.ExistsInImage.At(
					arg.TermAs[Fun[Nat, ExtendedNonnegReal]](
						"λk:num. extended_inf(image(λj:num. extended_of_real(a(k + j)), 𝕌))"),
					arg.TermAs[Set[Nat]]("𝕌"),
					arg.TermAs[Set[ExtendedNonnegReal]](
						"λy:extended_nonneg_real. extended_of_real(l - ε) < y")),
				set_basic.InUniv))
		late := arg.Have(
			"and so below every term of that tail",
			"∀n:num. l - ε < a(k + n)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				terms := b.TermAs[Fun[Nat, ExtendedNonnegReal]](
					"λj:num. extended_of_real(a(k + j))")
				term := b.TermAs[ExtendedNonnegReal]("extended_of_real(a(k + n))")
				infimum := b.TermAs[ExtendedNonnegReal](
					"extended_inf(image(λj:num. extended_of_real(a(k + j)), 𝕌))")
				b.Show(
					"the infimum of the tail lies below its term a(k + n), a nonnegative real",
					ByArith(
						reached,
						tail,
						nonneg.At(b.TermAs[Nat]("k + n")),
						set_image.FunInRange.At(terms, n),
						InfLower.At(
							b.TermAs[Set[ExtendedNonnegReal]](
								"image(λj:num. extended_of_real(a(k + j)), 𝕌)"),
							term),
						LtIffNotLe.At(lower, infimum),
						LeTrans.At(infimum, term, lower),
						OfRealLe.At(b.TermAs[Real]("a(k + n)"), b.TermAs[Real]("l - ε"))))
			}))
		arg.Take(k)
		n := arg.FixAs[Nat]("n")
		past := arg.Assume()
		d, shift := arg.ObtainAs[Nat](
			"n is k + d for some d",
			"∃d:num. n = k + d",
			By(past, nat_order.LessEqExists.At(n, k)))
		arg.Show(
			"so a(n) is a term of the tail",
			ByArith(late.At(d), shift))
	}),
})}

// LimitLeLiminf — the image in ⟦0, ∞⟧ of the limit of a convergent real
// sequence lies below the lower limit of the images of its terms. Where the
// limit l is not positive its image is 0. Otherwise, for 0 < c < 1, the
// terms eventually exceed c·l, so the image of c·l lies below the infimum of
// a tail, hence below the lower limit; and c times the image of l is the
// image of c·l. Every c below 1 doing so, the image of l does too. No sign
// is asked of the terms.
var LimitLeLiminf = limitLeLiminfThm{family.Add(registry.ProofEntry{
	Name: "LimitLeLiminf",
	Key:  "prop_47ac6155bceadf78",
	Build: family.Theorem(Statement{
		Binders:    "∀a:(num → real). ∀l:real.",
		Hypotheses: []string{"a ⟶ l"},
		Conclusion: "extended_of_real(l) ≤ «liminf»",
		Abbrev: Abbrev{
			{Name: "liminf", Text: "extended_liminf(λn:num. extended_of_real(a(n)))"},
		},
	}, func(arg *Argument, a *Arrow[Nat, Real], l *Expr[Real], converges Fact) {
		liminf := arg.TermAs[ExtendedNonnegReal]("«liminf»")
		positive := arg.Assuming(
			arg.Term("&0 < l"),
			"where l is not positive its image is 0, the least value",
			Given(func(b *Argument, nonpositive Fact) {
				b.Show(
					"the embedding clamps l to 0",
					ByArith(nonpositive, OfRealNeg.At(l), ZeroLe))
			}))
		scaled := arg.Have(
			"for 0 < c < 1, c times the image of l lies below the lower limit",
			"∀c:real. &0 < c ∧ c < &1 ⇒ extended_of_real(c) * extended_of_real(l) ≤ «liminf»",
			Derive(func(b *Argument) {
				c := b.FixAs[Real]("c")
				given := b.Conjuncts(
					b.Assume(),
					"c is positive",
					"c is below 1")
				N, near := b.ObtainAs[Nat](
					"past some N every term lies within l − c·l of l, c·l lying below l",
					"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < l - c * l",
					ByArith(
						converges,
						given[1],
						positive,
						real_order_ring.LessThanMulRight.At(c, b.TermAs[Real]("&1"), l),
						real_sequences.RealConvergesToDef.At(a, l)))
				tail := b.Have(
					"so the terms from N on exceed c·l, and so do their images",
					"∀n:num. extended_of_real(c * l) ≤ extended_of_real(a(N + n))",
					Derive(func(d *Argument) {
						d.FixAs[Nat]("n")
						late := d.TermAs[Nat]("N + n")
						d.Show(
							"a(N + n) is positive, so the embedding compares it with c·l as reals",
							ByArith(near.At(late), given[0], positive, OfRealLe.At(d.TermAs[Real]("c * l"), a.Apply(late))))
					}))
				belowLiminf := b.Have(
					"so the image of c·l lies below the infimum of the tail from N, and so below the lower limit",
					"extended_of_real(c * l) ≤ «liminf»",
					Unfold(ExtendedLiminfDef),
					By(
						tail,
						InfSequenceGreatest.At(
							b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_of_real(a(N + n))"),
							b.TermAs[ExtendedNonnegReal]("extended_of_real(c * l)")),
						SupSequenceUpper.At(
							b.TermAs[Fun[Nat, ExtendedNonnegReal]](
								"λk:num. extended_inf(image(λn:num. extended_of_real(a(k + n)), 𝕌))"),
							N),
						LeTrans))
				b.Show(
					"c times the image of l is the image of c·l",
					ByArith(belowLiminf, given[0], positive, OfRealMul.At(c, l)))
			}))
		arg.Show(
			"every c below 1 doing so, the image of l lies below the lower limit",
			By(scaled, LeOfScaledLe.At(arg.TermAs[ExtendedNonnegReal]("extended_of_real(l)"), liminf)))
	}),
})}
