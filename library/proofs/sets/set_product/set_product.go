// set_product.go — the product of two sets: membership read at a pair and at
// a point, the product against the other set operations, and its
// projections; and the diagonal of a set, membership read the same two
// ways, and the diagonal lying in the square.

package set_product

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Membership
// ---------------------------------------------------------------------------

// InCross — a pair lies in the product exactly when each component lies
// in its factor. Opened, the product is the set of pairs (a, b) with a ∈ s
// and b ∈ t, and (x, y) is such a pair exactly when x = a and y = b: pair
// injectivity leaves x and y themselves as the only witnesses.
var InCross = inCrossThm{family.Add(registry.ProofEntry{
	Name: "InCross",
	Key:  "prop_e6c606c3068414e4",
	Build: family.Theorem("∀s:set(A). ∀t:set(B). ∀x:A. ∀y:B. (x, y) ∈ set_cross(s, t) ⇔ x ∈ s ∧ y ∈ t",
		Opening(Unfold(SetCrossDef), BySets(pairs.PairEq))),
})}

// InCrossProjections — a point lies in the product exactly when its
// projections lie in the factors.
var InCrossProjections = inCrossProjectionsThm{family.Add(registry.ProofEntry{
	Name: "InCrossProjections",
	Key:  "prop_894cbbfad47802e7",
	Build: family.Theorem("∀s:set(A). ∀t:set(B). ∀p:prod(A, B). "+
		"    p ∈ set_cross(s, t) ⇔ fst(p) ∈ s ∧ snd(p) ∈ t",
		func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]], p *Expr[Prod[A, B]]) {
			a.Show(
				"p is the pair (fst(p), snd(p)), which lies in the product exactly when fst(p) ∈ s and snd(p) ∈ t",
				By(InCross.At(s, t, a.TermAs[A]("fst(p)"), a.TermAs[B]("snd(p)")), pairs.PairEta.At(p)))
		}),
})}

// InDiagonal — a pair lies on the diagonal exactly when its first
// component lies in the set and its second is the first. Opened, the
// diagonal is the set of pairs (a, a) with a ∈ s, and (x, y) is such a
// pair exactly when x = a and y = a.
var InDiagonal = inDiagonalThm{family.Add(registry.ProofEntry{
	Name: "InDiagonal",
	Key:  "prop_566ae0506b845fd7",
	Build: family.Theorem("∀s:set(A). ∀x y:A. (x, y) ∈ set_diagonal(s) ⇔ x ∈ s ∧ y = x",
		Opening(Unfold(SetDiagonalDef), BySets(pairs.PairEq))),
})}

// InDiagonalProjections — a point lies on the diagonal exactly when its
// first projection lies in the set and its second is the first.
var InDiagonalProjections = inDiagonalProjectionsThm{family.Add(registry.ProofEntry{
	Name: "InDiagonalProjections",
	Key:  "prop_8576d23c60a874f8",
	Build: family.Theorem("∀s:set(A). ∀p:prod(A, A). "+
		"    p ∈ set_diagonal(s) ⇔ fst(p) ∈ s ∧ snd(p) = fst(p)",
		func(a *Argument, s *Expr[Set[A]], p *Expr[Prod[A, A]]) {
			a.Show(
				"p is the pair (fst(p), snd(p)), which lies on the "+
					"diagonal exactly when fst(p) ∈ s and snd(p) = fst(p)",
				By(Normalized, InDiagonal.At(s, a.TermAs[A]("fst(p)"), a.TermAs[A]("snd(p)")), pairs.PairEta.At(p)))
		}),
})}

// DiagonalSubsetCross — the diagonal of a set lies in its square: a pair
// on the diagonal has its first component in the set and its second equal
// to the first.
var DiagonalSubsetCross = diagonalSubsetCrossThm{family.Add(registry.ProofEntry{
	Name: "DiagonalSubsetCross",
	Key:  "prop_9974eeeef268fbfb",
	Build: family.Theorem("∀s:set(A). set_diagonal(s) ⊆ set_cross(s, s)",
		func(a *Argument, s *Expr[Set[A]]) {
			a.Show(
				"a point on the diagonal has both its projections in s",
				BySets(At(InDiagonalProjections, s), At(InCrossProjections, s, s)))
		}),
})}

// ---------------------------------------------------------------------------
// The product and the set operations
// ---------------------------------------------------------------------------

// CrossEmptyIff — a product is empty exactly when a factor is.
var CrossEmptyIff = crossEmptyIffThm{family.Add(registry.ProofEntry{
	Name: "CrossEmptyIff",
	Key:  "prop_18e75301c38b4814",
	Build: family.Theorem("∀s:set(A). ∀t:set(B). set_cross(s, t) = ∅ ⇔ s = ∅ ∨ t = ∅",
		func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]]) {
			a.Show(
				"pointwise: a point of the product projects into each factor, "+
					"and a point of each factor pairs to a point of the product",
				BySets(At(InCross, s, t), At(InCrossProjections, s, t)))
		}),
})}

// CrossSubsetIff — a product lies in another exactly when it is empty
// or each factor lies in the other's.
var CrossSubsetIff = crossSubsetIffThm{family.Add(registry.ProofEntry{
	Name: "CrossSubsetIff",
	Key:  "prop_e1cb6f6a2ee6b98d",
	Build: family.Theorem("∀s u:set(A). ∀t v:set(B). "+
		"    set_cross(s, t) ⊆ set_cross(u, v) ⇔ s = ∅ ∨ t = ∅ ∨ (s ⊆ u ∧ t ⊆ v)",
		func(a *Argument, s, u *Expr[Set[A]], t, v *Expr[Set[B]]) {
			a.Iff()
			a.Forward(
				"the inclusion leaves a factor empty, or each factor inside the other's",
				func(b *Argument, inside Fact) {
					sInU := b.Have(
						"with t non-empty, a point of s paired with a point of t lies in set_cross(u, v), so in u",
						"¬(t = ∅) ⇒ s ⊆ u",
						BySets(inside, InCross))
					tInV := b.Have(
						"likewise, with s non-empty, a point of t paired "+
							"with a point of s lies in set_cross(u, v), so in v",
						"¬(s = ∅) ⇒ t ⊆ v",
						BySets(inside, InCross))
					// Normalized: over the atoms s = ∅, t = ∅, s ⊆ u and t ⊆ v,
					// each taken whole, the step is a propositional tautology,
					// and normalizing settles it as one.
					b.Show(
						"so a factor is empty, or each lies in the other's",
						By(Normalized, sInU, tInV))
				})
			a.Backward(
				"a point of the first product has its projections in s and t",
				func(b *Argument, either Fact) {
					b.Show(
						"so there is no such point when a factor is empty, and otherwise its projections lie in u and v",
						BySets(either, InCrossProjections))
				})
		}),
})}

// CrossInter — products meet factor by factor: a point lies in either side
// exactly when its first projection lies in s and u and its second in t and v.
var CrossInter = crossInterThm{family.Add(registry.ProofEntry{
	Name: "CrossInter",
	Key:  "prop_796385ab4db859a0",
	Build: family.Theorem(
		"∀s u:set(A). ∀t v:set(B). set_cross(s ∩ u, t ∩ v) = set_cross(s, t) ∩ set_cross(u, v)",
		BySets(InCrossProjections)),
})}

// CrossUnionLeft — a product distributes over a union in its first
// factor: a point lies in either side exactly when its first projection
// lies in s or u and its second in t.
var CrossUnionLeft = crossUnionLeftThm{family.Add(registry.ProofEntry{
	Name: "CrossUnionLeft",
	Key:  "prop_8524180309e02bcf",
	Build: family.Theorem(
		"∀s u:set(A). ∀t:set(B). set_cross(s ∪ u, t) = set_cross(s, t) ∪ set_cross(u, t)",
		BySets(InCrossProjections)),
})}

// CrossUnionRight — a product distributes over a union in its second
// factor: a point lies in either side exactly when its first projection
// lies in s and its second in t or v.
var CrossUnionRight = crossUnionRightThm{family.Add(registry.ProofEntry{
	Name: "CrossUnionRight",
	Key:  "prop_920585ef2652288d",
	Build: family.Theorem(
		"∀s:set(A). ∀t v:set(B). set_cross(s, t ∪ v) = set_cross(s, t) ∪ set_cross(s, v)",
		BySets(InCrossProjections)),
})}

// CrossDifference — a product less a product is two products: a point of
// the first lies outside the second exactly when its first projection lies
// outside u or its second outside v.
var CrossDifference = crossDifferenceThm{family.Add(registry.ProofEntry{
	Name: "CrossDifference",
	Key:  "prop_9f811d4a833eedf8",
	Build: family.Theorem(
		"∀s u:set(A). ∀t v:set(B). "+
			"    set_cross(s, t) ∖ set_cross(u, v) = set_cross(s ∖ u, t) ∪ set_cross(s, t ∖ v)",
		BySets(InCrossProjections)),
})}

// ---------------------------------------------------------------------------
// Projections
// ---------------------------------------------------------------------------

// ImageFstCross — the first projection of a product with a non-empty
// second factor is the first factor.
var ImageFstCross = imageFstCrossThm{family.Add(registry.ProofEntry{
	Name: "ImageFstCross",
	Key:  "prop_62eb231df8bfc67c",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀t:set(B).",
		Hypotheses: []string{
			"¬(t = ∅)",
		},
		Conclusion: "image(fst, set_cross(s, t)) = s",
	},
		func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]], nonEmpty Fact) {
			y0, inT := a.ObtainAs[B](
				"t is non-empty, so it has a point y₀",
				"∃y₀:B. y₀ ∈ t",
				By(nonEmpty, set_basic.MemberNotEmpty))
			below := a.Have(
				"the first projection of a point of the product lies in s",
				"image(fst, set_cross(s, t)) ⊆ s",
				BySets(At(InCrossProjections, s, t)))
			above := a.Have(
				"each x ∈ s is fst((x, y₀)), and (x, y₀) lies in the product as y₀ ∈ t",
				"s ⊆ image(fst, set_cross(s, t))",
				Unfold(set_basic.SubsetDef),
				a.ForEach(func(x *Expr[A]) Action {
					return BySets(inT, InCross.At(s, t, x, y0), pairs.Fst.At(x, y0))
				}))
			image := a.TermAs[Set[A]]("image(fst, set_cross(s, t))")
			a.Show(
				"each side lies in the other, so the image is s",
				By(set_order.SubsetAntisym.At(image, s), below, above))
		}),
})}

// ImageSndCross — the second projection of a product with a non-empty
// first factor is the second factor.
var ImageSndCross = imageSndCrossThm{family.Add(registry.ProofEntry{
	Name: "ImageSndCross",
	Key:  "prop_686ad4a1c21cc973",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀t:set(B).",
		Hypotheses: []string{
			"¬(s = ∅)",
		},
		Conclusion: "image(snd, set_cross(s, t)) = t",
	},
		func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]], nonEmpty Fact) {
			x0, inS := a.ObtainAs[A](
				"s is non-empty, so it has a point x₀",
				"∃x₀:A. x₀ ∈ s",
				By(nonEmpty, set_basic.MemberNotEmpty))
			below := a.Have(
				"the second projection of a point of the product lies in t",
				"image(snd, set_cross(s, t)) ⊆ t",
				BySets(At(InCrossProjections, s, t)))
			above := a.Have(
				"each y ∈ t is snd((x₀, y)), and (x₀, y) lies in the product as x₀ ∈ s",
				"t ⊆ image(snd, set_cross(s, t))",
				Unfold(set_basic.SubsetDef),
				a.ForEach(func(y *Expr[B]) Action {
					return BySets(inS, InCross.At(s, t, x0, y), pairs.Snd.At(x0, y))
				}))
			image := a.TermAs[Set[B]]("image(snd, set_cross(s, t))")
			a.Show(
				"each side lies in the other, so the image is t",
				By(set_order.SubsetAntisym.At(image, t), below, above))
		}),
})}

// CrossSwap — the product s × t is the product t × s with each pair's
// coordinates exchanged.
//
// Each side lies in the other. A point of the image is the swap of some
// q ∈ t × s, so what is asked is that (snd(q), fst(q)) lie in s × t,
// which is q's coordinates lying in t and s. And a point p of s × t is
// the swap of (snd(p), fst(p)), which lies in t × s for the same reason.
var CrossSwap = crossSwapThm{family.Add(registry.ProofEntry{
	Name: "CrossSwap",
	Key:  "prop_70c7d45ea30e38d5",
	Build: family.Theorem("∀s:set(A). ∀t:set(B). "+
		"    set_cross(s, t) = image(λq:prod(B, A). (snd(q), fst(q)), set_cross(t, s))",
		func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]]) {
			swap := a.TermAs[Fun[Prod[B, A], Prod[A, B]]]("λq:prod(B, A). (snd(q), fst(q))")
			flipped := a.TermAs[Set[Prod[B, A]]]("set_cross(t, s)")
			below := a.Have(
				"the swap of a point of t × s lies in s × t",
				"image(λq:prod(B, A). (snd(q), fst(q)), set_cross(t, s)) ⊆ set_cross(s, t)",
				// ↦ ∀q. q ∈ set_cross(t, s) ⇒ (snd(q), fst(q)) ∈ set_cross(s, t):
				// a property of every point of the image is one of every swap.
				Unfold(set_basic.SubsetDef),
				Simp(Fwd(set_image.ForallInImage)),
				Derive(func(b *Argument) {
					q := b.FixAs[Prod[B, A]]("q")
					b.Show(
						"q has its coordinates in t and s, so (snd(q), fst(q)) has them in s and t",
						By(InCrossProjections.At(t, s, q), InCross.At(s, t, b.TermAs[A]("snd(q)"), b.TermAs[B]("fst(q)"))))
				}))
			above := a.Have(
				"each p ∈ s × t is the swap of (snd(p), fst(p)), a point of t × s",
				"set_cross(s, t) ⊆ image(λq:prod(B, A). (snd(q), fst(q)), set_cross(t, s))",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[A, B]]("p")
					inProduct := b.Assume()
					first, second := b.TermAs[A]("fst(p)"), b.TermAs[B]("snd(p)")
					inFlipped := b.Have(
						"(snd(p), fst(p)) lies in t × s, p's coordinates lying in s and t",
						"(snd(p), fst(p)) ∈ set_cross(t, s)",
						By(inProduct, InCrossProjections.At(s, t, p), InCross.At(t, s, second, first)))
					b.Show(
						"and its swap is (fst(p), snd(p)), which is p",
						By(
							inFlipped,
							set_image.FunInImage.At(swap, flipped, b.TermAs[Prod[B, A]]("(snd(p), fst(p))")),
							pairs.Fst.At(second, first),
							pairs.Snd.At(second, first),
							pairs.PairEta.At(p)))
				}))
			product := a.TermAs[Set[Prod[A, B]]]("set_cross(s, t)")
			image := a.TermAs[Set[Prod[A, B]]]("image(λq:prod(B, A). (snd(q), fst(q)), set_cross(t, s))")
			a.Show(
				"each side lies in the other, so the two are one set",
				By(set_order.SubsetAntisym.At(product, image), below, above))
		}),
})}
