// order.go — card_le as a preorder and card_eq as an equivalence, the
// strict order composing with the preorder on either side, what an
// inclusion or a map says about size, and the room a strictly smaller
// set leaves outside it in a type whose pairs inject into it.

package cardinal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// CardLeRefl — every set is no larger than itself: the identity sends
// it into itself and identifies nothing.
var CardLeRefl = cardLeReflThm{family.Add(registry.ProofEntry{
	Name: "CardLeRefl",
	Key:  "prop_d8a9609369d81d70",
	Build: family.Theorem("∀s:set(A). card_le(s, s)",
		Opening(Chain(
			Unfold(CardLeDef), Unfold(functions.InjectiveOnDef)), func(a *Argument, s *Expr[Set[A]]) {
			a.Take(a.Term("λx:A. x"))
			a.Show(
				"the identity keeps every point where it is — once it is taken, a tautology",
				TrivialNormalized())
		})),
})}

// CardLeTrans — no larger than no larger is no larger: an injection of
// s into t followed by one of t into u is an injection of s into u.
var CardLeTrans = cardLeTransThm{family.Add(registry.ProofEntry{
	Name: "CardLeTrans",
	Key:  "prop_9b438f994c66e6e0",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀t:set(B). ∀u:set(C).",
		Hypotheses: []string{
			"card_le(s, t)",
			"card_le(t, u)",
		},
		Conclusion: "card_le(s, u)",
	},
		Opening(Chain(
			Unfold(CardLeDef),
			Unfold(
				functions.InjectiveOnDef)), func(
			a *Argument,
			s *Expr[Set[A]],
			t *Expr[Set[B]],
			u *Expr[Set[C]],
			both Fact,
		) {
			le := a.Conjuncts(
				both,
				"some f sends s into t injectively",
				"some g sends t into u injectively")
			sToT, tToU := le[0], le[1]
			_, fInjects := a.Unpack(sToT, "f")
			_, gInjects := a.Unpack(tToU, "g")
			a.Take(a.Term("λx:A. g(f(x))"))
			a.Show(
				"g after f sends s into u, and two points it identifies "+
					"were identified by g at points of t, hence by f",
				By(fInjects, gInjects))
		})),
})}

// CardLeSubset — a subset is no larger than the set containing it: the
// identity sends it in.
var CardLeSubset = cardLeSubsetThm{family.Add(registry.ProofEntry{
	Name: "CardLeSubset",
	Key:  "prop_cc10bbb3d646e0fc",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"s ⊆ t",
		},
		Conclusion: "card_le(s, t)",
	},
		Opening(Chain(
			Unfold(CardLeDef),
			Unfold(functions.InjectiveOnDef)), func(a *Argument, s, t *Expr[Set[A]], sInT Fact) {
			a.Take(a.Term("λx:A. x"))
			a.Show(
				"the identity sends each point of s to itself, a point of t",
				BySets(sInT))
		})),
})}

// CardEqRefl — every set is the same size as itself: the identity is a
// bijection of it onto itself.
var CardEqRefl = cardEqReflThm{family.Add(registry.ProofEntry{
	Name: "CardEqRefl",
	Key:  "prop_f5c2eb3298ab0684",
	Build: family.Theorem("∀s:set(A). card_eq(s, s)",
		Opening(Chain(
			Unfold(CardEqDef), Unfold(functions.InjectiveOnDef)), func(a *Argument, s *Expr[Set[A]]) {
			a.Take(a.Term("λx:A. x"))
			a.Show(
				"the identity keeps every point where it is, and each point of s is its own image",
				BySets())
		})),
})}

// CardEqImpLe — sets of the same size are each no larger than the
// other's: a bijection of s onto t is in particular an injection of s
// into t.
var CardEqImpLe = cardEqImpLeThm{family.Add(registry.ProofEntry{
	Name: "CardEqImpLe",
	Key:  "prop_168fcf88243c7d2a",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀t:set(B).",
		Hypotheses: []string{
			"card_eq(s, t)",
		},
		Conclusion: "card_le(s, t)",
	},
		Opening(Chain(
			Unfold(CardEqDef),
			Unfold(CardLeDef)), func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]], bijection Fact) {
			f, fBijective := a.Unpack(bijection, "f")
			a.Take(f)
			a.Show(
				"forget that f reaches every point of t: its image being t, it sends s there",
				BySets(fBijective))
		})),
})}

// CardLtLeTrans — strictly smaller, then no larger, is strictly
// smaller: s ≤ t ≤ u gives s ≤ u, and u ≤ s would give t ≤ u ≤ s.
var CardLtLeTrans = cardLtLeTransThm{family.Add(registry.ProofEntry{
	Name: "CardLtLeTrans",
	Key:  "prop_bf23a8cd6f09695c",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀t:set(B). ∀u:set(C).",
		Hypotheses: []string{
			"card_lt(s, t)",
			"card_le(t, u)",
		},
		Conclusion: "card_lt(s, u)",
	},
		Opening(Unfold(
			CardLtDef), func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]], u *Expr[Set[C]], h Fact) {
			a.Show(
				"s ≤ t ≤ u; and u ≤ s would put t ≤ u ≤ s",
				By(h, CardLeTrans.At(s, t, u), CardLeTrans.At(t, u, s)))
		})),
})}

// CardLeLtTrans — no larger, then strictly smaller, is strictly
// smaller: s ≤ t ≤ u gives s ≤ u, and u ≤ s would give u ≤ s ≤ t.
var CardLeLtTrans = cardLeLtTransThm{family.Add(registry.ProofEntry{
	Name: "CardLeLtTrans",
	Key:  "prop_dd2a591b324c0286",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀t:set(B). ∀u:set(C).",
		Hypotheses: []string{
			"card_le(s, t)",
			"card_lt(t, u)",
		},
		Conclusion: "card_lt(s, u)",
	},
		Opening(Unfold(
			CardLtDef), func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]], u *Expr[Set[C]], h Fact) {
			a.Show(
				"s ≤ t ≤ u; and u ≤ s would put u ≤ s ≤ t",
				By(h, CardLeTrans.At(s, t, u), CardLeTrans.At(u, s, t)))
		})),
})}

// CardLeCover — the surjective reading of ≤. An injection f of s into t
// has a left inverse g on s, and g covers s: each x ∈ s is g's value at
// f(x), a point of t. Conversely, when g covers s, choose for each
// x ∈ s a source h(x) ∈ t that g sends back to x; h sends s into t, and
// it identifies no two points of s, because g recovers each point from
// its value. Both directions choose: g by the left-inverse law of the
// functions chapter, h one source per point of s. No guard is needed: an
// empty s is covered and injected by any map, and a nonempty s is
// neither when t is empty.
var CardLeCover = cardLeCoverThm{family.Add(registry.ProofEntry{
	Name: "CardLeCover",
	Key:  "prop_238cce38d8c2d2a5",
	Build: family.Theorem("∀s:set(A). ∀t:set(B). card_le(s, t) ⇔ ∃g:(B → A). s ⊆ image(g, t)",
		Opening(Unfold(CardLeDef), func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]]) {
			a.Iff()
			a.Forward(
				"a left inverse of an injection covers the injected set",
				func(a *Argument, injection Fact) {
					_, fInjects := a.Unpack(injection, "f")
					parts := a.Conjuncts(
						fInjects,
						"f sends s into t",
						"f identifies no two points of s")
					into, oneToOne := parts[0], parts[1]
					g, undoes := a.Obtain(
						"f identifies no two points of s, so some g undoes it there",
						"∃g:(B → A). ∀x:A. x ∈ s ⇒ g(f(x)) = x",
						By(oneToOne, functions.InjectiveOnLeftInverse))
					a.Take(g)
					a.Show(
						"each x ∈ s is g's value at f(x), a point of t",
						BySets(into, undoes))
				})
			a.Backward(
				"a choice of sources for a cover is an injection",
				func(a *Argument, cover Fact) {
					_, covered := a.Unpack(cover, "g")
					h, picked := a.Obtain(
						"g reaches each point of s from t, so pick a source h(x) ∈ t for each x ∈ s",
						"∃h:(A → B). ∀x:A. x ∈ s ⇒ h(x) ∈ t ∧ g(h(x)) = x",
						BySets(covered))
					a.Take(h)
					a.Show(
						"h sends s into t, and g(h(x)) = x recovers x from h(x)",
						Simp(Fwd(functions.InjectiveOnDef)),
						By(picked))
				})
		})),
})}

// CardEqSym — being the same size is symmetric: a bijection of s onto t
// has a two-sided inverse on t, and the inverse is a bijection of t onto
// s.
var CardEqSym = cardEqSymThm{family.Add(registry.ProofEntry{
	Name: "CardEqSym",
	Key:  "prop_4066e45cbb493d08",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀t:set(B).",
		Hypotheses: []string{
			"card_eq(s, t)",
		},
		Conclusion: "card_eq(t, s)",
	},
		Opening(Unfold(CardEqDef), func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]], bijection Fact) {
			f, fBijective := a.UnpackAs[Fun[A, B]](bijection, "f")
			fClause := a.Conjuncts(
				fBijective,
				"f identifies no two points of s",
				"f carries s onto t")
			fOneToOne, fImage := fClause[0], fClause[1]
			// The image equation read as the two inclusions the inverse
			// law asks for.
			fInto := a.Have(
				"f sends s into t",
				"∀x:A. x ∈ s ⇒ f(x) ∈ t",
				BySets(fImage))
			fOnto := a.Have(
				"f reaches every point of t",
				"∀y:B. y ∈ t ⇒ ∃x:A. x ∈ s ∧ f(x) = y",
				BySets(fImage))
			// The claim keeps the grouping BijectiveOnLeftRightInverse states.
			g, inverse := a.ObtainAs[Fun[B, A]](
				"f has a two-sided inverse g on t",
				"∃g:(B → A). (∀y. y ∈ t ⇒ g(y) ∈ s) ∧ ((∀y. y ∈ t ⇒ f(g(y)) = y) ∧ (∀x. x ∈ s ⇒ g(f(x)) = x))",
				By(fInto, fOneToOne, fOnto, functions.BijectiveOnLeftRightInverse.At(f, s, t)))
			gClause := a.Conjuncts(
				inverse,
				"g sends t into s",
				"f undoes g on t",
				"g undoes f on s")
			gInto, fUndoesG, gUndoesF := gClause[0], gClause[1], gClause[2]
			oneToOne := a.Have(
				"g identifies no two points of t: g(y) = g(z) gives y = f(g(y)) = f(g(z)) = z",
				"injective_on(t, g)",
				Derive(func(b *Argument) {
					// Claimed of pairs of points of t.
					b.Do(Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[B](), TypeBinder.BindB[A]()))))
					y, z := b.FixAs[B]("y"), b.FixAs[B]("z")
					b.Show(
						"f undoes g at y and at z",
						By(fUndoesG.At(y), fUndoesG.At(z)))
				}))
			onto := a.Have(
				"g reaches every point of s",
				"∀x:A. x ∈ s ⇒ ∃y:B. y ∈ t ∧ g(y) = x",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					b.Take(b.TermAs[B]("f(x)"))
					b.Show(
						"f(x) is in t, and g takes it back to x",
						By(xIn, fInto.At(x), gUndoesF.At(x)))
				}))
			a.Take(g)
			a.Show(
				"g is a bijection of t onto s: injective there, and its image of t is s",
				BySets(gInto, oneToOne, onto))
		})),
})}

// CardEqTrans — being the same size is transitive: a bijection of s
// onto t followed by one of t onto u is a bijection of s onto u.
var CardEqTrans = cardEqTransThm{family.Add(registry.ProofEntry{
	Name: "CardEqTrans",
	Key:  "prop_a860814d1339a5ea",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀t:set(B). ∀u:set(C).",
		Hypotheses: []string{
			"card_eq(s, t)",
			"card_eq(t, u)",
		},
		Conclusion: "card_eq(s, u)",
	},
		Opening(Chain(
			Unfold(CardEqDef),
			Unfold(
				functions.InjectiveOnDef)), func(
			a *Argument,
			s *Expr[Set[A]],
			t *Expr[Set[B]],
			u *Expr[Set[C]],
			both Fact,
		) {
			eq := a.Conjuncts(
				both,
				"some f is a bijection of s onto t",
				"some g is a bijection of t onto u")
			sToT, tToU := eq[0], eq[1]
			_, fBijective := a.Unpack(sToT, "f")
			_, gBijective := a.Unpack(tToU, "g")
			a.Take(a.Term("λx:A. g(f(x))"))
			a.Show(
				"g after f identifies no two points of s, and its image of s is g's image of t, which is u",
				BySets(fBijective, gBijective))
		})),
})}

// CardLeImage — the image of a set is no larger than the set: the map
// itself covers its image, which is the surjective reading of ≤.
var CardLeImage = cardLeImageThm{family.Add(registry.ProofEntry{
	Name: "CardLeImage",
	Key:  "prop_1a4d77093e103601",
	Build: family.Theorem("∀f:(A → B). ∀s:set(A). card_le(image(f, s), s)",
		func(a *Argument, f *Arrow[A, B], s *Expr[Set[A]]) {
			covered := a.Have(
				"f itself covers its image",
				"∃g:(A → B). image(f, s) ⊆ image(g, s)",
				Derive(func(b *Argument) {
					b.Take(f)
					b.Show(
						"image(f, s) ⊆ image(f, s)",
						BySets())
				}))
			a.Show(
				"so the image is no larger than s",
				By(covered, CardLeCover.At(a.TermAs[Set[B]]("image(f, s)"), s)))
		}),
})}

// CardLeProduct — sizes multiply under the cartesian product: an
// injection of s into s' beside one of t into t' is an injection of the
// pairs of s and t into the pairs of s' and t', acting on each component.
var CardLeProduct = cardLeProductThm{family.Add(registry.ProofEntry{
	Name: "CardLeProduct",
	Key:  "prop_4de18a63e1047155",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀s':set(B). ∀t:set(C). ∀t':set(D).",
		Hypotheses: []string{
			"card_le(s, s')",
			"card_le(t, t')",
		},
		Conclusion: "card_le(set_cross(s, t), set_cross(s', t'))",
	},
		func(
			a *Argument,
			s *Expr[Set[A]],
			sPrime *Expr[Set[B]],
			t *Expr[Set[C]],
			tPrime *Expr[Set[D]],
			bounds Fact,
		) {
			f, fInjects := a.ObtainAs[Fun[A, B]](
				"choose an injection of s into s'",
				"∃f:(A → B). (∀x:A. x ∈ s ⇒ f(x) ∈ s') ∧ injective_on(s, f)",
				By(bounds, CardLeDef.At(s, sPrime)))
			g, gInjects := a.ObtainAs[Fun[C, D]](
				"choose an injection of t into t'",
				"∃g:(C → D). (∀y:C. y ∈ t ⇒ g(y) ∈ t') ∧ injective_on(t, g)",
				By(bounds, CardLeDef.At(t, tPrime)))
			h, hDef := a.LetAs[Fun[Prod[A, C], Prod[B, D]]](
				"h", "λp:prod(A, C). (f(fst(p)), g(snd(p)))")
			into := a.Have(
				"h sends each source pair to a pair in the target product",
				"∀p:prod(A, C). p ∈ set_cross(s, t) ⇒ h(p) ∈ set_cross(s', t')",
				hDef.Rw(),
				By(
					fInjects,
					gInjects,
					At(set_product.InCrossProjections, s, t),
					At(set_product.InCross, sPrime, tPrime)))
			oneToOne := a.Have(
				"h identifies no two source pairs",
				"injective_on(set_cross(s, t), h)",
				hDef.Rw(),
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					x, y := b.FixAs[Prod[A, C]]("x"), b.FixAs[Prod[A, C]]("y")
					sameImage := b.Assume()
					b.Show(
						"equal image pairs have equal coordinates, so f and g recover both source coordinates",
						By(
							fInjects,
							gInjects,
							sameImage,
							functions.InjectiveOnDef.At(s, f),
							functions.InjectiveOnDef.At(t, g),
							set_product.InCrossProjections.At(s, t, x),
							set_product.InCrossProjections.At(s, t, y),
							pairs.PairEq.At(
								b.TermAs[B]("f(fst(x))"), b.TermAs[D]("g(snd(x))"),
								b.TermAs[B]("f(fst(y))"), b.TermAs[D]("g(snd(y))")),
							pairs.PairEta.At(x),
							pairs.PairEta.At(y)))
				}))
			a.Show(
				"h witnesses that the source product is no larger than the target product",
				Simp(Fwd(CardLeDef)),
				Derive(func(b *Argument) {
					b.Take(h)
					b.Show(
						"h maps into the target product and is injective on the source",
						By(into, oneToOne))
				}))
		}),
	Reading: "No inhabitation is asked: with s or t " +
		"empty the product is empty and every map injects it.",
})}

// ComplementRoom — when the pairs of points of A inject into A, a set L
// strictly smaller than A leaves room for all of A outside it: A injects
// into the points not in L. Let c code each pair (x, y) as one point
// c((x, y)); a code determines both coordinates, so the codes with first
// coordinate x form a block, a copy of A, and distinct x have disjoint
// blocks. Were every block to meet L, a point of L chosen in each block
// would send A into L injectively, against card_lt. So some block misses
// L, and y ↦ c((x, y)) along it is the injection.
var ComplementRoom = complementRoomThm{family.Add(registry.ProofEntry{
	Name: "ComplementRoom",
	Key:  "prop_625565cae20ea378",
	Build: family.Theorem(Statement{
		Binders: "∀L:set(A).",
		Hypotheses: []string{
			"card_le(𝕌⟨A:prod(A, A)⟩, 𝕌⟨A:A⟩)",
			"card_lt(L, 𝕌⟨A:A⟩)",
		},
		Conclusion: "card_le(𝕌⟨A:A⟩, {x:A | x ∉ L})",
	},
		func(a *Argument, L *Expr[Set[A]], pairsInto, smaller Fact) {
			points := a.TermAs[Set[A]]("𝕌⟨A:A⟩")
			pairsOfPoints := a.TermAs[Set[Prod[A, A]]]("𝕌⟨A:prod(A, A)⟩")

			// The code of a pair of points, and what a code determines.
			_, coding := a.ObtainAs[Fun[Prod[A, A], A]](
				"the pairs of points inject into the points: let c be such a coding",
				"∃c:(prod(A, A) → A). injective_on(𝕌⟨A:prod(A, A)⟩, c)",
				By(Normalized, pairsInto, CardLeDef.At(pairsOfPoints, points)))
			decode := a.Have(
				"a code determines its pair, and so both coordinates",
				"∀x₁ y₁ x₂ y₂:A. c((x₁, y₁)) = c((x₂, y₂)) ⇒ x₁ = x₂ ∧ y₁ = y₂",
				Derive(func(b *Argument) {
					x1, y1 := b.FixAs[A]("x₁"), b.FixAs[A]("y₁")
					x2, y2 := b.FixAs[A]("x₂"), b.FixAs[A]("y₂")
					injective := b.Unfolded(coding, functions.InjectiveOnDef)
					b.Show(
						"c tells the pairs apart, and equal pairs have equal coordinates",
						By(
							injective.At(b.TermAs[Prod[A, A]]("(x₁, y₁)"), b.TermAs[Prod[A, A]]("(x₂, y₂)")),
							pairs.PairEq.At(x1, y1, x2, y2),
							set_basic.InUniv))
				}))

			_, missed := a.ObtainAs[A](
				"some block misses L: an x whose codes c((x, y)) all lie outside L",
				"∃x:A. ∀y:A. c((x, y)) ∉ L",
				Derive(func(b *Argument) {
					everyBlockMeets := b.SupposeNot()
					_, chosen := b.ObtainAs[Fun[A, A]](
						"then every block meets L: choose for each x a y = τ(x) with c((x, τ(x))) ∈ L",
						"∃τ:(A → A). ∀x:A. c((x, τ(x))) ∈ L",
						By(everyBlockMeets))
					intoL := b.Have(
						"x ↦ c((x, τ(x))) sends A into L, and the code c((x, τ(x))) determines x",
						"card_le(𝕌⟨A:A⟩, L)",
						Unfold(CardLeDef),
						Derive(func(d *Argument) {
							d.Take(d.TermAs[Fun[A, A]]("λx:A. c((x, τ(x)))"))
							d.Show(
								"each chosen code lies in L, and equal codes have one first coordinate",
								Unfold(functions.InjectiveOnDef),
								By(decode, chosen))
						}))
					b.Show(
						"yet L is strictly smaller than A",
						By(intoL, smaller, CardLtDef.At(L, points)))
				}))

			a.Show(
				"along that block, y ↦ c((x, y)) carries A outside L, and the code c((x, y)) determines y",
				Unfold(CardLeDef),
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Fun[A, A]]("λy:A. c((x, y))"))
					b.Show(
						"no code of the block lies in L, and equal codes have one second coordinate",
						Unfold(functions.InjectiveOnDef),
						BySets(missed, decode))
				}))
		}),
	Reading: "Both hypotheses are load-bearing. Without the strict bound, L = all of A " +
		"but one point is no larger than A, and its complement is that one point; without " +
		"the pairs, at a type of two points L = one of them is strictly smaller than A, and " +
		"its complement is the other. At L = ∅ the conclusion is card_le of A into itself.",
})}
