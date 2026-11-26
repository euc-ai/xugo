// schroeder_bernstein.go — the Schröder–Bernstein theorem: two sets
// each no larger than the other are the same size. Two injections
// facing each other, and a set fixed by the map X ↦ g(t ∖ f(s ∖ X)),
// join the two sets point for point; Knaster–Tarski supplies the set.

package cardinal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// SchroederBernsteinBijection — the map h that undoes g on u and follows
// f off u is a bijection of s onto t. The fixed point says that u is g's
// image of the part of t that f misses from s ∖ u, so h carries u onto
// that part and s ∖ u onto the rest of t, which f reaches. The two parts
// of t are disjoint and cover it, and h identifies no two points within
// either piece: on u because g undoes h there, off u because h is f.
var SchroederBernsteinBijection = schroederBernsteinBijectionThm{family.Add(registry.ProofEntry{
	Name: "SchroederBernsteinBijection",
	Key:  "prop_c4b597ac9500a46e",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀t:set(B). ∀f:(A → B). ∀g:(B → A). ∀u:set(A).",
		Hypotheses: []string{
			"∀x:A. x ∈ s ⇒ f(x) ∈ t",
			"injective_on(s, f)",
			"∀y:B. y ∈ t ⇒ g(y) ∈ s",
			"injective_on(t, g)",
			"image(g, t ∖ image(f, s ∖ u)) = u",
		},
		Conclusion: "card_eq(s, t)",
	},
		Opening(Unfold(CardEqDef), func(
			a *Argument,
			s *Expr[Set[A]],
			t *Expr[Set[B]],
			f *Arrow[A, B],
			g *Arrow[B, A],
			u *Expr[Set[A]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"f sends s into t",
				"f identifies no two points of s",
				"g sends t into s",
				"g identifies no two points of t",
				"u is fixed by X ↦ g(t ∖ f(s ∖ X))")
			fInto, fOneToOne, gInto, gOneToOne, fixed := given[0], given[1], given[2], given[3], given[4]
			// f's injectivity is spent at a pair of points, below.
			fOneToOneAtPoints := a.Unfolded(fOneToOne, functions.InjectiveOnDef)

			// The one choice in the argument.
			_, undoes := a.Obtain(
				"g identifies no two points of t, so some k undoes it there",
				"∃k:(A → B). ∀y:B. y ∈ t ⇒ k(g(y)) = y",
				By(gOneToOne, functions.InjectiveOnLeftInverse))

			// The fixed point, read as the two inclusions it is.
			missedIntoU := a.Have(
				"g carries the points of t that f does not reach from s ∖ u into u",
				"∀y:B. y ∈ t ∧ y ∉ image(f, s ∖ u) ⇒ g(y) ∈ u",
				BySets(fixed))
			kOnU := a.Have(
				"each x of u is g of a point of t that f does not reach from s ∖ u, and that point is k(x)",
				"∀x:A. x ∈ u ⇒ k(x) ∈ t ∧ k(x) ∉ image(f, s ∖ u) ∧ g(k(x)) = x",
				BySets(fixed, undoes))

			// h, the map that undoes g on u and follows f off u, read at a
			// point x of s in the two facts below.
			into := a.Have(
				"h sends s into t",
				"∀x:A. x ∈ s ⇒ COND(x ∈ u, k(x), f(x)) ∈ t",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xInS := b.Assume()
					b.Cases(b.TermAs[Bool]("x ∈ u"))
					b.When(
						"on u, h(x) = k(x): the point of t that g sends to x",
						func(c *Argument, onU Fact) {
							c.Show(
								"k(x) lies in t",
								By(onU, kOnU.At(x)))
						})
					b.Otherwise(
						"off u, h(x) = f(x), and f sends s into t",
						func(c *Argument, offU Fact) {
							c.Show(
								"f(x) lies in t",
								By(offU, xInS, fInto.At(x)))
						})
				}))
			reaches := a.Have(
				"h reaches every point of t",
				"∀y:B. y ∈ t ⇒ ∃x:A. x ∈ s ∧ COND(x ∈ u, k(x), f(x)) = y",
				Derive(func(b *Argument) {
					y := b.FixAs[B]("y")
					yInT := b.Assume()
					b.Cases(b.TermAs[Bool]("y ∈ image(f, s ∖ u)"))
					b.When(
						"f reaches y from s ∖ u, and h is f there",
						func(c *Argument, reached Fact) {
							w, from := c.Obtain(
								"y = f(w) for a point w of s off u",
								"∃w:A. w ∈ s ∧ w ∉ u ∧ y = f(w)",
								BySets(reached))
							c.Take(w)
							c.Show(
								"h(w) = f(w) = y",
								By(from))
						})
					b.Otherwise(
						"f misses y from s ∖ u, so h reaches y from g(y), a point of u",
						func(c *Argument, missed Fact) {
							gyInU := c.Have(
								"the fixed point puts g(y) in u",
								"g(y) ∈ u",
								By(missed, yInT, missedIntoU.At(y)))
							c.Take(g.Apply(y))
							c.Show(
								"g(y) lies in s, and h(g(y)) = k(g(y)) = y",
								By(gyInU, yInT, gInto.At(y), undoes.At(y)))
						})
				}))

			h := a.TermAs[Fun[A, B]]("λx:A. COND(x ∈ u, k(x), f(x))")
			a.Take(h)
			a.Do(SplitConj(
				Case(
					"h identifies no two points of s",
					Simp(Fwd(functions.InjectiveOnDef)),
					Derive(func(b *Argument) {
						x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
						collide := b.Assume()
						sameSide := b.Have(
							"the fixed point against f: h puts a point of u outside f(s ∖ "+
								"u), a point of s off u inside it — so x, y share a side of u",
							"x ∈ u ⇔ y ∈ u",
							BySets(collide, kOnU.At(x), kOnU.At(y)))
						b.Cases(b.TermAs[Bool]("x ∈ u"))
						b.When(
							"both in u, where h is k: k(x) = h(x) = h(y) = k(y), and g undoes k",
							func(c *Argument, onU Fact) {
								c.Show(
									"x = g(k(x)) = g(k(y)) = y",
									By(onU, sameSide, collide, kOnU.At(x), kOnU.At(y)))
							})
						b.Otherwise(
							"both off u, where h is f, and f identifies no two points of s",
							func(c *Argument, offU Fact) {
								c.Show(
									"f(x) = f(y), so x = y",
									By(offU, sameSide, collide, fOneToOneAtPoints.At(x, y)))
							})
					})),
				Case(
					"and h carries s onto t: it sends s there and reaches every point of it",
					BySets(into, reaches)),
			))
		})),
})}

// SchroederBernstein — two sets each no larger than the other are the
// same size, and conversely. Given injections f of s into t and g of t
// into s, the map X ↦ g(t ∖ f(s ∖ X)) is monotone, so by Knaster–Tarski
// it fixes the intersection u of the sets it shrinks, and f and g
// joined at a fixed point are a bijection (SchroederBernsteinBijection).
// Conversely a bijection of s onto t injects s into t, and its inverse
// injects t into s.
var SchroederBernstein = schroederBernsteinThm{family.Add(registry.ProofEntry{
	Name: "SchroederBernstein",
	Key:  "prop_5e1b24c9ff7fa2ba",
	Build: family.Theorem("∀s:set(A). ∀t:set(B). card_le(s, t) ∧ card_le(t, s) ⇔ card_eq(s, t)",
		func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]]) {
			a.Iff()
			a.Forward(
				"injections facing each other are joined at a fixed point",
				func(a *Argument, both Fact) {
					// Only the hypothesis is opened: card_eq stays folded, as the
					// core's conclusion and the Backward branch read it.
					injections := a.Conjuncts(
						a.Unfolded(both, CardLeDef),
						"some f sends s into t, identifying no two points of s",
						"some g sends t into s, identifying no two points of t")
					sToT, tToS := injections[0], injections[1]
					f, fInjects := a.UnpackAs[Fun[A, B]](sToT, "f")
					g, gInjects := a.UnpackAs[Fun[B, A]](tToS, "g")
					F := a.TermAs[Fun[Set[A], Set[A]]]("λX:set(A). image(g, t ∖ image(f, s ∖ X))")
					monotone := a.Have(
						"X ↦ g(t ∖ f(s ∖ X)) is monotone: a larger X leaves less of "+
							"s ∖ X, so f reaches less of t and g carries more of the rest",
						"∀X Y:set(A). X ⊆ Y ⇒ image(g, t ∖ image(f, s ∖ X)) ⊆ image(g, t ∖ image(f, s ∖ Y))",
						BySets())
					u, uDef := a.LetAs[Set[A]]("u", "⋂{b:set(A) | image(g, t ∖ image(f, s ∖ b)) ⊆ b}")
					fixed := a.Have(
						"u, the intersection of the sets the map shrinks, "+
							"is fixed by it: Knaster–Tarski at the monotone map",
						"image(g, t ∖ image(f, s ∖ u)) = u",
						uDef.Rw(),
						By(monotone, set_order.KnasterTarski.At(F)))
					a.Show(
						"f and g, joined at the fixed point u, give a bijection of s onto t",
						By(fInjects, gInjects, fixed, SchroederBernsteinBijection.At(s, t, f, g, u)))
				})
			a.Backward(
				"a bijection is an injection, and so is its inverse",
				func(a *Argument, bijection Fact) {
					a.Show(
						"s ≤ t by the bijection, t ≤ s by its inverse",
						By(bijection, CardEqImpLe.At(s, t), CardEqSym.At(s, t), CardEqImpLe.At(t, s)))
				})
		}),
})}
