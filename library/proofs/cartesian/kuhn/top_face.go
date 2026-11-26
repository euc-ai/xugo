// top_face.go — the top face of the cube one dimension up: a grid point
// raised to coordinate n in dimension n + 1, a point truncated back to its
// first n coordinates, Kuhn's order under both, and the faces of the
// (n + 1)-simplices lying in the plane x(n) = p, which are exactly the
// raised n-simplices.

package kuhn

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/carrier"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Raising and truncating a point
// ---------------------------------------------------------------------------

// KuhnGridExtend — a grid point given a value q ≤ p at coordinate n is a
// grid point one dimension up, and truncating it to n coordinates gives the
// point back: past n the point is junk already, below n nothing moves.
var KuhnGridExtend = kuhnGridExtendThm{family.Add(registry.ProofEntry{
	Name: "KuhnGridExtend",
	Key:  "prop_2ba77eea97f46637",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num. ∀x:(num → num). ∀q:num.",
		Hypotheses: []string{
			"x ∈ kuhn_grid(p, n)",
			"q ≤ p",
		},
		Conclusion: "(λi:num. COND(i = n, q, x(i))) ∈ kuhn_grid(p, n + 1) ∧ " +
			"tuple_take(n, λi:num. COND(i = n, q, x(i))) = x",
	}, func(a *Argument, p, n *Expr[Nat], x *Arrow[Nat, Nat], q *Expr[Nat], inGrid, qLe Fact) {
		parts := a.Conjuncts(
			a.Unfolded(inGrid, KuhnGridDef),
			"x is an n-tuple",
			"its first n coordinates are at most p")
		junkPast := a.Unfolded(parts[0], carrier.TupleDef)
		extended := a.TermAs[Fun[Nat, Nat]]("λi:num. COND(i = n, q, x(i))")
		tuple := a.Have(
			"the extended point is an (n + 1)-tuple: past n it is x, junk there",
			"tuple(n + 1, λi:num. COND(i = n, q, x(i)))",
			Unfold(carrier.TupleDef),
			ByArith(junkPast))
		bounded := a.Have(
			"its first n + 1 coordinates are at most p: q at n, x(i) below",
			"∀i:num. i < n + 1 ⇒ COND(i = n, q, x(i)) ≤ p",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				below := b.Assume()
				b.Show(
					"q ≤ p at n, and x(i) ≤ p for i < n",
					CondRewrite(),
					ByArith(parts[1].At(i), below, qLe))
			}))
		agree := a.Have(
			"below n the extended point is x",
			"∀i:num. i < n ⇒ COND(i = n, q, x(i)) = x(i)",
			ByArith())
		a.Show(
			"so the extension lies in the grid, and truncation returns x",
			Unfold(KuhnGridDef),
			By(bounded, tuple, agree, parts[0], carrier.TakeUnique.At(n, extended, x)))
	}),
})}

// KuhnGridTake — a grid point one dimension up truncates to a grid point,
// and putting its coordinate n back gives the point: the truncation is the
// point below n and junk from n on, where the point is junk past n.
var KuhnGridTake = kuhnGridTakeThm{family.Add(registry.ProofEntry{
	Name: "KuhnGridTake",
	Key:  "prop_e89588eeaad2e4e0",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num. ∀y:(num → num).",
		Hypotheses: []string{
			"y ∈ kuhn_grid(p, n + 1)",
		},
		Conclusion: "tuple_take(n, y) ∈ kuhn_grid(p, n) ∧ " +
			"(λi:num. COND(i = n, y(n), tuple_take(n, y, i))) = y",
	}, func(a *Argument, p, n *Expr[Nat], y *Arrow[Nat, Nat], inGrid Fact) {
		parts := a.Conjuncts(
			a.Unfolded(inGrid, KuhnGridDef),
			"y is an (n + 1)-tuple",
			"its first n + 1 coordinates are at most p")
		junkPast := a.Unfolded(parts[0], carrier.TupleDef)
		bounded := a.Have(
			"the truncation's first n coordinates are y's, at most p",
			"∀i:num. i < n ⇒ tuple_take(n, y, i) ≤ p",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				below := b.Assume()
				b.Show(
					"below n the truncation reads y",
					Unfold(carrier.TupleTakeDef),
					ByArith(parts[1].At(i), below))
			}))
		restored := a.Have(
			"coordinate by coordinate, y(n) at n, y below n and junk past n are y",
			"∀i:num. COND(i = n, y(n), tuple_take(n, y, i)) = y(i)",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				b.Show(
					"y(n) at n, y(i) below n, and junk past n, where y is junk too",
					Unfold(carrier.TupleTakeDef),
					CondRewrite(),
					ByArith(junkPast.At(i)))
			}))
		a.Show(
			"so the truncation lies in the grid, and restoring coordinate n gives y",
			Unfold(KuhnGridDef),
			By(bounded, restored, carrier.TakeClosed.At(n, y)))
	}),
})}

// ---------------------------------------------------------------------------
// Kuhn's order one dimension up and down
// ---------------------------------------------------------------------------

// KuhnLeExtend — two comparable points stay comparable one dimension up
// when their new coordinates n are q ≤ r ≤ q + 1: below n the order is
// theirs, at n it is the step from q to r, and past n both are unchanged.
var KuhnLeExtend = kuhnLeExtendThm{family.Add(registry.ProofEntry{
	Name: "KuhnLeExtend",
	Key:  "prop_6dd82ed22608a94b",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀x y:(num → num). ∀q r:num.",
		Hypotheses: []string{
			"kuhn_le(n, x, y)",
			"q ≤ r",
			"r ≤ q + 1",
		},
		Conclusion: "kuhn_le(n + 1, λi:num. COND(i = n, q, x(i)), λi:num. COND(i = n, r, y(i)))",
	}, func(a *Argument, n *Expr[Nat], x, y *Arrow[Nat, Nat], q, r *Expr[Nat], below, qr, rq Fact) {
		order := a.Unfolded(below, KuhnLeDef)
		a.Show(
			"coordinate by coordinate: x and y below n, q and r at n, equal past n",
			Unfold(KuhnLeDef),
			a.ForEach(func(i *Expr[Nat]) Action {
				return Chain(CondRewrite(), ByArith(order.At(i), qr, rq))
			}))
	}),
})}

// KuhnLeTake — Kuhn's order one dimension up survives truncation to the
// first n coordinates: below n the coordinates are the points', from n on
// both truncations are junk.
var KuhnLeTake = kuhnLeTakeThm{family.Add(registry.ProofEntry{
	Name: "KuhnLeTake",
	Key:  "prop_61a0d6df24fa0919",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀x y:(num → num).",
		Hypotheses: []string{
			"kuhn_le(n + 1, x, y)",
		},
		Conclusion: "kuhn_le(n, tuple_take(n, x), tuple_take(n, y))",
	}, func(a *Argument, n *Expr[Nat], x, y *Arrow[Nat, Nat], below Fact) {
		order := a.Unfolded(below, KuhnLeDef)
		a.Show(
			"coordinate by coordinate: x and y below n, junk from n on",
			Unfold(KuhnLeDef),
			a.ForEach(func(i *Expr[Nat]) Action {
				return Chain(Unfold(carrier.TupleTakeDef), CondRewrite(), ByArith(order.At(i)))
			}))
	}),
})}

// ---------------------------------------------------------------------------
// The faces in the plane x(n) = p
// ---------------------------------------------------------------------------

// KuhnTopFaceTruncation — a face of an (n + 1)-simplex lying in the plane
// x(n) = p, truncated to its first n coordinates, is an n-simplex, and
// raising it to x(n) = p gives the face back: truncation is one-to-one on
// the face and keeps its points comparable.
var KuhnTopFaceTruncation = kuhnTopFaceTruncationThm{family.Add(registry.ProofEntry{
	Name: "KuhnTopFaceTruncation",
	Key:  "prop_ab9a2d8ce0fdfb21",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num. ∀s:set(num → num). ∀a:(num → num).",
		Hypotheses: []string{
			"kuhn_simplex(p, n + 1, s)",
			"a ∈ s",
			"∀x:(num → num). x ∈ delete(s, a) ⇒ x(n) = p",
		},
		Conclusion: "kuhn_simplex(p, n, image(tuple_take(n), delete(s, a))) ∧ " +
			"delete(s, a) = " +
			"image(λx:(num → num). λi:num. COND(i = n, p, x(i)), image(tuple_take(n), delete(s, a)))",
	}, func(
		arg *Argument,
		p, n *Expr[Nat],
		s *Expr[Set[Fun[Nat, Nat]]],
		a *Arrow[Nat, Nat],
		simplex, aIn, top Fact,
	) {
		_, raiseDef := arg.LetAs[Fun[Fun[Nat, Nat], Fun[Nat, Nat]]](
			"raise", "λx:(num → num). λi:num. COND(i = n, p, x(i))")
		parts := arg.Conjuncts(
			arg.Unfolded(simplex, KuhnSimplexDef),
			"s lies in the grid",
			"s has n + 2 points",
			"any two points of s are comparable")
		inGrid := arg.Have(
			"the face lies in the grid",
			"∀y:(num → num). y ∈ delete(s, a) ⇒ y ∈ kuhn_grid(p, n + 1)",
			BySets(parts[0]))
		lowered := arg.Have(
			"each point of the face truncates into the grid, and raising the truncation gives it back",
			Statement{
				Binders: "∀y:(num → num).",
				Hypotheses: []string{
					"y ∈ delete(s, a)",
				},
				Conclusion: "tuple_take(n, y) ∈ kuhn_grid(p, n) ∧ raise(tuple_take(n, y)) = y",
			},
			Derive(func(b *Argument) {
				y := b.FixAs[Fun[Nat, Nat]]("y")
				yIn := b.Assume()
				b.Show(
					"its coordinate n is p, so restoring it is raising",
					raiseDef.Rw(),
					By(Normalized, top.At(y), inGrid.At(y), yIn, At(KuhnGridTake, p, n, y)))
			}))
		raisedBack := arg.Have(
			"raising the truncated face gives the face",
			"image(raise, image(tuple_take(n), delete(s, a))) = delete(s, a)",
			BySets(lowered))
		succ := arg.TermAs[Nat]("n + 1")
		faceSize := arg.Have(
			"the face has n + 1 points",
			"has_size(delete(s, a), n + 1)",
			By(parts[1], aIn, cardinality.HasSizeSuc.At(s, succ), nat_arith.Add1.At(succ)))
		injective := arg.Have(
			"truncation is one-to-one on the face, raising undoing it",
			"injective_on(delete(s, a), tuple_take(n))",
			Unfold(functions.InjectiveOnDef),
			Derive(func(b *Argument) {
				x := b.FixAs[Fun[Nat, Nat]]("x")
				y := b.FixAs[Fun[Nat, Nat]]("y")
				same := b.Assume()
				b.Show(
					"each is the raise of the common truncation",
					By(lowered.At(x), lowered.At(y), same))
			}))
		comparable := arg.Have(
			"truncation keeps two points of the face comparable",
			Statement{
				Binders: "∀x y:(num → num).",
				Hypotheses: []string{
					"x ∈ delete(s, a)",
					"y ∈ delete(s, a)",
				},
				Conclusion: "kuhn_le(n, tuple_take(n, x), tuple_take(n, y)) ∨ " +
					"kuhn_le(n, tuple_take(n, y), tuple_take(n, x))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[Fun[Nat, Nat]]("x")
				y := b.FixAs[Fun[Nat, Nat]]("y")
				both := b.Assume()
				b.Show(
					"they are comparable in s, and truncation keeps either order",
					By(parts[2].At(x, y), both, set_basic.InDelete, At(KuhnLeTake, n, x, y), At(KuhnLeTake, n, y, x)))
			}))
		truncatedIn := arg.Have(
			"the truncated face lies in the grid",
			"image(tuple_take(n), delete(s, a)) ⊆ kuhn_grid(p, n)",
			By(lowered, set_image.ImageSubsetIff))
		truncatedSize := arg.Have(
			"and has n + 1 points",
			"has_size(image(tuple_take(n), delete(s, a)), n + 1)",
			By(faceSize, injective, cardinality.HasSizeImageInj))
		take := arg.TermAs[Fun[Fun[Nat, Nat], Fun[Nat, Nat]]]("tuple_take(n)")
		related := arg.TermAs[Fun2[Fun[Nat, Nat], Fun[Nat, Nat], Bool]](
			"λx:(num → num). λy:(num → num). kuhn_le(n, x, y) ∨ kuhn_le(n, y, x)")
		face := arg.TermAs[Set[Fun[Nat, Nat]]]("delete(s, a)")
		truncatedChain := arg.Have(
			"and any two of its points are comparable",
			Statement{
				Binders: "∀x y:(num → num).",
				Hypotheses: []string{
					"x ∈ image(tuple_take(n), delete(s, a))",
					"y ∈ image(tuple_take(n), delete(s, a))",
				},
				Conclusion: "kuhn_le(n, x, y) ∨ kuhn_le(n, y, x)",
			},
			By(comparable, set_image.ForallInImagePair.At(take, related, face)))
		arg.Show(
			"so the truncated face is an n-simplex whose raise is the face",
			By(truncatedIn, truncatedSize, truncatedChain, raisedBack, KuhnSimplexDef))
	}),
})}

// KuhnRaisedSimplexFace — an n-simplex raised to the plane x(n) = p is a
// face of an (n + 1)-simplex: add the corner below its least point, at
// p − 1 in coordinate n, which lies below every raised point and in no
// raised point's place. It needs 0 < p for the corner to exist.
var KuhnRaisedSimplexFace = kuhnRaisedSimplexFaceThm{family.Add(registry.ProofEntry{
	Name: "KuhnRaisedSimplexFace",
	Key:  "prop_a57e8a4c27422a45",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num. ∀f:set(num → num).",
		Hypotheses: []string{
			"0 < p",
			"kuhn_simplex(p, n, f)",
		},
		Conclusion: "∃s:set(num → num). ∃a:(num → num). " +
			"    kuhn_simplex(p, n + 1, s) ∧ " +
			"    a ∈ s ∧ " +
			"    image(λx:(num → num). λi:num. COND(i = n, p, x(i)), f) = delete(s, a)",
	}, func(a *Argument, p, n *Expr[Nat], f *Expr[Set[Fun[Nat, Nat]]], positive, simplex Fact) {
		raise, raiseDef := a.LetAs[Fun[Fun[Nat, Nat], Fun[Nat, Nat]]](
			"raise", "λx:(num → num). λi:num. COND(i = n, p, x(i))")
		parts := a.Conjuncts(
			a.Unfolded(simplex, KuhnSimplexDef),
			"f lies in the grid",
			"f has n + 1 points",
			"any two points of f are comparable")
		b, least := a.ObtainAs[Fun[Nat, Nat]](
			"f has a least point b",
			"∃b:(num → num). b ∈ f ∧ ∀x:(num → num). x ∈ f ⇒ kuhn_le(n, b, x)",
			By(simplex, KuhnSimplexExtrema.At(p, n, f)))
		lowest := a.Conjuncts(
			least,
			"b lies in f",
			"b lies below every point of f")
		raised := a.Have(
			"raising a point of f lands in the grid, and truncation undoes it",
			"∀x:(num → num). x ∈ f ⇒ raise(x) ∈ kuhn_grid(p, n + 1) ∧ tuple_take(n, raise(x)) = x",
			Derive(func(c *Argument) {
				x := c.FixAs[Fun[Nat, Nat]]("x")
				xIn := c.Assume()
				c.Show(
					"a point of f is a grid point, raised with q = p",
					raiseDef.Rw(),
					By(xIn, parts[0], set_basic.SubsetDef, At(KuhnGridExtend, p, n, x, p), nat_order.LessEqRefl.At(p)))
			}))
		corner, cornerDef := a.LetAs[Fun[Nat, Nat]]("corner", "λi:num. COND(i = n, p - 1, b(i))")
		pMinusOne := a.TermAs[Nat]("p - 1")
		belowP := a.Have(
			"the corner's value p − 1 is a value of the grid",
			"p - 1 ≤ p",
			ByArith())
		cornerIn := a.Have(
			"the corner lies in the grid",
			"corner ∈ kuhn_grid(p, n + 1)",
			cornerDef.Rw(),
			By(belowP, lowest[0], parts[0], set_basic.SubsetDef, At(KuhnGridExtend, p, n, b, pMinusOne)))
		cornerValue := a.Have(
			"the corner is p − 1 at coordinate n, which is not p",
			"corner(n) = p - 1 ∧ ¬(p - 1 = p)",
			cornerDef.Rw(),
			ByArith(positive))
		cornerOut := a.Have(
			"so the corner is no raised point",
			"¬(corner ∈ image(raise, f))",
			By(raiseDef, cornerValue, set_basic.InImage))
		cornerBelow := a.Have(
			"the corner lies below every raised point: b lies below every point, and p − 1 below p",
			"∀x:(num → num). x ∈ f ⇒ kuhn_le(n + 1, corner, raise(x))",
			Derive(func(c *Argument) {
				x := c.FixAs[Fun[Nat, Nat]]("x")
				xIn := c.Assume()
				c.Show(
					"Kuhn's order extends from b ≤ x with p − 1 ≤ p ≤ (p − 1) + 1",
					raiseDef.Rw(),
					cornerDef.Rw(),
					ByArith(lowest[1].At(x), positive, xIn, At(KuhnLeExtend, n, b, x, pMinusOne, p)))
			}))
		raisedChain := a.Have(
			"raised points stay comparable",
			Statement{
				Binders: "∀x y:(num → num).",
				Hypotheses: []string{
					"x ∈ f",
					"y ∈ f",
				},
				Conclusion: "kuhn_le(n + 1, raise(x), raise(y)) ∨ kuhn_le(n + 1, raise(y), raise(x))",
			},
			Derive(func(c *Argument) {
				x := c.FixAs[Fun[Nat, Nat]]("x")
				y := c.FixAs[Fun[Nat, Nat]]("y")
				both := c.Assume()
				c.Show(
					"Kuhn's order extends either way with p at both",
					raiseDef.Rw(),
					ByArith(parts[2].At(x, y), both, At(KuhnLeExtend, n, x, y, p, p), At(KuhnLeExtend, n, y, x, p, p)))
			}))
		injective := a.Have(
			"raising is one-to-one on f, truncation undoing it",
			"injective_on(f, raise)",
			Unfold(functions.InjectiveOnDef),
			Derive(func(c *Argument) {
				x := c.FixAs[Fun[Nat, Nat]]("x")
				y := c.FixAs[Fun[Nat, Nat]]("y")
				same := c.Assume()
				c.Show(
					"each is the truncation of the common raise",
					By(raised.At(x), raised.At(y), same))
			}))
		raisedSize := a.Have(
			"the raised simplex has n + 1 points",
			"has_size(image(raise, f), n + 1)",
			By(parts[1], injective, cardinality.HasSizeImageInj))
		raisedSet := a.TermAs[Set[Fun[Nat, Nat]]]("image(raise, f)")
		simplexUp := a.TermAs[Set[Fun[Nat, Nat]]]("insert(corner, image(raise, f))")
		gridUp := a.TermAs[Set[Fun[Nat, Nat]]]("kuhn_grid(p, n + 1)")
		succ := a.TermAs[Nat]("n + 1")
		size := a.Have(
			"with the corner it has n + 2 points",
			"has_size(insert(corner, image(raise, f)), n + 1 + 1)",
			By(cornerOut, raisedSize, cardinality.HasSizeClauses.At(simplexUp, succ), nat_arith.Add1.At(succ)))
		inGrid := a.Have(
			"all of them lie in the grid",
			"insert(corner, image(raise, f)) ⊆ kuhn_grid(p, n + 1)",
			By(
				raised,
				cornerIn,
				set_order.InsertSubset.At(raisedSet, gridUp, corner),
				set_image.ImageSubsetIff.At(raise, f, gridUp)))
		related := a.TermAs[Fun2[Fun[Nat, Nat], Fun[Nat, Nat], Bool]](
			"λx:(num → num). λy:(num → num). kuhn_le(n + 1, x, y) ∨ kuhn_le(n + 1, y, x)")
		aboveCorner := a.TermAs[Set[Fun[Nat, Nat]]]("λy:(num → num). kuhn_le(n + 1, corner, y)")
		imageChain := a.Have(
			"any two raised points are comparable",
			Statement{
				Binders: "∀x y:(num → num).",
				Hypotheses: []string{
					"x ∈ image(raise, f)",
					"y ∈ image(raise, f)",
				},
				Conclusion: "kuhn_le(n + 1, x, y) ∨ kuhn_le(n + 1, y, x)",
			},
			By(raisedChain, set_image.ForallInImagePair.At(raise, related, f)))
		imageAbove := a.Have(
			"every raised point lies above the corner",
			"∀y:(num → num). y ∈ image(raise, f) ⇒ kuhn_le(n + 1, corner, y)",
			By(cornerBelow, set_image.ForallInImage.At(raise, f, aboveCorner)))
		chain := a.Have(
			"so any two of the n + 2 points are comparable",
			Statement{
				Binders: "∀x y:(num → num).",
				Hypotheses: []string{
					"x ∈ insert(corner, image(raise, f))",
					"y ∈ insert(corner, image(raise, f))",
				},
				Conclusion: "kuhn_le(n + 1, x, y) ∨ kuhn_le(n + 1, y, x)",
			},
			By(imageChain, imageAbove, KuhnLeRefl.At(succ, corner), set_basic.InInsert))
		face := a.Have(
			"removing the corner leaves the raised simplex",
			"image(raise, f) = delete(insert(corner, image(raise, f)), corner)",
			BySets(cornerOut))
		a.Take(simplexUp)
		a.Take(corner)
		a.Show(
			"so the corner and the raised simplex form an (n + "+
				"1)-simplex, the raised simplex its face opposite the corner",
			By(chain, size, inGrid, face, KuhnSimplexDef, set_basic.InInsert))
	}),
})}
