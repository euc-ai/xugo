package hypercube

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/simple_graph"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// NeighbourSumBound bounds a sum supported on the neighbours of x in H:
// at most the degree of x terms contribute, each of magnitude at most b.
var NeighbourSumBound = neighbourSumBoundThm{family.Add(registry.ProofEntry{
	Name: "NeighbourSumBound",
	Key:  "prop_237dcbec9c7b58e4",
	Build: family.Theorem(Statement{
		Binders: "∀V H:set(A). ∀R:(A → A → bool). ∀x:A. ∀f:(A → real). ∀b:real.",
		Hypotheses: []string{
			"finite(H)",
			"H ⊆ V",
			"∀y:A. y ∈ V ∧ (y ∉ H ∨ ¬R(x, y)) ⇒ f(y) = &0",
			"∀y:A. y ∈ H ∧ R(x, y) ⇒ |f(y)| ≤ b",
		},
		Conclusion: "|sum(V, f)| ≤ &graph_degree(H, R, x) * b",
	}, func(
		a *Argument,
		V, H *Expr[Set[A]],
		R *Arrow[A, Set[A]],
		x *Expr[A],
		f *Arrow[A, Real],
		b *Expr[Real],
		finite, sub, silent, bounded Fact,
	) {
		neighbours := a.TermAs[Set[A]]("graph_neighbours(H, R, x)")
		neighbourhood := simple_graph.NeighboursDef.At(H, R, x)
		within := a.Have(
			"the neighbours in H belong to H",
			"graph_neighbours(H, R, x) ⊆ H",
			BySets(neighbourhood))
		finiteNeighbours := a.Have(
			"there are finitely many such neighbours",
			"finite(graph_neighbours(H, R, x))",
			By(finite, within, finite_set.FiniteSubset.At(neighbours, H)))
		inside := a.Have(
			"these are vertices of V",
			"graph_neighbours(H, R, x) ⊆ V",
			By(sub, within, set_order.SubsetTrans))
		off := a.Have(
			"the summand vanishes at all other vertices",
			"∀y:A. y ∈ V ∧ y ∉ graph_neighbours(H, R, x) ⇒ f(y) = neutral_elem(real_add)",
			BySets(silent, neighbourhood, real_ring.NeutralAdd))
		restrict := a.Have(
			"only neighbours contribute to the sum",
			"sum(graph_neighbours(H, R, x), f) = sum(V, f)",
			By(
				inside,
				off,
				monoidal.Superset.At(a.TermAs[Op[Real]]("real_add"), neighbours, V, f),
				real_sum.RealSumDef))
		terms := a.Have(
			"each contributing term has magnitude at most b",
			"∀y:A. y ∈ graph_neighbours(H, R, x) ⇒ |f(y)| ≤ b",
			BySets(bounded, neighbourhood))
		a.Show(
			"the number of those terms is the degree in H",
			By(
				Normalized,
				finiteNeighbours,
				terms,
				restrict,
				real_sum.TriangleBound.At(neighbours, f, b),
				simple_graph.DegreeDef.At(H, R, x)))
	}),
})}

// SignedRowBound bounds a signed matrix row by the degree within H and
// a uniform bound on the values of its input there.
var SignedRowBound = signedRowBoundThm{family.Add(registry.ProofEntry{
	Name: "SignedRowBound", Key: "prop_f1713bc8e0a61538",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(A). " +
			"∀H:set(set(A)). " +
			"∀M:(set(A) → set(A) → real). " +
			"∀v:(set(A) → real). " +
			"∀X:set(A). " +
			"∀b:real.",
		Hypotheses: []string{
			"finite(H)",
			"H ⊆ «vertices»",
			"X ⊆ S",
			"cube_signing(S, M)",
			"∀Y:set(A). Y ⊆ S ∧ Y ∉ H ⇒ v(Y) = &0",
			"∀Y:set(A). Y ∈ H ⇒ |v(Y)| ≤ b",
		},
		Conclusion: "|cube_action(S, M, v, X)| ≤ &graph_degree(H, cube_adjacent(S), X) * b",
		Abbrev:     Abbrev{{Name: "vertices", Text: "{Y:set(A) | Y ⊆ S}"}},
	}, func(
		a *Argument,
		S *Expr[Set[A]],
		H *Expr[Set[Set[A]]],
		M *Arrow2[Set[A], Set[A], Real],
		v *Arrow[Set[A], Real],
		X *Expr[Set[A]],
		b *Expr[Real],
		finiteH, within, vertex, signing, supported, bound Fact,
	) {
		entries := a.Unfolded(signing, cubeSigningDef)
		zero := a.Have(
			"outside H or away from an edge the row summand vanishes",
			"∀Y:set(A). Y ∈ «vertices» ∧ (Y ∉ H ∨ ¬cube_adjacent(S, X, Y)) ⇒ M(X, Y) * v(Y) = &0",
			Derive(func(c *Argument) {
				Y := c.FixAs[Set[A]]("Y")
				off := c.Assume()
				inside := c.Have(
					"the column is a vertex of S",
					"Y ⊆ S",
					BySets(off))
				factor := c.Have(
					"either the coefficient or the input is zero",
					"M(X, Y) = &0 ∨ v(Y) = &0",
					By(vertex, inside, off, entries.At(X, Y), supported.At(Y)))
				c.Do(By(
					Normalized,
					factor,
					real_ring.MulLeftZero.At(c.TermAs[Real]("v(Y)")),
					real_ring.MulRightZero.At(c.TermAs[Real]("M(X, Y)"))))
			}))
		edge := a.Have(
			"on a contributing edge a sign preserves the magnitude of the input",
			"∀Y:set(A). Y ∈ H ∧ cube_adjacent(S, X, Y) ⇒ |M(X, Y) * v(Y)| ≤ b",
			Derive(func(c *Argument) {
				Y := c.FixAs[Set[A]]("Y")
				neighbor := c.Assume()
				inside := c.Have(
					"a column belonging to H lies on the cube",
					"Y ⊆ S",
					BySets(within, neighbor))
				sign := c.Have(
					"the coefficient on this edge is a sign",
					"M(X, Y) = &1 ∨ M(X, Y) = -&1",
					By(vertex, inside, neighbor, entries.At(X, Y)))
				c.Do(ByArith(
					sign,
					neighbor,
					bound.At(Y),
					real_sgn_abs.AbsMul.At(c.TermAs[Real]("M(X, Y)"), c.TermAs[Real]("v(Y)"))))
			}))
		a.Show(
			"at most the degree of X summands contribute",
			Unfold(cubeActionDef),
			By(
				finiteH,
				within,
				zero,
				edge,
				NeighbourSumBound.At(
					a.TermAs[Set[Set[A]]]("«vertices»"),
					H,
					a.TermAs[Fun2[Set[A], Set[A], Bool]]("cube_adjacent(S)"),
					X,
					a.TermAs[Fun[Set[A], Real]]("λY:set(A). M(X, Y) * v(Y)"),
					b)))
	}),
})}

// SupportedDegreeBound applies the row estimate twice to a nonzero vector.
// Both the vector and its first image vanish at the omitted cube vertices.
var SupportedDegreeBound = supportedDegreeBoundThm{family.Add(registry.ProofEntry{
	Name: "SupportedDegreeBound",
	Key:  "prop_32e1c1bbbbcebd89",
	Build: family.Sections(Statement{
		Binders: "∀S:set(A). ∀H:set(set(A)). ∀M:(set(A) → set(A) → real). ∀v:(set(A) → real).",
		Hypotheses: []string{
			"finite(S)",
			"H ⊆ «vertices»",
			"cube_signing(S, M)",
			"cube_square(S, M, &card(S))",
			"∃X:set(A). X ∈ H ∧ v(X) ≠ &0",
			"∀X:set(A). X ⊆ S ∧ X ∉ H ⇒ v(X) = &0",
			"∀X:set(A). X ⊆ S ∧ X ∉ H ⇒ cube_action(S, M, v, X) = &0",
		},
		Conclusion: "∃X:set(A). X ∈ H ∧ card(S) ≤ «degree»(X) * «degree»(X)",
		Abbrev: Abbrev{
			{Name: "vertices", Text: "{X:set(A) | X ⊆ S}"},
			{Name: "degree", Text: "λX:set(A). graph_degree(H, cube_adjacent(S), X)"},
			// «amplitude» spells the peak p and «rowBound» the maximizer d, both obtained in the body.
			{Name: "amplitude", Text: "|v(p)|"},
			{Name: "rowBound", Text: "&«degree»(d) * «amplitude»"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		maximum := ctx.Lemma(Statement{
			Binders:    "∀H:set(A). ∀f:(A → real).",
			Hypotheses: []string{"finite(H)", "H ≠ ∅"},
			Conclusion: "∃x:A. x ∈ H ∧ (∀y:A. y ∈ H ⇒ f(y) ≤ f(x))",
		},
			func(a *Argument, H *Expr[Set[A]], f *Arrow[A, Real], finiteH, nonempty Fact) {
				inhabited := a.Have(
					"the image of a nonempty set is nonempty",
					"image(f, H) ≠ ∅",
					BySets(nonempty))
				greatest := a.Have(
					"the supremum of the finite image is one of its values",
					"sup(image(f, H)) ∈ image(f, H) ∧ (∀z:real. z ∈ image(f, H) ⇒ z ≤ sup(image(f, H)))",
					By(
						inhabited,
						finiteH,
						finite_set.FiniteImage.At(f, H),
						real_sup_inf.SupFiniteAttained.At(a.TermAs[Set[Real]]("image(f, H)"))))
				a.Show(
					"some point attains that supremum",
					BySets(greatest))
			})
		return ctx.Theorem(headline, func(
			a *Argument,
			S *Expr[Set[A]],
			H *Expr[Set[Set[A]]],
			M *Arrow2[Set[A], Set[A], Real],
			v *Arrow[Set[A], Real],
			finiteS, within, signing, square, nonzero, support, imageSupport Fact,
		) {
			finiteH := a.Have(
				"the chosen vertices form a subset of a finite cube",
				"finite(H)",
				By(
					finiteS,
					within,
					finite_set.FinitePowerset.At(S),
					finite_set.FiniteSubset.At(H, a.TermAs[Set[Set[A]]]("«vertices»"))))
			nonempty := a.Have(
				"the nonzero coordinate supplies a vertex of H",
				"H ≠ ∅",
				BySets(nonzero))
			maximumOn := ctx.AtTypeVars(maximum, TypeBinder.BindA[Set[A]]())
			p, peak := a.ObtainAs[Set[A]](
				"choose a vertex attaining the largest absolute input value",
				"∃p:set(A). p ∈ H ∧ (∀Y:set(A). Y ∈ H ⇒ |v(Y)| ≤ |v(p)|)",
				Named("p"),
				By(finiteH, nonempty, At(maximumOn, H, a.Term("λY:set(A). |v(Y)|"))))
			d, largest := a.ObtainAs[Set[A]](
				"choose a vertex of greatest induced degree",
				"∃d:set(A). d ∈ H ∧ (∀Y:set(A). Y ∈ H ⇒ &«degree»(Y) ≤ &«degree»(d))",
				Named("d"),
				By(finiteH, nonempty, At(maximumOn, H, a.Term("λY:set(A). &«degree»(Y)"))))
			peakFacts := a.Conjuncts(
				peak,
				"the peak belongs to H",
				"the absolute input values are bounded by the peak")
			peakInH, belowPeak := peakFacts[0], peakFacts[1]
			degreeFacts := a.Conjuncts(
				largest,
				"the degree maximizer belongs to H",
				"all induced degrees are bounded by its degree")
			maximizerInH, belowMaxDegree := degreeFacts[0], degreeFacts[1]
			peakVertex := a.Have(
				"the peak is a vertex of the cube",
				"p ⊆ S",
				BySets(peakInH, within))
			positive := a.Have(
				"the peak magnitude dominates a positive magnitude",
				"&0 < «amplitude»",
				Derive(func(b *Argument) {
					q, nonzeroAt := b.UnpackAs[Set[A]](nonzero, "q")
					b.Do(ByArith(nonzeroAt, belowPeak.At(q), real_sgn_abs.AbsPosIffNonzero.At(b.TermAs[Real]("v(q)"))))
				}))
			image := a.TermAs[Fun[Set[A], Real]]("cube_action(S, M, v)")
			imageBound := a.Have(
				"the first image is bounded everywhere in H by the largest degree times the peak",
				"∀Y:set(A). Y ∈ H ⇒ |cube_action(S, M, v, Y)| ≤ «rowBound»",
				Derive(func(b *Argument) {
					Y := b.FixAs[Set[A]]("Y")
					inH := b.Assume()
					vertex := b.Have(
						"this row belongs to the cube",
						"Y ⊆ S",
						BySets(inH, within))
					local := b.Have(
						"the signed row sees only the neighbours of Y",
						"|cube_action(S, M, v, Y)| ≤ &«degree»(Y) * «amplitude»",
						By(
							finiteH,
							within,
							vertex,
							signing,
							support,
							belowPeak,
							SignedRowBound.At(S, H, M, v, Y, b.TermAs[Real]("«amplitude»"))))
					b.Do(ByArith(
						belowMaxDegree.At(Y),
						inH,
						local,
						positive,
						real_order_ring.LessEqMulRight.At(
							b.TermAs[Real]("&«degree»(Y)"),
							b.TermAs[Real]("&«degree»(d)"),
							b.TermAs[Real]("«amplitude»"))))
				}))
			second := a.Have(
				"at the peak the second application is bounded by its degree times the first bound",
				"|cube_action(S, M, cube_action(S, M, v), p)| ≤ &«degree»(p) * «rowBound»",
				By(
					finiteH,
					within,
					peakVertex,
					signing,
					imageSupport,
					imageBound,
					SignedRowBound.At(S, H, M, image, p, a.TermAs[Real]("«rowBound»"))))
			twice := a.Have(
				"at the same point the square gives the dimension times the original input",
				"cube_action(S, M, cube_action(S, M, v), p) = &card(S) * v(p)",
				By(square, peakVertex, cubeSquareDef.At(S, M, a.TermAs[Real]("&card(S)"))))
			boundNonneg := a.Have(
				"the degree times the peak is nonnegative",
				"&0 ≤ «rowBound»",
				ByArith(positive))
			peakDegree := a.Have(
				"the degree at the peak is at most the largest induced degree",
				"&«degree»(p) ≤ &«degree»(d)",
				By(belowMaxDegree.At(p), peakInH))
			grow := a.Have(
				"replacing the degree at the peak enlarges the second bound",
				"&«degree»(p) * «rowBound» ≤ &«degree»(d) * «rowBound»",
				By(
					peakDegree,
					boundNonneg,
					real_order_ring.LessEqMulRight.At(
						a.TermAs[Real]("&«degree»(p)"),
						a.TermAs[Real]("&«degree»(d)"),
						a.TermAs[Real]("«rowBound»"))))
			scaled := a.Have(
				"the squared degree times the peak bounds the dimension times the peak",
				"&card(S) * «amplitude» ≤ (&«degree»(d) * &«degree»(d)) * «amplitude»",
				ByArith(
					twice,
					second,
					grow,
					real_sgn_abs.AbsMul.At(a.TermAs[Real]("&card(S)"), a.TermAs[Real]("v(p)")),
					real_sgn_abs.AbsOfNum.At(a.TermAs[Nat]("card(S)"))))
			cancel := a.Have(
				"cancel the strictly positive peak magnitude",
				"&card(S) ≤ &«degree»(d) * &«degree»(d)",
				By(
					positive,
					scaled,
					real_order_ring.LessEqCancelMulRight.At(
						a.TermAs[Real]("&card(S)"),
						a.TermAs[Real]("&«degree»(d) * &«degree»(d)"),
						a.TermAs[Real]("«amplitude»"))))
			a.Take(d)
			a.Show(
				"the maximizing vertex thus satisfies the natural-number degree bound",
				By(
					maximizerInH,
					cancel,
					real_construction.OfNumMul.At(a.TermAs[Nat]("«degree»(d)"), a.TermAs[Nat]("«degree»(d)")),
					real_construction.OfNumLessEq.At(
						a.TermAs[Nat]("card(S)"), a.TermAs[Nat]("«degree»(d) * «degree»(d)"))))
		})
	}),
})}
