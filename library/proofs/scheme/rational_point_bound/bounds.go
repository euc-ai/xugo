// bounds.go — Bombieri's bound: the count that lets the Frobenius swap kernel hold a
// nonzero section, and the bound on the regular points that section gives.

package rational_point_bound

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/regular_point"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// TensorDimensionExcess — the count behind the bound: once s exceeds g² + 3g + 1,
// spaces of dimensions at least s - g and s + g + 1 have a tensor product larger than
// s(s - 1) + (s + 2g) + 1. Writing s = g + t + 1, the two lower bounds multiply to
// (t + 1)(2g + t + 2), and the comparison is linear in the monomials of g and t.
var TensorDimensionExcess = tensorDimensionExcessThm{family.Add(registry.ProofEntry{
	Name: "TensorDimensionExcess",
	Key:  "prop_e5abb0f8e3ea22a5",
	Build: family.Theorem(Statement{
		Binders: "∀s g e f:num.",
		Hypotheses: []string{
			"g * g + 3 * g + 1 < s",
			"s ≤ e + g",
			"s + g + 1 ≤ f",
		},
		Conclusion: "e * f > s * (s - 1) + (s + 2 * g) + 1",
	},
		func(a *Argument, s, g, e, f *Expr[Nat], large, first, second Fact) {
			_, tDef := a.LetAs[Nat]("t", "s - g - 1")
			shift := a.Have(
				"s exceeds g, so it is g + t + 1",
				"s = g + t + 1",
				ByArith(large, tDef))
			bounds := a.Have(
				"so e is at least t + 1 and f at least 2 * g + t + 2",
				"t + 1 ≤ e ∧ 2 * g + t + 2 ≤ f",
				ByArith(shift, first, second))
			product := a.Have(
				"and e * f is at least the product of these",
				"(t + 1) * (2 * g + t + 2) ≤ e * f",
				By(bounds, nat_order.LessEqMul2))
			gap := a.Have(
				"the hypothesis on s says t exceeds g * g + 2 * g",
				"g * g + 2 * g < t",
				ByArith(shift, large))
			a.Do(shift.Rw())
			a.Show(
				"in g and t, that product exceeds the bound by t - g * g - 2 * g",
				ByArith(product, gap))
		}),
})}

// BombieriUpperRegularPoints — Bombieri's bound: a curve of genus g over a field of
// s² elements with g² + 3g + 1 < s has at most s² + (2g + 1)s regular rational points.
// With no regular point there is nothing to count. Otherwise fix one, P, and take
// a = s - 1 and b = s + 2g: Riemann–Roch makes the pole spaces of orders a and b so
// large that the Frobenius swap kernel holds a nonzero section U with poles only at P,
// of order at most a + sb, vanishing at every other regular point. A nonzero section
// has at most that many zeros away from P, and P is one point more. The basis E of the
// space of order a is the adapted one, because the tensor's injectivity needs distinct
// orders on E alone; F is any finite basis of the space of order b.
var BombieriUpperRegularPoints = bombieriUpperRegularPointsThm{family.Add(registry.ProofEntry{
	Name: "BombieriUpperRegularPoints",
	Key:  "prop_1a670d1f10241451",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀s:num.",
		Hypotheses: []string{
			"«rbCurve»",
			"finite(k)",
			"card(k) = s * s",
			"«rbGenus» * «rbGenus» + 3 * «rbGenus» + 1 < s",
		},
		Conclusion: "finite(«points») ∧ card(«points») ≤ s * s + (2 * «rbGenus» + 1) * s",
		Abbrev: Abbrev{
			{Name: "points", Text: "{R:prod(set(A), set(A)) | «rbPoint»(R)}"},
			{Name: "poleSet", Text: "λi:num. fst(«rbPolePair»(i)) ∩ snd(«rbPolePair»(i))"},
			{Name: "zeros", Text: "{Q:prod(set(A), set(A)) | " +
				"    «rbPoint»(Q) ∧ Q ≠ P ∧ «rbEvaluation»(Q, «rbTensor»(c)) = L.zero}"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			s *Expr[Nat],
			curve, finiteK, size, large Fact,
		) {
			exists := arg.Assuming(
				arg.TermAs[Bool]("∃P:prod(set(A), set(A)). «rbPoint»(P)"),
				"with no regular point there is nothing to count",
				Given(func(d *Argument, none Fact) {
					empty := d.Have(
						"the regular points are the empty set",
						"«points» = ∅",
						BySets(none))
					d.Do(empty.Rw())
					d.Show(
						"which is finite, of size zero",
						ByArith(finite_set.FiniteRules, cardinality.CardClauses))
				}))
			P, point := arg.UnpackAs[_LatticePair](exists, "P")
			scalars := arg.TermAs[RingOps[A]]("«rbScalars»")
			inverse := arg.TermAs[Fun[A, A]]("L.inv")
			genus := arg.TermAs[Nat]("«rbGenus»")
			filtration := arg.Conjuncts(
				GroupPremises(
					curve, point, regular_point.SinglePointPoleFiltration.Read(L).At(k, A0, A1, A01, t, P)),
				"the zeroth pole space is k",
				"pole orders add under products",
				"each pole space is finite dimensional, of dimension at least n + 1 - g",
				"each pole space adds at most one dimension to the one before")
			dimensions := filtration[2]
			fieldScalars := arg.Have(
				"k is a field of scalars",
				"ring_subfield(«rbScalars», L.inv, k)",
				By(
					GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
					field.SubfieldRingSubfield.Read(L).At(k, k)))
			basisSizes := arg.Have(
				"so a finite basis of the n-th pole space has at least n + 1 - g elements",
				Statement{
					Binders:    "∀n:num. ∀B:set(A).",
					Hypotheses: []string{"finite(B)", "module_basis(«rbScalars», «rbPoles»(n), B)"},
					Conclusion: "n + 1 ≤ card(B) + «rbGenus»",
				},
				Derive(func(d *Argument) {
					n, B := d.FixAs[Nat]("n"), d.FixAs[Set[A]]("B")
					based := d.Assume()
					poles := d.TermAs[module_record.ModuleOps[A, A]]("«rbPoles»(n)")
					dimension := d.Have(
						"the dimension of the pole space, a module over k, is the size of any finite basis",
						"«rbPoleDim»(n) = card(B)",
						By(
							curve,
							point,
							regular_point.PoleSpaceModule.Read(L).At(k, A0, A1, A01, t, P, n),
							fieldScalars,
							based,
							module_dimension.DimBasis.At(scalars, poles, inverse, B)))
					d.Show(
						"the lower bound of the filtration, read back in ℕ",
						ByArith(
							dimension,
							dimensions.At(n),
							int_embed.OfNumLe.At(d.TermAs[Nat]("n + 1"), d.TermAs[Nat]("card(B) + «rbGenus»")),
							int_embed.OfNumAdd.At(n, d.TermAs[Nat]("1")),
							int_embed.OfNumAdd.At(d.TermAs[Nat]("card(B)"), genus)))
				}))

			a, aDef := arg.LetAs[Nat]("a", "s - 1")
			b, bDef := arg.LetAs[Nat]("b", "s + 2 * «rbGenus»")
			E, adapted := arg.UnpackAs[Set[A]](
				GroupPremises(
					curve, point, regular_point.PoleOrderAdaptedBasis.Read(L).At(k, A0, A1, A01, t, P, a)),
				"E")
			partsE := arg.Conjuncts(
				adapted,
				"E is finite",
				"E is a basis of the a-th pole space",
				"orders tell the elements of E apart",
				"and lie between -a and 0")
			finiteE, basisE, separated := partsE[0], partsE[1], partsE[2]
			F, based := arg.ObtainAs[Set[A]](
				"the b-th pole space, being finite dimensional, has a finite basis F",
				"∃F:set(A). finite(F) ∧ module_basis(«rbScalars», «rbPoles»(b), F)",
				By(dimensions.At(b), module_dimension.FiniteDimensionalDef),
				Named("F"))
			partsF := arg.Conjuncts(
				based,
				"F is finite",
				"F is a basis of the b-th pole space")
			finiteF, basisF := partsF[0], partsF[1]
			ordered := arg.Have(
				"s is positive and exceeds a",
				"0 < s ∧ a < s",
				ByArith(large, aDef))
			lower := arg.Have(
				"E has at least s - g elements, and F at least s + g + 1",
				"s ≤ card(E) + «rbGenus» ∧ s + «rbGenus» + 1 ≤ card(F)",
				ByArith(
					aDef,
					bDef,
					ordered,
					finiteE,
					basisE,
					finiteF,
					basisF,
					basisSizes.At(a, E),
					basisSizes.At(b, F)))
			excess := arg.Have(
				"so the products of E with F outnumber the conditions on the kernel",
				"card(E) * card(F) > s * a + b + 1",
				aDef.Rw(),
				bDef.Rw(),
				By(
					large,
					lower,
					At(
						TensorDimensionExcess,
						s,
						genus,
						arg.TermAs[Nat]("card(E)"),
						arg.TermAs[Nat]("card(F)"))))
			_, kernel := arg.ObtainAs[Fun[Prod[A, A], A]](
				"so the Frobenius swap kernel holds a nonzero section "+
					"of poles of order at most a + s * b, vanishing off P",
				"∃c:(prod(A, A) → A). "+
					"    «rbTensor»(c) ∈ «poleSet»(a + s * b) ∧ "+
					"    «rbTensor»(c) ≠ L.zero ∧ "+
					"    (∀Q:prod(set(A), set(A)). «rbPoint»(Q) ∧ Q ≠ P ⇒ «rbEvaluation»(Q, «rbTensor»(c)) = L.zero)",
				By(
					curve,
					finiteK,
					point,
					ordered,
					size,
					finiteE,
					finiteF,
					basisE,
					basisF,
					separated,
					excess,
					FrobeniusSwapKernel.Read(L).At(k, A0, A1, A01, t, P, a, b, s, E, F)),
				Named("c"))
			section := arg.Conjuncts(
				kernel,
				"the tensor U of c lies in the pole space of order a + s * b",
				"U is not zero",
				"U vanishes at every regular point other than P")
			inPoles, nonzero, vanishing := section[0], section[1], section[2]
			U := arg.TermAs[A]("«rbTensor»(c)")
			order := arg.TermAs[Nat]("a + s * b")
			zeros := arg.TermAs[Set[_LatticePair]]("«zeros»")
			counted := arg.Have(
				"a nonzero section with poles of order at most a + s * b has at most so many zeros",
				"finite(«zeros») ∧ card(«zeros») ≤ a + s * b",
				By(
					curve,
					point,
					inPoles,
					nonzero,
					regular_point.NonzeroSectionZeroCount.Read(L).At(k, A0, A1, A01, t, P, order, U)))
			cover := arg.Have(
				"every regular point is P or a zero of U other than P",
				"«points» ⊆ insert(P, «zeros»)",
				BySets(vanishing))
			enlarged := arg.Have(
				"and P is one point more",
				"finite(insert(P, «zeros»)) ∧ card(insert(P, «zeros»)) ≤ suc(a + s * b)",
				By(counted, cardinality.InsertCountsAtMostOneMore.At(zeros, P, order)))
			total := arg.Have(
				"which is the bound of the theorem",
				"suc(a + s * b) = s * s + (2 * «rbGenus» + 1) * s",
				ByArith(Scaled(s, bDef), aDef, ordered))
			regularPoints := arg.TermAs[Set[_LatticePair]]("«points»")
			covering := arg.TermAs[Set[_LatticePair]]("insert(P, «zeros»)")
			arg.Show(
				"a subset of a finite set is finite and no larger",
				ByArith(
					cover,
					enlarged,
					total,
					size,
					finite_set.FiniteSubset.At(regularPoints, covering),
					cardinality.CardSubset.At(regularPoints, covering)))
		}),
})}
