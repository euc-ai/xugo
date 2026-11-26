package product_measure

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// ProductMeasureUnique — a measure on the product σ-algebra that gives each
// measurable rectangle the product of its factor masses is the product
// measure. The measurable rectangles form a π-system generating the product
// σ-algebra, on which the two measures agree, and the products of increasing
// finite-mass covers of the two factors are increasing rectangles of finite
// mass that exhaust the product carrier.
var ProductMeasureUnique = productMeasureUniqueThm{family.Add(registry.ProofEntry{
	Name: "ProductMeasureUnique",
	Key:  "prop_948ef05211579e2a",
	Reading: "σ-finiteness of both factors is load-bearing: with μ the counting measure on " +
		"[0, 1] and ν Lebesgue, two measures agree on the rectangles and differ on the diagonal.",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀ν:(set(B) → extended_nonneg_real). " +
			"∀m:(set(prod(A, B)) → extended_nonneg_real). " +
			"∀E:set(prod(A, B)).",
		Hypotheses: []string{
			"sigma_finite_on(Ω, S, μ)",
			"sigma_finite_on(V, T, ν)",
			"measure_on(set_cross(Ω, V), product_sigma(Ω, S, V, T), m)",
			"∀s:set(A). ∀t:set(B). s ∈ S ∧ t ∈ T ⇒ m(set_cross(s, t)) = μ(s) * ν(t)",
			"E ∈ product_sigma(Ω, S, V, T)",
		},
		Conclusion: "m(E) = product_measure(Ω, S, μ, ν, E)",
		Abbrev: Abbrev{
			{Name: "rectangles", Text: "{set_cross(s, t):set(prod(A, B)) | " +
				"    s:set(A), " +
				"    t:set(B) | " +
				"    s ∈ S ∧ t ∈ T}"},
			{Name: "P", Text: "product_sigma(Ω, S, V, T)"},
			{Name: "mass", Text: "product_measure(Ω, S, μ, ν)"},
			{Name: "cover", Text: "λn:num. set_cross(p(n), q(n))"},
		},
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], V *Expr[Set[B]], T *Expr[Set[Set[B]]],
		ν *Arrow[Set[B], ExtendedNonnegReal], m *Arrow[Set[Prod[A, B]], ExtendedNonnegReal],
		E *Expr[Set[Prod[A, B]]], sigmaFiniteμ, sigmaFiniteν, measure, rectangleFormula, event Fact) {
		carrier := a.TermAs[Set[Prod[A, B]]]("set_cross(Ω, V)")
		P := a.TermAs[Set[Set[Prod[A, B]]]]("«P»")
		mass := a.TermAs[Fun[Set[Prod[A, B]], ExtendedNonnegReal]]("«mass»")
		C, cDef := a.LetAs[Set[Set[Prod[A, B]]]]("C", "«rectangles»")
		factors := a.Have(
			"the two sigma-finite factors are measures",
			"measure_on(Ω, S, μ) ∧ measure_on(V, T, ν) ∧ sigma_algebra_on(Ω, S) ∧ sigma_algebra_on(V, T)",
			By(
				sigmaFiniteμ,
				sigmaFiniteν,
				measure_space.SigmaFiniteDef.At(Ω, S, μ),
				measure_space.SigmaFiniteDef.At(V, T, ν),
				measure_space.MeasureOn.At(Ω, S, μ),
				measure_space.MeasureOn.At(V, T, ν)))
		productMeasure := a.Have(
			"the section integral also defines a measure on the product",
			"measure_on(set_cross(Ω, V), «P», «mass»)",
			By(factors, sigmaFiniteν, ProductMeasureOn.At(Ω, S, μ, V, T, ν)))
		within := a.Have(
			"each measurable rectangle lies in the product carrier",
			"∀s:set(A). ∀t:set(B). s ∈ S ∧ t ∈ T ⇒ set_cross(s, t) ⊆ set_cross(Ω, V)",
			Derive(func(b *Argument) {
				s := b.FixAs[Set[A]]("s")
				t := b.FixAs[Set[B]]("t")
				measurable := b.Assume()
				subsets := b.Have(
					"the factor events lie in their carriers",
					"S ⊆ {s:set(A) | s ⊆ Ω} ∧ T ⊆ {t:set(B) | t ⊆ V}",
					By(factors, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S), sigma_algebra.SigmaAlgebraOnDef.At(V, T)))
				b.Show(
					"take the product of the two inclusions",
					BySets(subsets, measurable, set_product.CrossSubsetIff.At(s, Ω, t, V)))
			}))
		rectangles := a.Have(
			"the measurable rectangles form a π-system generating the product σ-algebra",
			"pi_system_on(set_cross(Ω, V), C) ∧ «P» = generated_sigma(set_cross(Ω, V), C)",
			By(factors, cDef, measurable_space.ProductSigmaPiSystem.At(Ω, S, V, T)))
		agree := a.Have(
			"the two measures agree on every measurable rectangle",
			"∀R:set(prod(A, B)). R ∈ C ⇒ m(R) = «mass»(R)",
			Derive(func(b *Argument) {
				b.FixAs[Set[Prod[A, B]]]("R")
				member := b.Assume()
				s, t, rect := b.Unpack2As[Set[A], Set[B]](b.Simplified(member, Fwd(cDef)), "s", "t")
				b.Show(
					"both masses are the product of the factor masses",
					By(
						Normalized,
						factors,
						rect,
						rectangleFormula.At(s, t),
						measure_space.MeasureOn.At(V, T, ν),
						ProductMeasureRectangle.At(Ω, S, μ, ν, s, t)))
			}))
		p, pCover := a.ObtainAs[Fun[Nat, Set[A]]](
			"choose an increasing cover by finite-measure sets in the first factor",
			"∃p:(num → set(A)). "+
				"    (∀n:num. p(n) ∈ S ∧ μ(p(n)) ≠ extended_infinity) ∧ "+
				"    (∀n:num. p(n) ⊆ p(n + 1)) ∧ "+
				"    ⋃image(p, 𝕌) = Ω",
			By(sigmaFiniteμ, measure_space.SigmaFiniteIncreasingCover.At(Ω, S, μ)))
		q, qCover := a.ObtainAs[Fun[Nat, Set[B]]](
			"choose an increasing cover by finite-measure sets in the second factor",
			"∃q:(num → set(B)). "+
				"    (∀n:num. q(n) ∈ T ∧ ν(q(n)) ≠ extended_infinity) ∧ "+
				"    (∀n:num. q(n) ⊆ q(n + 1)) ∧ "+
				"    ⋃image(q, 𝕌) = V",
			By(sigmaFiniteν, measure_space.SigmaFiniteIncreasingCover.At(V, T, ν)))
		pLaws := a.Conjuncts(
			pCover,
			"the first cover sets have finite mass",
			"the first cover increases",
			"the first cover exhausts Ω")
		qLaws := a.Conjuncts(
			qCover,
			"the second cover sets have finite mass",
			"the second cover increases",
			"the second cover exhausts V")
		coverRectangles := a.Have(
			"every rectangle in the cover belongs to C and has finite mass",
			"∀n:num. «cover»(n) ∈ C ∧ m(«cover»(n)) ≠ extended_infinity",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				u := b.TermAs[Set[A]]("p(n)")
				v := b.TermAs[Set[B]]("q(n)")
				member := b.Have(
					"both factors are measurable",
					"«cover»(n) ∈ C",
					Simp(Fwd(cDef)),
					By(pLaws[0].At(n), qLaws[0].At(n)))
				b.Show(
					"a product of finite masses is finite",
					By(
						Normalized,
						member,
						pLaws[0].At(n),
						qLaws[0].At(n),
						rectangleFormula.At(u, v),
						extended_nonneg_real.MulEqInfinity.At(μ.Apply(u), ν.Apply(v))))
			}))
		index := a.Have(
			"the rectangle at i+j contains the product of factor sets at i and j",
			"∀i j:num. set_cross(p(i), q(j)) ⊆ «cover»(i + j)",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				j := b.FixAs[Nat]("j")
				k := b.TermAs[Nat]("i + j")
				bounds := b.Have(
					"the sum is at least each index",
					"i ≤ i + j ∧ j ≤ i + j",
					ByArith())
				inclusions := b.Have(
					"both sets lie in the cover at the sum",
					"p(i) ⊆ p(i + j) ∧ q(j) ⊆ q(i + j)",
					By(
						pLaws[1],
						qLaws[1],
						bounds,
						order.IncreasingFromSteps.At(p, i, k),
						order.IncreasingFromSteps.At(q, j, k)))
				b.Show(
					"take the product of the inclusions",
					BySets(
						inclusions,
						set_product.CrossSubsetIff.At(
							b.TermAs[Set[A]]("p(i)"), b.TermAs[Set[A]]("p(i + j)"),
							b.TermAs[Set[B]]("q(j)"), b.TermAs[Set[B]]("q(i + j)"))))
			}))
		exhaustion := a.Have(
			"the finite rectangles exhaust the product carrier",
			"⋃image(«cover», 𝕌) = set_cross(Ω, V)",
			Derive(func(b *Argument) {
				inCarrier := b.Have(
					"every rectangle lies in the carrier",
					"∀n:num. «cover»(n) ⊆ set_cross(Ω, V)",
					Derive(func(c *Argument) {
						n := c.FixAs[Nat]("n")
						c.Show(
							"both factors belong to their sigma algebras",
							By(pLaws[0].At(n), qLaws[0].At(n), within.At(c.TermAs[Set[A]]("p(n)"), c.TermAs[Set[B]]("q(n)"))))
					}))
				covered := b.Have(
					"each pair in the carrier lies in a finite rectangle",
					"∀z:prod(A, B). z ∈ set_cross(Ω, V) ⇒ z ∈ ⋃image(«cover», 𝕌)",
					Derive(func(c *Argument) {
						z := c.FixAs[Prod[A, B]]("z")
						member := c.Assume()
						projections := set_product.InCrossProjections.At(Ω, V, z)
						i, first := c.ObtainAs[Nat](
							"the first coordinate belongs to a cover set",
							"∃i:num. fst(z) ∈ p(i)",
							BySets(member, projections, pLaws[2]))
						j, second := c.ObtainAs[Nat](
							"the second coordinate belongs to a cover set",
							"∃j:num. snd(z) ∈ q(j)",
							BySets(member, projections, qLaws[2]))
						inProduct := c.Have(
							"the pair belongs to the product of those two sets",
							"z ∈ set_cross(p(i), q(j))",
							By(
								first,
								second,
								set_product.InCrossProjections.At(c.TermAs[Set[A]]("p(i)"), c.TermAs[Set[B]]("q(j)"), z)))
						c.Show(
							"the rectangle at i+j contains the pair",
							BySets(inProduct, index.At(i, j)))
					}))
				b.Show(
					"the two sets contain the same pairs",
					BySets(inCarrier, covered))
			}))
		coverGrowing := a.Have(
			"the cover rectangles increase",
			"∀n:num. «cover»(n) ⊆ «cover»(n + 1)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"the product of the increasing factors is increasing",
					BySets(
						pLaws[1].At(n),
						qLaws[1].At(n),
						set_product.CrossSubsetIff.At(
							b.TermAs[Set[A]]("p(n)"), b.TermAs[Set[A]]("p(n + 1)"),
							b.TermAs[Set[B]]("q(n)"), b.TermAs[Set[B]]("q(n + 1)"))))
			}))
		a.Show(
			"two measures agreeing on a generating pi system, exhausted by increasing finite rectangles, agree",
			By(
				measure,
				productMeasure,
				rectangles,
				agree,
				coverRectangles,
				coverGrowing,
				exhaustion,
				event,
				measure_space.MeasureDeterminedByPiExhaustion.At(
					carrier, C, P, m, mass, a.TermAs[Fun[Nat, Set[Prod[A, B]]]]("«cover»"), E)))
	}),
})}
