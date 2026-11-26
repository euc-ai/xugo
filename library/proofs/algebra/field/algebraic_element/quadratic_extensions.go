// quadratic_extensions.go — finite extensions of degree two over a subfield
// in which every element is a square.

package algebraic_element

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/registry"
)

// SquareClosedNoQuadraticExtension — a subfield in which every element is a
// square has no quadratic finite extension when two is nonzero: each minimal
// polynomial has degree at most two, and the quadratic formula
// (field.QuadraticFormula) puts its root back in the subfield.
var SquareClosedNoQuadraticExtension = squareClosedNoQuadraticExtensionThm{family.Add(registry.ProofEntry{
	Name: "SquareClosedNoQuadraticExtension",
	Key:  "prop_c70f4bbe83a4296a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_ops(A). ∀K E:set(A).",
		Hypotheses: []string{
			"field_on(L)",
			"subfield(L, K)",
			"subfield(L, E)",
			"K ⊆ E",
			"finite_extension(L, K, E)",
			"L.one + L.one ≠ L.zero",
			"square_closed(L, K)",
		},
		Conclusion: "extension_degree(L, K, E) ≠ 2",
	}, func(
		arg *Argument,
		L *Expr[FieldOps[A]],
		K, E *Expr[Set[A]],
		fieldL field.FieldFact[on.L],
		subfieldK, subfieldE, contains, finite, twoNonzero, squares Fact,
	) {
		everySquare := arg.Unfolded(squares, field.SquareClosedDef)
		denied := arg.SupposeNot()
		degreeTwo := arg.Have(
			"then the extension has degree two",
			"extension_degree(L, K, E) = 2",
			By(denied))
		allIn := arg.Have(
			"every element of E lies in K",
			"∀x:A. x ∈ E ⇒ x ∈ K",
			Derive(func(c *Argument) {
				x := c.FixAs[A]("x")
				xE := c.Assume()
				xIn := c.Have(
					"the element lies in the ambient field",
					"x ∈ L.carrier",
					BySets(xE, subfieldE, field.SubfieldSubset.At(L, E)))
				xm := c.MemberOf[on.L](x, xIn)
				algebraic := c.Have(
					"finite extensions are algebraic",
					"algebraic_over(L, K, x)",
					By(
						xE,
						subfieldE,
						subfieldK,
						contains,
						finite,
						FiniteExtensionAlgebraic.Read(fieldL).AsFact().At(K, E, x)))
				p, pDef := c.LetAs[Fun[Nat, A]]("p", "minimal_polynomial(L, K, x)")
				divides := c.Have(
					"the minimal-polynomial degree divides the extension degree",
					"polynomial_degree(p) ∣ extension_degree(L, K, E)",
					By(
						Normalized,
						pDef,
						subfieldK,
						subfieldE,
						contains,
						finite,
						xE,
						MinimalPolynomialDegreeDivides.Read(fieldL).At(K, E, x)))
				positive := c.Have(
					"a minimal polynomial has positive degree",
					"0 < polynomial_degree(p)",
					By(Normalized, pDef, subfieldK, xIn, algebraic, MinimalPolynomialPositive.Read(fieldL).At(K, xm)))
				alternatives := c.Have(
					"the minimal polynomial is linear or quadratic",
					"polynomial_degree(p) = 1 ∨ polynomial_degree(p) = 2",
					ByArith(
						positive,
						divides,
						degreeTwo,
						nat_divides.DividesLessEq.At(
							c.TermAs[Nat]("polynomial_degree(p)"), c.TermAs[Nat]("extension_degree(L, K, E)"))))
				c.Do(alternatives.SplitDisj(
					LeftHolds(
						"a linear minimal polynomial puts x in K",
						Given(func(d *Argument, linear Fact) {
							d.Show(
								"a point whose minimal polynomial is linear lies in K",
								By(
									Normalized,
									pDef,
									linear,
									subfieldK,
									algebraic,
									MinimalPolynomialLinearIff.Read(fieldL).At(K, xm)))
						})),
					RightHolds(
						"the quadratic formula puts the root in K",
						Given(func(d *Argument, quadratic Fact) {
							spec := d.Have(
								"the minimal polynomial is monic and vanishes at x",
								"polynomial_over(K, p) ∧ polynomial_monic(p) ∧ polynomial_eval(p, x) = L.zero",
								By(Normalized, pDef, subfieldK, xIn, algebraic, MinimalPolynomialSpec.Read(fieldL).At(K, xm)))
							polynomialData := d.Have(
								"its coefficients lie in K and hence in the ambient field",
								"polynomial_over(L.carrier, p) ∧ p(0) ∈ K ∧ p(1) ∈ K",
								By(
									spec,
									subfieldK,
									field.SubfieldSubset.At(L, K),
									polynomial.PolynomialOverMono.At(d.TermAs[A]("L.zero"), K, d.TermAs[Set[A]]("L.carrier"), p),
									polynomial.CoefficientIn.At(d.TermAs[A]("L.zero"), K, p, d.TermAs[Nat]("0")),
									polynomial.CoefficientIn.At(d.TermAs[A]("L.zero"), K, p, d.TermAs[Nat]("1"))))
							leading := d.Have(
								"the leading quadratic coefficient is one",
								"p(2) = L.one",
								By(
									Normalized,
									spec,
									quadratic,
									polynomial.PolynomialMonicDef.At(d.TermAs[A]("L.zero"), d.TermAs[A]("L.one"), p)))
							coefficients := d.Have(
								"the two remaining coefficients belong to the field",
								"p(0) ∈ L.carrier ∧ p(1) ∈ L.carrier",
								By(
									polynomialData,
									polynomial.CoefficientIn.At(
										d.TermAs[A]("L.zero"), d.TermAs[Set[A]]("L.carrier"), p, d.TermAs[Nat]("0")),
									polynomial.CoefficientIn.At(
										d.TermAs[A]("L.zero"), d.TermAs[Set[A]]("L.carrier"), p, d.TermAs[Nat]("1"))))
							short := d.Have(
								"the coefficients vanish from index three on",
								"vec⟨suc(2)⟩(p)",
								By(
									Normalized,
									polynomialData,
									quadratic,
									polynomial.DegreeVec.At(d.TermAs[A]("L.zero"), d.TermAs[Set[A]]("L.carrier"), p)))
							value := d.Have(
								"the value at x is the sum of the three terms",
								"polynomial_eval(p, x) = p(0) + p(1) * x + p(2) * (x * x)",
								By(
									polynomialData,
									short,
									polynomial_evaluation.EvalVecThree.Read(field.RingOn.Read(fieldL)).At(p, xm)))
							vanishes := d.Have(
								"the root satisfies a monic quadratic equation",
								"p(0) + p(1) * x + x * x = L.zero",
								ByArith(fieldL, coefficients, leading, value, spec, xIn))
							one, two := d.TermAs[A]("L.one"), d.TermAs[A]("L.one + L.one")
							constant, linear := d.TermAs[A]("p(0)"), d.TermAs[A]("p(1)")
							discriminantIn := d.Have(
								"the discriminant p(1)·p(1) − 4p(0) lies in K",
								"p(1) * p(1) - (L.one + L.one) * (L.one + L.one) * p(0) ∈ K",
								By(
									fieldL,
									subfieldK,
									polynomialData,
									field.SubfieldOne.At(L, K),
									field.SubfieldAdd.At(L, K, one, one),
									field.SubfieldMul.At(L, K, linear, linear),
									field.SubfieldMul.At(L, K, two, two),
									field.SubfieldMul.At(L, K, d.TermAs[A]("(L.one + L.one) * (L.one + L.one)"), constant),
									field.SubfieldSub.Read(fieldL).At(
										K, d.TermAs[A]("p(1) * p(1)"), d.TermAs[A]("(L.one + L.one) * (L.one + L.one) * p(0)"))))
							discriminantRoot := d.Have(
								"every element of K is a square, the discriminant among them",
								"∃s:A. s ∈ K ∧ s * s = p(1) * p(1) - (L.one + L.one) * (L.one + L.one) * p(0)",
								By(
									discriminantIn,
									everySquare.At(d.TermAs[A]("p(1) * p(1) - (L.one + L.one) * (L.one + L.one) * p(0)"))))
							d.Show(
								"the quadratic formula puts the root x in K",
								By(
									subfieldK,
									twoNonzero,
									polynomialData,
									discriminantRoot,
									vanishes,
									field.QuadraticFormula.Read(fieldL).At(K, constant, linear, xm)))
						}))))
			}))
		equal := arg.Have(
			"the extension equals K",
			"E = K",
			BySets(allIn, contains))
		degreeOne := arg.Have(
			"the extension therefore has degree one",
			"extension_degree(L, K, E) = 1",
			By(
				equal,
				subfieldK,
				subfieldE,
				contains,
				finite,
				field_extension.DegreeOneIff.Read(fieldL).At(K, E)))
		arg.Show(
			"one and two cannot be the same extension degree",
			ByArith(degreeOne, degreeTwo))
	}),
})}
