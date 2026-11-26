// coprime_forms.go — two forms F and G of one degree r over k without a
// common zero on the curve generate every form of large degree modulo the
// curve's ideal over k, which is prime. Their combinations F·U + G·V + W,
// with W in the ideal, have codimension at most h(d) − h(d − r) among the
// forms of degree d and no common zero in projective space, so the graded
// Nullstellensatz makes every form of large degree one. At a point x of the
// curve the value of a form of degree d + r is then F(x)·p + G(x)·q, with p
// and q values of forms of degree d.

package projective_form_pair

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// CoprimeFormsGenerate — two forms F and G over k of one degree r with no
// common zero on a smooth projective equation curve generate every form of
// large degree modulo its ideal J: from some d on, a form of degree d + r is
// F·P₀ + G·P₁ + W with P₀ and P₁ forms of degree d and W in J. The
// combinations of degree d, the forms F·U + G·V + W with U and V of degree
// d − r and W in J, are a subspace closed under multiplication by forms.
// They hold J's forms and F and G times every form of degree d − r, and F
// or G lies outside the prime J, both inside vanishing at a point of the
// curve; so their codimension is at most h(d) − h(d − r) = e·r
// (projective_curve.HyperplaneSectionBound). No point of projective space
// is a zero of all of them: off the curve an equation does not vanish
// there, on it F or G does not. The graded Nullstellensatz makes every form
// of large degree a combination.
var CoprimeFormsGenerate = coprimeFormsGenerateThm{family.Add(registry.ProofEntry{
	Name: "CoprimeFormsGenerate",
	Key:  "prop_676d026d7907ee3f",
	Reading: "This is the projective Nullstellensatz for the ideal (E, F, G), read " +
		"through a dimension count: the Hilbert function of a hyperplane section bounds the " +
		"codimension of the combinations. Without the no-common-zero hypothesis it fails at " +
		"every common zero, where every F·P₀ + G·P₁ vanishes and some form of every degree " +
		"does not. The degree r may be zero: forms of degree zero without a common zero " +
		"include a nonzero constant, and every form is a multiple of it. The closed field M " +
		"is read only by the graded Nullstellensatz, which would find a common zero in it.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n r:num. ∀E:set((num → num) → A). ∀F G:((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, G)",
			"«noCommonZero»",
		},
		Conclusion: "∃N:num. ∀d:num. " +
			"    N ≤ d ⇒ " +
			"    (∀P:((num → num) → A). " +
			"        homogeneous_polynomial(«hilbertCoefficients», n, d + r, P) ⇒ " +
			"        ∃P₀ P₁ W:((num → num) → A). " +
			"            homogeneous_polynomial(«hilbertCoefficients», n, d, P₀) ∧ " +
			"            homogeneous_polynomial(«hilbertCoefficients», n, d, P₁) ∧ " +
			"            W ∈ ideal_span(«polynomials», E) ∧ " +
			"            P = «combination»(P₀, P₁, W))",
		Abbrev: Abbrev{
			{Name: "forms", Text: "λd:num. " +
				"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"},
			{Name: "formSpace", Text: "λd:num. " +
				"    mk_module(fun_add, " +
				"        fun_zero, " +
				"        fun_neg, " +
				"        λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"        «forms»(d))"},
			{Name: "ideal", Text: "ideal_span(«polynomials», E)"},
			{Name: "polynomialsOverK", Text: "polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})"},
			{Name: "combination", Text: "λU:((num → num) → A). λV:((num → num) → A). λW:((num → num) → A). " +
				"    fun_add(fun_add(polynomial_algebra_mul(«hilbertCoefficients», F, U), " +
				"            polynomial_algebra_mul(«hilbertCoefficients», G, V)), " +
				"        W)"},
			{Name: "combinations", Text: "λd:num. " +
				"    {P:(num → num) → A | " +
				"        homogeneous_polynomial(«hilbertCoefficients», n, d, P) ∧ " +
				"        ∃U V W:((num → num) → A). " +
				"            homogeneous_polynomial(«hilbertCoefficients», n, d - r, U) ∧ " +
				"            homogeneous_polynomial(«hilbertCoefficients», n, d - r, V) ∧ " +
				"            W ∈ «ideal» ∧ " +
				"            P = «combination»(U, V, W)}"},
			{Name: "power", Text: "λl:num. λs:num. " +
				"    monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
				"        polynomial_algebra_one(«hilbertCoefficients»), " +
				"        polynomial_algebra_var(«hilbertCoefficients», l), " +
				"        s)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, r *Expr[Nat],
		E *Expr[Set[_Polynomial]],
		F, G *Arrow[Fun[Nat, Nat], A],
		closed, curve, formF, formG, coprime Fact,
	) {
		K := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
		fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		identityMap := a.TermAs[Fun[A, A]]("λa:A. a")
		variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
		zeroPoly := a.TermAs[_Polynomial]("fun_zero")
		combinations := a.TermAs[Fun[Nat, Set[_Polynomial]]]("«combinations»")
		subK := projective_curve.CurveConstantsSubfield.Read(curve)
		equations := projective_curve.CurveEquationsForms.Read(curve)
		_, e, _, slope := a.Unpack3As[Nat, Nat, Nat](
			projective_curve.CurveHilbertEventuallyLinear.Read(curve), "g", "e", "N")
		growth := a.Conjuncts(
			slope,
			"the slope e is positive",
			"and h(d) + g = e·d + 1 from N on")
		fieldRingOn := field.RingOn.Read(M)
		scalars := a.Have(
			"k is a commutative ring",
			"comm_ring_on(«hilbertCoefficients»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k)))
		// The ring of polynomials over k with its operations written out, the
		// sums coefficientwise and the product the convolution: the ring the
		// identities among combinations below are computed in and its laws
		// read.
		arithmetic := a.Simplified(
			GroupPremises(scalars, At(polynomial_algebra.PolynomialAlgebraCommRingOn, K, variables)),
			Fwd(polynomial_algebra.PolynomialAlgebraRingDef))
		prime := a.Have(
			"the ideal J over k is prime",
			"prime_ideal(«polynomials», «ideal»)",
			By(curve, Read(projective_curve.CurveIdealPrime, M).At(k, n, E)))
		ideal := a.Have(
			"so it is an ideal",
			"ring_ideal(«polynomials», «ideal»)",
			By(prime, ring_ideal.PrimeIdealIdeal))
		polynomial := a.Have(
			"a form is a polynomial over k",
			Statement{
				Binders:    "∀d:num. ∀P:((num → num) → A).",
				Hypotheses: []string{"homogeneous_polynomial(«hilbertCoefficients», n, d, P)"},
				Conclusion: "P ∈ «polynomialsOverK»",
			},
			By(homogeneous_polynomial.FormPolynomial))
		fg := a.Have(
			"F and G are polynomials over k",
			"F ∈ «polynomialsOverK» ∧ G ∈ «polynomialsOverK»",
			By(formF, formG, polynomial))
		inIdeal := a.Have(
			"and so is a member of the ideal",
			"«ideal» ⊆ «polynomialsOverK»",
			By(ideal, ring_ideal.IdealSubset))
		zero := a.Have(
			"zero is a form of every degree",
			"∀d:num. homogeneous_polynomial(«hilbertCoefficients», n, d, fun_zero)",
			By(
				homogeneous_polynomial.HomogeneousPolynomialDef,
				comm_ring.ZeroIn.Read(arithmetic),
				function_module.FunZeroDef))
		inclusion := a.Have(
			"k includes into M",
			"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
			By(
				subK,
				field.SubfieldSubring.Read(M).At(k),
				ring_homomorphism.SubringInclusionHom.Read(fieldRingOn).At(k)))
		combine := a.Have(
			"a form of degree d that is F·P₀ + G·P₁ + Q, with P₀ and "+
				"P₁ forms of degree d − r and Q in J, is a combination",
			Statement{
				Binders: "∀d:num. ∀P P₀ P₁ Q:((num → num) → A).",
				Hypotheses: []string{
					"homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
					"homogeneous_polynomial(«hilbertCoefficients», n, d - r, P₀)",
					"homogeneous_polynomial(«hilbertCoefficients», n, d - r, P₁)",
					"Q ∈ «ideal»",
					"P = «combination»(P₀, P₁, Q)",
				},
				Conclusion: "P ∈ «combinations»(d)",
			},
			BySets())
		multiples := a.Have(
			"from degree r on, a form times a combination is a combination",
			Statement{
				Binders: "∀d s:num. ∀H P:((num → num) → A).",
				Hypotheses: []string{
					"r ≤ d",
					"homogeneous_polynomial(«hilbertCoefficients», n, s, H)",
					"P ∈ «combinations»(d)",
				},
				Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», H, P) ∈ «combinations»(d + s)",
			},
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				sv := b.FixAs[Nat]("s")
				H := b.FixAs[_Polynomial]("H")
				P := b.FixAs[_Polynomial]("P")
				given := b.Conjuncts(
					b.Assume(),
					"r ≤ d",
					"H is a form of degree s",
					"P is a combination")
				below, formH := given[0], given[1]
				parts := b.Conjuncts(
					given[2],
					"P is a form of degree d",
					"and F·U + G·V + W")
				U, V, W, shape := b.Unpack3As[_Polynomial, _Polynomial, _Polynomial](parts[1], "U", "V", "W")
				pieces := b.Conjuncts(
					shape,
					"U is a form of degree d − r",
					"so is V",
					"W lies in J",
					"P = F·U + G·V + W")
				degree := b.Have(
					"s + (d − r) is (d + s) − r",
					"s + (d - r) = (d + s) - r",
					ByArith(below))
				shifted := b.TermAs[Nat]("d - r")
				cofactor0 := b.Simplified(
					b.Have(
						"H·U is a form of degree s + (d − r)",
						"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    s + (d - r), "+
							"    polynomial_algebra_mul(«hilbertCoefficients», H, U))",
						By(scalars, formH, pieces[0], At(homogeneous_polynomial.FormProduct, K, n, sv, shifted, H, U))),
					Fwd(degree))
				cofactor1 := b.Simplified(
					b.Have(
						"and so is H·V",
						"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    s + (d - r), "+
							"    polynomial_algebra_mul(«hilbertCoefficients», H, V))",
						By(scalars, formH, pieces[1], At(homogeneous_polynomial.FormProduct, K, n, sv, shifted, H, V))),
					Fwd(degree))
				turned := b.Have(
					"s + d is d + s",
					"s + d = d + s",
					ByArith())
				product := b.Simplified(
					b.Have(
						"H·P is a form of degree s + d",
						"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    s + d, "+
							"    polynomial_algebra_mul(«hilbertCoefficients», H, P))",
						By(scalars, formH, parts[0], At(homogeneous_polynomial.FormProduct, K, n, sv, d, H, P))),
					Fwd(turned))
				members := b.Have(
					"H, U, V and W are polynomials",
					"H ∈ «polynomialsOverK» ∧ U ∈ «polynomialsOverK» ∧ V ∈ «polynomialsOverK» ∧ W ∈ «polynomialsOverK»",
					By(formH, pieces[0], pieces[1], pieces[2], polynomial, inIdeal, set_basic.SubsetDef))
				expanded := b.Simplified(
					b.Have(
						"H·(F·U + G·V + W) = F·(H·U) + G·(H·V) + H·W",
						"polynomial_algebra_mul(«hilbertCoefficients», H, «combination»(U, V, W)) = "+
							"«combination»(polynomial_algebra_mul(«hilbertCoefficients», H, U), "+
							"    polynomial_algebra_mul(«hilbertCoefficients», H, V), "+
							"    polynomial_algebra_mul(«hilbertCoefficients», H, W))",
						ByArith(arithmetic, fg, members)),
					Rev(pieces[3]))
				b.Show(
					"and H·W lies in J, so H·P is a combination",
					By(
						product,
						cofactor0,
						cofactor1,
						expanded,
						members,
						pieces[2],
						ring_ideal.IdealMul.Read(ideal).AsFact().At(H, W),
						combine.At(
							b.TermAs[Nat]("d + s"),
							b.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», H, P)"),
							b.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», H, U)"),
							b.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», H, V)"),
							b.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», H, W)"))))
			}))
		subspace := a.Have(
			"from degree N + r on, the combinations of degree d are a subspace of the forms of degree d",
			"∀d:num. N + r ≤ d ⇒ submodule(«hilbertCoefficients», «formSpace»(d), «combinations»(d))",
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				large := b.Assume()
				below := b.Have(
					"r ≤ d, as N + r ≤ d",
					"r ≤ d",
					ByArith(large))
				space := b.Conjuncts(
					GroupPremises(subK, Read(projective_curve.FormsSubspace, M).At(k, n, d)),
					"the forms of degree d are a vector space",
					"meeting every ideal in a subspace")
				inside := b.Have(
					"a combination of degree d is a form of degree d",
					"«combinations»(d) ⊆ «forms»(d)",
					BySets())
				zeroSum := b.Have(
					"zero is F·0 + G·0 + 0",
					"fun_zero = «combination»(fun_zero, fun_zero, fun_zero)",
					ByArith(arithmetic, fg))
				zeroIn := b.Have(
					"so zero is a combination",
					"fun_zero ∈ «combinations»(d)",
					By(
						zero,
						zeroSum,
						ring_ideal.IdealZero.Read(ideal),
						combine.At(d, zeroPoly, zeroPoly, zeroPoly, zeroPoly)))
				sums := b.Have(
					"a sum of combinations is a combination",
					Statement{
						Binders:    "∀u v:((num → num) → A).",
						Hypotheses: []string{"u ∈ «combinations»(d)", "v ∈ «combinations»(d)"},
						Conclusion: "fun_add(u, v) ∈ «combinations»(d)",
					},
					Derive(func(c *Argument) {
						u := c.FixAs[_Polynomial]("u")
						v := c.FixAs[_Polynomial]("v")
						both := c.Conjuncts(
							c.Assume(),
							"u is a combination",
							"v is a combination")
						uParts := c.Conjuncts(
							both[0],
							"u is a form of degree d",
							"u = F·a₁ + G·b₁ + p")
						vParts := c.Conjuncts(
							both[1],
							"v is a form of degree d",
							"v = F·a₂ + G·b₂ + q")
						a1, b1, p, uShape := c.Unpack3As[_Polynomial, _Polynomial, _Polynomial](uParts[1], "a₁", "b₁", "p")
						a2, b2, q, vShape := c.Unpack3As[_Polynomial, _Polynomial, _Polynomial](vParts[1], "a₂", "b₂", "q")
						uPieces := c.Conjuncts(
							uShape,
							"a₁ is a form of degree d − r",
							"so is b₁",
							"p lies in J",
							"u = F·a₁ + G·b₁ + p")
						vPieces := c.Conjuncts(
							vShape,
							"a₂ is a form of degree d − r",
							"so is b₂",
							"q lies in J",
							"v = F·a₂ + G·b₂ + q")
						shifted := c.TermAs[Nat]("d - r")
						members := c.Have(
							"u, v, a₁, b₁, p, a₂, b₂ and q are polynomials",
							"u ∈ «polynomialsOverK» ∧ "+
								"v ∈ «polynomialsOverK» ∧ "+
								"a₁ ∈ «polynomialsOverK» ∧ "+
								"b₁ ∈ «polynomialsOverK» ∧ "+
								"p ∈ «polynomialsOverK» ∧ "+
								"a₂ ∈ «polynomialsOverK» ∧ "+
								"b₂ ∈ «polynomialsOverK» ∧ "+
								"q ∈ «polynomialsOverK»",
							By(
								uParts[0],
								vParts[0],
								uPieces[0],
								uPieces[1],
								uPieces[2],
								vPieces[0],
								vPieces[1],
								vPieces[2],
								polynomial,
								inIdeal,
								set_basic.SubsetDef))
						regrouped := c.Have(
							"u + v = F·(a₁ + a₂) + G·(b₁ + b₂) + (p + q)",
							"fun_add(u, v) = «combination»(fun_add(a₁, a₂), fun_add(b₁, b₂), fun_add(p, q))",
							ByArith(arithmetic, fg, members, uPieces[3], vPieces[3]))
						c.Show(
							"the cofactors add as forms of degree d − r and p + q lies in J",
							By(
								uParts[0],
								vParts[0],
								uPieces[0],
								uPieces[1],
								vPieces[0],
								vPieces[1],
								uPieces[2],
								vPieces[2],
								regrouped,
								scalars,
								At(homogeneous_polynomial.FormSum, K, n, d, u, v),
								At(homogeneous_polynomial.FormSum, K, n, shifted, a1, a2),
								At(homogeneous_polynomial.FormSum, K, n, shifted, b1, b2),
								ring_ideal.IdealAdd.Read(ideal).AsFact().At(p, q),
								combine.At(
									d,
									c.TermAs[_Polynomial]("fun_add(u, v)"),
									c.TermAs[_Polynomial]("fun_add(a₁, a₂)"),
									c.TermAs[_Polynomial]("fun_add(b₁, b₂)"),
									c.TermAs[_Polynomial]("fun_add(p, q)"))))
					}))
				scaled := b.Have(
					"a scalar multiple of a combination is one, a scalar multiple being the product by a constant",
					Statement{
						Binders:    "∀c:A. ∀u:((num → num) → A).",
						Hypotheses: []string{"c ∈ k", "u ∈ «combinations»(d)"},
						Conclusion: "(λm:(num → num). c * u(m)) ∈ «combinations»(d)",
					},
					Derive(func(c *Argument) {
						cv := c.FixAs[A]("c")
						u := c.FixAs[_Polynomial]("u")
						given := c.Conjuncts(
							c.Assume(),
							"c lies in k",
							"u is a combination")
						uParts := c.Conjuncts(
							given[1],
							"u is a form of degree d",
							"and F·U + G·V + W")
						constant := c.TermAs[_Polynomial]("polynomial_algebra_const(«hilbertCoefficients», c)")
						constantForm := c.Have(
							"the constant c is a form of degree zero",
							"homogeneous_polynomial(«hilbertCoefficients», "+
								"    n, "+
								"    0, "+
								"    polynomial_algebra_const(«hilbertCoefficients», c))",
							By(scalars, given[0], At(homogeneous_polynomial.FormConstant, K, n, cv)))
						product := c.Simplified(
							GroupPremises(below, constantForm, given[1], multiples.At(d, c.TermAs[Nat]("0"), constant, u)),
							Fwd(nat_arith.AddZero))
						scalarMultiple := c.Have(
							"c·u is the product of the constant c with u",
							"polynomial_algebra_mul(«hilbertCoefficients», "+
								"    polynomial_algebra_const(«hilbertCoefficients», c), "+
								"    u) = "+
								"(λm:(num → num). c * u(m))",
							By(
								scalars,
								given[0],
								uParts[0],
								polynomial.At(d, u),
								At(polynomial_algebra.PolynomialAlgebraConstMul, K, variables, cv, u)))
						c.Do(scalarMultiple.RwRev())
						c.Show(
							"a form of degree zero times a combination is a combination",
							By(product))
					}))
				b.Show(
					"so they are a subspace",
					By(space[0], inside, zeroIn, sums, scaled, submodule.SubmoduleCriterion))
			}))
		closure := a.Have(
			"from degree N + r on, a variable times a combination is a combination",
			Statement{
				Binders: "∀d i:num. ∀P:((num → num) → A).",
				Hypotheses: []string{
					"N + r ≤ d",
					"i ≤ n",
					"P ∈ «combinations»(d)",
				},
				Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», " +
					"    polynomial_algebra_var(«hilbertCoefficients», i), " +
					"    P) ∈ " +
					"«combinations»(d + 1)",
			},
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				i := b.FixAs[Nat]("i")
				P := b.FixAs[_Polynomial]("P")
				given := b.Conjuncts(
					b.Assume(),
					"d is past N + r",
					"i indexes a variable",
					"P is a combination")
				below := b.Have(
					"r ≤ d, as N + r ≤ d",
					"r ≤ d",
					ByArith(given[0]))
				b.Show(
					"the variable is a form of degree one",
					By(
						below,
						given[1],
						given[2],
						scalars,
						At(homogeneous_polynomial.FormVariable, K, n, i),
						multiples.At(
							d,
							b.TermAs[Nat]("1"),
							b.TermAs[_Polynomial]("polynomial_algebra_var(«hilbertCoefficients», i)"),
							P)))
			}))
		x, onCurve := a.UnpackAs[Fun[Nat, A]](projective_curve.CurveHasPoint.Read(curve), "x")
		outside := a.Have(
			"F or G lies outside J: J vanishes at the point x of the curve, where F or G does not",
			"F ∉ «ideal» ∨ G ∉ «ideal»",
			Derive(func(b *Argument) {
				inM := b.Have(
					"the coordinates of x up to n lie in M",
					"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
					By(onCurve, projective_curve.PointCoordinatesIn))
				vanishes := b.Have(
					"every equation vanishes at x",
					"∀P:((num → num) → A). P ∈ E ⇒ «at»(P) = M.zero",
					By(
						onCurve,
						At(projective_curve.PointEquationsVanish, fieldRing, k, b.TermAs[Set[A]]("M.carrier"), n, E, x)))
				evaluation := b.Have(
					"evaluation at x is a ring map from the polynomials over k into M",
					"ring_homomorphism(«polynomials», "+
						"    field_ring(M), "+
						"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, x))",
					By(subK, inM, Read(homogeneous_polynomial.EvaluationRingHom, M).At(k, n, x)))
				equationsIn := b.Have(
					"the equations are polynomials over k",
					"E ⊆ «polynomialsOverK»",
					BySets(equations, homogeneous_polynomial.FormPolynomial))
				vanishing := b.Have(
					"so J vanishes at x, its generators vanishing there",
					"«ideal» ⊆ "+
						"ring_kernel(M.zero, "+
						"    «polynomialsOverK», "+
						"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), x))",
					By(equationsIn, vanishes, ring_homomorphism.IdealSpanInKernel.Read(evaluation).At(E)))
				zeroAt := b.Have(
					"every member of J takes the value zero at x",
					Statement{
						Binders:    "∀P:((num → num) → A).",
						Hypotheses: []string{"P ∈ «ideal»"},
						Conclusion: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), x, P) = " +
							"M.zero",
					},
					BySets(
						vanishing,
						ring_homomorphism.RingKernelDef.At(
							b.TermAs[A]("M.zero"),
							b.TermAs[Set[_Polynomial]]("«polynomialsOverK»"),
							b.TermAs[Fun[_Polynomial, A]](
								"polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), x)"))))
				b.Show(
					"F and G both in J would both vanish at x",
					By(zeroAt, coprime.At(x), onCurve))
			}))
		bound := a.Have(
			"from degree N + r on, the combinations of degree d have codimension at most e·r",
			Statement{
				Binders: "∀d:num.",
				Hypotheses: []string{
					"N + r ≤ d",
				},
				Conclusion: "module_dim(«hilbertCoefficients», " +
					"    quotient_module(«formSpace»(d), «combinations»(d))) ≤ " +
					"e * r",
			},
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				large := b.Assume()
				shifted := b.TermAs[Nat]("d - r")
				degree := b.Have(
					"r + (d − r) is d",
					"r + (d - r) = d",
					ByArith(large))
				holdsIdeal := b.Have(
					"the combinations hold the forms of degree d in J",
					"«forms»(d) ∩ «ideal» ⊆ «combinations»(d)",
					Derive(func(c *Argument) {
						c.Do(Simp(Fwd(set_basic.SubsetDef)))
						P := c.FixAs[_Polynomial]("P")
						given := c.Assume()
						formP := c.Have(
							"P is a form of degree d in J",
							"homogeneous_polynomial(«hilbertCoefficients», n, d, P) ∧ P ∈ «ideal»",
							BySets(given))
						alone := c.Have(
							"P is F·0 + G·0 + P",
							"P = «combination»(fun_zero, fun_zero, P)",
							ByArith(arithmetic, fg, GroupPremises(formP, polynomial.At(d, P))))
						c.Show(
							"so it is a combination",
							By(formP, zero, alone, combine.At(d, P, zeroPoly, zeroPoly, P)))
					}))
				multiplesF := b.Have(
					"they hold F times every form of degree d − r",
					Statement{
						Binders:    "∀Q:((num → num) → A).",
						Hypotheses: []string{"homogeneous_polynomial(«hilbertCoefficients», n, d - r, Q)"},
						Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», F, Q) ∈ «combinations»(d)",
					},
					Derive(func(c *Argument) {
						Q := c.FixAs[_Polynomial]("Q")
						formQ := c.Assume()
						product := c.Simplified(
							c.Have(
								"F·Q is a form of degree r + (d − r)",
								"homogeneous_polynomial(«hilbertCoefficients», "+
									"    n, "+
									"    r + (d - r), "+
									"    polynomial_algebra_mul(«hilbertCoefficients», F, Q))",
								By(scalars, formF, formQ, At(homogeneous_polynomial.FormProduct, K, n, r, shifted, F, Q))),
							Fwd(degree))
						alone := c.Have(
							"F·Q is F·Q + G·0 + 0",
							"polynomial_algebra_mul(«hilbertCoefficients», F, Q) = «combination»(Q, fun_zero, fun_zero)",
							ByArith(arithmetic, fg, GroupPremises(formQ, polynomial.At(shifted, Q))))
						c.Show(
							"so it is a combination",
							By(
								product,
								formQ,
								zero,
								alone,
								ring_ideal.IdealZero.Read(ideal),
								combine.At(
									d,
									c.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», F, Q)"),
									Q,
									zeroPoly,
									zeroPoly)))
					}))
				multiplesG := b.Have(
					"and G times every form of degree d − r",
					Statement{
						Binders:    "∀Q:((num → num) → A).",
						Hypotheses: []string{"homogeneous_polynomial(«hilbertCoefficients», n, d - r, Q)"},
						Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», G, Q) ∈ «combinations»(d)",
					},
					Derive(func(c *Argument) {
						Q := c.FixAs[_Polynomial]("Q")
						formQ := c.Assume()
						product := c.Simplified(
							c.Have(
								"G·Q is a form of degree r + (d − r)",
								"homogeneous_polynomial(«hilbertCoefficients», "+
									"    n, "+
									"    r + (d - r), "+
									"    polynomial_algebra_mul(«hilbertCoefficients», G, Q))",
								By(scalars, formG, formQ, At(homogeneous_polynomial.FormProduct, K, n, r, shifted, G, Q))),
							Fwd(degree))
						alone := c.Have(
							"G·Q is F·0 + G·Q + 0",
							"polynomial_algebra_mul(«hilbertCoefficients», G, Q) = «combination»(fun_zero, Q, fun_zero)",
							ByArith(arithmetic, fg, GroupPremises(formQ, polynomial.At(shifted, Q))))
						c.Show(
							"so it is a combination",
							By(
								product,
								formQ,
								zero,
								alone,
								ring_ideal.IdealZero.Read(ideal),
								combine.At(
									d,
									c.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», G, Q)"),
									zeroPoly,
									Q,
									zeroPoly)))
					}))
				cut := b.Have(
					"so the one of F and G outside the prime J cuts the codimension to at most h(d) − h(d − r)",
					"module_dim(«hilbertCoefficients», quotient_module(«formSpace»(d), «combinations»(d))) + "+
						"projective_hilbert_function(field_ring(M), k, n, E, d - r) ≤ "+
						"projective_hilbert_function(field_ring(M), k, n, E, d)",
					Derive(func(c *Argument) {
						c.Cases(c.TermAs[Bool]("F ∈ «ideal»"))
						c.When(
							"with F in J, G lies outside it",
							func(w *Argument, inside Fact) {
								outsideG := w.Have(
									"G lies outside J",
									"G ∉ «ideal»",
									By(inside, outside))
								w.Show(
									"modulo J, G cuts the codimension",
									By(
										subK,
										prime,
										fg,
										outsideG,
										subspace.At(d),
										large,
										holdsIdeal,
										multiplesG,
										Read(projective_curve.HyperplaneSectionBound, M).At(
											k, n, d, shifted, E, w.TermAs[Set[_Polynomial]]("«combinations»(d)"), G)))
							})
						c.Otherwise(
							"with F outside J, F cuts it",
							func(w *Argument, outsideF Fact) {
								w.Show(
									"modulo J, F cuts the codimension",
									By(
										subK,
										prime,
										fg,
										outsideF,
										subspace.At(d),
										large,
										holdsIdeal,
										multiplesF,
										Read(projective_curve.HyperplaneSectionBound, M).At(
											k, n, d, shifted, E, w.TermAs[Set[_Polynomial]]("«combinations»(d)"), F)))
							})
					}))
				sum := b.Have(
					"(d − r) + r is d",
					"(d - r) + r = d",
					ByArith(large))
				distributed := b.Simplified(nat_arith.LeftAddDistrib.At(e, shifted, r), Fwd(sum))
				b.Show(
					"h(d) − h(d − r) = e·d − e·(d − r) = e·r",
					ByArith(cut, large, growth[1].At(d), growth[1].At(shifted), distributed))
			}))
		noZero := a.Have(
			"no point of projective space over M is a zero of every combination",
			Statement{
				Binders: "∀z:(num → A).",
				Hypotheses: []string{
					"z ∈ projective_equation_points(field_ring(M), k, M.carrier, n, ∅)",
				},
				Conclusion: "∃d:num. ∃P:((num → num) → A). " +
					"    N + r ≤ d ∧ " +
					"    P ∈ «combinations»(d) ∧ " +
					"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, z, P) ≠ M.zero",
			},
			Derive(func(b *Argument) {
				z := b.FixAs[Fun[Nat, A]]("z")
				point := b.Assume()
				coordinates := b.Conjuncts(
					b.Unfolded(point, projective_curve.ProjectiveEquationPointsDef),
					"the coordinates of z up to n lie in M",
					"those beyond n are zero",
					"one of them is one, the earlier ones zero",
					"and no equation is imposed")
				inM := coordinates[0]
				onCurve := b.Have(
					"where every equation vanishes, z is a point of the curve",
					Statement{
						Hypotheses: []string{
							"∀Q:((num → num) → A). " +
								"    Q ∈ E ⇒ " +
								"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, Q) = M.zero",
						},
						Conclusion: "z ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E)",
					},
					Derive(func(c *Argument) {
						vanishes := c.Assume()
						c.Show(
							"z has the coordinates of a point, and the equations vanish at it",
							Simp(Fwd(projective_curve.ProjectiveEquationPointsDef)),
							By(coordinates[0], coordinates[1], coordinates[2], vanishes))
					}))
				j, normalized := b.UnpackAs[Nat](coordinates[2], "j")
				unit := b.Conjuncts(
					normalized,
					"j ≤ n",
					"z(j) = 1",
					"and the coordinates before j are zero")
				evaluation := b.Have(
					"evaluation at z is a ring map from the polynomials over k into M",
					"ring_homomorphism(«polynomials», "+
						"    field_ring(M), "+
						"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, z))",
					By(subK, inM, Read(homogeneous_polynomial.EvaluationRingHom, M).At(k, n, z)))
				raise := b.TermAs[Nat]("N + r")
				variable := b.TermAs[_Polynomial]("polynomial_algebra_var(«hilbertCoefficients», j)")
				power := b.TermAs[_Polynomial]("«power»(j, N + r)")
				powerForm := b.Simplified(
					b.Have(
						"Xⱼ^(N + r) is a form of degree 1·(N + r)",
						"homogeneous_polynomial(«hilbertCoefficients», n, 1 * (N + r), «power»(j, N + r))",
						By(
							scalars,
							unit[0],
							At(homogeneous_polynomial.FormVariable, K, n, j),
							At(homogeneous_polynomial.FormPower, K, n, b.TermAs[Nat]("1"), variable, raise))),
					Fwd(nat_arith.OneMul))
				multiplicative := comm_ring.MulMonoidOn.Read(fieldRingOn)
				raised := b.Have(
					"Xⱼ^(N + r) times a form H is a form of degree raised by N + r, with the value of H at z",
					Statement{
						Binders:    "∀t:num. ∀H:((num → num) → A).",
						Hypotheses: []string{"homogeneous_polynomial(«hilbertCoefficients», n, t, H)"},
						Conclusion: "homogeneous_polynomial(«hilbertCoefficients», " +
							"    n, " +
							"    (N + r) + t, " +
							"    polynomial_algebra_mul(«hilbertCoefficients», «power»(j, N + r), H)) ∧ " +
							"polynomial_algebra_eval(«hilbertCoefficients», " +
							"    field_ring(M), " +
							"    (λa:A. a), " +
							"    z, " +
							"    polynomial_algebra_mul(«hilbertCoefficients», «power»(j, N + r), H)) = " +
							"polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, H)",
					},
					Derive(func(c *Argument) {
						t := c.FixAs[Nat]("t")
						H := c.FixAs[_Polynomial]("H")
						formH := c.Assume()
						valueH := c.TermAs[A](
							"polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, H)")
						c.Show(
							"the degrees add, and Xⱼ takes the value z(j) = 1 at z",
							By(
								scalars,
								formH,
								powerForm,
								unit[0],
								unit[1],
								inM,
								inclusion,
								polynomial.At(t, H),
								polynomial.At(raise, power),
								At(homogeneous_polynomial.FormVariable, K, n, j),
								polynomial.At(c.TermAs[Nat]("1"), variable),
								At(homogeneous_polynomial.FormProduct, K, n, raise, t, power, H),
								ring_homomorphism.MapMul.Read(evaluation).AsFact().At(power, H),
								ring_homomorphism.RingMapPower.Read(evaluation).AsFact().At(raise, variable),
								ring_homomorphism.MapIn.Read(evaluation).AsFact().At(H),
								polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(K, fieldRing, identityMap, z, j),
								comm_monoid.IdentityPowOn.Read(multiplicative).AsFact().At(raise),
								comm_monoid.LeftIdentityOn.Read(multiplicative).AsFact().At(valueH)))
					}))
				b.Cases(b.TermAs[Bool](
					"∀Q:((num → num) → A). " +
						"    Q ∈ E ⇒ " +
						"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, Q) = M.zero"))
				b.When(
					"on the curve, F or G does not vanish at z",
					func(c *Argument, vanishes Fact) {
						degree := c.Have(
							"((N + r) + r) − r is N + r, and (N + r) + r is at least N + r",
							"((N + r) + r) - r = N + r ∧ N + r ≤ (N + r) + r",
							ByArith())
						powerMember := c.Have(
							"Xⱼ^(N + r) is a polynomial",
							"«power»(j, N + r) ∈ «polynomialsOverK»",
							By(powerForm, polynomial.At(raise, power)))
						lifted := c.TermAs[Nat]("(N + r) + r")
						c.Cases(c.TermAs[Bool](
							"polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, F) = M.zero"))
						c.When(
							"F vanishes at z, so G does not, and Xⱼ^(N + r)·G is a combination of degree (N + r) + r",
							func(w *Argument, zeroF Fact) {
								alone := w.Have(
									"Xⱼ^(N + r)·G is F·0 + G·Xⱼ^(N + r) + 0",
									"polynomial_algebra_mul(«hilbertCoefficients», «power»(j, N + r), G) = "+
										"«combination»(fun_zero, «power»(j, N + r), fun_zero)",
									ByArith(arithmetic, fg, powerMember))
								multiple := w.TermAs[_Polynomial](
									"polynomial_algebra_mul(«hilbertCoefficients», «power»(j, N + r), G)")
								w.Take(lifted)
								w.Take(multiple)
								w.Show(
									"its value at z is G(z) ≠ 0",
									By(
										degree,
										alone,
										zero,
										powerForm,
										zeroF,
										vanishes,
										onCurve,
										coprime.At(z),
										ring_ideal.IdealZero.Read(ideal),
										GroupPremises(formG, raised.At(r, G)),
										combine.At(lifted, multiple, zeroPoly, power, zeroPoly)))
							})
						c.Otherwise(
							"F does not vanish at z, and Xⱼ^(N + r)·F is a combination of degree (N + r) + r",
							func(w *Argument, nonzeroF Fact) {
								alone := w.Have(
									"Xⱼ^(N + r)·F is F·Xⱼ^(N + r) + G·0 + 0",
									"polynomial_algebra_mul(«hilbertCoefficients», «power»(j, N + r), F) = "+
										"«combination»(«power»(j, N + r), fun_zero, fun_zero)",
									ByArith(arithmetic, fg, powerMember))
								multiple := w.TermAs[_Polynomial](
									"polynomial_algebra_mul(«hilbertCoefficients», «power»(j, N + r), F)")
								w.Take(lifted)
								w.Take(multiple)
								w.Show(
									"its value at z is F(z) ≠ 0",
									By(
										degree,
										alone,
										zero,
										powerForm,
										nonzeroF,
										ring_ideal.IdealZero.Read(ideal),
										GroupPremises(formF, raised.At(r, F)),
										combine.At(lifted, multiple, power, zeroPoly, zeroPoly)))
							})
					})
				b.Otherwise(
					"off the curve, an equation Q does not vanish at z, and Q·Xⱼ^(N + r) lies in J",
					func(c *Argument, notAll Fact) {
						Q, offQ := c.ObtainAs[_Polynomial](
							"some equation Q does not vanish at z",
							"∃Q:((num → num) → A). "+
								"    Q ∈ E ∧ "+
								"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, Q) ≠ M.zero",
							By(notAll))
						off := c.Conjuncts(
							offQ,
							"Q is an equation",
							"Q(z) is not zero")
						t, formQ := c.UnpackAs[Nat](equations.At(c.MemberOf[on.Any](Q, off[0])), "t")
						product := c.TermAs[_Polynomial](
							"polynomial_algebra_mul(«hilbertCoefficients», «power»(j, N + r), Q)")
						lifted := c.Conjuncts(
							GroupPremises(formQ, raised.At(t, Q)),
							"Xⱼ^(N + r)·Q is a form of degree (N + r) + t",
							"with the value Q(z) at z")
						members := c.Have(
							"Q and Xⱼ^(N + r) are polynomials",
							"Q ∈ «polynomialsOverK» ∧ «power»(j, N + r) ∈ «polynomialsOverK»",
							By(formQ, powerForm, polynomial))
						alone := c.Have(
							"Xⱼ^(N + r)·Q is F·0 + G·0 + Xⱼ^(N + r)·Q",
							"polynomial_algebra_mul(«hilbertCoefficients», «power»(j, N + r), Q) = "+
								"«combination»(fun_zero, "+
								"    fun_zero, "+
								"    polynomial_algebra_mul(«hilbertCoefficients», «power»(j, N + r), Q))",
							ByArith(arithmetic, fg, members))
						past := c.Have(
							"(N + r) + t is at least N + r",
							"N + r ≤ (N + r) + t",
							ByArith())
						degreeQ := c.TermAs[Nat]("(N + r) + t")
						c.Take(degreeQ)
						c.Take(product)
						c.Show(
							"Q lies in J, so its multiple does, and its value at z is Q(z) ≠ 0",
							By(
								past,
								alone,
								zero,
								members,
								lifted[0],
								lifted[1],
								off[0],
								off[1],
								ring_ideal.SpanContains.At(a.TermAs[module_record.RingOps[_Polynomial]]("«polynomials»"), E),
								set_basic.SubsetDef,
								ring_ideal.IdealMul.Read(ideal).AsFact().At(power, Q),
								combine.At(degreeQ, product, zeroPoly, zeroPoly, product)))
					})
			}))
		D, generated := a.UnpackAs[Nat](
			GroupPremises(
				closed,
				subK,
				subspace,
				closure,
				bound,
				noZero,
				Read(GradedNullstellensatz, M).At(
					k, n, a.TermAs[Nat]("e * r"), a.TermAs[Nat]("N + r"), combinations)),
			"D")
		a.Take(D)
		a.Show(
			"from degree D on every form is a combination: a form P of degree d "+
				"+ r with D ≤ d is F·U + G·V + W, with U and V of degree d and W in J",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("d")
				past := b.Assume()
				b.FixAs[_Polynomial]("P")
				formP := b.Assume()
				beyond := b.Have(
					"D ≤ d + r, as D ≤ d",
					"D ≤ d + r",
					ByArith(past))
				inCombinations := b.Have(
					"P, a form of degree d + r ≥ D, is a combination",
					"P ∈ «combinations»(d + r)",
					By(formP, beyond, generated.At(b.TermAs[Nat]("d + r")), set_basic.SubsetDef))
				U, V, W, shape := b.Obtain3As[_Polynomial, _Polynomial, _Polynomial](
					"so P is F·U + G·V + W with U and V of degree (d + r) − r and W in J",
					"∃U V W:((num → num) → A). "+
						"    homogeneous_polynomial(«hilbertCoefficients», n, (d + r) - r, U) ∧ "+
						"    homogeneous_polynomial(«hilbertCoefficients», n, (d + r) - r, V) ∧ "+
						"    W ∈ «ideal» ∧ "+
						"    P = «combination»(U, V, W)",
					By(inCombinations))
				pieces := b.Conjuncts(
					shape,
					"U is a form of degree (d + r) − r",
					"so is V",
					"W lies in J",
					"P = F·U + G·V + W")
				degree := b.Have(
					"(d + r) − r is d",
					"(d + r) - r = d",
					ByArith())
				cofactor0 := b.Simplified(pieces[0], Fwd(degree))
				cofactor1 := b.Simplified(pieces[1], Fwd(degree))
				b.Take(U)
				b.Take(V)
				b.Take(W)
				b.Show(
					"U and V are forms of degree d, W lies in J, and P = F·U + G·V + W",
					By(cofactor0, cofactor1, pieces[2], pieces[3]))
			}))
	}),
})}

// CoprimeValuesGenerate — at a point x of the curve, two forms F, G of one
// degree r without a common zero generate the values of the forms of large
// degree: from some N on, the value at x of a form of degree d + r is
// F(x)·p + G(x)·q with p, q values of forms of degree d. CoprimeFormsGenerate
// writes the form as F·Q₀ + G·Q₁ modulo the ideal, and the ideal, spanned
// by equations vanishing at x, lies in the kernel of evaluation at x.
var CoprimeValuesGenerate = coprimeValuesGenerateThm{family.Add(registry.ProofEntry{
	Name: "CoprimeValuesGenerate",
	Key:  "prop_7a90a9888a566f4f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k K:set(A). " +
			"∀n r:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀F G:((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
			"subfield(M, K)",
			"x ∈ projective_equation_points(field_ring(M), k, K, n, E)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, G)",
			"«noCommonZero»",
		},
		Conclusion: "∃N:num. ∀d:num. ∀w:A. " +
			"    N ≤ d ∧ w ∈ «values»(d + r) ⇒ " +
			"    ∃p q:A. p ∈ «values»(d) ∧ q ∈ «values»(d) ∧ w = «at»(F) * p + «at»(G) * q",
		Abbrev: Abbrev{
			{Name: "values", Text: "λd:num. " +
				"    image(«at», {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})"},
			{Name: "kernel", Text: "ring_kernel(M.zero, «polynomials».carrier, «at»)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, K *Expr[Set[A]],
		n, r *Expr[Nat],
		E *Expr[Set[_Polynomial]],
		x *Arrow[Nat, A],
		F, G *Arrow[Fun[Nat, Nat], A],
		closed, curve, subfieldBig, onCurve, formF, formG, coprime Fact,
	) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		subfieldK := projective_curve.CurveConstantsSubfield.Read(curve)
		inK := a.Have(
			"the coordinates of x up to n lie in K",
			"∀i:num. i ≤ n ⇒ x(i) ∈ K",
			By(onCurve, projective_curve.PointCoordinatesIn))
		vanishes := a.Have(
			"the equations vanish at x",
			"∀P:((num → num) → A). P ∈ E ⇒ «at»(P) = M.zero",
			By(onCurve, At(projective_curve.PointEquationsVanish, fieldRing, k, K, n, E, x)))
		coordinates := a.Have(
			"the coordinates of x up to n lie in M",
			"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
			BySets(inK, field.SubfieldSubset.At(fieldM, K), subfieldBig))
		evaluation := a.Have(
			"evaluation at x is a ring homomorphism",
			"ring_homomorphism(«polynomials», field_ring(M), «at»)",
			By(At(homogeneous_polynomial.EvaluationRingHom, fieldM, k, n, x), M, subfieldK, coordinates))
		polynomialRing := a.Have(
			"the polynomials are a commutative ring",
			"comm_ring_on(«polynomials»)",
			By(subfieldK, field.SubfieldCommRing.Read(M).At(k), polynomial_algebra.PolynomialAlgebraCommRingOn))
		equationsPolynomials := a.Have(
			"each equation is a form, so a polynomial",
			"E ⊆ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
			BySets(projective_curve.CurveEquationsForms.Read(curve), homogeneous_polynomial.FormPolynomial))
		idealIn := a.Have(
			"so the ideal they span lies in the kernel of evaluation at x, the equations vanishing there",
			"ideal_span(«polynomials», E) ⊆ «kernel»",
			By(equationsPolynomials, vanishes, ring_homomorphism.IdealSpanInKernel.Read(evaluation).At(E)))
		bound, generate := a.UnpackAs[Nat](
			GroupPremises(
				closed, curve, formF, formG, coprime, CoprimeFormsGenerate.Read(M).At(k, n, r, E, F, G)),
			"N")
		a.Take(bound)
		a.Show(
			"the value of a form of degree d + r is F(x)·p + G(x)·q with p, q values of forms of degree d",
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				w := b.FixAs[A]("w")
				assumed := b.Conjuncts(
					b.Assume(),
					"d is past the bound",
					"w is the value of a form of degree d + r")
				_, value := b.UnpackAs[_Polynomial](b.Have(
					"w is the value at x of a form P of degree d + r",
					"∃P:((num → num) → A). w = «at»(P) ∧ homogeneous_polynomial(«hilbertCoefficients», n, d + r, P)",
					By(
						assumed[1],
						set_basic.InImage.At(
							b.TermAs[Fun[_Polynomial, A]]("«at»"),
							b.TermAs[Set[_Polynomial]](
								"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d + r, P)}"),
							w))), "P")
				valueParts := b.Conjuncts(
					value,
					"w = P(x)",
					"P is a form of degree d + r")
				P := b.TermAs[_Polynomial]("P")
				Q0, Q1, W, cofactors := b.Unpack3As[_Polynomial, _Polynomial, _Polynomial](
					GroupPremises(assumed[0], valueParts[1], generate.At(d, P)), "Q₀", "Q₁", "W")
				parts := b.Conjuncts(
					cofactors,
					"Q₀ is a form of degree d",
					"so is Q₁",
					"W lies in the ideal",
					"P = F·Q₀ + G·Q₁ + W")
				kernelW := b.Unfolded(b.Have(
					"W lies in the kernel of evaluation at x, as the ideal does",
					"W ∈ «kernel»",
					By(idealIn, parts[2], set_basic.SubsetDef)), ring_homomorphism.RingKernelDef)
				members := b.Have(
					"P, F, G, Q₀, Q₁ and W are polynomials",
					"P ∈ «polynomials».carrier ∧ "+
						"F ∈ «polynomials».carrier ∧ "+
						"G ∈ «polynomials».carrier ∧ "+
						"Q₀ ∈ «polynomials».carrier ∧ "+
						"Q₁ ∈ «polynomials».carrier ∧ "+
						"W ∈ «polynomials».carrier",
					By(
						homogeneous_polynomial.FormPolynomial.Read(valueParts[1]),
						homogeneous_polynomial.FormPolynomial.Read(parts[0]),
						homogeneous_polynomial.FormPolynomial.Read(parts[1]),
						homogeneous_polynomial.FormPolynomial.Read(formF),
						homogeneous_polynomial.FormPolynomial.Read(formG),
						kernelW))
				FQ0 := b.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», F, Q₀)")
				GQ1 := b.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», G, Q₁)")
				products := b.Have(
					"so are F·Q₀, G·Q₁ and their sum",
					"polynomial_algebra_mul(«hilbertCoefficients», F, Q₀) ∈ «polynomials».carrier ∧ "+
						"polynomial_algebra_mul(«hilbertCoefficients», G, Q₁) ∈ «polynomials».carrier ∧ "+
						"fun_add(polynomial_algebra_mul(«hilbertCoefficients», F, Q₀), "+
						"    polynomial_algebra_mul(«hilbertCoefficients», G, Q₁)) ∈ "+
						"«polynomials».carrier",
					By(members, comm_ring.MulIn.Read(polynomialRing), comm_ring.AddIn.Read(polynomialRing)))
				expanded := b.Have(
					"evaluation at x is a ring homomorphism",
					"«at»(P) = «at»(F) * «at»(Q₀) + «at»(G) * «at»(Q₁) + «at»(W)",
					By(
						parts[3],
						members,
						products,
						ring_homomorphism.MapAdd.Read(evaluation).AsFact().At(
							b.TermAs[_Polynomial](
								"fun_add(polynomial_algebra_mul(«hilbertCoefficients», F, Q₀), "+
									"    polynomial_algebra_mul(«hilbertCoefficients», G, Q₁))"),
							W),
						ring_homomorphism.MapAdd.Read(evaluation).AsFact().At(FQ0, GQ1),
						ring_homomorphism.MapMul.Read(evaluation).AsFact().At(F, Q0),
						ring_homomorphism.MapMul.Read(evaluation).AsFact().At(G, Q1)))
				valuesIn := b.Have(
					"the values lie in M",
					"«at»(P) ∈ M.carrier ∧ "+
						"«at»(F) ∈ M.carrier ∧ "+
						"«at»(G) ∈ M.carrier ∧ "+
						"«at»(Q₀) ∈ M.carrier ∧ "+
						"«at»(Q₁) ∈ M.carrier ∧ "+
						"«at»(W) ∈ M.carrier",
					By(members, ring_homomorphism.MapIn.Read(evaluation)))
				killed := b.Have(
					"W vanishes at x, lying in the kernel",
					"«at»(W) = M.zero",
					By(kernelW))
				b.Take(b.TermAs[A]("«at»(Q₀)"))
				b.Take(b.TermAs[A]("«at»(Q₁)"))
				low := b.TermAs[Set[_Polynomial]](
					"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}")
				at := b.TermAs[Fun[_Polynomial, A]]("«at»")
				b.Do(SplitConjAll(
					Case(
						"Q₀(x) is the value of a form of degree d",
						By(parts[0], set_image.FunInImage.At(at, low, Q0))),
					Case(
						"so is Q₁(x)",
						By(parts[1], set_image.FunInImage.At(at, low, Q1))),
					Case(
						"and w = F(x)·Q₀(x) + G(x)·Q₁(x)",
						ByArith(M, killed, expanded, valueParts[0], valuesIn))))
			}))
	}),
})}
