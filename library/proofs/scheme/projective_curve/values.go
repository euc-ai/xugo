// values.go — the values of the forms of degree d at a point y of a field
// L, read along a coefficient map σ from k: evaluation is k-linear, its
// kernel the forms in the ideal, so the values span over k a space of
// dimension h(d). Inside a finite extension of σ(k) that dimension is
// bounded. At a point with one coordinate one, every power of another
// coordinate up to the d-th is the value of a form of degree d, so a
// transcendental coordinate gives a segment's worth of independent values,
// and two coordinates transcendental one over the other give a product of
// two segments' worth.

package projective_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// EvaluationLinear — evaluating the forms of degree d along σ at y is
// linear over k acting on L through σ: it is additive, being a ring
// homomorphism, and c·P is the product of P with the constant c, whose
// value is σ(c).
var EvaluationLinear = evaluationLinearThm{family.Add(registry.ProofEntry{
	Name: "EvaluationLinear",
	Key:  "prop_416edae8e4cf1d1f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀L:field_on(B). ∀k:set(A). ∀n d:num. ∀σ:(A → B). ∀y:(num → B).",
		Hypotheses: []string{
			"subfield(M, k)",
			"ring_homomorphism(«hilbertCoefficients», field_ring(L), σ)",
			"∀i:num. i ≤ n ⇒ y(i) ∈ L.carrier",
		},
		Conclusion: "module_homomorphism(«hilbertCoefficients», «formSpace», «LOverK», «evaluation»)",
		Abbrev: Abbrev{
			{Name: "formSpace", Text: "mk_module(«polynomials».add, " +
				"    «polynomials».zero, " +
				"    «polynomials».neg, " +
				"    λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"    {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})"},
			{Name: "LOverK", Text: "scalar_restriction(σ, regular_module(field_ring(L)))"},
			{Name: "evaluation", Text: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			n, d *Expr[Nat],
			σ *Arrow[A, B],
			y *Arrow[Nat, B],
			kSubfield, coefficientMap, coordinates Fact,
		) {
			rk := a.Term("«hilbertCoefficients»")
			ringL := a.Term("field_ring(L)")
			variables := a.Term("{i:num | i ≤ n}")
			ring := a.Have(
				"k, a subfield of M, is a ring",
				"comm_ring_on(«hilbertCoefficients»)",
				By(kSubfield, field.SubfieldCommRing.Read(M).At(k)))
			evaluation := a.Have(
				"evaluation along σ at y is a ring homomorphism out of the polynomials",
				"ring_homomorphism(«polynomials», field_ring(L), «evaluation»)",
				By(
					coordinates,
					coefficientMap,
					At(polynomial_algebra_evaluation.PolynomialAlgebraEvalHom, rk, ringL, σ, y, variables)))
			source := a.Have(
				"the forms of degree d are a module over k",
				"module_on(«hilbertCoefficients», «formSpace»)",
				By(kSubfield, Read(FormsSubspace, M).At(k, n, d)))
			target := a.Have(
				"L is a module over k through σ",
				"module_on(«hilbertCoefficients», «LOverK»)",
				By(
					coefficientMap,
					At(hom_module.RestrictScalarsModuleOn, rk, ringL, σ, a.Term("regular_module(field_ring(L))")),
					module.RegularModuleOn.Read(field.RingOn.Read(L))))
			values := a.Have(
				"a form takes its value in L",
				Statement{
					Binders: "∀P:((num → num) → A).",
					Hypotheses: []string{
						"homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
					},
					Conclusion: "«evaluation»(P) ∈ L.carrier",
				},
				By(ring_homomorphism.MapIn.Read(evaluation), homogeneous_polynomial.FormPolynomial))
			additive := a.Have(
				"the value of a sum is the sum of the values",
				Statement{
					Binders: "∀P Q:((num → num) → A).",
					Hypotheses: []string{
						"homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
						"homogeneous_polynomial(«hilbertCoefficients», n, d, Q)",
					},
					Conclusion: "«evaluation»(«polynomials».add(P, Q)) = «evaluation»(P) + «evaluation»(Q)",
				},
				By(ring_homomorphism.MapAdd.Read(evaluation), homogeneous_polynomial.FormPolynomial))
			scaled := a.Have(
				"the value of c·P is σ(c) times the value of P",
				Statement{
					Binders: "∀c:A. ∀P:((num → num) → A).",
					Hypotheses: []string{
						"c ∈ k",
						"homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
					},
					Conclusion: "«evaluation»(λm:(num → num). c * P(m)) = σ(c) * «evaluation»(P)",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					P := b.Fix("P")
					parts := b.Conjuncts(
						b.Assume(),
						"c lies in k",
						"P is a form of degree d")
					polynomial := homogeneous_polynomial.FormPolynomial.Read(parts[1])
					product := b.Have(
						"c·P is the product of P with the constant c",
						"polynomial_algebra_mul(«hilbertCoefficients», "+
							"    polynomial_algebra_const(«hilbertCoefficients», c), "+
							"    P) = "+
							"(λm:(num → num). c * P(m))",
						By(
							ring,
							parts[0],
							polynomial,
							At(polynomial_algebra.PolynomialAlgebraConstMul, rk, variables, c, P)))
					constants := b.Have(
						"the constants are a ring map into the polynomials",
						"ring_homomorphism(«hilbertCoefficients», "+
							"    «polynomials», "+
							"    polynomial_algebra_const(«hilbertCoefficients»))",
						By(ring, At(polynomial_algebra.PolynomialAlgebraConstHom, rk, variables)))
					b.Do(product.RwRev())
					b.Show(
						"a product evaluates to the product of the values, and the constant c to σ(c)",
						By(
							parts[0],
							polynomial,
							coefficientMap,
							ring_homomorphism.MapMul.Read(evaluation).AsFact().At(
								b.Term("polynomial_algebra_const(«hilbertCoefficients», c)"), P),
							ring_homomorphism.MapIn.Read(constants).AsFact().At(c),
							At(polynomial_algebra_evaluation.PolynomialAlgebraEvalConst, rk, ringL, σ, y, c)))
				}))
			a.Do(Unfold(module_homomorphism.ModuleHomomorphismDef))
			a.Show(
				"the forms and L are modules over k, and evaluation lands in L, adds and scales by σ",
				By(source, target, values, additive, scaled))
		}),
})}

// FormValuesDimension — the values at y of the forms of degree d are a
// subspace of L, over k acting through σ, of dimension h(d), when a form of
// degree d vanishes at y exactly when it lies in the ideal of E: evaluation
// is k-linear (EvaluationLinear), so its image is a subspace, with kernel
// the forms of degree d in the ideal, and by rank–nullity its image has the
// dimension of the quotient the Hilbert function measures.
var FormValuesDimension = formValuesDimensionThm{family.Add(registry.ProofEntry{
	Name: "FormValuesDimension",
	Key:  "prop_117e7a985407bf26",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀L:field_on(B). " +
			"∀k:set(A). " +
			"∀n d:num. " +
			"∀E:set((num → num) → A). " +
			"∀σ:(A → B). " +
			"∀y:(num → B).",
		Hypotheses: []string{
			"subfield(M, k)",
			"ring_homomorphism(«hilbertCoefficients», field_ring(L), σ)",
			"∀i:num. i ≤ n ⇒ y(i) ∈ L.carrier",
			"∀P:((num → num) → A). " +
				"    homogeneous_polynomial(«hilbertCoefficients», n, d, P) ⇒ " +
				"    («evaluation»(P) = L.zero ⇔ P ∈ ideal_span(«polynomials», E))",
		},
		Conclusion: "submodule(«hilbertCoefficients», «LOverK», «values») ∧ " +
			"finite_dimensional(«hilbertCoefficients», restrict_module(«LOverK», «values»)) ∧ " +
			"module_dim(«hilbertCoefficients», restrict_module(«LOverK», «values»)) = " +
			"projective_hilbert_function(field_ring(M), k, n, E, d)",
		Abbrev: Abbrev{
			{Name: "formSpace", Text: "mk_module(«polynomials».add, " +
				"    «polynomials».zero, " +
				"    «polynomials».neg, " +
				"    λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"    {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})"},
			{Name: "LOverK", Text: "scalar_restriction(σ, regular_module(field_ring(L)))"},
			{Name: "evaluation", Text: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y)"},
			{Name: "values", Text: "image(«evaluation», " +
				"    {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})"},
			{Name: "kernel", Text: "group_kernel(L.zero, " +
				"    {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}, " +
				"    «evaluation»)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			n, d *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			σ *Arrow[A, B],
			y *Arrow[Nat, B],
			kSubfield, coefficientMap, coordinates, generic Fact,
		) {
			rk := a.Term("«hilbertCoefficients»")
			formSpace := a.Term("«formSpace»")
			lOverK := a.Term("«LOverK»")
			evaluation := a.Term("«evaluation»")
			inverse := a.Term("M.inv")
			linear := a.Have(
				"evaluation is linear over k",
				"module_homomorphism(«hilbertCoefficients», «formSpace», «LOverK», «evaluation»)",
				By(
					M,
					L,
					kSubfield,
					coefficientMap,
					coordinates,
					At(EvaluationLinear, a.Term("M"), a.Term("L"), k, n, d, σ, y)))
			kernel := a.Have(
				"its kernel is the forms of degree d in the ideal: the generic clause",
				"«kernel» = "+
					"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)} ∩ "+
					"ideal_span(«polynomials», E)",
				Simp(Fwd(group_homomorphism.GroupKernelDef)),
				BySets(generic))
			finite := a.Have(
				"the forms of degree d are finite-dimensional",
				"finite_dimensional(«hilbertCoefficients», «formSpace»)",
				By(M, kSubfield, At(FormsDimension, a.Term("M"), k, n, d)))
			scalars := a.Have(
				"k is a field on its carrier",
				"ring_subfield(«hilbertCoefficients», M.inv, k)",
				By(kSubfield, field.SubfieldRingSubfield.Read(M).At(k, k)))
			rank := a.Have(
				"rank–nullity: the kernel and the values share the dimension of the forms",
				"module_dim(«hilbertCoefficients», restrict_module(«formSpace», «kernel»)) + "+
					"module_dim(«hilbertCoefficients», restrict_module(«LOverK», «values»)) = "+
					"module_dim(«hilbertCoefficients», «formSpace»)",
				By(
					finite,
					scalars,
					linear,
					module_homomorphism.HomSource.Read(linear),
					module_homomorphism.HomTarget.Read(linear),
					At(module_dimension.RankNullity, rk, formSpace, inverse, lOverK, evaluation)))
			quotient := a.Have(
				"the kernel and the quotient by it share the dimension of the forms",
				"module_dim(«hilbertCoefficients», restrict_module(«formSpace», «kernel»)) + "+
					"module_dim(«hilbertCoefficients», quotient_module(«formSpace», «kernel»)) = "+
					"module_dim(«hilbertCoefficients», «formSpace»)",
				By(
					finite,
					scalars,
					module_homomorphism.HomSource.Read(linear),
					module_homomorphism.KernelSubmodule.Read(linear),
					At(module_dimension.QuotientDim, rk, formSpace, inverse, a.Term("«kernel»"))))
			image := a.Have(
				"the values are finite-dimensional",
				"finite_dimensional(«hilbertCoefficients», restrict_module(«LOverK», «values»))",
				By(
					finite,
					scalars,
					linear,
					At(module_dimension.ImageDim, rk, inverse, formSpace, lOverK, evaluation)))
			hilbert := a.Have(
				"h(d) is the dimension of the forms of degree d modulo the kernel",
				"projective_hilbert_function(field_ring(M), k, n, E, d) = "+
					"module_dim(«hilbertCoefficients», quotient_module(«formSpace», «kernel»))",
				Simp(Fwd(ProjectiveHilbertFunctionDef)),
				kernel.RwRev(),
				Basic())
			a.Show(
				"so the values are a subspace of dimension h(d)",
				SplitConjAll(
					Case(
						"the image of a k-linear map is a subspace",
						By(module_homomorphism.ImageSubmodule.Read(linear))),
					Case(
						"finite-dimensional",
						By(image)),
					Case(
						"of dimension h(d)",
						ByArith(rank, quotient, hilbert, image))))
		}),
})}

// AlgebraicCoordinatesBound — when every coordinate of y is algebraic over
// σ(k), the Hilbert function is bounded by [σ(k)(y) : σ(k)]: the values of
// the forms lie in σ(k)(y), a finite extension (FiniteAlgebraicAdjoin), and
// a basis over k of the values (FormValuesDimension) stays independent
// over σ(k) (ScalarRestrictionIndependent), so has at most that many
// members.
var AlgebraicCoordinatesBound = algebraicCoordinatesBoundThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicCoordinatesBound",
	Key:  "prop_300730dd01dbc085",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀L:field_on(B). " +
			"∀k:set(A). " +
			"∀n d:num. " +
			"∀E:set((num → num) → A). " +
			"∀σ:(A → B). " +
			"∀y:(num → B).",
		Hypotheses: []string{
			"subfield(M, k)",
			"ring_homomorphism(«hilbertCoefficients», field_ring(L), σ)",
			"∀i:num. i ≤ n ⇒ y(i) ∈ L.carrier",
			"∀P:((num → num) → A). " +
				"    homogeneous_polynomial(«hilbertCoefficients», n, d, P) ⇒ " +
				"    («evaluation»(P) = L.zero ⇔ P ∈ ideal_span(«polynomials», E))",
			"∀i:num. i ≤ n ⇒ algebraic_over(L, image(σ, k), y(i))",
		},
		Conclusion: "projective_hilbert_function(field_ring(M), k, n, E, d) ≤ " +
			"extension_degree(L, image(σ, k), «adjoined»)",
		Abbrev: Abbrev{
			{Name: "evaluation", Text: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y)"},
			{Name: "coordinates", Text: "{y(i) | i:num | i ≤ n}"},
			{Name: "adjoined", Text: "field_adjoin(L, image(σ, k), «coordinates»)"},
			{Name: "LOverK", Text: "scalar_restriction(σ, regular_module(field_ring(L)))"},
			{Name: "values", Text: "image(«evaluation», " +
				"    {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})"},
			{Name: "formSpace", Text: "mk_module(«polynomials».add, " +
				"    «polynomials».zero, " +
				"    «polynomials».neg, " +
				"    λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"    {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			n, d *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			σ *Arrow[A, B],
			y *Arrow[Nat, B],
			kSubfield, coefficientMap, coordinates, generic, algebraic Fact,
		) {
			m, l := a.Term("M"), a.Term("L")
			rk := a.Term("«hilbertCoefficients»")
			ringL := a.Term("field_ring(L)")
			constants := a.TermAs[Set[B]]("image(σ, k)")
			adjoined := a.TermAs[Set[B]]("«adjoined»")
			variables := a.Term("{i:num | i ≤ n}")
			generators := a.Term("«coordinates»")
			imageParts := a.Conjuncts(
				GroupPremises(
					L,
					kSubfield,
					coefficientMap,
					ring_homomorphism.SubfieldHomomorphismEmbedding.Read(M).At(a.TermAs[FieldOps[B]]("L"), k, σ)),
				"σ(k) is a subfield of L",
				"σ is one-to-one on k")
			generatorsInL := a.Have(
				"the coordinates lie in L",
				"«coordinates» ⊆ L.carrier",
				BySets(coordinates))
			finitelyMany := a.Have(
				"there are finitely many of them",
				"finite(«coordinates»)",
				Simp(Fwd(set_image.SimpleImageGen)),
				By(
					num_segment.FiniteBelow.At(n),
					finite_set.FiniteImage.At(y, a.TermAs[Set[Nat]]("{i:num | i ≤ n}"))))
			algebraicGenerators := a.Have(
				"each of them is algebraic over σ(k)",
				"∀x:B. x ∈ «coordinates» ⇒ algebraic_over(L, image(σ, k), x)",
				BySets(algebraic))
			adjoinedField := a.Have(
				"σ(k)(y) is a subfield holding σ(k) and the coordinates, finite over σ(k)",
				"subfield(L, «adjoined») ∧ "+
					"image(σ, k) ⊆ «adjoined» ∧ "+
					"«coordinates» ⊆ «adjoined» ∧ "+
					"finite_extension(L, image(σ, k), «adjoined»)",
				By(
					L,
					finitelyMany,
					algebraicGenerators,
					imageParts[0],
					generatorsInL,
					At(field.SubfieldSubset, l, constants),
					At(algebraic_element.AdjoinSubfield, l, constants, generators),
					At(algebraic_element.FiniteAlgebraicAdjoin, l, constants, generators)))
			fieldParts := a.Conjuncts(
				adjoinedField,
				"σ(k)(y) is a subfield",
				"it holds σ(k)",
				"it holds the coordinates",
				"it is finite over σ(k)")
			subring := a.Have(
				"σ(k)(y) is a subring of L holding σ(k) and the coordinates",
				"subring(field_ring(L), «adjoined») ∧ "+
					"(∀c:A. c ∈ k ⇒ σ(c) ∈ «adjoined») ∧ "+
					"(∀x:num. x ∈ {i:num | i ≤ n} ⇒ y(x) ∈ «adjoined»)",
				By(
					fieldParts[0],
					fieldParts[1],
					fieldParts[2],
					field.SubfieldSubring.Read(L).At(adjoined),
					At(set_image.FunInImage, σ, k),
					At(set_basic.SubsetDef, constants, adjoined),
					At(set_basic.SubsetDef, generators, adjoined)))
			valueInside := a.Have(
				"a form of degree d takes its value in σ(k)(y): its "+
					"coefficients map into σ(k) and its variables to the coordinates",
				Statement{
					Binders: "∀P:((num → num) → A).",
					Hypotheses: []string{
						"homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
					},
					Conclusion: "«evaluation»(P) ∈ «adjoined»",
				},
				Derive(func(b *Argument) {
					P := b.Fix("P")
					form := b.Assume()
					b.Show(
						"evaluation into a subring holding the coefficients and the point stays there",
						By(
							coefficientMap,
							subring,
							homogeneous_polynomial.FormPolynomial.Read(form),
							polynomial_algebra.PolynomialAlgebraRingDef,
							At(
								polynomial_algebra_evaluation.PolynomialAlgebraEvalInSubring,
								rk,
								ringL,
								σ,
								y,
								variables,
								adjoined,
								P)))
				}))
			valuesInside := a.Have(
				"the values of the forms lie in σ(k)(y)",
				"«values» ⊆ «adjoined»",
				By(
					valueInside,
					At(set_basic.SubsetDef, a.Term("«values»"), adjoined),
					At(
						set_basic.InImage,
						a.Term("«evaluation»"),
						a.Term("{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"))))
			dimension := a.Conjuncts(
				GroupPremises(
					M,
					L,
					kSubfield,
					coefficientMap,
					coordinates,
					generic,
					At(FormValuesDimension, m, l, k, n, d, E, σ, y)),
				"the values are a subspace of L over k",
				"finite-dimensional",
				"of dimension h(d)")
			valuesModule := a.Have(
				"so the values are a module over k, L being one through σ",
				"module_on(«hilbertCoefficients», restrict_module(«LOverK», «values»))",
				By(
					dimension[0],
					coefficientMap,
					module.RegularModuleOn.Read(field.RingOn.Read(L)),
					At(hom_module.RestrictScalarsModuleOn, rk, ringL, σ, a.Term("regular_module(field_ring(L))")),
					submodule.SubmoduleModuleOn))
			_, basis := a.Obtain(
				"choose a finite basis of the values over k",
				"∃C:set(B). "+
					"    finite(C) ∧ module_basis(«hilbertCoefficients», restrict_module(«LOverK», «values»), C)",
				By(
					dimension[1],
					At(module_dimension.FiniteDimensionalDef, rk, a.Term("restrict_module(«LOverK», «values»)"))),
				Named("C"))
			scalars := a.Have(
				"k and σ(k) are fields on their carriers",
				"ring_subfield(«hilbertCoefficients», M.inv, k) ∧ "+
					"ring_subfield(restrict_ring(field_ring(L), image(σ, k)), L.inv, image(σ, k))",
				By(
					kSubfield,
					imageParts[0],
					field.SubfieldRingSubfield.Read(M).At(k, k),
					field.SubfieldRingSubfield.Read(L).At(constants, constants)))
			counted := a.Have(
				"the basis has h(d) members, lies among the values and is independent over k",
				"card(C) = projective_hilbert_function(field_ring(M), k, n, E, d) ∧ "+
					"C ⊆ «values» ∧ "+
					"module_independent(«hilbertCoefficients», restrict_module(«LOverK», «values»), C)",
				By(
					basis,
					dimension[2],
					valuesModule,
					scalars,
					At(
						module_dimension.FiniteBasisDim,
						rk,
						a.Term("restrict_module(«LOverK», «values»)"),
						a.Term("M.inv"),
						a.Term("C")),
					At(
						linear_independence.ModuleBasisDef, rk, a.Term("restrict_module(«LOverK», «values»)"), a.Term("C")),
					At(
						linear_independence.BasisInCarrier,
						rk,
						a.Term("restrict_module(«LOverK», «values»)"),
						a.Term("C"))))
			countedParts := a.Conjuncts(
				counted,
				"the basis has h(d) members",
				"it lies among the values",
				"it is independent over k")
			inside := a.Have(
				"σ(k)(y) and the values lie in L, and the basis in σ(k)(y)",
				"«adjoined» ⊆ L.carrier ∧ C ⊆ «adjoined» ∧ «values» ⊆ L.carrier",
				By(
					fieldParts[0],
					countedParts[1],
					valuesInside,
					At(field.SubfieldSubset, l, adjoined),
					At(set_order.SubsetTrans, a.Term("C"), a.Term("«values»"), adjoined),
					At(set_order.SubsetTrans, a.Term("«values»"), adjoined, a.Term("L.carrier"))))
			insideParts := a.Conjuncts(
				inside,
				"σ(k)(y) lies in L",
				"the basis lies in σ(k)(y)",
				"the values lie in L")
			overKAll := a.Have(
				"the basis is independent over k in all of L",
				"module_independent(«hilbertCoefficients», «LOverK», C)",
				By(
					insideParts[2],
					countedParts[2],
					At(
						linear_independence.IndependentRestrict, rk, a.Term("«LOverK»"), a.Term("«values»"), a.Term("C"))))
			overImage := a.Have(
				"and so over σ(k)",
				"module_independent(restrict_ring(field_ring(L), image(σ, k)), regular_module(field_ring(L)), C)",
				By(
					imageParts[1],
					overKAll,
					coefficientMap,
					At(
						hom_module.ScalarRestrictionIndependent,
						rk,
						ringL,
						σ,
						a.Term("regular_module(field_ring(L))"),
						a.Term("C"))))
			bounded := a.Have(
				"an independent set of σ(k)(y) over σ(k) has at most its degree of members",
				"card(C) ≤ extension_degree(L, image(σ, k), «adjoined»)",
				By(
					imageParts[0],
					fieldParts[0],
					fieldParts[1],
					fieldParts[3],
					insideParts[0],
					insideParts[1],
					overImage,
					scalars,
					At(
						linear_independence.IndependentRestrict,
						a.Term("restrict_ring(field_ring(L), image(σ, k))"),
						a.Term("regular_module(field_ring(L))"),
						adjoined,
						a.Term("C")),
					field_extension.ExtensionModuleOn.Read(L).At(constants, adjoined),
					At(field_extension.FiniteExtensionDef, l, constants, adjoined),
					At(field_extension.ExtensionDegreeDef, l, constants, adjoined),
					At(
						module_dimension.IndependentBound,
						a.Term("restrict_ring(field_ring(L), image(σ, k))"),
						a.Term("restrict_module(regular_module(field_ring(L)), «adjoined»)"),
						a.Term("L.inv"),
						a.Term("C"))))
			a.Show(
				"so h(d) is at most the degree",
				By(bounded, countedParts[0]))
		}),
})}

// TranscendentalPairBound — a coordinate y(a) transcendental over σ(k) and
// a coordinate y(b) transcendental over σ(k)(y(a)) give (p + 1)(q + 1)
// independent values of forms of degree d whenever p + q ≤ d. The products
// y(a)^i·y(b)^t, i ≤ p, t ≤ q, are the values of the forms
// X_a^i·X_b^t·X_j^(d − i − t), y(j) being one (FormVariable, FormPower, FormProduct); the powers of
// y(a) are independent over σ(k) and those of y(b) over σ(k)(y(a)), so the
// products are independent over σ(k) (TowerIndependent), hence over k
// (ScalarRestrictionIndependent), and there are at most h(d) of them
// (FormValuesDimension).
var TranscendentalPairBound = transcendentalPairBoundThm{family.Add(registry.ProofEntry{
	Name: "TranscendentalPairBound",
	Key:  "prop_739359c221148894",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀L:field_on(B). " +
			"∀k:set(A). " +
			"∀n d:num. " +
			"∀E:set((num → num) → A). " +
			"∀σ:(A → B). " +
			"∀y:(num → B). " +
			"∀j a b p q:num.",
		Hypotheses: []string{
			"subfield(M, k)",
			"ring_homomorphism(«hilbertCoefficients», field_ring(L), σ)",
			"∀i:num. i ≤ n ⇒ y(i) ∈ L.carrier",
			"∀P:((num → num) → A). " +
				"    homogeneous_polynomial(«hilbertCoefficients», n, d, P) ⇒ " +
				"    («evaluation»(P) = L.zero ⇔ P ∈ ideal_span(«polynomials», E))",
			"j ≤ n",
			"y(j) = L.one",
			"a ≤ n",
			"b ≤ n",
			"¬algebraic_over(L, image(σ, k), y(a))",
			"¬algebraic_over(L, «extended», y(b))",
			"p + q ≤ d",
		},
		Conclusion: "(p + 1) * (q + 1) ≤ projective_hilbert_function(field_ring(M), k, n, E, d)",
		Abbrev: Abbrev{
			{Name: "evaluation", Text: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y)"},
			{Name: "extended", Text: "field_adjoin(L, image(σ, k), {y(a)})"},
			{Name: "formSpace", Text: "mk_module(«polynomials».add, " +
				"    «polynomials».zero, " +
				"    «polynomials».neg, " +
				"    λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"    {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})"},
			{Name: "LOverK", Text: "scalar_restriction(σ, regular_module(field_ring(L)))"},
			{Name: "values", Text: "image(«evaluation», " +
				"    {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})"},
			{Name: "powersA", Text: "image(monoid_pow(L.mul, L.one, y(a)), {i:num | i ≤ p})"},
			{Name: "powersB", Text: "image(monoid_pow(L.mul, L.one, y(b)), {i:num | i ≤ q})"},
			{Name: "products", Text: "{u * v | u:B, v:B | u ∈ «powersA» ∧ v ∈ «powersB»}"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			n, d *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			σ *Arrow[A, B],
			y *Arrow[Nat, B],
			j, a, b, p, q *Expr[Nat],
			kSubfield, coefficientMap, coordinates, generic, jIn, jOne, aIn, bIn, aTranscendental, bTranscendental, degrees Fact,
		) {
			m, l := arg.Term("M"), arg.Term("L")
			rk := arg.Term("«hilbertCoefficients»")
			ringL := arg.Term("field_ring(L)")
			regular := arg.Term("regular_module(field_ring(L))")
			variables := arg.Term("{i:num | i ≤ n}")
			carrierL := arg.Term("L.carrier")
			constants := arg.TermAs[Set[B]]("image(σ, k)")
			extended := arg.TermAs[Set[B]]("«extended»")
			powersA, powersB, products := arg.Term("«powersA»"), arg.Term("«powersB»"), arg.Term("«products»")
			forms := arg.Term("{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}")
			evaluation := arg.Have(
				"evaluation along σ at y is a ring homomorphism out of the polynomials",
				"ring_homomorphism(«polynomials», field_ring(L), «evaluation»)",
				By(
					coordinates,
					coefficientMap,
					At(polynomial_algebra_evaluation.PolynomialAlgebraEvalHom, rk, ringL, σ, y, variables)))
			coefficientRing := ring_homomorphism.Source.Read(coefficientMap)
			powers := arg.Have(
				"each power of a coordinate is the value of a form of that degree, the power of its variable",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"i ≤ n",
					},
					Conclusion: "∀e:num. ∃P:((num → num) → A). " +
						"    homogeneous_polynomial(«hilbertCoefficients», n, e, P) ∧ " +
						"    «evaluation»(P) = monoid_pow(L.mul, L.one, y(i), e)",
				},
				Derive(func(h *Argument) {
					i := h.FixAs[Nat]("i")
					iIn := h.Assume()
					e := h.FixAs[Nat]("e")
					variable := h.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_var(«hilbertCoefficients», i)")
					h.Take(h.Term(
						"monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
							"    polynomial_algebra_one(«hilbertCoefficients»), " +
							"    polynomial_algebra_var(«hilbertCoefficients», i), " +
							"    e)"))
					linear := h.Have(
						"the variable Xᵢ is a form of degree 1",
						"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    1, "+
							"    polynomial_algebra_var(«hilbertCoefficients», i))",
						By(coefficientRing, iIn, At(homogeneous_polynomial.FormVariable, rk, n, i)))
					degree := h.Have(
						"so Xᵢ^e is a form of degree 1·e = e",
						"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    e, "+
							"    monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), "+
							"        polynomial_algebra_one(«hilbertCoefficients»), "+
							"        polynomial_algebra_var(«hilbertCoefficients», i), "+
							"        e))",
						By(
							coefficientRing,
							linear,
							nat_arith.OneMul.At(e),
							At(homogeneous_polynomial.FormPower, rk, n, h.TermAs[Nat]("1"), variable, e)))
					value := h.Have(
						"and its value is y(i)^e, evaluation keeping powers",
						"«evaluation»(monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), "+
							"        polynomial_algebra_one(«hilbertCoefficients»), "+
							"        polynomial_algebra_var(«hilbertCoefficients», i), "+
							"        e)) = "+
							"monoid_pow(L.mul, L.one, y(i), e)",
						By(
							coordinates.At(i),
							iIn,
							coefficientMap,
							homogeneous_polynomial.FormPolynomial.Read(linear),
							polynomial_algebra.PolynomialAlgebraRingDef,
							ring_homomorphism.RingMapPower.Read(evaluation).AsFact().At(e, variable),
							At(polynomial_algebra_evaluation.PolynomialAlgebraEvalVar, rk, ringL, σ, y, i)))
					h.Show(
						"Xᵢ^e is a form of degree e with the value y(i)^e",
						By(degree, value))
				}))
			aInL := arg.Have(
				"y(a) lies in L",
				"y(a) ∈ L.carrier",
				By(aIn, coordinates.At(a)))
			bInL := arg.Have(
				"and so does y(b)",
				"y(b) ∈ L.carrier",
				By(bIn, coordinates.At(b)))
			image := arg.Conjuncts(
				GroupPremises(
					L,
					kSubfield,
					coefficientMap,
					ring_homomorphism.SubfieldHomomorphismEmbedding.Read(M).At(arg.TermAs[FieldOps[B]]("L"), k, σ)),
				"σ(k) is a subfield of L",
				"σ is one-to-one on k")
			firstFacts := arg.Have(
				"σ(k)(y(a)) is a subfield of L holding σ(k) and y(a), and "+
					"the powers of y(a) are distinct and independent over σ(k)",
				"subfield(L, «extended») ∧ "+
					"image(σ, k) ⊆ «extended» ∧ "+
					"y(a) ∈ «extended» ∧ "+
					"(∀i t:num. monoid_pow(L.mul, L.one, y(a), i) = monoid_pow(L.mul, L.one, y(a), t) ⇒ i = t) ∧ "+
					"module_independent(restrict_ring(field_ring(L), image(σ, k)), "+
					"    regular_module(field_ring(L)), "+
					"    monoid_powers(L.mul, L.one, y(a)))",
				By(
					aTranscendental,
					aInL,
					image[0],
					algebraic_element.AdjoinElementSubfield.Read(L).AsFact().At(constants, y.Apply(a)),
					algebraic_element.TranscendentalPowersIndependent.Read(L).AsFact().At(constants, y.Apply(a))))
			first := arg.Conjuncts(
				firstFacts,
				"σ(k)(y(a)) is a subfield",
				"it holds σ(k)",
				"it holds y(a)",
				"the powers of y(a) are distinct",
				"and independent over σ(k)")
			secondFacts := arg.Have(
				"the powers of y(b) are distinct and independent over σ(k)(y(a))",
				"(∀i t:num. monoid_pow(L.mul, L.one, y(b), i) = monoid_pow(L.mul, L.one, y(b), t) ⇒ i = t) ∧ "+
					"module_independent(restrict_ring(field_ring(L), «extended»), "+
					"    regular_module(field_ring(L)), "+
					"    monoid_powers(L.mul, L.one, y(b)))",
				By(
					bTranscendental,
					bInL,
					first[0],
					algebraic_element.TranscendentalPowersIndependent.Read(L).AsFact().At(extended, y.Apply(b))))
			second := arg.Conjuncts(
				secondFacts,
				"the powers of y(b) are distinct",
				"and independent over σ(k)(y(a))")
			powA, powB := arg.Term("monoid_pow(L.mul, L.one, y(a))"), arg.Term("monoid_pow(L.mul, L.one, y(b))")
			upToP, upToQ := arg.TermAs[Set[Nat]]("{i:num | i ≤ p}"), arg.TermAs[Set[Nat]]("{i:num | i ≤ q}")
			sizeA := arg.Have(
				"there are p + 1 powers of y(a) up to p",
				"has_size(«powersA», p + 1)",
				By(
					first[3],
					num_segment.HasSizeBelow.At(p),
					At(functions.InjectiveOnDef, upToP, powA),
					At(cardinality.HasSizeImageInj, powA, upToP, arg.Term("p + 1"))))
			sizeB := arg.Have(
				"there are q + 1 powers of y(b) up to q",
				"has_size(«powersB», q + 1)",
				By(
					second[0],
					num_segment.HasSizeBelow.At(q),
					At(functions.InjectiveOnDef, upToQ, powB),
					At(cardinality.HasSizeImageInj, powB, upToQ, arg.Term("q + 1"))))
			allA := arg.Have(
				"the powers of y(a) up to p are among all its powers",
				"«powersA» ⊆ monoid_powers(L.mul, L.one, y(a))",
				BySets(At(comm_monoid.MonoidPowersDef, arg.Term("L.mul"), arg.Term("L.one"), y.Apply(a))))
			allB := arg.Have(
				"the powers of y(b) up to q are among all its powers",
				"«powersB» ⊆ monoid_powers(L.mul, L.one, y(b))",
				BySets(At(comm_monoid.MonoidPowersDef, arg.Term("L.mul"), arg.Term("L.one"), y.Apply(b))))
			inExtended := arg.Have(
				"the powers of y(a) lie in σ(k)(y(a))",
				"«powersA» ⊆ «extended»",
				By(
					L,
					first[2],
					first[0],
					At(set_basic.SubsetDef, powersA, extended),
					At(set_basic.InImage, powA, upToP),
					At(field.SubfieldPowerIn, l, extended, y.Apply(a))))
			inL := arg.Have(
				"the powers of y(b) lie in L",
				"«powersB» ⊆ L.carrier",
				By(
					L,
					bInL,
					At(set_basic.SubsetDef, powersB, carrierL),
					At(set_basic.InImage, powB, upToQ),
					At(field.CarrierSubfield, l),
					At(field.SubfieldPowerIn, l, carrierL, y.Apply(b))))
			independentA := arg.Have(
				"the powers of y(a) up to p are independent over σ(k) in σ(k)(y(a))",
				"module_independent(restrict_ring(field_ring(L), image(σ, k)), "+
					"    restrict_module(regular_module(field_ring(L)), «extended»), "+
					"    «powersA»)",
				By(
					first[0],
					allA,
					inExtended,
					first[4],
					At(field.SubfieldSubset, l, extended),
					At(
						linear_independence.IndependentSubset,
						arg.Term("restrict_ring(field_ring(L), image(σ, k))"),
						regular,
						arg.Term("monoid_powers(L.mul, L.one, y(a))"),
						powersA),
					At(
						linear_independence.IndependentRestrict,
						arg.Term("restrict_ring(field_ring(L), image(σ, k))"),
						regular,
						extended,
						powersA)))
			independentB := arg.Have(
				"the powers of y(b) up to q are independent over σ(k)(y(a)) in L",
				"module_independent(restrict_ring(field_ring(L), «extended»), "+
					"    restrict_module(regular_module(field_ring(L)), L.carrier), "+
					"    «powersB»)",
				By(
					allB,
					inL,
					second[1],
					At(set_order.SubsetRefl, carrierL),
					At(
						linear_independence.IndependentSubset,
						arg.Term("restrict_ring(field_ring(L), «extended»)"),
						regular,
						arg.Term("monoid_powers(L.mul, L.one, y(b))"),
						powersB),
					At(
						linear_independence.IndependentRestrict,
						arg.Term("restrict_ring(field_ring(L), «extended»)"),
						regular,
						carrierL,
						powersB)))
			towerFacts := arg.Have(
				"the products are independent over σ(k), and there are (p + 1)(q + 1) of them",
				"module_independent(restrict_ring(field_ring(L), image(σ, k)), "+
					"    restrict_module(regular_module(field_ring(L)), L.carrier), "+
					"    «products») ∧ "+
					"has_size(«products», (p + 1) * (q + 1))",
				By(
					L,
					sizeA,
					sizeB,
					image[0],
					first[0],
					first[1],
					independentA,
					independentB,
					At(cardinality.HasSizeDef, powersA, arg.Term("p + 1")),
					At(cardinality.HasSizeDef, powersB, arg.Term("q + 1")),
					At(field.CarrierSubfield, l),
					At(field.SubfieldSubset, l, extended),
					At(field_extension.TowerIndependent, l, constants, extended, carrierL, powersA, powersB)))
			tower := arg.Conjuncts(
				towerFacts,
				"the products are independent over σ(k)",
				"there are (p + 1)(q + 1) of them")
			productValues := arg.Have(
				"each product of powers is the value of a form of degree d",
				Statement{
					Binders:    "∀i t:num.",
					Hypotheses: []string{"i ≤ p", "t ≤ q"},
					Conclusion: "monoid_pow(L.mul, L.one, y(a), i) * monoid_pow(L.mul, L.one, y(b), t) ∈ «values»",
				},
				Derive(func(h *Argument) {
					i := h.Fix("i")
					t := h.Fix("t")
					bounds := h.Assume()
					rest := h.Term("d - (i + t)")
					P, pFacts := h.Unpack(GroupPremises(aIn, powers.At(a, i)), "P")
					Q, qFacts := h.Unpack(GroupPremises(bIn, powers.At(b, t)), "Q")
					H, hFacts := h.Unpack(GroupPremises(jIn, powers.At(j, rest)), "H")
					pp := h.Conjuncts(
						pFacts,
						"P is a form of degree i",
						"its value is y(a)^i")
					qq := h.Conjuncts(
						qFacts,
						"Q is a form of degree t",
						"its value is y(b)^t")
					hh := h.Conjuncts(
						hFacts,
						"H is a form of degree d − (i + t)",
						"its value is a power of y(j)")
					total := h.Have(
						"the degrees add up to d",
						"i + t + (d - (i + t)) = d",
						ByArith(bounds, degrees))
					pq := h.Have(
						"P·Q is a form of degree i + t",
						"homogeneous_polynomial(«hilbertCoefficients», n, i + t, «polynomials».mul(P, Q))",
						By(coefficientRing, pp[0], qq[0], At(homogeneous_polynomial.FormProduct, rk, n, i, t, P, Q)))
					summed := h.Have(
						"(P·Q)·H is a form of degree (i + t) + (d − (i + t))",
						"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    i + t + (d - (i + t)), "+
							"    «polynomials».mul(«polynomials».mul(P, Q), H))",
						By(
							coefficientRing,
							pq,
							hh[0],
							At(
								homogeneous_polynomial.FormProduct,
								rk,
								n,
								h.TermAs[Nat]("i + t"),
								rest,
								h.Term("«polynomials».mul(P, Q)"),
								H)))
					full := h.Have(
						"so of degree d",
						"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    d, "+
							"    «polynomials».mul(«polynomials».mul(P, Q), H))",
						By(total, summed))
					powerOfOne := h.Have(
						"y(j) is one, so its powers are one",
						"monoid_pow(L.mul, L.one, y(j), d - (i + t)) = L.one",
						By(
							Normalized,
							jOne,
							comm_monoid.IdentityPowOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(L))).At(
								h.TermAs[Nat]("d - (i + t)"))))
					polynomials := h.Have(
						"P, Q, H and P·Q are polynomials",
						"P ∈ «polynomials».carrier ∧ "+
							"Q ∈ «polynomials».carrier ∧ "+
							"H ∈ «polynomials».carrier ∧ "+
							"«polynomials».mul(P, Q) ∈ «polynomials».carrier",
						By(
							homogeneous_polynomial.FormPolynomial.Read(pp[0]),
							homogeneous_polynomial.FormPolynomial.Read(qq[0]),
							homogeneous_polynomial.FormPolynomial.Read(hh[0]),
							homogeneous_polynomial.FormPolynomial.Read(pq)))
					multiplied := h.Have(
						"the value of the product is the product of the values",
						"«evaluation»(«polynomials».mul(«polynomials».mul(P, Q), H)) = "+
							"«evaluation»(P) * «evaluation»(Q) * «evaluation»(H)",
						Simp(Fwd(polynomial_algebra.PolynomialAlgebraRingDef)),
						By(
							polynomials,
							ring_homomorphism.MapMul.Read(evaluation).AsFact().At(h.Term("«polynomials».mul(P, Q)"), H),
							ring_homomorphism.MapMul.Read(evaluation).AsFact().At(P, Q)))
					inCarrier := h.Have(
						"the two powers lie in L",
						"monoid_pow(L.mul, L.one, y(a), i) ∈ L.carrier ∧ monoid_pow(L.mul, L.one, y(b), t) ∈ L.carrier",
						By(
							L,
							aInL,
							bInL,
							At(field.CarrierSubfield, l),
							At(field.SubfieldPowerIn, l, carrierL, y.Apply(a), i),
							At(field.SubfieldPowerIn, l, carrierL, y.Apply(b), t)))
					value := h.Have(
						"so the value is y(a)^i·y(b)^t",
						"«evaluation»(«polynomials».mul(«polynomials».mul(P, Q), H)) = "+
							"monoid_pow(L.mul, L.one, y(a), i) * monoid_pow(L.mul, L.one, y(b), t)",
						ByArith(L, powerOfOne, hh[1], multiplied, inCarrier, pp[1], qq[1]))
					h.Show(
						"the product of powers is the value of a form of degree d",
						By(value, full, At(set_basic.InImage, arg.Term("«evaluation»"), forms)))
				}))
			productsInside := arg.Have(
				"the products are values of forms of degree d",
				"«products» ⊆ «values»",
				BySets(productValues))
			dimension := arg.Conjuncts(
				GroupPremises(
					M,
					L,
					kSubfield,
					coefficientMap,
					coordinates,
					generic,
					At(FormValuesDimension, m, l, k, n, d, E, σ, y)),
				"the values are a subspace of L over k",
				"finite-dimensional",
				"of dimension h(d)")
			scalars := arg.Have(
				"k is a field on its carrier",
				"ring_subfield(«hilbertCoefficients», M.inv, k)",
				By(kSubfield, field.SubfieldRingSubfield.Read(M).At(k, k)))
			valuesModule := arg.Have(
				"so the values lie in L and are a module over k, L being one through σ",
				"«values» ⊆ L.carrier ∧ module_on(«hilbertCoefficients», restrict_module(«LOverK», «values»))",
				By(
					dimension[0],
					coefficientMap,
					module.RegularModuleOn.Read(field.RingOn.Read(L)),
					At(hom_module.RestrictScalarsModuleOn, rk, ringL, σ, regular),
					submodule.SubmoduleModuleOn,
					submodule.SubmoduleSubset))
			valuesParts := arg.Conjuncts(
				valuesModule,
				"the values lie in L",
				"they are a module over k")
			overImage := arg.Have(
				"the products are independent over σ(k) in L",
				"module_independent(restrict_ring(field_ring(L), image(σ, k)), "+
					"    regular_module(field_ring(L)), "+
					"    «products»)",
				By(
					tower[0],
					At(set_order.SubsetRefl, carrierL),
					At(
						linear_independence.IndependentRestrict,
						arg.Term("restrict_ring(field_ring(L), image(σ, k))"),
						regular,
						carrierL,
						products)))
			overK := arg.Have(
				"so over k, among the values",
				"module_independent(«hilbertCoefficients», restrict_module(«LOverK», «values»), «products»)",
				By(
					image[1],
					productsInside,
					valuesParts[0],
					overImage,
					coefficientMap,
					At(hom_module.ScalarRestrictionIndependent, rk, ringL, σ, regular, products),
					At(
						linear_independence.IndependentRestrict, rk, arg.Term("«LOverK»"), arg.Term("«values»"), products)))
			counted := arg.Have(
				"an independent set of the values has at most their "+
					"dimension of members, and there are (p + 1)(q + 1) products",
				"card(«products») ≤ module_dim(«hilbertCoefficients», restrict_module(«LOverK», «values»)) ∧ "+
					"card(«products») = (p + 1) * (q + 1)",
				By(
					dimension[1],
					valuesParts[1],
					towerFacts,
					overK,
					scalars,
					At(cardinality.HasSizeDef, products, arg.Term("(p + 1) * (q + 1)")),
					At(
						module_dimension.IndependentBound,
						rk,
						arg.Term("restrict_module(«LOverK», «values»)"),
						arg.Term("M.inv"),
						products)))
			arg.Show(
				"so (p + 1)(q + 1) ≤ h(d)",
				ByArith(dimension[2], counted))
		}),
})}

// CoordinatePowerValue — at a point y of L with y(j) = 1, every power y(i)ᵗ
// with t ≤ d is the value along σ of a form of degree d over k: the
// monomial Xᵢᵗ·Xⱼᵈ⁻ᵗ, whose value is y(i)ᵗ·1ᵈ⁻ᵗ.
var CoordinatePowerValue = coordinatePowerValueThm{family.Add(registry.ProofEntry{
	Name: "CoordinatePowerValue",
	Key:  "prop_99cb177978d4e8cd",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀L:field_on(B). " +
			"∀k:set(A). " +
			"∀n d:num. " +
			"∀σ:(A → B). " +
			"∀y:(num → B). " +
			"∀i j t:num.",
		Hypotheses: []string{
			"subfield(M, k)",
			"ring_homomorphism(«hilbertCoefficients», field_ring(L), σ)",
			"∀l:num. l ≤ n ⇒ y(l) ∈ L.carrier",
			"i ≤ n",
			"j ≤ n",
			"y(j) = L.one",
			"t ≤ d",
		},
		Conclusion: "monoid_pow(L.mul, L.one, y(i), t) ∈ " +
			"image(«evaluation», " +
			"    {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})",
		Abbrev: Abbrev{
			{Name: "evaluation", Text: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y)"},
			{Name: "power", Text: "λl:num. λs:num. " +
				"    monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
				"        polynomial_algebra_one(«hilbertCoefficients»), " +
				"        polynomial_algebra_var(«hilbertCoefficients», l), " +
				"        s)"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			n, d *Expr[Nat],
			σ *Arrow[A, B],
			y *Arrow[Nat, B],
			i, j, t *Expr[Nat],
			kSubfield, coefficientMap, coordinates, iIn, jIn, jOne, below Fact,
		) {
			type poly = Fun[Fun[Nat, Nat], A]
			K := arg.TermAs[RingOps[A]]("«hilbertCoefficients»")
			ringL := arg.TermAs[RingOps[B]]("field_ring(L)")
			variables := arg.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			one := arg.TermAs[Nat]("1")
			rest := arg.TermAs[Nat]("d - t")
			multiplicative := comm_ring.MulMonoidOn.Read(field.RingOn.Read(L))
			varI := arg.TermAs[poly]("polynomial_algebra_var(«hilbertCoefficients», i)")
			varJ := arg.TermAs[poly]("polynomial_algebra_var(«hilbertCoefficients», j)")
			powerI := arg.TermAs[poly]("«power»(i, t)")
			powerJ := arg.TermAs[poly]("«power»(j, d - t)")
			monomial := arg.TermAs[poly](
				"polynomial_algebra_mul(«hilbertCoefficients», «power»(i, t), «power»(j, d - t))")
			scalars := arg.Have(
				"k is a commutative ring",
				"comm_ring_on(«hilbertCoefficients»)",
				By(kSubfield, field.SubfieldCommRing.Read(M).At(k)))
			evaluation := arg.Have(
				"evaluation along σ at y is a ring homomorphism out of the polynomials",
				"ring_homomorphism(«polynomials», field_ring(L), «evaluation»)",
				By(
					coordinates,
					coefficientMap,
					At(polynomial_algebra_evaluation.PolynomialAlgebraEvalHom, K, ringL, σ, y, variables)))
			formI := arg.Have(
				"Xᵢᵗ is a form of degree t",
				"homogeneous_polynomial(«hilbertCoefficients», n, 1 * t, «power»(i, t))",
				By(
					scalars,
					iIn,
					At(homogeneous_polynomial.FormVariable, K, n, i),
					At(homogeneous_polynomial.FormPower, K, n, one, varI, t)))
			formJ := arg.Have(
				"Xⱼᵈ⁻ᵗ is a form of degree d − t",
				"homogeneous_polynomial(«hilbertCoefficients», n, 1 * (d - t), «power»(j, d - t))",
				By(
					scalars,
					jIn,
					At(homogeneous_polynomial.FormVariable, K, n, j),
					At(homogeneous_polynomial.FormPower, K, n, one, varJ, rest)))
			total := arg.Have(
				"the degrees add to d",
				"1 * t + 1 * (d - t) = d",
				ByArith(below))
			form := arg.Simplified(
				arg.Have(
					"so their product is a form of degree d",
					"homogeneous_polynomial(«hilbertCoefficients», "+
						"    n, "+
						"    1 * t + 1 * (d - t), "+
						"    polynomial_algebra_mul(«hilbertCoefficients», «power»(i, t), «power»(j, d - t)))",
					By(
						scalars,
						formI,
						formJ,
						At(
							homogeneous_polynomial.FormProduct,
							K,
							n,
							arg.TermAs[Nat]("1 * t"),
							arg.TermAs[Nat]("1 * (d - t)"),
							powerI,
							powerJ))),
				Fwd(total))
			polynomials := arg.Have(
				"the variables and their powers are polynomials over k",
				"polynomial_algebra_var(«hilbertCoefficients», i) ∈ "+
					"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ "+
					"polynomial_algebra_var(«hilbertCoefficients», j) ∈ "+
					"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ "+
					"«power»(i, t) ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ "+
					"«power»(j, d - t) ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
				By(
					scalars,
					iIn,
					jIn,
					formI,
					formJ,
					At(homogeneous_polynomial.FormVariable, K, n, i),
					At(homogeneous_polynomial.FormVariable, K, n, j),
					homogeneous_polynomial.FormPolynomial.At(K, n, one, varI),
					homogeneous_polynomial.FormPolynomial.At(K, n, one, varJ),
					homogeneous_polynomial.FormPolynomial.Read(formI),
					homogeneous_polynomial.FormPolynomial.Read(formJ)))
			value := arg.Have(
				"its value is y(i)ᵗ·y(j)ᵈ⁻ᵗ = y(i)ᵗ, y(j) being one",
				"«evaluation»(polynomial_algebra_mul(«hilbertCoefficients», «power»(i, t), «power»(j, d - t))) = "+
					"monoid_pow(L.mul, L.one, y(i), t)",
				By(
					polynomials,
					iIn,
					jIn,
					jOne,
					coordinates,
					coefficientMap,
					ring_homomorphism.MapMul.Read(evaluation).AsFact().At(powerI, powerJ),
					ring_homomorphism.RingMapPower.Read(evaluation).AsFact().At(t, varI),
					ring_homomorphism.RingMapPower.Read(evaluation).AsFact().At(rest, varJ),
					polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(K, ringL, σ, y, i),
					polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(K, ringL, σ, y, j),
					comm_monoid.IdentityPowOn.Read(multiplicative).AsFact().At(rest),
					comm_monoid.PowIn.Read(multiplicative).AsFact().At(y.Apply(i), t),
					comm_monoid.RightIdentityOn.Read(multiplicative).AsFact().At(
						arg.TermAs[B]("monoid_pow(L.mul, L.one, y(i), t)"))))
			arg.Show(
				"so y(i)ᵗ is the value of a form of degree d",
				By(
					form,
					value,
					set_image.FunInImage.At(
						arg.TermAs[Fun[poly, B]]("«evaluation»"),
						arg.TermAs[Set[poly]](
							"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"),
						monomial)))
		}),
})}

// TranscendentalCoordinateBound — a coordinate y(a) transcendental over σ(k)
// gives p + 1 independent values of forms of degree d whenever p ≤ d. The
// powers y(a)^t, t ≤ p, are the values of the forms X_a^t·X_j^(d − t), y(j)
// being one; the powers of a transcendental are independent over σ(k)
// (TranscendentalPowersIndependent), hence over k
// (ScalarRestrictionIndependent), and an independent set of the values has at
// most h(d) members (FormValuesDimension).
var TranscendentalCoordinateBound = transcendentalCoordinateBoundThm{family.Add(registry.ProofEntry{
	Name: "TranscendentalCoordinateBound",
	Key:  "prop_fa0860489170b796",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀L:field_on(B). " +
			"∀k:set(A). " +
			"∀n d:num. " +
			"∀E:set((num → num) → A). " +
			"∀σ:(A → B). " +
			"∀y:(num → B). " +
			"∀j a p:num.",
		Hypotheses: []string{
			"subfield(M, k)",
			"ring_homomorphism(«hilbertCoefficients», field_ring(L), σ)",
			"∀i:num. i ≤ n ⇒ y(i) ∈ L.carrier",
			"∀P:((num → num) → A). " +
				"    homogeneous_polynomial(«hilbertCoefficients», n, d, P) ⇒ " +
				"    («evaluation»(P) = L.zero ⇔ P ∈ ideal_span(«polynomials», E))",
			"j ≤ n",
			"y(j) = L.one",
			"a ≤ n",
			"¬algebraic_over(L, image(σ, k), y(a))",
			"p ≤ d",
		},
		Conclusion: "p + 1 ≤ projective_hilbert_function(field_ring(M), k, n, E, d)",
		Abbrev: Abbrev{
			{Name: "evaluation", Text: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y)"},
			{Name: "formSpace", Text: "mk_module(«polynomials».add, " +
				"    «polynomials».zero, " +
				"    «polynomials».neg, " +
				"    λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"    {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})"},
			{Name: "LOverK", Text: "scalar_restriction(σ, regular_module(field_ring(L)))"},
			{Name: "values", Text: "image(«evaluation», " +
				"    {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})"},
			{Name: "powers", Text: "image(monoid_pow(L.mul, L.one, y(a)), {i:num | i ≤ p})"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			n, d *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			σ *Arrow[A, B],
			y *Arrow[Nat, B],
			j, a, p *Expr[Nat],
			kSubfield, coefficientMap, coordinates, generic, jIn, jOne, aIn, aTranscendental, degree Fact,
		) {
			m, l := arg.Term("M"), arg.Term("L")
			K := arg.TermAs[RingOps[A]]("«hilbertCoefficients»")
			ringL := arg.TermAs[RingOps[B]]("field_ring(L)")
			regular := arg.Term("regular_module(field_ring(L))")
			constants := arg.TermAs[Set[B]]("image(σ, k)")
			powers := arg.Term("«powers»")
			upToP := arg.TermAs[Set[Nat]]("{i:num | i ≤ p}")
			powA := arg.Term("monoid_pow(L.mul, L.one, y(a))")
			powerValues := arg.Have(
				"each power y(a)^t, t ≤ p, is the value of the form X_a^t·X_j^(d − t) of degree d",
				"∀t:num. t ≤ p ⇒ monoid_pow(L.mul, L.one, y(a), t) ∈ «values»",
				Derive(func(b *Argument) {
					t := b.FixAs[Nat]("t")
					below := b.Assume()
					b.Show(
						"t ≤ p ≤ d",
						By(
							M,
							L,
							kSubfield,
							coefficientMap,
							coordinates,
							aIn,
							jIn,
							jOne,
							b.Have(
								"t ≤ d",
								"t ≤ d",
								ByArith(below, degree)),
							CoordinatePowerValue.At(
								b.TermAs[FieldOps[A]]("M"), b.TermAs[FieldOps[B]]("L"), k, n, d, σ, y, a, j, t)))
				}))
			image := arg.Conjuncts(
				GroupPremises(
					L,
					kSubfield,
					coefficientMap,
					ring_homomorphism.SubfieldHomomorphismEmbedding.Read(M).At(arg.TermAs[FieldOps[B]]("L"), k, σ)),
				"σ(k) is a subfield of L",
				"σ is one-to-one on k")
			aInL := arg.Have(
				"y(a) lies in L",
				"y(a) ∈ L.carrier",
				By(aIn, coordinates.At(a)))
			transcendence := arg.Conjuncts(
				GroupPremises(
					aTranscendental,
					aInL,
					image[0],
					algebraic_element.TranscendentalPowersIndependent.Read(L).AsFact().At(constants, y.Apply(a))),
				"the powers of y(a) are distinct",
				"and independent over σ(k)")
			size := arg.Have(
				"there are p + 1 powers of y(a) up to p",
				"has_size(«powers», p + 1)",
				By(
					transcendence[0],
					num_segment.HasSizeBelow.At(p),
					At(functions.InjectiveOnDef, upToP, powA),
					At(cardinality.HasSizeImageInj, powA, upToP, arg.Term("p + 1"))))
			among := arg.Have(
				"the powers of y(a) up to p are among all its powers",
				"«powers» ⊆ monoid_powers(L.mul, L.one, y(a))",
				BySets(At(comm_monoid.MonoidPowersDef, arg.Term("L.mul"), arg.Term("L.one"), y.Apply(a))))
			overImage := arg.Have(
				"so they are independent over σ(k) in L",
				"module_independent(restrict_ring(field_ring(L), image(σ, k)), "+
					"    regular_module(field_ring(L)), "+
					"    «powers»)",
				By(
					among,
					transcendence[1],
					At(
						linear_independence.IndependentSubset,
						arg.Term("restrict_ring(field_ring(L), image(σ, k))"),
						regular,
						arg.Term("monoid_powers(L.mul, L.one, y(a))"),
						powers)))
			inside := arg.Have(
				"the powers are values of forms of degree d",
				"«powers» ⊆ «values»",
				BySets(powerValues))
			dimension := arg.Conjuncts(
				GroupPremises(
					M,
					L,
					kSubfield,
					coefficientMap,
					coordinates,
					generic,
					At(FormValuesDimension, m, l, k, n, d, E, σ, y)),
				"the values are a subspace of L over k",
				"finite-dimensional",
				"of dimension h(d)")
			linear := arg.Have(
				"evaluation is linear over k",
				"module_homomorphism(«hilbertCoefficients», «formSpace», «LOverK», «evaluation»)",
				By(M, L, kSubfield, coefficientMap, coordinates, At(EvaluationLinear, m, l, k, n, d, σ, y)))
			kField := arg.Have(
				"k is a field on its carrier",
				"ring_subfield(«hilbertCoefficients», M.inv, k)",
				By(kSubfield, field.SubfieldRingSubfield.Read(M).At(k, k)))
			valuesParts := arg.Conjuncts(
				arg.Have(
					"the values lie in L and are a module over k",
					"«values» ⊆ L.carrier ∧ module_on(«hilbertCoefficients», restrict_module(«LOverK», «values»))",
					By(
						module_homomorphism.HomTarget.Read(linear),
						module_homomorphism.ImageSubmodule.Read(linear),
						submodule.SubmoduleModuleOn,
						submodule.SubmoduleSubset)),
				"the values lie in L",
				"they are a module over k")
			overK := arg.Have(
				"so the powers are independent over k, among the values",
				"module_independent(«hilbertCoefficients», restrict_module(«LOverK», «values»), «powers»)",
				By(
					image[1],
					inside,
					valuesParts[0],
					overImage,
					coefficientMap,
					At(hom_module.ScalarRestrictionIndependent, K, ringL, σ, regular, powers),
					At(linear_independence.IndependentRestrict, K, arg.Term("«LOverK»"), arg.Term("«values»"), powers)))
			counted := arg.Have(
				"an independent set of the values has at most their "+
					"dimension of members, and there are p + 1 powers",
				"card(«powers») ≤ module_dim(«hilbertCoefficients», restrict_module(«LOverK», «values»)) ∧ "+
					"card(«powers») = p + 1",
				By(
					dimension[1],
					valuesParts[1],
					size,
					overK,
					kField,
					At(cardinality.HasSizeDef, powers, arg.Term("p + 1")),
					At(
						module_dimension.IndependentBound,
						K,
						arg.Term("restrict_module(«LOverK», «values»)"),
						arg.Term("M.inv"),
						powers)))
			arg.Show(
				"so p + 1 ≤ h(d)",
				ByArith(dimension[2], counted))
		}),
})}

// PointNormalization — a point w of M with coordinates in l, zero past n,
// nonzero at some coordinate up to n and a zero of the forms of E, scaled by
// the inverse of its first nonzero coordinate w(p), is a point of the curve
// over l: its p-th coordinate becomes one, those before p stay zero, and a
// form of E of degree d scales by w(p)^(−d) (FormScaling).
var PointNormalization = pointNormalizationThm{family.Add(registry.ProofEntry{
	Name: "PointNormalization",
	Key:  "prop_13870a43b41e661e",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k l:set(A). ∀n j:num. ∀E:set((num → num) → A). ∀w:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, l)",
			"∀P:((num → num) → A). P ∈ E ⇒ ∃d:num. homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
			"∀i:num. i ≤ n ⇒ w(i) ∈ l",
			"∀i:num. n < i ⇒ w(i) = M.zero",
			"j ≤ n",
			"w(j) ≠ M.zero",
			"∀P:((num → num) → A). P ∈ E ⇒ «valueAt»(w, P) = M.zero",
		},
		Conclusion: "∃c:A. " +
			"    c ∈ l ∧ " +
			"    c ≠ M.zero ∧ " +
			"    (λi:num. w(i) * c) ∈ projective_equation_points(field_ring(M), k, l, n, E)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, l *Expr[Set[A]],
			n, j *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			w *Arrow[Nat, A],
			kSub, lSub, forms, coordinates, past, jInRange, nonzero, equations Fact,
		) {
			ring := field.RingOn.Read(M)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			fieldOps := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			coefficients := a.TermAs[RingOps[A]]("«hilbertCoefficients»")
			identity := a.TermAs[Fun[A, A]]("λa:A. a")
			p, least := a.ObtainAs[Nat](
				"the nonzero coordinates of w have a least index p",
				"∃p:num. w(p) ≠ M.zero ∧ (∀i:num. i < p ⇒ w(i) = M.zero)",
				By(nonzero, nat_order.WellOrdering.At(a.TermAs[Set[Nat]]("λi:num. w(i) ≠ M.zero"))))
			first := a.Conjuncts(
				least,
				"w(p) is not zero",
				"and w vanishes before p")
			pInRange := a.Have(
				"p is at most n, j not being before it",
				"p ≤ n",
				ByArith(
					jInRange,
					a.Have(
						"j is not before p",
						"¬(j < p)",
						By(nonzero, first[1].At(j)))))
			wp := a.TermAs[A]("w(p)")
			c := a.TermAs[A]("M.inv(w(p))")
			members := a.Conjuncts(
				a.Have(
					"w(p) and its inverse lie in l, a subfield of M",
					"w(p) ∈ l ∧ M.inv(w(p)) ∈ l ∧ l ⊆ M.carrier",
					By(lSub, pInRange, coordinates.At(p), field.SubfieldInv, field.SubfieldSubset)),
				"w(p) lies in l",
				"so does its inverse",
				"and l lies in M")
			inM := a.Conjuncts(
				a.Have(
					"so w(p) and its inverse lie in M",
					"w(p) ∈ M.carrier ∧ M.inv(w(p)) ∈ M.carrier",
					BySets(members[0], members[1], members[2])),
				"w(p) lies in M",
				"and so does its inverse")
			wInM := a.Have(
				"the coordinates of w up to n lie in M",
				"∀i:num. i ≤ n ⇒ w(i) ∈ M.carrier",
				BySets(coordinates, members[2]))
			inclusion := a.Have(
				"the inclusion of k into M is a ring map",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
				By(
					kSub,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
			pastZero := a.Have(
				"the scaled coordinates past n stay zero",
				"∀i:num. n < i ⇒ w(i) * M.inv(w(p)) = M.zero",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					beyond := b.Assume()
					b.Show(
						"zero times the inverse is zero",
						GroupPremises(beyond, past.At(i)).Rw(),
						ByArith(M, inM[1]))
				}))
			beforeZero := a.Have(
				"and so do those before p",
				"∀i:num. i < p ⇒ w(i) * M.inv(w(p)) = M.zero",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					before := b.Assume()
					b.Show(
						"zero times the inverse is zero",
						GroupPremises(before, first[1].At(i)).Rw(),
						ByArith(M, inM[1]))
				}))
			scaledIn := a.Have(
				"the scaled coordinates up to n lie in l",
				"∀i:num. i ≤ n ⇒ w(i) * M.inv(w(p)) ∈ l",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					inRange := b.Assume()
					b.Show(
						"a product in the subfield l",
						By(
							lSub,
							inRange,
							coordinates.At(i),
							members[1],
							field.SubfieldMul.At(fieldOps, l, b.TermAs[A]("w(i)"), c)))
				}))
			vanishes := a.Have(
				"each form of E vanishes at the scaled point, scaling by a power of the inverse",
				"∀P:((num → num) → A). P ∈ E ⇒ «valueAt»(λi:num. w(i) * M.inv(w(p)), P) = M.zero",
				Derive(func(b *Argument) {
					P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
					inE := b.Assume()
					d, form := b.UnpackAs[Nat](GroupPremises(inE, forms.At(P)), "d")
					scaled := b.Have(
						"P(w·c) = c^d·P(w), P being a form of degree d",
						"«valueAt»(λi:num. w(i) * M.inv(w(p)), P) = "+
							"monoid_pow(M.mul, M.one, M.inv(w(p)), d) * «valueAt»(w, P)",
						By(
							inclusion,
							form,
							wInM,
							inM[1],
							At(homogeneous_polynomial.FormScaling, coefficients, fieldRing, identity, n, d, w, c, P)))
					b.Show(
						"and P(w) = 0",
						scaled.Rw(),
						GroupPremises(inE, equations.At(P)).Rw(),
						ByArith(M, GroupPremises(inM[1], comm_monoid.PowIn.Read(monoid).AsFact().At(c, d))))
				}))
			a.Show(
				"the inverse of w(p) scales w to a point of the curve over l",
				Witness(c),
				Unfold(ProjectiveEquationPointsDef),
				By(
					members[1],
					a.Have(
						"the inverse is not zero, w(p) not being zero",
						"M.inv(w(p)) ≠ M.zero",
						By(first[0], inM[0], field.InvEqZeroOn.Read(M).AsFact().At(wp))),
					scaledIn,
					pastZero,
					a.Have(
						"the first nonzero scaled coordinate, at p, is one",
						"∃j:num. j ≤ n ∧ w(j) * M.inv(w(p)) = M.one ∧ (∀i:num. i < j ⇒ w(i) * M.inv(w(p)) = M.zero)",
						Witness(p),
						By(
							pInRange,
							beforeZero,
							a.Have(
								"w(p)·w(p)^(−1) = 1",
								"w(p) * M.inv(w(p)) = M.one",
								By(first[0], inM[0], field.MulRightInverseOn.Read(M))))),
					vanishes))
		}),
})}

// EvaluationNatural — a ring map φ from a subring S of M into M that fixes k
// commutes with evaluating the polynomials over k at points θ of S:
// φ(P(θ)) = P(φ∘θ). Evaluation at θ reads only the operations of its target,
// which S shares with M, so P(θ) is P evaluated into S
// (PolynomialAlgebraEvalRestrictTarget), and a ring map out of S carries that
// value to P(φ∘θ), the coefficients going to themselves
// (PolynomialAlgebraEvalNatural).
var EvaluationNatural = evaluationNaturalThm{family.Add(registry.ProofEntry{
	Name: "EvaluationNatural",
	Key:  "prop_6c2636d64c21ec69",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k S:set(A). ∀n:num. ∀θ:(num → A). ∀φ:(A → A). ∀P:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"∀i:num. i ≤ n ⇒ θ(i) ∈ S",
			"ring_homomorphism(restrict_ring(field_ring(M), S), field_ring(M), φ)",
			"∀c:A. c ∈ k ⇒ φ(c) = c",
			"P ∈ «polynomials».carrier",
		},
		Conclusion: "φ(«valueAt»(θ, P)) = «valueAt»(λi:num. φ(θ(i)), P)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, S *Expr[Set[A]],
			n *Expr[Nat],
			θ *Arrow[Nat, A],
			φ *Arrow[A, A],
			P *Arrow[Fun[Nat, Nat], A],
			kSub, subring, kInS, coordinates, hom, fixes, polynomial Fact,
		) {
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			coefficients := a.TermAs[RingOps[A]]("«hilbertCoefficients»")
			identity := a.TermAs[Fun[A, A]]("λa:A. a")
			inclusion := a.Have(
				"the inclusion of k into M is a ring map",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
				By(
					kSub,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(field.RingOn.Read(M)).At(k)))
			intoS := a.Have(
				"and so is the inclusion of k into S",
				"ring_homomorphism(«hilbertCoefficients», restrict_ring(field_ring(M), S), λa:A. a)",
				BySets(
					inclusion,
					subring,
					kInS,
					ring_homomorphism.RingHomCorestrict.At(coefficients, fieldRing, identity, S)))
			a.Show(
				"P(θ) is its value in S, which φ carries to its value at φ∘θ, fixing the coefficients",
				By(
					intoS,
					hom,
					inclusion,
					fixes,
					coordinates,
					polynomial,
					polynomial_algebra_evaluation.PolynomialAlgebraEvalRestrictTarget.At(
						coefficients, fieldRing, S, identity, θ, P),
					polynomial_algebra_evaluation.PolynomialAlgebraEvalNatural.At(
						coefficients,
						a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), S)"),
						fieldRing,
						identity,
						φ,
						identity,
						a.TermAs[Set[Nat]]("{i:num | i ≤ n}"),
						θ,
						P)))
		}),
})}

// FormValuesSubspace — the values at the generic point x of the forms of
// degree e over k are a k-subspace of K of dimension h(e): this is
// FormValuesDimension along the inclusion of k into M, M read over k along
// the identity being M's own regular module (ScalarRestrictionIdentity), and
// the values lie in K, where evaluation at x lands (PointEvaluation).
var FormValuesSubspace = formValuesSubspaceThm{family.Add(registry.ProofEntry{
	Name: "FormValuesSubspace",
	Key:  "prop_9ebd5d67bbcc1762",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀n e:num. ∀E:set((num → num) → A). ∀x:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"«genericPoint»(x)",
		},
		Conclusion: "submodule(«hilbertCoefficients», regular_module(field_ring(M)), «values»(e)) ∧ " +
			"«values»(e) ⊆ K ∧ " +
			"finite_dimensional(«hilbertCoefficients», «vectors»(«values»(e))) ∧ " +
			"«dim»(«vectors»(«values»(e))) = projective_hilbert_function(field_ring(M), k, n, E, e)",
		Abbrev: Abbrev{
			{Name: "values", Text: "λd:num. " +
				"    image(«at», {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(M)))"},
			{Name: "dim", Text: "module_dim(«hilbertCoefficients»)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, e *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			given Fact,
		) {
			hyp := a.Conjuncts(
				given,
				"k is a subfield of M",
				"so is K",
				"x is a point of the curve over K",
				"K is generated over k by the coordinates of x",
				"a form vanishes at x exactly when it lies in the ideal")
			subfieldK, subfieldBig, point, generated, generic := hyp[0], hyp[1], hyp[2], hyp[3], hyp[4]
			fieldM := a.TermAs[FieldOps[A]]("M")
			identity := a.TermAs[Fun[A, A]]("λa:A. a")
			coordinatesInK := a.Have(
				"the coordinates of x up to n lie in K",
				"∀i:num. i ≤ n ⇒ x(i) ∈ K",
				By(point, PointCoordinatesIn))
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(subfieldBig, field.SubfieldSubset))
			kInK := a.Have(
				"k lies in K, the field the coordinates generate over k",
				"k ⊆ K",
				BySets(
					generated,
					subfieldK,
					coordinatesInK,
					KInM,
					field.SubfieldSubset.At(fieldM, k),
					algebraic_element.AdjoinSubfield.Read(M).At(k, a.TermAs[Set[A]]("{x(i) | i:num | i ≤ n}"))))
			evaluation := a.Conjuncts(
				GroupPremises(
					subfieldK, subfieldBig, kInK, coordinatesInK, Read(PointEvaluation, M).At(k, K, n, x)),
				"evaluation at x is a ring map",
				"with values in K")
			inclusion := a.Have(
				"the inclusion of k into M is a ring map",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
				By(
					subfieldK,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(field.RingOn.Read(M)).At(k)))
			inM := a.Have(
				"the coordinates of x up to n lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(coordinatesInK, KInM))
			vanishing := a.Have(
				"a form of degree e vanishes at x exactly when it lies in the ideal",
				Statement{
					Binders: "∀P:((num → num) → A).",
					Hypotheses: []string{
						"homogeneous_polynomial(«hilbertCoefficients», n, e, P)",
					},
					Conclusion: "«at»(P) = M.zero ⇔ P ∈ ideal_span(«polynomials», E)",
				},
				By(generic))
			dimension := a.Conjuncts(
				a.Simplified(
					GroupPremises(
						M,
						subfieldK,
						inclusion,
						inM,
						vanishing,
						At(FormValuesDimension, fieldM, fieldM, k, n, e, E, identity, x)),
					Fwd(module_record.ScalarRestrictionIdentity)),
				"the values are a k-subspace of M",
				"finite-dimensional",
				"of dimension h(e)")
			valuesInK := a.Have(
				"the values of the forms lie in K, as every value of a polynomial does",
				"«values»(e) ⊆ K",
				BySets(evaluation[1], homogeneous_polynomial.FormPolynomial))
			a.Show(
				"so the values are a k-subspace of M inside K, of dimension h(e)",
				By(dimension[0], valuesInK, dimension[1], dimension[2]))
		}),
})}
