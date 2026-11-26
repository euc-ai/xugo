// hilbert.go — the forms of one degree as a vector space, and bounds on the
// Hilbert function. Over a ring the forms of degree d in the variables
// 0, …, n are the free module on the monomials of degree d, so over a
// subfield k they have dimension binomial(d + n, n), and they meet every
// ideal of the polynomials over k in a subspace; for the ideal a set of
// equations spans, the codimension of that subspace is the Hilbert function
// at d. A subspace of the forms of degree d inside the ideal bounds the
// Hilbert function at d by its codimension; modulo a prime ideal, a subspace
// holding the ideal's forms of degree d and F times every form of degree e, F
// a polynomial outside the ideal, has codimension at most h(d) − h(e). The
// ideal over k of a smooth projective equation curve is prime. Multiplying by
// a form of degree e is a linear map from the forms of degree s to those of
// degree s + e, and a nonzero form F of degree e makes the degree-d part of
// its ideal a copy of the forms of degree d − e, the polynomials over an
// integral domain being an integral domain; the two give the Hilbert function
// of a plane curve of degree e, e·d + 1 − (e − 1)(e − 2)/2 from degree e on.

package projective_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/binomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/scheme/spec_functor"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// FormsFreeModule — over a ring R, the forms of degree d in the variables
// 0, …, n, under the sum of polynomials and coefficientwise scaling, are
// the free R-module on the monomials of degree d: a form of degree d is a
// finitely supported function into R vanishing off those monomials, and
// the operations are the free module's.
var FormsFreeModule = formsFreeModuleThm{family.Add(registry.ProofEntry{
	Name: "FormsFreeModule",
	Key:  "prop_262c0326a0055488",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d:num.",
		Conclusion: "mk_module(«polynomialsOver».add, " +
			"    «polynomialsOver».zero, " +
			"    «polynomialsOver».neg, " +
			"    λa:A. λP:((num → num) → A). λm:(num → num). R.mul(a, P(m)), " +
			"    {P:((num → num) → A) | homogeneous_polynomial(R, n, d, P)}) = " +
			"free_module_record(R, «monomialsOfDegree»)",
		Abbrev: Abbrev{
			{Name: "polynomialsOver", Text: "polynomial_algebra_ring(R, {i:num | i ≤ n})"},
			{Name: "monomialsOfDegree", Text: "{m:(num → num) | " +
				"    m ∈ monomials({i:num | i ≤ n}) ∧ nat_sum({i:num | i ≤ n}, m) = d}"},
		},
	}, func(a *Argument, R *Expr[RingOps[A]], n, d *Expr[Nat]) {
		carrier := a.Have(
			"a form of degree d is a finitely supported function "+
				"into R vanishing off the monomials of degree d",
			"{P:((num → num) → A) | homogeneous_polynomial(R, n, d, P)} = "+
				"finite_supp(R.zero, R.carrier, «monomialsOfDegree»)",
			Derive(func(b *Argument) {
				b.Do(Simp(Fwd(set_basic.Extension)))
				b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
				b.Show(
					"both memberships unfold to the same conditions on P",
					Simp(
						Fwd(homogeneous_polynomial.HomogeneousPolynomialDef),
						Fwd(polynomial_algebra.PolynomialAlgebraRingDef),
						Fwd(polynomial_algebra.PolynomialAlgebraDef),
						Fwd(function_module.FiniteSuppDef)),
					BySets())
			}))
		a.Show(
			"the sum, zero and negative of polynomials are "+
				"pointwise, and so is the scaling, as in the free module",
			Simp(
				Fwd(free_module.FreeModuleRecordDef),
				Fwd(polynomial_algebra.PolynomialAlgebraRingDef),
				Fwd(function_module.FunSmulDef),
				Fwd(carrier)),
			Refl())
	}),
})}

// FormsDimension — the forms of degree d in n + 1 variables over a field
// are a space of dimension binomial(d + n, n): they are the free module on
// the monomials of degree d, of which there are binomial(d + n, n), and the
// point masses at those monomials are a finite basis of it.
var FormsDimension = formsDimensionThm{family.Add(registry.ProofEntry{
	Name: "FormsDimension",
	Key:  "prop_f31c5c645f7d00f0",
	Reading: "The monomials of degree d in the variables 0, …, n are a basis; at n = 0 there " +
		"is the one monomial X₀^d, at d = 0 the constant one. The zero polynomial is a form of " +
		"every degree, so the forms of each degree are a subspace. module_dim is a choice, " +
		"pinned here because the scalars restricted to k are a field, so every basis has one size.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n d:num.",
		Hypotheses: []string{
			"subfield(M, k)",
		},
		Conclusion: "finite_dimensional(«hilbertCoefficients», " +
			"    mk_module(polynomial_algebra_ring(«hilbertCoefficients», {i:num | i ≤ n}).add, " +
			"        polynomial_algebra_ring(«hilbertCoefficients», {i:num | i ≤ n}).zero, " +
			"        polynomial_algebra_ring(«hilbertCoefficients», {i:num | i ≤ n}).neg, " +
			"        λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
			"        {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})) ∧ " +
			"module_dim(«hilbertCoefficients», " +
			"    mk_module(polynomial_algebra_ring(«hilbertCoefficients», {i:num | i ≤ n}).add, " +
			"        polynomial_algebra_ring(«hilbertCoefficients», {i:num | i ≤ n}).zero, " +
			"        polynomial_algebra_ring(«hilbertCoefficients», {i:num | i ≤ n}).neg, " +
			"        λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
			"        {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})) = " +
			"binomial(d + n, n)",
	}, func(a *Argument, M field.FieldFact[on.M], k *Expr[Set[A]], n, d *Expr[Nat], subK Fact) {
		K := a.TermAs[RingOps[A]]("«hilbertCoefficients»")
		inv := a.TermAs[Fun[A, A]]("M.inv")
		monomials := a.TermAs[Set[Fun[Nat, Nat]]](
			"{m:(num → num) | m ∈ monomials({i:num | i ≤ n}) ∧ nat_sum({i:num | i ≤ n}, m) = d}")
		free := a.TermAs[module_record.ModuleOps[A, Fun[Fun[Nat, Nat], A]]](
			"free_module_record(«hilbertCoefficients», " +
				"    {m:(num → num) | m ∈ monomials({i:num | i ≤ n}) ∧ nat_sum({i:num | i ≤ n}, m) = d})")
		masses := a.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
			"image(delta_at, " +
				"    {m:(num → num) | m ∈ monomials({i:num | i ≤ n}) ∧ nat_sum({i:num | i ≤ n}, m) = d})")
		scalars := a.Have(
			"k is a commutative ring",
			"comm_ring_on(«hilbertCoefficients»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k)))
		kField := a.Have(
			"k is a field",
			"ring_subfield(«hilbertCoefficients», M.inv, k)",
			By(subK, field.SubfieldRingSubfield.Read(M).At(k, k)))
		forms := a.Have(
			"the forms of degree d are the free module over k on the monomials of degree d",
			"mk_module(«polynomials».add, "+
				"    «polynomials».zero, "+
				"    «polynomials».neg, "+
				"    λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), "+
				"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}) = "+
				"free_module_record(«hilbertCoefficients», "+
				"    {m:(num → num) | m ∈ monomials({i:num | i ≤ n}) ∧ nat_sum({i:num | i ≤ n}, m) = d})",
			By(FormsFreeModule.At(K, n, d)))
		count := polynomial_algebra.MonomialsOfDegreeCount.At(n, d)
		a.Do(forms.Rw())
		a.Show(
			"the free module on the binomial(d + n, n) monomials of "+
				"degree d is finite-dimensional, of their number as dimension",
			SplitConj(
				Case(
					"the point masses at the finitely many monomials of degree d are a finite basis",
					By(
						scalars,
						kField,
						count,
						cardinality.HasSizeDef,
						free_module.FreeModuleOn.Read(scalars).At(monomials),
						free_module.DeltaAtBasis.Read(scalars).At(monomials),
						finite_set.FiniteImage.At(a.TermAs[Fun2[Fun[Nat, Nat], Fun[Nat, Nat], A]]("delta_at"), monomials),
						module_dimension.FiniteBasisDim.At(K, free, inv, masses))),
				Case(
					"its dimension is the number of the monomials",
					By(kField, count, cardinality.HasSizeDef, module_dimension.FreeModuleDim.At(K, inv, monomials)))))
	}),
})}

// PrincipalFormsShift — over a field, the forms of degree d in the ideal
// of a nonzero form F of degree e ≤ d are F times the forms of degree
// d − e, and multiplication by F is injective on them. Write d = s + e.
// The ideal of F is its multiples (ring_ideal.PrincipalIdealMultiples). A
// multiple F·Q that is a form of degree s + e is its own part of that
// degree (homogeneous_polynomial.FormOwnPart), which is F times the part
// of degree s of Q (FormTimesPart), a form of degree s; and F times a form
// of degree s is a form of degree s + e (FormProduct). The polynomials
// over k are an integral domain
// (polynomial_algebra.PolynomialAlgebraDomain), in which the nonzero F
// cancels.
var PrincipalFormsShift = principalFormsShiftThm{family.Add(registry.ProofEntry{
	Name: "PrincipalFormsShift",
	Key:  "prop_3e3961668d9a3349",
	Reading: "F ≠ 0 is load-bearing for injectivity and e ≤ d for the shift: below degree e the " +
		"only form in the ideal is zero. The ideal is that of F among the polynomials over k, the " +
		"one the Hilbert function reads, and it is exactly the multiples of F. e ≤ d also keeps (d − " +
		"e) + e = d exact under truncated subtraction; at e = d the shifted forms are the constants.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n e d:num. ∀F:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"homogeneous_polynomial(«hilbertCoefficients», n, e, F)",
			"F ≠ «polynomials».zero",
			"e ≤ d",
		},
		Conclusion: "«forms»(d) ∩ ideal_span(«polynomials», {F}) = image(«times», «forms»(d - e)) ∧ " +
			"injective_on(«forms»(d - e), «times»)",
		Abbrev: Abbrev{
			{Name: "polynomialSet", Text: "polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})"},
			{Name: "forms", Text: "λd:num. " +
				"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"},
			{Name: "times", Text: "λG:((num → num) → A). «polynomials».mul(F, G)"},
			{Name: "part", Text: "λd:num. λP:((num → num) → A). λm:(num → num). " +
				"    COND(sum({i:num | i ≤ n}, m) = d, P(m), M.zero)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, e, d *Expr[Nat],
		F *Arrow[Fun[Nat, Nat], A],
		subK, formF, nonzero, eLeD Fact,
	) {
		type polynomial = Fun[Fun[Nat, Nat], A]
		K := a.TermAs[RingOps[A]]("«hilbertCoefficients»")
		s, sDef := a.LetAs[Nat]("s", "d - e")
		degree := a.Have(
			"d is s + e, as e ≤ d",
			"d = s + e",
			ByArith(sDef, eLeD))
		a.Do(degree.Rw())
		kDomain := a.Have(
			"k, a subring of a field, is an integral domain",
			"integral_domain_on(«hilbertCoefficients»)",
			By(subK, field.SubfieldSubring.Read(M).At(k), integral_domain.SubringOfFieldDomain.Read(M).At(k)))
		domain := a.Have(
			"so the polynomials over k are an integral domain",
			"integral_domain_on(«polynomials»)",
			By(polynomial_algebra.PolynomialAlgebraDomain.Read(kDomain).At(
				a.TermAs[Set[Nat]]("{i:num | i ≤ n}"))))
		scalars := integral_domain.Ring.Read(kDomain)
		polynomials := integral_domain.Ring.Read(domain)
		polynomialF := a.Have(
			"F is a polynomial over k",
			"F ∈ «polynomialSet»",
			By(formF, homogeneous_polynomial.FormPolynomial.At(K, n, e, F)))
		multiples := a.Have(
			"the ideal of F is its multiples Q·F",
			"ideal_span(«polynomials», {F}) = "+
				"{P:(num → num) → A | "+
				"    ∃Q:((num → num) → A). "+
				"        Q ∈ «polynomialSet» ∧ P = polynomial_algebra_mul(«hilbertCoefficients», Q, F)}",
			By(polynomialF, ring_ideal.PrincipalIdealMultiples.Read(polynomials).AsFact().At(F)))
		divided := a.Have(
			"a form of degree s + e in the ideal is F times a form of degree s",
			"«forms»(s + e) ∩ ideal_span(«polynomials», {F}) ⊆ image(«times», «forms»(s))",
			multiples.Rw(),
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(b *Argument) {
				b.FixAs[polynomial]("P")
				given := b.Assume()
				formP := b.Have(
					"P is a form of degree s + e",
					"homogeneous_polynomial(«hilbertCoefficients», n, s + e, P)",
					BySets(given))
				Q, multiple := b.ObtainAs[polynomial](
					"and a multiple Q·F of F",
					"∃Q:((num → num) → A). "+
						"    Q ∈ «polynomialSet» ∧ P = polynomial_algebra_mul(«hilbertCoefficients», Q, F)",
					BySets(given))
				product := b.Have(
					"which is F·Q, the product of polynomials being commutative",
					"P = polynomial_algebra_mul(«hilbertCoefficients», F, Q)",
					By(
						multiple,
						polynomialF,
						comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(polynomials)).AsFact().At(Q, F)))
				factored := b.Have(
					"F·Q is its own part of degree s + e, which is F times the part of degree s of Q",
					"P = polynomial_algebra_mul(«hilbertCoefficients», F, «part»(s, Q))",
					By(
						scalars,
						product,
						formP,
						formF,
						multiple,
						homogeneous_polynomial.FormOwnPart.At(
							K,
							n,
							b.TermAs[Nat]("s + e"),
							b.TermAs[polynomial]("polynomial_algebra_mul(«hilbertCoefficients», F, Q)")),
						homogeneous_polynomial.FormTimesPart.At(K, n, e, s, F, Q)))
				b.Do(Simp(Fwd(set_basic.InImage)))
				b.Take(b.TermAs[polynomial]("«part»(s, Q)"))
				b.Show(
					"and the part of degree s of the polynomial Q is a form of degree s",
					By(scalars, factored, multiple, homogeneous_polynomial.FormPart.At(K, n, s, Q)))
			}))
		shifted := a.Have(
			"F times a form of degree s is a form of degree s + e in the ideal",
			"image(«times», «forms»(s)) ⊆ «forms»(s + e) ∩ ideal_span(«polynomials», {F})",
			multiples.Rw(),
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(b *Argument) {
				b.FixAs[polynomial]("P")
				given := b.Assume()
				G, image := b.ObtainAs[polynomial](
					"P is F·G for a form G of degree s",
					"∃G:((num → num) → A). "+
						"    homogeneous_polynomial(«hilbertCoefficients», n, s, G) ∧ "+
						"    P = polynomial_algebra_mul(«hilbertCoefficients», F, G)",
					BySets(given))
				commuted := b.Have(
					"which is G·F, the product of polynomials being commutative",
					"P = polynomial_algebra_mul(«hilbertCoefficients», G, F)",
					By(
						image,
						polynomialF,
						homogeneous_polynomial.FormPolynomial.At(K, n, s, G),
						comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(polynomials)).AsFact().At(F, G)))
				b.Show(
					"G·F is a form of degree s + e, and the multiple of F by the polynomial G",
					BySets(
						scalars,
						commuted,
						image,
						formF,
						homogeneous_polynomial.FormProduct.At(K, n, s, e, G, F),
						homogeneous_polynomial.FormPolynomial.At(K, n, s, G)))
			}))
		injective := a.Have(
			"multiplication by F is injective on the forms of degree s",
			"injective_on(«forms»(s), «times»)",
			Simp(Fwd(functions.InjectiveOnDef)),
			Derive(func(b *Argument) {
				G1 := b.FixAs[polynomial]("G₁")
				G2 := b.FixAs[polynomial]("G₂")
				given := b.Assume()
				b.Show(
					"F is not zero, and an integral domain cancels a nonzero factor",
					By(
						nonzero,
						given,
						polynomialF,
						homogeneous_polynomial.FormPolynomial.At(K, n, s, G1),
						homogeneous_polynomial.FormPolynomial.At(K, n, s, G2),
						integral_domain.MulCancelLeft.Read(domain).AsFact().At(F, G1, G2)))
			}))
		a.Show(
			"the two inclusions give the equality, and multiplication by F is injective",
			By(divided, shifted, injective, set_order.SubsetAntisym))
	}),
})}

// FormMultiplicationLinear — multiplying by a form F of degree e is a
// linear map over k from the forms of degree s to the forms of degree
// s + e. F·u is a form of degree e + s = s + e (FormProduct); the product
// distributes over sums; and a scalar multiple c·u is the product by the
// constant polynomial c (PolynomialAlgebraConstMul), which F passes, the
// product of polynomials being commutative.
var FormMultiplicationLinear = formMultiplicationLinearThm{family.Add(registry.ProofEntry{
	Name: "FormMultiplicationLinear",
	Key:  "prop_bf51bba7c1f18fd7",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n e s:num. ∀F:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"homogeneous_polynomial(«hilbertCoefficients», n, e, F)",
		},
		Conclusion: "module_homomorphism(«hilbertCoefficients», " +
			"    «formSpace»(s), " +
			"    «formSpace»(s + e), " +
			"    λG:((num → num) → A). polynomial_algebra_mul(«hilbertCoefficients», F, G))",
		Abbrev: Abbrev{
			{Name: "forms", Text: "λd:num. " +
				"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"},
			{Name: "formSpace", Text: "λd:num. " +
				"    mk_module(fun_add, " +
				"        fun_zero, " +
				"        fun_neg, " +
				"        λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"        «forms»(d))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, e, s *Expr[Nat],
		F *Arrow[Fun[Nat, Nat], A],
		subK, formF Fact,
	) {
		type polynomial = Fun[Fun[Nat, Nat], A]
		K := a.TermAs[RingOps[A]]("«hilbertCoefficients»")
		variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
		scalars := a.Have(
			"k is a commutative ring",
			"comm_ring_on(«hilbertCoefficients»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k)))
		polynomials := a.Have(
			"and so are the polynomials over k",
			"comm_ring_on(«polynomials»)",
			By(scalars, polynomial_algebra.PolynomialAlgebraCommRingOn))
		polynomialF := a.Have(
			"F is a polynomial over k",
			"F ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
			By(formF, homogeneous_polynomial.FormPolynomial.At(K, n, e, F)))
		into := a.Have(
			"F times a form of degree s is a form of degree s + e",
			Statement{
				Binders:    "∀u:((num → num) → A).",
				Hypotheses: []string{"u ∈ «forms»(s)"},
				Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», F, u) ∈ «forms»(s + e)",
			},
			a.ForEach(func(u *Expr[polynomial]) Action {
				return By(
					scalars,
					formF,
					homogeneous_polynomial.FormProduct.At(K, n, e, s, F, u),
					nat_arith.AddSym.At(e, s))
			}))
		additive := a.Have(
			"multiplication by F distributes over sums",
			Statement{
				Binders:    "∀u v:((num → num) → A).",
				Hypotheses: []string{"u ∈ «forms»(s)", "v ∈ «forms»(s)"},
				Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», F, fun_add(u, v)) = " +
					"fun_add(polynomial_algebra_mul(«hilbertCoefficients», F, u), " +
					"    polynomial_algebra_mul(«hilbertCoefficients», F, v))",
			},
			a.ForEach(func(u *Expr[polynomial]) Action {
				return a.ForEach(func(v *Expr[polynomial]) Action {
					return By(
						polynomialF,
						homogeneous_polynomial.FormPolynomial,
						comm_ring.LeftDistribOn.Read(polynomials).AsFact().At(F, u, v))
				})
			}))
		constants := a.Have(
			"the constants are a ring homomorphism into the polynomials",
			"ring_homomorphism(«hilbertCoefficients», "+
				"    «polynomials», "+
				"    polynomial_algebra_const(«hilbertCoefficients»))",
			By(scalars, polynomial_algebra.PolynomialAlgebraConstHom))
		scaled := a.Have(
			"multiplication by F commutes with scalars, a scalar multiple being the product by a constant",
			Statement{
				Binders:    "∀c:A. ∀u:((num → num) → A).",
				Hypotheses: []string{"c ∈ k", "u ∈ «forms»(s)"},
				Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», F, λm:(num → num). c * u(m)) = " +
					"λm:(num → num). c * polynomial_algebra_mul(«hilbertCoefficients», F, u, m)",
			},
			Derive(func(b *Argument) {
				c := b.FixAs[A]("c")
				u := b.FixAs[polynomial]("u")
				given := b.Assume()
				constant := b.TermAs[polynomial]("polynomial_algebra_const(«hilbertCoefficients», c)")
				product := b.TermAs[polynomial]("polynomial_algebra_mul(«hilbertCoefficients», F, u)")
				b.Show(
					"F times the constant c times u is the constant c times F times u",
					By(
						given,
						scalars,
						polynomialF,
						homogeneous_polynomial.FormPolynomial.At(K, n, s, u),
						ring_homomorphism.MapIn.Read(constants).AsFact().At(c),
						polynomial_algebra.PolynomialAlgebraConstMul.At(K, variables, c, u),
						polynomial_algebra.PolynomialAlgebraConstMul.At(K, variables, c, product),
						comm_ring.MulIn.Read(polynomials).AsFact().At(F, u),
						comm_monoid.LeftCommOn.Read(comm_ring.MulMonoidOn.Read(polynomials)).AsFact().At(F, constant, u)))
			}))
		a.Show(
			"the forms of degrees s and s + e are vector spaces, "+
				"and multiplication by F is linear between them",
			Simp(Fwd(module_homomorphism.ModuleHomomorphismDef)),
			By(
				subK,
				into,
				additive,
				scaled,
				FormsSubspace.Read(M).At(k, n, s),
				FormsSubspace.Read(M).At(k, n, a.TermAs[Nat]("s + e"))))
	}),
})}

// PlaneCurveHilbertFunction — a plane curve of degree e > 0 has Hilbert
// function e·d + 1 − (e − 1)(e − 2)/2 at every degree d ≥ e. Write
// d = s + e. The Hilbert function at d is binomial(d + 2, 2), the
// dimension of the forms of degree d, less the dimension of those in the
// ideal of F (HilbertFunctionCodimension). Those in the ideal are F times
// the forms of degree s, onto which multiplication by F is a one-to-one
// linear map (PrincipalFormsShift, FormMultiplicationLinear,
// InjectiveImageDim), so they have dimension binomial(s + 2, 2)
// (FormsDimension). Doubled, the difference is
// (s + e + 2)(s + e + 1) − (s + 2)(s + 1) = 2se + e² + 3e
// (binomial.ColumnTwo), and (e − 1)(e − 2) is e² − 3e + 2.
var PlaneCurveHilbertFunction = planeCurveHilbertFunctionThm{family.Add(registry.ProofEntry{
	Name: "PlaneCurveHilbertFunction",
	Key:  "prop_c07571112c0ea658",
	Reading: "Stated doubled, 2·h(d) + (e − 1)(e − 2) = 2(e·d + 1), to stay in the " +
		"naturals: (e − 1)(e − 2) is even, and its half is the genus of a smooth plane " +
		"curve of degree e. 0 < e is load-bearing: a nonzero constant generates the whole " +
		"ring, whose Hilbert function is zero. Neither irreducibility nor smoothness is " +
		"asked; at e = 3 the function is 3d and the genus one. Truncated subtraction is " +
		"harmless: at e = 1 and e = 2 the product (e − 1)(e − 2) is zero, its true value.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀e d:num. ∀F:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"homogeneous_polynomial(«hilbertCoefficients», 2, e, F)",
			"F ≠ polynomial_algebra_ring(«hilbertCoefficients», {i:num | i ≤ 2}).zero",
			"0 < e",
			"e ≤ d",
		},
		Conclusion: "2 * projective_hilbert_function(field_ring(M), k, 2, {F}, d) + (e - 1) * (e - 2) = " +
			"2 * (e * d + 1)",
		Abbrev: Abbrev{
			{Name: "forms", Text: "λd:num. " +
				"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», 2, d, P)}"},
			{Name: "formSpace", Text: "λd:num. " +
				"    mk_module(fun_add, " +
				"        fun_zero, " +
				"        fun_neg, " +
				"        λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"        «forms»(d))"},
			{Name: "ideal", Text: "ideal_span( " +
				"    polynomial_algebra_ring(«hilbertCoefficients», {i:num | i ≤ 2}), {F})"},
			{Name: "times", Text: "λG:((num → num) → A). polynomial_algebra_mul(«hilbertCoefficients», F, G)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		e, d *Expr[Nat],
		F *Arrow[Fun[Nat, Nat], A],
		subK, formF, nonzero, positive, eLeD Fact,
	) {
		type polynomial = Fun[Fun[Nat, Nat], A]
		type space = module_record.ModuleOps[A, polynomial]
		K := a.TermAs[RingOps[A]]("«hilbertCoefficients»")
		inv := a.TermAs[Fun[A, A]]("M.inv")
		two := a.TermAs[Nat]("2")
		s, sDef := a.LetAs[Nat]("s", "d - e")
		degree := a.Have(
			"write d as s + e, e being at most d",
			"d = s + e",
			ByArith(sDef, eLeD))
		a.Do(degree.Rw())
		shift := a.Conjuncts(
			a.Simplified(
				GroupPremises(
					subK, formF, nonzero, eLeD, PrincipalFormsShift.Read(M).At(k, two, e, a.TermAs[Nat]("s + e"), F)),
				Fwd(nat_monus.AddSubCancel)),
			"the forms of degree s + e in the ideal of F are F times the forms of degree s",
			"and multiplication by F is one-to-one on those")
		kField := a.Have(
			"k is a field",
			"ring_subfield(«hilbertCoefficients», M.inv, k)",
			By(subK, field.SubfieldRingSubfield.Read(M).At(k, k)))
		linear := a.Have(
			"multiplication by F is a linear map from the forms of degree s to those of degree s + e",
			"module_homomorphism(«hilbertCoefficients», «formSpace»(s), «formSpace»(s + e), «times»)",
			By(subK, formF, FormMultiplicationLinear.Read(M).At(k, two, e, s, F)))
		layer := a.Have(
			"so the forms of degree s + e in the ideal, its one-to-one image, "+
				"have the dimension binomial(s + 2, 2) of the forms of degree s",
			"module_dim(«hilbertCoefficients», "+
				"    restrict_module(«formSpace»(s + e), «forms»(s + e) ∩ «ideal»)) = "+
				"binomial(s + 2, 2)",
			By(
				subK,
				kField,
				linear,
				shift[0],
				shift[1],
				FormsDimension.Read(M).At(k, two, s),
				module_dimension.InjectiveImageDim.At(
					K,
					inv,
					a.TermAs[space]("«formSpace»(s)"),
					a.TermAs[space]("«formSpace»(s + e)"),
					a.TermAs[Fun[polynomial, polynomial]]("«times»"))))
		equation := a.Have(
			"F, a form, is a polynomial over k",
			"{F} ⊆ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ 2})",
			BySets(formF, homogeneous_polynomial.FormPolynomial.At(K, two, e, F)))
		quotient := a.Have(
			"the Hilbert function at s + e and that dimension add to the "+
				"dimension binomial(s + e + 2, 2) of the forms of degree s + e",
			"module_dim(«hilbertCoefficients», "+
				"    restrict_module(«formSpace»(s + e), «forms»(s + e) ∩ «ideal»)) + "+
				"projective_hilbert_function(field_ring(M), k, 2, {F}, s + e) = "+
				"binomial(s + e + 2, 2)",
			By(
				subK,
				equation,
				HilbertFunctionCodimension.Read(M).At(
					k, two, a.TermAs[Nat]("s + e"), a.TermAs[Set[polynomial]]("{F}"))))
		product := a.Have(
			"(e − 1)(e − 2) is e² − 3e + 2, e being positive",
			"(e - 1) * (e - 2) + 3 * e = e * e + 2",
			Derive(func(b *Argument) {
				b.Cases(b.Term("e = 1"))
				b.When(
					"at e = 1 both factors vanish",
					func(c *Argument, one Fact) {
						c.Show(
							"and both sides are 3",
							ByArith(one))
					})
				b.Otherwise(
					"past 1, e − 1 is t + 1 and e is t + 2, for t = e − 2",
					func(c *Argument, other Fact) {
						_, tDef := c.LetAs[Nat]("t", "e - 2")
						plusTwo := c.Have(
							"e is t + 2",
							"e = t + 2",
							ByArith(tDef, positive, other))
						minusOne := c.Have(
							"so e − 1 is t + 1",
							"e - 1 = t + 1",
							ByArith(plusTwo))
						c.Show(
							"and (t + 1)·t + 3(t + 2) is (t + 2)² + 2",
							minusOne.Rw(),
							plusTwo.Rw(),
							ByArith())
					})
			}))
		a.Show(
			"doubled, the Hilbert function is (s + e + 2)(s + e + 1) − (s + 2)(s + 1) = 2se + e² + 3e",
			ByArith(
				layer,
				quotient,
				product,
				binomial.ColumnTwo.At(a.TermAs[Nat]("s + 2")),
				binomial.ColumnTwo.At(a.TermAs[Nat]("s + e + 2"))))
	}),
})}

// FormsSubspace — the forms of degree d over a subfield k are a vector
// space over k under the pointwise operations, and an ideal of the
// polynomials over k meets them in a subspace. The forms of degree d are
// the free module over k on the monomials of degree d (FormsFreeModule);
// an ideal is closed under sums, and under scalar multiples because a
// scalar multiple is the product by a constant polynomial
// (PolynomialAlgebraConstMul).
var FormsSubspace = formsSubspaceThm{family.Add(registry.ProofEntry{
	Name: "FormsSubspace",
	Key:  "prop_35fed835d5f657cf",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n d:num.",
		Hypotheses: []string{
			"subfield(M, k)",
		},
		Conclusion: "module_on(«hilbertCoefficients», «formSpace»(d)) ∧ " +
			"(∀I:set((num → num) → A). " +
			"    ring_ideal(«polynomials», I) ⇒ " +
			"    submodule(«hilbertCoefficients», «formSpace»(d), «forms»(d) ∩ I))",
		Abbrev: Abbrev{
			{Name: "forms", Text: "λd:num. " +
				"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"},
			{Name: "formSpace", Text: "λd:num. " +
				"    mk_module(fun_add, " +
				"        fun_zero, " +
				"        fun_neg, " +
				"        λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"        «forms»(d))"},
		},
	}, func(a *Argument, M field.FieldFact[on.M], k *Expr[Set[A]], n, d *Expr[Nat], subK Fact) {
		scalars := a.Have(
			"k is a commutative ring",
			"comm_ring_on(«hilbertCoefficients»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k)))
		monomials := a.TermAs[Set[Fun[Nat, Nat]]](
			"{m:(num → num) | m ∈ monomials({i:num | i ≤ n}) ∧ nat_sum({i:num | i ≤ n}, m) = d}")
		free := a.Have(
			"the forms of degree d are the free module over k on the monomials of degree d",
			"«formSpace»(d) = "+
				"free_module_record(«hilbertCoefficients», "+
				"    {m:(num → num) | m ∈ monomials({i:num | i ≤ n}) ∧ nat_sum({i:num | i ≤ n}, m) = d})",
			By(FormsFreeModule.At(a.TermAs[RingOps[A]]("«hilbertCoefficients»"), n, d)))
		space := a.Have(
			"a free module over k is a vector space over k",
			"module_on(«hilbertCoefficients», «formSpace»(d))",
			free.Rw(),
			By(scalars, free_module.FreeModuleOn.Read(scalars).At(monomials)))
		constants := a.Have(
			"the constants are a ring homomorphism into the polynomials",
			"ring_homomorphism(«hilbertCoefficients», "+
				"    «polynomials», "+
				"    polynomial_algebra_const(«hilbertCoefficients»))",
			By(scalars, polynomial_algebra.PolynomialAlgebraConstHom))
		a.Show(
			"the forms of degree d are a vector space, and an ideal meets them in a subspace",
			SplitConj(
				Case(
					"the forms of degree d are a vector space over k",
					By(space)),
				Case(
					"an ideal of the polynomials over k meets them in a subspace",
					Derive(func(b *Argument) {
						I := b.FixAs[Set[Fun[Fun[Nat, Nat], A]]]("I")
						ideal := b.Assume()
						scaled := b.Have(
							"the ideal holds the scalar multiples of its forms of "+
								"degree d, a scalar multiple being the product by a constant",
							Statement{
								Binders:    "∀c:A. ∀u:((num → num) → A).",
								Hypotheses: []string{"c ∈ k", "u ∈ «forms»(d) ∩ I"},
								Conclusion: "(λm:(num → num). c * u(m)) ∈ «forms»(d) ∩ I",
							},
							Derive(func(c *Argument) {
								cv := c.FixAs[A]("c")
								u := c.FixAs[Fun[Fun[Nat, Nat], A]]("u")
								given := c.Assume()
								parts := c.Have(
									"u is a form of degree d in the ideal",
									"homogeneous_polynomial(«hilbertCoefficients», n, d, u) ∧ u ∈ I",
									BySets(given))
								asProduct := c.Have(
									"the scalar multiple is the product by the constant c",
									"polynomial_algebra_mul(«hilbertCoefficients», "+
										"    polynomial_algebra_const(«hilbertCoefficients», c), "+
										"    u) = "+
										"(λm:(num → num). c * u(m))",
									By(
										given,
										parts,
										scalars,
										homogeneous_polynomial.FormPolynomial,
										polynomial_algebra.PolynomialAlgebraConstMul.At(
											c.TermAs[RingOps[A]]("«hilbertCoefficients»"), c.TermAs[Set[Nat]]("{i:num | i ≤ n}"), cv, u)))
								c.Show(
									"a product by a polynomial stays in the ideal, and a scalar multiple of a form is a form",
									BySets(
										ideal,
										asProduct,
										given,
										module.SmulIn.Read(space).AsFact().At(cv, u),
										ring_homomorphism.MapIn.Read(constants).AsFact().At(cv),
										ring_ideal.IdealMul.At(
											c.TermAs[RingOps[Fun[Fun[Nat, Nat], A]]]("«polynomials»"),
											I,
											c.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_const(«hilbertCoefficients», c)"),
											u)))
							}))
						summed := b.Have(
							"the ideal holds the sums of its forms of degree d",
							Statement{
								Binders:    "∀u v:((num → num) → A).",
								Hypotheses: []string{"u ∈ «forms»(d) ∩ I", "v ∈ «forms»(d) ∩ I"},
								Conclusion: "«formSpace»(d).add(u, v) ∈ «forms»(d) ∩ I",
							},
							Derive(func(c *Argument) {
								u := c.FixAs[Fun[Fun[Nat, Nat], A]]("u")
								v := c.FixAs[Fun[Fun[Nat, Nat], A]]("v")
								given := c.Assume()
								c.Do(Simp(Fwd(module_record.ModAddDef)))
								c.Show(
									"a sum of members of the ideal is in it, and a sum of forms of degree d is one",
									BySets(
										ideal,
										given,
										ring_ideal.IdealAdd.At(c.TermAs[RingOps[Fun[Fun[Nat, Nat], A]]]("«polynomials»"), I, u, v),
										comm_monoid.OpIn.Read(module.AddMonoidOn.Read(space)).AsFact().At(u, v)))
							}))
						zero := b.Have(
							"the ideal holds the zero form",
							"«formSpace»(d).zero ∈ «forms»(d) ∩ I",
							Simp(Fwd(module_record.ModZeroDef)),
							BySets(ideal, ring_ideal.IdealZero, comm_monoid.IdentityIn.Read(module.AddMonoidOn.Read(space))))
						b.Show(
							"so the ideal meets the forms of degree d in a subspace",
							By(scaled, summed, zero, space, submodule.SubmoduleCriterion, set_order.InterSubset))
					})),
			))
	}),
})}

// HilbertFunctionCodimension — the Hilbert function at d is the codimension
// of the forms of degree d in the ideal E spans among all forms of degree d:
// that layer is finite-dimensional, and its dimension and h(d) add to
// binomial(d + n, n). The forms of degree d are a space of that dimension
// (FormsDimension) meeting the ideal in a subspace (FormsSubspace), and the
// subspace and the quotient by it, whose dimension is h(d), add their
// dimensions (QuotientDim).
var HilbertFunctionCodimension = hilbertFunctionCodimensionThm{family.Add(registry.ProofEntry{
	Name: "HilbertFunctionCodimension",
	Key:  "prop_6334deb357a56464",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n d:num. ∀E:set((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"E ⊆ «polynomials».carrier",
		},
		Conclusion: "finite_dimensional(«hilbertCoefficients», «idealForms») ∧ " +
			"module_dim(«hilbertCoefficients», «idealForms») + " +
			"projective_hilbert_function(field_ring(M), k, n, E, d) = " +
			"binomial(d + n, n)",
		Abbrev: Abbrev{
			{Name: "forms", Text: "λd:num. " +
				"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"},
			{Name: "formSpace", Text: "mk_module(fun_add, " +
				"    fun_zero, " +
				"    fun_neg, " +
				"    λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"    «forms»(d))"},
			{Name: "idealForms", Text: "restrict_module(«formSpace», " +
				"    «forms»(d) ∩ ideal_span(«polynomials», E))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, d *Expr[Nat],
		E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
		subK, equationsOverK Fact,
	) {
		kRing := a.TermAs[RingOps[A]]("«hilbertCoefficients»")
		inv := a.TermAs[Fun[A, A]]("M.inv")
		space := a.TermAs[module_record.ModuleOps[A, Fun[Fun[Nat, Nat], A]]]("«formSpace»")
		layer := a.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«forms»(d) ∩ ideal_span(«polynomials», E)")
		polynomialsRing := a.Have(
			"the polynomials over k are a commutative ring",
			"comm_ring_on(«polynomials»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k), polynomial_algebra.PolynomialAlgebraCommRingOn))
		subspace := a.Have(
			"the forms of degree d are a space over k, meeting the ideal E spans in a subspace",
			"module_on(«hilbertCoefficients», «formSpace») ∧ "+
				"submodule(«hilbertCoefficients», «formSpace», «forms»(d) ∩ ideal_span(«polynomials», E))",
			By(
				subK,
				equationsOverK,
				FormsSubspace.Read(M).At(k, n, d),
				ring_ideal.SpanIdeal.Read(polynomialsRing)))
		dimension := a.Have(
			"the forms of degree d are a space of dimension binomial(d + n, n)",
			"finite_dimensional(«hilbertCoefficients», «formSpace») ∧ "+
				"module_dim(«hilbertCoefficients», «formSpace») = binomial(d + n, n)",
			By(subK, FormsDimension.Read(M).At(k, n, d)))
		kField := a.Have(
			"k is a field",
			"ring_subfield(«hilbertCoefficients», M.inv, k)",
			By(subK, field.SubfieldRingSubfield.Read(M).At(k, k)))
		hilbert := a.Have(
			"the Hilbert function at d is the dimension of the forms of degree d modulo the ideal's",
			"projective_hilbert_function(field_ring(M), k, n, E, d) = "+
				"module_dim(«hilbertCoefficients», "+
				"    quotient_module(«formSpace», «forms»(d) ∩ ideal_span(«polynomials», E)))",
			By(ProjectiveHilbertFunctionDef))
		a.Show(
			"the ideal's forms of degree d are finite-dimensional, and their "+
				"dimension and that of the quotient add to binomial(d + n, n)",
			ByArith(
				hilbert,
				subspace,
				dimension,
				kField,
				module_dimension.DimFiniteIffSubAndQuotient.At(kRing, space, inv, layer),
				module_dimension.QuotientDim.At(kRing, space, inv, layer)))
	}),
})}

// CurveIdealPrime — the ideal of a smooth projective equation curve over k
// is prime, not only its ideal over M. The polynomials over k include into
// those over M as a ring map (polynomial_algebra.PolynomialAlgebraInclusionHom),
// so the polynomials over k in the prime ideal
// over M, its contraction, are a prime ideal of the polynomials over k
// (spec_functor.PreimagePrime). The contraction holds the equations, so it
// holds the ideal over k, and a polynomial over k in the ideal over M lies in
// the ideal over k (polynomial_algebra.IdealDescent): the ideal over k is the
// contraction.
var CurveIdealPrime = curveIdealPrimeThm{family.Add(registry.ProofEntry{
	Name: "CurveIdealPrime",
	Key:  "prop_977b9cfe3b812518",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n:num. ∀E:set((num → num) → A).",
		Hypotheses: []string{
			"smooth_projective_equation_curve(M, k, n, E)",
		},
		Conclusion: "prime_ideal(«polynomials», ideal_span(«polynomials», E))",
		Abbrev: Abbrev{
			{Name: "polynomialSet", Text: "polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})"},
			{Name: "ringOverM", Text: "polynomial_algebra_ring(field_ring(M), {i:num | i ≤ n})"},
			{Name: "idealOverM", Text: "ideal_span(«ringOverM», E)"},
			{Name: "contraction", Text: "preimage_on(«polynomialSet», λP:((num → num) → A). P, «idealOverM»)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n *Expr[Nat],
		E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
		curve Fact,
	) {
		subK := CurveConstantsSubfield.Read(curve)
		equations := CurveEquationsForms.Read(curve)
		primeM := CurveIdealGeometricallyPrime.Read(curve)
		ringOverK := a.TermAs[module_record.RingOps[Fun[Fun[Nat, Nat], A]]]("«polynomials»")
		ringOverM := a.TermAs[module_record.RingOps[Fun[Fun[Nat, Nat], A]]]("«ringOverM»")
		idealOverM := a.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«idealOverM»")
		contracted := a.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«contraction»")
		fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		scalars := a.Have(
			"k is a commutative ring",
			"comm_ring_on(«hilbertCoefficients»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k)))
		polynomials := a.Have(
			"and so are the polynomials over k",
			"comm_ring_on(«polynomials»)",
			By(scalars, polynomial_algebra.PolynomialAlgebraCommRingOn))
		polynomialsOverM := a.Have(
			"as are the polynomials over M",
			"comm_ring_on(«ringOverM»)",
			By(field.RingOn.Read(M), polynomial_algebra.PolynomialAlgebraCommRingOn))
		inK := a.Have(
			"the equations are polynomials over k",
			"E ⊆ «polynomialSet»",
			BySets(equations, homogeneous_polynomial.FormPolynomial))
		inclusion := a.Have(
			"the polynomials over k include into those over M as a ring map",
			"ring_homomorphism(«polynomials», «ringOverM», λP:((num → num) → A). P)",
			By(
				subK,
				field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("M"), k),
				scalars,
				field.RingOn.Read(M),
				polynomial_algebra.PolynomialAlgebraInclusionHom.At(
					fieldRing, k, a.TermAs[Set[Nat]]("{i:num | i ≤ n}"))))
		contraction := a.Have(
			"so the contraction of the prime ideal over M is a prime ideal of the polynomials over k",
			"prime_ideal(«polynomials», «contraction»)",
			By(
				polynomials,
				polynomialsOverM,
				inclusion,
				primeM,
				spec_functor.PreimagePrime.At(
					ringOverK,
					ringOverM,
					a.TermAs[Fun[Fun[Fun[Nat, Nat], A], Fun[Fun[Nat, Nat], A]]]("λP:((num → num) → A). P"),
					idealOverM)))
		generators := a.Have(
			"the contraction holds the equations, polynomials over k in the ideal over M",
			"E ⊆ «contraction»",
			Simp(Fwd(functions.PreimageOnDef)),
			BySets(inK, ring_ideal.SpanContains.At(ringOverM, E)))
		within := a.Have(
			"so it holds the ideal over k",
			"ideal_span(«polynomials», E) ⊆ «contraction»",
			By(
				contraction,
				generators,
				ring_ideal.PrimeIdealIdeal.At(ringOverK, contracted),
				ring_ideal.SpanLeast.At(ringOverK, E, contracted)))
		descent := a.Have(
			"and lies in it: a polynomial over k in the ideal over M lies in the ideal over k",
			"«contraction» ⊆ ideal_span(«polynomials», E)",
			Derive(func(b *Argument) {
				b.Do(Simp(Fwd(set_basic.SubsetDef), Fwd(functions.PreimageOnDef)))
				b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
				given := b.Assume()
				b.Show(
					"the ideal descends from M to k",
					By(given, inK, subK, polynomial_algebra.IdealDescent.Read(M)))
			}))
		equal := a.Have(
			"so the ideal over k is the contraction",
			"ideal_span(«polynomials», E) = «contraction»",
			By(within, descent, set_order.SubsetAntisym))
		a.Show(
			"which is prime",
			equal.Rw(),
			By(contraction))
	}),
})}

// HyperplaneSectionBound — for a polynomial F over k outside a prime ideal
// J, a subspace X of the forms of degree d holding the forms of degree d in
// J and F times every form of degree e has codimension at most h(d) − h(e).
// The forms of degree d modulo J split into the forms modulo X and X modulo
// J (QuotientChainDim); multiplication by F, read modulo J, maps the forms
// of degree e into X modulo J with kernel the forms of degree e in J, F
// being no zero divisor modulo the prime J, so its image there has
// dimension h(e) (RankNullity, HilbertFunctionCodimension).
var HyperplaneSectionBound = hyperplaneSectionBoundThm{family.Add(registry.ProofEntry{
	Name: "HyperplaneSectionBound",
	Key:  "prop_544be282d3e66f42",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k:set(A). " +
			"∀n d e:num. " +
			"∀E X:set((num → num) → A). " +
			"∀F:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"prime_ideal(«polynomials», «ideal»)",
			"F ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
			"F ∉ «ideal»",
			"submodule(«hilbertCoefficients», «formSpace»(d), X)",
			"«forms»(d) ∩ «ideal» ⊆ X",
			"∀Q:((num → num) → A). " +
				"    homogeneous_polynomial(«hilbertCoefficients», n, e, Q) ⇒ " +
				"    polynomial_algebra_mul(«hilbertCoefficients», F, Q) ∈ X",
		},
		Conclusion: "module_dim(«hilbertCoefficients», quotient_module(«formSpace»(d), X)) + " +
			"projective_hilbert_function(field_ring(M), k, n, E, e) ≤ " +
			"projective_hilbert_function(field_ring(M), k, n, E, d)",
		Abbrev: Abbrev{
			{Name: "ideal", Text: "ideal_span(«polynomials», E)"},
			{Name: "forms", Text: "λd:num. " +
				"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"},
			{Name: "formSpace", Text: "λd:num. " +
				"    mk_module(fun_add, " +
				"        fun_zero, " +
				"        fun_neg, " +
				"        λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"        «forms»(d))"},
			{Name: "quotient", Text: "quotient_module(restrict_module(«formSpace»(d), X), " +
				"    «forms»(d) ∩ «ideal»)"},
			{Name: "multiply", Text: "λP:((num → num) → A). " +
				"    coset_map(fun_add, " +
				"        «forms»(d) ∩ «ideal», " +
				"        polynomial_algebra_mul(«hilbertCoefficients», F, P))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, d, e *Expr[Nat],
		E, X *Expr[Set[Fun[Fun[Nat, Nat], A]]],
		F *Arrow[Fun[Nat, Nat], A],
		subK, prime, polynomialF, outside, subspace, holdsIdeal, holdsMultiples Fact,
	) {
		K := a.TermAs[RingOps[A]]("«hilbertCoefficients»")
		inv := a.TermAs[Fun[A, A]]("M.inv")
		spaceD := a.TermAs[module_record.ModuleOps[A, Fun[Fun[Nat, Nat], A]]]("«formSpace»(d)")
		spaceE := a.TermAs[module_record.ModuleOps[A, Fun[Fun[Nat, Nat], A]]]("«formSpace»(e)")
		spaceX := a.TermAs[module_record.ModuleOps[A, Fun[Fun[Nat, Nat], A]]](
			"restrict_module(«formSpace»(d), X)")
		quotient := a.TermAs[module_record.ModuleOps[A, Set[Fun[Fun[Nat, Nat], A]]]]("«quotient»")
		formsD := a.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«forms»(d)")
		idealD := a.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«forms»(d) ∩ «ideal»")
		multiply := a.TermAs[Fun[Fun[Fun[Nat, Nat], A], Set[Fun[Fun[Nat, Nat], A]]]]("«multiply»")
		scalars := a.Have(
			"k is a commutative ring",
			"comm_ring_on(«hilbertCoefficients»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k)))
		polynomials := a.Have(
			"and so are the polynomials over k",
			"comm_ring_on(«polynomials»)",
			By(scalars, polynomial_algebra.PolynomialAlgebraCommRingOn))
		kField := a.Have(
			"k is a field",
			"ring_subfield(«hilbertCoefficients», M.inv, k)",
			By(subK, field.SubfieldRingSubfield.Read(M).At(k, k)))
		idealJ := a.Have(
			"the prime ideal is an ideal",
			"ring_ideal(«polynomials», «ideal»)",
			By(prime, ring_ideal.PrimeIdealIdeal))
		equations := a.Have(
			"the equations lie in the ideal they span, so in the polynomials over k",
			"E ⊆ «polynomials».carrier",
			BySets(
				ring_ideal.SpanContains.At(a.TermAs[RingOps[Fun[Fun[Nat, Nat], A]]]("«polynomials»"), E),
				ring_ideal.IdealSubset.Read(idealJ)))
		spaceFactsD := a.Conjuncts(
			GroupPremises(subK, FormsSubspace.Read(M).At(k, n, d)),
			"the forms of degree d are a vector space",
			"meeting every ideal in a subspace")
		spaceFactsE := a.Conjuncts(
			GroupPremises(subK, FormsSubspace.Read(M).At(k, n, e)),
			"so are the forms of degree e",
			"meeting every ideal in a subspace")
		moduleD, moduleE := spaceFactsD[0], spaceFactsE[0]
		subD := a.Have(
			"the forms of degree d in the ideal are a subspace",
			"submodule(«hilbertCoefficients», «formSpace»(d), «forms»(d) ∩ «ideal»)",
			By(idealJ, spaceFactsD[1]))
		dimensionD := a.Conjuncts(
			GroupPremises(subK, FormsDimension.Read(M).At(k, n, d)),
			"the forms of degree d are finite-dimensional",
			"of dimension binomial(d + n, n)")
		dimensionE := a.Conjuncts(
			GroupPremises(subK, FormsDimension.Read(M).At(k, n, e)),
			"so are the forms of degree e",
			"of dimension binomial(e + n, n)")
		finiteD, finiteE := dimensionD[0], dimensionE[0]
		whole := a.Have(
			"the forms of degree d are the whole space",
			"restrict_module(«formSpace»(d), «forms»(d)) = «formSpace»(d)",
			Simp(Fwd(module_record.RestrictModuleDef)),
			Refl())
		finiteModJ := a.Have(
			"the forms of degree d modulo the ideal are finite-dimensional",
			"finite_dimensional(«hilbertCoefficients», "+
				"    quotient_module(restrict_module(«formSpace»(d), «forms»(d)), «forms»(d) ∩ «ideal»))",
			whole.Rw(),
			By(
				moduleD,
				kField,
				subD,
				finiteD,
				module_dimension.DimFiniteIffSubAndQuotient.At(K, spaceD, inv, idealD)))
		chain := a.Conjuncts(
			a.Simplified(
				a.Have(
					"the forms of degree d modulo the ideal split into the forms modulo X and X modulo the ideal",
					"finite_dimensional(«hilbertCoefficients», "+
						"    quotient_module(restrict_module(«formSpace»(d), «forms»(d)), X)) ∧ "+
						"finite_dimensional(«hilbertCoefficients», «quotient») ∧ "+
						"module_dim(«hilbertCoefficients», "+
						"    quotient_module(restrict_module(«formSpace»(d), «forms»(d)), «forms»(d) ∩ «ideal»)) = "+
						"module_dim(«hilbertCoefficients», "+
						"    quotient_module(restrict_module(«formSpace»(d), «forms»(d)), X)) + "+
						"module_dim(«hilbertCoefficients», «quotient»)",
					By(
						moduleD,
						kField,
						subspace,
						subD,
						holdsIdeal,
						finiteModJ,
						submodule.CarrierSubmodule.At(K, spaceD),
						submodule.SubmoduleSubset.At(K, spaceD, X),
						module_dimension.QuotientChainDim.At(K, spaceD, inv, formsD, X, idealD))),
				Fwd(whole)),
			"X has finite codimension",
			"X modulo the ideal is finite-dimensional",
			"and the dimensions add")
		hilbertD := a.Have(
			"so the Hilbert function at d is the codimension of X plus the dimension of X modulo the ideal",
			"projective_hilbert_function(field_ring(M), k, n, E, d) = "+
				"module_dim(«hilbertCoefficients», quotient_module(«formSpace»(d), X)) + "+
				"module_dim(«hilbertCoefficients», «quotient»)",
			By(ProjectiveHilbertFunctionDef, chain[2]))
		moduleX := a.Have(
			"X is a vector space",
			"module_on(«hilbertCoefficients», restrict_module(«formSpace»(d), X))",
			By(moduleD, subspace, submodule.SubmoduleModuleOn.At(K, spaceD, X)))
		idealInX := a.Have(
			"in which the forms of degree d in the ideal are a subspace",
			"submodule(«hilbertCoefficients», restrict_module(«formSpace»(d), X), «forms»(d) ∩ «ideal»)",
			By(subD, holdsIdeal, submodule.SubmoduleRestrict.At(K, spaceD, X, idealD)))
		additive := a.Have(
			"multiplication by F is additive",
			Statement{
				Binders:    "∀u v:((num → num) → A).",
				Hypotheses: []string{"u ∈ «forms»(e)", "v ∈ «forms»(e)"},
				Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», F, fun_add(u, v)) = " +
					"fun_add(polynomial_algebra_mul(«hilbertCoefficients», F, u), " +
					"    polynomial_algebra_mul(«hilbertCoefficients», F, v))",
			},
			Derive(func(b *Argument) {
				u := b.FixAs[Fun[Fun[Nat, Nat], A]]("u")
				v := b.FixAs[Fun[Fun[Nat, Nat], A]]("v")
				given := b.Assume()
				b.Show(
					"products by F distribute over sums of polynomials over k",
					By(
						given,
						polynomialF,
						homogeneous_polynomial.FormPolynomial,
						comm_ring.LeftDistribOn.Read(polynomials).AsFact().At(F, u, v)))
			}))
		constants := a.Have(
			"the constants are a ring homomorphism into the polynomials",
			"ring_homomorphism(«hilbertCoefficients», "+
				"    «polynomials», "+
				"    polynomial_algebra_const(«hilbertCoefficients»))",
			By(scalars, polynomial_algebra.PolynomialAlgebraConstHom))
		scaled := a.Have(
			"multiplication by F commutes with scalars, a scalar multiple being the product by a constant",
			Statement{
				Binders:    "∀c:A. ∀u:((num → num) → A).",
				Hypotheses: []string{"c ∈ k", "u ∈ «forms»(e)"},
				Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», F, λm:(num → num). c * u(m)) = " +
					"λm:(num → num). c * polynomial_algebra_mul(«hilbertCoefficients», F, u, m)",
			},
			Derive(func(b *Argument) {
				c := b.FixAs[A]("c")
				u := b.FixAs[Fun[Fun[Nat, Nat], A]]("u")
				given := b.Assume()
				members := b.Have(
					"u and the constant c are polynomials over k",
					"u ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ "+
						"polynomial_algebra_const(«hilbertCoefficients», c) ∈ "+
						"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					By(
						given,
						homogeneous_polynomial.FormPolynomial,
						ring_homomorphism.MapIn.Read(constants).AsFact().At(c)))
				variables := b.TermAs[Set[Nat]]("{i:num | i ≤ n}")
				constant := b.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_const(«hilbertCoefficients», c)")
				product := b.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_mul(«hilbertCoefficients», F, u)")
				b.Show(
					"F times the constant c times u is the constant c times F times u",
					By(
						given,
						members,
						polynomialF,
						scalars,
						polynomial_algebra.PolynomialAlgebraConstMul.At(K, variables, c, u),
						polynomial_algebra.PolynomialAlgebraConstMul.At(K, variables, c, product),
						comm_ring.MulIn.Read(polynomials).AsFact().At(F, u),
						comm_monoid.LeftCommOn.Read(comm_ring.MulMonoidOn.Read(polynomials)).AsFact().At(F, constant, u)))
			}))
		times := a.Have(
			"multiplication by F is a linear map from the forms of degree e into X",
			"module_homomorphism(«hilbertCoefficients», "+
				"    «formSpace»(e), "+
				"    restrict_module(«formSpace»(d), X), "+
				"    λP:((num → num) → A). polynomial_algebra_mul(«hilbertCoefficients», F, P))",
			Simp(Fwd(module_homomorphism.ModuleHomomorphismDef)),
			By(moduleE, moduleX, holdsMultiples, additive, scaled))
		composite := a.Simplified(
			a.Have(
				"and so is multiplication by F followed by the projection of X modulo the ideal",
				"module_homomorphism(«hilbertCoefficients», "+
					"    «formSpace»(e), "+
					"    «quotient», "+
					"    coset_map(fun_add, «forms»(d) ∩ «ideal») ∘ "+
					"    (λP:((num → num) → A). polynomial_algebra_mul(«hilbertCoefficients», F, P)))",
				By(
					times,
					moduleX,
					idealInX,
					module_homomorphism.ProjectionHom.At(K, spaceX, idealD),
					module_homomorphism.HomCompose)),
			Fwd(functions.ComposeApply))
		projectionKernel := a.Have(
			"the projection of X kills exactly the forms of degree d in the ideal",
			"group_kernel(«forms»(d) ∩ «ideal», X, coset_map(fun_add, «forms»(d) ∩ «ideal»)) = "+
				"«forms»(d) ∩ «ideal»",
			By(moduleX, idealInX, module_homomorphism.ProjectionKernel.At(K, spaceX, idealD)))
		cancel := a.Have(
			"F is no zero divisor modulo the prime ideal",
			Statement{
				Binders:    "∀u:((num → num) → A).",
				Hypotheses: []string{"u ∈ «forms»(e)"},
				Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», F, u) ∈ «ideal» ⇔ u ∈ «ideal»",
			},
			Derive(func(b *Argument) {
				u := b.FixAs[Fun[Fun[Nat, Nat], A]]("u")
				given := b.Assume()
				polynomial := b.Have(
					"u is a polynomial over k",
					"u ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					By(given, homogeneous_polynomial.FormPolynomial.At(K, n, e, u)))
				b.Show(
					"a product in the prime ideal has a factor in it, and the ideal absorbs products",
					By(
						polynomial,
						polynomialF,
						outside,
						ring_ideal.PrimeIdealPrime.Read(prime).AsFact().At(F, u),
						ring_ideal.IdealMul.Read(idealJ).AsFact().At(F, u)))
			}))
		killed := a.Have(
			"so F·u is zero modulo the ideal exactly when u is in the ideal",
			Statement{
				Binders:    "∀u:((num → num) → A).",
				Hypotheses: []string{"u ∈ «forms»(e)"},
				Conclusion: "coset_map(fun_add, " +
					"    «forms»(d) ∩ «ideal», " +
					"    polynomial_algebra_mul(«hilbertCoefficients», F, u)) = " +
					"«forms»(d) ∩ «ideal» ⇔ " +
					"u ∈ «ideal»",
			},
			Derive(func(b *Argument) {
				u := b.FixAs[Fun[Fun[Nat, Nat], A]]("u")
				given := b.Assume()
				product := b.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_mul(«hilbertCoefficients», F, u)")
				b.Show(
					"F·u lies in X, which lies in the forms of degree d, and the "+
						"projection's kernel is the forms of degree d in the ideal",
					By(
						given,
						cancel.At(u),
						holdsMultiples.At(u),
						projectionKernel,
						subspace,
						submodule.SubmoduleSubset.At(K, spaceD, X),
						set_basic.SubsetDef,
						group_homomorphism.InKernel.At(
							idealD,
							X,
							b.TermAs[Fun[Fun[Fun[Nat, Nat], A], Set[Fun[Fun[Nat, Nat], A]]]](
								"coset_map(fun_add, «forms»(d) ∩ «ideal»)"),
							product),
						set_basic.InInter.At(formsD, b.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«ideal»"), product)))
			}))
		kernel := a.Have(
			"the kernel of multiplication by F modulo the ideal is the forms of degree e in the ideal",
			"group_kernel(«forms»(d) ∩ «ideal», «forms»(e), «multiply») = «forms»(e) ∩ «ideal»",
			Derive(func(b *Argument) {
				members := b.Have(
					"a form of degree e is in the kernel exactly when it is in the ideal",
					"∀u:((num → num) → A). "+
						"    u ∈ group_kernel(«forms»(d) ∩ «ideal», «forms»(e), «multiply») ⇔ u ∈ «forms»(e) ∩ «ideal»",
					Derive(func(c *Argument) {
						u := c.FixAs[Fun[Fun[Nat, Nat], A]]("u")
						c.Show(
							"by the kernel's membership",
							By(
								killed.At(u),
								group_homomorphism.InKernel.At(
									idealD, c.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«forms»(e)"), multiply, u),
								set_basic.InInter.At(
									c.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«forms»(e)"),
									c.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«ideal»"),
									u)))
					}))
				b.Show(
					"so the two sets agree",
					By(members, set_basic.Extension))
			}))
		quotientModule := a.Have(
			"X modulo the ideal is a vector space",
			"module_on(«hilbertCoefficients», «quotient»)",
			By(module_homomorphism.HomTarget.Read(composite)))
		rank := a.Have(
			"by rank and nullity, the image of the forms of degree e has dimension "+
				"that of the forms of degree e less the forms of degree e in the ideal",
			"module_dim(«hilbertCoefficients», restrict_module(«formSpace»(e), «forms»(e) ∩ «ideal»)) + "+
				"module_dim(«hilbertCoefficients», restrict_module(«quotient», image(«multiply», «forms»(e)))) = "+
				"module_dim(«hilbertCoefficients», «formSpace»(e))",
			kernel.RwRev(),
			By(
				moduleE,
				kField,
				quotientModule,
				composite,
				finiteE,
				module_dimension.RankNullity.At(K, spaceE, inv, quotient, multiply)))
		hilbertE := a.Have(
			"which is the Hilbert function at e",
			"module_dim(«hilbertCoefficients», restrict_module(«formSpace»(e), «forms»(e) ∩ «ideal»)) + "+
				"projective_hilbert_function(field_ring(M), k, n, E, e) = "+
				"module_dim(«hilbertCoefficients», «formSpace»(e))",
			By(subK, equations, dimensionE[1], HilbertFunctionCodimension.Read(M).At(k, n, e, E)))
		image := a.Have(
			"the image is a subspace of X modulo the ideal, of dimension at most its dimension",
			"module_dim(«hilbertCoefficients», restrict_module(«quotient», image(«multiply», «forms»(e)))) ≤ "+
				"module_dim(«hilbertCoefficients», «quotient»)",
			By(
				quotientModule,
				kField,
				chain[1],
				module_homomorphism.ImageSubmodule.Read(composite),
				module_dimension.SubmoduleDim.At(
					K, quotient, inv, a.TermAs[Set[Set[Fun[Fun[Nat, Nat], A]]]]("image(«multiply», «forms»(e))"))))
		a.Show(
			"so the codimension of X and h(e) add to at most h(d)",
			ByArith(hilbertD, rank, hilbertE, image))
	}),
})}

// HilbertFunctionBelowCodimension — a subspace X of the forms of degree d
// inside the ideal E generates bounds the Hilbert function at d by its
// codimension. The forms of degree d modulo X split into the forms modulo
// the ideal and the ideal's forms modulo X (QuotientChainDim), and the first
// is the Hilbert function at d.
var HilbertFunctionBelowCodimension = hilbertFunctionBelowCodimensionThm{family.Add(registry.ProofEntry{
	Name: "HilbertFunctionBelowCodimension",
	Key:  "prop_1ddc8c17f009ff70",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n d:num. ∀E X:set((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"E ⊆ «polynomials».carrier",
			"submodule(«hilbertCoefficients», «formSpace»(d), X)",
			"X ⊆ «ideal»",
		},
		Conclusion: "projective_hilbert_function(field_ring(M), k, n, E, d) ≤ " +
			"module_dim(«hilbertCoefficients», quotient_module(«formSpace»(d), X))",
		Abbrev: Abbrev{
			{Name: "ideal", Text: "ideal_span(«polynomials», E)"},
			{Name: "forms", Text: "λd:num. " +
				"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"},
			{Name: "formSpace", Text: "λd:num. " +
				"    mk_module(fun_add, " +
				"        fun_zero, " +
				"        fun_neg, " +
				"        λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"        «forms»(d))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, d *Expr[Nat],
		E, X *Expr[Set[Fun[Fun[Nat, Nat], A]]],
		subK, polynomialE, subspace, insideIdeal Fact,
	) {
		K := a.TermAs[RingOps[A]]("«hilbertCoefficients»")
		inv := a.TermAs[Fun[A, A]]("M.inv")
		spaceD := a.TermAs[module_record.ModuleOps[A, Fun[Fun[Nat, Nat], A]]]("«formSpace»(d)")
		formsD := a.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«forms»(d)")
		idealD := a.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«forms»(d) ∩ «ideal»")
		scalars := a.Have(
			"k is a commutative ring",
			"comm_ring_on(«hilbertCoefficients»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k)))
		polynomials := a.Have(
			"and so are the polynomials over k",
			"comm_ring_on(«polynomials»)",
			By(scalars, polynomial_algebra.PolynomialAlgebraCommRingOn))
		kField := a.Have(
			"k is a field",
			"ring_subfield(«hilbertCoefficients», M.inv, k)",
			By(subK, field.SubfieldRingSubfield.Read(M).At(k, k)))
		spaceFacts := a.Conjuncts(
			GroupPremises(subK, FormsSubspace.Read(M).At(k, n, d)),
			"the forms of degree d are a vector space",
			"meeting every ideal in a subspace")
		moduleD := spaceFacts[0]
		subD := a.Have(
			"the forms of degree d in the ideal are a subspace",
			"submodule(«hilbertCoefficients», «formSpace»(d), «forms»(d) ∩ «ideal»)",
			By(polynomialE, ring_ideal.SpanIdeal.Read(polynomials), spaceFacts[1]))
		dimension := a.Conjuncts(
			GroupPremises(subK, FormsDimension.Read(M).At(k, n, d)),
			"the forms of degree d are finite-dimensional",
			"of dimension binomial(d + n, n)")
		whole := a.Have(
			"the forms of degree d are the whole space",
			"restrict_module(«formSpace»(d), «forms»(d)) = «formSpace»(d)",
			Simp(Fwd(module_record.RestrictModuleDef)),
			Refl())
		withinIdeal := a.Have(
			"X lies among the forms of degree d in the ideal",
			"X ⊆ «forms»(d) ∩ «ideal»",
			BySets(insideIdeal, subspace, submodule.SubmoduleSubset.At(K, spaceD, X)))
		finiteModX := a.Have(
			"the forms of degree d modulo X are finite-dimensional",
			"finite_dimensional(«hilbertCoefficients», "+
				"    quotient_module(restrict_module(«formSpace»(d), «forms»(d)), X))",
			whole.Rw(),
			By(
				moduleD,
				kField,
				subspace,
				dimension[0],
				module_dimension.DimFiniteIffSubAndQuotient.At(K, spaceD, inv, X)))
		chain := a.Conjuncts(
			a.Simplified(
				a.Have(
					"the forms of degree d modulo X split into the forms "+
						"modulo the ideal and the ideal's forms modulo X",
					"finite_dimensional(«hilbertCoefficients», "+
						"    quotient_module(restrict_module(«formSpace»(d), «forms»(d)), «forms»(d) ∩ «ideal»)) ∧ "+
						"finite_dimensional(«hilbertCoefficients», "+
						"    quotient_module(restrict_module(«formSpace»(d), «forms»(d) ∩ «ideal»), X)) ∧ "+
						"module_dim(«hilbertCoefficients», "+
						"    quotient_module(restrict_module(«formSpace»(d), «forms»(d)), X)) = "+
						"module_dim(«hilbertCoefficients», "+
						"    quotient_module(restrict_module(«formSpace»(d), «forms»(d)), «forms»(d) ∩ «ideal»)) + "+
						"module_dim(«hilbertCoefficients», "+
						"    quotient_module(restrict_module(«formSpace»(d), «forms»(d) ∩ «ideal»), X))",
					By(
						moduleD,
						kField,
						subD,
						subspace,
						withinIdeal,
						finiteModX,
						submodule.CarrierSubmodule.At(K, spaceD),
						set_order.InterSubset.At(formsD, a.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«ideal»")),
						module_dimension.QuotientChainDim.At(K, spaceD, inv, formsD, idealD, X))),
				Fwd(whole)),
			"the forms modulo the ideal are finite-dimensional",
			"so is the ideal's part modulo X",
			"and the dimensions add")
		hilbert := a.Have(
			"the Hilbert function at d is the dimension of the forms modulo the ideal",
			"projective_hilbert_function(field_ring(M), k, n, E, d) = "+
				"module_dim(«hilbertCoefficients», quotient_module(«formSpace»(d), «forms»(d) ∩ «ideal»))",
			By(ProjectiveHilbertFunctionDef))
		a.Show(
			"so it is at most the codimension of X",
			ByArith(hilbert, chain[2]))
	}),
})}
