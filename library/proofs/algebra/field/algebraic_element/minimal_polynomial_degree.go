// minimal_polynomial_degree.go — the minimal polynomial recognized by its
// degree: a monic polynomial over K of degree [K(a) : K] vanishing at a is the
// minimal polynomial of a; the degree bounded by a space holding the powers of
// a; a point of K recognized by its linear minimal polynomial; and the
// degree of a minimal polynomial dividing that of the extension.

package algebraic_element

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ShortPolynomialsAgree — two polynomials over K whose difference vanishes from
// the degree of the minimal polynomial of a on, with one value at a, are equal:
// their difference is a polynomial over K below that degree vanishing at a, and
// no nonzero polynomial over K of smaller degree than the minimal polynomial
// does.
var ShortPolynomialsAgree = shortPolynomialsAgreeThm{family.Add(registry.ProofEntry{
	Name: "ShortPolynomialsAgree",
	Key:  "prop_38905109a560e8fd",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A. ∀p q:(num → A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"polynomial_over(K, p)",
			"polynomial_over(K, q)",
			"vec⟨polynomial_degree(minimal_polynomial(L, K, a))⟩(vec_sub(p, q))",
			"polynomial_eval(p, a) = polynomial_eval(q, a)",
		},
		Conclusion: "p = q",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		K *Expr[Set[A]],
		a *Expr[A],
		p, q *Arrow[Nat, A],
		subK, aIn, pOver, qOver, short, sameValue Fact,
	) {
		ring := field.RingOn.Read(L)
		am := arg.MemberOf[on.L](a, aIn)
		difference := arg.TermAs[Fun[Nat, A]]("vec_sub(p, q)")
		inField := arg.Have(
			"both are polynomials over L, their coefficients in L",
			"polynomial_over(L.carrier, p) ∧ "+
				"polynomial_over(L.carrier, q) ∧ "+
				"(∀i:num. p(i) ∈ L.carrier ∧ q(i) ∈ L.carrier)",
			By(
				pOver,
				qOver,
				subK,
				field.SubfieldSubset,
				polynomial.PolynomialOverMono,
				polynomial.PolynomialOverDef))
		coefficients := arg.Have(
			"the coefficients of p − q lie in K",
			"∀i:num. p(i) - q(i) ∈ K",
			By(pOver, qOver, subK, polynomial.PolynomialOverDef, field.SubfieldSub.Read(L)))
		over := arg.Have(
			"so p − q is a polynomial over K",
			"polynomial_over(K, vec_sub(p, q))",
			By(short, coefficients, polynomial.PolynomialOverDef, vec_space.VecSubDef))
		vanishes := arg.Have(
			"p − q vanishes at a, p and q having one value there",
			"polynomial_eval(vec_sub(p, q), a) = L.zero",
			GroupPremises(inField, polynomial_evaluation.EvalSub.Read(ring).At(p, q, am)).Rw(),
			sameValue.Rw(),
			ByArith(L, polynomial_evaluation.EvalIn.Read(ring).At(q, am), inField))
		zero := arg.Have(
			"so p − q is zero: a nonzero polynomial over K vanishing "+
				"at a has at least the degree of the minimal polynomial",
			"vec_sub(p, q) = vec_zero",
			By(
				over,
				vanishes,
				short,
				subK,
				MinimalPolynomialLeast.Read(L).At(K, am, difference),
				polynomial.DegreeBelow.At(arg.TermAs[A]("L.zero"), proof.InhabitFrom(difference, short)),
				nat_order.NotLessEq))
		differences := arg.Have(
			"every coefficient of p − q is zero",
			"∀i:num. p(i) - q(i) = L.zero",
			By(zero, vec_space.VecSubDef, vec_space.VecZeroDef))
		equal := arg.Have(
			"so p and q have the same coefficients",
			"∀i:num. p(i) = q(i)",
			arg.ForEach(func(i *Expr[Nat]) Action {
				return ByArith(L, differences.At(i), inField)
			}))
		arg.Show(
			"p = q",
			By(Normalized, equal))
	}),
})}

// MinimalPolynomialOfDegree — a monic polynomial p over K that vanishes at a
// and has degree [K(a) : K] is the minimal polynomial of a. The minimal
// polynomial has the degree [K(a) : K] too (AdjoinDegree), so the two are
// monic of one degree and their difference vanishes from it on; both vanish at
// a, so they are equal (ShortPolynomialsAgree).
var MinimalPolynomialOfDegree = minimalPolynomialOfDegreeThm{family.Add(registry.ProofEntry{
	Name: "MinimalPolynomialOfDegree",
	Key:  "prop_2430aaaf2a7814dd",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A. ∀p:(num → A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"polynomial_over(K, p)",
			"polynomial_monic(p)",
			"polynomial_eval(p, a) = L.zero",
			"polynomial_degree(p) = extension_degree(L, K, field_adjoin(L, K, {a}))",
		},
		Conclusion: "p = minimal_polynomial(L, K, a)",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		K *Expr[Set[A]],
		a *Expr[A],
		p *Arrow[Nat, A],
		subK, aIn, pOver, monic, root, degree Fact,
	) {
		am := arg.MemberOf[on.L](a, aIn)
		minimal := arg.TermAs[Fun[Nat, A]]("minimal_polynomial(L, K, a)")
		nonzero := arg.Have(
			"p is not zero, its top coefficient being one",
			"p ≠ vec_zero",
			By(monic, polynomial.PolynomialMonicDef, field.OneNotZeroOn.Read(L), vec_space.VecZeroDef))
		algebraic := arg.Have(
			"so a is algebraic over K",
			"algebraic_over(L, K, a)",
			By(nonzero, pOver, root, AlgebraicOverDef))
		spec := arg.Have(
			"the minimal polynomial is monic over K, vanishes at a, and has the degree [K(a) : K] of p",
			"polynomial_over(K, minimal_polynomial(L, K, a)) ∧ "+
				"polynomial_monic(minimal_polynomial(L, K, a)) ∧ "+
				"polynomial_eval(minimal_polynomial(L, K, a), a) = L.zero ∧ "+
				"polynomial_degree(p) = polynomial_degree(minimal_polynomial(L, K, a))",
			By(
				algebraic,
				subK,
				aIn,
				degree,
				MinimalPolynomialSpec.Read(L).At(K, am),
				AdjoinDegree.Read(L).At(K, am)))
		tops := arg.Have(
			"both vanish past their common degree, and have top coefficient one",
			"vec⟨suc(polynomial_degree(p))⟩(p) ∧ "+
				"vec⟨suc(polynomial_degree(p))⟩(minimal_polynomial(L, K, a)) ∧ "+
				"p(polynomial_degree(p)) = L.one ∧ "+
				"minimal_polynomial(L, K, a, polynomial_degree(p)) = L.one",
			By(spec, pOver, monic, polynomial.DegreeVec, polynomial.PolynomialMonicDef))
		inField := arg.Have(
			"both are polynomials over L, their coefficients in L",
			"polynomial_over(L.carrier, p) ∧ "+
				"polynomial_over(L.carrier, minimal_polynomial(L, K, a)) ∧ "+
				"(∀i:num. p(i) ∈ L.carrier ∧ minimal_polynomial(L, K, a, i) ∈ L.carrier)",
			By(
				spec,
				pOver,
				subK,
				field.SubfieldSubset,
				polynomial.PolynomialOverMono,
				polynomial.PolynomialOverDef))
		agree := arg.Have(
			"from that degree on their coefficients agree",
			"∀i:num. polynomial_degree(p) ≤ i ⇒ p(i) = minimal_polynomial(L, K, a, i)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				from := b.Assume()
				b.Cases(b.TermAs[Bool]("i = polynomial_degree(p)"))
				b.When(
					"at the degree both are one",
					func(c *Argument, at Fact) {
						c.Show(
							"the top coefficients",
							By(Normalized, at, tops))
					})
				b.Otherwise(
					"past it both vanish",
					func(c *Argument, other Fact) {
						beyond := c.Have(
							"i lies past the degree",
							"suc(polynomial_degree(p)) ≤ i",
							ByArith(from, other))
						c.Show(
							"both vanish past the degree",
							By(beyond, tops, vec_space.VecDef))
					})
			}))
		short := arg.Have(
			"so p − minpoly vanishes from that degree on",
			"vec⟨polynomial_degree(p)⟩(vec_sub(p, minimal_polynomial(L, K, a)))",
			Simp(Fwd(vec_space.VecDef), Fwd(vec_space.VecSubDef)),
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				from := b.Assume()
				b.Show(
					"two equal coefficients differ by zero",
					ByArith(L, from, agree.At(i), inField))
			}))
		arg.Show(
			"so p is the minimal polynomial: p − minpoly vanishes "+
				"from their common degree on, and both vanish at a",
			By(subK, pOver, spec, short, root, ShortPolynomialsAgree.Read(L).At(K, am, p, minimal)))
	}),
})}

// BoundedPowersDegree — an element whose powers 1, a, …, a^D lie in a
// subspace V of L of dimension at most D over K is algebraic over K, of
// degree at most D: pairwise distinct, a⁰, …, a^D would be D + 1 vectors of
// V, so they cannot be independent. The powers of a transcendental a are
// distinct and independent, so a is algebraic; and were the degree m of its
// minimal polynomial above D, a⁰, …, a^D would be among the basis
// a⁰, …, a^(m−1) of K(a), distinct and independent again. So
// [K(a) : K] = m ≤ D.
var BoundedPowersDegree = boundedPowersDegreeThm{family.Add(registry.ProofEntry{
	Name: "BoundedPowersDegree",
	Key:  "prop_f03f97e62c89d34e",
	Reading: "D = 0 is vacuous: a space of dimension 0 is {zero}, and a⁰ = one cannot " +
		"lie in it, a field's one not being zero. An element of K is the case of degree one. " +
		"V is a subspace of L, not of K(a), which it need not contain: the powers, " +
		"independent over K in L, are counted inside V, where at most dim V of them can be " +
		"independent. a ∈ L.carrier is load-bearing in this encoding: no subfield of L holds " +
		"a point outside the carrier, so its K(a) is the empty intersection, the whole type, " +
		"and the product of L, unconstrained off the carrier, says nothing about its powers.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K V:set(A). ∀D:num. ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"submodule(«scalars», regular_module(field_ring(L)), V)",
			"finite_dimensional(«scalars», restrict_module(regular_module(field_ring(L)), V))",
			"module_dim(«scalars», restrict_module(regular_module(field_ring(L)), V)) ≤ D",
			"∀t:num. t ≤ D ⇒ monoid_pow(L.mul, L.one, a, t) ∈ V",
		},
		Conclusion: "algebraic_over(L, K, a) ∧ extension_degree(L, K, field_adjoin(L, K, {a})) ≤ D",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		K, V *Expr[Set[A]],
		D *Expr[Nat],
		a *Expr[A],
		subK, aIn, subV, finiteV, dimV, powersInV Fact,
	) {
		am := arg.MemberOf[on.L](a, aIn)
		scalars := arg.TermAs[module_record.RingOps[A]]("«scalars»")
		vectors := arg.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		powerMap := arg.TermAs[Fun[Nat, A]]("«powerMap»")
		upToD := arg.TermAs[Set[Nat]]("{t:num | t ≤ D}")
		low := arg.TermAs[Set[A]]("image(«powerMap», {t:num | t ≤ D})")
		size := arg.TermAs[Nat]("D + 1")

		// a⁰, …, a^D in V: pairwise distinct, they cannot be independent.
		space := arg.Conjuncts(
			arg.Have(
				"V is a vector space over K inside L",
				"module_on(«scalars», restrict_module(regular_module(field_ring(L)), V)) ∧ V ⊆ L.carrier",
				By(
					subK,
					subV,
					field_extension.SubfieldScalars.Read(L).At(K),
					submodule.SubmoduleModuleOn.At(scalars, vectors, V),
					submodule.SubmoduleSubset.At(scalars, vectors, V))),
			"V is a vector space over K",
			"lying in L")
		dependent := arg.Have(
			"so a⁰, …, a^D, if pairwise distinct, are dependent over K: "+
				"V, of dimension at most D, holds no D + 1 independent vectors",
			Statement{
				Hypotheses: []string{"injective_on({t:num | t ≤ D}, «powerMap»)"},
				Conclusion: "¬module_independent(«scalars», " +
					"    regular_module(field_ring(L)), " +
					"    image(«powerMap», {t:num | t ≤ D}))",
			},
			Derive(func(b *Argument) {
				distinct := b.Assume()
				independent := b.SupposeNot()
				count := b.Have(
					"being pairwise distinct, they are D + 1 in number",
					"has_size(image(«powerMap», {t:num | t ≤ D}), D + 1)",
					By(distinct, cardinality.HasSizeImageInj.At(powerMap, upToD, size), num_segment.HasSizeBelow.At(D)))
				withinV := b.Have(
					"independent in L and lying in V, they are independent inside V",
					"module_independent(«scalars», "+
						"    restrict_module(regular_module(field_ring(L)), V), "+
						"    image(«powerMap», {t:num | t ≤ D}))",
					By(
						independent,
						powersInV,
						set_image.ImageSubsetIff.At(powerMap, upToD, V),
						space[1],
						linear_independence.IndependentRestrict.At(scalars, vectors, V, low)))
				bound := b.Have(
					"so they number at most dim V",
					"card(image(«powerMap», {t:num | t ≤ D})) ≤ "+
						"module_dim(«scalars», restrict_module(regular_module(field_ring(L)), V))",
					By(
						subK,
						finiteV,
						withinV,
						field.SubfieldRingSubfield.Read(L).At(K, K),
						module_dimension.IndependentBound.Read(space[0]).At(b.TermAs[Fun[A, A]]("L.inv"), low)))
				b.Show(
					"yet dim V ≤ D < D + 1",
					ByArith(count, bound, dimV, cardinality.HasSizeDef.At(low, size)))
			}))

		// A transcendental a has distinct, independent powers.
		algebraic := arg.Have(
			"a is algebraic over K",
			"algebraic_over(L, K, a)",
			Derive(func(b *Argument) {
				transcendental := b.SupposeNot()
				free := b.Conjuncts(
					GroupPremises(subK, transcendental, TranscendentalPowersIndependent.Read(L).At(K, am)),
					"were a transcendental, its powers would be pairwise distinct",
					"and independent over K")
				among := b.Have(
					"a⁰, …, a^D are powers of a",
					"image(«powerMap», {t:num | t ≤ D}) ⊆ monoid_powers(L.mul, L.one, a)",
					BySets(comm_monoid.MonoidPowersDef.At(b.TermAs[Op[A]]("L.mul"), b.TermAs[A]("L.one"), a)))
				b.Show(
					"so a⁰, …, a^D would be pairwise distinct and independent, which they are not",
					By(
						dependent,
						free[0],
						functions.InjectiveOnDef.At(upToD, powerMap),
						among,
						free[1],
						linear_independence.IndependentSubset.At(
							scalars, vectors, b.TermAs[Set[A]]("monoid_powers(L.mul, L.one, a)"), low)))
			}))

		// The powers of a below its degree m are a basis of K(a), so distinct and independent.
		degree := arg.TermAs[Nat]("polynomial_degree(minimal_polynomial(L, K, a))")
		below := arg.TermAs[Set[Nat]]("{i:num | i < polynomial_degree(minimal_polynomial(L, K, a))}")
		powersBelow := arg.TermAs[Set[A]]("«powersBelowDegree»")
		adjoined := arg.TermAs[Set[A]]("field_adjoin(L, K, {a})")
		basis := arg.Conjuncts(
			GroupPremises(subK, algebraic, AdjoinPowerBasis.Read(L).At(K, am)),
			"the powers of a below the degree m of its minimal polynomial are a basis of K(a)",
			"and there are m of them")
		independentBelow := arg.Have(
			"so they are independent over K in L, which holds K(a)",
			"module_independent(«scalars», regular_module(field_ring(L)), «powersBelowDegree»)",
			By(
				subK,
				basis[0],
				AdjoinElementSubfield.Read(L).At(K, am),
				field.SubfieldSubset.At(arg.TermAs[FieldOps[A]]("L"), adjoined),
				linear_independence.ModuleBasisDef.At(
					scalars, arg.TermAs[module_record.ModuleOps[A, A]]("«adjoinVectors»"), powersBelow),
				linear_independence.IndependentRestrict.At(scalars, vectors, adjoined, powersBelow)))
		imageBelow := arg.Have(
			"they are the values of i ↦ aⁱ at the exponents i < m",
			"image(«powerMap», {i:num | i < polynomial_degree(minimal_polynomial(L, K, a))}) = "+
				"«powersBelowDegree»",
			Cite(set_image.SimpleImageGen))
		counted := arg.Have(
			"there are as many of them as exponents below m",
			"finite({i:num | i < polynomial_degree(minimal_polynomial(L, K, a))}) ∧ "+
				"card({i:num | i < polynomial_degree(minimal_polynomial(L, K, a))}) = card(«powersBelowDegree»)",
			By(
				basis[1],
				num_segment.HasSizeBelowStrict.At(degree),
				cardinality.HasSizeDef.At(powersBelow, degree),
				cardinality.HasSizeDef.At(below, degree)))
		distinctBelow := arg.Have(
			"so i ↦ aⁱ is one-to-one below m",
			"injective_on({i:num | i < polynomial_degree(minimal_polynomial(L, K, a))}, «powerMap»)",
			By(imageBelow, counted, cardinality.ImageImpInjectiveGen.At(below, powersBelow, powerMap)))
		bounded := arg.Have(
			"m is at most D",
			"polynomial_degree(minimal_polynomial(L, K, a)) ≤ D",
			Derive(func(b *Argument) {
				above := b.SupposeNot()
				exponents := b.Have(
					"were m above D, every t ≤ D would lie below m",
					"{t:num | t ≤ D} ⊆ {i:num | i < polynomial_degree(minimal_polynomial(L, K, a))}",
					Simp(Fwd(set_basic.SubsetDef)),
					b.ForEach(func(t *Expr[Nat]) Action {
						return ByArith(above)
					}))
				among := b.Have(
					"so a⁰, …, a^D would be among a⁰, …, a^(m−1)",
					"image(«powerMap», {t:num | t ≤ D}) ⊆ «powersBelowDegree»",
					By(exponents, imageBelow, set_image.ImageSubset.At(powerMap, upToD, below)))
				b.Show(
					"and pairwise distinct and independent with them, which they are not",
					By(
						dependent,
						exponents,
						distinctBelow,
						functions.InjectiveOnSubset.At(powerMap, upToD, below),
						among,
						independentBelow,
						linear_independence.IndependentSubset.At(scalars, vectors, powersBelow, low)))
			}))
		arg.Show(
			"so a is algebraic over K, and [K(a) : K] = m ≤ D",
			By(subK, algebraic, bounded, AdjoinDegree.Read(L).At(K, am)))
	}),
})}

// MinimalPolynomialLinearIff — an algebraic a lies in K exactly when its
// minimal polynomial over K is linear: that degree is [K(a) : K], which is
// one exactly when K(a) is K, and K(a) is K exactly when a lies in K.
var MinimalPolynomialLinearIff = minimalPolynomialLinearIffThm{family.Add(registry.ProofEntry{
	Name: "MinimalPolynomialLinearIff",
	Key:  "prop_13766d4f2185382d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"algebraic_over(L, K, a)",
		},
		Conclusion: "a ∈ K ⇔ polynomial_degree(minimal_polynomial(L, K, a)) = 1",
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], a *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"a is algebraic over K")
			subK, aInL, algebraic := hyp[0], hyp[1], hyp[2]
			am := arg.MemberOf[on.L](a, aInL)
			adjoined := arg.Have(
				"K(a) is a subfield of L holding K and a",
				"subfield(L, field_adjoin(L, K, {a})) ∧ K ⊆ field_adjoin(L, K, {a}) ∧ a ∈ field_adjoin(L, K, {a})",
				By(subK, AdjoinElementSubfield.Read(L).At(K, am)))
			degree := arg.Have(
				"K(a) is finite over K, of degree the degree of the minimal polynomial",
				"finite_extension(L, K, field_adjoin(L, K, {a})) ∧ "+
					"extension_degree(L, K, field_adjoin(L, K, {a})) = polynomial_degree(minimal_polynomial(L, K, a))",
				By(subK, algebraic, AdjoinDegree.Read(L).At(K, am)))
			trivial := arg.Have(
				"so the minimal polynomial is linear exactly when K(a) is K",
				"polynomial_degree(minimal_polynomial(L, K, a)) = 1 ⇔ field_adjoin(L, K, {a}) = K",
				By(
					subK,
					adjoined,
					degree,
					field_extension.DegreeOneIff.Read(L).At(K, arg.TermAs[Set[A]]("field_adjoin(L, K, {a})"))))
			arg.Iff()
			arg.Forward(
				"a point of K adjoins nothing to K",
				func(b *Argument, inK Fact) {
					equal := b.Have(
						"K(a) lies in K, which it holds, so it is K",
						"field_adjoin(L, K, {a}) = K",
						BySets(subK, inK, adjoined, AdjoinElementBetween.Read(L).At(K, K, a)))
					b.Show(
						"so the minimal polynomial is linear",
						By(equal, trivial))
				})
			arg.Backward(
				"a linear minimal polynomial makes K(a) the field K, which holds a",
				func(b *Argument, linear Fact) {
					b.Show(
						"a lies in K(a), which is K",
						By(linear, trivial, adjoined))
				})
		}),
})}

// MinimalPolynomialDegreeDivides — the minimal polynomial of a point x of a
// finite extension E of K has degree dividing [E : K]: that degree is
// [K(x) : K], and the tower K ⊆ K(x) ⊆ E multiplies it by [E : K(x)].
var MinimalPolynomialDegreeDivides = minimalPolynomialDegreeDividesThm{family.Add(registry.ProofEntry{
	Name: "MinimalPolynomialDegreeDivides",
	Key:  "prop_7039378243766079",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K E:set(A). ∀x:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, E)",
			"K ⊆ E",
			"finite_extension(L, K, E)",
			"x ∈ E",
		},
		Conclusion: "polynomial_degree(minimal_polynomial(L, K, x)) ∣ extension_degree(L, K, E)",
	},
		func(arg *Argument, L field.FieldFact[on.L], K, E *Expr[Set[A]], x *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"so is E",
				"K lies in E",
				"E is finite over K",
				"x lies in E")
			subK, subE, contains, finite, xE := hyp[0], hyp[1], hyp[2], hyp[3], hyp[4]
			C := arg.TermAs[Set[A]]("field_adjoin(L, K, {x})")
			between := arg.Have(
				"K(x) lies between K and E",
				"subfield(L, field_adjoin(L, K, {x})) ∧ "+
					"K ⊆ field_adjoin(L, K, {x}) ∧ "+
					"x ∈ field_adjoin(L, K, {x}) ∧ "+
					"field_adjoin(L, K, {x}) ⊆ E",
				By(subK, subE, contains, xE, AdjoinElementBetween.Read(L).At(K, E, x)))
			xm := arg.MemberOf[on.L](x, arg.Have(
				"x lies in L",
				"x ∈ L.carrier",
				BySets(xE, subE, field.SubfieldSubset.At(arg.TermAs[FieldOps[A]]("L"), E))))
			algebraic := arg.Have(
				"x is algebraic over K, E being finite over K",
				"algebraic_over(L, K, x)",
				By(subK, subE, contains, finite, xE, FiniteExtensionAlgebraic.Read(L).At(K, E, x)))
			degree := arg.Have(
				"[K(x) : K] is the degree of the minimal polynomial",
				"extension_degree(L, K, field_adjoin(L, K, {x})) = polynomial_degree(minimal_polynomial(L, K, x))",
				By(subK, algebraic, AdjoinDegree.Read(L).At(K, xm)))
			tower := arg.Have(
				"the degrees multiply along K ⊆ K(x) ⊆ E",
				"extension_degree(L, K, E) = "+
					"extension_degree(L, K, field_adjoin(L, K, {x})) * extension_degree(L, field_adjoin(L, K, {x}), E)",
				By(
					subK,
					subE,
					between,
					finite,
					field_extension.TowerFinite.Read(L).At(K, C, E),
					field_extension.TowerLaw.Read(L).At(K, C, E)))
			arg.Show(
				"so the degree of the minimal polynomial divides [E : K]",
				By(
					degree,
					tower,
					nat_divides.DividesOwnMultiple.At(
						arg.TermAs[Nat]("polynomial_degree(minimal_polynomial(L, K, x))"),
						arg.TermAs[Nat]("extension_degree(L, field_adjoin(L, K, {x}), E)"))))
		}),
})}
