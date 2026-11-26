// separating.go — separating elements and separating parameters in characteristic p.

package separating_parameter

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/perfect_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/formal_series"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// TranscendentalOutsidePowerAdjoin — an element t transcendental over k does
// not lie in k(t ^ p), for p at least two. Inside, with s = t ^ p, it would be a
// quotient f(s) / h(s) of polynomials over k with h(s) nonzero. The
// polynomials F and H that substitute T ^ p for the variable of f and h take
// at t the values f(s) and h(s), so H·T and F take one value at t, and t being
// transcendental they are one polynomial. But p * j + 1 is no multiple of p,
// so F vanishes there, while the coefficient of H·T
// there is h(j). So h is zero, and so is h(s).
var TranscendentalOutsidePowerAdjoin = transcendentalOutsidePowerAdjoinThm{family.Add(registry.ProofEntry{
	Name: "TranscendentalOutsidePowerAdjoin",
	Key:  "prop_cd356e82c4901e21",
	Build: family.Sections(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀t:A. ∀p:num.",
		Hypotheses: []string{
			"2 ≤ p",
			"subfield(M, k)",
			"t ∈ M.carrier",
			"¬algebraic_over(M, k, t)",
		},
		Conclusion: "t ∉ field_adjoin(M, k, {monoid_pow(M.mul, M.one, t, p)})",
	}, func(ctx *Script, headline string) *GoalStackNode {
		// Substituting T ^ d keeps the coefficients in k: each is a coefficient
		// of c, or zero.
		substitutionOver := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀k:set(A). ∀c:(num → A). ∀d:num.",
			Hypotheses: []string{
				"0 < d",
				"subfield(M, k)",
				"polynomial_over(k, c)",
			},
			Conclusion: "polynomial_over(k, series_substitute(field_ring(M), c, d))",
		}, func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			c *Arrow[Nat, A],
			d *Expr[Nat],
			positive, subfieldK, over Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			zero, carrier := a.TermAs[A]("M.zero"), a.TermAs[Set[A]]("M.carrier")
			substituted := a.TermAs[Fun[Nat, A]]("series_substitute(field_ring(M), c, d)")
			overField := a.Have(
				"over the field M the substitution is a polynomial",
				"polynomial_over(M.carrier, series_substitute(field_ring(M), c, d))",
				By(
					positive,
					subfieldK,
					over,
					field.SubfieldSubset.At(m, k),
					polynomial.PolynomialOverMono.At(zero, k, carrier, c),
					formal_series.SeriesSubstitutePolynomial.Read(field.RingOn.Read(M)).At(c, d)))
			coefficients := a.Have(
				"its coefficients lie in k, being coefficients of c or zero",
				"∀i:num. series_substitute(field_ring(M), c, d, i) ∈ k",
				By(
					subfieldK,
					over,
					polynomial.PolynomialOverDef,
					field.SubfieldZero,
					formal_series.SeriesSubstituteDef))
			a.Show(
				"a finitely supported sequence with coefficients in k is a polynomial over k",
				By(
					coefficients,
					overField,
					polynomial.PolynomialFiniteSupport.At(zero, carrier, substituted),
					polynomial.PolynomialFiniteSupport.At(zero, k, substituted)))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			t *Expr[A],
			p *Expr[Nat],
			two, subfieldK, tInM, transcendental Fact,
		) {
			ring := field.RingOn.Read(M)
			multiplicative := comm_ring.MulMonoidOn.Read(ring)
			m := a.TermAs[FieldOps[A]]("M")
			zero := a.TermAs[A]("M.zero")
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			tMember := a.MemberOf[on.M](t, tInM)
			positive := a.Have(
				"so p is positive",
				"0 < p",
				ByArith(two))
			s, sDef := a.LetAs[A]("s", "monoid_pow(M.mul, M.one, t, p)")
			sMember := a.MemberOf[on.M](s, a.Have(
				"s lies in M",
				"s ∈ M.carrier",
				By(Normalized, sDef, comm_monoid.PowIn.Read(multiplicative).At(tMember, p))))
			inside := a.SupposeNot()
			fractions := a.Have(
				"k(s) is the fraction field of k[s], so t times a nonzero element of k[s] lies in k[s]",
				"∃u v:A. "+
					"    u ∈ polynomial_image(field_ring(M), k, s) ∧ "+
					"    v ∈ polynomial_image(field_ring(M), k, s) ∧ "+
					"    v ≠ M.zero ∧ "+
					"    t * v = u",
				By(
					inside,
					subfieldK,
					field.FractionFieldCarrierDef,
					integral_element.RationalFunctionsFractionField.Read(M).At(k, sMember)))
			f, h, quotient := a.Obtain2As[Fun[Nat, A], Fun[Nat, A]](
				"those are the values at s of polynomials over k",
				"∃f h:(num → A). "+
					"    polynomial_over(k, f) ∧ "+
					"    polynomial_over(k, h) ∧ "+
					"    polynomial_eval(h, s) ≠ M.zero ∧ "+
					"    t * polynomial_eval(h, s) = polynomial_eval(f, s)",
				BySets(fractions, algebraic_element.PolynomialImageDef.At(fieldRing, k, s)))
			parts := a.Conjuncts(
				quotient,
				"f is a polynomial over k",
				"so is h",
				"h(s) is not zero",
				"t times h(s) is f(s)")
			fOver, hOver, nonzero, cleared := parts[0], parts[1], parts[2], parts[3]
			F, FDef := a.LetAs[Fun[Nat, A]]("F", "series_substitute(field_ring(M), f, p)")
			H, HDef := a.LetAs[Fun[Nat, A]]("H", "series_substitute(field_ring(M), h, p)")
			substitutions := a.Have(
				"F and H are polynomials over k",
				"polynomial_over(k, F) ∧ polynomial_over(k, H)",
				By(
					Normalized,
					M,
					positive,
					subfieldK,
					fOver,
					hOver,
					FDef,
					HDef,
					Read(substitutionOver, M).At(k, f, p),
					Read(substitutionOver, M).At(k, h, p)))
			fieldK := a.Have(
				"k is a field in its own right",
				"field_on(restrict_field(M, k))",
				By(subfieldK, field.SubfieldFieldOn.Read(M).At(k)))
			ringK := field.RingOn.Read(fieldK)
			productOver := a.Have(
				"so H times the variable is a polynomial over k",
				"polynomial_over(k, polynomial_mul(H, basis_vector(1)))",
				By(substitutions, polynomial.PolynomialMulOver.Read(ringK), polynomial.BasisVectorOver.Read(ringK)))
			overField := a.Have(
				"f and h are polynomials over M as well",
				"polynomial_over(M.carrier, f) ∧ polynomial_over(M.carrier, h)",
				By(subfieldK, fOver, hOver, field.SubfieldSubset.At(m, k), polynomial.PolynomialOverMono))
			values := a.Have(
				"F and H take at t the values of f and h at s",
				"polynomial_eval(F, t) = polynomial_eval(f, s) ∧ polynomial_eval(H, t) = polynomial_eval(h, s)",
				By(
					Normalized,
					ring,
					positive,
					overField,
					tInM,
					sDef,
					FDef,
					HDef,
					formal_series.EvalSeriesSubstitute.Read(ring).At(f, p, tMember),
					formal_series.EvalSeriesSubstitute.Read(ring).At(h, p, tMember)))
			hOverField := a.Have(
				"H is a polynomial over M",
				"polynomial_over(M.carrier, H)",
				By(
					Normalized,
					positive,
					overField,
					HDef,
					formal_series.SeriesSubstitutePolynomial.Read(ring).At(h, p)))
			agreement := a.Have(
				"t * h(s) = f(s) says that H times the variable and F take one value at t",
				"polynomial_eval(polynomial_mul(H, basis_vector(1)), t) = polynomial_eval(F, t)",
				CalcEq(
					Leg(
						a.TermAs[A]("polynomial_eval(H, t) * t"),
						"evaluation multiplies, and the variable takes the value t",
						By(
							hOverField,
							polynomial_evaluation.EvalMul.Read(ring).AsFact().At(
								H, a.TermAs[Fun[Nat, A]]("basis_vector(1)"), t),
							polynomial.BasisVectorOver.Read(ring),
							polynomial_evaluation.EvalBasisVector.Read(ring).At(a.TermAs[Nat]("1"), tMember),
							comm_monoid.PowOneOn.Read(multiplicative))),
					Leg(
						a.TermAs[A]("t * polynomial_eval(h, s)"),
						"H takes the value h(s), and multiplication commutes",
						By(
							values,
							overField,
							tInM,
							polynomial_evaluation.EvalIn.Read(ring).At(h, sMember),
							comm_monoid.CommOn.Read(multiplicative).AsFact().At(t, a.TermAs[A]("polynomial_eval(h, s)")))),
					Leg(
						a.TermAs[A]("polynomial_eval(f, s)"),
						"t * h(s) is f(s)",
						By(cleared)),
					FinalLeg(
						"which F takes at t",
						By(values))))
			product := a.TermAs[Fun[Nat, A]]("polynomial_mul(H, basis_vector(1))")
			same := a.Have(
				"t being transcendental over k, the two are one polynomial",
				"polynomial_mul(H, basis_vector(1)) = F",
				By(
					subfieldK,
					transcendental,
					substitutions,
					productOver,
					agreement,
					algebraic_element.EvalInjectiveTranscendental.Read(M).At(k, tMember, product, F)))
			vanishing := a.Have(
				"so every coefficient of h vanishes",
				"∀j:num. h(j) = M.zero",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					multiple := b.TermAs[Nat]("p * j")
					one := b.TermAs[Nat]("1")
					shifted := b.TermAs[Nat]("p * j + 1")
					notMultiple := b.Have(
						"p, at least two, does not divide one more than a multiple of it",
						"¬∃m:num. p * m = p * j + 1",
						ByArith(
							two,
							nat_divides.DividesFactor.At(p, shifted),
							nat_divides.DividesAddCancel.At(p, multiple, one),
							nat_divides.DividesOwnMultiple.At(p, j),
							nat_divides.DividesOne.At(p)))
					shift := b.Have(
						"one step past p * j",
						"1 ≤ p * j + 1 ∧ p * j + 1 - 1 = p * j",
						ByArith())
					moved := b.Have(
						"multiplying by the variable carries the coefficient h(j) of H at p * j to p * j + 1",
						"polynomial_mul(H, basis_vector(1), p * j + 1) = h(j)",
						By(
							positive,
							shift,
							hOverField,
							HDef,
							polynomial.PolynomialOverDef,
							polynomial.PolynomialMulBasisVector.Read(ring).At(H, one, shifted),
							formal_series.SeriesSubstituteAtMultiple.At(fieldRing, h, p, j)))
					b.Show(
						"and F has no coefficient at p * j + 1",
						By(
							Normalized,
							same,
							moved,
							notMultiple,
							FDef,
							formal_series.SeriesSubstituteOffMultiples.At(fieldRing, f, p, shifted)))
				}))
			polynomialZero := a.Have(
				"so h is the zero polynomial",
				"h = vec_zero",
				By(Normalized, vanishing, vec_space.VecZeroDef.Inst[A]().At(zero)))
			a.Show(
				"whose value at s is zero, against the choice of h",
				By(Normalized, nonzero, polynomialZero, polynomial_evaluation.EvalVecZero.Read(ring).At(sMember)))
		})
	}),
})}

// PowerSubfieldIndexBound — a finite extension L of k(t), with k equal to its
// own p-th powers, has degree at most p over its p-th powers. Write F for k(t).
// F is generated over its p-th powers by t, a root of X^p − t^p, so it has
// degree at most p over them. The p-th power map keeps [L : F], so the towers
// through F and through the p-th powers of L give [F : F^p] [L : F] =
// [L : F] [L : L^p], and [L : F] is positive.
var PowerSubfieldIndexBound = powerSubfieldIndexBoundThm{family.Add(registry.ProofEntry{
	Name: "PowerSubfieldIndexBound",
	Key:  "prop_5c389eede52f2a4e",
	Build: family.Sections(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀p:num.",
		Hypotheses: []string{
			"ring_prime_characteristic(field_ring(M), p)",
			"subfield(M, k)",
			"subfield(M, L)",
			"«powers»(k) = k",
			"k ⊆ L",
			"t ∈ L",
			"finite_extension(M, field_adjoin(M, k, {t}), L)",
		},
		Conclusion: "finite_extension(M, «powers»(L), L) ∧ extension_degree(M, «powers»(L), L) ≤ p",
		Abbrev: Abbrev{
			{Name: "powers", Text: "image(frobenius_power(field_ring(M), p))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// An element whose p-th power c lies in K has degree at most p over K: it
		// is a root of the polynomial X^p − c, which is over K, is not zero and has
		// no coefficient past p.
		rootDegree := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀K:set(A). ∀t c:A. ∀p:num.",
			Hypotheses: []string{
				"subfield(M, K)",
				"t ∈ M.carrier",
				"c ∈ K",
				"monoid_pow(M.mul, M.one, t, p) = c",
				"0 < p",
			},
			Conclusion: "finite_extension(M, K, field_adjoin(M, K, {t})) ∧ " +
				"extension_degree(M, K, field_adjoin(M, K, {t})) ≤ p",
			Abbrev: Abbrev{
				{Name: "constant", Text: "c • basis_vector(0)"},
				{Name: "binomial", Text: "basis_vector(p) - «constant»"},
			},
		}, func(
			a *Argument,
			M field.FieldFact[on.M],
			K *Expr[Set[A]],
			t, c *Expr[A],
			p *Expr[Nat],
			subfieldK, tIn, cIn, power, positive Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			zero := a.TermAs[A]("M.zero")
			ring := field.RingOn.Read(M)
			monomial := a.TermAs[Fun[Nat, A]]("basis_vector(p)")
			constant := a.TermAs[Fun[Nat, A]]("«constant»")
			binomial := a.TermAs[Fun[Nat, A]]("«binomial»")
			cInM := a.Have(
				"K lies in M, so c does",
				"c ∈ M.carrier",
				BySets(subfieldK, cIn, field.SubfieldSubset.At(m, K)))
			tMember, cMember := a.MemberOf[on.M](t, tIn), a.MemberOf[on.M](c, cInM)
			restricted := a.Have(
				"K is a field under the operations of M",
				"field_on(restrict_field(M, K))",
				By(subfieldK, field.SubfieldFieldOn.Read(M).At(K)))
			scalars := field.RingOn.Read(restricted)
			over := a.Have(
				"X^p − c is a polynomial over K, those being a ring and a module over K",
				"polynomial_over(K, «binomial»)",
				BySets(
					cIn,
					polynomial.BasisVectorOver.Read(scalars),
					module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(scalars)),
					comm_ring.SubIn.Read(polynomial.PolynomialRingOn.Read(scalars))))
			leading := a.Have(
				"its coefficient at p is one, p not being 0",
				"«binomial»(p) = M.one",
				Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)),
				ByArith(M, positive, cInM))
			nonzero := a.Have(
				"so X^p − c is not zero",
				"¬(«binomial» = vec_zero)",
				By(field.OneNotZeroOn.Read(M), leading, vec_space.VecZeroDef))
			bounded := a.Have(
				"past p its coefficients vanish",
				"vec⟨suc(p)⟩(«binomial»)",
				Unfold(vec_space.VecDef),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					past := b.Assume()
					b.Show(
						"an index past p is neither p nor 0",
						Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)),
						ByArith(M, positive, past, cInM))
				}))
			constantOver := a.Have(
				"the constant c is a polynomial over M",
				"polynomial_over(M.carrier, «constant»)",
				BySets(
					cInM,
					polynomial.BasisVectorOver.Read(ring),
					module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring))))
			root := a.Have(
				"t is a root of X^p − c, its value being t ^ p − c",
				"polynomial_eval(«binomial», t) = M.zero",
				ByArith(
					M,
					power,
					tIn,
					cInM,
					constantOver,
					polynomial.BasisVectorOver.Read(ring).At(p),
					polynomial_evaluation.EvalSub.Read(ring).At(monomial, constant, tMember),
					polynomial_evaluation.EvalBasisVector.Read(ring).At(p, tMember),
					polynomial_evaluation.EvalConstant.Read(ring).At(cMember, tMember)))
			algebraic := a.Have(
				"so t is algebraic over K",
				"algebraic_over(M, K, t)",
				Simp(Fwd(algebraic_element.AlgebraicOverDef)),
				Derive(func(b *Argument) {
					b.Take(binomial)
					b.Show(
						"X^p − c is a nonzero polynomial over K vanishing at t",
						By(over, nonzero, root))
				}))
			a.Show(
				"the minimal polynomial of t is no longer than X^p − c, of degree at most p",
				ByArith(
					subfieldK,
					tIn,
					algebraic,
					over,
					nonzero,
					root,
					bounded,
					algebraic_element.AdjoinDegree.Read(M).At(K, tMember),
					algebraic_element.MinimalPolynomialLeast.Read(M).At(K, tMember, binomial),
					polynomial.DegreeLeast.At(zero, binomial, p)))
		})

		// F = k(t) has degree at most p over its p-th powers. They hold k, which
		// is its own p-th powers, so with t they generate F; and t ^ p is one of
		// them.
		overPowers := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀k F:set(A). ∀t:A. ∀p:num.",
			Hypotheses: []string{
				"ring_prime_characteristic(field_ring(M), p)",
				"subfield(M, k)",
				"«powers»(k) = k",
				"t ∈ M.carrier",
				"F = field_adjoin(M, k, {t})",
			},
			Conclusion: "subfield(M, «powers»(F)) ∧ " +
				"«powers»(F) ⊆ F ∧ " +
				"finite_extension(M, «powers»(F), F) ∧ " +
				"extension_degree(M, «powers»(F), F) ≤ p",
		}, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, F *Expr[Set[A]],
			t *Expr[A],
			p *Expr[Nat],
			characteristic, subfieldK, fixed, tIn, generated Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			power := a.TermAs[Fun[A, A]]("frobenius_power(field_ring(M), p)")
			powersOfF := a.TermAs[Set[A]]("«powers»(F)")
			singleton := a.TermAs[Set[A]]("{t}")
			tMember := a.MemberOf[on.M](t, tIn)
			prime := a.Unfolded(characteristic, finite_field.PrimeCharacteristicDef)
			positive := a.Have(
				"a prime is positive",
				"0 < p",
				ByArith(prime, nat_prime.PrimeAtLeastTwo.At(p)))
			adjoined := a.Have(
				"F is a subfield over k holding t",
				"subfield(M, F) ∧ k ⊆ F ∧ t ∈ F",
				By(
					Normalized,
					generated,
					subfieldK,
					tIn,
					algebraic_element.AdjoinElementSubfield.Read(M).At(k, tMember)))
			powersField := a.Have(
				"the p-th powers of F are a subfield",
				"subfield(M, «powers»(F))",
				By(
					characteristic,
					finite_field.FrobeniusRingHomomorphism.Read(field.RingOn.Read(M)).At(p, a.TermAs[Nat]("1")),
					nat_arith.PowOne,
					adjoined,
					algebraic_element.FieldEmbeddingSubfieldsAdjoin.Read(M).At(m, power)))
			inside := a.Have(
				"F holds its own p-th powers",
				"«powers»(F) ⊆ F",
				By(adjoined, finite_field.PowersInsideSubfield.Read(M).At(p, F)))
			kInPowers := a.Have(
				"k is its own p-th powers, so it lies among those of F",
				"k ⊆ «powers»(F)",
				By(Normalized, fixed, adjoined, set_image.ImageSubset.At(power, k, F)))
			root := a.Have(
				"over the p-th powers of F, t has degree at most p",
				"finite_extension(M, «powers»(F), field_adjoin(M, «powers»(F), {t})) ∧ "+
					"extension_degree(M, «powers»(F), field_adjoin(M, «powers»(F), {t})) ≤ p",
				By(
					powersField,
					tIn,
					adjoined,
					positive,
					set_image.FunInImage.At(power, F, t),
					Read(rootDegree, M).At(powersOfF, t, a.TermAs[A]("frobenius_power(field_ring(M), p, t)"), p),
					finite_field.FrobeniusPowerDef.At(a.TermAs[module_record.RingOps[A]]("field_ring(M)"), p, t)))
			top := a.Have(
				"the field they generate with t holds both and is a subfield",
				"subfield(M, field_adjoin(M, «powers»(F), {t})) ∧ "+
					"«powers»(F) ⊆ field_adjoin(M, «powers»(F), {t}) ∧ "+
					"t ∈ field_adjoin(M, «powers»(F), {t})",
				By(powersField, tIn, algebraic_element.AdjoinElementSubfield.Read(M).At(powersOfF, tMember)))
			generators := a.Have(
				"so it holds the generators k and t of F",
				"k ⊆ field_adjoin(M, «powers»(F), {t}) ∧ {t} ⊆ field_adjoin(M, «powers»(F), {t})",
				BySets(top, kInPowers))
			fromBelow := a.Have(
				"so it holds F",
				"F ⊆ field_adjoin(M, «powers»(F), {t})",
				By(
					generated,
					top,
					generators,
					algebraic_element.AdjoinLeast.Read(M).At(
						k, singleton, a.TermAs[Set[A]]("field_adjoin(M, «powers»(F), {t})"))))
			fromAbove := a.Have(
				"and F holds the p-th powers and t, so it holds that field",
				"field_adjoin(M, «powers»(F), {t}) ⊆ F",
				BySets(adjoined, inside, algebraic_element.AdjoinLeast.Read(M).At(powersOfF, singleton, F)))
			same := a.Have(
				"so the p-th powers of F generate F with t",
				"field_adjoin(M, «powers»(F), {t}) = F",
				By(fromAbove, fromBelow, set_order.SubsetAntisym))
			a.Show(
				"so F has degree at most p over them",
				By(Normalized, same, powersField, inside, root))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, L *Expr[Set[A]],
			t *Expr[A],
			p *Expr[Nat],
			characteristic, subfieldK, subfieldL, fixed, kInL, tInL, finite Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			power := a.TermAs[Fun[A, A]]("frobenius_power(field_ring(M), p)")
			powersOfL := a.TermAs[Set[A]]("«powers»(L)")
			tInM := a.Have(
				"L lies in M, so t does",
				"t ∈ M.carrier",
				BySets(subfieldL, tInL, field.SubfieldSubset.At(m, L)))
			tMember := a.MemberOf[on.M](t, tInM)
			F, generated := a.LetAs[Set[A]]("F", "field_adjoin(M, k, {t})")
			powersOfF := a.TermAs[Set[A]]("«powers»(F)")
			adjoined := a.Have(
				"F is a subfield over k holding t",
				"subfield(M, F) ∧ k ⊆ F ∧ t ∈ F",
				By(
					Normalized,
					generated,
					subfieldK,
					tInM,
					algebraic_element.AdjoinElementSubfield.Read(M).At(k, tMember)))
			FInL := a.Have(
				"L holds k and t, so it holds F",
				"F ⊆ L",
				BySets(
					generated,
					subfieldL,
					kInL,
					tInL,
					algebraic_element.AdjoinLeast.Read(M).At(k, a.TermAs[Set[A]]("{t}"), L)))
			FOverPowers := a.Have(
				"F is a subfield over its p-th powers, of degree at most p",
				"subfield(M, «powers»(F)) ∧ "+
					"«powers»(F) ⊆ F ∧ "+
					"finite_extension(M, «powers»(F), F) ∧ "+
					"extension_degree(M, «powers»(F), F) ≤ p",
				By(characteristic, subfieldK, fixed, tInM, generated, Read(overPowers, M).At(k, F, t, p)))
			image := a.Have(
				"the p-th power map keeps the degree of L over F",
				"subfield(M, «powers»(L)) ∧ "+
					"finite_extension(M, «powers»(F), «powers»(L)) ∧ "+
					"extension_degree(M, «powers»(F), «powers»(L)) = extension_degree(M, F, L)",
				By(
					characteristic,
					adjoined,
					subfieldL,
					FInL,
					finite,
					perfect_field.FrobeniusImageDegree.Read(M).At(p, F, L)))
			powersInclusion := a.Have(
				"the p-th powers of L hold those of F",
				"«powers»(F) ⊆ «powers»(L)",
				By(FInL, set_image.ImageSubset.At(power, F, L)))
			inside := a.Have(
				"L holds its own p-th powers",
				"«powers»(L) ⊆ L",
				By(subfieldL, finite_field.PowersInsideSubfield.Read(M).At(p, L)))
			throughF := a.Have(
				"the tower through F",
				"finite_extension(M, «powers»(F), L) ∧ "+
					"extension_degree(M, «powers»(F), L) = "+
					"extension_degree(M, «powers»(F), F) * extension_degree(M, F, L)",
				By(
					FOverPowers,
					adjoined,
					subfieldL,
					FInL,
					finite,
					field_extension.TowerLaw.Read(M).At(powersOfF, F, L)))
			topFinite := a.Have(
				"L is finite over the larger field of the p-th powers of L",
				"finite_extension(M, «powers»(L), L)",
				By(
					FOverPowers,
					image,
					subfieldL,
					powersInclusion,
					inside,
					throughF,
					field_extension.TowerFinite.Read(M).At(powersOfF, powersOfL, L)))
			throughPowers := a.Have(
				"the tower through the p-th powers of L",
				"extension_degree(M, «powers»(F), L) = "+
					"extension_degree(M, «powers»(F), «powers»(L)) * extension_degree(M, «powers»(L), L)",
				By(
					FOverPowers,
					image,
					subfieldL,
					powersInclusion,
					inside,
					topFinite,
					field_extension.TowerLaw.Read(M).At(powersOfF, powersOfL, L)))
			degree := a.TermAs[Nat]("extension_degree(M, F, L)")
			index := a.TermAs[Nat]("extension_degree(M, «powers»(L), L)")
			lower := a.TermAs[Nat]("extension_degree(M, «powers»(F), F)")
			product := a.Have(
				"the two towers have one top",
				"extension_degree(M, F, L) * extension_degree(M, «powers»(L), L) = "+
					"extension_degree(M, F, L) * extension_degree(M, «powers»(F), F)",
				CalcEq(
					Leg(
						a.Term("extension_degree(M, «powers»(F), «powers»(L)) * extension_degree(M, «powers»(L), L)"),
						"the p-th powers of the tower have the degree of the tower",
						By(image)),
					Leg(
						a.Term("extension_degree(M, «powers»(F), L)"),
						"the tower through the p-th powers of L",
						By(throughPowers)),
					Leg(
						a.Term("extension_degree(M, «powers»(F), F) * extension_degree(M, F, L)"),
						"the tower through F",
						By(throughF)),
					FinalLeg(
						"factors commute",
						By(nat_arith.MulSym))))
			positive := a.Have(
				"L has positive degree over F",
				"0 < extension_degree(M, F, L)",
				By(adjoined, subfieldL, FInL, finite, field_extension.ExtensionDegreePositive.Read(M).At(F, L)))
			a.Show(
				"the positive degree of L over F cancels, leaving the degree of F over its p-th powers",
				ByArith(topFinite, FOverPowers, positive, product, nat_arith.MulEqLCancel.At(degree, index, lower)))
		})
	}),
})}

// SeparableOffPowerSubfield — an element t of K outside the p-th powers of K
// separates: when K is finite over F = k(t) and k is its own p-th powers, every
// x of K is separable over F. Put L = F(x). L has degree at most p over its p-th
// powers, and t has degree exactly p over them, lying outside them with t ^ p
// inside, so they generate L with t. They lie in F(x ^ p), which holds t as well,
// so F(x ^ p) = F(x). But were x inseparable, its minimal polynomial would be
// g(T ^ p) for a shorter g, a root of which is x ^ p, of smaller degree over F.
var SeparableOffPowerSubfield = separableOffPowerSubfieldThm{family.Add(registry.ProofEntry{
	Name: "SeparableOffPowerSubfield",
	Key:  "prop_74d089c4f439bf5a",
	Build: family.Sections(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀t x:A. ∀p:num.",
		Hypotheses: []string{
			"ring_prime_characteristic(field_ring(M), p)",
			"subfield(M, k)",
			"subfield(M, K)",
			"«powers»(k) = k",
			"k ⊆ K",
			"t ∈ K",
			"finite_extension(M, field_adjoin(M, k, {t}), K)",
			"t ∉ «powers»(K)",
			"x ∈ K",
		},
		Conclusion: "separable_over(M, field_adjoin(M, k, {t}), x)",
		Abbrev: Abbrev{
			{Name: "powers", Text: "image(frobenius_power(field_ring(M), p))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// t outside the p-th powers of L generates L over them: L has degree at most
		// p over them, and t has degree exactly p.
		rootGenerates := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀p:num.",
			Hypotheses: []string{
				"ring_prime_characteristic(field_ring(M), p)",
				"subfield(M, k)",
				"subfield(M, L)",
				"«powers»(k) = k",
				"k ⊆ L",
				"t ∈ L",
				"finite_extension(M, field_adjoin(M, k, {t}), L)",
				"t ∉ «powers»(L)",
			},
			Conclusion: "field_adjoin(M, «powers»(L), {t}) = L",
		}, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, L *Expr[Set[A]],
			t *Expr[A],
			p *Expr[Nat],
			characteristic, subfieldK, subfieldL, fixed, kInL, tInL, finite, tOutside Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			power := a.TermAs[Fun[A, A]]("frobenius_power(field_ring(M), p)")
			powersOfL := a.TermAs[Set[A]]("«powers»(L)")
			tMember := a.MemberOf[on.M](t, a.Have(
				"L lies in M, so t does",
				"t ∈ M.carrier",
				BySets(subfieldL, tInL, field.SubfieldSubset.At(m, L))))
			powersField := a.Have(
				"the p-th powers of L are a subfield",
				"subfield(M, «powers»(L))",
				By(
					characteristic,
					finite_field.FrobeniusRingHomomorphism.Read(field.RingOn.Read(M)).At(p, a.TermAs[Nat]("1")),
					nat_arith.PowOne,
					subfieldL,
					algebraic_element.FieldEmbeddingSubfieldsAdjoin.Read(M).At(m, power)))
			index := a.Have(
				"L has degree at most p over them",
				"finite_extension(M, «powers»(L), L) ∧ extension_degree(M, «powers»(L), L) ≤ p",
				By(
					characteristic,
					subfieldK,
					subfieldL,
					fixed,
					kInL,
					tInL,
					finite,
					PowerSubfieldIndexBound.Read(M).At(k, L, t, p)))
			Q, QDef := a.LetAs[Set[A]]("Q", "field_adjoin(M, «powers»(L), {t})")
			root := a.Have(
				"t lies outside them with t ^ p inside, so it has degree exactly p over them",
				"finite_extension(M, «powers»(L), Q) ∧ extension_degree(M, «powers»(L), Q) = p",
				By(
					Normalized,
					QDef,
					characteristic,
					powersField,
					tInL,
					tOutside,
					set_image.FunInImage.At(power, L, t),
					finite_field.FrobeniusPowerDef.At(a.TermAs[module_record.RingOps[A]]("field_ring(M)"), p, t),
					perfect_field.PrimeRootDegree.Read(M).At(powersOfL, p, tMember)))
			between := a.Have(
				"Q lies between them and L",
				"subfield(M, Q) ∧ «powers»(L) ⊆ Q ∧ t ∈ Q ∧ Q ⊆ L",
				By(
					Normalized,
					QDef,
					powersField,
					subfieldL,
					finite_field.PowersInsideSubfield.Read(M).At(p, L),
					tInL,
					algebraic_element.AdjoinElementBetween.Read(M).At(powersOfL, L, t)))
			comparison := a.Conjuncts(
				a.Have(
					"Q is an intermediate field of L over them",
					"extension_degree(M, «powers»(L), Q) ≤ extension_degree(M, «powers»(L), L) ∧ "+
						"(extension_degree(M, «powers»(L), Q) = extension_degree(M, «powers»(L), L) ⇒ Q = L)",
					By(
						powersField,
						between,
						subfieldL,
						index,
						field_extension.IntermediateDegree.Read(M).At(powersOfL, Q, L))),
				"so its degree over them is at most that of L",
				"and it is L when the degrees agree")
			equal := a.Have(
				"Q has degree p over them and L at most p, so the degrees agree",
				"extension_degree(M, «powers»(L), Q) = extension_degree(M, «powers»(L), L)",
				ByArith(index, root, comparison[0]))
			a.Show(
				"so Q is all of L",
				By(comparison[1], equal))
		})

		// An inseparable x has zero derivative for its minimal polynomial f, so f is
		// supported on the multiples of p: f is g(T ^ p) for a polynomial g over F of
		// smaller degree, and g vanishes at x ^ p.
		inseparableDrop := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀F:set(A). ∀x:A. ∀p:num.",
			Hypotheses: []string{
				"ring_prime_characteristic(field_ring(M), p)",
				"subfield(M, F)",
				"x ∈ M.carrier",
				"algebraic_over(M, F, x)",
				"¬polynomial_separable(restrict_ring(field_ring(M), F), minimal_polynomial(M, F, x))",
			},
			Conclusion: "extension_degree(M, F, field_adjoin(M, F, {monoid_pow(M.mul, M.one, x, p)})) < " +
				"extension_degree(M, F, field_adjoin(M, F, {x}))",
		}, func(
			a *Argument,
			M field.FieldFact[on.M],
			F *Expr[Set[A]],
			x *Expr[A],
			p *Expr[Nat],
			characteristic, subfieldF, xIn, algebraic, inseparable Fact,
		) {
			ring := field.RingOn.Read(M)
			m := a.TermAs[FieldOps[A]]("M")
			zero, one, carrier := a.TermAs[A]("M.zero"), a.TermAs[A]("M.one"), a.TermAs[Set[A]]("M.carrier")
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			xMember := a.MemberOf[on.M](x, xIn)
			prime := a.Unfolded(characteristic, finite_field.PrimeCharacteristicDef)
			two := a.Have(
				"a prime is at least two",
				"2 ≤ p",
				ByArith(prime, nat_prime.PrimeAtLeastTwo.At(p)))
			positive := a.Have(
				"so p is positive",
				"0 < p",
				ByArith(two))
			f, fDef := a.LetAs[Fun[Nat, A]]("f", "minimal_polynomial(M, F, x)")
			minimal := a.Conjuncts(
				a.Have(
					"f is a monic polynomial over F vanishing at x",
					"polynomial_over(F, f) ∧ polynomial_monic(f) ∧ polynomial_eval(f, x) = M.zero",
					By(
						Normalized,
						fDef,
						subfieldF,
						xIn,
						algebraic,
						algebraic_element.MinimalPolynomialSpec.Read(M).AsFact().At(F, x))),
				"f is a polynomial over F",
				"f is monic",
				"f vanishes at x")
			fOver, fMonic, fRoot := minimal[0], minimal[1], minimal[2]
			irreducible := a.Have(
				"f is irreducible over F",
				"polynomial_irreducible(restrict_ring(field_ring(M), F), f)",
				By(
					Normalized,
					fDef,
					subfieldF,
					algebraic,
					algebraic_element.MinimalPolynomialIrreducible.Read(M).At(F, xMember)))
			fieldF := a.Have(
				"F is a field under the operations of M",
				"field_on(restrict_field(M, F))",
				By(subfieldF, field.SubfieldFieldOn.Read(M).At(F)))
			derivative := a.Have(
				"f is irreducible and inseparable over the field F, so its derivative vanishes",
				"polynomial_derivative(f) = vec_zero",
				By(
					inseparable,
					irreducible,
					fieldF,
					field.RestrictFieldRing.At(m, F),
					separable_polynomial.SeparableIffDerivative.Read(fieldF).At(f)))
			fOverM := a.Have(
				"f is a polynomial over M as well",
				"polynomial_over(M.carrier, f)",
				By(
					subfieldF,
					fOver,
					field.SubfieldSubset.At(m, F),
					polynomial.PolynomialOverMono.At(zero, F, carrier, f)))
			off := a.Have(
				"so its coefficients vanish off the multiples of p",
				"∀i:num. ¬(p ∣ i) ⇒ f(i) = M.zero",
				By(characteristic, fOverM, derivative, perfect_field.ZeroDerivativeCoefficients.Read(M)))
			g, gDef := a.LetAs[Fun[Nat, A]]("g", "λi:num. f(p * i)")
			substitution := a.Have(
				"so f is g with T ^ p for the variable",
				"series_substitute(field_ring(M), g, p) = f",
				Derive(func(b *Argument) {
					b.Do(Funext())
					n := b.FixAs[Nat]("n")
					b.Cases(b.Term("p ∣ n"))
					b.When(
						"at a multiple p * j the substitution reads g(j), which is f(p * j)",
						func(c *Argument, multiple Fact) {
							j, factor := c.ObtainAs[Nat](
								"n is a multiple of p",
								"∃j:num. n = p * j",
								By(multiple, nat_divides.DividesFactor.At(p, n)))
							c.Show(
								"read the substitution at p * j",
								By(
									Normalized,
									factor,
									gDef,
									positive,
									formal_series.SeriesSubstituteAtMultiple.At(fieldRing, g, p, j)))
						})
					b.Otherwise(
						"off the multiples both vanish",
						func(c *Argument, notMultiple Fact) {
							c.Show(
								"the substitution has no term there, and neither has f",
								By(
									Normalized,
									notMultiple,
									off.At(n),
									nat_divides.DividesFactor.At(p, n),
									formal_series.SeriesSubstituteOffMultiples.At(fieldRing, g, p, n)))
						})
				}))
			d, dDef := a.LetAs[Nat]("d", "polynomial_degree(f)")
			dPositive := a.Have(
				"f is irreducible, so d is positive",
				"0 < d",
				By(Normalized, dDef, a.Unfolded(irreducible, polynomial_division.PolynomialIrreducibleDef)))
			past := a.Unfolded(
				a.Have(
					"f vanishes past d",
					"vec⟨suc(d)⟩(f)",
					By(Normalized, dDef, fOverM, polynomial.DegreeVec.At(zero, carrier, f))),
				vec_space.VecDef)
			gBound := a.Have(
				"g vanishes from d on, p * i exceeding d there",
				"vec⟨d⟩(g)",
				Unfold(vec_space.VecDef),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					beyond := b.Assume()
					multiple := b.TermAs[Nat]("p * i")
					exceeds := b.Have(
						"p is at least two and i at least d, which is positive",
						"suc(d) ≤ p * i",
						ByArith(two, beyond, dPositive, nat_order.LessEqMulRightCancel.At(b.TermAs[Nat]("2"), p, i)))
					b.Show(
						"so the coefficient of f at p * i vanishes",
						By(Normalized, gDef, exceeds, past.At(multiple)))
				}))
			gOver := a.Have(
				"g is a polynomial over F",
				"polynomial_over(F, g)",
				By(
					gDef,
					gBound,
					fOver,
					polynomial.PolynomialOverDef.At(zero, F, f),
					polynomial.PolynomialOverDef.At(zero, F, g)))
			gOverM := a.Have(
				"so over M",
				"polynomial_over(M.carrier, g)",
				By(
					subfieldF,
					gOver,
					field.SubfieldSubset.At(m, F),
					polynomial.PolynomialOverMono.At(zero, F, carrier, g)))
			gRoot := a.Have(
				"g takes at x ^ p the value of f at x, which is zero",
				"polynomial_eval(g, monoid_pow(M.mul, M.one, x, p)) = M.zero",
				By(
					substitution,
					positive,
					gOverM,
					xIn,
					fRoot,
					formal_series.EvalSeriesSubstitute.Read(ring).At(g, p, xMember)))
			leading := a.Have(
				"the leading coefficient of f is one, which is not zero",
				"f(d) ≠ M.zero",
				By(
					Normalized,
					fMonic,
					dDef,
					polynomial.PolynomialMonicDef.At(zero, one, f),
					field.OneNotZeroOn.Read(M)))
			j, factor := a.ObtainAs[Nat](
				"so d is a multiple of p",
				"∃j:num. d = p * j",
				By(Normalized, leading, off, nat_divides.DividesFactor.At(p, d)))
			gLeading := a.Have(
				"so g has the coefficient of f at d",
				"g(j) ≠ M.zero",
				By(Normalized, leading, gDef, factor))
			gNonzero := a.Have(
				"so g is not the zero polynomial",
				"g ≠ vec_zero",
				By(Normalized, gLeading, vec_space.VecZeroDef.At(zero, j)))
			e, predecessor := a.ObtainAs[Nat](
				"d is a successor",
				"∃e:num. d = suc(e)",
				ByArith(dPositive, peano.Cases.At(d)))
			gDegree := a.Have(
				"g vanishes from d = suc(e) on, so its degree is below d",
				"polynomial_degree(g) < d",
				predecessor.Rw(),
				ByArith(gBound, polynomial.DegreeLeast.At(zero, g, e)))
			powerMember := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)).At(xMember, p)
			powerAlgebraic := a.Have(
				"so x ^ p is algebraic over F",
				"algebraic_over(M, F, monoid_pow(M.mul, M.one, x, p))",
				By(
					gOver,
					gNonzero,
					gRoot,
					algebraic_element.AlgebraicOverDef.At(m, F, a.TermAs[A]("monoid_pow(M.mul, M.one, x, p)"))))
			a.Show(
				"over F, x ^ p has the degree of its minimal "+
					"polynomial, at most that of g, and x the degree d of f",
				ByArith(
					gDegree,
					dDef,
					fDef,
					subfieldF,
					algebraic,
					powerAlgebraic,
					gOver,
					gNonzero,
					gRoot,
					algebraic_element.AdjoinDegree.Read(M).At(F, xMember),
					algebraic_element.AdjoinDegree.Read(M).At(F, powerMember),
					algebraic_element.MinimalPolynomialLeast.Read(M).At(F, powerMember, g)))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			t, x *Expr[A],
			p *Expr[Nat],
			characteristic, subfieldK, subfieldTop, fixed, kInK, tInK, finite, tOutside, xInK Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			power := a.TermAs[Fun[A, A]]("frobenius_power(field_ring(M), p)")
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			xPower := a.TermAs[A]("monoid_pow(M.mul, M.one, x, p)")
			F, FDef := a.LetAs[Set[A]]("F", "field_adjoin(M, k, {t})")
			base := a.Have(
				"F is a subfield between k and K holding t",
				"subfield(M, F) ∧ k ⊆ F ∧ t ∈ F ∧ F ⊆ K",
				By(
					Normalized,
					FDef,
					subfieldK,
					subfieldTop,
					kInK,
					tInK,
					algebraic_element.AdjoinElementBetween.Read(M).At(k, K, t)))
			L, LDef := a.LetAs[Set[A]]("L", "field_adjoin(M, F, {x})")
			middle := a.Have(
				"L = F(x) is a subfield between F and K holding x",
				"subfield(M, L) ∧ F ⊆ L ∧ x ∈ L ∧ L ⊆ K",
				By(
					Normalized,
					LDef,
					base,
					subfieldTop,
					xInK,
					algebraic_element.AdjoinElementBetween.Read(M).At(F, K, x)))
			finiteL := a.Have(
				"L lies inside K, so it is finite over F",
				"finite_extension(M, F, L)",
				By(base, middle, subfieldTop, finite, field_extension.TowerFinite.Read(M).At(F, L, K)))
			below := a.Have(
				"L holds k and t",
				"k ⊆ L ∧ t ∈ L",
				BySets(base, middle))
			outside := a.Have(
				"t lies outside the p-th powers of L, which lie among those of K",
				"t ∉ «powers»(L)",
				BySets(tOutside, middle))
			generated := a.Have(
				"so the p-th powers of L generate L with t",
				"field_adjoin(M, «powers»(L), {t}) = L",
				By(
					FDef,
					characteristic,
					subfieldK,
					middle,
					fixed,
					below,
					finiteL,
					outside,
					Read(rootGenerates, M).At(k, L, t, p)))
			powerInL := a.Have(
				"x ^ p, a p-th power of a point of L, lies in L",
				"monoid_pow(M.mul, M.one, x, p) ∈ L",
				BySets(
					middle,
					finite_field.PowersInsideSubfield.Read(M).At(p, L),
					finite_field.FrobeniusPowerDef.At(fieldRing, p, x)))
			R, RDef := a.LetAs[Set[A]]("R", "field_adjoin(M, F, {monoid_pow(M.mul, M.one, x, p)})")
			top := a.Have(
				"R = F(x ^ p) is a subfield between F and L holding x ^ p",
				"subfield(M, R) ∧ F ⊆ R ∧ monoid_pow(M.mul, M.one, x, p) ∈ R ∧ R ⊆ L",
				By(
					Normalized,
					RDef,
					base,
					middle,
					powerInL,
					algebraic_element.AdjoinElementBetween.Read(M).At(F, L, xPower)))
			generators := a.Have(
				"F and x lie in M",
				"F ⊆ M.carrier ∧ {x} ⊆ M.carrier ∧ x ∈ M.carrier",
				BySets(subfieldTop, base, xInK, field.SubfieldSubset.At(m, K)))
			carried := a.Have(
				"the p-th power map, a ring endomorphism, carries "+
					"adjoined fields to the fields the images generate",
				Statement{
					Binders: "∀K E:set(A).",
					Hypotheses: []string{
						"K ⊆ M.carrier",
						"E ⊆ M.carrier",
					},
					Conclusion: "«powers»(field_adjoin(M, K, E)) = field_adjoin(M, «powers»(K), «powers»(E))",
				},
				By(
					characteristic,
					finite_field.FrobeniusRingHomomorphism.Read(field.RingOn.Read(M)).At(p, a.TermAs[Nat]("1")),
					nat_arith.PowOne,
					algebraic_element.FieldEmbeddingSubfieldsAdjoin.Read(M).At(m, power)))
			imageOfL := a.Have(
				"so it carries the field F(x) to the field the p-th powers of F and of x generate",
				"«powers»(L) = field_adjoin(M, «powers»(F), «powers»({x}))",
				By(LDef, generators, carried.At(F, a.TermAs[Set[A]]("{x}"))))
			images := a.Have(
				"R holds both, F holding its own p-th powers",
				"«powers»(F) ⊆ R ∧ «powers»({x}) ⊆ R",
				BySets(
					base,
					top,
					finite_field.PowersInsideSubfield.Read(M).At(p, F),
					finite_field.FrobeniusPowerDef.At(fieldRing, p, x)))
			powersInR := a.Have(
				"so R holds the p-th powers of L",
				"«powers»(L) ⊆ R",
				By(
					imageOfL,
					top,
					images,
					algebraic_element.AdjoinLeast.Read(M).At(
						a.TermAs[Set[A]]("«powers»(F)"), a.TermAs[Set[A]]("«powers»({x})"), R)))
			tInR := a.Have(
				"and t, which lies in F",
				"{t} ⊆ R",
				BySets(base, top))
			LInR := a.Have(
				"so R holds all of L",
				"L ⊆ R",
				By(
					Normalized,
					generated,
					top,
					powersInR,
					tInR,
					algebraic_element.AdjoinLeast.Read(M).At(
						a.TermAs[Set[A]]("«powers»(L)"), a.TermAs[Set[A]]("{t}"), R)))
			same := a.Have(
				"so x and x ^ p generate one field over F",
				"R = L",
				By(top, LInR, set_order.SubsetAntisym))
			algebraic := a.Have(
				"K is finite over F, so x is algebraic over F",
				"algebraic_over(M, F, x)",
				By(base, subfieldTop, finite, xInK, algebraic_element.FiniteExtensionAlgebraic.Read(M).At(F, K, x)))
			separable := a.Have(
				"an inseparable x would drop in degree at x ^ p, which generates the same field",
				"polynomial_separable(restrict_ring(field_ring(M), F), minimal_polynomial(M, F, x))",
				Derive(func(b *Argument) {
					inseparable := b.SupposeNot()
					drop := b.Have(
						"the degree of R over F would be below that of L",
						"extension_degree(M, F, R) < extension_degree(M, F, L)",
						By(
							Normalized,
							RDef,
							LDef,
							characteristic,
							base,
							generators,
							algebraic,
							inseparable,
							Read(inseparableDrop, M).At(F, x, p)))
					b.Show(
						"but R is L",
						same.Rw(),
						ByArith(drop))
				}))
			a.Show(
				"x is algebraic over F with a separable minimal polynomial",
				By(algebraic, separable, galois_correspondence.SeparableOverDef))
		})
	}),
})}

// SeparatingParameterExists — a finitely generated field K of transcendence degree
// one over a perfect field k has a separating parameter: an element t transcendental
// over k with K finite and separable over k(t). K is finite over k(s) for the
// transcendental s given, being finitely generated and algebraic over it. In
// characteristic zero s serves, an
// irreducible polynomial being separable. In characteristic p the perfect field
// k is its own p-th powers, and the degree of K descends: while the parameter in
// hand is a p-th power r ^ p of a point of K, r is again a parameter, of smaller
// degree, as it lies outside k(r ^ p). The parameter the descent ends at lies
// outside the p-th powers of K, and such a parameter separates.
var SeparatingParameterExists = separatingParameterExistsThm{family.Add(registry.ProofEntry{
	Name: "SeparatingParameterExists",
	Key:  "prop_6b3a91687ce9e851",
	Reading: "These are the clauses of regular_function_field without its exact constants, which no " +
		"step reads: K may hold a finite extension of k. Perfection is load-bearing: over k = 𝔽_p(a) the " +
		"field K = k(a^(1/p))(t) has no separating parameter, a^(1/p) being purely inseparable over k.",
	Build: family.Sections(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"k ⊆ K",
			"perfect_field(restrict_field(M, k))",
			"∃E:set(A). finite(E) ∧ E ⊆ K ∧ field_adjoin(M, k, E) = K",
			"∃s:A. " +
				"    s ∈ K ∧ " +
				"    ¬algebraic_over(M, k, s) ∧ " +
				"    (∀x:A. x ∈ K ⇒ algebraic_over(M, field_adjoin(M, k, {s}), x))",
		},
		Conclusion: "∃t:A. " +
			"    t ∈ K ∧ " +
			"    ¬algebraic_over(M, k, t) ∧ " +
			"    finite_extension(M, field_adjoin(M, k, {t}), K) ∧ " +
			"    (∀x:A. x ∈ K ⇒ separable_over(M, field_adjoin(M, k, {t}), x))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		// K is finite over k(s): over it the finite set E, every point of it
		// algebraic, generates K.
		finiteOverParameter := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀k K E:set(A). ∀s:A.",
			Hypotheses: []string{
				"subfield(M, k)",
				"subfield(M, K)",
				"k ⊆ K",
				"finite(E)",
				"E ⊆ K",
				"field_adjoin(M, k, E) = K",
				"s ∈ K",
				"∀x:A. x ∈ K ⇒ algebraic_over(M, field_adjoin(M, k, {s}), x)",
			},
			Conclusion: "finite_extension(M, field_adjoin(M, k, {s}), K)",
		}, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K, E *Expr[Set[A]],
			s *Expr[A],
			subfieldK, subfieldTop, kInK, finiteE, EInK, generated, sInK, algebraic Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			F, FDef := a.LetAs[Set[A]]("F", "field_adjoin(M, k, {s})")
			base := a.Have(
				"F is a subfield between k and K",
				"subfield(M, F) ∧ k ⊆ F ∧ s ∈ F ∧ F ⊆ K",
				By(
					Normalized,
					FDef,
					subfieldK,
					subfieldTop,
					kInK,
					sInK,
					algebraic_element.AdjoinElementBetween.Read(M).At(k, K, s)))
			inside := a.Have(
				"F and E lie in M",
				"F ⊆ M.carrier ∧ E ⊆ M.carrier",
				BySets(subfieldTop, base, EInK, field.SubfieldSubset.At(m, K)))
			G, GDef := a.LetAs[Set[A]]("G", "field_adjoin(M, F, E)")
			top := a.Have(
				"G = F(E) is a subfield holding F and E",
				"subfield(M, G) ∧ F ⊆ G ∧ E ⊆ G",
				By(Normalized, GDef, inside, algebraic_element.AdjoinSubfield.Read(M).At(F, E)))
			kInG := a.Have(
				"so it holds k",
				"k ⊆ G",
				BySets(base, top))
			same := a.Have(
				"G and K hold each other's generators, so G is K",
				"G = K",
				By(
					Normalized,
					GDef,
					generated,
					top,
					subfieldTop,
					kInG,
					base,
					EInK,
					algebraic_element.AdjoinLeast.Read(M).At(k, E, G),
					algebraic_element.AdjoinLeast.Read(M).At(F, E, K),
					set_order.SubsetAntisym.At(G, K)))
			algebraicE := a.Have(
				"E lies in K, so its points are algebraic over F",
				"∀x:A. x ∈ E ⇒ algebraic_over(M, F, x)",
				BySets(EInK, algebraic))
			a.Show(
				"a finite set of algebraic points generates a finite extension",
				By(
					Normalized,
					same,
					GDef,
					base,
					finiteE,
					inside,
					algebraicE,
					algebraic_element.FiniteAlgebraicAdjoin.Read(M).At(F, E)))
		})

		// A step of the descent. With r in K and r ^ p a parameter, r is one too: an
		// algebraic r would make k(r), a finite extension, hold r ^ p algebraic. And
		// r lies outside k(r ^ p), so k(r) is a proper extension of it, of degree at
		// least two, and the tower through k(r) drops the degree of K.
		rootStep := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀k K:set(A). ∀r:A. ∀p:num.",
			Hypotheses: []string{
				"2 ≤ p",
				"subfield(M, k)",
				"subfield(M, K)",
				"k ⊆ K",
				"r ∈ K",
				"¬algebraic_over(M, k, monoid_pow(M.mul, M.one, r, p))",
				"finite_extension(M, field_adjoin(M, k, {monoid_pow(M.mul, M.one, r, p)}), K)",
			},
			Conclusion: "¬algebraic_over(M, k, r) ∧ " +
				"finite_extension(M, field_adjoin(M, k, {r}), K) ∧ " +
				"extension_degree(M, field_adjoin(M, k, {r}), K) < " +
				"extension_degree(M, field_adjoin(M, k, {monoid_pow(M.mul, M.one, r, p)}), K)",
		}, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			r *Expr[A],
			p *Expr[Nat],
			two, subfieldK, subfieldTop, kInK, rInK, transcendental, finite Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			T, TDef := a.LetAs[A]("T", "monoid_pow(M.mul, M.one, r, p)")
			R, RDef := a.LetAs[Set[A]]("R", "field_adjoin(M, k, {r})")
			Q, QDef := a.LetAs[Set[A]]("Q", "field_adjoin(M, k, {T})")
			rational := a.Have(
				"R is a subfield between k and K holding r",
				"subfield(M, R) ∧ k ⊆ R ∧ r ∈ R ∧ R ⊆ K",
				By(
					Normalized,
					RDef,
					subfieldK,
					subfieldTop,
					kInK,
					rInK,
					algebraic_element.AdjoinElementBetween.Read(M).At(k, K, r)))
			fieldR := a.Have(
				"R is a field under the operations of M",
				"field_on(restrict_field(M, R))",
				By(rational, field.SubfieldFieldOn.Read(M).At(R)))
			rMember := a.MemberOf[on.M](r, a.Have(
				"K lies in M, so r does",
				"r ∈ M.carrier",
				BySets(subfieldTop, rInK, field.SubfieldSubset.At(m, K))))
			powerInR := a.Have(
				"R holds the power T of r",
				"T ∈ R",
				By(
					Normalized,
					TDef,
					rational,
					comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(fieldR))).AsFact().At(r, p)))
			rTranscendental := a.Have(
				"r algebraic would make R a finite extension of k holding T, then algebraic",
				"¬algebraic_over(M, k, r)",
				By(
					Normalized,
					transcendental,
					powerInR,
					subfieldK,
					rational,
					RDef,
					rMember,
					algebraic_element.AdjoinDegree.Read(M).At(k, rMember),
					algebraic_element.FiniteExtensionAlgebraic.Read(M).At(k, R, T)))
			lower := a.Have(
				"Q is a subfield between k and R",
				"subfield(M, Q) ∧ k ⊆ Q ∧ T ∈ Q ∧ Q ⊆ R",
				By(
					Normalized,
					QDef,
					subfieldK,
					rational,
					powerInR,
					algebraic_element.AdjoinElementBetween.Read(M).At(k, R, T)))
			tower := a.Have(
				"the tower Q ⊆ R ⊆ K",
				"finite_extension(M, Q, R) ∧ "+
					"finite_extension(M, R, K) ∧ "+
					"extension_degree(M, Q, K) = extension_degree(M, Q, R) * extension_degree(M, R, K)",
				By(
					lower,
					rational,
					subfieldTop,
					finite,
					field_extension.TowerFinite.Read(M).At(Q, R, K),
					field_extension.TowerLaw.Read(M).At(Q, R, K)))
			outside := a.Have(
				"r, transcendental over k, lies outside Q",
				"r ∉ Q",
				By(
					Normalized,
					QDef,
					TDef,
					two,
					subfieldK,
					rTranscendental,
					TranscendentalOutsidePowerAdjoin.Read(M).At(k, rMember, p)))
			proper := a.Have(
				"so R is not Q, and its degree over Q is not one",
				"extension_degree(M, Q, R) ≠ 1",
				By(Normalized, outside, rational, lower, tower, field_extension.DegreeOneIff.Read(M).At(Q, R)))
			positive := a.Have(
				"both steps of the tower have positive degree",
				"0 < extension_degree(M, Q, R) ∧ 0 < extension_degree(M, R, K)",
				By(
					lower,
					rational,
					subfieldTop,
					tower,
					field_extension.ExtensionDegreePositive.Read(M).At(Q, R),
					field_extension.ExtensionDegreePositive.Read(M).At(R, K)))
			drop := a.Have(
				"so the degree of R over Q, at least two, drops the degree of K from Q to R",
				"extension_degree(M, R, K) < extension_degree(M, Q, K)",
				ByArith(
					positive,
					proper,
					tower,
					nat_order.LessEqMulRightCancel.At(
						a.TermAs[Nat]("2"),
						a.TermAs[Nat]("extension_degree(M, Q, R)"),
						a.TermAs[Nat]("extension_degree(M, R, K)"))))
			a.Show(
				"r is a parameter with K of smaller degree over it",
				By(rTranscendental, tower, drop))
		})

		// The descent: by strong induction on the degree of K, any parameter leads to
		// one outside the p-th powers of K. A parameter that is a p-th power has a
		// root r in K, of smaller degree, and the induction goes on from r.
		descent := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀k K:set(A). ∀p:num. ∀t:A.",
			Hypotheses: []string{
				"ring_prime_characteristic(field_ring(M), p)",
				"subfield(M, k)",
				"subfield(M, K)",
				"k ⊆ K",
				"t ∈ K",
				"¬algebraic_over(M, k, t)",
				"finite_extension(M, field_adjoin(M, k, {t}), K)",
			},
			Conclusion: "«separating»",
			Abbrev: Abbrev{
				{Name: "powers", Text: "image(frobenius_power(field_ring(M), p))"},
				{Name: "separating", Text: "∃u:A. " +
					"    u ∈ K ∧ " +
					"    ¬algebraic_over(M, k, u) ∧ " +
					"    finite_extension(M, field_adjoin(M, k, {u}), K) ∧ " +
					"    u ∉ «powers»(K)"},
			},
		}, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			p *Expr[Nat],
			t *Expr[A],
			characteristic, subfieldK, subfieldTop, kInK, tInK, transcendental, finite Fact,
		) {
			two := a.Have(
				"a prime is at least two",
				"2 ≤ p",
				ByArith(
					characteristic,
					finite_field.PrimeCharacteristicDef.At(a.TermAs[module_record.RingOps[A]]("field_ring(M)"), p),
					nat_prime.PrimeAtLeastTwo.At(p)))
			indexed := a.Have(
				"every parameter of K, of whatever degree, leads to one outside the p-th powers of K",
				Statement{
					Binders: "∀n:num. ∀s:A.",
					Hypotheses: []string{
						"s ∈ K",
						"¬algebraic_over(M, k, s)",
						"finite_extension(M, field_adjoin(M, k, {s}), K)",
						"extension_degree(M, field_adjoin(M, k, {s}), K) = n",
					},
					Conclusion: "«separating»",
				},
				ByInduction(nat_order.StrongInduction,
					Case(
						"a parameter of degree n goes down to a root of "+
							"smaller degree, or is itself outside the p-th powers",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							smaller := b.Assume()
							s := b.FixAs[A]("s")
							data := b.Conjuncts(
								b.Assume(),
								"s lies in K",
								"s is transcendental over k",
								"K is finite over k(s)",
								"K has degree n over k(s)")
							sInK, sTranscendental, sFinite, sDegree := data[0], data[1], data[2], data[3]
							b.Cases(b.Term("s ∈ «powers»(K)"))
							b.When(
								"a p-th power s = r ^ p has a root r in K, of smaller degree",
								func(c *Argument, power Fact) {
									r, root := c.ObtainAs[A](
										"s is the p-th power of a point r of K",
										"∃r:A. r ∈ K ∧ s = monoid_pow(M.mul, M.one, r, p)",
										By(power, set_basic.InImage, finite_field.FrobeniusPowerDef))
									parts := c.Conjuncts(
										root,
										"r lies in K",
										"s is r ^ p")
									rInK, sPower := parts[0], parts[1]
									step := c.Have(
										"r is a parameter of K, of degree below n",
										"¬algebraic_over(M, k, r) ∧ "+
											"finite_extension(M, field_adjoin(M, k, {r}), K) ∧ "+
											"extension_degree(M, field_adjoin(M, k, {r}), K) < n",
										sPower.Rw(),
										By(
											two,
											subfieldK,
											subfieldTop,
											kInK,
											rInK,
											sTranscendental,
											sFinite,
											sDegree,
											Read(rootStep, M).At(k, K, r, p)))
									c.Show(
										"the induction goes on from r",
										By(smaller.At(c.TermAs[Nat]("extension_degree(M, field_adjoin(M, k, {r}), K)"), r), rInK, step))
								})
							b.Otherwise(
								"a parameter outside the p-th powers is the one sought",
								func(c *Argument, outside Fact) {
									c.Take(s)
									c.Show(
										"s lies in K, and is a parameter outside the p-th powers of K",
										By(sInK, sTranscendental, sFinite, outside))
								})
						}))))
			a.Show(
				"t is a parameter of some degree",
				By(
					indexed.At(a.TermAs[Nat]("extension_degree(M, field_adjoin(M, k, {t}), K)"), t),
					tInK,
					transcendental,
					finite))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			subfieldK, subfieldTop, kInK, perfect, generated, hasParameter Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			E, generators := a.UnpackAs[Set[A]](generated, "E")
			s, parameter := a.UnpackAs[A](hasParameter, "s")
			generatorParts := a.Conjuncts(
				generators,
				"E is finite",
				"E lies in K",
				"E generates K over k")
			parameterParts := a.Conjuncts(
				parameter,
				"s lies in K",
				"s is transcendental over k",
				"K is algebraic over k(s)")
			sInK, transcendental, algebraic := parameterParts[0], parameterParts[1], parameterParts[2]
			finite := a.Have(
				"E generates K over k(s) too, each point of it algebraic, so K is finite over k(s)",
				"finite_extension(M, field_adjoin(M, k, {s}), K)",
				By(
					subfieldK,
					subfieldTop,
					kInK,
					generatorParts[0],
					generatorParts[1],
					generatorParts[2],
					sInK,
					algebraic,
					Read(finiteOverParameter, M).At(k, K, E, s)))
			a.Cases(a.Term("characteristic_zero(field_ring(M))"))
			a.When(
				"in characteristic zero s serves, irreducible polynomials being separable",
				func(b *Argument, zero Fact) {
					base := b.Have(
						"k(s) is a subfield",
						"subfield(M, field_adjoin(M, k, {s}))",
						By(subfieldK, subfieldTop, kInK, sInK, algebraic_element.AdjoinElementBetween.Read(M).At(k, K, s)))
					separable := b.Have(
						"each x of K is algebraic over k(s), with an irreducible minimal polynomial",
						"∀x:A. x ∈ K ⇒ separable_over(M, field_adjoin(M, k, {s}), x)",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xInK := c.Assume()
							xMember := c.MemberOf[on.M](x, c.Have(
								"K lies in M, so x does",
								"x ∈ M.carrier",
								BySets(subfieldTop, xInK, field.SubfieldSubset.At(m, K))))
							xAlgebraic := c.Have(
								"x is algebraic over k(s)",
								"algebraic_over(M, field_adjoin(M, k, {s}), x)",
								By(algebraic.At(x), xInK))
							F := c.TermAs[Set[A]]("field_adjoin(M, k, {s})")
							c.Show(
								"its minimal polynomial is irreducible, and so separable in characteristic zero",
								By(
									zero,
									base,
									xMember,
									xAlgebraic,
									galois_correspondence.SeparableOverDef.At(m, F, x),
									algebraic_element.MinimalPolynomialIrreducible.Read(M).At(F, xMember),
									separable_polynomial.CharZeroIrreducibleSeparable.Read(M).At(
										F, c.TermAs[Fun[Nat, A]]("minimal_polynomial(M, field_adjoin(M, k, {s}), x)"))))
						}))
					b.Take(s)
					b.Show(
						"s lies in K, and K is finite and separable over k(s)",
						By(sInK, transcendental, finite, separable))
				})
			a.Otherwise(
				"in characteristic p the descent reaches a parameter outside the p-th powers of K, which separates",
				func(b *Argument, nonzero Fact) {
					p, characteristic := b.ObtainAs[Nat](
						"M has a prime characteristic p",
						"∃p:num. ring_prime_characteristic(field_ring(M), p)",
						By(Normalized, nonzero, finite_field.FieldCharacteristicCases.Read(M)))
					fixed := b.Have(
						"k, perfect, is its own p-th powers",
						"image(frobenius_power(field_ring(M), p), k) = k",
						By(characteristic, subfieldK, perfect, perfect_field.PerfectSubfieldPowers.Read(M).At(k, p)))
					u, found := b.ObtainAs[A](
						"the descent from s finds a parameter u outside the p-th powers of K",
						"∃u:A. "+
							"    u ∈ K ∧ "+
							"    ¬algebraic_over(M, k, u) ∧ "+
							"    finite_extension(M, field_adjoin(M, k, {u}), K) ∧ "+
							"    u ∉ image(frobenius_power(field_ring(M), p), K)",
						By(
							characteristic,
							subfieldK,
							subfieldTop,
							kInK,
							sInK,
							transcendental,
							finite,
							Read(descent, M).At(k, K, p, s)))
					parts := b.Conjuncts(
						found,
						"u lies in K",
						"u is transcendental over k",
						"K is finite over k(u)",
						"u is outside the p-th powers of K")
					uInK, uTranscendental, uFinite, uOutside := parts[0], parts[1], parts[2], parts[3]
					separable := b.Have(
						"so u separates K",
						"∀x:A. x ∈ K ⇒ separable_over(M, field_adjoin(M, k, {u}), x)",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xInK := c.Assume()
							c.Show(
								"u lies outside the p-th powers of K",
								By(
									characteristic,
									subfieldK,
									subfieldTop,
									fixed,
									kInK,
									uInK,
									uFinite,
									uOutside,
									xInK,
									SeparableOffPowerSubfield.Read(M).At(k, K, u, x, p)))
						}))
					b.Take(u)
					b.Show(
						"u lies in K, and K is finite and separable over k(u)",
						By(uInK, uTranscendental, uFinite, separable))
				})
		})
	}),
})}
