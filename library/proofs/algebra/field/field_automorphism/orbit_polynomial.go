// orbit_polynomial.go — a finite orbit as the roots of a polynomial over the fixed field.

package field_automorphism

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// FiniteOrbitPolynomial — a finite automorphism orbit is the root set of
// a polynomial over the fixed field, separable and split over M: multiply
// its distinct linear factors and use invariance of the finite product to
// fix every coefficient.
var FiniteOrbitPolynomial = finiteOrbitPolynomialThm{family.Add(registry.ProofEntry{
	Name: "FiniteOrbitPolynomial",
	Key:  "prop_e4d6f2a04d232366",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀M:set(A). ∀H:set(permutation(A)). ∀x:A.",
		Hypotheses: []string{
			"subfield(L, M)", "finite(H)", "subgroup(permutation_group, H)",
			"H ⊆ field_automorphisms(L, ∅, M)", "x ∈ M",
		},
		Conclusion: "∃p:(num → A). " +
			"    polynomial_over(L.zero, fixed_field(M, H), p) ∧ " +
			"    polynomial_separable(restrict_ring(field_ring(L), M), p) ∧ " +
			"    polynomial_splits(restrict_ring(field_ring(L), M), p) ∧ " +
			"    polynomial_roots(L.add, L.zero, L.mul, L.one, M, p) = «orbit»(H, x)",
		Abbrev: Abbrev{
			{Name: "line", Text: "λF:field_ops(A). λa:A. " +
				"    vec_sub(F.sub, " +
				"        basis_vector(F.zero, F.one, 1), " +
				"        vec_scalar_mul(F.mul, a, basis_vector(F.zero, F.one, 0)))"},
			{Name: "product", Text: "λF:field_ops(A). λS:set(A). " +
				"    module_sum(polynomial_mul(F.add, F.zero, F.mul), " +
				"        basis_vector(F.zero, F.one, 0), " +
				"        S, " +
				"        λa:A. «line»(F, a))"},
			{Name: "mapped", Text: "λh:(A → A). λp:(num → A). λi:num. h(p(i))"},
			{Name: "orbit", Text: "λH:set(permutation(A)). λx:A. " +
				"    image(λp:permutation(A). permutation_map(p, x), H)"},
			{Name: "polynomials", Text: "λF:field_ops(A). " +
				"    {p:(num → A) | polynomial_over(F.zero, F.carrier, p)}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		linearCoefficients := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀a:A. ∀n:num.", Hypotheses: []string{"a ∈ F.carrier"},
			Conclusion: "«line»(F, a, n) = COND(n = 0, -a, COND(n = 1, F.one, F.zero))",
		}, func(b *Argument, F field.FieldFact[on.F], a *Member[A, on.F], n *Expr[Nat]) {
			b.Do(Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)))
			b.Cases(b.TermAs[Bool]("n = 0"))
			b.When(
				"the constant coefficient is minus the root",
				func(c *Argument, zero Fact) {
					c.Show(
						"the constant coefficient has the claimed value",
						zero.Subst(),
						ByArith(F, a))
				})
			b.Otherwise(
				"the remaining coefficients have their linear-factor values",
				func(c *Argument, nonzero Fact) {
					c.Cases(c.TermAs[Bool]("n = 1"))
					c.When(
						"the leading coefficient is one",
						func(d *Argument, one Fact) {
							d.Show(
								"the linear coefficient has the claimed value",
								one.Subst(),
								ByArith(F, a))
						})
					c.Otherwise(
						"all higher coefficients are zero",
						func(d *Argument, notOne Fact) {
							d.Show(
								"the higher coefficient vanishes",
								ByArith(F, nonzero, notOne, a))
						})
				})
		})
		mapOne := ctx.Lemma(Statement{
			Binders:    "∀F:field_on(A). ∀h:(A → A).",
			Hypotheses: []string{"ring_homomorphism(field_ring(F), field_ring(F), h)"},
			Conclusion: "«mapped»(h, basis_vector(0)) = basis_vector(0)",
		}, func(b *Argument, F field.FieldFact[on.F], h *Arrow[A, A], hom Fact) {
			b.Do(Funext())
			b.FixAs[Nat]("i")
			b.Show(
				"a unital homomorphism fixes the coefficients of one",
				Simp(Fwd(vec_space.BasisVectorDef)),
				By(ring_homomorphism.MapZero.Read(hom), ring_homomorphism.MapOne.Read(hom)))
		})
		mapLinear := ctx.Lemma(Statement{
			Binders:    "∀F:field_on(A). ∀h:(A → A). ∀a:A.",
			Hypotheses: []string{"ring_homomorphism(field_ring(F), field_ring(F), h)", "a ∈ F.carrier"},
			Conclusion: "«mapped»(h, «line»(F, a)) = «line»(F, h(a))",
		}, func(b *Argument, F field.FieldFact[on.F], h *Arrow[A, A], a *Member[A, on.F], hom Fact) {
			b.Do(Funext())
			i := b.FixAs[Nat]("i")
			Ft := b.TermAs[FieldOps[A]]("F")
			b.Show(
				"the homomorphism carries the constant and leading coefficients to those of the image factor",
				By(
					Normalized,
					F,
					a,
					ring_homomorphism.MapIn.Read(hom).AsFact().At(a),
					At(linearCoefficients, Ft, a, i),
					At(linearCoefficients, Ft, h.Apply(a), i),
					ring_homomorphism.MapZero.Read(hom),
					ring_homomorphism.MapOne.Read(hom),
					ring_homomorphism.MapNeg.Read(hom).AsFact().At(a)))
		})
		mapMul := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀h:(A → A). ∀u v:(num → A).",
			Hypotheses: []string{
				"ring_homomorphism(field_ring(F), field_ring(F), h)",
				"polynomial_over(F.carrier, u)",
				"polynomial_over(F.carrier, v)",
			},
			Conclusion: "«mapped»(h, polynomial_mul(u, v)) = polynomial_mul(«mapped»(h, u), «mapped»(h, v))",
		}, func(
			b *Argument,
			F field.FieldFact[on.F],
			h *Arrow[A, A],
			u, v *Arrow[Nat, A],
			hypotheses Fact,
		) {
			Ft := b.TermAs[FieldOps[A]]("F")
			b.Show(
				"coefficient maps preserve polynomial multiplication",
				By(
					field.CarrierSubfield.Read(F),
					hypotheses,
					algebraic_element.FieldEmbeddingPolynomials.At(Ft, Ft, h, b.TermAs[Set[A]]("F.carrier"), u)))
		})
		permutationInjective := ctx.Lemma(
			"∀S:set(A). ∀q:permutation(A). injective_on(S, permutation_map(q))",
			func(b *Argument, S *Expr[Set[A]], q *Expr[Permutation[A]]) {
				b.Show(
					"a permutation is injective on every set",
					BySets(symmetric_group.MapBijective.At(q), functions.InjectiveOnDef))
			})
		orbitStable := ctx.Lemma(Statement{
			Binders:    "∀H:set(permutation(A)). ∀x:A. ∀q:permutation(A).",
			Hypotheses: []string{"finite(H)", "subgroup(permutation_group, H)", "q ∈ H"},
			Conclusion: "image(permutation_map(q), «orbit»(H, x)) = «orbit»(H, x)",
		}, func(
			b *Argument,
			H *Expr[Set[Permutation[A]]],
			x *Expr[A],
			q *Expr[Permutation[A]],
			hypotheses Fact,
		) {
			O, oDef := b.LetAs[Set[A]]("O", "«orbit»(H, x)")
			qm := b.TermAs[Fun[A, A]]("permutation_map(q)")
			finite := b.Have(
				"a finite group has a finite orbit",
				"finite(O)",
				By(
					Normalized,
					oDef,
					hypotheses,
					finite_set.FiniteImage.At(
						b.TermAs[Fun[Permutation[A], A]]("λp:permutation(A). permutation_map(p, x)"), H)))
			forward := b.Have(
				"composition carries every orbit point into the orbit",
				"∀p:permutation(A). p ∈ H ⇒ permutation_map(q, permutation_map(p, x)) ∈ O",
				Derive(func(c *Argument) {
					p := c.FixAs[Permutation[A]]("p")
					pIn := c.Assume()
					c.Show(
						"the composite belongs to the subgroup",
						BySets(
							oDef,
							pIn,
							hypotheses,
							group.SubgroupMul.At(c.TermAs[group.GroupOps[Permutation[A]]]("permutation_group"), H, q, p),
							symmetric_group.MapCompose.At(q, p, x)))
				}))
			subset := b.Have(
				"the orbit image is contained in the orbit",
				"image(permutation_map(q), O) ⊆ O",
				BySets(forward, oDef))
			b.Show(
				"an injective self-map of a finite set is onto",
				By(
					finite,
					At(permutationInjective, O, q),
					subset,
					cardinality.CardImageInj.At(qm, O),
					cardinality.CardSubsetEq.At(b.TermAs[Set[A]]("image(permutation_map(q), O)"), O)))
		})
		mapProduct := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀h:(A → A). ∀S:set(A).",
			Hypotheses: []string{
				"ring_homomorphism(field_ring(F), field_ring(F), h)",
				"finite(S)",
				"S ⊆ F.carrier",
				"injective_on(S, h)",
			},
			Conclusion: "«mapped»(h, «product»(F, S)) = «product»(F, image(h, S))",
		}, func(b *Argument, F field.FieldFact[on.F], h *Arrow[A, A], S *Expr[Set[A]], hypotheses Fact) {
			given := b.Conjuncts(
				hypotheses,
				"h is a ring homomorphism",
				"S is finite",
				"S lies in F",
				"h is injective on S")
			Ft := b.TermAs[FieldOps[A]]("F")
			monoid := comm_ring.MulMonoidOn.Read(polynomial.PolynomialRingOn.Read(field.RingOn.Read(F)))
			one := b.Have(
				"the coefficient map fixes the empty product",
				"«mapped»(h, basis_vector(0)) = basis_vector(0)",
				By(F, given[0], At(mapOne, Ft, h)))
			multiplicative := b.Have(
				"the coefficient map is multiplicative on the polynomial ring",
				Statement{
					Binders: "∀u v:(num → A).", Hypotheses: []string{"u ∈ «polynomials»(F)", "v ∈ «polynomials»(F)"},
					Conclusion: "«mapped»(h, polynomial_mul(u, v)) = polynomial_mul(«mapped»(h, u), «mapped»(h, v))",
				},
				Derive(func(c *Argument) {
					u := c.FixAs[Fun[Nat, A]]("u")
					v := c.FixAs[Fun[Nat, A]]("v")
					inRing := c.Assume()
					c.Show(
						"naturality applies to these polynomials",
						By(F, inRing, given[0], At(mapMul, Ft, h, u, v)))
				}))
			factors := b.Have(
				"the original and mapped linear factors lie in the polynomial ring",
				"∀a:A. a ∈ S ⇒ «line»(F, a) ∈ «polynomials»(F) ∧ «line»(F, h(a)) ∈ «polynomials»(F)",
				BySets(
					ring_homomorphism.MapIn.Read(given[0]),
					polynomial_roots.LinearFactor.Read(field.RingOn.Read(F)),
					given[2]))
			operation := b.TermAs[Op[Fun[Nat, A]]]("polynomial_mul(F.add, F.zero, F.mul)")
			unit := b.TermAs[Fun[Nat, A]]("basis_vector(F.zero, F.one, 0)")
			line := b.TermAs[Fun[A, Fun[Nat, A]]]("λa:A. «line»(F, a)")
			mappedFold := b.Have(
				"a multiplicative coefficient map commutes with the finite product",
				"«mapped»(h, «product»(F, S)) = "+
					"module_sum(polynomial_mul(F.add, F.zero, F.mul), "+
					"    basis_vector(0), "+
					"    S, "+
					"    λa:A. «mapped»(h, «line»(F, a)))",
				BySets(
					Normalized,
					given[1],
					factors,
					multiplicative,
					one,
					module.ModuleSumMonoidHomomorphism.Read(monoid).At(
						operation, unit, b.TermAs[Fun[Fun[Nat, A], Fun[Nat, A]]]("λp:(num → A). «mapped»(h, p)"), S, line)))
			mappedFactor := b.Have(
				"each factor maps to the factor at its image root",
				"∀a:A. a ∈ S ⇒ «mapped»(h, «line»(F, a)) = «line»(F, h(a))",
				Derive(func(c *Argument) {
					a := c.FixAs[A]("a")
					inS := c.Assume()
					c.Show(
						"the linear coefficient formula is natural",
						BySets(F, inS, given[2], given[0], At(mapLinear, Ft, h, a)))
				}))
			b.Show(
				"reindex the product by the injective image map",
				CalcEq(
					Leg(
						b.TermAs[Fun[Nat, A]](
							"module_sum(polynomial_mul(F.add, F.zero, F.mul), "+
								"    basis_vector(0), "+
								"    S, "+
								"    λa:A. «mapped»(h, «line»(F, a)))"),
						"map the product factor by factor",
						By(mappedFold)),
					Leg(
						b.TermAs[Fun[Nat, A]](
							"module_sum(polynomial_mul(F.add, F.zero, F.mul), basis_vector(0), S, λa:A. «line»(F, h(a)))"),
						"replace each mapped factor by its image factor",
						By(mappedFactor, module.ModuleSumCongruence)),
					FinalLeg(
						"an injective reindexing gives the product over the image",
						BySets(
							Normalized,
							given[1],
							factors,
							given[3],
							module.ModuleSumImageMonoid.Read(monoid).At(S, h, line)))))
		})
		return ctx.Theorem(headline, func(
			b *Argument,
			L field.FieldFact[on.L],
			M *Expr[Set[A]],
			H *Expr[Set[Permutation[A]]],
			x *Expr[A],
			hypotheses Fact,
		) {
			given := b.Conjuncts(
				hypotheses,
				"M is a subfield",
				"H is finite",
				"H is a subgroup",
				"H consists of automorphisms of M",
				"x lies in M")
			F, fDef := b.LetAs[FieldOps[A]]("F", "restrict_field(L, M)")
			O, oDef := b.LetAs[Set[A]]("O", "«orbit»(H, x)")
			P, pDef := b.LetAs[Fun[Nat, A]]("P", "«product»(F, O)")
			fieldF := b.Have(
				"the restriction to M is a field",
				"field_on(F)",
				By(Normalized, fDef, given[0], field.SubfieldFieldOn.Read(L).At(M)))
			finite := b.Have(
				"the orbit is finite",
				"finite(O)",
				By(
					Normalized,
					given[1],
					oDef,
					finite_set.FiniteImage.At(
						b.TermAs[Fun[Permutation[A], A]]("λq:permutation(A). permutation_map(q, x)"), H)))
			preservesM := b.Have(
				"every element of H permutes M",
				"H ⊆ symmetric_group(M)",
				Derive(func(c *Argument) {
					opened := c.Unfolded(given[3], FieldAutomorphismsDef)
					c.Show(
						"automorphisms belong to the symmetric group of M",
						BySets(opened))
				}))
			orbitInM := b.Have(
				"every orbit point lies in M",
				"O ⊆ M",
				BySets(oDef, given[4], preservesM, symmetric_group.SymmetricGroupMapsInto))
			orbitInF := b.Have(
				"the orbit lies in the restricted field",
				"O ⊆ F.carrier",
				Simp(Fwd(fDef), Fwd(field.RestrictFieldDef), Fwd(field.FieldCarrierDef)),
				By(orbitInM))
			properties := b.Have(
				"the distinct orbit product is separable and split with exactly the orbit as roots",
				"polynomial_over(F.zero, F.carrier, P) ∧ "+
					"polynomial_separable(field_ring(F), P) ∧ "+
					"polynomial_splits(field_ring(F), P) ∧ "+
					"polynomial_roots(F.add, F.zero, F.mul, F.one, F.carrier, P) = O",
				By(Normalized, fieldF, finite, pDef, orbitInF, separable_polynomial.DistinctLinearProduct.At(F, O)))
			overM := b.Have(
				"the same facts, spelled in the operations of L on M",
				"polynomial_over(L.zero, M, P) ∧ "+
					"polynomial_separable(restrict_ring(field_ring(L), M), P) ∧ "+
					"polynomial_splits(restrict_ring(field_ring(L), M), P) ∧ "+
					"polynomial_roots(L.add, L.zero, L.mul, L.one, M, P) = O",
				properties.Simp(Fwd(fDef), Rev(field.RestrictFieldRing)),
				By(properties))
			fixed := b.Have(
				"every automorphism in H fixes the orbit product coefficientwise",
				"∀q:permutation(A). q ∈ H ⇒ «mapped»(permutation_map(q), P) = P",
				Derive(func(c *Argument) {
					q := c.FixAs[Permutation[A]]("q")
					qIn := c.Assume()
					automorphism := c.Have(
						"q is an automorphism of M",
						"q ∈ field_automorphisms(L, ∅, M)",
						BySets(qIn, given[3]))
					qm := c.TermAs[Fun[A, A]]("permutation_map(q)")
					hom := c.Have(
						"q induces a ring homomorphism of the restricted field",
						"ring_homomorphism(field_ring(F), field_ring(F), permutation_map(q))",
						By(
							Normalized,
							fDef,
							automorphism,
							given[0],
							AutomorphismRingHomomorphism.Read(L).At(c.TermAs[Set[A]]("∅"), M, q)))
					stable := c.Have(
						"q maps the orbit onto itself",
						"image(permutation_map(q), O) = O",
						By(Normalized, given[1], oDef, qIn, given[2], At(orbitStable, H, x, q)))
					c.Show(
						"naturality and orbit stability fix the product",
						By(
							Normalized,
							fieldF,
							finite,
							stable,
							pDef,
							At(permutationInjective, O, q),
							orbitInF,
							hom,
							At(mapProduct, F, qm, O)))
				}))
			coefficients := b.Have(
				"every coefficient of P lies in the fixed field",
				"∀i:num. P(i) ∈ fixed_field(M, H)",
				BySets(
					fixed,
					overM,
					polynomial.PolynomialOverDef.At(b.TermAs[A]("L.zero"), M, P),
					FixedFieldDef.At(M, H)))
			overFixed := b.Have(
				"P is a polynomial over the fixed field",
				"polynomial_over(L.zero, fixed_field(M, H), P)",
				By(
					coefficients,
					overM,
					polynomial.PolynomialOverDef.At(b.TermAs[A]("L.zero"), M, P),
					polynomial.PolynomialOverDef.At(b.TermAs[A]("L.zero"), b.TermAs[Set[A]]("fixed_field(M, H)"), P)))
			b.Take(P)
			b.Show(
				"the orbit product witnesses the required polynomial",
				By(oDef, overM, overFixed))
		})
	}),
})}
