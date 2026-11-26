// fixed_field_galois.go — the fixed-field criteria for a Galois extension:
// a finite extension is Galois exactly when its automorphisms fix K alone,
// exactly when they number its degree, and a field is Galois over the
// field a finite group of its automorphisms fixes.

package galois_correspondence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// GaloisIffFixed — a finite extension is Galois exactly when the field
// its automorphisms fix is K.
var GaloisIffFixed = galoisIffFixedThm{family.Add(registry.ProofEntry{
	Name: "GaloisIffFixed",
	Key:  "prop_100171f500fb5560",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"K ⊆ M",
			"finite_extension(L, K, M)",
		},
		Conclusion: "galois_over(L, K, M) ⇔ fixed_field(M, field_automorphisms(L, K, M)) = K",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			fixedConjugate := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K M:set(A). ∀a b:A.",
				Hypotheses: []string{
					"subfield(L, K)",
					"subfield(L, M)",
					"K ⊆ M",
					"finite_extension(L, K, M)",
					"normal_over(L, K, M)",
					"a ∈ fixed_field(M, field_automorphisms(L, K, M))",
					"b ∈ M",
					"polynomial_eval(minimal_polynomial(L, K, a), b) = L.zero",
				},
				Conclusion: "b = a",
			},
				func(arg *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], a, b *Expr[A], h Fact) {
					arg.Show(
						"an automorphism sends a to b and fixes a",
						BySets(
							h,
							ConjugateAutomorphism.Read(L).At(K, M, a, b),
							field_automorphism.FixedFieldDef.At(
								M, arg.TermAs[Set[Permutation[A]]]("field_automorphisms(L, K, M)"))),
					)
				})
			fixedMember := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K M:set(A). ∀a:A.",
				Hypotheses: []string{
					"subfield(L, K)",
					"subfield(L, M)",
					"K ⊆ M",
					"finite_extension(L, K, M)",
					"galois_over(L, K, M)",
					"a ∈ fixed_field(M, field_automorphisms(L, K, M))",
				},
				Conclusion: "a ∈ K",
			},
				func(arg *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], a *Expr[A], h Fact) {
					aInM := arg.Have(
						"a fixed element belongs to M",
						"a ∈ M",
						BySets(
							h,
							field_automorphism.FixedFieldDef.At(
								M, arg.TermAs[Set[Permutation[A]]]("field_automorphisms(L, K, M)"))),
					)
					aInL := arg.Have(
						"the element belongs to the ambient field",
						"a ∈ L.carrier",
						BySets(aInM, h, field.SubfieldSubset.At(arg.TermAs[FieldOps[A]]("L"), M)),
					)
					ambientField := arg.TermAs[FieldOps[A]]("L")
					minimalPolynomial := arg.TermAs[Fun[Nat, A]]("minimal_polynomial(L, K, a)")
					ambientMember := arg.MemberOf[on.L](a, aInL)
					algebraic := arg.Have(
						"finiteness makes the element algebraic over K",
						"algebraic_over(L, K, a)",
						By(aInM, h, algebraic_element.FiniteExtensionAlgebraic.Read(L).At(K, M, a)),
					)
					rootsSingleton := arg.Have(
						"every conjugate is the fixed element itself",
						"polynomial_roots(M, minimal_polynomial(L, K, a)) = {a}",
						BySets(
							aInM,
							aInL,
							algebraic,
							h,
							At(fixedConjugate, ambientField, K, M, a),
							GaloisOverDef.At(ambientField, K, M),
							algebraic_element.MinimalPolynomialSpec.Read(L).At(K, ambientMember),
							polynomial_roots.PolynomialRootsDef.At(
								arg.TermAs[Op[A]]("L.add"),
								arg.TermAs[A]("L.zero"),
								arg.TermAs[Op[A]]("L.mul"),
								arg.TermAs[A]("L.one"),
								M,
								minimalPolynomial)),
					)
					degreeOne := arg.Have(
						"the conjugate count gives degree one",
						"polynomial_degree(minimal_polynomial(L, K, a)) = 1",
						By(
							Normalized,
							rootsSingleton,
							aInM,
							h,
							GaloisOverDef.At(ambientField, K, M),
							ConjugatesCount.Read(L).At(K, M, a),
							cardinality.HasSizeDef.At(
								arg.TermAs[Set[A]]("{a}"), arg.TermAs[Nat]("polynomial_degree(minimal_polynomial(L, K, a))")),
							cardinality.CardSing.At(a)),
					)
					adjoinDegreeOne := arg.Have(
						"adjoining the element gives a degree-one extension",
						"finite_extension(L, K, field_adjoin(L, K, {a})) ∧ "+
							"extension_degree(L, K, field_adjoin(L, K, {a})) = 1",
						By(degreeOne, aInL, algebraic, h, algebraic_element.AdjoinDegree.Read(L).At(K, ambientMember)),
					)
					arg.Show(
						"a degree-one adjunction is K itself",
						By(
							h,
							adjoinDegreeOne,
							algebraic_element.AdjoinElementSubfield.Read(L).At(K, ambientMember),
							field_extension.DegreeOneIff.Read(L).At(K, arg.TermAs[Set[A]]("field_adjoin(L, K, {a})"))),
					)
				})
			descendSeparable := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K M:set(A). ∀p:(num → A). ∀a:A.",
				Hypotheses: []string{
					"subfield(L, K)",
					"subfield(L, M)",
					"K ⊆ M",
					"polynomial_over(K, p)",
					"polynomial_irreducible(restrict_ring(field_ring(L), K), p)",
					"polynomial_separable(restrict_ring(field_ring(L), M), p)",
					"a ∈ M",
					"polynomial_eval(p, a) = L.zero",
				},
				Conclusion: "polynomial_separable(restrict_ring(field_ring(L), K), p)",
			},
				func(
					arg *Argument,
					L field.FieldFact[on.L],
					K, M *Expr[Set[A]],
					p *Arrow[Nat, A],
					a *Expr[A],
					h Fact,
				) {
					mField := arg.Have(
						"M is a field with the restricted operations",
						"field_on(restrict_field(L, M))",
						By(h, field.SubfieldFieldOn.Read(L).At(M)),
					)
					overM := arg.Have(
						"the coefficients in K also lie in M",
						"polynomial_over(M, p)",
						By(h, polynomial.PolynomialOverMono.At(arg.TermAs[A]("L.zero"), K, M, p)),
					)
					inRestrictedField := arg.Have(
						"the element belongs to the restricted field",
						"a ∈ restrict_field(L, M).carrier",
						By(h))
					restrictedMember := arg.MemberOf[on.Any](a, inRestrictedField)
					simpleRoot := arg.Have(
						"separability over M makes the root simple",
						"polynomial_eval(polynomial_derivative(p), a) ≠ L.zero",
						By(
							h,
							overM,
							separable_polynomial.SeparableRootSimple.Read(mField).At(p, restrictedMember),
							field.RestrictFieldRing.At(arg.TermAs[FieldOps[A]]("L"), M)),
					)
					derivativeNonzero := arg.Have(
						"a derivative nonzero at a root is not the zero polynomial",
						"polynomial_derivative(p) ≠ vec_zero",
						By(
							simpleRoot,
							h,
							polynomial_evaluation.EvalVecZero.Read(field.RingOn.Read(mField)).At(restrictedMember)),
					)
					kField := arg.Have(
						"K is a field with the restricted operations",
						"field_on(restrict_field(L, K))",
						By(h, field.SubfieldFieldOn.Read(L).At(K)),
					)
					kRing := arg.Simplified(field.RestrictFieldRing.At(arg.TermAs[FieldOps[A]]("L"), K))
					arg.Show(
						"the nonzero derivative gives separability over K",
						kRing.Rw(),
						By(derivativeNonzero, h, separable_polynomial.SeparableIffDerivative.Read(kField).At(p)),
					)
				})
			minimalFromPolynomial := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K M:set(A). ∀a:A. ∀p:(num → A).",
				Hypotheses: []string{
					"subfield(L, K)",
					"subfield(L, M)",
					"K ⊆ M",
					"finite_extension(L, K, M)",
					"a ∈ M",
					"polynomial_over(K, p)",
					"polynomial_separable(restrict_ring(field_ring(L), M), p)",
					"polynomial_splits(restrict_ring(field_ring(L), M), p)",
					"polynomial_eval(p, a) = L.zero",
				},
				Conclusion: "polynomial_splits(restrict_ring(field_ring(L), M), minimal_polynomial(L, K, a)) ∧ " +
					"separable_over(L, K, a)",
			},
				func(
					arg *Argument,
					L field.FieldFact[on.L],
					K, M *Expr[Set[A]],
					a *Expr[A],
					p *Arrow[Nat, A],
					h Fact,
				) {
					aInL := arg.Have(
						"the element belongs to the ambient field",
						"a ∈ L.carrier",
						BySets(h, field.SubfieldSubset.At(arg.TermAs[FieldOps[A]]("L"), M)),
					)
					minimalPolynomial := arg.TermAs[Fun[Nat, A]]("minimal_polynomial(L, K, a)")
					ambientMember := arg.MemberOf[on.L](a, aInL)
					algebraic := arg.Have(
						"finiteness makes the element algebraic over K",
						"algebraic_over(L, K, a)",
						By(h, algebraic_element.FiniteExtensionAlgebraic.Read(L).At(K, M, a)),
					)
					minimalSpec := arg.Have(
						"the minimal polynomial lies over K and vanishes at a",
						"polynomial_over(K, minimal_polynomial(L, K, a)) ∧ "+
							"polynomial_eval(minimal_polynomial(L, K, a), a) = L.zero",
						By(aInL, algebraic, h, algebraic_element.MinimalPolynomialSpec.Read(L).At(K, ambientMember)),
					)
					irreducible := arg.Have(
						"the minimal polynomial is irreducible over K",
						"polynomial_irreducible(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, a))",
						By(aInL, algebraic, h, algebraic_element.MinimalPolynomialIrreducible.Read(L).At(K, ambientMember)),
					)
					dividesK := arg.Have(
						"the minimal polynomial divides p over K",
						"polynomial_divides(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, a), p)",
						By(aInL, algebraic, h, algebraic_element.MinimalPolynomialDivides.Read(L).At(K, ambientMember, p)),
					)
					dividesM := arg.Have(
						"the divisibility passes to M",
						"polynomial_divides(restrict_ring(field_ring(L), M), minimal_polynomial(L, K, a), p)",
						By(
							dividesK,
							h,
							module_record.RestrictRingTwice.At(arg.TermAs[module_record.RingOps[A]]("field_ring(L)"), M, K),
							polynomial_division.DividesMono.At(
								arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), M)"), K, minimalPolynomial, p)),
					)
					minimalOverM := arg.Have(
						"the minimal polynomial also has its coefficients in M",
						"polynomial_over(M, minimal_polynomial(L, K, a))",
						By(
							minimalSpec,
							h,
							polynomial.PolynomialOverMono.At(arg.TermAs[A]("L.zero"), K, M, minimalPolynomial)),
					)
					mField := arg.Have(
						"M is a field with the restricted operations",
						"field_on(restrict_field(L, M))",
						By(h, field.SubfieldFieldOn.Read(L).At(M)),
					)
					mRing := arg.Simplified(field.RestrictFieldRing.At(arg.TermAs[FieldOps[A]]("L"), M))
					separableM := arg.Have(
						"a divisor of the separable polynomial is separable over M",
						"polynomial_separable(restrict_ring(field_ring(L), M), minimal_polynomial(L, K, a))",
						mRing.Rw(),
						By(
							h,
							dividesM,
							minimalOverM,
							separable_polynomial.SeparableDivisor.Read(field.RingOn.Read(mField)).At(minimalPolynomial, p)),
					)
					separableK := arg.Have(
						"irreducibility and the simple root descend separability to K",
						"polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, a))",
						By(
							L,
							irreducible,
							separableM,
							h,
							minimalSpec,
							At(descendSeparable, arg.TermAs[FieldOps[A]]("L"), K, M, minimalPolynomial, a)),
					)
					arg.Show(
						"the element has a splitting minimal polynomial and is separable",
						SplitConj(
							Case(
								"the divisor of the splitting polynomial splits over M",
								mRing.Rw(),
								By(
									h,
									dividesM,
									separable_polynomial.SplitsDivisor.Read(field.RingOn.Read(mField)).At(minimalPolynomial, p)),
							),
							Case(
								"the element is separable over K",
								By(separableK, algebraic, SeparableOverDef.At(arg.TermAs[FieldOps[A]]("L"), K, a)),
							),
						),
					)
				})
			polynomialCriterion := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K M:set(A).",
				Hypotheses: []string{
					"subfield(L, K)",
					"subfield(L, M)",
					"K ⊆ M",
					"finite_extension(L, K, M)",
					"∀a:A. " +
						"    a ∈ M ⇒ " +
						"    ∃p:(num → A). " +
						"        polynomial_over(K, p) ∧ " +
						"        polynomial_separable(restrict_ring(field_ring(L), M), p) ∧ " +
						"        polynomial_splits(restrict_ring(field_ring(L), M), p) ∧ " +
						"        polynomial_eval(p, a) = L.zero",
				},
				Conclusion: "galois_over(L, K, M)",
			},
				func(a *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], h Fact) {
					minimalProperties := a.Have(
						"each element has a splitting minimal polynomial and is separable",
						Statement{
							Binders: "∀a:A.",
							Hypotheses: []string{
								"a ∈ M",
							},
							Conclusion: "polynomial_splits(restrict_ring(field_ring(L), M), minimal_polynomial(L, K, a)) ∧ " +
								"separable_over(L, K, a)",
						},
						By(Normalized, L, h, At(minimalFromPolynomial, a.TermAs[FieldOps[A]]("L"), K, M)),
					)
					normal := a.Have(
						"splitting of every minimal polynomial gives normality",
						"normal_over(L, K, M)",
						By(h, minimalProperties, NormalIffMinimalPolynomial.Read(L).At(K, M)),
					)
					a.Show(
						"normality, separability and finiteness give a Galois extension",
						By(minimalProperties, h, normal, GaloisOverDef.At(a.TermAs[FieldOps[A]]("L"), K, M)),
					)
				})
			orbitRoot := ctx.Lemma(Statement{
				Binders: "∀L:field_ops(A). ∀M:set(A). ∀H:set(permutation(A)). ∀a:A. ∀p:(num → A).",
				Hypotheses: []string{
					"subgroup(permutation_group, H)",
					"polynomial_roots(M, p) = image(λq:permutation(A). permutation_map(q, a), H)",
				},
				Conclusion: "polynomial_eval(p, a) = L.zero",
			}, func(
				arg *Argument,
				L *Expr[FieldOps[A]],
				M *Expr[Set[A]],
				H *Expr[Set[Permutation[A]]],
				a *Expr[A],
				p *Arrow[Nat, A],
				h Fact,
			) {
				parts := arg.Conjuncts(
					h,
					"H is a subgroup",
					"the roots are the images of a")
				identity := arg.Have(
					"H contains the identity permutation",
					"permutation_identity ∈ H",
					By(group.SubgroupOne.Read(parts[0])))
				arg.Show(
					"the identity image makes a a root",
					BySets(
						parts[1],
						identity,
						symmetric_group.MapIdentity.At(a),
						polynomial_roots.PolynomialRootsDef.At(
							arg.TermAs[Op[A]]("L.add"),
							arg.TermAs[A]("L.zero"),
							arg.TermAs[Op[A]]("L.mul"),
							arg.TermAs[A]("L.one"),
							M,
							p)))
			})

			return ctx.Theorem(headline,
				func(a *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], extension Fact) {
					a.Iff()
					a.Forward(
						"a Galois extension has fixed field K",
						func(b *Argument, galois Fact) {
							b.Show(
								"fixed elements lie in K and every element of K is fixed",
								BySets(
									extension,
									galois,
									At(fixedMember, b.TermAs[FieldOps[A]]("L"), K, M),
									field_automorphism.SubfieldFixed.Read(L).At(K, M)))
						})
					a.Backward(
						"the fixed-field hypothesis gives a Galois extension",
						func(b *Argument, fixed Fact) {
							H, hDef := b.LetAs[Set[Permutation[A]]]("H", "field_automorphisms(L, K, M)")
							finiteH := b.Have(
								"finiteness of the extension bounds its automorphisms",
								"finite(H)",
								By(Normalized, hDef, extension, field_automorphism.AutomorphismsBound.Read(L).At(K, M)))
							subgroup := b.Have(
								"the automorphisms fixing K form a subgroup",
								"subgroup(permutation_group, H)",
								By(Normalized, hDef, field_automorphism.AutomorphismsSubgroup.Read(L).At(K, M)))
							automorphisms := b.Have(
								"every member of H is an automorphism of M",
								"H ⊆ field_automorphisms(L, ∅, M)",
								By(
									Normalized,
									hDef,
									set_order.EmptySubset,
									field_automorphism.AutomorphismsAntitone.Read(L).At(b.TermAs[Set[A]]("∅"), K, M)))
							polynomials := b.Have(
								"each element is a root of a separable polynomial over K that splits over M",
								Statement{
									Binders:    "∀x:A.",
									Hypotheses: []string{"x ∈ M"},
									Conclusion: "∃p:(num → A). " +
										"    polynomial_over(K, p) ∧ " +
										"    polynomial_separable(restrict_ring(field_ring(L), M), p) ∧ " +
										"    polynomial_splits(restrict_ring(field_ring(L), M), p) ∧ " +
										"    polynomial_eval(p, x) = L.zero",
								},
								Derive(func(c *Argument) {
									x := c.FixAs[A]("x")
									inM := c.Assume()
									p, orbit := c.ObtainAs[Fun[Nat, A]](
										"the finite orbit of x gives a separable splitting polynomial p over the fixed field",
										"∃p:(num → A). "+
											"    polynomial_over(fixed_field(M, H), p) ∧ "+
											"    polynomial_separable(restrict_ring(field_ring(L), M), p) ∧ "+
											"    polynomial_splits(restrict_ring(field_ring(L), M), p) ∧ "+
											"    polynomial_roots(M, p) = image(λq:permutation(A). permutation_map(q, x), H)",
										By(
											finiteH,
											inM,
											subgroup,
											automorphisms,
											extension,
											field_automorphism.FiniteOrbitPolynomial.Read(L).At(M, H, x)))
									c.Take(p)
									c.Show(
										"the fixed field is K and the identity makes x a root",
										By(Normalized, fixed, subgroup, orbit, At(orbitRoot, c.TermAs[FieldOps[A]]("L"), M, H, x, p)))
								}))
							b.Show(
								"the polynomial criterion gives normality and separability",
								By(L, polynomials, extension, At(polynomialCriterion, b.TermAs[FieldOps[A]]("L"), K, M)))
						})
				})

		}),
})}

// GaloisIffCard — a finite extension is Galois exactly when it has as
// many automorphisms fixing K as its degree: Artin identifies the degree
// over the fixed field, and the tower law detects when that field is K.
var GaloisIffCard = galoisIffCardThm{family.Add(registry.ProofEntry{
	Name: "GaloisIffCard",
	Key:  "prop_52dcfb11020bf0c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"K ⊆ M",
			"finite_extension(L, K, M)",
		},
		Conclusion: "galois_over(L, K, M) ⇔ card(field_automorphisms(L, K, M)) = extension_degree(L, K, M)",
	},
		func(a *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], extension Fact) {
			H, hDef := a.LetAs[Set[Permutation[A]]]("H", "field_automorphisms(L, K, M)")
			E, eDef := a.LetAs[Set[A]]("E", "fixed_field(M, H)")
			finiteH := a.Have(
				"there are finitely many automorphisms fixing K",
				"finite(H)",
				By(Normalized, hDef, extension, field_automorphism.AutomorphismsBound.Read(L).At(K, M)))
			subgroupH := a.Have(
				"these automorphisms form a subgroup of the permutations",
				"subgroup(permutation_group, H)",
				By(Normalized, L, hDef, field_automorphism.AutomorphismsSubgroup))
			automorphisms := a.Have(
				"every member of H is an automorphism of M",
				"H ⊆ field_automorphisms(L, ∅, M)",
				By(
					Normalized,
					hDef,
					set_order.EmptySubset,
					field_automorphism.AutomorphismsAntitone.Read(L).At(a.TermAs[Set[A]]("∅"), K, M)))
			fixedSubfield := a.Have(
				"the fixed field E is a subfield of L",
				"subfield(L, E)",
				By(
					Normalized,
					eDef,
					extension,
					automorphisms,
					field_automorphism.FixedFieldSubfield.Read(L).At(M, H)))
			kInE := a.Have(
				"H fixes K, so K lies in E",
				"K ⊆ E",
				By(Normalized, hDef, eDef, extension, field_automorphism.SubfieldFixed.Read(L).At(K, M)))
			eInM := a.Have(
				"the fixed field lies in M",
				"E ⊆ M",
				BySets(eDef, field_automorphism.FixedFieldDef.At(M, H)))
			artinDegree := a.Have(
				"Artin gives a finite extension of E with degree the number of automorphisms",
				"finite_extension(L, E, M) ∧ extension_degree(L, E, M) = card(H)",
				By(
					Normalized,
					eDef,
					extension,
					finiteH,
					subgroupH,
					automorphisms,
					field_automorphism.ArtinFixedField.Read(L).At(M, H)))

			a.Iff()
			a.Forward(
				"a Galois extension has as many automorphisms as its degree",
				func(b *Argument, galois Fact) {
					fixed := b.Have(
						"the fixed field of a Galois extension is K",
						"E = K",
						By(Normalized, hDef, eDef, extension, galois, GaloisIffFixed.Read(L).At(K, M)))
					b.Show(
						"Artin's degree over E is therefore the degree over K",
						By(Normalized, fixed, artinDegree))
				})
			a.Backward(
				"equality of the number of automorphisms and degree forces the fixed field to be K",
				func(b *Argument, count Fact) {
					finiteE := b.Have(
						"E is finite over K as an intermediate field",
						"finite_extension(L, K, E)",
						By(extension, fixedSubfield, kInE, eInM, field_extension.TowerFinite.Read(L).At(K, E, M)))
					towerDegree := b.Have(
						"the degrees over K multiply through E",
						"extension_degree(L, K, M) = extension_degree(L, K, E) * extension_degree(L, E, M)",
						By(
							extension,
							fixedSubfield,
							kInE,
							eInM,
							finiteE,
							artinDegree,
							field_extension.TowerLaw.Read(L).At(K, E, M)))
					identityInH := b.Have(
						"the identity permutation belongs to H",
						"permutation_identity ∈ H",
						By(group.SubgroupOne.Read(subgroupH)))
					nonemptyH := b.Have(
						"so H is nonempty",
						"H ≠ ∅",
						By(
							Normalized,
							identityInH,
							set_basic.NotInEmpty.At(b.TermAs[Permutation[A]]("permutation_identity"))))
					nonzeroCount := b.Have(
						"a finite nonempty group has nonzero cardinality",
						"card(H) ≠ 0",
						By(Normalized, finiteH, nonemptyH, cardinality.CardEqZero.At(H)))
					cardH := b.TermAs[Nat]("card(H)")
					degreeE := b.TermAs[Nat]("extension_degree(L, K, E)")
					degreeOne := b.Have(
						"cancelling the nonzero number of automorphisms gives degree one over K",
						"extension_degree(L, K, E) = 1",
						By(
							Normalized,
							nonzeroCount,
							count,
							artinDegree,
							towerDegree,
							nat_arith.MulSym.At(degreeE, cardH),
							nat_arith.MulOne.At(cardH),
							nat_arith.MulEqLCancel.At(cardH, degreeE, b.TermAs[Nat]("1"))))
					fixed := b.Have(
						"a degree-one extension of K is K itself",
						"E = K",
						By(
							extension,
							fixedSubfield,
							kInE,
							finiteE,
							degreeOne,
							field_extension.DegreeOneIff.Read(L).At(K, E)))
					b.Show(
						"the fixed-field characterization now gives that M is Galois over K",
						By(Normalized, extension, hDef, eDef, fixed, GaloisIffFixed.Read(L).At(K, M)))
				})
		}),
})}

// FixedFieldGalois — M is Galois over the field F a finite group H of its
// automorphisms fixes: by Artin, M is finite over F and the automorphisms
// of M fixing F are H itself, whose fixed field is F, so the fixed-field
// criterion makes the extension Galois.
var FixedFieldGalois = fixedFieldGaloisThm{family.Add(registry.ProofEntry{
	Name: "FixedFieldGalois",
	Key:  "prop_2bfa9c2d3e5d5011",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀M:set(A). ∀H:set(permutation(A)).",
		Hypotheses: []string{
			"subfield(L, M)",
			"finite(H)",
			"subgroup(permutation_group, H)",
			"H ⊆ field_automorphisms(L, ∅, M)",
		},
		Conclusion: "galois_over(L, fixed_field(M, H), M)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			M *Expr[Set[A]],
			H *Expr[Set[Permutation[A]]],
			finiteGroup Fact,
		) {
			F := a.TermAs[Set[A]]("fixed_field(M, H)")
			inM := a.Have(
				"F lies in M",
				"fixed_field(M, H) ⊆ M",
				BySets(field_automorphism.FixedFieldDef.At(M, H)))
			a.Show(
				"Artin makes M finite over F and Aut_F(M) = H, whose fixed field is F: M is Galois over F",
				By(
					Normalized,
					finiteGroup,
					inM,
					field_automorphism.FixedFieldSubfield.Read(L).At(M, H),
					field_automorphism.ArtinFixedField.Read(L).At(M, H),
					field_automorphism.ArtinAutomorphisms.Read(L).At(M, H),
					GaloisIffFixed.Read(L).At(F, M)))
		}),
})}
