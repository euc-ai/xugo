package functional_dual

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_pairing"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// MultiplicationFunctionalBilinear — a K-linear functional on L turns the
// product of L into a K-bilinear map: fixing the first variable composes
// the functional with a multiplication of L, and commutativity carries that
// to the second variable.
var MultiplicationFunctionalBilinear = multiplicationFunctionalBilinearThm{family.Add(registry.ProofEntry{
	Name: "MultiplicationFunctionalBilinear",
	Key:  "prop_f22b09741ab28894",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀l:(A → A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"module_homomorphism(«ScalarK», «Regular», «VectorsK», l)",
		},
		Conclusion: "bilinear_map(«ScalarK», «Regular», «Regular», «VectorsK», λx:A. λy:A. l(x * y))",
	},
		func(a *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], l *Arrow[A, A], subK, linear Fact) {
			rK := a.TermAs[RingOps[A]]("«ScalarK»")
			vL := a.TermAs[module_record.ModuleOps[A, A]]("«Regular»")
			vK := a.TermAs[module_record.ModuleOps[A, A]]("«VectorsK»")
			fixedLeft := a.Have(
				"the functional after multiplication by x is K-linear in the second variable",
				"∀x:A. x ∈ L.carrier ⇒ module_homomorphism(«ScalarK», «Regular», «VectorsK», λy:A. l(x * y))",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.MemberOf[on.L](x, b.Assume())
					composite := b.Have(
						"compose multiplication by x with the functional",
						"module_homomorphism(«ScalarK», «Regular», «VectorsK», l ∘ L.mul(x))",
						By(
							subK,
							xIn,
							linear,
							field_extension.MultiplicationLinear.Read(L).At(K, xIn),
							module_homomorphism.HomCompose.At(rK, vL, vL, vK, b.TermAs[Fun[A, A]]("L.mul(x)"), l)))
					b.Show(
						"the composite is pairing with x",
						By(b.Simplified(composite, Fwd(functions.ComposeApply))))
				}))
			fixedRight := a.Have(
				"commutativity gives linearity in the first variable",
				"∀y:A. y ∈ L.carrier ⇒ module_homomorphism(«ScalarK», «Regular», «VectorsK», λx:A. l(x * y))",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					yIn := b.MemberOf[on.L](y, b.Assume())
					b.Show(
						"the two orders of multiplication agree on L",
						By(
							fixedLeft.At(y),
							yIn,
							comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(L))),
							module_homomorphism.HomCongruence.At(rK, vL, vK,
								b.TermAs[Fun[A, A]]("λx:A. l(y * x)"),
								b.TermAs[Fun[A, A]]("λx:A. l(x * y)"))))
				}))
			a.Show(
				"linearity in each variable is bilinearity",
				Unfold(module_homomorphism.BilinearMapDef),
				By(fixedLeft, fixedRight))
		}),
})}

// MultiplicationFunctionalNondegenerate — a nonzero linear functional gives
// a nondegenerate multiplication pairing: the product read through the
// functional is bilinear, and a nonzero u pairs with z/u to give the nonzero
// value l(z).
var MultiplicationFunctionalNondegenerate = multiplicationFunctionalNondegenerateThm{family.Add(registry.ProofEntry{
	Name: "MultiplicationFunctionalNondegenerate",
	Key:  "prop_425d5e4f0cfcf69a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀l:(A → A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"module_homomorphism(«ScalarK», «Regular», «VectorsK», l)",
			"∃x:A. x ∈ L.carrier ∧ l(x) ≠ L.zero",
		},
		Conclusion: "bilinear_pairing(«ScalarK», «Regular», λx:A. λy:A. l(x * y)) ∧ " +
			"pairing_nondegenerate(«ScalarK», «Regular», λx:A. λy:A. l(x * y))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			K *Expr[Set[A]],
			l *Arrow[A, A],
			subK, linear, nonzeroValue Fact,
		) {
			bilinear := a.Have(
				"a bilinear map into the scalars is a bilinear pairing",
				"bilinear_pairing(«ScalarK», «Regular», λx:A. λy:A. l(x * y))",
				Simp(Fwd(linear_pairing.BilinearPairingDef), Fwd(module_record.RegularModuleRestrict)),
				By(a.Simplified(
					GroupPremises(subK, linear, MultiplicationFunctionalBilinear.Read(L).At(K, l)),
					Fwd(module_homomorphism.BilinearMapDef))))
			z, zValue := a.UnpackAs[A](nonzeroValue, "z")
			zParts := a.Conjuncts(
				zValue,
				"z lies in L",
				"l is nonzero at z")
			zIn := a.MemberOf[on.L](z, zParts[0])
			detects := a.Have(
				"each nonzero u has a partner giving the value l(z)",
				"∀u:A. u ∈ L.carrier ∧ u ≠ L.zero ⇒ ∃v:A. v ∈ L.carrier ∧ l(u * v) ≠ L.zero",
				Derive(func(b *Argument) {
					u := b.FixAs[A]("u")
					uParts := b.Conjuncts(
						b.Assume(),
						"u lies in L",
						"u is nonzero")
					uIn := b.MemberOf[on.L](u, uParts[0])
					b.Take(b.TermAs[A]("z / u"))
					b.Show(
						"the quotient lies in L and its pairing value is nonzero",
						SplitConj(
							Case(
								"L holds the quotient z/u",
								By(field.DivIn.Read(L).At(zIn, uIn))),
							Case(
								"u times z/u is z, where l has its nonzero value",
								By(Normalized, uParts[1], zParts[1], field.DivLeftMulOn.Read(L).At(zIn, uIn)))))
				}))
			a.Show(
				"the multiplication pairing is bilinear and detects every nonzero vector",
				By(detects, bilinear, linear_pairing.PairingNondegenerateDef))
		}),
})}

// MultiplicationFunctionalDualBasis — a nonzero K-linear functional l on L
// gives every finite K-basis E of L a dual basis under l: the d(e) pair with E
// by l(d(e) * f) = δ(e, f), and each x of L is the sum over E of l(x * e) * d(e).
// The multiplication pairing is nondegenerate, and a nondegenerate pairing over
// the field K has a dual basis.
var MultiplicationFunctionalDualBasis = multiplicationFunctionalDualBasisThm{family.Add(registry.ProofEntry{
	Name: "MultiplicationFunctionalDualBasis",
	Key:  "prop_7f87277f3e0ad32e",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀l:(A → A). ∀E:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"module_homomorphism(«ScalarK», «Regular», «VectorsK», l)",
			"∃x:A. x ∈ L.carrier ∧ l(x) ≠ L.zero",
			"finite(E)",
			"module_basis(«ScalarK», «Regular», E)",
		},
		Conclusion: "∃d:(A → A). " +
			"    (∀e:A. e ∈ E ⇒ d(e) ∈ L.carrier) ∧ " +
			"    (∀e f:A. e ∈ E ∧ f ∈ E ⇒ l(d(e) * f) = COND(e = f, L.one, L.zero)) ∧ " +
			"    module_basis(«ScalarK», «Regular», image(d, E)) ∧ " +
			"    (∀x:A. x ∈ L.carrier ⇒ x = module_sum(L.add, L.zero, E, λe:A. l(x * e) * d(e)))",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		K *Expr[Set[A]],
		l *Arrow[A, A],
		E *Expr[Set[A]],
		subK, linear, nonzero, finiteE, basisK Fact,
	) {
		pairing := a.Conjuncts(
			GroupPremises(subK, linear, nonzero, MultiplicationFunctionalNondegenerate.Read(L).At(K, l)),
			"the pairing is bilinear",
			"the pairing is nondegenerate")
		fieldK := a.Have(
			"K is a field under the ambient operations",
			"field_on(restrict_field(L, K))",
			By(subK, field.SubfieldFieldOn.Read(L).At(K)))
		a.Show(
			"the multiplication pairing is nondegenerate over the field K, so E has a dual basis",
			By(
				module_homomorphism.HomSource.Read(linear),
				pairing[0],
				pairing[1],
				finiteE,
				basisK,
				linear_pairing.NondegeneratePairingDualBasis.Read(fieldK).At(
					a.TermAs[module_record.ModuleOps[A, A]]("«Regular»"),
					a.TermAs[Fun2[A, A, A]]("λx:A. λy:A. l(x * y)"),
					E),
				field.RestrictFieldRing.At(a.TermAs[FieldOps[A]]("L"), K)))
	}),
})}

// FunctionalCoordinates — for a nonzero functional l, the values z ↦ l(z * e)
// on a finite F-basis E of L are free coordinates on L: any values in F are
// taken by one element of L and no two elements agree on E. E has a basis d dual
// to it under the pairing l(x * y) (MultiplicationFunctionalDualBasis);
// Σ c(e) * d(e) takes the values c, and every element is recovered from its
// values through d.
var FunctionalCoordinates = functionalCoordinatesThm{family.Add(registry.ProofEntry{
	Name: "FunctionalCoordinates",
	Key:  "prop_65f423205a1f7eaa",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀F:set(A). ∀l:(A → A). ∀E:set(A).",
		Hypotheses: []string{
			"subfield(L, F)",
			"«functional»",
			"∃x:A. x ∈ L.carrier ∧ l(x) ≠ L.zero",
			"finite(E)",
			"module_basis(«rings»(F), regular_module(field_ring(L)), E)",
		},
		Conclusion: "(∀c:(A → A). " +
			"    (∀e:A. e ∈ E ⇒ c(e) ∈ F) ⇒ ∃z:A. z ∈ L.carrier ∧ (∀e:A. e ∈ E ⇒ l(z * e) = c(e))) ∧ " +
			"(∀u v:A. u ∈ L.carrier ∧ v ∈ L.carrier ∧ (∀e:A. e ∈ E ⇒ l(u * e) = l(v * e)) ⇒ u = v)",
		Abbrev: Abbrev{
			{Name: "rings", Text: "restrict_ring(field_ring(L))"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(L)))"},
			{Name: "functional", Text: "module_homomorphism(«rings»(F), " +
				"    regular_module(field_ring(L)), " +
				"    «vectors»(F), " +
				"    l)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			F *Expr[Set[A]],
			l *Arrow[A, A],
			E *Expr[Set[A]],
			subfieldF, linear, nonzero, finiteE, basisE Fact,
		) {
			opsF := a.TermAs[RingOps[A]]("«rings»(F)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			scalars := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(F)")
			add, zero := a.TermAs[Op[A]]("L.add"), a.TermAs[A]("L.zero")
			moduleL := a.Have(
				"L is a module over F",
				"module_on(«rings»(F), regular_module(field_ring(L)))",
				By(module_homomorphism.HomSource.Read(linear)))
			_, dual := a.UnpackAs[Fun[A, A]](
				GroupPremises(
					subfieldF, linear, nonzero, finiteE, basisE, MultiplicationFunctionalDualBasis.Read(L).At(F, l, E)),
				"d")
			parts := a.Conjuncts(
				dual,
				"d takes E into L",
				"d is dual to E",
				"its image is a basis of L over F",
				"each element is expanded through d by its values")
			dualInL, deltas, expansion := parts[0], parts[1], parts[3]
			fixedRight := a.Conjuncts(
				a.Unfolded(
					GroupPremises(subfieldF, linear, MultiplicationFunctionalBilinear.Read(L).At(F, l)),
					module_homomorphism.BilinearMapDef),
				"with the first variable fixed, the pairing is F-linear",
				"with the second variable fixed, it is F-linear")[1]
			independent := a.Conjuncts(
				a.Unfolded(basisE, linear_independence.ModuleBasisDef),
				"E is independent over F",
				"E spans L over F")[0]
			basisInL := a.Have(
				"E lies in L",
				"E ⊆ L.carrier",
				By(linear_independence.IndependentInCarrier.Read(independent)))
			scalarsInL := a.Have(
				"F lies in L",
				"F ⊆ L.carrier",
				By(subfieldF, field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("L"), F)))
			values := a.Have(
				"any values on E are taken by the combination of d with those coefficients",
				"∀c:(A → A). (∀e:A. e ∈ E ⇒ c(e) ∈ F) ⇒ ∃z:A. z ∈ L.carrier ∧ (∀e:A. e ∈ E ⇒ l(z * e) = c(e))",
				Derive(func(b *Argument) {
					b.FixAs[Fun[A, A]]("c")
					coefficients := b.Assume()
					summand := b.TermAs[Fun[A, A]]("λe:A. c(e) * d(e)")
					terms := b.Have(
						"each c(e) * d(e) lies in L",
						"∀e:A. e ∈ E ⇒ c(e) * d(e) ∈ L.carrier",
						Derive(func(c *Argument) {
							c.FixAs[A]("e")
							eIn := c.Assume()
							c.Show(
								"L is closed under the scalars of F",
								By(coefficients, dualInL, eIn, module.SmulIn.Read(moduleL)))
						}))
					sum := b.TermAs[A]("module_sum(L.add, L.zero, E, λe:A. c(e) * d(e))")
					sumIn := b.Have(
						"so their sum lies in L",
						"module_sum(L.add, L.zero, E, λe:A. c(e) * d(e)) ∈ L.carrier",
						By(moduleL, finiteE, terms, module.ModuleSumIn.At(opsF, vectors, E, summand)))
					reads := b.Have(
						"and it takes the value c(f) at each f of E",
						"∀f:A. f ∈ E ⇒ l(module_sum(L.add, L.zero, E, λe:A. c(e) * d(e)) * f) = c(f)",
						Derive(func(c *Argument) {
							f := c.FixAs[A]("f")
							fIn := c.Assume()
							fInL := c.Have(
								"f lies in L",
								"f ∈ L.carrier",
								By(fIn, basisInL, set_basic.SubsetDef))
							pairing := c.Have(
								"pairing with f is F-linear",
								"module_homomorphism(«rings»(F), regular_module(field_ring(L)), «vectors»(F), λx:A. l(x * f))",
								By(fixedRight.At(f), fInL))
							termValues := c.Have(
								"the value at f of c(e) * d(e) is c(e) times the delta of e and f",
								"∀e:A. e ∈ E ⇒ l(c(e) * d(e) * f) = c(e) * COND(e = f, L.one, L.zero)",
								Derive(func(d *Argument) {
									e := d.FixAs[A]("e")
									eIn := d.Assume()
									places := d.Have(
										"c(e) lies in F and d(e) in L",
										"c(e) ∈ F ∧ d(e) ∈ L.carrier",
										By(coefficients, dualInL, eIn))
									d.Show(
										"pairing with f moves c(e) out and leaves the delta",
										By(
											pairing,
											places,
											deltas.At(e, f),
											eIn,
											fIn,
											At(Read(module_homomorphism.HomSmul, pairing), d.TermAs[A]("c(e)"), d.TermAs[A]("d(e)"))))
								}))
							sumValue := c.Have(
								"pairing with f carries the sum to the sum of the values",
								"l(module_sum(L.add, L.zero, E, λe:A. c(e) * d(e)) * f) = "+
									"module_sum(L.add, L.zero, E, λe:A. l((c(e) * d(e)) * f))",
								By(
									pairing,
									finiteE,
									terms,
									module_homomorphism.HomSum.At(
										opsF, vectors, scalars, c.TermAs[Fun[A, A]]("λx:A. l(x * f)"), E, summand)))
							termsInF := c.Have(
								"each value lies in F",
								"∀e:A. e ∈ E ⇒ l((c(e) * d(e)) * f) ∈ F",
								Derive(func(d *Argument) {
									d.FixAs[A]("e")
									eIn := d.Assume()
									d.Show(
										"pairing with f takes L into F",
										By(pairing, terms, eIn, At(Read(module_homomorphism.HomIn, pairing), d.TermAs[A]("c(e) * d(e)"))))
								}))
							offDiagonal := c.Have(
								"the values at e other than f vanish",
								"∀e:A. e ∈ E ∧ e ≠ f ⇒ l((c(e) * d(e)) * f) = L.zero",
								Derive(func(d *Argument) {
									e := d.FixAs[A]("e")
									away := d.Conjuncts(
										d.Assume(),
										"e lies in E",
										"e is not f")
									coefficient := d.Have(
										"c(e) lies in L",
										"c(e) ∈ L.carrier",
										By(coefficients, away[0], scalarsInL, set_basic.SubsetDef))
									d.Show(
										"the delta is zero",
										ByArith(L, coefficient, away[1], termValues.At(e), away[0]))
								}))
							single := c.Have(
								"so the sum of the values is the one at f",
								"module_sum(L.add, L.zero, E, λe:A. l((c(e) * d(e)) * f)) = l((c(f) * d(f)) * f)",
								By(
									module_homomorphism.HomTarget.Read(pairing),
									finiteE,
									fIn,
									termsInF,
									offDiagonal,
									module.ModuleSumSingle.At(opsF, scalars, E, f, c.TermAs[Fun[A, A]]("λe:A. l((c(e) * d(e)) * f)"))))
							coefficient := c.Have(
								"c(f) lies in L",
								"c(f) ∈ L.carrier",
								By(coefficients, fIn, scalarsInL, set_basic.SubsetDef))
							c.Show(
								"the value at f is c(f) times the delta of f and f",
								ByArith(L, coefficient, termValues.At(f), fIn, single, sumValue))
						}))
					b.Take(sum)
					b.Show(
						"the sum lies in L and takes the values c",
						By(sumIn, reads))
				}))
			unique := a.Have(
				"and two elements agreeing on E are equal, each being expanded through d by its values",
				"∀u v:A. u ∈ L.carrier ∧ v ∈ L.carrier ∧ (∀e:A. e ∈ E ⇒ l(u * e) = l(v * e)) ⇒ u = v",
				Derive(func(b *Argument) {
					u, v := b.FixAs[A]("u"), b.FixAs[A]("v")
					assumed := b.Conjuncts(
						b.Assume(),
						"u lies in L",
						"v lies in L",
						"u and v agree on E")
					termwise := b.Have(
						"their expansions agree term by term",
						"∀e:A. e ∈ E ⇒ l(u * e) * d(e) = l(v * e) * d(e)",
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							eIn := c.Assume()
							c.Show(
								"the coefficients agree",
								By(Normalized, assumed[2].At(e), eIn))
						}))
					same := b.Have(
						"so the expansions are one sum",
						"module_sum(L.add, L.zero, E, λe:A. l(u * e) * d(e)) = "+
							"module_sum(L.add, L.zero, E, λe:A. l(v * e) * d(e))",
						By(
							termwise,
							module.ModuleSumCongruence.At(
								add,
								zero,
								E,
								b.TermAs[Fun[A, A]]("λe:A. l(u * e) * d(e)"),
								b.TermAs[Fun[A, A]]("λe:A. l(v * e) * d(e)"))))
					b.Show(
						"each is the sum of its expansion",
						By(expansion.At(u), expansion.At(v), assumed[0], assumed[1], same))
				}))
			a.Show(
				"the values on E are free and determine the element",
				By(values, unique))
		}),
})}

// FunctionalPairingInHomSet — pairing with a member z of the dual of B valued in
// N, zero off B, is one of the S-linear maps from B into N: the multiplication
// pairing is F-linear in each slot (MultiplicationFunctionalBilinear),
// so pairing with z is S-linear on B, it passes the test of the dual, so it takes
// B into N, and the cut at B changes nothing on B.
var FunctionalPairingInHomSet = functionalPairingInHomSetThm{family.Add(registry.ProofEntry{
	Name: "FunctionalPairingInHomSet",
	Key:  "prop_4c58c23882150f8f",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀F:set(A). ∀l:(A → A). ∀S B N:set(A). ∀z:A.",
		Hypotheses: []string{
			"subfield(L, F)",
			"«functional»",
			"S ⊆ F",
			"S ⊆ B",
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"submodule(«rings»(S), «vectors»(F), N)",
			"z ∈ «dual»",
		},
		Conclusion: "(λb:A. COND(b ∈ B, l(z * b), L.zero)) ∈ «linearMaps»",
		Abbrev: Abbrev{
			{Name: "rings", Text: "restrict_ring(field_ring(L))"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(L)))"},
			{Name: "functional", Text: "module_homomorphism(«rings»(F), " +
				"    regular_module(field_ring(L)), " +
				"    «vectors»(F), " +
				"    l)"},
			{Name: "dual", Text: "functional_dual(field_ring(L), l, B, N)"},
			{Name: "throughInclusion", Text: "scalar_restriction(λa:A. a, regular_module(«rings»(B)))"},
			{Name: "linearMaps", Text: "hom_set(«rings»(S), «throughInclusion», «vectors»(N))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			F *Expr[Set[A]],
			l *Arrow[A, A],
			S, B, N *Expr[Set[A]],
			z *Expr[A],
			subfieldF, linear, sInF, sInB, subringS, subringB, submoduleN, zIn Fact,
		) {
			carrierRing := a.TermAs[RingOps[A]]("field_ring(L)")
			opsS := a.TermAs[RingOps[A]]("«rings»(S)")
			vectorsF := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(F)")
			vectorsN := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(N)")
			through := a.TermAs[module_record.ModuleOps[A, A]]("«throughInclusion»")
			twice := module_record.RestrictModuleTwice.At(
				a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"), F, N)
			ofZ := a.Conjuncts(
				a.Have(
					"z lies in L and passes the test",
					"z ∈ L.carrier ∧ (∀b:A. b ∈ B ⇒ l(z * b) ∈ N)",
					By(zIn, FunctionalDualMember.At(carrierRing, l, B, N, z))),
				"z lies in L",
				"z passes the test")
			sameModule := a.Have(
				"B read through the inclusion is the restricted module",
				"«throughInclusion» = «vectors»(B)",
				By(
					At(
						module_record.ScalarRestrictionIdentity,
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(«rings»(B))")),
					module_record.RegularModuleRestrict.At(carrierRing, B)))
			fixedLeft := a.Conjuncts(
				a.Unfolded(
					GroupPremises(subfieldF, linear, MultiplicationFunctionalBilinear.Read(L).At(F, l)),
					module_homomorphism.BilinearMapDef),
				"with the first variable fixed, the pairing is F-linear",
				"with the second variable fixed, it is F-linear")[0]
			overS := a.Have(
				"so pairing with z is S-linear on L, S lying in F",
				"module_homomorphism(«rings»(S), regular_module(field_ring(L)), «vectors»(F), λb:A. l(z * b))",
				By(fixedLeft.At(z), ofZ[0], subringS, sInF, module_homomorphism.HomRestrictSubring))
			pairing := a.Have(
				"and on B, an S-submodule of L",
				"module_homomorphism(«rings»(S), «throughInclusion», «vectors»(F), λb:A. l(z * b))",
				sameModule.Rw(),
				By(
					subringB,
					sInB,
					principal_ideal_domain.ConstantSubringSubmodule.Read(L).At(S, B),
					module_homomorphism.HomRestrictSource.Read(overS).At(B)))
			plain := a.TermAs[Fun[A, A]]("λb:A. l(z * b)")
			cut := a.TermAs[Fun[A, A]]("λb:A. COND(b ∈ B, l(z * b), L.zero)")
			valued := a.Have(
				"pairing with z is S-linear from B into N",
				"module_homomorphism(«rings»(S), «throughInclusion», «vectors»(N), λb:A. l(z * b))",
				By(
					pairing,
					submoduleN,
					ofZ[1],
					module_homomorphism.HomCorestrict.At(opsS, through, vectorsF, plain, N),
					twice))
			agree := a.Have(
				"on B the cut-off pairing is the pairing",
				"∀x:A. x ∈ B ⇒ COND(x ∈ B, l(z * x), L.zero) = l(z * x)",
				a.ForEach(func(_ *Expr[A]) Action { return Basic() }))
			cutLinear := a.Have(
				"so the cut-off pairing is S-linear",
				"module_homomorphism(«rings»(S), "+
					"    «throughInclusion», "+
					"    «vectors»(N), "+
					"    λb:A. COND(b ∈ B, l(z * b), L.zero))",
				By(valued, agree, module_homomorphism.HomCongruence.At(opsS, through, vectorsN, plain, cut)))
			vanishes := a.Have(
				"and it is zero off B",
				"∀u:A. u ∉ B ⇒ COND(u ∈ B, l(z * u), L.zero) = L.zero",
				a.ForEach(func(_ *Expr[A]) Action { return Basic() }))
			a.Show(
				"which is membership in the hom set",
				By(cutLinear, vanishes, hom_module.InHomSet.At(opsS, through, vectorsN, cut)))
		}),
})}

// FunctionalPairingHomomorphism — the pairing map is B-linear from the dual of B
// valued in N into the S-linear maps from B into N, B acting on them through the
// argument. The dual is a B-module (FunctionalDualSubmodule) and so are the maps;
// pairing is additive in its first slot, and a factor c of B moves into the
// argument, c * u against x reading u against c * x.
var FunctionalPairingHomomorphism = functionalPairingHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "FunctionalPairingHomomorphism",
	Key:  "prop_6d8e46c6a306de66",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀F:set(A). ∀l:(A → A). ∀S B N:set(A).",
		Hypotheses: []string{
			"subfield(L, F)",
			"«functional»",
			"S ⊆ F",
			"S ⊆ B",
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"submodule(«rings»(S), «vectors»(F), N)",
		},
		Conclusion: "module_homomorphism(«rings»(B), «vectors»(«dual»), «maps», «pairing»)",
		Abbrev: Abbrev{
			{Name: "rings", Text: "restrict_ring(field_ring(L))"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(L)))"},
			{Name: "functional", Text: "module_homomorphism(«rings»(F), " +
				"    regular_module(field_ring(L)), " +
				"    «vectors»(F), " +
				"    l)"},
			{Name: "dual", Text: "functional_dual(field_ring(L), l, B, N)"},
			{Name: "maps", Text: "coextend_scalars(«rings»(S), «rings»(B), λa:A. a, «vectors»(N))"},
			{Name: "pairing", Text: "λz:A. λb:A. COND(b ∈ B, l(z * b), L.zero)"},
			{Name: "throughInclusion", Text: "scalar_restriction(λa:A. a, regular_module(«rings»(B)))"},
			{Name: "linearMaps", Text: "hom_set(«rings»(S), «throughInclusion», «vectors»(N))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			F *Expr[Set[A]],
			l *Arrow[A, A],
			S, B, N *Expr[Set[A]],
			subfieldF, linear, sInF, sInB, subringS, subringB, submoduleN Fact,
		) {
			ring := field.RingOn.Read(L)
			carrierRing := a.TermAs[RingOps[A]]("field_ring(L)")
			opsS, opsB := a.TermAs[RingOps[A]]("«rings»(S)"), a.TermAs[RingOps[A]]("«rings»(B)")
			vectorsF := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(F)")
			vectorsN := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(N)")
			dualVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(«dual»)")
			maps := a.TermAs[module_record.ModuleOps[A, Fun[A, A]]]("«maps»")
			wholeField := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			dual := a.TermAs[Set[A]]("«dual»")
			pairing := a.TermAs[Fun2[A, A, A]]("«pairing»")
			ringB := a.Have(
				"B is a ring",
				"comm_ring_on(«rings»(B))",
				By(subringB, comm_ring.SubringRingOn.Read(ring).At(B)))
			ringS := a.Have(
				"S is a ring",
				"comm_ring_on(«rings»(S))",
				By(subringS, comm_ring.SubringRingOn.Read(ring).At(S)))
			inclusion := a.Have(
				"the inclusion of S in B is a ring map",
				"ring_homomorphism(«rings»(S), «rings»(B), λx:A. x)",
				Unfold(ring_homomorphism.RingHomomorphism),
				By(ringS, ringB, sInB, set_basic.SubsetDef.At(S, B)))
			// coextend_scalars reads its source through the ring map, here the
			// inclusion of S in B: a scalar r acts on x of B as f(r) * x, which is r * x.
			mapsCarrier := a.Have(
				"the carrier of the coextension is the S-linear maps from B read through the inclusion",
				"«maps».carrier = «linearMaps»",
				Simp(Fwd(hom_module.CoextendScalarsDef), Fwd(module_record.RestrictRingDef)),
				Basic())
			dualSubmodule := a.Have(
				"the dual is a B-submodule of L",
				"submodule(«rings»(B), regular_module(field_ring(L)), «dual»)",
				By(linear, subringB, submoduleN, FunctionalDualSubmodule.Read(L).At(F, l, S, B, N)))
			regularOverB := a.Have(
				"L is a module over B",
				"module_on(«rings»(B), regular_module(field_ring(L)))",
				By(subringB, fractional_ideal.FieldModuleOn.Read(L).At(B)))
			moduleOfDual := a.Have(
				"so the dual is a module over B",
				"module_on(«rings»(B), «vectors»(«dual»))",
				By(regularOverB, dualSubmodule, submodule.SubmoduleModuleOn.At(opsB, wholeField, dual)))
			moduleF := a.Have(
				"F is a module over itself",
				"module_on(«rings»(F), «vectors»(F))",
				By(module_homomorphism.HomTarget.Read(linear)))
			ringF := a.Have(
				"so F is a ring",
				"comm_ring_on(«rings»(F))",
				By(module.RingOn.Read(moduleF)))
			restricted := module_record.RestrictRingTwice.At(carrierRing, F, S)
			subringOfF := a.Have(
				"S, lying in F, is a subring of it",
				"subring(«rings»(F), S)",
				By(Normalized, ringS, sInF, comm_ring.SubringRingOn.Read(ringF).At(S), restricted))
			overS := a.Have(
				"so F is a module over S",
				"module_on(«rings»(S), «vectors»(F))",
				By(
					Normalized,
					moduleF,
					subringOfF,
					module.ModuleRestrictScalars.At(a.TermAs[RingOps[A]]("«rings»(F)"), vectorsF, S),
					restricted))
			twice := module_record.RestrictModuleTwice.At(wholeField, F, N)
			moduleN := a.Have(
				"so is N",
				"module_on(«rings»(S), «vectors»(N))",
				By(Normalized, overS, submoduleN, submodule.SubmoduleModuleOn.At(opsS, vectorsF, N), twice))
			moduleOfMaps := a.Have(
				"the S-linear maps from B into N are a module over B",
				"module_on(«rings»(B), «maps»)",
				By(
					inclusion,
					moduleN,
					hom_module.CoextendScalarsModuleOn.At(opsS, opsB, a.TermAs[Fun[A, A]]("λa:A. a"), vectorsN)))

			intoMaps := a.Have(
				"each pairing with a member of the dual is a vector of the maps",
				"∀z:A. z ∈ «dual» ⇒ (λb:A. COND(b ∈ B, l(z * b), L.zero)) ∈ «maps».carrier",
				mapsCarrier.Rw(),
				Derive(func(c *Argument) {
					z := c.FixAs[A]("z")
					zIn := c.Assume()
					c.Show(
						"it is an S-linear map from B into N, zero off B",
						By(
							subfieldF,
							linear,
							sInF,
							sInB,
							subringS,
							subringB,
							submoduleN,
							zIn,
							FunctionalPairingInHomSet.Read(L).At(F, l, S, B, N, z)))
				}))
			bInL := a.Have(
				"B lies in L",
				"B ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(subringB)))
			firstSlot := a.Have(
				"the pairing is additive in its first slot",
				"∀u v b:A. u ∈ L.carrier ∧ v ∈ L.carrier ∧ b ∈ L.carrier ⇒ l((u + v) * b) = l(u * b) + l(v * b)",
				Derive(func(c *Argument) {
					u, v, b := c.FixAs[A]("u"), c.FixAs[A]("v"), c.FixAs[A]("b")
					places := c.Conjuncts(
						c.Assume(),
						"u lies in L",
						"v lies in L",
						"b lies in L")
					um, vm, bm :=
						c.MemberOf[on.L](u, places[0]), c.MemberOf[on.L](v, places[1]), c.MemberOf[on.L](b, places[2])
					split := c.Have(
						"the product with b distributes over the sum",
						"(u + v) * b = u * b + v * b",
						ByArith(L, um, vm, bm))
					c.Show(
						"l is additive",
						split.Rw(),
						By(
							comm_ring.MulIn.Read(ring).At(um, bm),
							comm_ring.MulIn.Read(ring).At(vm, bm),
							module_homomorphism.HomAdd.Read(linear).AsFact().At(c.TermAs[A]("u * b"), c.TermAs[A]("v * b"))))
				}))
			additive := a.Have(
				"so the pairing map is additive",
				Statement{
					Binders: "∀u v:A.",
					Hypotheses: []string{
						"u ∈ «dual»",
						"v ∈ «dual»",
					},
					Conclusion: "(λb:A. COND(b ∈ B, l((u + v) * b), L.zero)) = " +
						"fun_add(λb:A. COND(b ∈ B, l(u * b), L.zero), λb:A. COND(b ∈ B, l(v * b), L.zero))",
				},
				Derive(func(c *Argument) {
					u, v := c.FixAs[A]("u"), c.FixAs[A]("v")
					both := c.Conjuncts(
						c.Assume(),
						"u lies in the dual",
						"v lies in the dual")
					inL := c.Have(
						"u and v lie in L",
						"u ∈ L.carrier ∧ v ∈ L.carrier",
						By(
							both[0],
							both[1],
							FunctionalDualMember.At(carrierRing, l, B, N, u),
							FunctionalDualMember.At(carrierRing, l, B, N, v)))
					c.Do(Funext())
					x := c.FixAs[A]("x")
					c.Do(Simp(Fwd(function_module.FunAddDef)))
					c.Cases(c.Term("x ∈ B"))
					c.When(
						"on B the value is the sum of the two values",
						func(d *Argument, xIn Fact) {
							xInL := d.Have(
								"x lies in L",
								"x ∈ L.carrier",
								BySets(xIn, bInL))
							d.Show(
								"and the pairing is additive in its first slot",
								By(xIn, xInL, inL, firstSlot.At(u, v, x)))
						})
					c.Otherwise(
						"off B each value is zero",
						func(d *Argument, xOut Fact) {
							d.Show(
								"zero is zero plus zero",
								ByArith(L, xOut))
						})
				}))
			homogeneous := a.Have(
				"and B-linear, B acting on the maps through the argument",
				Statement{
					Binders: "∀c u:A.",
					Hypotheses: []string{
						"c ∈ B",
						"u ∈ «dual»",
					},
					Conclusion: "(λb:A. COND(b ∈ B, l(c * u * b), L.zero)) = " +
						"λx:A. COND(x ∈ B, COND(c * x ∈ B, l(u * (c * x)), L.zero), L.zero)",
				},
				Derive(func(d *Argument) {
					c, u := d.FixAs[A]("c"), d.FixAs[A]("u")
					both := d.Conjuncts(
						d.Assume(),
						"c lies in B",
						"u lies in the dual")
					uInL := d.Have(
						"u lies in L",
						"u ∈ L.carrier",
						By(both[1], FunctionalDualMember.At(carrierRing, l, B, N, u)))
					cm := proof.MemberOf(c, both[0])
					d.Do(Funext())
					x := d.FixAs[A]("x")
					d.Cases(d.Term("x ∈ B"))
					d.When(
						"on B the factor c moves into the argument",
						func(e *Argument, xIn Fact) {
							product := comm_ring.MulIn.Read(ringB).At(cm, proof.MemberOf(x, xIn))
							inM := e.Have(
								"c, u and x lie in L",
								"c ∈ L.carrier ∧ u ∈ L.carrier ∧ x ∈ L.carrier",
								BySets(both[0], uInL, xIn, bInL))
							moved := e.Have(
								"the factor c moves across to x",
								"(c * u) * x = u * (c * x)",
								ByArith(L, inM))
							e.Show(
								"both sides read l(u * (c * x))",
								By(Normalized, xIn, product, moved))
						})
					d.Otherwise(
						"off B both sides are zero",
						func(e *Argument, xOut Fact) {
							e.Show(
								"x is off B",
								By(xOut))
						})
				}))
			a.Show(
				"so the pairing map is a B-linear map from the dual into the maps",
				By(
					moduleOfDual,
					moduleOfMaps,
					intoMaps,
					additive,
					homogeneous,
					module_homomorphism.ModuleHomomorphismDef.At(opsB, dualVectors, maps, pairing)))
		}),
})}

// FunctionalPairingBijective — when B is free over S on an F-basis E of L, the
// pairing map is one-to-one on the dual of B valued in N and carries it onto the
// S-linear maps from B into N: the values on E determine z and are free
// (FunctionalCoordinates), so a map's values on E are taken by some z, which
// passes the test on E (FunctionalDualOnBasis) and agrees with that map on E, so
// is that map (module_dimension.HomSetAgreeOnBasis).
var FunctionalPairingBijective = functionalPairingBijectiveThm{family.Add(registry.ProofEntry{
	Name: "FunctionalPairingBijective",
	Key:  "prop_3ff72f7e7c0cb80b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀F:set(A). ∀l:(A → A). ∀S B E N:set(A).",
		Hypotheses: []string{
			"subfield(L, F)",
			"«functional»",
			"∃x:A. x ∈ L.carrier ∧ l(x) ≠ L.zero",
			"S ⊆ F",
			"S ⊆ B",
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"finite(E)",
			"module_basis(«rings»(S), «vectors»(B), E)",
			"module_basis(«rings»(F), regular_module(field_ring(L)), E)",
			"submodule(«rings»(S), «vectors»(F), N)",
		},
		Conclusion: "injective_on(«dual», «pairing») ∧ image(«pairing», «dual») = «linearMaps»",
		Abbrev: Abbrev{
			{Name: "rings", Text: "restrict_ring(field_ring(L))"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(L)))"},
			{Name: "functional", Text: "module_homomorphism(«rings»(F), " +
				"    regular_module(field_ring(L)), " +
				"    «vectors»(F), " +
				"    l)"},
			{Name: "dual", Text: "functional_dual(field_ring(L), l, B, N)"},
			{Name: "pairing", Text: "λz:A. λb:A. COND(b ∈ B, l(z * b), L.zero)"},
			{Name: "throughInclusion", Text: "scalar_restriction(λa:A. a, regular_module(«rings»(B)))"},
			{Name: "linearMaps", Text: "hom_set(«rings»(S), «throughInclusion», «vectors»(N))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			F *Expr[Set[A]],
			l *Arrow[A, A],
			S, B, E, N *Expr[Set[A]],
			subfieldF, linear, nonzero, sInF, sInB, subringS, subringB, finiteE, basisS, basisF, submoduleN Fact,
		) {
			carrierRing := a.TermAs[RingOps[A]]("field_ring(L)")
			opsS := a.TermAs[RingOps[A]]("«rings»(S)")
			vectorsF := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(F)")
			vectorsN := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(N)")
			through := a.TermAs[module_record.ModuleOps[A, A]]("«throughInclusion»")
			dual := a.TermAs[Set[A]]("«dual»")
			linearMaps := a.TermAs[Set[Fun[A, A]]]("«linearMaps»")
			pairing := a.TermAs[Fun2[A, A, A]]("«pairing»")
			sameModule := a.Have(
				"B read through the inclusion is the restricted module",
				"«throughInclusion» = «vectors»(B)",
				By(
					At(
						module_record.ScalarRestrictionIdentity,
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(«rings»(B))")),
					module_record.RegularModuleRestrict.At(carrierRing, B)))
			into := a.Have(
				"pairing with a member of the dual is an S-linear map from B into N, zero off B",
				"∀z:A. z ∈ «dual» ⇒ (λb:A. COND(b ∈ B, l(z * b), L.zero)) ∈ «linearMaps»",
				Derive(func(c *Argument) {
					z := c.FixAs[A]("z")
					zIn := c.Assume()
					c.Show(
						"its pairing is one of the maps",
						By(
							subfieldF,
							linear,
							sInF,
							sInB,
							subringS,
							subringB,
							submoduleN,
							zIn,
							FunctionalPairingInHomSet.Read(L).At(F, l, S, B, N, z)))
				}))
			coordinates := a.Conjuncts(
				a.Have(
					"the values on E are free coordinates on L",
					"(∀c:(A → A). "+
						"    (∀e:A. e ∈ E ⇒ c(e) ∈ F) ⇒ ∃z:A. z ∈ L.carrier ∧ (∀e:A. e ∈ E ⇒ l(z * e) = c(e))) ∧ "+
						"(∀u v:A. u ∈ L.carrier ∧ v ∈ L.carrier ∧ (∀e:A. e ∈ E ⇒ l(u * e) = l(v * e)) ⇒ u = v)",
					By(subfieldF, linear, nonzero, finiteE, basisF, FunctionalCoordinates.Read(L).At(F, l, E))),
				"any values on E are taken",
				"the values on E determine the element")
			independent := a.Conjuncts(
				a.Unfolded(basisS, linear_independence.ModuleBasisDef),
				"E is independent over S",
				"E spans B over S")[0]
			basisInB := a.Have(
				"E lies in B",
				"E ⊆ B",
				By(linear_independence.IndependentInCarrier.Read(independent)))
			oneToOne := a.Have(
				"the pairing map is one-to-one: equal maps agree on E",
				"injective_on(«dual», «pairing»)",
				Derive(func(b *Argument) {
					b.Do(Unfold(functions.InjectiveOnDef))
					u, v := b.FixAs[A]("u"), b.FixAs[A]("v")
					assumed := b.Conjuncts(
						b.Assume(),
						"u lies in the dual",
						"v lies in the dual",
						"the two pairings are equal")
					inL := b.Have(
						"u and v lie in L",
						"u ∈ L.carrier ∧ v ∈ L.carrier",
						By(
							assumed[0],
							assumed[1],
							FunctionalDualMember.At(carrierRing, l, B, N, u),
							FunctionalDualMember.At(carrierRing, l, B, N, v)))
					onE := b.Have(
						"so u and v have one value at each e of E",
						"∀e:A. e ∈ E ⇒ l(u * e) = l(v * e)",
						Derive(func(c *Argument) {
							c.FixAs[A]("e")
							eIn := c.Assume()
							eInB := c.Have(
								"e lies in B",
								"e ∈ B",
								By(eIn, basisInB, set_basic.SubsetDef))
							c.Show(
								"the two pairings read those values at e",
								By(eInB, assumed[2]))
						}))
					b.Show(
						"so they are one element",
						By(coordinates[1].At(u, v), inL, onE))
				}))

			throughBasis := a.Have(
				"E is a basis of B read through the inclusion",
				"module_basis(«rings»(S), «throughInclusion», E)",
				sameModule.Rw(),
				By(basisS))
			testOnE := a.Have(
				"an element of L passing the test on E lies in the dual",
				"∀z:A. z ∈ L.carrier ∧ (∀e:A. e ∈ E ⇒ l(z * e) ∈ N) ⇒ z ∈ «dual»",
				Derive(func(c *Argument) {
					z := c.FixAs[A]("z")
					tested := c.Conjuncts(
						c.Assume(),
						"z lies in L",
						"z passes the test on E")
					c.Show(
						"testing on a basis tests on B",
						By(
							subfieldF,
							linear,
							sInF,
							sInB,
							subringS,
							subringB,
							basisS,
							submoduleN,
							tested[0],
							tested[1],
							At(Read(FunctionalDualOnBasis, L), F, l, S, B, E, N, z)))
				}))
			valuesInF := a.Have(
				"N lies in F",
				"N ⊆ F",
				By(submoduleN, submodule.SubmoduleSubset.At(opsS, vectorsF, N)))
			represented := a.Have(
				"every map of the hom set is the pairing with a member of the dual",
				"∀φ:(A → A). φ ∈ «linearMaps» ⇒ ∃z:A. z ∈ «dual» ∧ (λb:A. COND(b ∈ B, l(z * b), L.zero)) = φ",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[A, A]]("φ")
					φIn := b.Assume()
					φLinear := b.Conjuncts(
						b.Have(
							"φ is S-linear from B into N",
							"module_homomorphism(«rings»(S), «throughInclusion», «vectors»(N), φ) ∧ "+
								"(∀u:A. u ∉ B ⇒ φ(u) = L.zero)",
							By(φIn, hom_module.InHomSet.At(opsS, through, vectorsN, φ))),
						"φ is S-linear",
						"φ is zero off B")[0]
					valuesOnE := b.Have(
						"φ takes E into N",
						"∀e:A. e ∈ E ⇒ φ(e) ∈ N",
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							eIn := c.Assume()
							eInB := c.Have(
								"e lies in B",
								"e ∈ B",
								By(eIn, basisInB, set_basic.SubsetDef))
							c.Show(
								"φ takes B into N",
								By(module_homomorphism.HomIn.Read(φLinear).At(proof.MemberOf(e, eInB))))
						}))
					valuesAreInF := b.Have(
						"so φ takes E into F",
						"∀e:A. e ∈ E ⇒ φ(e) ∈ F",
						Derive(func(c *Argument) {
							c.FixAs[A]("e")
							eIn := c.Assume()
							c.Show(
								"N lies in F",
								By(valuesOnE, eIn, valuesInF, set_basic.SubsetDef))
						}))
					z, taken := b.ObtainAs[A](
						"some z of L takes the values of φ on E",
						"∃z:A. z ∈ L.carrier ∧ (∀e:A. e ∈ E ⇒ l(z * e) = φ(e))",
						By(coordinates[0].At(φ), valuesAreInF))
					takenParts := b.Conjuncts(
						taken,
						"z lies in L",
						"z takes the values of φ on E")
					passes := b.Have(
						"so z passes the test on E",
						"∀e:A. e ∈ E ⇒ l(z * e) ∈ N",
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							eIn := c.Assume()
							c.Show(
								"the value is φ(e), a member of N",
								GroupPremises(eIn, takenParts[1].At(e)).Rw(),
								By(valuesOnE, eIn))
						}))
					inDual := b.Have(
						"so z lies in the dual",
						"z ∈ «dual»",
						By(takenParts[0], passes, testOnE.At(z)))
					pairedMap := b.Have(
						"so pairing with z is a map of the hom set",
						"(λb:A. COND(b ∈ B, l(z * b), L.zero)) ∈ «linearMaps»",
						By(into.At(z), inDual))
					agree := b.Have(
						"which agrees with φ on E",
						"∀e:A. e ∈ E ⇒ COND(e ∈ B, l(z * e), L.zero) = φ(e)",
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							eIn := c.Assume()
							eInB := c.Have(
								"e lies in B",
								"e ∈ B",
								By(eIn, basisInB, set_basic.SubsetDef))
							c.Show(
								"on B the pairing reads l(z * e)",
								By(eInB, takenParts[1].At(e), eIn))
						}))
					same := b.Have(
						"so pairing with z is φ",
						"(λb:A. COND(b ∈ B, l(z * b), L.zero)) = φ",
						By(
							finiteE,
							throughBasis,
							pairedMap,
							φIn,
							agree,
							module_dimension.HomSetAgreeOnBasis.At(
								opsS, through, vectorsN, E, b.TermAs[Fun[A, A]]("λb:A. COND(b ∈ B, l(z * b), L.zero)"), φ)))
					b.Take(z)
					b.Show(
						"z is the member of the dual pairing to φ",
						By(inDual, same))
				}))
			imageInto := a.Have(
				"the image of the dual lies in the hom set",
				"image(«pairing», «dual») ⊆ «linearMaps»",
				By(into, set_image.ImageSubsetIff.At(pairing, dual, linearMaps)))
			imageOnto := a.Have(
				"and the image fills it",
				"«linearMaps» ⊆ image(«pairing», «dual»)",
				Derive(func(b *Argument) {
					b.Do(Unfold(set_basic.SubsetDef))
					φ := b.FixAs[Fun[A, A]]("φ")
					xInHom := b.Assume()
					z, witness := b.UnpackAs[A](GroupPremises(xInHom, represented.At(φ)), "z")
					parts := b.Conjuncts(
						witness,
						"z lies in the dual",
						"pairing with z is φ")
					expressed := b.Have(
						"φ is the pairing with some member of the dual",
						"∃y:A. φ = (λb:A. COND(b ∈ B, l(y * b), L.zero)) ∧ y ∈ «dual»",
						Derive(func(c *Argument) {
							c.Take(z)
							c.Show(
								"z is one",
								By(parts[0], parts[1]))
						}))
					b.Show(
						"so φ lies in the image",
						By(expressed, set_basic.InImage.At(pairing, dual, φ)))
				}))
			a.Show(
				"so the pairing map is one-to-one and fills the hom set",
				By(oneToOne, imageInto, imageOnto, set_order.SubsetAntisym))
		}),
})}

// FunctionalDualHomIso — the functional analogue of the trace dual's Hom
// isomorphism: when B is free over S on an F-basis E of L, z ↦ (b ↦ l(z * b)),
// zero off B, is a B-linear isomorphism of the dual of B valued in N onto the
// S-linear maps from B into N, B acting on them through the argument
// (FunctionalPairingHomomorphism, FunctionalPairingBijective).
var FunctionalDualHomIso = functionalDualHomIsoThm{family.Add(registry.ProofEntry{
	Name: "FunctionalDualHomIso",
	Key:  "prop_8a764d8c4c77c425",
	Reading: "The map is zero off B, and the codomain uses the B precomposition action " +
		"rather than pointwise B multiplication on N. E must be a basis of B over S and of " +
		"L over F at once: that is what ties S-linear maps on B to F-linear ones on L.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀F:set(A). ∀l:(A → A). ∀S B E N:set(A).",
		Hypotheses: []string{
			"subfield(L, F)",
			"«functional»",
			"∃x:A. x ∈ L.carrier ∧ l(x) ≠ L.zero",
			"S ⊆ F",
			"S ⊆ B",
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"finite(E)",
			"module_basis(«rings»(S), «vectors»(B), E)",
			"module_basis(«rings»(F), regular_module(field_ring(L)), E)",
			"submodule(«rings»(S), «vectors»(F), N)",
		},
		Conclusion: "module_isomorphism(«rings»(B), «vectors»(«dual»), «maps», «pairing»)",
		Abbrev: Abbrev{
			{Name: "rings", Text: "restrict_ring(field_ring(L))"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(L)))"},
			{Name: "functional", Text: "module_homomorphism(«rings»(F), " +
				"    regular_module(field_ring(L)), " +
				"    «vectors»(F), " +
				"    l)"},
			{Name: "dual", Text: "functional_dual(field_ring(L), l, B, N)"},
			{Name: "maps", Text: "coextend_scalars(«rings»(S), «rings»(B), λa:A. a, «vectors»(N))"},
			{Name: "pairing", Text: "λz:A. λb:A. COND(b ∈ B, l(z * b), L.zero)"},
			{Name: "throughInclusion", Text: "scalar_restriction(λa:A. a, regular_module(«rings»(B)))"},
			{Name: "linearMaps", Text: "hom_set(«rings»(S), «throughInclusion», «vectors»(N))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			F *Expr[Set[A]],
			l *Arrow[A, A],
			S, B, E, N *Expr[Set[A]],
			subfieldF, linear, nonzero, sInF, sInB, subringS, subringB, finiteE, basisS, basisF, submoduleN Fact,
		) {
			opsB := a.TermAs[RingOps[A]]("«rings»(B)")
			dualVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(«dual»)")
			maps := a.TermAs[module_record.ModuleOps[A, Fun[A, A]]]("«maps»")
			pairing := a.TermAs[Fun2[A, A, A]]("«pairing»")
			linearMap := a.Have(
				"the pairing map is a B-linear map from the dual into the maps",
				"module_homomorphism(«rings»(B), «vectors»(«dual»), «maps», «pairing»)",
				By(
					subfieldF,
					linear,
					sInF,
					sInB,
					subringS,
					subringB,
					submoduleN,
					FunctionalPairingHomomorphism.Read(L).At(F, l, S, B, N)))
			bijection := a.Conjuncts(
				GroupPremises(
					subfieldF,
					linear,
					nonzero,
					sInF,
					sInB,
					subringS,
					subringB,
					finiteE,
					basisS,
					basisF,
					submoduleN,
					FunctionalPairingBijective.Read(L).At(F, l, S, B, E, N)),
				"the pairing map is one-to-one",
				"and carries the dual onto the hom set")
			mapsCarrier := a.Have(
				"the carrier of the coextension is the S-linear maps from B read through the inclusion",
				"«maps».carrier = «linearMaps»",
				Simp(Fwd(hom_module.CoextendScalarsDef), Fwd(module_record.RestrictRingDef)),
				Basic())
			onto := a.Have(
				"so it carries the dual onto the maps",
				"image(«pairing», «dual») = «maps».carrier",
				mapsCarrier.Rw(),
				By(bijection[1]))
			a.Show(
				"a B-linear bijection of the dual onto the maps",
				By(
					linearMap,
					bijection[0],
					onto,
					module_homomorphism.ModuleIsomorphismDef.At(opsB, dualVectors, maps, pairing)))
		}),
})}

// NonzeroLinearFunctional — a finite extension L of a field F carries a
// nonzero F-linear functional, whether or not its field trace vanishes: a
// finite basis of L over F is not empty, L holding one, and the coordinate at
// a basis vector e is linear and takes the value one at e.
var NonzeroLinearFunctional = nonzeroLinearFunctionalThm{family.Add(registry.ProofEntry{
	Name: "NonzeroLinearFunctional",
	Key:  "prop_99d8a063d963461d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀F:set(A).",
		Hypotheses: []string{
			"subfield(L, F)",
			"finite_extension(L, F, L.carrier)",
		},
		Conclusion: "∃l:(A → A). " +
			"    module_homomorphism(«scalars», «vectors», restrict_module(«vectors», F), l) ∧ " +
			"    ∃x:A. x ∈ L.carrier ∧ l(x) ≠ L.zero",
		Abbrev: Abbrev{
			{Name: "scalars", Text: "restrict_ring(field_ring(L), F)"},
			{Name: "vectors", Text: "regular_module(field_ring(L))"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], F *Expr[Set[A]], subfieldF, finite Fact) {
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»")
			scalars := a.TermAs[RingOps[A]]("«scalars»")
			vectorSpace := a.Have(
				"L is a vector space over F",
				"module_on(«scalars», «vectors»)",
				By(subfieldF, field_extension.SubfieldScalars.Read(L).At(F)))
			fullModule := a.Have(
				"restricting the regular module to L's carrier leaves it unchanged",
				"restrict_module(«vectors», L.carrier) = «vectors»",
				Simp(
					Fwd(module_record.RegularModuleDef),
					Fwd(field.FieldRingDef),
					Fwd(module_record.RestrictModuleDef)),
				Basic())
			E, hasBasis := a.UnpackAs[Set[A]](
				a.Simplified(
					a.Unfolded(
						a.Unfolded(finite, field_extension.FiniteExtensionDef), module_dimension.FiniteDimensionalDef),
					Fwd(fullModule)),
				"E")
			basis := a.Conjuncts(
				hasBasis,
				"E is finite",
				"and a basis of L over F")
			spans := a.Have(
				"so its span is L",
				"module_span(«scalars», «vectors», E) = «vectors».carrier",
				By(basis[1], linear_independence.ModuleBasisDef.At(scalars, vectors, E)))
			oneIsZero := a.Have(
				"an empty basis would make one zero: the span of nothing is {zero}, and L holds one",
				"E = ∅ ⇒ L.one = L.zero",
				Derive(func(b *Argument) {
					empty := b.Assume()
					spansNothing := b.Have(
						"L is the span of nothing",
						"module_span(«scalars», «vectors», ∅) = «vectors».carrier",
						empty.RwRev(),
						By(spans))
					b.Show(
						"so one lies in {zero}",
						BySets(
							vectorSpace,
							spansNothing,
							submodule.SpanEmpty.At(scalars, vectors),
							comm_ring.OneIn.Read(field.RingOn.Read(L))))
				}))
			e, inE := a.ObtainAs[A](
				"so E, not being empty, holds a vector e",
				"∃e:A. e ∈ E",
				By(oneIsZero, field.OneNotZeroOn.Read(L), set_basic.MemberNotEmpty.At(E)))
			coordinate := a.TermAs[Fun[A, A]]("λv:A. module_basis_coordinates(«scalars», «vectors», E, v, e)")
			linear := a.Have(
				"the coordinate at e is an F-linear map of L into F",
				"module_homomorphism(«scalars», "+
					"    «vectors», "+
					"    restrict_module(«vectors», F), "+
					"    λv:A. module_basis_coordinates(«scalars», «vectors», E, v, e))",
				By(
					basis[0],
					basis[1],
					inE,
					module_record.RegularModuleRestrict.At(a.TermAs[RingOps[A]]("field_ring(L)"), F),
					module_dimension.BasisCoordinateLinear.Read(vectorSpace).At(E, e)))
			one := a.Have(
				"and at e it is the one of L, the coordinates of e being one at e and zero elsewhere",
				"module_basis_coordinates(«scalars», «vectors», E, e, e) = L.one",
				GroupPremises(
					basis[0], basis[1], inE, module_dimension.BasisCoordinateDelta.Read(vectorSpace).At(E, e)).Rw(),
				Basic())
			inField := a.Have(
				"e lies in L",
				"e ∈ L.carrier",
				BySets(basis[1], inE, linear_independence.BasisInCarrier.Read(basis[1])))
			a.Take(coordinate)
			a.Show(
				"the coordinate at e is linear, and it is one at e",
				SplitConj(
					Case(
						"it is linear",
						By(linear)),
					Case(
						"it is not zero at e",
						Derive(func(b *Argument) {
							b.Take(e)
							b.Show(
								"at e it is one, which is not zero",
								By(inField, one, field.OneNotZeroOn.Read(L)))
						}))))
		}),
})}
