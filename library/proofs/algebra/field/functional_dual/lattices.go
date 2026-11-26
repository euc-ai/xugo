package functional_dual

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_factorization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// FunctionalDualGenerators — testing a functional dual on a generating set
// suffices: pairing with a fixed element is linear, so the values on the
// generated module lie in the submodule containing the generator values.
var FunctionalDualGenerators = functionalDualGeneratorsThm{family.Add(registry.ProofEntry{
	Name: "FunctionalDualGenerators",
	Key:  "prop_1a0a7a45db17cbf0",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀l:(A → A). ∀S B N E:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"S ⊆ K",
			"subring(field_ring(L), S)",
			"module_homomorphism(«ScalarK», «Regular», «VectorsK», l)",
			"submodule(«ScalarS», «Regular», B)",
			"submodule(«ScalarS», «VectorsK», N)",
			"E ⊆ B",
			"module_span(«ScalarS», «VectorsB», E) = B",
		},
		Conclusion: "functional_dual(field_ring(L), l, B, N) = functional_dual(field_ring(L), l, E, N)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		K *Expr[Set[A]],
		l *Arrow[A, A],
		S, B, N, E *Expr[Set[A]],
		subK, sInK, subS, linear, subB, subN, eInB, spanB Fact,
	) {
		fixedLeft := a.Conjuncts(
			a.Simplified(
				GroupPremises(subK, linear, MultiplicationFunctionalBilinear.Read(L).At(K, l)),
				Fwd(module_homomorphism.BilinearMapDef)),
			"with the first variable fixed, the pairing is K-linear",
			"with the second variable fixed, it is K-linear")[0]
		extends := a.Have(
			"values in N on E extend to values in N on B",
			"∀z:A. z ∈ L.carrier ∧ (∀e:A. e ∈ E ⇒ l(z * e) ∈ N) ⇒ ∀b:A. b ∈ B ⇒ l(z * b) ∈ N",
			Derive(func(b *Argument) {
				z := b.FixAs[A]("z")
				given := b.Assume()
				linearK := b.Have(
					"the test map is K-linear",
					"module_homomorphism(«ScalarK», «Regular», «VectorsK», λy:A. l(z * y))",
					By(fixedLeft.At(z), given))
				linearS := b.Have(
					"restriction of scalars makes it S-linear",
					"module_homomorphism(«ScalarS», «Regular», «VectorsK», λy:A. l(z * y))",
					By(linearK, subS, sInK, module_homomorphism.HomRestrictSubring))
				linearB := b.Have(
					"and it remains linear on the submodule B",
					"module_homomorphism(«ScalarS», «VectorsB», «VectorsK», λy:A. l(z * y))",
					By(linearS, subB, module_homomorphism.HomRestrictSource.Read(linearS).At(B)))
				generators := b.Have(
					"the generators land in N",
					"image(λy:A. l(z * y), E) ⊆ N",
					BySets(given))
				within := b.Have(
					"so the whole span of E lands in the submodule N",
					"image(λy:A. l(z * y), module_span(«ScalarS», «VectorsB», E)) ⊆ N",
					By(eInB, subN, generators, linear_independence.HomSpanInSubmodule.Read(linearB).At(E, N)))
				b.Show(
					"and E spans B, so every value on B lies in N",
					BySets(within, spanB))
			}))
		a.Show(
			"the tests against B and against E define the same dual",
			Simp(Fwd(set_basic.Extension), Fwd(FunctionalDualMember)),
			BySets(extends, eInB))
	}),
})}

// FunctionalDualAdditive — under an additive map fixing zero, the dual of any
// subset of L against a set holding zero and closed under addition holds zero
// and is closed under addition: multiplication distributes over the sum, the
// map splits it, and zero annihilates every test element.
var FunctionalDualAdditive = functionalDualAdditiveThm{family.Add(registry.ProofEntry{
	Name: "FunctionalDualAdditive",
	Key:  "prop_56a55237bb3f4d9d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀l:(A → A). ∀X N:set(A).",
		Hypotheses: []string{
			"∀u v:A. u ∈ L.carrier ∧ v ∈ L.carrier ⇒ l(u + v) = l(u) + l(v)",
			"l(L.zero) = L.zero",
			"X ⊆ L.carrier",
			"L.zero ∈ N",
			"∀u v:A. u ∈ N ∧ v ∈ N ⇒ u + v ∈ N",
		},
		Conclusion: "L.zero ∈ «Dual» ∧ (∀x y:A. x ∈ «Dual» ∧ y ∈ «Dual» ⇒ x + y ∈ «Dual»)",
		Abbrev: Abbrev{
			{Name: "Dual", Text: "functional_dual(field_ring(L), l, X, N)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		l *Arrow[A, A],
		X, N *Expr[Set[A]],
		additive, fixesZero, xInL, zeroInN, sumsInN Fact,
	) {
		ring := field.RingOn.Read(L)
		inL := a.Unfolded(xInL, set_basic.SubsetDef)
		zeroTests := a.Have(
			"zero passes each test",
			"∀t:A. t ∈ X ⇒ l(L.zero * t) ∈ N",
			Derive(func(b *Argument) {
				t := b.FixAs[A]("t")
				tIn := b.Assume()
				annihilates := b.Have(
					"zero annihilates t",
					"L.zero * t = L.zero",
					By(tIn, comm_ring.MulLeftZeroOn.Read(ring).At(b.MemberOf[on.L](t, GroupPremises(tIn, inL.At(t))))))
				b.Show(
					"the map sends zero to zero, which N holds",
					annihilates.Rw(),
					By(Normalized, fixesZero, zeroInN))
			}))
		zeroIn := a.Have(
			"zero lies in the dual",
			"L.zero ∈ «Dual»",
			Simp(Fwd(FunctionalDualMember)),
			By(zeroTests, comm_ring.ZeroIn.Read(ring)))
		sums := a.Have(
			"the dual is closed under addition",
			"∀x y:A. x ∈ «Dual» ∧ y ∈ «Dual» ⇒ x + y ∈ «Dual»",
			Derive(func(b *Argument) {
				x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
				both := b.Conjuncts(
					b.Assume(),
					"x lies in the dual",
					"y lies in the dual")
				xTests := b.Conjuncts(
					b.Simplified(both[0], Fwd(FunctionalDualMember)),
					"x lies in L",
					"x passes the tests")
				yTests := b.Conjuncts(
					b.Simplified(both[1], Fwd(FunctionalDualMember)),
					"y lies in L",
					"y passes the tests")
				xL, yL := b.MemberOf[on.L](x, xTests[0]), b.MemberOf[on.L](y, yTests[0])
				tests := b.Have(
					"the sum passes each test",
					"∀t:A. t ∈ X ⇒ l((x + y) * t) ∈ N",
					Derive(func(test *Argument) {
						t := test.FixAs[A]("t")
						tIn := test.Assume()
						tL := test.MemberOf[on.L](t, GroupPremises(tIn, inL.At(t)))
						distribute := test.Have(
							"the product distributes over the sum",
							"(x + y) * t = x * t + y * t",
							ByArith(L, xL, yL, tL))
						test.Show(
							"the value is a sum of members of N",
							distribute.Rw(),
							By(
								comm_ring.MulIn.Read(ring).At(xL, tL),
								comm_ring.MulIn.Read(ring).At(yL, tL),
								xTests[1].At(t),
								yTests[1].At(t),
								tIn,
								additive.At(test.TermAs[A]("x * t"), test.TermAs[A]("y * t")),
								sumsInN.At(test.TermAs[A]("l(x * t)"), test.TermAs[A]("l(y * t)"))))
					}))
				b.Show(
					"the sum therefore lies in the dual",
					Simp(Fwd(FunctionalDualMember)),
					By(tests, comm_ring.AddIn.Read(ring).At(xL, yL)))
			}))
		a.Show(
			"the dual holds zero and its sums",
			By(zeroIn, sums))
	}),
})}

// FunctionalDualSubmodule — the dual of an S-submodule of K is a B-submodule
// of L: each test is additive in the tested element and N is closed under
// addition, and a B-factor moves off the tested element into the test.
var FunctionalDualSubmodule = functionalDualSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "FunctionalDualSubmodule",
	Key:  "prop_d4e513bc48887299",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀l:(A → A). ∀S B N:set(A).",
		Hypotheses: []string{
			"module_homomorphism(«ScalarK», «Regular», «VectorsK», l)",
			"subring(field_ring(L), B)",
			"submodule(«ScalarS», «VectorsK», N)",
		},
		Conclusion: "submodule(«ScalarB», «Regular», «Dual»)",
		Abbrev: Abbrev{
			{Name: "Dual", Text: "functional_dual(field_ring(L), l, B, N)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		K *Expr[Set[A]],
		l *Arrow[A, A],
		S, B, N *Expr[Set[A]],
		linear, subringB, subN Fact,
	) {
		rB := a.TermAs[RingOps[A]]("«ScalarB»")
		regular := a.TermAs[module_record.ModuleOps[A, A]]("«Regular»")
		dual := a.TermAs[Set[A]]("«Dual»")
		ring := field.RingOn.Read(L)
		inField := a.Have(
			"B lies in the field",
			"B ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(subringB)))
		closed := a.Have(
			"the dual holds zero and is closed under addition",
			"L.zero ∈ «Dual» ∧ (∀x y:A. x ∈ «Dual» ∧ y ∈ «Dual» ⇒ x + y ∈ «Dual»)",
			By(
				inField,
				module_homomorphism.HomAdd.Read(linear),
				module_homomorphism.HomZero.Read(linear),
				submodule.SubmoduleZero.Read(subN),
				submodule.SubmoduleAdd.Read(subN),
				FunctionalDualAdditive.Read(L).At(l, B, N)))
		multiples := a.Have(
			"B-multiples preserve the dual",
			"∀c u:A. c ∈ B ∧ u ∈ «Dual» ⇒ c * u ∈ «Dual»",
			Derive(func(b *Argument) {
				c, u := b.FixAs[A]("c"), b.FixAs[A]("u")
				multiple := b.Conjuncts(
					b.Assume(),
					"c lies in B",
					"u lies in the dual")
				uTests := b.Conjuncts(
					b.Simplified(multiple[1], Fwd(FunctionalDualMember)),
					"u lies in L",
					"u passes the tests")
				cInL := b.MemberOf[on.L](c, b.Have(
					"c lies in L",
					"c ∈ L.carrier",
					BySets(multiple[0], inField)))
				uInL := b.MemberOf[on.L](u, uTests[0])
				tests := b.Have(
					"the multiple passes each test",
					"∀t:A. t ∈ B ⇒ l(c * u * t) ∈ N",
					Derive(func(test *Argument) {
						t := test.FixAs[A]("t")
						tIn := test.Assume()
						tInL := test.MemberOf[on.L](t, test.Have(
							"t lies in L",
							"t ∈ L.carrier",
							BySets(tIn, inField)))
						regroup := test.Have(
							"commute c past u and associate the products",
							"(c * u) * t = u * (c * t)",
							ByArith(L, cInL, uInL, tInL))
						test.Show(
							"use u's test against c * t",
							regroup.Rw(),
							By(uTests[1], multiple[0], tIn, comm_ring.SubringMul.Read(subringB).AsFact().At(c, t)))
					}))
				b.Show(
					"the multiple lies in the dual",
					Simp(Fwd(FunctionalDualMember)),
					By(tests, comm_ring.MulIn.Read(ring).At(cInL, uInL)))
			}))
		dualInL := a.Have(
			"the dual lies in L",
			"«Dual» ⊆ L.carrier",
			Simp(Fwd(set_basic.SubsetDef), Fwd(FunctionalDualMember)),
			BySets())
		a.Show(
			"these closure properties make the dual a B-submodule",
			By(
				subringB,
				fractional_ideal.FieldModuleOn.Read(L).At(B),
				dualInL,
				closed,
				multiples,
				submodule.SubmoduleCriterion.At(rB, regular, dual)))
	}),
})}

// FunctionalDualOverScalars — under an S-linear functional, the dual of any
// subset of L against an S-submodule of K is an S-submodule of L: a test against
// X is an S-linear value of the product and N is an S-submodule, so a scalar of
// S moves out of the tested element and onto the value, and X needs no
// stability of its own.
var FunctionalDualOverScalars = functionalDualOverScalarsThm{family.Add(registry.ProofEntry{
	Name: "FunctionalDualOverScalars",
	Key:  "prop_825d7a6d3d43953f",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀l:(A → A). ∀S X N:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"module_homomorphism(«ScalarS», «Regular», «VectorsK», l)",
			"X ⊆ L.carrier",
			"submodule(«ScalarS», «VectorsK», N)",
		},
		Conclusion: "submodule(«ScalarS», «Regular», «Dual»)",
		Abbrev: Abbrev{
			{Name: "Dual", Text: "functional_dual(field_ring(L), l, X, N)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		K *Expr[Set[A]],
		l *Arrow[A, A],
		S, X, N *Expr[Set[A]],
		subS, linear, xInL, subN Fact,
	) {
		scalarsS := a.TermAs[RingOps[A]]("«ScalarS»")
		regular := a.TermAs[module_record.ModuleOps[A, A]]("«Regular»")
		dual := a.TermAs[Set[A]]("«Dual»")
		ring := field.RingOn.Read(L)
		inL := a.Unfolded(xInL, set_basic.SubsetDef)
		closed := a.Have(
			"the dual holds zero and is closed under addition",
			"L.zero ∈ «Dual» ∧ (∀x y:A. x ∈ «Dual» ∧ y ∈ «Dual» ⇒ x + y ∈ «Dual»)",
			By(
				xInL,
				module_homomorphism.HomAdd.Read(linear),
				module_homomorphism.HomZero.Read(linear),
				submodule.SubmoduleZero.Read(subN),
				submodule.SubmoduleAdd.Read(subN),
				FunctionalDualAdditive.Read(L).At(l, X, N)))
		multiples := a.Have(
			"S-multiples preserve the dual",
			"∀c u:A. c ∈ S ∧ u ∈ «Dual» ⇒ c * u ∈ «Dual»",
			Derive(func(b *Argument) {
				c, u := b.FixAs[A]("c"), b.FixAs[A]("u")
				multiple := b.Conjuncts(
					b.Assume(),
					"c lies in S",
					"u lies in the dual")
				uTests := b.Conjuncts(
					b.Simplified(multiple[1], Fwd(FunctionalDualMember)),
					"u lies in L",
					"u passes the tests")
				cL := b.MemberOf[on.L](c, b.Have(
					"c lies in L",
					"c ∈ L.carrier",
					BySets(multiple[0], comm_ring.SubringSubset.Read(subS))))
				uL := b.MemberOf[on.L](u, uTests[0])
				tests := b.Have(
					"the multiple passes each test",
					"∀t:A. t ∈ X ⇒ l(c * u * t) ∈ N",
					Derive(func(test *Argument) {
						t := test.FixAs[A]("t")
						tIn := test.Assume()
						tL := test.MemberOf[on.L](t, GroupPremises(tIn, inL.At(t)))
						associate := test.Have(
							"the scalar associates off the product",
							"(c * u) * t = c * (u * t)",
							ByArith(L, cL, uL, tL))
						test.Show(
							"the functional moves c onto the value, and N is an S-submodule",
							associate.Rw(),
							By(
								multiple[0],
								comm_ring.MulIn.Read(ring).At(uL, tL),
								uTests[1].At(t),
								tIn,
								module_homomorphism.HomSmul.Read(linear).AsFact().At(c, test.TermAs[A]("u * t")),
								submodule.SubmoduleSmul.Read(subN).AsFact().At(c, test.TermAs[A]("l(u * t)"))))
					}))
				b.Show(
					"the multiple therefore lies in the dual",
					Simp(Fwd(FunctionalDualMember)),
					By(tests, comm_ring.MulIn.Read(ring).At(cL, uL)))
			}))
		dualInL := a.Have(
			"the dual lies in L",
			"«Dual» ⊆ L.carrier",
			Simp(Fwd(set_basic.SubsetDef), Fwd(FunctionalDualMember)),
			BySets())
		a.Show(
			"these closure properties make the dual an S-submodule",
			By(
				subS,
				fractional_ideal.FieldModuleOn.Read(L).At(S),
				dualInL,
				closed,
				multiples,
				submodule.SubmoduleCriterion.At(scalarsS, regular, dual)))
	}),
})}

// FunctionalDualBounded — the functional dual of a finite free lattice is a
// bounded fractional ideal: the dual basis lies in the dual, it expands every
// member of the dual with coefficients in S, and a common denominator of the
// finite dual basis in B therefore clears the whole dual.
var FunctionalDualBounded = functionalDualBoundedThm{family.Add(registry.ProofEntry{
	Name: "FunctionalDualBounded",
	Key:  "prop_ad97a6d5a61248a4",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀l:(A → A). ∀S B E:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"module_homomorphism(«ScalarK», «Regular», «VectorsK», l)",
			"∃x:A. x ∈ L.carrier ∧ l(x) ≠ L.zero",
			"S ⊆ K",
			"S ⊆ B",
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"fraction_field_carrier(field_ring(L), B)",
			"finite(E)",
			"module_basis(«ScalarS», «VectorsB», E)",
			"module_basis(«ScalarK», «Regular», E)",
		},
		Conclusion: "bounded_fractional(field_ring(L), B, «Dual»)",
		Abbrev: Abbrev{
			{Name: "Dual", Text: "functional_dual(field_ring(L), l, B, S)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		dualBasis := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K:set(A). ∀l:(A → A). ∀S B E:set(A).",
			Hypotheses: []string{
				"subfield(L, K)",
				"module_homomorphism(«ScalarK», «Regular», «VectorsK», l)",
				"∃x:A. x ∈ L.carrier ∧ l(x) ≠ L.zero",
				"S ⊆ K",
				"subring(field_ring(L), S)",
				"finite(E)",
				"module_basis(«ScalarS», «VectorsB», E)",
				"module_basis(«ScalarK», «Regular», E)",
				"submodule(«ScalarS», «Regular», B)",
				"submodule(«ScalarS», «VectorsK», S)",
			},
			Conclusion: "∃d:(A → A). " +
				"    image(d, E) ⊆ «Dual» ∧ " +
				"    «Dual» ≠ {L.zero} ∧ " +
				"    (∀x:A. x ∈ L.carrier ⇒ x = module_sum(L.add, L.zero, E, λe:A. l(x * e) * d(e)))",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			K *Expr[Set[A]],
			l *Arrow[A, A],
			S, B, E *Expr[Set[A]],
			subK, linear, nonzeroValue, sInK, subS, finiteE, basisB, basisK, latticeB, scalars Fact,
		) {
			rK, rS := a.TermAs[RingOps[A]]("«ScalarK»"), a.TermAs[RingOps[A]]("«ScalarS»")
			regular := a.TermAs[module_record.ModuleOps[A, A]]("«Regular»")
			vB := a.TermAs[module_record.ModuleOps[A, A]]("«VectorsB»")
			moduleK := module_homomorphism.HomSource.Read(linear)
			d, data := a.UnpackAs[Fun[A, A]](
				GroupPremises(
					subK, linear, nonzeroValue, finiteE, basisK, MultiplicationFunctionalDualBasis.Read(L).At(K, l, E)),
				"d")
			parts := a.Conjuncts(
				data,
				"the dual vectors lie in L",
				"their pairings with E are Kronecker values",
				"they are a K-basis of L",
				"the pairings with E are expansion coefficients")
			dInL, delta, expansion := parts[0], parts[1], parts[3]
			basisInB, basisInL :=
				linear_independence.BasisInCarrier.Read(basisB), linear_independence.BasisInCarrier.Read(basisK)
			generatorTests := a.Have(
				"it suffices to test the functional dual against E",
				"«Dual» = functional_dual(field_ring(L), l, E, S)",
				By(
					subK,
					sInK,
					subS,
					linear,
					latticeB,
					scalars,
					basisInB,
					basisB,
					linear_independence.ModuleBasisDef.At(rS, vB, E),
					FunctionalDualGenerators.Read(L).At(K, l, S, B, S, E)))
			deltaS := a.Have(
				"the Kronecker pairing values lie in S",
				"∀e f:A. e ∈ E ∧ f ∈ E ⇒ l(d(e) * f) ∈ S",
				By(delta, comm_ring.SubringOne.Read(subS), comm_ring.SubringZero.Read(subS)))
			dInDual := a.Have(
				"each dual basis vector passes the S-valued tests",
				"image(d, E) ⊆ «Dual»",
				Simp(Fwd(generatorTests), Fwd(set_basic.SubsetDef), Fwd(FunctionalDualMember)),
				BySets(dInL, deltaS))
			nonzero := a.Have(
				"the dual holds a nonzero vector, d(e) at any member e of the basis",
				"«Dual» ≠ {L.zero}",
				Derive(func(b *Argument) {
					nonempty := b.Have(
						"a basis of the nonzero field L has a member",
						"∃e:A. e ∈ E",
						BySets(
							basisK,
							moduleK,
							linear_independence.ModuleBasisDef.At(rK, regular, E),
							submodule.SpanEmpty.At(rK, regular),
							comm_ring.OneIn.Read(field.RingOn.Read(L)),
							field.OneNotZeroOn.Read(L)))
					e, eIn := b.UnpackAs[A](nonempty, "e")
					eInL := b.MemberOf[on.L](e, b.Have(
						"e lies in the field",
						"e ∈ L.carrier",
						BySets(eIn, basisInL)))
					deNonzero := b.Have(
						"the diagonal pairing makes d(e) nonzero",
						"d(e) ≠ L.zero",
						By(
							eIn,
							eInL,
							delta.At(e, e),
							module_homomorphism.HomZero.Read(linear),
							comm_ring.MulLeftZeroOn.Read(field.RingOn.Read(L)).At(eInL),
							field.OneNotZeroOn.Read(L)))
					b.Show(
						"the functional dual contains that nonzero vector",
						BySets(eIn, deNonzero, dInDual))
				}))
			a.Take(d)
			a.Show(
				"the dual basis lies in the nonzero dual and expands L",
				By(dInDual, nonzero, expansion))
		})
		spanBound := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀l:(A → A). ∀S B E:set(A). ∀d:(A → A).",
			Hypotheses: []string{
				"subring(field_ring(L), S)",
				"finite(E)",
				"E ⊆ B",
				"image(d, E) ⊆ L.carrier",
				"∀x:A. x ∈ L.carrier ⇒ x = module_sum(L.add, L.zero, E, λe:A. l(x * e) * d(e))",
			},
			Conclusion: "«Dual» ⊆ «DualSpan»",
			Abbrev: Abbrev{
				{Name: "DualSpan", Text: "module_span(restrict_ring(field_ring(L), S), " +
					"    regular_module(field_ring(L)), " +
					"    image(d, E))"},
			},
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			l *Arrow[A, A],
			S, B, E *Expr[Set[A]],
			d *Arrow[A, A],
			subS, finiteE, basisInB, dInL, expansion Fact,
		) {
			rS := a.TermAs[RingOps[A]]("«ScalarS»")
			regular := a.TermAs[module_record.ModuleOps[A, A]]("«Regular»")
			duals := a.TermAs[Set[A]]("image(d, E)")
			span := a.TermAs[Set[A]]("«DualSpan»")
			moduleS := a.Have(
				"L is a module over S",
				"module_on(«ScalarS», «Regular»)",
				By(subS, fractional_ideal.FieldModuleOn.Read(L).At(S)))
			subSpan := a.Have(
				"the dual basis spans an S-submodule of L",
				"submodule(«ScalarS», «Regular», «DualSpan»)",
				By(moduleS, dInL, submodule.SpanSubmodule.At(rS, regular, duals)))
			generators := submodule.SubsetSpan.At(rS, regular, duals)
			a.Show(
				"each member of the dual is an S-combination of the dual basis",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					tests := b.Conjuncts(
						b.Simplified(b.Assume(), Fwd(FunctionalDualMember)),
						"x lies in L",
						"its pairings with B lie in S")
					terms := b.Have(
						"each expansion term lies in the S-span",
						"∀f:A. f ∈ E ⇒ l(x * f) * d(f) ∈ «DualSpan»",
						Derive(func(term *Argument) {
							term.FixAs[A]("f")
							fIn := term.Assume()
							df := term.TermAs[A]("d(f)")
							inSpan := term.MemberOf[on.Any](df, term.Have(
								"d(f) is a generator of the span",
								"d(f) ∈ «DualSpan»",
								BySets(fIn, generators)))
							coefficient := term.MemberOf[on.Any](term.TermAs[A]("l(x * f)"), term.Have(
								"the coefficient lies in S",
								"l(x * f) ∈ S",
								BySets(fIn, tests[1], basisInB)))
							term.Show(
								"the span is closed under S-multiples",
								By(submodule.SubmoduleSmul.Read(subSpan).At(coefficient, inSpan)))
						}))
					sum := b.Have(
						"the finite sum of expansion terms lies in the span",
						"module_sum(L.add, L.zero, E, λf:A. l(x * f) * d(f)) ∈ «DualSpan»",
						By(
							subSpan,
							finiteE,
							terms,
							submodule.SubmoduleModuleSum.Read(moduleS).At(
								span, E, b.TermAs[Fun[A, A]]("λf:A. l(x * f) * d(f)"))))
					b.Show(
						"that expansion is x",
						By(sum, expansion.At(x), tests[0]))
				}))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			L field.FieldFact[on.L],
			K *Expr[Set[A]],
			l *Arrow[A, A],
			S, B, E *Expr[Set[A]],
			subK, linear, nonzero, sInK, sInB, subS, subringB, fractionB, finiteE, basisB, basisE Fact,
		) {
			rL, rS := a.TermAs[RingOps[A]]("field_ring(L)"), a.TermAs[RingOps[A]]("«ScalarS»")
			rB := a.TermAs[RingOps[A]]("«ScalarB»")
			regular := a.TermAs[module_record.ModuleOps[A, A]]("«Regular»")
			dual := a.TermAs[Set[A]]("«Dual»")
			latticeB := a.Have(
				"B is an S-submodule of L",
				"submodule(«ScalarS», «Regular», B)",
				By(
					subringB,
					sInB,
					fractional_ideal.SubringSubmodule.Read(L).At(B),
					submodule.SubmoduleRestrictScalars.At(rB, regular, B, rS)))
			scalars := a.Have(
				"S is an S-submodule of K",
				"submodule(«ScalarS», «VectorsK», S)",
				By(
					subS,
					sInK,
					fractional_ideal.SubringSubmodule.Read(L).At(S),
					submodule.SubmoduleRestrict.At(rS, regular, K, S)))
			d, data := a.UnpackAs[Fun[A, A]](
				GroupPremises(
					subK,
					linear,
					nonzero,
					sInK,
					subS,
					finiteE,
					basisB,
					basisE,
					latticeB,
					scalars,
					Read(dualBasis, L).At(K, l, S, B, E)),
				"d")
			parts := a.Conjuncts(
				data,
				"the dual basis lies in the dual",
				"the dual is nonzero",
				"the dual basis expands L")
			dInDual, nonzero, expansion := parts[0], parts[1], parts[2]
			fractional := a.Have(
				"the dual is a B-submodule of L",
				"submodule(«ScalarB», «Regular», «Dual»)",
				By(linear, subringB, scalars, FunctionalDualSubmodule.Read(L).At(K, l, S, B, S)))
			dInL := a.Have(
				"the dual basis lies in L",
				"image(d, E) ⊆ L.carrier",
				BySets(dInDual, submodule.SubmoduleSubset.Read(fractional)))
			bound := a.Have(
				"the dual lies in the finite S-span of its basis",
				"«Dual» ⊆ module_span(«ScalarS», «Regular», image(d, E))",
				By(
					subS,
					finiteE,
					linear_independence.BasisInCarrier.Read(basisB),
					dInL,
					expansion,
					Read(spanBound, L).At(l, S, B, E, d)))
			a.Show(
				"a common denominator of that span bounds the nonzero B-submodule",
				By(
					fractional,
					nonzero,
					subS,
					subringB,
					fractionB,
					latticeB,
					finiteE,
					dInL,
					bound,
					finite_set.FiniteImage.At(d, E),
					integral_element.FiniteSpanCommonDenominator.Read(L).At(
						S, B, a.TermAs[Set[A]]("image(d, E)"), dual),
					integral_element.BoundedFractionalDef.At(rL, B, dual)))
		})
	}),
})}

// FunctionalDualBoundedInvertible — when every nonzero ideal of B is
// invertible, the functional dual of a finite free lattice is a bounded
// invertible fractional ideal: it is bounded, and under that hypothesis the
// bounded fractional ideals are the invertible ones.
var FunctionalDualBoundedInvertible = functionalDualBoundedInvertibleThm{family.Add(registry.ProofEntry{
	Name: "FunctionalDualBoundedInvertible",
	Key:  "prop_781acc1a7b1e2b2d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀l:(A → A). ∀S B E:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"module_homomorphism(«ScalarK», «Regular», «VectorsK», l)",
			"∃x:A. x ∈ L.carrier ∧ l(x) ≠ L.zero",
			"S ⊆ K",
			"S ⊆ B",
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"fraction_field_carrier(field_ring(L), B)",
			"finite(E)",
			"module_basis(«ScalarS», «VectorsB», E)",
			"module_basis(«ScalarK», «Regular», E)",
			"∀I:set(A). ring_ideal(«ScalarB», I) ∧ I ≠ {L.zero} ⇒ invertible_fractional(field_ring(L), B, I)",
		},
		Conclusion: "bounded_fractional(field_ring(L), B, «Dual») ∧ " +
			"invertible_fractional(field_ring(L), B, «Dual»)",
		Abbrev: Abbrev{
			{Name: "Dual", Text: "functional_dual(field_ring(L), l, B, S)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		K *Expr[Set[A]],
		l *Arrow[A, A],
		S, B, E *Expr[Set[A]],
		subK, linear, nonzeroValue, sInK, sInB, subS, subringB, fractionB, finiteE, basisB, basisK, allInvertible Fact,
	) {
		bounded := a.Have(
			"the dual is a bounded fractional ideal",
			"bounded_fractional(field_ring(L), B, «Dual»)",
			By(
				subK,
				linear,
				nonzeroValue,
				sInK,
				sInB,
				subS,
				subringB,
				fractionB,
				finiteE,
				basisB,
				basisK,
				FunctionalDualBounded.Read(L).At(K, l, S, B, E)))
		a.Show(
			"every nonzero ideal being invertible, a bounded fractional ideal is invertible",
			By(
				bounded,
				subringB,
				fractionB,
				allInvertible,
				ideal_factorization.FractionalIdealInvertibleIffBounded.Read(L).At(B, a.TermAs[Set[A]]("«Dual»"))))
	}),
})}

// FunctionalDualSubset — the dual of B valued in N lies in the ring: it collects
// members of the ring.
var FunctionalDualSubset = functionalDualSubsetThm{family.Add(registry.ProofEntry{
	Name: "FunctionalDualSubset",
	Key:  "prop_beeaf88c8d5c69d",
	Build: family.Theorem("∀R:ring_ops(A). ∀l:(A → A). ∀B N:set(A). "+
		"    functional_dual(R, l, B, N) ⊆ R.carrier",
		func(a *Argument, R *Expr[RingOps[A]], l *Arrow[A, A], B, N *Expr[Set[A]]) {
			a.Show(
				"the dual collects the members of the ring passing the test against B",
				Simp(Fwd(FunctionalDualDef)),
				BySets())
		}),
})}

// FunctionalDualOnBasis — the test of the dual need only be run on a basis E of
// B over S: B is an S-submodule of L spanned by E, and the dual of B is the dual
// of what generates it (FunctionalDualGenerators).
var FunctionalDualOnBasis = functionalDualOnBasisThm{family.Add(registry.ProofEntry{
	Name: "FunctionalDualOnBasis",
	Key:  "prop_36e52c1574fa7348",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀F:set(A). ∀l:(A → A). ∀S B E N:set(A). ∀z:A.",
		Hypotheses: []string{
			"subfield(L, F)",
			"«functional»",
			"S ⊆ F",
			"S ⊆ B",
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"module_basis(«rings»(S), «vectors»(B), E)",
			"submodule(«rings»(S), «vectors»(F), N)",
			"z ∈ L.carrier",
			"∀e:A. e ∈ E ⇒ l(z * e) ∈ N",
		},
		Conclusion: "z ∈ functional_dual(field_ring(L), l, B, N)",
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
			S, B, E, N *Expr[Set[A]],
			z *Expr[A],
			subfieldF, linear, sInF, sInB, subringS, subringB, basisE, submoduleN, zIn, onE Fact,
		) {
			basis := a.Conjuncts(
				a.Unfolded(basisE, linear_independence.ModuleBasisDef),
				"E is independent over S, so it lies in B",
				"E spans B over S")
			generated := a.Have(
				"the dual of B is the dual of its generating set E",
				"functional_dual(field_ring(L), l, B, N) = functional_dual(field_ring(L), l, E, N)",
				By(
					subfieldF,
					sInF,
					subringS,
					linear,
					subringB,
					sInB,
					principal_ideal_domain.ConstantSubringSubmodule.Read(L).At(S, B),
					submoduleN,
					linear_independence.IndependentInCarrier.Read(basis[0]),
					basis[1],
					FunctionalDualGenerators.Read(L).At(F, l, S, B, N, E)))
			a.Show(
				"and z lies in L and passes the test on E",
				generated.Rw(),
				By(zIn, onE, FunctionalDualMember.At(a.TermAs[RingOps[A]]("field_ring(L)"), l, E, N, z)))
		}),
})}

// FunctionalDualChartImage — let the pairing map carry the dual of B onto C,
// and let X lie in B with the dual of X valued in P inside the dual of B. Then
// the pairing map carries that dual onto the maps of C taking X into P: on X
// the pairing with z reads l(z * b), so z passes the test of X exactly when its
// pairing takes X into P.
var FunctionalDualChartImage = functionalDualChartImageThm{family.Add(registry.ProofEntry{
	Name: "FunctionalDualChartImage",
	Key:  "prop_e07fa74a9fa29d0b",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀l:(A → A). ∀B X N P:set(A). ∀C:set(A → A). ∀o:A.",
		Hypotheses: []string{
			"X ⊆ B",
			"«part» ⊆ «whole»",
			"image(«pairing», «whole») = C",
		},
		Conclusion: "image(«pairing», «part») = «maps»",
		Abbrev: Abbrev{
			{Name: "whole", Text: "functional_dual(R, l, B, N)"},
			{Name: "part", Text: "functional_dual(R, l, X, P)"},
			{Name: "pairing", Text: "λz:A. λb:A. COND(b ∈ B, l(z * b), o)"},
			{Name: "maps", Text: "{φ:A → A | φ ∈ C ∧ image(φ, X) ⊆ P}"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			l *Arrow[A, A],
			B, X, N, P *Expr[Set[A]],
			C *Expr[Set[Fun[A, A]]],
			o *Expr[A],
			xInB, nested, onto Fact,
		) {
			pairing := a.TermAs[Fun2[A, A, A]]("«pairing»")
			part, whole := a.TermAs[Set[A]]("«part»"), a.TermAs[Set[A]]("«whole»")
			maps := a.TermAs[Set[Fun[A, A]]]("«maps»")
			member := a.Have(
				"a map lies in the set exactly when it lies in C and carries X into P",
				"∀φ:(A → A). φ ∈ «maps» ⇔ φ ∈ C ∧ image(φ, X) ⊆ P",
				BySets())
			forward := a.Have(
				"pairing with an element of the dual of X is a map of C carrying X into P",
				"∀z:A. z ∈ «part» ⇒ (λb:A. COND(b ∈ B, l(z * b), o)) ∈ «maps»",
				Derive(func(c *Argument) {
					z := c.FixAs[A]("z")
					zIn := c.Assume()
					passes := c.Conjuncts(
						c.Have(
							"z passes the test of X",
							"z ∈ R.carrier ∧ (∀b:A. b ∈ X ⇒ l(z * b) ∈ P)",
							By(zIn, FunctionalDualMember.At(R, l, X, P, z))),
						"z lies in the ring",
						"z passes the test of X")[1]
					inWhole := c.Have(
						"z lies in the dual of B",
						"z ∈ «whole»",
						By(zIn, nested, set_basic.SubsetDef))
					cut := c.TermAs[Fun[A, A]]("λb:A. COND(b ∈ B, l(z * b), o)")
					inC := c.Have(
						"so its pairing lies in C",
						"(λb:A. COND(b ∈ B, l(z * b), o)) ∈ C",
						onto.RwRev(),
						By(inWhole, set_image.FunInImage.At(pairing, whole, z)))
					values := c.Have(
						"on X the pairing reads the values of the test",
						"∀x:A. x ∈ X ⇒ (λb:A. COND(b ∈ B, l(z * b), o))(x) ∈ P",
						Derive(func(d *Argument) {
							x := d.FixAs[A]("x")
							xIn := d.Assume()
							inB := d.Have(
								"x lies in B",
								"x ∈ B",
								By(xIn, xInB, set_basic.SubsetDef))
							d.Show(
								"where z passes",
								By(inB, passes.At(x), xIn))
						}))
					carried := c.Have(
						"so the pairing carries X into P",
						"image(λb:A. COND(b ∈ B, l(z * b), o), X) ⊆ P",
						By(values, set_image.ImageSubsetIff.At(cut, X, P)))
					c.Show(
						"which puts it in the set",
						By(member.At(cut), inC, carried))
				}))
			backward := a.Have(
				"a map of C carrying X into P is the pairing with an element of the dual of X",
				"∀φ:(A → A). φ ∈ «maps» ⇒ φ ∈ image(«pairing», «part»)",
				Derive(func(c *Argument) {
					φ := c.FixAs[Fun[A, A]]("φ")
					φIn := c.Assume()
					parts := c.Conjuncts(
						c.Have(
							"φ lies in C and carries X into P",
							"φ ∈ C ∧ image(φ, X) ⊆ P",
							By(member.At(φ), φIn)),
						"φ lies in C",
						"φ carries X into P")
					inImage := c.Have(
						"so φ is the image of a member of the dual of B",
						"φ ∈ image(«pairing», «whole»)",
						onto.Rw(),
						By(parts[0]))
					y, written := c.UnpackAs[A](
						c.Have(
							"write φ as the pairing with y",
							"∃y:A. φ = (λb:A. COND(b ∈ B, l(y * b), o)) ∧ y ∈ «whole»",
							By(inImage, set_basic.InImage.At(pairing, whole, φ))),
						"y")
					form := c.Conjuncts(
						written,
						"φ is the pairing with y",
						"y lies in the dual of B")
					inRing := c.Conjuncts(
						c.Have(
							"y lies in the ring",
							"y ∈ R.carrier ∧ (∀b:A. b ∈ B ⇒ l(y * b) ∈ N)",
							By(form[1], FunctionalDualMember.At(R, l, B, N, y))),
						"y lies in the ring",
						"y passes the test of B")[0]
					passes := c.Have(
						"y passes the test of X: its values on X are those of φ",
						"∀b:A. b ∈ X ⇒ l(y * b) ∈ P",
						Derive(func(d *Argument) {
							d.FixAs[A]("b")
							bIn := d.Assume()
							value := d.Have(
								"φ carries b into P",
								"φ(b) ∈ P",
								By(parts[1], bIn, set_image.ImageSubsetIff.At(φ, X, P)))
							inB := d.Have(
								"b lies in B",
								"b ∈ B",
								By(bIn, xInB, set_basic.SubsetDef))
							d.Show(
								"on B, φ reads l(y * b)",
								By(value, form[0], inB))
						}))
					inPart := c.Have(
						"so y lies in the dual of X",
						"y ∈ «part»",
						By(inRing, passes, FunctionalDualMember.At(R, l, X, P, y)))
					expressed := c.Have(
						"so φ is the pairing with a member of the dual of X",
						"∃w:A. φ = (λb:A. COND(b ∈ B, l(w * b), o)) ∧ w ∈ «part»",
						Derive(func(d *Argument) {
							d.Take(y)
							d.Show(
								"y is one",
								By(form[0], inPart))
						}))
					c.Show(
						"which is membership in the image",
						By(expressed, set_basic.InImage.At(pairing, part, φ)))
				}))
			a.Show(
				"so the image is the set",
				By(
					forward,
					set_image.ImageSubsetIff.At(pairing, part, maps),
					backward,
					set_basic.SubsetDef.At(maps, a.TermAs[Set[Fun[A, A]]]("image(«pairing», «part»)")),
					set_order.SubsetAntisym.At(a.TermAs[Set[Fun[A, A]]]("image(«pairing», «part»)"), maps)))
		}),
})}

// FunctionalDualValueScale — scaling the target of a dual by a nonzero scalar w
// of F scales the dual: l is F-linear, so l((w * x) * b) = w * l(x * b), and
// inv(w) undoes the scaling. Only a scalar of F moves through l.
var FunctionalDualValueScale = functionalDualValueScaleThm{family.Add(registry.ProofEntry{
	Name: "FunctionalDualValueScale",
	Key:  "prop_23431ea78deb71a9",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀F:set(A). ∀l:(A → A). ∀B N:set(A). ∀w:A.",
		Hypotheses: []string{
			"subfield(L, F)",
			"«functional»",
			"B ⊆ L.carrier",
			"N ⊆ F",
			"w ∈ F",
			"w ≠ L.zero",
		},
		Conclusion: "image(L.mul(w), «dual») = «scaledDual»",
		Abbrev: Abbrev{
			{Name: "rings", Text: "restrict_ring(field_ring(L))"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(L)))"},
			{Name: "functional", Text: "module_homomorphism(«rings»(F), " +
				"    regular_module(field_ring(L)), " +
				"    «vectors»(F), " +
				"    l)"},
			{Name: "dual", Text: "functional_dual(field_ring(L), l, B, N)"},
			{Name: "scaledDual", Text: "functional_dual(field_ring(L), l, B, image(L.mul(w), N))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			F *Expr[Set[A]],
			l *Arrow[A, A],
			B, N *Expr[Set[A]],
			w *Expr[A],
			subfieldF, linear, bInL, nInF, wIn, nonzero Fact,
		) {
			ring := field.RingOn.Read(L)
			record := a.TermAs[FieldOps[A]]("L")
			carrierRing := a.TermAs[RingOps[A]]("field_ring(L)")
			scaling := a.TermAs[Fun[A, A]]("L.mul(w)")
			scaledValues := a.TermAs[Set[A]]("image(L.mul(w), N)")
			dual, scaledDual := a.TermAs[Set[A]]("«dual»"), a.TermAs[Set[A]]("«scaledDual»")
			scalarsInL := a.Have(
				"F lies in L",
				"F ⊆ L.carrier",
				By(subfieldF, field.SubfieldSubset.At(record, F)))
			moves := a.Have(
				"a scalar of F moves out of the pairing",
				"∀c x b:A. c ∈ F ∧ x ∈ L.carrier ∧ b ∈ B ⇒ l((c * x) * b) = c * l(x * b)",
				Derive(func(d *Argument) {
					c, x, b := d.FixAs[A]("c"), d.FixAs[A]("x"), d.FixAs[A]("b")
					places := d.Conjuncts(
						d.Assume(),
						"c lies in F",
						"x lies in L",
						"b lies in B")
					cm := d.MemberOf[on.L](c, d.Have(
						"c lies in L",
						"c ∈ L.carrier",
						BySets(places[0], scalarsInL)))
					xm := d.MemberOf[on.L](x, places[1])
					bm := d.MemberOf[on.L](b, d.Have(
						"b lies in L",
						"b ∈ L.carrier",
						BySets(places[2], bInL)))
					moved := d.Have(
						"the product regroups around c",
						"(c * x) * b = c * (x * b)",
						ByArith(L, cm, xm, bm))
					d.Show(
						"l is linear over F",
						moved.Rw(),
						By(
							places[0],
							comm_ring.MulIn.Read(ring).At(xm, bm),
							module_homomorphism.HomSmul.Read(linear).AsFact().At(c, d.TermAs[A]("x * b"))))
				}))
			wm := a.MemberOf[on.L](w, a.Have(
				"w lies in L",
				"w ∈ L.carrier",
				BySets(wIn, scalarsInL)))
			into := a.Have(
				"w times a member of the dual passes the scaled test",
				"∀x:A. x ∈ «dual» ⇒ w * x ∈ «scaledDual»",
				Derive(func(c *Argument) {
					x := c.FixAs[A]("x")
					xIn := c.Assume()
					ofX := c.Conjuncts(
						c.Have(
							"x lies in L and passes the test",
							"x ∈ L.carrier ∧ (∀b:A. b ∈ B ⇒ l(x * b) ∈ N)",
							By(xIn, FunctionalDualMember.At(carrierRing, l, B, N, x))),
						"x lies in L",
						"x passes the test")
					tests := c.Have(
						"its values are w times the values of x",
						"∀b:A. b ∈ B ⇒ l((w * x) * b) ∈ image(L.mul(w), N)",
						Derive(func(d *Argument) {
							b := d.FixAs[A]("b")
							bIn := d.Assume()
							value := d.TermAs[A]("l(x * b)")
							d.Show(
								"w times a member of N lies in w N",
								GroupPremises(wIn, ofX[0], bIn, moves.At(w, x, b)).Rw(),
								By(ofX[1].At(b), bIn, set_image.FunInImage.At(scaling, N, value)))
						}))
					c.Show(
						"w * x lies in L and passes the scaled test",
						By(
							comm_ring.MulIn.Read(ring).At(wm, c.MemberOf[on.L](x, ofX[0])),
							tests,
							FunctionalDualMember.At(carrierRing, l, B, scaledValues, c.TermAs[A]("w * x"))))
				}))
			inverseIn := a.Have(
				"inv(w) lies in F",
				"L.inv(w) ∈ F",
				By(subfieldF, wIn, field.SubfieldInv.At(record, F, w)))
			inverse := a.MemberOf[on.L](a.TermAs[A]("L.inv(w)"), a.Have(
				"so it lies in L",
				"L.inv(w) ∈ L.carrier",
				BySets(inverseIn, scalarsInL)))
			cancels := a.Have(
				"inv(w) * w = 1",
				"L.inv(w) * w = L.one",
				By(wm, nonzero, field.MulLeftInverseOn.Read(L).AsFact().At(w)))
			back := a.Have(
				"inv(w) times a member of the scaled dual passes the test",
				"∀z:A. z ∈ «scaledDual» ⇒ L.inv(w) * z ∈ «dual»",
				Derive(func(c *Argument) {
					z := c.FixAs[A]("z")
					zIn := c.Assume()
					ofZ := c.Conjuncts(
						c.Have(
							"z lies in L and passes the scaled test",
							"z ∈ L.carrier ∧ (∀b:A. b ∈ B ⇒ l(z * b) ∈ image(L.mul(w), N))",
							By(zIn, FunctionalDualMember.At(carrierRing, l, B, scaledValues, z))),
						"z lies in L",
						"z passes the scaled test")
					tests := c.Have(
						"the values of inv(w) * z are those of z divided by w",
						"∀b:A. b ∈ B ⇒ l((L.inv(w) * z) * b) ∈ N",
						Derive(func(d *Argument) {
							b := d.FixAs[A]("b")
							bIn := d.Assume()
							value := d.TermAs[A]("l(z * b)")
							n, written := d.UnpackAs[A](
								d.Have(
									"the value of z at b is w * n for an n of N",
									"∃n:A. l(z * b) = L.mul(w, n) ∧ n ∈ N",
									By(ofZ[1].At(b), bIn, set_basic.InImage.At(scaling, N, value))),
								"n")
							form := d.Conjuncts(
								written,
								"the value is w * n",
								"n lies in N")
							nm := d.MemberOf[on.L](n, d.Have(
								"n lies in L",
								"n ∈ L.carrier",
								BySets(form[1], nInF, scalarsInL)))
							undone := d.Have(
								"inv(w) * (w * n) = n",
								"L.inv(w) * (w * n) = n",
								ByArith(L, wm, inverse, nm, Scaled(n, cancels)))
							d.Show(
								"so the value of inv(w) * z is n",
								GroupPremises(inverseIn, ofZ[0], bIn, moves.At(d.TermAs[A]("L.inv(w)"), z, b)).Rw(),
								form[0].Rw(),
								undone.Rw(),
								By(form[1]))
						}))
					c.Show(
						"inv(w) * z lies in L and passes the test",
						By(
							comm_ring.MulIn.Read(ring).At(inverse, c.MemberOf[on.L](z, ofZ[0])),
							tests,
							FunctionalDualMember.At(carrierRing, l, B, N, c.TermAs[A]("L.inv(w) * z"))))
				}))
			image := a.TermAs[Set[A]]("image(L.mul(w), «dual»)")
			forward := a.Have(
				"the scaled dual holds w times the dual",
				"image(L.mul(w), «dual») ⊆ «scaledDual»",
				By(into, set_image.ImageSubsetIff.At(scaling, dual, scaledDual)))
			backward := a.Have(
				"and every member of it is w times a member of the dual",
				"«scaledDual» ⊆ image(L.mul(w), «dual»)",
				Derive(func(b *Argument) {
					b.Do(Unfold(set_basic.SubsetDef))
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					xm := b.MemberOf[on.L](x, b.Have(
						"x lies in L",
						"x ∈ L.carrier",
						By(xIn, FunctionalDualMember.At(carrierRing, l, B, scaledValues, x))))
					restored := b.Have(
						"x is w * (inv(w) * x)",
						"w * (L.inv(w) * x) = x",
						ByArith(L, wm, inverse, xm, Scaled(x, cancels)))
					expressed := b.Have(
						"so x is w times a member of the dual",
						"∃y:A. x = L.mul(w, y) ∧ y ∈ «dual»",
						Derive(func(c *Argument) {
							c.Take(c.TermAs[A]("L.inv(w) * x"))
							c.Show(
								"inv(w) * x is one",
								By(restored, back.At(x), xIn))
						}))
					b.Show(
						"which is membership in the image",
						By(expressed, set_basic.InImage.At(scaling, dual, x)))
				}))
			a.Show(
				"so the two sets are equal",
				By(forward, backward, set_order.SubsetAntisym.At(image, scaledDual)))
		}),
})}

// SubringInFieldSubmodule — a subring S of M inside a subfield F is a submodule
// of F over itself: F is a module over S, and S holds zero and is closed under
// sums and products.
var SubringInFieldSubmodule = subringInFieldSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "SubringInFieldSubmodule",
	Key:  "prop_d38db842446e7f73",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀F S:set(A).",
		Hypotheses: []string{
			"subfield(M, F)",
			"S ⊆ F",
			"subring(field_ring(M), S)",
		},
		Conclusion: "submodule(«rings»(S), «vectors»(F), S)",
		Abbrev: Abbrev{
			{Name: "rings", Text: "restrict_ring(field_ring(M))"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(M)))"},
		},
	},
		func(a *Argument, M field.FieldFact[on.M], F, S *Expr[Set[A]], subfieldF, sInF, subringS Fact) {
			ring := field.RingOn.Read(M)
			ringOps := a.TermAs[RingOps[A]]("field_ring(M)")
			fieldOps := a.TermAs[RingOps[A]]("«rings»(F)")
			fieldVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(F)")
			fieldRing := a.Have(
				"F is a ring under M's operations",
				"comm_ring_on(«rings»(F))",
				By(
					subfieldF,
					field_extension.SubfieldScalars.Read(M).At(F),
					comm_ring.SubringRingOn.Read(ring).At(F)))
			subringRing := a.Have(
				"S is a ring under M's operations",
				"comm_ring_on(«rings»(S))",
				By(subringS, comm_ring.SubringRingOn.Read(ring).At(S)))
			twice := module_record.RestrictRingTwice.At(ringOps, F, S)
			subringOfF := a.Have(
				"so S is a subring of F",
				"subring(«rings»(F), S)",
				By(Normalized, subringRing, sInF, comm_ring.SubringRingOn.Read(fieldRing).At(S), twice))
			overS := a.Have(
				"F, a module over itself, is a module over S",
				"module_on(«rings»(S), «vectors»(F))",
				By(
					Normalized,
					subfieldF,
					set_order.SubsetRefl.At(F),
					field_extension.ExtensionModuleOn.Read(M).At(F, F),
					subringOfF,
					module.ModuleRestrictScalars.At(fieldOps, fieldVectors, S),
					twice))
			a.Show(
				"S lies in F, holds zero and is closed under sums and products",
				By(
					overS,
					sInF,
					comm_ring.ZeroIn.Read(subringRing),
					comm_ring.AddIn.Read(subringRing),
					comm_ring.MulIn.Read(subringRing),
					submodule.SubmoduleCriterion.At(a.TermAs[RingOps[A]]("«rings»(S)"), fieldVectors, S)))
		}),
})}
