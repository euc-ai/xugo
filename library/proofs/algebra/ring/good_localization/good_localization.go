// good_localization.go — the chapter: what holds over the fractions of a
// subring S already holds after inverting one nonzero element of S. First a
// Bezout certificate: a separable polynomial over S is coprime to its
// derivative over L, and one denominator in S clears the coefficients of both
// multipliers (SeparablePolynomialGoodOpen). Then two finite models: two
// subrings of L, finite as S-modules and with fraction field L, agree after
// inverting one nonzero element of S (FiniteModelsAgreeAfterLocalization),
// and they do so read in a subfield K of an ambient field M with the
// operations of M (ModelsAgreeInSubfield).

package good_localization

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// SeparablePolynomialGoodOpen — a separable polynomial over a
// fraction-field subring has a Bezout certificate with a nonzero constant a
// in the subring, so the good open is the locus S[1/a], where F stays
// separable: clear the coefficients of its two separability multipliers.
var SeparablePolynomialGoodOpen = separablePolynomialGoodOpenThm{family.Add(registry.ProofEntry{
	Name: "SeparablePolynomialGoodOpen",
	Key:  "prop_89e061efdba2a099",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀F:(num → A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"fraction_field_carrier(field_ring(L), S)",
			"polynomial_over(S, F)",
			"polynomial_separable(field_ring(L), F)",
		},
		Conclusion: "∃a:A. ∃U W:(num → A). " +
			"    a ∈ S ∧ " +
			"    a ≠ L.zero ∧ " +
			"    polynomial_over(S, U) ∧ " +
			"    polynomial_over(S, W) ∧ " +
			"    fun_add(polynomial_mul(U, F), polynomial_mul(W, polynomial_derivative(F))) = " +
			"    λn:num. COND(n = 0, a, L.zero)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		commonDenominator := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀S:set(A). ∀p q:(num → A).",
			Hypotheses: []string{
				"subring(field_ring(L), S)",
				"fraction_field_carrier(field_ring(L), S)",
				"polynomial_over(L.carrier, p)",
				"polynomial_over(L.carrier, q)",
			},
			Conclusion: "∃d:A. d ∈ S ∧ d ≠ L.zero ∧ polynomial_over(S, d • p) ∧ polynomial_over(S, d • q)",
			Abbrev: Abbrev{
				{Name: "coefficients", Text: "insert(L.zero, " +
					"    image(p, fun_support(L.zero, p)) ∪ image(q, fun_support(L.zero, q)))"},
			},
		}, func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], p, q *Arrow[Nat, A], h Fact) {
			ring := field.RingOn.Read(L)
			zero := a.TermAs[A]("L.zero")
			carrier := a.TermAs[Set[A]]("L.carrier")
			coefficients := a.TermAs[Set[A]]("«coefficients»")
			finiteCoefficients := a.Have(
				"the two polynomials have finitely many coefficient values",
				"finite(«coefficients»)",
				By(
					h,
					polynomial.PolynomialFiniteSupport.At(zero, carrier, p),
					polynomial.PolynomialFiniteSupport.At(zero, carrier, q),
					finite_set.FiniteImage.At(p, a.TermAs[Set[Nat]]("fun_support(L.zero, p)")),
					finite_set.FiniteImage.At(q, a.TermAs[Set[Nat]]("fun_support(L.zero, q)")),
					finite_set.FiniteUnionImp,
					finite_set.FiniteInsert))
			inCarrier := a.Have(
				"every coefficient value lies in the field",
				"«coefficients» ⊆ L.carrier",
				BySets(comm_ring.ZeroIn.Read(ring), h, polynomial.PolynomialOverDef))
			overCoefficients := a.Have(
				"polynomial_over asks every term to lie in the set, the vanishing ones too, so it holds zero",
				"polynomial_over(«coefficients», p) ∧ polynomial_over(«coefficients», q)",
				BySets(h, polynomial.PolynomialOverDef))
			d, denominator := a.ObtainAs[A](
				"one denominator clears the finite coefficient set",
				"∃d:A. d ∈ S ∧ d ≠ L.zero ∧ image(L.mul(d), «coefficients») ⊆ S",
				By(
					L,
					h,
					finiteCoefficients,
					inCarrier,
					integral_element.FiniteCommonDenominator.Read(L).At(S, coefficients)))
			dInCarrier := a.Have(
				"the denominator lies in the field",
				"d ∈ L.carrier",
				By(denominator, h, comm_ring.SubringSubset, set_basic.SubsetDef.At(S, carrier)))
			dm := a.MemberOf[on.L](d, dInCarrier)
			clearsCoefficients := a.Have(
				"multiplication by the denominator sends every coefficient into the subring",
				"∀x:A. x ∈ «coefficients» ⇒ d * x ∈ S",
				BySets(denominator))
			scale := a.TermAs[Fun[A, A]]("L.mul(d)")
			a.Show(
				"the same nonzero denominator clears both polynomials",
				Witness(d),
				Simp(Fwd(vec_space.VecScalarMulDef)),
				By(
					denominator,
					overCoefficients,
					comm_ring.MulRightZeroOn.Read(ring).At(dm),
					clearsCoefficients,
					polynomial.PolynomialOverMap.At(scale, zero, zero, coefficients, S, p),
					polynomial.PolynomialOverMap.At(scale, zero, zero, coefficients, S, q)))
		})
		return ctx.Theorem(headline,
			func(
				a *Argument,
				L field.FieldFact[on.L],
				S *Expr[Set[A]],
				F *Arrow[Nat, A],
				subring, fractions, overF, separable Fact,
			) {
				ring := field.RingOn.Read(L)
				zero := a.TermAs[A]("L.zero")
				carrier := a.TermAs[Set[A]]("L.carrier")
				u, v, bezout := a.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
					a.Unfolded(separable, separable_polynomial.PolynomialSeparableDef), "u", "v")
				d, denominator := a.ObtainAs[A](
					"clear both separability multipliers with one denominator",
					"∃d:A. d ∈ S ∧ d ≠ L.zero ∧ polynomial_over(S, d • u) ∧ polynomial_over(S, d • v)",
					By(L, fractions, subring, bezout, At(commonDenominator, a.TermAs[FieldOps[A]]("L"), S, u, v)))
				du := a.TermAs[Fun[Nat, A]]("d • u")
				dv := a.TermAs[Fun[Nat, A]]("d • v")
				derivative := a.TermAs[Fun[Nat, A]]("polynomial_derivative(F)")
				fieldPolynomials := a.Have(
					"the scalar and the polynomial factors lie in the field",
					"d ∈ L.carrier ∧ "+
						"polynomial_over(L.carrier, F) ∧ "+
						"polynomial_over(L.carrier, polynomial_derivative(F)) ∧ "+
						"polynomial_over(L.carrier, d • u) ∧ "+
						"polynomial_over(L.carrier, d • v)",
					By(
						polynomial.DerivativeOverCarrier.Read(ring),
						subring,
						denominator,
						overF,
						comm_ring.SubringSubset,
						set_basic.SubsetDef.At(S, carrier),
						polynomial.PolynomialOverMono.At(zero, S, carrier, F),
						polynomial.PolynomialOverMono.At(zero, S, carrier, du),
						polynomial.PolynomialOverMono.At(zero, S, carrier, dv)))
				dInCarrier := a.Conjuncts(
					fieldPolynomials,
					"the denominator belongs to the field carrier",
					"F has its coefficients in the field",
					"so does its derivative",
					"so does d • u",
					"and so does d • v")[0]
				dm := a.MemberOf[on.L](d, dInCarrier)
				scaling := a.Have(
					"the scalar passes through multiplication by a polynomial",
					Statement{
						Binders: "∀p q:(num → A).",
						Hypotheses: []string{
							"polynomial_over(L.carrier, p)",
							"polynomial_over(L.carrier, d • p)",
							"polynomial_over(L.carrier, q)",
						},
						Conclusion: "polynomial_mul(d • p, q) = d • polynomial_mul(p, q)",
					},
					Derive(func(b *Argument) {
						p, q := b.FixAs[Fun[Nat, A]]("p"), b.FixAs[Fun[Nat, A]]("q")
						over := b.Assume()
						dp := b.TermAs[Fun[Nat, A]]("d • p")
						b.Show(
							"commute the scalar's factor to the right, take the scalar out, commute back",
							By(
								over,
								polynomial.PolynomialOverDef,
								polynomial.PolynomialMulComm.Read(ring).At(dp, q),
								polynomial.PolynomialMulScalar.Read(ring).At(dm, q, p),
								polynomial.PolynomialMulComm.Read(ring).At(q, p)))
					}))
				uF := a.TermAs[Fun[Nat, A]]("polynomial_mul(u, F)")
				vDerivative := a.TermAs[Fun[Nat, A]]("polynomial_mul(v, polynomial_derivative(F))")
				scaledBezout := a.Have(
					"the scaled multipliers give the denominator times the unit polynomial",
					"polynomial_mul(d • u, F) + polynomial_mul(d • v, polynomial_derivative(F)) = d • basis_vector(0)",
					By(
						scaling.At(u, F),
						scaling.At(v, derivative),
						fieldPolynomials,
						bezout,
						polynomial.PolynomialMulOver.Read(ring).At(u, F),
						polynomial.PolynomialMulOver.Read(ring).At(v, derivative),
						polynomial.PolynomialOverDef.At(zero, carrier, uF),
						polynomial.PolynomialOverDef.At(zero, carrier, vDerivative),
						vec_space.SmulAddLeftOn.Read(ring).At(dm, uF, vDerivative)))
				constant := a.Have(
					"the scaled unit polynomial is the constant denominator",
					"d • basis_vector(0) = λn:num. COND(n = 0, d, L.zero)",
					Simp(Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)),
					By(
						fieldPolynomials,
						comm_ring.MulRightZeroOn.Read(ring).At(dm),
						comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(dm)))
				pointwiseBezout := a.Unfolded(scaledBezout, vec_space.VecAddDef)
				a.Show(
					"the integral multipliers certify the nonzero constant",
					Witness(d),
					Witness(du),
					Witness(dv),
					Simp(Fwd(function_module.FunAddDef)),
					By(constant, pointwiseBezout, denominator))
			})
	}),
})}

// FiniteModelsAgreeAfterLocalization — two finite algebras over a common subring
// with the same fraction field agree after inverting one nonzero scalar:
// over the fraction field K of the scalars each model's finitely many
// generators span L (integral_element.FiniteSubringSpansField), and
// finite-module localization then supplies a common denominator.
var FiniteModelsAgreeAfterLocalization = finiteModelsAgreeAfterLocalizationThm{family.Add(registry.ProofEntry{
	Name: "FiniteModelsAgreeAfterLocalization",
	Key:  "prop_b99f2cccf3ca3e20",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀S B C:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"subring(field_ring(L), C)",
			"S ⊆ B",
			"S ⊆ C",
			"fraction_field_carrier(field_ring(L), B)",
			"fraction_field_carrier(field_ring(L), C)",
			"module_finitely_generated(«baseScalars», «restricted»(B))",
			"module_finitely_generated(«baseScalars», «restricted»(C))",
		},
		Conclusion: "∃a:A. " +
			"    a ∈ S ∧ a ≠ L.zero ∧ ring_away(field_ring(L), B, a) = ring_away(field_ring(L), C, a)",
		Abbrev: Abbrev{
			{Name: "ambient", Text: "regular_module(field_ring(L))"},
			{Name: "scalars", Text: "λK:set(A). restrict_ring(field_ring(L), K)"},
			{Name: "baseScalars", Text: "restrict_ring(field_ring(L), S)"},
			{Name: "restricted", Text: "λT:set(A). restrict_module(«ambient», T)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		modelSpansField := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀S K B:set(A).",
			Hypotheses: []string{
				"subring(field_ring(L), S)",
				"subfield(L, K)",
				"S ⊆ K",
				"subring(field_ring(L), B)",
				"submodule(«baseScalars», «ambient», B)",
				"fraction_field_carrier(field_ring(L), B)",
				"module_finitely_generated(«baseScalars», «restricted»(B))",
			},
			Conclusion: "module_span(«scalars»(K), «ambient», B) = L.carrier",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			S, K, B *Expr[Set[A]],
			subringS, subfieldK, sInK, subringB, bSubmodule, fractionsB, generated Fact,
		) {
			kRing := a.TermAs[module_record.RingOps[A]]("«scalars»(K)")
			sRing := a.TermAs[module_record.RingOps[A]]("«baseScalars»")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
			E, generators := a.UnpackAs[Set[A]](
				a.Unfolded(generated, principal_ideal_domain.FinitelyGeneratedDef), "E")
			ambientK := a.Have(
				"the ambient field is a K-vector space",
				"module_on(«scalars»(K), «ambient»)",
				By(subfieldK, field_extension.SubfieldScalars.Read(L).At(K)))
			eInL := a.Have(
				"the generators lie in the field",
				"E ⊆ L.carrier",
				By(generators, subringB, comm_ring.SubringSubset, set_order.SubsetTrans))
			sSpan := a.Have(
				"the generators span B in the ambient module",
				"module_span(«baseScalars», «ambient», E) = B",
				By(
					Normalized,
					subringS,
					fractional_ideal.FieldModuleOn.Read(L).At(S),
					bSubmodule,
					generators,
					linear_independence.SpanRestrict.At(sRing, ambient, B, E)))
			kSpan := a.Have(
				"over K, the model and its generators have one span",
				"module_span(«scalars»(K), «ambient», B) = module_span(«scalars»(K), «ambient», E)",
				By(ambientK, sInK, eInL, sSpan, submodule.SpanOfSubringSpan.At(kRing, ambient, sRing, E)))
			a.Show(
				"the finitely many generators span the field",
				kSpan.Rw(),
				By(
					subfieldK,
					subringB,
					fractionsB,
					generators,
					kSpan,
					submodule.SubsetSpan.At(kRing, ambient, B),
					integral_element.FiniteSubringSpansField.Read(L).At(K, B, E)))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			L field.FieldFact[on.L],
			S, B, C *Expr[Set[A]],
			h Fact,
		) {
			l := a.TermAs[FieldOps[A]]("L")
			r := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
			K, kDef := a.LetAs[Set[A]]("K", "field_adjoin(L, S, ∅)")
			fractions := a.Have(
				"adjoin the fraction field of the scalar subring",
				"subfield(L, K) ∧ S ⊆ K ∧ fraction_field_carrier(«scalars»(K), S)",
				By(Normalized, h, kDef, integral_element.SubringFractionField.Read(L).At(S)))
			sRing := a.TermAs[module_record.RingOps[A]]("«baseScalars»")
			bModule := a.Have(
				"the first model is an S-submodule",
				"submodule(«baseScalars», «ambient», B)",
				By(
					h,
					fractional_ideal.SubringSubmodule.Read(L).At(B),
					submodule.SubmoduleRestrictScalars.At(
						a.TermAs[module_record.RingOps[A]]("«scalars»(B)"), ambient, B, sRing)))
			cModule := a.Have(
				"the second model is an S-submodule",
				"submodule(«baseScalars», «ambient», C)",
				By(
					h,
					fractional_ideal.SubringSubmodule.Read(L).At(C),
					submodule.SubmoduleRestrictScalars.At(
						a.TermAs[module_record.RingOps[A]]("«scalars»(C)"), ambient, C, sRing)))
			bSpans := a.Have(
				"the first model spans L over K",
				"module_span(«scalars»(K), «ambient», B) = L.carrier",
				By(L, fractions, h, bModule, At(modelSpansField, l, S, K, B)))
			cSpans := a.Have(
				"the second model spans L over K",
				"module_span(«scalars»(K), «ambient», C) = L.carrier",
				By(L, fractions, h, cModule, At(modelSpansField, l, S, K, C)))
			moduleK := a.Have(
				"L is the common ambient K-module",
				"module_on(«scalars»(K), «ambient»)",
				By(fractions, field_extension.SubfieldScalars.Read(L).At(K)))
			d, localizes := a.ObtainAs[A](
				"one denominator clears both finite generating sets, so the two saturations at it agree",
				"∃d:A. "+
					"    d ∈ S ∧ "+
					"    d ≠ L.zero ∧ "+
					"    module_saturation(«baseScalars», «ambient», d, B) = "+
					"    module_saturation(«baseScalars», «ambient», d, C)",
				By(
					L,
					fractions,
					h,
					moduleK,
					bModule,
					cModule,
					bSpans,
					cSpans,
					principal_ideal_domain.FiniteModulesSameLocalization.At(l, S, K, ambient, B, C)))
			a.Show(
				"the two localizations agree",
				By(localizes, ring_away.SaturationIsAway.At(r, S, B, d), ring_away.SaturationIsAway.At(r, S, C, d)))
		})
	}),
})}

// ModelsAgreeInSubfield — FiniteModelsAgreeAfterLocalization read in a subfield K of
// M, the models and the scalars taken with the operations of M: the rings of K are
// those of M on subsets of K, and inverting d in K is inverting it in M, K holding
// its inverse.
var ModelsAgreeInSubfield = modelsAgreeInSubfieldThm{family.Add(registry.ProofEntry{
	Name: "ModelsAgreeInSubfield",
	Key:  "prop_a0f90b937f1816dd",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K S B C:set(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"subring(field_ring(M), S)",
			"subring(field_ring(M), B)",
			"subring(field_ring(M), C)",
			"S ⊆ B",
			"S ⊆ C",
			"B ⊆ K",
			"C ⊆ K",
			"fraction_field_carrier(restrict_ring(field_ring(M), K), B)",
			"fraction_field_carrier(restrict_ring(field_ring(M), K), C)",
			"module_finitely_generated(«scalarRing», «over»(B))",
			"module_finitely_generated(«scalarRing», «over»(C))",
		},
		Conclusion: "∃d:A. " +
			"    d ∈ S ∧ d ≠ M.zero ∧ ring_away(field_ring(M), B, d) = ring_away(field_ring(M), C, d)",
		Abbrev: Abbrev{
			{Name: "scalarRing", Text: "restrict_ring(field_ring(M), S)"},
			{Name: "over", Text: "λT:set(A). restrict_module(regular_module(field_ring(M)), T)"},
			{Name: "innerScalars", Text: "restrict_ring(field_ring(restrict_field(M, K)), S)"},
			{Name: "innerOver", Text: "λT:set(A). " +
				"    restrict_module(regular_module(field_ring(restrict_field(M, K))), T)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, S, B, C *Expr[Set[A]],
			subfieldK, subringS, subringB, subringC, sInB, sInC, bInK, cInK, fractionsB, fractionsC, finiteB, finiteC Fact,
		) {
			fieldM := a.TermAs[FieldOps[A]]("M")
			R := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			ring := field.RingOn.Read(M)
			inner := a.TermAs[FieldOps[A]]("restrict_field(M, K)")
			restricted := a.Have(
				"K is a field on its own carrier",
				"field_on(restrict_field(M, K))",
				By(subfieldK, field.SubfieldFieldOn.Read(M).At(K)))
			subrings := a.Have(
				"a subring of M inside K is a subring of K",
				"∀T:set(A). subring(field_ring(M), T) ∧ T ⊆ K ⇒ subring(field_ring(restrict_field(M, K)), T)",
				Derive(func(b *Argument) {
					T := b.FixAs[Set[A]]("T")
					given := b.Assume()
					b.Show(
						"restriction keeps the operations",
						Simp(Rev(field.RestrictFieldRing)),
						By(given, comm_ring.SubringRestrict.At(R, T, K)))
				}))
			fractions := a.Have(
				"fractions over a ring read the same in K",
				Statement{
					Binders:    "∀T:set(A).",
					Hypotheses: []string{"fraction_field_carrier(restrict_ring(field_ring(M), K), T)"},
					Conclusion: "fraction_field_carrier(field_ring(restrict_field(M, K)), T)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("T")
					given := b.Assume()
					b.Show(
						"restriction keeps the operations",
						Simp(Rev(field.RestrictFieldRing)),
						By(given))
				}))
			finite := a.Have(
				"a finite module reads the same in K",
				Statement{
					Binders:    "∀T:set(A).",
					Hypotheses: []string{"module_finitely_generated(«scalarRing», «over»(T))"},
					Conclusion: "module_finitely_generated(«innerScalars», «innerOver»(T))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("T")
					given := b.Assume()
					b.Show(
						"restriction keeps the operations",
						Simp(
							Rev(field.RestrictFieldRing),
							Fwd(module_record.RestrictRingTwice),
							Fwd(module_record.RegularModuleRestrict),
							Fwd(module_record.RestrictModuleTwice)),
						By(given))
				}))
			sInK := a.Have(
				"S lies in K",
				"S ⊆ K",
				BySets(sInB, bInK))
			d, found := a.ObtainAs[A](
				"inside K one nonzero scalar d makes the models agree",
				"∃d:A. "+
					"    d ∈ S ∧ "+
					"    d ≠ M.zero ∧ "+
					"    ring_away(field_ring(restrict_field(M, K)), B, d) = "+
					"    ring_away(field_ring(restrict_field(M, K)), C, d)",
				By(
					restricted,
					subrings.At(S),
					subringS,
					sInK,
					subrings.At(B),
					subringB,
					bInK,
					subrings.At(C),
					subringC,
					cInK,
					sInB,
					sInC,
					fractions.At(B),
					fractionsB,
					fractions.At(C),
					fractionsC,
					finite.At(B),
					finiteB,
					finite.At(C),
					finiteC,
					At(FiniteModelsAgreeAfterLocalization, inner, S, B, C)))
			parts := a.Conjuncts(
				found,
				"d lies in S",
				"d is not zero",
				"the models agree inverting d in K")
			inverse := a.TermAs[A]("M.inv(d)")
			dInK := a.Have(
				"d lies in K",
				"d ∈ K",
				BySets(parts[0], sInK))
			dInField := a.Have(
				"d lies in M",
				"d ∈ M.carrier",
				BySets(dInK, subfieldK, field.SubfieldSubset.At(fieldM, K)))
			inverted := a.Have(
				"K holds the inverse of d",
				"M.inv(d) ∈ K ∧ d * M.inv(d) = M.one",
				By(
					subfieldK,
					dInK,
					dInField,
					parts[1],
					field.SubfieldInv.At(fieldM, K, d),
					field.MulRightInverseOn.Read(M).AsFact().At(d)))
			subringK := a.Have(
				"K is a subring of M",
				"subring(field_ring(M), K)",
				By(subfieldK, field.SubfieldSubring.Read(M)))
			readB := a.Have(
				"inverting d in B reads the same in K and in M",
				"ring_away(restrict_ring(field_ring(M), K), B, d) = ring_away(field_ring(M), B, d)",
				By(ring, subringK, dInK, bInK, inverted, ring_away.RingAwayInSubring.At(R, K, B, d, inverse)))
			readC := a.Have(
				"as does inverting it in C",
				"ring_away(restrict_ring(field_ring(M), K), C, d) = ring_away(field_ring(M), C, d)",
				By(ring, subringK, dInK, cInK, inverted, ring_away.RingAwayInSubring.At(R, K, C, d, inverse)))
			same := a.Have(
				"so the models agree read in the ring of K",
				"ring_away(restrict_ring(field_ring(M), K), B, d) = "+
					"ring_away(restrict_ring(field_ring(M), K), C, d)",
				Simp(Fwd(field.RestrictFieldRing)),
				By(parts[2]))
			a.Take(d)
			a.Show(
				"and in M",
				By(Normalized, parts[0], parts[1], same, readB, readC))
		}),
})}
