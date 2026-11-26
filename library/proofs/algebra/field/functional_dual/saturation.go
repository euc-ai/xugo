package functional_dual

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// FunctionalDualSaturation — the functional dual commutes with saturation at
// s, which at a nonzero s is localization (ring_away.SpanOverAwayIsSaturation):
// exponents add across the pairing, so the saturated dual pairs the
// saturation of B into the saturation of N; and when B is finitely generated,
// one power of s clears the values of z on its generators, which brings z
// from the dual of the saturations into the saturated dual.
var FunctionalDualSaturation = functionalDualSaturationThm{family.Add(registry.ProofEntry{
	Name: "FunctionalDualSaturation",
	Key:  "prop_1ab7400e00708854",
	Reading: "Finite generation of B is load-bearing: one power of s must serve " +
		"every test. Over S = ℤ_(p) in K = L = ℚ, with l the identity, B = ℚ, N = S " +
		"and s = p, the dual of the saturations is ℚ and the saturated dual is {0}.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀l:(A → A). ∀S B N:set(A). ∀s:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"module_homomorphism(«ScalarK», «Regular», «VectorsK», l)",
			"S ⊆ K",
			"subring(field_ring(L), S)",
			"submodule(«ScalarS», «Regular», B)",
			"submodule(«ScalarS», «VectorsK», N)",
			"module_finitely_generated(«ScalarS», «VectorsB»)",
			"s ∈ S",
		},
		Conclusion: "«DualOfSat» = «SatOfDual»",
		Abbrev: Abbrev{
			{Name: "SatB", Text: "module_saturation(«ScalarS», «Regular», s, B)"},
			{Name: "SatN", Text: "module_saturation(«ScalarS», «VectorsK», s, N)"},
			{Name: "Dual", Text: "functional_dual(field_ring(L), l, B, N)"},
			{Name: "SatOfDual", Text: "module_saturation(«ScalarS», «Regular», s, «Dual»)"},
			{Name: "DualOfSat", Text: "functional_dual(field_ring(L), l, «SatB», «SatN»)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		exponentsAdd := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K:set(A). ∀l:(A → A). ∀S B N:set(A). ∀s z:A.",
			Hypotheses: []string{
				"module_homomorphism(«ScalarK», «Regular», «VectorsK», l)",
				"S ⊆ K",
				"subring(field_ring(L), S)",
				"s ∈ S",
				"z ∈ «SatOfDual»",
			},
			Conclusion: "z ∈ «DualOfSat»",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			K *Expr[Set[A]],
			l *Arrow[A, A],
			S, B, N *Expr[Set[A]],
			s, z *Expr[A],
			linear, sInK, subS, sInS, zIn Fact,
		) {
			ring := field.RingOn.Read(L)
			ringS := a.Have(
				"S is a ring under L's operations",
				"comm_ring_on(«ScalarS»)",
				By(subS, comm_ring.SubringRingOn.Read(ring).At(S)))
			powersL, powersS := comm_ring.MulMonoidOn.Read(ring), comm_ring.MulMonoidOn.Read(ringS)
			powerInL := comm_monoid.PowIn.Read(powersL)
			sL := a.MemberOf[on.L](s, a.Have(
				"s lies in L",
				"s ∈ L.carrier",
				BySets(sInS, comm_ring.SubringSubset.Read(subS))))
			saturated := a.Conjuncts(
				a.Simplified(zIn, Fwd(principal_ideal_domain.ModuleSaturationMember)),
				"z lies in L",
				"a power of s carries z into the dual")
			zL := a.MemberOf[on.L](z, saturated[0])
			n, inDual := a.UnpackAs[Nat](saturated[1], "n")
			tests := a.Conjuncts(
				a.Simplified(inDual, Fwd(FunctionalDualMember)),
				"s^n z lies in L",
				"s^n z tests into N on B")[1]
			pairing := a.Have(
				"z pairs the saturation of B into the saturation of N",
				"∀y:A. y ∈ «SatB» ⇒ l(z * y) ∈ «SatN»",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					vector := b.Conjuncts(
						b.Simplified(b.Assume(), Fwd(principal_ideal_domain.ModuleSaturationMember)),
						"y lies in L",
						"a power of s carries y into B")
					yL := b.MemberOf[on.L](y, vector[0])
					q, inB := b.UnpackAs[Nat](vector[1], "q")
					zy := comm_ring.MulIn.Read(ring).At(zL, yL)
					regroup := b.Have(
						"s^n z · s^q y = s^(n+q) (z y)",
						"monoid_pow(L.mul, L.one, s, n) * z * (monoid_pow(L.mul, L.one, s, q) * y) = "+
							"monoid_pow(L.mul, L.one, s, n + q) * (z * y)",
						ByArith(
							L,
							powerInL.At(sL, n),
							powerInL.At(sL, q),
							zL,
							yL,
							sL,
							Scaled(zy, comm_monoid.PowAddOn.Read(powersL).AsFact().At(s, n, q))))
					sum := b.TermAs[Nat]("n + q")
					carried := b.Have(
						"s^(n+q) carries the value l(z y) into N",
						"monoid_pow(L.mul, L.one, s, n + q) * l(z * y) ∈ N",
						BySets(
							tests.At(b.TermAs[A]("monoid_pow(L.mul, L.one, s, q) * y")),
							inB,
							regroup,
							comm_monoid.PowIn.Read(powersS).At(b.MemberOf[on.Any](s, sInS), sum),
							sInK,
							zy,
							module_homomorphism.HomSmul.Read(linear).AsFact().At(
								b.TermAs[A]("monoid_pow(L.mul, L.one, s, n + q)"), zy)))
					b.Show(
						"so the value lies in the saturation of N",
						Simp(Fwd(principal_ideal_domain.ModuleSaturationMember)),
						By(Normalized, carried, zy, module_homomorphism.HomIn.Read(linear).AsFact().At(zy)))
				}))
			a.Show(
				"so z lies in the dual of the saturations",
				Simp(Fwd(FunctionalDualMember)),
				By(pairing, zL))
		})
		generatorsClear := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K:set(A). ∀l:(A → A). ∀S B N:set(A). ∀s z:A.",
			Hypotheses: []string{
				"subfield(L, K)",
				"module_homomorphism(«ScalarK», «Regular», «VectorsK», l)",
				"S ⊆ K",
				"subring(field_ring(L), S)",
				"submodule(«ScalarS», «Regular», B)",
				"submodule(«ScalarS», «VectorsK», N)",
				"module_finitely_generated(«ScalarS», «VectorsB»)",
				"s ∈ S",
				"z ∈ «DualOfSat»",
			},
			Conclusion: "z ∈ «SatOfDual»",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			K *Expr[Set[A]],
			l *Arrow[A, A],
			S, B, N *Expr[Set[A]],
			s, z *Expr[A],
			subK, linear, sInK, subS, subB, subN, generated, sInS, zIn Fact,
		) {
			rL := a.TermAs[RingOps[A]]("field_ring(L)")
			rS := a.TermAs[RingOps[A]]("«ScalarS»")
			vK := a.TermAs[module_record.ModuleOps[A, A]]("«VectorsK»")
			ring := field.RingOn.Read(L)
			ringS := a.Have(
				"S is a ring under L's operations",
				"comm_ring_on(«ScalarS»)",
				By(subS, comm_ring.SubringRingOn.Read(ring).At(S)))
			powersL, powersS := comm_ring.MulMonoidOn.Read(ring), comm_ring.MulMonoidOn.Read(ringS)
			sL := a.MemberOf[on.L](s, a.Have(
				"s lies in L",
				"s ∈ L.carrier",
				BySets(sInS, comm_ring.SubringSubset.Read(subS))))
			linearS := a.Have(
				"restriction of scalars makes l S-linear, and L and K modules over S",
				"module_homomorphism(«ScalarS», «Regular», «VectorsK», l)",
				By(linear, subS, sInK, module_homomorphism.HomRestrictSubring))
			bInL := a.Have(
				"B lies in L",
				"B ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(subB)))
			E, generating := a.UnpackAs[Set[A]](
				a.Unfolded(generated, principal_ideal_domain.FinitelyGeneratedDef), "E")
			parts := a.Conjuncts(
				generating,
				"E is finite",
				"E lies in B",
				"E spans B")
			finiteE, eInB, spanB := parts[0], parts[1], parts[2]
			zParts := a.Conjuncts(
				a.Simplified(zIn, Fwd(FunctionalDualMember)),
				"z lies in L",
				"z pairs the saturation of B into the saturation of N")
			zL, pairs := a.MemberOf[on.L](z, zParts[0]), zParts[1]
			values := a.Have(
				"the value of z on each generator lies in the saturation of N",
				"∀e:A. e ∈ E ⇒ l(z * e) ∈ «SatN»",
				BySets(
					pairs,
					eInB,
					bInL,
					principal_ideal_domain.ModuleSaturationHolds.Read(module_homomorphism.HomSource.Read(linearS)).At(
						s, B)))
			n, common := a.ObtainAs[Nat](
				"from one exponent on, the powers of s bring those values into N",
				"∃n:num. ∀m:num. n ≤ m ⇒ ∀e:A. e ∈ E ⇒ monoid_pow(L.mul, L.one, s, m) * l(z * e) ∈ N",
				By(
					finiteE,
					values,
					subN,
					sInS,
					module_homomorphism.HomTarget.Read(linearS),
					principal_ideal_domain.SaturationCommonExponent.At(
						rS, vK, s, N, E, a.TermAs[Fun[A, A]]("λe:A. l(z * e)"))),
				Named("n"))
			sn := comm_monoid.PowIn.Read(powersL).At(sL, n)
			tests := a.Have(
				"s^n z tests into N on every generator",
				"∀e:A. e ∈ E ⇒ l(monoid_pow(L.mul, L.one, s, n) * z * e) ∈ N",
				Derive(func(b *Argument) {
					e := b.FixAs[A]("e")
					inE := b.Assume()
					eL := b.MemberOf[on.L](e, b.Have(
						"the generator lies in L",
						"e ∈ L.carrier",
						BySets(inE, eInB, bInL)))
					ze := comm_ring.MulIn.Read(ring).At(zL, eL)
					b.Show(
						"linearity identifies the test with the cleared value",
						BySets(
							common.At(n, e),
							nat_order.LessEqRefl.At(n),
							inE,
							comm_monoid.PowIn.Read(powersS).At(b.MemberOf[on.Any](s, sInS), n),
							sInK,
							ze,
							comm_monoid.AssocOn.Read(powersL).At(sn, zL, eL),
							module_homomorphism.HomSmul.Read(linear).AsFact().At(sn, ze)))
				}))
			inDual := a.Have(
				"testing on the generators suffices, so s^n z lies in the dual",
				"monoid_pow(L.mul, L.one, s, n) * z ∈ «Dual»",
				By(
					subK,
					linear,
					sInK,
					subS,
					subB,
					subN,
					eInB,
					spanB,
					tests,
					comm_ring.MulIn.Read(ring).At(sn, zL),
					FunctionalDualGenerators.Read(L).At(K, l, S, B, N, E),
					FunctionalDualMember.At(rL, l, E, N, a.TermAs[A]("monoid_pow(L.mul, L.one, s, n) * z"))))
			a.Show(
				"so z lies in the saturated dual",
				Simp(Fwd(principal_ideal_domain.ModuleSaturationMember)),
				By(Normalized, zL, inDual))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			L field.FieldFact[on.L],
			K *Expr[Set[A]],
			l *Arrow[A, A],
			S, B, N *Expr[Set[A]],
			s *Expr[A],
			h Fact,
		) {
			a.Show(
				"each side lies in the other",
				BySets(
					h,
					Read(exponentsAdd, L).At(K, l, S, B, N, s),
					Read(generatorsClear, L).At(K, l, S, B, N, s)))
		})
	}),
})}
