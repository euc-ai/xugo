// duality.go — the canonical divisor of a smooth curve. A finite extension
// carries a nonzero linear functional, whatever the parameter of the line, and
// its multiplication pairing is an invertible model N of the dualizing pair ω;
// a closed divisor represents N, so the canonical divisor W, a closed divisor
// whose pair is a model, exists. The maps of an invertible pair X into a
// lattice pair N are the multiplications by the sections of N · X⁻¹, so a model
// measures Hom(X, ω) by those sections, and Hom(D, ω) by the sections of W − D.

package smooth_curve_riemann_roch

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/functional_dual"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/scheme/closed_divisor"
	"github.com/euc-ai/xugo/library/proofs/scheme/divisor_lattice_correspondence"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/serre_duality"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/registry"
)

// SmoothCurveDualizingInvertible — the dualizing pair of a smooth curve has an
// invertible model, whatever the parameter t: L is finite over k(t)
// (FunctionFieldOverLine), so it carries a nonzero k(t)-linear functional
// (functional_dual.NonzeroLinearFunctional), and the multiplication pairing of that functional
// gives the model on the original charts (DualizingFromLinearFunctional).
var SmoothCurveDualizingInvertible = smoothCurveDualizingInvertibleThm{family.Add(registry.ProofEntry{
	Name: "SmoothCurveDualizingInvertible",
	Key:  "prop_dd97a952065082c5",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«scCurve»",
		},
		Conclusion: "dualizing_invertible(L, k, t, A₀, A₁, A₀₁)",
		Abbrev: Abbrev{
			{Name: "rational", Text: "field_adjoin(L, k, {t})"},
			{Name: "scalars", Text: "restrict_ring(field_ring(L), «rational»)"},
			{Name: "vectors", Text: "regular_module(field_ring(L))"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			rational := a.TermAs[Set[A]]("«rational»")
			l, functional := a.ObtainAs[Fun[A, A]](
				"L is finite over its subfield k(t), so it carries a nonzero linear functional",
				"∃l:(A → A). "+
					"    module_homomorphism(«scalars», «vectors», restrict_module(«vectors», «rational»), l) ∧ "+
					"    ∃x:A. x ∈ L.carrier ∧ l(x) ≠ L.zero",
				By(
					curve,
					FunctionFieldOverLine.Read(L).At(k, A0, A1, A01, t),
					functional_dual.NonzeroLinearFunctional.Read(L).At(rational)))
			parts := a.Conjuncts(
				functional,
				"l is k(t)-linear",
				"and not zero")
			a.Show(
				"and its multiplication pairing gives a dualizing model",
				By(
					Normalized,
					curve,
					parts[0],
					parts[1],
					DualizingFromLinearFunctional.Read(L).At(k, A0, A1, A01, t, l),
					serre_duality.DualizingInvertibleDef.At(a.TermAs[FieldOps[A]]("L"), k, t, A0, A1, A01)))
		}),
})}

// CanonicalDivisorModel — the canonical divisor W of a smooth curve: a closed
// divisor whose pair is a dualizing model, of degree 2g − 2, with dim Hom(D, ω)
// = ℓ(W − D) for every closed divisor D. A dualizing model exists
// (SmoothCurveDualizingInvertible) and is invertible, so a closed divisor
// represents it, and the choice defining W succeeds; the degree is
// DualizingDegree read through the correspondence of divisors with pairs; and
// Hom(D, ω) has the dimension of the sections of the pair of W times the
// inverse of the pair of D (serre_duality.DualizingMapsDimension), which is the
// pair of W + (−D).
var CanonicalDivisorModel = canonicalDivisorModelThm{family.Add(registry.ProofEntry{
	Name: "CanonicalDivisorModel",
	Key:  "prop_e196beefe51814ae",
	Reading: "The given parameter t may be inseparable, for example x^p. " +
		"Its field trace can vanish, so this construction uses a nonzero linear " +
		"functional rather than transporting a model from a separating parameter.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«scCurve»",
		},
		Conclusion: "«scDivisor»(curve_canonical_divisor(L, k, t, A₀, A₁, A₀₁)) ∧ " +
			"dualizing_model(L, " +
			"    k, " +
			"    t, " +
			"    A₀, " +
			"    A₁, " +
			"    A₀₁, " +
			"    «scPair»(curve_canonical_divisor(L, k, t, A₀, A₁, A₀₁))) ∧ " +
			"«scDegree»(curve_canonical_divisor(L, k, t, A₀, A₁, A₀₁)) = " +
			"2 * curve_genus(field_ring(L), k, A₀, A₁, A₀₁) - &2 ∧ " +
			"(∀D:(prod(set(A), set(A)) → int). " +
			"    «scDivisor»(D) ⇒ " +
			"    module_dim(restrict_ring(field_ring(L), k), " +
			"        curve_dualizing_maps(L, k, t, A₀, A₁, A₀₁, «scPair»(D))) = " +
			"    «scSections»(«scPair»( " +
			"            λP:prod(set(A), set(A)). curve_canonical_divisor(L, k, t, A₀, A₁, A₀₁)(P) - D(P))))",
		Abbrev: Abbrev{
			{Name: "isModel", Text: "dualizing_model(L, k, t, A₀, A₁, A₀₁)"},
			{Name: "dualMaps", Text: "curve_dualizing_maps(L, k, t, A₀, A₁, A₀₁)"},
			{Name: "canonical", Text: "curve_canonical_divisor(L, k, t, A₀, A₁, A₀₁)"},
			{Name: "canonicalPair", Text: "«scPair»(«canonical»)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			fieldL := a.TermAs[FieldOps[A]]("L")
			datum := a.Have(
				"the charts make a curve over the line of t",
				"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
				By(curve, smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t)))
			correspondence := divisor_lattice_correspondence.WeightedDivisorLatticeCorrespondence.Read(L).At(
				k, A0, A1, A01, t)

			// A dualizing model exists, and a closed divisor represents it.
			N, model := a.UnpackAs[_IdealPair](
				a.Unfolded(
					GroupPremises(L, curve, SmoothCurveDualizingInvertible.At(fieldL, k, A0, A1, A01, t)),
					serre_duality.DualizingInvertibleDef),
				"N")
			invertible := a.Have(
				"the model is invertible",
				"«scInvertible»(N)",
				By(model, serre_duality.DualizingModelDef.At(fieldL, k, t, A0, A1, A01, N)))
			E, represented := a.ObtainAs[Fun[_IdealPair, Int]](
				"so it is the pair of a closed divisor E",
				"∃E:(prod(set(A), set(A)) → int). «scDivisor»(E) ∧ «scPair»(E) = N",
				By(correspondence, curve, invertible))
			representative := a.Conjuncts(
				represented,
				"E is a closed divisor",
				"whose pair is the model")
			choosable := a.Have(
				"so some closed divisor has a dualizing model as its pair",
				"∃D:(prod(set(A), set(A)) → int). «scDivisor»(D) ∧ «isModel»(«scPair»(D))",
				Derive(func(b *Argument) {
					b.Take(E)
					b.Show(
						"E is one",
						By(Normalized, model, representative[0], representative[1]))
				}))
			chosen := a.Conjuncts(
				a.Have(
					"so the choice defining W succeeds",
					"«scDivisor»(«canonical») ∧ «isModel»(«canonicalPair»)",
					Simp(Fwd(CanonicalDivisorDef)),
					By(choosable)),
				"W is a closed divisor",
				"and its pair is a dualizing model")
			pair := a.Conjuncts(
				a.Have(
					"the pair of W is invertible, of the degree of W",
					"«scInvertible»(«canonicalPair») ∧ "+
						"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «canonicalPair») = «scDegree»(«canonical»)",
					By(correspondence, curve, chosen[0])),
				"the pair of W is invertible",
				"of the degree of W")
			canonicalPair := a.TermAs[_IdealPair]("«canonicalPair»")
			degree := a.Have(
				"so W has degree 2g − 2",
				"«scDegree»(«canonical») = &(2 * curve_genus(field_ring(L), k, A₀, A₁, A₀₁)) - &2",
				ByArith(
					pair[1],
					datum,
					chosen[1],
					serre_duality.DualizingDegree.Read(L).At(k, t, A0, A1, A01, canonicalPair)))

			// Hom(D, ω) has the dimension of the sections of W − D.
			canonical := a.TermAs[Fun[_IdealPair, Int]]("«canonical»")
			hom := a.Have(
				"Hom into the dualizing pair is measured by the sections of W − D",
				Statement{
					Binders:    "∀D:(prod(set(A), set(A)) → int).",
					Hypotheses: []string{"«scDivisor»(D)"},
					Conclusion: "module_dim(restrict_ring(field_ring(L), k), «dualMaps»(«scPair»(D))) = " +
						"«scSections»(«scPair»(λP:prod(set(A), set(A)). «canonical»(P) - D(P)))",
				},
				Derive(func(b *Argument) {
					D := b.FixAs[Fun[_IdealPair, Int]]("D")
					divisor := b.Assume()
					difference := b.Conjuncts(
						GroupPremises(
							curve,
							chosen[0],
							divisor,
							closed_divisor.ClosedDivisorSub.Read(L).At(k, A0, A1, A01, t, canonical, D)),
						"W − D is a closed divisor",
						"its pair is the pair of W times the inverse of the pair of D",
						"its degree is the difference of the degrees")
					invertibleD := b.Have(
						"the pair of D is invertible",
						"«scInvertible»(«scPair»(D))",
						By(correspondence, curve, divisor))
					pairD := b.TermAs[_IdealPair]("«scPair»(D)")
					dimension := b.Have(
						"over the function field, Hom(D, ω) has the dimension of those sections",
						"module_dim(restrict_ring(restrict_ring(field_ring(L), A₀₁), k), «dualMaps»(«scPair»(D))) = "+
							"lattice_pair_h0_dim(restrict_ring(field_ring(L), A₀₁), "+
							"    k, "+
							"    regular_module(field_ring(L)), "+
							"    «scMul»(«canonicalPair», «scInverse»(«scPair»(D))))",
						By(
							datum,
							chosen[1],
							invertibleD,
							serre_duality.DualizingMapsDimension.Read(L).At(k, A0, A1, A01, t, canonicalPair, pairD)))
					b.Show(
						"which reads the same over L",
						difference[1].Rw(),
						By(b.Simplified(
							dimension,
							Fwd(lattice_pair.LatticePairH0DimDef),
							Fwd(module_record.RestrictRingTwice))))
				}))
			a.Show(
				"W is a closed divisor, its pair a dualizing model, of degree 2g − 2, and it measures Hom",
				By(chosen[0], chosen[1], degree, hom))
		}),
})}
