// riemann_roch.go — Riemann–Roch on the closed divisors of a smooth curve. The
// theorem for invertible pairs reads at the pair of a closed divisor D, and the
// canonical divisor W turns its dual term into ℓ(W − D). An invertible pair of
// negative degree has no sections, so ℓ(D) is known below degree 0 and above
// 2g − 2.

package smooth_curve_riemann_roch

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/scheme/closed_divisor"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	"github.com/euc-ai/xugo/library/proofs/scheme/divisor_lattice_correspondence"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/serre_duality"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/registry"
)

// RiemannRochClosedDivisors — Riemann–Roch on the closed divisors of a
// smooth curve: ℓ(D) − ℓ(W − D) = deg D + 1 − g, for W the canonical
// divisor. The theorem for invertible pairs applies to the pair of D, which
// is invertible of the degree of D, and the canonical model turns Hom into
// the dualizing pair into the sections of the pair of W − D.
var RiemannRochClosedDivisors = riemannRochClosedDivisorsThm{family.Add(registry.ProofEntry{
	Name: "RiemannRochClosedDivisors",
	Key:  "prop_6bacf70694343444",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(D)",
		},
		Conclusion: "«scSections»(«scPair»(D)) - " +
			"&«scSections»(«scPair»( " +
			"        λP:prod(set(A), set(A)). curve_canonical_divisor(L, k, t, A₀, A₁, A₀₁)(P) - D(P))) = " +
			"«scDegree»(D) + 1 - curve_genus(field_ring(L), k, A₀, A₁, A₀₁)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D *Arrow[_IdealPair, Int],
			curve, divisor Fact,
		) {
			X := a.TermAs[_IdealPair]("«scPair»(D)")
			overLine := a.Have(
				"the charts make a curve over the line of t",
				"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
				By(curve, smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t)))
			pair := a.Have(
				"the pair of D is invertible, and its degree is the degree of D",
				"«scInvertible»(«scPair»(D)) ∧ "+
					"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «scPair»(D)) = «scDegree»(D)",
				By(
					divisor_lattice_correspondence.WeightedDivisorLatticeCorrespondence.Read(L).At(k, A0, A1, A01, t),
					curve,
					divisor))
			duality := a.Have(
				"Hom from the pair of D into the dualizing pair has the dimension of the sections of W − D",
				"module_dim(restrict_ring(field_ring(L), k), "+
					"    curve_dualizing_maps(L, k, t, A₀, A₁, A₀₁, «scPair»(D))) = "+
					"«scSections»( "+
					"    «scPair»(λP:prod(set(A), set(A)). curve_canonical_divisor(L, k, t, A₀, A₁, A₀₁)(P) - D(P)))",
				By(CanonicalDivisorModel.Read(L).At(k, A0, A1, A01, t), curve, divisor))
			count := a.Simplified(
				GroupPremises(pair, overLine, serre_duality.RiemannRoch.Read(L).At(k, A0, A1, A01, t, X)),
				Fwd(lattice_pair.LatticePairH0DimDef),
				Fwd(module_record.RestrictRingTwice))
			a.Show(
				"ℓ(D) − ℓ(W − D) = deg D + 1 − g",
				ByArith(count, duality, pair))
		}),
})}

// SectionsByDivisorDegree — the two ranges where ℓ(D) is known: below degree
// 0 it vanishes, and above 2g − 2 it is deg D + 1 − g. A closed divisor of
// negative degree has no sections, and above 2g − 2 that vanishing reads at
// W − D, for W the canonical divisor, and takes the dual term out of
// Riemann–Roch.
var SectionsByDivisorDegree = sectionsByDivisorDegreeThm{family.Add(registry.ProofEntry{
	Name: "SectionsByDivisorDegree",
	Key:  "prop_2388ad8b575576ca",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(D)",
		},
		Conclusion: "(«scDegree»(D) < 0 ⇒ «scSections»(«scPair»(D)) = 0) ∧ " +
			"(int_of_num(2 * curve_genus(field_ring(L), k, A₀, A₁, A₀₁)) - 2 < «scDegree»(D) ⇒ " +
			"    int_of_num(«scSections»(«scPair»(D))) = " +
			"    «scDegree»(D) + 1 - int_of_num(curve_genus(field_ring(L), k, A₀, A₁, A₀₁)))",
		Abbrev: Abbrev{
			{Name: "scalars", Text: "restrict_ring(field_ring(L), k)"},
			{Name: "sections", Text: "lattice_pair_h0(regular_module(field_ring(L)))"},
			{Name: "canonical", Text: "curve_canonical_divisor(L, k, t, A₀, A₁, A₀₁)"},
			{Name: "complement", Text: "λP:prod(set(A), set(A)). «canonical»(P) - D(P)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D *Arrow[_IdealPair, Int],
			curve, divisor Fact,
		) {
			vanishing := a.Have(
				"a closed divisor of negative degree has no sections",
				Statement{
					Binders: "∀E:(prod(set(A), set(A)) → int).",
					Hypotheses: []string{
						"«scDivisor»(E)",
						"«scDegree»(E) < &0",
					},
					Conclusion: "module_dim(«scalars», «sections»(«scPair»(E))) = 0",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[_IdealPair, Int]]()
					given := b.Conjuncts(
						b.Assume(),
						"E is a closed divisor",
						"of negative degree")
					pair := b.Have(
						"the pair of E is invertible, of the degree of E",
						"«scInvertible»(«scPair»(E)) ∧ "+
							"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «scPair»(E)) = «scDegree»(E)",
						By(
							divisor_lattice_correspondence.WeightedDivisorLatticeCorrespondence.Read(L).At(k, A0, A1, A01, t),
							curve,
							given[0]))
					noSections := b.Have(
						"so it has no sections",
						"lattice_pair_h0_dim(restrict_ring(field_ring(L), A₀₁), "+
							"    k, "+
							"    regular_module(field_ring(L)), "+
							"    «scPair»(E)) = "+
							"0",
						By(
							curve,
							smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t),
							pair,
							given[1],
							curve_degree.NegativeDegreeNoSections.Read(L).At(
								k, A0, A1, A01, t, b.TermAs[_IdealPair]("«scPair»(E)"))))
					b.Show(
						"the dimension of its sections over k is that number",
						By(b.Simplified(
							noSections,
							Fwd(lattice_pair.LatticePairH0DimDef),
							Fwd(module_record.RestrictRingTwice))))
				}))
			a.Show(
				"ℓ(D) in each range",
				SplitConj(
					Case(
						"below degree 0, D has no sections",
						By(vanishing.At(D), divisor)),
					Case(
						"above 2g − 2, W − D has none, and Riemann–Roch gives ℓ(D)",
						Derive(func(b *Argument) {
							large := b.Assume()
							canonical := b.Have(
								"the canonical divisor is a closed divisor of degree 2g − 2",
								"«scDivisor»(«canonical») ∧ "+
									"«scDegree»(«canonical») = &(2 * curve_genus(field_ring(L), k, A₀, A₁, A₀₁)) - &2",
								By(CanonicalDivisorModel.Read(L).At(k, A0, A1, A01, t), curve))
							difference := b.Conjuncts(
								GroupPremises(
									curve,
									canonical,
									divisor,
									closed_divisor.ClosedDivisorSub.Read(L).At(
										k, A0, A1, A01, t, b.TermAs[Fun[_IdealPair, Int]]("«canonical»"), D)),
								"W − D is a closed divisor",
								"its pair is the pair of W times the inverse of the pair of D",
								"its degree is the difference of the degrees")
							negative := b.Have(
								"the degree of W − D is negative",
								"«scDegree»(«complement») < &0",
								ByArith(large, canonical, difference[2]))
							noDual := b.Have(
								"so W − D has no sections",
								"module_dim(«scalars», «sections»(«scPair»(«complement»))) = 0",
								By(vanishing.At(b.TermAs[Fun[_IdealPair, Int]]("«complement»")), difference[0], negative))
							b.Show(
								"Riemann–Roch loses its dual term",
								ByArith(RiemannRochClosedDivisors.Read(L).At(k, A0, A1, A01, t, D), curve, divisor, noDual))
						}))))
		}),
})}
