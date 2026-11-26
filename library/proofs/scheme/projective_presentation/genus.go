// genus.go — the genus of a smooth projective equation curve: the sections
// of the pair (A₀, tʲ·A₁) over the charts of F and G are, for large j, the
// forms of degree r·j over F(x)^j, so the Hilbert function is read off a
// Čech computation on those pairs and its constant term is the Čech genus.

package projective_presentation

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_form_chart"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_sections"
	"github.com/euc-ai/xugo/library/registry"
)

// ProjectiveGenusIsCurveGenus — the genus a smooth projective equation curve
// reads off its Hilbert polynomial is the Čech genus of the curve over the
// line its two form charts make: from some j on, ℓ(A₀, tʲ·A₁) + g = j·m + 1,
// m the degree of the zeros of t
// (algebraic_curve.PolePairSections), the sections of (A₀, tʲ·A₁) are the forms
// of degree r·j over F(x)ʲ (projective_sections.SectionsAreForms), a space of dimension h(r·j)
// (projective_form_chart.FormsOverSubspace), so h(r·j) + g = j·m + 1 along the multiples of r and the
// Hilbert genus is g (projective_curve.GenusAlongMultiples).
var ProjectiveGenusIsCurveGenus = projectiveGenusIsCurveGenusThm{family.Add(registry.ProofEntry{
	Name: "ProjectiveGenusIsCurveGenus",
	Key:  "prop_e13567d072ba007a",
	Reading: "No Serre duality, degree or dualizing pair enters. The Jacobian clause of smoothness " +
		"is not used — the charts are the curve's own, and the Čech genus of a singular equation curve " +
		"is still its Hilbert genus — only the hypotheses FormChartsAreCurve and SectionsAreForms read.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k K:set(A). " +
			"∀n r:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀F G:((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
			"subfield(M, K)",
			"«genericPoint»(x)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, G)",
			"0 < r",
			"«at»(F) ≠ M.zero",
			"«at»(G) ≠ M.zero",
			"«noCommonZero»",
		},
		Conclusion: "curve_genus(restrict_ring(field_ring(M), K), " +
			"    k, " +
			"    «chart»(F), " +
			"    «chart»(G), " +
			"    «overlap») = " +
			"projective_equation_genus(field_ring(M), k, n, E)",
		Abbrev: Abbrev{
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(M)))"},
			{Name: "dim", Text: "module_dim(«hilbertCoefficients»)"},
			// m, the dimension over k of the chart of F modulo t times it: the degree of the divisor of zeros of t.
			{Name: "zeroDegree", Text: "«dim»( " +
				"    quotient_module(«vectors»(«chart»(F)), image(M.mul(«parameter»), «chart»(F))))"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			F, G *Arrow[Fun[Nat, Nat], A],
			closed, curve, subfieldBig, generic, formF, formG, positive, fNonzero, gNonzero, noCommonZero Fact,
		) {
			chart0, chart1, overlap :=
				a.TermAs[Set[A]]("«chart»(F)"), a.TermAs[Set[A]]("«chart»(G)"), a.TermAs[Set[A]]("«overlap»")
			t := a.TermAs[A]("«parameter»")
			kSub := projective_curve.CurveConstantsSubfield.Read(curve)
			eventuallyLinear := projective_curve.CurveHilbertEventuallyLinear.Read(curve)
			charts := a.Have(
				"the charts of F and G, glued along t = G(x)/F(x), are a curve over the line",
				"curve_over_line(restrict_field(M, K), k, «parameter», «chart»(F), «chart»(G), «overlap»)",
				By(
					closed,
					curve,
					subfieldBig,
					generic,
					formF,
					formG,
					positive,
					fNonzero,
					gNonzero,
					noCommonZero,
					projective_form_chart.FormChartsAreCurve.Read(M).At(k, K, n, r, E, x, F, G)))
			functionField := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(subfieldBig, field.SubfieldFieldOn.Read(M).At(K)))
			_, sections := a.UnpackAs[Nat](
				GroupPremises(
					charts, algebraic_curve.PolePairSections.Read(functionField).At(k, chart0, chart1, overlap, t)),
				"N₁")
			_, meets := a.UnpackAs[Nat](a.Have(
				"from some j on the sections of (A₀, tʲ·A₁) are the forms of degree r·j over F(x)ʲ",
				"∃N:num. ∀j:num. N ≤ j ⇒ «chart»(F) ∩ «scaled»(j) = «formsOver»(j)",
				By(
					closed,
					curve,
					subfieldBig,
					generic,
					formF,
					formG,
					positive,
					fNonzero,
					gNonzero,
					noCommonZero,
					projective_sections.SectionsAreForms.Read(M).At(k, K, n, r, E, x, F, G))), "N₂")
			slope := a.TermAs[Nat]("«zeroDegree»")
			along := a.Have(
				"so along the multiples of r the Hilbert function is h(r·j) "+
					"= j·m + 1 − g from N₁ + N₂ on, m the degree of the zeros of t",
				"∃c N:num. ∀j:num. "+
					"    N ≤ j ⇒ "+
					"    projective_hilbert_function(field_ring(M), k, n, E, r * j) + "+
					"    curve_genus(restrict_ring(field_ring(M), K), k, «chart»(F), «chart»(G), «overlap») = "+
					"    c * j + 1",
				Derive(func(b *Argument) {
					b.Take(slope)
					b.Take(b.TermAs[Nat]("N₁ + N₂"))
					j := b.FixAs[Nat]("j")
					large := b.Assume()
					past := b.Have(
						"j is past N₁ and past N₂",
						"N₁ ≤ j ∧ N₂ ≤ j",
						ByArith(large))
					count := b.Simplified(
						GroupPremises(past, sections.At(j)),
						curve_point_count.InAmbient,
						Fwd(lattice_pair.LatticePairH0DimDef),
						Fwd(lattice_pair.LatticePairH0Def),
						Fwd(pairs.Fst),
						Fwd(pairs.Snd))
					meet := GroupPremises(past, meets.At(j))
					dimension := b.Conjuncts(
						GroupPremises(
							kSub,
							subfieldBig,
							generic,
							formF,
							fNonzero,
							projective_form_chart.FormsOverSubspace.Read(M).At(k, K, n, r, j, E, x, F)),
						"the forms of degree r·j over F(x)ʲ are the values of degree r·j over F(x)ʲ",
						"a k-subspace of M",
						"finite-dimensional",
						"of dimension h(r·j)")
					meetCount := b.Have(
						"read in M, ℓ(A₀, tʲ·A₁) is the dimension of the "+
							"meet of the chart of F with tʲ times the chart of G",
						"«dim»(«vectors»(«chart»(F) ∩ «scaled»(j))) + "+
							"curve_genus(restrict_ring(field_ring(M), K), k, «chart»(F), «chart»(G), «overlap») = "+
							"j * «zeroDegree» + 1",
						By(Normalized, count))
					formsCount := b.Have(
						"that meet is the space of the forms of degree r·j over F(x)ʲ",
						"«dim»(«vectors»(«formsOver»(j))) + "+
							"curve_genus(restrict_ring(field_ring(M), K), k, «chart»(F), «chart»(G), «overlap») = "+
							"j * «zeroDegree» + 1",
						meet.RwRev(),
						By(meetCount))
					b.Show(
						"whose dimension is h(r·j)",
						ByArith(formsCount, dimension[3]))
				}))
			a.Show(
				"so the Hilbert genus, read along the multiples of r, is the Čech genus",
				By(
					positive,
					eventuallyLinear,
					along,
					projective_curve.GenusAlongMultiples.At(
						a.TermAs[module_record.RingOps[A]]("field_ring(M)"),
						k,
						n,
						E,
						r,
						a.TermAs[Nat](
							"curve_genus(restrict_ring(field_ring(M), K), k, «chart»(F), «chart»(G), «overlap»)"))))
		}),
})}
