// biaffine_curve.go — an integral plane model read in the ambient field M, and
// its two charts A₀ = k[t][z] and A₁ = k[1/t][w], w = t^(−b)·z. Read in M, k(t),
// k[t] and k[1/t] are the ambient field's, and the chart members argue there.
// The scaled equation is the minimal polynomial of w, so each chart is free over
// its line on the powers of its generator below deg F; the charts glue along
// A₀[1/t] and meet in k, and the model is a curve over the projective line.

package plane_model

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/rational_function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PlaneModelInAmbient — an integral plane model read in the ambient field M:
// K is regular over k read in M, k lies in K and K in M, t is transcendental
// over k, z is algebraic over k(t), and F is its minimal polynomial over k(t)
// in M; and the second chart's data: t is not zero, w = t^(-b) z lies in M,
// k[1/t] is a subring of M inside k(t), and z = t^b w. The restriction keeps
// the operations, so k(t) and the minimal polynomial are those of M, and K is
// algebraic over the rational functions of any transcendental element; t,
// transcendental, is not zero, and k(1/t) = k(t).
var PlaneModelInAmbient = planeModelInAmbientThm{family.Add(registry.ProofEntry{
	Name: "PlaneModelInAmbient",
	Key:  "prop_e40d156043b596bd",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀t z:A. ∀F:(num → A). ∀b:num.",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
		},
		Conclusion: "regular_function_field(M, k, K) ∧ " +
			"subfield(M, k) ∧ " +
			"k ⊆ K ∧ " +
			"K ⊆ M.carrier ∧ " +
			"t ∈ K ∧ " +
			"z ∈ K ∧ " +
			"t ∈ M.carrier ∧ " +
			"z ∈ M.carrier ∧ " +
			"¬algebraic_over(M, k, t) ∧ " +
			"algebraic_over(M, «pmRational», z) ∧ " +
			"F = minimal_polynomial(M, «pmRational», z) ∧ " +
			"t ≠ M.zero ∧ " +
			"«pmGenerator» ∈ M.carrier ∧ " +
			"subring(field_ring(M), «pmInversePolynomials») ∧ " +
			"«pmInversePolynomials» ⊆ «pmRational» ∧ " +
			"z = monoid_pow(M.mul, M.one, t, b) * «pmGenerator»",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k *Expr[Set[A]],
		t, z *Expr[A],
		F *Arrow[Nat, A],
		b *Expr[Nat],
		subfieldK, model Fact,
	) {
		ring := field.RingOn.Read(M)
		multiplicative := comm_ring.MulMonoidOn.Read(ring)
		clauses := a.Conjuncts(
			a.Unfolded(model, IntegralPlaneModelDef),
			"K is regular over k read in K",
			"t lies in K",
			"t is transcendental over k",
			"z lies in K",
			"z generates K over k(t)",
			"F is the minimal polynomial of z",
			"F is separable",
			"F has positive degree",
			"the weight is positive",
			"below the degree d, F(i) is a polynomial in t over k of degree at most b(d − i)")
		regular := a.Have(
			"K is regular over k read in M",
			"regular_function_field(M, k, K)",
			By(subfieldK, clauses[0], function_field.RegularFunctionFieldInAmbient.Read(M).At(k, K)))
		transcendental := a.Have(
			"t stays transcendental over k read in M",
			"¬algebraic_over(M, k, t)",
			By(clauses[2], algebraic_element.AlgebraicOverDef))
		constants := a.Have(
			"k is a subfield of M inside K, and K lies in M",
			"subfield(M, k) ∧ k ⊆ K ∧ K ⊆ M.carrier",
			By(regular, subfieldK, function_field.RegularFunctionFieldDef, field.SubfieldSubset))
		sameBase := a.Have(
			"k(t) is one field read in K and in M",
			"«pmRationalInK» = «pmRational»",
			By(
				subfieldK,
				constants,
				clauses[1],
				algebraic_element.AdjoinInSubfield.Read(M).At(K, k, a.TermAs[Set[A]]("{t}")),
				set_order.SingSubset))
		isMinimal := a.Have(
			"F is the minimal polynomial of z over k(t) in M",
			"F = minimal_polynomial(M, «pmRational», z)",
			clauses[5].Rw(),
			sameBase.Rw(),
			Unfold(algebraic_element.MinimalPolynomialDef))
		algebraic := a.Have(
			"z is algebraic over k(t), K being algebraic over "+
				"the rational functions of any transcendental element",
			"algebraic_over(M, «pmRational», z)",
			By(
				regular,
				clauses[1],
				transcendental,
				clauses[3],
				rational_function_field.AlgebraicOverAnyTranscendental.Read(M).At(k, K, t, z)))
		points := a.Conjuncts(
			a.Have(
				"t and z lie in M",
				"t ∈ M.carrier ∧ z ∈ M.carrier",
				BySets(constants, clauses[1], clauses[3])),
			"t lies in M",
			"z lies in M")
		tIn, zIn := points[0], points[1]
		tm := a.MemberOf[on.M](t, tIn)
		um := field.InvIn.Read(M).At(tm)
		nonzero := a.Have(
			"t is not zero, being transcendental",
			"t ≠ M.zero",
			By(constants, transcendental, algebraic_element.TranscendentalInverse.Read(M).At(k, tm)))
		line := a.Have(
			"k[1/t] is a subring of M inside k(1/t) = k(t)",
			"subring(field_ring(M), «pmInversePolynomials») ∧ «pmInversePolynomials» ⊆ «pmRational»",
			By(
				constants,
				algebraic_element.PolynomialImageRing.Read(M).At(k, um),
				algebraic_element.AdjoinInverse.Read(M).At(k, tm)))
		wIn := a.Have(
			"w = t^(-b) z lies in M",
			"«pmGenerator» ∈ M.carrier",
			By(zIn, um, comm_monoid.PowIn.Read(multiplicative), comm_ring.MulIn.Read(ring)))
		inverse := a.Have(
			"t^b and t^(-b) are inverse",
			"monoid_pow(M.mul, M.one, t, b) * monoid_pow(M.mul, M.one, M.inv(t), b) = M.one",
			By(tm, um, nonzero, comm_monoid.PowInverseOn.Read(multiplicative), field.MulRightInverseOn.Read(M)))
		zFromW := a.Have(
			"z = t^b w",
			"z = monoid_pow(M.mul, M.one, t, b) * «pmGenerator»",
			ByArith(M, Scaled(z, inverse), tIn, zIn, um))
		a.Show(
			"each clause is in hand",
			BySets(
				regular,
				constants,
				clauses[1],
				clauses[3],
				transcendental,
				algebraic,
				isMinimal,
				nonzero,
				wIn,
				line,
				zFromW))
	}),
})}

// PlaneChartsInAmbient — the charts of a plane model are read off the ambient
// operations: the restriction keeps them, so k[t][z] and k[1/t][t^(-b) z] are the
// same sets in the restricted field and in M.
var PlaneChartsInAmbient = planeChartsInAmbientThm{family.Add(registry.ProofEntry{
	Name: "PlaneChartsInAmbient",
	Key:  "prop_6dc4841ed05c9037",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_ops(A). ∀K k:set(A). ∀t z:A. ∀b:num.",
		Conclusion: "«pmChart0» = «pmImage0» ∧ «pmChart1» = «pmImage1»",
	},
		func(a *Argument, M *Expr[FieldOps[A]], K, k *Expr[Set[A]], t, z *Expr[A], b *Expr[Nat]) {
			a.Do(SplitConj(
				Case(
					"the first chart",
					Simp(
						Fwd(PlaneChartZeroDef),
						Fwd(field.RestrictFieldRing),
						Fwd(algebraic_element.PolynomialsOverRestriction)),
					Refl()),
				Case(
					"the second chart",
					Simp(
						Fwd(PlaneChartOneDef),
						Fwd(PlaneChartZeroDef),
						Fwd(algebraic_element.PolynomialsOverRestriction)),
					Refl())))
		}),
})}

// PlaneModelRelation — the equation F of a plane model is a monic polynomial over
// k[t] vanishing at z: F lies over k[t] (PlaneModelOverPolynomials, k[t] being one
// ring read in K and in M), and it is the minimal polynomial of z, algebraic over
// k(t) (PlaneModelInAmbient), so it is monic with z a root.
var PlaneModelRelation = planeModelRelationThm{family.Add(registry.ProofEntry{
	Name: "PlaneModelRelation",
	Key:  "prop_11fa17393ecd8411",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀t z:A. ∀F:(num → A). ∀b:num.",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
		},
		Conclusion: "polynomial_over(«pmPolynomials», F) ∧ " +
			"polynomial_monic(F) ∧ " +
			"polynomial_eval(F, z) = M.zero",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k *Expr[Set[A]],
			t, z *Expr[A],
			F *Arrow[Nat, A],
			b *Expr[Nat],
			subfieldK, model Fact,
		) {
			fieldM := a.TermAs[FieldOps[A]]("M")
			base := a.TermAs[Set[A]]("«pmRational»")
			ambient := a.Conjuncts(
				a.Have(
					"read in M, k is a subfield, t and z lie in M, and F "+
						"is the minimal polynomial of z, algebraic over k(t)",
					"subfield(M, k) ∧ "+
						"t ∈ M.carrier ∧ "+
						"z ∈ M.carrier ∧ "+
						"algebraic_over(M, «pmRational», z) ∧ "+
						"F = minimal_polynomial(M, «pmRational», z)",
					By(subfieldK, model, PlaneModelInAmbient.Read(M).At(K, k, t, z, F, b))),
				"k is a subfield of M",
				"t lies in M",
				"z lies in M",
				"z is algebraic over k(t)",
				"F is its minimal polynomial")
			subK, tIn, zIn, algebraic, isMinimal := ambient[0], ambient[1], ambient[2], ambient[3], ambient[4]
			tm, zm := a.MemberOf[on.M](t, tIn), a.MemberOf[on.M](z, zIn)
			spec := a.Have(
				"so F is monic and vanishes at z",
				"polynomial_monic(F) ∧ polynomial_eval(F, z) = M.zero",
				isMinimal.Rw(),
				By(
					subK,
					algebraic,
					algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm),
					algebraic_element.MinimalPolynomialSpec.Read(M).At(base, zm)))
			over := a.Have(
				"F lies over k[t], one ring read in K and in M",
				"polynomial_over(«pmPolynomials», F)",
				By(
					Normalized,
					subfieldK,
					model,
					PlaneModelOverPolynomials.Read(M).At(K, k, t, z, F, b),
					algebraic_element.PolynomialsOverRestriction.At(fieldM, K, k, t)))
			a.Show(
				"monic over k[t] and vanishing at z",
				By(over, spec))
		}),
})}

// PlaneChartsBiaffine — the two charts of a plane model glue along their
// overlap: A₀ = k[t][z] and A₁ = k[1/t][w], w = t^(-b) z, are subrings of M
// holding t and 1/t, and A₀ with t inverted is A₁ with 1/t inverted, the ring
// A₀₁. Each overlap is the least ring holding its chart and the inverse of the
// element it inverts, and each holds the other chart, since z = t^b w and
// w = t^(-b) z.
var PlaneChartsBiaffine = planeChartsBiaffineThm{family.Add(registry.ProofEntry{
	Name: "PlaneChartsBiaffine",
	Key:  "prop_7925127b4508bc6e",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀t z:A. ∀b:num.",
		Hypotheses: []string{
			"subfield(M, k)",
			"t ∈ M.carrier",
			"t ≠ M.zero",
			"z ∈ M.carrier",
		},
		Conclusion: "biaffine(restrict_ring(field_ring(M), ring_away(field_ring(M), «chart0», t)), " +
			"    «chart0», " +
			"    «chart1», " +
			"    t, " +
			"    M.inv(t))",
		Abbrev: Abbrev{
			{Name: "chart0", Text: "plane_chart_zero(field_ring(M), k, t, z)"},
			{Name: "chart1", Text: "plane_chart_one(M, k, t, z, b)"},
			{Name: "away0", Text: "ring_away(field_ring(M), «pmImage0», t)"},
			{Name: "away1", Text: "ring_away(field_ring(M), «pmImage1», M.inv(t))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		t, z *Expr[A],
		b *Expr[Nat],
		subK, tIn, nonzero, zIn Fact,
	) {
		ring := field.RingOn.Read(M)
		fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
		tm := a.MemberOf[on.M](t, tIn)
		um := field.InvIn.Read(M).At(tm)
		u, w := a.TermAs[A]("M.inv(t)"), a.TermAs[A]("«pmGenerator»")
		line0, line1 := a.TermAs[Set[A]]("«pmPolynomials»"), a.TermAs[Set[A]]("«pmInversePolynomials»")
		ring0, ring1 := a.TermAs[Set[A]]("«pmImage0»"), a.TermAs[Set[A]]("«pmImage1»")
		away0, away1 := a.TermAs[Set[A]]("«away0»"), a.TermAs[Set[A]]("«away1»")
		inverse := a.Have(
			"1/t lies in M, is not zero, and is inverse to t",
			"M.inv(t) ∈ M.carrier ∧ "+
				"t * M.inv(t) = M.one ∧ "+
				"M.inv(t) * t = M.one ∧ "+
				"M.inv(t) ≠ M.zero ∧ "+
				"M.inv(M.inv(t)) = t",
			By(
				field.InvIn.Read(M),
				field.MulRightInverseOn.Read(M),
				field.MulLeftInverseOn.Read(M),
				field.InvEqZeroOn.Read(M),
				field.InvInvOn.Read(M),
				tIn,
				nonzero))
		lines := a.Have(
			"k[t] and k[1/t] are subrings of M holding k, and t and 1/t",
			"subring(field_ring(M), «pmPolynomials») ∧ "+
				"k ⊆ «pmPolynomials» ∧ "+
				"t ∈ «pmPolynomials» ∧ "+
				"subring(field_ring(M), «pmInversePolynomials») ∧ "+
				"k ⊆ «pmInversePolynomials» ∧ "+
				"M.inv(t) ∈ «pmInversePolynomials»",
			By(algebraic_element.PolynomialImageRing.Read(M), subK, tIn, inverse))
		wIn := a.Have(
			"w = t^(-b) z lies in M",
			"«pmGenerator» ∈ M.carrier",
			By(
				comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)),
				comm_ring.MulIn.Read(ring),
				zIn,
				inverse))
		charts := a.Have(
			"the charts A₀ = k[t][z] and A₁ = k[1/t][w] are "+
				"subrings of M holding their lines and their generators",
			"subring(field_ring(M), «pmImage0») ∧ "+
				"«pmPolynomials» ⊆ «pmImage0» ∧ "+
				"z ∈ «pmImage0» ∧ "+
				"subring(field_ring(M), «pmImage1») ∧ "+
				"«pmInversePolynomials» ⊆ «pmImage1» ∧ "+
				"«pmGenerator» ∈ «pmImage1»",
			By(algebraic_element.PolynomialImageSubring.Read(M), zIn, wIn, lines))
		units := a.Have(
			"t lies in A₀ and 1/t in A₁",
			"t ∈ «pmImage0» ∧ M.inv(t) ∈ «pmImage1»",
			BySets(lines, charts))

		// The two overlaps, A₀ with t inverted and A₁ with 1/t inverted.
		inverted0 := a.Have(
			"A₀[1/t] is a subring of M holding A₀ and 1/t",
			"«pmImage0» ⊆ «away0» ∧ subring(field_ring(M), «away0») ∧ M.inv(t) ∈ «away0»",
			By(ring, units, inverse, charts, ring_away.RingAwaySubring.At(fieldRing, ring0, t)))
		inverted1 := a.Have(
			"A₁[t] is a subring of M holding A₁ and t",
			"«pmImage1» ⊆ «away1» ∧ subring(field_ring(M), «away1») ∧ t ∈ «away1»",
			By(ring, tIn, units, inverse, charts, ring_away.RingAwaySubring.At(fieldRing, ring1, u)))
		awayRing0 := a.Have(
			"A₀[1/t] is a ring under M's operations",
			"comm_ring_on(restrict_ring(field_ring(M), «away0»))",
			By(inverted0, comm_ring.SubringRingOn.Read(ring).At(away0)))
		awayRing1 := a.Have(
			"and so is A₁[t]",
			"comm_ring_on(restrict_ring(field_ring(M), «away1»))",
			By(inverted1, comm_ring.SubringRingOn.Read(ring).At(away1)))
		members := a.Have(
			"each overlap holds k, and the generators of the other chart's line",
			"k ⊆ «away1» ∧ "+
				"«pmGenerator» ∈ «away1» ∧ "+
				"M.inv(t) ∈ «away1» ∧ "+
				"k ⊆ «away0» ∧ "+
				"z ∈ «away0» ∧ "+
				"t ∈ «away0»",
			BySets(inverted0, inverted1, lines, charts))

		// A₀[1/t] ⊆ A₁[t]: z = t^b w lies in A₁[t], so A₀ = k[t][z] does.
		powers := a.Have(
			"t^b and t^(-b) are inverse",
			"monoid_pow(M.mul, M.one, t, b) * monoid_pow(M.mul, M.one, M.inv(t), b) = M.one",
			By(comm_monoid.PowInverseOn.Read(comm_ring.MulMonoidOn.Read(ring)), tIn, inverse))
		zFromW := a.Have(
			"z = t^b w",
			"z = monoid_pow(M.mul, M.one, t, b) * «pmGenerator»",
			ByArith(M, Scaled(z, powers), tIn, zIn, inverse))
		zIn1 := a.Have(
			"so z lies in A₁[t]",
			"z ∈ «away1»",
			By(
				comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(awayRing1)),
				comm_ring.MulIn.Read(awayRing1),
				zFromW,
				inverted1,
				members))
		ring0In1 := a.Have(
			"A₀ lies in A₁[t], a ring holding k, t and z",
			"«pmImage0» ⊆ «away1»",
			By(
				awayRing1,
				zIn1,
				inverted1,
				members,
				algebraic_element.PolynomialImageLeast.Read(M).At(k, away1, t),
				algebraic_element.PolynomialImageLeast.Read(M).At(line0, away1, z)))
		forward := a.Have(
			"so A₀[1/t] ⊆ A₁[t], A₀[1/t] being the least ring holding A₀ and 1/t",
			"«away0» ⊆ «away1»",
			By(ring0In1, inverted1, members, nonzero, ring_away.RingAwayLeast.Read(M).At(ring0, away1, tm)))

		// A₁[t] ⊆ A₀[1/t]: w = t^(-b) z lies in A₀[1/t], so A₁ = k[1/t][w] does.
		ring1In0 := a.Have(
			"A₁ lies in A₀[1/t], a ring holding k, 1/t and w",
			"«pmImage1» ⊆ «away0»",
			By(
				comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(awayRing0)),
				comm_ring.MulIn.Read(awayRing0),
				inverted0,
				members,
				algebraic_element.PolynomialImageLeast.Read(M).At(k, away0, u),
				algebraic_element.PolynomialImageLeast.Read(M).At(line1, away0, w)))
		backward := a.Have(
			"so A₁[t] ⊆ A₀[1/t], A₁[t] being the least ring holding A₁ and t",
			"«away1» ⊆ «away0»",
			By(inverted0, ring1In0, members, inverse, ring_away.RingAwayLeast.Read(M).At(ring1, away0, um)))
		glued := a.Have(
			"the overlaps agree: A₀[1/t] = A₁[t]",
			"«away0» = «away1»",
			By(forward, backward, set_order.SubsetAntisym))

		// Inside the ring of A₀₁: each chart a subring, and each chart with its element inverted.
		subrings := a.Have(
			"each chart, a subring of M inside A₀₁, is a subring of the ring of A₀₁",
			"subring(restrict_ring(field_ring(M), «away0»), «pmImage0») ∧ "+
				"subring(restrict_ring(field_ring(M), «away0»), «pmImage1»)",
			By(inverted0, ring1In0, charts, comm_ring.SubringRestrict))
		awayFromT := a.Have(
			"computed in the ring of A₀₁, A₀ with t inverted is A₀₁",
			"ring_away(restrict_ring(field_ring(M), «away0»), «pmImage0», t) = «away0»",
			By(
				ring,
				inverted0,
				members,
				inverse,
				ring_away.RingAwayInSubring.At(fieldRing, away0, ring0, t, u)))
		awayFromU := a.Have(
			"and A₁ with 1/t inverted is A₁[t], which is A₀₁",
			"ring_away(restrict_ring(field_ring(M), «away0»), «pmImage1», M.inv(t)) = «away0»",
			By(
				ring,
				inverted0,
				members,
				inverse,
				ring1In0,
				glued,
				ring_away.RingAwayInSubring.At(fieldRing, away0, ring1, u, t)))
		a.Show(
			"so the ring of A₀₁, the two charts, t and 1/t form a biaffine datum",
			Simp(Fwd(PlaneChartOneDef), Fwd(PlaneChartZeroDef)),
			By(
				awayRing0,
				subrings,
				units,
				inverse,
				awayFromT,
				awayFromU,
				lattice_pair.BiaffineDef.At(
					a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), «away0»)"), ring0, ring1, t, u)))
	}),
})}

// ScaledMonicEquation — for an integral plane model of degree d = deg F and
// weight b, the polynomial whose i-th coefficient is t^(−b(d−i))·F(i) up to d is
// a monic polynomial over k[t⁻¹] of degree d vanishing at t^(−b)·z. Read in M,
// F is the monic minimal polynomial of z over k(t) and t is not zero
// (PlaneModelInAmbient). Below d the weight clause writes F(i) as a(t) with
// deg a ≤ b(d−i), and t^(−b(d−i))·a(t) lies in k[t⁻¹]
// (algebraic_element.ScaledValueInInverseImage); at d the coefficient is
// F(d) = 1, and past d it is zero; and the value at t^(−b)·z is t^(−bd)·F(z) = 0
// (polynomial_evaluation.EvalRescaled).
var ScaledMonicEquation = scaledMonicEquationThm{family.Add(registry.ProofEntry{
	Name: "ScaledMonicEquation",
	Key:  "prop_aa92c69e28d5281f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀t z:A. ∀F:(num → A). ∀b:num.",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
		},
		Conclusion: "polynomial_over(«pmInversePolynomials», «pmScaled») ∧ " +
			"polynomial_monic(«pmScaled») ∧ " +
			"polynomial_eval(«pmScaled», «pmGenerator») = M.zero ∧ " +
			"polynomial_degree(«pmScaled») = polynomial_degree(F)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k *Expr[Set[A]],
		t, z *Expr[A],
		F *Arrow[Nat, A],
		b *Expr[Nat],
		subfieldK, model Fact,
	) {
		ring := field.RingOn.Read(M)
		zero := a.TermAs[A]("M.zero")
		degree := a.TermAs[Nat]("polynomial_degree(F)")
		rational := a.TermAs[Set[A]]("«pmRational»")
		inversePolynomials := a.TermAs[Set[A]]("«pmInversePolynomials»")
		scaled := a.TermAs[Fun[Nat, A]]("«pmScaled»")
		ambient := a.Conjuncts(
			a.Have(
				"read in M: k is a subfield, t and z lie in M, z is algebraic over "+
					"k(t) with minimal polynomial F, t ≠ 0, and k[t⁻¹] is a subring",
				"subfield(M, k) ∧ "+
					"t ∈ M.carrier ∧ "+
					"z ∈ M.carrier ∧ "+
					"algebraic_over(M, «pmRational», z) ∧ "+
					"F = minimal_polynomial(M, «pmRational», z) ∧ "+
					"t ≠ M.zero ∧ "+
					"subring(field_ring(M), «pmInversePolynomials»)",
				By(subfieldK, model, PlaneModelInAmbient.Read(M).At(K, k, t, z, F, b))),
			"k is a subfield of M",
			"t lies in M",
			"z lies in M",
			"z is algebraic over k(t)",
			"F is its minimal polynomial",
			"t is not zero",
			"k[t⁻¹] is a subring of M")
		subK, tIn, zIn, algebraic, minimal, nonzero, inverseLine :=
			ambient[0], ambient[1], ambient[2], ambient[3], ambient[4], ambient[5], ambient[6]
		tm, zm := a.MemberOf[on.M](t, tIn), a.MemberOf[on.M](z, zIn)
		um := field.InvIn.Read(M).At(tm)
		lower := a.Have(
			"the weight clause: below the degree, F(i) is a(t) "+
				"for a polynomial a over k of degree at most b(d − i)",
			Statement{
				Binders:    "∀i:num.",
				Hypotheses: []string{"i < polynomial_degree(F)"},
				Conclusion: "∃a:(num → A). " +
					"    polynomial_over(k, a) ∧ " +
					"    polynomial_degree(a) ≤ b * (polynomial_degree(F) - i) ∧ " +
					"    polynomial_eval(a, t) = F(i)",
			},
			By(a.Unfolded(model, IntegralPlaneModelDef)))

		// F is the monic minimal polynomial of z over k(t), which z is algebraic over.
		rationalField := a.Have(
			"k(t) is a subfield of M",
			"subfield(M, «pmRational»)",
			By(subK, algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm)))
		spec := a.Conjuncts(
			a.Have(
				"so F is a monic polynomial over k(t) vanishing at z",
				"polynomial_over(«pmRational», F) ∧ polynomial_monic(F) ∧ polynomial_eval(F, z) = M.zero",
				minimal.Rw(),
				By(rationalField, algebraic, algebraic_element.MinimalPolynomialSpec.Read(M).At(rational, zm))),
			"F is a polynomial over k(t)",
			"it is monic",
			"it vanishes at z")
		overRational, monic, root := spec[0], spec[1], spec[2]
		overM := a.Have(
			"F is a polynomial over M, k(t) lying in M",
			"polynomial_over(M.carrier, F)",
			By(
				overRational,
				rationalField,
				field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("M"), rational),
				polynomial.PolynomialOverMono))

		vanishes := a.Have(
			"t^(−b)·z is a root: rescaling by t⁻¹ multiplies the value of F at z by t^(−bd)",
			"polynomial_eval(«pmScaled», «pmGenerator») = M.zero",
			ByArith(ring, overM, root, polynomial_evaluation.EvalRescaled.Read(ring).At(F, degree, b, um, zm)))

		// The coefficients lie in k[t⁻¹].
		kSubring := a.Have(
			"k is a subring of M",
			"subring(field_ring(M), k)",
			By(subK, field.SubfieldSubring.Read(M)))
		monicTop := a.Have(
			"F is monic: its coefficient at its degree is one",
			"F(polynomial_degree(F)) = M.one",
			By(monic, polynomial.PolynomialMonicDef))
		top := a.Have(
			"the top coefficient is t⁰·F(d) = 1",
			"«pmScaled»(polynomial_degree(F)) = M.one",
			ByArith(ring, monicTop, um, comm_ring.OneIn.Read(ring)))
		coefficients := a.Have(
			"every coefficient lies in k[t⁻¹]",
			"∀i:num. «pmScaled»(i) ∈ «pmInversePolynomials»",
			Derive(func(c *Argument) {
				i := c.FixAs[Nat]("i")
				c.Cases(c.TermAs[Bool]("i < polynomial_degree(F)"))
				c.When(
					"below the degree the weight clause writes F(i) as a(t) with deg a ≤ b(d − i)",
					func(d *Argument, below Fact) {
						weightPolynomial, weightData := d.UnpackAs[Fun[Nat, A]](GroupPremises(below, lower.At(i)), "a")
						cleared := d.Have(
							"t^(−b(d−i))·a(t) lies in k[t⁻¹], the degree of a being at most b(d − i)",
							"monoid_pow(M.mul, M.one, M.inv(t), b * (polynomial_degree(F) - i)) * polynomial_eval(a, t) ∈ "+
								"«pmInversePolynomials»",
							By(
								weightData,
								nonzero,
								kSubring,
								algebraic_element.ScaledValueInInverseImage.Read(M).At(
									k, tm, d.TermAs[Nat]("b * (polynomial_degree(F) - i)"), weightPolynomial)))
						d.Show(
							"and it is the coefficient",
							By(below, nat_order.LessEqOfLessThan.At(i, degree), weightData, cleared))
					})
				c.Otherwise(
					"from the degree on the coefficient is one or zero",
					func(d *Argument, notBelow Fact) {
						d.Cases(d.TermAs[Bool]("i = polynomial_degree(F)"))
						d.When(
							"at the degree it is one",
							func(e *Argument, same Fact) {
								e.Show(
									"which k[t⁻¹] holds",
									By(same, top, inverseLine, comm_ring.SubringOne))
							})
						d.Otherwise(
							"past the degree it is zero",
							func(e *Argument, other Fact) {
								past := e.Have(
									"i lies past the degree",
									"¬(i ≤ polynomial_degree(F))",
									ByArith(notBelow, other))
								e.Show(
									"which k[t⁻¹] holds",
									By(past, inverseLine, comm_ring.SubringZero))
							})
					})
			}))
		vanishesPast := a.Have(
			"the scaled equation vanishes past the degree",
			"vec⟨suc(polynomial_degree(F))⟩(«pmScaled»)",
			ByArith(vec_space.VecDef))
		overInverse := a.Have(
			"so it is a polynomial over k[t⁻¹]",
			"polynomial_over(«pmInversePolynomials», «pmScaled»)",
			By(coefficients, vanishesPast, polynomial.PolynomialOverDef))
		sameDegree := a.Have(
			"its degree is that of F, its top coefficient being one and not zero",
			"polynomial_degree(«pmScaled») = polynomial_degree(F)",
			By(
				overInverse,
				vanishesPast,
				top,
				field.OneNotZeroOn.Read(M),
				polynomial.DegreeExact.At(zero, inversePolynomials, scaled, degree)))
		a.Show(
			"so it is monic of degree d, and t^(−b)·z is its root",
			By(overInverse, top, sameDegree, vanishes, polynomial.PolynomialMonicDef))
	}),
})}

// PlaneScaledMinimalPolynomial — w = t^(-b) z is algebraic over k(t), and its
// minimal polynomial is the scaled equation G of the model, of degree deg F.
// G is monic over k[1/t] ⊆ k(t) of degree deg F and vanishes at w
// (ScaledMonicEquation); and k(t)(w) = k(t)(z), since w = t^(-b) z and
// z = t^b w, has degree deg F over k(t). A monic polynomial of degree
// [k(t)(w) : k(t)] vanishing at w is the minimal polynomial of w
// (MinimalPolynomialOfDegree).
var PlaneScaledMinimalPolynomial = planeScaledMinimalPolynomialThm{family.Add(registry.ProofEntry{
	Name: "PlaneScaledMinimalPolynomial",
	Key:  "prop_28961b2e464e030f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀t z:A. ∀F:(num → A). ∀b:num.",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
		},
		Conclusion: "algebraic_over(M, «pmRational», «pmGenerator») ∧ " +
			"minimal_polynomial(M, «pmRational», «pmGenerator») = «pmScaled» ∧ " +
			"polynomial_degree(«pmScaled») = polynomial_degree(F)",
		Abbrev: Abbrev{
			{Name: "adjoinedZ", Text: "field_adjoin(M, «pmRational», {z})"},
			{Name: "adjoinedW", Text: "field_adjoin(M, «pmRational», {«pmGenerator»})"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k *Expr[Set[A]],
		t, z *Expr[A],
		F *Arrow[Nat, A],
		b *Expr[Nat],
		subfieldK, model Fact,
	) {
		base := a.TermAs[Set[A]]("«pmRational»")
		adjoinedZ, adjoinedW := a.TermAs[Set[A]]("«adjoinedZ»"), a.TermAs[Set[A]]("«adjoinedW»")
		w, G := a.TermAs[A]("«pmGenerator»"), a.TermAs[Fun[Nat, A]]("«pmScaled»")
		ambient := a.Conjuncts(
			a.Have(
				"read in M: k is a subfield, t, z, w lie in M, z is algebraic over k(t) "+
					"with minimal polynomial F, t ≠ 0, k[1/t] ⊆ k(t) a subring, z = t^b w",
				"subfield(M, k) ∧ "+
					"t ∈ M.carrier ∧ "+
					"z ∈ M.carrier ∧ "+
					"«pmGenerator» ∈ M.carrier ∧ "+
					"algebraic_over(M, «pmRational», z) ∧ "+
					"F = minimal_polynomial(M, «pmRational», z) ∧ "+
					"t ≠ M.zero ∧ "+
					"subring(field_ring(M), «pmInversePolynomials») ∧ "+
					"«pmInversePolynomials» ⊆ «pmRational» ∧ "+
					"z = monoid_pow(M.mul, M.one, t, b) * «pmGenerator»",
				By(subfieldK, model, PlaneModelInAmbient.Read(M).At(K, k, t, z, F, b))),
			"k is a subfield of M",
			"t lies in M",
			"z lies in M",
			"w lies in M",
			"z is algebraic over k(t)",
			"F is its minimal polynomial over k(t)",
			"t is not zero",
			"k[1/t] is a subring of M",
			"inside k(t)",
			"z = t^b w")
		subK, algebraic, isMinimal, nonzero := ambient[0], ambient[4], ambient[5], ambient[6]
		lineRing, lineInBase, zFromW := ambient[7], ambient[8], ambient[9]
		tm, zm, wm :=
			a.MemberOf[on.M](t, ambient[1]), a.MemberOf[on.M](z, ambient[2]), a.MemberOf[on.M](w, ambient[3])
		adjoined := a.Have(
			"k(t) is a subfield of M holding k, t and 1/t, t not being zero",
			"subfield(M, «pmRational») ∧ k ⊆ «pmRational» ∧ t ∈ «pmRational» ∧ M.inv(t) ∈ «pmRational»",
			By(subK, nonzero, algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm), field.SubfieldInv))
		scaled := a.Have(
			"the scaled equation G of w is monic over k[1/t] of degree deg F and vanishes at w",
			"polynomial_over(«pmInversePolynomials», «pmScaled») ∧ "+
				"polynomial_monic(«pmScaled») ∧ "+
				"polynomial_eval(«pmScaled», «pmGenerator») = M.zero ∧ "+
				"polynomial_degree(«pmScaled») = polynomial_degree(F)",
			By(subfieldK, model, ScaledMonicEquation.Read(M).At(K, k, t, z, F, b)))
		ofZ := a.Have(
			"F, the minimal polynomial of z, has degree [k(t)(z) : k(t)]",
			"extension_degree(M, «pmRational», «adjoinedZ») = polynomial_degree(F)",
			By(isMinimal, algebraic, adjoined, algebraic_element.AdjoinDegree.Read(M).At(base, zm)))

		// k(t)(w) = k(t)(z): each generator lies in the field the other generates.
		fields := a.Have(
			"k(t)(z) and k(t)(w) are subfields of M over k(t), holding z and w",
			"subfield(M, «adjoinedZ») ∧ "+
				"«pmRational» ⊆ «adjoinedZ» ∧ "+
				"z ∈ «adjoinedZ» ∧ "+
				"subfield(M, «adjoinedW») ∧ "+
				"«pmRational» ⊆ «adjoinedW» ∧ "+
				"«pmGenerator» ∈ «adjoinedW»",
			By(
				adjoined,
				algebraic_element.AdjoinElementSubfield.Read(M).At(base, zm),
				algebraic_element.AdjoinElementSubfield.Read(M).At(base, wm)))
		ringZ := a.Have(
			"k(t)(z) is a ring under M's operations",
			"comm_ring_on(restrict_ring(field_ring(M), «adjoinedZ»))",
			By(fields, field.SubfieldCommRing.Read(M).At(adjoinedZ)))
		ringW := a.Have(
			"and so is k(t)(w)",
			"comm_ring_on(restrict_ring(field_ring(M), «adjoinedW»))",
			By(fields, field.SubfieldCommRing.Read(M).At(adjoinedW)))
		wInZ := a.Have(
			"w = t^(-b) z lies in k(t)(z)",
			"«pmGenerator» ∈ «adjoinedZ»",
			By(
				fields,
				adjoined,
				comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringZ)),
				comm_ring.MulIn.Read(ringZ),
				set_basic.SubsetDef))
		zInW := a.Have(
			"z = t^b w lies in k(t)(w)",
			"z ∈ «adjoinedW»",
			By(
				zFromW,
				fields,
				adjoined,
				comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringW)),
				comm_ring.MulIn.Read(ringW),
				set_basic.SubsetDef))
		sameField := a.Have(
			"so k(t)(w) = k(t)(z)",
			"«adjoinedW» = «adjoinedZ»",
			By(
				fields,
				zInW,
				wInZ,
				algebraic_element.AdjoinLeast.Read(M).At(base, a.TermAs[Set[A]]("{«pmGenerator»}"), adjoinedZ),
				algebraic_element.AdjoinLeast.Read(M).At(base, a.TermAs[Set[A]]("{z}"), adjoinedW),
				set_order.SingSubset,
				set_order.SubsetAntisym))
		minimal := a.Have(
			"G is the minimal polynomial of w over k(t): monic "+
				"over k(t) of degree [k(t)(w) : k(t)], vanishing at w",
			"«pmScaled» = minimal_polynomial(M, «pmRational», «pmGenerator»)",
			By(
				adjoined,
				scaled,
				lineRing,
				lineInBase,
				sameField,
				ofZ,
				algebraic_element.MinimalPolynomialOfDegree.Read(M).At(base, wm, G),
				polynomial.PolynomialOverMono))
		algebraicW := a.Have(
			"w is algebraic over k(t), lying in the finite extension k(t)(z)",
			"algebraic_over(M, «pmRational», «pmGenerator»)",
			By(
				adjoined,
				fields,
				algebraic,
				wInZ,
				algebraic_element.AdjoinDegree.Read(M).At(base, zm),
				algebraic_element.FiniteExtensionAlgebraic.Read(M).At(base, adjoinedZ, w)))
		a.Show(
			"w is algebraic over k(t), with minimal polynomial G of degree deg F",
			By(algebraicW, minimal, scaled))
	}),
})}

// PlaneChartOneBasis — the second chart of a plane model, k[1/t][w] with
// w = t^(-b) z, is free over k[1/t] on the powers of w below deg F: the minimal
// polynomial of w over k(t) is the scaled equation G, of degree deg F, whose
// coefficients lie in k[1/t] (PlaneScaledMinimalPolynomial), so its short
// powers are a basis of k[1/t][w] (MonicSubringPowerBasis).
var PlaneChartOneBasis = planeChartOneBasisThm{family.Add(registry.ProofEntry{
	Name: "PlaneChartOneBasis",
	Key:  "prop_4e8f609ecf035121",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀t z:A. ∀F:(num → A). ∀b:num.",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
		},
		Conclusion: "module_basis(restrict_ring(field_ring(M), «pmInversePolynomials»), " +
			"    restrict_module(regular_module(field_ring(M)), «pmChart1»), " +
			"    «pmPowersW») ∧ " +
			"has_size(«pmPowersW», polynomial_degree(F))",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k *Expr[Set[A]],
		t, z *Expr[A],
		F *Arrow[Nat, A],
		b *Expr[Nat],
		subfieldK, model Fact,
	) {
		base, line1 := a.TermAs[Set[A]]("«pmRational»"), a.TermAs[Set[A]]("«pmInversePolynomials»")
		w := a.TermAs[A]("«pmGenerator»")
		ambient := a.Conjuncts(
			a.Have(
				"read in M, k is a subfield, t and w lie in M, and k[1/t] is a subring of M inside k(t)",
				"subfield(M, k) ∧ "+
					"t ∈ M.carrier ∧ "+
					"«pmGenerator» ∈ M.carrier ∧ "+
					"subring(field_ring(M), «pmInversePolynomials») ∧ "+
					"«pmInversePolynomials» ⊆ «pmRational»",
				By(subfieldK, model, PlaneModelInAmbient.Read(M).At(K, k, t, z, F, b))),
			"k is a subfield of M",
			"t lies in M",
			"w lies in M",
			"k[1/t] is a subring of M",
			"inside k(t)")
		subK, lineRing, lineInBase := ambient[0], ambient[3], ambient[4]
		tm, wm := a.MemberOf[on.M](t, ambient[1]), a.MemberOf[on.M](w, ambient[2])
		adjoined := a.Have(
			"k(t) is a subfield of M",
			"subfield(M, «pmRational»)",
			By(subK, algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm)))
		scaled := a.Have(
			"the scaled equation G of w has its coefficients in k[1/t]",
			"polynomial_over(«pmInversePolynomials», «pmScaled»)",
			By(subfieldK, model, ScaledMonicEquation.Read(M).At(K, k, t, z, F, b)))
		minimal := GroupPremises(
			subfieldK, model, PlaneScaledMinimalPolynomial.Read(M).At(K, k, t, z, F, b))
		a.Show(
			"the powers of w below deg F are a basis of k[1/t][w] "+
				"over k[1/t], and k[1/t][w] is the second chart",
			By(
				adjoined,
				lineRing,
				lineInBase,
				scaled,
				minimal,
				integral_element.MonicSubringPowerBasis.Read(M).At(base, line1, wm),
				PlaneChartsInAmbient.At(a.TermAs[FieldOps[A]]("M"), K, k, t, z, b)))
	}),
})}

// PlaneChartsMeet — the functions regular on both charts of a plane model are
// the constants: k[t][z] ∩ k[1/t][w] = k. A common member x is r(z) with r over
// k[t] and s(w) with s over k[1/t], both vanishing from deg F on, F and the
// scaled equation G being monic of degree deg F (IntegralShortRepresentative).
// As w = t^(-b) z, s(w) is the value at z of s weighted by the powers of
// t^(-b) (EvalAtScaledPoint); r and the weighted s lie over k(t), and their
// difference vanishes from the degree of the minimal polynomial F of z on, so
// they agree (ShortPolynomialsAgree): r(i) = t^(-bi)·s(i). For i > 0 this forces r(i) = 0,
// k[t] meeting t^(-bi)·k[1/t] in zero (LineNegativeSectionsVanish); r(0) = s(0)
// lies in k[t] ∩ k[1/t] = k (LineGlobalSections); so x = r(0) lies in k.
var PlaneChartsMeet = planeChartsMeetThm{family.Add(registry.ProofEntry{
	Name: "PlaneChartsMeet",
	Key:  "prop_30e2d32c54a51396",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀t z:A. ∀F:(num → A). ∀b:num.",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
		},
		Conclusion: "«pmChart0» ∩ «pmChart1» = k",
		Abbrev: Abbrev{
			{Name: "weighted", Text: "λs:(num → A). λi:num. " +
				"    s(i) * monoid_pow(M.mul, M.one, monoid_pow(M.mul, M.one, M.inv(t), b), i)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k *Expr[Set[A]],
		t, z *Expr[A],
		F *Arrow[Nat, A],
		b *Expr[Nat],
		subfieldK, model Fact,
	) {
		ring := field.RingOn.Read(M)
		multiplicative := comm_ring.MulMonoidOn.Read(ring)
		base, line0, line1 :=
			a.TermAs[Set[A]]("«pmRational»"),
			a.TermAs[Set[A]]("«pmPolynomials»"),
			a.TermAs[Set[A]]("«pmInversePolynomials»")
		w, G := a.TermAs[A]("«pmGenerator»"), a.TermAs[Fun[Nat, A]]("«pmScaled»")
		ambient := a.Conjuncts(
			a.Have(
				"read in M: k is a subfield, t, z, w lie in M, t is transcendental "+
					"over k, F is the minimal polynomial of z, k[1/t] ⊆ k(t) is a subring",
				"subfield(M, k) ∧ "+
					"t ∈ M.carrier ∧ "+
					"z ∈ M.carrier ∧ "+
					"«pmGenerator» ∈ M.carrier ∧ "+
					"¬algebraic_over(M, k, t) ∧ "+
					"F = minimal_polynomial(M, «pmRational», z) ∧ "+
					"subring(field_ring(M), «pmInversePolynomials») ∧ "+
					"«pmInversePolynomials» ⊆ «pmRational»",
				By(subfieldK, model, PlaneModelInAmbient.Read(M).At(K, k, t, z, F, b))),
			"k is a subfield of M",
			"t lies in M",
			"z lies in M",
			"w lies in M",
			"t is transcendental over k",
			"F is the minimal polynomial of z over k(t)",
			"k[1/t] is a subring of M",
			"inside k(t)")
		subK, tIn, transcendental, isMinimal := ambient[0], ambient[1], ambient[4], ambient[5]
		lineRing, lineInBase := ambient[6], ambient[7]
		tm, zm, wm :=
			a.MemberOf[on.M](t, tIn), a.MemberOf[on.M](z, ambient[2]), a.MemberOf[on.M](w, ambient[3])
		um := field.InvIn.Read(M).At(tm)
		relation := a.Have(
			"F is monic over k[t] and vanishes at z",
			"polynomial_over(«pmPolynomials», F) ∧ polynomial_monic(F) ∧ polynomial_eval(F, z) = M.zero",
			By(subfieldK, model, PlaneModelRelation.Read(M).At(K, k, t, z, F, b)))
		scaled := a.Have(
			"the scaled equation G of w is monic over k[1/t], vanishes at w, and has degree deg F",
			"polynomial_over(«pmInversePolynomials», «pmScaled») ∧ "+
				"polynomial_monic(«pmScaled») ∧ "+
				"polynomial_eval(«pmScaled», «pmGenerator») = M.zero ∧ "+
				"polynomial_degree(«pmScaled») = polynomial_degree(F)",
			By(subfieldK, model, ScaledMonicEquation.Read(M).At(K, k, t, z, F, b)))
		positive := a.Have(
			"the weight b is positive",
			"0 < b",
			By(model, IntegralPlaneModelDef))
		lines := a.Have(
			"k(t) is a subfield of M, and k[t] and k[1/t] are subrings of M between k and k(t)",
			"subfield(M, «pmRational») ∧ "+
				"subring(field_ring(M), «pmPolynomials») ∧ "+
				"k ⊆ «pmPolynomials» ∧ "+
				"«pmPolynomials» ⊆ «pmRational» ∧ "+
				"subring(field_ring(M), «pmInversePolynomials») ∧ "+
				"k ⊆ «pmInversePolynomials» ∧ "+
				"«pmInversePolynomials» ⊆ «pmRational»",
			By(
				subK,
				lineRing,
				lineInBase,
				algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm),
				algebraic_element.PolynomialImageRing.Read(M).At(k, tm),
				algebraic_element.PolynomialImageRing.Read(M).At(k, um)))
		charts := a.Have(
			"the charts are subrings of M holding their lines",
			"subring(field_ring(M), «pmImage0») ∧ "+
				"«pmPolynomials» ⊆ «pmImage0» ∧ "+
				"subring(field_ring(M), «pmImage1») ∧ "+
				"«pmInversePolynomials» ⊆ «pmImage1»",
			By(
				lines,
				algebraic_element.PolynomialImageSubring.Read(M).At(line0, zm),
				algebraic_element.PolynomialImageSubring.Read(M).At(line1, wm)))
		baseRing := a.Have(
			"k(t) is a ring under M's operations",
			"comm_ring_on(restrict_ring(field_ring(M), «pmRational»))",
			By(lines, field.SubfieldCommRing.Read(M).At(base)))
		inverseInBase := a.Have(
			"1/t lies in k(t), as k[1/t] does",
			"M.inv(t) ∈ «pmRational»",
			By(lines, subK, algebraic_element.PolynomialImageRing.Read(M).At(k, um), set_basic.SubsetDef))
		power := a.Have(
			"t^(-b) lies in M",
			"monoid_pow(M.mul, M.one, M.inv(t), b) ∈ M.carrier",
			By(um, comm_monoid.PowIn.Read(multiplicative)))
		pm := a.MemberOf[on.M](a.TermAs[A]("monoid_pow(M.mul, M.one, M.inv(t), b)"), power)
		within := a.Have(
			"a function regular on both charts is a constant",
			"«pmImage0» ∩ «pmImage1» ⊆ k",
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(c *Argument) {
				x := c.FixAs[A]("x")
				inBoth := c.Assume()
				members := c.Have(
					"x lies in both charts",
					"x ∈ «pmImage0» ∧ x ∈ «pmImage1»",
					BySets(inBoth))
				r, rData := c.ObtainAs[Fun[Nat, A]](
					"x is the value at z of a polynomial r over k[t] vanishing from deg F on",
					"∃r:(num → A). "+
						"    polynomial_over(«pmPolynomials», r) ∧ "+
						"    vec⟨polynomial_degree(F)⟩(r) ∧ "+
						"    x = polynomial_eval(r, z)",
					By(
						members,
						lines,
						relation,
						integral_element.IntegralShortRepresentative.Read(M).At(line0, zm, x, F)))
				s, sData := c.ObtainAs[Fun[Nat, A]](
					"and the value at w of a polynomial s over k[1/t] vanishing from deg G = deg F on",
					"∃s:(num → A). "+
						"    polynomial_over(«pmInversePolynomials», s) ∧ "+
						"    vec⟨polynomial_degree(F)⟩(s) ∧ "+
						"    x = polynomial_eval(s, «pmGenerator»)",
					By(
						members,
						lines,
						scaled,
						integral_element.IntegralShortRepresentative.Read(M).At(line1, wm, x, G)))
				rParts := c.Conjuncts(
					rData,
					"r is over k[t]",
					"r vanishes from deg F on",
					"x = r(z)")
				sParts := c.Conjuncts(
					sData,
					"s is over k[1/t]",
					"s vanishes from deg F on",
					"x = s(w)")
				inField := c.Have(
					"r and s are polynomials over M",
					"polynomial_over(M.carrier, r) ∧ polynomial_over(M.carrier, s)",
					By(rParts[0], sParts[0], lines, comm_ring.SubringSubset, polynomial.PolynomialOverMono))
				weighted := c.TermAs[Fun[Nat, A]]("«weighted»(s)")
				atZ := c.Have(
					"as w = t^(-b) z, s(w) is the value at z of s weighted by the powers of t^(-b)",
					"polynomial_eval(s, «pmGenerator») = polynomial_eval(«weighted»(s), z)",
					By(inField, polynomial_evaluation.EvalAtScaledPoint.Read(ring).At(s, pm, zm)))
				weightedIn := c.Have(
					"the weighted coefficients lie in k(t)",
					"∀i:num. «weighted»(s, i) ∈ «pmRational»",
					By(
						sParts[0],
						lines,
						inverseInBase,
						comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(baseRing)),
						comm_ring.MulIn.Read(baseRing),
						polynomial.PolynomialOverDef,
						set_basic.SubsetDef))
				sPast := c.Unfolded(sParts[1], vec_space.VecDef)
				weightedShort := c.Have(
					"and vanish from deg F on, as the coefficients of s do",
					"vec⟨polynomial_degree(F)⟩(«weighted»(s))",
					Simp(Fwd(vec_space.VecDef)),
					Derive(func(d *Argument) {
						i := d.FixAs[Nat]("i")
						from := d.Assume()
						vanishes := d.Have(
							"s vanishes at i",
							"s(i) = M.zero",
							By(from, sPast.At(i)))
						d.Show(
							"so does its weighted coefficient",
							vanishes.Rw(),
							ByArith(M, power))
					}))
				rPast, weightedPast :=
					c.Unfolded(rParts[1], vec_space.VecDef), c.Unfolded(weightedShort, vec_space.VecDef)
				differenceShort := c.Have(
					"so r − weighted s vanishes from deg F on",
					"vec⟨polynomial_degree(F)⟩(vec_sub(r, «weighted»(s)))",
					Simp(Fwd(vec_space.VecDef), Fwd(vec_space.VecSubDef)),
					Derive(func(d *Argument) {
						i := d.FixAs[Nat]("i")
						from := d.Assume()
						d.Show(
							"both coefficients are zero there",
							GroupPremises(from, rPast.At(i)).Rw(),
							GroupPremises(from, weightedPast.At(i)).Rw(),
							ByArith(M))
					}))
				overBase := c.Have(
					"r and the weighted s are polynomials over k(t)",
					"polynomial_over(«pmRational», «weighted»(s)) ∧ polynomial_over(«pmRational», r)",
					By(
						weightedShort,
						weightedIn,
						rParts[0],
						lines,
						polynomial.PolynomialOverDef,
						polynomial.PolynomialOverMono))
				agree := c.Have(
					"so r is the weighted s: over k(t), with one value x at z, their "+
						"difference vanishing from deg F on, F the minimal polynomial of z",
					"r = «weighted»(s)",
					By(
						overBase,
						differenceShort,
						isMinimal,
						lines,
						atZ,
						rParts[2],
						sParts[2],
						algebraic_element.ShortPolynomialsAgree.Read(M).At(base, zm, r, weighted)))
				higher := c.Have(
					"the coefficients of r past the constant one vanish",
					"∀i:num. 0 < i ⇒ r(i) = M.zero",
					Derive(func(d *Argument) {
						i := d.FixAs[Nat]("i")
						above := d.Assume()
						coefficient := d.Have(
							"r(i) = t^(-bi)·s(i)",
							"r(i) = monoid_pow(M.mul, M.one, M.inv(t), b * i) * s(i)",
							By(
								agree,
								inField,
								comm_monoid.PowPowOn.Read(multiplicative).At(um, b, i),
								comm_monoid.CommOn.Read(multiplicative),
								comm_monoid.PowIn.Read(multiplicative),
								polynomial.PolynomialOverDef))
						exponent := d.Have(
							"bi is positive",
							"0 < b * i",
							ByArith(positive, above, nat_order.LessEqSelfMul.At(b, i)))
						d.Show(
							"so r(i) = 0: k[t] meets t^(-bi)·k[1/t] in zero",
							By(
								subK,
								transcendental,
								exponent,
								coefficient,
								rParts[0],
								sParts[0],
								polynomial.PolynomialOverDef,
								projective_line.LineNegativeSectionsVanish.Read(M).At(
									k, tm, d.TermAs[A]("r(i)"), d.TermAs[A]("s(i)"), d.TermAs[Nat]("b * i"))))
					}))
				constantTerms := c.Have(
					"the constant coefficients agree, t^(-b) to the power 0 being one",
					"r(0) = s(0)",
					By(
						agree,
						inField,
						comm_monoid.MonoidPowDef,
						comm_monoid.RightIdentityOn.Read(multiplicative),
						polynomial.PolynomialOverDef))
				constant := c.Have(
					"so r(0) lies in k[t] ∩ k[1/t] = k",
					"r(0) ∈ k",
					BySets(
						constantTerms,
						rParts[0],
						sParts[0],
						subK,
						tIn,
						transcendental,
						polynomial.PolynomialOverDef,
						projective_line.LineGlobalSections.Read(M).At(k, tm)))
				short := c.Have(
					"r vanishes from index one on",
					"vec⟨suc(0)⟩(r)",
					ByArith(higher, vec_space.VecDef))
				degree := c.Have(
					"so r is constant",
					"polynomial_degree(r) = 0",
					ByArith(short, polynomial.DegreeLeast.At(c.TermAs[A]("M.zero"), r, c.TermAs[Nat]("0"))))
				c.Show(
					"so x = r(z) = r(0) lies in k",
					By(
						Normalized,
						degree,
						inField,
						rParts[2],
						constant,
						polynomial_evaluation.DegreeZeroEval.Read(ring).At(r, zm)))
			}))
		meet := a.Have(
			"so the charts meet in k, which both contain",
			"«pmImage0» ∩ «pmImage1» = k",
			BySets(within, charts, lines))
		a.Show(
			"the charts are read with M's operations",
			By(meet, PlaneChartsInAmbient.At(a.TermAs[FieldOps[A]]("M"), K, k, t, z, b)))
	}),
})}

// PlaneEquationBiaffineCurve — an integral plane model is a curve over the
// projective line: its function field K = k(t)(z) is held by the charts
// A₀ = k[t][z] and A₁ = k[1/t][w], w = t^(-b) z, glued along A₀[1/t]. The
// subfield k, t and its transcendence are the model's; the charts are biaffine
// (PlaneChartsBiaffine), hold k[t] and k[1/t], and are free over them on the
// powers of z and of w below deg F (MonicSubringPowerBasis, PlaneChartOneBasis);
// they meet in k (PlaneChartsMeet); and K is the fraction field of A₀, each
// member of K times a nonzero member of k[t] lying in A₀
// (AdjoinCommonDenominator). The power basis of A₀ over k[t] is the second
// claim.
var PlaneEquationBiaffineCurve = planeEquationBiaffineCurveThm{family.Add(registry.ProofEntry{
	Name: "PlaneEquationBiaffineCurve",
	Key:  "prop_707326970b911a12",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀t z:A. ∀F:(num → A). ∀b:num.",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
		},
		Conclusion: "curve_over_line(restrict_field(M, K), k, t, «pmChart0», «pmChart1», «pmOverlap») ∧ " +
			"(∃E:set(A). " +
			"    finite(E) ∧ " +
			"    E = «pmPowersZ» ∧ " +
			"    module_basis(restrict_ring(field_ring(M), «pmPolynomials»), " +
			"        restrict_module(regular_module(field_ring(M)), «pmChart0»), " +
			"        E))",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k *Expr[Set[A]],
		t, z *Expr[A],
		F *Arrow[Nat, A],
		b *Expr[Nat],
		subfieldK, model Fact,
	) {
		ring := field.RingOn.Read(M)
		multiplicative := comm_ring.MulMonoidOn.Read(ring)
		ops := a.TermAs[FieldOps[A]]("M")
		base, line0, line1 :=
			a.TermAs[Set[A]]("«pmRational»"),
			a.TermAs[Set[A]]("«pmPolynomials»"),
			a.TermAs[Set[A]]("«pmInversePolynomials»")
		u, w := a.TermAs[A]("M.inv(t)"), a.TermAs[A]("«pmGenerator»")
		ambient := a.Conjuncts(
			a.Have(
				"read in M: k ⊆ K ⊆ M with k a subfield, t, z lie in K, t, z, w "+
					"lie in M, z is algebraic over k(t) with minimal polynomial F, t ≠ 0",
				"subfield(M, k) ∧ "+
					"k ⊆ K ∧ "+
					"K ⊆ M.carrier ∧ "+
					"t ∈ K ∧ "+
					"z ∈ K ∧ "+
					"t ∈ M.carrier ∧ "+
					"z ∈ M.carrier ∧ "+
					"«pmGenerator» ∈ M.carrier ∧ "+
					"algebraic_over(M, «pmRational», z) ∧ "+
					"F = minimal_polynomial(M, «pmRational», z) ∧ "+
					"t ≠ M.zero",
				By(subfieldK, model, PlaneModelInAmbient.Read(M).At(K, k, t, z, F, b))),
			"k is a subfield of M",
			"k lies in K",
			"K lies in M",
			"t lies in K",
			"z lies in K",
			"t lies in M",
			"z lies in M",
			"w lies in M",
			"z is algebraic over k(t)",
			"F is its minimal polynomial over k(t)",
			"t is not zero")
		subK, kInK, inM, tInK, zInK := ambient[0], ambient[1], ambient[2], ambient[3], ambient[4]
		algebraic, isMinimal, nonzero := ambient[8], ambient[9], ambient[10]
		tm, zm, wm :=
			a.MemberOf[on.M](t, ambient[5]), a.MemberOf[on.M](z, ambient[6]), a.MemberOf[on.M](w, ambient[7])
		um := field.InvIn.Read(M).At(tm)

		// Read in K: the constants, the parameter, and the charts glued along A₀[1/t].
		function := a.Have(
			"K is a field under M's operations",
			"field_on(restrict_field(M, K))",
			By(subfieldK, field.SubfieldFieldOn.Read(M).At(K)))
		readInK := a.Have(
			"read in K, K is regular over k, t is transcendental over k, and K is k(t)(z)",
			"regular_function_field(restrict_field(M, K), k, K) ∧ "+
				"¬algebraic_over(restrict_field(M, K), k, t) ∧ "+
				"field_adjoin(restrict_field(M, K), «pmRationalInK», {z}) = K",
			By(a.Unfolded(model, IntegralPlaneModelDef)))
		inK := a.Have(
			"so k is a subfield of K",
			"subfield(restrict_field(M, K), k)",
			By(readInK, function_field.RegularFunctionFieldDef))
		biaffine := a.Have(
			"read in K, the charts are biaffine, glued along A₀[1/t]",
			"biaffine(restrict_ring(«pmRing», «pmOverlap»), «pmChart0», «pmChart1», t, M.inv(t))",
			By(
				inK,
				nonzero,
				PlaneChartsBiaffine.Read(function).At(
					k, a.MemberOf[on.Any](t, tInK), a.MemberOf[on.Any](z, zInK), b),
				field.RestrictFieldRing))
		overlapInK := a.Have(
			"A₀[1/t] lies in K",
			"«pmOverlap» ⊆ K",
			Unfold(ring_away.RingAwayDef),
			BySets())

		// The power bases of the charts.
		relation := a.Have(
			"F is monic over k[t] and vanishes at z",
			"polynomial_over(«pmPolynomials», F) ∧ polynomial_monic(F) ∧ polynomial_eval(F, z) = M.zero",
			By(subfieldK, model, PlaneModelRelation.Read(M).At(K, k, t, z, F, b)))
		lines := a.Have(
			"k(t) is a subfield of M, and k[t] a subring of M inside it",
			"subfield(M, «pmRational») ∧ "+
				"subring(field_ring(M), «pmPolynomials») ∧ "+
				"«pmPolynomials» ⊆ «pmRational»",
			By(
				subK,
				algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm),
				algebraic_element.PolynomialImageRing.Read(M).At(k, tm)))
		basisZ := a.Have(
			"k[t][z] is free over k[t] on the powers of z below deg F, F being "+
				"the minimal polynomial of z over k(t) with coefficients in k[t]",
			"module_basis(restrict_ring(field_ring(M), «pmPolynomials»), "+
				"    restrict_module(regular_module(field_ring(M)), «pmImage0»), "+
				"    «pmPowersZ») ∧ "+
				"has_size(«pmPowersZ», polynomial_degree(F))",
			By(
				lines,
				algebraic,
				isMinimal,
				relation,
				integral_element.MonicSubringPowerBasis.Read(M).At(base, line0, zm)))
		second := a.Have(
			"the powers of z below deg F are a finite basis of A₀ over k[t]",
			"∃E:set(A). "+
				"    finite(E) ∧ "+
				"    E = «pmPowersZ» ∧ "+
				"    module_basis(restrict_ring(field_ring(M), «pmPolynomials»), "+
				"        restrict_module(regular_module(field_ring(M)), «pmChart0»), "+
				"        E)",
			Witness(a.TermAs[Set[A]]("«pmPowersZ»")),
			By(basisZ, cardinality.HasSizeDef, PlaneChartsInAmbient.At(ops, K, k, t, z, b)))
		basisW := a.Have(
			"A₁ is free over k[1/t] on the powers of w below deg F",
			"module_basis(restrict_ring(field_ring(M), «pmInversePolynomials»), "+
				"    restrict_module(regular_module(field_ring(M)), «pmChart1»), "+
				"    «pmPowersW») ∧ "+
				"has_size(«pmPowersW», polynomial_degree(F))",
			By(subfieldK, model, PlaneChartOneBasis.Read(M).At(K, k, t, z, F, b)))
		sameModules := a.Have(
			"restricted to a set, the regular module of K is that of M",
			"∀X:set(A). "+
				"    restrict_module(regular_module(field_ring(restrict_field(M, K))), X) = "+
				"    restrict_module(regular_module(field_ring(M)), X)",
			Unfold(module_record.RestrictModuleDef))
		sameRings := a.Have(
			"and so is the ring",
			"∀X:set(A). restrict_ring(field_ring(restrict_field(M, K)), X) = restrict_ring(field_ring(M), X)",
			Unfold(module_record.RestrictRingDef))
		sameInverse := a.Have(
			"the inverse of K is that of M",
			"restrict_field(M, K).inv(t) = M.inv(t)",
			Unfold(field.RestrictFieldDef))
		basis0 := a.Have(
			"read in K, A₀ has a finite basis over k[t]",
			"∃E:set(A). "+
				"    finite(E) ∧ "+
				"    module_basis(restrict_ring(field_ring(restrict_field(M, K)), «pmPolynomialsInK»), "+
				"        restrict_module(regular_module(field_ring(restrict_field(M, K))), «pmChart0»), "+
				"        E)",
			By(second, sameModules, sameRings, algebraic_element.PolynomialsOverRestriction.At(ops, K, k, t)))
		basis1 := a.Have(
			"and A₁ over k[1/t]",
			"∃E:set(A). "+
				"    finite(E) ∧ "+
				"    module_basis(restrict_ring(field_ring(restrict_field(M, K)), "+
				"            polynomial_image(field_ring(restrict_field(M, K)), "+
				"                k, "+
				"                restrict_field(M, K).inv(t))), "+
				"        restrict_module(regular_module(field_ring(restrict_field(M, K))), «pmChart1»), "+
				"        E)",
			Witness(a.TermAs[Set[A]]("«pmPowersW»")),
			By(
				basisW,
				sameModules,
				sameRings,
				sameInverse,
				cardinality.HasSizeDef,
				algebraic_element.PolynomialsOverRestriction.At(ops, K, k, u)))
		linesIn := a.Have(
			"k[1/t] lies in A₁ and k[t] in A₀",
			"«pmInversePolynomials» ⊆ «pmChart1» ∧ «pmPolynomials» ⊆ «pmChart0»",
			By(
				subK,
				lines,
				algebraic_element.PolynomialImageRing.Read(M).At(k, um),
				algebraic_element.PolynomialImageSubring.Read(M).At(line1, wm),
				algebraic_element.PolynomialImageSubring.Read(M).At(line0, zm),
				PlaneChartsInAmbient.At(ops, K, k, t, z, b)))

		// K is the fraction field of A₀.
		ringK := a.Have(
			"K is a ring under M's operations",
			"comm_ring_on(«pmRing»)",
			By(subfieldK, field.SubfieldCommRing.Read(M).At(K)))
		sameBase := a.Have(
			"k(t) is one field read in K and in M, and lies in K",
			"«pmRationalInK» = «pmRational» ∧ «pmRational» ⊆ K",
			By(
				subfieldK,
				subK,
				kInK,
				tInK,
				algebraic_element.AdjoinInSubfield.Read(M).At(K, k, a.TermAs[Set[A]]("{t}")),
				algebraic_element.AdjoinLeast.Read(M).At(k, a.TermAs[Set[A]]("{t}"), K),
				set_order.SingSubset))
		generated := a.Have(
			"so K, which is k(t)(z) read in K, is k(t)(z) read in M",
			"field_adjoin(M, «pmRational», {z}) = K",
			By(
				readInK,
				subfieldK,
				zInK,
				sameBase,
				algebraic_element.AdjoinInSubfield.Read(M).At(K, base, a.TermAs[Set[A]]("{z}")),
				set_order.SingSubset))
		denominators := a.Have(
			"every member of K times a nonzero member of k[t] lies in k[t][z]",
			"∀y:A. y ∈ K ⇒ ∃d:A. d ∈ «pmPolynomials» ∧ d ≠ M.zero ∧ d * y ∈ «pmImage0»",
			Derive(func(c *Argument) {
				y := c.FixAs[A]("y")
				yIn := c.Assume()
				c.Show(
					"K = k(t)(z) with z algebraic over k(t), the fractions of k[t]",
					By(
						yIn,
						generated,
						subK,
						algebraic,
						lines,
						algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm),
						integral_element.RationalFunctionsFractionField.Read(M).At(k, tm),
						integral_element.AdjoinCommonDenominator.Read(M).At(base, line0, zm, y)))
			}))
		imageInK := a.Have(
			"k[t][z] lies in K and holds k[t]",
			"«pmImage0» ⊆ K ∧ «pmPolynomials» ⊆ «pmImage0»",
			By(
				ringK,
				kInK,
				tInK,
				zInK,
				lines,
				algebraic_element.PolynomialImageLeast.Read(M).At(k, K, t),
				algebraic_element.PolynomialImageLeast.Read(M).At(line0, K, z),
				algebraic_element.PolynomialImageSubring.Read(M).At(line0, zm)))
		fraction := a.Have(
			"so K is the fraction field of A₀",
			"fraction_field_carrier(«pmRing», «pmChart0»)",
			Simp(Fwd(field.FractionFieldCarrierDef), Fwd(PlaneChartsInAmbient)),
			By(
				imageInK,
				denominators,
				inM,
				lines,
				comm_monoid.CommOn.Read(multiplicative),
				comm_ring.SubringSubset,
				set_basic.SubsetDef))

		// The meet, and every clause together.
		meet := a.Have(
			"the charts meet in k",
			"«pmChart0» ∩ «pmChart1» = k",
			By(subfieldK, model, PlaneChartsMeet.Read(M).At(K, k, t, z, F, b)))
		curve := a.Have(
			"so the charts make K a curve over the line",
			"curve_over_line(restrict_field(M, K), k, t, «pmChart0», «pmChart1», «pmOverlap»)",
			Simp(Fwd(algebraic_curve.CurveOverLineDef)),
			SplitConjAll(
				Case(
					"k is a subfield of K",
					By(inK)),
				Case(
					"t lies in K",
					By(tInK)),
				Case(
					"t is transcendental over k",
					By(readInK)),
				Case(
					"the overlap lies in K",
					By(overlapInK)),
				Case(
					"the charts are biaffine, glued along the overlap",
					Simp(Rev(field.RestrictFieldRing)),
					By(biaffine)),
				Case(
					"k[t] lies in the first chart",
					By(linesIn, algebraic_element.PolynomialsOverRestriction.At(ops, K, k, t))),
				Case(
					"k[1/t] lies in the second chart",
					By(linesIn, algebraic_element.PolynomialsOverRestriction.At(ops, K, k, u))),
				Case(
					"the first chart has a finite basis over k[t]",
					By(basis0)),
				Case(
					"the second chart has a finite basis over k[1/t]",
					By(basis1)),
				Case(
					"the charts meet in k",
					By(meet)),
				Case(
					"K is the fraction field of the first chart",
					By(fraction, field.RestrictFieldRing.At(ops, K)))))
		a.Show(
			"the curve over the line, and the power basis of A₀ over k[t]",
			By(curve, second))
	}),
})}
