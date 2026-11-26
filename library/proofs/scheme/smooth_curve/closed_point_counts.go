// closed_point_counts.go — closed points counted by colength: finitely many of bounded degree.

package smooth_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/sets/weighted_divisors"
	"github.com/euc-ai/xugo/library/registry"
)

// ChartIdealsAboveElement — a nonzero element of a chart lies in finitely many
// of its ideals: its span has finite index, and they all lie above the span.
var ChartIdealsAboveElement = chartIdealsAboveElementThm{family.Add(registry.ProofEntry{
	Name: "ChartIdealsAboveElement",
	Key:  "prop_61ae2b5c7f29f056",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t w:A.",
		Hypotheses: []string{"«scCurve»", "w ∈ A₀", "w ≠ L.zero"},
		Conclusion: "finite({J:set(A) | ring_ideal(«chart», J) ∧ w ∈ J})",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t, w *Expr[A],
			curve, inChart, nonzero Fact,
		) {
			chart := a.TermAs[RingOps[A]]("«chart»")
			single := a.TermAs[Set[A]]("{w}")
			chartRing := a.Have(
				"the chart is a ring",
				"comm_ring_on(«chart»)",
				By(curve, ChartCommRing.Read(L).At(k, A0, A1, A01, t)))
			H, spanDef := a.LetAs[Set[A]]("H", "ideal_span(«chart», {w})")
			singleton := a.Have(
				"{w} lies in the chart and holds w",
				"{w} ⊆ A₀ ∧ w ∈ {w}",
				BySets(inChart))
			spanFacts := a.Conjuncts(
				a.Have(
					"H is an ideal holding w",
					"ring_ideal(«chart», H) ∧ w ∈ H",
					By(
						Normalized,
						spanDef,
						singleton,
						ring_ideal.SpanIdeal.Read(chartRing).At(single),
						ring_ideal.SpanContains.At(chart, single),
						set_basic.SubsetDef)),
				"H is an ideal",
				"H holds w")
			ideal, holding := spanFacts[0], spanFacts[1]
			nonzeroSpan := a.Have(
				"so H is nonzero",
				"H ≠ {L.zero}",
				BySets(holding, nonzero))
			cosets := a.Have(
				"H has finite index",
				"finite(left_cosets(L.add, A₀, H))",
				By(curve, ideal, nonzeroSpan, ChartIdealFiniteQuotient.Read(L).At(k, A0, A1, A01, t, H)))
			above := a.Have(
				"so finitely many ideals lie above H",
				"finite({J:set(A) | ring_ideal(«chart», J) ∧ H ⊆ J})",
				By(ideal, cosets, quotient_ring.IdealsAboveFiniteIndex.Read(chartRing).At(H)))
			least := a.Have(
				"an ideal holding w lies above its span H",
				"∀J:set(A). ring_ideal(«chart», J) ∧ w ∈ J ⇒ H ⊆ J",
				Derive(func(b *Argument) {
					J := b.FixAs[Set[A]]("J")
					given := b.Conjuncts(
						b.Assume(),
						"J is an ideal",
						"J holds w")
					holds := b.Have(
						"J contains {w}",
						"{w} ⊆ J",
						BySets(given[1]))
					b.Show(
						"H is the least such ideal",
						By(Normalized, spanDef, given[0], holds, ring_ideal.SpanLeast.At(chart, single, J)))
				}))
			inside := a.Have(
				"so the ideals holding w are among those above H",
				"{J:set(A) | ring_ideal(«chart», J) ∧ w ∈ J} ⊆ {J:set(A) | ring_ideal(«chart», J) ∧ H ⊆ J}",
				BySets(least))
			a.Show(
				"a subset of a finite set is finite",
				By(
					above,
					inside,
					finite_set.FiniteSubset.At(
						a.TermAs[Set[Set[A]]]("{J:set(A) | ring_ideal(«chart», J) ∧ w ∈ J}"),
						a.TermAs[Set[Set[A]]]("{J:set(A) | ring_ideal(«chart», J) ∧ H ⊆ J}"))))
		}),
})}

// ChartMaximalColength — a maximal ideal of a chart has finite positive
// colength over the constants: it is nonzero, so its quotient is finite
// dimensional, and it is not the whole chart, so that dimension is not zero.
var ChartMaximalColength = chartMaximalColengthThm{family.Add(registry.ProofEntry{
	Name: "ChartMaximalColength",
	Key:  "prop_fbbbfac1d940f7f9",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀m:set(A).",
		Hypotheses: []string{"«scCurve»", "maximal_ideal(«chart», m)"},
		Conclusion: "finite_dimensional(«scalars», quotient_module(«chartVectors», m)) ∧ " +
			"0 < module_dim(«scalars», quotient_module(«chartVectors», m))",
		Abbrev: Abbrev{
			{Name: "scalars", Text: "restrict_ring(field_ring(L), k)"},
			{Name: "vectors", Text: "regular_module(field_ring(L))"},
			{Name: "chartVectors", Text: "restrict_module(«vectors», A₀)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			m *Expr[Set[A]],
			curve, maximal Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			chart := a.TermAs[RingOps[A]]("«chart»")
			scalars := a.TermAs[RingOps[A]]("«scalars»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»")
			read := a.Conjuncts(
				GroupPremises(curve, ChartSubring.Read(L).At(k, A0, A1, A01, t)),
				"the constants are a subfield of L",
				"the constants lie in the chart",
				"the chart is a subring of L")
			constants, kInChart, subring := read[0], read[1], read[2]
			ideal := a.Have(
				"m is an ideal of the chart",
				"ring_ideal(«chart», m)",
				By(maximal, ring_ideal.MaximalIdealIdeal.At(chart, m)))
			proper := a.Have(
				"m is proper, as one lies in the chart",
				"L.one ∉ m ∧ L.one ∈ A₀",
				By(maximal, subring, ring_ideal.MaximalIdealProper.At(chart, m), comm_ring.SubringOne.At(ring, A0)))
			colength := a.Have(
				"m is nonzero, so it has finite colength",
				"finite_dimensional(«scalars», quotient_module(«chartVectors», m))",
				By(
					curve,
					maximal,
					ideal,
					ChartMaximalNonzero.Read(L).At(k, A0, A1, A01, t, m),
					ChartIdealFiniteQuotient.Read(L).At(k, A0, A1, A01, t, m)))
			subspaces := a.Have(
				"over k, the chart and m are subspaces of L, and m lies in the chart",
				"submodule(«scalars», «vectors», A₀) ∧ submodule(«scalars», «vectors», m) ∧ m ⊆ A₀",
				By(
					subring,
					ideal,
					kInChart,
					fractional_ideal.SubringSubmodule.Read(L).At(A0),
					fractional_ideal.IntegralIdealFractional.Read(L).At(A0, m),
					submodule.SubmoduleRestrictScalars.At(chart, vectors, A0, scalars),
					submodule.SubmoduleRestrictScalars.At(chart, vectors, m, scalars),
					module_record.RestrictRingDef.At(ring, k),
					module_record.RestrictRingDef.At(ring, A0)))
			scalarField := a.Have(
				"k is a field of scalars for L",
				"ring_subfield(«scalars», L.inv, «scalars».carrier) ∧ module_on(«scalars», «vectors»)",
				By(
					constants,
					field.SubfieldRingSubfield.Read(L).At(k, k),
					field_extension.SubfieldScalars.Read(L).At(k),
					module_record.RestrictRingDef.At(ring, k)))
			zeroIff := a.Have(
				"the quotient vanishes exactly when m is the whole chart",
				"finite_dimensional(«scalars», quotient_module(«chartVectors», m)) ∧ "+
					"module_dim(«scalars», quotient_module(«chartVectors», m)) = 0 ⇔ "+
					"A₀ = m",
				By(
					scalarField,
					subspaces,
					module_dimension.QuotientDimZeroIff.At(scalars, vectors, a.TermAs[Fun[A, A]]("L.inv"), A0, m)))
			different := a.Have(
				"and m is not the whole chart",
				"A₀ ≠ m",
				BySets(proper))
			positive := a.Have(
				"so the colength is positive",
				"0 < module_dim(«scalars», quotient_module(«chartVectors», m))",
				Derive(func(b *Argument) {
					notPositive := b.SupposeNot()
					zero := b.Have(
						"suppose the colength vanishes",
						"module_dim(«scalars», quotient_module(«chartVectors», m)) = 0",
						ByArith(notPositive))
					b.Show(
						"then m would be the whole chart",
						By(different, colength, zero, zeroIff))
				}))
			a.Show(
				"so m has finite positive colength",
				By(colength, positive))
		}),
})}

// ChartMaximalPowerRepeat — the powers of t repeat modulo a maximal ideal of
// bounded colength: the ideal has at most q^n cosets, so two of the q^n + 1
// powers t⁰, …, t^(q^n) lie in one coset.
var ChartMaximalPowerRepeat = chartMaximalPowerRepeatThm{family.Add(registry.ProofEntry{
	Name: "ChartMaximalPowerRepeat",
	Key:  "prop_5693d84f8f0175ce",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀m:set(A). ∀n:num.",
		Hypotheses: []string{
			"«scCurve»",
			"maximal_ideal(«chart», m)",
			"«colength»(m) ≤ n",
		},
		Conclusion: "∃i j:num. i ≤ card(k) ^ n ∧ j ≤ card(k) ^ n ∧ i ≠ j ∧ -«tPow»(i) + «tPow»(j) ∈ m",
		Abbrev: Abbrev{
			{Name: "quotient", Text: "λm:set(A). " +
				"    quotient_module(restrict_module(regular_module(field_ring(L)), A₀), m)"},
			{Name: "colength", Text: "λm:set(A). module_dim(restrict_ring(field_ring(L), k), «quotient»(m))"},
			{Name: "tPow", Text: "λj:num. monoid_pow(L.mul, L.one, t, j)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			m *Expr[Set[A]],
			n *Expr[Nat],
			curve, maximal, bounded Fact,
		) {
			chart := a.TermAs[RingOps[A]]("«chart»")
			read := a.Conjuncts(
				GroupPremises(curve, ChartSubring.Read(L).At(k, A0, A1, A01, t)),
				"the constants are a subfield of L",
				"the constants lie in the chart",
				"the chart is a subring of L")
			constants, kInChart, subring := read[0], read[1], read[2]
			datum := a.Conjuncts(
				GroupPremises(curve, ChartOverlap.Read(L).At(k, A0, A1, A01, t)),
				"the overlap is a subring of L",
				"it contains the chart",
				"the chart holds t",
				"t is nonzero",
				"the overlap holds the inverse of t",
				"they multiply to one",
				"the overlap is the chart with t inverted, inside itself",
				"and inside L",
				"the powers of t and of its inverse")
			powers := datum[8]
			finiteConstants := a.Have(
				"there are finitely many constants",
				"finite(k)",
				By(curve, SmoothFiniteFieldCurveDef))
			chartRing := a.Have(
				"the chart is a ring",
				"comm_ring_on(«chart»)",
				By(curve, ChartCommRing.Read(L).At(k, A0, A1, A01, t)))
			ideal := a.Have(
				"m is an ideal of the chart",
				"ring_ideal(«chart», m)",
				By(maximal, ring_ideal.MaximalIdealIdeal.At(chart, m)))
			colength := a.Have(
				"m has finite colength",
				"finite_dimensional(restrict_ring(field_ring(L), k), «quotient»(m))",
				By(curve, maximal, ChartMaximalColength.Read(L).At(k, A0, A1, A01, t, m)))
			size := a.Simplified(
				a.Have(
					"so m has q^d cosets",
					"has_size(left_cosets(L.add, A₀, m), card(k) ^ «colength»(m))",
					By(
						constants,
						finiteConstants,
						subring,
						kInChart,
						ideal,
						colength,
						ColengthCosetCount.Read(L).At(k, A0, m))),
				Fwd(cardinality.HasSizeDef))
			constantsExist := a.Have(
				"there are constants",
				"card(k) ≠ 0",
				BySets(
					constants,
					finiteConstants,
					field.SubfieldOne.At(a.TermAs[FieldOps[A]]("L"), k),
					cardinality.CardEqZero.At(k)))
			monotone := a.Have(
				"so the number of cosets grows with the colength",
				"card(k) ^ «colength»(m) ≤ card(k) ^ n",
				Simp(Fwd(nat_order.LessEqPow)),
				By(constantsExist, bounded))
			counted := a.Have(
				"so m has at most q^n cosets",
				"finite(left_cosets(L.add, A₀, m)) ∧ card(left_cosets(L.add, A₀, m)) ≤ card(k) ^ n",
				ByArith(monotone, size))
			counts := a.Conjuncts(
				counted,
				"the cosets are finitely many",
				"at most q^n of them")
			additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(chartRing))
			subgroup := a.Have(
				"m is an additive subgroup of the chart, inside it",
				"subgroup(additive_group(«chart»), m) ∧ m ⊆ A₀",
				By(
					ideal,
					quotient_ring.IdealNormal.Read(chartRing).At(m),
					group.NormalSubgroupSubgroup.At(a.TermAs[group.GroupOps[A]]("additive_group(«chart»)"), m),
					ring_ideal.IdealSubset.At(chart, m)))
			parts := a.Conjuncts(
				subgroup,
				"m is a subgroup",
				"m lies in the chart")
			inChart := a.Have(
				"the powers of t lie in the chart",
				"∀j:num. «tPow»(j) ∈ A₀",
				a.ForEach(func(j *Expr[Nat]) Action {
					return By(powers.At(j))
				}))
			cosetIn := a.Have(
				"so the coset of each power is a coset of m",
				"∀i:num. i ≤ card(k) ^ n ⇒ left_coset(L.add, «tPow»(i), m) ∈ left_cosets(L.add, A₀, m)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					power := b.TermAs[A]("«tPow»(i)")
					b.Assume()
					b.Show(
						"each power lies in the chart",
						By(
							inChart.At(i),
							parts[1],
							quotient_group.LeftCosetInLeftCosets.Read(additive).AsFact().At(m, power)))
				}))
			i, j, repeat := a.Obtain2As[Nat, Nat](
				"two of the powers up to q^n lie in one coset",
				"∃i j:num. "+
					"    i ≤ card(k) ^ n ∧ "+
					"    j ≤ card(k) ^ n ∧ "+
					"    i ≠ j ∧ "+
					"    left_coset(L.add, «tPow»(i), m) = left_coset(L.add, «tPow»(j), m)",
				By(
					counts[0],
					counts[1],
					cosetIn,
					At(
						num_segment.FiniteRangeRepeats,
						a.TermAs[Set[Set[A]]]("left_cosets(L.add, A₀, m)"),
						a.TermAs[Fun[Nat, Set[A]]]("λi:num. left_coset(L.add, «tPow»(i), m)"),
						a.TermAs[Nat]("card(k) ^ n"))))
			clauses := a.Conjuncts(
				repeat,
				"the first index is in range",
				"so is the second",
				"they differ",
				"the cosets agree")
			first := a.TermAs[A]("«tPow»(i)")
			second := a.TermAs[A]("«tPow»(j)")
			difference := a.Have(
				"so their difference lies in m",
				"-«tPow»(i) + «tPow»(j) ∈ m",
				By(
					clauses[3],
					parts[0],
					inChart.At(i),
					inChart.At(j),
					group.LeftCosetEqOn.Read(additive).AsFact().At(first, second, m)))
			a.Take(i)
			a.Take(j)
			a.Show(
				"the two powers are the ones sought",
				By(clauses[0], clauses[1], clauses[2], difference))
		}),
})}

// ChartMaximalBoundedColength — a chart has finitely many maximal ideals of
// bounded colength: each contains a difference of two distinct powers of t up
// to q^n, these are finitely many nonzero elements since t is transcendental,
// and each lies in finitely many ideals.
var ChartMaximalBoundedColength = chartMaximalBoundedColengthThm{family.Add(registry.ProofEntry{
	Name: "ChartMaximalBoundedColength",
	Key:  "prop_2407fa240a87d37",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀n:num.",
		Hypotheses: []string{"«scCurve»"},
		Conclusion: "finite({m:set(A) | maximal_ideal(«chart», m) ∧ «colength»(m) ≤ n})",
		Abbrev: Abbrev{
			{Name: "colength", Text: "λm:set(A). " +
				"    module_dim(restrict_ring(field_ring(L), k), " +
				"        quotient_module(restrict_module(regular_module(field_ring(L)), A₀), m))"},
			{Name: "tPow", Text: "λj:num. monoid_pow(L.mul, L.one, t, j)"},
			{Name: "indices", Text: "{i:num | i ≤ card(k) ^ n}"},
			{Name: "indexPairs", Text: "{p:prod(num, num) | " +
				"    fst(p) ≤ card(k) ^ n ∧ snd(p) ≤ card(k) ^ n ∧ fst(p) ≠ snd(p)}"},
			{Name: "idealsOf", Text: "λp:prod(num, num). " +
				"    {J:set(A) | ring_ideal(«chart», J) ∧ -«tPow»(fst(p)) + «tPow»(snd(p)) ∈ J}"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			n *Expr[Nat],
			curve Fact,
		) {
			chart := a.TermAs[RingOps[A]]("«chart»")
			indices := a.TermAs[Set[Nat]]("«indices»")
			indexPairs := a.TermAs[Set[Prod[Nat, Nat]]]("«indexPairs»")
			transcendental := a.Have(
				"t is transcendental over the constants",
				"subfield(L, k) ∧ t ∈ L.carrier ∧ ¬algebraic_over(L, k, t)",
				By(
					a.Unfolded(curve, SmoothFiniteFieldCurveDef),
					algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			distinct := a.Have(
				"so its powers are distinct",
				"∀i j:num. «tPow»(i) = «tPow»(j) ⇒ i = j",
				By(transcendental, algebraic_element.TranscendentalPowersIndependent.Read(L).AsFact().At(k, t)))
			chartRing := a.Have(
				"the chart is a ring",
				"comm_ring_on(«chart»)",
				By(curve, ChartCommRing.Read(L).At(k, A0, A1, A01, t)))
			datum := a.Conjuncts(
				GroupPremises(curve, ChartOverlap.Read(L).At(k, A0, A1, A01, t)),
				"the overlap is a subring of L",
				"it contains the chart",
				"the chart holds t",
				"t is nonzero",
				"the overlap holds the inverse of t",
				"they multiply to one",
				"the overlap is the chart with t inverted, inside itself",
				"and inside L",
				"the powers of t and of its inverse")
			powers := datum[8]
			differences := a.Have(
				"the difference of two distinct powers is a nonzero element of the chart",
				"∀i j:num. i ≠ j ⇒ -«tPow»(i) + «tPow»(j) ∈ A₀ ∧ -«tPow»(i) + «tPow»(j) ≠ L.zero",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					j := b.FixAs[Nat]("j")
					different := b.Assume()
					first := b.Have(
						"the first power lies in the chart",
						"«tPow»(i) ∈ A₀",
						By(powers.At(i)))
					second := b.Have(
						"so does the second",
						"«tPow»(j) ∈ A₀",
						By(powers.At(j)))
					member := b.Have(
						"so their difference does",
						"-«tPow»(i) + «tPow»(j) ∈ A₀",
						By(first, second, comm_ring.AddIn.Read(chartRing), comm_ring.NegIn.Read(chartRing)))
					nonzero := b.Have(
						"and it is nonzero, the powers being distinct",
						"-«tPow»(i) + «tPow»(j) ≠ L.zero",
						Derive(func(c *Argument) {
							vanishing := c.SupposeNot()
							zero := c.Have(
								"suppose it vanishes",
								"-«tPow»(i) + «tPow»(j) = L.zero",
								By(vanishing))
							equal := c.Have(
								"then the two powers agree",
								"«tPow»(i) = «tPow»(j)",
								ByArith(chartRing, zero, first, second))
							c.Show(
								"and the indices agree",
								By(different, equal, distinct.At(i, j)))
						}))
					b.Show(
						"so the difference is a nonzero element of the chart",
						By(member, nonzero))
				}))
			inside := a.Have(
				"the pairs lie in the square of the numbers up to q^n",
				"«indexPairs» ⊆ set_cross(«indices», «indices»)",
				BySets(set_product.InCrossProjections))
			finitePairs := a.Have(
				"so there are finitely many pairs",
				"finite(«indexPairs»)",
				By(
					inside,
					num_segment.FiniteBelow.At(a.TermAs[Nat]("card(k) ^ n")),
					finite_set.FiniteProduct.At(indices, indices),
					finite_set.FiniteSubset.At(
						indexPairs,
						a.TermAs[Set[Prod[Nat, Nat]]]("set_cross(«indices», «indices»)"))))
			eachFinite := a.Have(
				"each pair of distinct indices gives finitely many ideals",
				"∀p:prod(num, num). fst(p) ≠ snd(p) ⇒ finite(«idealsOf»(p))",
				Derive(func(b *Argument) {
					b.FixAs[Prod[Nat, Nat]]("p")
					different := b.Assume()
					indexFirst := b.TermAs[Nat]("fst(p)")
					indexSecond := b.TermAs[Nat]("snd(p)")
					difference := b.TermAs[A]("-«tPow»(fst(p)) + «tPow»(snd(p))")
					b.Show(
						"a nonzero element of the chart lies in finitely many ideals",
						By(
							curve,
							different,
							differences.At(indexFirst, indexSecond),
							ChartIdealsAboveElement.Read(L).At(k, A0, A1, A01, t, difference)))
				}))
			idealsMap := a.TermAs[Fun[Prod[Nat, Nat], Set[Set[A]]]]("«idealsOf»")
			Y, familyDef := a.LetAs[Set[Set[Set[A]]]]("Y", "image(«idealsOf», «indexPairs»)")
			finiteFamily := a.Have(
				"so the family of those sets of ideals is finite",
				"finite(Y)",
				By(familyDef, finitePairs, finite_set.FiniteImage.At(idealsMap, indexPairs)))
			members := a.Have(
				"and each member of the family is finite",
				"∀Z:set(set(A)). Z ∈ Y ⇒ finite(Z)",
				Derive(func(b *Argument) {
					b.FixAs[Set[Set[A]]]("Z")
					member := b.Assume()
					inImage := b.Have(
						"a member of the family is the set of ideals of some pair",
						"Z ∈ image(«idealsOf», «indexPairs»)",
						By(member, familyDef))
					p, chosen := b.UnpackAs[Prod[Nat, Nat]](
						b.Simplified(inImage, Fwd(set_basic.InImage)),
						"p")
					parts := b.Conjuncts(
						chosen,
						"Z is the set of ideals of p",
						"p is a pair of distinct indices")
					different := b.Have(
						"its indices differ",
						"fst(p) ≠ snd(p)",
						BySets(parts[1]))
					b.Show(
						"so Z is finite",
						By(parts[0], eachFinite.At(p), different))
				}))
			finiteUnion := a.Have(
				"so the union of the family is finite",
				"finite(⋃Y)",
				By(finiteFamily, members, finite_set.FiniteFiniteUnions.At(Y)))
			covered := a.Have(
				"each maximal ideal of bounded colength lies in the family's union",
				"∀m:set(A). maximal_ideal(«chart», m) ∧ «colength»(m) ≤ n ⇒ m ∈ ⋃Y",
				Derive(func(b *Argument) {
					m := b.FixAs[Set[A]]("m")
					given := b.Conjuncts(
						b.Assume(),
						"m is maximal",
						"its colength is at most n")
					ideal := b.Have(
						"m is an ideal of the chart",
						"ring_ideal(«chart», m)",
						By(given[0], ring_ideal.MaximalIdealIdeal.At(chart, m)))
					_, _, repeat := b.Obtain2As[Nat, Nat](
						"two powers up to q^n differ by an element of m",
						"∃i j:num. i ≤ card(k) ^ n ∧ j ≤ card(k) ^ n ∧ i ≠ j ∧ -«tPow»(i) + «tPow»(j) ∈ m",
						By(curve, given[0], given[1], ChartMaximalPowerRepeat.Read(L).At(k, A0, A1, A01, t, m, n)))
					clauses := b.Conjuncts(
						repeat,
						"the first index is in range",
						"so is the second",
						"they differ",
						"the difference lies in m")
					pair := b.TermAs[Prod[Nat, Nat]]("(i, j)")
					inPairs := b.Have(
						"(i, j) is one of the pairs",
						"(i, j) ∈ «indexPairs»",
						BySets(clauses[0], clauses[1], clauses[2], pairs.Fst, pairs.Snd))
					inFamily := b.Have(
						"so the ideals holding that difference are a member of the family",
						"{J:set(A) | ring_ideal(«chart», J) ∧ -«tPow»(i) + «tPow»(j) ∈ J} ∈ Y",
						By(inPairs, familyDef, set_image.FunInImage.At(idealsMap, indexPairs, pair), pairs.Fst, pairs.Snd))
					b.Do(Simp(Fwd(set_basic.InUnions)))
					b.Take(b.TermAs[Set[Set[A]]]("{J:set(A) | ring_ideal(«chart», J) ∧ -«tPow»(i) + «tPow»(j) ∈ J}"))
					b.Show(
						"and m is one of them",
						BySets(inFamily, ideal, clauses[3]))
				}))
			coveredSet := a.Have(
				"so the maximal ideals of bounded colength lie in that union",
				"{m:set(A) | maximal_ideal(«chart», m) ∧ «colength»(m) ≤ n} ⊆ ⋃Y",
				BySets(covered))
			a.Show(
				"a subset of a finite set is finite",
				By(
					finiteUnion,
					coveredSet,
					finite_set.FiniteSubset.At(
						a.TermAs[Set[Set[A]]]("{m:set(A) | maximal_ideal(«chart», m) ∧ «colength»(m) ≤ n}"),
						a.TermAs[Set[Set[A]]]("⋃Y"))))
		}),
})}

// ChartPointsBoundedColength — finitely many closed points are proper in a
// chart with bounded colength there: the first component is a maximal ideal of
// bounded colength, of which there are finitely many, and it determines the
// point.
var ChartPointsBoundedColength = chartPointsBoundedColengthThm{family.Add(registry.ProofEntry{
	Name: "ChartPointsBoundedColength",
	Key:  "prop_3ac53dec44f868ad",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀n:num.",
		Hypotheses: []string{"«scCurve»"},
		Conclusion: "finite(«points»)",
		Abbrev: Abbrev{
			{Name: "colength", Text: "λm:set(A). " +
				"    module_dim(restrict_ring(field_ring(L), k), " +
				"        quotient_module(restrict_module(regular_module(field_ring(L)), A₀), m))"},
			{Name: "points", Text: "{P:prod(set(A), set(A)) | " +
				"    «scPoint»(P) ∧ fst(P) ≠ A₀ ∧ «colength»(fst(P)) ≤ n}"},
			{Name: "firstOf", Text: "λP:prod(set(A), set(A)). fst(P)"},
			{Name: "ideals", Text: "{m:set(A) | maximal_ideal(«chart», m) ∧ «colength»(m) ≤ n}"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			n *Expr[Nat],
			curve Fact,
		) {
			first := a.TermAs[Fun[Prod[Set[A], Set[A]], Set[A]]]("«firstOf»")
			points := a.TermAs[Set[Prod[Set[A], Set[A]]]]("«points»")
			maximal := a.Have(
				"a closed point proper in the chart has a maximal first component",
				"∀P:prod(set(A), set(A)). «scPoint»(P) ∧ fst(P) ≠ A₀ ⇒ maximal_ideal(«chart», fst(P))",
				Derive(func(b *Argument) {
					b.FixAs[Prod[Set[A], Set[A]]]("P")
					given := b.Conjuncts(
						b.Assume(),
						"P is a closed point",
						"it is proper in the chart")
					opened := b.Unfolded(given[0], CurveClosedPointDef)
					b.Show(
						"this is the first clause of a closed point",
						By(Normalized, given[1], opened))
				}))
			injective := a.Have(
				"the first component determines such a point",
				"injective_on(«points», «firstOf»)",
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					x := b.FixAs[Prod[Set[A], Set[A]]]("x")
					y := b.FixAs[Prod[Set[A], Set[A]]]("y")
					members := b.Assume()
					given := b.Conjuncts(
						b.Have(
							"both are closed points, the first proper, over one ideal",
							"«scPoint»(x) ∧ fst(x) ≠ A₀ ∧ «scPoint»(y) ∧ fst(x) = fst(y)",
							BySets(members)),
						"x is a closed point",
						"x is proper in the chart",
						"y is a closed point",
						"they have one first component")
					base := b.TermAs[Set[A]]("fst(x)")
					unique := b.Have(
						"there is one point over that ideal",
						"∃!P:prod(set(A), set(A)). «scPoint»(P) ∧ fst(P) = fst(x)",
						By(curve, given[0], given[1], maximal, ChartMaximalClosedPoint.Read(L).At(k, A0, A1, A01, t, base)))
					_, center := b.UnpackAs[Prod[Set[A], Set[A]]](unique, "c")
					b.Show(
						"so x and y agree",
						By(Normalized, center.At(x), center.At(y), given[0], given[2], given[3]))
				}))
			inside := a.Have(
				"the first components are maximal ideals of bounded colength",
				"image(«firstOf», «points») ⊆ «ideals»",
				BySets(maximal))
			finiteIdeals := a.Have(
				"of which there are finitely many",
				"finite(«ideals»)",
				By(curve, ChartMaximalBoundedColength.Read(L).At(k, A0, A1, A01, t, n)))
			finiteImage := a.Have(
				"so the first components are finitely many",
				"finite(image(«firstOf», «points»))",
				By(
					finiteIdeals,
					inside,
					finite_set.FiniteSubset.At(
						a.TermAs[Set[Set[A]]]("image(«firstOf», «points»)"),
						a.TermAs[Set[Set[A]]]("«ideals»"))))
			a.Show(
				"and they determine the points",
				By(injective, finiteImage, finite_set.FiniteImageInjEq.At(first, points)))
		}),
})}

// ClosedPointDegreeInField — the degree of a closed point read in the ambient
// field: restricted rings and modules keep M's operations, so the quotient of
// the definition is the quotient of a chart of M.
var ClosedPointDegreeInField = closedPointDegreeInFieldThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointDegreeInField",
	Key:  "prop_43d80eec804cf0c3",
	Build: family.Theorem("∀M:field_ops(A). ∀K k A₀ A₁:set(A). ∀P:prod(set(A), set(A)). "+
		"    curve_closed_degree(«ambientRing», k, A₀, A₁, P) = "+
		"    module_dim(restrict_ring(field_ring(M), k), "+
		"        quotient_module(restrict_module(regular_module(field_ring(M)), point_chart(A₀, A₁, P)), "+
		"            point_ideal(A₀, P)))",
		func(a *Argument, M *Expr[FieldOps[A]], K, k, A0, A1 *Expr[Set[A]], P *Expr[Prod[Set[A], Set[A]]]) {
			a.Show(
				"both sides are one dimension of one quotient, the restrictions keeping M's operations",
				Simp(Fwd(ClosedPointDegreeDef)),
				Simp(
					Fwd(module_record.RestrictRingTwice),
					Fwd(module_record.RegularModuleDef),
					Fwd(module_record.RestrictRingDef),
					Fwd(module_record.RestrictModuleDef)),
				Refl())
		}),
})}

// ClosedPointResidue — a closed point has finite positive degree: it is a
// maximal ideal of a chart, the second chart when its first component is all
// of A₀, and that ideal has finite positive colength.
var ClosedPointResidue = closedPointResidueThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointResidue",
	Key:  "prop_46f97ddaf7d2576b",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{"«scCurve»", "«scPoint»(P)"},
		Conclusion: "0 < «scPointDegree»(P) ∧ finite_dimensional(«scalars», «residue»(P))",
		Abbrev: Abbrev{
			{Name: "scalars", Text: "restrict_ring(field_ring(L), k)"},
			{Name: "vectors", Text: "regular_module(field_ring(L))"},
			{Name: "residue", Text: "λP:prod(set(A), set(A)). " +
				"    quotient_module(restrict_module(«vectors», point_chart(A₀, A₁, P)), point_ideal(A₀, P))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			curve, point Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			inverse := a.TermAs[A]("L.inv(t)")
			second := a.TermAs[Set[A]]("snd(P)")
			first := a.TermAs[Set[A]]("fst(P)")
			degree := a.Have(
				"the degree is the dimension of the residue quotient",
				"«scPointDegree»(P) = module_dim(«scalars», «residue»(P))",
				By(ClosedPointDegreeDef.At(ring, k, A0, A1, P)))
			maximal := a.Have(
				"the point is a maximal ideal of its chart",
				"maximal_ideal(restrict_ring(field_ring(L), point_chart(A₀, A₁, P)), point_ideal(A₀, P))",
				By(point, ClosedPointMaximal.At(ring, A0, A1, A01, P)))
			otherCurve := a.Have(
				"the curve read from its other chart",
				"smooth_finite_curve(L, k, L.inv(t), A₁, A₀, A₀₁)",
				By(curve, SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t)))
			a.Cases(a.Term("fst(P) = A₀"))
			a.When(
				"the point lies in the chart A₁ alone",
				func(b *Argument, whole Fact) {
					conditions := b.Conjuncts(
						GroupPremises(whole, biaffine_rational_point.PointOffChartZero.At(A0, A1, P)),
						"its chart is A₁",
						"its ideal is the second component")
					inChart := b.Have(
						"the second component is maximal in A₁",
						"maximal_ideal(restrict_ring(field_ring(L), A₁), snd(P))",
						By(Normalized, conditions[0], conditions[1], maximal))
					colength := b.Have(
						"so it has finite positive colength",
						"finite_dimensional(«scalars», quotient_module(restrict_module(«vectors», A₁), snd(P))) ∧ "+
							"0 < module_dim(«scalars», quotient_module(restrict_module(«vectors», A₁), snd(P)))",
						By(otherCurve, inChart, ChartMaximalColength.Read(L).At(k, A1, A0, A01, inverse, second)))
					b.Show(
						"which is the degree and the residue quotient",
						By(degree, conditions[0], conditions[1], colength))
				})
			a.Otherwise(
				"the point is proper in the chart A₀",
				func(b *Argument, proper Fact) {
					conditions := b.Conjuncts(
						GroupPremises(proper, biaffine_rational_point.PointOnChartZero.At(A0, A1, P)),
						"its chart is A₀",
						"its ideal is the first component")
					inChart := b.Have(
						"the first component is maximal in A₀",
						"maximal_ideal(restrict_ring(field_ring(L), A₀), fst(P))",
						By(Normalized, conditions[0], conditions[1], maximal))
					colength := b.Have(
						"so it has finite positive colength",
						"finite_dimensional(«scalars», quotient_module(restrict_module(«vectors», A₀), fst(P))) ∧ "+
							"0 < module_dim(«scalars», quotient_module(restrict_module(«vectors», A₀), fst(P)))",
						By(curve, inChart, ChartMaximalColength.Read(L).At(k, A0, A1, A01, t, first)))
					b.Show(
						"which is the degree and the residue quotient",
						By(degree, conditions[0], conditions[1], colength))
				})
		}),
})}

// ClosedPointsBoundedDegree — a smooth curve over a finite field has finitely
// many closed points of bounded degree: a point proper in A₀ is counted there,
// and any other is proper in A₁, counted there through the swap.
var ClosedPointsBoundedDegree = closedPointsBoundedDegreeThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointsBoundedDegree",
	Key:  "prop_6f43b0e561f43dad",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀n:num.",
		Hypotheses: []string{"«scCurve»"},
		Conclusion: "finite({P:prod(set(A), set(A)) | «scPoint»(P) ∧ «scPointDegree»(P) ≤ n})",
		Abbrev: Abbrev{
			{Name: "scalars", Text: "restrict_ring(field_ring(L), k)"},
			{Name: "vectors", Text: "regular_module(field_ring(L))"},
			{Name: "residue", Text: "λP:prod(set(A), set(A)). " +
				"    quotient_module(restrict_module(«vectors», point_chart(A₀, A₁, P)), point_ideal(A₀, P))"},
			{Name: "swap", Text: "λQ:prod(set(A), set(A)). (snd(Q), fst(Q))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			n *Expr[Nat],
			curve Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			inverse := a.TermAs[A]("L.inv(t)")
			swap := a.TermAs[Fun[Prod[Set[A], Set[A]], Prod[Set[A], Set[A]]]]("«swap»")
			otherCurve := a.Have(
				"the curve read from its other chart",
				"smooth_finite_curve(L, k, L.inv(t), A₁, A₀, A₀₁)",
				By(curve, SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t)))
			U, firstDef := a.LetAs[Set[Prod[Set[A], Set[A]]]](
				"U",
				"{P:prod(set(A), set(A)) | "+
					"    «scPoint»(P) ∧ "+
					"    fst(P) ≠ A₀ ∧ "+
					"    module_dim(«scalars», quotient_module(restrict_module(«vectors», A₀), fst(P))) ≤ n}")
			V, secondDef := a.LetAs[Set[Prod[Set[A], Set[A]]]](
				"V",
				"{Q:prod(set(A), set(A)) | "+
					"    curve_closed_point(field_ring(L), A₁, A₀, A₀₁, Q) ∧ "+
					"    fst(Q) ≠ A₁ ∧ "+
					"    module_dim(«scalars», quotient_module(restrict_module(«vectors», A₁), fst(Q))) ≤ n}")
			finiteFirst := a.Have(
				"finitely many points are counted in A₀",
				"finite(U)",
				By(firstDef, curve, ChartPointsBoundedColength.Read(L).At(k, A0, A1, A01, t, n)))
			finiteSecond := a.Have(
				"and finitely many in A₁",
				"finite(V)",
				By(secondDef, otherCurve, ChartPointsBoundedColength.Read(L).At(k, A1, A0, A01, inverse, n)))
			cover := a.Have(
				"each point of bounded degree is counted in A₀, or in A₁ through the swap",
				"∀P:prod(set(A), set(A)). «scPoint»(P) ∧ «scPointDegree»(P) ≤ n ⇒ P ∈ U ∨ P ∈ image(«swap», V)",
				Derive(func(b *Argument) {
					P := b.FixAs[Prod[Set[A], Set[A]]]("P")
					given := b.Conjuncts(
						b.Assume(),
						"P is a closed point",
						"its degree is at most n")
					point, bounded := given[0], given[1]
					degree := b.Have(
						"the degree is the dimension of the residue quotient",
						"«scPointDegree»(P) = module_dim(«scalars», «residue»(P))",
						By(ClosedPointDegreeDef.At(ring, k, A0, A1, P)))
					notBoth := b.Have(
						"the two components are not both whole",
						"¬(fst(P) = A₀ ∧ snd(P) = A₁)",
						By(b.Unfolded(point, CurveClosedPointDef)))
					b.Cases(b.Term("fst(P) = A₀"))
					b.When(
						"the first component is whole, so the swapped point is counted in A₁",
						func(c *Argument, whole Fact) {
							swapped := c.TermAs[Prod[Set[A], Set[A]]]("(snd(P), fst(P))")
							second := c.TermAs[Set[A]]("snd(P)")
							first := c.TermAs[Set[A]]("fst(P)")
							bound := c.Have(
								"the degree is the colength of the second component in A₁",
								"module_dim(«scalars», quotient_module(restrict_module(«vectors», A₁), snd(P))) ≤ n",
								By(Normalized, whole, degree, bounded, biaffine_rational_point.PointOffChartZero.At(A0, A1, P)))
							otherPoint := c.Have(
								"the swapped point is a closed point of the other chart",
								"curve_closed_point(field_ring(L), A₁, A₀, A₀₁, (snd(P), fst(P)))",
								By(point, ClosedPointSwap))
							counted := c.Have(
								"so it is counted in A₁",
								"(snd(P), fst(P)) ∈ V",
								secondDef.Rw(),
								By(otherPoint, bound, notBoth, whole, pairs.Fst.At(second, first)))
							inImage := c.Have(
								"and P is its swap",
								"P ∈ image(«swap», V)",
								By(
									counted,
									set_image.FunInImage.At(swap, V, swapped),
									pairs.Fst.At(second, first),
									pairs.Snd.At(second, first),
									pairs.PairEta.At(P)))
							c.Show(
								"so P is counted through the swap",
								By(inImage))
						})
					b.Otherwise(
						"the first component is proper, so P is counted in A₀",
						func(c *Argument, proper Fact) {
							counted := c.Have(
								"its degree is the colength of the first component in A₀",
								"P ∈ U",
								firstDef.Rw(),
								By(
									Normalized,
									point,
									proper,
									degree,
									bounded,
									biaffine_rational_point.PointOnChartZero.At(A0, A1, P)))
							c.Show(
								"so P is counted in A₀",
								By(counted))
						})
				}))
			inside := a.Have(
				"so the points of bounded degree lie in the two counts",
				"{P:prod(set(A), set(A)) | «scPoint»(P) ∧ «scPointDegree»(P) ≤ n} ⊆ U ∪ image(«swap», V)",
				BySets(cover))
			swapImage := a.TermAs[Set[Prod[Set[A], Set[A]]]]("image(«swap», V)")
			a.Show(
				"and those are finite",
				By(
					finiteFirst,
					finiteSecond,
					inside,
					finite_set.FiniteImage.At(swap, V),
					finite_set.FiniteUnionImp.At(U, swapImage),
					finite_set.FiniteSubset.At(
						a.TermAs[Set[Prod[Set[A], Set[A]]]](
							"{P:prod(set(A), set(A)) | «scPoint»(P) ∧ «scPointDegree»(P) ≤ n}"),
						a.TermAs[Set[Prod[Set[A], Set[A]]]]("U ∪ image(«swap», V)"))))
		}),
})}

// ClosedPointsFiniteByDegree — a smooth curve over a finite field has closed
// points, each of finite positive degree, finitely many of bounded degree, and
// so finitely many effective divisors of each degree.
var ClosedPointsFiniteByDegree = closedPointsFiniteByDegreeThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointsFiniteByDegree",
	Key:  "prop_a5e457c46613ffc",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{"«scCurve»"},
		Conclusion: "(∃P:prod(set(A), set(A)). «scPoint»(P)) ∧ " +
			"(∀P:prod(set(A), set(A)). " +
			"    «scPoint»(P) ⇒ " +
			"    0 < «scPointDegree»(P) ∧ " +
			"    finite_dimensional(restrict_ring(field_ring(L), k), " +
			"        quotient_module(restrict_module(regular_module(field_ring(L)), point_chart(A₀, A₁, P)), " +
			"            point_ideal(A₀, P)))) ∧ " +
			"(∀n:num. " +
			"    finite({P:prod(set(A), set(A)) | «scPoint»(P) ∧ «scPointDegree»(P) ≤ n}) ∧ " +
			"    finite({D:prod(set(A), set(A)) → num | " +
			"            weighted_effective({P:prod(set(A), set(A)) | «scPoint»(P)}, «scPointDegree», D) ∧ " +
			"            weighted_degree(«scPointDegree», D) = n}))",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			chartRing := a.Have(
				"the chart is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), A₀))",
				By(curve, ChartCommRing.Read(L).At(k, A0, A1, A01, t)))
			proper := a.Have(
				"the zero ideal of the chart is proper",
				"ring_ideal(restrict_ring(field_ring(L), A₀), {L.zero}) ∧ L.one ∉ {L.zero}",
				BySets(ring_ideal.ZeroIdeal.Read(chartRing), field.OneNotZeroOn.Read(L)))
			m, above := a.ObtainAs[Set[A]](
				"so the chart has a maximal ideal",
				"∃m:set(A). maximal_ideal(restrict_ring(field_ring(L), A₀), m) ∧ {L.zero} ⊆ m",
				By(proper, ring_ideal.ExistsMaximalAbove.Read(chartRing).At(a.TermAs[Set[A]]("{L.zero}"))))
			maximal := a.Conjuncts(
				above,
				"m is maximal",
				"m contains zero")
			unique := a.Have(
				"which is the first component of a closed point",
				"∃!P:prod(set(A), set(A)). «scPoint»(P) ∧ fst(P) = m",
				By(curve, maximal[0], ChartMaximalClosedPoint.Read(L).At(k, A0, A1, A01, t, m)))
			c, center := a.UnpackAs[Prod[Set[A], Set[A]]](unique, "c")
			exists := a.Have(
				"so closed points exist",
				"∃P:prod(set(A), set(A)). «scPoint»(P)",
				Derive(func(b *Argument) {
					b.Take(c)
					b.Show(
						"the point over m is a closed point",
						By(center.At(c)))
				}))
			positive := a.Have(
				"each closed point has finite positive degree",
				Statement{
					Binders: "∀P:prod(set(A), set(A)).",
					Hypotheses: []string{
						"«scPoint»(P)",
					},
					Conclusion: "0 < «scPointDegree»(P) ∧ " +
						"finite_dimensional(restrict_ring(field_ring(L), k), " +
						"    quotient_module(restrict_module(regular_module(field_ring(L)), point_chart(A₀, A₁, P)), " +
						"        point_ideal(A₀, P)))",
				},
				Derive(func(b *Argument) {
					P := b.FixAs[Prod[Set[A], Set[A]]]("P")
					point := b.Assume()
					b.Show(
						"a closed point is a maximal ideal of a chart, of finite positive colength",
						By(curve, point, ClosedPointResidue.Read(L).At(k, A0, A1, A01, t, P)))
				}))
			bounded := a.Have(
				"finitely many closed points have bounded degree",
				"∀n:num. finite({P:prod(set(A), set(A)) | «scPoint»(P) ∧ «scPointDegree»(P) ≤ n})",
				a.ForEach(func(n *Expr[Nat]) Action {
					return By(curve, ClosedPointsBoundedDegree.Read(L).At(k, A0, A1, A01, t, n))
				}))
			points := a.TermAs[Set[Prod[Set[A], Set[A]]]]("{P:prod(set(A), set(A)) | «scPoint»(P)}")
			degree := a.TermAs[Fun[Prod[Set[A], Set[A]], Nat]]("«scPointDegree»")
			divisors := a.Have(
				"so the finite levels leave finitely many effective divisors of each degree",
				"∀n:num. "+
					"    finite({D:prod(set(A), set(A)) → num | "+
					"            weighted_effective({P:prod(set(A), set(A)) | «scPoint»(P)}, «scPointDegree», D) ∧ "+
					"            weighted_degree(«scPointDegree», D) = n})",
				a.ForEach(func(n *Expr[Nat]) Action {
					return By(bounded, weighted_divisors.WeightedDivisorsFinite.At(points, degree, n))
				}))
			a.Show(
				"so closed points exist, with finite positive degrees "+
					"and finitely many points and divisors by degree",
				By(exists, positive, bounded, divisors))
		}),
})}
