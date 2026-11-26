// pole_pairs.go — the multiples of t's divisor of poles: the pairs
// (A₀, tʲ·A₁), chart 0 kept and chart 1 allowed a pole of order j along the
// poles of t. Each is a lattice pair with ambient the overlap. Multiplying by
// t carries one into the next with the quotient A₀/t·A₀ on chart 0 alone, so
// χ grows by n = dim_k A₀/t·A₀ at each step and χ(A₀, tʲ·A₁) = j·n + 1 − g.
// From some j on H¹ vanishes, a free pair on the line without H¹ lying
// inside with the same ambient, so ℓ(A₀, tʲ·A₁) = j·n + 1 − g there.

package algebraic_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/laurent_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/iterate/int/int_sum"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_map"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_sequence"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line_free_pair"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PolePairLattice — for every j, (A₀, tʲ·A₁) is a lattice pair of the curve
// whose ambient is the overlap: tʲ·A₁ is an A₁-submodule of L as A₁ is, and
// each chart spans A₀₁ over itself, A₀ holding one and tʲ·A₁ the unit tʲ of
// A₀₁.
var PolePairLattice = polePairLatticeThm{family.Add(registry.ProofEntry{
	Name: "PolePairLattice",
	Key:  "prop_1c84498fd2b4ea1f",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀j:num.",
		Hypotheses: []string{"«wcDatum»"},
		Conclusion: "lattice_pair(«wcOverlap», A₀, A₁, «wcField», «polePair»(j)) ∧ " +
			"lattice_pair_ambient(«wcOverlap», «wcField», «polePair»(j)) = A₀₁",
		Abbrev: Abbrev{
			// tʲ · A₁, and the pair of j times the divisor of poles of t: chart 0 kept, chart 1 multiplied by tʲ.
			{Name: "poleChart", Text: "λi:num. image(L.mul(monoid_pow(L.mul, L.one, t, i)), A₁)"},
			{Name: "polePair", Text: "λi:num. (A₀, «poleChart»(i))"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		j *Expr[Nat],
		curve Fact,
	) {
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
		invT := a.TermAs[A]("L.inv(t)")
		power, inversePower :=
			a.TermAs[A]("monoid_pow(L.mul, L.one, t, j)"), a.TermAs[A]("monoid_pow(L.mul, L.one, L.inv(t), j)")
		scaled := a.TermAs[Set[A]]("«poleChart»(j)")
		datum := a.Simplified(GroupPremises(curve, CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
		structure := a.Simplified(GroupPremises(curve, CurveLatticeData.Read(L).At(k, A0, A1, A01, t)))
		overlapRing := a.Have(
			"the overlap is a commutative ring under L's operations",
			"comm_ring_on(«wcOverlap»)",
			By(datum, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(A01)))
		inOverlap := a.Have(
			"t and its inverse lie in the overlap",
			"t ∈ A₀₁ ∧ L.inv(t) ∈ A₀₁",
			BySets(datum))
		overlapPowers := comm_ring.MulMonoidOn.Read(overlapRing)
		unit := a.Have(
			"so do tʲ and inv(t)ʲ, whose product is one: tʲ is a unit of the overlap",
			"monoid_pow(L.mul, L.one, t, j) ∈ A₀₁ ∧ "+
				"monoid_pow(L.mul, L.one, L.inv(t), j) ∈ A₀₁ ∧ "+
				"monoid_pow(L.mul, L.one, t, j) * monoid_pow(L.mul, L.one, L.inv(t), j) = L.one",
			By(
				inOverlap,
				datum,
				At(comm_monoid.PowIn.Read(overlapPowers), t, j),
				At(comm_monoid.PowIn.Read(overlapPowers), invT, j),
				At(comm_monoid.PowInverseOn.Read(overlapPowers), t, invT, j)))
		powerInField := a.Have(
			"tʲ lies in L",
			"monoid_pow(L.mul, L.one, t, j) ∈ L.carrier",
			BySets(unit, structure))
		chartOne := a.Have(
			"tʲ · A₁ is an A₁-submodule of L, as A₁ is",
			"submodule(restrict_ring(«wcOverlap», A₁), «wcField», «poleChart»(j))",
			Simp(Fwd(module_record.RestrictRingTwice)),
			By(
				datum,
				powerInField,
				fractional_ideal.SubringSubmodule.Read(L).At(A1),
				At(fractional_ideal.ScaleSubmodule.Read(L), A1, A1, power)))
		scaledInOverlap := a.Have(
			"tʲ · A₁ lies in the overlap and holds tʲ = tʲ · one",
			"«poleChart»(j) ⊆ A₀₁ ∧ monoid_pow(L.mul, L.one, t, j) ∈ «poleChart»(j)",
			BySets(
				unit,
				datum,
				At(comm_ring.SubringMul, fieldRing, A01),
				comm_ring.SubringOne.At(fieldRing, A1),
				At(comm_monoid.RightIdentityOn.Read(overlapPowers), power)))
		spans := a.Have(
			"A₀ holds one and tʲ · A₁ the unit tʲ, so each spans the overlap over itself",
			"module_span(«wcOverlap», «wcField», A₀) = A₀₁ ∧ "+
				"module_span(«wcOverlap», «wcField», «poleChart»(j)) = A₀₁",
			By(
				datum,
				unit,
				scaledInOverlap,
				comm_ring.SubringOne.At(fieldRing, A0),
				fractional_ideal.SpanHoldingOne.Read(L).At(A01, A0),
				fractional_ideal.SpanHoldingUnit.Read(L).At(A01, scaled, power, inversePower)))
		a.Show(
			"so the two charts are a lattice pair over the overlap, and A₀ spans its ambient A₀₁",
			By(
				structure,
				chartOne,
				spans,
				lattice_pair.LatticePairDef,
				lattice_pair.LatticePairAmbientDef,
				pairs.Fst,
				pairs.Snd))
	}),
})}

// PolePairEuler — the pairs (A₀, tʲ·A₁) have finite cohomology and
// χ = j·n + 1 − g, n the dimension of A₀/t·A₀ over k. At j = 0 the pair is the
// structure pair. Multiplying (A₀, tʲ·A₁) by t, an isomorphism, gives
// (t·A₀, tʲ⁺¹·A₁) inside (A₀, tʲ⁺¹·A₁) with chart quotients A₀/t·A₀ and zero,
// and with the same ambient, t being a unit of the overlap; EulerAdditive
// adds n.
var PolePairEuler = polePairEulerThm{family.Add(registry.ProofEntry{
	Name: "PolePairEuler",
	Key:  "prop_3fd524dec2ef93cc",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀j:num.",
		Hypotheses: []string{"«wcDatum»"},
		Conclusion: "lattice_pair_finite(«wcOverlap», k, «wcField», «polePair»(j)) ∧ " +
			"«wdEuler»(«polePair»(j)) = &j * &«zeroDegree» + &1 - «wdGenus»",
		Abbrev: Abbrev{
			{Name: "poleChart", Text: "λi:num. image(L.mul(monoid_pow(L.mul, L.one, t, i)), A₁)"},
			{Name: "polePair", Text: "λi:num. (A₀, «poleChart»(i))"},
			// n, the dimension over k of A₀ modulo t·A₀: the degree of the divisor of zeros of t.
			{Name: "zeroDegree", Text: "module_dim(«wcRing»(k), " +
				"    quotient_module(«wcVectors»(A₀), image(L.mul(t), A₀)))"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		curve Fact,
	) {
		overlap, scalars := a.TermAs[RingOps[A]]("«wcOverlap»"), a.TermAs[RingOps[A]]("«wdScalars»")
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
		vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
		invT := a.TermAs[A]("L.inv(t)")
		inv := a.TermAs[Fun[A, A]]("L.inv")
		multiplesOfT := a.TermAs[Set[A]]("image(L.mul(t), A₀)")
		datum := a.Simplified(GroupPremises(curve, CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
		structure := a.Simplified(GroupPremises(curve, CurveLatticeData.Read(L).At(k, A0, A1, A01, t)))
		tm := a.MemberOf[on.L](t, a.Have(
			"t lies in L",
			"t ∈ L.carrier",
			By(datum)))
		powersL := comm_ring.MulMonoidOn.Read(field.RingOn.Read(L))
		subfieldK := a.Have(
			"k, a subfield of L, is a field under the overlap's operations",
			"ring_subfield(«wcOverlap», L.inv, k)",
			By(datum, field.SubfieldRingSubfield.Read(L).At(k, A01)))
		scalarField := a.Have(
			"and under the operations of k itself",
			"ring_subfield(«wdScalars», L.inv, k)",
			By(subfieldK, field.RingSubfieldRestrict.At(overlap, k, inv, k)))
		kInCharts := a.Have(
			"k lies in both charts and in the overlap, and inv(t) lies in the overlap",
			"k ⊆ A₀ ∧ k ⊆ A₁ ∧ k ⊆ A₀₁ ∧ L.inv(t) ∈ A₀₁",
			BySets(datum))
		kSubring := a.Have(
			"so k is a subring of the overlap",
			"subring(«wcOverlap», k)",
			By(
				datum,
				kInCharts,
				field.SubfieldSubring.Read(L).At(k),
				comm_ring.SubringRestrict.At(fieldRing, k, A01)))
		multiples := a.Have(
			"t · A₀ lies in A₀ and in the overlap, and holds t = t · one",
			"image(L.mul(t), A₀) ⊆ A₀ ∧ image(L.mul(t), A₀) ⊆ A₀₁ ∧ t ∈ image(L.mul(t), A₀)",
			BySets(
				datum,
				At(comm_ring.SubringMul, fieldRing, A0),
				comm_ring.SubringOne.At(fieldRing, A0),
				At(comm_monoid.RightIdentityOn.Read(powersL), t)))
		zeros := a.Have(
			"A₀/t · A₀ is finite-dimensional over k, of dimension n",
			"finite_dimensional(«wdScalars», quotient_module(«wcVectors»(A₀), image(L.mul(t), A₀))) ∧ "+
				"module_dim(«wdScalars», quotient_module(«wcVectors»(A₀), image(L.mul(t), A₀))) = «zeroDegree»",
			Simp(Fwd(module_record.RestrictRingTwice)),
			By(curve, datum, PrincipalColengthFinite.Read(L).At(k, A0, A1, A01, t)))

		a.Induct("j")
		a.Base(
			"at j = 0 the pair is the structure pair, whose Euler characteristic is 1 − g",
			func(b *Argument) {
				structurePair := b.Have(
					"t⁰ · A₁ = A₁, so the pair is (A₀, A₁)",
					"«polePair»(0) = (A₀, A₁)",
					By(
						datum,
						comm_monoid.MonoidPowDef,
						comm_ring.SubringSubset.At(fieldRing, A1),
						fractional_ideal.ScaleOne.Read(L).At(A1)))
				b.Show(
					"the structure pair has finite cohomology and χ(O) = 1 − g",
					structurePair.Rw(),
					ByArith(
						curve,
						StructureFinite.Read(L).At(k, A0, A1, A01, t),
						StructureEuler.Read(L).At(k, A0, A1, A01, t)))
			})
		a.Step(
			"multiplying (A₀, tʲ·A₁) by t lands in (A₀, tʲ⁺¹·A₁) "+
				"with quotient A₀/t·A₀ on chart 0 and nothing else",
			func(b *Argument, previous Fact) {
				j, next := b.TermAs[Nat]("j"), b.TermAs[Nat]("suc(j)")
				pair, nextPair :=
					b.TermAs[Prod[Set[A], Set[A]]]("«polePair»(j)"),
					b.TermAs[Prod[Set[A], Set[A]]]("«polePair»(suc(j))")
				timesT := b.TermAs[Prod[Set[A], Set[A]]]("lattice_pair_scale(t, «polePair»(j))")
				inside := b.TermAs[Prod[Set[A], Set[A]]]("(image(L.mul(t), A₀), «poleChart»(suc(j)))")
				nextChart := b.TermAs[Set[A]]("«poleChart»(suc(j))")
				lattices := b.Have(
					"(A₀, tʲ·A₁) and (A₀, tʲ⁺¹·A₁) are lattice pairs, the second with ambient A₀₁",
					"lattice_pair(«wcOverlap», A₀, A₁, «wcField», «polePair»(j)) ∧ "+
						"lattice_pair(«wcOverlap», A₀, A₁, «wcField», «polePair»(suc(j))) ∧ "+
						"lattice_pair_ambient(«wcOverlap», «wcField», «polePair»(suc(j))) = A₀₁",
					By(
						curve,
						At(Read(PolePairLattice, L), k, A0, A1, A01, t, j),
						At(Read(PolePairLattice, L), k, A0, A1, A01, t, next)))
				chartsInField := b.Have(
					"the charts of (A₀, tʲ·A₁) lie in L",
					"fst(«polePair»(j)) ⊆ L.carrier ∧ snd(«polePair»(j)) ⊆ L.carrier",
					By(lattices, invertible_lattice_pair.LatticePairChartsInField.Read(L).At(A0, A1, A01, pair)))
				powerJ := comm_monoid.PowIn.Read(powersL).At(tm, j)
				product := b.Have(
					"t · (A₀, tʲ·A₁) is (t·A₀, tʲ⁺¹·A₁)",
					"lattice_pair_scale(t, «polePair»(j)) = (image(L.mul(t), A₀), «poleChart»(suc(j)))",
					Simp(
						Fwd(invertible_lattice_pair.LatticePairScaleDef),
						Fwd(pairs.Fst),
						Fwd(pairs.Snd),
						Fwd(comm_monoid.MonoidPowDef)),
					By(
						datum,
						comm_ring.SubringSubset.At(fieldRing, A1),
						fractional_ideal.ScaleScale.Read(L).At(A1, powerJ, tm)))
				isomorphic := b.Have(
					"multiplication by t, an isomorphism onto t · (A₀, tʲ·A₁), keeps finite cohomology and χ",
					"lattice_pair(«wcOverlap», A₀, A₁, «wcField», lattice_pair_scale(t, «polePair»(j))) ∧ "+
						"lattice_pair_finite(«wcOverlap», k, «wcField», lattice_pair_scale(t, «polePair»(j))) ∧ "+
						"«wdEuler»(lattice_pair_scale(t, «polePair»(j))) = «wdEuler»(«polePair»(j))",
					By(
						datum,
						structure,
						lattices,
						subfieldK,
						kInCharts,
						previous,
						chartsInField,
						invertible_lattice_pair.ScaleIsLattice.Read(L).At(A0, A1, A01, t, tm, pair),
						invertible_lattice_pair.ScaleIsomorphism.Read(L).At(A0, A1, A01, t, tm, pair),
						lattice_pair_map.IsomorphismSameEuler.At(
							overlap,
							A0,
							A1,
							t,
							invT,
							k,
							inv,
							vectors,
							vectors,
							pair,
							timesT,
							b.TermAs[Fun[A, A]](
								"λx:A. COND(x ∈ lattice_pair_ambient(«wcOverlap», «wcField», «polePair»(j)), t * x, L.zero)"))))
				subpair := b.Simplified(isomorphic, Fwd(product))
				subpairAmbient := b.Have(
					"(t·A₀, tʲ⁺¹·A₁) has ambient A₀₁, t · A₀ holding the unit t of the overlap",
					"lattice_pair_ambient(«wcOverlap», «wcField», (image(L.mul(t), A₀), «poleChart»(suc(j)))) = A₀₁",
					By(
						datum,
						multiples,
						kInCharts,
						lattice_pair.LatticePairAmbientDef,
						pairs.Fst,
						fractional_ideal.SpanHoldingUnit.Read(L).At(A01, multiplesOfT, t, invT)))
				overK := b.Conjuncts(
					b.Have(
						"over k, L is a vector space and tʲ⁺¹ · A₁ and the "+
							"overlap, the ambient of (A₀, tʲ⁺¹·A₁), are subspaces",
						"module_on(«wdScalars», «wcField») ∧ "+
							"submodule(«wdScalars», «wcField», «poleChart»(suc(j))) ∧ "+
							"submodule(«wdScalars», «wcField», A₀₁)",
						By(
							datum,
							kSubring,
							kInCharts,
							lattices,
							pairs.Snd,
							lattice_pair.PairOverSubring.At(overlap, A0, A1, t, invT, k, vectors, nextPair))),
					"L is a vector space over k",
					"tʲ⁺¹ · A₁ is a k-subspace of L",
					"and so is the overlap")
				unchanged := b.Have(
					"chart 1 and the ambient A₀₁ do not change, so their quotients are zero",
					"finite_dimensional(«wdScalars», "+
						"    quotient_module(«wcVectors»(«poleChart»(suc(j))), «poleChart»(suc(j)))) ∧ "+
						"module_dim(«wdScalars», "+
						"    quotient_module(«wcVectors»(«poleChart»(suc(j))), «poleChart»(suc(j)))) = "+
						"0 ∧ "+
						"module_dim(«wdScalars», quotient_module(«wcVectors»(A₀₁), A₀₁)) = 0",
					By(
						overK[0],
						overK[1],
						overK[2],
						scalarField,
						module_record.RestrictRingDef.At(overlap, k),
						set_order.SubsetRefl.At(nextChart),
						set_order.SubsetRefl.At(A01),
						At(module_dimension.QuotientDimZeroIff, scalars, vectors, inv, nextChart, nextChart),
						At(module_dimension.QuotientDimZeroIff, scalars, vectors, inv, A01, A01)))
				growth := b.Have(
					"so (A₀, tʲ⁺¹·A₁) has finite cohomology and its χ exceeds "+
						"that of (t·A₀, tʲ⁺¹·A₁) by the three quotient dimensions",
					"lattice_pair_finite(«wcOverlap», k, «wcField», «polePair»(suc(j))) ∧ "+
						"«wdEuler»(«polePair»(suc(j))) - «wdEuler»((image(L.mul(t), A₀), «poleChart»(suc(j)))) = "+
						"&module_dim(«wdScalars», quotient_module(«wcVectors»(A₀), image(L.mul(t), A₀))) + "+
						"&module_dim(«wdScalars», "+
						"    quotient_module(«wcVectors»(«poleChart»(suc(j))), «poleChart»(suc(j)))) - "+
						"&module_dim(«wdScalars», quotient_module(«wcVectors»(A₀₁), A₀₁))",
					By(
						datum,
						multiples,
						lattices,
						subpair,
						subpairAmbient,
						zeros,
						unchanged,
						subfieldK,
						kInCharts,
						pairs.Fst,
						pairs.Snd,
						set_order.SubsetRefl.At(nextChart),
						lattice_pair_sequence.EulerAdditive.At(
							overlap, A0, A1, t, invT, k, inv, vectors, nextPair, inside)))
				b.Show(
					"χ(A₀, tʲ⁺¹·A₁) = χ(A₀, tʲ·A₁) + n = (j + 1)·n + 1 − g",
					Simp(Fwd(int_embed.OfNumSuc)),
					ByArith(growth, unchanged, subpair, previous, zeros))
			})
	}),
})}

// PolePairH1Vanishes — from some j on, H¹(A₀, tʲ·A₁) = 0. In a finite basis E
// of A₀ over k[t], A₁ holds the k[1/t]-span of the inv(t)ᴺ · e for one N
// (InvertibleSandwichChart). For j = N + i, tʲ · A₁ then holds the k[1/t]-span
// of the tⁱ · e, so the free pair O(i)^E on the line lies inside (A₀, tʲ·A₁),
// with chart 0 and the ambient in common. It has no H¹ (FreeLinePairH1Dim), and
// H¹(A₀, tʲ·A₁) is a quotient of its H¹.
var PolePairH1Vanishes = polePairH1VanishesThm{family.Add(registry.ProofEntry{
	Name: "PolePairH1Vanishes",
	Key:  "prop_3456b93d847a1bb9",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{"«wcDatum»"},
		Conclusion: "∃N:num. ∀j:num. N ≤ j ⇒ «wdH1Dim»(«polePair»(j)) = 0",
		Abbrev: Abbrev{
			{Name: "poleChart", Text: "λi:num. image(L.mul(monoid_pow(L.mul, L.one, t, i)), A₁)"},
			{Name: "polePair", Text: "λi:num. (A₀, «poleChart»(i))"},
			// The free pair O(i)^E on the line along the basis E: chart 0 the k[t]-span of E, chart 1 the k[1/t]-span of the tⁱ · e.
			{Name: "freePair", Text: "projective_line_free_pair(L, k, t, E, λe:A. &i)"},
			{Name: "lowerSet", Text: "{L.mul(monoid_pow(L.mul, L.one, L.inv(t), N), e) | e:A | e ∈ E}"},
			{Name: "upperSet", Text: "{L.mul(monoid_pow(L.mul, L.one, t, i), e) | e:A | e ∈ E}"},
			{Name: "freeChartSum", Text: "set_mul(L.add, fst(«freePair»), snd(«freePair»))"},
			{Name: "chartSum", Text: "set_mul(L.add, A₀, «poleChart»(N + i))"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		curve Fact,
	) {
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
		overlap := a.TermAs[RingOps[A]]("«wcOverlap»")
		polynomialOps, inverseOps :=
			a.TermAs[RingOps[A]]("«wcRing»(«wcPolynomials»)"),
			a.TermAs[RingOps[A]]("«wcRing»(«wcInversePolynomials»)")
		chartRing := a.TermAs[RingOps[A]]("«wcRing»(A₀)")
		vectors, chartVectors :=
			a.TermAs[module_record.ModuleOps[A, A]]("«wcField»"),
			a.TermAs[module_record.ModuleOps[A, A]]("«wcVectors»(A₀)")
		fieldCarrier := a.TermAs[Set[A]]("L.carrier")
		invT := a.TermAs[A]("L.inv(t)")
		inv := a.TermAs[Fun[A, A]]("L.inv")
		datum := a.Simplified(GroupPremises(curve, CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
		structure := a.Simplified(GroupPremises(curve, CurveLatticeData.Read(L).At(k, A0, A1, A01, t)))
		tm := a.MemberOf[on.L](t, a.Have(
			"t lies in L",
			"t ∈ L.carrier",
			By(datum)))
		ringL := field.RingOn.Read(L)
		powersL := comm_ring.MulMonoidOn.Read(ringL)
		overLaurent := a.Have(
			"L is a module over k[t, 1/t]",
			"module_on(«wcRing»(«wcLaurent»), «wcField»)",
			By(datum))
		kInCharts := a.Have(
			"k lies in both charts and in the overlap",
			"k ⊆ A₀ ∧ k ⊆ A₁ ∧ k ⊆ A₀₁",
			BySets(datum))
		kSubring := a.Have(
			"so k is a subring of the overlap",
			"subring(«wcOverlap», k)",
			By(
				datum,
				kInCharts,
				field.SubfieldSubring.Read(L).At(k),
				comm_ring.SubringRestrict.At(fieldRing, k, A01)))

		E, basisE := a.UnpackAs[Set[A]](
			a.Have(
				"A₀ has a finite basis E over k[t]",
				"∃E:set(A). finite(E) ∧ «wcBasisOfChart»(E)",
				By(datum)),
			"E")
		finiteBasis := a.Conjuncts(
			basisE,
			"E is finite",
			"E is a basis of A₀ over k[t]")
		basis := a.Have(
			"E is independent in A₀ and spans it over k[t]",
			"module_independent(«wcRing»(«wcPolynomials»), «wcVectors»(A₀), E) ∧ "+
				"module_span(«wcRing»(«wcPolynomials»), «wcVectors»(A₀), E) = A₀",
			By(finiteBasis[1], linear_independence.ModuleBasisDef.At(polynomialOps, chartVectors, E)))
		basisInField := a.Have(
			"E lies in A₀ and in L",
			"E ⊆ A₀ ∧ E ⊆ L.carrier",
			By(
				basis,
				datum,
				comm_ring.SubringSubset.At(fieldRing, A0),
				linear_independence.IndependentInCarrier.At(polynomialOps, chartVectors, E),
				set_order.SubsetTrans.At(E, A0, fieldCarrier)))
		chartSubmodule := a.Have(
			"A₀ is a k[t]-submodule of L",
			"submodule(«wcRing»(«wcPolynomials»), «wcField», A₀)",
			By(
				datum,
				fractional_ideal.SubringSubmodule.Read(L).At(A0),
				submodule.SubmoduleRestrictScalars.At(chartRing, vectors, A0, polynomialOps)))
		spanned := a.Have(
			"so E spans A₀ over k[t] inside L",
			"module_span(«wcRing»(«wcPolynomials»), «wcField», E) = A₀",
			By(
				datum,
				basisInField,
				basis,
				chartSubmodule,
				linear_independence.SpanRestrict.At(polynomialOps, vectors, A0, E)))
		independent := a.Have(
			"and E is independent over k[t] in L",
			"module_independent(«wcRing»(«wcPolynomials»), «wcField», E)",
			By(
				basis,
				datum,
				comm_ring.SubringSubset.At(fieldRing, A0),
				module_record.RestrictModuleDef.At(vectors, A0),
				linear_independence.IndependentRestrict.At(polynomialOps, vectors, A0, E)))
		sandwich := a.Conjuncts(
			a.Have(
				"in E the ambient of the structure pair is the k[t, 1/t]-span "+
					"of E, and A₁ holds the k[1/t]-span of the inv(t)ᴺ · e for some N",
				"lattice_pair_ambient(«wcOverlap», «wcField», (A₀, A₁)) = "+
					"module_span(«wcRing»(«wcLaurent»), «wcField», E) ∧ "+
					"(∃N:num. "+
					"    module_span(«wcRing»(«wcInversePolynomials»), "+
					"        «wcField», "+
					"        {L.mul(monoid_pow(L.mul, L.one, L.inv(t), N), e) | e:A | e ∈ E}) ⊆ "+
					"    A₁)",
				By(
					curve,
					structure,
					finiteBasis[0],
					finiteBasis[1],
					pairs.Fst,
					pairs.Snd,
					InvertibleSandwichChart.Read(L).At(k, A0, A1, A01, t, a.TermAs[_LatticePair]("(A₀, A₁)"), E))),
			"the ambient of the structure pair is the k[t, 1/t]-span of E",
			"for some N, A₁ holds the k[1/t]-span of the inv(t)ᴺ · e")
		N, lower := a.UnpackAs[Nat](sandwich[1], "N")

		a.Take(N)
		j := a.FixAs[Nat]("j")
		large := a.Assume()
		i, shift := a.ObtainAs[Nat](
			"so j = N + i for some i",
			"∃i:num. j = N + i",
			By(large, nat_order.LessEqExists.At(j, N)),
			Named("i"))
		a.Do(shift.Rw())
		pair := a.TermAs[_LatticePair]("«polePair»(N + i)")
		poleChart := a.TermAs[Set[A]]("«poleChart»(N + i)")
		lattice := a.Conjuncts(
			a.Have(
				"(A₀, tᴺ⁺ⁱ·A₁) is a lattice pair with ambient A₀₁",
				"lattice_pair(«wcOverlap», A₀, A₁, «wcField», «polePair»(N + i)) ∧ "+
					"lattice_pair_ambient(«wcOverlap», «wcField», «polePair»(N + i)) = A₀₁",
				By(curve, At(Read(PolePairLattice, L), k, A0, A1, A01, t, a.TermAs[Nat]("N + i")))),
			"(A₀, tᴺ⁺ⁱ·A₁) is a lattice pair",
			"its ambient is A₀₁")
		chartOne := a.Have(
			"its chart 1, an A₁-submodule of L, is a k[1/t]-submodule",
			"submodule(«wcRing»(«wcInversePolynomials»), «wcField», «poleChart»(N + i))",
			By(
				datum,
				lattice[0],
				lattice_pair.LatticePairDef,
				pairs.Snd,
				submodule.SubmoduleRestrictScalars.At(
					a.TermAs[RingOps[A]]("restrict_ring(«wcOverlap», A₁)"), vectors, poleChart, inverseOps)))
		invTm := field.InvIn.Read(L).At(tm)
		lowering := a.TermAs[Fun[A, A]]("L.mul(monoid_pow(L.mul, L.one, L.inv(t), N))")
		powerSplit := a.Have(
			"tᴺ⁺ⁱ = tᴺ · tⁱ",
			"monoid_pow(L.mul, L.one, t, N + i) = "+
				"monoid_pow(L.mul, L.one, t, N) * monoid_pow(L.mul, L.one, t, i)",
			By(comm_monoid.PowAddOn.Read(powersL).At(tm, N, i)))
		powerUnit := a.Have(
			"tᴺ · inv(t)ᴺ = one, as t · inv(t) = one",
			"monoid_pow(L.mul, L.one, t, N) * monoid_pow(L.mul, L.one, L.inv(t), N) = L.one",
			By(datum, comm_monoid.PowInverseOn.Read(powersL).At(tm, invTm, N)))
		generators := a.Have(
			"each tⁱ · e lies in tᴺ⁺ⁱ · A₁, being tᴺ⁺ⁱ times inv(t)ᴺ · e, a member of A₁",
			"«upperSet» ⊆ «poleChart»(N + i)",
			Simp(Fwd(set_image.SimpleImage), Fwd(set_image.ImageSubsetIff)),
			Derive(func(b *Argument) {
				e := b.FixAs[A]("e")
				inE := b.Assume()
				em := b.MemberOf[on.L](e, b.Have(
					"e lies in L",
					"e ∈ L.carrier",
					BySets(inE, basisInField)))
				lowered := b.Have(
					"inv(t)ᴺ · e lies in A₁",
					"monoid_pow(L.mul, L.one, L.inv(t), N) * e ∈ A₁",
					BySets(
						inE,
						lower,
						submodule.SubsetSpan.At(inverseOps, vectors, b.TermAs[Set[A]]("«lowerSet»")),
						set_image.FunInImage.At(lowering, E, e)))
				identity := b.Have(
					"tⁱ · e = tᴺ⁺ⁱ · (inv(t)ᴺ · e), since tᴺ⁺ⁱ = tᴺ · tⁱ and tᴺ · inv(t)ᴺ = one",
					"monoid_pow(L.mul, L.one, t, i) * e = "+
						"monoid_pow(L.mul, L.one, t, N + i) * (monoid_pow(L.mul, L.one, L.inv(t), N) * e)",
					ByArith(
						ringL,
						em,
						comm_monoid.PowIn.Read(powersL).At(tm, i),
						comm_monoid.PowIn.Read(powersL).At(tm, N),
						comm_monoid.PowIn.Read(powersL).At(invTm, N),
						Scaled(b.TermAs[A]("monoid_pow(L.mul, L.one, L.inv(t), N) * e"), powerSplit),
						Scaled(b.TermAs[A]("monoid_pow(L.mul, L.one, t, i) * e"), powerUnit)))
				b.Show(
					"so tⁱ · e is the image of a member of A₁",
					By(
						identity,
						lowered,
						set_image.FunInImage.At(
							b.TermAs[Fun[A, A]]("L.mul(monoid_pow(L.mul, L.one, t, N + i))"),
							A1,
							b.TermAs[A]("monoid_pow(L.mul, L.one, L.inv(t), N) * e"))))
			}))
		upperSet := a.TermAs[Set[A]]("«upperSet»")
		upperChart := a.Have(
			"so tᴺ⁺ⁱ · A₁ holds the k[1/t]-span of the tⁱ · e",
			"module_span(«wcRing»(«wcInversePolynomials»), «wcField», «upperSet») ⊆ «poleChart»(N + i)",
			By(chartOne, generators, submodule.SpanLeast.At(inverseOps, vectors, upperSet, poleChart)))

		free := a.TermAs[_LatticePair]("«freePair»")
		twist := a.TermAs[Fun[A, Int]]("λe:A. &i")
		freeCharts := a.Conjuncts(
			a.Have(
				"O(i)^E has chart 0 the k[t]-span of E and chart 1 the k[1/t]-span of the tⁱ · e",
				"fst(«freePair») = module_span(«wcRing»(«wcPolynomials»), «wcField», E) ∧ "+
					"snd(«freePair») = module_span(«wcRing»(«wcInversePolynomials»), «wcField», «upperSet»)",
				Simp(
					Fwd(projective_line_free_pair.ProjectiveLineFreePairDef),
					Fwd(pairs.Fst),
					Fwd(pairs.Snd),
					Fwd(laurent_polynomial.LaurentMonomialOfNum)),
				Basic()),
			"chart 0 of O(i)^E",
			"chart 1 of O(i)^E")
		freeLattice := a.Have(
			"O(i)^E is a lattice pair on the line",
			"lattice_pair(«wcRing»(«wcLaurent»), "+
				"    «wcPolynomials», "+
				"    «wcInversePolynomials», "+
				"    «wcField», "+
				"    «freePair»)",
			By(
				datum,
				basisInField,
				projective_line_free_pair.FreeLinePairIsLattice.Read(L).At(k, tm, E, twist)))
		freeH1 := a.Conjuncts(
			a.Have(
				"H¹(O(i)^E) is finite-dimensional, its dimension the sum over E of max(−i − 1, 0)",
				"finite_dimensional(restrict_ring(«wcRing»(«wcLaurent»), k), "+
					"    lattice_pair_h1(«wcRing»(«wcLaurent»), «wcField», «freePair»)) ∧ "+
					"int_of_num(lattice_pair_h1_dim(«wcRing»(«wcLaurent»), k, «wcField», «freePair»)) = "+
					"int_sum(E, λe:A. int_max(-&i - &1, &0))",
				By(
					datum,
					finiteBasis[0],
					independent,
					projective_line_free_pair.FreeLinePairH1Dim.Read(L).At(k, tm, E, twist))),
			"H¹(O(i)^E) is finite-dimensional",
			"its dimension is the sum over E of max(−i − 1, 0)")
		termZero := a.Have(
			"each term max(−i − 1, 0) is zero",
			"int_max(-&i - &1, &0) = &0",
			ByArith())
		sumZero := a.Have(
			"so the sum is zero",
			"int_sum(E, λe:A. int_max(-&i - &1, &0)) = &0",
			Unfold(int_sum.IntSumDef),
			By(termZero, monoidal.EqNeutral, int_real_lift.MonoidalAdd, int_real_lift.NeutralAdd))
		freeDim := a.TermAs[Nat]("lattice_pair_h1_dim(«wcRing»(«wcLaurent»), k, «wcField», «freePair»)")
		noFreeH1 := a.Have(
			"and O(i)^E has no H¹",
			"lattice_pair_h1_dim(«wcRing»(«wcLaurent»), k, «wcField», «freePair») = 0",
			ByArith(freeH1[1], sumZero, int_embed.OfNumEq.At(freeDim, a.TermAs[Nat]("0"))))

		ringsAgree := a.Have(
			"read on k, the line's ring and the overlap's are both the field's ring on k",
			"restrict_ring(«wcRing»(«wcLaurent»), k) = «wdScalars»",
			Unfold(module_record.RestrictRingDef))
		overK := a.Conjuncts(
			a.Have(
				"over k, L is a vector space and the chart sum of (A₀, tᴺ⁺ⁱ·A₁) and the overlap are subspaces",
				"module_on(«wdScalars», «wcField») ∧ "+
					"submodule(«wdScalars», «wcField», «chartSum») ∧ "+
					"submodule(«wdScalars», «wcField», A₀₁)",
				By(
					datum,
					kSubring,
					kInCharts,
					lattice[0],
					lattice[1],
					pairs.Fst,
					pairs.Snd,
					lattice_pair.PairOverSubring.At(overlap, A0, A1, t, invT, k, vectors, pair))),
			"L is a vector space over k",
			"the chart sum of (A₀, tᴺ⁺ⁱ·A₁) is a k-subspace",
			"so is the overlap")
		freeSum := a.Have(
			"the chart sum of O(i)^E is a k-subspace of L",
			"submodule(«wdScalars», «wcField», «freeChartSum»)",
			ringsAgree.RwRev(),
			By(datum, freeLattice, projective_line.LineH1Module.Read(L).At(k, tm, vectors, free)))
		freeInside := a.Have(
			"O(i)^E lies inside (A₀, tᴺ⁺ⁱ·A₁) chart by chart, the two sharing chart 0",
			"fst(«freePair») ⊆ A₀ ∧ snd(«freePair») ⊆ «poleChart»(N + i)",
			freeCharts[0].Rw(),
			freeCharts[1].Rw(),
			spanned.Rw(),
			By(upperChart, set_order.SubsetRefl.At(A0)))
		sumsInside := a.Have(
			"so its chart sum lies in that of (A₀, tᴺ⁺ⁱ·A₁)",
			"«freeChartSum» ⊆ «chartSum»",
			By(
				freeInside,
				pairs.Fst,
				pairs.Snd,
				lattice_pair.SubpairInclusions.At(overlap, vectors, pair, free)))
		sumInAmbient := a.Have(
			"which lies in the overlap, the ambient",
			"«chartSum» ⊆ A₀₁",
			By(
				lattice[0],
				lattice[1],
				pairs.Fst,
				pairs.Snd,
				lattice_pair.ChartSumInAmbient.At(overlap, A0, A1, vectors, pair)))
		ambients := a.Have(
			"O(i)^E has the overlap as its ambient too, the k[t, 1/t]-span of E",
			"lattice_pair_ambient(«wcRing»(«wcLaurent»), «wcField», «freePair») = A₀₁",
			Simp(Fwd(lattice_pair.LatticePairAmbientDef)),
			freeCharts[0].Rw(),
			By(
				datum,
				structure,
				sandwich[0],
				basisInField,
				submodule.SpanOfSubringSpan.Read(overLaurent).At(polynomialOps, E)))
		freeQuotient := a.Have(
			"H¹(O(i)^E) is the overlap modulo its chart sum: finite-dimensional over k, of dimension zero",
			"finite_dimensional(«wdScalars», quotient_module(«wcVectors»(A₀₁), «freeChartSum»)) ∧ "+
				"module_dim(«wdScalars», quotient_module(«wcVectors»(A₀₁), «freeChartSum»)) = 0",
			ringsAgree.RwRev(),
			ambients.RwRev(),
			By(
				freeH1[0],
				noFreeH1,
				lattice_pair.LatticePairH1Def.At(a.TermAs[RingOps[A]]("«wcRing»(«wcLaurent»)"), vectors, free),
				lattice_pair.LatticePairH1DimDef.At(
					a.TermAs[RingOps[A]]("«wcRing»(«wcLaurent»)"), k, vectors, free)))
		chartSum, freeChartSum := a.TermAs[Set[A]]("«chartSum»"), a.TermAs[Set[A]]("«freeChartSum»")
		chain := a.Have(
			"the dimension of the overlap modulo the free chart sum is that "+
				"of H¹(A₀, tᴺ⁺ⁱ·A₁) plus that of the chart sum modulo the free one",
			"finite_dimensional(«wdScalars», quotient_module(«wcVectors»(A₀₁), «chartSum»)) ∧ "+
				"finite_dimensional(«wdScalars», quotient_module(«wcVectors»(«chartSum»), «freeChartSum»)) ∧ "+
				"module_dim(«wdScalars», quotient_module(«wcVectors»(A₀₁), «freeChartSum»)) = "+
				"module_dim(«wdScalars», quotient_module(«wcVectors»(A₀₁), «chartSum»)) + "+
				"module_dim(«wdScalars», quotient_module(«wcVectors»(«chartSum»), «freeChartSum»))",
			By(
				datum,
				field.SubfieldRingSubfield.Read(L).At(k, A01),
				field.RingSubfieldRestrict.At(overlap, k, inv, k),
				overK[1],
				overK[2],
				freeSum,
				sumsInside,
				sumInAmbient,
				freeQuotient,
				module_dimension.QuotientChainDim.Read(overK[0]).At(inv, A01, chartSum, freeChartSum)))
		a.Show(
			"so H¹(A₀, tᴺ⁺ⁱ·A₁), the overlap modulo the chart sum, has dimension zero",
			Simp(
				Fwd(lattice_pair.LatticePairH1DimDef),
				Fwd(lattice_pair.LatticePairH1Def),
				Fwd(pairs.Fst),
				Fwd(pairs.Snd)),
			lattice[1].Rw(),
			ByArith(chain, freeQuotient))
	}),
})}

// PolePairSections — Riemann's count for the multiples of the divisor of poles
// of t: from some j on, ℓ(A₀, tʲ·A₁) + g = j·n + 1, n = dim_k A₀/t·A₀. χ is
// j·n + 1 − g at every j (PolePairEuler) and H¹ vanishes from some j on
// (PolePairH1Vanishes), where χ is ℓ.
var PolePairSections = polePairSectionsThm{family.Add(registry.ProofEntry{
	Name: "PolePairSections",
	Key:  "prop_6cac574c9554d110",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{"«wcDatum»"},
		Conclusion: "∃N:num. ∀j:num. " +
			"    N ≤ j ⇒ " +
			"    lattice_pair_h0_dim(«wcOverlap», k, «wcField», «polePair»(j)) + " +
			"    curve_genus(field_ring(L), k, A₀, A₁, A₀₁) = " +
			"    j * «zeroDegree» + 1",
		Abbrev: Abbrev{
			{Name: "poleChart", Text: "λi:num. image(L.mul(monoid_pow(L.mul, L.one, t, i)), A₁)"},
			{Name: "polePair", Text: "λi:num. (A₀, «poleChart»(i))"},
			{Name: "zeroDegree", Text: "module_dim(«wcRing»(k), " +
				"    quotient_module(«wcVectors»(A₀), image(L.mul(t), A₀)))"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		curve Fact,
	) {
		N, vanishing := a.UnpackAs[Nat](
			GroupPremises(curve, At(Read(PolePairH1Vanishes, L), k, A0, A1, A01, t)), "N")
		a.Take(N)
		j := a.FixAs[Nat]("j")
		large := a.Assume()
		sections := a.TermAs[Nat]("lattice_pair_h0_dim(«wcOverlap», k, «wcField», «polePair»(j))")
		genus := a.TermAs[Nat]("curve_genus(field_ring(L), k, A₀, A₁, A₀₁)")
		zeroDegree := a.TermAs[Nat]("«zeroDegree»")
		euler := a.Conjuncts(
			GroupPremises(curve, At(Read(PolePairEuler, L), k, A0, A1, A01, t, j)),
			"(A₀, tʲ·A₁) has finite cohomology",
			"its Euler characteristic is j·n + 1 − g")
		a.Show(
			"χ = ℓ − h¹ with h¹ = 0, so ℓ + g = j·n + 1",
			ByArith(
				euler[1],
				vanishing.At(j),
				large,
				lattice_pair.LatticePairEulerDef.At(
					a.TermAs[RingOps[A]]("«wcOverlap»"),
					k,
					a.TermAs[module_record.ModuleOps[A, A]]("«wcField»"),
					a.TermAs[_LatticePair]("«polePair»(j)")),
				int_embed.OfNumEq.At(
					a.TermAs[Nat](
						"lattice_pair_h0_dim(«wcOverlap», k, «wcField», «polePair»(j)) + "+
							"curve_genus(field_ring(L), k, A₀, A₁, A₀₁)"),
					a.TermAs[Nat]("j * «zeroDegree» + 1")),
				int_embed.OfNumAdd.At(sections, genus),
				int_embed.OfNumAdd.At(a.TermAs[Nat]("j * «zeroDegree»"), a.TermAs[Nat]("1")),
				int_embed.OfNumMul.At(j, zeroDegree)))
	}),
})}
