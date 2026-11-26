// counting.go — the effective divisors of a class, counted by its sections, and
// the Euler product of the effective counts.

package curve_zeta

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/formal_series"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/closed_divisor"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/proofs/scheme/divisor_lattice_correspondence"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/weighted_divisors"
	"github.com/euc-ai/xugo/library/registry"
)

// ConstantsAtLeastTwo — the constants of a smooth curve have more than one element:
// by the definition of the curve they are a finite field, and they are a subfield
// of L, where a finite subfield holds both 0 and 1.
var ConstantsAtLeastTwo = constantsAtLeastTwoThm{family.Add(registry.ProofEntry{
	Name: "ConstantsAtLeastTwo",
	Key:  "prop_dbdb532cc857041",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«scCurve»",
		},
		Conclusion: "1 < card(k)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		curve Fact,
	) {
		a.Show(
			"k is a finite subfield of L, so it has more than one element",
			ByArith(
				curve,
				a.Unfolded(curve, smooth_curve.SmoothFiniteFieldCurveDef),
				smooth_curve.ChartSubring.Read(L).At(k, A0, A1, A01, t),
				finite_field.FiniteSubfieldAtLeastTwo.Read(L).At(k)))
	}),
})}

// PairMultiplesEqIff — two nonzero multiples of an invertible pair agree exactly
// when their multipliers differ by a constant. A product with the inverse pair,
// and with the pair again, carries the question to the structure pair. There 1
// lies in both charts, so equal multiples put the ratio of the multipliers in
// A₀ ∩ A₁ = k; and a nonzero constant is a unit of both charts.
var PairMultiplesEqIff = pairMultiplesEqIffThm{family.Add(registry.ProofEntry{
	Name: "PairMultiplesEqIff",
	Key:  "prop_533e69e7e955e826",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t u v:A. ∀Y:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scInvertible»(Y)",
			"u ∈ L.carrier",
			"u ≠ L.zero",
			"v ∈ L.carrier",
			"v ≠ L.zero",
		},
		Conclusion: "lattice_pair_scale(u, Y) = lattice_pair_scale(v, Y) ⇔ ∃c:A. c ∈ k ∧ u = c * v",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t, u, v *Expr[A],
			Y *Expr[_LatticePair],
			curve, invertible, uInL, uNonzero, vInL, vNonzero Fact,
		) {
			record := a.TermAs[FieldOps[A]]("L")
			charts := a.Conjuncts(
				a.Have(
					"the charts are subrings of L that meet in the subfield k",
					"subring(field_ring(L), A₀) ∧ subring(field_ring(L), A₁) ∧ A₀ ∩ A₁ = k ∧ subfield(L, k)",
					By(
						a.Unfolded(curve, smooth_curve.SmoothFiniteFieldCurveDef),
						algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t))),
				"chart 0 is a subring of L",
				"chart 1 is a subring of L",
				"they meet in k",
				"k is a subfield of L")
			laws := a.Conjuncts(
				GroupPremises(
					curve, divisor_lattice_correspondence.InvertiblePairLaws.Read(L).At(k, A0, A1, A01, t)),
				"the structure pair is invertible",
				"the inverse of an invertible pair",
				"scaling an invertible pair")
			inverse := a.Conjuncts(
				GroupPremises(invertible, laws[1].At(Y)),
				"fst(Y) lies in L",
				"snd(Y) lies in L",
				"the inverse of Y is invertible",
				"Y times its inverse is the structure pair",
				"and the inverse of that inverse is Y")
			inverseOfY := a.TermAs[_LatticePair]("«scInverse»(Y)")
			multiples := a.Have(
				"a multiple of Y over Y is that multiple of the structure "+
					"pair, and that multiple times Y is the multiple of Y",
				Statement{
					Binders:    "∀w:A.",
					Hypotheses: []string{"w ∈ L.carrier", "w ≠ L.zero"},
					Conclusion: "«scMul»(lattice_pair_scale(w, Y), «scInverse»(Y)) = " +
						"lattice_pair_scale(w, (A₀, A₁)) ∧ " +
						"«scMul»(lattice_pair_scale(w, (A₀, A₁)), Y) = lattice_pair_scale(w, Y)",
				},
				Derive(func(b *Argument) {
					w := b.FixAs[A]("w")
					wNonzero := b.Assume()
					scaled := b.Conjuncts(
						GroupPremises(wNonzero, invertible, laws[2].At(w, Y)),
						"w · Y is invertible",
						"w⁻¹ undoes it",
						"and w comes out of its products")
					b.Show(
						"the scalar comes out of the product with the inverse, and the quotient by Y gives back w · Y",
						By(
							curve,
							invertible,
							scaled[0],
							inverse[2],
							inverse[3],
							scaled[2].At(inverseOfY),
							closed_divisor.PairQuotient.Read(L).At(
								k, A0, A1, A01, t, b.TermAs[_LatticePair]("lattice_pair_scale(w, Y)"), Y)))
				}))
			transfer := a.Have(
				"so two multiples of Y agree exactly when those multiples of the structure pair do",
				"lattice_pair_scale(u, Y) = lattice_pair_scale(v, Y) ⇔ "+
					"lattice_pair_scale(u, (A₀, A₁)) = lattice_pair_scale(v, (A₀, A₁))",
				By(multiples.At(u), multiples.At(v), uInL, uNonzero, vInL, vNonzero))
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			subrings := a.Have(
				"a subring of L holds 1 and lies in L",
				"∀S:set(A). subring(field_ring(L), S) ⇒ L.one ∈ S ∧ S ⊆ L.carrier",
				Derive(func(b *Argument) {
					S := b.FixAs[Set[A]]("S")
					subring := b.Assume()
					b.Show(
						"it holds the ring's 1 and lies in its carrier",
						BySets(subring, comm_ring.SubringOne.At(ring, S), comm_ring.SubringSubset.At(ring, S)))
				}))
			uL := a.MemberOf[on.L](u, uInL)
			vL := a.MemberOf[on.L](v, vInL)
			inverseV := field.InvIn.Read(L).At(vL)
			cancelled := a.Have(
				"v⁻¹ v = 1",
				"L.inv(v) * v = L.one",
				By(L, vL, vNonzero, field.MulLeftInverseOn.At(record, v)))
			ratio := a.Have(
				"where the images of u and v agree in a subring S, the ratio v⁻¹ u lies in S",
				"∀S:set(A). subring(field_ring(L), S) ∧ image(L.mul(u), S) = image(L.mul(v), S) ⇒ L.inv(v) * u ∈ S",
				Derive(func(b *Argument) {
					S := b.FixAs[Set[A]]("S")
					given := b.Conjuncts(
						b.Assume(),
						"S is a subring of L",
						"the two images agree on S")
					unit := b.Have(
						"1 lies in S, and S lies in L",
						"L.one ∈ S ∧ S ⊆ L.carrier",
						By(given[0], subrings.At(S)))
					once := b.Have(
						"u is u times 1",
						"u * L.one = u",
						ByArith(L, uL))
					s, factored := b.ObtainAs[A](
						"so u lies in the image of v",
						"∃s:A. s ∈ S ∧ u = v * s",
						BySets(once, given[1], unit))
					parts := b.Conjuncts(
						factored,
						"s lies in S",
						"u is v times s")
					sL := b.MemberOf[on.L](s, b.Have(
						"s lies in L",
						"s ∈ L.carrier",
						BySets(parts[0], unit)))
					quotient := b.Have(
						"so the ratio is s",
						"L.inv(v) * u = s",
						ByArith(L, Scaled(inverseV, parts[1]), Scaled(s, cancelled), uL, vL, sL, inverseV))
					b.Show(
						"and s lies in S",
						By(Normalized, quotient, parts[0]))
				}))
			unitMultiple := a.Have(
				"a nonzero constant is a unit of a subring holding k, so u = c v and v have one image in it",
				Statement{
					Binders:    "∀c:A. ∀S:set(A).",
					Hypotheses: []string{"c ∈ k", "c ≠ L.zero", "u = c * v", "subring(field_ring(L), S)", "k ⊆ S"},
					Conclusion: "image(L.mul(u), S) = image(L.mul(v), S)",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					S := b.FixAs[Set[A]]("S")
					given := b.Conjuncts(
						b.Assume(),
						"c lies in k",
						"c is not zero",
						"u is c times v",
						"S is a subring of L",
						"k lies in S")
					cInverse := b.TermAs[A]("L.inv(c)")
					inCarrier := b.Have(
						"S lies in L",
						"S ⊆ L.carrier",
						By(given[3], subrings.At(S)))
					units := b.Have(
						"c and its inverse lie in k, so in S",
						"c ∈ S ∧ L.inv(c) ∈ S",
						BySets(given[0], given[4], charts[3], field.SubfieldInv.At(record, k, c)))
					cL := b.MemberOf[on.L](c, b.Have(
						"c lies in L",
						"c ∈ L.carrier",
						BySets(units, inCarrier)))
					inverseC := b.MemberOf[on.L](cInverse, b.Have(
						"c⁻¹ lies in L",
						"L.inv(c) ∈ L.carrier",
						BySets(units, inCarrier)))
					undone := b.Have(
						"c c⁻¹ = 1",
						"c * L.inv(c) = L.one",
						By(L, cL, given[1], field.MulRightInverseOn.At(record, c)))
					pointwise := b.Have(
						"a point of S and its product by c or by c⁻¹ carry each image to the other",
						"∀s:A. s ∈ S ⇒ c * s ∈ S ∧ L.inv(c) * s ∈ S ∧ u * s = v * (c * s) ∧ v * s = u * (L.inv(c) * s)",
						Derive(func(d *Argument) {
							s := d.FixAs[A]("s")
							sIn := d.Assume()
							sL := d.MemberOf[on.L](s, d.Have(
								"s lies in L",
								"s ∈ L.carrier",
								BySets(sIn, inCarrier)))
							products := d.Have(
								"the products stay in S",
								"c * s ∈ S ∧ L.inv(c) * s ∈ S",
								By(
									sIn,
									units,
									given[3],
									comm_ring.SubringMul.At(ring, S, c, s),
									comm_ring.SubringMul.At(ring, S, cInverse, s)))
							first := d.Have(
								"u s = v (c s)",
								"u * s = v * (c * s)",
								ByArith(L, Scaled(s, given[2]), uL, cL, vL, sL))
							second := d.Have(
								"v s = u (c⁻¹ s)",
								"v * s = u * (L.inv(c) * s)",
								ByArith(
									L,
									Scaled(d.TermAs[A]("L.inv(c) * s"), given[2]),
									Scaled(d.TermAs[A]("v * s"), undone),
									uL,
									cL,
									vL,
									sL,
									inverseC))
							d.Show(
								"these are the four clauses",
								By(products, first, second))
						}))
					b.Show(
						"so the two images agree",
						BySets(pointwise))
				}))
			a.Iff()
			a.Forward(
				"equal multiples have a constant ratio",
				func(b *Argument, same Fact) {
					images := b.Conjuncts(
						b.Simplified(
							b.Have(
								"the multiples of the structure pair agree",
								"lattice_pair_scale(u, (A₀, A₁)) = lattice_pair_scale(v, (A₀, A₁))",
								By(same, transfer)),
							Fwd(invertible_lattice_pair.LatticePairScaleDef),
							Fwd(pairs.PairEq),
							Fwd(pairs.Fst),
							Fwd(pairs.Snd)),
						"the images agree on chart 0",
						"and on chart 1")
					constant := b.Have(
						"so the ratio lies in both charts, which meet in k",
						"L.inv(v) * u ∈ k",
						BySets(ratio.At(A0), ratio.At(A1), images[0], images[1], charts[0], charts[1], charts[2]))
					rebuilt := b.Have(
						"and the ratio times v is u",
						"u = L.inv(v) * u * v",
						ByArith(L, Scaled(u, cancelled), uL, vL, inverseV))
					b.Take(b.TermAs[A]("L.inv(v) * u"))
					b.Show(
						"the ratio is the constant",
						By(constant, rebuilt))
				})
			a.Backward(
				"a constant ratio gives equal multiples",
				func(b *Argument, constant Fact) {
					c, chosen := b.UnpackAs[A](constant, "c")
					given := b.Conjuncts(
						chosen,
						"c lies in k",
						"u is c times v")
					nonzero := b.Have(
						"c is not zero, since u is not",
						"c ≠ L.zero",
						Derive(func(d *Argument) {
							zero := d.SupposeNot()
							d.Show(
								"a zero c would make u zero",
								By(Normalized, zero, uNonzero, given[1], comm_ring.MulLeftZeroOn.Read(field.RingOn.Read(L)).At(vL)))
						}))
					inCharts := b.Have(
						"k lies in both charts",
						"k ⊆ A₀ ∧ k ⊆ A₁",
						BySets(charts[2]))
					images := b.Have(
						"the images of u and v agree on each chart",
						"image(L.mul(u), A₀) = image(L.mul(v), A₀) ∧ image(L.mul(u), A₁) = image(L.mul(v), A₁)",
						By(
							given[0],
							nonzero,
							given[1],
							charts[0],
							charts[1],
							inCharts,
							unitMultiple.At(c, A0),
							unitMultiple.At(c, A1)))
					structure := b.Have(
						"so the multiples of the structure pair agree",
						"lattice_pair_scale(u, (A₀, A₁)) = lattice_pair_scale(v, (A₀, A₁))",
						Simp(
							Fwd(invertible_lattice_pair.LatticePairScaleDef),
							Fwd(pairs.PairEq),
							Fwd(pairs.Fst),
							Fwd(pairs.Snd)),
						By(images))
					b.Show(
						"and so do the multiples of Y",
						By(structure, transfer))
				})
		}),
})}

// SectionLinesCount — the lines through 0 in the sections of an invertible pair
// are finite in number, and that number times q − 1 is q^ℓ − 1, for q the size of
// the constants k and ℓ the dimension of the sections. The sections are a module
// over the finite field k, finite dimensional since the pair is invertible, and
// projective counting applies to it.
var SectionLinesCount = sectionLinesCountThm{family.Add(registry.ProofEntry{
	Name: "SectionLinesCount",
	Key:  "prop_291609df419ee5b3",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀X:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scInvertible»(X)",
		},
		Conclusion: "finite(«lines») ∧ card(«lines») * (card(k) - 1) = card(k) ^ «scSections»(X) - 1",
		Abbrev: Abbrev{
			{Name: "lines", Text: "{image(λc:A. c * v, k) | v:A | v ∈ fst(X) ∩ snd(X) ∧ v ≠ L.zero}"},
			{Name: "fieldModule", Text: "regular_module(field_ring(L))"},
			{Name: "scalars", Text: "restrict_ring(field_ring(L), k)"},
			{Name: "space", Text: "lattice_pair_h0(«fieldModule», X)"},
			{Name: "constantRing", Text: "field_ring(restrict_field(L, k))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			X *Expr[_LatticePair],
			curve, invertible Fact,
		) {
			record := a.TermAs[FieldOps[A]]("L")
			overlap := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₀₁)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«fieldModule»")
			over := a.Have(
				"the curve lies over the line of t",
				"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
				By(curve, smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t)))
			data := a.Conjuncts(
				GroupPremises(over, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in L",
				"the charts are biaffine over the line of t",
				"k is a subfield of L",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"k is a field",
				"k lies in both charts")
			finiteDimension := a.Have(
				"an invertible pair has finite-dimensional sections",
				"finite_dimensional(«scalars», «space»)",
				By(
					over,
					invertible,
					algebraic_curve.InvertibleFinite.Read(L).At(k, A0, A1, A01, t, X),
					lattice_pair.LatticePairFiniteDef.At(overlap, k, vectors, X),
					module_record.RestrictRingTwice))
			sectionsSubmodule := a.Have(
				"the intersection of the two charts is a submodule over k",
				"submodule(«scalars», «fieldModule», fst(X) ∩ snd(X))",
				By(
					invertible,
					data[7],
					lattice_pair.H0Submodule.At(overlap, A0, A1, k, vectors, X),
					invertible_lattice_pair.InvertibleLatticePairDef.At(
						a.TermAs[RingOps[A]]("field_ring(L)"), A0, A1, A01, X),
					module_record.RestrictRingTwice,
					set_order.SubsetInter.At(k, A0, A1)))
			sections := a.Have(
				"so the sections are a module over k",
				"module_on(«scalars», «space»)",
				By(
					data[2],
					sectionsSubmodule,
					module.ModuleRestrictScalars.Read(module.RegularModuleOn.Read(field.RingOn.Read(L))).At(k),
					field.SubfieldSubring.Read(L).At(k),
					submodule.SubmoduleModuleOn,
					lattice_pair.LatticePairH0Def))
			finiteConstants := a.Have(
				"k is a finite field",
				"finite_field(restrict_field(L, k))",
				By(data[6], curve, finite_field.FiniteFieldDef, smooth_curve.SmoothFiniteFieldCurveDef))
			sectionsOverK := a.Have(
				"read over the field k, the sections are a finite-dimensional module",
				"module_on(«constantRing», «space») ∧ finite_dimensional(«constantRing», «space»)",
				By(Normalized, sections, finiteDimension, field.RestrictFieldRing.At(record, k)))
			count := a.Simplified(
				GroupPremises(
					finiteConstants,
					sectionsOverK,
					finite_field.ProjectiveCount.At(
						a.TermAs[FieldOps[A]]("restrict_field(L, k)"), a.TermAs[module_record.ModuleOps[A, A]]("«space»"))),
				Rev(field.RestrictFieldRing),
				Fwd(finite_field.FieldSizeDef))
			a.Show(
				"projective counting, the ring of the field k being L's ring restricted to k",
				By(count))
		}),
})}

// EffectiveDivisorsInClass — the effective divisors of a class are counted by
// the lines of sections: for a closed divisor D the effective divisors linearly
// equivalent to D are finite, and (q − 1) times their number is q^ℓ − 1, with
// ℓ = dim H⁰(D). A nonzero section v writes the pair X of D as v times the pair
// of an effective divisor E; conversely an effective E of the class has 1 in both
// components of its pair, so the multiplier of X over it is a section. Two
// sections give one E exactly when their ratio is a constant, so E ↦ {multipliers
// of X over E} ∪ {0} is one-to-one, onto the lines of sections.
var EffectiveDivisorsInClass = effectiveDivisorsInClassThm{family.Add(registry.ProofEntry{
	Name: "EffectiveDivisorsInClass",
	Key:  "prop_eed98655b7bb72ed",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(D)",
		},
		Conclusion: "finite(«scEffectiveInClass»(«scClass»(D))) ∧ " +
			"(card(k) - 1) * card(«scEffectiveInClass»(«scClass»(D))) = " +
			"card(k) ^ «scSections»(«scPair»(D)) - 1",
		Abbrev: Abbrev{
			{Name: "lines", Text: "{image(λc:A. c * v, k) | v:A | v ∈ fst(X) ∩ snd(X) ∧ v ≠ L.zero}"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D *Arrow[_LatticePair, Int],
			curve, divisor Fact,
		) {
			record := a.TermAs[FieldOps[A]]("L")
			X, pairDefinition := a.LetAs[_LatticePair]("X", "«scPair»(D)")
			divisorsOfClass, classDefinition := a.LetAs[Set[_Divisor]](
				"T", "«scEffectiveInClass»(curve_pair_class(field_ring(L), X))")
			line, lineDefinition := a.LetAs[Fun[_Divisor, Set[A]]](
				"line",
				"λE:(prod(set(A), set(A)) → int). "+
					"    {x:A | x ∈ L.carrier ∧ (x = L.zero ∨ X = lattice_pair_scale(x, «scPair»(E)))}")
			over := a.Have(
				"the curve lies over the line of t",
				"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
				By(curve, smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t)))
			correspondence := divisor_lattice_correspondence.WeightedDivisorLatticeCorrespondence.Read(L).At(
				k, A0, A1, A01, t)
			laws := a.Conjuncts(
				GroupPremises(
					curve, divisor_lattice_correspondence.InvertiblePairLaws.Read(L).At(k, A0, A1, A01, t)),
				"the structure pair is invertible",
				"the inverse of an invertible pair",
				"scaling an invertible pair")
			invertible := a.Have(
				"the pair of a closed divisor is invertible",
				"∀E:(prod(set(A), set(A)) → int). «scDivisor»(E) ⇒ «scInvertible»(«scPair»(E))",
				By(curve, correspondence))
			invertibleX := a.Have(
				"in particular the pair X of D is",
				"«scInvertible»(X)",
				By(Normalized, divisor, invertible.At(D), pairDefinition))
			chartsInL := a.Conjuncts(
				a.Simplified(
					GroupPremises(laws[0], laws[1].At(a.TermAs[_LatticePair]("(A₀, A₁)"))),
					Fwd(pairs.Fst),
					Fwd(pairs.Snd)),
				"chart 0 lies in L",
				"chart 1 lies in L",
				"the inverse of the structure pair is invertible",
				"the structure pair times its inverse is itself",
				"and the inverse of that inverse is the structure pair")
			pairX := a.Conjuncts(
				GroupPremises(invertibleX, laws[1].At(X)),
				"fst(X) lies in L",
				"snd(X) lies in L",
				"the inverse of X is invertible",
				"X times its inverse is the structure pair",
				"and the inverse of that inverse is X")
			sectionsInL := a.Have(
				"the sections of X lie in L",
				"fst(X) ∩ snd(X) ⊆ L.carrier",
				BySets(pairX[0]))
			constants := a.Have(
				"k is a subfield of L, so it lies in L",
				"subfield(L, k) ∧ k ⊆ L.carrier",
				By(
					over,
					algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t),
					field.SubfieldSubset.At(record, k)))
			one := comm_ring.OneIn.Read(field.RingOn.Read(L))
			criterion := a.Have(
				"the class of a closed divisor is the class of D exactly "+
					"when the pair of D is a nonzero multiple of its pair",
				Statement{
					Binders:    "∀E:(prod(set(A), set(A)) → int).",
					Hypotheses: []string{"«scDivisor»(E)"},
					Conclusion: "«scClass»(E) = curve_pair_class(field_ring(L), X) ⇔ " +
						"∃w:A. w ∈ L.carrier ∧ w ≠ L.zero ∧ X = lattice_pair_scale(w, «scPair»(E))",
				},
				Derive(func(b *Argument) {
					E := b.FixAs[_Divisor]("E")
					divisorE := b.Assume()
					b.Show(
						"the classes of two invertible pairs agree when one is a nonzero multiple of the other",
						By(
							over,
							divisorE,
							invertible.At(E),
							invertibleX,
							algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t),
							curve_degree.PairClassEqIff.Read(L).At(A0, A1, A01, t, b.TermAs[_LatticePair]("«scPair»(E)"), X)))
				}))
			member := a.Have(
				"a member of the class is an effective closed divisor over whose pair X is a nonzero multiple",
				"∀E:(prod(set(A), set(A)) → int). "+
					"    E ∈ T ⇔ "+
					"    «scDivisor»(E) ∧ "+
					"    (∀P:prod(set(A), set(A)). 0 ≤ E(P)) ∧ "+
					"    ∃w:A. w ∈ L.carrier ∧ w ≠ L.zero ∧ X = lattice_pair_scale(w, «scPair»(E))",
				Derive(func(b *Argument) {
					E := b.FixAs[_Divisor]("E")
					reading := b.Have(
						"a member of the class is an effective closed divisor of the class of D",
						"E ∈ T ⇔ "+
							"«scDivisor»(E) ∧ "+
							"(∀P:prod(set(A), set(A)). 0 ≤ E(P)) ∧ "+
							"«scClass»(E) = curve_pair_class(field_ring(L), X)",
						classDefinition.Rw(),
						BySets())
					b.Show(
						"and that class is read by the criterion",
						By(reading, criterion.At(E)))
				}))
			multiplier := a.Have(
				"a point of the line of E is a point of L, 0 or a multiplier of X over E",
				"∀E:(prod(set(A), set(A)) → int). ∀x:A. "+
					"    x ∈ line(E) ⇔ x ∈ L.carrier ∧ (x = L.zero ∨ X = lattice_pair_scale(x, «scPair»(E)))",
				lineDefinition.Rw(),
				BySets())
			closedIn := a.Have(
				"a divisor of the class is a closed divisor",
				"∀E:(prod(set(A), set(A)) → int). E ∈ T ⇒ «scDivisor»(E)",
				a.ForEach(func(E *Expr[_Divisor]) Action {
					return By(member.At(E))
				}))
			unit := a.Have(
				"1 lies in the inverse of a part of a chart",
				"∀S I:set(A). I ⊆ S ∧ S ⊆ L.carrier ⇒ L.one ∈ fractional_inverse(field_ring(L), S, I)",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("S")
					b.FixAs[Set[A]]("I")
					given := b.Assume()
					contained := b.Have(
						"a point of I, times 1, stays in S",
						"∀m:A. m ∈ I ⇒ L.one * m ∈ S",
						Derive(func(c *Argument) {
							m := c.FixAs[A]("m")
							mIn := c.Assume()
							mS := c.Have(
								"m lies in S and in L",
								"m ∈ S ∧ m ∈ L.carrier",
								BySets(mIn, given))
							mL := c.MemberOf[on.L](m, c.Have(
								"m lies in L",
								"m ∈ L.carrier",
								BySets(mS)))
							unchanged := c.Have(
								"1 m = m",
								"L.one * m = m",
								ByArith(L, mL))
							c.Show(
								"so it lies in S",
								By(Normalized, unchanged, mS))
						}))
					b.Show(
						"1 lies in L and carries I into S",
						Simp(Fwd(fractional_ideal.FractionalInverseDef)),
						By(contained, one))
				}))
			ones := a.Have(
				"the pair of an effective divisor holds 1 in both components",
				Statement{
					Binders:    "∀E:(prod(set(A), set(A)) → int).",
					Hypotheses: []string{"«scDivisor»(E)", "∀P:prod(set(A), set(A)). 0 ≤ E(P)"},
					Conclusion: "L.one ∈ fst(«scPair»(E)) ∧ L.one ∈ snd(«scPair»(E))",
				},
				Derive(func(b *Argument) {
					E := b.FixAs[_Divisor]("E")
					given := b.Conjuncts(
						b.Assume(),
						"E is a closed divisor",
						"E is effective")
					inverted := b.Have(
						"the pair of E is the inverse of the pair of −E, an integral pair",
						"«scPair»(E) = «scInverse»(«scPair»(λP:prod(set(A), set(A)). -E(P))) ∧ "+
							"fst(«scPair»(λP:prod(set(A), set(A)). -E(P))) ⊆ A₀ ∧ "+
							"snd(«scPair»(λP:prod(set(A), set(A)). -E(P))) ⊆ A₁",
						By(
							curve,
							given[0],
							given[1],
							laws[1].At(b.TermAs[_LatticePair]("«scPair»(E)")),
							closed_divisor.ClosedDivisorNegate.Read(L).At(k, A0, A1, A01, t, E),
							closed_divisor.EffectivePairIntegral.Read(L).At(k, A0, A1, A01, t, E)))
					parts := b.Conjuncts(
						inverted,
						"the pair of E is the inverse of the pair of −E",
						"the pair of −E lies in chart 0",
						"and in chart 1")
					b.Show(
						"and 1 lies in the inverse of a part of a chart",
						parts[0].Rw(),
						Simp(Fwd(invertible_lattice_pair.LatticePairInverseDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
						By(
							unit.At(A0, b.TermAs[Set[A]]("fst(«scPair»(λP:prod(set(A), set(A)). -E(P)))")),
							unit.At(A1, b.TermAs[Set[A]]("snd(«scPair»(λP:prod(set(A), set(A)). -E(P)))")),
							parts[1],
							parts[2],
							chartsInL[0],
							chartsInL[1]))
				}))
			sectionOf := a.Have(
				"an effective divisor of the class gives a nonzero section of X",
				Statement{
					Binders:    "∀E:(prod(set(A), set(A)) → int).",
					Hypotheses: []string{"E ∈ T"},
					Conclusion: "∃v:A. v ∈ fst(X) ∩ snd(X) ∧ v ≠ L.zero ∧ X = lattice_pair_scale(v, «scPair»(E))",
				},
				Derive(func(b *Argument) {
					E := b.FixAs[_Divisor]("E")
					inClass := b.Assume()
					given := b.Conjuncts(
						b.Have(
							"E is an effective closed divisor over whose pair X is a nonzero multiple",
							"«scDivisor»(E) ∧ "+
								"(∀P:prod(set(A), set(A)). 0 ≤ E(P)) ∧ "+
								"∃w:A. w ∈ L.carrier ∧ w ≠ L.zero ∧ X = lattice_pair_scale(w, «scPair»(E))",
							By(inClass, member.At(E))),
						"E is a closed divisor",
						"E is effective",
						"X is a nonzero multiple of its pair")
					w, multiple := b.UnpackAs[A](given[2], "w")
					chosen := b.Conjuncts(
						multiple,
						"w lies in L",
						"w is not zero",
						"X is w times the pair of E")
					wL := b.MemberOf[on.L](w, chosen[0])
					once := b.Have(
						"w is w times 1",
						"w * L.one = w",
						ByArith(L, wL))
					components := b.Have(
						"the components of X are the images of those of the pair of E under w",
						"fst(X) = image(L.mul(w), fst(«scPair»(E))) ∧ snd(X) = image(L.mul(w), snd(«scPair»(E)))",
						chosen[2].Rw(),
						Simp(Fwd(invertible_lattice_pair.LatticePairScaleDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
						Basic())
					section := b.Have(
						"so w, the image of 1, is a section of X",
						"w ∈ fst(X) ∩ snd(X)",
						BySets(once, components, given[0], given[1], ones.At(E)))
					b.Take(w)
					b.Show(
						"w is the section",
						By(section, chosen[1], chosen[2]))
				}))
			divisorOf := a.Have(
				"a nonzero section of X gives an effective divisor of the class",
				Statement{
					Binders:    "∀v:A.",
					Hypotheses: []string{"v ∈ fst(X) ∩ snd(X)", "v ≠ L.zero"},
					Conclusion: "∃E:(prod(set(A), set(A)) → int). E ∈ T ∧ X = lattice_pair_scale(v, «scPair»(E))",
				},
				Derive(func(b *Argument) {
					v := b.FixAs[A]("v")
					given := b.Conjuncts(
						b.Assume(),
						"v is a section of X",
						"v is not zero")
					inL := b.Have(
						"v lies in L",
						"v ∈ L.carrier",
						BySets(given[0], sectionsInL))
					E, section := b.UnpackAs[_Divisor](
						GroupPremises(
							curve,
							invertibleX,
							given[0],
							given[1],
							divisor_lattice_correspondence.EffectiveDivisorOfSection.Read(L).At(k, A0, A1, A01, t, X, v)),
						"E")
					parts := b.Conjuncts(
						section,
						"E is a closed divisor",
						"E is effective",
						"X is v times the pair of E")
					multiple := b.Have(
						"so X is a nonzero multiple of the pair of E",
						"∃w:A. w ∈ L.carrier ∧ w ≠ L.zero ∧ X = lattice_pair_scale(w, «scPair»(E))",
						Witness(v),
						By(inL, given[1], parts[2]))
					inClass := b.Have(
						"so E lies in the class",
						"E ∈ T",
						By(member.At(E), multiple, parts[0], parts[1]))
					b.Show(
						"E is the divisor",
						Witness(E),
						By(inClass, parts[2]))
				}))
			multiples := At(PairMultiplesEqIff.Read(L), k, A0, A1, A01, t)
			lineEq := a.Have(
				"the constant multiples of a nonzero section v with divisor E are the points of line(E)",
				Statement{
					Binders: "∀v:A. ∀E:(prod(set(A), set(A)) → int).",
					Hypotheses: []string{
						"v ∈ fst(X) ∩ snd(X)",
						"v ≠ L.zero",
						"E ∈ T",
						"X = lattice_pair_scale(v, «scPair»(E))",
					},
					Conclusion: "image(λc:A. c * v, k) = line(E)",
				},
				Derive(func(b *Argument) {
					v := b.FixAs[A]("v")
					E := b.FixAs[_Divisor]("E")
					given := b.Conjuncts(
						b.Assume(),
						"v is a section of X",
						"v is not zero",
						"E lies in the class",
						"X is v times the pair of E")
					inL := b.Have(
						"v lies in L",
						"v ∈ L.carrier",
						BySets(given[0], sectionsInL))
					closedE := closedIn.At(E)
					vL := b.MemberOf[on.L](v, inL)
					constantMultiple := b.Have(
						"a nonzero x of L is a multiplier of X over E exactly when it is a constant times v",
						Statement{
							Binders:    "∀x:A.",
							Hypotheses: []string{"x ∈ L.carrier", "x ≠ L.zero"},
							Conclusion: "X = lattice_pair_scale(x, «scPair»(E)) ⇔ ∃c:A. c ∈ k ∧ x = c * v",
						},
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							nonzero := c.Assume()
							c.Show(
								"X is v times the pair of E, and two multiples agree when the ratio is a constant",
								By(
									curve,
									nonzero,
									inL,
									given[1],
									given[2],
									given[3],
									closedE,
									invertible.At(E),
									multiples.At(x, v, c.TermAs[_LatticePair]("«scPair»(E)"))))
						}))
					zero := b.Have(
						"0 is 0 times v",
						"L.zero ∈ k ∧ L.zero * v = L.zero",
						ByArith(L, vL, constants, field.SubfieldZero))
					multiplesInL := b.Have(
						"a constant times v lies in L",
						"∀c:A. c ∈ k ⇒ c * v ∈ L.carrier",
						Derive(func(d *Argument) {
							c := d.FixAs[A]("c")
							constant := d.Assume()
							cInL := d.Have(
								"c lies in L",
								"c ∈ L.carrier",
								BySets(constant, constants))
							d.Show(
								"both factors lie in L",
								By(comm_ring.MulIn.Read(field.RingOn.Read(L)).At(d.MemberOf[on.L](c, cInL), vL)))
						}))
					b.Show(
						"so the line of v and the line of E have one set of points",
						BySets(constantMultiple, zero, multiplesInL, multiplier.At(E)))
				}))
			linesOfClass := a.Have(
				"so the lines of sections are the sets of multipliers of the divisors of the class",
				"∀ℓ:set(A). ℓ ∈ «lines» ⇔ ∃E:(prod(set(A), set(A)) → int). E ∈ T ∧ ℓ = line(E)",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("ℓ")
					b.Iff()
					b.Forward(
						"the line of a nonzero section is the set of multipliers of its divisor",
						func(c *Argument, isLine Fact) {
							v, chosen := c.ObtainAs[A](
								"a line is the line of a nonzero section v",
								"∃v:A. v ∈ fst(X) ∩ snd(X) ∧ v ≠ L.zero ∧ ℓ = image(λc:A. c * v, k)",
								By(isLine))
							parts := c.Conjuncts(
								chosen,
								"v is a section",
								"v is not zero",
								"ℓ is its line")
							E, section := c.UnpackAs[_Divisor](GroupPremises(parts[0], parts[1], divisorOf.At(v)), "E")
							details := c.Conjuncts(
								section,
								"E lies in the class",
								"X is v times the pair of E")
							c.Take(E)
							c.Show(
								"E is the divisor of the line",
								By(lineEq.At(v, E), parts[0], parts[1], parts[2], details[0], details[1]))
						})
					b.Backward(
						"the set of multipliers of a divisor of the class is the line of its section",
						func(c *Argument, multipliers Fact) {
							E, chosen := c.UnpackAs[_Divisor](multipliers, "E")
							parts := c.Conjuncts(
								chosen,
								"E lies in the class",
								"ℓ is its set of multipliers")
							v, section := c.UnpackAs[A](GroupPremises(parts[0], sectionOf.At(E)), "v")
							details := c.Conjuncts(
								section,
								"v is a section",
								"v is not zero",
								"X is v times the pair of E")
							ofSection := c.Have(
								"so ℓ is the line of v",
								"ℓ = image(λc:A. c * v, k)",
								By(parts[0], parts[1], lineEq.At(v, E), details[0], details[1], details[2]))
							c.Show(
								"and v is a nonzero section",
								By(details[0], details[1], ofSection))
						})
				}))
			injects := a.Have(
				"two divisors of the class with one set of multipliers are one",
				"injective_on(T, line)",
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					x := b.FixAs[_Divisor]("x")
					y := b.FixAs[_Divisor]("y")
					given := b.Conjuncts(
						b.Assume(),
						"x lies in the class",
						"y lies in the class",
						"they have one set of multipliers")
					v, section := b.UnpackAs[A](GroupPremises(given[0], sectionOf.At(x)), "v")
					parts := b.Conjuncts(
						section,
						"v is a section",
						"v is not zero",
						"X is v times the pair of x")
					inL := b.Have(
						"v lies in L",
						"v ∈ L.carrier",
						BySets(parts[0], sectionsInL))
					alsoY := b.Have(
						"so v is a multiplier of X over y",
						"X = lattice_pair_scale(v, «scPair»(y))",
						BySets(given[2], inL, parts[1], parts[2], multiplier.At(x, v), multiplier.At(y, v)))
					closedX := closedIn.At(x)
					closedY := closedIn.At(y)
					equal := b.Have(
						"undoing v, the pairs of x and y agree",
						"«scPair»(x) = «scPair»(y)",
						By(
							Normalized,
							given[0],
							given[1],
							laws[2].At(v, b.TermAs[_LatticePair]("«scPair»(x)")),
							laws[2].At(v, b.TermAs[_LatticePair]("«scPair»(y)")),
							invertible.At(x),
							invertible.At(y),
							closedX,
							closedY,
							inL,
							parts[1],
							parts[2],
							alsoY))
					b.Show(
						"and a closed divisor is determined by its pair",
						By(
							curve,
							given[0],
							given[1],
							closedX,
							closedY,
							equal,
							divisor_lattice_correspondence.ClosedDivisorPairInjective.Read(L).At(k, A0, A1, A01, t, x, y)))
				}))
			onto := a.Have(
				"the image of the class is the set of lines of sections",
				"image(line, T) = «lines»",
				BySets(linesOfClass))
			count := a.Conjuncts(
				GroupPremises(curve, invertibleX, SectionLinesCount.Read(L).At(k, A0, A1, A01, t, X)),
				"the lines of sections are finite",
				"and counted by the dimension")
			finiteClass := a.Have(
				"so the class is finite",
				"finite(T)",
				By(injects, onto, count[0], finite_set.FiniteImageInjEq.At(line, divisorsOfClass)))
			sameSize := a.Have(
				"and has as many divisors as there are lines",
				"card(«lines») = card(T)",
				onto.RwRev(),
				By(injects, finiteClass, cardinality.CardImageInj.At(line, divisorsOfClass)))
			identity := a.Have(
				"so (q − 1) times its number is q^ℓ − 1",
				"(card(k) - 1) * card(T) = card(k) ^ «scSections»(X) - 1",
				ByArith(sameSize, count[1]))
			a.Show(
				"the class is finite, and that is its number",
				By(finiteClass, identity))
		}),
})}

// ZetaEulerProductAndLogDerivative — the effective-divisor counts of a smooth
// curve over a finite field satisfy the logarithmic recurrence with the point
// counts of its constant extensions, and each is its coefficient in the Euler
// product over the closed points. These counts are the weighted count of the
// closed points under their degrees, where the Euler product and the natural
// counting identity hold; the weighted multiples are the extension counts, each
// the sum of the degrees of the closed points whose degree divides the
// extension's, so the cast of that identity is the recurrence.
var ZetaEulerProductAndLogDerivative = zetaEulerProductAndLogDerivativeThm{family.Add(registry.ProofEntry{
	Name: "ZetaEulerProductAndLogDerivative",
	Key:  "prop_9a2f0fd6d6de6ad",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«curve»",
		},
		Conclusion: "series_recurrence(real_ring, «zeta», λm:num. real_of_num(«count»(m))) ∧ " +
			"(∀n:num. " +
			"    «effective»(int_of_num(n)) = " +
			"    real_of_num(set_fold(λP:prod(set(A), set(A)). λa:(num → num). " +
			"                polynomial_mul(λi:num. λj:num. i + j, " +
			"                    0, " +
			"                    λi:num. λj:num. i * j, " +
			"                    λm:num. COND(«pointDegree»(P) ∣ m, 1, 0), " +
			"                    a), " +
			"            {P:prod(set(A), set(A)) | «point»(P) ∧ «pointDegree»(P) ≤ n}, " +
			"            λm:num. COND(m = 0, 1, 0), " +
			"            n)))",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		algebraicallyClosed, inField, curve Fact,
	) {
		points := a.TermAs[Set[_LatticePair]]("«points»")
		degree := a.TermAs[Fun[_LatticePair, Nat]]("«pointDegree»")
		functionField := a.Have(
			"K is a field under M's operations",
			"field_on(restrict_field(M, K))",
			By(inField, field.SubfieldFieldOn.Read(M).At(K)))
		closedPoints := a.Conjuncts(
			a.Simplified(
				GroupPremises(
					curve, smooth_curve.ClosedPointsFiniteByDegree.Read(functionField).At(k, A0, A1, A01, t)),
				curve_point_count.InAmbient),
			"the curve has a closed point",
			"closed points have finite positive degree",
			"finitely many have bounded degree, and finitely many divisors each degree")
		weighted := a.Have(
			"at a natural number the effective count is the cast of the weighted count",
			"∀n:num. «effective»(n) = real_of_num(weighted_count(«points», «pointDegree», n))",
			a.ForEach(func(_ *Expr[Nat]) Action {
				return By(
					CurveEffectiveCountDef,
					int_embed.OfNumRetract,
					int_embed.OfNumLt,
					nat_order.LessThanZeroClause)
			}))
		levels := a.Have(
			"a level of the weight is the set of closed points of bounded degree",
			"∀n:num. "+
				"    {x:prod(set(A), set(A)) | x ∈ «points» ∧ «pointDegree»(x) ≤ n} = "+
				"    {P:prod(set(A), set(A)) | «point»(P) ∧ «pointDegree»(P) ≤ n}",
			a.ForEach(func(_ *Expr[Nat]) Action { return BySets() }))
		finiteLevels := a.Have(
			"so every level of the weight is finite",
			"∀n:num. finite({x:prod(set(A), set(A)) | x ∈ «points» ∧ «pointDegree»(x) ≤ n})",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"finitely many closed points have degree at most n",
					levels.At(n).Rw(),
					By(closedPoints[2].At(n)))
			}))
		counts := a.Have(
			"the weighted multiples are the point counts of the constant extensions",
			"∀m:num. weighted_multiples(«points», «pointDegree», m) = «count»(m)",
			Derive(func(b *Argument) {
				m := b.FixAs[Nat]("m")
				b.Cases(b.TermAs[Bool]("m = 0"))
				b.When(
					"both vanish at zero",
					func(c *Argument, zero Fact) {
						c.Show(
							"both are defined to be zero there",
							By(zero, weighted_divisors.WeightedMultiplesDef, curve_point_count.CurveExtensionCountDef))
					})
				b.Otherwise(
					"at positive m each sums the degrees of the closed points whose degree divides m",
					func(c *Argument, nonzero Fact) {
						dividing := c.Have(
							"the points of weight dividing m are the closed points of degree dividing m",
							"{x:prod(set(A), set(A)) | x ∈ «points» ∧ «pointDegree»(x) ∣ m} = "+
								"{P:prod(set(A), set(A)) | «point»(P) ∧ «pointDegree»(P) ∣ m}",
							BySets())
						c.Show(
							"so the two sums are one",
							By(
								algebraicallyClosed,
								inField,
								curve,
								nonzero,
								dividing,
								nat_order.PosIffNonzero.At(m),
								weighted_divisors.WeightedMultiplesDef,
								curve_point_count.ExtensionCountClosedPoints.Read(M).At(K, k, A0, A1, A01, t, m)))
					})
			}))
		a.Show(
			"the two conjuncts are the Euler-product theorem at the closed points",
			SplitConj(
				Case(
					"the effective counts satisfy the recurrence with the point counts",
					Derive(func(b *Argument) {
						start := b.Have(
							"the zero divisor alone has degree zero, so the series starts at one",
							"«effective»(0) = real_of_num(1)",
							By(weighted.At(b.TermAs[Nat]("0")), weighted_divisors.WeightedCountZero.At(points, degree)))
						convolution := b.Have(
							"n times the effective count at n is the convolution of the point counts with the effective counts",
							"∀n:num. "+
								"    real_of_num(n) * «effective»(n) = "+
								"    module_sum(real_add, "+
								"        &0, "+
								"        {i:num | 0 < i ∧ i ≤ n}, "+
								"        λi:num. real_of_num(«count»(i)) * «effective»(n - i))",
							Derive(func(c *Argument) {
								n := c.FixAs[Nat]("n")
								indices := c.TermAs[Set[Nat]]("{i:num | 0 < i ∧ i ≤ n}")
								finiteIndices := c.Have(
									"finitely many indices stand at or below n",
									"finite({i:num | 0 < i ∧ i ≤ n})",
									BySets(
										num_segment.FiniteBelow.At(n),
										finite_set.FiniteSubset.At(indices, c.TermAs[Set[Nat]]("{x:num | x ≤ n}"))))
								terms := c.Have(
									"term by term the cast convolution is the convolution of the casts",
									"∀i:num. "+
										"    real_of_num(weighted_multiples(«points», «pointDegree», i) * "+
										"        weighted_count(«points», «pointDegree», n - i)) = "+
										"    real_of_num(«count»(i)) * «effective»(int_of_num(n - i))",
									Derive(func(d *Argument) {
										i := d.FixAs[Nat]("i")
										d.Show(
											"the cast of a product is the product of the casts",
											By(counts.At(i), weighted.At(d.TermAs[Nat]("n - i")), real_construction.OfNumMul))
									}))
								castConvolution := c.TermAs[Fun[Nat, Real]](
									"λi:num. " +
										"    real_of_num(weighted_multiples(«points», «pointDegree», i) * " +
										"        weighted_count(«points», «pointDegree», n - i))")
								convolved := c.TermAs[Fun[Nat, Real]]("λi:num. real_of_num(«count»(i)) * «effective»(n - i)")
								c.Show(
									"the natural counting identity, cast to the reals",
									CalcEq(
										Leg(
											c.TermAs[Real]("real_of_num(n) * real_of_num(weighted_count(«points», «pointDegree», n))"),
											"the effective count is the cast of the weighted count",
											By(weighted.At(n))),
										Leg(
											c.TermAs[Real]("real_of_num(n * weighted_count(«points», «pointDegree», n))"),
											"the cast of a product is the product of the casts",
											By(real_construction.OfNumMul.At(n, c.TermAs[Nat]("weighted_count(«points», «pointDegree», n)")))),
										Leg(
											c.TermAs[Real](
												"real_of_num(sum({i:num | 0 < i ∧ i ≤ n}, "+
													"        λi:num. "+
													"            weighted_multiples(«points», «pointDegree», i) * "+
													"            weighted_count(«points», «pointDegree», n - i)))"),
											"the recurrence of the weighted count",
											By(finiteLevels, weighted_divisors.WeightedCountRecurrence.At(points, degree, n))),
										Leg(
											c.TermAs[Real](
												"sum({i:num | 0 < i ∧ i ≤ n}, "+
													"    λi:num. "+
													"        real_of_num(weighted_multiples(«points», «pointDegree», i) * "+
													"            weighted_count(«points», «pointDegree», n - i)))"),
											"the cast of a finite sum is the sum of the casts",
											By(
												finiteIndices,
												real_sum.RealOfNatSum.At(
													indices,
													c.TermAs[Fun[Nat, Nat]](
														"λi:num. "+
															"    weighted_multiples(«points», «pointDegree», i) * "+
															"    weighted_count(«points», «pointDegree», n - i)")))),
										Leg(
											c.TermAs[Real](
												"sum({i:num | 0 < i ∧ i ≤ n}, λi:num. real_of_num(«count»(i)) * «effective»(n - i))"),
											"the two sums agree term by term",
											By(terms, real_sum.CongruenceEverywhere.At(indices, castConvolution, convolved))),
										FinalLeg(
											"a finite real sum is the fold at real addition",
											By(finiteIndices, real_sum.RealModuleSum.At(convolved, indices)))))
							}))
						b.Show(
							"these are the clauses of the recurrence at the ring of reals",
							Simp(
								Fwd(formal_series.SeriesRecurrenceDef),
								Fwd(real_ring.RealRingDef),
								Fwd(real_ring.AddPowOne),
								Fwd(set_basic.InUniv)),
							By(start, convolution, curve_point_count.CurveExtensionCountDef))
					})),
				Case(
					"each effective count is its coefficient in the Euler product",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.Show(
							"the closed points of degree at most n are a level of "+
								"the weight, where the product computes the weighted count",
							levels.At(n).RwRev(),
							By(weighted.At(n), finiteLevels, weighted_divisors.WeightedCountProduct.At(points, degree, n)))
					}))))
	}),
})}
