// duality.go — duality on the line by coefficient extraction: a map φ
// from a lattice pair M into O(−2) gives the functional on H¹(M) that
// reads the coefficient of t⁻¹ in φ, k-linear in φ; a functional u on
// H¹(M) gives back the map x ↦ Σ u([t^(−m−1) · x]) · tᵐ, a map of lattice
// pairs into O(−2); the two are inverse to each other for every lattice
// pair on the line, which is Serre duality on the line, and the line's
// genus and dualizing pair are read off it.

package projective_line_duality

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/laurent_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_map"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The functional of a map into O(−2)
// ---------------------------------------------------------------------------

// DualityMapKillsLattice — a map of lattice pairs into O(−2) has no
// coefficient at t⁻¹ on fst(M) + snd(M), so the coefficient of t⁻¹ is
// well defined on H¹(M): φ carries the chart sum of M into the chart sum
// of O(−2) (lattice_pair_map.PairMapChartSum), which has no coefficient
// strictly between −2 and 0 (projective_line.LineChartSumCoefficients).
var DualityMapKillsLattice = dualityMapKillsLatticeThm{family.Add(registry.ProofEntry{
	Name: "DualityMapKillsLattice",
	Key:  "prop_82c5a8daf8839d0b",
	Reading: "Transcendence is what makes the coefficient of t⁻¹ a function of φ(x): " +
		"for t algebraic a Laurent polynomial has many expansions. O(−2) is the one twist " +
		"whose chart sum misses t⁻¹ and nothing else, which is why it is the dualizing pair.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀φ:(B → A). " +
			"∀x:B.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"«plPairOnLine»",
			"φ ∈ «plMaps»",
			"x ∈ set_mul(V.add, fst(M), snd(M))",
		},
		Conclusion: "laurent_polynomial_coefficient(k, t, φ(x), -&1) = L.zero",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			φ *Arrow[B, A],
			x *Expr[B],
			h Fact,
		) {
			parts := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k",
				"M is a lattice pair on the line",
				"φ is a map of lattice pairs from M into O(−2)",
				"x lies in fst(M) + snd(M)")
			tm := a.MemberOf[on.L](t, parts[1])
			inChartSum := a.Have(
				"φ, a map of lattice pairs, carries x into the chart sum k[t] + t⁻² · k[1/t] of O(−2)",
				"φ(x) ∈ set_mul(L.add, fst(«plDualizing»), snd(«plDualizing»))",
				By(
					parts[3],
					parts[4],
					parts[5],
					lattice_pair_map.PairMapChartSum.At(
						a.TermAs[module_record.RingOps[A]]("«plRing»"),
						a.TermAs[Set[A]]("«plChart0»"),
						a.TermAs[Set[A]]("«plChart1»"),
						V,
						a.TermAs[ModuleOps[A, A]]("«plField»"),
						M,
						a.TermAs[Prod[Set[A], Set[A]]]("«plDualizing»"),
						φ,
						x)))
			a.Show(
				"which has no coefficient at t⁻¹, as −2 < −1 < 0",
				By(
					parts[0],
					parts[2],
					inChartSum,
					projective_line.LineChartSumCoefficients.Read(L).At(
						k, tm, a.TermAs[Int]("-&2"), a.TermAs[Int]("-&1"), φ.Apply(x))))
		}),
})}

// LinePairMapAmbient — a map of lattice pairs from M into O(n) carries the
// ambient of M into k[t, 1/t]: it carries the ambient of M into the ambient
// of O(n) (lattice_pair_map.PairMapAmbient), which is the overlap
// (projective_line.LinePairAmbient).
var LinePairMapAmbient = linePairMapAmbientThm{family.Add(registry.ProofEntry{
	Name: "LinePairMapAmbient",
	Key:  "prop_37d135a2578d3d99",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀n:int. " +
			"∀φ:(B → A). " +
			"∀x:B.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"«plPairOnLine»",
			"φ ∈ «linePairMapAmbientMaps»",
			"x ∈ «plAmbient»",
		},
		Conclusion: "φ(x) ∈ «plOverlap»",
		Abbrev: Abbrev{
			{Name: "linePairMapAmbientMaps", Text: "lattice_pair_maps(«plRing», V, M, «plField», «plPairN»)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			n *Expr[Int],
			φ *Arrow[B, A],
			x *Expr[B],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"M is a lattice pair on the line",
				"φ is a map of lattice pairs into O(n)",
				"x lies in the ambient of M")
			subK, tInL, nonzero, pair, isMap, xIn := given[0], given[1], given[2], given[3], given[4], given[5]
			tm := a.MemberOf[on.L](t, tInL)
			into := a.Have(
				"φ, a map of lattice pairs, carries the ambient of M into the ambient of O(n)",
				"image(φ, «plAmbient») ⊆ lattice_pair_ambient(«plRing», «plField», «plPairN»)",
				By(
					pair,
					isMap,
					lattice_pair_map.PairMapAmbient.At(
						a.TermAs[module_record.RingOps[A]]("«plRing»"),
						a.TermAs[Set[A]]("«plChart0»"),
						a.TermAs[Set[A]]("«plChart1»"),
						V,
						a.TermAs[ModuleOps[A, A]]("«plField»"),
						M,
						a.TermAs[Prod[Set[A], Set[A]]]("«plPairN»"),
						φ)))
			ambientN := a.Have(
				"and the ambient of O(n) is the overlap",
				"lattice_pair_ambient(«plRing», «plField», «plPairN») = «plOverlap»",
				By(subK, tInL, nonzero, projective_line.LinePairAmbient.Read(L).At(k, tm, n)))
			intoOverlap := a.Simplified(into, Fwd(ambientN), Fwd(set_image.ImageSubsetIff))
			a.Show(
				"so φ carries x, a member of the ambient of M, into the overlap",
				By(intoOverlap.At(x), xIn))
		}),
})}

// DualityFunctional — for φ a map of lattice pairs into O(−2), the
// functional of φ is a k-linear functional on H¹(M), and at the class of
// x it reads the coefficient of t⁻¹ in φ(x). The map g : x ↦ the
// coefficient of t⁻¹ in φ(x) is k-linear on the ambient, the composite of
// φ, k-linear there (lattice_pair_map.PairMapLinear) with values in the overlap
// (LinePairMapAmbient), and the coefficient, k-linear on the overlap
// (laurent_polynomial.LaurentCoeffLinear); and g kills fst(M) + snd(M)
// (DualityMapKillsLattice), so it induces a k-linear map on the quotient
// H¹(M) (module_homomorphism.InducedMapHom). The functional is that map on
// the classes and zero off them.
var DualityFunctional = dualityFunctionalThm{family.Add(registry.ProofEntry{
	Name: "DualityFunctional",
	Key:  "prop_3983b7266a0b19e9",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀φ:(B → A).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"«plPairOnLine»",
			"φ ∈ «plMaps»",
		},
		Conclusion: "«plFunctional» ∈ «plDualSet» ∧ " +
			"(∀x:B. " +
			"    x ∈ «plAmbient» ⇒ " +
			"    projective_line_duality_map(L, k, t, V, M, φ, left_coset(V.add, x, «plChartSum»)) = " +
			"    laurent_polynomial_coefficient(k, t, φ(x), -&1))",
		Abbrev: Abbrev{
			{Name: "plFunctional", Text: "λX:set(B). projective_line_duality_map(L, k, t, V, M, φ, X)"},
			{Name: "dualityFunctionalCoefficient", Text: "λx:B. " +
				"    laurent_polynomial_coefficient(k, t, φ(x), -&1)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			φ *Arrow[B, A],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k",
				"M is a lattice pair on the line",
				"φ is a map of lattice pairs into O(−2)")
			subK, tInL, transcendental, pair, isMap := given[0], given[1], given[2], given[3], given[4]
			tm := a.MemberOf[on.L](t, tInL)
			nonzero := a.Have(
				"t, transcendental, is not zero",
				"t ≠ L.zero",
				By(subK, transcendental, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			ring, scalars :=
				a.TermAs[module_record.RingOps[A]]("«plRing»"), a.TermAs[module_record.RingOps[A]]("«plScalars»")
			sum := a.TermAs[Set[B]]("«plChartSum»")
			ambientModule := a.TermAs[ModuleOps[A, B]]("«plAmbientModule»")
			scalarModule := a.TermAs[ModuleOps[A, A]]("«plModuleK»")
			h1 := a.TermAs[ModuleOps[A, Set[B]]]("«plH1»")
			coefficientOf := a.TermAs[Fun[B, A]]("«dualityFunctionalCoefficient»")

			// Over k, a subring of both charts, the ambient is a vector space with the
			// chart sum a subspace of it, and the class map onto H¹(M) is k-linear.
			chart0, chart1 := a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»")
			datum := a.Conjuncts(
				a.Have(
					"the line is a biaffine datum with k inside both charts",
					"biaffine(«plRing», «plChart0», «plChart1», t, L.inv(t)) ∧ k ⊆ «plChart0» ∧ k ⊆ «plChart1»",
					By(subK, nonzero, projective_line.LineDatum.Read(L).At(k, tm))),
				"the line is a biaffine datum",
				"k lies in k[t]",
				"k lies in k[1/t]")
			kSubring := a.Have(
				"k is a subring of the overlap",
				"subring(«plRing», k)",
				By(subK, tInL, nonzero, Read(laurent_polynomial.LaurentScalarSubring, L).At(k, t)))
			overK := a.Conjuncts(
				a.Unfolded(a.Have(
					"over k the ambient is a vector space, the chart sum a subspace "+
						"of it, H¹(M) a vector space and the class map onto it k-linear",
					"module_on(«plScalars», «plAmbientModule») ∧ "+
						"submodule(«plScalars», «plAmbientModule», «plChartSum») ∧ "+
						"module_on(«plScalars», «plH1») ∧ "+
						"module_homomorphism(«plScalars», «plAmbientModule», «plH1», coset_map(V.add, «plChartSum»))",
					By(
						datum[0],
						kSubring,
						datum[1],
						datum[2],
						pair,
						lattice_pair.H1OverSubring.At(ring, chart0, chart1, t, a.TermAs[A]("L.inv(t)"), k, V, M))),
					group.CosetMapDef),
				"the ambient is a vector space over k",
				"with the chart sum a k-subspace of it",
				"H¹(M) is a vector space over k",
				"and x ↦ the class of x is k-linear onto it")
			sumInAmbient, projection := overK[1], overK[3]
			inside := a.Conjuncts(
				GroupPremises(given[3], lattice_pair.ChartSumInAmbient.At(ring, chart0, chart1, V, M)),
				"the chart sum lies in the ambient",
				"and holds zero")[0]

			// g : x ↦ the coefficient of t⁻¹ in φ(x) is k-linear on the ambient: φ is
			// k-linear there and carries it into the overlap, a k-subspace of L, on
			// which the coefficient of t⁻¹ is k-linear; g is the one after the other.
			fieldOps, dualizing :=
				a.TermAs[ModuleOps[A, A]]("«plField»"), a.TermAs[Prod[Set[A], Set[A]]]("«plDualizing»")
			minusTwo := a.TermAs[Int]("-&2")
			kLinear := a.Have(
				"φ, a map of lattice pairs, is k-linear on the ambient, k lying in the overlap",
				"module_homomorphism(«plScalars», «plAmbientModule», «plField», φ)",
				By(isMap, kSubring, lattice_pair_map.PairMapLinear.At(ring, k, V, fieldOps, M, dualizing, φ)))
			intoOverlap := a.Have(
				"φ carries the ambient into the overlap",
				"∀x:B. x ∈ «plAmbient» ⇒ φ(x) ∈ «plOverlap»",
				Derive(func(b *Argument) {
					x := b.FixAs[B]()
					xIn := b.Assume()
					b.Show(
						"a map into O(−2) carries the ambient into the overlap",
						By(subK, nonzero, pair, isMap, xIn, LinePairMapAmbient.Read(L).At(k, tm, V, M, minusTwo, φ, x)))
				}))
			dualizingPair := a.Have(
				"O(−2) is a lattice pair on the line",
				"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plDualizing»)",
				By(subK, tInL, nonzero, projective_line.LinePairIsLattice.Read(L).At(k, tm, minusTwo)))
			ambientD := a.Have(
				"whose ambient is the overlap",
				"lattice_pair_ambient(«plRing», «plField», «plDualizing») = «plOverlap»",
				By(subK, tInL, nonzero, projective_line.LinePairAmbient.Read(L).At(k, tm, minusTwo)))
			overlapOverK := a.Conjuncts(
				a.Simplified(
					GroupPremises(
						given[0],
						nonzero,
						dualizingPair,
						projective_line.LineH1Module.Read(L).At(k, tm, fieldOps, dualizing)),
					Fwd(ambientD)),
				"so the overlap is a k-subspace of L",
				"and so is the chart sum of O(−2)",
				"which lies in the overlap",
				"and H¹(O(−2)) is a vector space over k")[0]
			corestricted := a.Have(
				"so φ is a k-linear map from the ambient into the overlap",
				"module_homomorphism(«plScalars», «plAmbientModule», restrict_module(«plField», «plOverlap»), φ)",
				By(
					kLinear,
					overlapOverK,
					intoOverlap,
					module_homomorphism.HomCorestrict.At(
						scalars, ambientModule, fieldOps, φ, a.TermAs[Set[A]]("«plOverlap»"))))
			coefficient := a.Have(
				"the coefficient of t⁻¹ is a k-linear map from the overlap to k",
				"module_homomorphism(«plScalars», "+
					"    restrict_module(«plField», «plOverlap»), "+
					"    «plModuleK», "+
					"    λf:A. laurent_polynomial_coefficient(k, t, f, -&1))",
				By(
					subK,
					transcendental,
					laurent_polynomial.LaurentCoeffLinear.Read(L).At(k, tm, a.TermAs[Int]("-&1")),
					module_record.RestrictRingDef.At(ring, k),
					module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("field_ring(L)"), k)))
			composite := a.Have(
				"so g, the coefficient of t⁻¹ after φ, is a k-linear map from the ambient to k",
				"module_homomorphism(«plScalars», "+
					"    «plAmbientModule», "+
					"    «plModuleK», "+
					"    (λf:A. laurent_polynomial_coefficient(k, t, f, -&1)) ∘ φ)",
				By(
					corestricted,
					coefficient,
					module_homomorphism.HomCompose.At(
						scalars,
						ambientModule,
						a.TermAs[ModuleOps[A, A]]("restrict_module(«plField», «plOverlap»)"),
						scalarModule,
						φ,
						a.TermAs[Fun[A, A]]("λf:A. laurent_polynomial_coefficient(k, t, f, -&1)"))))
			gLinear := a.Simplified(composite, Fwd(functions.ComposeApply))

			// g kills the chart sum, so it induces a k-linear map on H¹(M).
			kills := a.Have(
				"g kills fst(M) + snd(M), which lies in the ambient",
				"«plChartSum» ⊆ group_kernel(L.zero, «plAmbient», «dualityFunctionalCoefficient»)",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					w := b.FixAs[B]("w")
					wIn := b.Assume()
					inAmbient := b.Have(
						"w lies in the ambient",
						"w ∈ «plAmbient»",
						BySets(wIn, inside))
					killed := b.Have(
						"φ(w) has no coefficient at t⁻¹",
						"laurent_polynomial_coefficient(k, t, φ(w), -&1) = L.zero",
						By(subK, transcendental, pair, isMap, wIn, DualityMapKillsLattice.Read(L).At(k, tm, V, M, φ, w)))
					b.Show(
						"so w lies in the kernel of g",
						Simp(Fwd(group_homomorphism.GroupKernelDef)),
						BySets(inAmbient, killed))
				}))
			induced := a.Conjuncts(
				a.Have(
					"so g induces a k-linear map on H¹(M), the ambient "+
						"modulo the chart sum, reading g(x) at the class of x",
					"module_homomorphism(«plScalars», "+
						"    «plH1», "+
						"    «plModuleK», "+
						"    induced_map(«dualityFunctionalCoefficient»)) ∧ "+
						"(∀x:B. "+
						"    x ∈ «plAmbient» ⇒ "+
						"    induced_map(«dualityFunctionalCoefficient», left_coset(V.add, x, «plChartSum»)) = "+
						"    laurent_polynomial_coefficient(k, t, φ(x), -&1))",
					Simp(Fwd(lattice_pair.LatticePairH1Def)),
					By(
						sumInAmbient,
						gLinear,
						kills,
						module_homomorphism.InducedMapHom.At(scalars, ambientModule, scalarModule, sum, coefficientOf))),
				"the induced map is k-linear on H¹(M)",
				"and reads g at each class")

			// The functional is the induced map on the classes and zero off them.
			onClasses := a.Have(
				"on a class X of H¹(M) the functional reads g at the chosen member of X, as the induced map does",
				Statement{
					Binders: "∀X:set(B).",
					Hypotheses: []string{
						"X ∈ «plClasses»",
					},
					Conclusion: "projective_line_duality_map(L, k, t, V, M, φ, X) = " +
						"induced_map(«dualityFunctionalCoefficient», X)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[B]]()
					isClass := b.Assume()
					b.Show(
						"the definition's condition holds",
						Simp(Fwd(ProjectiveLineDualityMapDef), Fwd(equivalence.InducedMapDef)),
						By(isClass))
				}))
			offClasses := a.Have(
				"off the classes the functional is zero",
				"∀X:set(B). X ∉ «plClasses» ⇒ projective_line_duality_map(L, k, t, V, M, φ, X) = L.zero",
				Derive(func(b *Argument) {
					b.FixAs[Set[B]]()
					notClass := b.Assume()
					b.Show(
						"the definition's condition fails",
						Simp(Fwd(ProjectiveLineDualityMapDef)),
						By(notClass))
				}))
			functional := a.TermAs[Fun[Set[B], A]]("«plFunctional»")
			onH1 := a.Have(
				"so the functional is k-linear on H¹(M)",
				"module_homomorphism(«plScalars», «plH1», «plModuleK», «plFunctional»)",
				By(
					induced[0],
					onClasses,
					module_homomorphism.HomCongruence.At(
						scalars,
						h1,
						scalarModule,
						a.TermAs[Fun[Set[B], A]]("induced_map(«dualityFunctionalCoefficient»)"),
						functional)))
			inDual := a.Have(
				"and, zero off the classes, it lies in the k-dual of H¹(M)",
				"«plFunctional» ∈ «plDualSet»",
				By(onH1, offClasses, hom_module.InHomSet.At(scalars, h1, scalarModule, functional)))

			// At the class of x it reads the coefficient of t⁻¹ in φ(x).
			atClass := a.Have(
				"at the class of a member x of the ambient the functional reads the coefficient of t⁻¹ in φ(x)",
				Statement{
					Binders: "∀x:B.",
					Hypotheses: []string{
						"x ∈ «plAmbient»",
					},
					Conclusion: "projective_line_duality_map(L, k, t, V, M, φ, left_coset(V.add, x, «plChartSum»)) = " +
						"laurent_polynomial_coefficient(k, t, φ(x), -&1)",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[B]()
					xIn := b.Assume()
					class := b.TermAs[Set[B]]("«plClass»")
					isClass := b.Have(
						"the class of x is a class of H¹(M)",
						"«plClass» ∈ «plClasses»",
						By(module_homomorphism.HomIn.Read(projection).At(proof.MemberOf(x, xIn))))
					b.Show(
						"the functional is the induced map there, which reads g at x",
						GroupPremises(isClass, onClasses.At(class)).Rw(),
						By(induced[1].At(x), xIn, isClass))
				}))
			a.Show(
				"the functional lies in the dual and reads the coefficient of t⁻¹ at each class",
				By(inDual, atClass))
		}),
})}

// DualityMapLinear — the functional of a map into O(−2) is a k-linear
// functional on H¹(M), and it depends k-linearly on the map. Both sides are
// vector spaces over k (lattice_pair_map.PairMapsLinearSpace,
// hom_module.HomSetModuleOn), each functional lies in the dual
// (DualityFunctional), and the dependence on φ is checked one class at a time:
// a class X of H¹(M) is the class of a member x of the ambient, the functional
// of φ reads the coefficient of t⁻¹ in φ(x) there, and that coefficient is
// k-linear in φ(x) (laurent_polynomial.LaurentCoeffLinear); off the classes
// every functional is zero.
var DualityMapLinear = dualityMapLinearThm{family.Add(registry.ProofEntry{
	Name: "DualityMapLinear",
	Key:  "prop_e4f51246278e226b",
	Reading: "Transcendence enters only through the coefficient of t⁻¹, which " +
		"the functional reads. The linearity is over k and not over the overlap: " +
		"fst(M) + snd(M), the zero of H¹(M), is stable only under k[t] ∩ k[1/t] = k.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"«plPairOnLine»",
		},
		Conclusion: "module_homomorphism(«plScalars», " +
			"    lattice_pair_hom(«plRing», V, M, «plField», «plDualizing»), " +
			"    «plDualModule», " +
			"    «plDuality»)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k",
				"M is a lattice pair on the line")
			subK, tInL, transcendental, pair := given[0], given[1], given[2], given[3]
			tm := a.MemberOf[on.L](t, tInL)
			nonzero := a.Have(
				"t, transcendental, is not zero",
				"t ≠ L.zero",
				By(subK, transcendental, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			ring, scalars :=
				a.TermAs[module_record.RingOps[A]]("«plRing»"), a.TermAs[module_record.RingOps[A]]("«plScalars»")
			chart0, chart1 := a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»")
			ambient, sum := a.TermAs[Set[B]]("«plAmbient»"), a.TermAs[Set[B]]("«plChartSum»")
			scalarModule := a.TermAs[ModuleOps[A, A]]("«plModuleK»")
			h1 := a.TermAs[ModuleOps[A, Set[B]]]("«plH1»")
			minusTwo := a.TermAs[Int]("-&2")

			// Hom(M, O(−2)) and the dual of H¹(M) are vector spaces over k.
			subfield := a.Conjuncts(
				a.Have(
					"k is a field lying in L",
					"k ⊆ L.carrier ∧ field_on(restrict_field(L, k))",
					By(subK, field.SubfieldFieldOn.Read(L).At(k))),
				"k lies in L",
				"k is a field")
			datum := a.Simplified(GroupPremises(given[0], nonzero, projective_line.LineDatum.Read(L).At(k, tm)))
			kInCharts := a.Conjuncts(
				a.Have(
					"k lies in both charts",
					"k ⊆ «plChart0» ∧ k ⊆ «plChart1»",
					By(datum)),
				"k lies in k[t]",
				"k lies in k[1/t]")
			dualizing := a.Have(
				"O(−2) is a lattice pair on the line",
				"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plDualizing»)",
				By(subK, tInL, nonzero, projective_line.LinePairIsLattice.Read(L).At(k, tm, minusTwo)))
			kSubring := a.Have(
				"k is a subring of the overlap",
				"subring(«plRing», k)",
				By(subK, tInL, nonzero, Read(laurent_polynomial.LaurentScalarSubring, L).At(k, t)))
			mapsSpace := a.Have(
				"the maps of lattice pairs from M into O(−2) are a vector space over k",
				"module_on(«plScalars», lattice_pair_hom(«plRing», V, M, «plField», «plDualizing»))",
				By(
					datum,
					kSubring,
					kInCharts[0],
					kInCharts[1],
					pair,
					dualizing,
					lattice_pair_map.PairMapsLinearSpace.At(
						ring,
						chart0,
						chart1,
						k,
						V,
						a.TermAs[ModuleOps[A, A]]("«plField»"),
						M,
						a.TermAs[Prod[Set[A], Set[A]]]("«plDualizing»"))))
			h1Space := a.Have(
				"H¹(M) is a vector space over k",
				"module_on(«plScalars», «plH1»)",
				By(subK, nonzero, pair, projective_line.LineH1Module.Read(L).At(k, tm, V, M)))
			coefficient := a.Have(
				"the coefficient of t⁻¹ is a k-linear map from the overlap to k",
				"module_homomorphism(«plRingK», "+
					"    «plOverlapModule», "+
					"    «plModuleK», "+
					"    λf:A. laurent_polynomial_coefficient(k, t, f, -&1))",
				By(
					subK,
					transcendental,
					laurent_polynomial.LaurentCoeffLinear.Read(L).At(k, tm, a.TermAs[Int]("-&1"))))
			scalarSpace := a.Have(
				"k is a vector space over itself",
				"module_on(«plScalars», «plModuleK»)",
				By(
					module_homomorphism.HomTarget.Read(coefficient),
					module_record.RestrictRingDef.At(ring, k),
					module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("field_ring(L)"), k)))
			dualSpace := a.Have(
				"so is the k-dual of H¹(M)",
				"module_on(«plScalars», «plDualModule»)",
				By(h1Space, scalarSpace, hom_module.HomSetModuleOn.At(scalars, h1, scalarModule)))

			// Each map gives a functional, and its value at a class is read off one member.
			into := a.Have(
				"the functional of a map into O(−2) lies in the dual",
				Statement{
					Binders: "∀φ:(B → A).",
					Hypotheses: []string{
						"φ ∈ «plMaps»",
					},
					Conclusion: "(λX:set(B). projective_line_duality_map(L, k, t, V, M, φ, X)) ∈ «plDualSet»",
				},
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[B, A]]()
					isMap := b.Assume()
					b.Show(
						"the functional of φ lies in the dual",
						By(subK, transcendental, pair, isMap, DualityFunctional.Read(L).At(k, tm, V, M, φ)))
				}))
			reads := a.Have(
				"at the class of x the functional of a map φ into O(−2) reads the coefficient of t⁻¹ in φ(x)",
				Statement{
					Binders: "∀φ:(B → A). ∀x:B.",
					Hypotheses: []string{
						"φ ∈ «plMaps»",
						"x ∈ «plAmbient»",
					},
					Conclusion: "projective_line_duality_map(L, k, t, V, M, φ, left_coset(V.add, x, «plChartSum»)) = " +
						"laurent_polynomial_coefficient(k, t, φ(x), -&1)",
				},
				Derive(func(b *Argument) {
					φ, x := b.FixAs[Fun[B, A]](), b.FixAs[B]()
					in := b.Conjuncts(
						b.Assume(),
						"φ is a map into O(−2)",
						"x lies in the ambient")
					functional := b.Conjuncts(
						GroupPremises(given[0], given[2], given[3], in[0], DualityFunctional.Read(L).At(k, tm, V, M, φ)),
						"the functional of φ lies in the dual",
						"and reads φ at each class")
					b.Show(
						"and reads φ at the class of x",
						By(functional[1].At(x), in[1]))
				}))
			intoOverlap := a.Have(
				"a map into O(−2) carries the ambient into the overlap",
				"∀φ:(B → A). ∀x:B. φ ∈ «plMaps» ∧ x ∈ «plAmbient» ⇒ φ(x) ∈ «plOverlap»",
				Derive(func(b *Argument) {
					φ, x := b.FixAs[Fun[B, A]](), b.FixAs[B]()
					in := b.Assume()
					b.Show(
						"as a map into any O(n) does",
						By(subK, nonzero, pair, in, LinePairMapAmbient.Read(L).At(k, tm, V, M, minusTwo, φ, x)))
				}))
			offClasses := a.Have(
				"off the classes every functional is zero",
				Statement{
					Binders: "∀φ:(B → A). ∀X:set(B).",
					Hypotheses: []string{
						"X ∉ «plClasses»",
					},
					Conclusion: "projective_line_duality_map(L, k, t, V, M, φ, X) = L.zero",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[B, A]]()
					b.FixAs[Set[B]]()
					notClass := b.Assume()
					b.Show(
						"the definition's condition fails",
						Simp(Fwd(ProjectiveLineDualityMapDef)),
						By(notClass))
				}))

			// A class of H¹(M) is the class of a member of the ambient.
			ambientFacts := a.Conjuncts(
				a.Have(
					"the ambient is a submodule of V over the overlap, holding chart 0 + chart 1",
					"submodule(«plRing», V, «plAmbient») ∧ «plChartSum» ⊆ «plAmbient»",
					By(
						pair,
						lattice_pair.AmbientContains.At(ring, chart0, chart1, V, M),
						lattice_pair.ChartSumInAmbient.At(ring, chart0, chart1, V, M))),
				"the ambient is a submodule over the overlap",
				"chart 0 + chart 1 lies in the ambient")
			overOverlap := a.Have(
				"V is a module over the overlap",
				"module_on(«plRing», V)",
				By(pair, lattice_pair.PairModuleOn))
			ambientModule := a.Have(
				"so the ambient is a module over the overlap in its own right",
				"module_on(«plRing», «plAmbientModule»)",
				By(ambientFacts[0], submodule.SubmoduleModuleOn.Read(overOverlap).At(ambient)))
			representatives := a.Have(
				"every class of H¹(M) is the class of a member of the ambient",
				"∀X:set(B). X ∈ «plClasses» ⇒ ∃x:B. X = left_coset(V.add, x, «plChartSum») ∧ x ∈ «plAmbient»",
				Derive(func(b *Argument) {
					X := b.FixAs[Set[B]]()
					isClass := b.Assume()
					b.Show(
						"a left coset of the chart sum in the ambient's group",
						By(
							isClass,
							ambientFacts[1],
							quotient_group.InLeftCosets.Read(module.AddGroupOn.Read(ambientModule)).At(sum, X)))
				}))

			// The functional of a sum is the sum of the functionals.
			additive := a.Have(
				"the functional of φ + ψ is the sum of the functionals of φ and ψ",
				Statement{
					Binders: "∀φ ψ:(B → A).",
					Hypotheses: []string{
						"φ ∈ «plMaps»",
						"ψ ∈ «plMaps»",
					},
					Conclusion: "(λX:set(B). projective_line_duality_map(L, k, t, V, M, fun_add(φ, ψ), X)) = " +
						"fun_add(λX:set(B). projective_line_duality_map(L, k, t, V, M, φ, X), " +
						"    λX:set(B). projective_line_duality_map(L, k, t, V, M, ψ, X))",
				},
				Derive(func(b *Argument) {
					φ, ψ := b.FixAs[Fun[B, A]](), b.FixAs[Fun[B, A]]()
					maps := b.Conjuncts(
						b.Assume(),
						"φ is a map into O(−2)",
						"ψ is a map into O(−2)")
					sumMap := b.TermAs[Fun[B, A]]("fun_add(φ, ψ)")
					pointwise := b.Have(
						"at every X the functional of φ + ψ is the sum",
						"∀X:set(B). "+
							"    projective_line_duality_map(L, k, t, V, M, fun_add(φ, ψ), X) = "+
							"    projective_line_duality_map(L, k, t, V, M, φ, X) + "+
							"    projective_line_duality_map(L, k, t, V, M, ψ, X)",
						Derive(func(c *Argument) {
							X := c.FixAs[Set[B]]()
							c.Cases(c.Term("X ∈ «plClasses»"))
							c.When(
								"on the class of a member x of the ambient each functional reads its map at x",
								func(d *Argument, isClass Fact) {
									x, member := d.ObtainAs[B](
										"X is the class of some x in the ambient",
										"∃x:B. X = left_coset(V.add, x, «plChartSum») ∧ x ∈ «plAmbient»",
										By(representatives.At(X), isClass))
									rep := d.Conjuncts(
										member,
										"X is the class of x",
										"x lies in the ambient")
									atSum := d.Have(
										"the functional of φ + ψ reads (φ + ψ)(x)",
										"projective_line_duality_map(L, k, t, V, M, fun_add(φ, ψ), «plClass») = "+
											"laurent_polynomial_coefficient(k, t, fun_add(φ, ψ, x), -&1)",
										By(
											reads.At(sumMap, x),
											group.MulIn.Read(module.AddGroupOn.Read(mapsSpace)).At(
												proof.MemberOf(φ, maps[0]), proof.MemberOf(ψ, maps[1])),
											rep[1]))
									atφ := d.Have(
										"the functional of φ reads φ(x)",
										"projective_line_duality_map(L, k, t, V, M, φ, «plClass») = "+
											"laurent_polynomial_coefficient(k, t, φ(x), -&1)",
										By(reads.At(φ, x), maps[0], rep[1]))
									atψ := d.Have(
										"the functional of ψ reads ψ(x)",
										"projective_line_duality_map(L, k, t, V, M, ψ, «plClass») = "+
											"laurent_polynomial_coefficient(k, t, ψ(x), -&1)",
										By(reads.At(ψ, x), maps[1], rep[1]))
									φx := proof.MemberOf(d.TermAs[A]("φ(x)"), d.Have(
										"φ(x) lies in the overlap",
										"φ(x) ∈ «plOverlap»",
										By(maps[0], rep[1], intoOverlap.At(φ, x))))
									ψx := proof.MemberOf(d.TermAs[A]("ψ(x)"), d.Have(
										"ψ(x) lies in the overlap",
										"ψ(x) ∈ «plOverlap»",
										By(maps[1], rep[1], intoOverlap.At(ψ, x))))
									d.Show(
										"and the coefficient of t⁻¹ is additive on the overlap",
										rep[0].Rw(),
										atSum.Rw(),
										atφ.Rw(),
										atψ.Rw(),
										Simp(Fwd(function_module.FunAddDef)),
										By(module_homomorphism.HomAdd.Read(coefficient).At(φx, ψx)))
								})
							c.Otherwise(
								"off the classes all three functionals are zero",
								func(d *Argument, notClass Fact) {
									d.Show(
										"and zero is zero + zero",
										GroupPremises(notClass, offClasses.At(sumMap, X)).Rw(),
										GroupPremises(notClass, offClasses.At(φ, X)).Rw(),
										GroupPremises(notClass, offClasses.At(ψ, X)).Rw(),
										ByArith(field.RingOn.Read(L)))
								})
						}))
					b.Show(
						"so the two functionals are one function",
						Funext(),
						SimpAll(Fwd(function_module.FunAddDef)),
						By(pointwise))
				}))

			// The functional of a k-multiple is the multiple of the functional.
			homogeneous := a.Have(
				"the functional of c · φ is c times the functional of φ",
				Statement{
					Binders: "∀c:A. ∀φ:(B → A).",
					Hypotheses: []string{
						"c ∈ k",
						"φ ∈ «plMaps»",
					},
					Conclusion: "(λX:set(B). projective_line_duality_map(L, k, t, V, M, fun_smul(c, φ), X)) = " +
						"fun_smul(c, λX:set(B). projective_line_duality_map(L, k, t, V, M, φ, X))",
				},
				Derive(func(b *Argument) {
					c, φ := b.FixAs[A](), b.FixAs[Fun[B, A]]()
					in := b.Conjuncts(
						b.Assume(),
						"c lies in k",
						"φ is a map into O(−2)")
					cInL := b.Have(
						"c lies in L",
						"c ∈ L.carrier",
						BySets(in[0], subfield[0]))
					multiple := b.TermAs[Fun[B, A]]("fun_smul(c, φ)")
					pointwise := b.Have(
						"at every X the functional of c · φ is c times that of φ",
						"∀X:set(B). "+
							"    projective_line_duality_map(L, k, t, V, M, fun_smul(c, φ), X) = "+
							"    c * projective_line_duality_map(L, k, t, V, M, φ, X)",
						Derive(func(d *Argument) {
							X := d.FixAs[Set[B]]()
							d.Cases(d.Term("X ∈ «plClasses»"))
							d.When(
								"on the class of a member x of the ambient both functionals read their maps at x",
								func(e *Argument, isClass Fact) {
									x, member := e.ObtainAs[B](
										"X is the class of some x in the ambient",
										"∃x:B. X = left_coset(V.add, x, «plChartSum») ∧ x ∈ «plAmbient»",
										By(representatives.At(X), isClass))
									rep := e.Conjuncts(
										member,
										"X is the class of x",
										"x lies in the ambient")
									atMultiple := e.Have(
										"the functional of c · φ reads (c · φ)(x)",
										"projective_line_duality_map(L, k, t, V, M, fun_smul(c, φ), «plClass») = "+
											"laurent_polynomial_coefficient(k, t, fun_smul(c, φ, x), -&1)",
										By(
											reads.At(multiple, x),
											module.SmulIn.Read(mapsSpace).At(proof.MemberOf(c, in[0]), proof.MemberOf(φ, in[1])),
											rep[1]))
									atφ := e.Have(
										"the functional of φ reads φ(x)",
										"projective_line_duality_map(L, k, t, V, M, φ, «plClass») = "+
											"laurent_polynomial_coefficient(k, t, φ(x), -&1)",
										By(reads.At(φ, x), in[1], rep[1]))
									φx := proof.MemberOf(e.TermAs[A]("φ(x)"), e.Have(
										"φ(x) lies in the overlap",
										"φ(x) ∈ «plOverlap»",
										By(in[1], rep[1], intoOverlap.At(φ, x))))
									e.Show(
										"and the coefficient of t⁻¹ is k-linear on the overlap",
										rep[0].Rw(),
										atMultiple.Rw(),
										atφ.Rw(),
										Simp(Fwd(function_module.FunSmulDef)),
										By(module_homomorphism.HomSmul.Read(coefficient).At(proof.MemberOf(c, in[0]), φx)))
								})
							d.Otherwise(
								"off the classes both functionals are zero",
								func(e *Argument, notClass Fact) {
									e.Show(
										"and c times zero is zero",
										GroupPremises(notClass, offClasses.At(multiple, X)).Rw(),
										GroupPremises(notClass, offClasses.At(φ, X)).Rw(),
										ByArith(field.RingOn.Read(L), cInL))
								})
						}))
					b.Show(
						"so the two functionals are one function",
						Funext(),
						SimpAll(Fwd(function_module.FunSmulDef)),
						By(pointwise))
				}))

			a.Show(
				"so φ ↦ the functional of φ is a k-linear map from Hom(M, O(−2)) into the k-dual of H¹(M)",
				By(
					mapsSpace,
					dualSpace,
					into,
					additive,
					homogeneous,
					lattice_pair_map.LatticePairHomDef.At(
						ring,
						V,
						M,
						a.TermAs[ModuleOps[A, A]]("«plField»"),
						a.TermAs[Prod[Set[A], Set[A]]]("«plDualizing»")),
					module_homomorphism.ModuleHomomorphismDef))
		}),
})}

// ---------------------------------------------------------------------------
// The map of a functional on H¹
// ---------------------------------------------------------------------------

// DualityKillsChartSum — a k-linear functional u on H¹(M) kills the
// class of every member y of fst(M) + snd(M): that class is fst(M) +
// snd(M) itself, the zero of H¹(M), a submodule of V having the class of
// each of its members as itself (quotient_group.LeftCosetIsSubgroupIffIn),
// and a linear map sends zero to zero (module_homomorphism.HomZero).
var DualityKillsChartSum = dualityKillsChartSumThm{family.Add(registry.ProofEntry{
	Name: "DualityKillsChartSum",
	Key:  "prop_b0bf40ba58f64773",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀u:(set(B) → A). " +
			"∀y:B.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"«plPairOnLine»",
			"u ∈ «plDualSet»",
			"y ∈ set_mul(V.add, fst(M), snd(M))",
		},
		Conclusion: "u(left_coset(V.add, y, set_mul(V.add, fst(M), snd(M)))) = L.zero",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			u *Arrow[Set[B], A],
			y *Expr[B],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"M is a lattice pair on the line",
				"u is a k-linear functional on H¹(M)",
				"y lies in fst(M) + snd(M)")
			subK, tInL, nonzero, pair, dual, yIn := given[0], given[1], given[2], given[3], given[4], given[5]
			tm := a.MemberOf[on.L](t, tInL)
			vectors := a.Have(
				"V is a module over the overlap",
				"module_on(«plRing», V)",
				By(pair, lattice_pair.PairModuleOn))
			sum := a.Have(
				"fst(M) + snd(M) is a k-subspace of V",
				"submodule(«plScalars», V, «plChartSum»)",
				By(subK, tInL, nonzero, pair, projective_line.LineH1Module.Read(L).At(k, tm, V, M)))
			yV := a.Have(
				"y is a vector",
				"y ∈ V.carrier",
				By(yIn, submodule.SubmoduleSubset.Read(sum), set_basic.SubsetDef))
			zeroClass := a.Have(
				"the class of y is fst(M) + snd(M) itself, the zero of H¹(M)",
				"left_coset(V.add, y, «plChartSum») = «plChartSum»",
				By(
					yIn,
					yV,
					quotient_group.LeftCosetIsSubgroupIffIn.Read(module.AddGroupOn.Read(vectors)),
					submodule.SubmoduleSubgroup.Read(sum)))
			linear := a.Have(
				"u is a k-linear map from H¹(M) to k",
				"module_homomorphism(«plScalars», «plH1», restrict_module(regular_module(field_ring(L)), k), u)",
				By(dual, hom_module.InHomSet))
			a.Show(
				"a linear map sends zero to zero",
				By(zeroClass, module_homomorphism.HomZero.Read(linear)))
		}),
})}

// DualityInverseFinite — for a functional u on H¹(M) and x in the ambient, only
// finitely many classes [t^(−m−1) · x] are not killed by u. Over the overlap
// each chart spans the vectors a power of its generator carries into it
// (lattice_pair.ChartSpanAway), and the two spans are the ambient, so t^n₀ · x
// lies in fst(M) and t^(−n₁) · x in snd(M) for some n₀, n₁. Raising the power
// keeps a vector in fst(M) and lowering it keeps it in snd(M)
// (projective_line.LinePairChartPowers): for m < −n₀ the shifted x lies in
// fst(M), for m ≥ n₁ − 1 in snd(M), its class is the zero of H¹(M) either way,
// and u kills it (DualityKillsChartSum). The remaining m lie between −n₀ and n₁
// − 2.
var DualityInverseFinite = dualityInverseFiniteThm{family.Add(registry.ProofEntry{
	Name: "DualityInverseFinite",
	Key:  "prop_1d7afbba7ab8ce29",
	Reading: "Transcendence is not asked, only t ≠ zero, and of u nothing beyond its killing the " +
		"zero class: the bound on the exponents comes from the pair, not from u. For t algebraic and " +
		"nonzero, k[t] = k[1/t] is a field equal to the overlap, so every lattice pair has a single " +
		"class in H¹, every dual vector is zero, and the statement holds trivially; the same holds " +
		"of the other members about the map of a functional that ask only t ≠ zero.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀u:(set(B) → A). " +
			"∀x:B.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"«plPairOnLine»",
			"u ∈ «plDualSet»",
			"x ∈ «plAmbient»",
		},
		Conclusion: "finite(«plShiftedSupport»)",
		Abbrev: Abbrev{
			{Name: "dualityInverseFiniteSpan0", Text: "module_span(«plRing», V, fst(M))"},
			{Name: "dualityInverseFiniteSpan1", Text: "module_span(«plRing», V, snd(M))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			u *Arrow[Set[B], A],
			x *Expr[B],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"M is a lattice pair on the line",
				"u is a k-linear functional on H¹(M)",
				"x lies in the ambient of M")
			subK, tInL, nonzero, pair, dual, xIn := given[0], given[1], given[2], given[3], given[4], given[5]
			tm := a.MemberOf[on.L](t, tInL)
			invT := a.TermAs[A]("L.inv(t)")
			ring := a.TermAs[module_record.RingOps[A]]("«plRing»")
			chart0, chart1 := a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»")
			fstM, sndM := a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)")
			parts := a.Conjuncts(
				a.Unfolded(pair, lattice_pair.LatticePairDef),
				"V is a module over the overlap",
				"fst(M) is a k[t]-submodule of V",
				"snd(M) is a k[1/t]-submodule of V",
				"the two charts span one module over the overlap")
			vectors, sub0, sub1, spans := parts[0], parts[1], parts[2], parts[3]
			biaffine := a.Have(
				"k[t] and k[1/t], glued along the overlap, form a biaffine datum",
				"biaffine(«plRing», «plChart0», «plChart1», t, L.inv(t))",
				By(subK, nonzero, projective_line.ProjectiveLineBiaffine.Read(L).At(k, tm)))

			// Some power of t carries x into fst(M), and some power of inv(t) into snd(M).
			span0 := a.Have(
				"over the overlap, fst(M) spans the vectors that some power of t carries into it",
				"«dualityInverseFiniteSpan0» = "+
					"{v:B | v ∈ V.carrier ∧ (∃n:num. monoid_pow(L.mul, L.one, t, n) • v ∈ fst(M))}",
				By(biaffine, vectors, sub0, lattice_pair.ChartSpanAway.At(ring, chart0, chart1, t, invT, V, fstM)))
			span1 := a.Have(
				"and snd(M) spans those that some power of inv(t) carries into it",
				"«dualityInverseFiniteSpan1» = "+
					"{v:B | v ∈ V.carrier ∧ (∃n:num. monoid_pow(L.mul, L.one, L.inv(t), n) • v ∈ snd(M))}",
				By(
					biaffine,
					lattice_pair.BiaffineSwap,
					vectors,
					sub1,
					lattice_pair.ChartSpanAway.At(ring, chart1, chart0, invT, t, V, sndM)))
			in0 := a.Have(
				"so a vector lies in the span of fst(M) when some power of t carries it into fst(M)",
				"∀v:B. "+
					"    v ∈ «dualityInverseFiniteSpan0» ⇔ "+
					"    v ∈ V.carrier ∧ (∃n:num. monoid_pow(L.mul, L.one, t, n) • v ∈ fst(M))",
				BySets(span0))
			in1 := a.Have(
				"and in the span of snd(M) when some power of inv(t) carries it into snd(M)",
				"∀v:B. "+
					"    v ∈ «dualityInverseFiniteSpan1» ⇔ "+
					"    v ∈ V.carrier ∧ (∃n:num. monoid_pow(L.mul, L.one, L.inv(t), n) • v ∈ snd(M))",
				BySets(span1))
			xIn0 := a.Unfolded(xIn, lattice_pair.LatticePairAmbientDef)
			xIn1 := a.Have(
				"x lies in the span of snd(M) too, the two spans being one",
				"x ∈ «dualityInverseFiniteSpan1»",
				Simp(Rev(spans)),
				By(xIn0))
			xV := a.Have(
				"x is a vector",
				"x ∈ V.carrier",
				By(in0.At(x), xIn0))
			_, into0 := a.ObtainAs[Nat](
				"some power t^n₀ carries x into fst(M)",
				"∃n:num. monoid_pow(L.mul, L.one, t, n) • x ∈ fst(M)",
				By(in0.At(x), xIn0),
				Named("n₀"))
			_, into1 := a.ObtainAs[Nat](
				"and some power inv(t)^n₁ carries it into snd(M)",
				"∃n:num. monoid_pow(L.mul, L.one, L.inv(t), n) • x ∈ snd(M)",
				By(in1.At(x), xIn1),
				Named("n₁"))
			start0 := a.Have(
				"as powers at integer exponents, t^n₀ · x lies in fst(M)",
				"laurent_monomial(t, &n₀) • x ∈ fst(M)",
				Simp(Fwd(laurent_polynomial.LaurentMonomialOfNum)),
				By(into0))
			start1 := a.Have(
				"and t^(−n₁) · x in snd(M)",
				"laurent_monomial(t, -&n₁) • x ∈ snd(M)",
				Simp(Fwd(laurent_polynomial.LaurentMonomialOfNum)),
				By(into1))

			// A member of either chart has the zero class, which u kills.
			kSubring := a.Have(
				"k is a subring of the overlap",
				"subring(«plRing», k)",
				By(subK, tInL, nonzero, Read(laurent_polynomial.LaurentScalarSubring, L).At(k, t)))
			inSum := a.Conjuncts(
				a.Have(
					"each chart lies in fst(M) + snd(M), both being k-subspaces of V",
					"fst(M) ⊆ «plChartSum» ∧ snd(M) ⊆ «plChartSum»",
					By(
						nonzero,
						tInL,
						pair,
						subK,
						kSubring,
						projective_line.LineDatum.Read(L).At(k, tm),
						lattice_pair.PairOverSubring.At(ring, chart0, chart1, t, invT, k, V, M),
						submodule.SumContainsLeft,
						submodule.SumContainsRight)),
				"fst(M) lies in the chart sum",
				"snd(M) lies in the chart sum")
			sum0, sum1 := a.Unfolded(inSum[0], set_basic.SubsetDef), a.Unfolded(inSum[1], set_basic.SubsetDef)
			kills := DualityKillsChartSum.Read(L)

			// Far enough out, the shifted x stays in a chart, so u kills its class.
			belowKilled := a.Have(
				"for m below −n₀, t^(−m−1) · x lies in fst(M), its "+
					"exponent being at least n₀, so u kills its class",
				Statement{
					Binders: "∀m:int.",
					Hypotheses: []string{
						"m < -&n₀",
					},
					Conclusion: "u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»)) = L.zero",
				},
				Derive(func(b *Argument) {
					b.FixAs[Int]("m")
					below := b.Assume()
					far := b.Have(
						"−m − 1 is at least n₀",
						"&n₀ ≤ -m - &1",
						ByArith(below))
					inChart := b.Have(
						"raising the power of t keeps a vector in fst(M)",
						"laurent_monomial(t, -m - &1) • x ∈ fst(M)",
						By(
							subK,
							nonzero,
							pair,
							xV,
							far,
							start0,
							projective_line.LinePairChartPowers.Read(L).At(
								k, tm, V, M, x, b.TermAs[Int]("&n₀"), b.TermAs[Int]("-m - &1"))))
					b.Show(
						"a functional on H¹(M) kills the class of a member of fst(M) + snd(M)",
						By(
							subK,
							nonzero,
							pair,
							dual,
							sum0,
							inChart,
							kills.At(k, tm, V, M, u, b.TermAs[B]("laurent_monomial(t, -m - &1) • x"))))
				}))
			aboveKilled := a.Have(
				"for m from n₁ − 1 on, t^(−m−1) · x lies in snd(M), "+
					"its exponent being at most −n₁, so u kills its class",
				Statement{
					Binders: "∀m:int.",
					Hypotheses: []string{
						"&n₁ - &1 ≤ m",
					},
					Conclusion: "u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»)) = L.zero",
				},
				Derive(func(b *Argument) {
					b.FixAs[Int]("m")
					above := b.Assume()
					far := b.Have(
						"−m − 1 is at most −n₁",
						"-m - &1 ≤ -&n₁",
						ByArith(above))
					inChart := b.Have(
						"lowering the power of t keeps a vector in snd(M)",
						"laurent_monomial(t, -m - &1) • x ∈ snd(M)",
						By(
							subK,
							nonzero,
							pair,
							xV,
							far,
							start1,
							projective_line.LinePairChartPowers.Read(L).At(
								k, tm, V, M, x, b.TermAs[Int]("-m - &1"), b.TermAs[Int]("-&n₁"))))
					b.Show(
						"a functional on H¹(M) kills the class of a member of fst(M) + snd(M)",
						By(
							subK,
							nonzero,
							pair,
							dual,
							sum1,
							inChart,
							kills.At(k, tm, V, M, u, b.TermAs[B]("laurent_monomial(t, -m - &1) • x"))))
				}))

			// The classes u does not kill lie in a bounded interval of integers.
			bounds := a.Have(
				"a class u does not kill has −n₀ ≤ m ≤ n₁ − 2",
				Statement{
					Binders: "∀m:int.",
					Hypotheses: []string{
						"u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»)) ≠ L.zero",
					},
					Conclusion: "-&n₀ ≤ m ∧ m ≤ &n₁ - &2",
				},
				Derive(func(b *Argument) {
					m := b.FixAs[Int]("m")
					alive := b.Assume()
					b.Show(
						"so m is neither below −n₀ nor at least n₁ − 1",
						ByArith(alive, belowKilled.At(m), aboveKilled.At(m)))
				}))
			support := a.Have(
				"so those m lie in the interval from −n₀ to n₁ − 2",
				"«plShiftedSupport» ⊆ {m:int | -&n₀ ≤ m ∧ m ≤ &n₁ - &2}",
				BySets(bounds))
			a.Show(
				"a set of integers inside a bounded interval is finite",
				By(
					support,
					int_embed.IntIntervalSize.At(a.TermAs[Int]("-&n₀"), a.TermAs[Int]("&n₁ - &2")),
					finite_set.FiniteSubset))
		}),
})}

// LaurentMonomialSmulInAmbient — for a lattice pair M on the line, a power tʲ
// of t carries the ambient of M into itself: tʲ lies in the overlap
// (laurent_polynomial.LaurentMonomialInRing), and the ambient is a submodule of
// V over the overlap (lattice_pair.AmbientContains).
var LaurentMonomialSmulInAmbient = laurentMonomialSmulInAmbientThm{family.Add(registry.ProofEntry{
	Name: "LaurentMonomialSmulInAmbient",
	Key:  "prop_3e36ddd6ba67ac5b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀j:int. " +
			"∀x:B.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"«plPairOnLine»",
			"x ∈ «plAmbient»",
		},
		Conclusion: "V.smul(laurent_monomial(t, j), x) ∈ «plAmbient»",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			j *Expr[Int],
			x *Expr[B],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"M is a lattice pair on the line",
				"x lies in the ambient")
			subK, tInL, nonzero, pair, xIn := given[0], given[1], given[2], given[3], given[4]
			tm := a.MemberOf[on.L](t, tInL)
			ring := a.TermAs[module_record.RingOps[A]]("«plRing»")
			ambient := a.TermAs[Set[B]]("«plAmbient»")
			powerIn := a.Have(
				"tʲ lies in the overlap",
				"laurent_monomial(t, j) ∈ «plOverlap»",
				By(subK, tInL, nonzero, laurent_polynomial.LaurentMonomialInRing.Read(L).At(k, tm, j)))
			a.Show(
				"the ambient, a submodule of V over the overlap, holds tʲ · x",
				By(
					powerIn,
					xIn,
					pair,
					lattice_pair.AmbientContains.At(
						ring, a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»"), V, M),
					submodule.SubmoduleSmul.At(ring, V, ambient, a.TermAs[A]("laurent_monomial(t, j)"), x)))
		}),
})}

// DualityFunctionalOnAmbient — a k-linear functional u on H¹(M), read on
// the ambient through the classes, y ↦ u([y]), is a k-linear map from the
// ambient into k: H¹(M) is the ambient modulo chart 0 + chart 1, a
// k-subspace of it, so the class map onto H¹(M) is k-linear
// (lattice_pair.H1OverSubring), and so is u after it.
var DualityFunctionalOnAmbient = dualityFunctionalOnAmbientThm{family.Add(registry.ProofEntry{
	Name: "DualityFunctionalOnAmbient",
	Key:  "prop_4052cdda23853061",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀u:(set(B) → A).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"«plPairOnLine»",
			"u ∈ «plDualSet»",
		},
		Conclusion: "module_homomorphism(«plScalars», " +
			"    «plAmbientModule», " +
			"    restrict_module(regular_module(field_ring(L)), k), " +
			"    «plFunctionalOnAmbient»)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			u *Arrow[Set[B], A],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"M is a lattice pair on the line",
				"u is a k-linear functional on H¹(M)")
			subK, tInL, nonzero, pair, dual := given[0], given[1], given[2], given[3], given[4]
			tm := a.MemberOf[on.L](t, tInL)
			ring, scalars :=
				a.TermAs[module_record.RingOps[A]]("«plRing»"), a.TermAs[module_record.RingOps[A]]("«plScalars»")
			chart0, chart1 := a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»")
			ambientModule := a.TermAs[ModuleOps[A, B]]("«plAmbientModule»")
			h1 := a.TermAs[ModuleOps[A, Set[B]]]("«plH1»")
			scalarModule := a.TermAs[ModuleOps[A, A]]("restrict_module(regular_module(field_ring(L)), k)")

			datum := a.Have(
				"t ≠ zero makes the line a biaffine datum over k",
				"biaffine(«plRing», «plChart0», «plChart1», t, L.inv(t)) ∧ "+
					"k ⊆ «plChart0» ∧ "+
					"k ⊆ «plChart1» ∧ "+
					"«plChart0» ⊆ «plOverlap» ∧ "+
					"«plChart1» ⊆ «plOverlap» ∧ "+
					"subring(field_ring(L), «plChart0») ∧ "+
					"subring(field_ring(L), «plChart1») ∧ "+
					"subring(field_ring(L), «plOverlap») ∧ "+
					"t ∈ «plChart0» ∧ "+
					"L.inv(t) ∈ «plChart1» ∧ "+
					"L.inv(t) ∈ «plOverlap» ∧ "+
					"module_on(«plScalars», «plField») ∧ "+
					"module_on(«plRing0», «plField») ∧ "+
					"module_on(«plRing1», «plField») ∧ "+
					"module_on(«plRing», «plField»)",
				By(subK, nonzero, projective_line.LineDatum.Read(L).At(k, tm)))
			kSubring := a.Have(
				"k is a subring of the overlap",
				"subring(«plRing», k)",
				By(subK, tInL, nonzero, Read(laurent_polynomial.LaurentScalarSubring, L).At(k, t)))
			classes := a.Unfolded(a.Have(
				"over k, a subring of both charts, the class map y ↦ [y] "+
					"onto H¹(M), the ambient modulo chart 0 + chart 1, is k-linear",
				"module_homomorphism(«plScalars», "+
					"    «plAmbientModule», "+
					"    «plH1», "+
					"    coset_map(V.add, set_mul(V.add, fst(M), snd(M))))",
				By(
					datum,
					pair,
					kSubring,
					lattice_pair.H1OverSubring.At(ring, chart0, chart1, t, a.TermAs[A]("L.inv(t)"), k, V, M))),
				group.CosetMapDef)
			classMap := a.TermAs[Fun[B, Set[B]]]("λy:B. left_coset(V.add, y, set_mul(V.add, fst(M), snd(M)))")
			composite := a.Have(
				"u, k-linear on H¹(M), stays so after the class map",
				"module_homomorphism(«plScalars», "+
					"    «plAmbientModule», "+
					"    restrict_module(regular_module(field_ring(L)), k), "+
					"    u ∘ λy:B. left_coset(V.add, y, set_mul(V.add, fst(M), snd(M))))",
				By(
					classes,
					dual,
					hom_module.InHomSet.At(scalars, h1, scalarModule, u),
					module_homomorphism.HomCompose.At(scalars, ambientModule, h1, scalarModule, classMap, u)))
			a.Show(
				"which is y ↦ u([y])",
				By(a.Simplified(composite, Fwd(functions.ComposeApply))))
		}),
})}

// DualityInverseExpansion — on the ambient, the map of a functional u at x
// is the finite expansion Σ u([t^(−m−1) · x]) · tᵐ with coefficients in k:
// each t^(−m−1) · x lies in the ambient, an overlap-submodule of V, so its
// class is read by y ↦ u([y]) into k (DualityFunctionalOnAmbient), only
// finitely many of them are not zero (DualityInverseFinite), and on the
// ambient the definition's condition picks the sum.
var DualityInverseExpansion = dualityInverseExpansionThm{family.Add(registry.ProofEntry{
	Name: "DualityInverseExpansion",
	Key:  "prop_624e1bfaddb3d77d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀u:(set(B) → A). " +
			"∀x:B.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"«plPairOnLine»",
			"u ∈ «plDualSet»",
			"x ∈ «plAmbient»",
		},
		Conclusion: "finite(«plShiftedSupport») ∧ " +
			"(∀m:int. u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»)) ∈ k) ∧ " +
			"«plInverseAtX»(x) = «plShiftedExpansion»",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			u *Arrow[Set[B], A],
			x *Expr[B],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"M is a lattice pair on the line",
				"u is a k-linear functional on H¹(M)",
				"x lies in the ambient")
			subK, tInL, nonzero, pair, dual, xIn := given[0], given[1], given[2], given[3], given[4], given[5]
			tm := a.MemberOf[on.L](t, tInL)
			scalars := a.TermAs[module_record.RingOps[A]]("«plScalars»")
			ambientModule := a.TermAs[ModuleOps[A, B]]("«plAmbientModule»")
			scalarModule := a.TermAs[ModuleOps[A, A]]("restrict_module(regular_module(field_ring(L)), k)")
			functionalMap := a.TermAs[Fun[B, A]]("«plFunctionalOnAmbient»")

			functional := a.Have(
				"y ↦ u([y]) is a k-linear map from the ambient into k",
				"module_homomorphism(«plScalars», "+
					"    «plAmbientModule», "+
					"    restrict_module(regular_module(field_ring(L)), k), "+
					"    «plFunctionalOnAmbient»)",
				By(subK, nonzero, pair, dual, DualityFunctionalOnAmbient.Read(L).At(k, tm, V, M, u)))
			values := a.Have(
				"each coefficient u([t^(−m−1) · x]) lies in k, t^(−m−1) · x lying in the ambient",
				"∀m:int. u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»)) ∈ k",
				Derive(func(b *Argument) {
					b.FixAs[Int]("m")
					shifted := b.TermAs[B]("V.smul(laurent_monomial(t, -m - &1), x)")
					shiftedIn := b.Have(
						"t^(−m−1) · x lies in the ambient",
						"V.smul(laurent_monomial(t, -m - &1), x) ∈ «plAmbient»",
						By(
							subK,
							tInL,
							nonzero,
							pair,
							xIn,
							LaurentMonomialSmulInAmbient.Read(L).At(k, tm, V, M, b.TermAs[Int]("-m - &1"), x)))
					b.Show(
						"and y ↦ u([y]) takes it into k",
						By(
							shiftedIn,
							functional,
							module_homomorphism.HomIn.At(scalars, ambientModule, scalarModule, functionalMap, shifted)))
				}))
			finitelyMany := a.Have(
				"only finitely many of them are not zero",
				"finite(«plShiftedSupport»)",
				By(subK, nonzero, pair, dual, xIn, DualityInverseFinite.Read(L).At(k, tm, V, M, u, x)))
			sum := a.Have(
				"on the ambient the map is the sum of the coefficients times the powers of t",
				"«plInverseAtX»(x) = «plShiftedExpansion»",
				Unfold(projectiveLineDualityInverseDef),
				By(xIn))
			a.Show(
				"so the map at x is a finite expansion with coefficients in k",
				By(finitelyMany, values, sum))
		}),
})}

// DualityInverseShift — multiplying x by tʲ multiplies the map of u by tʲ: the
// coefficient of tᵐ at tʲ · x is u([t^(−m−1) · tʲ · x]), the coefficient of
// t^(m−j) at x, so the expansion at tʲ · x is the one at x moved j places
// (laurent_polynomial.LaurentExpansionShift), which is tʲ times it.
var DualityInverseShift = dualityInverseShiftThm{family.Add(registry.ProofEntry{
	Name: "DualityInverseShift",
	Key:  "prop_77dc510d9085c2f2",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀u:(set(B) → A). " +
			"∀x:B. " +
			"∀j:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"«plPairOnLine»",
			"u ∈ «plDualSet»",
			"x ∈ «plAmbient»",
		},
		Conclusion: "projective_line_duality_inverse(L, " +
			"    k, " +
			"    t, " +
			"    V, " +
			"    M, " +
			"    u, " +
			"    V.smul(laurent_monomial(t, j), x)) = " +
			"laurent_monomial(t, j) * projective_line_duality_inverse(L, k, t, V, M, u, x)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			u *Arrow[Set[B], A],
			x *Expr[B],
			j *Expr[Int],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"M is a lattice pair on the line",
				"u is a k-linear functional on H¹(M)",
				"x lies in the ambient")
			// u ∈ dual (given[4]) stays resident: the two expansions below read it as their guard.
			subK, tInL, nonzero, pair, xIn := given[0], given[1], given[2], given[3], given[5]
			tm := a.MemberOf[on.L](t, tInL)
			ring := a.TermAs[module_record.RingOps[A]]("«plRing»")
			chart0, chart1 := a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»")
			ambient := a.TermAs[Set[B]]("«plAmbient»")
			power := a.TermAs[A]("laurent_monomial(t, j)")
			shifted := a.TermAs[B]("V.smul(laurent_monomial(t, j), x)")

			xInV := a.Have(
				"x lies in V",
				"x ∈ V.carrier",
				By(
					xIn,
					a.Unfolded(a.Have(
						"the ambient lies in V",
						"«plAmbient» ⊆ V.carrier",
						By(
							pair,
							lattice_pair.AmbientContains.At(ring, chart0, chart1, V, M),
							submodule.SubmoduleSubset.At(ring, V, ambient))), set_basic.SubsetDef)))
			powerIn := a.Have(
				"tʲ lies in the overlap",
				"laurent_monomial(t, j) ∈ «plOverlap»",
				By(subK, tInL, nonzero, laurent_polynomial.LaurentMonomialInRing.Read(L).At(k, tm, j)))
			shiftInAmbient := a.Have(
				"tʲ · x lies in the ambient",
				"V.smul(laurent_monomial(t, j), x) ∈ «plAmbient»",
				By(subK, tInL, nonzero, pair, xIn, LaurentMonomialSmulInAmbient.Read(L).At(k, tm, V, M, j, x)))
			atX := a.Conjuncts(
				a.Simplified(GroupPremises(
					given[0],
					given[2],
					given[3],
					given[4],
					given[5],
					DualityInverseExpansion.Read(L).At(k, tm, V, M, u, x))),
				"the coefficients at x have finite support",
				"they lie in k",
				"and the map at x is their expansion")
			atShifted := a.Conjuncts(
				a.Simplified(GroupPremises(
					given[0],
					given[2],
					given[3],
					given[4],
					shiftInAmbient,
					DualityInverseExpansion.Read(L).At(k, tm, V, M, u, shifted))),
				"the coefficients at tʲ · x have finite support",
				"they lie in k",
				"and the map at tʲ · x is their expansion")

			product := a.Have(
				"powers of t multiply by adding exponents",
				"∀p q:int. laurent_monomial(t, p) * laurent_monomial(t, q) = laurent_monomial(t, p + q)",
				By(nonzero, laurent_polynomial.LaurentMonomialProduct.Read(L).At(tm)))
			exponent := a.Have(
				"the exponents add up",
				"∀m:int. (-m - &1) + j = -(m - j) - &1",
				ByArith())
			moved := a.Have(
				"t^(−m−1) · (tʲ · x) is t^(−(m − j)−1) · x",
				"∀m:int. "+
					"    V.smul(laurent_monomial(t, -m - &1), V.smul(laurent_monomial(t, j), x)) = "+
					"    V.smul(laurent_monomial(t, -(m - j) - &1), x)",
				Derive(func(b *Argument) {
					m := b.FixAs[Int]("m")
					exponentOf := b.TermAs[Int]("-m - &1")
					powerOf := b.TermAs[A]("laurent_monomial(t, -m - &1)")
					powerOfIn := b.Have(
						"t^(−m−1) lies in the overlap",
						"laurent_monomial(t, -m - &1) ∈ «plOverlap»",
						By(subK, tInL, nonzero, laurent_polynomial.LaurentMonomialInRing.Read(L).At(k, tm, exponentOf)))
					b.Show(
						"scale by the product of the two powers, which is the power at the sum of the exponents",
						CalcEq(
							Leg(
								b.TermAs[B]("V.smul(laurent_monomial(t, -m - &1) * laurent_monomial(t, j), x)"),
								"scaling twice is scaling by the product",
								By(
									pair,
									lattice_pair.PairModuleOn,
									powerOfIn,
									powerIn,
									xInV,
									module.SmulMul.At(ring, V, powerOf, power, x))),
							Leg(
								b.TermAs[B]("V.smul(laurent_monomial(t, (-m - &1) + j), x)"),
								"powers of t multiply by adding exponents",
								By(product.At(exponentOf, j))),
							FinalLeg(
								"(−m − 1) + j = −(m − j) − 1",
								By(exponent.At(m))),
						))
				}))
			shiftedSum := a.Have(
				"tʲ times the map at x is the expansion at x moved j places",
				"laurent_monomial(t, j) * projective_line_duality_inverse(L, k, t, V, M, u, x) = "+
					"module_sum(L.add, "+
					"    L.zero, "+
					"    fun_support(L.zero, "+
					"        λm:int. "+
					"            u(left_coset(V.add, "+
					"                    V.smul(laurent_monomial(t, -(m - j) - &1), x), "+
					"                    set_mul(V.add, fst(M), snd(M))))), "+
					"    λm:int. "+
					"        u(left_coset(V.add, "+
					"                V.smul(laurent_monomial(t, -(m - j) - &1), x), "+
					"                set_mul(V.add, fst(M), snd(M)))) * "+
					"        laurent_monomial(t, m))",
				By(
					subK,
					tInL,
					nonzero,
					atX[0],
					atX[1],
					atX[2],
					laurent_polynomial.LaurentExpansionShift.Read(L).At(
						k,
						tm,
						a.TermAs[Fun[Int, A]](
							"λm:int. u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»))"),
						a.TermAs[A]("projective_line_duality_inverse(L, k, t, V, M, u, x)"),
						j)))
			a.Show(
				"the expansion at tʲ · x is the expansion at x moved j places",
				Simp(Fwd(atShifted[2]), Fwd(moved)),
				By(shiftedSum))
		}),
})}

// DualityInverseLinear — the map of a functional u is k-linear on the ambient
// and zero off it: on the ambient it is the expansion Σ u([t^(−m−1) · x]) · tᵐ
// (DualityInverseExpansion), whose coefficients are k-linear in x, y ↦ u([y])
// being k-linear (DualityFunctionalOnAmbient), and an expansion is k-linear in
// its coefficients (laurent_polynomial.LaurentSumAdd,
// laurent_polynomial.LaurentSumScale); off the ambient the definition's
// condition makes it zero.
var DualityInverseLinear = dualityInverseLinearThm{family.Add(registry.ProofEntry{
	Name: "DualityInverseLinear",
	Key:  "prop_e3fda66b47b441c2",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀u:(set(B) → A).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"«plPairOnLine»",
			"u ∈ «plDualSet»",
		},
		Conclusion: "«plInverseOf» ∈ hom_set(«plScalars», restrict_module(V, «plAmbient»), «plField»)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			u *Arrow[Set[B], A],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"M is a lattice pair on the line",
				"u is a k-linear functional on H¹(M)")
			subK, tInL, nonzero, pair, dual := given[0], given[1], given[2], given[3], given[4]
			tm := a.MemberOf[on.L](t, tInL)
			ring, scalars :=
				a.TermAs[module_record.RingOps[A]]("«plRing»"), a.TermAs[module_record.RingOps[A]]("«plScalars»")
			chart0, chart1 := a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»")
			ambient := a.TermAs[Set[B]]("«plAmbient»")
			ambientModule := a.TermAs[ModuleOps[A, B]]("«plAmbientModule»")
			container := a.TermAs[ModuleOps[A, A]]("«plField»")
			scalarModule := a.TermAs[ModuleOps[A, A]]("restrict_module(regular_module(field_ring(L)), k)")
			inverse := a.TermAs[Fun[B, A]]("«plInverseOf»")
			functionalMap := a.TermAs[Fun[B, A]]("«plFunctionalOnAmbient»")
			ringL := field.RingOn.Read(L)
			regular := module.RegularModuleOn.Read(ringL)

			functional := a.Have(
				"y ↦ u([y]) is a k-linear map from the ambient into k",
				"module_homomorphism(«plScalars», "+
					"    «plAmbientModule», "+
					"    restrict_module(regular_module(field_ring(L)), k), "+
					"    «plFunctionalOnAmbient»)",
				By(subK, nonzero, pair, dual, DualityFunctionalOnAmbient.Read(L).At(k, tm, V, M, u)))
			ambientSpace := module_homomorphism.HomSource.At(
				scalars, ambientModule, scalarModule, functionalMap)
			vModule := a.Have(
				"V is a module over the overlap",
				"module_on(«plRing», V)",
				By(pair, lattice_pair.PairModuleOn))
			ambientSub := a.Have(
				"the ambient is a submodule of V over the overlap",
				"submodule(«plRing», V, «plAmbient»)",
				By(pair, lattice_pair.AmbientContains.At(ring, chart0, chart1, V, M)))
			inV := a.Unfolded(a.Have(
				"the ambient lies in V",
				"«plAmbient» ⊆ V.carrier",
				By(ambientSub, submodule.SubmoduleSubset.At(ring, V, ambient))), set_basic.SubsetDef)
			overlap := a.Conjuncts(
				a.Have(
					"the overlap is a subring of L holding k, t and inv(t)",
					"subring(field_ring(L), «plOverlap») ∧ k ⊆ «plOverlap» ∧ t ∈ «plOverlap» ∧ L.inv(t) ∈ «plOverlap»",
					By(subK, tInL, nonzero, laurent_polynomial.LaurentRingSubring.Read(L).At(k, tm))),
				"the overlap is a subring of L",
				"it holds k",
				"it holds t",
				"it holds inv(t)")
			kInOverlap := a.Unfolded(overlap[1], set_basic.SubsetDef)
			overlapInL := a.Unfolded(a.Have(
				"the overlap lies in L",
				"«plOverlap» ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(overlap[0]))), set_basic.SubsetDef)
			datum := a.Simplified(
				GroupPremises(given[0], given[2], projective_line.LineDatum.Read(L).At(k, tm)))
			powerIn := a.Have(
				"the powers t^(−m−1) lie in the overlap",
				"∀m:int. laurent_monomial(t, -m - &1) ∈ «plOverlap»",
				Derive(func(b *Argument) {
					b.FixAs[Int]("m")
					b.Show(
						"t^(−m−1) is a power of t",
						By(
							subK,
							tInL,
							nonzero,
							laurent_polynomial.LaurentMonomialInRing.Read(L).At(k, tm, b.TermAs[Int]("-m - &1"))))
				}))
			shiftIn := a.Have(
				"and they carry the ambient into itself",
				"∀m:int. ∀y:B. y ∈ «plAmbient» ⇒ V.smul(laurent_monomial(t, -m - &1), y) ∈ «plAmbient»",
				Derive(func(b *Argument) {
					b.FixAs[Int]("m")
					y := b.FixAs[B]("y")
					yIn := b.Assume()
					b.Show(
						"a power of t carries the ambient into itself",
						By(
							subK,
							tInL,
							nonzero,
							pair,
							yIn,
							LaurentMonomialSmulInAmbient.Read(L).At(k, tm, V, M, b.TermAs[Int]("-m - &1"), y)))
				}))

			// Into L: on the ambient the map is a finite sum of terms of L.
			intoL := a.Have(
				"the map carries the ambient into L",
				"∀x:B. x ∈ «plAmbient» ⇒ projective_line_duality_inverse(L, k, t, V, M, u, x) ∈ L.carrier",
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					xInAmbient := b.Assume()
					atX := b.Conjuncts(
						b.Simplified(GroupPremises(
							given[0],
							given[2],
							given[3],
							given[4],
							xInAmbient,
							DualityInverseExpansion.Read(L).At(k, tm, V, M, u, x))),
						"the coefficients at x have finite support",
						"they lie in k",
						"and the map at x is their expansion")
					coefficients := b.TermAs[Fun[Int, A]](
						"λm:int. u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»))")
					// laurent_polynomial.LaurentTermsInField concludes ∀j; the
					// untyped cite keeps the ∀m the Have states, the typed At
					// wanting the exponent too.
					terms := b.Have(
						"its terms lie in L",
						"∀m:int. "+
							"    u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»)) * "+
							"    laurent_monomial(t, m) ∈ "+
							"    L.carrier",
						By(
							subK,
							tInL,
							nonzero,
							atX[1],
							Read(laurent_polynomial.LaurentTermsInField, L).At(k, t, coefficients)))
					b.Show(
						"a finite sum of members of L lies in L",
						By(
							atX[0],
							atX[2],
							terms,
							module.ModuleSumIn.Read(regular).At(
								b.TermAs[Set[Int]]("«plShiftedSupport»"),
								b.TermAs[Fun[Int, A]](
									"λm:int. "+
										"    u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»)) * "+
										"    laurent_monomial(t, m)"))))
				}))

			// Additivity: the coefficients of x + y are those of x plus those of y.
			additive := a.Have(
				"the map is additive on the ambient",
				Statement{
					Binders: "∀x y:B.",
					Hypotheses: []string{
						"x ∈ «plAmbient»",
						"y ∈ «plAmbient»",
					},
					Conclusion: "projective_line_duality_inverse(L, k, t, V, M, u, V.add(x, y)) = " +
						"projective_line_duality_inverse(L, k, t, V, M, u, x) + " +
						"projective_line_duality_inverse(L, k, t, V, M, u, y)",
				},
				Derive(func(b *Argument) {
					x, y := b.FixAs[B]("x"), b.FixAs[B]("y")
					both := b.Conjuncts(
						b.Assume(),
						"x lies in the ambient",
						"and so does y")
					xIn, yIn := both[0], both[1]
					sumInAmbient := b.Have(
						"so does x + y",
						"V.add(x, y) ∈ «plAmbient»",
						By(xIn, yIn, ambientSub, submodule.SubmoduleAdd.At(ring, V, ambient, x, y)))
					atX := b.Conjuncts(
						b.Simplified(GroupPremises(
							given[0],
							given[2],
							given[3],
							given[4],
							both[0],
							DualityInverseExpansion.Read(L).At(k, tm, V, M, u, x))),
						"the coefficients at x have finite support",
						"they lie in k",
						"and the map at x is their expansion")
					atY := b.Conjuncts(
						b.Simplified(GroupPremises(
							given[0],
							given[2],
							given[3],
							given[4],
							both[1],
							DualityInverseExpansion.Read(L).At(k, tm, V, M, u, y))),
						"the coefficients at y have finite support",
						"they lie in k",
						"and the map at y is their expansion")
					atSum := b.Conjuncts(
						b.Simplified(GroupPremises(
							given[0],
							given[2],
							given[3],
							given[4],
							sumInAmbient,
							DualityInverseExpansion.Read(L).At(k, tm, V, M, u, b.TermAs[B]("V.add(x, y)")))),
						"the coefficients at x + y have finite support",
						"they lie in k",
						"and the map at x + y is their expansion")
					split := b.Have(
						"the coefficient of x + y at m is the sum of those of x and y",
						"∀m:int. "+
							"    u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), V.add(x, y)), «plChartSum»)) = "+
							"    u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»)) + "+
							"    u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), y), «plChartSum»))",
						Derive(func(c *Argument) {
							m := c.FixAs[Int]("m")
							p := c.TermAs[A]("laurent_monomial(t, -m - &1)")
							px, py :=
								c.TermAs[B]("V.smul(laurent_monomial(t, -m - &1), x)"),
								c.TermAs[B]("V.smul(laurent_monomial(t, -m - &1), y)")
							c.Show(
								"t^(−m−1) distributes over x + y, and y ↦ u([y]) is additive",
								CalcEq(
									Leg(
										c.TermAs[A](
											"u(left_coset(V.add, "+
												"        V.add(V.smul(laurent_monomial(t, -m - &1), x), "+
												"            V.smul(laurent_monomial(t, -m - &1), y)), "+
												"        «plChartSum»))"),
										"t^(−m−1) distributes over x + y",
										By(
											xIn,
											yIn,
											vModule,
											powerIn.At(m),
											inV.At(x),
											inV.At(y),
											module.SmulAddLeft.At(ring, V, p, x, y))),
									FinalLeg(
										"and y ↦ u([y]) is additive on the ambient, which holds both",
										By(
											xIn,
											yIn,
											shiftIn.At(m, x),
											shiftIn.At(m, y),
											functional,
											module_homomorphism.HomAdd.At(scalars, ambientModule, scalarModule, functionalMap, px, py))),
								))
						}))
					b.Show(
						"so the expansion at x + y is the sum of the expansions at x and y",
						Simp(Fwd(atSum[2]), Fwd(split)),
						By(
							subK,
							nonzero,
							atX[0],
							atY[0],
							atX[1],
							atY[1],
							atX[2],
							atY[2],
							laurent_polynomial.LaurentSumAdd.Read(L).At(
								k,
								tm,
								b.TermAs[Fun[Int, A]](
									"λm:int. u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»))"),
								b.TermAs[Fun[Int, A]](
									"λm:int. u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), y), «plChartSum»))"))))
				}))

			// Homogeneity: the coefficients of c · x are c times those of x.
			homogeneous := a.Have(
				"the map is k-homogeneous on the ambient",
				Statement{
					Binders: "∀c:A. ∀x:B.",
					Hypotheses: []string{
						"c ∈ k",
						"x ∈ «plAmbient»",
					},
					Conclusion: "projective_line_duality_inverse(L, k, t, V, M, u, V.smul(c, x)) = " +
						"c * projective_line_duality_inverse(L, k, t, V, M, u, x)",
				},
				Derive(func(b *Argument) {
					c, x := b.FixAs[A]("c"), b.FixAs[B]("x")
					both := b.Conjuncts(
						b.Assume(),
						"c lies in k",
						"x lies in the ambient")
					cIn, xIn := both[0], both[1]
					cInOverlap := b.Have(
						"c lies in the overlap",
						"c ∈ «plOverlap»",
						By(cIn, kInOverlap))
					scaledInAmbient := b.Have(
						"so c · x lies in the ambient",
						"V.smul(c, x) ∈ «plAmbient»",
						By(cInOverlap, xIn, ambientSub, submodule.SubmoduleSmul.At(ring, V, ambient, c, x)))
					atX := b.Conjuncts(
						b.Simplified(GroupPremises(
							given[0],
							given[2],
							given[3],
							given[4],
							both[1],
							DualityInverseExpansion.Read(L).At(k, tm, V, M, u, x))),
						"the coefficients at x have finite support",
						"they lie in k",
						"and the map at x is their expansion")
					atScaled := b.Conjuncts(
						b.Simplified(GroupPremises(
							given[0],
							given[2],
							given[3],
							given[4],
							scaledInAmbient,
							DualityInverseExpansion.Read(L).At(k, tm, V, M, u, b.TermAs[B]("V.smul(c, x)")))),
						"the coefficients at c · x have finite support",
						"they lie in k",
						"and the map at c · x is their expansion")
					scale := b.Have(
						"the coefficient of c · x at m is c times that of x",
						"∀m:int. "+
							"    u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), V.smul(c, x)), «plChartSum»)) = "+
							"    c * u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»))",
						Derive(func(d *Argument) {
							m := d.FixAs[Int]("m")
							p := d.TermAs[A]("laurent_monomial(t, -m - &1)")
							commute := d.Have(
								"c and t^(−m−1) commute",
								"laurent_monomial(t, -m - &1) * c = c * laurent_monomial(t, -m - &1)",
								ByArith(ringL, powerIn.At(m), overlapInL, cInOverlap))
							d.Show(
								"t^(−m−1) · (c · x) is c · (t^(−m−1) · x), and y ↦ u([y]) is k-homogeneous",
								CalcEq(
									Leg(
										d.TermAs[A](
											"u(left_coset(V.add, V.smul(c, V.smul(laurent_monomial(t, -m - &1), x)), «plChartSum»))"),
										"t^(−m−1) · (c · x) is c · (t^(−m−1) · x), c and t^(−m−1) commuting",
										By(
											xIn,
											vModule,
											powerIn.At(m),
											cInOverlap,
											inV.At(x),
											commute,
											module.SmulMul.At(ring, V, p, c, x),
											module.SmulMul.At(ring, V, c, p, x))),
									FinalLeg(
										"and y ↦ u([y]) is k-homogeneous on the ambient",
										By(
											xIn,
											shiftIn.At(m, x),
											cIn,
											functional,
											module_homomorphism.HomSmul.At(
												scalars,
												ambientModule,
												scalarModule,
												functionalMap,
												c,
												d.TermAs[B]("V.smul(laurent_monomial(t, -m - &1), x)")))),
								))
						}))
					b.Show(
						"so the expansion at c · x is c times the expansion at x",
						Simp(Fwd(atScaled[2]), Fwd(scale)),
						By(
							subK,
							nonzero,
							atX[0],
							atX[1],
							atX[2],
							cIn,
							laurent_polynomial.LaurentSumScale.Read(L).At(
								k,
								tm,
								b.TermAs[Fun[Int, A]](
									"λm:int. u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»))"),
								c)))
				}))

			// Off the ambient the definition's condition makes the map zero.
			zeroOff := a.Have(
				"off the ambient the map is zero",
				"∀x:B. x ∉ «plAmbient» ⇒ projective_line_duality_inverse(L, k, t, V, M, u, x) = L.zero",
				Derive(func(b *Argument) {
					b.FixAs[B]("x")
					off := b.Assume()
					b.Show(
						"the definition's condition fails",
						Unfold(projectiveLineDualityInverseDef),
						By(off))
				}))
			homomorphism := a.Have(
				"so the map of u is k-linear on the ambient",
				"module_homomorphism(«plScalars», «plAmbientModule», «plField», «plInverseOf»)",
				By(
					ambientSpace,
					functional,
					datum,
					intoL,
					additive,
					homogeneous,
					module_homomorphism.ModuleHomomorphismDef.At(scalars, ambientModule, container, inverse)))
			a.Show(
				"and, zero off the ambient, it lies in hom_set over k",
				By(homomorphism, zeroOff, hom_module.InHomSet.At(scalars, ambientModule, container, inverse)))
		}),
})}

// DualityInverseLaurentLinear — the map of a functional u is linear over the
// overlap k[t, 1/t] on the ambient of M, and zero off it: it is k-linear there
// and zero off it (DualityInverseLinear), and a member c of the overlap is a
// finite k-combination Σ aᵢ · tⁱ of powers of t
// (laurent_polynomial.LaurentExpansion), so c · x is the sum of the aᵢ · (tⁱ ·
// x), which the map sends to the sum of the aᵢ · tⁱ times its value at x,
// multiplying by tⁱ moving the coefficients i places (DualityInverseShift).
var DualityInverseLaurentLinear = dualityInverseLaurentLinearThm{family.Add(registry.ProofEntry{
	Name: "DualityInverseLaurentLinear",
	Key:  "prop_91993e0b0f765074",
	Reading: "The map sums over all of ℤ rather than over a basis of M, which is why it is " +
		"linear over the overlap with no choice made. t ≠ zero suffices, as for DualityInverseFinite.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀u:(set(B) → A).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"«plPairOnLine»",
			"u ∈ «plDualSet»",
		},
		Conclusion: "«plInverseOf» ∈ hom_set(«plRing», restrict_module(V, «plAmbient»), «plField»)",
		Abbrev: Abbrev{
			{Name: "dualityInverseLaurentLinearSumOfC", Text: "module_sum(L.add, " +
				"    L.zero, " +
				"    fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, c, i)), " +
				"    λi:int. laurent_polynomial_coefficient(k, t, c, i) * laurent_monomial(t, i))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			u *Arrow[Set[B], A],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"M is a lattice pair on the line",
				"u is a k-linear functional on H¹(M)")
			subK, tInL, nonzero, pair, dual := given[0], given[1], given[2], given[3], given[4]
			tm := a.MemberOf[on.L](t, tInL)
			ring, scalars :=
				a.TermAs[module_record.RingOps[A]]("«plRing»"), a.TermAs[module_record.RingOps[A]]("«plScalars»")
			chart0, chart1 := a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»")
			ambient := a.TermAs[Set[B]]("«plAmbient»")
			ambientModule := a.TermAs[ModuleOps[A, B]]("«plAmbientModule»")
			container := a.TermAs[ModuleOps[A, A]]("«plField»")
			inverse := a.TermAs[Fun[B, A]]("«plInverseOf»")
			ringL := field.RingOn.Read(L)

			// Over k the map is linear on the ambient and zero off it.
			kLinear := a.Conjuncts(
				a.Have(
					"over k the map of u is linear on the ambient and zero off it",
					"module_homomorphism(«plScalars», «plAmbientModule», «plField», «plInverseOf») ∧ "+
						"(∀x:B. x ∉ «plAmbient» ⇒ projective_line_duality_inverse(L, k, t, V, M, u, x) = L.zero)",
					By(
						subK,
						nonzero,
						pair,
						dual,
						DualityInverseLinear.Read(L).At(k, tm, V, M, u),
						hom_module.InHomSet.At(scalars, ambientModule, container, inverse))),
				"the map of u is k-linear on the ambient",
				"and zero off it")
			linear, zeroOff := kLinear[0], kLinear[1]
			kParts := a.Conjuncts(
				a.Unfolded(linear, module_homomorphism.ModuleHomomorphismDef),
				"the ambient is a vector space over k",
				"so is L",
				"the map carries the ambient into L",
				"it is additive",
				"and k-homogeneous")

			// The overlap, the ambient over it and L over it.
			overlap := a.Conjuncts(
				a.Have(
					"the overlap is a subring of L holding k, t and inv(t)",
					"subring(field_ring(L), «plOverlap») ∧ k ⊆ «plOverlap» ∧ t ∈ «plOverlap» ∧ L.inv(t) ∈ «plOverlap»",
					By(subK, tInL, nonzero, laurent_polynomial.LaurentRingSubring.Read(L).At(k, tm))),
				"the overlap is a subring of L",
				"it holds k",
				"it holds t",
				"it holds inv(t)")
			kInOverlap := a.Unfolded(overlap[1], set_basic.SubsetDef)
			overlapInL := a.Unfolded(a.Have(
				"the overlap lies in L",
				"«plOverlap» ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(overlap[0]))), set_basic.SubsetDef)
			vModule := a.Have(
				"V is a module over the overlap",
				"module_on(«plRing», V)",
				By(pair, lattice_pair.PairModuleOn))
			ambientSub := a.Have(
				"the ambient is a submodule of V over the overlap",
				"submodule(«plRing», V, «plAmbient»)",
				By(pair, lattice_pair.AmbientContains.At(ring, chart0, chart1, V, M)))
			inV := a.Unfolded(a.Have(
				"the ambient lies in V",
				"«plAmbient» ⊆ V.carrier",
				By(ambientSub, submodule.SubmoduleSubset.At(ring, V, ambient))), set_basic.SubsetDef)
			datum := a.Simplified(
				GroupPremises(given[0], given[2], projective_line.LineDatum.Read(L).At(k, tm)))
			containerModule := a.Have(
				"L is a module over the overlap",
				"module_on(«plRing», «plField»)",
				By(datum))

			// Linearity over the overlap: expand c in powers of t.
			homogeneous := a.Have(
				"the map commutes with multiplication by a member of the overlap",
				Statement{
					Binders: "∀c:A. ∀x:B.",
					Hypotheses: []string{
						"c ∈ «plOverlap»",
						"x ∈ «plAmbient»",
					},
					Conclusion: "projective_line_duality_inverse(L, k, t, V, M, u, V.smul(c, x)) = " +
						"c * projective_line_duality_inverse(L, k, t, V, M, u, x)",
				},
				Derive(func(b *Argument) {
					c, x := b.FixAs[A]("c"), b.FixAs[B]("x")
					assumed := b.Conjuncts(
						b.Assume(),
						"c lies in the overlap",
						"x lies in the ambient")
					cIn, xIn := assumed[0], assumed[1]
					expansion := b.Conjuncts(
						b.Simplified(
							GroupPremises(cIn, given[0], given[2], laurent_polynomial.LaurentExpansion.Read(L).At(k, tm, c))),
						"the coefficients aᵢ of c have finite support",
						"they lie in k",
						"and c is Σ aᵢ · tⁱ")
					xInV := b.Have(
						"x lies in V",
						"x ∈ V.carrier",
						By(inV, xIn))
					value := b.Have(
						"the map at x lies in L",
						"projective_line_duality_inverse(L, k, t, V, M, u, x) ∈ L.carrier",
						By(xIn, kParts[2]))
					coefficientsIn := b.Have(
						"the coefficients lie in the overlap, which holds k",
						"∀i:int. laurent_polynomial_coefficient(k, t, c, i) ∈ «plOverlap»",
						By(kInOverlap, expansion[1]))
					powersIn := b.Have(
						"and so do the powers of t",
						"∀i:int. laurent_monomial(t, i) ∈ «plOverlap»",
						b.ForEach(func(i *Expr[Int]) Action {
							return By(subK, tInL, nonzero, laurent_polynomial.LaurentMonomialInRing.Read(L).At(k, tm, i))
						}))
					termsIn := b.Have(
						"so the terms aᵢ · tⁱ lie in the overlap",
						"∀i:int. laurent_polynomial_coefficient(k, t, c, i) * laurent_monomial(t, i) ∈ «plOverlap»",
						By(coefficientsIn, powersIn, comm_ring.SubringMul.Read(overlap[0])))
					termsAtX := b.Have(
						"and each (aᵢ · tⁱ) · x lies in the ambient",
						"∀i:int. "+
							"    V.smul(laurent_polynomial_coefficient(k, t, c, i) * laurent_monomial(t, i), x) ∈ «plAmbient»",
						Derive(func(d *Argument) {
							i := d.FixAs[Int]("i")
							d.Show(
								"a member of the overlap times a member of the ambient",
								By(
									termsIn.At(i),
									xIn,
									ambientSub,
									submodule.SubmoduleSmul.At(
										ring,
										V,
										ambient,
										d.TermAs[A]("laurent_polynomial_coefficient(k, t, c, i) * laurent_monomial(t, i)"),
										x)))
						}))
					termwise := b.Have(
						"the map sends (aᵢ · tⁱ) · x to aᵢ · tⁱ times its value at x",
						"∀i:int. "+
							"    projective_line_duality_inverse(L, "+
							"        k, "+
							"        t, "+
							"        V, "+
							"        M, "+
							"        u, "+
							"        V.smul(laurent_polynomial_coefficient(k, t, c, i) * laurent_monomial(t, i), x)) = "+
							"    laurent_polynomial_coefficient(k, t, c, i) * "+
							"    laurent_monomial(t, i) * "+
							"    projective_line_duality_inverse(L, k, t, V, M, u, x)",
						Derive(func(d *Argument) {
							i := d.FixAs[Int]("i")
							coefficient := d.TermAs[A]("laurent_polynomial_coefficient(k, t, c, i)")
							power := d.TermAs[A]("laurent_monomial(t, i)")
							shiftedIn := d.Have(
								"tⁱ · x lies in the ambient",
								"V.smul(laurent_monomial(t, i), x) ∈ «plAmbient»",
								By(subK, tInL, nonzero, pair, xIn, LaurentMonomialSmulInAmbient.Read(L).At(k, tm, V, M, i, x)))
							d.Show(
								"scale by tⁱ, then by aᵢ ∈ k",
								CalcEq(
									Leg(
										d.TermAs[A](
											"projective_line_duality_inverse(L, "+
												"    k, "+
												"    t, "+
												"    V, "+
												"    M, "+
												"    u, "+
												"    V.smul(laurent_polynomial_coefficient(k, t, c, i), V.smul(laurent_monomial(t, i), x)))"),
										"scaling by a product is scaling twice",
										By(
											vModule,
											coefficientsIn.At(i),
											powersIn.At(i),
											xInV,
											module.SmulMul.At(ring, V, coefficient, power, x))),
									Leg(
										d.TermAs[A](
											"laurent_polynomial_coefficient(k, t, c, i) * "+
												"projective_line_duality_inverse(L, k, t, V, M, u, V.smul(laurent_monomial(t, i), x))"),
										"the map is k-homogeneous",
										By(
											linear,
											expansion[1].At(i),
											shiftedIn,
											module_homomorphism.HomSmul.At(
												scalars,
												ambientModule,
												container,
												inverse,
												coefficient,
												d.TermAs[B]("V.smul(laurent_monomial(t, i), x)")))),
									Leg(
										d.TermAs[A](
											"laurent_polynomial_coefficient(k, t, c, i) * "+
												"(laurent_monomial(t, i) * projective_line_duality_inverse(L, k, t, V, M, u, x))"),
										"multiplying x by tⁱ multiplies the map by tⁱ",
										By(subK, nonzero, pair, dual, xIn, DualityInverseShift.Read(L).At(k, tm, V, M, u, x, i))),
									FinalLeg(
										"regrouped in the commutative ring L",
										ByArith(ringL, coefficientsIn.At(i), overlapInL, powersIn.At(i), value)),
								))
						}))
					support := b.TermAs[Set[Int]](
						"fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, c, i))")
					terms := b.TermAs[Fun[Int, A]](
						"λi:int. laurent_polynomial_coefficient(k, t, c, i) * laurent_monomial(t, i)")
					b.Show(
						"so the map at c · x is c times the map at x",
						CalcEq(
							Leg(
								b.TermAs[A](
									"projective_line_duality_inverse(L, "+
										"    k, "+
										"    t, "+
										"    V, "+
										"    M, "+
										"    u, "+
										"    V.smul(«dualityInverseLaurentLinearSumOfC», x))"),
								"c is Σ aᵢ · tⁱ",
								By(expansion[2])),
							Leg(
								b.TermAs[A](
									"projective_line_duality_inverse(L, "+
										"    k, "+
										"    t, "+
										"    V, "+
										"    M, "+
										"    u, "+
										"    module_sum(V.add, "+
										"        V.zero, "+
										"        fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, c, i)), "+
										"        λi:int. V.smul(laurent_polynomial_coefficient(k, t, c, i) * laurent_monomial(t, i), x)))"),
								"a finite sum of scalars scales x term by term",
								By(vModule, expansion[0], termsIn, xInV, module.ModuleSumSmulRight.At(ring, V, support, terms, x))),
							Leg(
								b.TermAs[A](
									"module_sum(L.add, "+
										"    L.zero, "+
										"    fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, c, i)), "+
										"    λi:int. "+
										"        projective_line_duality_inverse(L, "+
										"            k, "+
										"            t, "+
										"            V, "+
										"            M, "+
										"            u, "+
										"            V.smul(laurent_polynomial_coefficient(k, t, c, i) * laurent_monomial(t, i), x)))"),
								"the map, k-linear, passes through the finite sum",
								By(
									linear,
									expansion[0],
									termsAtX,
									module_homomorphism.HomSum.At(scalars, ambientModule, container, inverse, support,
										b.TermAs[Fun[Int, B]](
											"λi:int. V.smul(laurent_polynomial_coefficient(k, t, c, i) * laurent_monomial(t, i), x)")))),
							Leg(
								b.TermAs[A](
									"module_sum(L.add, "+
										"    L.zero, "+
										"    fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, c, i)), "+
										"    λi:int. "+
										"        laurent_polynomial_coefficient(k, t, c, i) * "+
										"        laurent_monomial(t, i) * "+
										"        projective_line_duality_inverse(L, k, t, V, M, u, x))"),
								"term by term",
								By(termwise, module.ModuleSumCongruence)),
							Leg(
								b.TermAs[A](
									"«dualityInverseLaurentLinearSumOfC» * projective_line_duality_inverse(L, k, t, V, M, u, x)"),
								"the map at x factors out of the sum, L being a module over the overlap",
								By(
									containerModule,
									expansion[0],
									termsIn,
									value,
									module.ModuleSumSmulRight.At(ring, container, support, terms,
										b.TermAs[A]("projective_line_duality_inverse(L, k, t, V, M, u, x)")))),
							FinalLeg(
								"and the sum is c",
								By(expansion[2])),
						))
				}))

			homomorphism := a.Have(
				"so the map of u is linear over the overlap on the ambient",
				"module_homomorphism(«plRing», «plAmbientModule», «plField», «plInverseOf»)",
				By(
					ambientSub,
					submodule.SubmoduleModuleOn.Read(vModule).At(ambient),
					containerModule,
					kParts[2],
					kParts[3],
					homogeneous,
					module_homomorphism.ModuleHomomorphismDef.At(ring, ambientModule, container, inverse)))
			a.Show(
				"and, zero off the ambient, it lies in hom_set over the overlap",
				By(homomorphism, zeroOff, hom_module.InHomSet.At(ring, ambientModule, container, inverse)))
		}),
})}

// DualityInverseCharts — the map of a functional u carries fst(M) into
// k[t] and snd(M) into t⁻² · k[1/t], the two charts of O(−2). At x in a
// chart the map is the finite sum of the c(m) · tᵐ, c(m) = u([t^(−m−1) · x])
// a member of k (DualityInverseExpansion). Where t^(−m−1) lies in the chart's ring, t^(−m−1) · x stays
// in the chart, inside fst(M) + snd(M), and u kills its class: so c(m) is
// zero below m = 0 on fst(M) and above m = −2 on snd(M), and the sum lies
// in the matching chart of O(−2) (laurent_polynomial.LaurentSumInPolynomials).
var DualityInverseCharts = dualityInverseChartsThm{family.Add(registry.ProofEntry{
	Name: "DualityInverseCharts",
	Key:  "prop_6d2f0a720c45ff84",
	Reading: "The shift by −m − 1 in the definition is what puts the cut at −2, so that the map " +
		"of u lands in O(−2) and in no other twist. t ≠ zero suffices, as for DualityInverseFinite.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀u:(set(B) → A).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"«plPairOnLine»",
			"u ∈ «plDualSet»",
		},
		Conclusion: "image(«plInverseOf», fst(M)) ⊆ fst(«plDualizing») ∧ " +
			"image(«plInverseOf», snd(M)) ⊆ snd(«plDualizing»)",
		Abbrev: Abbrev{
			{Name: "dualityInverseChartsChart1", Text: "image(L.mul(laurent_monomial(t, -&2)), «plChart1»)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			u *Arrow[Set[B], A],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"M is a lattice pair on the line",
				"u is a k-linear functional on H¹(M)")
			subK, tInL, nonzero, pair, dual := given[0], given[1], given[2], given[3], given[4]
			tm := a.MemberOf[on.L](t, tInL)
			ring := a.TermAs[module_record.RingOps[A]]("«plRing»")
			chart0, chart1 := a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»")
			fstM, sndM := a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)")

			// The charts of M: modules over k[t] and k[1/t], inside the ambient and inside fst(M) + snd(M).
			parts := a.Conjuncts(
				a.Unfolded(pair, lattice_pair.LatticePairDef),
				"V is a module over the overlap",
				"fst(M) is a k[t]-submodule of V",
				"snd(M) is a k[1/t]-submodule of V",
				"the two charts span one module over the overlap")
			sub0, sub1 := parts[1], parts[2]
			ambient := a.Conjuncts(
				GroupPremises(given[3], lattice_pair.AmbientContains.At(ring, chart0, chart1, V, M)),
				"the ambient is a submodule over the overlap",
				"fst(M) lies in the ambient",
				"snd(M) lies in the ambient")
			kSubring := a.Have(
				"k is a subring of the overlap",
				"subring(«plRing», k)",
				By(subK, tInL, nonzero, Read(laurent_polynomial.LaurentScalarSubring, L).At(k, t)))
			inSum := a.Conjuncts(
				a.Have(
					"each chart lies in fst(M) + snd(M), both being k-subspaces of V",
					"fst(M) ⊆ «plChartSum» ∧ snd(M) ⊆ «plChartSum»",
					By(
						nonzero,
						tInL,
						pair,
						subK,
						kSubring,
						projective_line.LineDatum.Read(L).At(k, tm),
						lattice_pair.PairOverSubring.At(ring, chart0, chart1, t, a.TermAs[A]("L.inv(t)"), k, V, M),
						submodule.SumContainsLeft,
						submodule.SumContainsRight)),
				"fst(M) lies in the chart sum",
				"snd(M) lies in the chart sum")

			// u kills the zero class fst(M) + snd(M).
			kills := a.Have(
				"u kills the class of every member of fst(M) + snd(M)",
				"∀y:B. y ∈ «plChartSum» ⇒ u(left_coset(V.add, y, «plChartSum»)) = L.zero",
				a.ForEach(func(y *Expr[B]) Action {
					return By(subK, nonzero, pair, dual, DualityKillsChartSum.Read(L).At(k, tm, V, M, u, y))
				}))

			// At x in a chart the map of u is a finite expansion over k, whose exponents the chart bounds.
			charts, expansions :=
				laurent_polynomial.LaurentMonomialInPolynomials.Read(L),
				laurent_polynomial.LaurentSumInPolynomials.Read(L)
			cut := a.TermAs[Int]("-&2")
			inChart0 := a.Have(
				"the map of u carries fst(M) into k[t]",
				"∀x:B. x ∈ fst(M) ⇒ «plInverseAtX»(x) ∈ «plChart0»",
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					xIn := b.Assume()
					xInAmbient := b.Have(
						"x lies in the ambient",
						"x ∈ «plAmbient»",
						BySets(ambient[1], xIn))
					expansion := b.Conjuncts(
						GroupPremises(
							given[0],
							given[2],
							given[3],
							given[4],
							xInAmbient,
							DualityInverseExpansion.Read(L).At(k, tm, V, M, u, x)),
						"only finitely many c(m) are not zero",
						"each c(m) lies in k",
						"and the map of u at x is the sum of the c(m) · tᵐ")
					natural := b.Have(
						"and none below m = 0, where t^(−m−1) · x stays in the k[t]-module fst(M)",
						Statement{
							Binders: "∀m:int.",
							Hypotheses: []string{
								"u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»)) ≠ L.zero",
							},
							Conclusion: "&0 ≤ m",
						},
						Derive(func(c *Argument) {
							c.FixAs[Int]("m")
							term := c.Assume()
							negative := c.SupposeNot()
							exponent := c.Have(
								"−m − 1 is not negative",
								"&0 ≤ -m - &1",
								ByArith(negative))
							power := c.Have(
								"so t^(−m−1) lies in k[t]",
								"laurent_monomial(t, -m - &1) ∈ «plChart0»",
								By(subK, exponent, charts.At(k, tm, c.TermAs[Int]("-m - &1"))))
							shifted := c.Have(
								"and t^(−m−1) · x in fst(M)",
								"laurent_monomial(t, -m - &1) • x ∈ fst(M)",
								By(power, xIn, submodule.SubmoduleSmul.Read(sub0), module_record.RestrictRingDef))
							inSumShifted := c.Have(
								"so in fst(M) + snd(M)",
								"laurent_monomial(t, -m - &1) • x ∈ «plChartSum»",
								BySets(inSum[0], shifted))
							c.Show(
								"its class is the zero class, which u kills",
								By(term, inSumShifted, kills.At(c.TermAs[B]("laurent_monomial(t, -m - &1) • x"))))
						}))
					inChart := b.Have(
						"a finite expansion over k with no negative exponent lies in k[t]",
						"«plShiftedExpansion» ∈ «plChart0»",
						By(
							subK,
							nonzero,
							expansion[0],
							expansion[1],
							natural,
							expansions.At(
								k,
								tm,
								b.TermAs[Fun[Int, A]](
									"λm:int. u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»))"),
								cut)))
					b.Show(
						"so does the map of u at x",
						expansion[2].Rw(),
						By(inChart))
				}))
			inChart1 := a.Have(
				"and snd(M) into t⁻² · k[1/t]",
				"∀x:B. x ∈ snd(M) ⇒ «plInverseAtX»(x) ∈ «dualityInverseChartsChart1»",
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					xIn := b.Assume()
					xInAmbient := b.Have(
						"x lies in the ambient",
						"x ∈ «plAmbient»",
						BySets(ambient[2], xIn))
					expansion := b.Conjuncts(
						GroupPremises(
							given[0],
							given[2],
							given[3],
							given[4],
							xInAmbient,
							DualityInverseExpansion.Read(L).At(k, tm, V, M, u, x)),
						"only finitely many c(m) are not zero",
						"each c(m) lies in k",
						"and the map of u at x is the sum of the c(m) · tᵐ")
					bounded := b.Have(
						"and none above m = −2, where t^(−m−1) · x stays in the k[1/t]-module snd(M)",
						Statement{
							Binders: "∀m:int.",
							Hypotheses: []string{
								"u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»)) ≠ L.zero",
							},
							Conclusion: "m ≤ -&2",
						},
						Derive(func(c *Argument) {
							c.FixAs[Int]("m")
							term := c.Assume()
							above := c.SupposeNot()
							exponent := c.Have(
								"−m − 1 is not positive",
								"-m - &1 ≤ &0",
								ByArith(above))
							power := c.Have(
								"so t^(−m−1) lies in k[1/t]",
								"laurent_monomial(t, -m - &1) ∈ «plChart1»",
								By(subK, exponent, charts.At(k, tm, c.TermAs[Int]("-m - &1"))))
							shifted := c.Have(
								"and t^(−m−1) · x in snd(M)",
								"laurent_monomial(t, -m - &1) • x ∈ snd(M)",
								By(power, xIn, submodule.SubmoduleSmul.Read(sub1), module_record.RestrictRingDef))
							inSumShifted := c.Have(
								"so in fst(M) + snd(M)",
								"laurent_monomial(t, -m - &1) • x ∈ «plChartSum»",
								BySets(inSum[1], shifted))
							c.Show(
								"its class is the zero class, which u kills",
								By(term, inSumShifted, kills.At(c.TermAs[B]("laurent_monomial(t, -m - &1) • x"))))
						}))
					inChart := b.Have(
						"a finite expansion over k with no exponent above −2 lies in t⁻² · k[1/t]",
						"«plShiftedExpansion» ∈ «dualityInverseChartsChart1»",
						By(
							subK,
							nonzero,
							expansion[0],
							expansion[1],
							bounded,
							expansions.At(
								k,
								tm,
								b.TermAs[Fun[Int, A]](
									"λm:int. u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»))"),
								cut)))
					b.Show(
						"so does the map of u at x",
						expansion[2].Rw(),
						By(inChart))
				}))

			// O(−2) is (k[t], t⁻² · k[1/t]), and each image lies in its chart.
			inverse := a.TermAs[Fun[B, A]]("«plInverseOf»")
			a.Show(
				"so the images of fst(M) and snd(M) lie in the two charts of O(−2)",
				Unfold(projective_line.ProjectiveLinePairDef),
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(
					inChart0,
					set_image.ImageSubsetIff.At(inverse, fstM, chart0),
					inChart1,
					set_image.ImageSubsetIff.At(inverse, sndM, a.TermAs[Set[A]]("«dualityInverseChartsChart1»"))))
		}),
})}

// DualityInversePairMap — the map of a functional u on H¹(M) is a map of
// lattice pairs from M into O(−2): it is linear over k[t, 1/t] on the
// ambient and zero off it (DualityInverseLaurentLinear), and it carries
// each chart of M into that of O(−2) (DualityInverseCharts).
var DualityInversePairMap = dualityInversePairMapThm{family.Add(registry.ProofEntry{
	Name: "DualityInversePairMap",
	Key:  "prop_799ee14780c462b5",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀u:(set(B) → A).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"«plPairOnLine»",
			"u ∈ «plDualSet»",
		},
		Conclusion: "«plInverseOf» ∈ «plMaps»",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			u *Arrow[Set[B], A],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"M is a lattice pair on the line",
				"u is a k-linear functional on H¹(M)")
			subK, tInL, nonzero, pair, dual := given[0], given[1], given[2], given[3], given[4]
			tm := a.MemberOf[on.L](t, tInL)
			conditions := a.Have(
				"the map of u is linear over k[t, 1/t] on the ambient "+
					"and carries each chart of M into that of O(−2)",
				"«plInverseOf» ∈ hom_set(«plRing», restrict_module(V, «plAmbient»), «plField») ∧ "+
					"image(«plInverseOf», fst(M)) ⊆ fst(«plDualizing») ∧ "+
					"image(«plInverseOf», snd(M)) ⊆ snd(«plDualizing»)",
				By(
					subK,
					tInL,
					nonzero,
					pair,
					dual,
					DualityInverseLaurentLinear.Read(L).At(k, tm, V, M, u),
					DualityInverseCharts.Read(L).At(k, tm, V, M, u)))
			a.Show(
				"which is what a map of lattice pairs into O(−2) is",
				Simp(Fwd(lattice_pair_map.LatticePairMapsDef)),
				BySets(conditions))
		}),
})}

// ---------------------------------------------------------------------------
// The round trips and the duality
// ---------------------------------------------------------------------------

// DualityRoundTripOne — the functional of the map of u is u: the map of u
// is a map of lattice pairs into O(−2) (DualityInversePairMap), so on the
// class X = [y] of a member y of the ambient its functional reads the
// coefficient of t⁻¹ in the map at y (DualityFunctional); the map at y is
// a finite expansion with coefficients u([t^(−m−1) · y]) in k, so for t
// transcendental the coefficient is the term at m = −1,
// u([t⁰ · y]) = u([y]) = u(X); off the classes both sides are zero.
var DualityRoundTripOne = dualityRoundTripOneThm{family.Add(registry.ProofEntry{
	Name: "DualityRoundTripOne",
	Key:  "prop_1600ff4f6ef05ffb",
	Reading: "Transcendence is load-bearing: the coefficient of t⁻¹ in the map at a member y of " +
		"X is the term at m = −1 only because expansions over k are unique. Of u nothing is asked " +
		"beyond its lying in the dual, and off the classes both sides are zero by the definitions.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀u:(set(B) → A). " +
			"∀X:set(B).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"«plPairOnLine»",
			"u ∈ «plDualSet»",
		},
		Conclusion: "projective_line_duality_map(L, k, t, V, M, «plInverseOf», X) = u(X)",
		Abbrev: Abbrev{
			{Name: "dualityRoundTripOneTerm", Text: "u( " +
				"    left_coset(V.add, V.smul(laurent_monomial(t, -(-&1) - &1), y), «plChartSum»))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			u *Arrow[Set[B], A],
			X *Expr[Set[B]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k",
				"M is a lattice pair on the line",
				"u is a k-linear functional on H¹(M)")
			subK, tInL, transcendental, pair, dual := given[0], given[1], given[2], given[3], given[4]
			tm := a.MemberOf[on.L](t, tInL)
			a.Cases(a.Term("X ∈ «plClasses»"))
			a.Otherwise(
				"off the classes of H¹(M) both sides are zero",
				func(b *Argument, notClass Fact) {
					vanishes := b.Have(
						"u, a member of hom_set, is zero off the classes",
						"u(X) = L.zero",
						By(
							notClass,
							dual,
							hom_module.InHomSet.At(
								b.TermAs[module_record.RingOps[A]]("«plScalars»"),
								b.TermAs[ModuleOps[A, Set[B]]]("«plH1»"),
								b.TermAs[ModuleOps[A, A]]("restrict_module(regular_module(field_ring(L)), k)"),
								u)))
					b.Show(
						"the functional of the map and u both vanish off the classes",
						CalcEq(
							Leg(
								b.Term("L.zero"),
								"the functional of the map is zero off the classes, by its definition's condition",
								Unfold(ProjectiveLineDualityMapDef),
								By(notClass)),
							FinalLeg(
								"and so is u",
								By(vanishes)),
						))
				})
			a.When(
				"on a class X, the class of a member y of the "+
					"ambient, the functional of the map reads the map at y",
				func(b *Argument, isClass Fact) {
					nonzero := b.Have(
						"t, transcendental over k, is not zero",
						"t ≠ L.zero",
						By(subK, transcendental, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))

					// The map of u is a map of lattice pairs into O(−2), so its functional reads it at the class of each member of the ambient.
					isMap := b.Have(
						"the map of u is a map of lattice pairs into O(−2)",
						"«plInverseOf» ∈ «plMaps»",
						By(subK, tInL, nonzero, pair, dual, DualityInversePairMap.Read(L).At(k, tm, V, M, u)))
					reads := b.Have(
						"at the class of a member y of the ambient the functional "+
							"of the map reads the coefficient of t⁻¹ in the map at y",
						Statement{
							Binders: "∀y:B.",
							Hypotheses: []string{
								"y ∈ «plAmbient»",
							},
							Conclusion: "projective_line_duality_map(L, " +
								"    k, " +
								"    t, " +
								"    V, " +
								"    M, " +
								"    «plInverseOf», " +
								"    left_coset(V.add, y, «plChartSum»)) = " +
								"laurent_polynomial_coefficient(k, t, projective_line_duality_inverse(L, k, t, V, M, u, y), -&1)",
						},
						By(
							subK,
							transcendental,
							pair,
							isMap,
							DualityFunctional.Read(L).At(k, tm, V, M, b.TermAs[Fun[B, A]]("«plInverseOf»"))))

					// X is the coset of some y in the ambient, a group under V's addition.
					spaces := b.Conjuncts(
						GroupPremises(given[0], nonzero, given[3], projective_line.LineH1Module.Read(L).At(k, tm, V, M)),
						"over k the ambient is a subspace of V",
						"so is chart 0 + chart 1",
						"which lies in the ambient",
						"and H¹(M) is a vector space over k")
					ambient, sum := b.TermAs[Set[B]]("«plAmbient»"), b.TermAs[Set[B]]("«plChartSum»")
					vectors := b.Have(
						"V is a module over the overlap",
						"module_on(«plRing», V)",
						By(pair, lattice_pair.PairModuleOn))
					groupAmbient := b.Have(
						"the ambient is a group under V's addition",
						"group_on(restrict_group(module_additive_group(V), «plAmbient»))",
						By(
							group.SubgroupGroupOn.Read(module.AddGroupOn.Read(vectors)).At(ambient),
							submodule.SubmoduleSubgroup.Read(spaces[0])))
					y, represented := b.ObtainAs[B](
						"X is the coset of some y in the ambient",
						"∃y:B. X = left_coset(V.add, y, «plChartSum») ∧ y ∈ «plAmbient»",
						By(quotient_group.InLeftCosets.Read(groupAmbient).At(sum, X), isClass, spaces[2]))
					coset := b.Conjuncts(
						represented,
						"X is the coset of y",
						"y lies in the ambient")
					yInV := b.Have(
						"y is a vector of V, the ambient lying in V",
						"y ∈ V.carrier",
						BySets(coset[1], submodule.SubmoduleSubset.Read(spaces[0])))

					// The map at y is a finite expansion over k, and its coefficient at −1 is the term at m = −1.
					expansion := b.Conjuncts(
						GroupPremises(
							given[0],
							nonzero,
							given[3],
							given[4],
							coset[1],
							DualityInverseExpansion.Read(L).At(k, tm, V, M, u, y)),
						"only finitely many coefficients u([t^(−m−1) · y]) are not zero",
						"each of them lies in k",
						"and the map at y is their sum against the powers of t")
					coefficients := b.TermAs[Fun[Int, A]](
						"λm:int. u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), y), «plChartSum»))")
					value := b.TermAs[A]("projective_line_duality_inverse(L, k, t, V, M, u, y)")
					coefficient := b.Have(
						"t being transcendental, the coefficient of t⁻¹ in that expansion is its term at m = −1",
						"laurent_polynomial_coefficient(k, "+
							"    t, "+
							"    projective_line_duality_inverse(L, k, t, V, M, u, y), "+
							"    -&1) = "+
							"«dualityRoundTripOneTerm»",
						By(
							subK,
							transcendental,
							expansion[0],
							expansion[1],
							expansion[2],
							laurent_polynomial.LaurentCoeffWellDefined.Read(L).At(
								k, tm, coefficients, value, b.TermAs[Int]("-&1"))))
					// An equation of numerals alone pins no embedding for `&`, so one side spells int_of_num longhand.
					exponent := b.Have(
						"the exponent −m − 1 at m = −1 is 0",
						"-(-&1) - &1 = int_of_num(0)",
						ByArith())
					powers := b.Conjuncts(
						GroupPremises(nonzero, laurent_polynomial.LaurentMonomialProduct.Read(L).At(tm)),
						"t⁰ = one",
						"t¹ = t",
						"t⁻¹ = inv(t)",
						"and the powers of t are nonzero members of L adding exponents")
					b.Show(
						"so the functional of the map at X = [y] is u([t⁰ · y]) = u([y])",
						coset[0].Rw(),
						CalcEq(
							Leg(
								b.TermAs[A](
									"laurent_polynomial_coefficient(k, t, projective_line_duality_inverse(L, k, t, V, M, u, y), -&1)"),
								"the functional of the map reads the coefficient of t⁻¹ in the map at y",
								By(reads.At(y), coset[1])),
							Leg(
								b.TermAs[A]("«dualityRoundTripOneTerm»"),
								"which is the term of the expansion at m = −1",
								By(coefficient)),
							FinalLeg(
								"t⁰ = one fixes y",
								By(exponent, powers[0], module.SmulOne.Read(vectors).At(proof.MemberOf(y, yInV)))),
						))
				})
		}),
})}

// DualityRoundTripTwo — the map of the functional of φ is φ: on the
// ambient the term at m, the functional at the class of t^(−m−1) · x, is
// the coefficient of t⁻¹ in φ(t^(−m−1) · x) = t^(−m−1) · φ(x), which is
// the coefficient of tᵐ in φ(x), so the map's sum at x is the Laurent
// expansion of φ(x) in the overlap; off the ambient both sides are zero.
var DualityRoundTripTwo = dualityRoundTripTwoThm{family.Add(registry.ProofEntry{
	Name: "DualityRoundTripTwo",
	Key:  "prop_945a048eb2ffedc5",
	Reading: "Transcendence is load-bearing: the coefficients of φ(x) are well defined, and a " +
		"power of t moves them without collision. φ's linearity over the overlap, not only over k, " +
		"is what lets t^(−m−1) pass through φ. Off the ambient both sides are zero by the definitions.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀φ:(B → A). " +
			"∀x:B.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"«plPairOnLine»",
			"φ ∈ «plMaps»",
		},
		Conclusion: "projective_line_duality_inverse(L, " +
			"    k, " +
			"    t, " +
			"    V, " +
			"    M, " +
			"    λX:set(B). projective_line_duality_map(L, k, t, V, M, φ, X), " +
			"    x) = " +
			"φ(x)",
		Abbrev: Abbrev{
			{Name: "dualityRoundTripTwoCoefficient", Text: "laurent_polynomial_coefficient(k, t, φ(x))"},
			{Name: "dualityRoundTripTwoTermSum", Text: "module_sum(L.add, " +
				"    L.zero, " +
				"    fun_support(L.zero, " +
				"        λm:int. " +
				"            projective_line_duality_map(L, " +
				"                k, " +
				"                t, " +
				"                V, " +
				"                M, " +
				"                φ, " +
				"                left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»))), " +
				"    λm:int. " +
				"        projective_line_duality_map(L, " +
				"            k, " +
				"            t, " +
				"            V, " +
				"            M, " +
				"            φ, " +
				"            left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»)) * " +
				"        laurent_monomial(t, m))"},
			{Name: "dualityRoundTripTwoExpansion", Text: "module_sum(L.add, " +
				"    L.zero, " +
				"    fun_support(L.zero, λm:int. «dualityRoundTripTwoCoefficient»(m)), " +
				"    λm:int. «dualityRoundTripTwoCoefficient»(m) * laurent_monomial(t, m))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			φ *Arrow[B, A],
			x *Expr[B],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k",
				"M is a lattice pair on the line",
				"φ is a map of lattice pairs into O(−2)")
			subK, tInL, transcendental, pair, isMap := given[0], given[1], given[2], given[3], given[4]
			ring := a.TermAs[module_record.RingOps[A]]("«plRing»")
			ambientModule := a.TermAs[ModuleOps[A, B]]("restrict_module(V, «plAmbient»)")
			container := a.TermAs[ModuleOps[A, A]]("«plField»")

			a.Cases(a.Term("x ∈ «plAmbient»"))
			a.Otherwise(
				"off the ambient both sides are zero",
				func(b *Argument, off Fact) {
					inHom := b.Have(
						"φ lies in hom_set",
						"φ ∈ hom_set(«plRing», restrict_module(V, «plAmbient»), «plField»)",
						BySets(b.Unfolded(isMap, lattice_pair_map.LatticePairMapsDef)))
					vanishes := b.Have(
						"φ, which lies in hom_set, vanishes off the ambient",
						"φ(x) = L.zero",
						By(off, inHom, hom_module.InHomSet.At(ring, ambientModule, container, φ)))
					b.Show(
						"the map of a functional and φ both vanish off the ambient",
						CalcEq(
							Leg(
								b.Term("L.zero"),
								"the map of a functional is zero off the ambient, by its definition's condition",
								Unfold(projectiveLineDualityInverseDef),
								By(off)),
							FinalLeg(
								"and so is φ",
								By(vanishes)),
						))
				})
			a.When(
				"on the ambient the map of the functional of φ is the Laurent expansion of φ(x)",
				func(b *Argument, xIn Fact) {
					tm := b.MemberOf[on.L](t, tInL)
					φx := φ.Apply(x)
					nonzero := b.Have(
						"t, transcendental, is not zero",
						"t ≠ L.zero",
						By(subK, transcendental, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
					reads := b.Have(
						"at the class of a member y of the ambient the "+
							"functional of φ reads the coefficient of t⁻¹ in φ(y)",
						Statement{
							Binders: "∀y:B.",
							Hypotheses: []string{
								"y ∈ «plAmbient»",
							},
							Conclusion: "projective_line_duality_map(L, " +
								"    k, " +
								"    t, " +
								"    V, " +
								"    M, " +
								"    φ, " +
								"    left_coset(V.add, y, set_mul(V.add, fst(M), snd(M)))) = " +
								"laurent_polynomial_coefficient(k, t, φ(y), -&1)",
						},
						By(subK, transcendental, pair, isMap, DualityFunctional.Read(L).At(k, tm, V, M, φ)))
					linear := b.Have(
						"φ, a map of lattice pairs, is linear over the overlap on the ambient",
						"module_homomorphism(«plRing», restrict_module(V, «plAmbient»), «plField», φ)",
						By(
							isMap,
							lattice_pair_map.PairMapHomomorphism.At(
								ring, V, container, M, b.TermAs[Prod[Set[A], Set[A]]]("«plDualizing»"), φ)))
					φxIn := b.Have(
						"φ carries x into the overlap k[t, 1/t]",
						"φ(x) ∈ «plOverlap»",
						By(
							subK,
							nonzero,
							pair,
							isMap,
							xIn,
							LinePairMapAmbient.Read(L).At(k, tm, V, M, b.TermAs[Int]("-&2"), φ, x)))

					terms := b.Have(
						"the term at m is the coefficient of tᵐ in φ(x)",
						"∀m:int. "+
							"    projective_line_duality_map(L, "+
							"        k, "+
							"        t, "+
							"        V, "+
							"        M, "+
							"        φ, "+
							"        left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»)) = "+
							"    «dualityRoundTripTwoCoefficient»(m)",
						Derive(func(c *Argument) {
							c.FixAs[Int]("m")
							exponent := c.TermAs[Int]("-m - &1")
							power := c.TermAs[A]("laurent_monomial(t, -m - &1)")
							shifted := c.TermAs[B]("V.smul(laurent_monomial(t, -m - &1), x)")
							powerIn := c.Have(
								"t^(−m−1) lies in the overlap",
								"laurent_monomial(t, -m - &1) ∈ «plOverlap»",
								By(subK, tInL, nonzero, laurent_polynomial.LaurentMonomialInRing.Read(L).At(k, tm, exponent)))
							shiftedIn := c.Have(
								"t^(−m−1) · x lies in the ambient",
								"V.smul(laurent_monomial(t, -m - &1), x) ∈ «plAmbient»",
								By(
									subK,
									tInL,
									nonzero,
									pair,
									xIn,
									LaurentMonomialSmulInAmbient.Read(L).At(k, tm, V, M, exponent, x)))
							back := c.Have(
								"−1 − (−m − 1) = m",
								"-&1 - (-m - &1) = m",
								ByArith())
							c.Show(
								"the coefficient of t⁻¹ in φ(t^(−m−1) · x) = t^(−m−1) · φ(x) is the coefficient of tᵐ in φ(x)",
								CalcEq(
									Leg(
										c.Term("laurent_polynomial_coefficient(k, t, φ(V.smul(laurent_monomial(t, -m - &1), x)), -&1)"),
										"the functional of φ reads the coefficient of t⁻¹ at a member of the class",
										By(shiftedIn, reads.At(shifted))),
									Leg(
										c.Term("laurent_polynomial_coefficient(k, t, laurent_monomial(t, -m - &1) * φ(x), -&1)"),
										"φ is linear over the overlap, which holds t^(−m−1)",
										By(module_homomorphism.HomSmul.Read(linear).At(
											proof.MemberOf(power, powerIn), proof.MemberOf(x, xIn)))),
									Leg(
										c.Term("laurent_polynomial_coefficient(k, t, φ(x), -&1 - (-m - &1))"),
										"multiplying by t^(−m−1) moves each coefficient −m − 1 places up",
										By(
											subK,
											tInL,
											transcendental,
											φxIn,
											laurent_polynomial.LaurentCoeffShift.Read(L).At(k, tm, φx, exponent, c.TermAs[Int]("-&1")))),
									FinalLeg(
										"whose exponent is m",
										By(Normalized, back)),
								))
						}))
					expansion := b.Have(
						"φ(x), a member of the overlap, is the sum of its coefficients times the powers of t",
						"φ(x) = «dualityRoundTripTwoExpansion»",
						By(subK, nonzero, φxIn, laurent_polynomial.LaurentExpansion.Read(L).At(k, tm, φx)))
					b.Show(
						"the map at x is the sum of the coefficients of φ(x) times the powers of t, which is φ(x)",
						CalcEq(
							Leg(
								b.Term("«dualityRoundTripTwoTermSum»"),
								"on the ambient the map of a functional is the sum of its terms times the powers of t",
								Unfold(projectiveLineDualityInverseDef),
								By(xIn)),
							Leg(
								b.Term("«dualityRoundTripTwoExpansion»"),
								"whose term at m is the coefficient of tᵐ in φ(x)",
								Simp(Fwd(terms)),
								Refl()),
							FinalLeg(
								"which is φ(x)",
								By(expansion)),
						))
				})
		}),
})}

// LineSerreDuality — Serre duality on the line: for every lattice pair M
// on the line, φ ↦ (the coefficient of t⁻¹ in φ) is a k-isomorphism from
// Hom(M, O(−2)) onto the k-dual of H¹(M); when H¹(M) is finite over k,
// Hom(M, O(−2)) has its dimension. The map of a functional is a two-sided
// inverse — the round trips — so the linear map φ ↦ its functional is a
// bijection; the dual of a finite-dimensional H¹(M) has its dimension, and
// the inverse isomorphism carries it to Hom(M, O(−2)).
var LineSerreDuality = lineSerreDualityThm{family.Add(registry.ProofEntry{
	Name: "LineSerreDuality",
	Key:  "prop_280b2690d379cc5d",
	Reading: "Neither freeness nor finiteness is asked for the isomorphism: both round trips hold " +
		"for every lattice pair on the line, a curve's lattice pair read over k[t] and k[1/t] among " +
		"them. The dimension half needs H¹(M) finite over k, the dual of an infinite-dimensional " +
		"space being larger than it; the free pairs have it (FreeLinePairH1Dim). The inverse's sums " +
		"are finite because two powers of t bring x into the two charts, a property of the pair and " +
		"not of the functional, so even for an infinite-dimensional H¹ the whole algebraic dual is " +
		"reached: Serre duality for quasi-coherent sheaves on the line.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"«plPairOnLine»",
		},
		Conclusion: "module_isomorphism(«plScalars», " +
			"    lattice_pair_hom(«plRing», V, M, «plField», «plDualizing»), " +
			"    «plDualModule», " +
			"    «plDuality») ∧ " +
			"(finite_dimensional(«plScalars», «plH1») ⇒ " +
			"    finite_dimensional(«plScalars», " +
			"        lattice_pair_hom(«plRing», V, M, «plField», «plDualizing»)) ∧ " +
			"    module_dim(«plScalars», lattice_pair_hom(«plRing», V, M, «plField», «plDualizing»)) = " +
			"    lattice_pair_h1_dim(«plRing», k, V, M))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k",
				"M is a lattice pair on the line")
			subK, tInL, transcendental, pair := given[0], given[1], given[2], given[3]
			tm := a.MemberOf[on.L](t, tInL)
			nonzero := a.Have(
				"t, transcendental, is not zero",
				"t ≠ L.zero",
				By(h, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			ring, scalars :=
				a.TermAs[module_record.RingOps[A]]("«plRing»"), a.TermAs[module_record.RingOps[A]]("«plScalars»")
			maps, functionals :=
				a.TermAs[Set[Fun[B, A]]]("«plMaps»"), a.TermAs[Set[Fun[Set[B], A]]]("«plDualSet»")
			mapsModule := a.TermAs[ModuleOps[A, Fun[B, A]]](
				"lattice_pair_hom(«plRing», V, M, «plField», «plDualizing»)")
			dualModule := a.TermAs[ModuleOps[A, Fun[Set[B], A]]]("«plDualModule»")
			duality := a.TermAs[Fun[Fun[B, A], Fun[Set[B], A]]]("«plDuality»")
			inverse := a.TermAs[Fun[Fun[Set[B], A], Fun[B, A]]](
				"λu:(set(B) → A). λx:B. projective_line_duality_inverse(L, k, t, V, M, u, x)")

			linear := a.Have(
				"φ ↦ the functional of φ is a k-linear map from Hom(M, O(−2)) to the dual of H¹(M)",
				"module_homomorphism(«plScalars», "+
					"    lattice_pair_hom(«plRing», V, M, «plField», «plDualizing»), "+
					"    «plDualModule», "+
					"    «plDuality»)",
				By(h, DualityMapLinear.Read(L).At(k, tm, V, M)))
			mapsReturn := a.Have(
				"a pair map into O(−2) is the map of its functional",
				Statement{
					Binders: "∀φ:(B → A).",
					Hypotheses: []string{
						"φ ∈ «plMaps»",
					},
					Conclusion: "(λx:B. " +
						"    projective_line_duality_inverse(L, " +
						"        k, " +
						"        t, " +
						"        V, " +
						"        M, " +
						"        λX:set(B). projective_line_duality_map(L, k, t, V, M, φ, X), " +
						"        x)) = " +
						"φ",
				},
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[B, A]]()
					isMap := b.Assume()
					b.Show(
						"the two maps agree at every point",
						Funext(),
						b.ForEach(func(x *Expr[B]) Action {
							return By(
								subK,
								tInL,
								transcendental,
								pair,
								isMap,
								DualityRoundTripTwo.Read(L).At(k, tm, V, M, φ, x))
						}))
				}))
			functionalsReturn := a.Have(
				"a functional on H¹(M) is the functional of its map",
				Statement{
					Binders: "∀u:(set(B) → A).",
					Hypotheses: []string{
						"u ∈ «plDualSet»",
					},
					Conclusion: "(λX:set(B). " +
						"    projective_line_duality_map(L, " +
						"        k, " +
						"        t, " +
						"        V, " +
						"        M, " +
						"        λx:B. projective_line_duality_inverse(L, k, t, V, M, u, x), " +
						"        X)) = " +
						"u",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[Fun[Set[B], A]]()
					functional := b.Assume()
					b.Show(
						"the two functionals agree at every class",
						Funext(),
						b.ForEach(func(X *Expr[Set[B]]) Action {
							return By(
								subK,
								tInL,
								transcendental,
								pair,
								functional,
								DualityRoundTripOne.Read(L).At(k, tm, V, M, u, X))
						}))
				}))
			mapsOfFunctionals := a.Have(
				"the map of a functional is a pair map into O(−2)",
				Statement{
					Binders: "∀u:(set(B) → A).",
					Hypotheses: []string{
						"u ∈ «plDualSet»",
					},
					Conclusion: "(λx:B. projective_line_duality_inverse(L, k, t, V, M, u, x)) ∈ «plMaps»",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[Fun[Set[B], A]]()
					functional := b.Assume()
					b.Show(
						"as it is for every functional",
						By(subK, tInL, nonzero, pair, functional, DualityInversePairMap.Read(L).At(k, tm, V, M, u)))
				}))
			iso := a.Have(
				"so φ ↦ its functional is a bijection with inverse u ↦ the map of u, a k-isomorphism",
				"module_isomorphism(«plScalars», "+
					"    lattice_pair_hom(«plRing», V, M, «plField», «plDualizing»), "+
					"    «plDualModule», "+
					"    «plDuality»)",
				By(
					linear,
					mapsReturn,
					functionalsReturn,
					module_homomorphism.HomIn.Read(linear),
					mapsOfFunctionals,
					functions.TwoSidedInverseBijection.At(maps, functionals, duality, inverse),
					lattice_pair_map.LatticePairHomDef.At(
						ring,
						V,
						M,
						a.TermAs[ModuleOps[A, A]]("«plField»"),
						a.TermAs[Prod[Set[A], Set[A]]]("«plDualizing»")),
					module_homomorphism.ModuleIsomorphismDef))

			inv := a.TermAs[Fun[A, A]]("L.inv")
			fieldK := a.Have(
				"k, a subfield of L, is a field under the operations of its scalar ring, with L's inverse",
				"ring_subfield(«plScalars», L.inv, k)",
				By(
					subK,
					field.SubfieldRingSubfield.Read(L).At(k, a.TermAs[Set[A]]("«plOverlap»")),
					field.RingSubfieldRestrict.At(ring, k, inv, k)))
			h1Space := a.Have(
				"H¹(M) is a vector space over k",
				"module_on(«plScalars», «plH1»)",
				By(subK, tInL, nonzero, pair, projective_line.LineH1Module.Read(L).At(k, tm, V, M)))
			backward := a.TermAs[Fun[Fun[Set[B], A], Fun[B, A]]](
				"inverse_on(lattice_pair_hom(«plRing», V, M, «plField», «plDualizing»).carrier, «plDuality»)")
			dimensions := a.Have(
				"when H¹(M) is finite over k, so is Hom(M, O(−2)), of dimension h¹(M)",
				Statement{
					Hypotheses: []string{
						"finite_dimensional(«plScalars», «plH1»)",
					},
					Conclusion: "finite_dimensional(«plScalars», " +
						"    lattice_pair_hom(«plRing», V, M, «plField», «plDualizing»)) ∧ " +
						"module_dim(«plScalars», lattice_pair_hom(«plRing», V, M, «plField», «plDualizing»)) = " +
						"lattice_pair_h1_dim(«plRing», k, V, M)",
				},
				Derive(func(b *Argument) {
					finite := b.Assume()
					dual := b.Have(
						"the dual of the finite-dimensional H¹(M) is finite of the same dimension",
						"finite_dimensional(«plScalars», «plDualModule») ∧ "+
							"module_dim(«plScalars», «plDualModule») = module_dim(«plScalars», «plH1»)",
						By(
							finite,
							fieldK,
							module_dimension.DualDim.Read(h1Space).At(inv),
							module_record.RegularModuleDef.At(scalars),
							module_record.RestrictModuleDef.At(b.TermAs[ModuleOps[A, A]]("«plField»"), k)))
					b.Show(
						"and the inverse of the isomorphism carries the dual "+
							"onto Hom(M, O(−2)), which so has its dimension, h¹(M)",
						By(
							dual,
							fieldK,
							iso,
							module_homomorphism.IsomorphismInverse.At(scalars, mapsModule, dualModule, duality),
							module_dimension.IsomorphismDim.At(scalars, dualModule, inv, mapsModule, backward),
							lattice_pair.LatticePairH1DimDef.At(ring, k, V, M)))
				}))
			a.Show(
				"Serre duality on the line: the isomorphism, and the dimension count for H¹(M) finite",
				By(iso, dimensions))
		}),
})}

// LineCanonicalCheck — the structure pair and the dualizing pair of the
// line have the cohomology duality predicts: h⁰(O) = h¹(O(−2)) = 1 and
// h¹(O) = h⁰(O(−2)) = 0.
var LineCanonicalCheck = lineCanonicalCheckThm{family.Add(registry.ProofEntry{
	Name: "LineCanonicalCheck",
	Key:  "prop_27f475148a82ef4",
	Reading: "These are LineH0Dim and LineH1Dim at n = 0 and n = −2, with O(0) read " +
		"as the structure pair (k[t], k[1/t]) — the pair the genus of a curve is taken at.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
		},
		Conclusion: "lattice_pair_h0_dim(«plRing», k, «plField», («plChart0», «plChart1»)) = 1 ∧ " +
			"lattice_pair_h1_dim(«plRing», k, «plField», («plChart0», «plChart1»)) = 0 ∧ " +
			"lattice_pair_h0_dim(«plRing», k, «plField», «plDualizing») = 0 ∧ " +
			"lattice_pair_h1_dim(«plRing», k, «plField», «plDualizing») = 1",
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], line Fact) {
			zero := a.TermAs[Int]("&0")
			minusTwo := a.TermAs[Int]("-&2")
			a.Do(
				Simp(Rev(projective_line.LinePairZero.Read(L))),
				SplitConjAll(
					Case(
						"H⁰(O) has dimension one, the zero-twist section formula",
						ByArith(line, projective_line.LineH0Dim.Read(L).AsFact().At(k, t, zero), int_embed.OfNumEq)),
					Case(
						"H¹(O) vanishes, the zero-twist quotient formula",
						ByArith(line, projective_line.LineH1Dim.Read(L).AsFact().At(k, t, zero), int_embed.OfNumEq)),
					Case(
						"H⁰(O(−2)) vanishes, the section formula at −2",
						ByArith(line, projective_line.LineH0Dim.Read(L).AsFact().At(k, t, minusTwo), int_embed.OfNumEq)),
					Case(
						"H¹(O(−2)) has dimension one, the quotient formula at −2",
						ByArith(line, projective_line.LineH1Dim.Read(L).AsFact().At(k, t, minusTwo), int_embed.OfNumEq))))
		}),
})}
