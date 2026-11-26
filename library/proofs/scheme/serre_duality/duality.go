// duality.go — the dualizing pair of a curve and Serre duality. The curve
// is finite over the projective line, f say, so its dualizing pair is
// f^!(O(−2)), built as the coextension dual Hom_{k[t, 1/t]}(A₀₁, k[t, 1/t]):
// the k[t, 1/t]-linear maps from the overlap into k[t, 1/t], a module over
// the overlap by coextension of scalars, chart 0 the maps carrying A₀ into
// k[t] and chart 1 the maps carrying A₁ into t⁻² · k[1/t], the charts of
// O(−2); no trace map is built. The maps of lattice pairs from M into it
// are the maps of M read on the line into O(−2) (DualizingMapsOnLine), and
// the line's duality by coefficient extraction makes H¹(M) dual to
// Hom(M, ω) for every lattice pair of the curve. An invertible model N of
// ω, an invertible pair onto which an isomorphism carries ω, measures
// Hom(X, ω) by the sections of N · X⁻¹ and has degree 2g − 2.

package serre_duality

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/laurent_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_map"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line_duality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The dualizing pair
// ---------------------------------------------------------------------------

// CurveDualizingModuleDef — `curve_dualizing_module(L, k, t, A₀₁)`: the
// k[t, 1/t]-linear maps from the overlap A₀₁ into k[t, 1/t], zero off
// A₀₁, as a module over A₀₁ acting on the argument — the coextension of
// k[t, 1/t] along its inclusion in A₀₁.
var CurveDualizingModuleDef = curveDualizingModuleDefThm{family.Define(registry.DefEntry{
	Name:     "CurveDualizingModuleDef",
	Key:      "prop_bd410a338d03460a",
	Const:    "curve_dualizing_module",
	Type:     "ring_ops(A) → set(A) → A → set(A) → (module_ops(A, A → A))",
	Implicit: []string{},
	Bundles:  []string{},
	Reading: "It is a module over A₀₁ where k[t, 1/t] ⊆ A₀₁, the inclusion being " +
		"then a ring map (CoextendScalarsModuleOn): at a curve, k[t] ⊆ A₀ and inv(t) ∈ " +
		"A₁. A basis of A₀₁ over k[t, 1/t] gives the dual basis of this module.",
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀t:A. ∀A₀₁:set(A). " +
			"    curve_dualizing_module(R, k, t, A₀₁) = " +
			"    coextend_scalars(restrict_ring(R, ring_away(R, polynomial_image(R, k, t), t)), " +
			"        restrict_ring(R, A₀₁), " +
			"        λx:A. x, " +
			"        restrict_module(regular_module(R), ring_away(R, polynomial_image(R, k, t), t)))",
	},
})}

// CurveDualizingPairDef — `curve_dualizing_pair(L, k, t, A₀, A₁, A₀₁)`,
// written ω: in the dualizing container, chart 0 the maps carrying A₀ into
// k[t] and chart 1 the maps carrying A₁ into t⁻² · k[1/t] — the maps that
// carry the curve's structure pair into the line's O(−2).
var CurveDualizingPairDef = curveDualizingPairDefThm{family.Define(registry.DefEntry{
	Name:     "CurveDualizingPairDef",
	Key:      "prop_c8372561aa09fe58",
	Const:    "curve_dualizing_pair",
	Type:     "field_ops(A) → set(A) → A → set(A) → set(A) → set(A) → (prod(set(A → A), set(A → A)))",
	Implicit: []string{},
	Bundles:  []string{},
	Reading: "Chart 0 is Hom_{k[t]}(A₀, k[t]), each such map extending uniquely to the " +
		"overlap; chart 1 is Hom_{k[1/t]}(A₁, t⁻² · k[1/t]). O(−2) is the line's dualizing pair, " +
		"so ω is the pair pushed down to the line and dualized there — no differential forms enter.",
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). ∀t:A. ∀A₀:set(A). ∀A₁:set(A). ∀A₀₁:set(A). " +
			"    curve_dualizing_pair(F, k, t, A₀, A₁, A₀₁) = " +
			"    ({φ:A → A | " +
			"            φ ∈ curve_dualizing_module(field_ring(F), k, t, A₀₁).carrier ∧ " +
			"            image(φ, A₀) ⊆ fst(projective_line_pair(F, k, t, -&2))}, " +
			"        {φ:A → A | " +
			"            φ ∈ curve_dualizing_module(field_ring(F), k, t, A₀₁).carrier ∧ " +
			"            image(φ, A₁) ⊆ snd(projective_line_pair(F, k, t, -&2))})",
	},
	Deps: []registry.EntryLike{CurveDualizingModuleDef},
})}

// CurveDualizingMapsDef — `curve_dualizing_maps(L, k, t, A₀, A₁, A₀₁, M)`,
// written Hom(M, ω): the module lattice_pair_hom of the maps of lattice
// pairs from M in the field into the dualizing pair.
var CurveDualizingMapsDef = curveDualizingMapsDefThm{family.Define(registry.DefEntry{
	Name:  "CurveDualizingMapsDef",
	Key:   "prop_830dab2fd076e0e2",
	Const: "curve_dualizing_maps",
	Type: "field_ops(A) → " +
		"set(A) → " +
		"A → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"prod(set(A), set(A)) → " +
		"(module_ops(A, A → A → A))",
	Implicit: []string{},
	Bundles:  []string{},
	Reading: "The operations are over the overlap, but the maps are a " +
		"module over k only (PairMapsLinearSpace): an overlap multiple of a " +
		"map need not keep the charts. Its dimension is always read over k.",
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). ∀t:A. ∀A₀:set(A). ∀A₁:set(A). ∀A₀₁:set(A). ∀M:prod(set(A), set(A)). " +
			"    curve_dualizing_maps(F, k, t, A₀, A₁, A₀₁, M) = " +
			"    lattice_pair_hom(restrict_ring(field_ring(F), A₀₁), " +
			"        regular_module(field_ring(F)), " +
			"        M, " +
			"        curve_dualizing_module(field_ring(F), k, t, A₀₁), " +
			"        curve_dualizing_pair(F, k, t, A₀, A₁, A₀₁))",
	},
	Deps: []registry.EntryLike{CurveDualizingModuleDef, CurveDualizingPairDef},
})}

// DualizingIsLattice — the dualizing pair is a lattice pair over the
// overlap, and its ambient is the whole dualizing container. The container
// is a module over the overlap (DualizingModuleOn); each chart of ω, the
// maps carrying a chart ring into the matching chart of O(−2), is a
// submodule over that ring, the charts of O(−2) holding zero and closed
// under sums (DualizingChartSubmodule); and each chart spans the whole
// container (DualizingChartsSpan), so the two spans agree and the ambient
// is the container.
var DualizingIsLattice = dualizingIsLatticeThm{family.Add(registry.ProofEntry{
	Name: "DualizingIsLattice",
	Key:  "prop_4a731c331f12b1eb",
	Reading: "The load-bearing clause of the datum is that each chart is free of finite " +
		"rank over the line's ring, A₀ over k[t] and A₁ over k[1/t]: over an infinite basis " +
		"the coordinate functionals span only the maps vanishing on all but finitely many " +
		"basis vectors, and the charts of ω would not glue to the whole container. The last " +
		"conjunct makes the container ω's ambient, so the cohomology of ω is read inside it.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«wcDatum»",
		},
		Conclusion: "module_on(«wcOverlap», «wdDualizingModule») ∧ " +
			"lattice_pair(«wcOverlap», A₀, A₁, «wdDualizingModule», «wdDualizing») ∧ " +
			"lattice_pair_ambient(«wcOverlap», «wdDualizingModule», «wdDualizing») = " +
			"«wdDualizingModule».carrier",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			container := a.Conjuncts(
				GroupPremises(curve, DualizingModuleOn.Read(L).At(k, A0, A1, A01, t)),
				"k[t, 1/t] is a ring",
				"it lies in the overlap",
				"its inclusion is a ring map",
				"the overlap is a module over it",
				"the container is a module over the overlap")[4]
			spans := a.Conjuncts(
				GroupPremises(curve, DualizingChartsSpan.Read(L).At(k, A0, A1, A01, t)),
				"chart 0 of ω spans the container",
				"chart 1 of ω spans the container")

			datum := a.Simplified(
				GroupPremises(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			tm := a.MemberOf[on.L](t, a.Have(
				"t lies in L",
				"t ∈ L.carrier",
				By(datum)))

			line := a.Conjuncts(
				a.Unfolded(a.Have(
					"O(−2) is a lattice pair on the line",
					"lattice_pair(«wcRing»(«wcLaurent»), "+
						"    «wcPolynomials», "+
						"    «wcInversePolynomials», "+
						"    «wcField», "+
						"    «lineDualizing»)",
					By(datum, projective_line.LinePairIsLattice.Read(L).At(k, tm, a.TermAs[Int]("-&2")))),
					lattice_pair.LatticePairDef),
				"L is a module over k[t, 1/t]",
				"chart 0 of O(−2) is a module over k[t]",
				"chart 1 of O(−2) is a module over k[1/t]",
				"both span the same")

			sub0 := a.Have(
				"the maps carrying A₀ into k[t] are a submodule over A₀",
				"submodule(restrict_ring(«wcOverlap», A₀), «wdDualizingModule», «omegaChart0»)",
				By(
					container,
					datum,
					submodule.SubmoduleZero.Read(line[1]),
					submodule.SubmoduleAdd.Read(line[1]),
					DualizingChartSubmodule.Read(L).At(k, A01, A0, a.TermAs[Set[A]]("fst(«lineDualizing»)"), t)))
			sub1 := a.Have(
				"the maps carrying A₁ into t⁻² · k[1/t] are a submodule over A₁",
				"submodule(restrict_ring(«wcOverlap», A₁), «wdDualizingModule», «omegaChart1»)",
				By(
					container,
					datum,
					submodule.SubmoduleZero.Read(line[2]),
					submodule.SubmoduleAdd.Read(line[2]),
					DualizingChartSubmodule.Read(L).At(k, A01, A1, a.TermAs[Set[A]]("snd(«lineDualizing»)"), t)))
			omega := a.Conjuncts(
				a.Have(
					"the charts of ω are those maps",
					"fst(«wdDualizing») = «omegaChart0» ∧ snd(«wdDualizing») = «omegaChart1»",
					Simp(
						Fwd(CurveDualizingPairDef),
						Fwd(pairs.Fst),
						Fwd(pairs.Snd),
						Fwd(CurveDualizingModuleDef),
						Fwd(hom_module.CoextendScalarsDef)),
					Basic()),
				"chart 0 of ω",
				"chart 1 of ω")
			a.Show(
				"a module over the overlap whose two charts are submodules "+
					"over the chart rings, each spanning the whole container",
				Simp(Fwd(lattice_pair.LatticePairDef), Fwd(lattice_pair.LatticePairAmbientDef)),
				By(container, sub0, sub1, omega[0], omega[1], spans[0], spans[1]))
		}),
})}

// DualizingModuleOn — the overlap of a curve contains the ring k[t, 1/t]
// (algebraic_curve.LaurentRingInOverlap), the inclusion is a ring map and the
// overlap a module over k[t, 1/t] through it, and the dualizing container, the
// coextension of k[t, 1/t] along the inclusion, is a module over the overlap.
var DualizingModuleOn = dualizingModuleOnThm{family.Add(registry.ProofEntry{
	Name: "DualizingModuleOn",
	Key:  "prop_4d2653d89ba5ac6e",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«wcDatum»",
		},
		Conclusion: "subring(field_ring(L), «wcLaurent») ∧ " +
			"«wcLaurent» ⊆ A₀₁ ∧ " +
			"«inclusionRingMap» ∧ " +
			"module_on(«wcRing»(«wcLaurent»), «wcVectors»(A₀₁)) ∧ " +
			"module_on(«wcOverlap», «wdDualizingModule»)",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			datum := a.Simplified(
				GroupPremises(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			ringL := field.RingOn.Read(L)
			overlapRing := a.Have(
				"the overlap, a subring of L, is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), A₀₁))",
				By(datum, comm_ring.SubringRingOn.Read(ringL).At(A01)))
			laurentSubring := a.Have(
				"k[t, 1/t] is a subring of L",
				"subring(field_ring(L), «wcLaurent»)",
				By(datum))
			laurentRing := a.Have(
				"so it is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), «wcLaurent»))",
				By(laurentSubring, comm_ring.SubringRingOn.Read(ringL).At(a.TermAs[Set[A]]("«wcLaurent»"))))
			inclusion := a.Have(
				"k[t, 1/t] lies in the overlap",
				"«wcLaurent» ⊆ A₀₁",
				By(curve, algebraic_curve.LaurentRingInOverlap.Read(L).At(k, A0, A1, A01, t)))
			ringMap := a.Have(
				"so its inclusion there is a ring map",
				"«inclusionRingMap»",
				Unfold(ring_homomorphism.RingHomomorphism),
				By(
					laurentRing,
					overlapRing,
					inclusion,
					set_basic.SubsetDef.At(a.TermAs[Set[A]]("«wcLaurent»"), A01)))

			laurentOps := a.TermAs[module_record.RingOps[A]]("«wcRing»(«wcLaurent»)")
			overlapOps := a.TermAs[module_record.RingOps[A]]("«wcOverlap»")
			inclusionMap := a.TermAs[Fun[A, A]]("λx:A. x")
			// A ring on a part of L, as a module over itself, is L's regular module restricted to that part: the same record.
			fieldModule := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			regular := a.Have(
				"k[t, 1/t] is a module over itself",
				"module_on(«wcRing»(«wcLaurent»), «wcVectors»(«wcLaurent»))",
				By(
					module.RegularModuleOn.Read(laurentRing),
					module_record.RegularModuleDef.At(laurentOps),
					module_record.RestrictModuleDef.At(fieldModule, a.TermAs[Set[A]]("«wcLaurent»"))))
			overlapModule := a.Have(
				"the overlap is a module over k[t, 1/t], read through the inclusion",
				"module_on(«wcRing»(«wcLaurent»), «wcVectors»(A₀₁))",
				By(
					ringMap,
					module.RegularModuleOn.Read(overlapRing),
					hom_module.RestrictScalarsModuleOn.At(
						laurentOps, overlapOps, inclusionMap, a.TermAs[module_record.ModuleOps[A, A]]("«wcVectors»(A₀₁)")),
					module_record.ScalarRestrictionDef.At(
						inclusionMap, a.TermAs[module_record.ModuleOps[A, A]]("«wcVectors»(A₀₁)")),
					module_record.RegularModuleDef.At(overlapOps),
					module_record.RestrictModuleDef.At(fieldModule, A01)))
			container := a.Have(
				"the container, k[t, 1/t] coextended along the inclusion, is a module over the overlap",
				"module_on(«wcOverlap», «wdDualizingModule»)",
				Simp(Fwd(CurveDualizingModuleDef)),
				By(
					ringMap,
					regular,
					hom_module.CoextendScalarsModuleOn.At(
						laurentOps,
						overlapOps,
						inclusionMap,
						a.TermAs[module_record.ModuleOps[A, A]]("«wcVectors»(«wcLaurent»)"))))
			a.Show(
				"k[t, 1/t] a subring of L inside the overlap by a ring map, "+
					"the overlap over it, and the container over the overlap",
				By(laurentSubring, inclusion, ringMap, overlapModule, container))
		}),
})}

// DualizingChartSubmodule — in the dualizing container, read as a module
// over the overlap, the maps carrying a subring S of the overlap into a set
// P holding zero and closed under sums form a submodule over S. The zero
// map, a sum and an S-multiple of such maps are maps of the container, and
// their values on S are zero, sums of values and values at s * x ∈ S, the
// container scaling through the argument.
var DualizingChartSubmodule = dualizingChartSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "DualizingChartSubmodule",
	Key:  "prop_b42212735a72863e",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀₁ S P:set(A). ∀t:A.",
		Hypotheses: []string{
			"module_on(«wcOverlap», «wdDualizingModule»)",
			"S ⊆ A₀₁",
			"subring(field_ring(L), S)",
			"L.zero ∈ P",
			"∀x y:A. x ∈ P ∧ y ∈ P ⇒ x + y ∈ P",
		},
		Conclusion: "submodule(restrict_ring(«wcOverlap», S), «wdDualizingModule», «mapsCarrying»)",
		Abbrev: Abbrev{
			{Name: "mapsCarrying", Text: "{φ:A → A | φ ∈ «wdDualizingModule».carrier ∧ image(φ, S) ⊆ P}"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k, A01, S, P *Expr[Set[A]], t *Expr[A], h Fact) {
			given := a.Conjuncts(
				h,
				"the container is a module over the overlap",
				"S lies in the overlap",
				"S is a subring of L",
				"zero lies in P",
				"P is closed under sums")
			container, sInOverlap, subringS, zeroInP, sums := given[0], given[1], given[2], given[3], given[4]
			ringS := a.Have(
				"S is a ring under L's operations",
				"comm_ring_on(restrict_ring(field_ring(L), S))",
				By(subringS, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			overlapSubring := a.Have(
				"so S, lying in the overlap, is a subring of it",
				"subring(«wcOverlap», S)",
				By(
					Normalized,
					ringS,
					sInOverlap,
					comm_ring.SubringRingOn.Read(module.RingOn.Read(container)).At(S),
					module_record.RestrictRingTwice.At(a.TermAs[module_record.RingOps[A]]("field_ring(L)"), A01, S)))
			overS := a.Have(
				"so the container is a module over S",
				"module_on(restrict_ring(«wcOverlap», S), «wdDualizingModule»)",
				By(overlapSubring, module.ModuleRestrictScalars.Read(container).At(S)))
			additive := module.AddGroupOn.Read(container)
			chart, chartDef := a.LetAs[Set[Fun[A, A]]]("C", "«mapsCarrying»")
			member := a.Have(
				"a map lies in C exactly when it is a vector carrying S into P",
				"∀φ:(A → A). φ ∈ C ⇔ φ ∈ «wdDualizingModule».carrier ∧ image(φ, S) ⊆ P",
				BySets(chartDef))

			zero := a.TermAs[A]("L.zero")
			zeroMap := a.TermAs[Fun[A, A]]("fun_zero")
			zeroValues := a.Have(
				"the zero map's values are zero, which lies in P",
				"∀x:A. x ∈ S ⇒ fun_zero(x) ∈ P",
				a.ForEach(func(x *Expr[A]) Action {
					return By(Normalized, function_module.FunZeroDef.At(zero, x), zeroInP)
				}))
			zeroIn := a.Have(
				"the zero map lies in C",
				"fun_zero ∈ C",
				By(
					member.At(zeroMap),
					group.OneIn.Read(additive),
					zeroValues,
					set_image.ImageSubsetIff.At(zeroMap, S, P)))

			sumIn := a.Have(
				"a sum of two maps of C lies in C",
				"∀u v:(A → A). u ∈ C ∧ v ∈ C ⇒ fun_add(u, v) ∈ C",
				Derive(func(b *Argument) {
					u, v := b.FixAs[Fun[A, A]]("u"), b.FixAs[Fun[A, A]]("v")
					inChart := b.Conjuncts(
						b.Assume(),
						"u lies in C",
						"v lies in C")
					ofU := b.Conjuncts(
						b.Have(
							"u is a map of the container carrying S into P",
							"u ∈ «containerMaps» ∧ image(u, S) ⊆ P",
							By(member.At(u), inChart[0])),
						"u is a map of the container",
						"u carries S into P")
					ofV := b.Conjuncts(
						b.Have(
							"so is v",
							"v ∈ «containerMaps» ∧ image(v, S) ⊆ P",
							By(member.At(v), inChart[1])),
						"v is a map of the container",
						"v carries S into P")
					sumValues := b.Have(
						"the value of u + v at x in S is u(x) + v(x), a sum of members of P",
						"∀x:A. x ∈ S ⇒ fun_add(u, v, x) ∈ P",
						Derive(func(c *Argument) {
							c.FixAs[A]("x")
							xInS := c.Assume()
							uValue := c.Have(
								"u(x) lies in P",
								"u(x) ∈ P",
								By(ofU[1], set_image.ImageSubsetIff.At(u, S, P), xInS))
							vValue := c.Have(
								"v(x) lies in P",
								"v(x) ∈ P",
								By(ofV[1], set_image.ImageSubsetIff.At(v, S, P), xInS))
							c.Show(
								"so does their sum",
								Simp(Fwd(function_module.FunAddDef)),
								By(uValue, vValue, sums.At(c.TermAs[A]("u(x)"), c.TermAs[A]("v(x)"))))
						}))
					sum := b.TermAs[Fun[A, A]]("fun_add(u, v)")
					b.Show(
						"so u + v, a map of the container carrying S into P, lies in C",
						By(
							member.At(sum),
							group.MulIn.Read(additive).At(proof.MemberOf(u, ofU[0]), proof.MemberOf(v, ofV[0])),
							sumValues,
							set_image.ImageSubsetIff.At(sum, S, P)))
				}))

			smulIn := a.Have(
				"an S-multiple of a map of C lies in C: on S it reads the map at s * x, a member of S",
				"∀c:A. ∀u:(A → A). c ∈ S ∧ u ∈ C ⇒ (λx:A. COND(x ∈ A₀₁, u(c * x), L.zero)) ∈ C",
				Derive(func(b *Argument) {
					c, u := b.FixAs[A]("c"), b.FixAs[Fun[A, A]]("u")
					assumed := b.Conjuncts(
						b.Assume(),
						"c lies in S",
						"u lies in C")
					ofU := b.Conjuncts(
						b.Have(
							"u is a map of the container carrying S into P",
							"u ∈ «containerMaps» ∧ image(u, S) ⊆ P",
							By(member.At(u), assumed[1])),
						"u is a map of the container",
						"u carries S into P")
					cInOverlap := b.Have(
						"c lies in the overlap",
						"c ∈ A₀₁",
						By(assumed[0], sInOverlap, set_basic.SubsetDef))
					scaledValues := b.Have(
						"the value of c · u at x in S is u(c * x), c * x lying in S",
						"∀x:A. x ∈ S ⇒ COND(x ∈ A₀₁, u(c * x), L.zero) ∈ P",
						Derive(func(d *Argument) {
							x := d.FixAs[A]("x")
							xInS := d.Assume()
							xInOverlap := d.Have(
								"x lies in the overlap",
								"x ∈ A₀₁",
								By(xInS, sInOverlap, set_basic.SubsetDef))
							product := comm_ring.MulIn.Read(ringS).At(proof.MemberOf(c, assumed[0]), proof.MemberOf(x, xInS))
							value := d.Have(
								"u(c * x) lies in P",
								"u(c * x) ∈ P",
								By(ofU[1], set_image.ImageSubsetIff.At(u, S, P), product))
							d.Show(
								"which is the value at x",
								By(xInOverlap, value))
						}))
					scaled := b.TermAs[Fun[A, A]]("λx:A. COND(x ∈ A₀₁, u(c * x), L.zero)")
					b.Show(
						"so c · u, a map of the container carrying S into P, lies in C",
						By(
							member.At(scaled),
							module.SmulIn.Read(container).At(proof.MemberOf(c, cInOverlap), proof.MemberOf(u, ofU[0])),
							scaledValues,
							set_image.ImageSubsetIff.At(scaled, S, P)))
				}))

			inMaps := a.Have(
				"C lies among the maps of the container",
				"C ⊆ «containerMaps»",
				BySets(a.Have(
					"each member of C is a map of the container",
					"∀φ:(A → A). φ ∈ C ⇒ φ ∈ «containerMaps»",
					a.ForEach(func(φ *Expr[Fun[A, A]]) Action { return By(member.At(φ)) }))))
			a.Show(
				"so C is a submodule over S: it lies in the container, "+
					"holds the zero map, and is closed under sums and S-multiples",
				By(inMaps, zeroIn, sumIn, smulIn, submodule.SubmoduleCriterion.Read(overS).At(chart)))
		}),
})}

// DualBasisSpans — the coordinate functionals of a finite basis E of the
// overlap over k[t, 1/t] are maps of the dualizing container, and they span
// it over the overlap. A map φ of the container is the sum over E of the
// functionals scaled by φ(e) ∈ k[t, 1/t] ⊆ A₀₁: at x in the overlap that
// sum is Σ φ(e) · coord_e(x), the scaling acting through the argument and
// the coordinates of φ(e) · x being φ(e) times those of x, and that is
// φ(Σ coord_e(x) · e) = φ(x), φ carrying a k[t, 1/t]-combination of E to
// the same combination of its values; off the overlap both sides are zero.
var DualBasisSpans = dualBasisSpansThm{family.Add(registry.ProofEntry{
	Name: "DualBasisSpans",
	Key:  "prop_c213be1e70e7e108",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀E:set(A).",
		Hypotheses: []string{
			"«wcDatum»",
			"finite(E)",
			"module_basis(«wcRing»(«wcLaurent»), «wcVectors»(A₀₁), E)",
		},
		Conclusion: "«dualBasisE» ⊆ «wdDualizingModule».carrier ∧ " +
			"«containerSpan»(«dualBasisE») = «wdDualizingModule».carrier",
		Abbrev: Abbrev{
			// e ↦ φ(e) · e*, for the map φ of the container the proof fixes.
			{Name: "scaledFunctionals", Text: "λe:A. λx:A. " +
				"    COND(x ∈ A₀₁, COND(φ(e) * x ∈ A₀₁, «overlapCoordinates»(E, φ(e) * x, e), L.zero), L.zero)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			E *Expr[Set[A]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"the curve datum",
				"E is finite",
				"E is a basis of the overlap over k[t, 1/t]")
			finiteE, basisE := given[1], given[2]
			onLaurent := a.Conjuncts(
				GroupPremises(given[0], DualizingModuleOn.Read(L).At(k, A0, A1, A01, t)),
				"k[t, 1/t] is a subring of L",
				"it lies in the overlap",
				"its inclusion is a ring map",
				"the overlap is a module over it",
				"the container is a module over the overlap")
			laurentSubring, laurentInOverlap, overlapModule, container :=
				onLaurent[0], onLaurent[1], onLaurent[3], onLaurent[4]
			laurentRing := a.Have(
				"so k[t, 1/t] is a ring under L's operations",
				"comm_ring_on(«wcRing»(«wcLaurent»))",
				By(
					laurentSubring,
					comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(a.TermAs[Set[A]]("«wcLaurent»"))))
			// k[t, 1/t] as a module over itself is L's regular module restricted to it: the same record.
			regular := a.Have(
				"k[t, 1/t] is a module over itself",
				"module_on(«wcRing»(«wcLaurent»), «wcVectors»(«wcLaurent»))",
				By(
					module.RegularModuleOn.Read(laurentRing),
					module_record.RegularModuleDef.At(a.TermAs[module_record.RingOps[A]]("«wcRing»(«wcLaurent»)")),
					module_record.RestrictModuleDef.At(
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"),
						a.TermAs[Set[A]]("«wcLaurent»"))))
			independent := a.Conjuncts(
				a.Unfolded(basisE, linear_independence.ModuleBasisDef),
				"E is independent",
				"E spans the overlap")[0]
			eInOverlap := a.Have(
				"E lies in the overlap",
				"E ⊆ A₀₁",
				By(linear_independence.IndependentInCarrier.Read(independent)))
			vectors := a.Have(
				"the container's vectors are the k[t, 1/t]-linear "+
					"maps into k[t, 1/t] from the overlap, zero off it",
				"«wdDualizingModule».carrier = «containerMaps»",
				Simp(Fwd(CurveDualizingModuleDef), Fwd(hom_module.CoextendScalarsDef)),
				Basic())

			laurentOps := a.TermAs[module_record.RingOps[A]]("«wcRing»(«wcLaurent»)")
			throughInclusion := a.TermAs[module_record.ModuleOps[A, A]]("«overlapThroughInclusion»")
			laurentVectors := a.TermAs[module_record.ModuleOps[A, A]]("«wcVectors»(«wcLaurent»)")
			star := a.TermAs[Fun[A, Fun[A, A]]](
				"λe:A. λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero)")
			zeroInLaurent := comm_ring.ZeroIn.Read(laurentRing)
			overlapRing := module.RingOn.Read(container)
			coordinates := a.Have(
				"the coordinates of a member v of the overlap lie in k[t, 1/t] and expand v",
				Statement{
					Binders: "∀v:A.",
					Hypotheses: []string{
						"v ∈ A₀₁",
					},
					Conclusion: "(∀e:A. e ∈ E ⇒ «overlapCoordinates»(E, v, e) ∈ «wcLaurent») ∧ " +
						"module_sum(L.add, L.zero, E, λe:A. «overlapCoordinates»(E, v, e) * e) = v",
				},
				Derive(func(b *Argument) {
					v := b.FixAs[A]("v")
					vIn := b.Assume()
					b.Show(
						"they are its coordinates in the basis E",
						By(
							finiteE,
							basisE,
							module_dimension.BasisCoordinatesSpec.Read(overlapModule).At(E, proof.MemberOf(v, vIn))))
				}))

			functionals := a.Have(
				"each coordinate functional is a k[t, 1/t]-linear map "+
					"from the overlap into k[t, 1/t], zero off the overlap",
				"∀e:A. e ∈ E ⇒ (λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero)) ∈ «containerMaps»",
				Derive(func(b *Argument) {
					e := b.FixAs[A]("e")
					eInE := b.Assume()
					functional := b.TermAs[Fun[A, A]]("λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero)")
					fieldModule := b.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
					coordinate := b.TermAs[Fun[A, A]]("λx:A. «overlapCoordinates»(E, x, e)")
					coordinateLinear := b.Have(
						"the coordinate at e is k[t, 1/t]-linear on the overlap",
						"module_homomorphism(«wcRing»(«wcLaurent»), "+
							"    «overlapThroughInclusion», "+
							"    «wcVectors»(«wcLaurent»), "+
							"    λx:A. «overlapCoordinates»(E, x, e))",
						By(
							finiteE,
							basisE,
							eInE,
							module_dimension.BasisCoordinateLinear.Read(overlapModule).At(E, e),
							module_record.ScalarRestrictionDef.At(
								b.TermAs[Fun[A, A]]("λx:A. x"),
								b.TermAs[module_record.ModuleOps[A, A]]("regular_module(«wcOverlap»)")),
							module_record.RegularModuleDef.At(laurentOps),
							module_record.RestrictModuleDef.At(fieldModule, b.TermAs[Set[A]]("«wcLaurent»")),
							module_record.RestrictModuleDef.At(fieldModule, A01)))
					agree := b.Have(
						"on the overlap the functional is the coordinate",
						Statement{
							Binders: "∀x:A.",
							Hypotheses: []string{
								"x ∈ A₀₁",
							},
							Conclusion: "COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero) = «overlapCoordinates»(E, x, e)",
						},
						b.ForEach(func(_ *Expr[A]) Action { return Basic() }))
					linear := b.Have(
						"so is the functional, zero off the overlap",
						"module_homomorphism(«wcRing»(«wcLaurent»), "+
							"    «overlapThroughInclusion», "+
							"    «wcVectors»(«wcLaurent»), "+
							"    λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero))",
						By(
							coordinateLinear,
							agree,
							module_homomorphism.HomCongruence.At(
								laurentOps, throughInclusion, laurentVectors, coordinate, functional)))
					vanishes := b.Have(
						"and zero off the overlap",
						"∀u:A. u ∉ A₀₁ ⇒ COND(u ∈ A₀₁, «overlapCoordinates»(E, u, e), L.zero) = L.zero",
						b.ForEach(func(_ *Expr[A]) Action { return Basic() }))
					b.Show(
						"so it is a map of the container",
						By(
							linear,
							vanishes,
							hom_module.InHomSet.At(laurentOps, throughInclusion, laurentVectors, functional)))
				}))
			dualInMaps := a.Have(
				"so they lie among the maps of the container",
				"«dualBasisE» ⊆ «containerMaps»",
				By(functionals, set_image.ImageSubsetIff.At(star, E, a.TermAs[Set[Fun[A, A]]]("«containerMaps»"))))
			dualSet := a.TermAs[Set[Fun[A, A]]]("«dualBasisE»")
			spanSub := a.Have(
				"their span is a submodule over the overlap",
				"submodule(«wcOverlap», «wdDualizingModule», «containerSpan»(«dualBasisE»))",
				By(dualInMaps, submodule.SpanSubmodule.Read(container).At(dualSet)))

			// Every map of the container is the sum of the functionals scaled by its values on E.
			add, zero := a.TermAs[Op[A]]("L.add"), a.TermAs[A]("L.zero")
			mapsInSpan := a.Have(
				"every map of the container lies in the span",
				"∀φ:(A → A). φ ∈ «containerMaps» ⇒ φ ∈ «containerSpan»(«dualBasisE»)",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[A, A]]("φ")
					φMap := b.Assume()
					φParts := b.Conjuncts(
						b.Have(
							"so φ is k[t, 1/t]-linear on the overlap and zero off it",
							"module_homomorphism(«wcRing»(«wcLaurent»), "+
								"    «overlapThroughInclusion», "+
								"    «wcVectors»(«wcLaurent»), "+
								"    φ) ∧ "+
								"(∀u:A. u ∉ A₀₁ ⇒ φ(u) = L.zero)",
							By(φMap, hom_module.InHomSet.At(laurentOps, throughInclusion, laurentVectors, φ))),
						"φ is k[t, 1/t]-linear",
						"φ is zero off the overlap")
					φLinear, φVanishes := φParts[0], φParts[1]
					values := b.Have(
						"φ takes the members of E into k[t, 1/t], inside the overlap",
						"∀e:A. e ∈ E ⇒ φ(e) ∈ «wcLaurent» ∧ φ(e) ∈ A₀₁",
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							eInE := c.Assume()
							eIn := c.Have(
								"e lies in the overlap",
								"e ∈ A₀₁",
								By(eInE, eInOverlap, set_basic.SubsetDef))
							c.Show(
								"φ(e) lies in k[t, 1/t] and so in the overlap",
								By(
									module_homomorphism.HomIn.Read(φLinear).At(proof.MemberOf(e, eIn)),
									laurentInOverlap,
									set_basic.SubsetDef))
						}))
					summand := b.TermAs[Fun2[A, A, A]]("«scaledFunctionals»")
					terms := b.Have(
						"each functional scaled by φ(e), the overlap acting through the argument, lies in the span",
						Statement{
							Binders: "∀e:A.",
							Hypotheses: []string{
								"e ∈ E",
							},
							Conclusion: "(λx:A. " +
								"    COND(x ∈ A₀₁, " +
								"        COND(φ(e) * x ∈ A₀₁, «overlapCoordinates»(E, φ(e) * x, e), L.zero), " +
								"        L.zero)) ∈ " +
								"«containerSpan»(«dualBasisE»)",
						},
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							eInE := c.Assume()
							functional := c.TermAs[Fun[A, A]]("λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero)")
							inDual := c.Have(
								"the functional at e is one of the functionals",
								"(λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero)) ∈ «dualBasisE»",
								By(eInE, set_image.FunInImage.At(star, E, e)))
							inSpan := c.Have(
								"so it lies in their span",
								"(λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero)) ∈ «containerSpan»(«dualBasisE»)",
								By(
									inDual,
									set_basic.SubsetDef,
									submodule.SubsetSpan.At(
										c.TermAs[module_record.RingOps[A]]("«wcOverlap»"),
										c.TermAs[module_record.ModuleOps[A, Fun[A, A]]]("«wdDualizingModule»"),
										dualSet)))
							scalar := c.Have(
								"φ(e) lies in the overlap",
								"φ(e) ∈ A₀₁",
								By(values, eInE))
							c.Show(
								"and the span is closed under the overlap's scaling",
								By(submodule.SubmoduleSmul.Read(spanSub).At(
									proof.MemberOf(c.TermAs[A]("φ(e)"), scalar), proof.MemberOf(functional, inSpan))))
						}))
					sumInSpan := b.Have(
						"so their sum over E lies in the span",
						"module_sum(fun_add, fun_zero, E, «scaledFunctionals») ∈ «containerSpan»(«dualBasisE»)",
						By(
							spanSub,
							finiteE,
							terms,
							submodule.SubmoduleModuleSum.Read(container).At(
								b.TermAs[Set[Fun[A, A]]]("«containerSpan»(«dualBasisE»)"), E, summand)))
					valuesInLaurent := b.Have(
						"each scaled functional takes its values in k[t, "+
							"1/t], so their sum is read at a point term by term",
						Statement{
							Binders: "∀e z:A.",
							Hypotheses: []string{
								"e ∈ E",
							},
							Conclusion: "COND(z ∈ A₀₁, " +
								"    COND(φ(e) * z ∈ A₀₁, «overlapCoordinates»(E, φ(e) * z, e), L.zero), " +
								"    L.zero) ∈ " +
								"«wcLaurent»",
						},
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							c.FixAs[A]("z")
							eInE := c.Assume()
							c.Cases(c.Term("φ(e) * z ∈ A₀₁"))
							c.When(
								"where φ(e) · z lies in the overlap the value is a coordinate of it",
								func(d *Argument, inside Fact) {
									ofProduct := d.Conjuncts(
										GroupPremises(inside, coordinates.At(d.TermAs[A]("φ(e) * z"))),
										"the coordinates of φ(e) · z lie in k[t, 1/t]",
										"they expand it")
									d.Show(
										"so the value lies in k[t, 1/t], as zero does",
										By(inside, ofProduct[0].At(e), eInE, zeroInLaurent))
								})
							c.Otherwise(
								"elsewhere the value is zero",
								func(d *Argument, outside Fact) {
									d.Show(
										"which lies in k[t, 1/t]",
										By(outside, zeroInLaurent))
								})
						}))
					expansion := b.Have(
						"that sum is φ",
						"module_sum(fun_add, fun_zero, E, «scaledFunctionals») = φ",
						Derive(func(c *Argument) {
							c.Do(Funext())
							x := c.FixAs[A]("x")
							atX := c.TermAs[Fun[A, A]](
								"λe:A. COND(x ∈ A₀₁, COND(φ(e) * x ∈ A₀₁, «overlapCoordinates»(E, φ(e) * x, e), L.zero), L.zero)")
							applied := c.Have(
								"read at x, it is the sum of the values at x",
								"module_sum(fun_add, fun_zero, E, «scaledFunctionals», x) = "+
									"module_sum(L.add, "+
									"    L.zero, "+
									"    E, "+
									"    λe:A. "+
									"        COND(x ∈ A₀₁, "+
									"            COND(φ(e) * x ∈ A₀₁, «overlapCoordinates»(E, φ(e) * x, e), L.zero), "+
									"            L.zero))",
								By(finiteE, valuesInLaurent, function_module.ModuleSumApply.Read(regular).At(E, summand, x)))
							c.Cases(c.Term("x ∈ A₀₁"))
							c.When(
								"at x in the overlap the values are φ(e) · coord_e(x), which sum to φ(x)",
								func(d *Argument, xIn Fact) {
									xm := proof.MemberOf(x, xIn)
									ofX := d.Conjuncts(
										GroupPremises(xIn, coordinates.At(x)),
										"the coordinates of x lie in k[t, 1/t]",
										"they expand x")
									coordinatesOfX := d.TermAs[Fun[A, A]]("«overlapCoordinates»(E, x)")
									termwise := d.Have(
										"each value is φ(e) · coord_e(x), the coordinates "+
											"being k[t, 1/t]-linear, which is coord_e(x) · φ(e)",
										Statement{
											Binders: "∀e:A.",
											Hypotheses: []string{
												"e ∈ E",
											},
											Conclusion: "COND(x ∈ A₀₁, " +
												"    COND(φ(e) * x ∈ A₀₁, «overlapCoordinates»(E, φ(e) * x, e), L.zero), " +
												"    L.zero) = " +
												"«overlapCoordinates»(E, x, e) * φ(e)",
										},
										Derive(func(f *Argument) {
											e := f.FixAs[A]("e")
											eInE := f.Assume()
											onE := f.Conjuncts(
												GroupPremises(eInE, values.At(e)),
												"φ(e) lies in k[t, 1/t]",
												"φ(e) lies in the overlap")
											φe := f.TermAs[A]("φ(e)")
											scaled := f.Have(
												"the coordinates of φ(e) · x are φ(e) times those of x",
												"«overlapCoordinates»(E, φ(e) * x) = λd:A. φ(e) * «overlapCoordinates»(E, x, d)",
												By(
													finiteE,
													basisE,
													module_dimension.BasisCoordinatesSmul.Read(overlapModule).At(E, proof.MemberOf(φe, onE[0]), xm)))
											value := f.Have(
												"so the value at e is φ(e) · coord_e(x)",
												"COND(x ∈ A₀₁, COND(φ(e) * x ∈ A₀₁, «overlapCoordinates»(E, φ(e) * x, e), L.zero), L.zero) = "+
													"φ(e) * «overlapCoordinates»(E, x, e)",
												By(xIn, comm_ring.MulIn.Read(overlapRing).At(proof.MemberOf(φe, onE[1]), xm), scaled))
											coordinate := f.Have(
												"coord_e(x) lies in k[t, 1/t]",
												"«overlapCoordinates»(E, x, e) ∈ «wcLaurent»",
												By(ofX[0], eInE))
											f.Show(
												"which is coord_e(x) · φ(e)",
												By(
													value,
													comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(laurentRing)).At(proof.MemberOf(φe, onE[0]),
														proof.MemberOf(f.TermAs[A]("«overlapCoordinates»(E, x, e)"), coordinate))))
										}))
									overE := d.Have(
										"so the sum of the values is Σ coord_e(x) · φ(e)",
										"module_sum(L.add, "+
											"    L.zero, "+
											"    E, "+
											"    λe:A. "+
											"        COND(x ∈ A₀₁, "+
											"            COND(φ(e) * x ∈ A₀₁, «overlapCoordinates»(E, φ(e) * x, e), L.zero), "+
											"            L.zero)) = "+
											"module_sum(L.add, L.zero, E, λe:A. «overlapCoordinates»(E, x, e) * φ(e))",
										By(
											termwise,
											module.ModuleSumCongruence.At(
												add, zero, E, atX, d.TermAs[Fun[A, A]]("λe:A. «overlapCoordinates»(E, x, e) * φ(e)"))))
									combination := d.Have(
										"φ, k[t, 1/t]-linear, carries the expansion of x in E to Σ coord_e(x) · φ(e)",
										"φ(module_sum(L.add, L.zero, E, λe:A. «overlapCoordinates»(E, x, e) * e)) = "+
											"module_sum(L.add, L.zero, E, λe:A. «overlapCoordinates»(E, x, e) * φ(e))",
										By(
											finiteE,
											d.Unfolded(eInOverlap, set_basic.SubsetDef),
											ofX[0],
											module_homomorphism.HomCombination.Read(φLinear).At(
												E, coordinatesOfX, d.TermAs[Fun[A, A]]("λe:A. e"))))
									d.Show(
										"so the sum at x is φ(x)",
										By(applied, overE, combination, ofX[1]))
								})
							c.Otherwise(
								"off the overlap every value is zero, and so is φ(x)",
								func(d *Argument, xOut Fact) {
									zeros := d.Have(
										"every value is zero",
										Statement{
											Binders: "∀e:A.",
											Hypotheses: []string{
												"e ∈ E",
											},
											Conclusion: "COND(x ∈ A₀₁, " +
												"    COND(φ(e) * x ∈ A₀₁, «overlapCoordinates»(E, φ(e) * x, e), L.zero), " +
												"    L.zero) = " +
												"L.zero",
										},
										d.ForEach(func(_ *Expr[A]) Action { return By(xOut) }))
									sumZero := d.Have(
										"so is their sum",
										"module_sum(L.add, "+
											"    L.zero, "+
											"    E, "+
											"    λe:A. "+
											"        COND(x ∈ A₀₁, "+
											"            COND(φ(e) * x ∈ A₀₁, «overlapCoordinates»(E, φ(e) * x, e), L.zero), "+
											"            L.zero)) = "+
											"L.zero",
										By(finiteE, zeros, module.ModuleSumZero.Read(regular).At(E, atX)))
									d.Show(
										"and φ vanishes off the overlap",
										By(applied, sumZero, φVanishes.At(x), xOut))
								})
						}))
					b.Show(
						"so φ lies in the span",
						expansion.Rw(),
						By(sumInSpan))
				}))
			mapsSubsetSpan := a.Have(
				"so the maps of the container lie in the span",
				"«containerMaps» ⊆ «containerSpan»(«dualBasisE»)",
				BySets(mapsInSpan))
			a.Show(
				"the functionals are vectors, and their span is all of the container",
				vectors.Rw(),
				By(dualInMaps, submodule.SubmoduleSubset.Read(spanSub), mapsSubsetSpan, set_order.SubsetAntisym))
		}),
})}

// ContainerMapsAgreeOnBasis — two maps of the dualizing container that
// agree on a finite basis E of the overlap over k[t, 1/t] are equal. Each
// is k[t, 1/t]-linear on the overlap, so its value at a member there is the
// combination of its values on E by that member's coordinates
// (HomCombination), and each is zero off the overlap.
var ContainerMapsAgreeOnBasis = containerMapsAgreeOnBasisThm{family.Add(registry.ProofEntry{
	Name: "ContainerMapsAgreeOnBasis",
	Key:  "prop_53f39e5457d5ee26",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀E:set(A). ∀φ ψ:(A → A).",
		Hypotheses: []string{
			"«wcDatum»",
			"finite(E)",
			"module_basis(«wcRing»(«wcLaurent»), «wcVectors»(A₀₁), E)",
			"φ ∈ «wdDualizingModule».carrier",
			"ψ ∈ «wdDualizingModule».carrier",
			"∀e:A. e ∈ E ⇒ φ(e) = ψ(e)",
		},
		Conclusion: "φ = ψ",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			E *Expr[Set[A]],
			φ, ψ *Expr[Fun[A, A]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"the curve datum",
				"E is finite",
				"E is a basis of the overlap over k[t, 1/t]",
				"φ is a vector of the container",
				"so is ψ",
				"φ and ψ agree on E")
			finiteE, basisE, φIn, ψIn, agreeOnE := given[1], given[2], given[3], given[4], given[5]
			overlapModule := a.Conjuncts(
				GroupPremises(given[0], DualizingModuleOn.Read(L).At(k, A0, A1, A01, t)),
				"k[t, 1/t] is a ring",
				"it lies in the overlap",
				"its inclusion is a ring map",
				"the overlap is a module over it",
				"the container is a module over the overlap")[3]
			independent := a.Conjuncts(
				a.Unfolded(basisE, linear_independence.ModuleBasisDef),
				"E is independent",
				"E spans the overlap")[0]
			eInOverlap := a.Have(
				"E lies in the overlap",
				"E ⊆ A₀₁",
				By(linear_independence.IndependentInCarrier.Read(independent)))

			// φ and ψ are k[t, 1/t]-linear on the overlap and zero off it.
			vectors := a.Have(
				"the container's vectors are the k[t, 1/t]-linear "+
					"maps into k[t, 1/t] from the overlap, zero off it",
				"«wdDualizingModule».carrier = «containerMaps»",
				Simp(Fwd(CurveDualizingModuleDef), Fwd(hom_module.CoextendScalarsDef)),
				Basic())
			laurentOps := a.TermAs[module_record.RingOps[A]]("«wcRing»(«wcLaurent»)")
			throughInclusion := a.TermAs[module_record.ModuleOps[A, A]]("«overlapThroughInclusion»")
			laurentVectors := a.TermAs[module_record.ModuleOps[A, A]]("«wcVectors»(«wcLaurent»)")
			ofφ := a.Conjuncts(
				a.Have(
					"so φ is k[t, 1/t]-linear on the overlap and zero off it",
					"module_homomorphism(«wcRing»(«wcLaurent»), "+
						"    «overlapThroughInclusion», "+
						"    «wcVectors»(«wcLaurent»), "+
						"    φ) ∧ "+
						"(∀v:A. v ∉ A₀₁ ⇒ φ(v) = L.zero)",
					By(
						a.Simplified(φIn, Fwd(vectors)),
						hom_module.InHomSet.At(laurentOps, throughInclusion, laurentVectors, φ))),
				"φ is k[t, 1/t]-linear",
				"φ vanishes off the overlap")
			ofψ := a.Conjuncts(
				a.Have(
					"and so is ψ",
					"module_homomorphism(«wcRing»(«wcLaurent»), "+
						"    «overlapThroughInclusion», "+
						"    «wcVectors»(«wcLaurent»), "+
						"    ψ) ∧ "+
						"(∀v:A. v ∉ A₀₁ ⇒ ψ(v) = L.zero)",
					By(
						a.Simplified(ψIn, Fwd(vectors)),
						hom_module.InHomSet.At(laurentOps, throughInclusion, laurentVectors, ψ))),
				"ψ is k[t, 1/t]-linear",
				"ψ vanishes off the overlap")

			a.Do(Funext())
			z := a.FixAs[A]("z")
			a.Cases(a.Term("z ∈ A₀₁"))
			a.When(
				"on the overlap z is the combination of E by its coordinates, "+
					"which φ and ψ carry to one combination of their values",
				func(d *Argument, zIn Fact) {
					coordinates := d.Conjuncts(
						GroupPremises(
							given[1],
							given[2],
							module_dimension.BasisCoordinatesSpec.Read(overlapModule).At(E, proof.MemberOf(z, zIn))),
						"the coordinates of z lie in k[t, 1/t]",
						"they vanish off E",
						"they expand z")
					coefficients := d.TermAs[Fun[A, A]]("«overlapCoordinates»(E, z)")
					inOverlap := d.Unfolded(eInOverlap, set_basic.SubsetDef)
					φz := d.Have(
						"φ(z) is the combination of the values of φ on E by the coordinates of z",
						"φ(z) = module_sum(L.add, L.zero, E, λe:A. «overlapCoordinates»(E, z, e) * φ(e))",
						By(
							finiteE,
							inOverlap,
							coordinates[0],
							coordinates[2],
							module_homomorphism.HomCombination.Read(ofφ[0]).At(
								E, coefficients, d.TermAs[Fun[A, A]]("λe:A. e"))))
					ψz := d.Have(
						"and ψ(z) that of the values of ψ",
						"ψ(z) = module_sum(L.add, L.zero, E, λe:A. «overlapCoordinates»(E, z, e) * ψ(e))",
						By(
							finiteE,
							inOverlap,
							coordinates[0],
							coordinates[2],
							module_homomorphism.HomCombination.Read(ofψ[0]).At(
								E, coefficients, d.TermAs[Fun[A, A]]("λe:A. e"))))
					agree := d.Have(
						"the terms agree, φ and ψ agreeing on E",
						"∀e:A. e ∈ E ⇒ «overlapCoordinates»(E, z, e) * φ(e) = «overlapCoordinates»(E, z, e) * ψ(e)",
						d.ForEach(func(e *Expr[A]) Action { return By(agreeOnE.At(e)) }))
					same := d.Have(
						"so the two combinations are equal",
						"module_sum(L.add, L.zero, E, λe:A. «overlapCoordinates»(E, z, e) * φ(e)) = "+
							"module_sum(L.add, L.zero, E, λe:A. «overlapCoordinates»(E, z, e) * ψ(e))",
						By(
							agree,
							module.ModuleSumCongruence.At(
								d.TermAs[Op[A]]("L.add"),
								d.TermAs[A]("L.zero"),
								E,
								d.TermAs[Fun[A, A]]("λe:A. «overlapCoordinates»(E, z, e) * φ(e)"),
								d.TermAs[Fun[A, A]]("λe:A. «overlapCoordinates»(E, z, e) * ψ(e)"))))
					d.Show(
						"so φ(z) = ψ(z)",
						By(φz, ψz, same))
				})
			a.Otherwise(
				"off the overlap both are zero",
				func(d *Argument, zOut Fact) {
					d.Show(
						"φ and ψ vanish off the overlap",
						GroupPremises(zOut, ofφ[1].At(z)).Rw(),
						GroupPremises(zOut, ofψ[1].At(z)).Rw(),
						Basic())
				})
		}),
})}

// DualizingChartsSpan — each chart of the dualizing pair spans the whole
// container over the overlap. Chart 0 holds the coordinate functionals of a
// finite basis E of A₀ over k[t], a basis of the overlap over k[t, 1/t]
// (algebraic_curve.BasisSpansOverlap): on A₀ their values are the coordinates
// over k[t]. Chart 1 holds t⁻² times the coordinate functionals of a finite
// basis F of A₁ over k[1/t], and each functional is t² times one of those. Both
// sets of functionals span the container (DualBasisSpans).
var DualizingChartsSpan = dualizingChartsSpanThm{family.Add(registry.ProofEntry{
	Name: "DualizingChartsSpan",
	Key:  "prop_e9615dd7888099f7",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«wcDatum»",
		},
		Conclusion: "«containerSpan»(fst(«wdDualizing»)) = «wdDualizingModule».carrier ∧ " +
			"«containerSpan»(snd(«wdDualizing»)) = «wdDualizingModule».carrier",
		Abbrev: Abbrev{
			{Name: "tSquare", Text: "laurent_monomial(t, &2)"},
			{Name: "tInvSquare", Text: "laurent_monomial(t, -&2)"},
			{Name: "dualBasisF", Text: "image( " +
				"    λe:A. λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(F, x, e), L.zero), F)"},
			// t⁻² · f* for the member f of F the proof fixes, and t² · (t⁻² · f*).
			{Name: "loweredFunctional", Text: "λx:A. " +
				"    COND(x ∈ A₀₁, " +
				"        COND(«tInvSquare» * x ∈ A₀₁, «overlapCoordinates»(F, «tInvSquare» * x, f), L.zero), " +
				"        L.zero)"},
			{Name: "raisedFunctional", Text: "λx:A. " +
				"    COND(x ∈ A₀₁, " +
				"        COND(«tSquare» * x ∈ A₀₁, " +
				"            COND(«tInvSquare» * («tSquare» * x) ∈ A₀₁, " +
				"                «overlapCoordinates»(F, «tInvSquare» * («tSquare» * x), f), " +
				"                L.zero), " +
				"            L.zero), " +
				"        L.zero)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			datum := a.Simplified(
				GroupPremises(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			ringL := field.RingOn.Read(L)
			chart0Ring := a.Have(
				"chart 0, a subring of L, is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), A₀))",
				By(datum, comm_ring.SubringRingOn.Read(ringL).At(A0)))
			chart0In := a.Have(
				"chart 0 lies in the overlap",
				"A₀ ⊆ A₀₁",
				By(datum))
			tm := a.MemberOf[on.L](t, a.Have(
				"t lies in L",
				"t ∈ L.carrier",
				By(datum)))
			polynomials, inversePolynomials :=
				a.TermAs[Set[A]]("«wcPolynomials»"), a.TermAs[Set[A]]("«wcInversePolynomials»")
			line := a.Conjuncts(
				a.Have(
					"k[t] and k[1/t] are subrings of L inside k[t, 1/t]",
					"subring(field_ring(L), «wcPolynomials») ∧ "+
						"subring(field_ring(L), «wcInversePolynomials») ∧ "+
						"«wcPolynomials» ⊆ «wcLaurent» ∧ "+
						"«wcInversePolynomials» ⊆ «wcLaurent»",
					By(datum)),
				"k[t] is a subring of L",
				"k[1/t] is a subring of L",
				"k[t] lies in k[t, 1/t]",
				"k[1/t] lies in k[t, 1/t]")
			onLaurent := a.Conjuncts(
				GroupPremises(curve, DualizingModuleOn.Read(L).At(k, A0, A1, A01, t)),
				"k[t, 1/t] is a ring",
				"it lies in the overlap",
				"its inclusion is a ring map",
				"the overlap is a module over it",
				"the container is a module over the overlap")
			overlapModule, container := onLaurent[3], onLaurent[4]
			laurentOps := a.TermAs[module_record.RingOps[A]]("«wcRing»(«wcLaurent»)")
			overlapVectors := a.TermAs[module_record.ModuleOps[A, A]]("«wcVectors»(A₀₁)")
			// A chart as a module over itself is L's regular module restricted to the chart, and k[t] read
			// inside a chart's ring is k[t] read inside L: the same records.
			fieldOps, fieldModule :=
				a.TermAs[module_record.RingOps[A]]("field_ring(L)"),
				a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			chart0Ops, chart1Ops :=
				a.TermAs[module_record.RingOps[A]]("«wcRing»(A₀)"),
				a.TermAs[module_record.RingOps[A]]("«wcRing»(A₁)")
			vectors := a.Have(
				"the container's vectors are the k[t, 1/t]-linear "+
					"maps into k[t, 1/t] from the overlap, zero off it",
				"«wdDualizingModule».carrier = «containerMaps»",
				Simp(Fwd(CurveDualizingModuleDef), Fwd(hom_module.CoextendScalarsDef)),
				Basic())
			overlapBases := a.Conjuncts(
				GroupPremises(curve, algebraic_curve.BasisSpansOverlap.Read(L).At(k, A0, A1, A01, t)),
				"a basis of chart 0 over k[t] is a basis of the overlap over k[t, 1/t]",
				"so is a basis of chart 1 over k[1/t]")
			lineCharts := a.Conjuncts(
				a.Have(
					"the charts of O(−2) on the line are k[t] and t⁻² · k[1/t]",
					"fst(«lineDualizing») = «wcPolynomials» ∧ "+
						"snd(«lineDualizing») = image(L.mul(laurent_monomial(t, -&2)), «wcInversePolynomials»)",
					Simp(Fwd(projective_line.ProjectiveLinePairDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
					Basic()),
				"chart 0 of O(−2) is k[t]",
				"chart 1 of O(−2) is t⁻² · k[1/t]")
			omega := a.Conjuncts(
				a.Have(
					"the charts of ω are the maps carrying A₀ into k[t] and A₁ into t⁻² · k[1/t]",
					"fst(«wdDualizing») = «omegaChart0» ∧ snd(«wdDualizing») = «omegaChart1»",
					Simp(
						Fwd(CurveDualizingPairDef),
						Fwd(pairs.Fst),
						Fwd(pairs.Snd),
						Fwd(CurveDualizingModuleDef),
						Fwd(hom_module.CoextendScalarsDef)),
					Basic()),
				"chart 0 of ω",
				"chart 1 of ω")
			chart0Def := a.Let("C_0", a.Term("«omegaChart0»"))
			chart1Def := a.Let("C_1", a.Term("«omegaChart1»"))
			member0 := a.Have(
				"a map lies in C₀ exactly when it is a map of the container carrying A₀ into chart 0 of O(−2)",
				"∀φ:(A → A). φ ∈ C₀ ⇔ φ ∈ «containerMaps» ∧ image(φ, A₀) ⊆ fst(«lineDualizing»)",
				BySets(chart0Def))
			member1 := a.Have(
				"and in C₁ when it is a map of the container carrying A₁ into chart 1 of O(−2)",
				"∀φ:(A → A). φ ∈ C₁ ⇔ φ ∈ «containerMaps» ∧ image(φ, A₁) ⊆ snd(«lineDualizing»)",
				BySets(chart1Def))

			// Chart 0: the coordinate functionals of a basis of A₀ over k[t].
			E, basis0 := a.UnpackAs[Set[A]](a.Have(
				"chart 0 has a finite basis over k[t]",
				"∃E:set(A). finite(E) ∧ «wcBasisOfChart»(E)",
				By(datum)), "E")
			ofE := a.Conjuncts(
				basis0,
				"E is finite",
				"E is a basis of chart 0 over k[t]")
			overlapBasisE := a.Have(
				"E is a basis of the overlap over k[t, 1/t]",
				"module_basis(«wcRing»(«wcLaurent»), «wcVectors»(A₀₁), E)",
				By(basis0, overlapBases[0].At(E)))
			dualE := a.Conjuncts(
				GroupPremises(curve, ofE[0], overlapBasisE, DualBasisSpans.Read(L).At(k, A0, A1, A01, t, E)),
				"the coordinate functionals of E are vectors",
				"they span the container")
			polynomialsIn0Subring := a.Have(
				"k[t], a ring lying in chart 0, is a subring of it",
				"subring(«wcRing»(A₀), «wcPolynomials»)",
				By(
					line[0],
					comm_ring.SubringRingOn.Read(ringL).At(polynomials),
					datum,
					comm_ring.SubringRingOn.Read(chart0Ring).At(polynomials),
					module_record.RestrictRingTwice.At(fieldOps, A0, polynomials)))
			module0 := a.Have(
				"chart 0 is a module over k[t], a subring of it",
				"module_on(«wcRing»(«wcPolynomials»), «wcVectors»(A₀))",
				By(
					polynomialsIn0Subring,
					module.RegularModuleOverSubring.Read(chart0Ring).At(polynomials),
					module_record.RestrictRingDef.At(chart0Ops, polynomials),
					module_record.RestrictRingDef.At(fieldOps, polynomials),
					module_record.RegularModuleDef.At(chart0Ops),
					module_record.RestrictModuleDef.At(fieldModule, A0)))
			functionalValues := a.Have(
				"on A₀ the coordinate functionals of E take the coordinates over k[t], which lie in k[t]",
				"∀e:A. "+
					"    e ∈ E ⇒ ∀x:A. x ∈ A₀ ⇒ COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero) ∈ «wcPolynomials»",
				Derive(func(b *Argument) {
					e := b.FixAs[A]("e")
					eInE := b.Assume()
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					xInOverlap := b.Have(
						"x lies in the overlap",
						"x ∈ A₀₁",
						By(xIn, chart0In, set_basic.SubsetDef))
					same := b.Have(
						"its coordinates over k[t, 1/t] are those over k[t]",
						"«overlapCoordinates»(E, x) = "+
							"module_basis_coordinates(«wcRing»(«wcPolynomials»), «wcVectors»(A₀), E, x)",
						By(
							line[2],
							chart0In,
							module0,
							ofE[0],
							ofE[1],
							overlapBasisE,
							xIn,
							module_dimension.BasisCoordinatesRestrict.Read(overlapModule).At(polynomials, A0, E, x),
							module_record.RestrictRingDef.At(laurentOps, polynomials),
							module_record.RestrictModuleDef.At(overlapVectors, A0),
							module_record.RestrictRingDef.At(fieldOps, polynomials),
							module_record.RestrictModuleDef.At(fieldModule, A0)))
					overPolynomials := b.Conjuncts(
						GroupPremises(
							ofE[0], ofE[1], module_dimension.BasisCoordinatesSpec.Read(module0).At(E, proof.MemberOf(x, xIn))),
						"the coordinates over k[t] lie in k[t]",
						"they vanish off E",
						"they expand x")
					b.Show(
						"so the value at x lies in k[t]",
						By(xInOverlap, same, overPolynomials[0].At(e), eInE))
				}))
			starE := a.TermAs[Fun[A, Fun[A, A]]](
				"λe:A. λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero)")
			dualInChart0 := a.Have(
				"so chart 0 holds the coordinate functional of each member of E",
				"∀e:A. e ∈ E ⇒ (λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero)) ∈ C₀",
				Derive(func(b *Argument) {
					e := b.FixAs[A]("e")
					eInE := b.Assume()
					functional := b.TermAs[Fun[A, A]]("λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero)")
					functionalMap := b.Have(
						"it is a map of the container",
						"(λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero)) ∈ «containerMaps»",
						By(eInE, set_image.FunInImage.At(starE, E, e), dualE[0], set_basic.SubsetDef))
					intoPolynomials := b.Have(
						"it carries A₀ into k[t]",
						"image(λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero), A₀) ⊆ «wcPolynomials»",
						By(functionalValues.At(e), eInE, set_image.ImageSubsetIff.At(functional, A0, polynomials)))
					intoChart := b.Have(
						"that is, into chart 0 of O(−2)",
						"image(λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero), A₀) ⊆ fst(«lineDualizing»)",
						lineCharts[0].Rw(),
						By(intoPolynomials))
					b.Show(
						"so it lies in C₀",
						By(member0.At(functional), functionalMap, intoChart))
				}))
			overlapOps := a.TermAs[module_record.RingOps[A]]("«wcOverlap»")
			containerOps := a.TermAs[module_record.ModuleOps[A, Fun[A, A]]]("«wdDualizingModule»")
			maps := a.TermAs[Set[Fun[A, A]]]("«containerMaps»")
			chart0Set := a.TermAs[Set[Fun[A, A]]]("C₀")
			dualSetE := a.TermAs[Set[Fun[A, A]]]("«dualBasisE»")
			chart0Maps := a.Have(
				"C₀ lies among the maps of the container",
				"C₀ ⊆ «containerMaps»",
				BySets(a.Have(
					"each member of C₀ is a map of the container",
					"∀φ:(A → A). φ ∈ C₀ ⇒ φ ∈ «containerMaps»",
					a.ForEach(func(φ *Expr[Fun[A, A]]) Action { return By(member0.At(φ)) }))))
			span0Sub := a.Have(
				"so its span is a submodule over the overlap",
				"submodule(«wcOverlap», «wdDualizingModule», «containerSpan»(C₀))",
				By(chart0Maps, submodule.SpanSubmodule.Read(container).At(chart0Set)))
			span0Set := a.TermAs[Set[Fun[A, A]]]("«containerSpan»(C₀)")
			least0 := a.Have(
				"the span of chart 0, holding the functionals of E, holds their span",
				"«containerSpan»(«dualBasisE») ⊆ «containerSpan»(C₀)",
				By(
					span0Sub,
					dualInChart0,
					set_image.ImageSubsetIff.At(starE, E, chart0Set),
					submodule.SubsetSpan.At(overlapOps, containerOps, chart0Set),
					set_order.SubsetTrans.At(dualSetE, chart0Set, span0Set),
					submodule.SpanLeast.At(overlapOps, containerOps, dualSetE, span0Set)))
			span0 := a.Have(
				"chart 0 spans the container",
				"«containerSpan»(C₀) = «wdDualizingModule».carrier",
				vectors.Rw(),
				By(
					submodule.SubmoduleSubset.Read(span0Sub),
					dualE[1],
					least0,
					set_order.SubsetAntisym.At(span0Set, maps)))

			// Chart 1: t⁻² times the coordinate functionals of a basis of A₁ over k[1/t].
			chart1Ring := a.Have(
				"chart 1, a subring of L, is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), A₁))",
				By(datum, comm_ring.SubringRingOn.Read(ringL).At(A1)))
			chart1In := a.Have(
				"chart 1 lies in the overlap",
				"A₁ ⊆ A₀₁",
				By(datum))
			overlapSubring := a.Have(
				"the overlap is a subring of L",
				"subring(field_ring(L), A₀₁)",
				By(datum))
			overlapInL := a.Have(
				"so it lies in L",
				"A₀₁ ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(overlapSubring)))
			F, basis1 := a.UnpackAs[Set[A]](a.Have(
				"chart 1 has a finite basis over k[1/t]",
				"∃F:set(A). finite(F) ∧ «wcBasisOfInverseChart»(F)",
				By(datum)), "F")
			ofF := a.Conjuncts(
				basis1,
				"F is finite",
				"F is a basis of chart 1 over k[1/t]")
			overlapBasisF := a.Have(
				"F is a basis of the overlap over k[t, 1/t]",
				"module_basis(«wcRing»(«wcLaurent»), «wcVectors»(A₀₁), F)",
				By(basis1, overlapBases[1].At(F)))
			dualF := a.Conjuncts(
				GroupPremises(curve, ofF[0], overlapBasisF, DualBasisSpans.Read(L).At(k, A0, A1, A01, t, F)),
				"the coordinate functionals of F are vectors",
				"they span the container")
			inversePolynomialsIn1Subring := a.Have(
				"k[1/t], a ring lying in chart 1, is a subring of it",
				"subring(«wcRing»(A₁), «wcInversePolynomials»)",
				By(
					line[1],
					comm_ring.SubringRingOn.Read(ringL).At(inversePolynomials),
					datum,
					comm_ring.SubringRingOn.Read(chart1Ring).At(inversePolynomials),
					module_record.RestrictRingTwice.At(fieldOps, A1, inversePolynomials)))
			module1 := a.Have(
				"chart 1 is a module over k[1/t], a subring of it",
				"module_on(«wcRing»(«wcInversePolynomials»), «wcVectors»(A₁))",
				By(
					inversePolynomialsIn1Subring,
					module.RegularModuleOverSubring.Read(chart1Ring).At(inversePolynomials),
					module_record.RestrictRingDef.At(chart1Ops, inversePolynomials),
					module_record.RestrictRingDef.At(fieldOps, inversePolynomials),
					module_record.RegularModuleDef.At(chart1Ops),
					module_record.RestrictModuleDef.At(fieldModule, A1)))
			tInvSqIn := a.Conjuncts(
				a.Have(
					"t⁻² lies in k[t, 1/t] and in the overlap",
					"«tInvSquare» ∈ «wcLaurent» ∧ «tInvSquare» ∈ A₀₁",
					By(
						datum,
						onLaurent[1],
						set_basic.SubsetDef,
						laurent_polynomial.LaurentMonomialInRing.Read(L).At(k, tm, a.TermAs[Int]("-&2")))),
				"t⁻² lies in k[t, 1/t]",
				"t⁻² lies in the overlap")
			tSqIn := a.Conjuncts(
				a.Have(
					"t² lies in k[t, 1/t] and in the overlap",
					"«tSquare» ∈ «wcLaurent» ∧ «tSquare» ∈ A₀₁",
					By(
						datum,
						onLaurent[1],
						set_basic.SubsetDef,
						laurent_polynomial.LaurentMonomialInRing.Read(L).At(k, tm, a.TermAs[Int]("&2")))),
				"t² lies in k[t, 1/t]",
				"t² lies in the overlap")
			cancel := a.Have(
				"t² · t⁻² = one",
				"«tSquare» * «tInvSquare» = L.one",
				By(datum, laurent_polynomial.LaurentMonomialInverse.Read(L).At(tm, a.TermAs[Int]("&2"))))
			chart1Set := a.TermAs[Set[Fun[A, A]]]("C₁")
			chart1Maps := a.Have(
				"C₁ lies among the maps of the container",
				"C₁ ⊆ «containerMaps»",
				BySets(a.Have(
					"each member of C₁ is a map of the container",
					"∀φ:(A → A). φ ∈ C₁ ⇒ φ ∈ «containerMaps»",
					a.ForEach(func(φ *Expr[Fun[A, A]]) Action { return By(member1.At(φ)) }))))
			span1Sub := a.Have(
				"so its span is a submodule over the overlap",
				"submodule(«wcOverlap», «wdDualizingModule», «containerSpan»(C₁))",
				By(chart1Maps, submodule.SpanSubmodule.Read(container).At(chart1Set)))
			tInvSq, tSq := a.TermAs[A]("«tInvSquare»"), a.TermAs[A]("«tSquare»")
			starF := a.TermAs[Fun[A, Fun[A, A]]](
				"λe:A. λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(F, x, e), L.zero)")
			dualInSpan1 := a.Have(
				"the coordinate functional of each member of F lies in the span of chart "+
					"1: it is t² times t⁻² times itself, and t⁻² times it lies in chart 1",
				"∀f:A. f ∈ F ⇒ (λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(F, x, f), L.zero)) ∈ «containerSpan»(C₁)",
				Derive(func(b *Argument) {
					f := b.FixAs[A]("f")
					fInF := b.Assume()
					functional := b.TermAs[Fun[A, A]]("λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(F, x, f), L.zero)")
					lowered := b.TermAs[Fun[A, A]]("«loweredFunctional»")
					functionalMap := b.Have(
						"the functional of f is a map of the container",
						"(λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(F, x, f), L.zero)) ∈ «containerMaps»",
						By(fInF, set_image.FunInImage.At(starF, F, f), dualF[0], set_basic.SubsetDef))
					loweredValues := b.Have(
						"on A₁ the values of t⁻² times it lie in t⁻² · "+
							"k[1/t]: they are t⁻² times the coordinates over k[1/t]",
						Statement{
							Binders: "∀x:A.",
							Hypotheses: []string{
								"x ∈ A₁",
							},
							Conclusion: "COND(x ∈ A₀₁, " +
								"    COND(«tInvSquare» * x ∈ A₀₁, «overlapCoordinates»(F, «tInvSquare» * x, f), L.zero), " +
								"    L.zero) ∈ " +
								"image(L.mul(«tInvSquare»), «wcInversePolynomials»)",
						},
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xIn := c.Assume()
							xInOverlap := c.Have(
								"x lies in the overlap",
								"x ∈ A₀₁",
								By(xIn, chart1In, set_basic.SubsetDef))
							xm := proof.MemberOf(x, xInOverlap)
							scaled := c.Have(
								"the coordinates of t⁻² · x are t⁻² times those of x",
								"«overlapCoordinates»(F, «tInvSquare» * x) = λd:A. «tInvSquare» * «overlapCoordinates»(F, x, d)",
								By(
									ofF[0],
									overlapBasisF,
									module_dimension.BasisCoordinatesSmul.Read(overlapModule).At(
										F, proof.MemberOf(tInvSq, tInvSqIn[0]), xm)))
							same := c.Have(
								"the coordinates of x over k[t, 1/t] are those over k[1/t]",
								"«overlapCoordinates»(F, x) = "+
									"module_basis_coordinates(«wcRing»(«wcInversePolynomials»), «wcVectors»(A₁), F, x)",
								By(
									line[3],
									chart1In,
									module1,
									ofF[0],
									ofF[1],
									overlapBasisF,
									xIn,
									module_dimension.BasisCoordinatesRestrict.Read(overlapModule).At(inversePolynomials, A1, F, x),
									module_record.RestrictRingDef.At(laurentOps, inversePolynomials),
									module_record.RestrictModuleDef.At(overlapVectors, A1),
									module_record.RestrictRingDef.At(fieldOps, inversePolynomials),
									module_record.RestrictModuleDef.At(fieldModule, A1)))
							overInverse := c.Conjuncts(
								GroupPremises(
									ofF[0], ofF[1], module_dimension.BasisCoordinatesSpec.Read(module1).At(F, proof.MemberOf(x, xIn))),
								"the coordinates over k[1/t] lie in k[1/t]",
								"they vanish off F",
								"they expand x")
							coordinate := c.TermAs[A](
								"module_basis_coordinates(«wcRing»(«wcInversePolynomials»), «wcVectors»(A₁), F, x, f)")
							inImage := c.Have(
								"t⁻² times the coordinate at f over k[1/t] lies in t⁻² · k[1/t]",
								"«tInvSquare» * "+
									"module_basis_coordinates(«wcRing»(«wcInversePolynomials»), «wcVectors»(A₁), F, x, f) ∈ "+
									"image(L.mul(«tInvSquare»), «wcInversePolynomials»)",
								By(
									overInverse[0].At(f),
									fInF,
									set_image.FunInImage.At(
										c.TermAs[Fun[A, A]]("L.mul(«tInvSquare»)"), inversePolynomials, coordinate)))
							value := c.Have(
								"the value at x is t⁻² times the coordinate of x at f over k[1/t]",
								"COND(x ∈ A₀₁, "+
									"    COND(«tInvSquare» * x ∈ A₀₁, «overlapCoordinates»(F, «tInvSquare» * x, f), L.zero), "+
									"    L.zero) = "+
									"«tInvSquare» * "+
									"module_basis_coordinates(«wcRing»(«wcInversePolynomials»), «wcVectors»(A₁), F, x, f)",
								By(
									xInOverlap,
									comm_ring.MulIn.Read(module.RingOn.Read(container)).At(proof.MemberOf(tInvSq, tInvSqIn[1]), xm),
									scaled,
									same))
							c.Show(
								"which lies in t⁻² · k[1/t]",
								value.Rw(),
								By(inImage))
						}))
					intoChart := b.Have(
						"so t⁻² times it carries A₁ into chart 1 of O(−2)",
						"image(«loweredFunctional», A₁) ⊆ snd(«lineDualizing»)",
						lineCharts[1].Rw(),
						By(
							loweredValues,
							set_image.ImageSubsetIff.At(
								lowered, A1, b.TermAs[Set[A]]("image(L.mul(«tInvSquare»), «wcInversePolynomials»)"))))
					loweredInChart := b.Have(
						"so it lies in C₁",
						"(«loweredFunctional») ∈ C₁",
						By(
							member1.At(lowered),
							module.SmulIn.Read(container).At(
								proof.MemberOf(tInvSq, tInvSqIn[1]), proof.MemberOf(functional, functionalMap)),
							intoChart))
					loweredInSpan := b.Have(
						"and in its span",
						"(«loweredFunctional») ∈ «containerSpan»(C₁)",
						By(
							loweredInChart,
							submodule.SubsetSpan.At(overlapOps, containerOps, chart1Set),
							set_basic.SubsetDef))
					raised := b.Have(
						"so t² times it lies in the span too",
						"(«raisedFunctional») ∈ «containerSpan»(C₁)",
						By(submodule.SubmoduleSmul.Read(span1Sub).At(
							proof.MemberOf(tSq, tSqIn[1]), proof.MemberOf(lowered, loweredInSpan))))
					back := b.Have(
						"and t² times t⁻² times the functional is the functional",
						"(«raisedFunctional») = λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(F, x, f), L.zero)",
						Derive(func(c *Argument) {
							c.Do(Funext())
							x := c.FixAs[A]("x")
							c.Cases(c.Term("x ∈ A₀₁"))
							c.When(
								"on the overlap t⁻² · (t² · x) = x",
								func(d *Argument, xIn Fact) {
									xm := d.MemberOf[on.L](x, d.Have(
										"x lies in L",
										"x ∈ L.carrier",
										By(xIn, overlapInL, set_basic.SubsetDef)))
									tInvSqm := d.MemberOf[on.L](tInvSq, d.Have(
										"t⁻² lies in L",
										"«tInvSquare» ∈ L.carrier",
										By(tInvSqIn[1], overlapInL, set_basic.SubsetDef)))
									tSqm := d.MemberOf[on.L](tSq, d.Have(
										"t² lies in L",
										"«tSquare» ∈ L.carrier",
										By(tSqIn[1], overlapInL, set_basic.SubsetDef)))
									undone := d.Have(
										"t⁻² · (t² · x) = x",
										"«tInvSquare» * («tSquare» * x) = x",
										ByArith(ringL, xm, tInvSqm, tSqm, Scaled(x, cancel)))
									d.Show(
										"so both sides are the coordinate of x at f",
										By(
											Normalized,
											xIn,
											comm_ring.MulIn.Read(module.RingOn.Read(container)).At(
												proof.MemberOf(tSq, tSqIn[1]), proof.MemberOf(x, xIn)),
											undone))
								})
							c.Otherwise(
								"off the overlap both sides are zero",
								func(d *Argument, xOut Fact) {
									d.Show(
										"both are zero",
										By(xOut))
								})
						}))
					b.Show(
						"so it lies in the span",
						back.Rw(),
						By(raised))
				}))
			dualSetF := a.TermAs[Set[Fun[A, A]]]("«dualBasisF»")
			span1Set := a.TermAs[Set[Fun[A, A]]]("«containerSpan»(C₁)")
			least1 := a.Have(
				"the span of chart 1, holding the functionals of F, holds their span",
				"«containerSpan»(«dualBasisF») ⊆ «containerSpan»(C₁)",
				By(
					span1Sub,
					dualInSpan1,
					set_image.ImageSubsetIff.At(starF, F, span1Set),
					submodule.SpanLeast.At(overlapOps, containerOps, dualSetF, span1Set)))
			span1 := a.Have(
				"chart 1 spans the container",
				"«containerSpan»(C₁) = «wdDualizingModule».carrier",
				vectors.Rw(),
				By(
					submodule.SubmoduleSubset.Read(span1Sub),
					dualF[1],
					least1,
					set_order.SubsetAntisym.At(span1Set, maps)))
			a.Show(
				"both charts of ω span the container",
				omega[0].Rw(),
				omega[1].Rw(),
				By(chart0Def, chart1Def, span0, span1))
		}),
})}

// ---------------------------------------------------------------------------
// Maps into the dualizing pair and Serre duality
// ---------------------------------------------------------------------------

// HomDualizingSections — the maps of the structure pair into ω are its
// sections: evaluation at one is a k-isomorphism from Hom(O, ω) onto
// H⁰(ω).
var HomDualizingSections = homDualizingSectionsThm{family.Add(registry.ProofEntry{
	Name: "HomDualizingSections",
	Key:  "prop_ca95ca2d764f9051",
	Reading: "A map ψ of lattice pairs out of O is linear over the overlap on A₀₁, so ψ(x) = x · " +
		"ψ(one); ψ(one) lies on both charts of ω because one lies on both charts of O. Conversely a " +
		"section v of ω gives x ↦ x · v on A₀₁, zero off it. This is the classical Hom(O, ω) = H⁰(ω).",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«wcDatum»",
		},
		Conclusion: "module_isomorphism(«wdScalars», " +
			"    «wdDualizingMaps»((A₀, A₁)), " +
			"    lattice_pair_h0(«wdDualizingModule», «wdDualizing»), " +
			"    λψ:(A → A → A). ψ(L.one))",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			data := a.Conjuncts(
				GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in the field",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field under L's operations",
				"the constants lie in both charts")
			biaffine, structurePair, ambientIsOverlap, kField, kInCharts :=
				data[1], data[3], data[4], data[6], data[7]
			omegaParts := a.Conjuncts(
				GroupPremises(curve, DualizingIsLattice.Read(L).At(k, A0, A1, A01, t)),
				"ω is an overlap module",
				"the two dualizing charts form a lattice pair",
				"its ambient is the overlap module")
			overlap, overlapDef := a.LetAs[module_record.RingOps[A]]("overlap", "«wcOverlap»")
			omega, omegaDef := a.LetAs[module_record.ModuleOps[A, Fun[A, A]]]("omega", "«wdDualizingModule»")
			dualizing, dualizingDef := a.LetAs[Prod[Set[Fun[A, A]], Set[Fun[A, A]]]](
				"dualizing", "«wdDualizing»")
			maps, mapsDef := a.LetAs[module_record.ModuleOps[A, Fun2[A, A, A]]](
				"maps", "«wdDualizingMaps»((A₀, A₁))")
			sections, sectionsDef := a.LetAs[module_record.ModuleOps[A, Fun[A, A]]](
				"sections", "lattice_pair_h0(omega, dualizing)")
			omegaModule, omegaLattice := omegaParts[0], omegaParts[1]
			cover := a.Unfolded(biaffine, lattice_pair.BiaffineDef)
			overlapRing := a.Have(
				"the overlap is a ring",
				"comm_ring_on(overlap)",
				By(cover))
			chart0Subring := a.Have(
				"chart zero is a subring of it",
				"subring(overlap, A₀)",
				By(cover))
			chart1Subring := a.Have(
				"and so is chart one",
				"subring(overlap, A₁)",
				By(cover))
			fieldOps := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			fieldModule := a.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
			structure := a.TermAs[_LatticePair]("(A₀, A₁)")
			scalars := a.TermAs[module_record.RingOps[A]]("restrict_ring(overlap, k)")
			records := a.Conjuncts(
				a.Have(
					"the overlap has the field's unit and its own regular module",
					"overlap.one = L.one ∧ regular_module(overlap) = «wcVectors»(A₀₁)",
					overlapDef.Rw(),
					Simp(
						Fwd(module_record.RestrictRingDef),
						Fwd(module_record.RegularModuleDef),
						Fwd(module_record.RestrictModuleDef)),
					TrivialNormalized()),
				"its unit is the field's unit",
				"its regular module is the restricted field module")
			overlapOne, overlapRegular := records[0], records[1]
			kInOverlap := a.Have(
				"the constants lie in the overlap",
				"k ⊆ overlap.carrier",
				BySets(comm_ring.SubringSubset.Read(chart0Subring), kInCharts))
			kRing := a.Have(
				"the constants form a ring",
				"comm_ring_on(«wcRing»(k))",
				By(
					field.RingOn.Read(kField),
					field.FieldRingDef.At(a.TermAs[field.FieldOps[A]]("restrict_field(L, k)")),
					module_record.RestrictRingDef.At(fieldOps, k)))
			kSubring := a.Have(
				"the constants are a subring of the overlap",
				"subring(overlap, k)",
				By(
					Normalized,
					kRing,
					kInOverlap,
					overlapDef,
					module_record.RestrictRingTwice.At(fieldOps, A01, k),
					comm_ring.SubringRingOn.Read(overlapRing).At(k)))
			constants := a.Have(
				"the constants lie in each chart",
				"k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(kInCharts))
			omegaOverK := a.Have(
				"ω is a module over the constants",
				"module_on(restrict_ring(overlap, k), omega)",
				By(omegaModule, kSubring, module.ModuleRestrictScalars.At(overlap, omega, k)))
			sectionSubmodule := a.Have(
				"the intersection of the dualizing charts is a k-submodule",
				"submodule(restrict_ring(overlap, k), omega, fst(dualizing) ∩ snd(dualizing))",
				By(constants, omegaLattice, lattice_pair.H0Submodule.At(overlap, A0, A1, k, omega, dualizing)))
			mapsModule := a.Have(
				"the pair maps form a k-module",
				"module_on(restrict_ring(overlap, k), maps)",
				Simp(Fwd(mapsDef), Fwd(CurveDualizingMapsDef), Rev(overlapDef), Rev(omegaDef), Rev(dualizingDef)),
				By(
					kSubring,
					constants,
					structurePair,
					omegaLattice,
					biaffine,
					lattice_pair_map.PairMapsLinearSpace.At(
						overlap, A0, A1, k, fieldModule, omega, structure, dualizing)))
			sectionsModule := a.Have(
				"the sections form a k-module",
				"module_on(restrict_ring(overlap, k), sections)",
				Simp(Fwd(sectionsDef), Fwd(lattice_pair.LatticePairH0Def)),
				By(
					omegaOverK,
					sectionSubmodule,
					submodule.SubmoduleModuleOn.At(
						scalars, omega, a.TermAs[Set[Fun[A, A]]]("fst(dualizing) ∩ snd(dualizing)"))))
			pairMaps := a.Have(
				"a pair map is a normalized overlap-linear map preserving both charts",
				"∀ψ:(A → A → A). "+
					"    ψ ∈ maps.carrier ⇔ "+
					"    ψ ∈ hom_set(overlap, regular_module(overlap), omega) ∧ "+
					"    image(ψ, A₀) ⊆ fst(dualizing) ∧ "+
					"    image(ψ, A₁) ⊆ snd(dualizing)",
				Simp(
					Fwd(mapsDef),
					Fwd(CurveDualizingMapsDef),
					Fwd(lattice_pair_map.LatticePairHomDef),
					Rev(overlapDef),
					Rev(omegaDef),
					Rev(dualizingDef),
					Fwd(ambientIsOverlap),
					Rev(overlapRegular),
					Fwd(lattice_pair_map.LatticePairMapsDef)),
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				BySets())
			oneInCharts := a.Have(
				"one lies on both charts",
				"L.one ∈ A₀ ∧ L.one ∈ A₁",
				By(
					Normalized,
					comm_ring.SubringOne.Read(chart0Subring),
					comm_ring.SubringOne.Read(chart1Subring),
					overlapOne))
			chartSubmodules := a.Have(
				"each dualizing chart is a module over the corresponding curve chart",
				"submodule(restrict_ring(overlap, A₀), omega, fst(dualizing)) ∧ "+
					"submodule(restrict_ring(overlap, A₁), omega, snd(dualizing))",
				By(omegaLattice, lattice_pair.LatticePairDef.At(overlap, A0, A1, omega, dualizing)))
			charts := a.Conjuncts(
				chartSubmodules,
				"the first dualizing chart is an A₀-module",
				"the second dualizing chart is an A₁-module")
			chart0Submodule, chart1Submodule := charts[0], charts[1]
			sectionCarrier := a.Have(
				"a section belongs to both dualizing charts",
				"sections.carrier = fst(dualizing) ∩ snd(dualizing)",
				Simp(Fwd(sectionsDef), Fwd(lattice_pair.LatticePairH0Def)),
				TrivialNormalized())
			_, scalingDef := a.LetAs[Fun[Fun[A, A], Fun2[A, A, A]]](
				"scaling", "λv:(A → A). λx:A. COND(x ∈ overlap.carrier, omega.smul(x, v), omega.zero)")
			evaluationIn := a.Have(
				"evaluation at one gives a section",
				"∀ψ:(A → A → A). ψ ∈ maps.carrier ⇒ ψ(L.one) ∈ sections.carrier",
				Derive(func(b *Argument) {
					ψ := b.FixAs[Fun2[A, A, A]]("ψ")
					ψIn := b.Assume()
					b.Show(
						"the images of one lie in both charts",
						BySets(ψIn, oneInCharts, sectionCarrier, pairMaps.At(ψ)))
				}))
			scalingLifts := a.Have(
				"a section defines a pair map whose value at one is that section",
				"∀v:(A → A). v ∈ sections.carrier ⇒ scaling(v) ∈ maps.carrier ∧ scaling(v)(L.one) = v",
				Derive(func(b *Argument) {
					v := b.FixAs[Fun[A, A]]("v")
					vIn := b.Assume()
					inOmega := b.Have(
						"the section lies in the overlap module",
						"v ∈ omega.carrier",
						BySets(vIn, sectionCarrier, submodule.SubmoduleSubset.Read(sectionSubmodule)))
					normalized := b.Have(
						"its normalized scalar map is overlap-linear",
						"scaling(v) ∈ hom_set(overlap, regular_module(overlap), omega)",
						scalingDef.Rw(),
						By(overlapRing, omegaModule, inOmega, hom_module.ScalarMapIsRegularHom.At(overlap, omega, v)))
					chart0 := b.Have(
						"the scalar map preserves chart zero",
						"image(scaling(v), A₀) ⊆ fst(dualizing)",
						scalingDef.Rw(),
						Simp(Fwd(set_image.ImageSubsetIff)),
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xIn := c.Assume()
							inputs := c.Have(
								"the scalar lies in the overlap and the section in the first chart",
								"x ∈ overlap.carrier ∧ v ∈ fst(dualizing)",
								BySets(xIn, vIn, sectionCarrier, comm_ring.SubringSubset.Read(chart0Subring)))
							c.Show(
								"the first dualizing chart is closed under its chart scalars",
								By(xIn, inputs, submodule.SubmoduleSmul.Read(chart0Submodule).AsFact().At(x, v)))
						}))
					chart1 := b.Have(
						"the scalar map preserves chart one",
						"image(scaling(v), A₁) ⊆ snd(dualizing)",
						scalingDef.Rw(),
						Simp(Fwd(set_image.ImageSubsetIff)),
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xIn := c.Assume()
							inputs := c.Have(
								"the scalar lies in the overlap and the section in the second chart",
								"x ∈ overlap.carrier ∧ v ∈ snd(dualizing)",
								BySets(xIn, vIn, sectionCarrier, comm_ring.SubringSubset.Read(chart1Subring)))
							c.Show(
								"the second dualizing chart is closed under its chart scalars",
								By(xIn, inputs, submodule.SubmoduleSmul.Read(chart1Submodule).AsFact().At(x, v)))
						}))
					b.Show(
						"scaling by the section is a pair map with value v at one",
						SplitConj(
							Case(
								"the map lies in the pair-map space",
								By(normalized, chart0, chart1, pairMaps.At(b.TermAs[Fun2[A, A, A]]("scaling(v)")))),
							Case(
								"its value at one is v",
								scalingDef.Rw(),
								By(
									Normalized,
									inOmega,
									overlapOne,
									comm_ring.OneIn.Read(overlapRing),
									module.SmulOne.Read(omegaModule).AsFact().At(v)))))
				}))
			reconstructed := a.Have(
				"evaluation at one determines every pair map",
				"∀ψ:(A → A → A). ψ ∈ maps.carrier ⇒ ψ = scaling(ψ(L.one))",
				Derive(func(b *Argument) {
					ψ := b.FixAs[Fun2[A, A, A]]("ψ")
					ψIn := b.Assume()
					b.Show(
						"a pair map's values are the scalar multiples of its value at one",
						scalingDef.Rw(),
						By(
							Normalized,
							overlapRing,
							ψIn,
							pairMaps.At(ψ),
							overlapOne,
							hom_module.RegularHomIsScalarMap.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[Fun[A, A]]()).At(
								overlap, omega, ψ)))
				}))
			evaluation := a.TermAs[Fun[Fun2[A, A, A], Fun[A, A]]]("λψ:(A → A → A). ψ(L.one)")
			linear := a.Have(
				"evaluation at one is k-linear",
				"module_homomorphism(restrict_ring(overlap, k), maps, sections, λψ:(A → A → A). ψ(L.one))",
				Unfold(module_homomorphism.ModuleHomomorphismDef),
				SplitConjAll(
					Case(
						"the source, the pair maps, is a k-module",
						By(mapsModule)),
					Case(
						"the target, the sections, is a k-module",
						By(sectionsModule)),
					Case(
						"evaluation at one carries a pair map to a section",
						By(evaluationIn)),
					Case(
						"evaluation at one preserves addition: (ψ + φ)(one) = ψ(one) + φ(one)",
						Simp(
							Fwd(mapsDef),
							Fwd(CurveDualizingMapsDef),
							Fwd(lattice_pair_map.LatticePairHomDef),
							Fwd(sectionsDef),
							Fwd(lattice_pair.LatticePairH0Def),
							Fwd(hom_module.HomModuleDef),
							Fwd(module_record.RestrictModuleDef),
							Rev(omegaDef),
							Fwd(function_module.FunAddDef)),
						TrivialNormalized()),
					Case(
						"evaluation at one preserves scalar multiplication: (c · ψ)(one) = c · ψ(one)",
						Simp(
							Fwd(mapsDef),
							Fwd(CurveDualizingMapsDef),
							Fwd(lattice_pair_map.LatticePairHomDef),
							Fwd(sectionsDef),
							Fwd(lattice_pair.LatticePairH0Def),
							Fwd(hom_module.HomModuleDef),
							Fwd(module_record.RestrictModuleDef),
							Rev(omegaDef),
							Fwd(function_module.FunSmulDef)),
						TrivialNormalized())))
			injective := a.Have(
				"equal values at one give equal pair maps",
				"injective_on(maps.carrier, λψ:(A → A → A). ψ(L.one))",
				Unfold(functions.InjectiveOnDef),
				Derive(func(b *Argument) {
					x, y := b.FixAs[Fun2[A, A, A]]("x"), b.FixAs[Fun2[A, A, A]]("y")
					sameValue := b.Assume()
					b.Show(
						"both maps are the scaling by their common value",
						By(Normalized, sameValue, reconstructed.At(x), reconstructed.At(y)))
				}))
			onto := a.Have(
				"each section is the value at one of its scalar map",
				"image(λψ:(A → A → A). ψ(L.one), maps.carrier) = sections.carrier",
				BySets(evaluationIn, scalingLifts))
			a.Show(
				"evaluation at one is the k-isomorphism from Hom(O, ω) to its sections",
				By(
					linear,
					injective,
					onto,
					module_homomorphism.ModuleIsomorphismDef.At(scalars, maps, sections, evaluation)))
		}),
})}

// SerreDualityPairing — Serre duality on the curve: for every lattice pair M of
// the curve in its function field, the pairing that sends ψ to the coefficient
// of t⁻¹ in x ↦ ψ(x)(one) is a k-isomorphism from Hom(M, ω) onto the k-dual of
// H¹(M). It is the composite of the identification of Hom(M, ω) with the maps
// of M on the line into O(−2) (DualizingMapsOnLine) and the line's duality
// (LineSerreDuality), M being a lattice pair on the line with the curve's H¹
// (algebraic_curve.CurvePairOnLine).
var SerreDualityPairing = serreDualityPairingThm{family.Add(registry.ProofEntry{
	Name: "SerreDualityPairing",
	Key:  "prop_ba0303cc29b48054",
	Reading: "Neither invertibility nor finiteness of M is asked: the isomorphism holds " +
		"for every lattice pair of the curve, and for an infinite-dimensional H¹(M) it " +
		"reaches the whole algebraic dual, as on the line. ω and the pairing are both made " +
		"from the map to the line that t gives — the functional reads the coefficient of t⁻¹ " +
		"— and the statement says nothing of another choice of t; t being transcendental " +
		"over k, a clause of the datum, is what makes that coefficient well defined.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"lattice_pair(«wcOverlap», A₀, A₁, «wcField», M)",
		},
		Conclusion: "module_isomorphism(«wdScalars», " +
			"    «wdDualizingMaps»(M), " +
			"    hom_module(«wdScalars», «wdH1»(M), «wcVectors»(k)), " +
			"    λψ:(A → A → A). λX:set(A). " +
			"        projective_line_duality_map(L, k, t, «wcField», M, λx:A. ψ(x)(L.one), X))",
		Abbrev: Abbrev{
			{Name: "lineFunctional", Text: "λφ:(A → A). λX:set(A). " +
				"    projective_line_duality_map(L, k, t, «wcField», M, φ, X)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M *Expr[_LatticePair],
			given Fact,
		) {
			givenParts := a.Conjuncts(
				given,
				"the curve lies over the line",
				"M is a lattice pair of the curve")
			datum := a.Simplified(
				GroupPremises(givenParts[0], algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			tm := a.MemberOf[on.L](t, a.Have(
				"t lies in L",
				"t ∈ L.carrier",
				By(datum)))
			onLine := a.Conjuncts(
				GroupPremises(
					givenParts[0], givenParts[1], algebraic_curve.CurvePairOnLine.Read(L).At(k, A0, A1, A01, t, M)),
				"M is a lattice pair on the line",
				"with the curve's ambient",
				"and the curve's H¹")
			evaluation := a.Have(
				"evaluation at one identifies Hom(M, ω) with the pair maps of M into O(−2) on the line",
				"module_isomorphism(«wdScalars», "+
					"    «wdDualizingMaps»(M), "+
					"    lattice_pair_hom(«wcRing»(«wcLaurent»), «wcField», M, «wcField», «lineDualizing»), "+
					"    «evaluationAtOne»)",
				By(given, DualizingMapsOnLine.Read(L).At(k, A0, A1, A01, t, M)))
			lineRing, curveRing :=
				a.TermAs[module_record.RingOps[A]]("«wcRing»(«wcLaurent»)"),
				a.TermAs[module_record.RingOps[A]]("«wcOverlap»")
			lineDuality := a.Have(
				"Serre duality on the line identifies those with the "+
					"k-dual of H¹(M), the coefficient of t⁻¹ being the pairing",
				"module_isomorphism(«wdScalars», "+
					"    lattice_pair_hom(«wcRing»(«wcLaurent»), «wcField», M, «wcField», «lineDualizing»), "+
					"    hom_module(«wdScalars», «wdH1»(M), «wcVectors»(k)), "+
					"    «lineFunctional»)",
				By(
					projective_line_duality.LineSerreDuality.Read(L).At(
						k, tm, a.TermAs[module_record.ModuleOps[A, A]]("«wcField»"), M),
					datum,
					onLine[0],
					onLine[2],
					module_record.RestrictRingDef.At(lineRing, k),
					module_record.RestrictRingDef.At(curveRing, k)))
			composite := a.Have(
				"so is their composite",
				"module_isomorphism(«wdScalars», "+
					"    «wdDualizingMaps»(M), "+
					"    hom_module(«wdScalars», «wdH1»(M), «wcVectors»(k)), "+
					"    «lineFunctional» ∘ «evaluationAtOne»)",
				By(
					module_homomorphism.IsomorphismCompose.At(
						a.TermAs[module_record.RingOps[A]]("«wdScalars»"),
						a.TermAs[module_record.ModuleOps[A, Fun[A, Fun[A, A]]]]("«wdDualizingMaps»(M)"),
						a.TermAs[module_record.ModuleOps[A, Fun[A, A]]](
							"lattice_pair_hom(«wcRing»(«wcLaurent»), «wcField», M, «wcField», «lineDualizing»)"),
						a.TermAs[module_record.ModuleOps[A, Fun[Set[A], A]]](
							"hom_module(«wdScalars», «wdH1»(M), «wcVectors»(k))"),
						a.TermAs[Fun[Fun[A, Fun[A, A]], Fun[A, A]]]("«evaluationAtOne»"),
						a.TermAs[Fun[Fun[A, A], Fun[Set[A], A]]]("«lineFunctional»")),
					evaluation,
					lineDuality))
			pairing := a.Simplified(composite, Fwd(functions.ComposeApply))
			a.Show(
				"the composite is the pairing: ψ read at one, then the coefficient of t⁻¹",
				By(pairing))
		}),
})}

// DualizingMapsOnLine — evaluation at one is a k-isomorphism from the maps
// of a lattice pair M of the curve into ω onto the maps of M, read as a
// lattice pair on the line, into O(−2). It is the coextension's
// adjunction for the inclusion of k[t, 1/t] in A₀₁, read on the pair
// maps: ψ(m) carries A₀ into k[t] exactly when ψ(y · m)(one) lies in k[t]
// for every y of A₀, as ψ(m)(y) = ψ(y · m)(one) and A₀ · fst(M) ⊆ fst(M);
// and a map of the ambient into L that carries fst(M) into k[t] takes its
// values in k[t, 1/t], every member of the ambient being brought into
// fst(M) by a power of t.
var DualizingMapsOnLine = dualizingMapsOnLineThm{family.Add(registry.ProofEntry{
	Name: "DualizingMapsOnLine",
	Key:  "prop_e3b76f70200c631e",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"lattice_pair(«wcOverlap», A₀, A₁, «wcField», M)",
		},
		Conclusion: "module_isomorphism(«wdScalars», " +
			"    «wdDualizingMaps»(M), " +
			"    lattice_pair_hom(«wcRing»(«wcLaurent»), «wcField», M, «wcField», «lineDualizing»), " +
			"    «evaluationAtOne»)",
		Abbrev: Abbrev{
			{Name: "laurentMapsOfOverlap", Text: "hom_set(«wcRing»(«wcLaurent»), " +
				"    «wcVectors»(A₀₁), " +
				"    «wcVectors»(«wcLaurent»))"},
			{Name: "ambientModule", Text: "restrict_module(«wcField», «ambientOnCurve»)"},
			{Name: "ambientBareModule", Text: "scalar_restriction(λx:A. x, «ambientModule»)"},
			{Name: "omegaPairMaps", Text: "lattice_pair_maps(«wcOverlap», " +
				"    «wcField», " +
				"    M, " +
				"    «wdDualizingModule», " +
				"    «wdDualizing»)"},
			{Name: "overlapLinearMaps", Text: "hom_set(«wcOverlap», «ambientModule», «wdDualizingModule»)"},
			{Name: "laurentLinearMaps", Text: "hom_set(«wcRing»(«wcLaurent»), " +
				"    «ambientBareModule», " +
				"    «wcVectors»(«wcLaurent»))"},
			{Name: "lineLinearMaps", Text: "hom_set(«wcRing»(«wcLaurent»), «ambientModule», «wcField»)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M *Expr[_LatticePair],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the curve lies over the line",
				"M is a lattice pair of the curve")
			curve, pair := parts[0], parts[1]

			// The two data: the curve's charts and the line's.
			datum := a.Simplified(
				GroupPremises(parts[0], algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			tm := a.MemberOf[on.L](t, a.Have(
				"t lies in L",
				"t ∈ L.carrier",
				By(datum)))
			invTm := a.TermAs[A]("L.inv(t)")
			ringL := field.RingOn.Read(L)
			laurent := a.Conjuncts(
				a.Have(
					"k[t, 1/t] is a subring of L holding k and t, as k[t] does",
					"subring(field_ring(L), «wcLaurent») ∧ k ⊆ «wcLaurent» ∧ t ∈ «wcLaurent»",
					BySets(datum)),
				"k[t, 1/t] is a subring of L",
				"holding k",
				"and t")
			laurentRing := a.Have(
				"so it is a ring under L's operations",
				"comm_ring_on(«wcRing»(«wcLaurent»))",
				By(laurent[0], comm_ring.SubringRingOn.Read(ringL).At(a.TermAs[Set[A]]("«wcLaurent»"))))
			lineModule := a.Have(
				"L is a module over k[t, 1/t]",
				"module_on(«wcRing»(«wcLaurent»), «wcField»)",
				By(datum))
			constantsOnLine := a.Have(
				"k lies in k[t] and in k[1/t]",
				"k ⊆ «wcPolynomials» ∧ k ⊆ «wcInversePolynomials»",
				By(datum))
			curveBiaffine := a.Have(
				"the curve's charts, glued along A₀₁, are a biaffine datum",
				"biaffine(«wcOverlap», A₀, A₁, t, L.inv(t))",
				By(datum))
			overlapRing := a.Have(
				"the overlap, a subring of L, is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), A₀₁))",
				By(datum, comm_ring.SubringRingOn.Read(ringL).At(A01)))
			chartRings := a.Have(
				"both charts are subrings of L, which lie in the overlap",
				"subring(field_ring(L), A₀) ∧ subring(field_ring(L), A₁) ∧ A₀ ⊆ A₀₁ ∧ A₁ ⊆ A₀₁",
				By(datum))
			chartRing := a.Conjuncts(
				chartRings,
				"chart 0 is a subring of L",
				"chart 1 is a subring of L",
				"chart 0 lies in the overlap",
				"chart 1 lies in the overlap")
			oneIn := a.Have(
				"one lies in both charts",
				"L.one ∈ A₀ ∧ L.one ∈ A₁",
				By(comm_ring.SubringOne.Read(chartRing[0]), comm_ring.SubringOne.Read(chartRing[1])))
			constants := a.Have(
				"the constants lie in both charts, which meet in them",
				"k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(datum))
			kField := a.Have(
				"k is a field under the field's operations",
				"field_on(restrict_field(L, k))",
				By(datum))
			kRing := a.Have(
				"so k is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), k))",
				By(
					field.RingOn.Read(kField),
					field.FieldRingDef.At(a.TermAs[field.FieldOps[A]]("restrict_field(L, k)")),
					module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("field_ring(L)"), k)))

			// M on the curve and on the line, with one ambient.
			lineRing := a.TermAs[module_record.RingOps[A]]("«wcRing»(«wcLaurent»)")
			curveRing := a.TermAs[module_record.RingOps[A]]("«wcOverlap»")
			fieldOps := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
			polynomials, inversePolynomials :=
				a.TermAs[Set[A]]("«wcPolynomials»"), a.TermAs[Set[A]]("«wcInversePolynomials»")
			ambientSet := a.TermAs[Set[A]]("«ambientOnCurve»")
			chart0Set, chart1Set := a.TermAs[Set[A]]("fst(M)"), a.TermAs[Set[A]]("snd(M)")
			onLine := a.Conjuncts(
				GroupPremises(parts[0], parts[1], algebraic_curve.CurvePairOnLine.Read(L).At(k, A0, A1, A01, t, M)),
				"M is a lattice pair on the line",
				"with the curve's ambient",
				"and the curve's H¹")
			onCurve := a.Conjuncts(
				a.Unfolded(pair, lattice_pair.LatticePairDef),
				"L is a module over the overlap",
				"fst(M) is a module over chart 0",
				"snd(M) is a module over chart 1",
				"the two charts span one submodule")
			curveAmbient := a.Conjuncts(
				GroupPremises(parts[1], lattice_pair.AmbientContains.At(curveRing, A0, A1, vectors, M)),
				"the ambient is a submodule over the overlap",
				"holding fst(M)",
				"and snd(M)")
			lineAmbient := a.Have(
				"on the line the ambient is a submodule over k[t, 1/t]",
				"submodule(«wcRing»(«wcLaurent»), «wcField», «ambientOnCurve»)",
				By(
					lattice_pair.AmbientContains.At(lineRing, polynomials, inversePolynomials, vectors, M),
					onLine[0],
					onLine[1]))
			ambientMembers := a.Have(
				"v lies in the ambient exactly when it lies in L and a power of t brings it into fst(M)",
				"∀v:A. "+
					"    v ∈ «ambientOnCurve» ⇔ v ∈ L.carrier ∧ (∃n:num. monoid_pow(L.mul, L.one, t, n) * v ∈ fst(M))",
				Derive(func(b *Argument) {
					span := b.Have(
						"the ambient, the span of fst(M), is the vectors a power of t brings into fst(M)",
						"«ambientOnCurve» = {v:A | v ∈ L.carrier ∧ (∃n:num. monoid_pow(L.mul, L.one, t, n) * v ∈ fst(M))}",
						Unfold(lattice_pair.LatticePairAmbientDef),
						By(
							lattice_pair.ChartSpanAway.At(curveRing, A0, A1, t, invTm, vectors, chart0Set),
							curveBiaffine,
							onCurve[0],
							onCurve[1]))
					b.Show(
						"read at each vector",
						BySets(span))
				}))

			// Evaluation at one: the coextension's adjunction along k[t, 1/t] ⊆ A₀₁,
			// whose hypotheses are the ring map, k[t, 1/t] over itself and the
			// ambient over A₀₁.
			inclusionRingMap := a.Have(
				"the inclusion of k[t, 1/t] in A₀₁ is a ring map",
				"«inclusionRingMap»",
				By(curve, DualizingModuleOn.Read(L).At(k, A0, A1, A01, t)))
			laurentModule := a.Have(
				"k[t, 1/t] is a module over itself",
				"module_on(«wcRing»(«wcLaurent»), «wcVectors»(«wcLaurent»))",
				By(
					module.RegularModuleOn.Read(laurentRing),
					module_record.RegularModuleDef.At(lineRing),
					module_record.RestrictModuleDef.At(
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"),
						a.TermAs[Set[A]]("«wcLaurent»"))))
			ambientOverOverlap := a.Have(
				"the ambient of M is a module over the overlap",
				"module_on(«wcOverlap», «ambientModule»)",
				By(submodule.SubmoduleModuleOn.At(curveRing, vectors, ambientSet), onCurve[0], curveAmbient[0]))
			adjunction := a.Simplified(
				GroupPremises(laurentModule, inclusionRingMap, ambientOverOverlap, hom_module.CoextendScalarsAdjunction.At(
					lineRing,
					curveRing,
					a.TermAs[Fun[A, A]]("λx:A. x"),
					a.TermAs[module_record.ModuleOps[A, A]]("«wcVectors»(«wcLaurent»)"),
					a.TermAs[module_record.ModuleOps[A, A]]("«ambientModule»"))),
				Rev(CurveDualizingModuleDef))
			iso := a.Conjuncts(
				a.Unfolded(adjunction, module_homomorphism.ModuleIsomorphismDef),
				"evaluation at one is linear over k[t, 1/t]",
				"one-to-one on the overlap-linear maps",
				"onto the k[t, 1/t]-linear maps into k[t, 1/t]")
			evaluation := a.Conjuncts(
				a.Unfolded(iso[0], module_homomorphism.ModuleHomomorphismDef),
				"the overlap-linear maps into ω's container are a module over k[t, 1/t]",
				"so are the k[t, 1/t]-linear maps into k[t, 1/t]",
				"evaluation carries the one into the other",
				"evaluation adds",
				"evaluation is k[t, 1/t]-linear")

			// The maps in play, read pointwise.
			curveMaps := a.Have(
				"a pair map into ω is an overlap-linear map of the ambient "+
					"whose values on a chart of M lie in that chart of ω",
				"∀ψ:(A → A → A). "+
					"    ψ ∈ «omegaPairMaps» ⇔ "+
					"    ψ ∈ «overlapLinearMaps» ∧ "+
					"    (∀m:A. m ∈ fst(M) ⇒ ψ(m) ∈ fst(«wdDualizing»)) ∧ "+
					"    (∀m:A. m ∈ snd(M) ⇒ ψ(m) ∈ snd(«wdDualizing»))",
				Unfold(lattice_pair_map.LatticePairMapsDef),
				Simp(Fwd(set_image.ImageSubsetIff)),
				BySets())
			lineMaps := a.Have(
				"a pair map into O(−2) on the line is a k[t, 1/t]-linear map of the "+
					"ambient into L whose values on a chart of M lie in that chart of O(−2)",
				"∀φ:(A → A). "+
					"    φ ∈ «linePairMaps» ⇔ "+
					"    φ ∈ «lineLinearMaps» ∧ "+
					"    (∀x:A. x ∈ fst(M) ⇒ φ(x) ∈ fst(«lineDualizing»)) ∧ "+
					"    (∀x:A. x ∈ snd(M) ⇒ φ(x) ∈ snd(«lineDualizing»))",
				Unfold(lattice_pair_map.LatticePairMapsDef),
				onLine[1].Rw(),
				Simp(Fwd(set_image.ImageSubsetIff)),
				BySets())
			dualizing0 := a.Have(
				"chart 0 of ω is the maps of the container whose value at each member of A₀ lies in k[t]",
				"∀φ:(A → A). "+
					"    φ ∈ fst(«wdDualizing») ⇔ "+
					"    φ ∈ «laurentMapsOfOverlap» ∧ (∀y:A. y ∈ A₀ ⇒ φ(y) ∈ fst(«lineDualizing»))",
				Simp(
					Fwd(CurveDualizingPairDef),
					Fwd(CurveDualizingModuleDef),
					Fwd(hom_module.CoextendScalarsDef),
					Fwd(module_record.ScalarRestrictionDef),
					Fwd(pairs.Fst),
					Fwd(set_image.ImageSubsetIff),
					Fwd(module_record.RestrictModuleDef)),
				BySets())
			dualizing1 := a.Have(
				"chart 1 of ω is the maps of the container whose value at each member of A₁ lies in t⁻² · k[1/t]",
				"∀φ:(A → A). "+
					"    φ ∈ snd(«wdDualizing») ⇔ "+
					"    φ ∈ «laurentMapsOfOverlap» ∧ (∀y:A. y ∈ A₁ ⇒ φ(y) ∈ snd(«lineDualizing»))",
				Simp(
					Fwd(CurveDualizingPairDef),
					Fwd(CurveDualizingModuleDef),
					Fwd(hom_module.CoextendScalarsDef),
					Fwd(module_record.ScalarRestrictionDef),
					Fwd(pairs.Snd),
					Fwd(set_image.ImageSubsetIff),
					Fwd(module_record.RestrictModuleDef)),
				BySets())
			curveSourceOps := a.TermAs[module_record.ModuleOps[A, A]]("«ambientModule»")
			containerOps := a.TermAs[module_record.ModuleOps[A, Fun[A, A]]]("«wdDualizingModule»")
			curveLinear := a.Have(
				"an overlap-linear ψ takes its values in the container, and a "+
					"scalar y of the overlap moves into the argument of the value",
				Statement{
					Binders: "∀ψ:(A → A → A).",
					Hypotheses: []string{
						"ψ ∈ «overlapLinearMaps»",
					},
					Conclusion: "(∀n:A. n ∈ «ambientOnCurve» ⇒ ψ(n) ∈ «laurentMapsOfOverlap») ∧ " +
						"(∀y n:A. y ∈ A₀₁ ∧ n ∈ «ambientOnCurve» ⇒ ψ(y * n) = λx:A. COND(x ∈ A₀₁, ψ(n)(y * x), L.zero))",
				},
				Derive(func(b *Argument) {
					ψ := b.FixAs[Fun[A, Fun[A, A]]]("ψ")
					hom := b.Have(
						"ψ is a homomorphism over the overlap",
						"module_homomorphism(«wcOverlap», «ambientModule», «wdDualizingModule», ψ)",
						By(hom_module.InHomSet.At(curveRing, curveSourceOps, containerOps, ψ), b.Assume()))
					linear := b.Unfolded(hom, module_homomorphism.ModuleHomomorphismDef)
					// The overlap read as L's regular module on A₀₁ is the overlap the container's maps start from.
					b.Show(
						"which is what a homomorphism of the ambient into the container says",
						By(
							linear,
							module_record.ScalarRestrictionDef.At(
								b.TermAs[Fun[A, A]]("λx:A. x"),
								b.TermAs[module_record.ModuleOps[A, A]]("regular_module(«wcOverlap»)")),
							module_record.RestrictModuleDef.At(
								b.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"), A01)))
				}))
			lineSource := a.Have(
				"on the line the ambient is a module over k[t, 1/t]",
				"module_on(«wcRing»(«wcLaurent»), «ambientModule»)",
				By(submodule.SubmoduleModuleOn.At(lineRing, vectors, ambientSet), lineModule, lineAmbient))
			lineLinear := a.Have(
				"a k[t, 1/t]-linear map of the ambient into L, read pointwise",
				"∀φ:(A → A). "+
					"    φ ∈ «lineLinearMaps» ⇔ "+
					"    (∀u:A. u ∈ «ambientOnCurve» ⇒ φ(u) ∈ L.carrier) ∧ "+
					"    (∀u v:A. u ∈ «ambientOnCurve» ∧ v ∈ «ambientOnCurve» ⇒ φ(u + v) = φ(u) + φ(v)) ∧ "+
					"    (∀c u:A. c ∈ «wcLaurent» ∧ u ∈ «ambientOnCurve» ⇒ φ(c * u) = c * φ(u)) ∧ "+
					"    (∀u:A. u ∉ «ambientOnCurve» ⇒ φ(u) = L.zero)",
				Simp(Fwd(hom_module.InHomSet), Fwd(module_homomorphism.ModuleHomomorphismDef)),
				By(lineSource, lineModule))
			laurentLinear := a.Have(
				"a k[t, 1/t]-linear map of the ambient into k[t, 1/t], read pointwise",
				"∀φ:(A → A). "+
					"    φ ∈ «laurentLinearMaps» ⇔ "+
					"    (∀u:A. u ∈ «ambientOnCurve» ⇒ φ(u) ∈ «wcLaurent») ∧ "+
					"    (∀u v:A. u ∈ «ambientOnCurve» ∧ v ∈ «ambientOnCurve» ⇒ φ(u + v) = φ(u) + φ(v)) ∧ "+
					"    (∀c u:A. c ∈ «wcLaurent» ∧ u ∈ «ambientOnCurve» ⇒ φ(c * u) = c * φ(u)) ∧ "+
					"    (∀u:A. u ∉ «ambientOnCurve» ⇒ φ(u) = L.zero)",
				Simp(Fwd(hom_module.InHomSet), Fwd(module_homomorphism.ModuleHomomorphismDef)),
				By(
					lineSource,
					module_record.RestrictModuleDef.At(vectors, ambientSet),
					module_record.ScalarRestrictionDef.At(
						a.TermAs[Fun[A, A]]("λx:A. x"),
						a.TermAs[module_record.ModuleOps[A, A]]("«ambientModule»")),
					laurentModule))

			intoField := a.Have(
				"a k[t, 1/t]-linear map of the ambient into k[t, 1/t] is one into L",
				"∀φ:(A → A). φ ∈ «laurentLinearMaps» ⇒ φ ∈ «lineLinearMaps»",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[A, A]]("φ")
					linear := b.Conjuncts(
						b.Have(
							"φ is k[t, 1/t]-linear on the ambient with values in k[t, 1/t], and zero off it",
							"(∀u:A. u ∈ «ambientOnCurve» ⇒ φ(u) ∈ «wcLaurent») ∧ "+
								"(∀u v:A. u ∈ «ambientOnCurve» ∧ v ∈ «ambientOnCurve» ⇒ φ(u + v) = φ(u) + φ(v)) ∧ "+
								"(∀c u:A. c ∈ «wcLaurent» ∧ u ∈ «ambientOnCurve» ⇒ φ(c * u) = c * φ(u)) ∧ "+
								"(∀u:A. u ∉ «ambientOnCurve» ⇒ φ(u) = L.zero)",
							By(laurentLinear.At(φ), b.Assume())),
						"φ takes its values in k[t, 1/t]",
						"φ adds",
						"φ is k[t, 1/t]-linear",
						"φ is zero off the ambient")
					values := b.Have(
						"so its values lie in L",
						"∀u:A. u ∈ «ambientOnCurve» ⇒ φ(u) ∈ L.carrier",
						By(
							linear[0],
							comm_ring.SubringSubset.Read(laurent[0]),
							set_basic.SubsetDef.At(b.TermAs[Set[A]]("«wcLaurent»"), b.TermAs[Set[A]]("L.carrier"))))
					b.Show(
						"a k[t, 1/t]-linear map of the ambient into L",
						By(lineLinear.At(φ), values, linear[1], linear[2], linear[3]))
				}))
			intoLaurent := a.Have(
				"a pair map into O(−2) on the line takes its values in k[t, 1/t]",
				"∀φ:(A → A). φ ∈ «linePairMaps» ⇒ φ ∈ «laurentLinearMaps»",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[A, A]]("φ")
					onLineMap := b.Conjuncts(
						b.Have(
							"φ is k[t, 1/t]-linear into L and carries each chart of M into the same chart of O(−2)",
							"φ ∈ «lineLinearMaps» ∧ "+
								"(∀x:A. x ∈ fst(M) ⇒ φ(x) ∈ fst(«lineDualizing»)) ∧ "+
								"(∀x:A. x ∈ snd(M) ⇒ φ(x) ∈ snd(«lineDualizing»))",
							By(lineMaps.At(φ), b.Assume())),
						"φ is a linear map into L",
						"it carries fst(M) into k[t]",
						"and snd(M) into t⁻² · k[1/t]")
					linear := b.Conjuncts(
						b.Have(
							"φ is k[t, 1/t]-linear on the ambient with values in L, and zero off it",
							"(∀u:A. u ∈ «ambientOnCurve» ⇒ φ(u) ∈ L.carrier) ∧ "+
								"(∀u v:A. u ∈ «ambientOnCurve» ∧ v ∈ «ambientOnCurve» ⇒ φ(u + v) = φ(u) + φ(v)) ∧ "+
								"(∀c u:A. c ∈ «wcLaurent» ∧ u ∈ «ambientOnCurve» ⇒ φ(c * u) = c * φ(u)) ∧ "+
								"(∀u:A. u ∉ «ambientOnCurve» ⇒ φ(u) = L.zero)",
							By(lineLinear.At(φ), onLineMap[0])),
						"φ takes its values in L",
						"φ adds",
						"φ is k[t, 1/t]-linear",
						"φ is zero off the ambient")
					lineChart0 := b.Have(
						"chart 0 of O(−2) is k[t]",
						"fst(«lineDualizing») = «wcPolynomials»",
						Simp(Fwd(projective_line.ProjectiveLinePairDef)),
						By(pairs.Fst))
					powers := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(laurentRing))
					values := b.Have(
						"φ(u) lies in k[t, 1/t]: a power tⁿ brings u into fst(M), so tⁿ · φ(u) = φ(tⁿ · u) lies in k[t]",
						"∀u:A. u ∈ «ambientOnCurve» ⇒ φ(u) ∈ «wcLaurent»",
						Derive(func(c *Argument) {
							u := c.FixAs[A]("u")
							uIn := c.Assume()
							n, cleared := c.ObtainAs[Nat](
								"some power tⁿ brings u into fst(M)",
								"∃n:num. monoid_pow(L.mul, L.one, t, n) * u ∈ fst(M)",
								By(ambientMembers.At(u), uIn))
							power := powers.At(proof.MemberOf(t, laurent[2]), n)
							moved := c.Have(
								"φ moves tⁿ out",
								"φ(monoid_pow(L.mul, L.one, t, n) * u) = monoid_pow(L.mul, L.one, t, n) * φ(u)",
								By(linear[2].At(c.TermAs[A]("monoid_pow(L.mul, L.one, t, n)"), u), power, uIn))
							inPolynomials := c.Have(
								"so tⁿ · φ(u) lies in k[t], chart 0 of O(−2)",
								"monoid_pow(L.mul, L.one, t, n) * φ(u) ∈ «wcPolynomials»",
								moved.RwRev(),
								lineChart0.RwRev(),
								By(onLineMap[1].At(c.TermAs[A]("monoid_pow(L.mul, L.one, t, n) * u")), cleared))
							c.Show(
								"φ(u) lies in L, and tⁿ brings it into k[t]",
								By(
									ring_away.RingAwayMember.At(fieldOps, polynomials, t, c.TermAs[A]("φ(u)")),
									linear[0].At(u),
									uIn,
									inPolynomials))
						}))
					b.Show(
						"so φ is a k[t, 1/t]-linear map into k[t, 1/t]",
						By(laurentLinear.At(φ), values, linear[1], linear[2], linear[3]))
				}))

			// The facts module_isomorphism asks for of evaluation at one.
			evaluationMap := a.TermAs[Fun[Fun[A, Fun[A, A]], Fun[A, A]]]("«evaluationAtOne»")
			curveMapSet := a.TermAs[Set[Fun[A, Fun[A, A]]]]("«omegaPairMaps»")
			curveLinearSet := a.TermAs[Set[Fun[A, Fun[A, A]]]]("«overlapLinearMaps»")
			pairMapsLinear := a.Have(
				"every pair map into ω is overlap-linear on the ambient",
				"«omegaPairMaps» ⊆ «overlapLinearMaps»",
				Simp(Fwd(set_basic.SubsetDef)),
				a.ForEach(func(ψ *Expr[Fun[A, Fun[A, A]]]) Action { return By(curveMaps.At(ψ)) }))
			kInOverlap := a.Have(
				"k lies in the overlap, as chart 0 does",
				"k ⊆ A₀₁",
				BySets(constants, chartRing[2]))
			kOnCurve := a.Have(
				"so k, a ring lying in the overlap, is a subring of it",
				"subring(«wcOverlap», k)",
				By(
					Normalized,
					kRing,
					kInOverlap,
					comm_ring.SubringRingOn.Read(overlapRing).At(k),
					module_record.RestrictRingTwice.At(fieldOps, A01, k)))
			kOnLine := a.Have(
				"and, lying in k[t, 1/t], a subring of k[t, 1/t]",
				"subring(«wcRing»(«wcLaurent»), k)",
				By(
					kRing,
					laurent[1],
					comm_ring.SubringRingOn.Read(laurentRing).At(k),
					module_record.RestrictRingTwice.At(fieldOps, a.TermAs[Set[A]]("«wcLaurent»"), k)))
			curveMapsModule := a.Have(
				"the maps of M into ω are a vector space over k",
				"module_on(«wdScalars», «wdDualizingMaps»(M))",
				Simp(Fwd(CurveDualizingMapsDef)),
				By(
					lattice_pair_map.PairMapsLinearSpace.At(
						curveRing,
						A0,
						A1,
						k,
						vectors,
						a.TermAs[module_record.ModuleOps[A, Fun[A, A]]]("«wdDualizingModule»"),
						M,
						a.TermAs[Prod[Set[Fun[A, A]], Set[Fun[A, A]]]]("«wdDualizing»")),
					curveBiaffine,
					kOnCurve,
					constants,
					pair,
					DualizingIsLattice.Read(L).At(k, A0, A1, A01, t),
					curve,
					module_record.RestrictRingDef.At(curveRing, k),
					module_record.RestrictRingDef.At(fieldOps, k)))
			lineMapsModule := a.Have(
				"so are the maps of M into O(−2) on the line",
				"module_on(«wdScalars», "+
					"    lattice_pair_hom(«wcRing»(«wcLaurent»), «wcField», M, «wcField», «lineDualizing»))",
				By(
					lattice_pair_map.PairMapsLinearSpace.At(
						lineRing,
						polynomials,
						inversePolynomials,
						k,
						vectors,
						vectors,
						M,
						a.TermAs[_LatticePair]("«lineDualizing»")),
					datum,
					kOnLine,
					constantsOnLine,
					onLine[0],
					projective_line.LinePairIsLattice.Read(L).At(k, tm, a.TermAs[Int]("-&2")),
					module_record.RestrictRingDef.At(lineRing, k),
					module_record.RestrictRingDef.At(curveRing, k),
					module_record.RestrictRingDef.At(fieldOps, k)))
			carried := a.Have(
				"evaluation at one carries a pair map into ω to a pair map into O(−2) on the line",
				"∀ψ:(A → A → A). ψ ∈ «omegaPairMaps» ⇒ (λx:A. ψ(x)(L.one)) ∈ «linePairMaps»",
				Derive(func(b *Argument) {
					ψ := b.FixAs[Fun[A, Fun[A, A]]]("ψ")
					ψParts := b.Conjuncts(
						b.Have(
							"ψ is overlap-linear and carries each chart of M into the same chart of ω",
							"ψ ∈ «overlapLinearMaps» ∧ "+
								"(∀m:A. m ∈ fst(M) ⇒ ψ(m) ∈ fst(«wdDualizing»)) ∧ "+
								"(∀m:A. m ∈ snd(M) ⇒ ψ(m) ∈ snd(«wdDualizing»))",
							By(curveMaps.At(ψ), b.Assume())),
						"ψ is overlap-linear",
						"it carries fst(M) into chart 0 of ω",
						"and snd(M) into chart 1")
					evaluated := b.TermAs[Fun[A, A]]("λx:A. ψ(x)(L.one)")
					linear := b.Have(
						"its evaluation is k[t, 1/t]-linear into k[t, 1/t], so into L",
						"(λx:A. ψ(x)(L.one)) ∈ «lineLinearMaps»",
						By(intoField.At(evaluated), evaluation[2].At(ψ), ψParts[0]))
					chart0 := b.Have(
						"ψ(m) carries one, a member of A₀, into k[t]",
						"∀m:A. m ∈ fst(M) ⇒ ψ(m)(L.one) ∈ fst(«lineDualizing»)",
						By(ψParts[1], dualizing0, oneIn))
					chart1 := b.Have(
						"ψ(m) carries one, a member of A₁, into t⁻² · k[1/t]",
						"∀m:A. m ∈ snd(M) ⇒ ψ(m)(L.one) ∈ snd(«lineDualizing»)",
						By(ψParts[2], dualizing1, oneIn))
					b.Show(
						"so the evaluation is a pair map into O(−2)",
						By(lineMaps.At(evaluated), linear, chart0, chart1))
				}))
			adds := a.Have(
				"evaluation at one adds: (ψ + χ)(x)(one) = ψ(x)(one) + χ(x)(one)",
				Statement{
					Binders: "∀ψ χ:(A → A → A).",
					Hypotheses: []string{
						"ψ ∈ «omegaPairMaps»",
						"χ ∈ «omegaPairMaps»",
					},
					Conclusion: "(λx:A. fun_add(fun_add, ψ, χ, x)(L.one)) = " +
						"fun_add(λx:A. ψ(x)(L.one), λx:A. χ(x)(L.one))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[A, Fun[A, A]]]("ψ")
					b.FixAs[Fun[A, Fun[A, A]]]("χ")
					b.Assume()
					b.Show(
						"at each x both sides are ψ(x)(one) + χ(x)(one)",
						Funext(),
						Simp(Fwd(function_module.FunAddDef)),
						Basic())
				}))
			scales := a.Have(
				"evaluation at one is k-linear: (c · ψ)(x)(one) = ψ(x)(c) = c · ψ(x)(one)",
				Statement{
					Binders: "∀c:A. ∀ψ:(A → A → A).",
					Hypotheses: []string{
						"c ∈ k",
						"ψ ∈ «omegaPairMaps»",
					},
					Conclusion: "(λx:A. " +
						"    fun_smul(λs:A. λφ:(A → A). λy:A. COND(y ∈ A₀₁, φ(s * y), L.zero), c, ψ, x)(L.one)) = " +
						"fun_smul(c, λx:A. ψ(x)(L.one))",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					ψ := b.FixAs[Fun[A, Fun[A, A]]]("ψ")
					assumed := b.Conjuncts(
						b.Assume(),
						"c lies in k",
						"ψ is a pair map into ω")
					scalar := b.Have(
						"c lies in k[t, 1/t]",
						"c ∈ «wcLaurent»",
						BySets(laurent[1], assumed[0]))
					linear := b.Have(
						"ψ is overlap-linear",
						"ψ ∈ «overlapLinearMaps»",
						BySets(pairMapsLinear, assumed[1]))
					b.Show(
						"the adjunction's evaluation is k[t, 1/t]-linear",
						By(evaluation[4].At(c, ψ), scalar, linear))
				}))
			injective := a.Have(
				"evaluation at one is one-to-one on the pair maps into ω",
				"injective_on(«omegaPairMaps», «evaluationAtOne»)",
				By(
					functions.InjectiveOnSubset.At(evaluationMap, curveMapSet, curveLinearSet),
					iso[1],
					pairMapsLinear))
			reached := a.Have(
				"every pair map into O(−2) on the line is the evaluation of a pair map into ω",
				"«linePairMaps» ⊆ image(«evaluationAtOne», «omegaPairMaps»)",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[A, A]]("φ")
					φIn := b.Assume()
					onLineMap := b.Conjuncts(
						b.Have(
							"φ carries each chart of M into the same chart of O(−2)",
							"φ ∈ «lineLinearMaps» ∧ "+
								"(∀x:A. x ∈ fst(M) ⇒ φ(x) ∈ fst(«lineDualizing»)) ∧ "+
								"(∀x:A. x ∈ snd(M) ⇒ φ(x) ∈ snd(«lineDualizing»))",
							By(lineMaps.At(φ), φIn)),
						"φ is a linear map into L",
						"it carries fst(M) into k[t]",
						"and snd(M) into t⁻² · k[1/t]")
					evaluated := b.Have(
						"φ, a k[t, 1/t]-linear map into k[t, 1/t], is the evaluation of an overlap-linear map",
						"φ ∈ image(«evaluationAtOne», «overlapLinearMaps»)",
						iso[2].Rw(),
						By(intoLaurent.At(φ), φIn))
					ψ, from := b.ObtainAs[Fun[A, Fun[A, A]]](
						"call it ψ",
						"∃ψ:(A → A → A). φ = (λx:A. ψ(x)(L.one)) ∧ ψ ∈ «overlapLinearMaps»",
						By(set_basic.InImage.At(evaluationMap, curveLinearSet, φ), evaluated))
					fromParts := b.Conjuncts(
						from,
						"φ is ψ read at one",
						"ψ is overlap-linear")
					readAtOne, ψLinear := fromParts[0], fromParts[1]
					pointwise := b.Have(
						"φ(n) = ψ(n)(one) at every n",
						"∀n:A. φ(n) = ψ(n)(L.one)",
						By(Normalized, readAtOne))
					linear := b.Conjuncts(
						GroupPremises(fromParts[1], curveLinear.At(ψ)),
						"ψ takes its values in the container",
						"a scalar of the overlap moves into the argument")
					readOff := b.Have(
						"on the overlap ψ is read off φ: ψ(m)(y) = ψ(y · m)(one) = φ(y · m)",
						"∀y m:A. y ∈ A₀₁ ∧ m ∈ «ambientOnCurve» ⇒ ψ(m)(y) = φ(y * m)",
						Derive(func(c *Argument) {
							y, m := c.FixAs[A]("y"), c.FixAs[A]("m")
							members := c.Conjuncts(
								c.Assume(),
								"y lies in the overlap",
								"m lies in the ambient")
							c.Show(
								"ψ(y · m) is y acting on ψ(m), which at one reads ψ(m) at y · one = y",
								By(
									linear[1].At(y, m),
									members[0],
									members[1],
									pointwise.At(c.TermAs[A]("y * m")),
									comm_ring.OneIn.Read(overlapRing),
									comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(overlapRing)).At(
										proof.MemberOf(y, members[0]))))
						}))
					chart0 := b.Have(
						"ψ carries fst(M) into chart 0 of ω: ψ(m)(y) = φ(y · "+
							"m) lies in k[t] for y in A₀, as y · m lies in fst(M)",
						"∀m:A. m ∈ fst(M) ⇒ ψ(m) ∈ fst(«wdDualizing»)",
						Derive(func(c *Argument) {
							m := c.FixAs[A]("m")
							mIn := c.Assume()
							mAmbient := c.Have(
								"m lies in the ambient",
								"m ∈ «ambientOnCurve»",
								BySets(curveAmbient[1], mIn))
							values := c.Have(
								"ψ(m) carries A₀ into k[t]",
								"∀y:A. y ∈ A₀ ⇒ ψ(m)(y) ∈ fst(«lineDualizing»)",
								Derive(func(d *Argument) {
									y := d.FixAs[A]("y")
									yIn := d.Assume()
									product := d.Have(
										"y · m lies in fst(M), a module over A₀",
										"y * m ∈ fst(M)",
										By(
											submodule.SubmoduleSmul.At(
												d.TermAs[module_record.RingOps[A]]("restrict_ring(«wcOverlap», A₀)"), vectors, chart0Set, y, m),
											onCurve[1],
											yIn,
											mIn,
											module_record.RestrictRingDef.At(curveRing, A0)))
									yOverlap := d.Have(
										"y lies in the overlap, as chart 0 does",
										"y ∈ A₀₁",
										BySets(chartRing[2], yIn))
									d.Show(
										"ψ(m)(y) = φ(y · m), which φ carries into k[t]",
										By(readOff.At(y, m), yOverlap, mAmbient, onLineMap[1].At(d.TermAs[A]("y * m")), product))
								}))
							c.Show(
								"so ψ(m) lies in chart 0 of ω",
								By(dualizing0.At(c.TermAs[Fun[A, A]]("ψ(m)")), linear[0].At(m), mAmbient, values))
						}))
					chart1 := b.Have(
						"ψ carries snd(M) into chart 1 of ω: ψ(m)(y) = φ(y · m) "+
							"lies in t⁻² · k[1/t] for y in A₁, as y · m lies in snd(M)",
						"∀m:A. m ∈ snd(M) ⇒ ψ(m) ∈ snd(«wdDualizing»)",
						Derive(func(c *Argument) {
							m := c.FixAs[A]("m")
							mIn := c.Assume()
							mAmbient := c.Have(
								"m lies in the ambient",
								"m ∈ «ambientOnCurve»",
								BySets(curveAmbient[2], mIn))
							values := c.Have(
								"ψ(m) carries A₁ into t⁻² · k[1/t]",
								"∀y:A. y ∈ A₁ ⇒ ψ(m)(y) ∈ snd(«lineDualizing»)",
								Derive(func(d *Argument) {
									y := d.FixAs[A]("y")
									yIn := d.Assume()
									product := d.Have(
										"y · m lies in snd(M), a module over A₁",
										"y * m ∈ snd(M)",
										By(
											submodule.SubmoduleSmul.At(
												d.TermAs[module_record.RingOps[A]]("restrict_ring(«wcOverlap», A₁)"), vectors, chart1Set, y, m),
											onCurve[2],
											yIn,
											mIn,
											module_record.RestrictRingDef.At(curveRing, A1)))
									yOverlap := d.Have(
										"y lies in the overlap, as chart 1 does",
										"y ∈ A₀₁",
										BySets(chartRing[3], yIn))
									d.Show(
										"ψ(m)(y) = φ(y · m), which φ carries into t⁻² · k[1/t]",
										By(readOff.At(y, m), yOverlap, mAmbient, onLineMap[2].At(d.TermAs[A]("y * m")), product))
								}))
							c.Show(
								"so ψ(m) lies in chart 1 of ω",
								By(dualizing1.At(c.TermAs[Fun[A, A]]("ψ(m)")), linear[0].At(m), mAmbient, values))
						}))
					inMaps := b.Have(
						"so ψ is a pair map into ω",
						"ψ ∈ «omegaPairMaps»",
						By(curveMaps.At(ψ), ψLinear, chart0, chart1))
					b.Show(
						"and φ is its evaluation",
						readAtOne.Rw(),
						By(set_image.FunInImage.At(evaluationMap, curveMapSet, ψ), inMaps))
				}))
			image := a.TermAs[Set[Fun[A, A]]]("image(«evaluationAtOne», «omegaPairMaps»)")
			lineMapSet := a.TermAs[Set[Fun[A, A]]]("«linePairMaps»")
			onto := a.Have(
				"so evaluation at one maps the pair maps into ω onto those into O(−2)",
				"image(«evaluationAtOne», «omegaPairMaps») = «linePairMaps»",
				By(
					set_order.SubsetAntisym.At(image, lineMapSet),
					set_image.ImageSubsetIff.At(evaluationMap, curveMapSet, lineMapSet),
					carried,
					reached))
			scalars := a.TermAs[module_record.RingOps[A]]("«wdScalars»")
			curveMapsOps := a.TermAs[module_record.ModuleOps[A, Fun[A, Fun[A, A]]]]("«wdDualizingMaps»(M)")
			lineMapsOps := a.TermAs[module_record.ModuleOps[A, Fun[A, A]]](
				"lattice_pair_hom(«wcRing»(«wcLaurent»), «wcField», M, «wcField», «lineDualizing»)")
			a.Show(
				"evaluation at one is a k-linear bijection of Hom(M, "+
					"ω) onto the pair maps of M into O(−2) on the line",
				By(
					module_homomorphism.ModuleIsomorphismDef.At(scalars, curveMapsOps, lineMapsOps, evaluationMap),
					module_homomorphism.ModuleHomomorphismDef.At(scalars, curveMapsOps, lineMapsOps, evaluationMap),
					curveMapsModule,
					lineMapsModule,
					carried,
					adds,
					scales,
					injective,
					onto))
		}),
})}

// SerreDuality — for an invertible pair M, H¹(M) and Hom(M, ω) are
// finite-dimensional over k, of one dimension: H¹(M) is finite for an
// invertible pair, and it is H¹(M) read on the line
// (algebraic_curve.CurvePairOnLine), where Serre duality makes the maps of M
// into O(−2) finite-dimensional of dimension h¹(M) (LineSerreDuality); Hom(M,
// ω) is isomorphic to those maps (DualizingMapsOnLine), and isomorphic spaces
// have one dimension.
var SerreDuality = serreDualityThm{family.Add(registry.ProofEntry{
	Name: "SerreDuality",
	Key:  "prop_e99e79853ad4029e",
	Reading: "Invertibility is load-bearing only through finiteness: it makes H¹(M) " +
		"finite-dimensional over k (InvertibleFinite), and for a lattice pair with an " +
		"infinite-dimensional H¹ the dimension half fails, the dual being larger than H¹(M), while " +
		"SerreDualityPairing still holds. Both finiteness conclusions are derived, not assumed.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdInvertible»(M)",
		},
		Conclusion: "finite_dimensional(«wdScalars», «wdH1»(M)) ∧ " +
			"finite_dimensional(«wdScalars», «wdDualizingMaps»(M)) ∧ " +
			"module_dim(«wdScalars», «wdDualizingMaps»(M)) = «wdH1Dim»(M)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M *Expr[_LatticePair],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"the curve datum",
				"M is an invertible pair")
			curve, invertible := given[0], given[1]
			pair := a.Have(
				"an invertible pair is a lattice pair over the overlap",
				"lattice_pair(«wcOverlap», A₀, A₁, «wcField», M)",
				By(a.Unfolded(invertible, invertible_lattice_pair.InvertibleLatticePairDef)))
			finite := a.Have(
				"an invertible pair has finite-dimensional cohomology, H¹(M) among it",
				"finite_dimensional(«wdScalars», «wdH1»(M))",
				By(
					curve,
					invertible,
					algebraic_curve.InvertibleFinite.Read(L).At(k, A0, A1, A01, t, M),
					lattice_pair.LatticePairFiniteDef))

			datum := a.Simplified(
				GroupPremises(given[0], algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			tm := a.MemberOf[on.L](t, a.Have(
				"t lies in L",
				"t ∈ L.carrier",
				By(datum)))
			onLine := a.Conjuncts(
				GroupPremises(given[0], pair, algebraic_curve.CurvePairOnLine.Read(L).At(k, A0, A1, A01, t, M)),
				"M is a lattice pair on the line",
				"with the curve's ambient",
				"and the curve's H¹")
			lineRing, curveRing :=
				a.TermAs[module_record.RingOps[A]]("«wcRing»(«wcLaurent»)"),
				a.TermAs[module_record.RingOps[A]]("«wcOverlap»")
			space := a.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
			lineMaps := a.Have(
				"so Serre duality on the line makes the maps of M into "+
					"O(−2) finite-dimensional over k, of dimension h¹(M)",
				"finite_dimensional(«wdScalars», "+
					"    lattice_pair_hom(«wcRing»(«wcLaurent»), «wcField», M, «wcField», «lineDualizing»)) ∧ "+
					"module_dim(«wdScalars», "+
					"    lattice_pair_hom(«wcRing»(«wcLaurent»), «wcField», M, «wcField», «lineDualizing»)) = "+
					"«wdH1Dim»(M)",
				By(
					projective_line_duality.LineSerreDuality.Read(L).At(k, tm, space, M),
					datum,
					onLine[0],
					onLine[2],
					finite,
					module_record.RestrictRingDef.At(lineRing, k),
					module_record.RestrictRingDef.At(curveRing, k),
					lattice_pair.LatticePairH1DimDef.At(lineRing, k, space, M),
					lattice_pair.LatticePairH1DimDef.At(curveRing, k, space, M)))

			evaluation := a.Have(
				"evaluation at one is a k-isomorphism of Hom(M, ω) onto those maps",
				"module_isomorphism(«wdScalars», "+
					"    «wdDualizingMaps»(M), "+
					"    lattice_pair_hom(«wcRing»(«wcLaurent»), «wcField», M, «wcField», «lineDualizing»), "+
					"    «evaluationAtOne»)",
				By(curve, pair, DualizingMapsOnLine.Read(L).At(k, A0, A1, A01, t, M)))
			inv := a.TermAs[Fun[A, A]]("L.inv")
			scalars := a.TermAs[module_record.RingOps[A]]("«wdScalars»")
			lineMapsModule := a.TermAs[module_record.ModuleOps[A, Fun[A, A]]](
				"lattice_pair_hom(«wcRing»(«wcLaurent»), «wcField», M, «wcField», «lineDualizing»)")
			maps := a.TermAs[module_record.ModuleOps[A, Op[A]]]("«wdDualizingMaps»(M)")
			backward := a.TermAs[Fun[Fun[A, A], Op[A]]](
				"inverse_on(«wdDualizingMaps»(M).carrier, «evaluationAtOne»)")
			a.Show(
				"so Hom(M, ω), isomorphic to them, is finite-dimensional of dimension h¹(M)",
				By(
					finite,
					lineMaps,
					module_homomorphism.IsomorphismInverse.Read(evaluation),
					datum,
					field.SubfieldRingSubfield.Read(L).At(k, A01),
					field.RingSubfieldRestrict.At(curveRing, k, inv, k),
					module_dimension.IsomorphismDim.At(scalars, lineMapsModule, inv, maps, backward)))
		}),
})}

// GenusDual — the genus is the dimension of the sections of the
// dualizing pair: g = ℓ(ω).
var GenusDual = genusDualThm{family.Add(registry.ProofEntry{
	Name: "GenusDual",
	Key:  "prop_c0bf1960530f0880",
	Reading: "g = dim H¹(O) by definition; Serre duality " +
		"at O makes it dim Hom(O, ω), and Hom(O, ω) is H⁰(ω).",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«wcDatum»",
		},
		Conclusion: "finite_dimensional(«wdScalars», " +
			"    lattice_pair_h0(«wdDualizingModule», «wdDualizing»)) ∧ " +
			"lattice_pair_h0_dim(«wcOverlap», k, «wdDualizingModule», «wdDualizing») = " +
			"curve_genus(field_ring(L), k, A₀, A₁, A₀₁)",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			structure := a.TermAs[_LatticePair]("(A₀, A₁)")
			data := a.Conjuncts(
				GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in the field",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field under L's operations",
				"the constants lie in both charts")
			subfield, invertible := data[2], data[5]
			homDimension := a.Have(
				"Serre duality makes Hom(O, ω) finite-dimensional of dimension g",
				"finite_dimensional(«wdScalars», «wdDualizingMaps»((A₀, A₁))) ∧ "+
					"module_dim(«wdScalars», «wdDualizingMaps»((A₀, A₁))) = curve_genus(field_ring(L), k, A₀, A₁, A₀₁)",
				Unfold(algebraic_curve.CurveGenusDef),
				By(curve, invertible, SerreDuality.Read(L).At(k, A0, A1, A01, t, structure)))
			evaluation := a.Have(
				"evaluation at one identifies Hom(O, ω) with its sections",
				"module_isomorphism(«wdScalars», "+
					"    «wdDualizingMaps»((A₀, A₁)), "+
					"    lattice_pair_h0(«wdDualizingModule», «wdDualizing»), "+
					"    λψ:(A → A → A). ψ(L.one))",
				By(curve, HomDualizingSections.Read(L).At(k, A0, A1, A01, t)))
			scalars := a.TermAs[module_record.RingOps[A]]("«wdScalars»")
			maps := a.TermAs[module_record.ModuleOps[A, Op[A]]]("«wdDualizingMaps»((A₀, A₁))")
			sections := a.TermAs[module_record.ModuleOps[A, Fun[A, A]]](
				"lattice_pair_h0(«wdDualizingModule», «wdDualizing»)")
			atOne := a.TermAs[Fun[Op[A], Fun[A, A]]]("λψ:(A → A → A). ψ(L.one)")
			inv := a.TermAs[Fun[A, A]]("L.inv")
			overlap := a.TermAs[module_record.RingOps[A]]("«wcOverlap»")
			dimension := a.Have(
				"the isomorphism keeps the finite dimension, so the sections have dimension g",
				"finite_dimensional(«wdScalars», lattice_pair_h0(«wdDualizingModule», «wdDualizing»)) ∧ "+
					"module_dim(«wdScalars», lattice_pair_h0(«wdDualizingModule», «wdDualizing»)) = "+
					"curve_genus(field_ring(L), k, A₀, A₁, A₀₁)",
				By(
					homDimension,
					evaluation,
					subfield,
					field.SubfieldRingSubfield.Read(L).At(k, A01),
					field.RingSubfieldRestrict.At(overlap, k, inv, k),
					module_dimension.IsomorphismDim.At(scalars, maps, inv, sections, atOne)))
			omega := a.TermAs[module_record.ModuleOps[A, Fun[A, A]]]("«wdDualizingModule»")
			dualizing := a.TermAs[Prod[Set[Fun[A, A]], Set[Fun[A, A]]]]("«wdDualizing»")
			a.Show(
				"the dimension of the dualizing sections is the genus",
				By(dimension, lattice_pair.LatticePairH0DimDef.At(overlap, k, omega, dualizing)))
		}),
})}

// ---------------------------------------------------------------------------
// Invertible models of the dualizing pair
// ---------------------------------------------------------------------------

// DualizingModelDef — `dualizing_model(L, k, t, A₀, A₁, A₀₁, N)`: N is an
// invertible pair in the field and an isomorphism of lattice pairs carries
// the dualizing pair ω onto it.
var DualizingModelDef = dualizingModelDefThm{family.Define(registry.DefEntry{
	Name:     "DualizingModelDef",
	Key:      "prop_73c5197f78b2e238",
	Const:    "dualizing_model",
	Type:     "field_ops(A) → set(A) → A → set(A) → set(A) → set(A) → prod(set(A), set(A)) → bool",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). ∀t:A. ∀A₀:set(A). ∀A₁:set(A). ∀A₀₁:set(A). ∀N:prod(set(A), set(A)). " +
			"    dualizing_model(F, k, t, A₀, A₁, A₀₁, N) ⇔ " +
			"    invertible_lattice_pair(field_ring(F), A₀, A₁, A₀₁, N) ∧ " +
			"    (∃f:(A → A) → A. " +
			"        lattice_pair_isomorphism(restrict_ring(field_ring(F), A₀₁), " +
			"            curve_dualizing_module(field_ring(F), k, t, A₀₁), " +
			"            curve_dualizing_pair(F, k, t, A₀, A₁, A₀₁), " +
			"            regular_module(field_ring(F)), " +
			"            N, " +
			"            f))",
	},
	Deps: []registry.EntryLike{CurveDualizingModuleDef, CurveDualizingPairDef},
})}

// DualizingInvertibleDef — `dualizing_invertible(L, k, t, A₀, A₁, A₀₁)`:
// the dualizing pair has an invertible model.
var DualizingInvertibleDef = dualizingInvertibleDefThm{family.Define(registry.DefEntry{
	Name:     "DualizingInvertibleDef",
	Key:      "prop_f1d465d2f71589a0",
	Const:    "dualizing_invertible",
	Type:     "field_ops(A) → set(A) → A → set(A) → set(A) → set(A) → bool",
	Implicit: []string{},
	Bundles:  []string{},
	Deps:     []registry.EntryLike{DualizingModelDef},
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). ∀t:A. ∀A₀:set(A). ∀A₁:set(A). ∀A₀₁:set(A). " +
			"    dualizing_invertible(F, k, t, A₀, A₁, A₀₁) ⇔ " +
			"    ∃N:prod(set(A), set(A)). dualizing_model(F, k, t, A₀, A₁, A₀₁, N)",
	},
})}

// InvertibleEndomorphisms — the endomorphisms of an invertible pair M form a
// space of dimension one over the constants: End(M) = k. Multiplication
// identifies the sections of M · M⁻¹ with the maps of M into itself
// (invertible_lattice_pair.SectionsAreMaps); M · M⁻¹ is the structure pair,
// whose sections are the constants.
var InvertibleEndomorphisms = invertibleEndomorphismsThm{family.Add(registry.ProofEntry{
	Name: "InvertibleEndomorphisms",
	Key:  "prop_fafaa29cdacfd785",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdInvertible»(M)",
		},
		Conclusion: "finite_dimensional(«wcRing»(k), " +
			"    lattice_pair_hom(«wcOverlap», «wcField», M, «wcField», M)) ∧ " +
			"module_dim(«wcRing»(k), lattice_pair_hom(«wcOverlap», «wcField», M, «wcField», M)) = 1",
		Abbrev: Abbrev{
			{Name: "multiplication", Text: "λa:A. λz:A. COND(z ∈ «ambientOnCurve», a * z, L.zero)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M *Expr[_LatticePair],
			curve, invertible Fact,
		) {
			fieldOps, fieldRing := a.TermAs[FieldOps[A]]("L"), a.TermAs[RingOps[A]]("field_ring(L)")
			data := a.Conjuncts(
				GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in L",
				"the charts and the overlap are a biaffine datum",
				"k is a subfield of L",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"it is invertible",
				"k is a field",
				"k lies in both charts")
			inField, biaffine, subfield := data[0], data[1], data[2]
			pairM := a.Have(
				"M is a lattice pair over the overlap",
				"lattice_pair(«wcOverlap», A₀, A₁, «wcField», M)",
				By(a.Unfolded(invertible, invertible_lattice_pair.InvertibleLatticePairDef)))

			// The scalars k lie in both charts, and form a subring of the overlap.
			kCharts := a.Have(
				"k lies in each chart",
				"k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(data[7]))
			chart0 := a.Conjuncts(
				GroupPremises(
					inField, biaffine, invertible_lattice_pair.ChartRingsInField.Read(L).At(A0, A1, A01, t)),
				"chart 0 lies in the overlap",
				"and so does chart 1",
				"the overlap is a subring of L",
				"and so is chart 0",
				"and so is chart 1")[0]
			kInOverlap := a.Have(
				"so k lies in the overlap",
				"k ⊆ A₀₁",
				BySets(kCharts, chart0))
			kSubring := a.Have(
				"and k, a subring of L, is a subring of the overlap",
				"subring(«wcOverlap», k)",
				By(
					subfield,
					kInOverlap,
					field.SubfieldSubring.Read(L).At(k),
					comm_ring.SubringRestrict.At(fieldRing, k, A01)))

			// Multiplication identifies H⁰(M · M⁻¹) with the maps M → M, and M · M⁻¹ is the structure pair.
			product := a.Conjuncts(
				GroupPremises(
					inField,
					biaffine,
					invertible,
					invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, M)),
				"M⁻¹ is invertible",
				"M · M⁻¹ is the structure pair",
				"and M⁻¹⁻¹ = M")[1]
			isomorphism := a.Have(
				"so multiplication is a k-isomorphism of H⁰(A₀, A₁) onto the endomorphisms of M",
				"module_isomorphism(«wcRing»(k), "+
					"    lattice_pair_h0(«wcField», (A₀, A₁)), "+
					"    lattice_pair_hom(«wcOverlap», «wcField», M, «wcField», M), "+
					"    «multiplication»)",
				By(
					GroupPremises(L, inField, biaffine, kSubring, kCharts, invertible, pairM,
						invertible_lattice_pair.SectionsAreMaps.At(fieldOps, A0, A1, A01, k, t, M, M)),
					product,
					module_record.RestrictRingTwice.At(fieldRing, A01, k)))

			// The sections of the structure pair are the constants: one-dimensional over k.
			sections := a.Conjuncts(
				a.Simplified(
					GroupPremises(curve, algebraic_curve.StructureH0.Read(L).At(k, A0, A1, A01, t)),
					Fwd(lattice_pair.LatticePairH0DimDef),
					Fwd(module_record.RestrictRingTwice)),
				"H⁰(A₀, A₁) is finite-dimensional over k",
				"of dimension one")

			scalars := a.TermAs[RingOps[A]]("«wcRing»(k)")
			structureSections := a.TermAs[module_record.ModuleOps[A, A]]("lattice_pair_h0(«wcField», (A₀, A₁))")
			endomorphisms := a.TermAs[module_record.ModuleOps[A, Fun[A, A]]](
				"lattice_pair_hom(«wcOverlap», «wcField», M, «wcField», M)")
			multiplication := a.TermAs[Fun[A, Fun[A, A]]]("«multiplication»")
			// Dimension is measured over k as a field, with L's inverse.
			kInverse := a.TermAs[Fun[A, A]]("L.inv")
			a.Show(
				"so the endomorphisms of M are finite-dimensional over k, of dimension one",
				By(
					sections[0],
					sections[1],
					subfield,
					field.SubfieldRingSubfield.Read(L).At(k, k),
					isomorphism,
					module_dimension.IsomorphismDim.At(
						scalars, structureSections, kInverse, endomorphisms, multiplication)))
		}),
})}

// DualizingMapsDimension — a dualizing model N measures Hom into the
// dualizing pair ω: for an invertible pair X, dim Hom(X, ω) = ℓ(N · X⁻¹).
// Composing with the isomorphism of ω onto N carries Hom(X, ω) onto
// Hom(X, N) (lattice_pair_map.MapsPostcomposeIsomorphism), which is H⁰(N · X⁻¹)
// by multiplication (invertible_lattice_pair.SectionsAreMaps), and N · X⁻¹ is
// invertible, so its sections are finite-dimensional.
var DualizingMapsDimension = dualizingMapsDimensionThm{family.Add(registry.ProofEntry{
	Name: "DualizingMapsDimension",
	Key:  "prop_6c0b75d1aaed7bfb",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀N X:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"dualizing_model(L, k, t, A₀, A₁, A₀₁, N)",
			"«wdInvertible»(X)",
		},
		Conclusion: "module_dim(«wdScalars», «wdDualizingMaps»(X)) = " +
			"lattice_pair_h0_dim(«wcOverlap», k, «wcField», «quotient»)",
		Abbrev: Abbrev{
			{Name: "ambient", Text: "lattice_pair_ambient(«wcOverlap», «wcField», X)"},
			{Name: "quotient", Text: "«wdMul»(N, «wdInverse»(X))"},
			{Name: "sections", Text: "lattice_pair_h0(«wcField», «quotient»)"},
			{Name: "multiplication", Text: "λa:A. λz:A. COND(z ∈ «ambient», a * z, L.zero)"},
			{Name: "composing", Text: "λh:(A → A → A). f ∘ h"},
			{Name: "backward", Text: "inverse_on(«wdDualizingMaps»(X).carrier, «composing»)"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			N, X *Expr[_LatticePair],
			curve, model, invertible Fact,
		) {
			fieldOps, inverseT := arg.TermAs[FieldOps[A]]("L"), arg.TermAs[A]("L.inv(t)")
			overlapRing, scalars := arg.TermAs[RingOps[A]]("«wcOverlap»"), arg.TermAs[RingOps[A]]("«wdScalars»")
			fieldModule := arg.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
			inverse, quotient :=
				arg.TermAs[_LatticePair]("«wdInverse»(X)"), arg.TermAs[_LatticePair]("«quotient»")
			data := arg.Conjuncts(
				GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in L",
				"the charts and the overlap are a biaffine datum",
				"k is a subfield of L",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"it is invertible",
				"k is a field",
				"k lies in both charts")
			inField, biaffine, subfield, kField, kInCharts := data[0], data[1], data[2], data[6], data[7]
			modelParts := arg.Conjuncts(
				arg.Unfolded(model, DualizingModelDef),
				"N is invertible",
				"an isomorphism carries the dualizing pair onto N")
			f, isomorphism := arg.UnpackAs[Fun[Fun[A, A], A]](modelParts[1], "f")
			pairN := arg.Have(
				"N is a lattice pair over the overlap",
				"lattice_pair(«wcOverlap», A₀, A₁, «wcField», N)",
				By(arg.Unfolded(modelParts[0], invertible_lattice_pair.InvertibleLatticePairDef)))
			pairX := arg.Have(
				"so is X",
				"lattice_pair(«wcOverlap», A₀, A₁, «wcField», X)",
				By(arg.Unfolded(invertible, invertible_lattice_pair.InvertibleLatticePairDef)))
			dualizing := arg.Conjuncts(
				GroupPremises(curve, DualizingIsLattice.Read(L).At(k, A0, A1, A01, t)),
				"the dualizing container is a module over the overlap",
				"the dualizing pair is a lattice pair",
				"and its ambient is the container")

			// k as the scalars of the maps, a ring inside both charts.
			kRing := arg.Have(
				"k is a ring under the overlap's operations",
				"comm_ring_on(«wdScalars»)",
				By(
					field.RingOn.Read(kField),
					field.FieldRingDef.At(arg.TermAs[FieldOps[A]]("restrict_field(L, k)")),
					field.RestrictFieldDef.At(fieldOps, k),
					module_record.RestrictRingDef.At(overlapRing, k)))
			kCharts := arg.Conjuncts(
				arg.Have(
					"k lies in each chart",
					"k ⊆ A₀ ∧ k ⊆ A₁",
					BySets(kInCharts)),
				"k lies in chart 0",
				"k lies in chart 1")
			rings := arg.Conjuncts(
				GroupPremises(
					data[0], data[1], invertible_lattice_pair.ChartRingsInField.Read(L).At(A0, A1, A01, t)),
				"chart 0 lies in the overlap",
				"and so does chart 1",
				"the overlap is a subring of L",
				"and so is chart 0",
				"and so is chart 1")
			overlapIsRing := arg.Have(
				"the overlap is a ring under L's operations",
				"comm_ring_on(«wcOverlap»)",
				By(rings[2], comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(A01)))
			kInOverlap := arg.Have(
				"k lies in the overlap, as chart 0 does",
				"k ⊆ A₀₁",
				BySets(kCharts[0], rings[0]))
			kSubring := arg.Have(
				"so k is a subring of the overlap",
				"subring(«wcOverlap», k)",
				By(kInOverlap, kRing, comm_ring.SubringRingOn.Read(overlapIsRing).At(k)))

			// H⁰(N · X⁻¹) ≅ Hom(X, N) ≅ Hom(X, ω).
			sectionsIso := arg.Have(
				"multiplication is a k-isomorphism of H⁰(N · X⁻¹) onto Hom(X, N)",
				"module_isomorphism(«wdScalars», "+
					"    «sections», "+
					"    lattice_pair_hom(«wcOverlap», «wcField», X, «wcField», N), "+
					"    «multiplication»)",
				By(
					L,
					inField,
					biaffine,
					kSubring,
					kCharts[0],
					kCharts[1],
					invertible,
					pairN,
					invertible_lattice_pair.SectionsAreMaps.At(fieldOps, A0, A1, A01, k, t, X, N)))
			postcompose := arg.Have(
				"composing with f is a k-isomorphism of Hom(X, ω) onto Hom(X, N)",
				"module_isomorphism(«wdScalars», "+
					"    «wdDualizingMaps»(X), "+
					"    lattice_pair_hom(«wcOverlap», «wcField», X, «wcField», N), "+
					"    «composing»)",
				By(
					biaffine,
					kSubring,
					kCharts[0],
					kCharts[1],
					pairX,
					dualizing[1],
					isomorphism,
					lattice_pair_map.MapsPostcomposeIsomorphism.At(
						overlapRing,
						A0,
						A1,
						k,
						t,
						inverseT,
						fieldModule,
						arg.TermAs[module_record.ModuleOps[A, Fun[A, A]]]("«wdDualizingModule»"),
						fieldModule,
						X,
						arg.TermAs[Prod[Set[Fun[A, A]], Set[Fun[A, A]]]]("«wdDualizing»"),
						N,
						f),
					CurveDualizingMapsDef))
			sectionsModule := arg.TermAs[module_record.ModuleOps[A, A]]("«sections»")
			modelMaps := arg.TermAs[module_record.ModuleOps[A, Fun[A, A]]](
				"lattice_pair_hom(«wcOverlap», «wcField», X, «wcField», N)")
			dualizingMaps := arg.TermAs[module_record.ModuleOps[A, Fun[A, Fun[A, A]]]]("«wdDualizingMaps»(X)")
			multiplication := arg.TermAs[Fun[A, Fun[A, A]]]("«multiplication»")
			composing := arg.TermAs[Fun[Fun[A, Fun[A, A]], Fun[A, A]]]("«composing»")
			backward := arg.TermAs[Fun[Fun[A, A], Fun[A, Fun[A, A]]]]("«backward»")
			composed := arg.TermAs[Fun[A, Fun[A, Fun[A, A]]]]("«backward» ∘ «multiplication»")
			compositeIso := arg.Have(
				"so multiplication, then the inverse of composing with "+
					"f, is a k-isomorphism of H⁰(N · X⁻¹) onto Hom(X, ω)",
				"module_isomorphism(«wdScalars», «sections», «wdDualizingMaps»(X), «backward» ∘ «multiplication»)",
				By(
					sectionsIso,
					postcompose,
					module_homomorphism.IsomorphismInverse.At(scalars, dualizingMaps, modelMaps, composing),
					module_homomorphism.IsomorphismCompose.At(
						scalars, sectionsModule, modelMaps, dualizingMaps, multiplication, backward)))

			// So the two have one dimension, ℓ(N · X⁻¹): H⁰ of an invertible pair is finite-dimensional.
			inverseInvertible := arg.Have(
				"X⁻¹ is invertible",
				"«wdInvertible»(«wdInverse»(X))",
				By(
					inField,
					biaffine,
					invertible,
					invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, X)))
			quotientFinite := arg.Have(
				"so N · X⁻¹ is, and it has finite cohomology",
				"lattice_pair_finite(«wcOverlap», k, «wcField», «quotient»)",
				By(
					curve,
					algebraic_curve.InvertibleFinite.Read(L).At(k, A0, A1, A01, t, quotient),
					inField,
					biaffine,
					modelParts[0],
					inverseInvertible,
					invertible_lattice_pair.InvertibleLatticeProduct.Read(L).At(A0, A1, A01, t, N, inverse)))
			// The dimension is measured over k as a field under L's operations, with L's inverse.
			kInverse := arg.TermAs[Fun[A, A]]("L.inv")
			arg.Show(
				"so dim Hom(X, ω) = ℓ(N · X⁻¹)",
				By(
					quotientFinite,
					lattice_pair.LatticePairFiniteDef.At(overlapRing, k, fieldModule, quotient),
					compositeIso,
					subfield,
					field.SubfieldRingSubfield.Read(L).At(k, A01),
					field.RingSubfieldRestrict.At(overlapRing, k, kInverse, k),
					module_dimension.IsomorphismDim.At(scalars, sectionsModule, kInverse, dualizingMaps, composed),
					lattice_pair.LatticePairH0DimDef.At(overlapRing, k, fieldModule, quotient)))
		}),
})}

// DualizingDegree — an invertible pair isomorphic to the dualizing pair has
// degree 2g − 2. The inverse isomorphism carries N onto the dualizing pair, so
// ℓ(N) is the dualizing pair's ℓ, the genus g; Hom(N, ω) has dimension
// ℓ(N · N⁻¹), and N · N⁻¹ is the structure pair, of ℓ one; and Riemann–Roch at
// N reads g − 1 = deg N + 1 − g.
var DualizingDegree = dualizingDegreeThm{family.Add(registry.ProofEntry{
	Name: "DualizingDegree",
	Key:  "prop_a06d1caf0371a21d",
	Reading: "Degree is evaluated on the field-valued invertible model N. The function-valued " +
		"dualizing pair itself has a different carrier type and is not an argument of curve_degree.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀A₀ A₁ A₀₁:set(A). ∀N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"dualizing_model(L, k, t, A₀, A₁, A₀₁, N)",
		},
		Conclusion: "«wdDegree»(N) = &2 * «wdGenus» - &2",
		Abbrev: Abbrev{
			{Name: "inverseMap", Text: "λw:A. " +
				"    COND(w ∈ lattice_pair_ambient(«wcOverlap», «wcField», N), " +
				"        inverse_on(lattice_pair_ambient(«wcOverlap», «wdDualizingModule», «wdDualizing»), " +
				"            f, " +
				"            w), " +
				"        «wdDualizingModule».zero)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			A0, A1, A01 *Expr[Set[A]],
			N *Expr[_LatticePair],
			curve, model Fact,
		) {
			overlap := a.TermAs[RingOps[A]]("«wcOverlap»")
			fieldModule := a.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
			dualizingModule := a.TermAs[module_record.ModuleOps[A, Fun[A, A]]]("«wdDualizingModule»")
			dualizingPair := a.TermAs[Prod[Set[Fun[A, A]], Set[Fun[A, A]]]]("«wdDualizing»")
			inverseT, kInverse := a.TermAs[A]("L.inv(t)"), a.TermAs[Fun[A, A]]("L.inv")
			data := a.Conjuncts(
				GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in L",
				"the charts and the overlap are a biaffine datum",
				"k is a subfield of L",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"it is invertible",
				"k is a field",
				"k lies in both charts")
			inField, biaffine, subfield := data[0], data[1], data[2]
			modelParts := a.Conjuncts(
				a.Unfolded(model, DualizingModelDef),
				"N is invertible",
				"an isomorphism carries the dualizing pair onto N")
			f, isomorphism := a.UnpackAs[Fun[Fun[A, A], A]](modelParts[1], "f")
			pairN := a.Have(
				"N is a lattice pair over the overlap",
				"lattice_pair(«wcOverlap», A₀, A₁, «wcField», N)",
				By(a.Unfolded(modelParts[0], invertible_lattice_pair.InvertibleLatticePairDef)))
			dualizing := a.Conjuncts(
				GroupPremises(curve, DualizingIsLattice.Read(L).At(k, A0, A1, A01, t)),
				"the dualizing container is a module over the overlap",
				"the dualizing pair is a lattice pair",
				"and its ambient is the container")[1]
			riemannRoch := a.Conjuncts(
				GroupPremises(curve, modelParts[0], RiemannRoch.Read(L).At(k, A0, A1, A01, t, N)),
				"N has finite cohomology",
				"Hom(N, ω) is finite-dimensional over k",
				"and ℓ(N) − dim Hom(N, ω) = deg N + 1 − g")

			kCharts := a.Have(
				"k lies in each chart",
				"k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(data[7]))

			// ℓ(N) = g. An isomorphism of lattice pairs keeps ℓ when its source has
			// finite cohomology, which Riemann–Roch gives for N and nothing gives for
			// ω; so the law is read along the inverse of f, from N onto ω.
			inverseMap := a.TermAs[Fun[A, Fun[A, A]]]("«inverseMap»")
			sections := a.Have(
				"N has as many sections as the dualizing pair: ℓ(N) = g",
				"lattice_pair_h0_dim(«wcOverlap», k, «wcField», N) = curve_genus(field_ring(L), k, A₀, A₁, A₀₁)",
				By(
					curve,
					biaffine,
					subfield,
					kCharts,
					pairN,
					dualizing,
					isomorphism,
					riemannRoch[0],
					GenusDual.Read(L).At(k, A0, A1, A01, t),
					field.SubfieldRingSubfield.Read(L).At(k, A01),
					lattice_pair_map.IsomorphismInverse.At(
						overlap, A0, A1, dualizingModule, fieldModule, dualizingPair, N, f),
					lattice_pair_map.IsomorphismSameEuler.At(
						overlap,
						A0,
						A1,
						t,
						inverseT,
						k,
						kInverse,
						fieldModule,
						dualizingModule,
						N,
						dualizingPair,
						inverseMap)))

			maps := a.Have(
				"so Hom(N, ω) has dimension ℓ(N · N⁻¹) = ℓ(A₀, A₁) = 1",
				"module_dim(«wdScalars», «wdDualizingMaps»(N)) = 1",
				By(
					curve,
					model,
					modelParts[0],
					inField,
					biaffine,
					DualizingMapsDimension.Read(L).At(k, A0, A1, A01, t, N, N),
					invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, N),
					algebraic_curve.StructureH0.Read(L).At(k, A0, A1, A01, t)))

			a.Show(
				"so Riemann–Roch at N reads g − 1 = deg N + 1 − g: deg N = 2g − 2",
				ByArith(riemannRoch[2], sections, maps))
		}),
})}

// LineDualizingModel — on the projective line, k(t) with the charts k[t] and
// k[1/t], O(−2) is a model of the dualizing pair: a linear functional of
// k[t, 1/t] into itself is multiplication by its value at one, and
// evaluation at one carries ω onto O(−2).
var LineDualizingModel = lineDualizingModelThm{family.Add(registry.ProofEntry{
	Name: "LineDualizingModel",
	Key:  "prop_b456ae6eeecc82f8",
	Deps: []registry.EntryLike{
		hom_module.CoextendScalarsAdjunction,
		algebraic_curve.ProjectiveLineCurve,
		projective_line.LinePairInvertible,
		CurveDualizingPairDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
		},
		Conclusion: "dualizing_model(restrict_field(L, «wcRationalFunctions»), " +
			"    k, " +
			"    t, " +
			"    «wcPolynomials», " +
			"    «wcInversePolynomials», " +
			"    «wcLaurent», " +
			"    «lineDualizing»)",
	},
		"For the line the overlap is k[t,t^-1]. A linear functional from that ring "+
			"to itself is multiplication by its value at one. Evaluation at one "+
			"identifies the dualizing chart conditions with O(−2), which is invertible."),
})}

// DualizingDegreeLine — on the projective line the model O(−2) of the
// dualizing pair has degree −2.
var DualizingDegreeLine = dualizingDegreeLineThm{family.Add(registry.ProofEntry{
	Name: "DualizingDegreeLine",
	Key:  "prop_55e138fadda42e1a",
	Deps: []registry.EntryLike{LineDualizingModel, DualizingDegree, algebraic_curve.GenusZeroLine},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
		},
		Conclusion: "curve_degree(«wcRing»(«wcRationalFunctions»), " +
			"    k, " +
			"    «wcPolynomials», " +
			"    «wcInversePolynomials», " +
			"    «wcLaurent», " +
			"    «lineDualizing») = " +
			"-&2",
	},
		"LineDualizingModel permits DualizingDegree; GenusZeroLine gives g=0."),
})}
