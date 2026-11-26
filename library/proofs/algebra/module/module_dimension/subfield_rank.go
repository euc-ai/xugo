// subfield_rank.go — three dimension counts. A change of scalars bounds the
// rank: vectors with coordinates in a subfield span over the field a space no
// larger than the one they span over the subfield. Restricting the scalars
// along a one-to-one ring homomorphism keeps the dimension the module has
// over the image. A submodule of codimension at most one leaves any two
// vectors dependent modulo it.

package module_dimension

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// SubfieldRankBound — vectors whose coordinates lie in a subfield L of a field
// R span over R a space no larger than the one they span over L. The L-span
// of W lies in the finite-dimensional L^S, so it has a finite basis B. An
// L-combination is an R-combination, L sharing R's operations, so the L-span
// of W lies in the R-span of W and in that of B: B and W span one R-space,
// whose dimension the finite B bounds (SpanningBound) by its size, the
// L-dimension (DimBasis).
var SubfieldRankBound = subfieldRankBoundThm{family.Add(registry.ProofEntry{
	Name: "SubfieldRankBound",
	Key:  "prop_57b5b3fcb864c4d2",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀inv:(A → A). ∀L:set(A). ∀S:set(D). ∀W:set(D → A).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"ring_subfield(R, inv, L)",
			"L ⊆ R.carrier",
			"finite(S)",
			"W ⊆ finite_supp(R.zero, L, S)",
		},
		Conclusion: "module_dim(R, restrict_module(free_module_record(R, S), «span»)) ≤ " +
			"module_dim(restrict_ring(R, L), restrict_module(«subfieldVectors», «subfieldSpan»))",
		Abbrev: Abbrev{
			{Name: "subfieldVectors", Text: "free_module_record(restrict_ring(R, L), S)"},
			{Name: "span", Text: "module_span(R, free_module_record(R, S), W)"},
			{Name: "subfieldSpan", Text: "module_span(restrict_ring(R, L), «subfieldVectors», W)"},
		},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		inv *Arrow[A, A],
		L *Expr[Set[A]],
		S *Expr[Set[D]],
		W *Expr[Set[Fun[D, A]]],
		h Fact,
	) {
		given := a.Conjuncts(
			h,
			"R is a field under inv",
			"L is a field under R's operations",
			"L lies in R",
			"S is finite",
			"W has its coordinates in L")
		fieldR, fieldL, lInR, finiteS, wInL := given[0], given[1], given[2], given[3], given[4]
		K := a.TermAs[RingOps[A]]("restrict_ring(R, L)")
		vectors := a.TermAs[ModuleOps[A, Fun[D, A]]]("free_module_record(R, S)")
		subfieldVectors := a.TermAs[ModuleOps[A, Fun[D, A]]]("«subfieldVectors»")
		span := a.TermAs[Set[Fun[D, A]]]("«span»")
		subfieldSpan := a.TermAs[Set[Fun[D, A]]]("«subfieldSpan»")

		fieldK := a.Have(
			"L with R's operations is a field on its own carrier",
			"ring_subfield(restrict_ring(R, L), inv, restrict_ring(R, L).carrier)",
			By(fieldL, field.RingSubfieldRestrict))
		ringR := a.Have(
			"R is the ring of the field on its carrier",
			"comm_ring_on(R)",
			By(
				field.RingOn.Read(a.Unfolded(fieldR, field.RingSubfieldDef)),
				field.FieldRingDef,
				module_record.RestrictRingDef.At(R, a.TermAs[Set[A]]("R.carrier")),
				module_record.RestrictRingCarrier.At(R)))
		ringK := a.Have(
			"and L with R's operations, a subring of R, is a ring",
			"comm_ring_on(restrict_ring(R, L))",
			By(ringR, lInR, fieldL, field.RingSubfieldSubring.At(R, inv, L), comm_ring.SubringRingOn.At(R, L)))
		moduleR := a.Have(
			"R^S is a module over R",
			"module_on(R, free_module_record(R, S))",
			By(free_module.FreeModuleOn.Read(ringR).At(S)))
		moduleK := a.Have(
			"and L^S a module over K",
			"module_on(restrict_ring(R, L), «subfieldVectors»)",
			By(free_module.FreeModuleOn.Read(ringK).At(S)))
		finiteK := a.Have(
			"L^S is finite-dimensional, the indicators of the points of the finite S a basis of it",
			"finite_dimensional(restrict_ring(R, L), «subfieldVectors»)",
			By(
				finiteS,
				moduleK,
				fieldK,
				free_module.DeltaAtBasis.Read(ringK).At(S),
				finite_set.FiniteImage.At(
					a.TermAs[Fun2[D, D, A]]("delta_at(restrict_ring(R, L).zero, restrict_ring(R, L).one)"), S),
				FiniteBasisDim.At(
					K,
					subfieldVectors,
					inv,
					a.TermAs[Set[Fun[D, A]]]("image(delta_at(restrict_ring(R, L).zero, restrict_ring(R, L).one), S)"))))

		lVectorsInR := a.Have(
			"a vector with coordinates in L has its coordinates in R",
			"finite_supp(R.zero, L, S) ⊆ finite_supp(R.zero, R.carrier, S)",
			Derive(func(b *Argument) {
				b.Do(Unfold(set_basic.SubsetDef))
				v := b.FixAs[Fun[D, A]]("v")
				vIn := b.Assume()
				zero := b.TermAs[A]("R.zero")
				b.Show(
					"v has the same finite support, and its coordinates, in L, lie in R",
					By(
						lInR,
						vIn,
						function_module.FiniteSuppMember.At(zero, L, S, v),
						function_module.FiniteSuppMember.At(zero, b.TermAs[Set[A]]("R.carrier"), S, v)))
			}))
		combinations := a.Have(
			"an L-combination is an R-combination, L sharing R's "+
				"operations: the L-span of L-vectors lies in their R-span",
			Statement{
				Binders:    "∀X:set(D → A).",
				Hypotheses: []string{"X ⊆ finite_supp(R.zero, L, S)"},
				Conclusion: "module_span(restrict_ring(R, L), «subfieldVectors», X) ⊆ " +
					"module_span(R, free_module_record(R, S), X)",
			},
			Derive(func(b *Argument) {
				b.FixAs[Set[Fun[D, A]]]("X")
				xIn := b.Assume()
				xInCarriers := b.Have(
					"X lies in L^S and in R^S",
					"X ⊆ «subfieldVectors».carrier ∧ X ⊆ free_module_record(R, S).carrier",
					BySets(xIn, lVectorsInR))
				// Both spans are the sets of finite combinations of X, X lying
				// in each module's carrier; they are written with one addition
				// and one scaling and differ in where the coefficients lie.
				b.Do(
					Simp(Fwd(linear_independence.SpanCombinations), Fwd(xInCarriers)),
					Unfold(set_basic.SubsetDef))
				b.FixAs[Fun[D, A]]("v")
				_, _, combination := b.Unpack2(b.Assume(), "T", "c")
				b.Show(
					"v is the combination over T with the coefficients c, which lie in L and so in R",
					By(lInR, combination))
			}))

		inCarriers := a.Have(
			"W lies in L^S and in R^S",
			"W ⊆ «subfieldVectors».carrier ∧ W ⊆ free_module_record(R, S).carrier",
			BySets(wInL, lVectorsInR))
		submodules := a.Have(
			"the two spans of W are submodules",
			"submodule(restrict_ring(R, L), «subfieldVectors», «subfieldSpan») ∧ "+
				"submodule(R, free_module_record(R, S), «span»)",
			By(moduleR, moduleK, inCarriers, submodule.SpanSubmodule))
		B, basis := a.ObtainAs[Set[Fun[D, A]]](
			"the L-span of W, inside the finite-dimensional L^S, has a finite basis B",
			"∃B:set(D → A). "+
				"    finite(B) ∧ "+
				"    module_basis(restrict_ring(R, L), restrict_module(«subfieldVectors», «subfieldSpan»), B)",
			By(
				finiteK,
				moduleK,
				submodules,
				fieldK,
				SubmoduleDim.At(K, subfieldVectors, inv, subfieldSpan),
				FiniteDimensionalDef))
		dimensionK := a.Have(
			"its L-dimension is the size of B",
			"module_dim(restrict_ring(R, L), restrict_module(«subfieldVectors», «subfieldSpan»)) = card(B)",
			By(
				moduleK,
				basis,
				submodules,
				fieldK,
				submodule.SubmoduleModuleOn.At(K, subfieldVectors, subfieldSpan),
				DimBasis.At(
					K,
					a.TermAs[ModuleOps[A, Fun[D, A]]]("restrict_module(«subfieldVectors», «subfieldSpan»)"),
					inv,
					B)))
		generators := a.Have(
			"B has its coordinates in L and spans the L-span of W",
			"B ⊆ finite_supp(R.zero, L, S) ∧ "+
				"module_span(restrict_ring(R, L), «subfieldVectors», B) = «subfieldSpan»",
			BySets(
				moduleK,
				basis,
				submodules,
				linear_independence.BasisRestrict.At(K, subfieldVectors, subfieldSpan, B),
				linear_independence.IndependentInCarrier))
		inside := a.Have(
			"so the L-span of W lies in the R-span of W and in that of B",
			"«subfieldSpan» ⊆ «span» ∧ «subfieldSpan» ⊆ module_span(R, free_module_record(R, S), B)",
			By(combinations.At(W), combinations.At(B), wInL, generators))
		spanB := a.TermAs[Set[Fun[D, A]]]("module_span(R, free_module_record(R, S), B)")
		bInSpan := a.Have(
			"B lies in its L-span, the L-span of W, and so in the R-span of W",
			"B ⊆ «span»",
			BySets(generators, inside, submodule.SubsetSpan.At(K, subfieldVectors, B)))
		wInSpanB := a.Have(
			"and W lies in its L-span, which lies in the R-span of B",
			"W ⊆ module_span(R, free_module_record(R, S), B)",
			BySets(inside, submodule.SubsetSpan.At(K, subfieldVectors, W)))
		same := a.Have(
			"B and W, each in the other's R-span, span one R-space",
			"module_span(R, free_module_record(R, S), B) = «span»",
			BySets(
				bInSpan,
				wInSpanB,
				submodules,
				moduleR,
				lVectorsInR,
				generators,
				submodule.SpanSubmodule.At(R, vectors, B),
				submodule.SpanLeast.At(R, vectors, B, span),
				submodule.SpanLeast.At(R, vectors, W, spanB)))
		spanning := a.Have(
			"B spans the R-span of W, read as a module of its own",
			"module_span(R, restrict_module(free_module_record(R, S), «span»), B) = «span»",
			By(
				moduleR,
				bInSpan,
				same,
				submodules,
				linear_independence.SpanningRestrict.At(R, vectors, span, B)))
		a.Show(
			"a finite spanning set bounds the dimension, and B has the L-dimension as its size",
			ByArith(
				spanning,
				dimensionK,
				moduleR,
				basis,
				submodules,
				fieldR,
				submodule.SubmoduleModuleOn.At(R, vectors, span),
				SpanningBound.At(
					R, a.TermAs[ModuleOps[A, Fun[D, A]]]("restrict_module(free_module_record(R, S), «span»)"), inv, B)))
	}),
})}

// ScalarRestrictionDim — restricting the scalars of a module N along a
// one-to-one ring homomorphism f keeps its dimension: read over R acting
// through f, N has the dimension it has over the image of f. A scalar f(c)
// with c in R is every scalar of the image, so the two readings have the
// same submodules and the same spans; independence is
// ScalarRestrictionIndependent; so the two have the same bases.
var ScalarRestrictionDim = scalarRestrictionDimThm{family.Add(registry.ProofEntry{
	Name: "ScalarRestrictionDim",
	Key:  "prop_9b0edd98bfc18dae",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(C). ∀f:(A → C). ∀N:module_ops(C, D).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, f)",
			"injective_on(R.carrier, f)",
		},
		Conclusion: "module_dim(R, scalar_restriction(f, N)) = " +
			"module_dim(restrict_ring(T, image(f, R.carrier)), N)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		T *Expr[RingOps[C]],
		f *Arrow[A, C],
		N *Expr[ModuleOps[C, D]],
		hom, oneToOne Fact,
	) {
		image := a.TermAs[RingOps[C]]("restrict_ring(T, image(f, R.carrier))")
		restricted := a.TermAs[ModuleOps[A, D]]("scalar_restriction(f, N)")
		submodules := a.Have(
			"the two readings have the same submodules, f(c) for c in R being every scalar of the image",
			"∀X:set(D). "+
				"    submodule(R, scalar_restriction(f, N), X) ⇔ "+
				"    submodule(restrict_ring(T, image(f, R.carrier)), N, X)",
			Simp(
				Fwd(submodule.SubmoduleDef),
				Fwd(module_record.RestrictRingDef),
				Fwd(module_record.ScalarRestrictionDef),
				Fwd(module_record.ModuleAdditiveGroupDef)),
			BySets())
		spans := a.Have(
			"so the same spans, each the meet of the submodules holding a set",
			"∀S:set(D). "+
				"    module_span(R, scalar_restriction(f, N), S) = "+
				"    module_span(restrict_ring(T, image(f, R.carrier)), N, S)",
			Derive(func(b *Argument) {
				b.FixAs[Set[D]]("S")
				b.Do(Simp(Fwd(submodule.ModuleSpanDef)))
				b.Show(
					"the two meets run over the same submodules",
					By(submodules))
			}))
		bases := a.Have(
			"and the same bases: a basis spans the same span and is independent over both at once",
			"∀S:set(D). "+
				"    module_basis(R, scalar_restriction(f, N), S) ⇔ "+
				"    module_basis(restrict_ring(T, image(f, R.carrier)), N, S)",
			a.ForEach(func(S *Expr[Set[D]]) Action {
				return By(
					spans,
					hom,
					oneToOne,
					linear_independence.ModuleBasisDef.At(R, restricted, S),
					linear_independence.ModuleBasisDef.At(image, N, S),
					hom_module.ScalarRestrictionIndependent.At(R, T, f, N, S),
					module_record.ScalarRestrictionDef.At(f, N))
			}))
		a.Show(
			"the dimension, read off the bases, is the same",
			Simp(Fwd(ModuleDimDef)),
			Simp(Fwd(bases)),
			Refl())
	}),
})}

// PairDependentModuloCodimOne — over a field, two vectors u, w of a
// finite-dimensional M are dependent modulo a submodule N of codimension at
// most one: c • u + d • w lies in N for scalars c, d not both zero. If u lies
// in N, 1 • u + 0 • w does. Otherwise the span P of u and N holds N and the
// vector u outside it, so its dimension exceeds N's (ProperSubmoduleDimLess)
// and reaches M's: P is M (SubmoduleDimEq), w is c • u + x with x in N
// (SpanInsert), and −c • u + 1 • w is x.
var PairDependentModuloCodimOne = pairDependentModuloCodimOneThm{family.Add(registry.ProofEntry{
	Name: "PairDependentModuloCodimOne",
	Key:  "prop_c2e4f5c33cc9038b",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀N:set(B). ∀u w:B.",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"finite_dimensional(R, M)",
			"submodule(R, M, N)",
			"module_dim(R, M) ≤ module_dim(R, restrict_module(M, N)) + 1",
			"u ∈ M.carrier",
			"w ∈ M.carrier",
		},
		Conclusion: "∃c d:A. c ∈ R.carrier ∧ d ∈ R.carrier ∧ (c ≠ R.zero ∨ d ≠ R.zero) ∧ c • u + d • w ∈ N",
		Abbrev: Abbrev{
			{Name: "P", Text: "module_span(R, M, insert(u, N))"},
		},
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			N *Expr[Set[B]],
			u, w *Expr[B],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"M is finite-dimensional",
				"N is a submodule of M",
				"N has codimension at most one",
				"u lies in M",
				"w lies in M")
			scalarsField, finiteM, submoduleN, codimension, uInM, wInM :=
				given[0], given[1], given[2], given[3], given[4], given[5]
			ring := module.RingOn.Read(moduleOn)
			oneNotZero := a.Have(
				"one is not zero, the scalars forming a field",
				"R.one ≠ R.zero",
				By(field.OneNotZeroOn.Read(a.Unfolded(scalarsField, field.RingSubfieldDef))))
			a.Cases(a.Term("u ∈ N"))
			a.When(
				"if u lies in N, then 1 • u + 0 • w does",
				func(b *Argument, uInN Fact) {
					b.Take(b.TermAs[A]("R.one"))
					b.Take(b.TermAs[A]("R.zero"))
					b.Show(
						"1 • u lies in N, and 0 • w is zero, which N holds",
						By(
							oneNotZero,
							comm_ring.OneIn.Read(ring),
							comm_ring.ZeroIn.Read(ring),
							uInN,
							wInM,
							submoduleN,
							submodule.SubmoduleSmul,
							module.ZeroSmul,
							submodule.SubmoduleZero,
							submodule.SubmoduleAdd))
				})
			a.Otherwise(
				"otherwise the span P of u and N is M, so w is c • u plus a member x of N, and −c • u + 1 • w is x",
				func(b *Argument, uOutside Fact) {
					R, M := b.TermAs[RingOps[A]]("R"), b.TermAs[ModuleOps[A, B]]("M")
					P := b.TermAs[Set[B]]("«P»")
					generators := b.Have(
						"u and N lie in M",
						"insert(u, N) ⊆ M.carrier",
						BySets(uInM, submodule.SubmoduleSubset.Read(submoduleN)))
					submoduleP := b.Have(
						"P is a submodule of M",
						"submodule(R, M, «P»)",
						By(moduleOn, generators, submodule.SpanSubmodule))
					holds := b.Have(
						"P holds N and u",
						"N ⊆ «P» ∧ u ∈ «P»",
						BySets(submodule.SubsetSpan.At(R, M, b.TermAs[Set[B]]("insert(u, N)"))))
					larger := b.Have(
						"P holds N and the vector u outside it, so P's dimension exceeds N's",
						"module_dim(R, restrict_module(M, N)) + 1 ≤ module_dim(R, restrict_module(M, «P»))",
						By(
							uOutside,
							scalarsField,
							moduleOn,
							finiteM,
							submoduleN,
							submoduleP,
							holds,
							ProperSubmoduleDimLess.At(R, inv, M, N, P, u)))
					full := b.Have(
						"so P has the dimension of M, which is at most one more than N's",
						"module_dim(R, restrict_module(M, «P»)) = module_dim(R, M)",
						ByArith(
							larger,
							codimension,
							scalarsField,
							moduleOn,
							finiteM,
							submoduleP,
							SubmoduleDim.Read(moduleOn).At(inv, P)))
					everything := b.Have(
						"so P is M",
						"«P» = M.carrier",
						By(full, scalarsField, moduleOn, finiteM, submoduleP, SubmoduleDimEq.Read(moduleOn).At(inv, P)))
					c, _, decomposed := b.Obtain2As[A, B](
						"w lies in P, the sums c • u + x with c a scalar and x in N",
						"∃c:A. ∃x:B. c ∈ R.carrier ∧ x ∈ N ∧ w = c • u + x",
						BySets(
							everything,
							moduleOn,
							wInM,
							uInM,
							submoduleN,
							submodule.SpanInsert.At(R, M, N, u),
							submodule.SpanOfSubmodule.At(R, M, N),
							submodule.SubmoduleSubset.At(R, M, N)))
					cancel := b.Have(
						"−c • u + 1 • w is x",
						"-c • u + R.one • w = x",
						ByChase(Depth(0), moduleOn, uInM, decomposed, submoduleN))
					b.Take(b.TermAs[A]("-c"))
					b.Take(b.TermAs[A]("R.one"))
					b.Show(
						"−c and 1 are scalars, 1 is not zero, and −c • u + 1 • w is x, in N",
						By(
							Normalized,
							oneNotZero,
							comm_ring.OneIn.Read(ring),
							cancel,
							decomposed,
							comm_ring.NegIn.Read(ring).AsFact().At(c)))
				})
		}),
})}
