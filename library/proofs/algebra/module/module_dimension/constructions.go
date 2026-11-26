// constructions.go — the dimension of a module built from others: the
// product of two modules and the dual of one, each by exhibiting a basis
// of the constructed module and counting it.

package module_dimension

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The product and the dual
// ---------------------------------------------------------------------------

// DimProduct — over a field, the product of two finite-dimensional
// modules is finite-dimensional, and the dimensions add: finite bases E
// of M and F of N, carried into the two axes u ↦ (u, N.zero) and
// v ↦ (M.zero, v), together form a basis of the product with
// card(E) + card(F) members.
var DimProduct = dimProductThm{family.Add(registry.ProofEntry{
	Name: "DimProduct",
	Key:  "prop_929e7753a84f4b19",
	Reading: "The two halves of the basis do not meet: (e, N.zero) = (M.zero, e') would " +
		"put M.zero in a basis of M, which over a field holds no zero (one ≠ zero). With M " +
		"or N the zero module its basis is ∅ and the product's dimension is the other's.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_on(R, N)",
			"finite_dimensional(R, M)",
			"finite_dimensional(R, N)",
		},
		Conclusion: "finite_dimensional(R, product_module(M, N)) ∧ " +
			"module_dim(R, product_module(M, N)) = module_dim(R, M) + module_dim(R, N)",
		Abbrev: Abbrev{
			{Name: "dimProductFirstHalf", Text: "image(λu:B. (u, N.zero), E)"},
			{Name: "dimProductSecondHalf", Text: "image(λv:C. (M.zero, v), F)"},
			{Name: "dimProductBasis", Text: "«dimProductFirstHalf» ∪ «dimProductSecondHalf»"},
			{Name: "dimProductSpan", Text: "module_span(R, product_module(M, N), «dimProductBasis»)"},
			{Name: "dimProductFirstAxis", Text: "image(λu:B. (u, N.zero), M.carrier)"},
			{Name: "dimProductSecondAxis", Text: "image(λv:C. (M.zero, v), N.carrier)"},
		},
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			N *Expr[ModuleOps[A, C]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"N is an R-module",
				"M is finite-dimensional",
				"N is finite-dimensional")
			scalarsField, moduleN, finiteM, finiteN := given[0], given[1], given[2], given[3]
			fieldR := a.Unfolded(scalarsField, field.RingSubfieldDef)
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			P := a.TermAs[ModuleOps[A, Prod[B, C]]]("product_module(M, N)")
			carrierM, carrierN := a.TermAs[Set[B]]("M.carrier"), a.TermAs[Set[C]]("N.carrier")

			// A finite basis E of M and one F of N.
			E, onE := a.UnpackAs[Set[B]](a.Unfolded(finiteM, FiniteDimensionalDef), "E")
			F, onF := a.UnpackAs[Set[C]](a.Unfolded(finiteN, FiniteDimensionalDef), "F")
			ofE := a.Conjuncts(
				onE,
				"E is finite",
				"E is a basis of M")
			ofF := a.Conjuncts(
				onF,
				"F is finite",
				"F is a basis of N")
			finiteE, basisE := ofE[0], ofE[1]
			finiteF, basisF := ofF[0], ofF[1]
			ofBasisE := a.Conjuncts(
				a.Unfolded(basisE, linear_independence.ModuleBasisDef),
				"E is independent in M",
				"E spans M")
			ofBasisF := a.Conjuncts(
				a.Unfolded(basisF, linear_independence.ModuleBasisDef),
				"F is independent in N",
				"F spans N")
			independentE, spansM := ofBasisE[0], ofBasisE[1]
			independentF, spansN := ofBasisF[0], ofBasisF[1]

			// The product, and M and N inside it as the two axes.
			product := a.Conjuncts(
				a.Have(
					"the product is an R-module, M entering it by u ↦ (u, N.zero) and N by v ↦ (M.zero, v)",
					"module_on(R, product_module(M, N)) ∧ "+
						"module_homomorphism(R, M, product_module(M, N), λu:B. (u, N.zero)) ∧ "+
						"module_homomorphism(R, N, product_module(M, N), λv:C. (M.zero, v))",
					By(moduleOn, moduleN, module_homomorphism.ProductModuleOn.At(R, M, N))),
				"the product is an R-module",
				"u ↦ (u, N.zero) is a homomorphism",
				"v ↦ (M.zero, v) is a homomorphism")
			moduleP, intoFirst, intoSecond := product[0], product[1], product[2]
			first, second :=
				a.TermAs[Fun[B, Prod[B, C]]]("λu:B. (u, N.zero)"), a.TermAs[Fun[C, Prod[B, C]]]("λv:C. (M.zero, v)")
			firstOneToOne := a.Have(
				"u ↦ (u, N.zero) is one-to-one: a pair determines its first component",
				"∀s:set(B). injective_on(s, λu:B. (u, N.zero))",
				Unfold(functions.InjectiveOnDef),
				By(pairs.PairEq))
			secondOneToOne := a.Have(
				"and so is v ↦ (M.zero, v): a pair determines its second component",
				"∀t:set(C). injective_on(t, λv:C. (M.zero, v))",
				Unfold(functions.InjectiveOnDef),
				By(pairs.PairEq))

			// The two halves of the basis, and the axes they span.
			firstHalf, secondHalf :=
				a.TermAs[Set[Prod[B, C]]]("«dimProductFirstHalf»"),
				a.TermAs[Set[Prod[B, C]]]("«dimProductSecondHalf»")
			basis, span :=
				a.TermAs[Set[Prod[B, C]]]("«dimProductBasis»"), a.TermAs[Set[Prod[B, C]]]("«dimProductSpan»")
			firstAxis := a.Have(
				"the first half spans the first axis: u ↦ (u, N.zero) carries "+
					"the span of E, all of M, onto the span of the image of E",
				"module_span(R, product_module(M, N), «dimProductFirstHalf») = «dimProductFirstAxis»",
				By(
					linear_independence.HomSpan.At(R, M, P, first, E),
					intoFirst,
					linear_independence.IndependentInCarrier.Read(independentE),
					spansM))
			secondAxis := a.Have(
				"and the second half the second axis, the image of N",
				"module_span(R, product_module(M, N), «dimProductSecondHalf») = «dimProductSecondAxis»",
				By(
					linear_independence.HomSpan.At(R, N, P, second, F),
					intoSecond,
					linear_independence.IndependentInCarrier.Read(independentF),
					spansN))

			// The union is independent: each half is, and their spans, the two axes, meet only in zero.
			firstIndependent := a.Have(
				"the first half is independent, u ↦ (u, N.zero) being a one-to-one homomorphism",
				"module_independent(R, product_module(M, N), «dimProductFirstHalf»)",
				By(
					linear_independence.IndependentImage.At(R, M, P, first, E),
					intoFirst,
					firstOneToOne.At(carrierM),
					independentE))
			secondIndependent := a.Have(
				"and so is the second half",
				"module_independent(R, product_module(M, N), «dimProductSecondHalf»)",
				By(
					linear_independence.IndependentImage.At(R, N, P, second, F),
					intoSecond,
					secondOneToOne.At(carrierN),
					independentF))
			axesMeet := a.Have(
				"the axes meet only in (M.zero, N.zero): (u, N.zero) "+
					"= (M.zero, v) forces u = M.zero and v = N.zero",
				"«dimProductFirstAxis» ∩ «dimProductSecondAxis» ⊆ {(M.zero, N.zero)}",
				BySets(pairs.PairEq))
			spansMeet := a.Have(
				"so the spans of the halves meet only in the zero of the product",
				"module_span(R, product_module(M, N), «dimProductFirstHalf») ∩ "+
					"module_span(R, product_module(M, N), «dimProductSecondHalf») ⊆ "+
					"{(M.zero, N.zero)}",
				firstAxis.Rw(),
				secondAxis.Rw(),
				By(axesMeet))
			independent := a.Have(
				"so the union of the halves is independent",
				"module_independent(R, product_module(M, N), «dimProductBasis»)",
				By(
					linear_independence.IndependentUnion.Read(moduleP).At(firstHalf, secondHalf),
					firstIndependent,
					secondIndependent,
					spansMeet))

			// The union spans: a pair is the sum of a point of each axis.
			spanSubmodule := a.Have(
				"its span is a submodule of the product",
				"submodule(R, product_module(M, N), «dimProductSpan»)",
				By(
					moduleP,
					submodule.SpanSubmodule.At(R, P, basis),
					linear_independence.IndependentInCarrier.Read(independent)))
			halves := a.Conjuncts(
				a.Have(
					"which holds both halves",
					"«dimProductFirstHalf» ⊆ «dimProductSpan» ∧ «dimProductSecondHalf» ⊆ «dimProductSpan»",
					By(submodule.SubsetSpan.At(R, P, basis), set_order.UnionSubset.At(firstHalf, secondHalf, span))),
				"the span holds the first half",
				"the span holds the second half")
			firstHalfIn, secondHalfIn := halves[0], halves[1]
			firstAxisIn := a.Have(
				"so it holds the first axis, the least submodule holding the first half",
				"«dimProductFirstAxis» ⊆ «dimProductSpan»",
				firstAxis.RwRev(),
				By(spanSubmodule, firstHalfIn, submodule.SpanLeast.At(R, P, firstHalf, span)))
			secondAxisIn := a.Have(
				"and the second axis",
				"«dimProductSecondAxis» ⊆ «dimProductSpan»",
				secondAxis.RwRev(),
				By(spanSubmodule, secondHalfIn, submodule.SpanLeast.At(R, P, secondHalf, span)))
			onFirstAxis, onSecondAxis :=
				a.Unfolded(firstAxisIn, set_basic.SubsetDef), a.Unfolded(secondAxisIn, set_basic.SubsetDef)
			everyPair := a.Have(
				"a pair z of the product is (fst(z), N.zero) + (M.zero, snd(z)), a point of each axis added",
				"∀z:prod(B, C). z ∈ set_cross(M.carrier, N.carrier) ⇒ z ∈ «dimProductSpan»",
				Derive(func(b *Argument) {
					z := b.FixAs[Prod[B, C]]("z")
					inProduct := b.Assume()
					parts := b.Conjuncts(
						b.Have(
							"its components lie in M and N",
							"fst(z) ∈ M.carrier ∧ snd(z) ∈ N.carrier",
							By(inProduct, set_product.InCrossProjections.At(carrierM, carrierN, z))),
						"fst(z) lies in M",
						"snd(z) lies in N")
					xInM, yInN := parts[0], parts[1]
					x, y := b.TermAs[B]("fst(z)"), b.TermAs[C]("snd(z)")
					onFirst, onSecond :=
						b.TermAs[Prod[B, C]]("(fst(z), N.zero)"), b.TermAs[Prod[B, C]]("(M.zero, snd(z))")
					firstIn := b.Have(
						"(fst(z), N.zero) lies on the first axis, so in the span",
						"(fst(z), N.zero) ∈ «dimProductSpan»",
						By(onFirstAxis.At(onFirst), set_image.FunInImage.At(first, carrierM, x), xInM))
					secondIn := b.Have(
						"(M.zero, snd(z)) lies on the second axis, so in the span",
						"(M.zero, snd(z)) ∈ «dimProductSpan»",
						By(onSecondAxis.At(onSecond), set_image.FunInImage.At(second, carrierN, y), yInN))
					sum := b.Have(
						"so does their sum, added componentwise, the span being a submodule",
						"(fst(z) + M.zero, N.zero + snd(z)) ∈ «dimProductSpan»",
						By(
							spanSubmodule,
							firstIn,
							secondIn,
							pairs.Fst,
							pairs.Snd,
							submodule.SubmoduleAdd.At(R, P, span, onFirst, onSecond)))
					b.Show(
						"and the sum is z, M.zero and N.zero being the identities of the two additions",
						By(
							sum,
							group.RightIdentityOn.Read(module.AddGroupOn.Read(moduleOn)).At(b.MemberOf[on.M](x, xInM)),
							group.LeftIdentityOn.Read(module.AddGroupOn.Read(moduleN)).At(proof.MemberOf(y, yInN)),
							pairs.PairEta.At(z)))
				}))
			cross := a.TermAs[Set[Prod[B, C]]]("set_cross(M.carrier, N.carrier)")
			holds := a.Have(
				"so the span holds the carrier of the product",
				"set_cross(M.carrier, N.carrier) ⊆ «dimProductSpan»",
				BySets(everyPair))
			spans := a.Have(
				"and, a submodule, lies in that carrier, so the union spans the product",
				"«dimProductSpan» = set_cross(M.carrier, N.carrier)",
				By(
					spanSubmodule,
					submodule.SubmoduleSubset.At(R, P, span),
					holds,
					set_order.SubsetAntisym.At(span, cross)))
			basisP := a.Have(
				"the union is a basis of the product",
				"module_basis(R, product_module(M, N), «dimProductBasis»)",
				By(independent, spans, linear_independence.ModuleBasisDef.At(R, P, basis)))

			// The union has card(E) + card(F) members.
			zeroOutside := a.Have(
				"M.zero is not in E, an independent set over a field, where one ≠ zero",
				"M.zero ∉ E",
				By(
					independentE,
					field.OneNotZeroOn.Read(fieldR),
					linear_independence.IndependentZeroNotIn.Read(moduleOn).At(E)))
			disjointHalves := a.Have(
				"the halves are disjoint: (u, N.zero) = (M.zero, v) with u in E would put M.zero in E",
				"disjoint(«dimProductFirstHalf», «dimProductSecondHalf»)",
				Unfold(set_basic.DisjointDef),
				BySets(zeroOutside, pairs.PairEq))
			cardE, cardF := a.TermAs[Nat]("card(E)"), a.TermAs[Nat]("card(F)")
			firstSize := a.Have(
				"the first half has card(E) members, u ↦ (u, N.zero) being one-to-one",
				"has_size(«dimProductFirstHalf», card(E))",
				By(
					firstOneToOne.At(E),
					finiteE,
					cardinality.FiniteHasSize.At(E),
					cardinality.HasSizeImageInj.At(first, E, cardE)))
			secondSize := a.Have(
				"and the second card(F)",
				"has_size(«dimProductSecondHalf», card(F))",
				By(
					secondOneToOne.At(F),
					finiteF,
					cardinality.FiniteHasSize.At(F),
					cardinality.HasSizeImageInj.At(second, F, cardF)))
			size := a.Have(
				"so the union of the disjoint halves has card(E) + card(F)",
				"has_size(«dimProductBasis», card(E) + card(F))",
				By(
					firstSize,
					secondSize,
					disjointHalves,
					cardinality.HasSizeUnion.At(firstHalf, secondHalf, cardE, cardF)))
			counted := a.Conjuncts(
				a.Unfolded(size, cardinality.HasSizeDef),
				"the union is finite",
				"it has card(E) + card(F) members")
			finiteBasis, unionSize := counted[0], counted[1]

			// Three dimensions, each the size of a finite basis.
			productDim := a.Conjuncts(
				a.Have(
					"so the union is a finite basis of the product, which is finite-dimensional of dimension its size",
					"finite_dimensional(R, product_module(M, N)) ∧ "+
						"module_dim(R, product_module(M, N)) = card(«dimProductBasis»)",
					By(scalarsField, basisP, finiteBasis, FiniteBasisDim.Read(moduleP).At(inv, basis))),
				"the product is finite-dimensional",
				"its dimension is the size of the union")
			finiteP, dimP := productDim[0], productDim[1]
			dimM := a.Have(
				"the dimension of M is the size of its basis E",
				"module_dim(R, M) = card(E)",
				By(scalarsField, basisE, finiteE, DimBasis.Read(moduleOn).At(inv, E)))
			dimN := a.Have(
				"and that of N the size of F",
				"module_dim(R, N) = card(F)",
				By(scalarsField, basisF, finiteF, DimBasis.Read(moduleN).At(inv, F)))
			dimension := a.Have(
				"the dimensions add",
				"module_dim(R, product_module(M, N)) = module_dim(R, M) + module_dim(R, N)",
				CalcEq(
					Leg(
						a.TermAs[Nat]("card(«dimProductBasis»)"),
						"the product's is the size of its finite basis",
						By(dimP)),
					Leg(
						a.TermAs[Nat]("card(E) + card(F)"),
						"which counts the two halves",
						By(unionSize)),
					FinalLeg(
						"which are the dimensions of M and N",
						By(Normalized, dimM, dimN)),
				))
			a.Show(
				"the product is finite-dimensional, of the summed dimension",
				By(finiteP, dimension))
		}),
})}

// DualDim — over a field, the dual of a finite-dimensional module, its
// linear maps to the scalars, is finite-dimensional of the same
// dimension: the coordinate functionals of a finite basis E of M, coord(e)
// reading off a vector its coefficient at e, are a basis of the dual with
// one member for each member of E.
var DualDim = dualDimThm{family.Add(registry.ProofEntry{
	Name: "DualDim",
	Key:  "prop_b530c72465425399",
	Reading: "The dual is hom_module(R, M, R): the R-linear maps from M to the scalars, R a " +
		"module over itself through its product, each zero off M.carrier as hom_set asks, under " +
		"the pointwise operations. finite_dimensional(R, M) is load-bearing: without it " +
		"module_dim(R, M) is a chosen number, and an infinite-dimensional space's dual has no " +
		"finite basis. At the zero module the dual is the one zero map and both dimensions are 0.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"finite_dimensional(R, M)",
		},
		Conclusion: "finite_dimensional(R, hom_module(R, M, regular_module(R))) ∧ " +
			"module_dim(R, hom_module(R, M, regular_module(R))) = module_dim(R, M)",
		Abbrev: Abbrev{
			{Name: "dualDimSpace", Text: "hom_module(R, M, regular_module(R))"},
			{Name: "dualDimMaps", Text: "hom_set(R, M, regular_module(R))"},
			{Name: "dualDimSpan", Text: "module_span(R, «dualDimSpace», image(coord, E))"},
		},
	},
		func(a *Argument, moduleOn module.ModuleFact[on.R, on.M], inv *Arrow[A, A], hypotheses Fact) {
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			scalars := a.TermAs[ModuleOps[A, A]]("regular_module(R)")
			dual := a.TermAs[ModuleOps[A, Fun[B, A]]]("«dualDimSpace»")
			maps := a.TermAs[Set[Fun[B, A]]]("«dualDimMaps»")
			mul := a.TermAs[Op[A]]("R.mul")
			ring := module.RingOn.Read(moduleOn)
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"M is finite-dimensional")
			scalarsField, finiteM := given[0], given[1]
			fieldR := a.Unfolded(scalarsField, field.RingSubfieldDef)

			E, hasBasis := a.UnpackAs[Set[B]](a.Unfolded(finiteM, FiniteDimensionalDef), "E")
			onE := a.Conjuncts(
				hasBasis,
				"E is finite",
				"E is a basis of M")
			finiteE, basisE := onE[0], onE[1]
			eInM := a.Have(
				"a basis lies in M",
				"E ⊆ M.carrier",
				By(linear_independence.BasisInCarrier.Read(basisE)))
			inM := a.Unfolded(eInM, set_basic.SubsetDef)

			// The dual and its members.
			selfModule := a.Have(
				"R is a module over itself, scaling by its product",
				"module_on(R, regular_module(R))",
				By(module.RegularModuleOn, ring))
			dualModule := a.Have(
				"so the linear maps from M to R, zero off M, form a module under the pointwise operations",
				"module_on(R, «dualDimSpace»)",
				By(moduleOn, selfModule, hom_module.HomSetModuleOn.At(R, M, scalars)))
			inDual := a.Have(
				"a map lies in the dual when it is linear and zero off M",
				"∀φ:(B → A). "+
					"    φ ∈ «dualDimMaps» ⇔ "+
					"    module_homomorphism(R, M, regular_module(R), φ) ∧ (∀u:B. u ∉ M.carrier ⇒ φ(u) = R.zero)",
				Simp(Fwd(hom_module.HomSetDef)),
				BySets())
			values := a.Have(
				"a member of the dual takes its values in R: on M by linearity, and off M it is R.zero",
				"∀φ:(B → A). ∀z:B. φ ∈ «dualDimMaps» ⇒ φ(z) ∈ R.carrier",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[B, A]]("φ")
					z := b.FixAs[B]("z")
					member := b.Assume()
					b.Show(
						"φ(z) is a value of a linear map into R, or R.zero",
						By(
							member,
							inDual.At(φ),
							module_homomorphism.HomIn.At(R, M, scalars, φ, z),
							comm_ring.ZeroIn.Read(ring)))
				}))

			// The coordinate functionals: coord(e) reads off a vector of M its
			// coefficient at e, and is R.zero off M.
			coord, coordDef := a.LetAs[Fun[B, Fun[B, A]]](
				"coord", "λe:B. λv:B. COND(v ∈ M.carrier, module_basis_coordinates(R, M, E, v, e), R.zero)")
			functionals := a.TermAs[Set[Fun[B, A]]]("image(coord, E)")
			coordInDual := a.Have(
				"each coord(e) is linear and zero off M, a member of the dual",
				"∀e:B. e ∈ E ⇒ coord(e) ∈ «dualDimMaps»",
				Derive(func(b *Argument) {
					e := b.FixAs[B]("e")
					eIn := b.Assume()
					guarded := b.TermAs[Fun[B, A]](
						"λv:B. COND(v ∈ M.carrier, module_basis_coordinates(R, M, E, v, e), R.zero)")
					agree := b.Have(
						"on M the COND form is the coordinate at e",
						Statement{
							Binders: "∀v:B.",
							Hypotheses: []string{
								"v ∈ M.carrier",
							},
							Conclusion: "COND(v ∈ M.carrier, module_basis_coordinates(R, M, E, v, e), R.zero) = " +
								"module_basis_coordinates(R, M, E, v, e)",
						},
						b.ForEach(func(_ *Expr[B]) Action { return Basic() }))
					b.Show(
						"the coefficient at e is a linear functional, and the COND makes it R.zero off M",
						coordDef.Rw(),
						By(
							eIn,
							finiteE,
							basisE,
							agree,
							inDual.At(guarded),
							BasisCoordinateLinear.Read(moduleOn).At(E, e),
							module_homomorphism.HomCongruence.At(R, M, b.TermAs[ModuleOps[A, A]]("regular_module(R)"),
								b.TermAs[Fun[B, A]]("λv:B. module_basis_coordinates(R, M, E, v, e)"), guarded)))
				}))
			delta := a.Have(
				"coord(e) is R.one at e and R.zero at the other members of E",
				"∀e d:B. e ∈ E ∧ d ∈ E ⇒ coord(e)(d) = COND(e = d, R.one, R.zero)",
				Derive(func(b *Argument) {
					b.FixAs[B]("e")
					d := b.FixAs[B]("d")
					both := b.Assume()
					kronecker := b.Have(
						"the coordinates of d, a member of E, are the Kronecker delta at d",
						"module_basis_coordinates(R, M, E, d) = λx:B. COND(x = d, R.one, R.zero)",
						By(both, finiteE, basisE, BasisCoordinateDelta.Read(moduleOn).At(E, d)))
					b.Show(
						"coord(e)(d) is the coordinate of d at e, d lying in M, and that is the delta at d read at e",
						coordDef.Rw(),
						kronecker.Rw(),
						By(both, inM.At(d)))
				}))
			among := a.Have(
				"each member of image(coord, E) is some coord(e), a member of the dual",
				"∀φ:(B → A). φ ∈ image(coord, E) ⇒ φ ∈ «dualDimMaps»",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[B, A]]("φ")
					inImage := b.Assume()
					_, isCoordinate := b.ObtainAs[B](
						"φ is coord(e) for some e of E",
						"∃e:B. φ = coord(e) ∧ e ∈ E",
						By(inImage, set_basic.InImage.At(coord, E, φ)))
					b.Show(
						"and coord(e) lies in the dual",
						By(isCoordinate, coordInDual))
				}))
			functionalsInDual := a.Have(
				"so the coordinate functionals lie in the dual",
				"image(coord, E) ⊆ «dualDimMaps»",
				BySets(among))

			// One functional for each member of E: coord(x) is R.one at x and
			// coord(y) is R.zero there, and over a field one ≠ zero.
			separated := a.Have(
				"distinct members of E have distinct coordinate functionals",
				"∀x y:B. x ∈ E ∧ y ∈ E ∧ coord(x) = coord(y) ⇒ x = y",
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					y := b.FixAs[B]("y")
					equal := b.Assume()
					b.Show(
						"coord(x) and coord(y) agree at x, where one is R.one and the other R.zero unless x = y",
						By(equal, delta.At(x, x), delta.At(y, x), field.OneNotZeroOn.Read(fieldR)))
				}))
			size := a.Have(
				"so e ↦ coord(e) is one-to-one on E, and the "+
					"coordinate functionals are as many as the members of E",
				"has_size(image(coord, E), card(E))",
				By(
					separated,
					functions.InjectiveOnDef.At(E, coord),
					finiteE,
					cardinality.FiniteHasSize.At(E),
					cardinality.HasSizeImageInj.At(coord, E, a.TermAs[Nat]("card(E)"))))

			// Independent: a vanishing combination, evaluated at the member d of
			// E with ψ = coord(d), is its coefficient at ψ.
			vanishing := a.Have(
				"only the zero combination of coordinate functionals is the zero map",
				Statement{
					Binders: "∀T:set(B → A). ∀c:((B → A) → A).",
					Hypotheses: []string{
						"finite(T)",
						"T ⊆ image(coord, E)",
						"∀x:(B → A). x ∈ T ⇒ c(x) ∈ R.carrier",
						"module_sum(fun_add(R.add), fun_zero(R.zero), T, λx:(B → A). fun_smul(c(x), x)) = fun_zero(R.zero)",
					},
					Conclusion: "∀ψ:(B → A). ψ ∈ T ⇒ c(ψ) = R.zero",
				},
				Derive(func(b *Argument) {
					T := b.FixAs[Set[Fun[B, A]]]("T")
					b.FixAs[Fun[Fun[B, A], A]]("c")
					combination := b.Conjuncts(
						b.Assume(),
						"T is finite",
						"T consists of coordinate functionals",
						"c is a scalar on T",
						"the combination is the zero map")
					finiteT, inFunctionals, scalarsT, vanishes :=
						combination[0], combination[1], combination[2], combination[3]
					amongFunctionals := b.Unfolded(inFunctionals, set_basic.SubsetDef)
					tInDual := b.Unfolded(b.Have(
						"T lies in the dual",
						"T ⊆ «dualDimMaps»",
						By(
							inFunctionals,
							functionalsInDual,
							set_order.SubsetTrans.At(T, functionals, maps))), set_basic.SubsetDef)
					terms := b.Have(
						"each term c(x) • x takes its values in R",
						"∀x:(B → A). ∀z:B. x ∈ T ⇒ fun_smul(c(x), x, z) ∈ R.carrier",
						Derive(func(p *Argument) {
							x := p.FixAs[Fun[B, A]]("x")
							z := p.FixAs[B]("z")
							xIn := p.Assume()
							p.Show(
								"c(x) and x(z) lie in R, and so does their product",
								By(
									Normalized,
									xIn,
									scalarsT.At(x),
									tInDual.At(x),
									values.At(x, z),
									function_module.FunSmulDef.At(mul, p.TermAs[A]("c(x)"), x, z),
									comm_ring.MulIn.Read(ring)))
						}))

					ψ := b.FixAs[Fun[B, A]]("ψ")
					ψIn := b.Assume()
					d, ψIsCoordinate := b.ObtainAs[B](
						"ψ is coord(d) for some d of E",
						"∃d:B. ψ = coord(d) ∧ d ∈ E",
						By(ψIn, amongFunctionals.At(ψ), set_basic.InImage.At(coord, E, ψ)))
					onψ := b.Conjuncts(
						ψIsCoordinate,
						"ψ is coord(d)",
						"d lies in E")
					ψIs, dIn := onψ[0], onψ[1]
					evaluated := b.Have(
						"evaluated at d, the vanishing combination is a vanishing sum in R",
						"module_sum(R.add, R.zero, T, λx:(B → A). fun_smul(c(x), x, d)) = R.zero",
						By(
							vanishes,
							finiteT,
							terms,
							function_module.FunZeroDef,
							function_module.ModuleSumApply.Read(selfModule).At(
								T, b.TermAs[Fun2[Fun[B, A], B, A]]("λx:(B → A). fun_smul(c(x), x)"), d)))
					offDiagonal := b.Have(
						"every other functional of T is R.zero at d, and so is its term",
						"∀y:(B → A). y ∈ T ∧ ¬(y = ψ) ⇒ fun_smul(c(y), y, d) = R.zero",
						Derive(func(p *Argument) {
							y := p.FixAs[Fun[B, A]]("y")
							other := p.Assume()
							e, yIsCoordinate := p.ObtainAs[B](
								"y is coord(e) for some e of E",
								"∃e:B. y = coord(e) ∧ e ∈ E",
								By(other, amongFunctionals.At(y), set_basic.InImage.At(coord, E, y)))
							onY := p.Conjuncts(
								yIsCoordinate,
								"y is coord(e)",
								"e lies in E")
							apart := p.Have(
								"e ≠ d, as y ≠ ψ = coord(d)",
								"¬(e = d)",
								By(other, onY[0], ψIs))
							cy := p.TermAs[A]("c(y)")
							p.Show(
								"coord(e) is R.zero at d, and c(y) * R.zero = R.zero",
								By(
									Normalized,
									other,
									onY[0],
									onY[1],
									dIn,
									apart,
									delta.At(e, d),
									scalarsT.At(y),
									function_module.FunSmulDef.At(mul, cy, y, d),
									comm_ring.MulRightZeroOn.Read(ring).AsFact().At(cy)))
						}))
					single := b.Have(
						"so the sum at d is its term at ψ",
						"module_sum(R.add, R.zero, T, λx:(B → A). fun_smul(c(x), x, d)) = fun_smul(c(ψ), ψ, d)",
						By(
							finiteT,
							ψIn,
							terms,
							offDiagonal,
							module.ModuleSumSingle.Read(selfModule).At(
								T, ψ, b.TermAs[Fun[Fun[B, A], A]]("λx:(B → A). fun_smul(c(x), x, d)"))))
					atOne := b.Have(
						"ψ = coord(d) is R.one at d",
						"ψ(d) = R.one",
						By(Normalized, ψIs, dIn, delta.At(d, d)))
					cψ := b.TermAs[A]("c(ψ)")
					b.Show(
						"c(ψ) is c(ψ) * ψ(d), the sum at d, which is R.zero",
						CalcEq(
							Leg(
								b.TermAs[A]("fun_smul(c(ψ), ψ, d)"),
								"ψ(d) = R.one",
								By(
									Normalized,
									atOne,
									ψIn,
									scalarsT.At(ψ),
									function_module.FunSmulDef.At(mul, cψ, ψ, d),
									comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(cψ))),
							Leg(
								b.TermAs[A]("module_sum(R.add, R.zero, T, λx:(B → A). fun_smul(c(x), x, d))"),
								"the term at ψ is the whole sum at d",
								By(single)),
							FinalLeg(
								"and the sum at d vanishes",
								By(evaluated)),
						))
				}))
			independent := a.Have(
				"the coordinate functionals are independent in the dual",
				"module_independent(R, «dualDimSpace», image(coord, E))",
				By(
					functionalsInDual,
					vanishing,
					linear_independence.ModuleIndependentDef.At(R, dual, functionals),
					hom_module.HomModuleDef.At(R, M, scalars)))

			// Spanning: a member φ of the dual is Σ φ(e) • coord(e), the two
			// agreeing on M along the expansion of a vector by its coordinates
			// and both R.zero off M.
			spanned := a.TermAs[Set[Fun[B, A]]]("«dualDimSpan»")
			carrierSubmodule := a.Have(
				"the dual's carrier is a submodule of the dual",
				"submodule(R, «dualDimSpace», «dualDimMaps»)",
				By(dualModule, submodule.CarrierSubmodule.At(R, dual), hom_module.HomModuleDef.At(R, M, scalars)))
			withinDual := a.Have(
				"so the span of the coordinate functionals lies in the dual",
				"«dualDimSpan» ⊆ «dualDimMaps»",
				By(carrierSubmodule, functionalsInDual, submodule.SpanLeast.At(R, dual, functionals, maps)))
			spanSubmodule := a.Have(
				"the span is a submodule of the dual",
				"submodule(R, «dualDimSpace», «dualDimSpan»)",
				By(
					dualModule,
					functionalsInDual,
					submodule.SpanSubmodule.At(R, dual, functionals),
					hom_module.HomModuleDef.At(R, M, scalars)))
			inSpan := a.Unfolded(a.Have(
				"the span holds the coordinate functionals",
				"image(coord, E) ⊆ «dualDimSpan»",
				Cite(submodule.SubsetSpan, R, dual, functionals)), set_basic.SubsetDef)
			reached := a.Have(
				"every member of the dual lies in the span",
				"∀φ:(B → A). φ ∈ «dualDimMaps» ⇒ φ ∈ «dualDimSpan»",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[B, A]]("φ")
					φIn := b.Assume()
					onφ := b.Conjuncts(
						b.Have(
							"φ is linear and zero off M",
							"module_homomorphism(R, M, regular_module(R), φ) ∧ (∀u:B. u ∉ M.carrier ⇒ φ(u) = R.zero)",
							By(φIn, inDual.At(φ))),
						"φ is linear",
						"φ is R.zero off M")
					linearφ, zeroOff := onφ[0], onφ[1]
					terms := b.Have(
						"each term φ(e) • coord(e) takes its values in R",
						"∀e z:B. e ∈ E ⇒ fun_smul(φ(e), coord(e), z) ∈ R.carrier",
						Derive(func(p *Argument) {
							e := p.FixAs[B]("e")
							z := p.FixAs[B]("z")
							eIn := p.Assume()
							coordE := p.TermAs[Fun[B, A]]("coord(e)")
							p.Show(
								"φ(e) and coord(e)(z) lie in R, and so does their product",
								By(
									eIn,
									φIn,
									values.At(φ, e),
									values.At(coordE, z),
									coordInDual.At(e),
									function_module.FunSmulDef.At(mul, p.TermAs[A]("φ(e)"), coordE, z),
									comm_ring.MulIn.Read(ring)))
						}))
					termsInSpan := b.Have(
						"each term lies in the span, a submodule closed under scaling",
						"∀e:B. e ∈ E ⇒ fun_smul(φ(e), coord(e)) ∈ «dualDimSpan»",
						Derive(func(p *Argument) {
							e := p.FixAs[B]("e")
							eIn := p.Assume()
							coordIn := p.Have(
								"coord(e) lies in the span",
								"coord(e) ∈ «dualDimSpan»",
								By(eIn, inSpan.At(p.TermAs[Fun[B, A]]("coord(e)")), set_image.FunInImage.At(coord, E, e)))
							p.Show(
								"φ(e) is a scalar, and the span is closed under scaling",
								By(
									coordIn,
									φIn,
									values.At(φ, e),
									submodule.SubmoduleSmul.Read(spanSubmodule),
									hom_module.HomModuleDef))
						}))
					combinationIn := b.Have(
						"so the combination Σ φ(e) • coord(e) lies in the span",
						"module_sum(fun_add(R.add), fun_zero(R.zero), E, λe:B. fun_smul(φ(e), coord(e))) ∈ «dualDimSpan»",
						By(
							finiteE,
							termsInSpan,
							dualModule,
							spanSubmodule,
							submodule.SubmoduleModuleSum.At(
								R, dual, spanned, E, b.TermAs[Fun[B, Fun[B, A]]]("λe:B. fun_smul(φ(e), coord(e))"))))
					pointwise := b.Have(
						"φ and the combination agree at every point",
						"∀w:B. φ(w) = module_sum(fun_add(R.add), fun_zero(R.zero), E, λe:B. fun_smul(φ(e), coord(e)), w)",
						Derive(func(p *Argument) {
							w := p.FixAs[B]("w")
							atW := p.Have(
								"at w the combination is the sum of the terms at w",
								"module_sum(fun_add(R.add), fun_zero(R.zero), E, λe:B. fun_smul(φ(e), coord(e)), w) = "+
									"module_sum(R.add, R.zero, E, λe:B. fun_smul(φ(e), coord(e), w))",
								By(
									finiteE,
									terms,
									function_module.ModuleSumApply.Read(selfModule).At(
										E, p.TermAs[Fun2[B, B, A]]("λe:B. fun_smul(φ(e), coord(e))"), w)))
							p.Cases(p.Term("w ∈ M.carrier"))
							p.When(
								"on M, φ(w) is φ of the expansion of w along E",
								func(q *Argument, wIn Fact) {
									expansion := q.Conjuncts(
										q.Have(
											"the coordinates of w along E are scalars on E, R.zero off E, and expand w",
											"(∀e:B. e ∈ E ⇒ module_basis_coordinates(R, M, E, w, e) ∈ R.carrier) ∧ "+
												"(∀e:B. e ∉ E ⇒ module_basis_coordinates(R, M, E, w, e) = R.zero) ∧ "+
												"module_sum(M.add, M.zero, E, λe:B. module_basis_coordinates(R, M, E, w, e) • e) = w",
											By(finiteE, basisE, BasisCoordinatesSpec.Read(moduleOn).At(E, q.MemberOf[on.M](w, wIn)))),
										"the coordinates are scalars on E",
										"they are R.zero off E",
										"they expand w")
									scalarsE, expands := expansion[0], expansion[2]
									termwise := q.Have(
										"the coordinate of w at e times φ(e) is φ(e) times coord(e)(w), the term at w",
										"∀e:B. e ∈ E ⇒ module_basis_coordinates(R, M, E, w, e) * φ(e) = fun_smul(φ(e), coord(e), w)",
										Derive(func(r *Argument) {
											e := r.FixAs[B]("e")
											eIn := r.Assume()
											coordinate := r.TermAs[A]("module_basis_coordinates(R, M, E, w, e)")
											value := r.TermAs[A]("φ(e)")
											r.Show(
												"the product of scalars commutes, and coord(e)(w) is the coordinate at e on M",
												CalcEq(
													Leg(
														r.TermAs[A]("φ(e) * module_basis_coordinates(R, M, E, w, e)"),
														"the product of scalars commutes",
														By(
															eIn,
															scalarsE.At(e),
															φIn,
															values.At(φ, e),
															comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(coordinate, value))),
													FinalLeg(
														"and coord(e) is the coordinate at e on M",
														By(wIn, coordDef, function_module.FunSmulDef.At(mul, value, r.TermAs[Fun[B, A]]("coord(e)"), w))),
												))
										}))
									q.Show(
										"φ(w) is φ of the expansion of w, the combination of the values "+
											"φ(e) by the coordinates, term by term the combination at w",
										CalcEq(
											Leg(
												q.TermAs[A]("φ(module_sum(M.add, M.zero, E, λe:B. module_basis_coordinates(R, M, E, w, e) • e))"),
												"w is its expansion along E",
												By(Normalized, expands)),
											Leg(
												q.TermAs[A]("module_sum(R.add, R.zero, E, λe:B. module_basis_coordinates(R, M, E, w, e) * φ(e))"),
												"φ carries the combination to the combination of the values φ(e)",
												By(
													finiteE,
													inM,
													scalarsE,
													module_homomorphism.HomCombination.Read(linearφ).At(
														E, q.TermAs[Fun[B, A]]("module_basis_coordinates(R, M, E, w)"), q.TermAs[Fun[B, B]]("λe:B. e")))),
											Leg(
												q.TermAs[A]("module_sum(R.add, R.zero, E, λe:B. fun_smul(φ(e), coord(e), w))"),
												"term by term",
												By(
													termwise,
													module.ModuleSumCongruence.At(q.TermAs[Op[A]]("R.add"), q.TermAs[A]("R.zero"), E,
														q.TermAs[Fun[B, A]]("λe:B. module_basis_coordinates(R, M, E, w, e) * φ(e)"),
														q.TermAs[Fun[B, A]]("λe:B. fun_smul(φ(e), coord(e), w)")))),
											FinalLeg(
												"which is the combination at w",
												By(atW)),
										))
								})
							p.Otherwise(
								"off M, φ(w) and every coord(e)(w) are R.zero",
								func(q *Argument, wOut Fact) {
									zeroTerms := q.Have(
										"each term is R.zero at w",
										"∀e:B. e ∈ E ⇒ fun_smul(φ(e), coord(e), w) = R.zero",
										Derive(func(r *Argument) {
											e := r.FixAs[B]("e")
											r.Assume()
											value := r.TermAs[A]("φ(e)")
											r.Show(
												"coord(e)(w) is R.zero off M, and φ(e) * R.zero = R.zero",
												By(
													wOut,
													φIn,
													values.At(φ, e),
													coordDef,
													function_module.FunSmulDef.At(mul, value, r.TermAs[Fun[B, A]]("coord(e)"), w),
													comm_ring.MulRightZeroOn.Read(ring).AsFact().At(value)))
										}))
									q.Show(
										"both sides are R.zero",
										By(
											atW,
											zeroOff.At(w),
											wOut,
											finiteE,
											zeroTerms,
											module.ModuleSumZero.Read(selfModule).At(
												E, q.TermAs[Fun[B, A]]("λe:B. fun_smul(φ(e), coord(e), w)"))))
								})
						}))
					expansion := b.Have(
						"so φ is the combination",
						"φ = module_sum(fun_add(R.add), fun_zero(R.zero), E, λe:B. fun_smul(φ(e), coord(e)))",
						Funext(),
						By(pointwise))
					b.Show(
						"so φ lies in the span",
						By(Normalized, expansion, combinationIn))
				}))
			reachesDual := a.Have(
				"so the dual lies in the span",
				"«dualDimMaps» ⊆ «dualDimSpan»",
				BySets(reached))
			spanning := a.Have(
				"the coordinate functionals span the dual",
				"«dualDimSpan» = «dualDimMaps»",
				By(withinDual, reachesDual, set_order.SubsetAntisym.At(spanned, maps)))
			dualBasis := a.Have(
				"so they are a basis of the dual",
				"module_basis(R, «dualDimSpace», image(coord, E))",
				By(
					independent,
					spanning,
					linear_independence.ModuleBasisDef.At(R, dual, functionals),
					hom_module.HomModuleDef.At(R, M, scalars)))

			// The count: both dimensions are card(E).
			counted := a.Conjuncts(
				a.Have(
					"the dual basis is finite, with as many members as E",
					"finite(image(coord, E)) ∧ card(image(coord, E)) = card(E)",
					By(size, cardinality.HasSizeDef.At(functionals, a.TermAs[Nat]("card(E)")))),
				"the dual basis is finite",
				"it has card(E) members")
			finiteFunctionals, sameCount := counted[0], counted[1]
			dualDimension := a.Have(
				"the coordinate functionals are a finite basis of the "+
					"dual, so it is finite-dimensional of dimension their number",
				"finite_dimensional(R, «dualDimSpace») ∧ module_dim(R, «dualDimSpace») = card(image(coord, E))",
				By(
					dualModule,
					scalarsField,
					dualBasis,
					finiteFunctionals,
					FiniteBasisDim.At(R, dual, inv, functionals)))
			moduleDimension := a.Have(
				"M's dimension is the size of E",
				"module_dim(R, M) = card(E)",
				By(scalarsField, basisE, finiteE, DimBasis.Read(moduleOn).At(inv, E)))
			a.Show(
				"the dual is finite-dimensional, and both dimensions are card(E)",
				By(Normalized, dualDimension, moduleDimension, sameCount))
		}),
})}
