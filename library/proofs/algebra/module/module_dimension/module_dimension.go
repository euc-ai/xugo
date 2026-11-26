// module_dimension.go — the chapter: the dimension of a module on a set
// over a field, the size of any of its bases, and what it measures —
// independent and spanning sets, submodules, kernels and images,
// quotients, isomorphic modules, the free module on a finite set, the
// chain of images of an endomorphism, and an ideal whose quotient is
// one-dimensional; modules built from others — a product, a dual, a
// direct sum — are counted from these.

package module_dimension

import (
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The definitions
// ---------------------------------------------------------------------------

// FiniteDimensionalDef — `finite_dimensional(R, M)`: M has a finite
// basis.
var FiniteDimensionalDef = finiteDimensionalDefThm{family.Define(registry.DefEntry{
	Name:  "FiniteDimensionalDef",
	Key:   "prop_e00f3c3c9c73bbe",
	Const: "finite_dimensional",
	Type:  "ring_ops(A) → module_ops(A, B) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). " +
			"    finite_dimensional(R, M) ⇔ ∃S:set(B). finite(S) ∧ module_basis(R, M, S)",
	},
})}

// ModuleDimDef — `module_dim(R, M)`: the size of a basis of M, chosen.
// Over a field a finite-dimensional M has one value the choice can make
// (DimBasis); where M has no finite basis the dimension is a number
// nothing is said about.
var ModuleDimDef = moduleDimDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleDimDef",
	Key:   "prop_7704ea171bfd7b9e",
	Const: "module_dim",
	Type:  "ring_ops(A) → module_ops(A, B) → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). " +
			"    module_dim(R, M) = εn:num. ∃S:set(B). module_basis(R, M, S) ∧ has_size(S, n)",
	},
})}

// ---------------------------------------------------------------------------
// Bases have one size
// ---------------------------------------------------------------------------

// BasisSizeUnique — over a field, beside a finite basis every basis is
// finite and of the same size: each lies in the span of the other, and
// the replacement theorem bounds each size by the other.
var BasisSizeUnique = basisSizeUniqueThm{family.Add(registry.ProofEntry{
	Name: "BasisSizeUnique",
	Key:  "prop_33399e9e59c93be8",
	Reading: "The field is load-bearing: over the zero ring every module " +
		"is {M.zero}, and both ∅ and {M.zero} are bases of it, of sizes 0 and 1.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀S T:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_basis(R, M, S)",
			"module_basis(R, M, T)",
			"finite(S)",
		},
		Conclusion: "finite(T) ∧ card(T) = card(S)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			S, T *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"S is a basis",
				"T is a basis",
				"S is finite")
			scalarsField, basisS, basisT, finiteS := given[0], given[1], given[2], given[3]
			onS := a.Conjuncts(
				a.Unfolded(basisS, linear_independence.ModuleBasisDef),
				"S is independent",
				"S spans M")
			onT := a.Conjuncts(
				a.Unfolded(basisT, linear_independence.ModuleBasisDef),
				"T is independent",
				"T spans M")
			independentS, spannedByS := onS[0], onS[1]
			independentT, spannedByT := onT[0], onT[1]

			sInM := a.Have(
				"an independent set lies in M, so S does",
				"S ⊆ M.carrier",
				By(linear_independence.IndependentInCarrier.Read(independentS)))
			tInM := a.Have(
				"and so does T",
				"T ⊆ M.carrier",
				By(linear_independence.IndependentInCarrier.Read(independentT)))
			tInSpanS := a.Have(
				"T lies in M, which is the span of S",
				"T ⊆ module_span(R, M, S)",
				By(Normalized, tInM, spannedByS))
			sInSpanT := a.Have(
				"S lies in M, which is the span of T",
				"S ⊆ module_span(R, M, T)",
				By(Normalized, sInM, spannedByT))

			bound := a.Conjuncts(
				a.Have(
					"the replacement theorem: T, independent inside the "+
						"span of the finite S, is finite and no larger than S",
					"finite(T) ∧ card(T) ≤ card(S)",
					By(
						scalarsField,
						finiteS,
						sInM,
						independentT,
						tInSpanS,
						linear_independence.Steinitz.Read(moduleOn).At(inv, S, T))),
				"T is finite",
				"T has at most card(S) members")
			finiteT, tAtMostS := bound[0], bound[1]
			sAtMostT := a.Have(
				"and read the other way, T now finite: S, independent inside the span of T, is no larger than T",
				"card(S) ≤ card(T)",
				By(
					scalarsField,
					finiteT,
					tInM,
					independentS,
					sInSpanT,
					linear_independence.Steinitz.Read(moduleOn).At(inv, T, S)))
			a.Show(
				"each size bounds the other, so the two are equal",
				By(
					finiteT,
					tAtMostS,
					sAtMostT,
					nat_order.LessEqAntisym.At(a.TermAs[Nat]("card(T)"), a.TermAs[Nat]("card(S)"))))
		}),
})}

// IndexedBasisSizeUnique — over a field, two indexed bases have the same
// length: the vectors of each form a finite basis with as many members as
// its length, and two finite bases have the same size (BasisSizeUnique).
var IndexedBasisSizeUnique = indexedBasisSizeUniqueThm{family.Add(registry.ProofEntry{
	Name: "IndexedBasisSizeUnique",
	Key:  "prop_be4cc95929f32db6",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀n k:num. ∀e h:(num → B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"indexed_module_basis(R, M, n, e)",
			"indexed_module_basis(R, M, k, h)",
		},
		Conclusion: "k = n",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			n, k *Expr[Nat],
			e *Vec[B, DimN],
			h *Vec[B, DimK],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"e is an indexed basis",
				"h is an indexed basis")
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			E := a.TermAs[Set[B]]("{e(i):B | i:num | i < n}")
			H := a.TermAs[Set[B]]("{h(i):B | i:num | i < k}")
			a.Show(
				"the vectors of e and of h are finite bases of n and of k members, so of one size",
				By(
					given[0],
					given[1],
					given[2],
					linear_independence.IndexedBasisImage.At(R, M, n, e),
					linear_independence.IndexedBasisImage.At(R, M, k, h),
					BasisSizeUnique.Read(moduleOn).At(inv, E, H)))
		}),
})}

// DimBasis — over a field, the dimension is the size of any finite basis:
// the dimension is the size of a basis, chosen; S shows that a size can
// be chosen, and the basis T of the chosen size has the size of S
// (BasisSizeUnique).
var DimBasis = dimBasisThm{family.Add(registry.ProofEntry{
	Name: "DimBasis",
	Key:  "prop_77c8a0c7bc93e4c2",
	Reading: "finite(S) is load-bearing: with an infinite " +
		"basis both card(S) and the chosen number are unconstrained.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀S:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_basis(R, M, S)",
			"finite(S)",
		},
		Conclusion: "module_dim(R, M) = card(S)",
		Abbrev: Abbrev{
			{Name: "sized", Text: "∃n:num. ∃T:set(B). module_basis(R, M, T) ∧ has_size(T, n)"},
		},
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			S *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"S is a basis",
				"S is finite")
			scalarsField, basisS, finiteS := given[0], given[1], given[2]

			// The choice the dimension makes: a size n with a basis of n members.
			const sized = "∃n:num. ∃T:set(B). module_basis(R, M, T) ∧ has_size(T, n)"
			possible := a.Have(
				"S is a basis with card(S) members, so a size can be chosen",
				"«sized»",
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Nat]("card(S)"))
					b.Take(S)
					b.Show(
						"S, being finite, has card(S) members",
						By(basisS, finiteS, cardinality.HasSizeDef))
				}))
			dim, chosen := a.ObtainChosen(
				"so the chosen size is that of a basis T",
				"«sized»",
				possible)
			T, onT := a.UnpackAs[Set[B]](chosen)
			parts := a.Conjuncts(
				onT,
				"T is a basis",
				"T has the chosen size")
			basisT, sizeT := parts[0], parts[1]

			sameSize := a.Have(
				"beside the finite basis S, the basis T is finite of the same size",
				"finite(T) ∧ card(T) = card(S)",
				By(scalarsField, basisS, basisT, finiteS, BasisSizeUnique.Read(moduleOn).At(inv, S, T)))
			a.Show(
				"so the dimension, the chosen size, is the size of T, which is the size of S",
				By(
					ModuleDimDef.At(a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")),
					sizeT,
					cardinality.HasSizeDef.At(T, ext.As[Nat](dim)),
					sameSize))
		}),
})}

// FiniteBasisDim — over a field, a module with a finite basis is
// finite-dimensional, of dimension the size of the basis: the basis
// witnesses the definition, and the dimension is its size (DimBasis).
var FiniteBasisDim = finiteBasisDimThm{family.Add(registry.ProofEntry{
	Name: "FiniteBasisDim",
	Key:  "prop_257bf1d06894528d",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀S:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_basis(R, M, S)",
			"finite(S)",
		},
		Conclusion: "finite_dimensional(R, M) ∧ module_dim(R, M) = card(S)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			S *Expr[Set[B]],
			hypotheses Fact,
		) {
			finiteM := a.Have(
				"S is a finite basis of M, so M is finite-dimensional",
				"finite_dimensional(R, M)",
				Simp(Fwd(FiniteDimensionalDef)),
				Witness(S),
				By(hypotheses))
			a.Show(
				"and its dimension is the size of the finite basis S",
				By(finiteM, hypotheses, DimBasis.Read(moduleOn).At(inv, S)))
		}),
})}

// FiniteDimensionalSpanning — over a field, M is finite-dimensional
// exactly when a finite subset spans it: a finite basis is such a subset,
// and a finite spanning subset holds a basis, finite as a part of it.
var FiniteDimensionalSpanning = finiteDimensionalSpanningThm{family.Add(registry.ProofEntry{
	Name: "FiniteDimensionalSpanning",
	Key:  "prop_46491da762f54bcc",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
		},
		Conclusion: "finite_dimensional(R, M) ⇔ " +
			"∃S:set(B). finite(S) ∧ S ⊆ M.carrier ∧ module_span(R, M, S) = M.carrier",
	},
		func(a *Argument, moduleOn module.ModuleFact[on.R, on.M], inv *Arrow[A, A], scalarsField Fact) {
			a.Iff()
			a.Forward(
				"a finite basis is a finite subset of M that spans it",
				func(b *Argument, finiteM Fact) {
					S, finiteBasis := b.ObtainAs[Set[B]](
						"M has a finite basis S",
						"∃S:set(B). finite(S) ∧ module_basis(R, M, S)",
						By(finiteM, FiniteDimensionalDef))
					given := b.Conjuncts(
						finiteBasis,
						"S is finite",
						"S is a basis of M")
					finiteS, basisS := given[0], given[1]
					basis := b.Conjuncts(
						b.Unfolded(basisS, linear_independence.ModuleBasisDef),
						"S is independent",
						"S spans M")
					independent, spansM := basis[0], basis[1]
					b.Take(S)
					b.Show(
						"S is finite, lies in M and spans it",
						By(finiteS, linear_independence.IndependentInCarrier.Read(independent), spansM))
				})
			a.Backward(
				"a basis inside a finite spanning set is finite",
				func(b *Argument, spanning Fact) {
					S, spanningS := b.UnpackAs[Set[B]](spanning, "S")
					given := b.Conjuncts(
						spanningS,
						"S is finite",
						"S lies in M",
						"S spans M")
					finiteS, spansM := given[0], given[2]
					E, inside := b.ObtainAs[Set[B]](
						"over a field the spanning set S holds a basis E of M",
						"∃E:set(B). E ⊆ S ∧ module_basis(R, M, E)",
						By(scalarsField, spansM, linear_independence.BasisWithinSpanning.Read(moduleOn).At(inv, S)))
					parts := b.Conjuncts(
						inside,
						"E lies in S",
						"E is a basis of M")
					eInS, basisE := parts[0], parts[1]
					finiteE := b.Have(
						"E is finite, a subset of the finite S",
						"finite(E)",
						By(eInS, finiteS, finite_set.FiniteSubset.At(E, S)))
					b.Show(
						"so E is a finite basis of M",
						Simp(Fwd(FiniteDimensionalDef)),
						Witness(E),
						By(finiteE, basisE))
				})
		}),
})}

// FiniteDimensionalBasis — over a field, every basis of a
// finite-dimensional M is finite, of size its dimension. M has a finite
// basis E by definition; beside it every basis is finite of E's size
// (BasisSizeUnique), and E's size is the dimension (DimBasis).
var FiniteDimensionalBasis = finiteDimensionalBasisThm{family.Add(registry.ProofEntry{
	Name: "FiniteDimensionalBasis",
	Key:  "prop_fbf561285e209f9b",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀S:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"finite_dimensional(R, M)",
			"module_basis(R, M, S)",
		},
		Conclusion: "finite(S) ∧ card(S) = module_dim(R, M)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			S *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"M is finite-dimensional",
				"S is a basis")
			scalarsField, finiteM, basisS := given[0], given[1], given[2]
			E, finiteBasisE := a.UnpackAs[Set[B]](a.Unfolded(finiteM, FiniteDimensionalDef), "E")
			sameSize := a.Have(
				"beside the finite basis E, the basis S is finite of E's size",
				"finite(S) ∧ card(S) = card(E)",
				By(scalarsField, finiteBasisE, basisS, BasisSizeUnique.Read(moduleOn).At(inv, E, S)))
			dimension := a.Have(
				"and E's size is the dimension",
				"module_dim(R, M) = card(E)",
				By(scalarsField, finiteBasisE, DimBasis.Read(moduleOn).At(inv, E)))
			a.Show(
				"so S is finite, of the dimension's size",
				By(Normalized, sameSize, dimension))
		}),
})}

// ---------------------------------------------------------------------------
// What the dimension bounds
// ---------------------------------------------------------------------------

// IndependentBound — over a field, an independent subset of a
// finite-dimensional M is finite and no larger than the dimension: a
// finite basis S spans M, which holds I, so the replacement theorem
// bounds I by the size of S, and that size is the dimension.
var IndependentBound = independentBoundThm{family.Add(registry.ProofEntry{
	Name: "IndependentBound",
	Key:  "prop_3c1c8d01d7feeb57",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀I:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"finite_dimensional(R, M)",
			"module_independent(R, M, I)",
		},
		Conclusion: "finite(I) ∧ card(I) ≤ module_dim(R, M)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			I *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"M is finite-dimensional",
				"I is independent")
			scalarsField, finiteM, independent := given[0], given[1], given[2]

			S, finiteBasis := a.UnpackAs[Set[B]](a.Unfolded(finiteM, FiniteDimensionalDef), "S")
			onS := a.Conjuncts(
				finiteBasis,
				"S is finite",
				"S is a basis of M")
			finiteS, basis := onS[0], onS[1]
			ofBasis := a.Conjuncts(
				a.Unfolded(basis, linear_independence.ModuleBasisDef),
				"S is independent",
				"S spans M")
			independentS, spans := ofBasis[0], ofBasis[1]
			iInSpan := a.Have(
				"I, independent, lies in M, which S spans",
				"I ⊆ module_span(R, M, S)",
				By(Normalized, spans, linear_independence.IndependentInCarrier.Read(independent)))

			bound := a.Have(
				"the replacement theorem: I is finite and no larger than S",
				"finite(I) ∧ card(I) ≤ card(S)",
				By(
					scalarsField,
					finiteS,
					linear_independence.IndependentInCarrier.Read(independentS),
					independent,
					iInSpan,
					linear_independence.Steinitz.Read(moduleOn).At(inv, S, I)))
			dimension := a.Have(
				"the dimension is the size of the finite basis S",
				"module_dim(R, M) = card(S)",
				By(scalarsField, basis, finiteS, DimBasis.Read(moduleOn).At(inv, S)))
			a.Show(
				"so I is finite with at most module_dim(R, M) members",
				By(Normalized, bound, dimension))
		}),
})}

// SpanningBound — over a field, a finite set spanning M is at least as
// large as the dimension: S holds a basis of M (BasisWithinSpanning), which
// is finite, a subset of the finite S, and has the dimension as its size.
var SpanningBound = spanningBoundThm{family.Add(registry.ProofEntry{
	Name: "SpanningBound",
	Key:  "prop_3ea8a606aa322132",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀S:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"finite(S)",
			"module_span(R, M, S) = M.carrier",
		},
		Conclusion: "module_dim(R, M) ≤ card(S)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			S *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"S is finite",
				"S spans M")
			scalarsField, finiteS, spansM := given[0], given[1], given[2]
			E, inside := a.ObtainAs[Set[B]](
				"over a field the spanning set S holds a basis E of M",
				"∃E:set(B). E ⊆ S ∧ module_basis(R, M, E)",
				By(scalarsField, spansM, linear_independence.BasisWithinSpanning.Read(moduleOn).At(inv, S)))
			parts := a.Conjuncts(
				inside,
				"E lies in S",
				"E is a basis of M")
			eInS, basisE := parts[0], parts[1]
			finiteE := a.Have(
				"E is finite, a subset of the finite S",
				"finite(E)",
				By(eInS, finiteS, finite_set.FiniteSubset.At(E, S)))
			dimension := a.Have(
				"the dimension is the size of the finite basis E",
				"module_dim(R, M) = card(E)",
				By(scalarsField, basisE, finiteE, DimBasis.Read(moduleOn).At(inv, E)))
			a.Show(
				"and E, a subset of the finite S, has at most card(S) members",
				By(Normalized, dimension, finiteS, eInS, cardinality.CardSubset.At(E, S)))
		}),
})}

// IndependentFullBasis — over a field, an independent subset of a
// finite-dimensional M with as many members as the dimension is a basis:
// I extends to a basis, which is finite of the dimension's size, so I
// lies inside a finite set of its own size and is that set.
var IndependentFullBasis = independentFullBasisThm{family.Add(registry.ProofEntry{
	Name: "IndependentFullBasis",
	Key:  "prop_db5c3d64b3dc3c70",
	Reading: "finite_dimensional(R, M) is load-bearing: without it module_dim(R, M) is an " +
		"arbitrary chosen number n, and any independent set of n members would be declared a basis.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀I:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"finite_dimensional(R, M)",
			"module_independent(R, M, I)",
			"has_size(I, module_dim(R, M))",
		},
		Conclusion: "module_basis(R, M, I)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			I *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"M is finite-dimensional",
				"I is independent",
				"I has as many members as the dimension")
			scalarsField, finiteM, independent, fullSize := given[0], given[1], given[2], given[3]
			E, extension := a.ObtainAs[Set[B]](
				"I extends to a basis E of M",
				"∃E:set(B). I ⊆ E ∧ module_basis(R, M, E)",
				By(scalarsField, independent, linear_independence.BasisExtends.Read(moduleOn).At(inv, I)))
			extended := a.Conjuncts(
				extension,
				"I lies in E",
				"E is a basis of M")
			inE, basis := extended[0], extended[1]
			sizeE := a.Have(
				"a basis of the finite-dimensional M is finite, of the dimension's size",
				"finite(E) ∧ card(E) = module_dim(R, M)",
				By(scalarsField, finiteM, basis, FiniteDimensionalBasis.Read(moduleOn).At(inv, E)))
			sizeI := a.Have(
				"I is finite with the dimension's number of members",
				"finite(I) ∧ card(I) = module_dim(R, M)",
				By(fullSize, cardinality.HasSizeDef.At(I, a.TermAs[Nat]("module_dim(R, M)"))))
			sameSize := a.Have(
				"I and E have the same size",
				"card(I) = card(E)",
				By(Normalized, sizeE, sizeI))
			same := a.Have(
				"I lies in the finite set E and has its size, so I is E",
				"I = E",
				By(sizeE, inE, sameSize, cardinality.CardSubsetEq.At(I, E)))
			a.Show(
				"so I is the basis E",
				same.Rw(),
				By(basis))
		}),
})}

// SpanningFullBasis — over a field, a set spanning M with as many members
// as the dimension is a basis: S holds a basis E, finite as a part of the
// finite S, whose size is the dimension and so the size of S; a part of a
// finite set with the set's size is the whole set, so E is S.
var SpanningFullBasis = spanningFullBasisThm{family.Add(registry.ProofEntry{
	Name:    "SpanningFullBasis",
	Key:     "prop_25e66a184d12b468",
	Reading: "S ⊆ M.carrier need not be assumed: S lies in its span, which is M.carrier.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀S:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_span(R, M, S) = M.carrier",
			"has_size(S, module_dim(R, M))",
		},
		Conclusion: "module_basis(R, M, S)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			S *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"S spans M",
				"S has as many members as the dimension")
			scalarsField, spansM, fullSize := given[0], given[1], given[2]
			E, inside := a.ObtainAs[Set[B]](
				"over a field the spanning set S holds a basis E of M",
				"∃E:set(B). E ⊆ S ∧ module_basis(R, M, E)",
				By(scalarsField, spansM, linear_independence.BasisWithinSpanning.Read(moduleOn).At(inv, S)))
			parts := a.Conjuncts(
				inside,
				"E lies in S",
				"E is a basis of M")
			eInS, basisE := parts[0], parts[1]
			sizeS := a.Have(
				"S is finite with the dimension's number of members",
				"finite(S) ∧ card(S) = module_dim(R, M)",
				By(fullSize, cardinality.HasSizeDef.At(S, a.TermAs[Nat]("module_dim(R, M)"))))
			finiteE := a.Have(
				"E is finite, a subset of the finite S",
				"finite(E)",
				By(eInS, sizeS, finite_set.FiniteSubset.At(E, S)))
			dimension := a.Have(
				"the dimension is the size of the finite basis E",
				"module_dim(R, M) = card(E)",
				By(scalarsField, basisE, finiteE, DimBasis.Read(moduleOn).At(inv, E)))
			sameSize := a.Have(
				"E and S have the same size",
				"card(E) = card(S)",
				By(Normalized, sizeS, dimension))
			same := a.Have(
				"E lies in the finite set S and has its size, so E is S",
				"E = S",
				By(sizeS, eInS, sameSize, cardinality.CardSubsetEq.At(E, S)))
			a.Show(
				"so S is the basis E",
				same.RwRev(),
				By(basisE))
		}),
})}

// DimZero — over a field, a finite-dimensional M has dimension zero
// exactly when it is the zero module. Both directions go through the span
// of ∅, which is {M.zero}: ⇒, a finite basis of size zero is ∅, so M is
// that span; ⇐, ∅ is then a basis of M, of size zero.
var DimZero = dimZeroThm{family.Add(registry.ProofEntry{
	Name: "DimZero",
	Key:  "prop_55fa09a6bcb70fcc",
	Reading: "finite_dimensional(R, M) is load-bearing for ⇒: a module with no " +
		"finite basis has a chosen dimension, which may be 0 although M is not {M.zero}.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"finite_dimensional(R, M)",
		},
		Conclusion: "module_dim(R, M) = 0 ⇔ M.carrier = {M.zero}",
	},
		func(a *Argument, moduleOn module.ModuleFact[on.R, on.M], inv *Arrow[A, A], hypotheses Fact) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"M has a finite basis")
			scalarsField, finiteM := given[0], given[1]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			empty := a.TermAs[Set[B]]("∅")
			emptySpan := a.TermAs[Set[B]]("module_span(R, M, ∅)")
			spanEmpty := submodule.SpanEmpty.Read(moduleOn)

			a.Iff()
			a.Forward(
				"a finite basis of size zero is ∅, so M is the span of ∅",
				func(b *Argument, dimZero Fact) {
					S, hasBasis := b.UnpackAs[Set[B]](b.Unfolded(finiteM, FiniteDimensionalDef))
					onS := b.Conjuncts(
						hasBasis,
						"S is finite",
						"S is a basis of M")
					finiteS, basis := onS[0], onS[1]
					spans := b.Conjuncts(
						b.Unfolded(basis, linear_independence.ModuleBasisDef),
						"S is independent",
						"S spans M")[1]
					size := b.Have(
						"the dimension is the size of the finite basis S",
						"module_dim(R, M) = card(S)",
						By(scalarsField, basis, finiteS, DimBasis.Read(moduleOn).At(inv, S)))
					isEmpty := b.Have(
						"a finite set of size zero is ∅",
						"S = ∅",
						By(Normalized, dimZero, size, finiteS, cardinality.CardEqZero.At(S)))
					b.Show(
						"M is the span of S, which is ∅, whose span is {M.zero}",
						CalcEq(
							Leg(
								b.TermAs[Set[B]]("module_span(R, M, S)"),
								"S spans M",
								By(Normalized, spans)),
							Leg(
								emptySpan,
								"S is ∅",
								isEmpty.Rw(),
								Basic()),
							FinalLeg(
								"the span of ∅ is {M.zero}",
								By(spanEmpty)),
						))
				})
			a.Backward(
				"∅ is a basis of the zero module, so the dimension is card(∅) = 0",
				func(b *Argument, zeroModule Fact) {
					basis := b.Have(
						"∅ is independent, and its span {M.zero} is M",
						"module_basis(R, M, ∅)",
						By(
							Normalized,
							linear_independence.IndependentEmpty.At(R, M),
							spanEmpty,
							zeroModule,
							linear_independence.ModuleBasisDef.At(R, M, empty)))
					// ∅⟨A:B⟩ is the empty set of vectors: the text alone leaves the
					// type of its members open, and the annotation pins it at M's type B.
					b.Show(
						"the dimension is the size of the basis ∅, which has no members",
						CalcEq(
							Leg(
								b.TermAs[Nat]("card(∅⟨A:B⟩)"),
								"the dimension is the size of the finite basis ∅",
								By(scalarsField, basis, finite_set.FiniteRules, DimBasis.Read(moduleOn).At(inv, empty))),
							FinalLeg(
								"and ∅ has no members",
								By(cardinality.CardClauses)),
						))
				})
		}),
})}

// LineDim — over a field, a module spanned by one nonzero vector e is
// finite-dimensional of dimension one: the span of ∅ is zero alone, so the
// nonzero e is independent, every vector is a multiple of e, so {e} spans,
// and the one-element basis {e} gives dimension one.
var LineDim = lineDimThm{family.Add(registry.ProofEntry{
	Name: "LineDim",
	Key:  "prop_c678db5124151564",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀inv:(A → A). ∀e:B.",
		Hypotheses: []string{
			"module_on(R, M)",
			"ring_subfield(R, inv, R.carrier)",
			"e ∈ M.carrier",
			"e ≠ M.zero",
			"∀x:B. x ∈ M.carrier ⇒ ∃c:A. c ∈ R.carrier ∧ x = c • e",
		},
		Conclusion: "finite_dimensional(R, M) ∧ module_dim(R, M) = 1",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			inv *Arrow[A, A],
			e *Expr[B],
			given Fact,
		) {
			empty, singleton := a.TermAs[Set[B]]("∅"), a.TermAs[Set[B]]("{e}")
			lineSpan := a.TermAs[Set[B]]("module_span(R, M, {e})")
			independent := a.Have(
				"the span of ∅ being {M.zero} alone, a nonzero vector extends the empty independent set",
				"module_independent(R, M, {e})",
				BySets(
					submodule.SpanEmpty.At(R, M),
					given,
					linear_independence.IndependentInsertIff.At(R, M, inv, empty, e),
					linear_independence.IndependentEmpty.At(R, M)))
			spanning := a.Have(
				"all scalar multiples of e lie in its span, so it spans M",
				"module_span(R, M, {e}) = M.carrier",
				BySets(
					given,
					submodule.SpanSubmodule.At(R, M, singleton),
					submodule.SubmoduleSubset.At(R, M, lineSpan),
					submodule.SubsetSpan.At(R, M, singleton),
					At(submodule.SubmoduleSmul, R, M, lineSpan)))
			basis := a.Have(
				"the singleton is a basis",
				"module_basis(R, M, {e})",
				By(spanning, independent, linear_independence.ModuleBasisDef.At(R, M, singleton)))
			a.Show(
				"its one-element basis gives finite dimension one",
				By(
					Normalized,
					given,
					basis,
					FiniteBasisDim.At(R, M, inv, singleton),
					finite_set.FiniteSing.At(e),
					cardinality.CardSing.At(e)))
		}),
})}

// DimTwo — over a field, a finite-dimensional M has dimension two exactly
// when it holds two vectors with only the trivial relation between them and
// any three of its vectors satisfy a nontrivial one. A vector lies in the
// span of u and v exactly when it is a • u + b • v (SpanInsert twice, from
// the span {M.zero} of ∅). ⇒: a basis of two vectors gives the two; three
// vectors with only the trivial relation would be three independent vectors,
// the first outside the span of the other two (IndependentInsertIff), more
// than the dimension allows (IndependentBound). ⇐: the two are independent
// (IndependentPair) and span M, since in a relation a • u + b • v + c • w =
// M.zero the coefficient c is not zero and w is solved for; so they are a
// basis of two vectors (DimBasis).
var DimTwo = dimTwoThm{family.Add(registry.ProofEntry{
	Name: "DimTwo",
	Key:  "prop_74a584c51464bdc",
	Reading: "finite_dimensional(R, M) is load-bearing for ⇒: a module with no finite " +
		"basis has a chosen dimension, which may be 2 although no two of its vectors span " +
		"it. In ⇐ the two vectors are a basis, so the hypothesis is not used there.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"finite_dimensional(R, M)",
		},
		Conclusion: "module_dim(R, M) = 2 ⇔ " +
			"(∃u v:B. " +
			"    u ∈ M.carrier ∧ " +
			"    v ∈ M.carrier ∧ " +
			"    (∀a b:A. " +
			"        a ∈ R.carrier ∧ b ∈ R.carrier ∧ a • u + b • v = M.zero ⇒ a = R.zero ∧ b = R.zero)) ∧ " +
			"(∀u v w:B. " +
			"    u ∈ M.carrier ∧ v ∈ M.carrier ∧ w ∈ M.carrier ⇒ " +
			"    ∃a b c:A. " +
			"        a ∈ R.carrier ∧ " +
			"        b ∈ R.carrier ∧ " +
			"        c ∈ R.carrier ∧ " +
			"        ¬(a = R.zero ∧ b = R.zero ∧ c = R.zero) ∧ " +
			"        a • u + b • v + c • w = M.zero)",
	},
		func(arg *Argument, moduleOn module.ModuleFact[on.R, on.M], inv *Arrow[A, A], hypotheses Fact) {
			given := arg.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"M is finite-dimensional")
			scalarsField, finiteM := given[0], given[1]
			fieldR := arg.Unfolded(scalarsField, field.RingSubfieldDef)
			ring := module.RingOn.Read(moduleOn)
			R, M := arg.TermAs[RingOps[A]]("R"), arg.TermAs[ModuleOps[A, B]]("M")
			two := arg.TermAs[Nat]("2")
			oneNotZero := arg.Have(
				"one is not zero, the scalars forming a field",
				"R.one ≠ R.zero",
				By(field.OneNotZeroOn.Read(fieldR)))
			apart := arg.Have(
				"two vectors with only the trivial relation are distinct, as 1 • u + (-1) • u = M.zero",
				Statement{
					Binders: "∀u v:B.",
					Hypotheses: []string{
						"u ∈ M.carrier",
						"v ∈ M.carrier",
						"∀a b:A. a ∈ R.carrier ∧ b ∈ R.carrier ∧ a • u + b • v = M.zero ⇒ a = R.zero ∧ b = R.zero",
					},
					Conclusion: "u ≠ v",
				},
				Derive(func(b *Argument) {
					b.FixAs[B]("u")
					b.FixAs[B]("v")
					pair := b.Conjuncts(
						b.Assume(),
						"u lies in M",
						"so does v",
						"u and v have only the trivial relation")
					cancel := b.Have(
						"u less u is zero",
						"R.one • u + -R.one • u = M.zero",
						ByChase(Depth(0), moduleOn, pair[0]))
					b.Show(
						"so u = v would make one zero",
						By(
							oneNotZero,
							cancel,
							pair[2].At(b.TermAs[A]("R.one"), b.TermAs[A]("-R.one")),
							comm_ring.OneIn.Read(ring),
							comm_ring.NegIn.Read(ring)))
				}))
			pairSpan := arg.Have(
				"a vector lies in the span of two vectors u and v of M exactly when it is a • u + b • v",
				Statement{
					Binders: "∀u v x:B.",
					Hypotheses: []string{
						"u ∈ M.carrier",
						"v ∈ M.carrier",
					},
					Conclusion: "x ∈ module_span(R, M, {u, v}) ⇔ " +
						"∃a b:A. a ∈ R.carrier ∧ b ∈ R.carrier ∧ x = a • u + b • v",
				},
				Derive(func(b *Argument) {
					b.FixAs[B]("u")
					b.FixAs[B]("v")
					b.FixAs[B]("x")
					pair := b.Conjuncts(
						b.Assume(),
						"u lies in M",
						"so does v")
					inner := b.Have(
						"{v} and ∅ lie in M",
						"{v} ⊆ M.carrier ∧ ∅ ⊆ M.carrier",
						BySets(pair[1]))
					nested := b.Have(
						"the span of u added to v added to ∅, by SpanInsert twice from the span {M.zero} of ∅",
						"x ∈ module_span(R, M, {u, v}) ⇔ "+
							"∃a b:A. a ∈ R.carrier ∧ b ∈ R.carrier ∧ x = a • u + (b • v + M.zero)",
						Simp(Fwd(submodule.SpanInsert), Fwd(submodule.SpanEmpty), Fwd(inner)),
						BySets())
					b.Show(
						"and b • v + M.zero is b • v",
						By(
							nested,
							pair[1],
							group.RightIdentityOn.Read(module.AddGroupOn.Read(moduleOn)),
							module.SmulIn.Read(moduleOn)))
				}))

			arg.Iff()
			arg.Forward(
				"a basis of two vectors gives the two, and three vectors with "+
					"only the trivial relation would be three independent vectors",
				func(fw *Argument, dimTwo Fact) {
					S, hasBasis := fw.UnpackAs[Set[B]](fw.Unfolded(finiteM, FiniteDimensionalDef), "S")
					onS := fw.Conjuncts(
						hasBasis,
						"S is finite",
						"S is a basis of M")
					finiteS, basis := onS[0], onS[1]
					sized := fw.Have(
						"the basis S has the dimension's size, two",
						"has_size(S, 2)",
						By(
							Normalized,
							scalarsField,
							dimTwo,
							finiteS,
							basis,
							DimBasis.Read(moduleOn).At(inv, S),
							cardinality.HasSizeDef.At(S, two)))
					e, t, pointAdded := fw.Obtain2As[B, Set[B]](
						"so S is a point e added to a set t of one point",
						"∃e:B. ∃t:set(B). has_size(t, 1) ∧ e ∉ t ∧ S = insert(e, t)",
						By(sized, nat_arith.Two, cardinality.HasSizeClauses.At(S, fw.TermAs[Nat]("1"))))
					added := fw.Conjuncts(
						pointAdded,
						"t has one point",
						"e lies outside t",
						"S is e added to t")
					f, singleton := fw.ObtainAs[B](
						"t is a singleton {f}",
						"∃f:B. t = {f}",
						By(
							added[0],
							nat_arith.OneIsSucZero,
							cardinality.HasSizeClauses.At(t, fw.TermAs[Nat]("0")),
							cardinality.HasSizeZero))
					pair := fw.TermAs[Set[B]]("{e, f}")
					distinct := fw.Have(
						"e lies outside {f}, so e is not f",
						"e ≠ f",
						BySets(added[1], singleton))
					pairBasis := fw.Have(
						"so the basis S is the pair {e, f}",
						"module_basis(R, M, {e, f})",
						By(Normalized, basis, added[2], singleton))
					onPair := fw.Conjuncts(
						fw.Have(
							"e and f lie in M and are independent",
							"e ∈ M.carrier ∧ f ∈ M.carrier ∧ module_independent(R, M, {e, f})",
							BySets(
								pairBasis,
								linear_independence.BasisInCarrier.At(R, M, pair),
								linear_independence.ModuleBasisDef.At(R, M, pair))),
						"e lies in M",
						"so does f",
						"e and f are independent")
					em, fm := fw.MemberOf[on.M](e, onPair[0]), fw.MemberOf[on.M](f, onPair[1])
					pairClause := fw.Have(
						"e and f have only the trivial relation",
						"∃u v:B. "+
							"    u ∈ M.carrier ∧ "+
							"    v ∈ M.carrier ∧ "+
							"    (∀a b:A. a ∈ R.carrier ∧ b ∈ R.carrier ∧ a • u + b • v = M.zero ⇒ a = R.zero ∧ b = R.zero)",
						Derive(func(b *Argument) {
							b.Take(e)
							b.Take(f)
							b.Show(
								"independent and distinct, they have only the trivial relation",
								By(distinct, onPair[2], linear_independence.IndependentPair.Read(moduleOn).At(em, fm)))
						}))
					tripleClause := fw.Have(
						"three vectors with only the trivial relation would be three independent vectors in dimension two",
						Statement{
							Binders: "∀u v w:B.",
							Hypotheses: []string{
								"u ∈ M.carrier",
								"v ∈ M.carrier",
								"w ∈ M.carrier",
							},
							Conclusion: "∃a b c:A. " +
								"    a ∈ R.carrier ∧ " +
								"    b ∈ R.carrier ∧ " +
								"    c ∈ R.carrier ∧ " +
								"    ¬(a = R.zero ∧ b = R.zero ∧ c = R.zero) ∧ " +
								"    a • u + b • v + c • w = M.zero",
						},
						Derive(func(b *Argument) {
							u := b.FixAs[B]("u")
							v := b.FixAs[B]("v")
							w := b.FixAs[B]("w")
							inM := b.Conjuncts(
								b.Assume(),
								"u lies in M",
								"so does v",
								"and w")
							um, vm, wm := b.MemberOf[on.M](u, inM[0]), b.MemberOf[on.M](v, inM[1]), b.MemberOf[on.M](w, inM[2])
							none := b.SupposeNot()
							trivial := b.Have(
								"then u, v and w have only the trivial relation",
								Statement{
									Binders: "∀a b c:A.",
									Hypotheses: []string{
										"a ∈ R.carrier",
										"b ∈ R.carrier",
										"c ∈ R.carrier",
										"a • u + b • v + c • w = M.zero",
									},
									Conclusion: "a = R.zero ∧ b = R.zero ∧ c = R.zero",
								},
								By(none))
							trivialVW := b.Have(
								"and so do v and w, a • v + b • w being 0 • u + a • v + b • w",
								"∀a b:A. a ∈ R.carrier ∧ b ∈ R.carrier ∧ a • v + b • w = M.zero ⇒ a = R.zero ∧ b = R.zero",
								Derive(func(c *Argument) {
									s := c.FixAs[A]("a")
									t := c.FixAs[A]("b")
									relation := c.Conjuncts(
										c.Assume(),
										"a is a scalar",
										"so is b",
										"a • v + b • w = M.zero")
									padded := c.Have(
										"0 • u + a • v + b • w = M.zero",
										"R.zero • u + a • v + b • w = M.zero",
										ByChase(Depth(0), moduleOn, relation[0], relation[1], relation[2], um, vm, wm))
									c.Show(
										"u, v and w have only the trivial relation",
										By(
											padded,
											relation[0],
											relation[1],
											comm_ring.ZeroIn.Read(ring),
											trivial.At(c.TermAs[A]("R.zero"), s, t)))
								}))
							vwApart := b.Have(
								"v and w are distinct",
								"v ≠ w",
								By(apart.At(v, w), inM[1], inM[2], trivialVW))
							independentVW := b.Have(
								"so v and w are independent",
								"module_independent(R, M, {v, w})",
								By(vwApart, trivialVW, linear_independence.IndependentPair.Read(moduleOn).At(vm, wm)))
							outside := b.Have(
								"u is no combination a • v + b • w: that would give the relation -1 • u + a • v + b • w = M.zero",
								"u ∉ module_span(R, M, {v, w})",
								Derive(func(c *Argument) {
									inSpan := c.SupposeNot()
									s, t, combination := c.Obtain2As[A, A](
										"u is a combination of v and w",
										"∃a b:A. a ∈ R.carrier ∧ b ∈ R.carrier ∧ u = a • v + b • w",
										By(inSpan, inM[1], inM[2], pairSpan.At(v, w, u)))
									parts := c.Conjuncts(
										combination,
										"a is a scalar",
										"so is b",
										"u = a • v + b • w")
									relation := c.Have(
										"-1 • u + a • v + b • w = M.zero",
										"-R.one • u + a • v + b • w = M.zero",
										ByChase(Depth(0), moduleOn, parts[0], parts[1], parts[2], um, vm, wm))
									minusOne := c.Have(
										"so -1 is zero",
										"-R.one = R.zero",
										By(
											relation,
											parts[0],
											parts[1],
											comm_ring.NegIn.Read(ring),
											comm_ring.OneIn.Read(ring),
											trivial.At(c.TermAs[A]("-R.one"), s, t)))
									c.Show(
										"and so is 1",
										ByArith(ring, oneNotZero, minusOne))
								}))
							around := b.Have(
								"v and w lie in M, and u, outside their span, is neither",
								"{v, w} ⊆ M.carrier ∧ u ∉ {v, w}",
								BySets(outside, inM[1], inM[2], submodule.SubsetSpan.At(R, M, b.TermAs[Set[B]]("{v, w}"))))
							independent := b.Have(
								"so u, v and w are independent",
								"module_independent(R, M, {u, v, w})",
								By(
									scalarsField,
									outside,
									independentVW,
									around,
									linear_independence.IndependentInsertIff.Read(moduleOn).At(inv, b.TermAs[Set[B]]("{v, w}"), um)))
							pairSize := b.Have(
								"the distinct v and w are two",
								"finite({v, w}) ∧ card({v, w}) = 2",
								By(
									vwApart,
									cardinality.HasSizePair.At(v, w),
									cardinality.HasSizeDef.At(b.TermAs[Set[B]]("{v, w}"), two)))
							count := b.Have(
								"and with u outside them, u, v and w are three",
								"card({u, v, w}) = 3",
								ByArith(pairSize, around, cardinality.InsertCountsOneMore.At(b.TermAs[Set[B]]("{v, w}"), u)))
							b.Show(
								"more independent vectors than the dimension two",
								ByArith(
									scalarsField,
									finiteM,
									dimTwo,
									independent,
									count,
									IndependentBound.Read(moduleOn).At(inv, b.TermAs[Set[B]]("{u, v, w}"))))
						}))
					fw.Show(
						"both clauses hold",
						By(pairClause, tripleClause))
				})
			arg.Backward(
				"two vectors with only the trivial relation, on which every third vector depends, are a basis of M",
				func(bw *Argument, clauses Fact) {
					both := bw.Conjuncts(
						clauses,
						"two vectors with only the trivial relation",
						"any three vectors satisfy a nontrivial relation")
					u, v, chosen := bw.Unpack2As[B, B](both[0], "u", "v")
					onPair := bw.Conjuncts(
						chosen,
						"u lies in M",
						"so does v",
						"u and v have only the trivial relation")
					uIn, vIn, trivial := onPair[0], onPair[1], onPair[2]
					um, vm := bw.MemberOf[on.M](u, uIn), bw.MemberOf[on.M](v, vIn)
					pair := bw.TermAs[Set[B]]("{u, v}")
					distinct := bw.Have(
						"u and v are distinct",
						"u ≠ v",
						By(apart.At(u, v), uIn, vIn, trivial))
					independent := bw.Have(
						"so they are independent",
						"module_independent(R, M, {u, v})",
						By(distinct, trivial, linear_independence.IndependentPair.Read(moduleOn).At(um, vm)))
					spanned := bw.Have(
						"every vector w of M is a combination of u and v",
						"∀w:B. w ∈ M.carrier ⇒ w ∈ module_span(R, M, {u, v})",
						Derive(func(b *Argument) {
							w := b.FixAs[B]("w")
							wIn := b.Assume()
							s, t, _, relation := b.Obtain3As[A, A, A](
								"u, v and w satisfy a nontrivial relation a • u + b • v + c • w = M.zero",
								"∃a b c:A. "+
									"    a ∈ R.carrier ∧ "+
									"    b ∈ R.carrier ∧ "+
									"    c ∈ R.carrier ∧ "+
									"    ¬(a = R.zero ∧ b = R.zero ∧ c = R.zero) ∧ "+
									"    a • u + b • v + c • w = M.zero",
								By(uIn, vIn, wIn, both[1].At(u, v, w)))
							parts := b.Conjuncts(
								relation,
								"a is a scalar",
								"so is b",
								"and c",
								"not all three are zero",
								"a • u + b • v + c • w = M.zero")
							withoutC := b.Have(
								"were c zero, a • u + b • v would be",
								"c = R.zero ⇒ a • u + b • v = M.zero",
								Derive(func(c *Argument) {
									cZero := c.Assume()
									c.Show(
										"the term c • w vanishes",
										ByChase(Depth(0), moduleOn, cZero, parts[4], parts[0], parts[1], parts[2], uIn, vIn, wIn))
								}))
							nonzero := b.Have(
								"so c is not zero, else a and b would be",
								"c ≠ R.zero",
								By(parts[0], parts[1], parts[3], withoutC, trivial.At(s, t)))
							inverse := b.Conjuncts(
								b.Have(
									"c is invertible",
									"inv(c) ∈ R.carrier ∧ inv(c) * c = R.one",
									By(nonzero, parts[2], field.InvIn.Read(fieldR), field.MulLeftInverseOn.Read(fieldR))),
								"inv(c) is a scalar",
								"inv(c) * c = R.one")
							solved := b.Have(
								"solving the relation for w",
								"w = -(inv(c) * a) • u + -(inv(c) * b) • v",
								ByChase(
									Depth(0),
									moduleOn,
									inverse[1],
									parts[4],
									parts[0],
									parts[1],
									parts[2],
									inverse[0],
									uIn,
									vIn,
									wIn))
							b.Show(
								"w is a combination of u and v",
								By(
									solved,
									uIn,
									vIn,
									parts[0],
									parts[1],
									inverse[0],
									comm_ring.NegIn.Read(ring),
									comm_ring.MulIn.Read(ring),
									pairSpan.At(u, v, w)))
						}))
					spans := bw.Have(
						"so u and v span M",
						"module_span(R, M, {u, v}) = M.carrier",
						BySets(
							moduleOn,
							spanned,
							independent,
							linear_independence.IndependentInCarrier.At(R, M, pair),
							submodule.SpanLeast.At(R, M, pair, bw.TermAs[Set[B]]("M.carrier")),
							submodule.CarrierSubmodule.At(R, M)))
					bw.Show(
						"{u, v} is a basis of two vectors",
						By(
							scalarsField,
							distinct,
							independent,
							spans,
							DimBasis.Read(moduleOn).At(inv, pair),
							linear_independence.ModuleBasisDef.At(R, M, pair),
							cardinality.HasSizePair.At(u, v),
							cardinality.HasSizeDef.At(pair, two)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Submodules, kernels and images, quotients
// ---------------------------------------------------------------------------

// ZeroSubmoduleDim — over a field, the zero submodule is finite-dimensional
// of dimension zero: ∅ is a basis of it, its span being zero alone.
var ZeroSubmoduleDim = zeroSubmoduleDimThm{family.Add(registry.ProofEntry{
	Name: "ZeroSubmoduleDim",
	Key:  "prop_9653e43336013d0b",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀inv:(A → A). ∀M:module_ops(A, B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_on(R, M)",
		},
		Conclusion: "finite_dimensional(R, restrict_module(M, {M.zero})) ∧ " +
			"module_dim(R, restrict_module(M, {M.zero})) = 0",
	},
		func(a *Argument, R *Expr[RingOps[A]], inv *Arrow[A, A], M *Expr[ModuleOps[A, B]], h Fact) {
			given := a.Conjuncts(
				h,
				"the scalars form a field",
				"M is a module")
			scalarsField, moduleM := given[0], given[1]
			zero := a.TermAs[Set[B]]("{M.zero}")
			Z := a.TermAs[ModuleOps[A, B]]("restrict_module(M, {M.zero})")
			empty := a.TermAs[Set[B]]("∅")
			zeroModule := a.Have(
				"the zero submodule is a module of its own",
				"module_on(R, restrict_module(M, {M.zero}))",
				By(submodule.ZeroSubmodule.Read(moduleM), submodule.SubmoduleModuleOn.Read(moduleM).At(zero)))
			spanEmpty := submodule.SpanEmpty.Read(zeroModule)
			basis := a.Have(
				"∅ is independent and spans it: a basis",
				"module_basis(R, restrict_module(M, {M.zero}), ∅)",
				By(
					linear_independence.IndependentEmpty.At(R, Z),
					spanEmpty,
					linear_independence.ModuleBasisDef.At(R, Z, empty)))
			sized := a.Have(
				"so the zero submodule is finite-dimensional, of dimension card(∅)",
				"finite_dimensional(R, restrict_module(M, {M.zero})) ∧ "+
					"module_dim(R, restrict_module(M, {M.zero})) = card(∅⟨A:B⟩)",
				By(scalarsField, basis, finite_set.FiniteRules, FiniteBasisDim.Read(zeroModule).At(inv, empty)))
			a.Show(
				"and ∅ has no members",
				By(sized, cardinality.CardClauses))
		}),
})}

// SubmoduleDim — over a field, a submodule of a finite-dimensional M is
// finite-dimensional, of dimension at most M's: a basis of N is
// independent in M as well, so it is finite and no larger than M's
// dimension, and its size is N's dimension.
var SubmoduleDim = submoduleDimThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleDim",
	Key:  "prop_8f6c3020825bbff2",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀N:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"finite_dimensional(R, M)",
			"submodule(R, M, N)",
		},
		Conclusion: "finite_dimensional(R, restrict_module(M, N)) ∧ " +
			"module_dim(R, restrict_module(M, N)) ≤ module_dim(R, M)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			N *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"M is finite-dimensional",
				"N is a submodule")
			scalarsField, finiteM, isSubmodule := given[0], given[1], given[2]
			nModule := a.Have(
				"N with M's operations is a module over R",
				"module_on(R, restrict_module(M, N))",
				By(isSubmodule, submodule.SubmoduleModuleOn.Read(moduleOn).At(N)))
			E, basis := a.ObtainAs[Set[B]](
				"over a field the module N has a basis E",
				"∃E:set(B). module_basis(R, restrict_module(M, N), E)",
				By(scalarsField, linear_independence.BasisExists.Read(nModule).At(inv)))

			R, M, restricted :=
				a.TermAs[RingOps[A]]("R"),
				a.TermAs[ModuleOps[A, B]]("M"),
				a.TermAs[ModuleOps[A, B]]("restrict_module(M, N)")
			independentInM := a.Have(
				"E, a basis of N, is independent in M, N's combinations being M's",
				"module_independent(R, M, E)",
				By(
					basis,
					linear_independence.ModuleBasisDef.At(R, restricted, E),
					submodule.SubmoduleSubset.Read(isSubmodule),
					linear_independence.IndependentRestrict.At(R, M, N, E)))

			bound := a.Have(
				"an independent set of the finite-dimensional M is finite, with at most dim M members",
				"finite(E) ∧ card(E) ≤ module_dim(R, M)",
				By(scalarsField, finiteM, independentInM, IndependentBound.Read(moduleOn).At(inv, E)))
			dimN := a.Have(
				"E is a finite basis of N, so N is finite-dimensional, of dimension its size",
				"finite_dimensional(R, restrict_module(M, N)) ∧ module_dim(R, restrict_module(M, N)) = card(E)",
				By(scalarsField, basis, bound, FiniteBasisDim.Read(nModule).At(inv, E)))
			a.Show(
				"so dim N = card(E) ≤ dim M",
				By(Normalized, dimN, bound))
		}),
})}

// SubmoduleDimEq — over a field, a submodule of a finite-dimensional M
// with M's dimension is M: a basis of the submodule stays independent in
// M and has M's dimension as its size, so it is a basis of M, and M's
// carrier, its span, lies in the submodule.
var SubmoduleDimEq = submoduleDimEqThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleDimEq",
	Key:  "prop_38eef1f50d4bb858",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀N:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"finite_dimensional(R, M)",
			"submodule(R, M, N)",
			"module_dim(R, restrict_module(M, N)) = module_dim(R, M)",
		},
		Conclusion: "N = M.carrier",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			N *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"M is finite-dimensional",
				"N is a submodule of M",
				"N has M's dimension")
			scalarsField, finiteM, isSubmodule, fullDimension := given[0], given[1], given[2], given[3]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			restricted, carrier :=
				a.TermAs[ModuleOps[A, B]]("restrict_module(M, N)"), a.TermAs[Set[B]]("M.carrier")

			// N with M's operations is a finite-dimensional module of its own.
			nModule := a.Have(
				"N with M's operations is a module over R",
				"module_on(R, restrict_module(M, N))",
				By(isSubmodule, submodule.SubmoduleModuleOn.Read(moduleOn)))
			finiteN := a.Have(
				"a submodule of a finite-dimensional module is finite-dimensional",
				"finite_dimensional(R, restrict_module(M, N))",
				By(scalarsField, finiteM, isSubmodule, SubmoduleDim.Read(moduleOn).At(inv, N)))
			nInM := a.Have(
				"N lies in M's carrier",
				"N ⊆ M.carrier",
				By(submodule.SubmoduleSubset.Read(isSubmodule)))

			// A basis E of N, of M's dimension.
			E, basisN := a.ObtainAs[Set[B]](
				"over a field, N has a basis E",
				"∃E:set(B). module_basis(R, restrict_module(M, N), E)",
				By(scalarsField, linear_independence.BasisExists.Read(nModule).At(inv)))
			size := a.Have(
				"E has N's dimension as its size, and that is M's",
				"has_size(E, module_dim(R, M))",
				By(
					Normalized,
					scalarsField,
					finiteN,
					basisN,
					fullDimension,
					FiniteDimensionalBasis.Read(nModule).At(inv, E),
					cardinality.HasSizeDef.At(E, a.TermAs[Nat]("module_dim(R, M)"))))
			inM := a.Conjuncts(
				a.Have(
					"E lies in N and is independent in M, N's combinations being M's",
					"E ⊆ N ∧ module_independent(R, M, E)",
					By(
						basisN,
						linear_independence.ModuleBasisDef.At(R, restricted, E),
						nInM,
						linear_independence.IndependentRestrict.At(R, M, N, E))),
				"E lies in N",
				"E is independent in M")
			eInN, independentInM := inM[0], inM[1]

			// E is a basis of M as well, so it spans M inside N.
			basisM := a.Have(
				"an independent set with M's dimension as its size is a basis of M",
				"module_basis(R, M, E)",
				By(scalarsField, finiteM, independentInM, size, IndependentFullBasis.Read(moduleOn).At(inv, E)))
			spansM := a.Have(
				"so E spans M",
				"module_span(R, M, E) = M.carrier",
				By(a.Unfolded(basisM, linear_independence.ModuleBasisDef)))
			covered := a.Have(
				"M's carrier, the span of E, lies in the submodule N holding E",
				"M.carrier ⊆ N",
				spansM.RwRev(),
				By(isSubmodule, eInN, submodule.SpanLeast.At(R, M, E, N)))
			a.Show(
				"N and M's carrier lie in each other",
				By(nInM, covered, set_order.SubsetAntisym.At(N, carrier)))
		}),
})}

// RankNullity — over a field, the kernel and the image of a
// homomorphism out of a finite-dimensional M have dimensions summing to
// M's: a finite basis K of the kernel extends to a basis E of M; the
// kernel, the span of K, meets the span of E ∖ K only in zero, so f is
// one-to-one on E ∖ K and carries it to an independent set, which spans
// the image as f kills K; the two dimensions count the two parts K and
// E ∖ K of E.
var RankNullity = rankNullityThm{family.Add(registry.ProofEntry{
	Name: "RankNullity",
	Key:  "prop_3153766febbeeb35",
	Reading: "Neither the kernel nor the image is assumed finite-dimensional; both " +
		"follow from M. At the zero map the kernel is M's carrier and the image {N.zero}.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_on(R, N)",
			"module_homomorphism(R, M, N, f)",
			"finite_dimensional(R, M)",
		},
		Conclusion: "module_dim(R, restrict_module(M, group_kernel(N.zero, M.carrier, f))) + " +
			"module_dim(R, restrict_module(N, image(f, M.carrier))) = " +
			"module_dim(R, M)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"N is a module",
				"f is a homomorphism",
				"M is finite-dimensional")
			scalarsField, moduleN, linear, finiteM := given[0], given[1], given[2], given[3]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			carrierM := a.TermAs[Set[B]]("M.carrier")
			kernel := a.TermAs[Set[B]]("group_kernel(N.zero, M.carrier, f)")

			// The kernel is a finite-dimensional module; a finite basis K of it
			// is independent in M and spans the kernel there, the kernel's
			// sums being M's.
			kernelSub := a.Have(
				"the kernel of f is a submodule of M",
				"submodule(R, M, group_kernel(N.zero, M.carrier, f))",
				By(module_homomorphism.KernelSubmodule.Read(linear)))
			kernelModule := a.Have(
				"so it is a module of its own",
				"module_on(R, restrict_module(M, group_kernel(N.zero, M.carrier, f)))",
				By(kernelSub, submodule.SubmoduleModuleOn.Read(moduleOn).At(kernel)))
			kernelFinite := a.Have(
				"and finite-dimensional, as a submodule of M",
				"finite_dimensional(R, restrict_module(M, group_kernel(N.zero, M.carrier, f)))",
				By(scalarsField, finiteM, kernelSub, SubmoduleDim.Read(moduleOn).At(inv, kernel)))
			K, kernelBasis := a.UnpackAs[Set[B]](a.Unfolded(kernelFinite, FiniteDimensionalDef), "K")
			onK := a.Conjuncts(
				kernelBasis,
				"K is finite",
				"K is a basis of the kernel")
			finiteK, basisK := onK[0], onK[1]
			inKernel := a.Conjuncts(
				a.Unfolded(basisK, linear_independence.ModuleBasisDef),
				"K is independent in the kernel",
				"K spans the kernel")
			independentInKernel, spansKernel := inKernel[0], inKernel[1]
			ofK := a.Conjuncts(
				a.Have(
					"K lies in the kernel and is independent in M, the kernel's combinations being M's",
					"K ⊆ group_kernel(N.zero, M.carrier, f) ∧ module_independent(R, M, K)",
					By(
						independentInKernel,
						submodule.SubmoduleSubset.Read(kernelSub),
						linear_independence.IndependentRestrict.At(R, M, kernel, K))),
				"K lies in the kernel",
				"K is independent in M")
			kInKernel, kIndependent := ofK[0], ofK[1]
			spanK := a.Have(
				"and spans the kernel in M, the kernel's spans being M's",
				"module_span(R, M, K) = group_kernel(N.zero, M.carrier, f)",
				By(
					spansKernel,
					kernelSub,
					kInKernel,
					linear_independence.SpanRestrict.Read(moduleOn).At(kernel, K)))

			// K extends to a basis E of M, finite of the dimension of M.
			E, extension := a.ObtainAs[Set[B]](
				"extend K to a basis E of M",
				"∃E:set(B). K ⊆ E ∧ module_basis(R, M, E)",
				By(scalarsField, kIndependent, linear_independence.BasisExtends.Read(moduleOn).At(inv, K)))
			onE := a.Conjuncts(
				extension,
				"K lies in E",
				"E is a basis of M")
			kInE, basisE := onE[0], onE[1]
			sizeE := a.Conjuncts(
				a.Have(
					"E is finite, of the dimension of M as its size",
					"finite(E) ∧ card(E) = module_dim(R, M)",
					By(scalarsField, finiteM, basisE, FiniteDimensionalBasis.Read(moduleOn).At(inv, E))),
				"E is finite",
				"E has the dimension of M as its size")
			finiteE, cardE := sizeE[0], sizeE[1]
			spanningE := a.Conjuncts(
				a.Unfolded(basisE, linear_independence.ModuleBasisDef),
				"E is independent in M",
				"E spans M")
			independentE, spansM := spanningE[0], spanningE[1]
			eInM := a.Have(
				"E lies in M",
				"E ⊆ M.carrier",
				By(linear_independence.IndependentInCarrier.Read(independentE)))
			rest := a.TermAs[Set[B]]("E ∖ K")

			// The kernel, the span of K, meets the span of E ∖ K only in zero,
			// so f is one-to-one on E ∖ K and keeps it independent.
			partition := a.Conjuncts(
				a.Have(
					"E is K together with E ∖ K, which do not meet",
					"K ∪ (E ∖ K) = E ∧ K ∩ (E ∖ K) = ∅",
					BySets(kInE)),
				"K and E ∖ K make up E",
				"K and E ∖ K do not meet")
			union, disjoint := partition[0], partition[1]
			meet := a.Have(
				"the kernel, the span of K, meets the span of E ∖ K only in "+
					"zero, K and E ∖ K being disjoint parts of the independent E",
				"group_kernel(N.zero, M.carrier, f) ∩ module_span(R, M, E ∖ K) ⊆ {M.zero}",
				spanK.RwRev(),
				By(
					independentE,
					union,
					disjoint,
					linear_independence.IndependentSpansMeet.Read(moduleOn).At(K, rest)))
			restIndependent := a.Have(
				"E ∖ K is independent, as a part of E",
				"module_independent(R, M, E ∖ K)",
				By(
					independentE,
					a.Have(
						"E ∖ K lies in E",
						"E ∖ K ⊆ E",
						BySets()),
					linear_independence.IndependentSubset.At(R, M, E, rest)))
			images := a.Conjuncts(
				a.Have(
					"so f is one-to-one on E ∖ K and carries it to an independent set of N",
					"injective_on(E ∖ K, f) ∧ module_independent(R, N, image(f, E ∖ K))",
					By(linear, restIndependent, meet, linear_independence.IndependentImageKernel.At(R, M, N, f, rest))),
				"f is one-to-one on E ∖ K",
				"the images of E ∖ K are independent in N")
			oneToOne, independentInN := images[0], images[1]

			// The span W of the images of E ∖ K is the image of f: f carries E
			// into W, K going to N.zero, so it carries the span of E, all of M,
			// into W.
			imageSet := a.TermAs[Set[C]]("image(f, M.carrier)")
			imagesOfRest := a.TermAs[Set[C]]("image(f, E ∖ K)")
			span := a.TermAs[Set[C]]("module_span(R, N, image(f, E ∖ K))")
			imageSub := a.Have(
				"the image of f is a submodule of N",
				"submodule(R, N, image(f, M.carrier))",
				By(module_homomorphism.ImageSubmodule.Read(linear)))
			imageModule := a.Have(
				"so it is a module of its own",
				"module_on(R, restrict_module(N, image(f, M.carrier)))",
				By(imageSub, submodule.SubmoduleModuleOn.Read(moduleN).At(imageSet)))
			imageInN := a.Have(
				"the image lies in N",
				"image(f, M.carrier) ⊆ N.carrier",
				By(submodule.SubmoduleSubset.Read(imageSub)))
			imagesInImage := a.Have(
				"the images of E ∖ K lie in the image of f",
				"image(f, E ∖ K) ⊆ image(f, M.carrier)",
				By(
					a.Have(
						"E ∖ K lies in M",
						"E ∖ K ⊆ M.carrier",
						BySets(eInM)),
					set_image.ImageSubset.At(f, rest, carrierM)))
			spanSub := a.Have(
				"their span W is a submodule of N",
				"submodule(R, N, module_span(R, N, image(f, E ∖ K)))",
				By(
					imagesInImage,
					imageInN,
					set_order.SubsetTrans.At(imagesOfRest, imageSet, a.TermAs[Set[C]]("N.carrier")),
					submodule.SpanSubmodule.Read(moduleN).At(imagesOfRest)))
			kernelOf := a.Unfolded(kInKernel, set_basic.SubsetDef)
			intoSpan := a.Unfolded(submodule.SubsetSpan.At(R, N, imagesOfRest), set_basic.SubsetDef)
			imagesInSpan := a.Have(
				"f carries E into W: K to N.zero, E ∖ K to the images",
				"image(f, E) ⊆ module_span(R, N, image(f, E ∖ K))",
				Simp(Fwd(set_basic.SubsetDef), Fwd(set_image.ForallInImage)),
				Derive(func(b *Argument) {
					z := b.FixAs[B]("z")
					zInE := b.Assume()
					b.Cases(b.Term("z ∈ K"))
					b.When(
						"z lies in K: f kills it, and W holds N.zero",
						func(c *Argument, zInK Fact) {
							killed := c.Have(
								"z lies in the kernel, so f kills it",
								"f(z) = N.zero",
								By(kernelOf.At(z), zInK, group_homomorphism.InKernel.At(c.TermAs[C]("N.zero"), carrierM, f, z)))
							c.Show(
								"W is a submodule, so it holds N.zero",
								killed.Rw(),
								By(submodule.SubmoduleZero.Read(spanSub)))
						})
					b.Otherwise(
						"z lies in E ∖ K: f(z) is one of the images, all in W",
						func(c *Argument, zOutsideK Fact) {
							c.Show(
								"f(z) is the image of a member of E ∖ K",
								By(
									intoSpan.At(f.Apply(z)),
									set_image.FunInImage.At(f, rest, z),
									set_basic.InDiff.At(E, K, z),
									zInE,
									zOutsideK))
						})
				}))
			outside := a.Have(
				"so f carries M, the span of E, into W, a submodule holding the images of E",
				"image(f, M.carrier) ⊆ module_span(R, N, image(f, E ∖ K))",
				By(
					linear,
					eInM,
					spansM,
					spanSub,
					imagesInSpan,
					linear_independence.HomSpanInSubmodule.At(R, M, N, f, E, span)))
			inside := a.Have(
				"and W lies in the image, a submodule holding the images of E ∖ K",
				"module_span(R, N, image(f, E ∖ K)) ⊆ image(f, M.carrier)",
				By(imageSub, imagesInImage, submodule.SpanLeast.At(R, N, imagesOfRest, imageSet)))
			wIsImage := a.Have(
				"so W is the image",
				"module_span(R, N, image(f, E ∖ K)) = image(f, M.carrier)",
				By(inside, outside, set_order.SubsetAntisym.At(span, imageSet)))
			spanned := a.Have(
				"and the images of E ∖ K span the image read as a module of its own, its spans being N's",
				"module_span(R, restrict_module(N, image(f, M.carrier)), image(f, E ∖ K)) = image(f, M.carrier)",
				By(
					wIsImage,
					imageSub,
					imagesInImage,
					linear_independence.SpanRestrict.Read(moduleN).At(imageSet, imagesOfRest)))

			// The images of E ∖ K are a basis of the image, and the two
			// dimensions count K and E ∖ K.
			independentImages := a.Have(
				"the images of E ∖ K are independent in the image, independent in N and lying in it",
				"module_independent(R, restrict_module(N, image(f, M.carrier)), image(f, E ∖ K))",
				By(
					imageInN,
					imagesInImage,
					independentInN,
					linear_independence.IndependentRestrict.At(R, N, imageSet, imagesOfRest)))
			basisImages := a.Have(
				"and, spanning it, a basis of it",
				"module_basis(R, restrict_module(N, image(f, M.carrier)), image(f, E ∖ K))",
				By(
					independentImages,
					spanned,
					linear_independence.ModuleBasisDef.At(
						R, a.TermAs[ModuleOps[A, C]]("restrict_module(N, image(f, M.carrier))"), imagesOfRest)))
			finiteRest := a.Have(
				"E ∖ K is finite",
				"finite(E ∖ K)",
				By(finiteE, finite_set.FiniteDiff.At(E, K)))
			kernelDim := a.Have(
				"the kernel's dimension is the size of its basis K",
				"module_dim(R, restrict_module(M, group_kernel(N.zero, M.carrier, f))) = card(K)",
				By(scalarsField, basisK, finiteK, DimBasis.Read(kernelModule).At(inv, K)))
			imageDim := a.Have(
				"the image's is the size of its basis, the images of E ∖ K",
				"module_dim(R, restrict_module(N, image(f, M.carrier))) = card(image(f, E ∖ K))",
				By(
					scalarsField,
					basisImages,
					finiteRest,
					finite_set.FiniteImage.At(f, rest),
					DimBasis.Read(imageModule).At(inv, imagesOfRest)))
			counted := a.Have(
				"f is one-to-one on E ∖ K, so it has as many images as members",
				"card(image(f, E ∖ K)) = card(E ∖ K)",
				By(oneToOne, finiteRest, cardinality.CardImageInj.At(f, rest)))
			split := a.Have(
				"so E has card(K) + card(E ∖ K) members",
				"card(E) = card(K) + card(E ∖ K)",
				By(finiteE, union, disjoint, cardinality.CardOfDisjointParts.At(K, rest, E)))
			a.Show(
				"the two dimensions count K and E ∖ K, the two parts of a basis of M",
				CalcEq(
					Leg(
						a.TermAs[Nat]("card(K) + card(E ∖ K)"),
						"each dimension is the size of a basis",
						By(kernelDim, imageDim, counted)),
					Leg(
						a.TermAs[Nat]("card(E)"),
						"K and E ∖ K make up E",
						By(split)),
					FinalLeg(
						"E has the dimension of M as its size",
						By(cardE)),
				))
		}),
})}

// LinearKernelVector — a homomorphism of finite-dimensional spaces over a field
// into a space of smaller dimension kills a nonzero vector: by rank-nullity the
// kernel has positive dimension, so it holds more than zero.
var LinearKernelVector = linearKernelVectorThm{family.Add(registry.ProofEntry{
	Name: "LinearKernelVector",
	Key:  "prop_d1c861d3e60c3a4",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀inv:(A → A). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_homomorphism(R, M, N, f)",
			"finite_dimensional(R, M)",
			"finite_dimensional(R, N)",
			"module_dim(R, N) < module_dim(R, M)",
		},
		Conclusion: "∃u:B. u ∈ M.carrier ∧ u ≠ M.zero ∧ f(u) = N.zero",
		Abbrev: Abbrev{
			{Name: "kernelSpace", Text: "restrict_module(M, group_kernel(N.zero, M.carrier, f))"},
			{Name: "imageSpace", Text: "restrict_module(N, image(f, M.carrier))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[module_record.ModuleOps[A, B]],
			inv *Arrow[A, A],
			N *Expr[module_record.ModuleOps[A, C]],
			f *Arrow[B, C],
			scalars, hom, finiteM, finiteN, smaller Fact,
		) {
			source := a.Have(
				"M is a module",
				"module_on(R, M)",
				By(module_homomorphism.HomSource.Read(hom)))
			target := a.Have(
				"N is a module",
				"module_on(R, N)",
				By(module_homomorphism.HomTarget.Read(hom)))
			kernelIn := a.Have(
				"the kernel is a submodule of M",
				"submodule(R, M, group_kernel(N.zero, M.carrier, f))",
				By(module_homomorphism.KernelSubmodule.Read(hom)))
			imageIn := a.Have(
				"the image is a submodule of N",
				"submodule(R, N, image(f, M.carrier))",
				By(module_homomorphism.ImageSubmodule.Read(hom)))
			kernel, image :=
				a.TermAs[Set[B]]("group_kernel(N.zero, M.carrier, f)"), a.TermAs[Set[C]]("image(f, M.carrier)")
			ranks := a.Have(
				"rank-nullity: the kernel and the image add up to M",
				"module_dim(R, «kernelSpace») + module_dim(R, «imageSpace») = module_dim(R, M)",
				By(source, scalars, target, hom, finiteM, RankNullity.At(R, M, inv, N, f)))
			sizes := a.Have(
				"the kernel is finite-dimensional, and the image no larger than N",
				"finite_dimensional(R, «kernelSpace») ∧ module_dim(R, «imageSpace») ≤ module_dim(R, N)",
				By(
					source,
					target,
					scalars,
					finiteM,
					finiteN,
					kernelIn,
					imageIn,
					SubmoduleDim.At(R, M, inv, kernel),
					SubmoduleDim.At(R, N, inv, image)))
			kernelOn := a.Have(
				"the kernel is a module",
				"module_on(R, «kernelSpace»)",
				By(source, kernelIn, submodule.SubmoduleModuleOn.At(R, M, kernel)))
			positive := a.Have(
				"so the kernel has positive dimension",
				"module_dim(R, «kernelSpace») ≠ 0",
				ByArith(smaller, ranks, sizes))
			proper := a.Have(
				"a module of positive dimension is more than zero",
				"group_kernel(N.zero, M.carrier, f) ≠ {M.zero}",
				By(
					kernelOn,
					scalars,
					sizes,
					positive,
					DimZero.At(R, a.TermAs[module_record.ModuleOps[A, B]]("«kernelSpace»"), inv)))
			zero := a.Have(
				"zero lies in the kernel",
				"M.zero ∈ group_kernel(N.zero, M.carrier, f)",
				By(kernelIn, submodule.SubmoduleZero.At(R, M, kernel)))
			vector := a.Have(
				"so the kernel holds a vector other than zero",
				"∃u:B. u ∈ group_kernel(N.zero, M.carrier, f) ∧ u ≠ M.zero",
				BySets(proper, zero))
			a.Show(
				"a vector of the kernel lies in M, and f kills it",
				By(vector, group_homomorphism.InKernel))
		}),
})}

// ImageDim — over a field, the image of a finite-dimensional module under
// a linear map is finite-dimensional, of dimension at most the source's:
// the images of a finite basis span it, and rank–nullity bounds its
// dimension.
var ImageDim = imageDimThm{family.Add(registry.ProofEntry{
	Name: "ImageDim",
	Key:  "prop_5941043fb6910ae5",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀inv:(A → A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_homomorphism(R, M, N, f)",
			"finite_dimensional(R, M)",
		},
		Conclusion: "finite_dimensional(R, restrict_module(N, image(f, M.carrier))) ∧ " +
			"module_dim(R, restrict_module(N, image(f, M.carrier))) ≤ module_dim(R, M)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			inv *Arrow[A, A],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"f is a homomorphism",
				"M is finite-dimensional")
			scalarsField, linear, finiteM := given[0], given[1], given[2]
			moduleM := module_homomorphism.HomSource.Read(linear)
			moduleN := module_homomorphism.HomTarget.Read(linear)
			image := a.TermAs[Set[C]]("image(f, M.carrier)")
			imageSub := a.Have(
				"the image of f is a submodule of N",
				"submodule(R, N, image(f, M.carrier))",
				By(module_homomorphism.ImageSubmodule.Read(linear)))
			imageModule := a.Have(
				"so a module of its own",
				"module_on(R, restrict_module(N, image(f, M.carrier)))",
				By(imageSub, submodule.SubmoduleModuleOn.Read(moduleN).At(image)))

			// The images of a finite basis E of M span the image.
			E, finiteBasis := a.UnpackAs[Set[B]](a.Unfolded(finiteM, FiniteDimensionalDef), "E")
			aboutE := a.Conjuncts(
				finiteBasis,
				"E is finite",
				"E is a basis of M")
			ofBasis := a.Conjuncts(
				a.Unfolded(aboutE[1], linear_independence.ModuleBasisDef),
				"E is independent",
				"E spans M")
			eInM := a.Have(
				"E lies in M",
				"E ⊆ M.carrier",
				By(linear_independence.IndependentInCarrier.Read(ofBasis[0])))
			images := a.TermAs[Set[C]]("image(f, E)")
			spans := a.Have(
				"f carries the span of E, all of M, onto the span of the images of E",
				"image(f, M.carrier) = module_span(R, N, image(f, E))",
				By(Normalized, linear, eInM, ofBasis[1], linear_independence.HomSpan.At(R, M, N, f, E)))
			inImage := a.Have(
				"the images of E lie in the image",
				"image(f, E) ⊆ image(f, M.carrier)",
				By(eInM, set_image.ImageSubset.At(f, E, a.TermAs[Set[B]]("M.carrier"))))
			spansImage := a.Have(
				"and span it read as a module of its own, its spans being N's",
				"module_span(R, restrict_module(N, image(f, M.carrier)), image(f, E)) = image(f, M.carrier)",
				By(spans, imageSub, inImage, linear_independence.SpanRestrict.Read(moduleN).At(image, images)))
			spanning := a.Have(
				"so the image has a finite spanning set, the finitely many images of E",
				"∃S:set(C). "+
					"    finite(S) ∧ "+
					"    S ⊆ image(f, M.carrier) ∧ "+
					"    module_span(R, restrict_module(N, image(f, M.carrier)), S) = image(f, M.carrier)",
				Witness(images),
				By(aboutE[0], finite_set.FiniteImage.At(f, E), inImage, spansImage))
			finite := a.Have(
				"and is finite-dimensional",
				"finite_dimensional(R, restrict_module(N, image(f, M.carrier)))",
				By(scalarsField, spanning, FiniteDimensionalSpanning.Read(imageModule).At(inv)))

			// Rank–nullity bounds its dimension.
			counted := a.Have(
				"the kernel's and the image's dimensions sum to M's",
				"module_dim(R, restrict_module(M, group_kernel(N.zero, M.carrier, f))) + "+
					"module_dim(R, restrict_module(N, image(f, M.carrier))) = "+
					"module_dim(R, M)",
				By(scalarsField, moduleN, linear, finiteM, RankNullity.Read(moduleM).At(inv, N, f)))
			bounded := a.Have(
				"so the image's is at most M's",
				"module_dim(R, restrict_module(N, image(f, M.carrier))) ≤ module_dim(R, M)",
				ByArith(counted))
			a.Show(
				"the image is finite-dimensional, of dimension at most M's",
				By(finite, bounded))
		}),
})}

// InjectiveImageDim — over a field, a one-to-one linear map carries a
// finite-dimensional module onto an image of the same dimension: onto its
// image the map is an isomorphism.
var InjectiveImageDim = injectiveImageDimThm{family.Add(registry.ProofEntry{
	Name: "InjectiveImageDim",
	Key:  "prop_c6076a88af1834bd",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀inv:(A → A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_homomorphism(R, M, N, f)",
			"injective_on(M.carrier, f)",
			"finite_dimensional(R, M)",
		},
		Conclusion: "finite_dimensional(R, restrict_module(N, image(f, M.carrier))) ∧ " +
			"module_dim(R, restrict_module(N, image(f, M.carrier))) = module_dim(R, M)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			inv *Arrow[A, A],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"f is a homomorphism",
				"f is one-to-one on M",
				"M is finite-dimensional")
			scalarsField, linear, oneToOne, finiteM := given[0], given[1], given[2], given[3]
			imageModuleRecord := a.TermAs[ModuleOps[A, C]]("restrict_module(N, image(f, M.carrier))")
			a.Show(
				"one-to-one, f is an isomorphism of M onto its image, "+
					"so the image is finite-dimensional, of M's dimension",
				By(
					scalarsField,
					linear,
					oneToOne,
					finiteM,
					module_homomorphism.IsomorphismOntoImage.At(R, M, N, f),
					IsomorphismDim.At(R, M, inv, imageModuleRecord, f)))
		}),
})}

// QuotientDim — over a field, a submodule's dimension and the quotient's
// sum to M's: rank–nullity at the projection u ↦ u + N onto the quotient
// module, whose kernel is N and whose image is every coset, the cosets of
// N being the image of M's carrier under the projection.
var QuotientDim = quotientDimThm{family.Add(registry.ProofEntry{
	Name: "QuotientDim",
	Key:  "prop_6f6d482e3e5d898a",
	Reading: "At N = M.carrier there is one coset, M itself, " +
		"the quotient's zero, and the quotient has dimension zero.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀N:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"finite_dimensional(R, M)",
			"submodule(R, M, N)",
		},
		Conclusion: "module_dim(R, restrict_module(M, N)) + module_dim(R, quotient_module(M, N)) = " +
			"module_dim(R, M)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			N *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"M is finite-dimensional",
				"N is a submodule of M")
			scalarsField, finiteM, submoduleN := given[0], given[1], given[2]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			quotient := a.TermAs[ModuleOps[A, Set[B]]]("quotient_module(M, N)")
			projection := a.TermAs[Fun[B, Set[B]]]("coset_map(M.add, N)")

			kernel := a.Have(
				"the projection u ↦ u + N kills exactly N",
				"group_kernel(N, M.carrier, coset_map(M.add, N)) = N",
				By(moduleOn, submoduleN, module_homomorphism.ProjectionKernel.At(R, M, N)))
			// The quotient's carrier is the cosets of N, the quotient of M's
			// carrier by "lies in u + N"; N lying in M, they are the cosets u + N
			// of the u in M, the projection's image. Unfolding the two records
			// below, the quotient's carrier is rewritten by this equation and
			// the two sides meet.
			cosets := a.Have(
				"the cosets of N are the image of M's carrier under u ↦ u + N",
				"left_cosets(M.add, M.carrier, N) = image(coset_map(M.add, N), M.carrier)",
				By(
					submodule.SubmoduleSubset.Read(submoduleN),
					quotient_group.LeftCosetsImage.Read(module.AddGroupOn.Read(moduleOn)).At(N)))
			onto := a.Have(
				"the projection is onto: restricted to its image, the quotient module is itself",
				"restrict_module(quotient_module(M, N), image(coset_map(M.add, N), M.carrier)) = "+
					"quotient_module(M, N)",
				Unfold(module_record.RestrictModuleDef),
				Unfold(submodule.QuotientModuleDef),
				cosets.Rw(),
				Basic())
			a.Show(
				"rank–nullity at the projection, a homomorphism onto the quotient module",
				By(
					kernel,
					onto,
					scalarsField,
					finiteM,
					submoduleN,
					submodule.QuotientModuleOn.Read(moduleOn).At(N),
					module_homomorphism.ProjectionHom.At(R, M, N),
					RankNullity.Read(moduleOn).At(inv, quotient, projection)))
		}),
})}

// DimFiniteIffSubAndQuotient — over a field, a module is
// finite-dimensional exactly when a submodule and the quotient by it
// are: ⇒ by SubmoduleDim and the projection's image; ⇐ by a basis of N
// plus lifts of a basis of M/N.
var DimFiniteIffSubAndQuotient = dimFiniteIffSubAndQuotientThm{family.Add(registry.ProofEntry{
	Name: "DimFiniteIffSubAndQuotient",
	Key:  "prop_ec15e5bff78d48d9",
	Reading: "QuotientDim adds the dimensions once M is finite-dimensional; this " +
		"is the finiteness itself, in both directions. The field is load-bearing for " +
		"⇒, finite_dimensional asking a finite basis: over ℤ, M = ℤ has the basis {1}, " +
		"but its quotient by 2ℤ has no basis at all, 2 • (1 + 2ℤ) being the zero coset.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀N:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"submodule(R, M, N)",
		},
		Conclusion: "finite_dimensional(R, M) ⇔ " +
			"finite_dimensional(R, restrict_module(M, N)) ∧ finite_dimensional(R, quotient_module(M, N))",
	},
		func(
			a *Argument,
			ambient module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			N *Expr[Set[B]],
			scalarsField, submoduleN Fact,
		) {
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			carrier := a.TermAs[Set[B]]("M.carrier")
			quotient := a.TermAs[ModuleOps[A, Set[B]]]("quotient_module(M, N)")
			projection := a.TermAs[Fun[B, Set[B]]]("coset_map(M.add, N)")
			restricted := a.TermAs[ModuleOps[A, B]]("restrict_module(M, N)")
			contained := a.Have(
				"the submodule lies in the ambient carrier",
				"N ⊆ M.carrier",
				By(submoduleN, submodule.SubmoduleSubset))
			a.Iff()
			a.Forward(
				"a submodule and quotient inherit finite dimensionality",
				func(b *Argument, finiteM Fact) {
					b.Show(
						"the submodule and quotient are finite dimensional",
						SplitConj(
							Case(
								"the submodule of a finite-dimensional module is finite dimensional",
								By(finiteM, scalarsField, submoduleN, SubmoduleDim.Read(ambient).At(inv, N))),
							Case(
								"the quotient is the image of the linear projection",
								Derive(func(c *Argument) {
									onto := c.Have(
										"every quotient element is the coset of an ambient vector",
										"image(coset_map(M.add, N), M.carrier) = quotient_module(M, N).carrier",
										Simp(Fwd(submodule.QuotientModuleDef), Fwd(module_record.ModCarrierDef)),
										By(
											Normalized,
											contained,
											quotient_group.LeftCosetsImage.Read(module.AddGroupOn.Read(ambient)).At(N)))
									imageModule := c.Have(
										"the image module is the whole quotient",
										"restrict_module(quotient_module(M, N), image(coset_map(M.add, N), M.carrier)) = "+
											"quotient_module(M, N)",
										Simp(Fwd(onto), Fwd(module_record.RestrictModuleCarrier)),
										Basic())
									c.Show(
										"the linear image of the finite-dimensional source is finite dimensional",
										By(
											imageModule,
											finiteM,
											scalarsField,
											submoduleN,
											module_homomorphism.ProjectionHom.Read(ambient).At(N),
											ImageDim.At(R, inv, M, quotient, projection)))
								}))))
				})
			a.Backward(
				"finite-dimensional submodule and quotient give a finite spanning set",
				func(b *Argument, finiteBoth Fact) {
					parts := b.Conjuncts(
						finiteBoth,
						"the submodule is finite dimensional",
						"the quotient is finite dimensional")
					E, basis := b.ObtainAs[Set[B]](
						"choose a finite basis of the submodule",
						"∃E:set(B). finite(E) ∧ module_basis(R, restrict_module(M, N), E)",
						By(parts[0], FiniteDimensionalDef.At(R, restricted)))
					T, lifts := b.ObtainAs[Set[B]](
						"choose finitely many quotient lifts spanning M modulo N",
						"∃T:set(B). finite(T) ∧ T ⊆ M.carrier ∧ M.carrier ⊆ set_mul(M.add, module_span(R, M, T), N)",
						By(
							submodule.CarrierSubmodule.Read(ambient),
							parts[1],
							contained,
							scalarsField,
							submoduleN,
							module_record.RestrictModuleCarrier.At(M),
							QuotientComplementLift.Read(ambient).At(inv, carrier, N)))
					spansN := b.Have(
						"the finite basis spans N inside the ambient module",
						"module_span(R, M, E) = N ∧ E ⊆ M.carrier",
						By(
							basis,
							submoduleN,
							linear_independence.BasisRestrict.Read(ambient).At(N, E),
							linear_independence.IndependentInCarrier.At(R, M, E)))
					union := b.TermAs[Set[B]]("E ∪ T")
					finiteUnion := b.Have(
						"the union of the basis and quotient lifts is finite and lies in M",
						"finite(E ∪ T) ∧ E ∪ T ⊆ M.carrier",
						BySets(basis, spansN, lifts, finite_set.FiniteUnion.At(E, T)))
					contains := b.Have(
						"the union span contains N and the span of the quotient lifts",
						"N ⊆ module_span(R, M, E ∪ T) ∧ module_span(R, M, T) ⊆ module_span(R, M, E ∪ T)",
						By(
							Normalized,
							spansN,
							submodule.SpanMono.At(R, M, E, union),
							submodule.SpanMono.At(R, M, T, union),
							set_order.SubsetUnion.At(E, T),
							set_order.SubsetUnion.At(T, E)))
					spanSubmodule := b.Have(
						"the union span is a submodule of M",
						"submodule(R, M, module_span(R, M, E ∪ T))",
						By(finiteUnion, submodule.SpanSubmodule.Read(ambient).At(union)))
					spans := b.Have(
						"closure under addition and the quotient-lift coverage make the union span all of M",
						"module_span(R, M, E ∪ T) = M.carrier",
						BySets(
							submodule.SubmoduleAdd.Read(spanSubmodule),
							submodule.SubmoduleSubset.Read(spanSubmodule),
							contains,
							lifts,
							At(quotient_group.InSetMul, b.TermAs[Op[B]]("M.add"), b.TermAs[Set[B]]("module_span(R, M, T)"), N)))
					b.Show(
						"the explicit finite spanning set makes M finite dimensional",
						Simp(Fwd(FiniteDimensionalSpanning.Read(ambient))),
						Witness(union),
						By(spans, finiteUnion))
				})
		}),
})}

// DimFiniteOfKernelAndImage — over a field, a linear map whose kernel and
// image are finite-dimensional has a finite-dimensional source: the
// quotient by the kernel is isomorphic to the image, so it is
// finite-dimensional, and a module is finite-dimensional when a submodule
// and the quotient by it are.
var DimFiniteOfKernelAndImage = dimFiniteOfKernelAndImageThm{family.Add(registry.ProofEntry{
	Name: "DimFiniteOfKernelAndImage",
	Key:  "prop_feb96c9e4036da62",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀inv:(A → A). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_homomorphism(R, M, N, f)",
			"finite_dimensional(R, restrict_module(M, group_kernel(N.zero, M.carrier, f)))",
			"finite_dimensional(R, restrict_module(N, image(f, M.carrier)))",
		},
		Conclusion: "finite_dimensional(R, M)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			inv *Arrow[A, A],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"f is a homomorphism",
				"its kernel is finite-dimensional",
				"and so is its image")
			scalarsField, linear, finiteKernel, finiteImage := given[0], given[1], given[2], given[3]
			kernel := a.TermAs[Set[B]]("group_kernel(N.zero, M.carrier, f)")
			quotient := a.TermAs[ModuleOps[A, Set[B]]]("quotient_module(M, group_kernel(N.zero, M.carrier, f))")
			image := a.TermAs[ModuleOps[A, C]]("restrict_module(N, image(f, M.carrier))")
			induced := a.TermAs[Fun[Set[B], C]]("induced_map(f)")
			inverse := a.TermAs[Fun[C, Set[B]]](
				"inverse_on(quotient_module(M, group_kernel(N.zero, M.carrier, f)).carrier, induced_map(f))")
			first := a.Simplified(module_homomorphism.FirstIsomorphism.Read(linear))
			finiteQuotient := a.Have(
				"by the first isomorphism theorem the quotient by the kernel "+
					"is isomorphic to the image, so it is finite-dimensional",
				"finite_dimensional(R, quotient_module(M, group_kernel(N.zero, M.carrier, f)))",
				By(
					scalarsField,
					finiteImage,
					first,
					module_homomorphism.IsomorphismInverse.At(R, quotient, image, induced),
					IsomorphismDim.At(R, image, inv, quotient, inverse)))
			a.Show(
				"the finite-dimensional kernel and quotient make M finite-dimensional",
				By(
					scalarsField,
					finiteKernel,
					finiteQuotient,
					module_homomorphism.HomSource.Read(linear),
					module_homomorphism.KernelSubmodule.Read(linear),
					DimFiniteIffSubAndQuotient.At(R, M, inv, kernel)))
		}),
})}

// QuotientDimZeroIff — over a field, a quotient I/J of submodules
// J ⊆ I is finite-dimensional of dimension zero exactly when I = J: I/J
// has only its zero class J exactly when the two agree (QuotientTrivialIff).
// A finite-dimensional I/J of dimension zero is its zero class by DimZero,
// and at I = J the whole quotient is the zero submodule of itself, which
// ZeroSubmoduleDim counts.
var QuotientDimZeroIff = quotientDimZeroIffThm{family.Add(registry.ProofEntry{
	Name: "QuotientDimZeroIff",
	Key:  "prop_3d3881a1b17b79e5",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀I J:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"submodule(R, M, I)",
			"submodule(R, M, J)",
			"J ⊆ I",
		},
		Conclusion: "(finite_dimensional(R, «iModJ») ∧ module_dim(R, «iModJ») = 0) ⇔ I = J",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			I, J *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"I is a submodule of M",
				"so is J",
				"J lies in I")
			scalarsField, subI, subJ, jInI := given[0], given[1], given[2], given[3]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			restricted := a.TermAs[ModuleOps[A, B]]("restrict_module(M, I)")
			quotient := a.TermAs[ModuleOps[A, Set[B]]]("«iModJ»")
			moduleI := a.Have(
				"I is a module of its own",
				"module_on(R, restrict_module(M, I))",
				By(subI, submodule.SubmoduleModuleOn.Read(moduleOn).At(I)))
			denominator := a.Have(
				"J is a submodule of I",
				"submodule(R, restrict_module(M, I), J)",
				By(subJ, jInI, submodule.SubmoduleRestrict.At(R, M, I, J)))
			moduleQuotient := a.Have(
				"I/J is a module",
				"module_on(R, «iModJ»)",
				By(moduleI, denominator, submodule.QuotientModuleOn.At(R, restricted, J)))
			trivial := a.Have(
				"I/J has only its zero class exactly when I and J agree",
				"left_cosets(M.add, I, J) = {J} ⇔ I = J",
				By(
					submodule.SubmoduleSubgroup.Read(denominator),
					quotient_group.QuotientTrivialIff.Read(module.AddGroupOn.Read(moduleI)).At(J)))
			finiteZero := a.Have(
				"a finite-dimensional I/J has dimension zero exactly when I and J agree",
				"finite_dimensional(R, «iModJ») ⇒ (module_dim(R, «iModJ») = 0 ⇔ I = J)",
				By(Normalized, moduleQuotient, scalarsField, trivial, DimZero.At(R, quotient, inv)))
			equalZero := a.Have(
				"and I = J makes I/J finite-dimensional of dimension zero",
				"I = J ⇒ finite_dimensional(R, «iModJ») ∧ module_dim(R, «iModJ») = 0",
				Derive(func(b *Argument) {
					equal := b.Assume()
					whole := b.Have(
						"the zero class is then the whole of I/J",
						"restrict_module(«iModJ», {J}) = «iModJ»",
						Unfold(module_record.RestrictModuleDef),
						Unfold(submodule.QuotientModuleDef),
						By(Normalized, trivial, equal))
					b.Show(
						"so I/J is the zero submodule of itself",
						By(moduleQuotient, scalarsField, whole, ZeroSubmoduleDim.At(R, inv, quotient)))
				}))
			a.Show(
				"finiteness and dimension zero characterize I = J",
				By(finiteZero, equalZero))
		}),
})}

// QuotientEnlargeMap — for submodules J ⊆ I' ⊆ I, the map x + J ↦ x + I' is
// the linear comparison of the three quotients: its image is the whole of
// I/I', and I/J restricted to its kernel is I'/J, both stated on
// restrict_module, the shape RankNullity reads. A class x + J enlarged by
// I' is x + I', as I', a subgroup holding J, absorbs J; so every class of
// I/I' is reached, and x + J goes to I' exactly when x lies in I'.
var QuotientEnlargeMap = quotientEnlargeMapThm{family.Add(registry.ProofEntry{
	Name: "QuotientEnlargeMap",
	Key:  "prop_9ea3830b8a436167",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀I I' J:set(B).",
		Hypotheses: []string{
			"submodule(R, M, I)",
			"submodule(R, M, I')",
			"submodule(R, M, J)",
			"J ⊆ I'",
			"I' ⊆ I",
		},
		Conclusion: "module_homomorphism(R, «iModJ», «iModIPrime», «enlarging») ∧ " +
			"restrict_module(«iModIPrime», image(«enlarging», left_cosets(M.add, I, J))) = «iModIPrime» ∧ " +
			"restrict_module(«iModJ», «kernelClasses») = «iPrimeModJ»",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			I, IPrime, J *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"I is a submodule of M",
				"so is I'",
				"so is J",
				"J lies in I'",
				"I' lies in I")
			subI, subIPrime, subJ, jInIPrime, iPrimeInI := given[0], given[1], given[2], given[3], given[4]
			additive := module.AddGroupOn.Read(moduleOn)
			jInI := a.Have(
				"J lies in I",
				"J ⊆ I",
				By(jInIPrime, iPrimeInI, set_order.SubsetTrans.At(J, IPrime, I)))
			moduleI := a.Have(
				"I is a module of its own",
				"module_on(R, restrict_module(M, I))",
				By(subI, submodule.SubmoduleModuleOn.Read(moduleOn).At(I)))
			moduleIPrime := a.Have(
				"and so is I'",
				"module_on(R, restrict_module(M, I'))",
				By(subIPrime, submodule.SubmoduleModuleOn.Read(moduleOn).At(IPrime)))
			additiveI, additiveIPrime := module.AddGroupOn.Read(moduleI), module.AddGroupOn.Read(moduleIPrime)

			enlarge := a.TermAs[Fun[Set[B], Set[B]]]("«enlarging»")
			classes := a.TermAs[Set[Set[B]]]("left_cosets(M.add, I, J)")
			linear := a.Have(
				"enlarging a class of J by I' is a linear map from I/J to I/I'",
				"module_homomorphism(R, «iModJ», «iModIPrime», «enlarging»)",
				By(
					subI,
					subJ,
					subIPrime,
					jInI,
					iPrimeInI,
					jInIPrime,
					set_order.SubsetRefl.At(I),
					module_homomorphism.QuotientInclusionHom.Read(moduleOn).At(I, I, J, IPrime)))
			inM := a.Unfolded(submodule.SubmoduleSubset.Read(subI).AsFact(), set_basic.SubsetDef)
			subgroupIPrime := a.Have(
				"I' is a subgroup of M",
				"subgroup(module_additive_group(M), I')",
				By(submodule.SubmoduleSubgroup.Read(subIPrime)))
			value := a.Have(
				"the class x + J, enlarged by I', is x + I'",
				"∀x:B. x ∈ I ⇒ set_mul(M.add, left_coset(M.add, x, J), I') = left_coset(M.add, x, I')",
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					inI := b.Assume()
					vector := b.MemberOf[on.M](x, b.Have(
						"x is a vector, I lying in M",
						"x ∈ M.carrier",
						By(inM, inI)))
					b.Show(
						"I', a subgroup holding J and so zero, absorbs J",
						By(
							quotient_group.LeftCosetSetMulAbsorb.Read(additive).At(vector, J, IPrime),
							subgroupIPrime,
							jInIPrime,
							submodule.SubmoduleZero.Read(subJ)))
				}))
			classesOfI := a.Have(
				"the class of a member of I is a class of I/J",
				"∀u:B. u ∈ I ⇒ left_coset(M.add, u, J) ∈ left_cosets(M.add, I, J)",
				Simp(Fwd(quotient_group.LeftCosetsImage.Read(additiveI)), Fwd(group.CosetMapDef)),
				By(set_image.FunInImage))
			classesOfIPrime := a.Have(
				"and the class of a member of I' one of I'/J",
				"∀u:B. u ∈ I' ⇒ left_coset(M.add, u, J) ∈ left_cosets(M.add, I', J)",
				Simp(Fwd(quotient_group.LeftCosetsImage.Read(additiveIPrime)), Fwd(group.CosetMapDef)),
				By(set_image.FunInImage))

			killedAreIPrimeClasses := a.Have(
				"a class s of I/J the map sends to I' is one of I'/J: "+
					"s is x + J for an x in I, and x + I' = I' puts x in I'",
				"∀s:set(B). "+
					"    s ∈ left_cosets(M.add, I, J) ⇒ set_mul(M.add, s, I') = I' ⇒ s ∈ left_cosets(M.add, I', J)",
				Simp(Fwd(quotient_group.ForallInLeftCosets.Read(additiveI))),
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					inI := b.Assume()
					killed := b.Simplified(b.Assume(), Fwd(value))
					vector := b.MemberOf[on.M](x, b.Have(
						"x is a vector, I lying in M",
						"x ∈ M.carrier",
						By(inM, inI)))
					inIPrime := b.Have(
						"x + I' is I', so x lies in I'",
						"x ∈ I'",
						By(
							killed,
							subgroupIPrime,
							quotient_group.LeftCosetIsSubgroupIffIn.Read(additive).At(vector, IPrime)))
					b.Show(
						"so x + J is a class of I'/J",
						By(classesOfIPrime.At(x), inIPrime))
				}))
			iPrimeClassesKilled := a.Have(
				"a class s of I'/J is one of I/J the map sends to I': s is x + J for an x in I', and x + I' is I'",
				Statement{
					Binders: "∀s:set(B).",
					Hypotheses: []string{
						"s ∈ left_cosets(M.add, I', J)",
					},
					Conclusion: "s ∈ left_cosets(M.add, I, J) ∧ set_mul(M.add, s, I') = I'",
				},
				Simp(Fwd(quotient_group.ForallInLeftCosets.Read(additiveIPrime))),
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					inIPrime := b.Assume()
					inI := b.Have(
						"x lies in I, as I' does",
						"x ∈ I",
						By(inIPrime, iPrimeInI, set_basic.SubsetDef))
					vector := b.MemberOf[on.M](x, b.Have(
						"x is a vector, I lying in M",
						"x ∈ M.carrier",
						By(inM, inI)))
					b.Show(
						"x + J is a class of I/J, and x + I' is I' as x lies in I'",
						GroupPremises(inI, value.At(x)).Rw(),
						By(
							classesOfI.At(x),
							inI,
							inIPrime,
							subgroupIPrime,
							quotient_group.LeftCosetIsSubgroupIffIn.Read(additive).At(vector, IPrime)))
				}))
			pointwise := a.Have(
				"so the classes the map kills are the classes of I'/J",
				"∀s:set(B). s ∈ «kernelClasses» ⇔ s ∈ left_cosets(M.add, I', J)",
				a.ForEach(func(s *Expr[Set[B]]) Action {
					return By(
						killedAreIPrimeClasses.At(s),
						iPrimeClassesKilled.At(s),
						group_homomorphism.InKernel.At(IPrime, classes, enlarge, s))
				}))
			kernel := a.Have(
				"the kernel of the map is the carrier of I'/J",
				"«kernelClasses» = left_cosets(M.add, I', J)",
				By(pointwise, set_basic.Extension))

			image := a.Have(
				"the classes of I/J are those of the members of I, and the map "+
					"takes the class of x to x + I', so its image is all of I/I'",
				"image(«enlarging», left_cosets(M.add, I, J)) = left_cosets(M.add, I, I')",
				Simp(Fwd(quotient_group.LeftCosetsImage.Read(additiveI)), Fwd(group.CosetMapDef)),
				Simp(Rev(set_image.ImageCompose), Fwd(functions.ComposeApply)),
				By(value, set_image.ImageCongruence))
			subquotient := a.Have(
				"restricted to the classes of I'/J, I/J has the operations of I'/J",
				"restrict_module(«iModJ», left_cosets(M.add, I', J)) = «iPrimeModJ»",
				Unfold(module_record.RestrictModuleDef),
				Unfold(submodule.QuotientModuleDef))
			whole := a.Have(
				"and restricted to its own classes, I/I' is itself",
				"restrict_module(«iModIPrime», left_cosets(M.add, I, I')) = «iModIPrime»",
				Unfold(module_record.RestrictModuleDef),
				Unfold(submodule.QuotientModuleDef))
			a.Show(
				"so the image is the whole of I/I', and I/J restricted to the kernel is I'/J",
				image.Rw(),
				kernel.Rw(),
				By(linear, whole, subquotient))
		}),
})}

// QuotientChainDim — over a field, colengths add along a chain of
// submodules J ⊆ I' ⊆ I: dim(I/J) = dim(I/I') + dim(I'/J). The map
// x + J ↦ x + I' carries I/J onto I/I', and I/J restricted to its kernel
// is I'/J (QuotientEnlargeMap); rank–nullity at it adds the two dimensions,
// and the image and the kernel of the finite-dimensional I/J are
// finite-dimensional.
var QuotientChainDim = quotientChainDimThm{family.Add(registry.ProofEntry{
	Name: "QuotientChainDim",
	Key:  "prop_3baa121a474243b5",
	Reading: "Only I/J is asked to be finite-dimensional; the two smaller quotients " +
		"are a quotient and a submodule of it. M itself may be infinite-dimensional, " +
		"which is how colengths of ideals and of fractional ideals are counted.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀I I' J:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"submodule(R, M, I)",
			"submodule(R, M, I')",
			"submodule(R, M, J)",
			"J ⊆ I'",
			"I' ⊆ I",
			"finite_dimensional(R, «iModJ»)",
		},
		Conclusion: "finite_dimensional(R, «iModIPrime») ∧ " +
			"finite_dimensional(R, «iPrimeModJ») ∧ " +
			"module_dim(R, «iModJ») = module_dim(R, «iModIPrime») + module_dim(R, «iPrimeModJ»)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			I, IPrime, J *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"I is a submodule of M",
				"so is I'",
				"so is J",
				"J lies in I'",
				"I' lies in I",
				"I/J is finite-dimensional")
			scalarsField, finiteQuotient := given[0], given[6]
			R := a.TermAs[RingOps[A]]("R")
			quotientByJ := a.TermAs[ModuleOps[A, Set[B]]]("«iModJ»")
			quotientByIPrime := a.TermAs[ModuleOps[A, Set[B]]]("«iModIPrime»")
			enlarge := a.TermAs[Fun[Set[B], Set[B]]]("«enlarging»")
			kernelSet := a.TermAs[Set[Set[B]]]("«kernelClasses»")
			enlarged := a.Conjuncts(
				GroupPremises(
					given[1],
					given[2],
					given[3],
					given[4],
					given[5],
					QuotientEnlargeMap.Read(moduleOn).At(I, IPrime, J)),
				"enlarging a class of J by I' is a linear map from I/J to I/I'",
				"its image is the whole of I/I'",
				"and I/J restricted to its kernel is I'/J")
			linear, image, kernel := enlarged[0], enlarged[1], enlarged[2]

			moduleQuotient := module_homomorphism.HomSource.Read(linear)
			counted := a.Have(
				"the kernel's and the image's dimensions sum to that of I/J",
				"module_dim(R, restrict_module(«iModJ», «kernelClasses»)) + "+
					"module_dim(R, restrict_module(«iModIPrime», image(«enlarging», left_cosets(M.add, I, J)))) = "+
					"module_dim(R, «iModJ»)",
				By(
					scalarsField,
					module_homomorphism.HomTarget.Read(linear),
					linear,
					finiteQuotient,
					RankNullity.Read(moduleQuotient).At(inv, quotientByIPrime, enlarge)))
			finiteImage := a.Have(
				"the image of the finite-dimensional I/J is finite-dimensional",
				"finite_dimensional(R, "+
					"    restrict_module(«iModIPrime», image(«enlarging», left_cosets(M.add, I, J))))",
				By(
					scalarsField,
					linear,
					finiteQuotient,
					ImageDim.At(R, inv, quotientByJ, quotientByIPrime, enlarge)))
			finiteKernel := a.Have(
				"and so is the kernel, a submodule of I/J",
				"finite_dimensional(R, restrict_module(«iModJ», «kernelClasses»))",
				By(
					scalarsField,
					finiteQuotient,
					module_homomorphism.KernelSubmodule.Read(linear),
					SubmoduleDim.Read(moduleQuotient).At(inv, kernelSet)))
			a.Show(
				"the kernel is I'/J and the image is I/I', so both are "+
					"finite-dimensional and their dimensions add up to that of I/J",
				kernel.Rw(),
				image.Rw(),
				By(
					counted,
					finiteImage,
					finiteKernel,
					nat_arith.AddSym.At(
						a.TermAs[Nat]("module_dim(R, «iPrimeModJ»)"), a.TermAs[Nat]("module_dim(R, «iModIPrime»)"))))
		}),
})}

// QuotientChainExtend — over a field, finite-dimensional layers stack: for
// submodules J ⊆ I' ⊆ I with I/I' and I'/J finite-dimensional, I/J is
// finite-dimensional of the sum of their dimensions. The map x + J ↦ x + I'
// has image I/I' and, as a restriction of I/J, kernel I'/J
// (QuotientEnlargeMap), so DimFiniteOfKernelAndImage makes I/J
// finite-dimensional, and QuotientChainDim adds the dimensions.
var QuotientChainExtend = quotientChainExtendThm{family.Add(registry.ProofEntry{
	Name: "QuotientChainExtend",
	Key:  "prop_a38fdd2b33485d19",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀I I' J:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"submodule(R, M, I)",
			"submodule(R, M, I')",
			"submodule(R, M, J)",
			"J ⊆ I'",
			"I' ⊆ I",
			"finite_dimensional(R, «iModIPrime»)",
			"finite_dimensional(R, «iPrimeModJ»)",
		},
		Conclusion: "finite_dimensional(R, «iModJ») ∧ " +
			"module_dim(R, «iModJ») = module_dim(R, «iModIPrime») + module_dim(R, «iPrimeModJ»)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			I, IPrime, J *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"I is a submodule of M",
				"so is I'",
				"so is J",
				"J lies in I'",
				"I' lies in I",
				"I/I' is finite-dimensional",
				"I'/J is finite-dimensional")
			scalarsField, finiteUpper, finiteLower := given[0], given[6], given[7]
			R := a.TermAs[RingOps[A]]("R")
			quotientByJ := a.TermAs[ModuleOps[A, Set[B]]]("«iModJ»")
			quotientByIPrime := a.TermAs[ModuleOps[A, Set[B]]]("«iModIPrime»")
			enlarge := a.TermAs[Fun[Set[B], Set[B]]]("«enlarging»")
			enlarged := a.Conjuncts(
				GroupPremises(
					given[1],
					given[2],
					given[3],
					given[4],
					given[5],
					QuotientEnlargeMap.Read(moduleOn).At(I, IPrime, J)),
				"enlarging a class of J by I' is a linear map from I/J to I/I'",
				"its image is the whole of I/I'",
				"and I/J restricted to its kernel is I'/J")
			linear, image, kernel := enlarged[0], enlarged[1], enlarged[2]
			finite := a.Have(
				"the kernel is I'/J and the image is I/I', both finite-dimensional, and so is I/J",
				"finite_dimensional(R, «iModJ»)",
				By(
					scalarsField,
					linear,
					kernel,
					image,
					finiteLower,
					finiteUpper,
					DimFiniteOfKernelAndImage.At(R, quotientByJ, inv, quotientByIPrime, enlarge)))
			a.Show(
				"the two layers add up to the dimension of I/J",
				By(hypotheses, finite, QuotientChainDim.Read(moduleOn).At(inv, I, IPrime, J)))
		}),
})}

// IsomorphismDim — over a field, an isomorphism carries a
// finite-dimensional module to a finite-dimensional one of the same
// dimension: f carries a finite basis E of M to a basis image(f, E) of
// N — independent as f is a one-to-one homomorphism, spanning as f maps
// the span of E, all of M, onto N — with as many members as E.
var IsomorphismDim = isomorphismDimThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismDim",
	Key:  "prop_3febf97b2b40fad5",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀inv:(A → A). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_isomorphism(R, M, N, f)",
			"finite_dimensional(R, M)",
		},
		Conclusion: "finite_dimensional(R, N) ∧ module_dim(R, N) = module_dim(R, M)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			inv *Arrow[A, A],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"f is an isomorphism of M onto N",
				"M is finite-dimensional")
			scalarsField, isomorphism, finiteM := given[0], given[1], given[2]
			onF := a.Conjuncts(
				a.Unfolded(isomorphism, module_homomorphism.ModuleIsomorphismDef),
				"f is a homomorphism of M into N",
				"f is one-to-one on M",
				"f maps M onto N")
			linear, oneToOne, onto := onF[0], onF[1], onF[2]
			moduleM := module_homomorphism.HomSource.Read(linear)
			moduleN := module_homomorphism.HomTarget.Read(linear)

			// A finite basis E of M.
			E, finiteBasis := a.UnpackAs[Set[B]](a.Unfolded(finiteM, FiniteDimensionalDef), "E")
			aboutE := a.Conjuncts(
				finiteBasis,
				"E is finite",
				"E is a basis of M")
			finiteE, basisE := aboutE[0], aboutE[1]
			ofBasis := a.Conjuncts(
				a.Unfolded(basisE, linear_independence.ModuleBasisDef),
				"E is independent",
				"E spans M")
			independentE, spansM := ofBasis[0], ofBasis[1]
			eInM := a.Have(
				"an independent set lies in M",
				"E ⊆ M.carrier",
				By(linear_independence.IndependentInCarrier.Read(independentE)))

			// Its image is a basis of N with as many members.
			image := a.TermAs[Set[C]]("image(f, E)")
			independent := a.Have(
				"the image of E is independent, f being a one-to-one homomorphism",
				"module_independent(R, N, image(f, E))",
				By(linear, oneToOne, independentE, linear_independence.IndependentImage.At(R, M, N, f, E)))
			spans := a.Have(
				"and spans N: f carries the span of E, all of M, onto the span of the image, and M onto N",
				"module_span(R, N, image(f, E)) = N.carrier",
				By(Normalized, linear, eInM, spansM, onto, linear_independence.HomSpan.At(R, M, N, f, E)))
			basisN := a.Have(
				"so the image of E is a basis of N",
				"module_basis(R, N, image(f, E))",
				By(independent, spans, linear_independence.ModuleBasisDef.At(R, N, image)))
			counted := a.Have(
				"f is one-to-one on E, so the image of E has as many members as E",
				"card(image(f, E)) = card(E)",
				By(
					oneToOne,
					eInM,
					finiteE,
					functions.InjectiveOnSubset.At(f, E, a.TermAs[Set[B]]("M.carrier")),
					cardinality.CardImageInj.At(f, E)))

			// The two dimensions.
			dimN := a.Have(
				"N has the finite basis image(f, E), so it is finite-dimensional of dimension its size",
				"finite_dimensional(R, N) ∧ module_dim(R, N) = card(image(f, E))",
				By(
					scalarsField,
					basisN,
					finiteE,
					finite_set.FiniteImage.At(f, E),
					FiniteBasisDim.Read(moduleN).At(inv, image)))
			dimM := a.Have(
				"M's dimension is the size of its finite basis E",
				"module_dim(R, M) = card(E)",
				By(scalarsField, basisE, finiteE, DimBasis.Read(moduleM).At(inv, E)))
			a.Show(
				"N is finite-dimensional, of the dimension of M",
				By(Normalized, dimN, counted, dimM))
		}),
})}

// IsomorphicDim — over a field, a module isomorphic to a
// finite-dimensional one is finite-dimensional of the same dimension: an
// isomorphism f of M onto N carries M's dimension to N (IsomorphismDim).
var IsomorphicDim = isomorphicDimThm{family.Add(registry.ProofEntry{
	Name: "IsomorphicDim",
	Key:  "prop_6412837a3a98bbdc",
	Reading: "module_on(R, M) and module_on(R, N) are not " +
		"read: the isomorphism, a homomorphism, carries both.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_on(R, N)",
			"module_isomorphic(R, M, N)",
			"finite_dimensional(R, M)",
		},
		Conclusion: "finite_dimensional(R, N) ∧ module_dim(R, N) = module_dim(R, M)",
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
				"M and N are isomorphic",
				"M is finite-dimensional")
			scalarsField, isomorphic, finiteM := given[0], given[2], given[3]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			f, isomorphism := a.UnpackAs[Fun[B, C]](
				a.Unfolded(isomorphic, module_homomorphism.ModuleIsomorphicDef), "f")
			a.Show(
				"the isomorphism f carries M's dimension to N",
				By(scalarsField, isomorphism, finiteM, IsomorphismDim.At(R, M, inv, N, f)))
		}),
})}

// FreeModuleDim — over a field, the free module on a finite set has the
// set's size as its dimension: the indicators of its points are a basis.
var FreeModuleDim = freeModuleDimThm{family.Add(registry.ProofEntry{
	Name: "FreeModuleDim",
	Key:  "prop_9ae49cf38eeccfdb",
	Reading: "The indicators of distinct points are distinct because one ≠ zero, " +
		"which the field supplies; over the zero ring they would all be the zero function.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀inv:(A → A). ∀S:set(D).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"finite(S)",
		},
		Conclusion: "module_dim(R, free_module_record(R, S)) = card(S)",
	},
		func(a *Argument, R *Expr[RingOps[A]], inv *Arrow[A, A], S *Expr[Set[D]], hypotheses Fact) {
			given := a.Conjuncts(
				hypotheses,
				"R is a field under inv",
				"S is finite")
			scalars := a.Unfolded(given[0], field.RingSubfieldDef)
			ring := a.Have(
				"the scalar ring of the field is R itself",
				"comm_ring_on(R)",
				By(
					field.RingOn.Read(scalars),
					field.FieldRingDef,
					module_record.RestrictRingDef.At(R, a.TermAs[Set[A]]("R.carrier")),
					module_record.RestrictRingCarrier.At(R)))
			zero, one := a.TermAs[A]("R.zero"), a.TermAs[A]("R.one")
			injective := a.Have(
				"distinct points of S have distinct indicators",
				"injective_on(S, delta_at)",
				Derive(func(b *Argument) {
					b.Do(Unfold(functions.InjectiveOnDef))
					x, y := b.FixAs[D]("x"), b.FixAs[D]("y")
					same := b.Assume()
					b.Show(
						"equal indicators agree at x, where distinct indices would give one equal to zero",
						By(
							same,
							field.OneNotZeroOn.Read(scalars),
							free_module.DeltaAtDef.At(zero, one, x, x),
							free_module.DeltaAtDef.At(zero, one, y, x)))
				}))
			E, Edef := a.LetAs[Set[Fun[D, A]]]("E", "image(delta_at, S)")
			delta := a.TermAs[Fun2[D, D, A]]("delta_at")
			a.Show(
				"the dimension counts the distinct indicators of S",
				CalcEq(
					Leg(
						a.TermAs[Nat]("card(E)"),
						"E is a finite basis of the free module",
						By(
							Normalized,
							given[1],
							Edef,
							given[0],
							free_module.FreeModuleOn.Read(ring).At(S),
							free_module.DeltaAtBasis.Read(ring).At(S),
							finite_set.FiniteImage.At(delta, S),
							DimBasis.At(R, a.TermAs[ModuleOps[A, Fun[D, A]]]("free_module_record(R, S)"), inv, E))),
					FinalLeg(
						"the injective indicator map counts one basis vector per point of S",
						By(Normalized, given[1], Edef, injective, cardinality.CardImageInj.At(delta, S))),
				))
		}),
})}

// FreeModuleFiniteDim — over a field, the free module on a finite set S is
// finite-dimensional, of dimension |S|: the point masses of S are a finite
// basis of it (DeltaAtBasis), and FreeModuleDim counts them.
var FreeModuleFiniteDim = freeModuleFiniteDimThm{family.Add(registry.ProofEntry{
	Name: "FreeModuleFiniteDim",
	Key:  "prop_d7d931a1c79069e9",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀inv:(A → A). ∀S:set(D).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"finite(S)",
		},
		Conclusion: "finite_dimensional(R, free_module_record(R, S)) ∧ " +
			"module_dim(R, free_module_record(R, S)) = card(S)",
	}, func(
		arg *Argument,
		R *Expr[RingOps[A]],
		inv *Arrow[A, A],
		S *Expr[Set[D]],
		scalarsField, finiteS Fact,
	) {
		ring := arg.Have(
			"the scalar ring of the field is R itself",
			"comm_ring_on(R)",
			By(
				field.RingOn.Read(arg.Unfolded(scalarsField, field.RingSubfieldDef)),
				field.FieldRingDef,
				module_record.RestrictRingDef.At(R, arg.TermAs[Set[A]]("R.carrier")),
				module_record.RestrictRingCarrier.At(R)))
		masses := arg.TermAs[Set[Fun[D, A]]]("image(delta_at(R.zero, R.one), S)")
		arg.Show(
			"the point masses of S are a finite basis, as many as the points of S",
			By(
				scalarsField,
				finiteS,
				free_module.FreeModuleOn.Read(ring).At(S),
				free_module.DeltaAtBasis.Read(ring).At(S),
				finite_set.FiniteImage.At(arg.TermAs[Fun2[D, D, A]]("delta_at(R.zero, R.one)"), S),
				FiniteBasisDim.At(R, arg.TermAs[ModuleOps[A, Fun[D, A]]]("free_module_record(R, S)"), inv, masses),
				FreeModuleDim.At(R, inv, S)))
	}),
})}

// ---------------------------------------------------------------------------
// A chain of images
// ---------------------------------------------------------------------------

// ImageChainStabilizes — over a field, the images of a
// finite-dimensional module under the iterates of an endomorphism
// stop shrinking: each image is a submodule inside the one before, so
// their dimensions never grow; where the dimension is least the next
// image has the same dimension inside it and is equal to it, and from
// there the recursion repeats itself.
var ImageChainStabilizes = imageChainStabilizesThm{family.Add(registry.ProofEntry{
	Name: "ImageChainStabilizes",
	Key:  "prop_feaa6f316f973aeb",
	Reading: "The chain is given by its recursion, W(0) = M.carrier and W(n + 1) = image(f, " +
		"W(n)), which fixes W: W(n) is f applied n times to M. The field is load-bearing through " +
		"the dimension: over ℤ, f = multiplication by 2 on ℤ has the images 2ⁿℤ, which never stop.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀f:(B → B). ∀W:(num → set(B)).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"finite_dimensional(R, M)",
			"module_homomorphism(R, M, M, f)",
			"W(0) = M.carrier",
			"∀n:num. W(n + 1) = image(f, W(n))",
		},
		Conclusion: "∃m:num. ∀n:num. m ≤ n ⇒ W(n) = W(m)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			f *Arrow[B, B],
			W *Arrow[Nat, Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"M is finite-dimensional",
				"f is an endomorphism of M",
				"the chain starts at M",
				"each term is the image of the one before")
			scalarsField, finiteM, endo, start, next := given[0], given[1], given[2], given[3], given[4]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")

			// An induction step reaches W(suc(n)) where the recursion speaks of
			// W(n + 1); nat_arith.Add1, suc(n) = n + 1, carries the one to the other.
			submodules := a.Have(
				"every W(n) is a submodule of M",
				"∀n:num. submodule(R, M, W(n))",
				Derive(func(b *Argument) {
					b.Induct("n")
					b.Base(
						"W(0) is M's carrier",
						start.Rw(),
						By(submodule.CarrierSubmodule.Read(moduleOn)))
					b.Step(
						"W(n + 1) is the image of the submodule W(n)",
						func(c *Argument, ih Fact) {
							n := c.TermAs[Nat]("n")
							c.Show(
								"a homomorphism carries the submodule W(n) to a submodule",
								By(
									Normalized,
									ih,
									endo,
									module_homomorphism.HomImageSubmodule.At(R, M, M, f, W.Apply(n)),
									next.At(n),
									nat_arith.Add1.At(n)))
						})
				}))
			descending := a.Have(
				"each W(n + 1) lies inside W(n)",
				"∀n:num. W(n + 1) ⊆ W(n)",
				Derive(func(b *Argument) {
					b.Induct("n")
					b.Base(
						"W(1) is a submodule of M, so it lies in M's carrier, which is W(0)",
						func(c *Argument) {
							one := c.TermAs[Nat]("0 + 1")
							c.Show(
								"W(1) lies in W(0)",
								start.Rw(),
								By(submodules.At(one), submodule.SubmoduleSubset.At(R, M, W.Apply(one))))
						})
					b.Step(
						"f keeps the inclusion: W(n + 2) = f(W(n + 1)) ⊆ f(W(n)) = W(n + 1)",
						func(c *Argument, ih Fact) {
							n, sucN := c.TermAs[Nat]("n"), c.TermAs[Nat]("suc(n)")
							c.Show(
								"the image of the smaller set is the smaller image",
								By(
									Normalized,
									ih,
									next.At(sucN),
									next.At(n),
									nat_arith.Add1.At(n),
									set_image.ImageSubset.At(f, W.Apply(c.TermAs[Nat]("n + 1")), W.Apply(n))))
						})
				}))

			// Each W(n) read as a module of its own, W(n + 1) a submodule of it.
			modules := a.Have(
				"each W(n) is a module over R",
				"∀n:num. module_on(R, restrict_module(M, W(n)))",
				a.ForEach(func(n *Expr[Nat]) Action {
					return By(submodules.At(n), submodule.SubmoduleModuleOn.Read(moduleOn).At(W.Apply(n)))
				}))
			finite := a.Have(
				"each W(n) is finite-dimensional",
				"∀n:num. finite_dimensional(R, restrict_module(M, W(n)))",
				a.ForEach(func(n *Expr[Nat]) Action {
					return By(scalarsField, finiteM, submodules.At(n), SubmoduleDim.Read(moduleOn).At(inv, W.Apply(n)))
				}))
			inner := a.Have(
				"W(n + 1) is a submodule of W(n)",
				"∀n:num. submodule(R, restrict_module(M, W(n)), W(n + 1))",
				Derive(func(b *Argument) {
					n, after := b.FixAs[Nat]("n"), b.TermAs[Nat]("n + 1")
					b.Show(
						"a submodule of M inside W(n)",
						By(
							descending.At(n),
							submodules.At(after),
							submodule.SubmoduleRestrict.At(R, M, W.Apply(n), W.Apply(after))))
				}))
			shrinking := a.Have(
				"the dimensions never grow",
				"∀n:num. module_dim(R, restrict_module(M, W(n + 1))) ≤ module_dim(R, restrict_module(M, W(n)))",
				Derive(func(b *Argument) {
					n, after := b.FixAs[Nat]("n"), W.Apply(b.TermAs[Nat]("n + 1"))
					b.Show(
						"a submodule of the finite-dimensional W(n) has no larger dimension",
						By(
							module_record.RestrictModuleTwice.At(M, W.Apply(n), after),
							modules.At(n),
							finite.At(n),
							inner.At(n),
							scalarsField,
							SubmoduleDim.At(R, b.TermAs[ModuleOps[A, B]]("restrict_module(M, W(n))"), inv, after)))
				}))

			// Where the dimension is least, it does not drop at the next step, and the chain pauses there.
			m, least := a.ObtainAs[Nat](
				"some W(m) has the least dimension in the chain",
				"∃m:num. ∀j:num. module_dim(R, restrict_module(M, W(m))) ≤ module_dim(R, restrict_module(M, W(j)))",
				By(
					nat_order.WellOrdering.At(
						a.TermAs[Set[Nat]]("λk:num. ∃i:num. module_dim(R, restrict_module(M, W(i))) = k")),
					nat_order.NotLessThan))
			mNext := a.TermAs[Nat]("m + 1")
			pause := a.Have(
				"so the dimension does not drop from W(m) to W(m + 1)",
				"module_dim(R, restrict_module(M, W(m + 1))) = module_dim(R, restrict_module(M, W(m)))",
				By(shrinking.At(m), least.At(mNext), nat_order.LessEqAntisym))
			settles := a.Have(
				"W(m + 1), a submodule of W(m) of the same dimension, is W(m)",
				"W(m + 1) = W(m)",
				By(
					module_record.RestrictModuleTwice.At(M, W.Apply(m), W.Apply(mNext)),
					modules.At(m),
					finite.At(m),
					inner.At(m),
					scalarsField,
					pause,
					SubmoduleDimEq.At(R, a.TermAs[ModuleOps[A, B]]("restrict_module(M, W(m))"), inv, W.Apply(mNext))))
			stays := a.Have(
				"from m on the chain stays at W(m), by induction on the distance d",
				"∀d:num. W(m + d) = W(m)",
				Derive(func(b *Argument) {
					b.Induct("d")
					b.Base(
						"at distance 0 it is W(m)",
						By(Normalized, nat_arith.AddZero.At(m)))
					b.Step(
						"one step further the recursion repeats the pause",
						func(c *Argument, ih Fact) {
							md := c.TermAs[Nat]("m + d")
							c.Show(
								"W(m + d + 1) = f(W(m + d)) = f(W(m)) = W(m + 1) = W(m)",
								Simp(Fwd(nat_arith.AddSuc), Fwd(nat_arith.Add1)),
								CalcEq(
									Leg(
										c.TermAs[Set[B]]("image(f, W(m + d))"),
										"the recursion at m + d",
										By(next.At(md))),
									Leg(
										c.TermAs[Set[B]]("image(f, W(m))"),
										"W(m + d) is W(m)",
										ih.Rw(),
										Basic()),
									Leg(
										W.Apply(mNext),
										"the recursion at m",
										By(Normalized, next.At(m))),
									FinalLeg(
										"and the chain pauses at m",
										By(settles)),
								))
						})
				}))
			a.Take(m)
			n := a.FixAs[Nat]("n")
			atLeast := a.Assume()
			d, distance := a.ObtainAs[Nat](
				"n is m plus some distance d",
				"∃d:num. n = m + d",
				By(atLeast, nat_order.LessEqExists.At(n, m)))
			a.Show(
				"and at that distance the chain is W(m)",
				By(Normalized, distance, stays.At(d)))
		}),
})}

// BoundedChainUnion — over a field, a module covered by an increasing chain
// of submodules W(0) ⊆ W(1) ⊆ … of dimension at most b is
// finite-dimensional, of dimension at most b: some W(c) has the largest
// dimension; a later W(e) holds W(c) as a submodule of the same dimension,
// so the chain stays at W(c), and every member of M, lying in some W(d),
// lies in W(c).
var BoundedChainUnion = boundedChainUnionThm{family.Add(registry.ProofEntry{
	Name: "BoundedChainUnion",
	Key:  "prop_df329aeffb7aeb2e",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀W:(num → set(B)). ∀b:num.",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"∀d:num. submodule(R, M, W(d))",
			"∀d e:num. d ≤ e ⇒ W(d) ⊆ W(e)",
			"∀d:num. " +
				"    finite_dimensional(R, restrict_module(M, W(d))) ∧ module_dim(R, restrict_module(M, W(d))) ≤ b",
			"∀u:B. u ∈ M.carrier ⇒ ∃d:num. u ∈ W(d)",
		},
		Conclusion: "finite_dimensional(R, M) ∧ module_dim(R, M) ≤ b",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			W *Arrow[Nat, Set[B]],
			b *Expr[Nat],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"every W(d) is a submodule of M",
				"the chain increases",
				"each W(d) is finite-dimensional, of dimension at most b",
				"every member of M lies in some W(d)")
			scalarsField, submodules, increasing, bounded, covering :=
				given[0], given[1], given[2], given[3], given[4]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")

			// The dimensions are bounded by b, so one of them is largest.
			c, largest := a.ObtainAs[Nat](
				"some W(c) has the largest dimension in the chain",
				"∃c:num. ∀d:num. module_dim(R, restrict_module(M, W(d))) ≤ module_dim(R, restrict_module(M, W(c)))",
				By(
					bounded,
					nat_order.MaximumExists.At(
						a.TermAs[Set[Nat]]("λx:num. ∃d:num. x = module_dim(R, restrict_module(M, W(d)))"))))
			stays := a.Have(
				"past c the chain stays at W(c)",
				"∀e:num. c ≤ e ⇒ W(e) = W(c)",
				Derive(func(sub *Argument) {
					e := sub.FixAs[Nat]("e")
					later := sub.Assume()
					outer := sub.TermAs[ModuleOps[A, B]]("restrict_module(M, W(e))")
					inner := sub.Have(
						"W(c) is a submodule of W(e), the chain increasing",
						"submodule(R, restrict_module(M, W(e)), W(c))",
						By(
							submodules.At(c),
							increasing.At(c, e),
							later,
							submodule.SubmoduleRestrict.At(R, M, W.Apply(e), W.Apply(c))))
					outerModule := sub.Have(
						"W(e) is a module over R",
						"module_on(R, restrict_module(M, W(e)))",
						By(submodules.At(e), submodule.SubmoduleModuleOn.Read(moduleOn).At(W.Apply(e))))
					atMost := sub.Have(
						"so W(c) has no larger dimension than W(e)",
						"module_dim(R, restrict_module(M, W(c))) ≤ module_dim(R, restrict_module(M, W(e)))",
						By(
							Normalized,
							outerModule,
							scalarsField,
							bounded.At(e),
							inner,
							SubmoduleDim.At(R, outer, inv, W.Apply(c)),
							module_record.RestrictModuleTwice.At(M, W.Apply(e), W.Apply(c))))
					same := sub.Have(
						"and no smaller, W(c) being largest: the two dimensions agree",
						"module_dim(R, restrict_module(restrict_module(M, W(e)), W(c))) = "+
							"module_dim(R, restrict_module(M, W(e)))",
						Simp(Fwd(module_record.RestrictModuleTwice)),
						ByArith(atMost, largest.At(e)))
					sub.Show(
						"a submodule of the finite-dimensional W(e) of its dimension is W(e)",
						By(
							Normalized,
							outerModule,
							scalarsField,
							bounded.At(e),
							inner,
							same,
							SubmoduleDimEq.At(R, outer, inv, W.Apply(c))))
				}))
			covered := a.Have(
				"every member of M lies in W(c)",
				"∀u:B. u ∈ M.carrier ⇒ u ∈ W(c)",
				Derive(func(sub *Argument) {
					u := sub.FixAs[B]("u")
					inM := sub.Assume()
					index, inW := sub.UnpackAs[Nat](GroupPremises(inM, covering.At(u)), "d")
					past := sub.TermAs[Nat]("d + c")
					bounds := sub.Have(
						"d and c are at most d + c",
						"d ≤ d + c ∧ c ≤ d + c",
						ByArith())
					sub.Show(
						"u lies in W(d), inside W(d + c), which is W(c)",
						BySets(inW, bounds, increasing.At(index, past), stays.At(past)))
				}))
			whole := a.Have(
				"so W(c) is all of M",
				"W(c) = M.carrier",
				BySets(covered, submodules.At(c), submodule.SubmoduleSubset.At(R, M, W.Apply(c))))
			a.Show(
				"M is W(c), finite-dimensional of dimension at most b",
				By(whole, bounded.At(c), module_record.RestrictModuleCarrier.At(M)))
		}),
})}

// ---------------------------------------------------------------------------
// An ideal of colength one
// ---------------------------------------------------------------------------

// ScalarPowerImagesStabilize — over a field k inside S, a module
// finite-dimensional over k has images under the powers of a scalar c of
// S that stop shrinking: scaling by c is a k-linear endomorphism, and the
// images of its iterates are the images of the powers of c.
var ScalarPowerImagesStabilize = scalarPowerImagesStabilizeThm{family.Add(registry.ProofEntry{
	Name: "ScalarPowerImagesStabilize",
	Key:  "prop_48939d785d8c240c",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S k:set(A). ∀inv:(A → A). ∀M:module_ops(A, B). ∀c:A.",
		Hypotheses: []string{
			"module_on(restrict_ring(R, S), M)",
			"ring_subfield(R, inv, k)",
			"k ⊆ S",
			"finite_dimensional(restrict_ring(R, k), M)",
			"c ∈ S",
		},
		Conclusion: "∃N:num. ∀n:num. " +
			"    N ≤ n ⇒ " +
			"    image(λu:B. monoid_pow(R.mul, R.one, c, n) • u, M.carrier) = " +
			"    image(λu:B. monoid_pow(R.mul, R.one, c, N) • u, M.carrier)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S, k *Expr[Set[A]],
			inv *Arrow[A, A],
			M *Expr[ModuleOps[A, B]],
			c *Expr[A],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"M is a module over S",
				"k is a field under R's operations",
				"k lies in S",
				"M is finite-dimensional over k",
				"c is a scalar of S")
			overS, subfieldK, kS, finite, cS := parts[0], parts[1], parts[2], parts[3], parts[4]
			fieldK := a.Unfolded(subfieldK, field.RingSubfieldDef)
			fieldRing := a.Simplified(field.RingOn.Read(fieldK), Fwd(field.FieldRingDef))
			subringK := a.Have(
				"k, a commutative ring under R's operations, is a subring of S",
				"subring(restrict_ring(R, S), k)",
				By(
					comm_ring.SubringRingOn.Read(module.RingOn.Read(overS)).At(k),
					module_record.RestrictRingTwice.At(R, S, k),
					fieldRing,
					module_record.RestrictRingDef.At(R, k),
					kS))
			linear := a.Have(
				"scaling by c is a k-linear endomorphism of M",
				"module_homomorphism(restrict_ring(R, k), M, M, λu:B. c • u)",
				By(
					Normalized,
					module_homomorphism.ScalingLinearOverSubring.At(
						a.TermAs[RingOps[A]]("restrict_ring(R, S)"), S, k, M, c),
					module_record.RestrictRingTwice.At(R, S, S),
					module_record.RestrictRingTwice.At(R, S, k),
					overS,
					subringK,
					kS,
					cS))
			start := a.Have(
				"the zeroth power of c is one, which fixes every vector, so its image is all of M",
				"image(λu:B. monoid_pow(R.mul, R.one, c, 0) • u, M.carrier) = M.carrier",
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				By(
					set_image.ImageCongruence.At(
						a.TermAs[Fun[B, B]]("λu:B. R.one • u"),
						a.TermAs[Fun[B, B]]("λu:B. u"),
						a.TermAs[Set[B]]("M.carrier")),
					module.SmulOne.Read(overS),
					set_image.ImageIdentity))
			next := a.Have(
				"each image is the one before, scaled by c",
				"∀n:num. "+
					"    image(λu:B. monoid_pow(R.mul, R.one, c, n + 1) • u, M.carrier) = "+
					"    image(λu:B. c • u, image(λu:B. monoid_pow(R.mul, R.one, c, n) • u, M.carrier))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.Show(
						"c^(n + 1) • u = c • (c^n • u), the powers of c lying in S",
						Simp(
							Rev(nat_arith.Add1),
							Fwd(comm_monoid.MonoidPowDef),
							Rev(set_image.ImageCompose),
							Fwd(functions.ComposeApply)),
						By(
							set_image.ImageCongruence,
							module.SmulMul.Read(overS),
							cS,
							comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(module.RingOn.Read(overS)))))
				}))
			a.Show(
				"the images of the iterates of an endomorphism of a finite-dimensional space stop shrinking",
				By(
					ImageChainStabilizes.At(
						a.TermAs[RingOps[A]]("restrict_ring(R, k)"),
						M,
						inv,
						a.TermAs[Fun[B, B]]("λu:B. c • u"),
						a.TermAs[Fun2[Nat, B, Bool]]("λn:num. image(λu:B. monoid_pow(R.mul, R.one, c, n) • u, M.carrier)")),
					module_homomorphism.HomSource.Read(linear),
					subfieldK,
					field.RingSubfieldRestrict.At(R, k, inv, k),
					finite,
					linear,
					start,
					next))
		}),
})}

// IdealQuotientModuleOn — over a field k inside a commutative ring R, R is
// a module over k, an ideal I a submodule of it, and R modulo I a module
// over k: k is a subring of R, so R scaled by k is R as a module over
// itself with fewer scalars, and the ideal I, a submodule of R over R, is
// one over k as well.
var IdealQuotientModuleOn = idealQuotientModuleOnThm{family.Add(registry.ProofEntry{
	Name: "IdealQuotientModuleOn",
	Key:  "prop_c2224f02829bfd0",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀k:set(A). ∀inv:(A → A). ∀I:set(A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"ring_subfield(R, inv, k)",
			"k ⊆ R.carrier",
			"ring_ideal(R, I)",
		},
		Conclusion: "module_on(restrict_ring(R, k), regular_module(R)) ∧ " +
			"submodule(restrict_ring(R, k), regular_module(R), I) ∧ " +
			"module_on(restrict_ring(R, k), «Q»)",
		Abbrev: Abbrev{
			{Name: "Q", Text: "quotient_module(regular_module(R), I)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			I *Expr[Set[A]],
			given Fact,
		) {
			premises := a.Conjuncts(
				given,
				"R is a commutative ring",
				"k is a field",
				"k lies in R",
				"I is an ideal")
			ring, scalars, kInR, ideal := premises[0], premises[1], premises[2], premises[3]
			K, V := a.TermAs[RingOps[A]]("restrict_ring(R, k)"), a.TermAs[ModuleOps[A, A]]("regular_module(R)")
			subfield := a.Have(
				"the scalar field is a subring of R",
				"subring(R, k)",
				By(scalars, kInR, field.RingSubfieldSubring.At(R, inv, k)))
			quotientData := a.Have(
				"R and I are modules over k",
				"module_on(restrict_ring(R, k), regular_module(R)) ∧ "+
					"submodule(restrict_ring(R, k), regular_module(R), I)",
				By(
					ideal,
					subfield,
					kInR,
					module.RegularModuleOverSubring.Read(ring).At(k),
					submodule.IdealIffRegularSubmodule.At(R, I),
					submodule.SubmoduleRestrictScalars.At(R, V, I, K),
					module_record.RestrictRingDef.At(R, k)))
			a.Show(
				"so their quotient is a k-module",
				By(quotientData, submodule.QuotientModuleOn.At(K, V, I)))
		}),
})}

// QuotientOneNonzero — modulo a proper ideal I of a commutative ring R,
// the class of one is a nonzero vector of R/I: one lies in R, so its class
// is a coset of I, and that class is I, the quotient's zero, only when one
// lies in I.
var QuotientOneNonzero = quotientOneNonzeroThm{family.Add(registry.ProofEntry{
	Name: "QuotientOneNonzero",
	Key:  "prop_299def9291964eea",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀I:set(A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"ring_ideal(R, I)",
			"R.one ∉ I",
		},
		Conclusion: "left_coset(R.add, R.one, I) ∈ «Q».carrier ∧ left_coset(R.add, R.one, I) ≠ «Q».zero",
		Abbrev: Abbrev{
			{Name: "Q", Text: "quotient_module(regular_module(R), I)"},
		},
	},
		func(a *Argument, R *Expr[RingOps[A]], I *Expr[Set[A]], given Fact) {
			premises := a.Conjuncts(
				given,
				"R is a commutative ring",
				"I is an ideal",
				"I does not hold one")
			ring, ideal, proper := premises[0], premises[1], premises[2]
			one := a.TermAs[A]("R.one")
			additiveOps := a.TermAs[quotient_group.GroupOps[A]]("additive_group(R)")
			a.Show(
				"one lies in R, so its class is a coset of I, and that class is I only when one lies in I",
				Simp(Fwd(module_record.RegularModuleDef), Fwd(submodule.QuotientModuleDef)),
				By(
					comm_ring.OneIn.Read(ring),
					abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring)),
					ring,
					ideal,
					proper,
					ring_ideal.IdealSubset.At(R, I),
					quotient_ring.CosetEqIdealIff.At(R, I, one),
					quotient_group.LeftCosetInLeftCosets.At(additiveOps, I, one),
					module_record.AdditiveGroupDef.At(R)))
		}),
})}

// FieldResiduesColength — over a field k inside a commutative ring R, R
// modulo an ideal I that is all of R, or the ideal of a k-rational point
// of R, is finite-dimensional over k, of dimension zero for I = R and one
// otherwise: the quotient is a k-module;
// for I = R it is the one class I, the zero module; otherwise the class of
// one is not zero, and the residue c of a representative x makes the class
// of x the multiple c of the class of one, so that class spans a line
// (LineDim).
var FieldResiduesColength = fieldResiduesColengthThm{family.Add(registry.ProofEntry{
	Name: "FieldResiduesColength",
	Key:  "prop_19c64f72a7631bd6",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀k:set(A). ∀inv:(A → A). ∀I:set(A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"ring_subfield(R, inv, k)",
			"k ⊆ R.carrier",
			"ring_ideal(R, I)",
			"I = R.carrier ∨ rational_ideal(R, k, R.carrier, I)",
		},
		Conclusion: "finite_dimensional(restrict_ring(R, k), «Q») ∧ " +
			"module_dim(restrict_ring(R, k), «Q») = COND(I = R.carrier, 0, 1)",
		Abbrev: Abbrev{
			{Name: "Q", Text: "quotient_module(regular_module(R), I)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			I *Expr[Set[A]],
			given Fact,
		) {
			premises := a.Conjuncts(
				given,
				"R is a commutative ring",
				"k is a field",
				"k lies in R",
				"I is an ideal",
				"I is all of R or the ideal of a k-rational point")
			ring, scalars, kInR, ideal, zeroOrResidues :=
				premises[0], premises[1], premises[2], premises[3], premises[4]
			// k under the restriction of R to it: the scalar field the
			// dimension laws below are read at.
			scalarField := a.Have(
				"k is a field under the operations of R restricted to k, which are R's",
				"ring_subfield(restrict_ring(R, k), inv, k)",
				By(scalars, field.RingSubfieldRestrict.At(R, k, inv, k)))
			K, V, Q :=
				a.TermAs[RingOps[A]]("restrict_ring(R, k)"),
				a.TermAs[ModuleOps[A, A]]("regular_module(R)"),
				a.TermAs[ModuleOps[A, Set[A]]]("«Q»")
			one := a.TermAs[A]("R.one")
			additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
			additiveOps := a.TermAs[quotient_group.GroupOps[A]]("additive_group(R)")
			quotient := a.Conjuncts(
				a.Have(
					"R, I and R modulo I are modules over k",
					"module_on(restrict_ring(R, k), regular_module(R)) ∧ "+
						"submodule(restrict_ring(R, k), regular_module(R), I) ∧ "+
						"module_on(restrict_ring(R, k), «Q»)",
					By(ring, scalars, kInR, ideal, IdealQuotientModuleOn.At(R, k, inv, I))),
				"R is a module over k",
				"I is a submodule over k",
				"the quotient is a module over k")
			quotientOn := quotient[2]
			a.Cases(a.TermAs[Bool]("I = R.carrier"))
			a.When(
				"the whole ideal gives the zero quotient",
				func(b *Argument, whole Fact) {
					zeroCarrier := b.Have(
						"every quotient class is its zero class",
						"«Q».carrier = {«Q».zero}",
						Simp(Fwd(module_record.RegularModuleDef), Fwd(submodule.QuotientModuleDef)),
						Simp(Fwd(set_basic.Extension)),
						Derive(func(d *Argument) {
							X := d.FixAs[Set[A]]("X")
							d.Show(
								"every class is I",
								BySets(
									additive,
									ring,
									whole,
									ideal,
									At(quotient_ring.CosetEqIdealIff, R, I),
									quotient_ring.IdealSubgroup.At(R, I),
									quotient_group.InLeftCosets.At(additiveOps, I, X),
									quotient_group.SubgroupInLeftCosets.At(additiveOps, I)))
						}))
					zeroRestriction := b.Have(
						"restricting this quotient to zero changes nothing",
						"restrict_module(«Q», {«Q».zero}) = «Q»",
						zeroCarrier.RwRev(),
						Cite(module_record.RestrictModuleCarrier))
					zeroClass := b.Have(
						"the quotient zero is I",
						"«Q».zero = I",
						Simp(Fwd(submodule.QuotientModuleDef)),
						Basic())
					b.Show(
						"the zero quotient has finite dimension zero",
						By(scalarField, whole, zeroClass, zeroRestriction, quotientOn, ZeroSubmoduleDim.At(K, inv, Q)))
				})
			a.Otherwise(
				"a proper ideal gives a one-dimensional residue quotient",
				func(b *Argument, proper Fact) {
					rational := b.Have(
						"a proper I is the ideal of a k-rational point",
						"rational_ideal(R, k, R.carrier, I)",
						By(Normalized, proper, zeroOrResidues))
					residue := b.Conjuncts(
						b.Unfolded(rational, quotient_ring.RationalIdealDef),
						"I is an ideal of R",
						"one stays outside I",
						"every element has a scalar residue")
					e := b.TermAs[Set[A]]("left_coset(R.add, R.one, I)")
					nonzero := b.Have(
						"the class of one is a nonzero quotient vector",
						"left_coset(R.add, R.one, I) ∈ «Q».carrier ∧ left_coset(R.add, R.one, I) ≠ «Q».zero",
						By(ring, ideal, residue[1], QuotientOneNonzero.At(R, I)))
					spanning := b.Have(
						"each quotient vector is a scalar multiple of the class of one",
						Statement{
							Binders:    "∀X:set(A).",
							Hypotheses: []string{"X ∈ «Q».carrier"},
							Conclusion: "∃c:A. c ∈ restrict_ring(R, k).carrier ∧ X = «Q».smul(c, left_coset(R.add, R.one, I))",
						},
						Derive(func(d *Argument) {
							X := d.FixAs[Set[A]]("X")
							inQ := d.Assume()
							classMember := d.Simplified(
								inQ,
								Fwd(module_record.RegularModuleDef),
								Fwd(submodule.QuotientModuleDef))
							x, representative := d.ObtainAs[A](
								"choose a representative of X",
								"∃x:A. X = left_coset(R.add, x, I) ∧ x ∈ R.carrier",
								By(
									ideal,
									classMember,
									quotient_group.InLeftCosets.Read(additive).At(I, X),
									ring_ideal.IdealSubset.At(R, I),
									module_record.AdditiveGroupDef.At(R)))
							c, residueOfX := d.ObtainAs[A](
								"choose the scalar residue of this representative",
								"∃c:A. c ∈ k ∧ x + -c ∈ I",
								By(residue[2], representative))
							cInR := d.Have(
								"the residue scalar lies in R",
								"c ∈ R.carrier",
								BySets(kInR, residueOfX))
							classOfC := d.Have(
								"the residue scalar represents the same quotient class",
								"X = left_coset(R.add, c, I)",
								By(
									Normalized,
									ring,
									ideal,
									cInR,
									representative,
									residueOfX,
									quotient_ring.CosetEqIff.At(R, I, x, c),
									comm_ring.SubAddNegOn.Read(ring).AsFact().At(x, c)))
							unit := d.Have(
								"multiplication by one fixes the scalar",
								"c * R.one = c",
								ByArith(ring, cInR))
							d.Show(
								"the class is c times the class of one",
								Simp(
									Fwd(module_record.RegularModuleDef),
									Fwd(module_record.RestrictRingDef),
									Fwd(submodule.QuotientModuleDef)),
								Witness(c),
								By(
									comm_ring.OneIn.Read(ring),
									unit,
									classOfC,
									quotient[0],
									quotient[1],
									residueOfX,
									submodule.QuotientSmulCoset.At(K, V, I, c, one),
									module_record.RegularModuleDef.At(R),
									module_record.RestrictRingDef.At(R, k)))
						}))
					b.Show(
						"the nonzero spanning vector gives finite dimension one",
						By(scalarField, proper, spanning, quotientOn, nonzero, LineDim.At(K, Q, inv, e)))
				})
		}),
})}

// IdealColengthOneRational — over a field k inside a commutative ring R, an
// ideal I with R/I of dimension one over k is the ideal of a k-rational point,
// the converse of FieldResiduesColength. I misses one, since R/R has dimension
// zero, so the class of one is a nonzero vector and by itself a basis of the
// line R/I; each class is then a multiple c of it, which is the class of c, and
// c is the residue of every representative.
var IdealColengthOneRational = idealColengthOneRationalThm{family.Add(registry.ProofEntry{
	Name: "IdealColengthOneRational",
	Key:  "prop_cbbbb4c828187148",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀k:set(A). ∀inv:(A → A). ∀I:set(A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"ring_subfield(R, inv, k)",
			"k ⊆ R.carrier",
			"ring_ideal(R, I)",
			"finite_dimensional(restrict_ring(R, k), «Q»)",
			"module_dim(restrict_ring(R, k), «Q») = 1",
		},
		Conclusion: "rational_ideal(R, k, R.carrier, I)",
		Abbrev: Abbrev{
			{Name: "Q", Text: "quotient_module(regular_module(R), I)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			I *Expr[Set[A]],
			given Fact,
		) {
			premises := a.Conjuncts(
				given,
				"R is a commutative ring",
				"k is a field",
				"k lies in R",
				"I is an ideal",
				"R modulo I is finite-dimensional over k",
				"and of dimension one")
			ring, scalars, kInR, ideal, finite, line :=
				premises[0], premises[1], premises[2], premises[3], premises[4], premises[5]
			K, V, Q :=
				a.TermAs[RingOps[A]]("restrict_ring(R, k)"),
				a.TermAs[ModuleOps[A, A]]("regular_module(R)"),
				a.TermAs[ModuleOps[A, Set[A]]]("«Q»")
			one := a.TermAs[A]("R.one")
			e := a.TermAs[Set[A]]("left_coset(R.add, R.one, I)")
			single := a.TermAs[Set[Set[A]]]("{left_coset(R.add, R.one, I)}")
			empty := a.TermAs[Set[Set[A]]]("∅")
			additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
			additiveOps := a.TermAs[quotient_group.GroupOps[A]]("additive_group(R)")
			scalarField := a.Have(
				"k is a field under the operations of R restricted to k, which are R's",
				"ring_subfield(restrict_ring(R, k), inv, k)",
				By(scalars, field.RingSubfieldRestrict.At(R, k, inv, k)))
			quotient := a.Conjuncts(
				a.Have(
					"R, I and R modulo I are modules over k",
					"module_on(restrict_ring(R, k), regular_module(R)) ∧ "+
						"submodule(restrict_ring(R, k), regular_module(R), I) ∧ "+
						"module_on(restrict_ring(R, k), «Q»)",
					By(ring, scalars, kInR, ideal, IdealQuotientModuleOn.At(R, k, inv, I))),
				"R is a module over k",
				"I is a submodule over k",
				"the quotient is a module over k")
			quotientOn := quotient[2]
			proper := a.Have(
				"I misses one: else it is all of R, and R modulo R has dimension zero",
				"R.one ∉ I",
				By(
					scalars,
					kInR,
					ideal,
					line,
					ring_ideal.IdealOneIff.Read(ring).At(I),
					FieldResiduesColength.At(R, k, inv, I),
					nat_arith.OneIsSucZero,
					peano.SucNotZero))
			nonzero := a.Have(
				"so the class of one is a nonzero quotient vector",
				"left_coset(R.add, R.one, I) ∈ «Q».carrier ∧ left_coset(R.add, R.one, I) ≠ «Q».zero",
				By(ring, ideal, proper, QuotientOneNonzero.At(R, I)))
			zeroClass := a.Have(
				"the quotient zero is the class I",
				"«Q».zero = I",
				Simp(Fwd(submodule.QuotientModuleDef)),
				Basic())
			offZero := a.Have(
				"the class of one lies outside the span of ∅, which is the zero class alone",
				"left_coset(R.add, R.one, I) ∉ module_span(restrict_ring(R, k), «Q», ∅)",
				By(zeroClass, nonzero, quotientOn, set_basic.InSing.At(e, I), submodule.SpanEmpty.At(K, Q)))
			independent := a.Have(
				"so the class of one is independent",
				"module_independent(restrict_ring(R, k), «Q», {left_coset(R.add, R.one, I)})",
				By(
					offZero,
					nonzero,
					quotientOn,
					scalarField,
					set_order.EmptySubset,
					set_basic.NotInEmpty,
					linear_independence.IndependentInsertIff.At(K, Q, inv, empty, e),
					linear_independence.IndependentEmpty.At(K, Q)))
			basis := a.Have(
				"one independent vector of the line R/I is a basis of it",
				"module_basis(restrict_ring(R, k), «Q», {left_coset(R.add, R.one, I)})",
				By(
					independent,
					quotientOn,
					scalarField,
					finite,
					line,
					IndependentFullBasis.At(K, Q, inv, single),
					cardinality.HasSizeDef.At(single, a.TermAs[Nat]("1")),
					finite_set.FiniteSing.At(e),
					cardinality.CardSing.At(e)))
			multiples := a.Have(
				"each quotient vector is a multiple of the class of one",
				"∀X:set(A). X ∈ «Q».carrier ⇒ ∃c:A. c ∈ k ∧ X = «Q».smul(c, left_coset(R.add, R.one, I))",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("X")
					inQ := b.Assume()
					spanned := b.Have(
						"X lies in the span of the basis",
						"X ∈ module_span(restrict_ring(R, k), «Q», {left_coset(R.add, R.one, I)})",
						By(inQ, basis, linear_independence.ModuleBasisDef))
					sums := b.Have(
						"that span is the multiples of the class of one plus the span of ∅",
						"module_span(restrict_ring(R, k), «Q», {left_coset(R.add, R.one, I)}) = "+
							"{«Q».add(«Q».smul(c, left_coset(R.add, R.one, I)), w) | "+
							"    c:A, "+
							"    w:set(A) | "+
							"    c ∈ restrict_ring(R, k).carrier ∧ w ∈ module_span(restrict_ring(R, k), «Q», ∅)}",
						By(nonzero, quotientOn, set_order.EmptySubset, submodule.SpanInsert.At(K, Q, empty, e)))
					c, w, sum := b.Obtain2As[A, Set[A]](
						"so X is a multiple c of the class of one plus a vector w of the span of ∅",
						"∃c:A. ∃w:set(A). "+
							"    c ∈ k ∧ "+
							"    w ∈ module_span(restrict_ring(R, k), «Q», ∅) ∧ "+
							"    X = «Q».add(«Q».smul(c, left_coset(R.add, R.one, I)), w)",
						sums.Rw(),
						By(spanned))
					scaled := b.TermAs[Set[A]]("«Q».smul(c, left_coset(R.add, R.one, I))")
					plusZero := b.Have(
						"the multiple is a quotient vector, which the zero class leaves fixed",
						"«Q».add(«Q».smul(c, left_coset(R.add, R.one, I)), «Q».zero) = "+
							"«Q».smul(c, left_coset(R.add, R.one, I))",
						By(
							nonzero,
							sum,
							group.RightIdentityOn.Read(module.AddGroupOn.Read(quotientOn)).AsFact().At(scaled),
							module.SmulIn.Read(quotientOn).AsFact().At(c, e)))
					b.Take(c)
					b.Show(
						"w lies in the span of ∅, so it is the zero class and X is the multiple",
						By(zeroClass, plusZero, sum, quotientOn, set_basic.InSing.At(w, I), submodule.SpanEmpty.At(K, Q)))
				}))
			residues := a.Have(
				"each element of R has a residue in k",
				"∀x:A. x ∈ R.carrier ⇒ ∃y:A. y ∈ k ∧ x + -y ∈ I",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					class := b.Have(
						"the class of x is a quotient vector",
						"left_coset(R.add, x, I) ∈ «Q».carrier",
						Simp(Fwd(module_record.RegularModuleDef), Fwd(submodule.QuotientModuleDef)),
						By(
							xIn,
							additive,
							ideal,
							ring_ideal.IdealSubset.At(R, I),
							quotient_group.LeftCosetInLeftCosets.At(additiveOps, I, x),
							module_record.AdditiveGroupDef.At(R)))
					c, multiple := b.ObtainAs[A](
						"so it is a multiple c of the class of one",
						"∃c:A. c ∈ k ∧ left_coset(R.add, x, I) = «Q».smul(c, left_coset(R.add, R.one, I))",
						By(multiples, class))
					cIn := b.Have(
						"c lies in R",
						"c ∈ R.carrier",
						BySets(kInR, multiple))
					unit := b.Have(
						"multiplication by one fixes c",
						"c * R.one = c",
						ByArith(ring, cIn))
					computed := b.Simplified(
						multiple,
						Fwd(module_record.RegularModuleDef),
						Fwd(submodule.QuotientModuleDef))
					sameClass := b.Have(
						"c times the class of one is the class of c, so x and c share a class",
						"left_coset(R.add, x, I) = left_coset(R.add, c, I)",
						By(
							comm_ring.OneIn.Read(ring),
							quotient[0],
							quotient[1],
							unit,
							computed,
							submodule.QuotientSmulCoset.At(K, V, I, c, one)))
					b.Take(c)
					b.Show(
						"x − c lies in I, the two sharing a class",
						By(
							sameClass,
							ideal,
							cIn,
							xIn,
							computed,
							quotient_ring.CosetEqIff.At(R, I, x, c),
							comm_ring.SubAddNegOn.Read(ring).AsFact().At(x, c)))
				}))
			a.Show(
				"I is proper and has its residues in k",
				Simp(Fwd(quotient_ring.RationalIdealDef), Fwd(module_record.RestrictRingCarrier)),
				By(proper, residues, ideal))
		}),
})}

// RationalIffColengthOne — over a field k inside a subring S of a commutative
// ring R, an ideal I of S is the ideal of a k-rational point exactly when S/I
// has dimension one over k. S is a commutative ring of its own under R's
// operations, and read there the two directions are FieldResiduesColength and
// IdealColengthOneRational.
var RationalIffColengthOne = rationalIffColengthOneThm{family.Add(registry.ProofEntry{
	Name: "RationalIffColengthOne",
	Key:  "prop_bf569b9fb9892d3a",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀k:set(A). ∀inv:(A → A). ∀S I:set(A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"ring_subfield(R, inv, k)",
			"subring(R, S)",
			"k ⊆ S",
			"ring_ideal(restrict_ring(R, S), I)",
		},
		Conclusion: "rational_ideal(R, k, S, I) ⇔ " +
			"finite_dimensional(restrict_ring(R, k), «Q») ∧ module_dim(restrict_ring(R, k), «Q») = 1",
		Abbrev: Abbrev{
			{Name: "Q", Text: "quotient_module(restrict_module(regular_module(R), S), I)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			S, I *Expr[Set[A]],
			given Fact,
		) {
			premises := a.Conjuncts(
				given,
				"R is a commutative ring",
				"k is a field",
				"S is a subring of R",
				"k lies in S",
				"I is an ideal of S")
			ring, scalars, subringS, kInS, ideal :=
				premises[0], premises[1], premises[2], premises[3], premises[4]
			ringS := a.TermAs[RingOps[A]]("restrict_ring(R, S)")
			own := a.Conjuncts(
				a.Have(
					"S is a commutative ring under R's operations, and k a field in it",
					"comm_ring_on(restrict_ring(R, S)) ∧ ring_subfield(restrict_ring(R, S), inv, k)",
					By(
						subringS,
						scalars,
						comm_ring.SubringRingOn.Read(ring).At(S),
						field.RingSubfieldRestrict.At(R, S, inv, k))),
				"S is a commutative ring",
				"k is a field in it")
			sameRational := a.Have(
				"I is rational under R's operations exactly when under S's, which are R's",
				"rational_ideal(R, k, S, I) ⇔ rational_ideal(restrict_ring(R, S), k, S, I)",
				Simp(
					Fwd(quotient_ring.RationalIdealDef),
					Fwd(module_record.RestrictRingTwice),
					Fwd(module_record.RestrictRingDef)),
				Basic())
			sameScalars := a.Have(
				"restricting S to k is restricting R to k",
				"restrict_ring(restrict_ring(R, S), k) = restrict_ring(R, k)",
				Cite(module_record.RestrictRingTwice))
			sameVectors := a.Have(
				"and S as a module over itself is R's regular module restricted to S",
				"regular_module(restrict_ring(R, S)) = restrict_module(regular_module(R), S)",
				Cite(module_record.RegularModuleRestrict))
			a.Do(sameRational.Rw(), sameScalars.RwRev(), sameVectors.RwRev())
			a.Iff()
			a.Forward(
				"a rational ideal of the ring S has a line as its quotient",
				func(b *Argument, rational Fact) {
					b.Show(
						"S modulo the rational ideal I is a line over k, I missing the one S holds",
						By(
							rational,
							own[0],
							own[1],
							kInS,
							ideal,
							comm_ring.OneIn.Read(own[0]),
							quotient_ring.RationalIdealDef.At(ringS, k, S, I),
							FieldResiduesColength.At(ringS, k, inv, I)))
				})
			a.Backward(
				"and an ideal of the ring S with a line as its quotient is rational",
				func(b *Argument, line Fact) {
					b.Show(
						"an ideal of S whose quotient is a line over k is rational",
						By(line, own[0], own[1], kInS, ideal, IdealColengthOneRational.At(ringS, k, inv, I)))
				})
		}),
})}

// HomSetAgreeOnBasis — two maps of a hom set that agree on a finite basis are
// equal: on the carrier each is the combination of its values on the basis by
// the coordinates (HomBasisExpansion), and off it each is zero.
var HomSetAgreeOnBasis = homSetAgreeOnBasisThm{family.Add(registry.ProofEntry{
	Name: "HomSetAgreeOnBasis",
	Key:  "prop_f172503720ea98c1",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀E:set(B). ∀φ ψ:(B → C).",
		Hypotheses: []string{
			"finite(E)",
			"module_basis(R, M, E)",
			"φ ∈ hom_set(R, M, N)",
			"ψ ∈ hom_set(R, M, N)",
			"∀e:B. e ∈ E ⇒ φ(e) = ψ(e)",
		},
		Conclusion: "φ = ψ",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[module_record.ModuleOps[A, B]],
			N *Expr[module_record.ModuleOps[A, C]],
			E *Expr[Set[B]],
			φ, ψ *Arrow[B, C],
			finiteE, basisE, φIn, ψIn, agree Fact,
		) {
			ofφ := a.Conjuncts(
				a.Have(
					"φ is R-linear and zero off M",
					"module_homomorphism(R, M, N, φ) ∧ (∀u:B. u ∉ M.carrier ⇒ φ(u) = N.zero)",
					By(φIn, hom_module.InHomSet.At(R, M, N, φ))),
				"φ is R-linear",
				"φ vanishes off M")
			ofψ := a.Conjuncts(
				a.Have(
					"ψ is R-linear and zero off M",
					"module_homomorphism(R, M, N, ψ) ∧ (∀u:B. u ∉ M.carrier ⇒ ψ(u) = N.zero)",
					By(ψIn, hom_module.InHomSet.At(R, M, N, ψ))),
				"ψ is R-linear",
				"ψ vanishes off M")
			a.Do(Funext())
			x := a.FixAs[B]("x")
			a.Cases(a.Term("x ∈ M.carrier"))
			a.When(
				"on M each map is the combination of its values on E",
				func(b *Argument, xIn Fact) {
					add, zero := b.TermAs[Op[C]]("N.add"), b.TermAs[C]("N.zero")
					expandφ := b.Have(
						"φ(x) is the combination of its values on E",
						"φ(x) = module_sum(N.add, N.zero, E, λe:B. module_basis_coordinates(R, M, E, x, e) • φ(e))",
						By(finiteE, basisE, ofφ[0], xIn, HomBasisExpansion.At(R, M, N, E, φ, x)))
					expandψ := b.Have(
						"so is ψ(x)",
						"ψ(x) = module_sum(N.add, N.zero, E, λe:B. module_basis_coordinates(R, M, E, x, e) • ψ(e))",
						By(finiteE, basisE, ofψ[0], xIn, HomBasisExpansion.At(R, M, N, E, ψ, x)))
					termwise := b.Have(
						"the two combinations agree term by term",
						Statement{
							Binders: "∀e:B.",
							Hypotheses: []string{
								"e ∈ E",
							},
							Conclusion: "module_basis_coordinates(R, M, E, x, e) • φ(e) = " +
								"module_basis_coordinates(R, M, E, x, e) • ψ(e)",
						},
						Derive(func(c *Argument) {
							e := c.FixAs[B]("e")
							eIn := c.Assume()
							c.Show(
								"the values agree on E",
								By(Normalized, agree.At(e), eIn))
						}))
					b.Show(
						"so the two sums are one",
						By(
							expandφ,
							expandψ,
							termwise,
							module.ModuleSumCongruence.At(
								add,
								zero,
								E,
								b.TermAs[Fun[B, C]]("λe:B. module_basis_coordinates(R, M, E, x, e) • φ(e)"),
								b.TermAs[Fun[B, C]]("λe:B. module_basis_coordinates(R, M, E, x, e) • ψ(e)"))))
				})
			a.Otherwise(
				"off M both maps are zero",
				func(b *Argument, xOut Fact) {
					b.Show(
						"both read N.zero",
						By(Normalized, ofφ[1].At(x), ofψ[1].At(x), xOut))
				})
		}),
})}

// FiniteCarrierFiniteDimensional — a module with finitely many elements over a
// field is finite-dimensional: its carrier is a submodule, so it spans itself.
var FiniteCarrierFiniteDimensional = finiteCarrierFiniteDimensionalThm{family.Add(registry.ProofEntry{
	Name: "FiniteCarrierFiniteDimensional",
	Key:  "prop_5f0b156f25815972",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀inv:(A → A).",
		Hypotheses: []string{
			"module_on(R, M)",
			"ring_subfield(R, inv, R.carrier)",
			"finite(M.carrier)",
		},
		Conclusion: "finite_dimensional(R, M)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		M *Expr[module_record.ModuleOps[A, B]],
		inv *Arrow[A, A],
		module, scalars, finiteCarrier Fact,
	) {
		carrier := a.TermAs[Set[B]]("M.carrier")
		spans := a.Have(
			"the carrier is a submodule, so it spans itself",
			"module_span(R, M, M.carrier) = M.carrier",
			By(module, submodule.CarrierSubmodule.At(R, M), submodule.SpanOfSubmodule.At(R, M, carrier)))
		a.Show(
			"the carrier is a finite spanning set",
			By(
				module,
				scalars,
				finiteCarrier,
				spans,
				FiniteDimensionalSpanning.At(R, M, inv),
				set_order.SubsetRefl))
	}),
})}
