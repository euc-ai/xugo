package linear_independence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

var IndexedModuleBasisDef = indexedModuleBasisDefThm{family.Define(registry.DefEntry{
	Name: "IndexedModuleBasisDef",
	Key:  "prop_be528a0854b737bf",
	Reading: "Injective indexing preserves the number of basis vectors; replacing " +
		"an indexed family by its image set must not silently drop repeated columns.",
	Deps:  []registry.EntryLike{ModuleBasisDef},
	Const: "indexed_module_basis",
	Type:  "ring_ops(A) → module_ops(A, B) → num → (num → B) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀e:(num → B). " +
			"    indexed_module_basis(R, M, n, e) ⇔ " +
			"    injective_on({i:num | i < n}, e) ∧ module_basis(R, M, {e(i) | i:num | i < n})",
	},
})}

// IndexedBasisImage — the vectors of an indexed basis of length n form a
// finite basis of n members, indexed one-to-one: the set is a basis and
// the indexing injective by definition, and the set is the image of the
// n numbers below n under an injective map, so it has n members.
var IndexedBasisImage = indexedBasisImageThm{family.Add(registry.ProofEntry{
	Name: "IndexedBasisImage",
	Key:  "prop_3306e16d03fe04cb",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀e:(num → B).",
		Hypotheses: []string{
			"indexed_module_basis(R, M, n, e)",
		},
		Conclusion: "finite({e(i) | i:num | i < n}) ∧ " +
			"card({e(i) | i:num | i < n}) = n ∧ " +
			"module_basis(R, M, {e(i) | i:num | i < n}) ∧ " +
			"injective_on({i:num | i < n}, e)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			n *Expr[Nat],
			e *Vec[B, DimN],
			indexed Fact,
		) {
			image := a.Have(
				"the vectors of the basis are the image of the indexing",
				"{e(i):B | i:num | i < n} = image(e, {i:num | i < n})",
				BySets())
			E := a.TermAs[Set[B]]("{e(i):B | i:num | i < n}")
			indices := a.TermAs[Set[Nat]]("{i:num | i < n}")
			a.Show(
				"injective indexing preserves the size of the initial segment",
				By(
					image,
					indexed,
					IndexedModuleBasisDef.At(R, M, n, e),
					num_segment.HasSizeBelowStrict.At(n),
					cardinality.HasSizeImageInj.At(e, indices, n),
					cardinality.HasSizeDef.At(E, n)))
		}),
})}

// IndexedBasisInCarrier — the vectors of an indexed basis lie in the
// module: they form a basis (IndexedBasisImage), which lies in M's carrier.
var IndexedBasisInCarrier = indexedBasisInCarrierThm{family.Add(registry.ProofEntry{
	Name: "IndexedBasisInCarrier",
	Key:  "prop_88157e6224129a1a",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀e:(num → B). ∀i:num.",
		Hypotheses: []string{
			"indexed_module_basis(R, M, n, e)",
			"i < n",
		},
		Conclusion: "e(i) ∈ M.carrier",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			n *Expr[Nat],
			e *Vec[B, DimN],
			indexed Fact,
		) {
			a.Show(
				"every indexed vector lies in the basis they form, and hence in M",
				BySets(
					indexed,
					IndexedBasisImage.At(R, M, n, e),
					BasisInCarrier.At(R, M, a.TermAs[Set[B]]("{e(k):B | k:num | k < n}"))))
		}),
})}

// FiniteBasisIndexed — a finite basis E is indexed one-to-one by the numbers
// below its size: two finite sets of one size are matched by a bijection
// (cardinality.CardEqBijection), and the enumeration of E it gives is an
// indexed basis of card(E) vectors.
var FiniteBasisIndexed = finiteBasisIndexedThm{family.Add(registry.ProofEntry{
	Name: "FiniteBasisIndexed",
	Key:  "prop_ede77f11aaa8bb13",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀E:set(B).",
		Hypotheses: []string{"finite(E)", "module_basis(R, M, E)"},
		Conclusion: "∃e:(num → B). indexed_module_basis(R, M, card(E), e)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		M *Expr[ModuleOps[A, B]],
		E *Expr[Set[B]],
		assumptions Fact,
	) {
		I := a.TermAs[Set[Nat]]("{i:num | i < card(E)}")
		size := a.Have(
			"the initial segment has the basis cardinality",
			"finite({i:num | i < card(E)}) ∧ card({i:num | i < card(E)}) = card(E)",
			By(
				num_segment.HasSizeBelowStrict.At(a.TermAs[Nat]("card(E)")),
				cardinality.HasSizeDef.Inst[Nat]().At(I, a.TermAs[Nat]("card(E)"))))
		e, bijection := a.ObtainAs[Fun[Nat, B]](
			"enumerate the finite basis by its cardinality",
			"∃e:(num → B). "+
				"    (∀i:num. i ∈ {j:num | j < card(E)} ⇒ e(i) ∈ E) ∧ "+
				"    (∀v:B. v ∈ E ⇒ ∃i:num. i ∈ {j:num | j < card(E)} ∧ e(i) = v) ∧ "+
				"    injective_on({i:num | i < card(E)}, e)",
			By(size, assumptions, cardinality.CardEqBijection.At(I, E)),
			Named("e"))
		image := a.Have(
			"the indexed comprehension equals the basis set",
			"{e(i):B | i:num | i < card(E)} = E",
			BySets(bijection))
		a.Take(e)
		a.Show(
			"the injective enumeration carries the given basis",
			By(assumptions, bijection, image, IndexedModuleBasisDef.At(R, M, a.TermAs[Nat]("card(E)"), e)))
	}),
})}

// IndependentImageCriterion — a family one-to-one on X has an independent
// image once its combinations over the finite parts of X are tested: a
// finite part V of the image lifts to a finite part T of X, on which e is
// still one-to-one, so a vanishing combination of V reads over T with the
// coefficients taken through e (ModuleSumImage), and the test clears them.
var IndependentImageCriterion = independentImageCriterionThm{family.Add(registry.ProofEntry{
	Name: "IndependentImageCriterion",
	Key:  "prop_2e2ccb5b2a4cd0ad",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀e:(C → B). ∀X:set(C).",
		Hypotheses: []string{
			"∀x:C. x ∈ X ⇒ e(x) ∈ M.carrier",
			"injective_on(X, e)",
			"∀T:set(C). ∀c:(C → A). " +
				"    finite(T) ∧ " +
				"    T ⊆ X ∧ " +
				"    (∀x:C. x ∈ T ⇒ c(x) ∈ R.carrier) ∧ " +
				"    module_sum(M.add, M.zero, T, λx:C. c(x) • e(x)) = M.zero ⇒ " +
				"    (∀x:C. x ∈ T ⇒ c(x) = R.zero)",
		},
		Conclusion: "module_independent(R, M, image(e, X))",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			e *Arrow[C, B],
			X *Expr[Set[C]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"e sends X into M",
				"e is one-to-one on X",
				"over a finite part of X only the zero combination vanishes")
			vectors, oneToOne, clears := given[0], given[1], given[2]
			vanishing := a.Have(
				"a combination of the image of X that vanishes has every coefficient zero",
				Statement{
					Binders: "∀V:set(B). ∀c:(B → A).",
					Hypotheses: []string{
						"finite(V)",
						"V ⊆ image(e, X)",
						"∀v:B. v ∈ V ⇒ c(v) ∈ R.carrier",
						"module_sum(M.add, M.zero, V, λv:B. c(v) • v) = M.zero",
					},
					Conclusion: "∀v:B. v ∈ V ⇒ c(v) = R.zero",
				},
				Derive(func(b *Argument) {
					V := b.FixAs[Set[B]]("V")
					b.FixAs[Fun[B, A]]("c")
					onV := b.Conjuncts(
						b.Assume(),
						"V is finite",
						"V lies in the image of X",
						"c is a scalar on V",
						"the combination vanishes")
					T, lifted := b.ObtainAs[Set[C]](
						"V is the image of a finite part T of X",
						"∃T:set(C). finite(T) ∧ V = image(e, T) ∧ T ⊆ X",
						By(onV[0], onV[1], finite_set.FiniteSubsetImage.At(e, X, V)))
					onT := b.Conjuncts(
						lifted,
						"T is finite",
						"V is the image of T",
						"T lies in X")
					inX := b.Unfolded(onT[2], set_basic.SubsetDef)
					intoV := b.Have(
						"e carries T into V",
						"∀x:C. x ∈ T ⇒ e(x) ∈ V",
						b.ForEach(func(x *Expr[C]) Action {
							return By(Normalized, onT[1], set_image.FunInImage.At(e, T, x))
						}))
					scalarsT := b.Have(
						"so c(e(x)) is a scalar on T",
						"∀x:C. x ∈ T ⇒ c(e(x)) ∈ R.carrier",
						b.ForEach(func(x *Expr[C]) Action {
							return By(intoV.At(x), onV[2].At(e.Apply(x)))
						}))
					terms := b.Have(
						"each c(e(x)) • e(x) lies in M",
						"∀x:C. x ∈ T ⇒ c(e(x)) • e(x) ∈ M.carrier",
						b.ForEach(func(x *Expr[C]) Action {
							return By(inX.At(x), vectors.At(x), scalarsT.At(x), module.SmulIn.Read(moduleOn))
						}))
					reindexed := b.Have(
						"read over T, the combination takes its coefficients through e",
						"module_sum(M.add, M.zero, T, λx:C. c(e(x)) • e(x)) = M.zero",
						By(
							onT[0],
							onT[1],
							oneToOne,
							onT[2],
							terms,
							onV[3],
							functions.InjectiveOnSubset.At(e, T, X),
							module.ModuleSumImage.Read(moduleOn).At(T, e, b.TermAs[Fun[B, B]]("λv:B. c(v) • v"))))
					cleared := b.Have(
						"the test on T clears the coefficients c(e(x))",
						"∀x:C. x ∈ T ⇒ c(e(x)) = R.zero",
						By(onT[0], onT[2], scalarsT, reindexed, clears.At(T, b.TermAs[Fun[C, A]]("λx:C. c(e(x))"))))
					b.Do(onT[1].Rw())
					b.Show(
						"and so c vanishes on V",
						Simp(Fwd(set_image.ForallInImage)),
						By(cleared))
				}))
			a.Show(
				"the image lies in M, and only its zero combination vanishes",
				By(
					vectors,
					set_image.ImageSubsetIff.At(e, X, a.TermAs[Set[B]]("M.carrier")),
					vanishing,
					ModuleIndependentDef))
		}),
})}
