package indexed_functions

import (
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// IndexedFunctionsDef — Functions are normalized outside the active index carrier.
var IndexedFunctionsDef = indexedFunctionsDefThm{family.Define(registry.DefEntry{
	Name:  "IndexedFunctionsDef",
	Key:   "prop_5e7d8d1025c78be0",
	Const: "indexed_functions",
	Type:  "set(I) → (I → A) → (I → set(A)) → set(I → A)",
	Equations: []string{
		"∀J:set(I). ∀z:(I → A). ∀X:(I → set(A)). " +
			"    indexed_functions(J, z, X) = " +
			"    {f:I → A | (∀i:I. i ∈ J ⇒ f(i) ∈ X(i)) ∧ (∀i:I. i ∉ J ⇒ f(i) = z(i))}",
	},
	Reading: "Functions are normalized outside the active index carrier.",
})}

// FiniteCoordinateDependenceDef — One fixed finite set of active coordinates determines the output on the source carrier.
var FiniteCoordinateDependenceDef = finiteCoordinateDependenceDefThm{family.Define(registry.DefEntry{
	Name:  "FiniteCoordinateDependenceDef",
	Key:   "prop_2a568918828bfc2d",
	Const: "finite_coordinate_dependence",
	Type:  "set(I) → set(I → A) → ((I → A) → B) → bool",
	Equations: []string{
		"∀J:set(I). ∀C:set(I → A). ∀f:((I → A) → B). " +
			"    finite_coordinate_dependence(J, C, f) ⇔ " +
			"    ∃K:set(I). " +
			"        finite(K) ∧ " +
			"        K ⊆ J ∧ " +
			"        (∀x y:(I → A). x ∈ C ∧ y ∈ C ∧ (∀i:I. i ∈ K ⇒ x(i) = y(i)) ⇒ f(x) = f(y))",
	},
	Reading: "The finite support may depend on f and C, but is fixed for every pair of inputs " +
		"in C. No restriction is imposed on values outside C, and no topology or algebra is assumed.",
})}

// IndexedFunctionsCoordinate — an indexed function sends each active
// coordinate into its factor: this is the first clause of the
// definition, read at one index.
var IndexedFunctionsCoordinate = indexedFunctionsCoordinateThm{family.Add(registry.ProofEntry{
	Name: "IndexedFunctionsCoordinate",
	Key:  "prop_430d2028efc3fa4f",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀X:(I → set(A)). ∀i:I. ∀f:(I → A).",
		Hypotheses: []string{
			"f ∈ indexed_functions(J, z, X)",
			"i ∈ J",
		},
		Conclusion: "f(i) ∈ X(i)",
	}, func(
		a *Argument,
		J *Expr[Set[I]],
		z *Arrow[I, A],
		X *Arrow[I, Set[A]],
		i *Expr[I],
		f *Arrow[I, A],
		given Fact,
	) {
		a.Show(
			"an active coordinate of an indexed function lies in its factor",
			BySets(given, IndexedFunctionsDef.At(J, z, X)))
	}),
})}

// IndexedFunctionsExtensional — two indexed functions over the same
// carriers are equal once they agree on the active indices: off the
// index set both take the prescribed value.
var IndexedFunctionsExtensional = indexedFunctionsExtensionalThm{family.Add(registry.ProofEntry{
	Name: "IndexedFunctionsExtensional",
	Key:  "prop_cc0d8040a66a32f",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀X:(I → set(A)). ∀f g:(I → A).",
		Hypotheses: []string{
			"f ∈ indexed_functions(J, z, X)",
			"g ∈ indexed_functions(J, z, X)",
			"∀i:I. i ∈ J ⇒ f(i) = g(i)",
		},
		Conclusion: "f = g",
	}, func(
		a *Argument,
		J *Expr[Set[I]],
		z *Arrow[I, A],
		X *Arrow[I, Set[A]],
		f, g *Arrow[I, A],
		given Fact,
	) {
		a.Show(
			"active coordinates agree by hypothesis and inactive coordinates both equal z",
			Funext(),
			StripQuant(),
			BySets(given, IndexedFunctionsDef.At(J, z, X)))
	}),
})}

// IndexedFunctionsCongruence — the indexed functions depend on the
// factors only at the active indices: factors that agree there give the
// same set, since the off-index condition does not read them.
var IndexedFunctionsCongruence = indexedFunctionsCongruenceThm{family.Add(registry.ProofEntry{
	Name: "IndexedFunctionsCongruence",
	Key:  "prop_aa301669578e2d54",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀X Y:(I → set(A)).",
		Hypotheses: []string{
			"∀i:I. i ∈ J ⇒ X(i) = Y(i)",
		},
		Conclusion: "indexed_functions(J, z, X) = indexed_functions(J, z, Y)",
	}, func(a *Argument, J *Expr[Set[I]], z *Arrow[I, A], X, Y *Arrow[I, Set[A]], equal Fact) {
		a.Do(Unfold(IndexedFunctionsDef), Simp(Fwd(set_basic.Extension)))
		a.FixAs[Fun[I, A]]("f")
		a.Iff()
		a.Forward(
			"an indexed function over X is one over Y",
			func(b *Argument, source Fact) {
				b.Show(
					"the active coordinate conditions transfer to Y",
					BySets(equal, source))
			})
		a.Backward(
			"an indexed function over Y is one over X",
			func(b *Argument, target Fact) {
				b.Show(
					"the active coordinate conditions transfer to X",
					BySets(equal, target))
			})
	}),
})}

// IndexedFunctionsChangedCoordinates — when the prescribed value at each
// active index lies in its factor, a function is an indexed function
// exactly when it departs from the prescribed values only at active
// indices, and there within the factor.
var IndexedFunctionsChangedCoordinates = indexedFunctionsChangedCoordinatesThm{family.Add(registry.ProofEntry{
	Name: "IndexedFunctionsChangedCoordinates",
	Key:  "prop_6a7ded2b142b9a6e",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀X:(I → set(A)). ∀f:(I → A).",
		Hypotheses: []string{
			"∀i:I. i ∈ J ⇒ z(i) ∈ X(i)",
		},
		Conclusion: "f ∈ indexed_functions(J, z, X) ⇔ (∀i:I. f(i) ≠ z(i) ⇒ i ∈ J ∧ f(i) ∈ X(i))",
	}, func(
		a *Argument,
		J *Expr[Set[I]],
		z *Arrow[I, A],
		X *Arrow[I, Set[A]],
		f *Arrow[I, A],
		admissible Fact,
	) {
		a.Show(
			"an unchanged active coordinate takes the admissible prescribed value",
			BySets(admissible, IndexedFunctionsDef.At(J, z, X)))
	}),
})}
