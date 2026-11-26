// Coordinate maps preserve products, exactness and finite sums.

package function_module

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

var IndexedProductModule = indexedProductModuleThm{family.Add(registry.ProofEntry{
	Name: "IndexedProductModule",
	Key:  "prop_2699d1318b2fa5c0",
	Reading: "The scalar ring hypothesis is needed only for J empty, when the " +
		"product is the singleton zero module and the factor hypothesis is " +
		"vacuous. For J nonempty, module_on of an active factor already contains it.",
	Deps: []registry.EntryLike{IndexedProductModuleDef, module.ModuleOn},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀J:set(I). ∀M:(I → module_ops(A, B)).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀i:I. i ∈ J ⇒ module_on(R, M(i))",
		},
		Conclusion: "module_on(R, indexed_product_module(J, M))",
	},
		"Check the module axioms at an active coordinate using its factor module, and at an inactive "+
			"coordinate using the fixed normalization. Function extensionality combines these equations."),
})}

var IndexedMapHom = indexedMapHomThm{family.Add(registry.ProofEntry{
	Name: "IndexedMapHom",
	Key:  "prop_1decb08b5099c6af",
	Deps: []registry.EntryLike{
		IndexedProductModule,
		indexedModuleMapDef,
		module_homomorphism.ModuleHomomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀J:set(I). " +
			"∀M:(I → module_ops(A, B)). " +
			"∀N:(I → module_ops(A, C)). " +
			"∀f:(I → B → C).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀i:I. i ∈ J ⇒ module_homomorphism(R, M(i), N(i), f(i))",
		},
		Conclusion: "module_homomorphism(R, " +
			"    indexed_product_module(J, M), " +
			"    indexed_product_module(J, N), " +
			"    indexed_module_map(J, N, f))",
	},
		"Use the component homomorphisms at active coordinates and the target zero off J. "+
			"IndexedProductModule supplies both endpoint modules, including the empty index case."),
})}

var IndexedMapIsomorphism = indexedMapIsomorphismThm{family.Add(registry.ProofEntry{
	Name:    "IndexedMapIsomorphism",
	Key:     "prop_65352fca7f788d4c",
	Reading: "No finiteness of J is required; choosing simultaneous component preimages uses choice.",
	Deps: []registry.EntryLike{
		IndexedMapHom,
		module_homomorphism.ModuleIsomorphismDef,
		indexed_functions.IndexedFunctionsExtensional,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀J:set(I). " +
			"∀M:(I → module_ops(A, B)). " +
			"∀N:(I → module_ops(A, C)). " +
			"∀f:(I → B → C).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀i:I. i ∈ J ⇒ module_isomorphism(R, M(i), N(i), f(i))",
		},
		Conclusion: "module_isomorphism(R, " +
			"    indexed_product_module(J, M), " +
			"    indexed_product_module(J, N), " +
			"    indexed_module_map(J, N, f))",
	},
		"IndexedMapHom gives linearity. Component injectivity and normalization "+
			"give injectivity of the product map; choose a preimage in each active "+
			"source carrier and put the source zero elsewhere to obtain surjectivity."),
})}

// IndexedProductExact — a product of exact sequences is exact: the image of a
// source vector lies in the target product and the product map of g kills it,
// coordinate by coordinate; and a target vector that map kills is the image of
// the source vector taking a chosen preimage at each active index and the
// source zero at the others.
var IndexedProductExact = indexedProductExactThm{family.Add(registry.ProofEntry{
	Name: "IndexedProductExact",
	Key:  "prop_a49fdd74f7d465c7",
	Reading: "Only exactness of the components is read: no linearity of the " +
		"maps, no module law and no scalar ring. Products are exact using choice, " +
		"even for infinite J. Equality off J is forced by the prescribed zeros.",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). " +
			"∀M:(I → module_ops(A, B)). " +
			"∀N:(I → module_ops(A, C)). " +
			"∀f:(I → B → C). " +
			"∀P:(I → module_ops(A, D)). " +
			"∀g:(I → C → D).",
		Hypotheses: []string{
			"∀i:I. i ∈ J ⇒ exact_at(P(i).zero, M(i).carrier, N(i).carrier, f(i), g(i))",
		},
		Conclusion: "exact_at(indexed_product_module(J, P).zero, " +
			"    indexed_product_module(J, M).carrier, " +
			"    indexed_product_module(J, N).carrier, " +
			"    indexed_module_map(J, N, f), " +
			"    indexed_module_map(J, P, g))",
	}, func(
		a *Argument,
		J *Expr[Set[I]],
		M *Arrow[I, ModuleOps[A, B]],
		N *Arrow[I, ModuleOps[A, C]],
		f *Arrow2[I, B, C],
		P *Arrow[I, ModuleOps[A, D]],
		g *Arrow2[I, C, D],
		exact Fact,
	) {
		pointwise := a.Have(
			"at an active index, y is an image under f(i) exactly when it lies in N(i) and g(i) kills it",
			"∀i:I. ∀y:C. i ∈ J ⇒ (y ∈ image(f(i), M(i).carrier) ⇔ y ∈ N(i).carrier ∧ g(i, y) = P(i).zero)",
			BySets(a.Unfolded(exact, module_homomorphism.ExactAtDef), group_homomorphism.GroupKernelDef))
		a.Do(
			Unfold(module_homomorphism.ExactAtDef),
			Simp(Fwd(set_basic.Extension), Fwd(set_basic.InImage), Fwd(group_homomorphism.GroupKernelDef)))
		a.FixAs[Fun[I, C]]("t")
		a.Iff()
		a.Forward(
			"the image of a source vector lies in the target product, and the product map of g kills it",
			func(b *Argument, image Fact) {
				_, preimage := b.UnpackAs[Fun[I, B]](image, "s")
				parts := b.Conjuncts(
					preimage,
					"t is the image of s",
					"s lies in the source product")
				killedCoordinates := b.Have(
					"at an active index f(i, s(i)) is an image under f(i), so it lies in N(i) and g(i) kills it",
					"∀i:I. i ∈ J ⇒ f(i, s(i)) ∈ N(i).carrier ∧ g(i, f(i, s(i))) = P(i).zero",
					By(pointwise, parts[1], indexed_functions.IndexedFunctionsCoordinate, set_basic.InImage))
				inTarget := b.Have(
					"the image of s lies in the target product, the target zero standing off J",
					"indexed_module_map(J, N, f, s) ∈ indexed_functions(J, λi:I. N(i).zero, λi:I. N(i).carrier)",
					Simp(Fwd(indexedModuleMapDef), Fwd(indexed_functions.IndexedFunctionsDef)),
					By(killedCoordinates))
				killed := b.Have(
					"the product map of g kills the image of s: g(i) kills "+
						"f(i, s(i)) on J, and the map is the zero of P(i) off J",
					"indexed_module_map(J, P, g, indexed_module_map(J, N, f, s)) = (λi:I. P(i).zero)",
					Simp(Fwd(indexedModuleMapDef)),
					Funext(),
					By(killedCoordinates))
				b.Show(
					"so t lies in the kernel of the product map of g",
					By(parts[0], killed, inTarget))
			})
		a.Backward(
			"a target vector the product map of g kills is the image of a preimage chosen at each active index",
			func(b *Argument, kernel Fact) {
				parts := b.Conjuncts(
					kernel,
					"t lies in the target product",
					"the product map of g kills t")
				coordinates := b.Conjuncts(
					b.Unfolded(parts[0], indexed_functions.IndexedFunctionsDef),
					"at an active index t(i) lies in N(i)",
					"off J t(i) is the zero of N(i)")
				images := b.Have(
					"at an active index t(i) lies in N(i) and g(i) kills it, so it is an image under f(i)",
					"∀i:I. i ∈ J ⇒ t(i) ∈ image(f(i), M(i).carrier)",
					By(pointwise, coordinates[0], parts[1], indexedModuleMapDef))
				s, sDef := b.LetAs[Fun[I, B]](
					"s", "λi:I. COND(i ∈ J, inverse_on(M(i).carrier, f(i), t(i)), M(i).zero)")
				sIn := b.Have(
					"s lies in the source product: a preimage in M(i) on J, the zero of M(i) off it",
					"s ∈ indexed_functions(J, λi:I. M(i).zero, λi:I. M(i).carrier)",
					Simp(Fwd(indexed_functions.IndexedFunctionsDef)),
					By(images, sDef, functions.InverseOnIn))
				mapsTo := b.Have(
					"the product map of f takes s to t",
					"indexed_module_map(J, N, f, s) = t",
					Simp(Fwd(indexedModuleMapDef)),
					Funext(),
					Derive(func(c *Argument) {
						i := c.FixAs[I]("i")
						c.Cases(c.Term("i ∈ J"))
						c.When(
							"on J, f(i) takes the chosen preimage of t(i) back to t(i)",
							func(d *Argument, active Fact) {
								d.Show(
									"t(i) being an image under f(i), inverse_on picks a preimage that f(i) maps back to it",
									By(active, sDef, images.At(i), functions.InverseOnRight))
							})
						c.Otherwise(
							"off J both sides are the zero of N(i)",
							func(d *Argument, inactive Fact) {
								d.Show(
									"t being normalized off J",
									By(inactive, coordinates[1].At(i)))
							})
					}))
				b.Take(s)
				b.Show(
					"s is a preimage of t in the source product",
					By(Normalized, mapsTo, sIn))
			})
	}),
})}

var IndexedProductSumHom = indexedProductSumHomThm{family.Add(registry.ProofEntry{
	Name: "IndexedProductSumHom",
	Key:  "prop_dadf49e1b3899574",
	Reading: "Finiteness is required for the total module_sum to express a finite linear " +
		"combination. The target module hypothesis supplies the ring laws even when J is empty.",
	Deps: []registry.EntryLike{
		IndexedProductModule,
		module_homomorphism.ModuleHomomorphismDef,
		module.ModuleSumAdd,
		module.ModuleSumSmul,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀J:set(I). " +
			"∀M:(I → module_ops(A, B)). " +
			"∀P:module_ops(A, C). " +
			"∀f:(I → B → C).",
		Hypotheses: []string{
			"finite(J)",
			"module_on(R, P)",
			"∀i:I. i ∈ J ⇒ module_homomorphism(R, M(i), P, f(i))",
		},
		Conclusion: "module_homomorphism(R, " +
			"    indexed_product_module(J, M), " +
			"    P, " +
			"    (λs:(I → B). module_sum(P.add, P.zero, J, (λi:I. f(i, s(i))))))",
	},
		"Each coordinate followed by its given map is linear. Sum these maps over the "+
			"finite index set using the module sum laws; the empty sum is the zero homomorphism."),
})}
