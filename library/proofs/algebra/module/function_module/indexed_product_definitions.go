// Indexed products use the factor zero at every inactive coordinate.

package function_module

import (
	_ "github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	"github.com/euc-ai/xugo/library/registry"
)

var IndexedProductModuleDef = indexedProductModuleDefThm{family.Define(registry.DefEntry{
	Name:  "IndexedProductModuleDef",
	Key:   "prop_6bc1b0529cd29618",
	Const: "indexed_product_module",
	Type:  "set(I) → (I → module_ops(A, B)) → module_ops(A, I → B)",
	Reading: "The factors share a scalar type and a vector host type, but their " +
		"carriers and operations may vary with the index. Every operation returns the " +
		"prescribed zero outside J; no module laws are required of an inactive factor.",
	Deps: []registry.EntryLike{},
	Equations: []string{
		"∀J:set(I). ∀M:(I → module_ops(A, B)). " +
			"    indexed_product_module(J, M) = " +
			"    mk_module((λs:(I → B). λt:(I → B). λi:I. COND(i ∈ J, M(i).add(s(i), t(i)), M(i).zero)), " +
			"        (λi:I. M(i).zero), " +
			"        (λs:(I → B). λi:I. COND(i ∈ J, M(i).neg(s(i)), M(i).zero)), " +
			"        (λa:A. λs:(I → B). λi:I. COND(i ∈ J, M(i).smul(a, s(i)), M(i).zero)), " +
			"        indexed_functions(J, (λi:I. M(i).zero), (λi:I. M(i).carrier)))",
	},
})}

var indexedModuleMapDef = indexedModuleMapDefThm{family.Define(registry.DefEntry{
	Name:  "indexedModuleMapDef",
	Key:   "prop_471f83cdc7dac2f6",
	Const: "indexed_module_map",
	Type:  "set(I) → (I → module_ops(A, C)) → (I → B → C) → (I → B) → I → C",
	Reading: "The target family supplies the normalization outside J. " +
		"Source module records enter the linearity claim, not this total map.",
	Deps: []registry.EntryLike{},
	Equations: []string{
		"∀J:set(I). ∀N:(I → module_ops(A, C)). ∀f:(I → B → C). ∀s:(I → B). " +
			"    indexed_module_map(J, N, f, s) = (λi:I. COND(i ∈ J, f(i, s(i)), N(i).zero))",
	},
})}
