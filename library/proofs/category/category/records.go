// records.go — the chapter's definitional layer: the three record
// types category theory is held in.
//
// A category's components are one value, `category_ops(A, M)`: the
// objects, a set of a type A, the morphisms, a set of a type M, and
// the four operations between them. A functor is one value too,
// `functor_ops(A, M, B, N)`, its map of objects beside its map of
// morphisms, so that the functors between two categories form a set
// and a category of their own. A morphism of a category assembled from
// hom data (`category_from_hom`) is a datum framed by its two ends,
// `morphism_triple(A, D)`. Each is a record — a datatype with one
// constructor, its parts read off by projections — so that a statement
// binds `∀C:category_ops(A, M)` and reads a component as a field of
// the value, `C.objects`, `C.compose(g, f)`, `F.obj(x)`, `t.source`.
// The record door mints the type, the constructor and the projections,
// and registers each projection's equation at the constructor, the
// record's extensionality, injectivity, induction and recursion.

package category

import (
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// recordRows are the recursive-type universe's rows a record's
// derivations read, and the pair rows its multi-part payload needs.
var recordRows = []registry.EntryLike{
	datatype_universe.Recursion,
	datatype_universe.FamilyCons,
	datatype_universe.NodeInjective,
	pairs.PairEq,
	pairs.Fst,
	pairs.Snd,
}

// CategoryOpsData — the record `category_ops(A, M)`: `mk_category(Ob,
// Mor, src, tgt, ident, comp)` packs a category's objects, morphisms,
// source, target, identity and composition. Under a binder C of the
// type, `C.objects` is the set of objects, `C.source(f)` the source of
// a morphism and `C.compose(g, f)` the composite, g after f.
var CategoryOpsData = family.DefineData(registry.DataEntry{
	Name:   "CategoryOps",
	Type:   "category_ops",
	Params: []string{"A", "M"},
	Constructors: []proof.DataConstructorSpec{
		{Name: "mk_category", Args: []string{"set(A)", "set(M)", "M → A", "M → A", "A → M", "M → M → M"}},
	},
	Fields: []registry.DataField{
		{Name: "CategoryObjectsDef", Const: "category_objects", Field: "objects"},
		{Name: "CategoryMorphismsDef", Const: "category_morphisms", Field: "morphisms"},
		{Name: "CategorySourceDef", Const: "category_source", Field: "source"},
		{Name: "CategoryTargetDef", Const: "category_target", Field: "target"},
		{Name: "CategoryIdentityDef", Const: "category_identity", Field: "identity"},
		{Name: "CategoryComposeDef", Const: "category_compose", Field: "compose"},
	},
	Principles: registry.DataPrinciples{
		Induction:      "CategoryOpsInduction",
		Recursion:      "CategoryOpsRecursion",
		Injective:      "MkCategoryInjective",
		Extensionality: "CategoryOpsEq",
	},
	Deps: recordRows,
})

// FunctorOpsData — the record `functor_ops(A, M, B, N)`: `mk_functor(F₀,
// F₁)` packs a functor's map of objects and map of morphisms, from a
// category on the types A and M to one on the types B and N. Under a
// binder F of the type, `F.obj(x)` is the image of an object and
// `F.map(f)` the image of a morphism. The door asks its parameter
// letters in ascending order, so they are spelled A, B, C, D here; the
// positions are the source's objects and morphisms, then the target's.
var FunctorOpsData = family.DefineData(registry.DataEntry{
	Name:   "FunctorOps",
	Type:   "functor_ops",
	Params: []string{"A", "B", "C", "D"},
	Constructors: []proof.DataConstructorSpec{
		{Name: "mk_functor", Args: []string{"A → C", "B → D"}},
	},
	Fields: []registry.DataField{
		{Name: "FunctorObjDef", Const: "functor_obj", Field: "obj"},
		{Name: "FunctorMapDef", Const: "functor_map", Field: "map"},
	},
	Principles: registry.DataPrinciples{
		Induction:      "FunctorOpsInduction",
		Recursion:      "FunctorOpsRecursion",
		Injective:      "MkFunctorInjective",
		Extensionality: "FunctorOpsEq",
	},
	Deps: recordRows,
})

// MorphismTripleData — the record `morphism_triple(A, D)`:
// `mk_morphism(x, y, f)` frames a datum f of a type D by its source x
// and target y, objects of a type A. Under a binder t of the type,
// `t.source`, `t.target` and `t.map` are its three parts.
var MorphismTripleData = family.DefineData(registry.DataEntry{
	Name:   "MorphismTriple",
	Type:   "morphism_triple",
	Params: []string{"A", "D"},
	Constructors: []proof.DataConstructorSpec{
		{Name: "mk_morphism", Args: []string{"A", "A", "D"}},
	},
	Fields: []registry.DataField{
		{Name: "TripleSourceDef", Const: "triple_source", Field: "source"},
		{Name: "TripleTargetDef", Const: "triple_target", Field: "target"},
		{Name: "TripleMapDef", Const: "triple_map", Field: "map"},
	},
	Principles: registry.DataPrinciples{
		Induction:      "MorphismTripleInduction",
		Recursion:      "MorphismTripleRecursion",
		Injective:      "MkMorphismInjective",
		Extensionality: "MorphismTripleEq",
	},
	Deps: recordRows,
})
