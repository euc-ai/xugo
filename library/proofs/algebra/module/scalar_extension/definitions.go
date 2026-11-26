package scalar_extension

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/tensor_product"
	"github.com/euc-ai/xugo/library/registry"
)

// tensorScalarActionDef — `tensor_scalar_action(S, R, V, a)`: the map a ⊗ id
// on R ⊗ₛ V, chosen as an S-linear endomorphism taking b ⊗ v to (a · b) ⊗ v.
var tensorScalarActionDef = tensorScalarActionDefThm{family.Define(registry.DefEntry{
	Name:  "tensorScalarActionDef",
	Key:   "prop_af84235ebcff2a73",
	Deps:  []registry.EntryLike{},
	Const: "tensor_scalar_action",
	Type: "ring_ops(A) → " +
		"ring_ops(A) → " +
		"module_ops(A, B) → " +
		"A → " +
		"set(prod(A, B) → A) → " +
		"set(prod(A, B) → A)",
	Equations: []string{
		"∀S R:ring_ops(A). ∀V:module_ops(A, B). ∀a:A. " +
			"    tensor_scalar_action(S, R, V, a) = " +
			"    εf:(set(prod(A, B) → A) → set(prod(A, B) → A)). " +
			"        module_homomorphism(S, " +
			"            tensor_module(S, regular_module(R), V), " +
			"            tensor_module(S, regular_module(R), V), " +
			"            f) ∧ " +
			"        (∀b:A. ∀v:B. " +
			"            b ∈ R.carrier ∧ v ∈ V.carrier ⇒ " +
			"            f(tensor(S, regular_module(R), V, b, v)) = " +
			"            tensor(S, regular_module(R), V, R.mul(a, b), v))",
	},
})}

// ScalarExtensionDef — `scalar_extension(S, R, V)`: R ⊗ₛ V as a module
// record, with the tensor module's points and addition and with R acting on
// the first factor by `tensor_scalar_action`.
var ScalarExtensionDef = scalarExtensionDefThm{family.Define(registry.DefEntry{
	Name:  "ScalarExtensionDef",
	Key:   "prop_a7d9911fe39b8146",
	Deps:  []registry.EntryLike{tensorScalarActionDef},
	Const: "scalar_extension",
	Type:  "ring_ops(A) → ring_ops(A) → module_ops(A, B) → module_ops(A, set(prod(A, B) → A))",
	Equations: []string{
		"∀S R:ring_ops(A). ∀V:module_ops(A, B). " +
			"    scalar_extension(S, R, V) = " +
			"    mk_module(tensor_module(S, regular_module(R), V).add, " +
			"        tensor_module(S, regular_module(R), V).zero, " +
			"        tensor_module(S, regular_module(R), V).neg, " +
			"        tensor_scalar_action(S, R, V), " +
			"        tensor_module(S, regular_module(R), V).carrier)",
	},
})}

// ScalarExtensionMapDef — `scalar_extension_map(S, R, V, W, f)`: the map
// id ⊗ f from R ⊗ₛ V to R ⊗ₛ W. A map out of the tensor quotient comes from
// its universal property, which gives existence and no term, so this one is
// chosen: an R-linear map taking a ⊗ v to a ⊗ f(v). That description determines
// it on the carrier only, and off the carrier the choice is unconstrained,
// which is why every functor law is stated at a point of the carrier and none
// as an equation of functions.
var ScalarExtensionMapDef = scalarExtensionMapDefThm{family.Define(registry.DefEntry{
	Name:  "ScalarExtensionMapDef",
	Key:   "prop_ed404878bf495188",
	Deps:  []registry.EntryLike{ScalarExtensionDef},
	Const: "scalar_extension_map",
	Type: "ring_ops(A) → " +
		"ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"(B → C) → " +
		"set(prod(A, B) → A) → " +
		"set(prod(A, C) → A)",
	Equations: []string{
		"∀S R:ring_ops(A). ∀V:module_ops(A, B). ∀W:module_ops(A, C). ∀f:(B → C). " +
			"    scalar_extension_map(S, R, V, W, f) = " +
			"    εg:(set(prod(A, B) → A) → set(prod(A, C) → A)). " +
			"        module_homomorphism(R, scalar_extension(S, R, V), scalar_extension(S, R, W), g) ∧ " +
			"        (∀a:A. ∀v:B. " +
			"            a ∈ R.carrier ∧ v ∈ V.carrier ⇒ " +
			"            g(tensor(S, regular_module(R), V, a, v)) = tensor(S, regular_module(R), W, a, f(v)))",
	},
})}
