// records.go — the operations, degree carriers and differential of a complex.

package chain_complex

import (
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ComplexOpsData — common vector operations, a carrier in every degree,
// and a differential. The chain or cochain predicate supplies its laws.
var ComplexOpsData = family.DefineData(registry.DataEntry{
	Name: "ComplexOps", Type: "complex_ops", Params: []string{"A", "B"},
	Constructors: []proof.DataConstructorSpec{{
		Name: "pack_complex",
		Args: []string{"B → B → B", "B", "B → B", "A → B → B", "num → set(B)", "num → B → B"},
	}},
	Fields: []registry.DataField{
		{Name: "ComplexAddDef", Const: "complex_ops_add", Field: "add"},
		{Name: "ComplexZeroDef", Const: "complex_ops_zero", Field: "zero"},
		{Name: "ComplexNegDef", Const: "complex_ops_neg", Field: "neg"},
		{Name: "ComplexSmulDef", Const: "complex_ops_smul", Field: "smul"},
		{Name: "ComplexTermsDef", Const: "complex_ops_terms", Field: "terms"},
		{Name: "ComplexDifferentialDef", Const: "complex_ops_differential", Field: "d"},
	},
	Principles: registry.DataPrinciples{
		Induction:      "ComplexOpsInduction",
		Recursion:      "ComplexOpsRecursion",
		Injective:      "MkComplexInjective",
		Extensionality: "ComplexOpsEq",
	},
	Deps: []registry.EntryLike{
		datatype_universe.Recursion,
		datatype_universe.FamilyCons,
		datatype_universe.NodeInjective,
		pairs.PairEq,
		pairs.Fst,
		pairs.Snd,
	},
})

// ComplexModuleDef — the module data at one degree of a complex.
var ComplexModuleDef = complexModuleDefThm{family.Define(registry.DefEntry{
	Name: "ComplexModuleDef", Const: "complex_module",
	Key:  "prop_be6badedb7947450",
	Type: "complex_ops(A, B) → num → module_ops(A, B)",
	Equations: []string{
		"∀P:complex_ops(A, B). ∀n:num. " +
			"    complex_module(P, n) = mk_module(P.add, P.zero, P.neg, P.smul, P.terms(n))",
	},
	Deps: []registry.EntryLike{
		ComplexAddDef,
		ComplexZeroDef,
		ComplexNegDef,
		ComplexSmulDef,
		ComplexTermsDef,
	},
})}
