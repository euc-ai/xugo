package sobolev_section

import (
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

var SobolevLocalizationData = family.DefineData(registry.DataEntry{
	Name: "SobolevLocalization", Type: "sobolev_localization", Params: []string{"A"},
	Constructors: []proof.DataConstructorSpec{{
		Name: "sobolev_localization_data",
		Args: []string{"num", "num → prod(set(A), A → num → real)", "num → A → real"},
	}},
	Fields: []registry.DataField{
		{Name: "LocalizationCountDef", Const: "sobolev_localization_count", Field: "count"},
		{Name: "LocalizationChartsDef", Const: "sobolev_localization_charts", Field: "charts"},
		{Name: "LocalizationPartitionDef", Const: "sobolev_localization_partition", Field: "partition"},
	},
	Principles: registry.DataPrinciples{
		Induction:      "LocalizationInduction",
		Recursion:      "LocalizationRecursion",
		Injective:      "LocalizationInjective",
		Extensionality: "LocalizationExtensionality",
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
