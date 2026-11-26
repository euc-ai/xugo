package baire_category

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed baire_category.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("topology/baire_category", familyCNF).WithAbbrev(Abbrev{
	{Name: "prodTop", Text: "product_topology(metric_topology(M, d), metric_topology(M, d))"},
})
