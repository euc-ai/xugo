package cech_cohomology

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed cech_cohomology.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("topology/cech_cohomology", familyCNF)
