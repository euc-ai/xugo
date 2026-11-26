package principal_ideal_domain

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed principal_ideal_domain.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/module/principal_ideal_domain", familyCNF).WithOuterAbbrev(
	free_module.ChapterAbbrev, polynomial_division.ChapterAbbrev)
