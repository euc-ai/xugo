package real_closure

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_closure.cnf.pb
var familyCNF []byte

// family is the family handle. The chapter reads algebraic_closure's table,
// whose «closureEmbedding» is the embedding of a field's carrier into the
// host of its algebraic closure.
var family = registry.NewFamily("algebra/field/real_closure", familyCNF).WithOuterAbbrev(
	algebraic_closure.ChapterAbbrev)
