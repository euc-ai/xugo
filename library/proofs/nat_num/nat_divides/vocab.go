// vocab.go — the statement vocabulary the chapter's members are
// written in. The chapter's constant is defined in definitions.go.

package nat_divides

import (
	"github.com/euc-ai/xugo/library/proofs/nat_num/internal/natvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name, the family
// installing them into each member's ParseScope (family.go's
// WithVocabSpec).
//
// `nat_divides` is ours, and it is what the mixfix `∣` denotes at num;
// its row puts the definition-carrying meta where the parser looks
// first, so `∣` resolves to it rather than to the parser's own bare
// surface constant. ℕ's arithmetic (`+ * ≤ <` and the numerals) needs
// no row: the text parser supplies it.
var vocab = registry.NewVocabSpec(natvocab.Table()).
	OpsName("dividesOps").
	Defined("nat_divides") // the minted meta is the one type authority
