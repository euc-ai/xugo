// vocab.go — the statement vocabulary the chapter's members are
// written in. The chapter's constant is defined in definitions.go.

package nat_congruence

import (
	"github.com/euc-ai/xugo/library/proofs/nat_num/internal/natvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name, the family
// installing them into each member's ParseScope (family.go's
// WithVocabSpec).
//
// `nat_cong` and `nat_mod` are what the statements are written with, their
// rows resolving both to the definition-carrying metas rather than to
// the parser's own bare surface constants — `nat_cong` being what the
// mixfix `x ≡ y (mod n)` lowers to at three num operands.
var vocab = registry.NewVocabSpec(natvocab.Table()).
	OpsName("congOps").
	Defined("nat_cong"). // the minted meta is the one type authority
	Term("nat_mod")      // the operation the definition computes with
