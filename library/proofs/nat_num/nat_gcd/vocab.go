// vocab.go — the statement vocabulary the chapter's members are
// written in. The chapter's constants are defined in definitions.go.

package nat_gcd

import (
	"github.com/euc-ai/xugo/library/proofs/nat_num/internal/natvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name, the family
// installing them into each member's ParseScope (family.go's
// WithVocabSpec).
//
// The three names are ℕ's, and they are what the chapter is about —
// `nat_divides` being what the mixfix `∣` denotes at num. ℕ's
// arithmetic (`+ * nat_div nat_mod ≤` and the numerals) needs no row: the text
// parser supplies it.
//
// No ℤ vocabulary: no statement in the chapter names an integer.
var vocab = registry.NewVocabSpec(natvocab.Table()).
	OpsName("gcdOps").
	Defined("nat_gcd").     // the minted meta is the one type authority
	Defined("nat_coprime"). // likewise
	Defined("nat_divides")  // the sibling's mint (nat_num/nat_divides)
