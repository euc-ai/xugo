// vocab.go — the statement vocabulary the chapter's members are
// written in. The chapter's constant is defined in definitions.go.

package nat_prime

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/internal/natvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// natDividesType is `nat_divides`'s type — nat_num/nat_divides's predicate,
// which this chapter is written over and never re-mints — spelled by
// hand for the members that build over it as a term.
var natDividesType = MakeFun(NumType, NumType, TypeBool)

// vocab is the chapter alphabet as data — one row per name, the family
// installing them into each member's ParseScope (family.go's
// WithVocabSpec).
//
// The four names are ℕ's, and they are what the chapter is about; the
// def-carrying `nat_divides` meta's row is also what makes the mixfix
// `∣` resolve to it rather than to the parser's own bare surface
// constant. ℕ's arithmetic (`+ * ≤ <` and the numerals) needs no row:
// the text parser supplies it.
var vocab = registry.NewVocabSpec(natvocab.Table()).
	OpsName("primeOps").
	Defined("nat_prime").   // the minted meta is the one type authority
	Defined("nat_divides"). // the sibling's mint (nat_num/nat_divides)
	Defined("nat_coprime"). // the sibling's mint (nat_num/nat_gcd)
	Defined("nat_gcd")      // likewise
