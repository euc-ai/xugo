// vocab.go — the chapter's alphabet, declared once.
//
// A comparison of sizes is a statement about a map between two sets, so
// the alphabet is membership and the chapter's own four relations; the
// universe enters with `countable`, whose yardstick is the set of all
// naturals. Each name's type is read off its mint.

package cardinal

import (
	"github.com/euc-ai/xugo/library/proofs/sets/internal/setvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data: the family installs it into
// every member's ParseScope (family.go's WithVocabSpec), and the vocab
// generator renders the build surface from it (zz_vocab_gen.go).
var vocab = registry.NewVocabSpec(setvocab.Table()).
	OpsName("cardinalOps").
	Term("set_member"). // where a point lies
	// ℕ as a set, the yardstick of countability
	Poly("universe").
	Term("card_le").Term("card_eq").Term("card_lt").Term("countable") // the chapter's own relations
