// vocab.go — the chapter's statement vocabulary.
//
// Every nat_monus statement is written in the same alphabet: truncated
// subtraction and its predecessor, the distance function and the pair
// it is stated over, the ℕ operations the compensation laws are written
// in, and the order relations the case splits run on. The TYPES live in
// the ℕ domain's natvocab table; the rows below state WHICH names this
// chapter's statements spell — the family installs them into each
// member's ParseScope (family.go's WithVocabSpec), and the build
// surface members take with `v := ops(a.Ctx())` is rendered from the
// same rows (zz_vocab_gen.go).

package nat_monus

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/internal/natvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name.
var vocab = registry.NewVocabSpec(natvocab.Table()).
	OpsName("monusOps").
	Term("suc").As("SucOp"). // the Suc shorthand below builds suc(a)
	Term("predecessor").
	Term("_0").As("Zero").
	Term("+").As("Plus").
	Term("*").As("Times").
	Term("-").As("Minus").
	Term("nat_dist").     // the symmetric distance, stated over the ℕ pair
	Term(",").As("Pair"). // the pair constructor dist's laws are stated over
	Term("<=").As("Le").
	Term("<").As("Lt")

// Term-building shorthands, so a witness list reads as arithmetic
// rather than as applications.

// Add is a + b.
func (v *monusOps) Add(a, b Term) Term { return v.Plus.Apply(a, b) }

// Mul is a · b.
func (v *monusOps) Mul(a, b Term) Term { return v.Times.Apply(a, b) }

// Suc is suc(a).
func (v *monusOps) Suc(a Term) Term { return v.SucOp.Apply(a) }

// LessEq is the order atom a ≤ b.
func (v *monusOps) LessEq(a, b Term) Term { return v.Le.Apply(a, b) }

// LessThan is the order atom a < b.
func (v *monusOps) LessThan(a, b Term) Term { return v.Lt.Apply(a, b) }
