// vocab.go — the chapter's statement vocabulary.
//
// peano's alphabet spans two types, because the chapter's whole subject
// is the passage between them: `ind`, where the axiom of infinity gives
// an injection missing a point, and `num`, carved out of `ind` by the
// is_num predicate. The `num` half's TYPES live in the ℕ domain's
// natvocab table; the `ind`-typed bootstrap layer is deliberately NOT
// in that table — it is the alphabet of this one chapter's
// construction, not names of the domain — so those rows spell their
// types here (the Spelled rows). The family installs the rows into
// each member's ParseScope (family.go's WithVocabSpec), and the build
// surface members take with `v := ops(a.Ctx())` is rendered from the
// same rows (zz_vocab_gen.go).
//
// `ind` itself is this chapter's: the axiom of infinity introduces it
// (peano.go: Infinity), and nothing below the chapters mentions it.

package peano

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/internal/natvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// Ind is `ind`, the type of individuals, as a phantom of the typed term
// surface — declared beside the axiom that introduces the type, per
// the phantom vocabulary's decentralization rule
// (ext/holtype_phantom.go). A signature over the chapter reads
// `Typed[Ind]` exactly as its statement reads `x:ind`.
type Ind struct{}

func (Ind) Reify() ext.HolType { return MakeType("ind") }

// The `ind` layer's types — what the Spelled rows below need and the
// domain table deliberately does not carry.
var vocab = registry.NewVocabSpec(natvocab.Table()).
	OpsName("peanoOps").
	Term("ind_zero").As("IndZero").
	Term("ind_suc").
	Term("is_num").
	Term("mk_num").
	Term("dest_num").
	Term("_0").As("Zero").
	Term("suc")
