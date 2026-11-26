// vocab.go — the chapter's statement vocabulary.
//
// A stated name resolves through its mint without a row, so a row
// buys one of two things only: a handle a body builds with, or a
// pinned instance of a polymorphic constant. This chapter's bodies
// build nothing — every term is spelled as text against the chapter
// scope — so its one row is the pin the statements need: 𝕌.
// It is nullary and polymorphic, so an undeclared 𝕌 would freshen
// silently at whatever type the statement happened to fix, and the
// only universe here is ℕ's, the index set every sequence ranges
// over. Pinned, the statements write `image(a, 𝕌)` bare. The family
// installs the row into each member's ParseScope.
//
// Beside the pin, the chapter declares its numeric domain: the values
// of a sequence are reals, so an `&` that no neighbouring operand
// anchors — `&0 < &1` — is ℝ's embedding by declaration.

package real_sequences

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/internal/realvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// numSetT is ℕ's set type, the instance 𝕌 is pinned at.
func numSetT() HolType { return MakeFun(NumType, TypeBool) }

// vocab is the chapter alphabet as data — the domain and one row, the pin.
var vocab = registry.NewVocabSpec(realvocab.Table()).
	OpsName("sequenceOps").
	CoerceDomain(RealDomain).
	Spelled("universe", numSetT).As("Naturals")
