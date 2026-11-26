// vocab.go — the statement vocabulary the chapter's members are
// written in, and the bundle the reading-face chapters embed. The
// chapter's constants are defined in definitions.go.

package machine_word

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ConstMeta fetches an already-registered constant's canonical meta —
// the one every other proof reads, never a look-alike. Exported for
// the reading-face chapters that build terms over the chapter's
// constants.
func ConstMeta(name string) core.ConstTermMeta {
	meta, ok := registry.GetConstMetaManager().LoadConstMeta(core.TermName(name))
	if !ok || meta.IsZero() {
		panic(
			"words/machine_word: const " + name + " is not registered — the ℕ arithmetic vocabulary has not been loaded")
	}
	return meta
}

// vocab is the chapter alphabet as data: the alphabet the chapter's
// statement and proof texts are written in — the minted operations,
// the ℕ vocabulary the val-face twins read them through (nat_mod/nat_div/nat_pow,
// COND at num), and ℕ's congruence, which the CONG twins state. Every
// minted name reads its type off its mint; COND alone is pinned by
// hand, at the num instance the twins state it at. The ops struct is
// EXPORTED because the reading-face chapters embed it (Bundle below).
var vocab = registry.NewVocabSpec(nil).
	OpsName("WordOps").
	Defined("word_add").
	Defined("word_mul").
	Defined("word_neg").
	Defined("word_sub").
	Defined("word_unsigned_div").
	Defined("word_unsigned_mod").
	Defined("word_bit").
	Term("nat_odd").
	Term("suc").
	Defined("bit_value").
	Defined("word_bitwise_unary").
	Defined("word_bitwise_binary").
	Defined("word_of_bits").
	Defined("word_and").
	Defined("word_or").
	Defined("word_xor").
	Defined("word_not").
	Term("nat_mod").
	Term("nat_div").
	Term("nat_pow").
	Spelled(
		"COND",
		func() core.HolType {
			return core.MakeFun(
				core.TypeBool(), ext.NumType, ext.NumType, ext.NumType)
		}).
	// nat_min/nat_max name the sharper bound the order twins state — the meet
	// sits below the smaller operand, the join above the larger — and
	// each unfolds at term level to a COND on the same test.
	Term("nat_min").
	Term("nat_max").
	// ℕ's congruence — nat_num/nat_congruence's definition, what the mixfix
	// `x ≡ y (mod m)` denotes at num. Read off the manager so the
	// definition-carrying meta is the one the CONG members unfold; the
	// import that guarantees the definition has run is values.go's typed
	// cite of that chapter.
	Term("nat_cong")

// NewWordOps builds the alphabet's handles — the constructor the
// reading-face chapters' generated surfaces embed.
func NewWordOps(ctx *proof.Script) WordOps { return *ops(ctx) }

// Bundle is the words alphabet as a domain-owned bundle. The four
// reading-face chapters (word_bits, bit_set, bitwise_algebra, bit_arith) state the
// names this chapter mints, so each embeds the bundle whole rather
// than restating the list; installing it declares every row above.
var Bundle = registry.Bundle{
	Path: "github.com/euc-ai/xugo/library/proofs/words/machine_word",
	Pkg:  "machine_word", Type: "WordOps", New: "NewWordOps",
	Install: func(ctx *proof.Script) { vocab.Install(ctx) },
}
