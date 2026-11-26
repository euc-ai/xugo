// vocab.go — the chapter's statement vocabulary as data.
//
// treal values are pairs (a, b) : hreal × hreal, thought of as the
// formal difference a − b. Every treal operation unfolds to a
// component-wise hreal expression, and treal_eq unfolds to the
// cross-sum identity `(fst(x) + snd(y)) = (fst(y) + snd(x))` — no
// quotient here, this layer's proofs live entirely on the hreal side
// after one def-unfold of a treal constant. The vocabulary therefore
// spans two floors: the treal operations themselves, and the
// hreal-side subset every proof reduces to. A closure body holds the
// handles as a local (`v := ops(ctx)`).

package nonneg_real_formal_diff

import "github.com/euc-ai/xugo/library/registry"

// vocab is the chapter alphabet as data — one row per name; every
// constant reads its type off its mint.
var vocab = registry.NewVocabSpec(nil).
	OpsName("trealVocab").
	// Declaration-only treal constants: statements and Unfolds name
	// them — treal_neg / treal_inv / treal_of_num / treal_le literally,
	// treal_add also through the + surface at the pair type, which
	// resolves scope-first to these metas — and no body builds with
	// them.
	Defined("treal_add").
	Defined("treal_neg").
	Defined("treal_inv").
	Defined("treal_of_num").
	Defined("treal_le").
	// The treal floor a body builds with.
	Defined("treal_mul").
	Defined("treal_eq").
	// The hreal-side subset the proofs reduce to.
	Defined("hreal_add").
	Defined("hreal_mul").
	Defined("hreal_inv").
	Defined("hreal_le").
	Defined("hreal_of_num")
