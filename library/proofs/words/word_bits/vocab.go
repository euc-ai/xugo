// vocab.go — the chapter's statement vocabulary: the words substrate's
// alphabet, embedded whole from words/machine_word, the definitional home
// of the minted constants.

package word_bits

import (
	"github.com/euc-ai/xugo/library/proofs/words/machine_word"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — the carrier bundle, one row.
var vocab = registry.NewVocabSpec(nil).Embed(machine_word.Bundle)
