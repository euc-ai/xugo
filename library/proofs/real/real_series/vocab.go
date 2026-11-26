// vocab.go — the chapter's statement vocabulary: its numeric domain
// alone. A series' terms and sums are reals, so an `&` that no
// neighbouring operand anchors — the `&0` the terms of a convergent
// series tend to — is ℝ's embedding by declaration.

package real_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/internal/realvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — the domain alone.
var vocab = registry.NewVocabSpec(realvocab.Table()).
	OpsName("seriesOps").
	CoerceDomain(RealDomain)
