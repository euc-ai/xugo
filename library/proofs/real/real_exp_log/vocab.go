// vocab.go — the chapter's statement vocabulary: its numeric domain
// alone. exp and log are functions of a real, so an `&` that no
// neighbouring operand anchors is ℝ's embedding by declaration.

package real_exp_log

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/internal/realvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — the domain alone.
var vocab = registry.NewVocabSpec(realvocab.Table()).
	OpsName("expLogOps").
	CoerceDomain(RealDomain)
