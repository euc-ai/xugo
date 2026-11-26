// vocab.go — the chapter's statement vocabulary as data.
//
// This layer's proofs live entirely on the real side until the
// definitions compute at the classes: a law over ℝ inducts each binder
// to a pre-real, the lifted operations compute at the classes and class
// equality reads as treal_eq, and the residual is the `treal`-side
// statement proved in `nonneg_real_formal_diff`. The vocabulary therefore spans two
// floors: the real operations themselves, and the treal-side subset
// every proof reduces to. A body that builds terms takes the handles
// in one line — a `family.Sections` closure local (`v := ops(ctx)`), or
// `ops(a.Ctx())` inside a `family.Theorem` body.

package real_construction

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/internal/realvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name. The
// CoerceDomain row makes an unanchored `&` in a statement text ℝ by
// DECLARATION, not by global default — the embedding lemmas
// (`&m ≤ &n ⇔ m ≤ n`) are exactly the shape nothing anchors.
var vocab = registry.NewVocabSpec(realvocab.Table()).
	OpsName("realVocab").
	CoerceDomain(RealDomain).
	// Declaration-only treal floor: statements name these — treal_neg /
	// treal_inv / treal_of_num literally, treal_add / treal_mul /
	// treal_le through the + * ≤ surface at the pair type, which
	// resolves scope-first to these metas — and no body builds with
	// them. They are construction constants, not part of ℝ's statement
	// alphabet, so they read their types off nonneg_real_formal_diff's mints rather
	// than off the domain alphabet.
	Defined("treal_add").
	Defined("treal_mul").
	Defined("treal_neg").
	Defined("treal_inv").
	Defined("treal_of_num").
	Defined("treal_le").
	// The real floor's types come from the ℝ domain alphabet, so this
	// family states WHICH names it uses and the domain states what each
	// one is — the same route real_ring, real_field and real_order_ring
	// take.
	Term("real_add").
	Term("real_mul").
	Term("real_neg").
	Term("real_inv").
	Term("real_of_num").
	Term("real_le").
	// treal_eq — the equivalence the quotient is taken by (nonneg_real_formal_diff's
	// constant); real_of_treal — the class map (⁅p⁆); mk_real /
	// dest_real — the bijection underneath it.
	Defined("treal_eq").
	Defined("real_of_treal").
	Defined("mk_real").
	Defined("dest_real")
