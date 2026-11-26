// vocab.go — the chapter's statement vocabulary as data.
//
// The vocabulary spans two floors: the hreal quotient's own constants
// (the class map, the lifted operations) and the slope-side subset
// (nadd_eq and the operations it descends) — every member's statement
// or proof talks across the quotient boundary. A closure body holds
// the handles as a local (`v := ops(ctx)`).

package nonneg_real

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name; every
// constant reads its type off its mint.
var vocab = registry.NewVocabSpec(nil).
	OpsName("hrealVocab").
	// Declaration-only nadd operations: statements name them —
	// nadd_inv literally, nadd_add / nadd_mul / nadd_le through the
	// + * ≤ surface at nadd operands, which resolves scope-first to
	// these metas — and no body builds with them.
	Defined("nadd_le").
	Defined("nadd_add").
	Defined("nadd_mul").
	Defined("nadd_inv").
	// The quotient floor: the class map (⁅x⁆), the bijection underneath
	// it, and the lifted operations.
	Defined("hreal_of_nadd").
	Defined("mk_hreal").
	Defined("dest_hreal").
	Defined("hreal_add").
	Defined("hreal_mul").
	Defined("hreal_le").
	Defined("hreal_inv").
	Defined("hreal_of_num").
	// The slope-side bridge.
	Defined("nadd_eq")

// Hreal is `:hreal` — the non-negative reals this family mints as the
// quotient of nadd by nadd_eq — as a phantom of the typed term
// surface, declared beside the mint per the vocabulary's
// decentralization rule (ext/holtype_phantom.go).
type Hreal struct{}

func (Hreal) Reify() ext.HolType { return MakeType("hreal") }
