// vocab.go — the chapter's statement vocabulary as data.
//
// The vocabulary spans three layers the completeness spur touches:
// the nadd slope operations, ℕ arithmetic + the numeral-encoding
// constants, and the hreal quotient's own operations. Files that also
// mention the pair constructor "," or the real/treal floor declare
// those inline — polymorphic "," conflicts across layers (num-prod vs
// hreal-prod), and the real/treal vocabulary is file-local (see
// real_hreal_lemma1's realHrealVocab for the transport-side vocab and
// real_complete's local declarations for the real-group operations).
// A closure body holds the handles as a local (`v := ops(ctx)`).

package real_completeness

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

func naddType() HolType { return MakeType("nadd") }

// vocab is the chapter alphabet as data — one row per name; every
// constant reads its type off its mint.
var vocab = registry.NewVocabSpec(nil).
	OpsName("completeVocab").
	// Declared for the parser and held by nobody: numerals reach
	// statement texts as literals (`nadd_of_num(2)`) and bodies build
	// them with `ctx.Numeral`, so the chapter needs the names resolvable
	// but never applies them itself.
	Term("bit0").
	Term("bit1").
	// The chapter's standard free variables (the sequent-chapter half):
	// ArchZero's headline reads x and k free, sequent-style, and the
	// statement doors resolve strictly — a free name must be declared.
	// Bodies re-declare them at the same type (Var is idempotent);
	// binders shadow them as usual.
	Free("x", naddType).
	Free("k", naddType).
	// Declaration-only: statement texts name these — is_nadd literally,
	// <= and hreal_le
	// through the ≤ surface at num / hreal operands, which resolves
	// scope-first to these metas — and no body builds with them.
	Defined("is_nadd").
	Term("<=").As("Le").
	Defined("hreal_le").
	// The nadd (slope) layer.
	Defined("dest_nadd").
	Defined("mk_nadd").
	Defined("nadd_eq").
	Defined("nadd_le").
	Defined("nadd_add").
	Defined("nadd_mul").
	Defined("nadd_of_num").
	// ℕ arithmetic and the numeral base.
	Term("+").As("Plus").
	Term("*").As("Times").
	Term("suc").As("Suc").
	Term("_0").As("Zero").
	// The hreal quotient.
	Defined("mk_hreal").
	Defined("hreal_of_nadd").
	Defined("hreal_of_num")
