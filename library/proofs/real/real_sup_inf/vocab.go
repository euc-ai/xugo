// vocab.go — the chapter's statement vocabulary.
//
// The extrema chapter states everything in one alphabet: the two
// binary operations, the order they are defined by and compared under,
// and — as the set wing lands — the set-level operators and their
// attained-bound relations. The declarations live here rather than as
// a `ctx.Const` preamble per proof, because which names a chapter uses
// is a fact about the chapter. The family installs the rows into each
// member's ParseScope (family.go's WithVocabSpec), and the build
// surface members take with `v := ops(a.Ctx())` is rendered from the
// same rows (zz_vocab_gen.go).
//
// The ℝ names' types come from the domain alphabet
// (real/internal/realvocab), so this chapter states WHICH names it
// uses and the domain states what each one is. The rest of the
// alphabet cannot come from a table and is Spelled here, in two
// groups.
//
// The SET surface the sup/inf statements speak, at the ℝ instance —
// the same local-declaration arrangement as the ℕ constants below
// (setvocab is internal to sets/). subset has its row for the ⊆ in the
// comparison statements, which parses to it.
//
// The ℕ constants are the transport members' subjects: they state ℕ's
// own lattice on one side of an equation. They are spelled inline
// rather than through an alphabet because ℕ has none: `int_num`,
// `real`, `sets` and `words` each own an `internal/…vocab` table,
// `nat_num` does not, so every chapter outside it that states a ℕ
// constant spells the type itself. `sets/num_segment/vocab.go` does
// exactly this for the same ℕ names, and `real/tower/real_completeness` and
// `real/tower/internal/eudoxus_slope` do it for `<=` and `suc` inside this
// very domain.

package real_sup_inf

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/internal/realvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// The type spellings the domain table cannot supply: the ℝ-set surface
// and ℕ's own lattice.
func realSetT() HolType  { return MakeFun(MakeType("real"), TypeBool) }
func memT() HolType      { return MakeFun(MakeType("real"), MakeFun(realSetT(), TypeBool)) }
func setRelT() HolType   { return MakeFun(realSetT(), MakeFun(realSetT(), TypeBool)) }
func setPredT() HolType  { return MakeFun(realSetT(), TypeBool) }
func insertT() HolType   { return MakeFun(MakeType("real"), MakeFun(realSetT(), realSetT())) }
func setBinOpT() HolType { return MakeFun(realSetT(), MakeFun(realSetT(), realSetT())) }
func numBinOpT() HolType { return MakeFun(NumType, MakeFun(NumType, NumType)) }
func numRelT() HolType   { return MakeFun(NumType, MakeFun(NumType, TypeBool)) }

// vocab is the chapter alphabet as data — one row per name.
//
// Le is what Guard below is built from. The embedded literals come
// from the domain's shared builder (the NumeralsBundle row): the
// relation wing needs `&1` as a TERM — it manufactures a value on the
// far side of an attained bound (`l ± &1`) and grounds the order laws
// there — which a parse-only declaration of real_of_num cannot supply.
//
// The two attained-bound relations are spelled by existence.go's
// statements and named by its Unfolds, nothing more.
// (`&m` parses through real_of_num, which the NumeralsBundle declares.)
//
// finite is statement-only: the attainment statements spell it and
// nothing else. insert and union are the sets the structural equations
// COMPUTE with — `{a}`, a set with one or two points laid on top of
// it, and two sets side by side — in each case because a law that
// quantifies over the SET is cited raw and has to be handed the
// constructed set itself. Sing below names the singleton case the two
// shortest equations are about.
//
// empty_set is polymorphic-nullary, so an undeclared ∅ would freshen
// silently; declaring it here — the Custom row, which pins it at the ℝ
// instance in every member's ParseScope at install — is what pins it.
// The Built row beside it reproduces the same pinned constant as the
// build handle, so the declaration and the handle cannot drift.
//
// The binary pair real_max / real_min is built, not merely spelled, by
// the structural equations: the insertion equations state a set whose
// new point is `real_max(a, b)`, and that term is what a ground cite
// of the same-bounds law has to be handed. ℕ's own nat_max / nat_min are
// statement-only, same arrangement as the two relations above: the transport
// members' statements and Unfolds name them, no body builds with them.
//
// Add and Sub build the relation wing's two values past an attained
// bound, `l + &1` and `l - &1`.
var vocab = registry.NewVocabSpec(realvocab.Table()).
	OpsName("extremaOps").
	CoerceDomain(RealDomain).
	Embed(realvocab.NumeralsBundle).
	Term("real_le").As("Le").
	Term("real_sup").
	Term("real_inf").
	Term("real_has_sup").
	Term("real_has_inf").
	Spelled("set_member", memT).As("Mem").
	Spelled("subset", setRelT).
	Spelled("finite", setPredT).
	Spelled("insert", insertT).
	Spelled("union", setBinOpT).
	Custom(func(ctx *Script) { ctx.Const("empty_set", realSetT()) }).
	Built("Empty", func(ctx *Script) *TermWrapper { return ctx.Const("empty_set", realSetT()) }).
	Spelled("nat_max", numBinOpT).As("NumMax").
	Spelled("nat_min", numBinOpT).As("NumMin").
	Spelled("<=", numRelT).As("NumLe").
	Term("real_max").As("Max").
	Term("real_min").As("Min").
	Term("real_add").As("Add").
	Term("real_sub").As("Sub")

// Guard is `x ≤ y` — the comparison both ℝ definitions branch on, and
// the term every member of real_sup_inf.go splits on. Named for the role it
// plays rather than for the relation it builds.
func (v *extremaOps) Guard(x, y Term) Term { return v.Le.Apply(x, y) }

// NumGuard is `m ≤ n` on ℕ — the guard ℕ's own nat_max and nat_min test, and
// the term the transport members split on. They split on the ℕ side
// rather than the ℝ side because that is where the branch hypothesis
// decides BOTH definitions: the ℝ guard follows from it, while the
// reverse would leave ℕ's COND standing.
func (v *extremaOps) NumGuard(m, n Term) Term { return v.NumLe.Apply(m, n) }

// In is `x ∈ s` — the membership atom the set wing's statements are
// built from, and the term the existence proofs λ-abstract to ground
// completeness at a set.
func (v *extremaOps) In(x, s Term) Term { return v.Mem.Apply(x, s) }

// Sing is `{a}` — the one-point set, spelled as the empty set with a
// laid on it. It is a term the structural equations pass to the
// attainment law rather than a name of its own: the chapter has no
// singleton constant, and `insert(a, ∅)` is what `{a}` means.
func (v *extremaOps) Sing(a Term) Term { return v.Insert.Apply(a, v.Empty) }
