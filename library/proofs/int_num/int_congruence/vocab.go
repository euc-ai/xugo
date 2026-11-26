// vocab.go — the chapter's statement vocabulary.
//
// The text-DSL's default scope covers ℕ and nothing of ℤ, so every
// constant a statement here names has a row below. The types come from
// the domain's one NAME → type table, `int_num/internal/intvocab` —
// with one exception: ℕ's own congruence, which one member carries
// across the embedding.
//
// A reader will rarely see `int_cong`: `x ≡ y (mod n)` is the surface,
// and the DSL lowers it to `int_cong(x, y, n)` once the operands type
// as int. The constant is nonetheless declared, because the mixfix
// resolves it SCOPE-FIRST — binding the DSL's own def-less meta instead
// of the chapter's def-carrying mint would leave the congruence opaque
// to the very unfolding the chapter's floor member performs.
//
// The family installs the rows into each member's ParseScope
// (family.go's WithVocabSpec), and the build surface members take with
// `v := ops(a.Ctx())` is rendered from the same rows (zz_vocab_gen.go),
// so a constant's type is spelled once per package and the parse
// surface cannot drift from the build surface.

package int_congruence

import (
	"github.com/euc-ai/xugo/library/proofs/int_num/internal/intvocab"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// vocab is the chapter alphabet as data — one row per name.
var vocab = registry.NewVocabSpec(intvocab.Table()).
	OpsName("congOps").

	// The division pair. Congruence is decided by the remainder, so `Rem`
	// is the handle this chapter builds with most; `Div` appears wherever
	// a quotient has to be named to exhibit a multiple.
	Term("int_div").
	Term("int_rem").

	// The ring operations, and each is used both ways: to write a
	// multiple of the modulus, and as an operation congruent quantities
	// are combined by. That the two roles coincide is the chapter's own
	// point — the relation respects the ring structure.
	Term("int_add").As("Add").
	Term("int_mul").As("Mul").
	Term("int_sub").As("Sub").

	// Raising to a power, whose exponent is a NATURAL — it is iterated
	// multiplication and nothing more, which is the only property this
	// chapter asks of it.
	Term("int_pow").As("Pow").

	// The size of an integer, which is the width of the stretch a
	// congruence class has exactly one member in — so it is what a
	// statement about representatives compares against, and the term a
	// proof about them has to name.
	Term("int_abs").As("Abs").

	// The embedding's partial inverse, defined on the nonnegatives. No
	// statement here names it — a class member is asked to be a natural,
	// which is said by embedding one — but a proof that produces such a
	// member has to build the natural it produces.
	Term("num_of_int").

	// The embedding itself, and ℤ's zero built through it. Statements
	// name the zero freely as `&0`, which the parser builds without help
	// beside an integer; the Zero handle is for a body that builds it
	// alone — to SPLIT on whether a difference is it, or to exhibit it as
	// the multiple that makes a congruence reflexive.
	Term("int_of_num").
	TermText("Zero", "int_of_num(0)").

	// The order. A statement that traps a residue between `&0` and the
	// modulus's size names both relations, and no member assembles such
	// a bound — each cites it whole from the chapter that proves it.
	Term("int_le").
	Term("int_lt").

	// The congruence the `≡ … (mod …)` surface hides, and what it
	// unfolds to. Every statement resolves it through this row, and the
	// floor members take it apart with `Unfold` by name; no body builds
	// with it.
	Term("int_cong").
	Term("int_divides").

	// ℕ's congruence, for the one member that carries it across the
	// embedding (OfNumCongruent). The constant is nat_num/nat_congruence's
	// mint; the row binds the definition-carrying meta, which that member
	// unfolds, and referencing the definition first pins the
	// initialization order — the spec cannot be built before the meta is
	// in the manager.
	Custom(func(*proof.Script) { _ = nat_congruence.CongDef }).
	Defined("nat_cong")
