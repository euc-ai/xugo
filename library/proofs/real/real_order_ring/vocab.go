// vocab.go — the chapter's statement vocabulary.
//
// Declaring the constants a statement names is what makes a text-form
// statement PARSE the way the rest of the corpus reads it. The DSL
// carries `≤` and `<` as surface notation and will parse them
// undeclared — but its own metas for them are def-LESS, so an
// undeclared `real_lt` gives an `Unfold` nothing to open, which
// is this chapter's whole method. The declaration is what supplies it.
//
// The TYPES come from the ℝ domain alphabet (real/internal/realvocab):
// the rows below state WHICH names the chapter uses, the domain states
// what each one is. The family installs the rows into each member's
// ParseScope (family.go's WithVocabSpec), and the build surface members
// take with `v := ops(a.Ctx())` is rendered from the same rows
// (zz_vocab_gen.go).
//
// A row names a constant one of the chapter's members states, and no
// other — the Alphabet contract's rule. The members state `≤`, `<`,
// `real_gt`, `+`, unary `−`, binary `−`, `·` and the embedded literals
// `&0` and `&1`: negation because translating a comparison BACKWARDS is
// how the additive laws are inverted, subtraction for the laws that
// transport a comparison across it, `·` for the multiplicative
// compatibility laws, which compare two products, and `real_gt`, the
// numerals and the chapter's ONE ℕ constant for the ℕ-embedding members
// — see the note on `>` below.

package real_order_ring

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/internal/realvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// natRel is ℕ's binary relation type — what the one ℕ constant below
// is spelled at.
func natRel() HolType { return MakeFun(NumType, MakeFun(NumType, TypeBool)) }

// vocab is the chapter alphabet as data — one row per name. The
// CoerceDomain row makes an unanchored `&` ℝ by declaration, not by
// global default.
//
// Plus, Neg, Minus, Times and OfNum are the fields bodies BUILD with:
// the witness terms the additive, transport and multiplicative tiers
// ground their cites at — `x + y` at the four Add2 members, `-x` in
// LessEqAddLeft's cancellation lemma and throughout the negation
// transport laws, `y - z` at the four *SubAdd* laws and at both
// scaled-difference members, `x * y` wherever a product is the thing
// compared, and the literals `&0` — what the three Self laws and the
// two difference-sign laws compare against — and `&1`, the unit
// LessThanAddOne steps by.
//
// Minus builds `x - y` and never unfolds it. The chapter reads
// subtraction off its own LessEqSubAdd* laws instead, which is what
// keeps `−` a term of the order theory rather than a detour through
// the ring's definition of it.
//
// `real_le`, `real_lt` and `real_gt` are the order names themselves:
// no member builds `≤`, `<` or `>` — the notation does.
//
// The Spelled row is ℕ's strict order, at ℕ's type — the chapter's one
// constant from outside ℝ, admitted because the ℕ-embedding members are
// where the chapter's STATEMENTS reach ℕ: ofNumGreaterThan says that
// the embedding carries `>`, so `m > n` has to parse. There is no natvocab to borrow the type from, so it
// is spelled here the way nat_order spells its own relations.
//
// `real_inv` and `real_div` are absent, and that absence is the
// chapter's boundary stated in code: no headline here and no cited dep
// statement mentions either, because everything they generate belongs
// to real_order_field.
var vocab = registry.NewVocabSpec(realvocab.Table()).
	OpsName("realOps").
	CoerceDomain(RealDomain).
	Embed(realvocab.NumeralsBundle).
	Term("real_le").As("Le").
	Term("real_lt").As("Lt").
	Term("real_gt").As("Gt").
	Spelled(">", natRel).As("NumGt").
	Term("real_add").As("Plus").
	Term("real_neg").As("Neg").
	Term("real_sub").As("Minus").
	Term("real_mul").As("Times").
	Term("real_of_num").As("OfNum")

// Term-building shorthands, so a witness list reads as algebra rather
// than as applications.

// Add is a + b.
func (v *realOps) Add(a, b Term) Term { return v.Plus.Apply(a, b) }

// Negate is -a.
func (v *realOps) Negate(a Term) Term { return v.Neg.Apply(a) }

// Sub is a - b.
func (v *realOps) Sub(a, b Term) Term { return v.Minus.Apply(a, b) }

// Mul is a * b.
func (v *realOps) Mul(a, b Term) Term { return v.Times.Apply(a, b) }
