// vocab.go — the chapter's statement vocabulary.
//
// The chapter states its theorems in ℝ's alphabet — the integer power,
// the natural power it is read through, and the field operations its
// laws are written in — with the types coming from the domain's one
// NAME → type table (real/internal/realvocab). `&` is the type-directed
// coercion the DSL resolves to real_of_num once the surrounding term is
// real-typed.
//
// The exponents are ℤ's, and they come from the SAME table as the rest
// — the ℤ domain's own intvocab sits under `int_num/internal/`, which
// Go's import rule puts out of reach of a package rooted at
// `proofs/real`, and a constant's type is one fact either way. `&`
// keeps working in the exponent slot: the coercion is type-directed and
// real_zpow's second argument is int, so `&1` there resolves to
// int_of_num(1) — the same statement, verified to the same key, as
// spelling int_of_num by hand.
//
// Declaring the alphabet is what makes a text-form statement PARSE,
// and it is identical in every member, so the family installs it into
// each member's ParseScope (family.go's WithVocabSpec) rather than
// each proof re-typing a `ctx.Const` preamble. The term-BUILDING half
// is the generated `ops` (zz_vocab_gen.go), rendered from the same
// rows, and a member takes it only if it assembles terms rather than
// merely stating them.

package real_zpow

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/internal/realvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name: what the
// theorems name, and the operations a proof builds terms from. The
// natural power, the product and the inverse are the second kind:
// ZpowAdd's chains cross to the ℕ-indexed powers and name them, their
// products and their inverses leg by leg.
//
// The embedded literals come from the domain's shared builder (the
// NumeralsBundle row): `v.Lit(1)` is `&1`, where a bare ctx.Numeral(1)
// would be the EXPONENT.
//
// int_of_num is ℕ ↪ ℤ, the exponents. Its handle earns its keep
// because ZpowNeg splits on whether its exponent is zero, and a
// case-split discriminant is a TERM the proof assembles (`Unless`
// takes one); the evaluations only state `&0`/`&1`/`&2`, which the
// coercion resolves through this same constant without needing the
// handle.
//
// Statement-only names, and there are exactly two. `real_div` appears
// in DivZpow's and ZpowSub's headlines and is unfolded on the first
// move, so no term this chapter builds is ever a quotient. `real_zpow`
// is stated and never built — a member's headline spells the
// ℤ-indexed power, and the proofs ground their cites at the BASE and
// at ℕ exponents, which are terms the chapter already has.
//
// What is NOT here is the point. The DSL's arithmetic operators
// (`+ - * / < ≤ > ≥ ∣`) dispatch on OPERAND TYPE through fixed const
// metas rather than through the ParseScope (ext/dsl/arith.go), so
// `int_neg`, `int_le` and their kind parse with no declaration at all,
// which is why the chapter's int-typed `-` and `≤` work while neither
// name appears; `num_of_int` needs no row either. Only NON-operator
// names have to be declared, and the way to find out which is to
// delete a name and replay.
var vocab = registry.NewVocabSpec(realvocab.Table()).
	OpsName("zpowOps").
	CoerceDomain(RealDomain).
	Embed(realvocab.NumeralsBundle).
	Term("real_pow").As("Pow").  // the natural power every law crosses to
	Term("real_mul").As("Mul").  // the products ZpowAdd's chains name
	Term("real_inv").As("Inv").  // the inverse a negative exponent reads
	Term("int_of_num").          // ℕ ↪ ℤ — the exponents
	Term("real_div").As("Div").  // stated by DivZpow/ZpowSub, unfolded on the first move
	Term("real_zpow").As("Zpow") // stated and never built
