// vocab.go — the chapter's statement vocabulary.
//
// The chapter states its theorems in ℝ's alphabet — the power itself
// plus the field operations the power laws are written in —
// with the types coming from the domain's one NAME → type table
// (real/internal/realvocab). ℕ's `suc`, `nat_pow` and the numerals arrive
// from the text-DSL's default scope; `&` is the type-directed coercion
// the DSL resolves to real_of_num (whose constant IS declared) once
// the surrounding term is real-typed.
//
// Declaring the alphabet is what makes a text-form statement PARSE,
// and it is identical in every member, so the family installs it into
// each member's ParseScope (family.go's WithVocabSpec) rather than
// each proof re-typing a `ctx.Const` preamble. The term-BUILDING half
// is the generated `ops` (zz_vocab_gen.go), rendered from the same
// rows, and a member takes it only if it assembles terms rather than
// merely stating them.

package real_pow

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/internal/realvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name: what the
// mint assembles its clause parameters from, and what the theorems
// name — the embedded literals they pin a slot to, the power itself
// where a proof has to talk about 0ⁿ rather than merely state it, and
// the operations that build the BASE a proof reads the recursion at.
// real_inv is the last of those: InvPow grounds Pow's zero clause at x⁻¹,
// so that term must exist before the cite can be grounded.
//
// The embedded literals come from the domain's shared builder (the
// NumeralsBundle row): `v.Lit(1)` is `&1`, where a bare ctx.Numeral(1)
// would be the EXPONENT — the one confusion this chapter, whose every
// name turns on base-vs-exponent, cannot afford.
//
// There is one statement-only name: `real_div` appears in DivPow's
// headline and is unfolded on the first move, so no term this chapter
// builds is ever a quotient.
//
// What is NOT here is the point. The DSL's arithmetic operators
// (`+ - * / < ≤ > ≥ ∣`) dispatch on OPERAND TYPE through fixed const
// metas rather than through the ParseScope (ext/dsl/arith.go), so
// `real_le`, `real_lt` and their kind parse with no declaration at
// all — in ANY domain, which is why the order tier's `≤` works while
// neither name appears. Only NON-operator names have to be declared.
// Measured by deletion against the full family: `real_le`/`real_lt`.
// The alphabet you must declare is smaller than the alphabet you
// write, and the way to find out is to delete a name and replay.
var vocab = registry.NewVocabSpec(realvocab.Table()).
	OpsName("powOps").
	CoerceDomain(RealDomain).
	Embed(realvocab.NumeralsBundle).
	Term("real_pow").As("Pow").      // the chapter's subject
	Term("real_mul").As("Mul").      // the step clause's product
	Term("real_of_num").As("OfNum"). // the embedded base of OfNumPow
	Term("real_inv").As("Inv").      // the inverted base of InvPow
	Term("real_abs").As("Abs").      // the base the absolute-value tier reads powers at
	Term("real_sgn").As("Sgn").      // the sign of a power (SgnPow), read at the base and at the power
	Term("real_div").As("Div")       // stated by DivPow, unfolded on the first move
