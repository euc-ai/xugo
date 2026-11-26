// vocab.go — the chapter's statement vocabulary.
//
// One alphabet, ℤ's: the division pair `int_div`/`int_rem`, the ring operations
// a quotient-remainder equation is written in, and the order plus
// absolute value the remainder bound `0 ≤ rem < |n|` needs. The
// text-DSL's default scope covers ℕ and nothing of ℤ, so every constant
// a statement here names has a row below — the types coming from the
// domain's one NAME → type table, `int_num/internal/intvocab`. The
// family installs the rows into each member's ParseScope (family.go's
// WithVocabSpec), and the build surface members take with
// `v := ops(a.Ctx())` is rendered from the same rows (zz_vocab_gen.go).
//
// `COND` is deliberately absent: the DSL reads it from a polymorphic
// meta it holds itself, so `COND(n = &0, …, …)` types itself from its
// branches. So is `&`, which the coercion builds into `int_of_num` once
// the surrounding term is int-typed — but the constant it builds is
// declared, since the spec states `&0` explicitly.
//
// ONE constant is declared outside this file, and the criterion is the
// DOMAIN rather than the rarity. `DivNonneg` (`arithmetic.go`) names ℕ's
// `nat_div` — the chapter's only statement about a natural — and declares
// it in its own body, because it belongs to the ℕ domain's table
// (`nat_num`'s, not `intvocab`) and admitting it here would
// misdescribe the alphabet this spec installs. Everything ℤ's is here,
// however few members name it: `Sgn` has two.
//
// Two of ℤ's own, however, cannot come from `intvocab` — the Spelled
// rows for `int_gcd` and `int_lcm`. Each takes its two integers as ONE
// PAIR, and a product type is not an ℤ type, so the domain's
// NAME → ℤ-type table has no entry it could give
// (`int_num/int_divides` declares `int_gcd` for exactly this reason).

package int_div_rem

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/internal/intvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// intType is ℤ. The domain table types the chapter's CONSTANTS; this is
// for the places a body has to name the type itself — the pair that
// `int_gcd` and `int_lcm` take, and the pairing constructor `arithmetic.go`
// builds it with.
var intType = MakeType("int")

// pairToInt is the type of a function consuming the ℤ pair — what the
// Spelled rows below need and the domain table cannot supply.
func pairToInt() HolType { return MakeFun(pairs.ProdType(intType, intType), intType) }

// vocab is the chapter alphabet as data — one row per name. `Div` and
// `Rem` because a proof has to name the pair it is talking about
// rather than merely state it; the ring and order operations because
// the divmod specification is assembled as a term — it appears as a
// witness body under two ε-binders, where no text form can reach it.
var vocab = registry.NewVocabSpec(intvocab.Table()).
	OpsName("divRemOps").
	Term("int_div"). // int_div(m, n) — the quotient
	Term("int_rem"). // int_rem(m, n) — the remainder
	Term("int_add").As("Add").
	Term("int_mul").As("Mul").
	Term("int_sub").As("Sub"). // two decompositions are compared by difference
	Term("int_neg").As("Neg").
	Term("int_abs").As("Abs"). // the bound's right-hand side
	Term("int_sgn").As("Sgn"). // which way a negated dividend steps
	Term("int_le").As("Le").
	Term("int_lt").As("Lt").

	// Raising to a power, whose exponent is a NATURAL. `arithmetic.go`'s
	// last member runs an induction along that exponent.
	Term("int_pow").As("Pow").

	// Divisibility: `d ∣ e` is defined as the existence of a cofactor,
	// and every member of `arithmetic.go` unfolds it — the content
	// there is that the cofactor and the quotient are the same number.
	Term("int_divides").As("Divides").

	// The gcd and the lcm `arithmetic.go` reaches: it unfolds `int_lcm`
	// and names the `int_gcd` term the unfolded definition divides by.
	Spelled("int_gcd", pairToInt).
	Spelled("int_lcm", pairToInt).
	Term("int_of_num").As("OfNum").    // & as a builder; `division.go` names the embedded naturals
	TermText("Zero", "int_of_num(0)"). // the ℤ literal, not ℕ's
	TermText("One", "int_of_num(1)")   // the unit divisor, and the gap discreteness closes
