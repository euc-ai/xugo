// Package intvocab holds the ℤ domain's statement alphabet: the map
// from a constant's NAME to the type it is declared at, as an instance
// of the framework's registry.Alphabet.
//
// The text-DSL's default scope supplies ℕ (`+ * nat_div nat_mod ≤ <` and the
// numerals) but nothing of ℤ, so every int chapter must declare what
// its statements name — and before this table three families spelled
// the same types independently: int_embed's ops closure, int_real_lift's
// declareVocab, and int_div's in-proof preamble each typed `int_add`
// for themselves. The type of an ℤ constant is a fact about the
// DOMAIN; this is its one spelling.
//
// WHICH names a chapter declares stays the chapter's own statement
// (`Declare` takes them explicitly), and a name a chapter BUILDS terms
// with comes through `Term`, so its handle and its declaration cannot
// drift — the Alphabet contract, registry/alphabet.go. No entry is
// nullary: ℤ literals arrive as `&n` through the coercion, so the
// domain has no `∅`-class name and no Pinned site.
//
// It lives under `internal/` so that only packages rooted at
// `proofs/int_num` can reach it.
package intvocab

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

func intT() core.HolType  { return ext.MakeType("int") }
func unOp() core.HolType  { return core.MakeFun(intT(), intT()) }
func binOp() core.HolType { return core.MakeFun(intT(), core.MakeFun(intT(), intT())) }
func rel() core.HolType   { return core.MakeFun(intT(), core.MakeFun(intT(), core.TypeBool())) }

// powOp is the odd type in the table: an integer power takes its
// EXPONENT from ℕ, because negative exponents leave ℤ.
func powOp() core.HolType { return core.MakeFun(intT(), core.MakeFun(dsl.NumType, intT())) }

// congRel is the congruence's type: two integers and the modulus they
// agree under, in the order `x ≡ y (mod m)` reads them.
func congRel() core.HolType {
	return core.MakeFun(intT(), core.MakeFun(intT(), core.MakeFun(intT(), core.TypeBool())))
}

var alphabet = registry.NewAlphabet("int").
	// The boundary with ℕ: the embedding (spelled `&` in statement
	// texts — the DSL builds int_of_num once the surrounding term is
	// int-typed) and its partial inverse, total on the nonnegatives.
	Const("int_of_num", func() core.HolType { return core.MakeFun(dsl.NumType, intT()) }).
	Const("num_of_int", func() core.HolType { return core.MakeFun(intT(), dsl.NumType) }).

	// The ring operations, negation, and absolute value. Subtraction is
	// total here, unlike ℕ's — which is the whole reason a ℕ difference
	// has to be guarded before it crosses.
	Const("int_add", binOp).
	Const("int_mul", binOp).
	Const("int_sub", binOp).
	Const("int_neg", unOp).
	Const("int_abs", unOp).
	Const("int_pow", powOp).

	// The sign, which is what an absolute value is missing: |x| = sgn(x)·x
	// on all of ℤ, and the division laws under negation need it because
	// negating a dividend moves the quotient by one step in whichever
	// direction the divisor points.
	Const("int_sgn", unOp).

	// The division algorithm's pair, and the congruence it decides:
	// `int_cong(x, y, n)` is `n ∣ (x − y)`, which the `x ≡ y (mod n)`
	// surface lowers to at int. (That it is ALSO equality of remainders
	// is a theorem — int_congruence's — not the definition.)
	Const("int_div", binOp).
	Const("int_rem", binOp).
	Const("int_cong", congRel).

	// Divisibility, which congruence is defined from: `x ≡ y (mod n)`
	// unfolds to `n ∣ (x - y)`.
	Const("int_divides", rel).

	// The order and its strict part — and their flipped spellings, which
	// exist as their own constants (`x > y` is DEFINED as `y < x`). Then
	// the two selectors the order defines.
	Const("int_le", rel).
	Const("int_lt", rel).
	Const("int_ge", rel).
	Const("int_gt", rel).
	Const("int_max", binOp).
	Const("int_min", binOp)

// Table exposes the alphabet for a chapter's VocabSpec — the
// declarative route to the same Declare/Term verbs below.
func Table() *registry.Alphabet { return alphabet }

// Declare registers the named constants into ctx's ParseScope at the
// domain's types — statement-only names; a built name enters via Term.
func Declare(ctx *proof.Script, names ...string) { alphabet.Declare(ctx, names...) }

// Term declares name and returns its build handle — see
// registry.Alphabet.Term.
func Term(ctx *proof.Script, name string) *ext.TermWrapper { return alphabet.Term(ctx, name) }

// Known lists the typed names, sorted.
func Known() []string { return alphabet.Known() }
