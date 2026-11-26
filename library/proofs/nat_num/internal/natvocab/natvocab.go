// Package natvocab holds the ℕ domain's statement alphabet, as an
// instance of the framework's registry.Alphabet — and, since the
// domain defines its own constants, almost nothing is left in it.
//
// A ℕ chapter names the constants its statements spell in its
// VocabSpec rows, and every one of them reads its type off its MINT:
// peano defines the construction (`_0`, `suc`, and the ind-typed
// bootstrap), nat_arith the operations and the numeral digits, nat_order
// the order, nat_monus predecessor / `-` / dist, nat_parity nat_even / nat_odd,
// nat_div_mod nat_div / nat_mod, and the chapters above them their own
// (`nat_divides`, `nat_cong`, `nat_gcd`, `nat_prime`). A table entry
// for any of those would be a second spelling of the mint's one
// authoritative type; the Alphabet falls back to the mint for a name
// the table does not carry.
//
// What remains is the one name whose mint is POLYMORPHIC and which the
// domain declares at a fixed instance: the pair constructor `,` at
// (num, num), the ℕ pair that nat_monus states its distance laws over.
// Naming another domain's TYPE at an instance is what a type table is
// for (the realvocab precedent for ℕ and ℤ).
//
// It lives under `internal/` so that only packages rooted at
// `proofs/nat_num` can reach it.
package natvocab

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

func numT() core.HolType    { return dsl.NumType }
func unOp() core.HolType    { return core.MakeFun(numT(), numT()) }
func binOp() core.HolType   { return core.MakeFun(numT(), core.MakeFun(numT(), numT())) }
func rel() core.HolType     { return core.MakeFun(numT(), core.MakeFun(numT(), core.TypeBool())) }
func pred() core.HolType    { return core.MakeFun(numT(), core.TypeBool()) }
func numPair() core.HolType { return pairs.ProdType(numT(), numT()) }

var alphabet = registry.NewAlphabet("nat").
	// The successor structure and the numeral tower `n` parses
	// through: _0 the base, bit0/bit1 the binary digits.

	// The operations. Subtraction is ℕ's truncated monus — which is
	// the whole reason nat_monus exists — and division is the nat_div/nat_mod
	// pair the division algorithm characterizes.

	// The ℕ pair's constructor at the num instance — the one name
	// whose polymorphic mint (pairs) a chapter still declares at a
	// fixed instance; every other constant of the domain is minted by
	// its chapter and reads its type off the mint.
	Const(",", func() core.HolType { return core.MakeFun(numT(), core.MakeFun(numT(), numPair())) })

// Table exposes the alphabet for a chapter's VocabSpec — the
// declarative route to the same Declare/Term verbs below.
func Table() *registry.Alphabet { return alphabet }

// Declare registers the named constants into ctx's ParseScope at the
// domain's types — statement-only names; a built name enters via Term.
func Declare(ctx *proof.Script, names ...string) { alphabet.Declare(ctx, names...) }

// Term declares name and returns its build handle — see
// registry.Alphabet.Term.
func Term(ctx *proof.Script, name string) ext.Term { return alphabet.Term(ctx, name) }

// Known lists the typed names, sorted.
func Known() []string { return alphabet.Known() }
