// Package realvocab holds the ℝ domain's statement alphabet: the map
// from a constant's NAME to the type it is declared at, as an instance
// of the framework's registry.Alphabet.
//
// The text-DSL parses ℝ's infix surface — `+ - * / ≤ <` and the
// embedded literal `&n` — but its metas for those constants are
// def-less, and every ℝ chapter's method is citing or unfolding the
// constants a statement names. So each chapter must declare what its
// statements mention, and before this table each spelled the same
// curried types for itself: `real_ring`'s `ops` and `real_field`'s
// `registry.Vocab` closure both typed `real_add`, `real_mul`,
// `real_neg` and `real_of_num` independently. The type of an ℝ
// constant is a fact about the DOMAIN; this is its one spelling.
//
// WHICH names a chapter declares stays the chapter's own statement
// about its alphabet — `Declare` takes them explicitly, and a chapter
// names a constant when one of its members states it, never in
// advance. A name a chapter BUILDS terms with comes through `Term`, so
// its handle and its declaration cannot drift — the Alphabet contract,
// registry/alphabet.go.
//
// Some entries are not ℝ constants at all, and the table's subject is
// what an ℝ STATEMENT spells rather than what ℝ is made of. `_0`,
// `bit0` and `bit1` are ℕ's numeral constructors, carried here because
// `&n` in an ℝ statement parses through them: `&1` is
// `real_of_num(bit1(_0))`, and a chapter that declares `real_of_num`
// alone gets a parse failure on its first literal. `int_of_num` is here
// on the same grounds — `real_zpow` takes an ℤ exponent, so a statement
// about it spells that name whatever domain the theorem belongs to. (ℤ needs no
// counterpart ℕ-numeral entry — see intvocab's note — because `&n`
// there resolves through the DSL's default ℕ scope.)
//
// No entry is POLYMORPHIC-nullary, so the domain has no `Pinned` site:
// ℝ's literals arrive through the embedding rather than as constants
// of their own. (`_0` is nullary by arity but monomorphic, so it takes
// the ordinary `Const` route — `Pinned` exists for the `∅`-class name
// that must stay polymorphic, which ℝ has none of.)
//
// It lives under `internal/` so that only packages rooted at
// `proofs/real` can reach it: this is domain machinery, not a
// chapter, and Go's import rule says so rather than a convention
// anyone can forget.
package realvocab

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

func realT() core.HolType { return ext.MakeType("real") }
func setT() core.HolType  { return core.MakeFun(realT(), core.TypeBool()) }
func unOp() core.HolType  { return core.MakeFun(realT(), realT()) }
func binOp() core.HolType { return core.MakeFun(realT(), core.MakeFun(realT(), realT())) }
func rel() core.HolType   { return core.MakeFun(realT(), core.MakeFun(realT(), core.TypeBool())) }
func numUnOp() core.HolType {
	return core.MakeFun(dsl.NumType, dsl.NumType)
}
func setToReal() core.HolType { return core.MakeFun(setT(), realT()) }
func setToRealRel() core.HolType {
	return core.MakeFun(setT(), core.MakeFun(realT(), core.TypeBool()))
}

// powOp / zpowOp — ℝ powers. The exponents come from OTHER domains (ℕ
// and ℤ), which is fine for a type table: the operation itself is ℝ's,
// its values are ℝ's, and naming another domain's TYPE is exactly what
// numUnOp above already does for ℕ.
func powOp() core.HolType { return core.MakeFun(realT(), core.MakeFun(dsl.NumType, realT())) }
func zpowOp() core.HolType {
	return core.MakeFun(
		realT(), core.MakeFun(ext.MakeType("int"), realT()))
}

func intT() core.HolType { return ext.MakeType("int") }

var alphabet = registry.NewAlphabet("real").
	// The field operations. real_sub and real_div are DEFINED
	// (`x - y` is `x + -y`, `x / y` is `x · inv y`), which is why
	// chapters unfold rather than cite them — but they are still
	// names a statement spells, so they are typed here like any other.
	Const("real_add", binOp).
	Const("real_mul", binOp).
	Const("real_sub", binOp).
	Const("real_div", binOp).
	Const("real_neg", unOp).
	Const("real_inv", unOp).
	Const("real_abs", unOp).
	Const("real_sgn", unOp).

	// The ℕ→ℝ embedding.
	Const("real_of_num", func() core.HolType { return core.MakeFun(dsl.NumType, realT()) }).

	// The order, its strict part, and the two mirrored spellings.
	// real_lt, real_ge and real_gt are all DEFINED from real_le.
	Const("real_le", rel).
	Const("real_lt", rel).
	Const("real_ge", rel).
	Const("real_gt", rel).

	// The extrema layer (real_sup_inf's subject): the binary lattice
	// pair, the set-level least-upper/greatest-lower bound operators,
	// and their attained-bound relations. sup and inf consume an ℝ set
	// (real → bool); real_has_sup/real_has_inf relate a set to the bound it
	// attains.
	Const("real_max", binOp).
	Const("real_min", binOp).
	Const("real_sup", setToReal).
	Const("real_inf", setToReal).
	Const("real_has_sup", setToRealRel).
	Const("real_has_inf", setToRealRel).

	// The powers — ℕ-indexed and ℤ-indexed iteration of the product.
	Const("real_pow", powOp).
	Const("real_zpow", zpowOp).

	// ℤ's side of real_zpow, for the same reason `_0`/`bit0`/`bit1`
	// are here: this is what a statement ABOUT real_zpow has to spell,
	// not an operation of ℝ. `&n` in the exponent slot resolves
	// through it, the coercion being type-directed and zpowOp pinning
	// that slot to int. ℤ's own chapters take the same constant from
	// intvocab — that table is the ℤ domain's, this one is ℝ's, and a
	// constant's type is the same fact in both.
	//
	// It is the ONLY ℤ name here, and deliberately so. `int_neg`,
	// `int_le` and the rest of ℤ's OPERATORS need no entry: the DSL
	// dispatches `+ - * < ≤ > ≥ ∣` on operand type through fixed const
	// metas (ext/dsl/arith.go), never through the ParseScope, so an
	// int-typed `-` or `≤` parses undeclared. Measured in real_pow,
	// which states both and declares neither. Only non-operator names
	// need declaring — this one, and `num_of_int` if a chapter ever
	// spells it in its own text rather than merely meeting it in an
	// unfolded goal.
	Const("int_of_num", func() core.HolType { return core.MakeFun(dsl.NumType, intT()) }).

	// ℕ's numeral constructors — what `&n` parses through. See the
	// package comment.
	Const("_0", func() core.HolType { return dsl.NumType }).
	Const("bit0", numUnOp).
	Const("bit1", numUnOp)

// Table exposes the alphabet for a chapter's VocabSpec — the
// declarative route to the same Declare/Term verbs below.
func Table() *registry.Alphabet { return alphabet }

// Declare registers the named constants into ctx's ParseScope at the
// domain's types — statement-only names; a built name enters via Term.
func Declare(ctx *proof.Script, names ...string) { alphabet.Declare(ctx, names...) }

// Term declares name and returns its build handle — see
// registry.Alphabet.Term.
func Term(ctx *proof.Script, name string) *ext.TermWrapper { return alphabet.Term(ctx, name) }

// NumeralsBundle is Numerals as a VocabSpec row: `.Embed(realvocab.
// NumeralsBundle)` declares what NewNumerals declares and embeds the
// builder in the chapter's generated ops struct.
var NumeralsBundle = registry.Bundle{
	Path: "github.com/euc-ai/xugo/library/proofs/real/internal/realvocab",
	Pkg:  "realvocab", Type: "Numerals", New: "NewNumerals",
	Install: func(ctx *proof.Script) { NewNumerals(ctx) },
}

// Numerals builds ℝ's embedded ℕ literals. Every chapter of the domain
// needs them and the construction is the same one in each — `&n` is
// real_of_num applied to ℕ's numeral tower — so the domain owns it,
// exactly as it owns the constants' types. A chapter's ops struct
// EMBEDS this, so `v.Lit(1)` reads the same at every call site it
// already did.
//
// Both spellings matter and they are not interchangeable: Lit takes a
// numeral known at authoring time, Embed a ℕ-typed TERM a member is
// quantified over.
type Numerals struct {
	ctx   *proof.Script
	ofNum *ext.TermWrapper
}

// NewNumerals declares real_of_num plus the numeral constructors `&n`
// parses through, and returns the builder.
func NewNumerals(ctx *proof.Script) Numerals {
	Declare(ctx, "_0", "bit0", "bit1")
	return Numerals{ctx: ctx, ofNum: Term(ctx, "real_of_num")}
}

// Lit is the embedded numeral &n. It builds the same term the statement
// text `&n` parses to, through the same bit0/bit1 tower, so a witness
// list and its statement stay spelled alike.
func (v Numerals) Lit(n int64) ext.Term { return v.ofNum.Apply(v.ctx.Numeral(n)) }

// Embed is `&t` for a ℕ-typed term — what a member quantified over its
// natural needs, where Lit's authoring-time numeral will not do.
func (v Numerals) Embed(t ext.Term) ext.Term { return v.ofNum.Apply(t) }
