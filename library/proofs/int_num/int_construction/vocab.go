// vocab.go — the chapter's statement vocabulary.
//
// One alphabet, spanning both sides of the bijection — see the README
// for why ℤ and ℝ are peers here and what that costs `&`.
//
// Declaring the alphabet is what makes a text-form statement PARSE; it
// is identical in every member, so the family installs the rows into
// each member's ParseScope (family.go's WithVocabSpec) rather than each
// proof re-typing a `ctx.Const` preamble. The term-BUILDING half is the
// surface rendered from the same rows (zz_vocab_gen.go), and a member
// calls it only when it builds. The ℤ names' types come from the
// domain's one NAME → type table (int_num/internal/intvocab); the ℝ
// side's are spelled here, in the Spelled rows, because real/'s own
// table is internal to another domain.

package int_construction

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/internal/intvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// intType is ℤ. It is a TYPE here rather than a domain: this chapter is
// where it gets carved out of ℝ, so no member may assume anything about
// it that the bijection has not yet supplied.
var intType = MakeType("int")

// realType is ℝ — the carrier the Spelled rows' types are written over.
func realType() HolType { return MakeType("real") }

func realUnOp() HolType  { return MakeFun(realType(), realType()) }
func realBinOp() HolType { return MakeFun(realType(), MakeFun(realType(), realType())) }

// vocab is the chapter alphabet as data — one row per name.
var vocab = registry.NewVocabSpec(intvocab.Table()).
	OpsName("consOps").

	// The chapter's numbers are reals — ℤ is what it carves out of them
	// — so an `&` no operand anchors embeds into ℝ, by declaration.
	CoerceDomain(RealDomain).

	// ℤ's own operations are declared and not built. A bridge NAMES its
	// operation in its statement and then unfolds it by name, so no body
	// constructs over one; and leaving the two `&`s and the two `-`s to
	// the DSL surface would let each resolve to whichever alphabet the
	// parser reached first.
	Term("int_of_num").
	Term("int_neg").
	Term("int_sgn").
	Term("int_abs").
	Term("int_max").
	Term("int_min").
	Term("int_mul").
	Term("int_add").
	Term("int_sub").

	// The representative map's partial inverse, total on `integer`. It is
	// declared and never built: it enters the chapter through the type
	// definition, which names it as a string (int_construction.go's
	// TypeDefExpand), and every other appearance is inside a statement's
	// text.
	Spelled("int_of_real", func() HolType { return MakeFun(realType(), intType) }).

	// The ℝ-side answers the sign, max and min bridges transport,
	// declared and not built for the same reason: a bridge names one in
	// its headline and in the claim that it is again an integer, and then
	// unfolds it by name.
	Spelled("real_sgn", realUnOp).
	Spelled("real_max", realBinOp).
	Spelled("real_min", realBinOp).

	// The representative map, the ℝ predicate it is a bijection onto, and
	// the embedding a ± characterization spells its `&` with.
	// ℤ ↪ ℝ — the representative map
	Spelled("real_of_int", func() HolType { return MakeFun(intType, realType()) }).
	// integer(x) — the ℝ subset ℤ is carved from
	Spelled("integer", func() HolType { return MakeFun(realType(), TypeBool) }).
	// ℕ ↪ ℝ — the `&` of a ± characterization
	Spelled("real_of_num", func() HolType { return MakeFun(NumType, realType()) }).
	// negation in ℝ — what int_neg transports
	Spelled("real_neg", realUnOp).

	// `integer` is defined by "some natural is my absolute value", so
	// this appears the moment the chapter says what `integer` means.
	Spelled("real_abs", realUnOp).

	// Built, not merely declared, because the two bridges that carry
	// them argue about their ℝ answer term by term: the product and the
	// sum of two representatives are the terms their closure claims are
	// stated at, and the ℝ laws those claims cite are read at &m, -&n
	// and the sums and products built from them.
	Spelled("real_mul", realBinOp).
	Spelled("real_add", realBinOp).

	// Built for the same reason, one step removed: its bridge states a
	// closure claim at the ℝ answer and then unfolds this one away
	// inside it, so it is named once as a term and never again.
	Spelled("real_sub", realBinOp)
