// vocab.go — the chapter's statement vocabulary.
//
// One alphabet, ℤ's: divisibility, the greatest common divisor, and the
// ring and order operations the chapter's statements are written in — a
// Bézout combination, a sign moved across `∣`, a size compared. The
// text-DSL has no default scope for any of them — its defaults cover ℕ
// — so every constant a statement here names has a row below, at the
// types the domain's one NAME → type table gives them
// (`int_num/internal/intvocab`).
//
// The family installs the rows into each member's ParseScope
// (family.go's WithVocabSpec), so a proof body opens with mathematics
// rather than with a `ctx.Const` preamble; the build surface members
// take with `v := ops(a.Ctx())` is rendered from the same rows
// (zz_vocab_gen.go), so a constant's type is spelled once per package
// and the parse surface cannot drift from the build surface.
//
// The pair constructor `,` is deliberately ABSENT even though int_gcd
// takes a pair: it needs no declaration, the builder reading `,` from a
// polymorphic meta it holds itself, so `(a, b)` types itself from its
// components.

package int_divides

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/internal/intvocab"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// intType is ℤ, the only object this chapter's statements mention. The
// domain table types the chapter's CONSTANTS; this is for the two
// places a body needs the type itself — int_gcd's pair argument, and
// the projections' instance.
var intType = MakeType("int")

// pairToInt is the type of a function consuming the ℤ pair — what the
// int_gcd row below needs and the domain table cannot supply.
func pairToInt() HolType { return MakeFun(pairs.ProdType(intType, intType), intType) }

// vocab is the chapter alphabet as data — one row per name.
var vocab = registry.NewVocabSpec(intvocab.Table()).
	OpsName("divOps").

	// int_gcd is the one name the domain table does not carry: its
	// argument is a PAIR, and a product type is not an ℤ type. It earns
	// its handle because the mint unfolds it; the size, because a
	// divisibility bound is a statement about sizes and the terms it
	// compares have to be named.
	Spelled("int_gcd", pairToInt).
	Term("int_abs").As("Abs").

	// Negation, which is what a size is made of: `int_abs(x)` is `x` or
	// `int_neg(x)` and nothing else, so both sign laws are stated over
	// it and both proofs build the negated cofactor a sign change asks
	// for.
	Term("int_neg").As("Neg").

	// Multiplication and the order. A size bound is assembled rather
	// than merely stated — the intermediate claims name a product of two
	// sizes and a comparison against the unit — and the terms it is
	// assembled from are built through these.
	Term("int_mul").As("Mul").
	Term("int_le").As("Le").

	// Addition and subtraction, which the Bézout tier builds with: the
	// descent recombines two cofactors into k₁ + k₀ or k₁ − k₀, and
	// every ground order instance the exhaustiveness argument cites is
	// spelled over a shifted argument a ± b.
	Term("int_add").As("Add").
	Term("int_sub").As("Sub").

	// The strict order, which the descent's measure comparisons are
	// stated with but never built, and the embedding, which is what
	// makes `&0` and `&1` parse — the literal rows below need the
	// DECLARATION since they are built from text. Both are declared
	// rather than left to the DSL surface so that they resolve through
	// the mints' def-carrying metas.
	Term("int_lt").
	Term("int_of_num").

	// The partial inverse of the embedding, total on the nonnegatives:
	// the ℕ cofactor OfNumDivides hands back is num_of_int of a size.
	Term("num_of_int").

	// Divisibility itself. The `∣` infix dispatches by operand type, and
	// this is its ℤ branch — every statement resolves through it, and
	// every argument about `∣` that is not pure citation opens it with
	// `Unfold` by name; no body builds with it.
	Term("int_divides").

	// ℕ's divisibility, for the one member that carries it across the
	// embedding (OfNumDivides). The constant is nat_num/nat_divides's
	// mint; the row binds the definition-carrying meta, which that member
	// unfolds, and referencing the definition first pins the
	// initialization order — the spec cannot be built before the meta is
	// in the manager.
	Custom(func(*proof.Script) { _ = nat_divides.DividesFactor }).
	Defined("nat_divides").

	// fst / snd enter POLYMORPHICALLY: int_gcd's specification is stated
	// over a PAIR while the choice function that mints it is written
	// over the pair's components, so the projections appear the moment
	// the choice is applied. The type variables are what let one
	// declaration serve both.
	Custom(func(ctx *proof.Script) {
		pairs.ProjectionsAt(ctx, MakeVarType("A"), MakeVarType("B"))
	}).

	// ℤ's two literals, spelled unsugared. `&` takes its target type
	// from the term around it and a witness slot supplies none, so
	// `int_of_num(0)` is what keeps a literal in ℤ where `&0` would
	// resolve to ℝ.
	// what a cofactor is compared against, and the discreteness step's floor
	TermText("Zero", "int_of_num(0)").
	TermText("One", "int_of_num(1)") // the least a nonzero factor's size can be
