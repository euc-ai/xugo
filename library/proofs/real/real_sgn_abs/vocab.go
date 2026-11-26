// vocab.go — the chapter's statement vocabulary.
//
// Every statement in this chapter is written in the same alphabet: the
// absolute value and the sign, the two orders their guards are stated
// in, negation (which either case definition's later branches produce),
// the ℕ→ℝ embedding, and the numeral tower `&0` expands through.
// Declaring that alphabet is what makes a text-form statement PARSE,
// and it is identical in every member — so it is stated once, as the
// rows below, and installed into each member's ParseScope by the family
// (family.go's WithVocabSpec), not re-typed as a `ctx.Const` preamble
// per proof. The TYPES come from the ℝ domain's realvocab table; the
// rows state WHICH names this chapter's statements spell.
//
// The second half is the *TermWrapper values a body needs to BUILD
// terms with — the generated ops struct (zz_vocab_gen.go), rendered
// from the same rows. That half is genuinely per-proof — only a body
// constructing witnesses wants it — so a member takes it in one line,
// `v := ops(a.Ctx())`, and a member whose body only names facts takes
// nothing at all.

package real_sgn_abs

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/internal/realvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name. Both
// halves of the pair are here, but only the size's handle BUILDS
// anything: the sign appears solely as the order comparisons its
// guards are stated in. The alphabet a statement is WRITTEN in and the
// alphabet a body BUILDS with are different sets, and `real_sgn`
// belongs to the first alone.
//
// Abs is the subject. Le and Lt are here because this chapter's
// characteristic move CONSTRUCTS a comparison rather than merely naming
// one — the two case definitions' guards are the terms a member splits
// on, and they have to be built to be passed. The size's guard
// `&0 ≤ x` is one comparison and the sign's are the strict pair
// `&0 < x`, `x < &0`, so the two relations arrive separately and for
// separate members. Neg is here because a body states the size's guard
// at `-x` too, and Times because a two-argument statement has a product
// to name before it can say anything about it.
//
// Inv arrives with the division wing, which is the first material whose
// bodies hold inverses rather than merely citing laws about them:
// `AbsInv` grounds a uniqueness law at the pair `(|x|, |x⁻¹|)`, and the
// two calculations name every midpoint of their rearrangement ladders as
// a term, most of which are products of inverses.
//
// The quotient those same statements spell is never built, because
// every member of that wing unfolds it before the body reaches it — so
// the wing builds the inverse a quotient is MADE of, and never the
// quotient.
//
// Minus arrives with `AbsBetween` (real_sgn_abs.go): what it takes the
// size of is a DIFFERENCE, so `y - x` is a term its every premise has
// to name. Its file-mate `AbsBounds` never builds one.
//
// Add arrives with `AbsTriangle` (real_sgn_abs.go), the first member whose
// subject is a SUM: the sum it bounds and the sum of sizes bounding it
// are both terms its premises name, and the pair is what its closing
// citation is read at.
//
// Two of the names below are declared for their ParseScope effect
// alone, and no body builds a term with either. The numeral tower
// needs no row of its own: it is the NumeralsBundle row that declares
// `_0`/`bit0`/`bit1` and `Lit` that builds through them.
//
// `real_sgn`: the sign members are ABOUT it, so every one of their
// statements spells it, but each opens by unfolding the definition and
// then argues about the guards — a body that never lets a sign term
// survive its first step has nothing to build one for, and the unfold
// itself takes the name rather than a handle.
// `real_div`: the division wing's statements spell `x / y`, and it is a
// DEFINED name — every member of that wing unfolds it at its first step
// and argues about the product underneath, so no body ever holds a
// quotient long enough to need to build one.
var vocab = registry.NewVocabSpec(realvocab.Table()).
	OpsName("sgnAbsOps").
	CoerceDomain(RealDomain).
	Embed(realvocab.NumeralsBundle).
	Term("real_abs").As("Abs").
	Term("real_neg").As("Neg").
	Term("real_le").As("Le").
	Term("real_lt").As("Lt").
	Term("real_mul").As("Times").
	Term("real_add").As("Add").
	Term("real_sub").As("Minus").
	Term("real_inv").As("Inv").
	Term("real_sgn").As("Sgn").
	Term("real_div").As("Div")

// Size is |a| — needed wherever a witness names the absolute value
// itself rather than the value under it.
func (v *sgnAbsOps) Size(a Term) Term { return v.Abs.Apply(a) }

// Product is a·b — for a body that names the product its statement is
// about, which the multiplicative members do at every premise. Named
// for the term rather than the operation so that it does not collide,
// at a reader's eye, with the `Mul` MEMBER it is used to state.
func (v *sgnAbsOps) Product(a, b Term) *TermWrapper { return v.Times.Apply(a, b) }

// Negate is -a — for a body that states the guard at a negated
// argument rather than letting the COND produce the negation.
func (v *sgnAbsOps) Negate(a Term) Term { return v.Neg.Apply(a) }

// Nonneg is the guard `&0 ≤ a` — the ABSOLUTE VALUE's own test, and so
// the term a member splits on when it splits on the size. Most members
// do not split at all: splitting is a move available to a member rather
// than one the chapter requires.
func (v *sgnAbsOps) Nonneg(a Term) Term { return v.Le.Apply(v.Lit(0), a) }

// Positive is the sign's outer guard `&0 < a` — what Nonneg is for the
// size, one relation stricter.
func (v *sgnAbsOps) Positive(a Term) Term { return v.Lt.Apply(v.Lit(0), a) }

// Negative is its mirror `a < &0`, the sign's inner guard. There are
// two because the definition asks two questions, nested, and neither is
// the other's negation: between them they leave a third region, which is
// the branch the sign sends to &0.
func (v *sgnAbsOps) Negative(a Term) Term { return v.Lt.Apply(a, v.Lit(0)) }

// Diff is a - b — the quantity the interval members take the size of.
func (v *sgnAbsOps) Diff(a, b Term) Term { return v.Minus.Apply(a, b) }

// Sum is a + b — the quantity the triangle inequality is about, and the
// bound it is compared against.
func (v *sgnAbsOps) Sum(a, b Term) Term { return v.Add.Apply(a, b) }

// Invert is a⁻¹ — the argument the division wing's members take the size
// or the sign of. Named for the operation rather than for the term
// because `Inv` is already the field's own word for the function, and a
// body reads better asking for the inverse OF something.
func (v *sgnAbsOps) Invert(a Term) Term { return v.Inv.Apply(a) }
