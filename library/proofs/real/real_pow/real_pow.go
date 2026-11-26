// real_pow.go — the chapter: ℝ's powers.
//
// Four parts, marked by banners:
//
// - Where ℝ's power comes from (the mint
// - The homomorphism laws
// - The factorization
// - The order part

package real_pow

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Where ℝ's power comes from (the mint
// ---------------------------------------------------------------------------
//
// where ℝ's power comes from (the mint, on Pow below), its two clauses as
// citable projections, and then the evaluations that pin one slot of the
// power and read the answer off those clauses: the base at 1 and at 0, the
// exponent at 1 and at 2, and the law that the embedding ℕ ↪ ℝ carries ℕ's
// power to this one. The same two clauses make it the monoid power of
// ℝ's product (MonoidPow).
//
// Each evaluation reads Pow's clauses plus one or two further facts
// it cites — a unit or zero law of multiplication, a numeral
// identity, or the embedding's product law. Three induct on the
// exponent (OnePow, ZeroPow, OfNumPow); PowOne and PowTwo have no
// branches at all, since a numeral exponent becomes a successor and
// Pow's step clause then fires a fixed number of times. No law here
// relates two exponents to one another; that is the tier above.
//
// Reading the `//` glosses on premises: each shows the equation in the
// direction the argument USES, which for most cites is the reverse of
// the clause as stated (`Normalize` picks the orientation an install
// arrives in). Where that choice is load-bearing rather than cosmetic,
// the site says so — see ZeroPow's base case.
//
// The members divide by SHAPE, and how a clause is cited follows: OnePow
// and ZeroPow close each case on a premise LIST, so they ground every
// clause they name, while PowOne, PowTwo and OfNumPow are chains and
// their clause cites sit in Calc legs, bare, acting as rewrite rules.
// The homomorphism part below states that position rule in full.

// ---------------------------------------------------------------------------
// Pow — the recursion equations of ℝ's power
// ---------------------------------------------------------------------------

// Pow — the recursion equations of exponentiation over ℝ: the empty
// product is &1, and each successor in the exponent is one more factor
// of the base.
//
// The two clauses ARE the definition (compiled against ℕ's recursion
// schema): the empty product is one, and one more factor multiplies by
// the base. `*` occurs in the step clause as an uninterpreted symbol —
// no property of multiplication is used.
var Pow = powThm{family.Define(registry.DefEntry{
	Name:  "Pow",
	Key:   "prop_2487de87ba158ef",
	Const: "real_pow",
	Type:  "real → num → real",
	Equations: []string{
		"∀x:real. real_pow(x, 0) = &1",
		"∀x:real. ∀n:num. real_pow(x, suc(n)) = x * real_pow(x, n)",
	},
})}

// ---------------------------------------------------------------------------
// PowExpZeroClause · PowExpSucClause — Pow's two clauses, one apiece
// ---------------------------------------------------------------------------

// The clause projections, mirroring nat_arith's per-operation pairs: each
// entry binds exactly the variables its equation mentions, so an
// induction case cites the one clause it reads instead of installing
// the pack. `Exp` in the names marks the slot the recursion runs on —
// the EXPONENT — which is what keeps them honest against the chapter's
// base/exponent naming convention: PowExpZeroClause is x⁰ = &1, the
// exponent pinned to zero. The law with the BASE pinned to zero is
// ZeroPow below, a theorem rather than a clause of the definition.

// PowExpZeroClause — Pow's zero clause: the empty product is &1,
// whatever the base.
var PowExpZeroClause = powExpZeroClauseThm{family.Add(registry.ProofEntry{
	Name: "PowExpZeroClause",
	Key:  "prop_db085324b0ce7d29",
	Build: family.Theorem("∀x:real. real_pow(x, 0) = &1",
		func(a *Argument, x Term) {
			a.Do(By(Pow))
		}),
})}

// PowExpSucClause — Pow's successor clause: one more factor of the
// base per successor in the exponent.
var PowExpSucClause = powExpSucClauseThm{family.Add(registry.ProofEntry{
	Name: "PowExpSucClause",
	Key:  "prop_fa6e27d623b9ec37",
	Build: family.Theorem("∀x:real. ∀n:num. real_pow(x, suc(n)) = x * real_pow(x, n)",
		func(a *Argument, x, n Term) {
			a.Do(By(Pow))
		}),
})}

// PowAddOne — the successor clause with the exponent spelled n + 1, the
// way an indexed statement writes the next index: n + 1 is suc(n).
var PowAddOne = powAddOneThm{family.Add(registry.ProofEntry{
	Name: "PowAddOne",
	Key:  "prop_4daa8acaa5f50634",
	Build: family.Theorem("∀x:real. ∀n:num. real_pow(x, n + 1) = x * real_pow(x, n)",
		func(a *Argument, x, n Term) {
			a.Do(Simp(Rev(nat_arith.Add1)))
			a.Show(
				"n + 1 is suc(n), and the successor clause fires",
				Cite(PowExpSucClause))
		}),
})}

// MonoidPow — ℝ's power is the monoid power of its product: both are x
// combined with itself n times by the same recursion, the empty product
// being 1, so the two agree at every n. Through it a law of the generic
// power reads at ℝ (comm_monoid.MapPow carries a power along a map into
// or out of ℝ's product).
var MonoidPow = monoidPowThm{family.Add(registry.ProofEntry{
	Name: "MonoidPow",
	Key:  "prop_af7e3579eb6dcd2e",
	Build: family.Theorem("∀x:real. ∀n:num. real_pow(x, n) = monoid_pow(real_mul, &1, x, n)",
		func(arg *Argument, x *Expr[Real], n *Expr[Nat]) {
			arg.Induct(n)
			arg.Base(
				"both are the empty product 1",
				Simp(Fwd(PowExpZeroClause), Fwd(comm_monoid.MonoidPowDef.Inst[Real]())),
				Refl())
			arg.Step(
				"both shed one factor of x",
				func(d *Argument, ih Fact) {
					d.Do(Simp(Fwd(PowExpSucClause), Fwd(comm_monoid.MonoidPowDef.Inst[Real]())), ih.Rw(), Basic())
				})
		}),
})}

// ===========================================================================
// The evaluations — one slot of the power pinned, the answer read off
// the clauses above
// ===========================================================================

// ---------------------------------------------------------------------------
// OnePow — every power of the base 1 is 1
// ---------------------------------------------------------------------------

// OnePow — every power of 1 is 1: the generic law that every power of
// the identity is the identity, at ℝ's product, ℝ's power being its
// product's monoid power (MonoidPow).
var OnePow = onePowThm{family.Add(registry.ProofEntry{
	Name: "OnePow",
	Key:  "prop_7c5e12b4b768e860",
	Build: family.Theorem("∀n:num. real_pow(&1, n) = &1",
		func(arg *Argument) {
			arg.Show(
				"every power of the identity is the identity: read as the monoid power of the reals' product",
				Simp(Fwd(MonoidPow)),
				By(comm_monoid.IdentityPow, real_ring.MulMonoid))
		}),
})}

// ---------------------------------------------------------------------------
// ZeroPow — the powers of the base 0, the one evaluation whose value is
// not uniform
// ---------------------------------------------------------------------------

// ZeroPow — the empty product is &1 whatever it is a product of, while
// every longer product of zeroes is &0. That is why the statement
// carries a COND, and why the proof settles the exponent's SHAPE rather
// than computing a single value; the two cases below say which shape
// gives which value.
//
// The induction is num's case split here: the two branches are computed
// independently and the step never reads its hypothesis.
var ZeroPow = zeroPowThm{family.Add(registry.ProofEntry{
	Name: "ZeroPow",
	Key:  "prop_66da8be66b34d509",
	Build: family.Theorem("∀n:num. real_pow(&0, n) = COND(n = 0, &1, &0)",
		func(a *Argument) {
			v := ops(a.Ctx())
			zero := v.Lit(0) // &0 — the base

			n := a.Binder("n")

			a.Induct(n)
			a.Base(
				"0 = 0 holds, so the COND is &1 — which is Pow's zero clause",
				// The clause is cited in its RAW stated orientation; the
				// chapter default (a bare entry premise) installs the
				// normalized one, `&1 = real_pow(x, 0)`. What makes this
				// leaf need the escape where its twins do not: here the
				// goal's &1 sits inside a COND and is the ONLY rewritable
				// occurrence, so the normalized direction fires there and
				// turns it back into a power of an unconstrained base —
				// leaving a free variable. The sibling base cases escape
				// this not by having more powers to rewrite — OnePow's and
				// OfNumPow's each carry exactly one — but because their
				// goal offers no second site the normalized direction can
				// fire at. What decides it in general is whether the
				// matched pattern BINDS: `&1` is closed and binds nothing,
				// so the rewrite cannot choose which power to produce.
				By(a.Ctx().Dep(PowExpZeroClause)),
			)
			a.Step(
				"suc n ≠ 0 sends the COND to &0, and Pow opens 0^suc "+
					"n into &0 · 0ⁿ, which the left-zero law collapses",
				By(
					At(PowExpSucClause, zero, n), // &0 · 0ⁿ = 0^suc n
					peano.SucNotZero,             // a successor is never 0, so the condition fails
					real_ring.MulLeftZero,
				),
			)
		}),
})}

// ---------------------------------------------------------------------------
// PowOne — the first power of a base is that base
// ---------------------------------------------------------------------------

// PowOne — the first power of a base is the base: the generic law at
// ℝ's product, through MonoidPow.
var PowOne = powOneThm{family.Add(registry.ProofEntry{
	Name: "PowOne",
	Key:  "prop_348733308bce7f27",
	Build: family.Theorem("∀x:real. real_pow(x, 1) = x",
		func(arg *Argument) {
			arg.Show(
				"the first power is the base: read as the monoid power of the reals' product",
				Simp(Fwd(MonoidPow)),
				By(comm_monoid.PowOne, real_ring.MulMonoid))
		}),
})}

// ---------------------------------------------------------------------------
// PowTwo — the square is the base times itself
// ---------------------------------------------------------------------------

// PowTwo — the square is the base times itself: the generic law at
// ℝ's product, through MonoidPow.
var PowTwo = powTwoThm{family.Add(registry.ProofEntry{
	Name: "PowTwo",
	Key:  "prop_8cf7a15e1b3a20cf",
	Build: family.Theorem("∀x:real. real_pow(x, 2) = x * x",
		func(arg *Argument) {
			arg.Show(
				"the square is the base times itself: read as the monoid power of the reals' product",
				Simp(Fwd(MonoidPow)),
				By(comm_monoid.PowTwo, real_ring.MulMonoid))
		}),
})}

// ---------------------------------------------------------------------------
// OfNumPow — the embedding carries ℕ's power to ℝ's
// ---------------------------------------------------------------------------

// OfNumPow — a power of an embedded natural is the embedded power. Only
// the BASE is embedded: an exponent is an ℕ index on both sides and
// never crosses.
//
// By induction on the exponent, and the two recursions run in lockstep:
// each side's zero clause gives the empty product (&1 on the left, 1
// embedded on the right), and each side's step clause sheds one factor
// of its own base. What joins the two sheddings is the one fact about
// the embedding this proof uses — that & carries a product to a product
// (OfNumMul). The legs of each case are those links.
//
// The two legs that read ℕ's recursion take it in its RAW stated
// orientation, and a PACK turns out to be no exception to the escape the
// members above take on single clauses: normalized, nat_pow's zero clause is
// flipped to `1 = nat_pow(m, 0)`, whose left pattern is the closed term `1`
// and binds nothing. Stated the other way round both clauses have
// patterns that bind, and the conjunction then rewrites where it stands
// — one clause per leg, which is why neither leg has to say which
// clause it means.
//
// Stated power-first, like every other fixed-slot member of this file:
// the subject is the ℝ power and the right-hand side is its value. (ℤ's
// twin, int_pow.OfNumPow, spells the mirror; both normalize alike, and
// each reads in its own chapter's direction.)
var OfNumPow = ofNumPowThm{family.Add(registry.ProofEntry{
	Name: "OfNumPow",
	Key:  "prop_1531fac503ecd58a",
	Build: family.Theorem("∀m n:num. real_pow(&m, n) = &nat_pow(m, n)",
		func(a *Argument, m, n Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			base := v.OfNum.Apply(m) // &m₀ — the embedded base

			// `nat_arith.NatPow` is the nat_pow recursion PACK — nat_arith's own
			// clause projections are unexported, so the pack is what
			// crosses the package boundary. Each case reads one of its two
			// clauses, and which one is decided by the leg's own shape, so
			// neither cite names an instance.
			a.Induct(n)
			a.Base(
				"n = 0: both empty products are &1 — Pow's zero clause "+
					"on the left, nat_pow's under the embedding on the right",
				CalcEq(
					Leg(
						v.Lit(1),
						// RAW orientation: normalized the clause reads
						// `&1 = real_pow(x, 0)`, whose left pattern is the
						// closed term `&1` and so cannot decide which power
						// to become.
						"the ℝ-side empty product is &1",
						Cite(PowExpZeroClause)),
					FinalLeg(
						"and ℕ's empty product is 1, which the embedding carries to that same &1",
						Cite(nat_arith.NatPow)),
				),
			)
			a.Step(
				"n → suc n: each side sheds one factor of its own base, and & identifies the two products",
				func(b *Argument, ih Fact) {
					// The ℕ-side power and the ℕ-side product the chain
					// passes through. nat_pow and ℕ's `*` belong to ℕ's
					// alphabet, not this chapter's, so both are read back
					// out of the leaf's own scope instead of being declared
					// here; `m₀` and `n₀` are the fixed spellings of this
					// section's own binders m and n, which is what makes
					// the terms the ones the goal shows.
					powMN := b.Term("nat_pow(m₀, n₀)")
					prodMN := b.Term("m₀ * nat_pow(m₀, n₀)")

					b.Do(CalcEq(
						Leg(
							v.Mul.Apply(base, v.Pow.Apply(base, n)),
							"Pow's step clause sheds one factor of the embedded base",
							Cite(PowExpSucClause)),
						Leg(
							v.Mul.Apply(base, v.OfNum.Apply(powMN)),
							"and the hypothesis turns the power that remains into the embedded ℕ power",
							ih.Rw(),
							Basic()),
						Leg(
							v.OfNum.Apply(prodMN),
							"the two embedded factors then gather into one — & carrying a product "+
								"to a product is the single fact about the embedding this proof uses",
							Cite(real_construction.OfNumMul)),
						FinalLeg(
							"and that ℕ product is what nat_pow's own step clause sheds",
							Cite(nat_arith.NatPow)),
					))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// The homomorphism laws
// ---------------------------------------------------------------------------
//
// the homomorphism laws: how the power interacts with the operations its
// base and its exponent are built from.
//
// Everything in the tier below pins one slot of the power and reads the
// answer off Pow's clauses. Nothing there relates two powers to one
// another. These do: each takes an operation — ℕ's addition or
// multiplication on the exponent side, ℝ's product, inverse or quotient
// on the base side — and says what the power does to it. README's
// movement 2 tells that story; what follows here is what a reader of
// the Go needs on top of it.
//
// The members are in the README's order: the two ℕ-exponent laws first,
// PowPow reading PowAdd, then the three ℝ-base laws, DivPow last with
// both of its premises immediately above it. The sign-and-size laws
// follow — AbsPow because it is InvPow's twin at the other unary
// operation, both saying the power commutes with something applied to
// the base, SgnPow because it is AbsPow's own twin at the sign, and
// SquareOfAbs because it belongs with AbsPow and its twin even though it
// is a statement about the SIGN rather than about iteration and does not
// cite it.
//
// Two reading conventions. The first is the chapter's, stated in
// the mint part above and repeated here only because this part leans on it
// harder: a `//` gloss on a premise shows that dep's equation in the
// direction the argument USES, which is often the reverse of the form
// the install arrives in — `Normalize` picks the orientation, and a site
// depends on which one it picked only where the comment says so. A `↦`
// gloss means something different and is used only for that: the goal
// this action leaves behind.
//
// ℕ's `+` and `*` belong to nat_arith's alphabet rather than this chapter's,
// so where a proof needs one as a term it reads it back out of the
// leaf's own scope (`a.Term`) instead of declaring it here.
//
// The second convention is this file's own:
//
// Every member here is a chain, so this file's clause cites sit in
// REWRITE position — inside a Calc leg — and are bare. What decides that
// is the POSITION, not the theorem, and the tier below shows both halves
// of the rule in one file: the members there that close on a premise
// LIST ground every clause they name, the ones that are chains cite bare
// exactly as here.
//
// In rewrite position a bare cite acts as a rewrite RULE and collapses
// every matching power in the goal at once, which is what a leg naming
// two or three powers wants; forcing witnesses there panics ("witnesses
// are unused", "install added no hyp"), and that panic says go bare,
// not restructure.
//
// The one crossing case is InvPow's base, where a Calc leg IS the clause
// read backwards: nothing is there to rewrite, so the cite has to install
// and is grounded and followed by Basic(). It is this part's only ground
// clause cite. Where a power sits under another operation the answer is
// still not grounding but Congr(), which strips the operation and hands
// the leg a goal the bare clause matches.

// ---------------------------------------------------------------------------
// PowAdd — adding exponents multiplies powers
// ---------------------------------------------------------------------------

// PowAdd — the statement that n ↦ xⁿ carries ℕ's addition to ℝ's
// multiplication: the generic law at ℝ's product, through MonoidPow.
//
// This theorem is part of the foundation the real-arithmetic decision
// procedure stands on, so everything it depends on joins that
// foundation: the generic power's laws, MonoidPow and ℝ's product monoid
// use no real arithmetic.
var PowAdd = powAddThm{family.Add(registry.ProofEntry{
	Name: "PowAdd",
	Key:  "prop_fe16ec538a2e009a",
	Build: family.Theorem("∀x:real. ∀m n:num. real_pow(x, m + n) = real_pow(x, m) * real_pow(x, n)",
		func(arg *Argument) {
			arg.Show(
				"exponents add: read as the monoid power of the reals' product",
				Simp(Fwd(MonoidPow)),
				By(comm_monoid.PowAdd, real_ring.MulMonoid))
		}),
})}

// ---------------------------------------------------------------------------
// PowPow — a power of a power multiplies the exponents
// ---------------------------------------------------------------------------

// PowPow — a power of a power is the power at the product of the
// exponents: the generic law at ℝ's product, through MonoidPow. It is
// part of the arithmetic decision procedure's foundation, as PowAdd is.
var PowPow = powPowThm{family.Add(registry.ProofEntry{
	Name: "PowPow",
	Key:  "prop_7e2a5d7b7765337d",
	Build: family.Theorem("∀x:real. ∀m n:num. real_pow(real_pow(x, m), n) = real_pow(x, m * n)",
		func(arg *Argument) {
			arg.Show(
				"a power of a power multiplies the exponents: read as the monoid power of the reals' product",
				Simp(Fwd(MonoidPow)),
				By(comm_monoid.PowPow, real_ring.MulMonoid))
		}),
})}

// ---------------------------------------------------------------------------
// MulPowDistrib — a power of a product is the product of the powers
// ---------------------------------------------------------------------------

// MulPowDistrib — a power of a product is the product of the powers:
// the generic law at ℝ's product, through MonoidPow; it is where the
// product's commutativity enters. It is part of the arithmetic decision
// procedure's foundation, as PowAdd is.
var MulPowDistrib = mulPowDistribThm{family.Add(registry.ProofEntry{
	Name: "MulPowDistrib",
	Key:  "prop_206110a9ce77d165",
	Build: family.Theorem("∀x y:real. ∀n:num. real_pow(x * y, n) = real_pow(x, n) * real_pow(y, n)",
		func(arg *Argument) {
			arg.Show(
				"a power of a product is the product of the powers: read as the monoid power of the reals' product",
				Simp(Fwd(MonoidPow)),
				By(comm_monoid.MulPow, real_ring.MulMonoid))
		}),
})}

// ---------------------------------------------------------------------------
// InvPow — inversion passes through a power
// ---------------------------------------------------------------------------

// InvPow — inverting a base and then taking a power is taking the power
// and then inverting.
//
// By induction on the exponent, with the two sides running the same
// recursion at bases x⁻¹ and x. The base case is the empty product on
// both sides — &1 on the left, and &1 again on the right once
// field.InvOne.Read(real_field.Field) says &1 is its own inverse. Each successor then
// sheds one factor per side, which leaves a product of inverses on the
// left against the inverse of a product on the right; that those two
// are the same thing is all the step knows about inversion:
//
//	(x⁻¹)^suc n = x⁻¹ · (x⁻¹)ⁿ = x⁻¹ · (xⁿ)⁻¹ = (x · xⁿ)⁻¹ = (x^suc n)⁻¹
//
// the second equality being the induction hypothesis and the third
// field.InvMul.Read(real_field.Field), read from right to left.
//
// The statement needs no hypothesis on x, and neither does the proof:
// neither inversion fact it cites carries a non-zero condition of its
// own, so the argument never has to ask whether x is invertible.
var InvPow = invPowThm{family.Add(registry.ProofEntry{
	Name: "InvPow",
	Key:  "prop_bf96b2e5615c515c",
	Build: family.Theorem("∀x:real. ∀n:num. real_pow(real_inv(x), n) = real_inv(real_pow(x, n))",
		func(a *Argument, x, n Term) {
			v := ops(a.Ctx())
			one := v.Lit(1)            // &1 — the empty product both sides collapse to
			invX := v.Inv.Apply(x)     // x₀⁻¹ — the base the left side iterates
			powXN := v.Pow.Apply(x, n) // x₀ⁿ — the power the right side inverts

			// Both cases are chains rather than single closes, and for the
			// same reason: each side's power has to be evaluated on its own
			// before the two meet, and the right side's evaluation happens
			// underneath the inverse. Cited there, the clause settles beside
			// the goal as a hypothesis without reaching into it. So each
			// chain ends with Congr(), which strips the common real_inv and
			// leaves a last leg whose goal IS the clause.
			a.Induct(n)
			a.Base(
				"n = 0: both empty products are &1, and &1 is its own inverse",
				CalcEq(
					Leg(
						one,
						"the empty product is &1 whatever it is a product of — here, of x₀⁻¹",
						Cite(PowExpZeroClause, invX)),
					Leg(
						v.Inv.Apply(one),
						"&1 is its own inverse",
						Cite(field.InvOne.Read(real_field.Field))),
					FinalLeg(
						"and under that inverse stands x₀'s own empty product",
						Congr(),
						Cite(PowExpZeroClause)), // ↦ &1 = real_pow(x₀, 0)
				),
			)
			a.Step(
				"n → suc n: each side sheds one factor of its own base, and inversion identifies the two products",
				func(b *Argument, ih Fact) {
					b.Do(CalcEq(
						Leg(
							v.Mul.Apply(invX, v.Pow.Apply(invX, n)),
							"the left side sheds a factor of its own base, x₀⁻¹",
							// the step clause, read at base x₀⁻¹.
							Cite(PowExpSucClause)),
						Leg(
							v.Mul.Apply(invX, v.Inv.Apply(powXN)),
							"and the hypothesis inverts the power that is left",
							ih.Rw(),
							Basic()),
						Leg(
							v.Inv.Apply(v.Mul.Apply(x, powXN)),
							"a product of inverses is the inverse of the product — all "+
								"the step knows about inversion, read from right to left",
							// multiplicativity, at the factors x₀ and x₀ⁿ.
							Cite(field.InvMul.Read(real_field.Field))),
						FinalLeg(
							"and under that inverse the right side sheds the matching factor of x₀",
							Congr(),
							Cite(PowExpSucClause)), // ↦ x₀ · x₀ⁿ = real_pow(x₀, suc n₀)
					))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// DivPow — a power of a quotient is the quotient of the powers
// ---------------------------------------------------------------------------

// DivPow — the one law in this file with no induction in it, because
// division is not an operation the power has to be related to: `/` is
// an abbreviation for multiplication by an inverse, so opening it
// leaves a product and an inverse, and the two laws already proved
// about those say everything.
//
//	(x/y)ⁿ = (x·y⁻¹)ⁿ = xⁿ·(y⁻¹)ⁿ = xⁿ·(yⁿ)⁻¹ = xⁿ/yⁿ
//
// the second equality being MulPowDistrib — the product it distributes
// over is the one the quotient became — and the third InvPow. The outer
// two are that same abbreviation read in its two directions, and they
// cost nothing: one unfold opens the quotients on both sides of the goal
// at once, so the chain the proof actually runs is the middle two links.
//
// As in InvPow, no hypothesis on y is needed anywhere — the quotient is
// a formal expression until something asks for y⁻¹·y, and nothing here
// does.
var DivPow = divPowThm{family.Add(registry.ProofEntry{
	Name: "DivPow",
	Key:  "prop_a0108d18349e988e",
	Build: family.Theorem("∀x y:real. ∀n:num. real_pow(x / y, n) = real_pow(x, n) / real_pow(y, n)",
		func(a *Argument, x, y, n Term) {
			v := ops(a.Ctx())
			powX := v.Pow.Apply(x, n) // x₀ⁿ — the factor that rides through untouched
			invY := v.Inv.Apply(y)    // y₀⁻¹ — the base the second power is taken at

			a.Do(
				// x / y ↦ x · y⁻¹, on both sides of the equation at once, and
				// neither quotient is rebuilt afterwards.
				Unfold(real_field.RealDivDef),
				CalcEq(
					Leg(
						v.Mul.Apply(powX, v.Pow.Apply(invY, n)),
						"the power distributes over the product the quotient has become",
						Cite(MulPowDistrib)),
					FinalLeg(
						"and the inversion in the second factor moves out from under its power",
						Cite(InvPow)),
				),
			)
		}),
})}

// ---------------------------------------------------------------------------
// AbsPow — the size of a power is the power of the size
// ---------------------------------------------------------------------------

// AbsPow — taking sizes commutes with taking powers. It holds because a
// power is an iterated product and |·| carries a product to the product
// of the sizes; beyond that one law the proof asks only what the size of
// &1 is.
//
// By induction on the exponent, the two recursions running in lockstep.
// Each side's zero clause gives the empty product — &1 on the left under
// a size, &1 on the right — and the two agree because the unit is its
// own size. Each successor sheds one factor from its own base, and what
// joins the two sheddings is real_sgn_abs.AbsMul:
//
//	|x^suc n| = |x · xⁿ| = |x| · |xⁿ|
//	 = |x| · |x|ⁿ = |x|^suc n
//
// the third equality being the induction hypothesis and the outer two
// Pow's step clause, read at the base x on the left and at |x| on the
// right. Nothing here consults the SIGN of x: the argument never asks
// which branch of |·| is taken, only that the branch commutes with
// multiplication.
var AbsPow = absPowThm{family.Add(registry.ProofEntry{
	Name: "AbsPow",
	Key:  "prop_2281df4cad935c70",
	Build: family.Theorem("∀x:real. ∀n:num. |real_pow(x, n)| = real_pow(|x|, n)",
		func(a *Argument, x, n Term) {
			ctx := a.Ctx()
			v := ops(ctx)

			absX := v.Abs.Apply(x)     // |x₀| — the base the right-hand power iterates
			powXN := v.Pow.Apply(x, n) // x₀ⁿ — the power the induction hypothesis is about

			a.Induct(n)
			a.Base(
				"n = 0: both sides are the empty product, and the unit is its own size",
				// The zero clause in its RAW stated orientation. Normalized
				// it reads `&1 = real_pow(x, 0)`, whose left-hand pattern
				// `&1` is a closed term: matching it binds nothing, so the
				// rewrite cannot tell which power the goal's &1 should
				// become and the leaf is left open — measured here, not
				// only inherited from the siblings that meet it. Stated the
				// other way round the clause collapses both powers where
				// they stand.
				Cite(PowExpZeroClause), // ↦ real_abs(&1) = &1
				Cite(real_sgn_abs.AbsOfOne),
			)
			a.Step(
				"n → suc n: each side sheds one factor of its own base, and |·| identifies the two products",
				func(b *Argument, ih Fact) {
					b.Do(CalcEq(
						Leg(
							v.Abs.Apply(v.Mul.Apply(x, powXN)),
							"Pow's step clause sheds one factor of x₀, inside the size where the power stands",
							Cite(PowExpSucClause)),
						Leg(
							v.Mul.Apply(absX, v.Abs.Apply(powXN)),
							"sizes multiply, so the size of that product splits at the "+
								"factor just shed — the one thing about |·| this proof uses",
							Cite(real_sgn_abs.AbsMul)),
						Leg(
							v.Mul.Apply(absX, v.Pow.Apply(absX, n)),
							"and the induction hypothesis turns the size of the power that remains into a power of the size",
							ih.Rw(),
							Basic()),
						FinalLeg(
							"which the step clause, read now at the base |x₀|, folds back into a power of suc n₀",
							Cite(PowExpSucClause)),
					))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// SgnPow — the sign of a power is the power of the sign
// ---------------------------------------------------------------------------

// SgnPow — taking signs commutes with taking powers: AbsPow's twin, with
// the sign where that member has the size. It holds for the same reason
// — a power is an iterated product and real_sgn carries a product to the
// product of the signs — and beyond that one law the proof asks only
// what the sign of &1 is.
//
// By induction on the exponent, the two recursions in lockstep exactly
// as in AbsPow. Each side's zero clause gives the empty product, and the
// two agree because the unit is its own sign; each successor sheds one
// factor from its own base, and what joins the two sheddings is
// real_sgn_abs.SgnMul:
//
//	sgn(x^suc n) = sgn(x · xⁿ) = sgn x · sgn(xⁿ)
//	 = sgn x · (sgn x)ⁿ = (sgn x)^suc n
//
// the third equality being the induction hypothesis and the outer two
// Pow's step clause, read at the base x on the left and at sgn x on the
// right.
//
// The sign of &1 is not a law the sign chapter states, so the base case
// establishes it in place from real_sgn's own definition: the outer
// guard asks whether &0 < &1, which real_order_ring.ZeroLessThanOne
// settles, and the definition then reads &1 off its first branch.
var SgnPow = sgnPowThm{family.Add(registry.ProofEntry{
	Name: "SgnPow",
	Key:  "prop_56a1d095386ad618",
	Build: family.Theorem("∀x:real. ∀n:num. sgn(real_pow(x, n)) = real_pow(sgn(x), n)",
		func(a *Argument, x, n Term) {
			v := ops(a.Ctx())

			sgnX := v.Sgn.Apply(x)     // sgn x₀ — the base the right-hand power iterates
			powXN := v.Pow.Apply(x, n) // x₀ⁿ — the power the induction hypothesis is about

			a.Induct(n)
			a.Base(
				"n = 0: both sides are the empty product, and the unit is its own sign",
				func(b *Argument) {
					signOfOne := b.Have(
						"the sign of one is one: the outer guard &0 < &1 holds and the definition reads its first branch",
						"sgn(&1) = &1",
						Unfold(real_sgn_abs.RealSgnDef),
						Simp(Fwd(real_order_ring.ZeroLessThanOne)),
						Basic())
					b.Show(
						"both powers at exponent zero are the unit, so the claim is that one fact",
						// x⁰ ↦ &1 on both sides — the direction named by hand, as at AbsPow's base
						Simp(Fwd(PowExpZeroClause)),
						By(signOfOne))
				},
			)
			a.Step(
				"n → suc n: each side sheds one factor of its own base, "+
					"and the sign of that product splits at the factor shed",
				func(b *Argument, ih Fact) {
					b.Do(CalcEq(
						Leg(
							v.Sgn.Apply(v.Mul.Apply(x, powXN)),
							"Pow's step clause sheds one factor of x₀, inside the sign where the power stands",
							Cite(PowExpSucClause)),
						Leg(
							v.Mul.Apply(sgnX, v.Sgn.Apply(powXN)),
							"signs multiply, so the sign of that product splits at the "+
								"factor just shed — the one law about real_sgn this proof cites",
							Cite(real_sgn_abs.SgnMul)),
						Leg(
							v.Mul.Apply(sgnX, v.Pow.Apply(sgnX, n)),
							"and the induction hypothesis turns the sign of the power that remains into a power of the sign",
							ih.Rw(),
							Basic()),
						FinalLeg(
							"which the step clause, read now at the base sgn x₀, folds back into a power of suc n₀",
							Cite(PowExpSucClause)),
					))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// SquareOfAbs — the square cannot tell |x| from x
// ---------------------------------------------------------------------------

// SquareOfAbs — squaring forgets the sign, so taking the absolute value
// of the base first changes nothing.
//
// The only case analysis is real_abs's own definition: |x| is x when the
// base is nonnegative and −x when it is not. The first branch leaves the
// goal an identity and closes itself, so the whole argument is the
// second — and there the sign hypothesis is never consulted again,
// because (−x)² = x² holds of every base. PowTwo turns both squares into
// products, and the two signs then come out of the two factors and
// cancel:
//
//	x · x = −(−(x · x)) = −(x · (−x)) = (−x) · (−x)
//
// read in the direction the goal wants — a double negation put in, then
// one sign distributed into each factor.
//
// It does not cite AbsPow, though |x|² = |x²| is the short route and
// AbsPow stands two members above it. That route is closed by the
// constraint below, read in the awkward direction: AbsPow already sits
// inside the foundation this theorem founds.
//
// The dependency list is four long and stops there deliberately.
// Real arithmetic's decision procedure is founded on this theorem, so
// everything reachable from here joins that foundation, and a law inside
// it can no longer use real arithmetic in its own proof.
// All four deps are clear of it; a fifth would have to be checked before
// being added. PowTwoNonneg is the other theorem that procedure is
// founded on and carries the same constraint.
var SquareOfAbs = squareOfAbsThm{family.Add(registry.ProofEntry{
	Name: "SquareOfAbs",
	Key:  "prop_9c5a952c9b029207",
	Build: family.Theorem("∀x:real. real_pow(x, 2) = real_pow(|x|, 2)",
		func(a *Argument, x Term) {
			// The chain's two bridges. real_neg is not one of this chapter's
			// build handles — it belongs to the ring — so both terms are read
			// out of the leaf's own scope, the way OfNumPow reads ℕ's nat_pow.
			doubled := a.Term("--(x * x)") // −(−(x₀ · x₀))
			oneSign := a.Term("-(x * -x)") // −(x₀ · (−x₀))

			a.Do(
				// |x₀| is x₀ or −x₀ according to its sign.
				Unfold(real_sgn_abs.RealAbsDef),
				// ↦ ¬(&0 ≤ x₀) ⇒ x₀² = (−x₀)². The nonnegative branch became
				// x₀² = x₀² and closed itself.
				CondRewrite(),
				// The surviving branch's hypothesis plays no part below.
				StripImp(),
				// ↦ x₀ · x₀ = −x₀ · −x₀. A bare cite in rewrite position acts
				// as a rewrite RULE, so this one collapses both squares at
				// once — which is what a goal naming two of them wants.
				Cite(PowTwo),
				CalcEq(
					Leg(
						doubled,
						"a double negation leaves the square where it was",
						Cite(real_ring.NegNeg)),
					Leg(
						oneSign,
						"under that outer sign, the inner one moves into the right factor",
						Congr(),
						Cite(real_ring.MulRightNeg)),
					FinalLeg(
						"and the outer sign moves into the left factor",
						Cite(real_ring.MulLeftNeg)),
				),
			)
		}),
})}

// ---------------------------------------------------------------------------
// The factorization
// ---------------------------------------------------------------------------
//
// One identity, standing apart from the homomorphism laws above: it
// relates no operation to the power but factors a DIFFERENCE of two
// powers through a sum of mixed products, and it is the chapter's one
// law that reaches into Σ — the sums chapter's telescope evaluates it.
// The entry below carries the mechanism; nothing here is inducted on,
// and where its legs read Pow's clauses they ground them on a premise
// list, as the order part does throughout.

// ---------------------------------------------------------------------------
// DifferenceOfPowers — a difference of powers factors through the sum
// of the mixed products
// ---------------------------------------------------------------------------

// DifferenceOfPowers — the classical factorization: x − y divides
// xⁿ − yⁿ, and the quotient is the sum of the mixed products of degree
// n − 1, written here as a sum over 0 .. n − 1. It is a telescope.
//
// Write F(i) := xⁱ · y^(n − i). Between the bounds, each term of the
// sum scaled by x − y is a forward difference of F,
//
//	(x − y) · xⁱ · y^(n−1−i) = x · xⁱ · y^(n−1−i) − xⁱ · y · y^(n−1−i)
//	 = F(i + 1) − F(i)
//
// because below the top of the interval n − i is one more than
// n − 1 − i, and Pow's step clause reads each successor as one more
// factor of its base. So the scalar moves inside the sum, the sum reads
// as Σ (F(i + 1) − F(i)), and the telescope evaluates that at the two
// ends — the interval is non-empty exactly because 1 ≤ n. At the ends
// the exponents n − n and n − 0 collapse and both empty products become
// &1, which leaves xⁿ − yⁿ.
//
// This is the one member of the part that reaches into Σ; the three
// series tools it needs — the scalar law, congruence over an interval,
// the telescope — are the sums chapter's, and Pow's clauses do the
// rest.
//
// What is spent on ℕ is the monus bookkeeping of the exponents. Below
// the top, n is (n − 1 − i) + (i + 1), from which n − (i + 1) and n − i
// are read off by cancelling; at the ends, n − n is 0 and n − 0 is n.
var DifferenceOfPowers = differenceOfPowersThm{family.Add(registry.ProofEntry{
	Name: "DifferenceOfPowers",
	Key:  "prop_2e0d1b1cec796115",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real. ∀n:num.",
		Hypotheses: []string{
			"1 ≤ n",
		},
		Conclusion: "real_pow(x, n) - real_pow(y, n) = " +
			"(x - y) * sum(0 .. n - 1, λi:num. real_pow(x, i) * real_pow(y, n - 1 - i))",
	},
		func(a *Argument, x, y *Expr[Real], n *Expr[Nat], atLeastOne Fact) {
			ctx := a.Ctx()
			zero := ctx.Nat(0)
			one := ctx.Nat(1)
			top := a.TermAs[Nat]("n - 1") // the top of the interval

			// The summand and the interval it is summed over, the summand
			// scaled by x − y, and the function F whose forward differences
			// the scaled summand turns out to be — spelled in the form the
			// telescope's summand takes, F(k + 1) − F(k).
			difference := a.TermAs[Real]("x - y")
			interval := a.TermAs[Set[Nat]]("0 .. n - 1")
			summand := a.TermAs[Fun[Nat, Real]]("λi:num. real_pow(x, i) * real_pow(y, n - 1 - i)")
			scaled := a.TermAs[Fun[Nat, Real]]("λi:num. (x - y) * (real_pow(x, i) * real_pow(y, n - 1 - i))")
			F := a.TermAs[Fun[Nat, Real]]("λi:num. real_pow(x, i) * real_pow(y, n - i)")
			differences := a.TermAs[Fun[Nat, Real]](
				"λk:num. real_pow(x, k + 1) * real_pow(y, n - (k + 1)) - real_pow(x, k) * real_pow(y, n - k)")

			rule := a.Have(
				"between the bounds, each term of the scaled sum is a forward difference of F",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"0 ≤ i",
						"i ≤ n - 1",
					},
					Conclusion: "(x - y) * (real_pow(x, i) * real_pow(y, n - 1 - i)) = " +
						"real_pow(x, i + 1) * real_pow(y, n - (i + 1)) - real_pow(x, i) * real_pow(y, n - i)",
				},
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					between := b.Assume()
					gap := b.TermAs[Nat]("n - 1 - i") // the summand's exponent of y
					next := b.TermAs[Nat]("i + 1")
					sucGap := b.TermAs[Nat]("suc(n - 1 - i)")
					// The rearrangements the step makes — one sum in ℕ, two
					// products in ℝ — come from the AC kits over the chapters'
					// own associativity and commutativity certificates.
					addAC := nat_arith.AddAC(ctx)
					mulAC := real_construction.MulAC(ctx)
					gapPlusNext := b.TermAs[Nat]("n - 1 - i + (i + 1)")
					gapPlusOnePlusI := b.TermAs[Nat]("n - 1 - i + 1 + i")

					asSum := b.Have(
						"n is the gap n − 1 − i, plus i + 1",
						"n = n - 1 - i + (i + 1)",
						By(
							between,
							atLeastOne,
							nat_monus.SubAddCancel.At(top, i),
							nat_monus.SubAddCancel.At(n, one),
							nat_arith.AddAssoc.At(gap, i, one)))
					down := b.Have(
						"so n − (i + 1) is the gap",
						"n - (i + 1) = n - 1 - i",
						// Normalized: with n read as the sum, cancelling is a
						// simplification, so no refutation is wanted.
						By(Normalized, asSum, nat_monus.AddSubCancel.At(gap, next)))
					up := b.Have(
						"and n − i is one more than it",
						"n - i = suc(n - 1 - i)",
						// Normalized: the sum regrouped and its 1 folded into a
						// successor, cancelling is again a simplification.
						By(
							Normalized,
							asSum,
							addAC.Eq(gapPlusNext, gapPlusOnePlusI),
							nat_arith.Add1.At(gap),
							nat_monus.AddSubCancel.At(sucGap, i)))

					// The two regroupings, as equations: a product of powers is
					// opaque to the closer, so each drives a rewrite rather than
					// serving as a premise.
					joinX := b.Have(
						"x joins its own power",
						"x * (real_pow(x, i) * real_pow(y, n - 1 - i)) = x * real_pow(x, i) * real_pow(y, n - 1 - i)",
						ACRegroupWith(mulAC))
					crossY := b.Have(
						"and y crosses xⁱ to join its own",
						"y * (real_pow(x, i) * real_pow(y, n - 1 - i)) = real_pow(x, i) * (y * real_pow(y, n - 1 - i))",
						ACRegroupWith(mulAC))

					b.Do(CalcEq(
						Leg(
							b.TermAs[Real]("x * (real_pow(x, i) * real_pow(y, n - 1 - i)) - "+
								"y * (real_pow(x, i) * real_pow(y, n - 1 - i))"),
							"the factor x − y distributes",
							Cite(real_ring.SubRightDistrib)),
						Leg(
							b.TermAs[Real]("x * real_pow(x, i) * real_pow(y, n - 1 - i) - "+
								"real_pow(x, i) * (y * real_pow(y, n - 1 - i))"),
							"regroup, so that each base stands beside its own power",
							joinX.Rw(),
							crossY.Rw(),
							Basic()),
						FinalLeg(
							"and Pow's step clause folds each pair back into a power, at the exponents i + 1 and n − i",
							By(up, down, nat_arith.Add1.At(i), PowExpSucClause.At(x, i), PowExpSucClause.At(y, gap))),
					))
				}))

			a.Do(
				// The chain runs from the product side, where the
				// factorization is expanded rather than found, so the goal
				// is turned round first.
				Symm(),
				CalcEq(
					Leg(
						a.TermAs[Real]("sum(0 .. n - 1, λi:num. (x - y) * (real_pow(x, i) * real_pow(y, n - 1 - i)))"),
						"the factor x − y moves inside the sum",
						Cite(real_sum.ScalarLeft, difference, summand, interval)),
					Leg(
						a.TermAs[Real]("sum(0 .. n - 1, "+
							"    λk:num. real_pow(x, k + 1) * real_pow(y, n - (k + 1)) - real_pow(x, k) * real_pow(y, n - k))"),
						"where, between the bounds, each term is a forward difference of F",
						// Normalized: the rule IS the congruence's antecedent, so
						// the equation of sums is read off by simplification.
						By(rule, real_sum.IntervalCongruence.At(zero, top, scaled, differences))),
					Leg(
						a.TermAs[Real]("COND(0 ≤ n - 1, "+
							"    real_pow(x, n - 1 + 1) * real_pow(y, n - (n - 1 + 1)) - "+
							"    real_pow(x, 0) * real_pow(y, n - 0), "+
							"    &0)"),
						"so the sum telescopes: F one above the top of the interval, less F at its bottom",
						By(real_sum.TelescopeUp.At(zero, top, F))),
					Leg(
						a.TermAs[Real]("real_pow(x, n) * real_pow(y, n - n) - real_pow(x, 0) * real_pow(y, n - 0)"),
						"the interval is not empty, and one above its top is n",
						By(atLeastOne, nat_order.ZeroLessEq.At(top), nat_monus.SubAddCancel.At(n, one))),
					Leg(
						a.TermAs[Real]("real_pow(x, n) * real_pow(y, 0) - real_pow(x, 0) * real_pow(y, n)"),
						"n − n is 0, and n − 0 is n",
						// Normalized: three ground evaluations, each a rewrite.
						// n − 0 takes two of them, n + 0 − 0 = n and then n + 0 = n,
						// because m − 0 = m is exported only inside the
						// nat_monus.Sub pack.
						By(
							Normalized,
							nat_monus.SubRefl.At(n),
							nat_monus.AddSubCancel.At(n, zero),
							nat_arith.AddZero.At(n))),
					Leg(
						a.TermAs[Real]("real_pow(x, n) * &1 - &1 * real_pow(y, n)"),
						"and both empty products are &1",
						// The zero clause in its RAW stated orientation, as
						// PowOne's descent takes it: normalized, its closed
						// left pattern `&1` cannot decide which power to become.
						Cite(PowExpZeroClause)),
					FinalLeg(
						"which the two unit laws drop",
						Cite(real_ring.MulRightId),
						Cite(real_construction.MulLeftId)),
				),
			)
		}),
})}

// ---------------------------------------------------------------------------
// The order part
// ---------------------------------------------------------------------------
//
// the order part: what a power does to the sign of its base, and how
// powers compare.
//
// The parts above are about equalities; nothing in them mentions ≤. Five
// of these members reach their results by iterating a product one factor
// at a time, and the rest by citing them — which is why the file reads
// as five inductions followed by four consequences.
//
// One mechanical note, because four members meet it and the reason is
// not local to any of them. Pow's ZERO clause resists being named as a
// premise: normalized it reads `&1 = real_pow(x, 0)`, whose left-hand
// pattern `&1` is a CLOSED term, so matching it binds nothing and the
// `x` on the other side stays free — the rewrite cannot tell which power
// the `&1` should become. Measured three ways on `&0 ≤ real_pow(x₀, 0)`:
// the clause cited bare, in its raw orientation, and as a ground
// `At(clause, x)` premise all fail the same way. The direction has to be
// named by hand, and two spellings do it — `LeanRw` where several powers
// must clear at once (it runs to fixpoint), `a.Have(instance, …)` +
// `f.Rw()` where one must and naming it reads better.
//
// Pow's SUCCESSOR clause has no such trouble: its pattern binds, so a
// plain ground `At(PowExpSucClause, x, n)` premise closes comparison
// goals throughout this file. The obstruction is a fact about that one
// clause, not about comparison goals.

// ---------------------------------------------------------------------------
// PowNonneg — a nonnegative base has nonnegative powers
// ---------------------------------------------------------------------------

// PowNonneg — nonnegativity survives every power, because it survives
// each single factor.
//
// By induction on the exponent. The base case never consults the
// hypothesis at all: the empty product is &1 whatever the base was, and
// &1 is nonnegative for the reason every embedded natural number is.
// The step multiplies by one more copy of the base, so it is exactly one
// application of the law that a product of two nonnegatives is
// nonnegative —
//
//	&0 ≤ x^suc n ⇐ &0 ≤ x · xⁿ ⇐ &0 ≤ x and &0 ≤ xⁿ
//
// the left arrow being Pow's step clause and the right real_construction.LessEqMul,
// with the hypothesis supplying the first premise and the induction
// hypothesis the second. The hypothesis is therefore consulted at
// exactly one place in the proof, and that place says nothing about the
// exponent — which is why it can stand outside the induction rather than
// being carried through it.
//
// The two cases are the same two moves: read Pow's clause for this
// exponent, rewrite the goal through it, and cite the sign fact that
// covers what the clause left behind. Only that last fact differs —
// about an embedded number in one case, about a product in the other —
// so the induction contributes no machinery of its own beyond choosing
// which of the two clauses is read.
var PowNonneg = powNonnegThm{family.Add(registry.ProofEntry{
	Name: "PowNonneg",
	Key:  "prop_5babea2f80164d41",
	Build: family.Theorem(Statement{
		Binders: "∀x:real. ∀n:num.",
		Hypotheses: []string{
			"&0 ≤ x",
		},
		Conclusion: "&0 ≤ real_pow(x, n)",
	},
		func(a *Argument, x, n Term, nonneg Fact) {
			ctx := a.Ctx()
			v := ops(ctx)
			powXN := v.Pow.Apply(x, n) // x₀ⁿ — the power the step adds a factor to
			// The empty exponent, as an ℕ numeral: the slot Pow's zero
			// clause pins, not the ℝ literal the clause evaluates to.
			expZero := ctx.Numeral(0)

			a.Induct(n)
			a.Base(
				"n = 0: the empty product is &1, which is nonnegative because it is an embedded number",
				func(b *Argument) {
					empty := b.Have(
						"the empty exponent leaves the empty product, whatever the base",
						MakeProp(v.Pow.Apply(x, expZero).Eq(v.Lit(1))),
						Cite(PowExpZeroClause))

					b.Do(empty.Rw()) // ↦ &0 ≤ &1

					b.Show(
						"and &1 is an embedded natural number, none of which is negative",
						Cite(real_order_ring.NumNonneg))
				},
			)
			a.Step(
				"n → suc n: one more factor of x₀, and a product of two nonnegatives is nonnegative",
				func(b *Argument, ih Fact) {
					expSuc := b.Ctx().TermText("suc(n₀)") // the exponent this case is about

					oneMore := b.Have(
						"a successor exponent is one more factor of the base on top of the power below it",
						MakeProp(v.Pow.Apply(x, expSuc).Eq(v.Mul.Apply(x, powXN))),
						Cite(PowExpSucClause))

					b.Do(oneMore.Rw()) // ↦ &0 ≤ x₀ · x₀ⁿ

					b.Show(
						"the two factors are the base, nonnegative by hypothesis, and "+
							"the power below it, nonnegative by the induction hypothesis",
						By(
							nonneg, // &0 ≤ x₀
							ih,     // &0 ≤ x₀ⁿ
							At(real_construction.LessEqMul, x, powXN), // &0 ≤ x₀ ∧ &0 ≤ x₀ⁿ ⇒ &0 ≤ x₀ · x₀ⁿ
						))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// PowPos — a positive base has positive powers
// ---------------------------------------------------------------------------

// PowPos — by induction on the exponent, with the base's positivity
// standing throughout rather than being spent: every successor
// multiplies by x once more, so the hypothesis is read again at each of
// them.
//
// The empty product is &1, which is positive whatever the base was —
// the one case that does not use the hypothesis at all. Each successor
// sheds one factor,
//
//	x^suc n = x · xⁿ
//
// and the two factors are positive for different reasons: the left by
// the hypothesis, the right by the induction hypothesis. That a product
// of two positives is positive is real_order_ring.MulPos, and it is the
// whole of the step.
var PowPos = powPosThm{family.Add(registry.ProofEntry{
	Name: "PowPos",
	Key:  "prop_d760effd8eb9bc84",
	Build: family.Theorem(Statement{
		Binders: "∀x:real. ∀n:num.",
		Hypotheses: []string{
			"&0 < x",
		},
		Conclusion: "&0 < real_pow(x, n)",
	},
		func(a *Argument, x, n Term, pos Fact) {
			ctx := a.Ctx()
			v := ops(ctx)
			powXN := v.Pow.Apply(x, n) // x₀^n₀ — the second factor, and what the induction hypothesis is about

			a.Induct(n)
			a.Base(
				"n = 0: the empty product is &1 whatever its base, and the unit is positive",
				// Rewritten in place rather than named as a fact first (as
				// PowNonneg does): the zero clause is wanted at one power
				// only, so doing it here is shorter.
				Expect(LeanRw(ctx.Dep(PowExpZeroClause)),
					Case(
						"the empty product is &1, whatever its base",
						Cite(PowExpZeroClause)),
					// ↦ &0 < &1
					Case(
						"which is the unit's own positivity",
						Cite(real_order_ring.ZeroLessThanOne)),
				),
			)
			a.Step(
				"n → suc n: the power sheds one factor of x₀",
				func(b *Argument, ih Fact) {
					b.Show(
						"and a product of two positives is positive — x₀ by "+
							"the standing hypothesis, x₀^n₀ by the induction's",
						// Normalized — engine shaping: the product law arrives
						// with its guards negated, and the two positivity facts
						// discharge them by simplification.
						By(
							Normalized,
							At(PowExpSucClause, x, n), // x₀ · x₀^n₀ = x₀^suc n₀
							pos,                       // &0 < x₀
							ih,                        // &0 < x₀^n₀
							// &0 < x₀ ∧ &0 < x₀^n₀ ⇒ &0 < x₀ · x₀^n₀
							At(real_order_ring.MulPos, x, powXN),
						))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// PowMonoBase — a bigger nonnegative base gives bigger powers
// ---------------------------------------------------------------------------

// PowMonoBase — the power is monotone in its base, once the lower base
// is known not to be negative.
//
// By induction on the exponent, with the hypothesis standing throughout
// rather than being spent: the empty product is &1 on either side, so
// the base case compares &1 with itself, and each successor multiplies
// both sides by one more copy of their own base,
//
//	x^suc n = x · xⁿ	y^suc n = y · yⁿ
//
// which leaves the step a single comparison of two products, at the two
// bases and the two powers below them. That is what
// real_order_ring.LessEqMul2 does, and the instance it needs here is
// supplied three-quarters over: x ≤ y is the hypothesis, xⁿ ≤ yⁿ the
// induction hypothesis, &0 ≤ x the hypothesis again. The remaining
// quarter is &0 ≤ xⁿ, which the induction never produces — getting it
// is what PowNonneg is for, and what makes this member sit above that
// one.
//
// So the nonnegativity hypothesis does two jobs, and the second is the
// reason the theorem needs it at all: a comparison of products is only
// as good as the sign of what does the multiplying. It is the LOWER
// side that has to be signed, both times. Nothing here ever asks about
// y or about yⁿ — both are nonnegative anyway, sitting where they do,
// but no step of the argument consults it.
var PowMonoBase = powMonoBaseThm{family.Add(registry.ProofEntry{
	Name: "PowMonoBase",
	Key:  "prop_74a597c333808a70",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real. ∀n:num.",
		Hypotheses: []string{
			"&0 ≤ x",
			"x ≤ y",
		},
		Conclusion: "real_pow(x, n) ≤ real_pow(y, n)",
	},
		func(a *Argument, x, y, n Term, bounds Fact) {
			ctx := a.Ctx()
			v := ops(ctx)
			// The two powers the step compares underneath its new factor.
			powXN := v.Pow.Apply(x, n) // x₀ⁿ
			powYN := v.Pow.Apply(y, n) // y₀ⁿ

			a.Induct(n)
			a.Base(
				"n = 0: both sides are the empty product, so the comparison is &1 against itself",
				// One rewrite clears BOTH powers: the clause is read as a
				// rule rather than at an instance, so its pattern matches
				// each base in turn. Naming the direction by hand is the
				// part's standing obligation on a comparison goal, stated
				// once in its header.
				Expect(LeanRw(ctx.Dep(PowExpZeroClause)),
					Case(
						"the empty product is &1, whatever its base",
						Cite(PowExpZeroClause)),
					// ↦ &1 ≤ &1
					Case(
						"what it leaves is reflexivity's own instance",
						Cite(real_order_ring.LessEqRefl)),
				),
			)
			a.Step(
				"n → suc n: one more factor on each side, and two products compare factor by factor",
				func(b *Argument, ih Fact) {
					nonneg := b.Have(
						"the power being multiplied is itself nonnegative, its base being nonnegative",
						"&0 ≤ real_pow(x₀, n₀)",
						By(bounds, At(PowNonneg, x, n))) // &0 ≤ x₀ ⇒ &0 ≤ x₀ⁿ

					b.Show(
						"the left product's two factors are both nonnegative and each sits below its partner on the right",
						// Normalized: the product law arrives as a clause with
						// its four guards negated, and the facts beside it
						// discharge them by simplification.
						By(
							Normalized,
							At(PowExpSucClause, x, n), // x₀ · x₀ⁿ = x₀^suc n₀
							At(PowExpSucClause, y, n), // y₀ · y₀ⁿ = y₀^suc n₀
							bounds,                    // &0 ≤ x₀, and x₀ ≤ y₀
							nonneg,                    // &0 ≤ x₀ⁿ
							ih,                        // x₀ⁿ ≤ y₀ⁿ
							// &0 ≤ x₀ ∧ x₀ ≤ y₀ ∧ &0 ≤ x₀ⁿ ∧ x₀ⁿ ≤ y₀ⁿ ⇒ x₀ · x₀ⁿ ≤ y₀ · y₀ⁿ
							At(real_order_ring.LessEqMul2, x, y, powXN, powYN),
						))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// PowMonoBaseStrict — and strictly bigger, once the exponent is nonzero
// ---------------------------------------------------------------------------

// PowMonoBaseStrict — two ordered nonnegative bases stay strictly
// ordered under a common exponent, provided the exponent is not zero.
//
// The guard is the whole difference from the non-strict comparison, and
// it is mathematics rather than bookkeeping: x⁰ and y⁰ are both &1, so
// strictness genuinely fails at the empty exponent. An induction on the
// exponent therefore has no base to stand on — and needs none, the guard
// having made that case vacuous. What it needs instead is a base one rung
// up, and that rung appears inside the step: when the exponent below is
// zero the powers are single factors,
//
//	x^suc 0 = x · x⁰ = x · &1 = x
//
// so the goal there IS the hypothesis x < y, and nothing is proved that
// was not assumed. That is the induction's true base; it appears inside
// the step because an induction over ℕ starts at 0, and suc 0 is one
// rung above where it starts.
//
// Above that rung the exponent below is nonzero, which is exactly what
// unlocks the induction hypothesis, and one more factor of the base joins
// each side. The two products are then compared factor by factor by
// real_order_ring.LessThanMul2, whose four premises are the two standing
// hypotheses about the bases, the nonnegativity of the smaller tail power
// (PowNonneg), and the induction hypothesis comparing the two tails —
// which is where the strictness that the conclusion needs comes from.
var PowMonoBaseStrict = powMonoBaseStrictThm{family.Add(registry.ProofEntry{
	Name: "PowMonoBaseStrict",
	Key:  "prop_f9b80d0c241792fe",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real. ∀n:num.",
		Hypotheses: []string{
			"n ≠ 0",
			"&0 ≤ x",
			"x < y",
		},
		Conclusion: "real_pow(x, n) < real_pow(y, n)",
	},
		func(a *Argument, x, y Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			// The exponent stays bound: the guard names it, so stripping it
			// ahead of the induction would leave a hypothesis about the very
			// variable the induction has to generalize. The goal spells it n₀
			// once x and y are stripped off in front of it; Binder takes the
			// statement's name.
			n := a.Binder("n")
			expZero := ctx.Numeral(0) // the ℕ numeral the guard compares against
			powXN := v.Pow.Apply(x, n)
			powYN := v.Pow.Apply(y, n)

			a.Induct(n)
			a.Base(
				"n = 0: the guard reads 0 ≠ 0, so this case is excluded "+
					"rather than proved — as it must be, x⁰ and y⁰ both being &1",
				TrivialNormalized())
			a.Step(
				"n → suc n: one more factor of each base, compared against each other",
				func(b *Argument, ih Fact) {
					expSuc := b.Ctx().TermText("suc(n₀)") // the exponent this case is about
					bounds := b.Assume()

					nonzero := b.Unless(
						n.Eq(expZero),
						"n₀ = 0: suc 0 is where the induction really starts, and there each power is a single factor",
						Given(func(c *Argument, isZero Fact) {
							// x^suc 0 = x is PowOne, and this recomputes it rather than
							// citing it. Not for economy: this theorem is denied real
							// arithmetic by the capability witness — it is inside that
							// decision procedure's foundation — while PowOne is still
							// allowed it. Depending on PowOne from here would pull it
							// into the foundation and make its own proof circular, the
							// same constraint that sends PowTwo through MonoidPow and
							// comm_monoid.PowTwo.
							//
							// Both sides collapse the same way, so the computation
							// is written once and read at each base in turn.
							collapse := func(label string, base Term) Fact {
								return c.Have(
									label,
									MakeProp(v.Pow.Apply(base, expSuc).Eq(base)),
									CalcEq(
										Leg(
											v.Mul.Apply(base, v.Pow.Apply(base, n)),
											"Pow's step clause sheds the one factor there is",
											Cite(PowExpSucClause)),
										Leg(
											v.Mul.Apply(base, v.Lit(1)),
											"and what stands below it is the empty product, this case's exponent being zero",
											// Congr() sets the shared factor aside, leaving the zero
											// clause itself at the base.
											isZero.Rw(),
											Congr(),
											Cite(PowExpZeroClause, base)),
										FinalLeg(
											"which is the unit, and a factor of &1 changes nothing",
											Cite(real_ring.MulRightId)),
									))
							}
							firstX := collapse("the smaller base's first power is that base", x)
							firstY := collapse("and so is the larger's", y)

							c.Show(
								"so the comparison to prove is the one already assumed",
								By(Normalized, firstX, firstY, bounds))
						}))

					tailNonneg := b.Have(
						"the smaller base's tail power is nonnegative, the base being so",
						"&0 ≤ real_pow(x₀, n₀)",
						By(bounds, At(PowNonneg, x, n))) // &0 ≤ x₀ ⇒ &0 ≤ x₀^n₀

					tailStrict := b.Have(
						"and the induction hypothesis compares the two tails, now that the exponent below is nonzero",
						"real_pow(x₀, n₀) < real_pow(y₀, n₀)",
						By(bounds, nonzero, ih))

					b.Show(
						"one more factor on each side keeps the comparison: base against base, tail against tail",
						By(
							bounds,
							tailNonneg,
							tailStrict,
							// &0 ≤ x₀ ∧ x₀ < y₀ ∧ &0 ≤ x₀^n₀ ∧ x₀^n₀ < y₀^n₀ ⇒ x₀ · x₀^n₀ < y₀ · y₀^n₀
							At(real_order_ring.LessThanMul2, x, y, powXN, powYN),
							// Pow's step clause, bare: the comparison above is between
							// two products, and each is an instance of it, so no single
							// witness tuple names the work. In rewrite position the
							// clause folds both back into powers of suc n₀ at once.
							PowExpSucClause,
						))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Bernoulli — a power of 1 + x stays above its linear part
// ---------------------------------------------------------------------------

// Bernoulli — Bernoulli's inequality: for x at least −1, the powers of
// 1 + x never fall below the linear part 1 + n·x of their expansion,
// which is what turns a multiple into a power. By induction on the
// exponent, the hypothesis standing throughout: at 0 both sides are &1,
// and each successor multiplies the power by one more factor 1 + x. The
// step passes through the product of that factor with the old linear
// part,
//
//	(1 + x)(1 + n·x) = 1 + (n + 1)·x + n·x²
//
// which exceeds the new linear part by n·x², never negative, and which
// the induction hypothesis puts below the next power once it is scaled
// by 1 + x. That scaling is where each step reads the hypothesis: a
// comparison keeps its direction only under a factor that is not
// negative.
var Bernoulli = bernoulliThm{family.Add(registry.ProofEntry{
	Name: "Bernoulli",
	Key:  "prop_2bc6ef7a2eda892f",
	Build: family.Theorem(Statement{
		Binders: "∀x:real. ∀n:num.",
		Hypotheses: []string{
			"-&1 ≤ x",
		},
		Conclusion: "&1 + &n * x ≤ real_pow(&1 + x, n)",
	},
		func(a *Argument, x *Expr[Real], n *Expr[Nat], atLeastMinusOne Fact) {
			a.Induct(n)
			a.Base(
				"n = 0: both sides are &1, no multiple of x on the left and the empty product on the right",
				// Bernoulli sits above real arithmetic's foundation, so arith
				// evaluates the empty power itself.
				ByArith())
			a.Step(
				"n → suc n: the power takes one more factor 1 + x, which is not negative",
				func(b *Argument, ih Fact) {
					base := b.TermAs[Real]("&1 + x")
					linear := b.TermAs[Real]("&1 + &n * x")        // the linear part the induction hypothesis bounds
					power := b.TermAs[Real]("real_pow(&1 + x, n)") // the power it bounds it by

					baseNonneg := b.Have(
						"the new factor is not negative, x being at least −1",
						"&0 ≤ &1 + x",
						ByArith(atLeastMinusOne))
					squareTerm := b.Have(
						"nor is n·x², a square scaled by an embedded natural",
						"&0 ≤ &n * (x * x)",
						ByArith())

					b.Show(
						"so one rung up the linear part still stays below the power",
						real_order_ring.OrderCalc(b.Ctx()).CalcLeibniz(b.TermAs[Real]("&1 + &suc(n) * x"),
							EqLeg(
								b.TermAs[Real]("&1 + (&n + &1) * x"),
								"the successor embeds as n + 1",
								Cite(real_ring.OfNumSuc)),
							LeLeg(
								b.TermAs[Real]("(&1 + x) * (&1 + &n * x)"),
								"multiplied out, the product exceeds it by n·x²",
								ByArith(squareTerm)),
							LeLeg(
								b.TermAs[Real]("(&1 + x) * real_pow(&1 + x, n)"),
								"the induction hypothesis, scaled by the nonnegative factor",
								By(baseNonneg, ih, real_order_ring.LessEqMulLeft.At(base, linear, power))),
							EqLeg(
								b.TermAs[Real]("real_pow(&1 + x, suc(n))"),
								"which is Pow's step clause: one more factor of the base",
								Cite(PowExpSucClause))))
				})
		}),
})}

// ---------------------------------------------------------------------------
// PowAboveTangentLine — on ⟦0, ∞⟭ a power lies above its tangent lines
// ---------------------------------------------------------------------------

// PowAboveTangentLine — on ⟦0, ∞⟭ the power tⁿ⁺¹ lies above its
// tangent line at u: uⁿ⁺¹ + (n + 1)·uⁿ·(v − u) ≤ vⁿ⁺¹. By induction on
// n: the gap at n + 1 is v times the gap at n plus (n + 1)·uⁿ·(v − u)²,
// and both parts are nonnegative.
var PowAboveTangentLine = powAboveTangentLineThm{family.Add(registry.ProofEntry{
	Name: "PowAboveTangentLine",
	Key:  "prop_fc77f3898350d799",
	Build: family.Theorem(Statement{
		Binders: "∀u v:real. ∀n:num.",
		Hypotheses: []string{
			"&0 ≤ u",
			"&0 ≤ v",
		},
		Conclusion: "real_pow(u, n + 1) + &(n + 1) * real_pow(u, n) * (v - u) ≤ real_pow(v, n + 1)",
	},
		func(arg *Argument, u, v *Expr[Real], uNonneg, vNonneg Fact) {
			arg.Induct("n")
			arg.Base(
				"at n = 0 both sides are v",
				ByArith())
			arg.Step(
				"the gap at n + 1 is v times the gap at n plus (n + 1)·uⁿ·(v − u)²",
				func(b *Argument, ih Fact) {
					n := b.TermAs[Nat]("n")
					coefficient := b.TermAs[Real]("&(n + 1) * real_pow(u, n)")
					gap := b.Have(
						"the gap at n + 1 splits as v times the gap at n plus (n + 1)·uⁿ·(v − u)²",
						"real_pow(v, n + 1 + 1) - "+
							"(real_pow(u, n + 1 + 1) + &(n + 1 + 1) * real_pow(u, n + 1) * (v - u)) = "+
							"v * (real_pow(v, n + 1) - (real_pow(u, n + 1) + &(n + 1) * real_pow(u, n) * (v - u))) + "+
							"&(n + 1) * real_pow(u, n) * (v - u) * (v - u)",
						Simp(Fwd(PowAddOne), Fwd(real_construction.OfNumAdd)),
						ByArith())
					positive := b.Have(
						"(n + 1)·uⁿ is nonnegative",
						"&0 ≤ &(n + 1) * real_pow(u, n)",
						ByArith(uNonneg, PowNonneg.At(u, n)))
					square := b.Have(
						"so is (n + 1)·uⁿ·(v − u)²",
						"&0 ≤ &(n + 1) * real_pow(u, n) * (v - u) * (v - u)",
						ByArith(positive, real_construction.LessEqMul.At(coefficient, b.TermAs[Real]("(v - u) * (v - u)"))))
					scaled := b.Have(
						"and so is v times the gap at n, by the induction hypothesis",
						"&0 ≤ v * (real_pow(v, n + 1) - (real_pow(u, n + 1) + &(n + 1) * real_pow(u, n) * (v - u)))",
						ByArith(
							ih,
							vNonneg,
							real_construction.LessEqMul.At(
								v,
								b.TermAs[Real]("real_pow(v, n + 1) - (real_pow(u, n + 1) + &(n + 1) * real_pow(u, n) * (v - u))"))))
					b.Show(
						"so the gap at n + 1 is nonnegative",
						Simp(Fwd(nat_arith.Add1)),
						ByArith(gap, scaled, square))
				})
		}),
})}

// ---------------------------------------------------------------------------
// OneLessEqPow — a base at or above the unit never falls below it
// ---------------------------------------------------------------------------

// OneLessEqPow — no induction, and that is the whole point of where it
// sits: the comparison it asserts is between two bases raised to the
// SAME exponent, which is what PowMonoBase already settled. Take that
// comparison at the two bases &1 and x —
//
//	&1ⁿ ≤ xⁿ
//
// and read the left side, which is the unit whatever the exponent was
// (OnePow). The nonnegativity PowMonoBase asks of its lower base is
// asked of &1 rather than of x, so the hypothesis of this theorem is
// never used for it: &1 is nonnegative because it is an embedded
// natural number, which is real_order_ring.NumNonneg at 1.
//
// Inducting instead would work and would prove a weaker-looking thing
// twice: the step's `&1 ≤ x · xⁿ` is a product comparison, so it would
// re-derive on the spot the case of PowMonoBase's own step that is
// already standing above it.
var OneLessEqPow = oneLessEqPowThm{family.Add(registry.ProofEntry{
	Name: "OneLessEqPow",
	Key:  "prop_63a057bfc58c7380",
	Build: family.Theorem(Statement{
		Binders: "∀x:real. ∀n:num.",
		Hypotheses: []string{
			"&1 ≤ x",
		},
		Conclusion: "&1 ≤ real_pow(x, n)",
	},
		func(a *Argument, x, n Term, atLeastOne Fact) {
			ctx := a.Ctx()
			v := ops(ctx)
			one := v.Lit(1)          // &1 — the lower of the two bases
			expOne := ctx.Numeral(1) // the ℕ 1 that names &1 as an embedded number

			mono := a.Have(
				"the unit lies below x₀ and is itself nonnegative, so the powers of the two compare the same way",
				"real_pow(&1, n₀) ≤ real_pow(x₀, n₀)",
				By(
					atLeastOne,                            // &1 ≤ x₀
					At(real_order_ring.NumNonneg, expOne), // &0 ≤ &1
					// &0 ≤ &1 ∧ &1 ≤ x₀ ⇒ &1ⁿ ≤ x₀ⁿ
					At(PowMonoBase, one, x, n),
				))

			a.Show(
				"and the unit's own powers are all the unit, so that is what stands on the left",
				By(mono, OnePow))
		}),
})}

// ---------------------------------------------------------------------------
// PowMonoExp — a base at or above the unit grows with its exponent
// ---------------------------------------------------------------------------

// PowMonoExp — monotonicity in the EXPONENT, where PowMonoBase above
// is monotonicity in the base: there the exponent was common and the
// two bases compared, here the base is common and the two exponents do.
//
// No induction, and again the reason is that the recursion is already
// packaged: PowAdd says what a sum of exponents is, and ℕ's order is
// the existence of a gap (nat_order.LessEqExists), so m ≤ n IS
// n = m + d for some d, and
//
//	xⁿ = x^(m+d) = xᵐ · x^d
//
// turns a comparison of two exponents into a comparison of a factor
// with itself times something. That something is at least the unit —
// OneLessEqPow immediately above, at the gap — so multiplying the whole
// comparison &1 ≤ x^d by xᵐ gives the theorem, once xᵐ·&1 is read as
// xᵐ.
//
// Scaling a comparison needs the scaling factor to be nonnegative, and
// that is the one place the hypothesis &1 ≤ x is consulted a second
// time: OneLessEqPow at the SMALLER exponent puts &1 below xᵐ, and the
// unit is above &0, so transitivity through the unit signs the factor.
// The chain the argument runs is therefore
//
//	xᵐ = xᵐ · &1 ≤ xᵐ · x^d = x^(m+d) = xⁿ
//
// with the middle link the scaled comparison and the outer three all
// equations.
var PowMonoExp = powMonoExpThm{family.Add(registry.ProofEntry{
	Name: "PowMonoExp",
	Key:  "prop_b9e6aaf78e9ec4d7",
	Build: family.Theorem(Statement{
		Binders: "∀x:real. ∀m n:num.",
		Hypotheses: []string{
			"&1 ≤ x",
			"m ≤ n",
		},
		Conclusion: "real_pow(x, m) ≤ real_pow(x, n)",
	},
		func(a *Argument, x, m, n Term, bounds Fact) {
			ctx := a.Ctx()
			v := ops(ctx)
			zero, one := v.Lit(0), v.Lit(1)
			expOne := ctx.Numeral(1)  // the ℕ 1 that names &1 as an embedded number
			powM := v.Pow.Apply(x, m) // x₀^m₀ — the smaller power, and the scaling factor

			// ℕ's order IS the existence of a gap, so the two exponents differ
			// by a d₀ the rest of the proof raises x₀ to.
			d, gap := a.Obtain(
				"the larger exponent is the smaller one plus a gap",
				"∃d:num. n₀ = m₀ + d",
				By(bounds, nat_order.LessEqExists))

			powD := v.Pow.Apply(x, d) // x₀^d₀ — what the gap contributes

			gapAtLeastOne := a.Have(
				"what the gap contributes is at least the unit, the base being at least the unit",
				"&1 ≤ real_pow(x₀, d₀)",
				By(bounds, At(OneLessEqPow, x, d))) // &1 ≤ x₀ ⇒ &1 ≤ x₀^d₀

			smallAtLeastOne := a.Have(
				"and so is the smaller power itself",
				"&1 ≤ real_pow(x₀, m₀)",
				By(bounds, At(OneLessEqPow, x, m))) // the same law, read at the smaller exponent

			smallNonneg := a.Have(
				"which signs it: it sits above the unit, and the unit above &0",
				"&0 ≤ real_pow(x₀, m₀)",
				By(
					smallAtLeastOne,
					At(real_order_ring.NumNonneg, expOne),               // &0 ≤ &1
					At(real_construction.LessEqTrans, zero, one, powM))) // &0 ≤ &1 ∧ &1 ≤ x₀^m₀ ⇒ &0 ≤ x₀^m₀

			scaled := a.Have(
				"so it may scale the gap's comparison without turning it round",
				"real_pow(x₀, m₀) * &1 ≤ real_pow(x₀, m₀) * real_pow(x₀, d₀)",
				By(
					smallNonneg,
					gapAtLeastOne,
					// &0 ≤ x₀^m₀ ∧ &1 ≤ x₀^d₀ ⇒ x₀^m₀ · &1 ≤ x₀^m₀ · x₀^d₀
					At(real_order_ring.LessEqMulLeft, powM, one, powD)))

			a.Show(
				"and the two ends of that comparison are the powers the theorem names",
				By(
					scaled,
					gap,                            // n₀ = m₀ + d₀
					At(real_ring.MulRightId, powM), // x₀^m₀ · &1 = x₀^m₀
					// Last, and the goal closes as it installs: with the gap
					// already read into the larger exponent, this is what
					// identifies the scaled comparison's right end with x₀^n₀.
					PowAdd,
				))
		}),
})}

// ---------------------------------------------------------------------------
// PowMonoExpBelowOne — a base between zero and the unit falls with its exponent
// ---------------------------------------------------------------------------

// PowMonoExpBelowOne — a nonnegative base at most one is nonincreasing
// in its exponent: the extra factors form a power at most one.
var PowMonoExpBelowOne = powMonoExpBelowOneThm{family.Add(registry.ProofEntry{
	Name: "PowMonoExpBelowOne",
	Key:  "prop_2fe81e6d9ce437e",
	Build: family.Theorem(Statement{
		Binders: "∀r:real. ∀m n:num.",
		Hypotheses: []string{
			"&0 ≤ r",
			"r ≤ &1",
			"m ≤ n",
		},
		Conclusion: "r ^ n ≤ r ^ m",
	}, func(a *Argument, r *Expr[Real], m, n *Expr[Nat], bounds Fact) {
		d, gap := a.ObtainAs[Nat](
			"the larger exponent is the smaller one plus a gap",
			"∃d:num. n = m + d",
			By(bounds, nat_order.LessEqExists))
		tail := a.Have(
			"the extra factors have product at most one",
			"r ^ d ≤ &1",
			By(bounds, PowMonoBase.At(r, a.TermAs[Real]("&1"), d), OnePow))
		factorization := a.Have(
			"adding the gap multiplies by its power",
			"r ^ n = r ^ m * r ^ d",
			By(gap, PowAdd))
		a.Show(
			"multiplying a nonnegative power by a factor at most one cannot increase it",
			ByArith(factorization, tail, bounds, PowNonneg.At(r, m)))
	}),
})}

// ---------------------------------------------------------------------------
// PowTwoNonneg — the square is never negative
// ---------------------------------------------------------------------------

// PowTwoNonneg — a square is never negative, stated of this chapter's
// power. There is no argument of its own to make: PowTwo evaluates the
// numeral exponent, turning the power into a product of the base with
// itself, and what is left standing is precisely what
// real_order_ring.SquareNonneg establishes of such a product.
//
// So the two say one thing at the two spellings of "square" — real_pow(x, 2)
// here, x · x in the ring — and the whole content of this member is that
// they are the same square. The name records that too: the plain
// SquareNonneg is taken, by the ring's own entry for its own spelling.
//
// The dependency list stops at those two on purpose, and not for economy.
// Real arithmetic's decision procedure is founded on this theorem, so
// everything reachable from here joins that foundation — and a law inside
// the foundation can no longer use real arithmetic in its own proof. Both
// deps are clear of it; a third would have to be checked before being
// added. That is the same constraint that sends PowTwo through MonoidPow and
// comm_monoid.PowTwo rather than the shorter route through PowOne — and this
// entry is one of the two roots that made it bite.
var PowTwoNonneg = powTwoNonnegThm{family.Add(registry.ProofEntry{
	Name: "PowTwoNonneg",
	Key:  "prop_2082e8045fc19a1c",
	Build: family.Theorem("∀x:real. &0 ≤ real_pow(x, 2)",
		func(a *Argument, x Term) {
			a.Do(
				// ↦ &0 ≤ x₀ * x₀
				Cite(PowTwo),
				Cite(real_order_ring.SquareNonneg),
			)
		}),
})}

// ---------------------------------------------------------------------------
// AbsLessEqIffPowTwoLessEq — squares compare as the sizes of their bases do
// ---------------------------------------------------------------------------

// AbsLessEqIffPowTwoLessEq — one square is at most another exactly when the size
// of its base is at most the size of the other's. The square's order
// fact, and the part's boundary with the sign-and-size chapter: squaring
// forgets the sign and keeps the order of what remains.
//
// SquareOfAbs reads each square as the square of a size, x² = |x|² and
// y² = |y|², so the statement compares two powers at a common exponent
// against a comparison of their bases, and those bases are nonnegative
// (real_sgn_abs.AbsNonneg). The two directions are then the two
// monotonicity laws of the base:
//
//	⇐ by contraposition: were |x| ≤ |y| false, |y| < |x|
//	 (real_order_ring.NotLessThan), so |y|² < |x|² by PowMonoBaseStrict
//	 at (|y|, |x|, 2) — the exponent, being suc 1, is not zero — which
//	 NotLessThan again reads as the denial of |x|² ≤ |y|²;
//	⇒ |x| ≤ |y| gives |x|² ≤ |y|², PowMonoBase at (|x|, |y|, 2).
//
// Each direction is one deduction from its ground instances; nothing
// is unfolded, and no comparison is ever made between x and y
// themselves.
var AbsLessEqIffPowTwoLessEq = absLessEqIffPowTwoLessEqThm{family.Add(registry.ProofEntry{
	Name: "AbsLessEqIffPowTwoLessEq",
	Key:  "prop_b265210dd0958a0e",
	Build: family.Theorem("∀x y:real. |x| ≤ |y| ⇔ real_pow(x, 2) ≤ real_pow(y, 2)",
		func(a *Argument, x, y Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			absX := v.Abs.Apply(x) // |x₀|
			absY := v.Abs.Apply(y) // |y₀|
			one := ctx.Numeral(1)
			two := ctx.Numeral(2)            // the exponent, suc 1
			sqAbsX := v.Pow.Apply(absX, two) // |x₀|²
			sqAbsY := v.Pow.Apply(absY, two) // |y₀|²

			a.Iff()
			a.Forward(
				"the bases are nonnegative and in order, so their squares are in order",
				func(b *Argument, sizes Fact) {
					b.Show(
						"|x₀|² ≤ |y₀|² by the monotonicity of a power in a "+
							"nonnegative base, and those are the squares of x₀ and y₀",
						By(
							Normalized,
							At(SquareOfAbs, x),            // x₀² = |x₀|²
							At(SquareOfAbs, y),            // y₀² = |y₀|²
							sizes,                         // |x₀| ≤ |y₀|
							At(real_sgn_abs.AbsNonneg, x), // &0 ≤ |x₀|
							// &0 ≤ |x₀| ∧ |x₀| ≤ |y₀| ⇒ |x₀|² ≤ |y₀|²
							At(PowMonoBase, absX, absY, two),
						))
				})
			a.Backward(
				"by contraposition: sizes out of order would put the "+
					"squares strictly out of order, against the hypothesis",
				func(b *Argument, squares Fact) {
					b.Show(
						"so |x₀| ≤ |y₀|: NotLessThan read at the sizes and "+
							"again at their squares brackets the strict monotonicity",
						By(
							At(SquareOfAbs, x), // x₀² = |x₀|²
							At(SquareOfAbs, y), // y₀² = |y₀|²
							squares,            // x₀² ≤ y₀²
							// ¬(|y₀| < |x₀|) ⇔ |x₀| ≤ |y₀|
							At(real_order_ring.NotLessThan, absY, absX),
							At(real_sgn_abs.AbsNonneg, y), // &0 ≤ |y₀|
							nat_arith.Two,                 // 2 = suc(1)
							At(peano.SucNotZero, one),     // suc(1) ≠ 0
							// 2 ≠ 0 ∧ &0 ≤ |y₀| ∧ |y₀| < |x₀| ⇒ |y₀|² < |x₀|²
							At(PowMonoBaseStrict, absY, absX, two),
							// ¬(|y₀|² < |x₀|²) ⇔ |x₀|² ≤ |y₀|²
							At(real_order_ring.NotLessThan, sqAbsY, sqAbsX),
						))
				})
		}),
})}
