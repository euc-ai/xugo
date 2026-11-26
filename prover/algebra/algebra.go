// Package algebra is the group/monoid proof-script KIT: a ladder
// generator whose output is proof.Action values composed from the
// exported cite verbs. Placement (see prover/README.md for the tent
// doctrine): prover/ collects the fixed machinery that does not grow
// as theorems accumulate — the fixed/growing criterion (kits grow
// constructively, an engineering event per member; theorem corpora
// grow without bound and live in library/) — and within the tent this
// package sits ABOVE prover/proof, as a generator of proof script,
// unlike the certificate manufacturers under prover/solver/ that sit
// below it. Trust regime: every mathematical fact arrives as an
// explicit certificate parameter (no gates needed — every generated
// step cites only what the consumer passed, adding nothing to any
// proof's dependency or procedure base); a solver that bakes facts in
// and searches (omega, the linarith solver) pays the foundation-gate
// tax instead.
//
// The kit serves the "by group theory" folds that families
// otherwise re-derive from their own copies of the axioms. Any family
// with a commutative operation qualifies: the real tower's four
// additive layers today; ℕ's +/× monoids and future towers (int,
// rat) as they land. A consumer builds a Spec once per proof (its
// op/neg/zero vocabulary plus the axiom certificates, resolved
// through its OWN registry deps) and the Spec's methods generate the
// sections and cite-ladders.
//
// Migration lien: a member that produces a STATEMENT (RegroupSection)
// is a theorem in disguise — when an algebra chapter exists,
// that content moves there as a hypothesis-laden polymorphic theorem
// and this package keeps only the kit-shaped residue: statement
// templates, ladder generators, the instantiation ceremony.
//
// Applicability boundaries: RegroupSection needs only Sym + Assoc — a
// commutative-MONOID member, usable with Neg/LInv/LId left nil (ℕ
// qualifies). The Cancel* ladders need the full unconditional group.
// A CONDITIONAL group (real multiplication's x ≠ 0 ⇒ inv(x)·x = 1)
// does not fit the blind cite packs — a guarded variant is future
// work, gated on a concrete consumer.
//
// Two kinds of member, mirroring the lift package's split:
//
//   - Section generators (RegroupSection): a whole lemma — the caller's
//     statement text (the lift existenceText precedent) + proof — the
//     "prove it once over the signature" fold. The consumer's entry
//     reads the same deps it would with a handwritten section.
//   - Ladder generators (CancelShift / CancelShiftNeg): Action-valued
//     functions that COMPUTE the ground-cite tuples of a recurring
//     group-cancellation micro-pattern; the emitted cites are exactly
//     the ones the handwritten ladder spells, in the same order, so a
//     converted proof keeps its recorded .cnf.pb hitting.
package algebra

import (
	"fmt"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/proof"
)

// Group is the additive-group spec a consumer family instantiates per
// proof: term vocabulary (bound through the consumer's Script) plus
// the axiom certificates in the form its cite verbs want (normalized —
// ctx.DepNormalized / ctx.NormalizedThm of the family's own entries).
// LInv and LId are needed only by the cancellation methods.
type Group struct {
	// TypeText / OpText spell the carrier type and the operation as the
	// family's text DSL writes them (e.g. "hreal", "hreal_add") — used
	// by the section generators' statement templates.
	TypeText, OpText string

	Op, Neg ext.Term // the operation and (for cancellation) the inverse

	Sym, Assoc proof.Thm // commutativity / associativity certificates
	LInv, LId  proof.Thm // left-inverse / left-identity certificates (cancellation only)
}

// RegroupSection proves a ∀-closed AC rearrangement — an equation
// between two ⊕-sums over the same leaves, in any arity and any
// permutation:
//
//	⊢ ∀a b c d. (a⊕b) ⊕ (c⊕d) = (a⊕c) ⊕ (b⊕d)
//	⊢ ∀a b c d. (a⊕b) ⊕ (c⊕d) = (a⊕d) ⊕ (c⊕b)
//	⊢ ∀A B C D. (A⊕B) ⊕ (C⊕D) = (A⊕D) ⊕ (B⊕C)
//
// — the regrouping workhorse of the welldef and distributivity proofs,
// each of which wants a different bracketing. The STATEMENT is the
// interface: it is the section's headline, the thing a reader reads, so
// the caller writes it and the kit derives everything else. There is no
// permutation index and no shape closure to align against the text,
// because there is nothing for them to say that the statement does not
// already say.
//
// The proof is proof.ACRegroup at the section's own binders: the ac
// solver flattens both sides, checks the leaf multisets agree, and
// composes the rearrangement out of the supplied Assoc + Sym
// certificates by kernel steps alone. So the section carries no
// refutation — nothing searches, and a mis-stated permutation fails at
// the kit's validation with both leaf lists printed, rather than as a
// refute that quietly does not close.
//
// Returns the proved section; the consumer grounds it at its own atom
// tuples (or cites it as a simp rule).
func (g Group) RegroupSection(ctx *proof.Script, stmt string) *proof.GoalStackNode {
	sec := ctx.SectionText(stmt)
	sec.Do(g.Regroup())
	sec.Qed()
	return sec
}

// Regroup is RegroupSection's proof as a standalone Action, for a
// rearrangement stated somewhere other than a section — a Derive
// block's `Have`, say, whose claim is the same ∀-closed equation. The
// goal it runs on must be that equation; it strips the binders and
// derives the rearrangement at the resulting frees.
func (g Group) Regroup() proof.Action {
	return proof.Chain(
		proof.StripQuant(),
		proof.ACRegroup(g.Assoc, g.Sym),
	)
}

// Perm4Text spells RegroupSection's most common statement, the 4-atom
// transposition `(a⊕b) ⊕ (c⊕d) = (a⊕c) ⊕ (b⊕d)`, over this Group's
// type and operation. It exists so the two welldef proofs that want
// exactly this shape do not each re-spell it; a proof wanting any other
// bracketing passes its own text.
func (g Group) Perm4Text() string {
	return fmt.Sprintf(
		"∀a b c d:%[1]s. %[2]s(%[2]s(a, b), %[2]s(c, d)) = %[2]s(%[2]s(a, c), %[2]s(b, d))",
		g.TypeText, g.OpText)
}

// CancelShift emits the ground-cite ladder that cancels a LEADING
// shift z out of z ∘ (-z ∘ t):
//
//	z ∘ (-z ∘ t)  =  (z ∘ -z) ∘ t   [Assoc at (z, -z, t)]
//	              =  (-z ∘ z) ∘ t   [Sym at (z, -z)]
//	              =  e ∘ t          [LInv at z]
//	              =  t              [LId at t]
//
// The four tuples are computed from (z, t) — the plumbing the
// handwritten ladders spell by hand. Cites install ground facts; the
// caller's closing refutation (or eqSimplify at the cite) consumes
// them.
func (g Group) CancelShift(z, t ext.Term) proof.Action {
	return proof.Chain(
		proof.Cite(proof.MakeFact(g.Assoc), z, ext.Apply(g.Neg, z), t),
		proof.Cite(proof.MakeFact(g.Sym), z, ext.Apply(g.Neg, z)),
		proof.Cite(proof.MakeFact(g.LInv), z),
		proof.Cite(proof.MakeFact(g.LId), t),
	)
}

// CancelShiftNeg is CancelShift's mirror for a leading NEGATED shift
// -z ∘ (z ∘ t): Assoc at (-z, z, t) puts the inverse pair together
// already in LInv's orientation, so no Sym flip is needed.
func (g Group) CancelShiftNeg(z, t ext.Term) proof.Action {
	return proof.Chain(
		proof.Cite(proof.MakeFact(g.Assoc), ext.Apply(g.Neg, z), z, t),
		proof.Cite(proof.MakeFact(g.LInv), z),
		proof.Cite(proof.MakeFact(g.LId), t),
	)
}
