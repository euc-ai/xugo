/**
 * File: rewrite.go
 *
 * Defines term rewriting system and specific rewrite rules for logical transformations.
 *
 * Type definition:
 * - Rewrite: Function type that converts a term t to a theorem ⊢ t = ...
 *
 * Basic rewrites:
 * - BetaRewrite: (λx.t(x))(y) → t(y) (shallow)
 * - DeepBeta: Beta reduction at all levels (deep)
 * - EtaRewrite: λx.t(x) → t when x not free in t (shallow)
 * - etaContextRewrite: η-reduction of a λ argument or λ body, outside ∀/∃/∃!/ε/= (shallow)
 * - DeepBetaEta: Combined beta-eta reduction at all levels (deep)
 * - HilbertRewrite: Converts εx.(x=t) → t, εP → εx.P(x) (shallow)
 * - HilbertExistsRewrite: P(εx.P(x)) → ∃x.P(x) (deep)
 * - BoolRewrite: Basic boolean simplifications (shallow)
 * - DeepBoolRewrite: Boolean simplifications at all levels (deep)
 *
 * Negation handling:
 * - DoubleNegRewrite: ¬¬A → A (shallow)
 * - PushNegRewrite: Moves negation inward (shallow)
 * - DeepNegRewrite: Combined negation normalization (deep)
 *
 * Quantifier handling:
 * - QuantifierRewrite: ∀P → ∀x.P(x), ∃P → ∃x.P(x), etc. (shallow)
 * - UniqueRewrite: expands ∃! to ∀ and ∃ using AltUnique (shallow)
 * - UniqueWitnessRewrite: ∃!x.P(x) → ∃x.(P(x) ∧ ∀y.(P(y) ⇒ y = x)), using WitnessUnique (shallow)
 * - UniversalPrenexRewrite: Moves ∀ outward (shallow)
 * - DeepUniversalPrenexRewrite: Prenex form for ∀ at all levels (deep)
 * - ExistentialPrenexRewrite: Moves ∃ outward (shallow)
 * - DeepExistentialPrenexRewrite: Prenex form for ∃ at all levels (deep)
 * - IndependentExistsPrenexRewrite: ∀ȳ.∃k̄.Φ → ∃K₀.(… ∀ȳ.∃K₁.…) for the
 *   ∃-binders whose part of Φ mentions no ȳ (independent_exists_prenex.go)
 *
 * Formula conversion:
 * - ImplyToOrRewrite: (l ⇒ r) → (¬l ∨ r) (shallow)
 * - IffToOrRewrite: (l ⇔ r) → ((l ∧ r) ∨ (¬l ∧ ¬r)) (shallow)
 * - FunEqRewrite: λx.l = λx.r → ∀x.(l = r) (shallow)
 *
 * Associativity and commutativity:
 * - AssocANDRewrite: Normalizes AND structure, e.g., (x ∧ (y ∧ z)) → ((x ∧ y) ∧ z)
 * - AssocORRewrite: Normalizes OR structure
 * - ArrangeANDChain, ArrangeORChain, arrangeIFFChain: Reorders terms
 *
 * Distributivity:
 * - DistributeListORAND: p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)
 * - DistributeListANDOR: p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r)
 *
 * Simplification:
 * - MergeANDRewrite, MergeORRewrite: Removes redundant terms
 * - SimplifyConjunct, SimplifyDisjunct: Complex simplifications
 * - DisjunctSortRewrite: Orders disjunction components
 * - ConjunctSortRewrite: Orders conjunction components
 *
 * Function composition:
 * - BasicRewritesWith(...): Combines basic rewrites with extra rewrites
 * - BasicRewrite: Standard set of combined rewrites
 *
 * Specialized rewrites:
 * - SkolemRewrite: Handles Skolemization (shallow)
 * - ForAllANDRewrite: ∀x.(l ∧ r) → (∀x.l ∧ ∀x.r) (shallow)
 * - ExistsORRewrite: ∃x.(l ∨ r) → (∃x.l ∨ ∀x.r) (shallow)
 * - ForAllORRewrite: ∀x.∀y.(l(x) ∨ r(y)) → (∀x.l(x) ∨ ∀y.r(y))
 * - ExistsANDRewrite: ∃x.∃y.(l(x) ∧ r(y)) → (∃x.l(x) ∧ ∃y.r(y))
 *
 * Term substitution:
 * - EqRewrite, EqReplacementRewrite: Various forms of equality substitution
 * - BoundVarRewrite: Controls bound variable renaming
 */

package prop

import "github.com/euc-ai/xugo/core"

// Converts a term t to a thm in the form of ⊢ t = ...
type Rewrite func(Term) *PropWrapper

var NilRewrite = func(Term) *PropWrapper { return nil }

// Rewrites all possible β-collapse, e.g. (λx.t(x))(y) = t(y).
// Shallow rewrite.
var betaRewrite = betaRewriteImpl()

// BetaRewrite is the shallow β-collapse, for a caller merging it with
// rewrites of its own in one deep walk.
var BetaRewrite Rewrite = betaRewrite

// Deep β-collapse rewrite.
var DeepBeta = DeepRewrite(betaRewrite)

// Rewrite a term using β-collapse of the input abs term.
var betaAbsRewrite = betaAbsRewriteImpl

// Deep β-collapse rewrite for a certain abs term.
func DeepBetaAbs(abs AbsTerm) Rewrite { return DeepRewrite(betaAbsRewrite(abs)) }

// Rewrites all possible η-collapse, e.g. λx.t(x) = t (providing x not in t).
// Shallow rewrite.
var etaRewrite = etaRewriteImpl()

// Deep β-collapse η-collapse rewrite.
var DeepBetaEta = DeepRewrite(betaRewrite, etaRewrite)

// η-reduces a λ where the normal form is η-short: as an argument (of
// anything but ∀ / ∃ / ∃! / ε / =) or as the body of a λ. The
// normalizer's η; see etaContextRewriteImpl for why the context decides.
// Shallow rewrite.
var etaContextRewrite = etaContextRewriteImpl()

// Rewrites εx.(x = t) to t (if x is not free in t).
// Rewrites εP to εx.P(x).
// Shallow rewrite.
var hilbertRewrite = hilbertRewriteImpl()

// Rewrite P(εx.P(x)) to ∃x.P(x).
// Deep rewrite.
var HilbertExistsRewrite = hilbertExistsRewriteImpl()

// Rewrites using boolean thms.
// Shallow rewrite.
var BoolRewrite = boolRewriteImpl()

// Deep bool rewrite.
var DeepBoolRewrite = DeepRewrite(BoolRewrite)

// Cancels ¬¬.
// Shallow rewrite.
var DoubleNegRewrite = doubleNegRewriteImpl()

// (p ⊕ q) → (¬p ⇔ q)
// ¬(p ⇔ ¬q) → (p ⇔ q)
// ¬(p ∧ q) → (¬p ∨ ¬q)
// ¬(p ∨ q) → (¬p ∧ ¬q)
// ¬(p ⇒ q) → (p ∧ ¬q)
// ¬(∃x.P(x)) → ∀x.¬P(x)
// ¬(∀x.P(x)) → ∃x.¬P(x)
// Shallow rewrite.
var PushNegRewrite = pushNegRewriteImpl()

// Deep push neg / double neg rewrite.
var DeepNegRewrite = DeepRewrite(PushNegRewrite, DoubleNegRewrite)

// Cond(_, x, x) → x
// Cond(⊤, x, y) → x
// Cond(⊥, x, y) → y
// Shallow rewrite.
var trivialCondRewrite = trivialCondRewriteImpl()

// CondRewrite eliminates the first COND subterm whose case term is not captured by an
// enclosing binder. Two modes depending on the type of the term being rewritten:
//
//   - Bool:     P(Cond(c, x, y)) → (c ⇒ P(x)) ∧ (¬c ⇒ P(y))   [COND elim]
//   - Non-bool: P(Cond(c, x, y)) → Cond(c, P(x), P(y))        [COND swap]
//
// The bool case fully eliminates COND into standard propositional connectives;
// the non-bool case pushes COND outward through function applications.
// Both modes use BoolInduct on a fresh variable α₀ substituted for the case term
// to derive the rewrite, then restore the original case term.
//
// When the case term has free variables captured by an outer lambda (e.g.
// λx. ...Cond(f(x), a, b)...), the rewrite declines at this level and returns
// nil, deferring to DeepRewrite which will recurse inside the binder and retry
// at a level where the case term is free.
var CondElimRewrite = condElimRewriteImpl()
var CondSwapRewrite = condSwapRewriteImpl()

// CondDecideByHyps decides a COND whose guard the CONTEXT asserts:
//
//	Cond(c, x, y) → x    under the hypothesis c
//	Cond(c, x, y) → y    under the hypothesis ¬c
//	Cond(¬d, x, y) → y   under the hypothesis d
//
// anyHyp reports whether some hypothesis of the goal α-equals a term
// (Prop.AnyHyp). The equality CARRIES that hypothesis — `{c} ⊢
// Cond(c, x, y) = x` — so a driver composing it must discharge the
// hypothesis from the goal it rewrites, and must walk binders
// capture-aware (DeepRewriteWithEnv): the guard is compared to the
// hypothesis as a TERM, so a guard mentioning a bound variable that
// spells like a hypothesis's free variable is a different guard, and
// the env walk renames the binder before the equality is lifted
// through it. Shallow rewrite.
func CondDecideByHyps(anyHyp func(func(Term) bool) bool) Rewrite {
	return condDecideByHypsImpl(anyHyp)
}

// FormulaDecideByHyps decides a formula the CONTEXT asserts:
//
//	t → ⊤    under the hypothesis t
//	t → ⊥    under the hypothesis ¬t
//
// whatever t is — a membership, an opaque predicate, a propositional
// variable, a compound formula. anyHyp and the contract are
// CondDecideByHyps': the equality carries the deciding hypothesis, so a
// driver composing it discharges that hypothesis from the goal it
// rewrites and walks binders capture-aware (DeepRewriteWithEnv). A ¬d
// under the hypothesis d needs no clause of its own in a driver that
// carries the bool rewrites (BasicRewritesWithEnv): d reads ⊤ and ¬⊤
// folds. Shallow rewrite.
func FormulaDecideByHyps(anyHyp func(func(Term) bool) bool) Rewrite {
	return formulaDecideByHypsImpl(anyHyp)
}

// Rewrites ∀P, ∃P, ∃!P to ∀x.P(x), ∃x.P(x), ∃!x.P(x).
// Rewrites ∀P.P(...), ∀P.¬P(...), ∀x.(x ≠ s) to ⊥.
// Rewrites ∃P.P(...), ∃P.¬P(...), ∃x.(x = s) to ⊤.
// Shallow rewrite.
var QuantifierRewrite = quantifierRewriteImpl()

// Basic rewrites merged together, plus extra rewrites if any.
// This function is equivalent to
// DeepRewrite(basicRewrite, extraRewrites...)
// in terms of result, but DeepRewrite inside DeepRewrite is slower,
// so for efficiency we just flatten one level of DeepRewrite.
func BasicRewritesWith(extraRewrites ...Rewrite) Rewrite {
	return DeepRewrite(append([]Rewrite{
		betaRewrite,
		etaContextRewrite,
		hilbertRewrite,
		BoolRewrite,
		DoubleNegRewrite,
		PushNegRewrite,
		QuantifierRewrite,
		trivialCondRewrite},
		extraRewrites...)...)
}

// BasicRewritesWithEnv is BasicRewritesWith built on the capture-aware
// DeepRewriteWithEnv (see it for the env / anyHyp contract). Use when the extra
// leaves may return hyp-carrying equalities whose free vars could be captured by
// a binder in the term being rewritten — e.g. a hyp-conditioned arithmetic
// decision rewrite. anyHyp over-approximates those hyps (typically the goal's
// whole hyp set).
func BasicRewritesWithEnv(anyHyp func(func(Term) bool) bool, extraRewrites ...Rewrite) Rewrite {
	return DeepRewriteWithEnv(anyHyp, append([]Rewrite{
		betaRewrite,
		etaContextRewrite,
		hilbertRewrite,
		BoolRewrite,
		DoubleNegRewrite,
		PushNegRewrite,
		QuantifierRewrite,
		trivialCondRewrite},
		extraRewrites...)...)
}

// Basic rewrites merged together.
var BasicRewrite = BasicRewritesWith()

// Rewrites ∃! to ∀ and ∃.
// Shallow rewrite.
var UniqueRewrite = uniqueRewriteImpl()

// Rewrites ∃!x.P(x) to ∃x.(P(x) ∧ ∀y.(P(y) ⇒ y = x)): the form whose ∃ a
// witness instantiates, leaving P at the witness and that P holds of
// nothing else.
// Shallow rewrite.
var UniqueWitnessRewrite = uniqueWitnessRewriteImpl()

// (l ⇒ r) → (¬l ∨ r)
// Shallow rewrite.
var ImplyToOrRewrite = implyToOrRewriteImpl()

// (l ⇔ r) → ((l ∧ r) ∨ (¬l ∧ ¬r))
// Shallow rewrite.
var IffToOrRewrite = iffToOrRewriteImpl()

// Rewrites λx.l = λx.r to ∀x.(l = r), i.e. functional extensionality.
// If either side of the equality is not abs term, make it abs by eta extension,
// i.r. rewrite f = λx.r to λx.(f(x)) = λx.r, then rewrite it to ∀x.(f(x) = r).
// Shallow rewrite.
var FunEqRewrite = funEqRewriteImpl()

// Deep fun eq rewrite.
var DeepFunEqRewrite = DeepRewrite(FunEqRewrite)

// Rewrites using prenex thms for ∀, one ∧/∨ chain at a time: same-type
// ∀ over ∧ merge into one binder however the chain is associated (see
// quantifierPrenexRewriteImpl). This rewrite is not handling ¬, ⇔ and ⇒,
// so it should only be used after BasicRewrite, BooleanDisjunctiveRewrite
// so only ∧ and ∨ are left. Chain-level, not deep: it never enters a
// component, and it waits for a component's own binders to surface.
var UniversalPrenexRewrite = universalPrenexRewriteImpl()

// Deep univ prenex rewrite.
var DeepUniversalPrenexRewrite = DeepRewrite(UniversalPrenexRewrite)

// Rewrites using prenex thms for ∃, one ∧/∨ chain at a time: same-type
// ∃ over ∨ merge into one binder however the chain is associated (see
// quantifierPrenexRewriteImpl). This rewrite is not handling ¬, ⇔ and ⇒,
// so it should only be used after BasicRewrite, BooleanDisjunctiveRewrite
// so only ∧ and ∨ are left. Chain-level, not deep: it never enters a
// component, and it waits for a component's own binders to surface.
var ExistentialPrenexRewrite = existentialPrenexRewriteImpl()

// Deep existential prenex rewrite.
var DeepExistentialPrenexRewrite = DeepRewrite(ExistentialPrenexRewrite)

// E.g. (x0 ∧ ((x1 ∧ x2) ∧ x3)) → ((x0 ∧ x1) ∧ x2) ∧ x3
var AssocANDRewrite = AssocRewrite(
	AND, MatchesAND,
	TernaryThms["((p ∧ q) ∧ r) ⇔ (p ∧ (q ∧ r))"])

// E.g. (x0 ∨ ((x1 ∨ x2) ∨ x3)) → ((x0 ∨ x1) ∨ x2) ∨ x3
var AssocORRewrite = AssocRewrite(
	OR, MatchesOR,
	TernaryThms["((p ∨ q) ∨ r) ⇔ (p ∨ (q ∨ r))"])

// p ⇒ (q ∧ ... ∧ r) → (p ⇒ q) ∧ ... ∧ (p ⇒ r): an implication whose
// consequent is a conjunction is the conjunction of the implications —
// a Horn clause pack (`monoidal_op(op) ⇒ eq₁ ∧ eq₂`) read as one clause
// per conjunct. Shallow rewrite.
var ImplyANDRewrite = DistributeRewrite(
	AND, MatchesIMPLY, MatchesAND,
	TernaryThms["(p ⇒ (q ∧ r)) ⇔ ((p ⇒ q) ∧ (p ⇒ r))"])

// p ∨ (q ∧ ... ∧ r) → (p ∨ q) ∧ ... ∧ (p ∨ r)
// Shallow rewrite.
var DistributeListORAND = DistributeRewrite(
	AND, MatchesOR, MatchesAND,
	TernaryThms["(p ∨ (q ∧ r)) ⇔ ((p ∨ q) ∧ (p ∨ r))"])

// p ∧ (q ∨ ... ∨ r) → (p ∧ q) ∨ ... ∨ (p ∧ r)
// Shallow rewrite.
var DistributeListANDOR = DistributeRewrite(
	OR, MatchesAND, MatchesOR,
	TernaryThms["(p ∧ (q ∨ r)) ⇔ ((p ∧ q) ∨ (p ∧ r))"])

// Given a chain term with a binary op,
// e.g. (x0 . ((x1 . x2) . x3)), and indices i < j,
// moves xj right next to xi.
// If nothing to move, return Refl, not nil.
// This is a different behavior from most other rewrites.
// Shallow rewrite.
var ArrangeANDChain = ArrangeChain(
	AND, MatchesAND,
	CommuteAND,
	TernaryThms["((p ∧ q) ∧ r) ⇔ (p ∧ (q ∧ r))"])
var ArrangeORChain = ArrangeChain(
	OR, MatchesOR,
	CommuteOR,
	TernaryThms["((p ∨ q) ∨ r) ⇔ (p ∨ (q ∨ r))"])
var ArrangeIFFChain = ArrangeChain(
	core.IFF(), MatchesIFF,
	CommuteEQ,
	TernaryThms["((p ⇔ q) ⇔ r) ⇔ (p ⇔ (q ⇔ r))"])

// Cancels redundant terms inside an AND chain
// e.g. p ∧ (... ∧ p ∧ ...) → p ∧ ..., p ∧ (... ∧ ¬p ∧ ...) → ⊥
// Rewrite on the top level, but works for the whole series.
var MergeANDRewrite = binaryOpMergeRewrite(
	MatchesAND, DecomposesAND, ArrangeANDChain)

// Cancels redundant terms inside an OR chain
// e.g. p ∨ (... ∨ p ∨ ...) → p ∨ ..., p ∨ (... ∨ ¬p ∨ ...) → ⊤
// Rewrite on the top level, but works for the whole series.
var MergeORRewrite = binaryOpMergeRewrite(
	MatchesOR, DecomposesOR, ArrangeORChain)

// p ∧ (p ∨ ...) → p, p ∧ (¬p ∨ ...) → p ∧ ...
var distributeSimplifyANDOR = distributeSimplifyRewrite(
	MatchesAND, MatchesOR, DecomposesOR, ArrangeORChain,
	BinaryThms["p ∧ (p ∨ q) ⇔ p"],
	TernaryThms["(p ∧ (q ∨ r)) ⇔ ((p ∧ q) ∨ (p ∧ r))"])

// p ∨ (p ∧ ...) → p, p ∨ (¬p ∧ ...) → p ∨ ...
var distributeSimplifyORAND = distributeSimplifyRewrite(
	MatchesOR, MatchesAND, DecomposesAND, ArrangeANDChain,
	BinaryThms["p ∨ (p ∧ q) ⇔ p"],
	TernaryThms["(p ∨ (q ∧ r)) ⇔ ((p ∨ q) ∧ (p ∨ r))"])

// Simplifies conjunct of disjuncts
// Only works for the top level. Should not be called recursively.
var simplifyANDORRewrite = crossBinaryOpSimplifyRewrite(
	AND, OR, MatchesAND, MatchesOR, DecomposesAND, DecomposesOR,
	ArrangeANDChain, ArrangeORChain, MergeANDRewrite, MergeORRewrite,
	DistributeListANDOR, distributeSimplifyANDOR, CommuteAND)

// Simplifies disjunct of conjuncts
// Only works for the top level. Should not be called recursively.
var simplifyORANDRewrite = crossBinaryOpSimplifyRewrite(
	OR, AND, MatchesOR, MatchesAND, DecomposesOR, DecomposesAND,
	ArrangeORChain, ArrangeANDChain, MergeORRewrite, MergeANDRewrite,
	DistributeListORAND, distributeSimplifyORAND, CommuteOR)

// p ∨ (... ∨ p) → p ∨ ...
// p ∨ (... ∨ ¬p ∨ ...) → ⊤
// p ∨ (... ∧ p ∧ ...) → p
// p ∨ (... ∧ ¬p ∧ ...) → p ∨ ...
// Only works for the top level. Should not be called recursively.
var SimplifyDisjunct = ChainRewrites(
	MergeORRewrite,
	simplifyORANDRewrite,
)

// p ∧ (... ∧ p) → p ∧ ...
// p ∧ (... ∧ ¬p ∧ ...) → ⊥
// p ∧ (... ∨ p ∨ ...) → p
// p ∧ (... ∨ ¬p ∨ ...) → p ∧ ...
// Only works for the top level. Should not be called recursively.
var SimplifyConjunct = ChainRewrites(
	MergeANDRewrite,
	simplifyANDORRewrite,
)

// Disjunct components sorting rewrites
// Only works for the top level. Should not be called recursively.
var DisjunctSortRewrite = BinaryOpSortRewrite(
	MatchesOR, DecomposesOR, ArrangeORChain, SimplifyDisjunct, AssocORRewrite)

// Conjunct components sorting rewrites
// Only works for the top level. Should not be called recursively.
var ConjunctSortRewrite = BinaryOpSortRewrite(
	MatchesAND, DecomposesAND, ArrangeANDChain, SimplifyConjunct, AssocANDRewrite)

// Rewrites using skolem.
// Shallow rewrite.
var SkolemRewrite = skolemRewriteImpl()

// ∀x.(l ∧ r) → (∀x.l ∧ ∀x.r).
// This rewrite contradicts Prenex rewrite.
// Shallow rewrite.
var ForAllANDRewrite = forAllANDRewriteImpl()

// ∃x.(l ∨ r) → (∃x.l ∨ ∀x.r).
// This rewrite contradicts Prenex rewrite.
// Shallow rewrite.
var ExistsORRewrite = existsORRewriteImpl()

// ∀x.∀y.(l(x) ∨ r(y)) → (∀x.l(x) ∨ ∀y.r(y)).
// This rewrite contradicts Prenex rewrite.
// Rewrite only regarding the outmost universal quantifiers
// (but there can be multiple of them).
var ForAllORRewrite = forAllORRewriteImpl()

// ∃x.∃y.(l(x) ∧ r(y)) → (∃x.l(x) ∧ ∃y.r(y)).
// This rewrite contradicts Prenex rewrite.
// Rewrite only regarding the outmost existential quantifiers
// (but there can be multiple of them).
var ExistsANDRewrite = existsANDRewriteImpl()

// Given an abs term λx.P(x) and pair x ↦ y, returns a thm λx.P(x) = λy.P(y)
// Useful to control the bound vars in thms.
var BoundVarRewrite = boundVarRewriteImpl
