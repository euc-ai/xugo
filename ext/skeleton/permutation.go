// permutation.go implements the ordered-rewriting classifier — the
// third term encoding in this package, alongside the structural skeleton
// (skeleton.go: positional discrimination, wildcarded variables) and
// the whistle embedding (embed.go: containment). Where those two ask
// "could this shape match?" and "is structure being re-contained?",
// this one asks the opposite-invariance question: "are these two terms
// the SAME material, merely rearranged?" — exact, position-independent,
// name-carrying.
//
// Consumer: the fire whistle's ordered-permutation blade
// (ext/prop.fireWhistle) gates permutation-class rewrite fires to the
// strictly Compare-decreasing direction — the ordered-rewriting
// discipline at fire granularity. See PermutationFireAllowed.

package skeleton

import (
	"context"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// PermutationFireAllowed is the ordered-rewriting blade of the fire
// whistle: a fire whose two sides are PERMUTATION-CLASS — their
// βη-normal forms are α-equal as UNORDERED trees (sibling arguments
// rearranged under unchanged heads: COMM-class instances, including
// η-lifted pointwise variants whose raw RHS carries a λ-wrap) — is
// allowed only in the strictly Compare-DECREASING direction. This is
// the ordered-rewriting discipline for permutative rewrites,
// applied at fire granularity so it covers every leaf kind (unification
// rewrites, structural EqRewrite, mined ground instances) without
// rule-level detection. ASSOC-class fires are NOT gated — see
// unorderedAlphaEqual for the classifier boundary.
//
// Termination is exact, not heuristic: within a fixed symbol multiset
// the same-size term space is finite and a strictly decreasing chain in
// the total structural order cannot revisit a form, so a permutative
// storm terminates at its order-normal (locally sorted) form instead of
// churning the AC form space (~8!·Catalan(7) forms for 8 atoms, the
// shape of a cardinality-of-a-union proof, which slips every other blade: permuted RHSs are
// same-size, don't consistently grow, and pairwise never path-embed,
// stretching the trajectory antichain indefinitely).
// Unlike a fire-count cap, the gate suppresses exactly the churning
// direction — the allowed fires still make sorting progress, and the
// result is the canonical form rather than an arbitrary truncation.
//
// A fire whose sides are βη-EQUAL — β-reduction, η-contraction, or an
// η-expansion at a head whose normal form is the expanded λ — moves no
// material and is not a permutation: this blade passes it. It is NOT
// admitted only as a raw shrink, because a βη-class's normal form is
// not its smallest member: under ∀/∃/∃!/ε and at a function-typed = the
// engine's normal form is η-LONG (etaContextRewrite excludes exactly
// those heads so that QuantifierRewrite, hilbertRewrite and
// FunEqRewrite can expand there), and a shrink-only clause silently
// declined FunEqRewrite's η-alignment `F = λx.b` → `λx.F(x) = λx.b` and
// QuantifierRewrite's `∀P` → `∀x.P(x)`, so a whistled composition
// carrying either leaf lost the expansion without trace. No fire-local
// rule can do better: which η-direction is progress is a property of
// the CONTEXT, which the fire pair does not carry (the contracting fire
// sits at the λ, the expanding one at its parent), so η-termination is
// the composition's business — the normalizer's leaves partition the
// heads between them. A composition that contradicts itself, an
// η-contracting lemma under a head an engine leaf expands, 2-cycles;
// the trajectory blade cuts that exactly as it cuts left-commutativity.
//
// Everything here is a pure function of the two terms (BetaEtaNormalize,
// symbol counts, structural Compare — α-invariant on bound variables via
// the binder-pairing env), hence deterministic and replay-stable.
func PermutationFireAllowed(lhs, rhs core.Term) bool {
	// Cheap pre-filter: any permutation-class fire — even an η-lifted
	// one, whose raw RHS adds a λ-wrap and bound occurrences — keeps the
	// multiset of RIGID leaves (consts and free vars) unchanged. Fires
	// that create or consume rigid material are not this blade's
	// business; the β-normalization below is only paid past this test.
	if !sameSymbolMultiset(lhs, rhs, true) {
		return true
	}
	ctx := context.Background()
	ln := ext.BetaEtaNormalize(ctx, lhs)
	rn := ext.BetaEtaNormalize(ctx, rhs)
	if ln.AlphaEquals(rn) {
		// βη-administrative fire: not a permutation (see above).
		return true
	}
	if ln.Size() != rn.Size() || !sameSymbolMultiset(ln, rn, false) ||
		!unorderedAlphaEqual(ln, rn, nil) {
		return true
	}
	// A permutation-class fire at a FUNCTION-TYPED site (a partial
	// application / η level) has no sound orientation: BetaEtaNormalize
	// η-EXPANDS, and a bound λ-var is Compare-MINIMAL, so the "λ-var
	// first" flip is unconditionally "decreasing" at this level while
	// the enclosing applied level orders the concrete arguments — the
	// two verdicts contradict on every already-sorted application, and
	// blessing both directions (each at its own level) is the COMM
	// storm of int_add_th. Decline; the applied-level fire is the
	// sound decision point. An ordering decline, not a whistle cut —
	// same contract as the decreasing test below.
	if ext.IsFunType(lhs.Type()) {
		return false
	}
	// Permutation-class fire: ordered rewriting, decreasing only.
	return rn.Compare(ln) < 0
}

// unorderedAlphaEqual reports whether a and b are α-equal AS UNORDERED
// TREES: at every application spine the heads must match and the
// arguments match as a MULTISET (recursively). This is the instance-
// level projection of the simplifier literature's "permutative rule"
// test (lhs and rhs are variants — Isabelle's mk_perm
// eligibility): a COMM-class fire only swaps sibling
// arguments under an unchanged head, so its two sides are unordered-
// equal, while an ASSOC-class fire ROTATES the tree — its sides are
// unordered-DISTINCT, and the rule stays free to fire in its written
// direction (either orientation of assoc terminates on its own: the
// one-sided nesting measure is monotone; and gating assoc breaks
// list_append — its associativity is stated toward LEFT nesting,
// which is Compare-increasing). Left-commutativity
// (x∘(y∘z) = y∘(x∘z)) is also unordered-distinct and thus NOT gated;
// its 2-cycles are short and the trajectory blade cuts them — if an
// ac_simps-style LC lemma ever storms in practice, the precise fix is
// rule-level variants detection at the rewrite constructors.
//
// Bound-variable labels compare positionally (the same binder-pairing
// env as CompareWithEnv), so the test is α-invariant; the ordered
// CompareWithEnv == 0 shortcut resolves all untouched subtrees cheaply.
// Greedy multiset matching is complete here because unordered α-equality
// is an equivalence relation — any match choice is exchangeable.
func unorderedAlphaEqual(a, b core.Term, env []core.VarPair) bool {
	if a.CompareWithEnv(b, env) == 0 {
		return true
	}
	if aAbs, ok := a.AsAbsTerm(); ok {
		bAbs, ok := b.AsAbsTerm()
		if !ok || !aAbs.Var().Type().Equals(bAbs.Var().Type()) {
			return false
		}
		return unorderedAlphaEqual(
			aAbs.Body(), bAbs.Body(),
			append(env, core.VarPair{V0: aAbs.Var(), V1: bAbs.Var()}))
	}
	headA, argsA := ext.MatchesApply(a)
	headB, argsB := ext.MatchesApply(b)
	if len(argsA) == 0 || len(argsA) != len(argsB) ||
		!unorderedAlphaEqual(headA, headB, env) {
		return false
	}
	used := make([]bool, len(argsB))
	for _, x := range argsA {
		matched := false
		for j, y := range argsB {
			if !used[j] && unorderedAlphaEqual(x, y, env) {
				used[j], matched = true, true
				break
			}
		}
		if !matched {
			return false
		}
	}
	return true
}

// sameSymbolMultiset reports whether a and b carry the same multiset of
// node symbols. leavesOnly counts just the rigid leaves — consts and
// free vars — which β/η administration preserves (the pre-filter view);
// the full view additionally counts λ-binders and bound-variable
// occurrences as anonymous markers (binder names are α-noise — η-lifts
// mint fresh ones). Contrast the sibling encoders: ExtractPaths
// wildcards free-variable NAMES (bucketing wants shape classes) and
// EmbPaths collapses duplicates (containment wants sets) — this
// classifier needs both names and multiplicity, exactly.
func sameSymbolMultiset(a, b core.Term, leavesOnly bool) bool {
	counts := map[string]int{}
	bound := map[core.TermName]int{}
	addSymbolCounts(a, leavesOnly, bound, counts, 1)
	addSymbolCounts(b, leavesOnly, bound, counts, -1)
	for _, c := range counts {
		if c != 0 {
			return false
		}
	}
	return true
}

// PermutativeRulePattern is the RULE-LEVEL permutativity test — the
// simplifier literature's variants check (Isabelle's permutative-rule
// eligibility): given the two sides of a
// rewrite rule's equality (typically λ-abstractions over the rule's
// ∀-vars, as shaped by contextAbsEq or UnifyEqRewrite's callers), it
// reports whether the RHS is the LHS under a BIJECTIVE renaming of the
// λ-peeled pattern variables.
//
//	COMM      u(x,y)   = u(y,x)     yes  (x↦y, y↦x)
//	left-comm x∘(y∘z)  = y∘(x∘z)    yes  (x↦y, y↦x, z↦z)
//	ASSOC   (x∘y)∘z    = x∘(y∘z)    no   (tree shape differs)
//	x - y = x + (-y) no (material differs)
//
// This is strictly finer than the fire whistle's instance-level
// classifier (PermutationFireAllowed): left-comm instances are
// unordered-DISTINCT trees, invisible at fire granularity, but at the
// pattern level LC is a plain variable renaming. A constructor that
// certifies a rule permutative should gate every instance with
// OrderedInstanceDecreasing — the pair implements rule-level ordered
// rewriting, terminating for the same fixed-material strictly-
// decreasing-chain reason as the fire-level gate.
//
// The walk is a single deterministic pass: variants have IDENTICAL tree
// structure (only variable names permute), so the first occurrence of
// each pattern var pins the bijection and later occurrences check
// consistency. Inner binders pair positionally (α-invariant) and shadow
// pattern vars of the same name.
func PermutativeRulePattern(l, r core.Term) bool {
	if l.Size() != r.Size() {
		return false
	}
	lVars, lBody := ext.MatchesAbs(l)
	rVars, rBody := ext.MatchesAbs(r)
	if len(lVars) == 0 || len(lVars) != len(rVars) {
		// No pattern vars (a ground equation cannot be a non-trivial
		// variant of itself), or λ-arity mismatch.
		return false
	}
	flex := map[core.TermName]bool{}
	for _, v := range lVars {
		flex[v.Name()] = true
	}
	for _, v := range rVars {
		flex[v.Name()] = true
	}
	fwd := map[core.TermName]core.TermName{}
	bwd := map[core.TermName]core.TermName{}
	return variantBodies(lBody, rBody, flex, fwd, bwd, nil, nil)
}

// RearrangementRulePattern is the material-preserving extension of
// PermutativeRulePattern for the rule-level ordered channels: it
// reports whether the rule's two sides (λ-abstractions over the rule's
// ∀-vars, as shaped by contextAbsEq) abstract the SAME variables and
// their bodies carry EXACTLY the same symbol material — same multiset
// of consts, pattern-var occurrences (by name), inner λ-binders and
// bound occurrences — merely rearranged. PermutativeRulePattern
// catches COMM/left-comm (variants: identical tree, renamed vars);
// this test additionally catches ASSOC-class rotations, whose sides
// are structurally DIFFERENT trees over the same material:
//
//	ASSOC   m+(n+p) = (m+n)+p    yes  (rotation, material fixed)
//	x - y = x + (-y) no (material differs)
//	x+(x+y) = y+(y+x)            no   (per-name counts differ)
//
// Why the fixpoint ordered channels need it: a simp set carrying an
// AC triple {COMM, left-comm, ASSOC} terminates only if EVERY
// material-preserving fire strictly decreases ONE common order
// (Martin–Nipkow ordered rewriting). Gating only the variants leaves
// ASSOC free to fire in its written direction; Normalize's
// orientation states ASSOC toward LEFT nesting, which
// is Compare-INCREASING under the engine's leftmost-first structural
// order, so each ungated ASSOC rotation re-opens exactly the
// positions the ordered COMM/LC fires just sorted — a 4-fire cycle
// around the AC class (the int_add_th SimpWith storm, second layer).
// An instance of a same-material rule keeps the fired term's symbol
// multiset fixed, so the strictly-decreasing-chain termination
// argument of the fire blade (PermutationFireAllowed) applies
// verbatim: within a fixed symbol multiset the same-size term space
// is finite and a strictly Compare-decreasing chain cannot revisit a
// form. One-shot explicit rewrite channels are NOT gated by this test
// (ordered mode is caller-scoped — see unifyEqRewriteImpl); an
// agent-directed ASSOC cite keeps its written orientation.
func RearrangementRulePattern(l, r core.Term) bool {
	if l.Size() != r.Size() {
		return false
	}
	lVars, lBody := ext.MatchesAbs(l)
	rVars, rBody := ext.MatchesAbs(r)
	if len(lVars) == 0 || len(lVars) != len(rVars) {
		return false
	}
	// contextAbsEq abstracts both sides over the SAME ∀-vars; require
	// that so the by-name material comparison below is meaningful.
	for i := range lVars {
		if lVars[i].Name() != rVars[i].Name() ||
			!lVars[i].Type().Equals(rVars[i].Type()) {
			return false
		}
	}
	return sameSymbolMultiset(lBody, rBody, false)
}

// OrderedInstanceDecreasing reports whether a rule instance firing
// lhs → rhs is strictly decreasing in the total structural order,
// comparing βη-normal forms (rule instances carry η-lift λ-wraps and
// β-redex residue). Deterministic — safe for recorded-step replay.
func OrderedInstanceDecreasing(lhs, rhs core.Term) bool {
	ctx := context.Background()
	return ext.BetaEtaNormalize(ctx, rhs).Compare(ext.BetaEtaNormalize(ctx, lhs)) < 0
}

// variantBodies walks a and b in lockstep requiring identical structure,
// with pattern vars (flex) pairing bijectively via fwd/bwd, inner-bound
// vars pairing positionally via envA/envB (shadowing flex names), and
// everything else matching exactly.
func variantBodies(a, b core.Term, flex map[core.TermName]bool,
	fwd, bwd map[core.TermName]core.TermName,
	envA, envB []core.TermName) bool {
	if aa, ok := a.AsAppliedTerm(); ok {
		bb, ok := b.AsAppliedTerm()
		return ok &&
			variantBodies(aa.Fun(), bb.Fun(), flex, fwd, bwd, envA, envB) &&
			variantBodies(aa.Arg(), bb.Arg(), flex, fwd, bwd, envA, envB)
	}
	if aa, ok := a.AsAbsTerm(); ok {
		bb, ok := b.AsAbsTerm()
		if !ok || !aa.Var().Type().Equals(bb.Var().Type()) {
			return false
		}
		return variantBodies(aa.Body(), bb.Body(), flex, fwd, bwd,
			append(envA, aa.Var().Name()), append(envB, bb.Var().Name()))
	}
	if av, ok := a.AsVar(); ok {
		bv, ok := b.AsVar()
		if !ok || !av.Type().Equals(bv.Type()) {
			return false
		}
		ia, ib := lastNameIndex(envA, av.Name()), lastNameIndex(envB, bv.Name())
		if ia >= 0 || ib >= 0 {
			// Inner-bound occurrence: positional α-pairing.
			return ia == ib
		}
		if flex[av.Name()] || flex[bv.Name()] {
			if !flex[av.Name()] || !flex[bv.Name()] {
				return false
			}
			if n, ok := fwd[av.Name()]; ok && n != bv.Name() {
				return false
			}
			if n, ok := bwd[bv.Name()]; ok && n != av.Name() {
				return false
			}
			fwd[av.Name()], bwd[bv.Name()] = bv.Name(), av.Name()
			return true
		}
		return av.Name() == bv.Name()
	}
	if ac, ok := a.AsConst(); ok {
		bc, ok := b.AsConst()
		return ok && ac.Name() == bc.Name() && ac.Type().Equals(bc.Type())
	}
	return false
}

func lastNameIndex(env []core.TermName, n core.TermName) int {
	for i := len(env) - 1; i >= 0; i-- {
		if env[i] == n {
			return i
		}
	}
	return -1
}

func addSymbolCounts(
	t core.Term, leavesOnly bool,
	bound map[core.TermName]int, counts map[string]int, delta int) {
	switch t := t.Core().(type) {
	case core.AppliedTerm:
		addSymbolCounts(t.Fun(), leavesOnly, bound, counts, delta)
		addSymbolCounts(t.Arg(), leavesOnly, bound, counts, delta)
	case core.AbsTerm:
		if !leavesOnly {
			counts["λ"] += delta
		}
		n := t.Var().Name()
		bound[n]++
		addSymbolCounts(t.Body(), leavesOnly, bound, counts, delta)
		bound[n]--
	case core.VarTerm:
		if bound[t.Name()] > 0 {
			if !leavesOnly {
				counts["•"] += delta
			}
		} else {
			counts["v\x00"+string(t.Name())] += delta
		}
	case core.ConstTerm:
		counts["c\x00"+string(t.Name())] += delta
	}
}
