package unify

// MatchFilter is a conservative pre-filter for βη-unification-based
// rewrite-rule matching (prop.unifyEq): built once per rule from the
// rule's LHS, it answers CouldMatch(t) per candidate target with the
// one-sided guarantee
//
//	CouldMatch(t) == false  ⟹  the rule cannot fire on t
//
// i.e. no substitution of the rule's flexible (peeled-binder) vars makes
// the LHS βη-equal to t — at any peel level, and invariantly under
// unifyEqRewrite's λ-env wrapping of t (wrapping only adds leading
// binders, which spineHead skips). False positives are expected and
// harmless: the unifier stays the decision procedure; the filter only
// skips unify calls that are guaranteed to yield nothing.
//
// The zero-false-negative contract is load-bearing. The filter runs
// inside recorded tactics (lean_rw / def_expand / the BasicTactics
// fixpoint), so a missed match would change SubGoals shapes and diverge
// replay of the stored corpus. prop.TestCouldMatchNeverBlocksUnifyEq
// pins the contract differentially against unifyEq itself.
//
// Mechanism: compare rigid spine heads. A rule LHS whose fully λ-stripped
// application spine is headed by a Const c keeps that head under any
// flexible-var substitution (substitution never touches a const) and
// under βη-normalization (no redex can form at a const head; η-conversion
// changes only the λ/arity envelope). A target keeps its own head the
// same way, and the substitution does not reach it: unifyEq renames the
// peeled binders away from the target's names and holds every name of
// the target rigid. So a target headed by a Const c' ≠ c cannot match,
// and neither can one headed by a var, free or bound. That second case
// is the common one: a resident ∀x.P(x) reads as the rule
// λx.P(x) = λx.⊤, whose LHS has a set's type, so every bare set variable
// of a goal is a candidate. Two cases decline to filter. A rule headed by
// a var: that head may be a peeled binder (flexible, it can absorb
// anything) or a free var (eqSimplify renames rule vars against the goal,
// so its identity is unstable across the match). A target headed by a λ:
// an unreduced β-redex whose eventual head this walk does not compute.
// The heads are compared as constants at their type instance: unifyEq
// unifies terms and instantiates no type (unify.UnifyTerms), so the
// unifier's rigid-rigid step takes two heads of one name for one head
// only at one type, and a rule whose LHS is an equation at a record's
// type cannot fire on an equation at any other. A rule of that shape —
// an injectivity or extensionality law read left to right — otherwise
// meets every equation of the goal, and each meeting costs the βη-normal
// form of the rule's whole pattern before the unifier compares the heads.
type MatchFilter struct {
	head      TermName
	headType  HolType
	filtering bool
}

// MatchFilterFor analyzes a rewrite rule's LHS. Rules without a rigid
// const spine head yield a non-filtering filter (CouldMatch ≡ true).
func MatchFilterFor(lhs Term) MatchFilter {
	if c, ok := spineHead(lhs).AsConst(); ok {
		return MatchFilter{head: c.Name(), headType: c.Type(), filtering: true}
	}
	return MatchFilter{}
}

// Filtering reports whether this filter can exclude anything at all.
func (f MatchFilter) Filtering() bool { return f.filtering }

// CouldMatch reports whether the rule could possibly rewrite t. See the
// type comment for the one-sided guarantee.
func (f MatchFilter) CouldMatch(t Term) bool {
	if !f.filtering {
		return true
	}
	head := spineHead(t)
	if c, ok := head.AsConst(); ok {
		return c.Name() == f.head && c.Type().Equals(f.headType)
	}
	_, unreduced := head.AsAbsTerm()
	return unreduced
}

// SpineHeadConst returns the name of t's rigid spine-head constant:
// strip the leading λ-binders, flatten the application spine, and
// report the head iff it is a ConstTerm. ok=false for var heads and
// for λ heads (an unreduced β-redex, whose eventual head this does not
// compute). Where it does claim a const, the claim is βη-stable: β
// cannot rewrite a const-headed spine's head, and η-conversion
// (t ↔ λx.t(x)) changes only the λ/arity envelope this walk skips — so
// the reported head equals the head of t's βη-normal form.
func SpineHeadConst(t Term) (TermName, bool) {
	if c, ok := spineHead(t).AsConst(); ok {
		return c.Name(), true
	}
	return "", false
}

// spineHead is what stands at the head of t once its leading λ-binders
// are stripped and its application spine flattened: a const, a var, or a
// λ when t is an unreduced β-redex.
func spineHead(t Term) Term {
	for {
		if abs, ok := t.AsAbsTerm(); ok {
			t = abs.Body()
			continue
		}
		break
	}
	for {
		if app, ok := t.AsAppliedTerm(); ok {
			t = app.Fun()
			continue
		}
		break
	}
	return t
}
