/**
 * File: flexible.go
 *
 * Handles unification of flexible terms (terms with instantiable variables as heads).
 * Implements strategies for:
 * - Flexible/flexible pairs: Multiple unification possibilities
 * - Flexible/rigid pairs: Imitation and projection strategies
 */

package unify

import (
	"context"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// unifies a flexible/flexible term pair.
// Because there may be multiple ways to unify a flexible/flexible pair,
// we return all options from the most trivial to the most general.
func unifyFlexiblePair(
	ctx context.Context,
	p _TermPair,
	ground TermNamePredicate,
	tooDeep func(TermSubstsGroup) bool,
	avoidNames TermNameSet) []TermSubstsGroup {

	// Decompose both terms to get their heads and arguments
	f0, args0, isRigid0 := decomposeHead(p.t0, &p.boundVars, ground)
	f1, args1, isRigid1 := decomposeHead(p.t1, &p.boundVars, ground)
	Assert(!isRigid0 && !isRigid1) // Both terms must be flexible

	env := _UnifyEnv{
		p.t0,
		p.t1,
		utils.EmptyPredicate[VarType],
		utils.Disjunct(ground, p.boundVars.HasName),
		tooDeep}

	// Extract types of the function heads
	fTypes0, fTypes1 := ext.MatchesFun(f0.Type()), ext.MatchesFun(f1.Type())
	if !f0.Type().Equals(f1.Type()) {
		Assert(utils.Last(fTypes0).Equals(utils.Last(fTypes1)))
	}

	var substsGroups []TermSubstsGroup

	// Case 1: Both terms are simple variables x ↔ y
	if len(fTypes0) == 1 && len(fTypes1) == 1 {
		substsGroups = []TermSubstsGroup{makeUnifyTermSubst(ctx, f0, f1)}

	} else if len(fTypes0) == 1 {
		// Case 2: First term is a variable, second is a compound term x ↔ f1(...)
		// If x doesn't occur in f1(...) and f1(...) doesn't contain bound variables
		// we can substitute x ↦ f1(...)
		if !p.t1.HasFree(f0.(VarTerm)) && p.t1.AllFree(p.boundVars.HasNo) {
			substsGroups = []TermSubstsGroup{makeUnifyTermSubst(ctx, f0, p.t1)}
		}
		// We can also substitute f1 ↦ λ... .x
		substsGroups = append(substsGroups,
			makeUnifyTermSubst(ctx, f1, mapToTarget(fTypes1, f0.(VarTerm))))

	} else if len(fTypes1) == 1 {
		// Case 3: Second term is a variable, first is a compound term f0(...) ↔ x
		// Switch the pair and use case 2
		return unifyFlexiblePair(
			ctx, makePair(ctx, p.t1, p.t0, &p.boundVars), ground, tooDeep, avoidNames)

	} else if f0.Type().Equals(f1.Type()) &&
		slices.EqualFunc(args0, args1, Term.AlphaEquals) {
		// Case 4: Both terms have same function type and identical arguments

		// If args are identical, we can assign f0 ↦ f1 or f1 ↦ f0
		// We choose f0 ↦ f1 arbitrarily
		Assert(!f0.Equals(f1) &&
			p.boundVars.HasNo(f0.(VarTerm)) &&
			p.boundVars.HasNo(f1.(VarTerm)))
		substsGroups = []TermSubstsGroup{makeUnifyTermSubst(ctx, f0, f1)}

	} else if len(fTypes0) < len(fTypes1) &&
		slices.EqualFunc(fTypes0, fTypes1[len(fTypes1)-len(fTypes0):], HolType.Equals) &&
		slices.EqualFunc(args0, args1[len(args1)-len(args0):], Term.AlphaEquals) {
		// Case 5: First term has fewer arguments and its types are a suffix of second term's types
		// E.g. f0(z, ...) vs. f1(x, y, z, ...) where both f0 and f1 are flexible,
		// and the arguments of f0 match the suffix of f1's arguments

		// Create the partial application f1(x, y) from the example above
		_f1 := Apply(f1, args1[:len(args1)-len(args0)]...)
		// Create appropriate type for the substitution
		_fTypes1 := utils.CloneAppend(fTypes1[:len(fTypes1)-len(fTypes0)], f0.Type())

		// We can substitute f1 ↦ λx...f0
		substsGroups = []TermSubstsGroup{
			makeUnifyTermSubst(ctx, f1, mapToTarget(_fTypes1, f0.(VarTerm)))}

		// We may also substitute f0 ↦ f1(x, y) if the necessary conditions are met
		if !_f1.HasFree(f0.(VarTerm)) && _f1.AllFree(p.boundVars.HasNo) {
			substsGroups = append(substsGroups, makeUnifyTermSubst(ctx, f0, _f1))
		}
	} else if len(fTypes0) > len(fTypes1) &&
		slices.EqualFunc(fTypes0[len(fTypes0)-len(fTypes1):], fTypes1, HolType.Equals) &&
		slices.EqualFunc(args0[len(args0)-len(args1):], args1, Term.AlphaEquals) {
		// Case 6: Second term has fewer arguments than first (mirror of case 5)
		// Switch the pair and use case 5
		return unifyFlexiblePair(
			ctx, makePair(ctx, p.t1, p.t0, &p.boundVars), ground, tooDeep, avoidNames)

	} else {
		// Case 7: General case - handle more complex unification patterns
		// The general cases, where we either map functions to const mappings
		// like f ↦ λx.y, or we try unification among args.

		if f0.Equals(f1) {
			// When head variables are the same, create a substitution to a fresh variable
			// f0 ↦ λ... x where x is a new var.
			target := Var(chooseName("x", avoidNames.Has), utils.Last(fTypes0))
			addNames(target, avoidNames)
			substsGroups = append(substsGroups,
				makeUnifyTermSubst(ctx, f0, mapToTarget(fTypes0, target)))
		} else {
			// Try f1 ↦ λ... t0 (constant function mapping everything to t0)
			if len(fTypes1) > 1 &&
				!p.t0.HasFree(f1.(VarTerm)) && p.t0.AllFree(p.boundVars.HasNo) {
				substsGroups = append(substsGroups,
					makeUnifyTermSubst(ctx, f1, mapToTarget(fTypes1, p.t0)))
			}

			// Try f0 ↦ λ... t1 (constant function mapping everything to t1)
			if len(fTypes0) > 1 &&
				!p.t1.HasFree(f0.(VarTerm)) && p.t1.AllFree(p.boundVars.HasNo) {
				substsGroups = append(substsGroups,
					makeUnifyTermSubst(ctx, f0, mapToTarget(fTypes0, p.t1)))
			}

			// Try mapping both function heads to a fresh variable
			Assert(utils.Last(fTypes0).Equals(utils.Last(fTypes1)) &&
				!slices.EqualFunc(args0, args1, Term.AlphaEquals))
			target := Var(chooseName("x", avoidNames.Has), utils.Last(fTypes0))
			addNames(target, avoidNames)
			substsGroups = append(substsGroups,
				append(
					makeUnifyTermSubst(ctx, f0, mapToTarget(fTypes0, target)),
					makeUnifyTermSubst(ctx, f1, mapToTarget(fTypes1, target))...))
		}

		// When the function types are equal, try unifying head-by-head and arg-by-arg
		if f0.Type().Equals(f1.Type()) {
			Assert(len(args0) == len(args1) &&
				!slices.EqualFunc(args0, args1, Term.AlphaEquals))

			// Try to unify {f0, x, ...} and {f1, y, ...} pairwise
			_pairs := make([]_TermPair, len(args0)+1)
			_pairs[0] = makePair(ctx, f0, f1, &p.boundVars)
			for i := range args0 {
				_pairs[i+1] = makePair(ctx, args0[i], args1[i], &p.boundVars)
			}
			clonePairs := utils.Clone(_pairs)
			for _, _substs := range env.tryUnify(
				ctx, _pairs, SubstsTuple{}, avoidNames) {
				termSubsts := cleanupSubsts(ctx, _substs.TermSubsts, clonePairs)
				substsGroups = append(substsGroups, termSubsts)
			}

			// Handle case where first term's type is a suffix of second term's type
		} else if len(fTypes0) < len(fTypes1) &&
			slices.EqualFunc(
				fTypes0, fTypes1[len(fTypes1)-len(fTypes0):],
				HolType.Equals) {
			// E.g. f0(w, ...) vs. f1(x, y, z, ...) where both f0 and f1 are flexible,
			// f0 and f1(x, y) have equal types, i.e. the types of the args of f0 are identical
			// to the types of the last several args of f1.
			Assert(len(args0) < len(args1) &&
				!slices.EqualFunc(
					args0, args1[len(args1)-len(args0):],
					Term.AlphaEquals))
			// the f1(x, y) part in the example above.
			_f1 := Apply(f1, args1[:len(args1)-len(args0)]...)
			// Try to unify {f0, w, ...} and {f1(x, y), z, ...}
			_pairs := make([]_TermPair, len(args0)+1)
			_pairs[0] = makePair(ctx, f0, _f1, &p.boundVars)
			for i := range args0 {
				_pairs[i+1] = makePair(
					ctx,
					args0[i], args1[len(args1)-len(args0)+i], &p.boundVars)
			}
			clonePairs := utils.Clone(_pairs)
			for _, _substs := range env.tryUnify(
				ctx, _pairs, SubstsTuple{}, avoidNames) {
				termSubsts := cleanupSubsts(ctx, _substs.TermSubsts, clonePairs)
				substsGroups = append(substsGroups, termSubsts)
			}

		} else if len(fTypes0) > len(fTypes1) &&
			slices.EqualFunc(
				fTypes1, fTypes0[len(fTypes0)-len(fTypes1):],
				HolType.Equals) {
			// Switch the pair, it's handled above.
			return unifyFlexiblePair(
				ctx,
				makePair(ctx, p.t1, p.t0, &p.boundVars), ground, tooDeep, avoidNames)
		}
	}
	Assert(len(substsGroups) > 0 &&
		utils.All(substsGroups, func(substs TermSubstsGroup) bool {
			return ext.BetaEtaEquals(
				ctx,
				p.t0.Substitute(substs...),
				p.t1.Substitute(substs...))
		}))
	return substsGroups
}

// unifies pairs where each one is a flexible/flexible pair.
func unifyAllFlexiblePairs(
	parentEnv _UnifyEnv,
	ctx context.Context,
	pairs []_TermPair,
	avoidNames TermNameSet) []TermSubstsGroup {
	Assert(len(pairs) > 0)

	p := pairs[0]
	pairs = pairs[1:]
	Assert(!p.t0.AlphaEquals(p.t1))
	substsOptions := unifyFlexiblePair(ctx, p, parentEnv.ground, parentEnv.tooDeep, avoidNames)

	// we don't need type substitution here.
	env := _UnifyEnv{
		parentEnv.origTerm0,
		parentEnv.origTerm1,
		utils.EmptyPredicate[VarType],
		parentEnv.ground,
		parentEnv.tooDeep}

	if ctx.Err() != nil {
		return nil
	}
	Assert(len(substsOptions) > 0)

	// flexibleBranch explores one substitution option: commit it to the
	// remaining pairs and recurse. QuitSentinel from a fired ctx is
	// swallowed so a cancelled branch does not discard sibling results.
	flexibleBranch := func(s TermSubstsGroup) (out []TermSubstsGroup) {
		defer func() {
			if utils.RecoverQuit(recover()) {
				out = nil
			}
		}()
		_pairs := utils.MapSlice(pairs, func(p _TermPair) _TermPair {
			return termSubstPair(ctx, p, s)
		})
		clonePairs := utils.Clone(_pairs)
		for _, _substs := range env.tryUnify(
			ctx, _pairs, SubstsTuple{}, avoidNames) {
			termSubsts := cleanupSubsts(ctx, _substs.TermSubsts, clonePairs)
			termSubsts, _ = insertOrderedTermSubsts(
				ctx, s.Clone(), termSubsts...)
			out = append(out, termSubsts)
		}
		return out
	}

	// The options are explored in order on this goroutine, under either
	// cut; see expandSearchTree for why.
	var results []TermSubstsGroup
	for _, s := range substsOptions {
		// Early pruning: skip substitutions that are already too deep
		if env.tooDeep(s) {
			continue
		}
		results = append(results, flexibleBranch(s)...)
	}
	return results
}

// containsUnaryOperatorCycle checks if unifying would create a cyclic pattern
// through repeated application of unary operators that leads to infinite loop
func containsUnaryOperatorCycle(t1 Term, flexVar Term, rigidOp Term) bool {
	// Detect risky imitation cases:
	// - Unary rigid head: block when the direct argument already exposes the
	//   flexible head (any args).
	// - Unary constant head: if the flexible head is base-typed and does not
	//   occur anywhere in t1, skip imitation to avoid helper-only chains.
	// - Nested constant head (depth ≥ 2) and flex absent in t1: also skip.

	// Check unary rigid head by type arity
	arity := len(ext.MatchesFun(rigidOp.Type())) - 1
	if arity != 1 {
		return false
	}
	// Ensure t1 is headed by rigidOp and get its first argument
	head, args := ext.MatchesApply(t1)
	if !head.Equals(rigidOp) || len(args) == 0 {
		return false
	}

	if v, ok := flexVar.AsVar(); ok {
		// Direct-argument check: arg contains subterm with head = F
		if termContainsHeadVarAnyArgs(args[0], v) {
			return true
		}

		// Nested constant check (depth ≥ 2) with flex absent in t1
		if _, ok := rigidOp.AsConst(); ok {
			cur := args[0]
			depth := 1
			for {
				h, a := ext.MatchesApply(cur)
				if !h.Equals(rigidOp) || len(a) == 0 {
					break
				}
				depth++
				cur = a[0]
			}
			if depth >= 2 && !t1.HasFree(v) {
				return true
			}
		}
	}

	return false
}

// termContainsHeadVarAnyArgs returns true if some subterm has head equal to v (ignore args).
func termContainsHeadVarAnyArgs(t Term, v VarTerm) bool {
	switch tt := t.Core().(type) {
	case VarTerm:
		return tt.EqualsVar(v)
	case ConstTerm:
		return false
	case AppliedTerm:
		h, _ := ext.MatchesApply(tt)
		if hv, ok := h.AsVar(); ok && hv.EqualsVar(v) {
			return true
		}
		return termContainsHeadVarAnyArgs(tt.Fun(), v) || termContainsHeadVarAnyArgs(tt.Arg(), v)
	case AbsTerm:
		return termContainsHeadVarAnyArgs(tt.Body(), v)
	default:
		panic("Wrong term type.")
	}
}

// creates substitutions for a flexible/rigid term pair using imitation and projection.
// Imitation: Creates a substitution that makes the flexible term imitate the structure of the rigid term
// Projection: Creates substitutions that project one of the arguments of the flexible term
// Returns all possible substitutions that could unify this pair
func matchFlexibleRigid(
	ctx context.Context,
	p *_TermPair,
	avoidNames TermNameSet,
	env _UnifyEnv,
	millerOnly bool) []SubstsTuple {

	f0, args0, isRigid0 := decomposeHead(p.t0, &p.boundVars, env.ground)
	f1, args1, isRigid1 := decomposeHead(p.t1, &p.boundVars, env.ground)
	Assert(!isRigid0 && isRigid1) // This must be a flexible/rigid pair

	// Miller-pattern fast path: when (t0, t1) is M(a1,...,an) ≐ t with
	// a1,...,an pairwise-distinct in-scope bound variables, M absent from
	// t, and every other in-scope bound variable absent from t, the
	// equation has a unique most-general unifier λa1...λan. t. Return it
	// directly without enumerating the Huet imitate/project branches —
	// this is the decidable, unitary subset of higher-order unification
	// (Miller 1991). Outside the pattern we fall through to the existing
	// Huet-style branches; we never relax the preconditions, because the
	// neighboring cases (repeated args, non-bound args) are genuinely
	// undecidable in general.
	var miller *SubstsTuple
	if miller = tryMillerPattern(ctx, f0, args0, p); miller != nil && millerOnly {
		return []SubstsTuple{*miller}
	}
	if miller == nil && len(args0) == 0 && baseFlexAgainstBoundVarUnsolvable(p, env) {
		return nil
	}

	avoidNames = avoidNames.Clone()
	addNames(p.t0, avoidNames)
	addNames(p.t1, avoidNames)
	zName := chooseName(utils.Z_STROKE, avoidNames.Has)
	avoidNames.Add(zName)
	hName := chooseName(utils.H_STROKE, avoidNames.Has)
	avoidNames.Add(hName)

	var substs []SubstsTuple
	if miller != nil {
		substs = append(substs, *miller)
	}
	f1Bound := false
	if f1, ok := f1.AsVar(); ok && p.boundVars.Has(f1) {
		f1Bound = true
	}

	substs = project(ctx, f0, f1, args0, zName, hName, env.allowedVarTypes, avoidNames)

	if !f1Bound {
		// Check if we're about to create a problematic imitation with a unary operator
		// This prevents infinite loops when the rigid head is a unary operator
		if containsUnaryOperatorCycle(p.t1, f0, f1) {
			// Skip imitation to prevent infinite loop
			return substs
		}

		im := imitate(ctx, f0, f1, args0, args1, zName, hName, avoidNames)
		substs = append(substs, SubstsTuple{nil, im})
	}
	return substs
}

// tryMillerPattern returns the Miller-pattern MGU for an equation
// M(a1,...,an) ≐ t when it lies in the *pattern fragment* of higher-order
// unification (Miller, "A logic programming language with lambda-abstraction,
// function variables, and simple unification", J. Logic and Computation 1(4),
// 1991; Nipkow, "Functional unification of higher-order patterns", LICS 1993).
// The fragment requires:
//
//   - the head M of the flexible side is a meta-variable (i.e. f0 is a
//     free, non-ground VarTerm — already guaranteed by the caller, since
//     matchFlexibleRigid is only entered with isRigid0=false);
//   - the args a1,...,an are pairwise-distinct variables, each currently
//     bound by the surrounding term context (`p.boundVars`), read modulo
//     η: the unifier works in η-long normal form, where a bound variable
//     of function type stands as its η-expansion `λys. x(ys)` — a rule
//     variable over sets of functions, `s : (B → A) → bool`, applies to
//     one — and the η-collapse of that expansion is the variable;
//   - M does not occur free in t (the standard occurs check); and
//   - every bound variable free in t lies in {a1,...,an}, so abstracting
//     them captures all in-scope occurrences (no leftover free bound-var
//     reference at the outer substitution site).
//
// Under those conditions the equation has a unique most-general unifier
// — the inverse abstraction λa1...λan. t — found in linear time with no
// branching and no fresh metavariables. This remains true when t mentions
// other free meta-variables: later substitutions for those variables compose
// through this witness via insertOrderedTermSubsts. Returning the pattern MGU
// here avoids falling through to Huet projection/imitation branches that may
// synthesize helper-dependent candidates outside the original binding scope.
//
// n = 0 — a bare base-typed meta-variable M ≐ t — is the fragment's base
// case and is handled here like every other n: the MGU is M ↦ t itself.
// This is the shape a FIRST-ORDER rewrite rule's variables take at the
// unifier (a rule variable against the subterm it stands for — the
// projection law `re(complex(a, b)) = a` against `re(complex(X, Y))`;
// a rule whose left side is a bare head applied to its binders fires on
// the head by η and never unifies), and it is exactly the shape Huet's
// imitation serves worst: imitation copies
// t one constructor per recursion level, minting a fresh variable per
// argument, and every level re-verifies, re-substitutes and re-normalizes
// every pending pair, so matching a variable against a term of N nodes
// costs Θ(N²) and more — 3.6 s for one variable against 513 nodes, and
// at 257 nodes the deterministic work budget runs out and the match
// silently FAILS. The imitation chain's final substitution is the same
// M ↦ t whenever it completes, so committing it here agrees with every
// result imitation completes, and succeeds where the budget would cut
// it.
//
// Outside the fragment we return nil and the caller falls through to the
// Huet-style projection/imitation branches. The preconditions are NOT
// relaxed here: repeated args (`M(x, x)`), non-variable args (`M(f(x), y)`
// — an argument that is no bound variable up to η), bound-variable
// leakage (`t` mentions a bound variable that isn't an arg) are genuinely
// undecidable / over-committing in general, and accepting them here would
// either lose unitariness or re-introduce the Huet branching cost that
// Miller's restriction exists to avoid.
func tryMillerPattern(
	ctx context.Context,
	f0 Term, args0 []Term, p *_TermPair) *SubstsTuple {
	fVar, ok := f0.AsVar()
	if !ok {
		return nil
	}

	// All args must be pairwise-distinct, in-scope bound variables, each
	// read through its η-collapse (`λys. x(ys)` is x). The distinctness
	// check uses VarTerm.Equals (name + type + deBruijn), the same notion
	// of identity boundVars.Has uses.
	boundArgs := make([]VarTerm, 0, len(args0))
	for _, a := range args0 {
		av, ok := ext.EtaCollapse(ctx, a).AsVar()
		if !ok {
			return nil
		}
		if !p.boundVars.Has(av) {
			return nil
		}
		for _, prev := range boundArgs {
			if av.Equals(prev) {
				return nil
			}
		}
		boundArgs = append(boundArgs, av)
	}

	// Occurs check: M must not be free in t. (makeUnifyTermSubst asserts
	// this internally; we check ourselves so we can return nil gracefully
	// for the non-Miller case rather than panicking the unifier.)
	if p.t1.HasFree(fVar) {
		return nil
	}

	// Capture-avoidance side-condition: every in-scope bound variable
	// occurring free in t must be one of the args. A leftover bound
	// reference would survive λ-abstraction and appear free at the outer
	// substitution site, where it is not in scope — that case is outside
	// the pattern.
	isArg := func(v VarTerm) bool {
		for _, av := range boundArgs {
			if av.Equals(v) {
				return true
			}
		}
		return false
	}
	for v := range p.boundVars.Iter() {
		if isArg(v) {
			continue
		}
		if p.t1.HasFree(v) {
			return nil
		}
	}

	// Build the unique MGU: M := λa1...λan. t. makeUnifyTermSubst then
	// runs β-η normalization on the witness, which may η-collapse e.g.
	// `λa1...λan. h(a1,...,an)` to `h` — semantically identical and
	// preferred by downstream code.
	witness := ext.ReverseAbsVars(p.t1, boundArgs...)
	return &SubstsTuple{
		TypeSubsts: nil,
		TermSubsts: makeUnifyTermSubst(ctx, fVar, witness),
	}
}

// baseFlexAgainstBoundVarUnsolvable reports that the pair M ≐ t — M a
// bare base-typed meta-variable, args0 = [] — has no unifier because t
// mentions a variable bound in the surrounding context and no
// meta-variable. A substitution instantiates M with a term closed with
// respect to the context's binders, and t's bound variable survives
// every substitution when nothing in t is instantiable, so the two
// sides can never agree. Huet's branches reach the same verdict only
// after imitating t down to the bound variable, one level per
// constructor, and failing there: the projection branch has no
// argument to project to, and a fresh helper is minted for each
// argument of each copied constructor and never for the context's
// binder, so no branch produces it. With a meta-variable in t the
// verdict does not hold — its instantiation may erase the bound
// variable (N(x) ≐ c under λx) — and the caller falls through.
func baseFlexAgainstBoundVarUnsolvable(p *_TermPair, env _UnifyEnv) bool {
	mentionsBound := false
	for v := range p.boundVars.Iter() {
		if p.t1.HasFree(v) {
			mentionsBound = true
			break
		}
	}
	if !mentionsBound {
		return false
	}
	return p.t1.AllFree(func(v VarTerm) bool {
		return p.boundVars.Has(v) || env.ground(v.Name())
	})
}

// imitate implements the imitation strategy for flexible/rigid pairs.
// For a flexible/rigid pair
// λx0.λx1....λxk.f(t0, t1, ..., tm)
// λx0.λx1....λxk.C(u0, u1, ..., un)
// returns substitution
// f ↦ λƶ0.λƶ1....λƶm.C(ħ0(ƶ0, ..., ƶm), ħ1(ƶ0, ..., ƶm), ... , ħn(ƶ0, ..., ƶm)).
// Imitation creates a substitution that mimics the structure of the rigid term.
// For example, if we need to unify F(x,y) with g(a,b), imitation creates
// F ↦ λx,y.g(H₁(x,y), H₂(x,y)) where H₁ and H₂ are fresh variables.
// This allows F to have the same top-level structure as the rigid term.
func imitate(
	ctx context.Context,
	f0, f1 Term, args0, args1 []Term,
	zName, hName TermName, avoidNames TermNameSet) TermSubstsGroup {
	zTypes := utils.MapSlice(args0, Term.Type)
	zVars := make([]Term, len(args0))
	for i, arg := range args0 {
		zVars[i] = core.Var(
			chooseName(utils.Subscript(zName, i), avoidNames.Has),
			arg.Type())
		addNames(zVars[i], avoidNames)
	}

	c := f1
	hs := make([]Term, len(args1))
	for i, arg := range args1 {
		if len(args0) == 0 {
			hs[i] = Var(
				chooseName(utils.Subscript(hName, i), avoidNames.Has),
				arg.Type())
		} else {
			types := utils.CloneAppend(zTypes, arg.Type())
			hs[i] = Apply(Var(
				chooseName(utils.Subscript(hName, i), avoidNames.Has),
				MakeFun(types[0], types[1], types[2:]...)), zVars...)
		}
		addNames(hs[i], avoidNames)
		c = Apply(c, hs[i])
	}
	c = ext.ReverseAbsVars(c, zVars...)
	return makeUnifyTermSubst(ctx, f0, c)
}

// project implements the projection strategy for flexible/rigid pairs.
// For a flexible/rigid pair
// λx0.λx1....λxk.f(t0, t1, ..., tm)
// λx0.λx1....λxk.C(u0, u1, ..., un)
// returns substitutions
// f ↦ λƶ0.λƶ1....λƶm.ƶi(ħ0(ƶ0, ..., ƶm), ħ1(ƶ0, ..., ƶm), ...)
// for each i such that the target type of ƶi (i.e. the eventual type it maps things to)
// equals the target type of C.
// The number of the args of ƶi is determined by the type of ƶi, which
// is determined by the type of f.
func project(
	ctx context.Context,
	f0, f1 Term, args0 []Term, zName, hName TermName,
	allowedVarTypes VarTypePredicate,
	avoidNames TermNameSet) []SubstsTuple {
	substs := make([]SubstsTuple, 0, len(args0))
	targetType := utils.Last(ext.MatchesFun(f1.Type()))
	zTypes := utils.MapSlice(args0, Term.Type)
	zVars := make([]Term, len(args0))
	for i, arg := range args0 {
		zVars[i] = core.Var(
			chooseName(utils.Subscript(zName, i), avoidNames.Has),
			arg.Type())
		addNames(zVars[i], avoidNames)
	}
	for i, arg := range args0 {
		argTypes := ext.MatchesFun(arg.Type())
		// projection works only when the target type of the arg matches the target type
		if typeSubsts, ok := unifyTypePair(
			utils.Last(argTypes), targetType, allowedVarTypes); ok {
			t := projectTerm(ctx, zVars, zTypes, argTypes, i, hName, avoidNames)
			substs = append(substs,
				SubstsTuple{
					typeSubsts,
					makeUnifyTermSubst(
						ctx,
						f0.TypeSubstitute(typeSubsts...),
						t.TypeSubstitute(typeSubsts...))})
		}
	}
	return substs
}

// creates a projection term for a specific argument index.
func projectTerm(
	ctx context.Context,
	zVars []Term, zTypes, argTypes []HolType, i int,
	hName TermName, avoidNames TermNameSet) Term {
	t := zVars[i]
	if len(argTypes) > 1 {
		hs := make([]Term, len(argTypes)-1)
		for j, zArgType := range utils.BeforeLast(argTypes) {
			types := utils.CloneAppend(zTypes, zArgType)
			hs[j] = Apply(Var(
				chooseName(utils.Subscript(hName, j), avoidNames.Has),
				MakeFun(types[0], types[1], types[2:]...)), zVars...)
			addNames(hs[j], avoidNames)
		}
		t = Apply(zVars[i], hs...)
	}
	t = ext.ReverseAbsVars(t, zVars...)
	return ext.BetaEtaNormalize(ctx, t)
}
