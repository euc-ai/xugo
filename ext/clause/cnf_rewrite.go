/**
 * File: cnf_rewrite.go
 *
 * Implements transformation algorithms for converting terms to Conjunctive Normal Form (CNF).
 *
 * CNF preprocessing is structured as three explicit stages:
 *
 *   1. prelude  — overlaps with prop.Normalize / PreCNFNormalizeRewrite. NNF,
 *                 ⇒-elim, prenex (without Skolem), β/η, sort. Reusable across
 *                 statement identity and CNF preprocessing.
 *   2. middle   — refuter-only Skolemization, after an independent ∃ block
 *                 has risen above the ∀ block the prelude put over it
 *                 (prop.IndependentExistsPrenexRewrite). Changes a prop's
 *                 identity (introduces fresh Skolem symbols) so cannot be
 *                 part of the statement identity.
 *   3. tail     — recursive denoting + distribute ∨ over ∧ (the part that
 *                 may time out) + per-clause normalization.
 *
 * Main functions:
 * - cnfRewrite: Core recursive CNF conversion algorithm (tail's distribution).
 *   Handles quantifiers, AND/OR structures, and distributes OR over AND.
 *   Returns a PropWrapper representing ⊢ t = <term in CNF>.
 * - cnfRewriteWithTimeout: Wrapper adding timeout protection to CNF conversion.
 *   Focuses on standardizing the structure after basic CNF conversion is complete.
 * - insideDenoteRewrite: Extracts nested quantifiers using denotational rewrites.
 * - clauseWiseNormalizationRewrite: Normalizes individual clauses in a CNF term.
 * - cnfNormalizeWorkFlow: full prelude + middle + tail pipeline (raw input).
 * - cnfNormalizeWorkFlowFromPreNormalized: middle + tail only, for input that
 *   has already passed prop.Normalize / PreCNFNormalize-equivalent prelude.
 */

package clause

import (
	"context"
	"errors"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

var errCNF = errors.New("fail to convert to cnf")

// Not a conversion failure: the (negated) goal is `{} ⊢ ⊥`, whose CNF is the
// empty conjunction — a legal but unrefutable input, so the refuter declines.
var errNothingToRefute = errors.New("goal has no hypotheses; negated-goal CNF is empty")

// Rewrite a term to its conjunctive normal form.
// It's recursive in itself.
// The function attempts to transform a logical term into CNF by repeatedly
// applying appropriate rewrite rules, with context for timeout handling.
func cnfRewrite(ctx context.Context, t Term) (w *PropWrapper, err error) {
	defer func() {
		if w != nil && err == nil {
			Assert(t.Equals(Lhs(w)) && !t.AlphaEquals(Rhs(w)) && w.NumHyps() == 0)
		}
	}()

	// Handle existential and universal quantifiers by pushing the rewrite operation inside
	existsVars, existsBody := DecomposesEXISTS(t)
	univVars, univBody := DecomposesFORALL(existsBody)

	if !existsVars.Empty() || !univVars.Empty() {
		if u, err := cnfRewrite(ctx, univBody); u != nil && err == nil {
			return prop.EqReplacementRewrite(u)(t), nil
		} else if err != nil {
			return nil, err
		}
	}

	if _, ok := univBody.AsAppliedTerm(); !ok {
		return nil, nil
	}

	if ctx.Err() != nil {
		return w, errCNF
	}

	// simplify OR-related redundancy before the dispatch.
	w = prop.RewriteOrRefl(prop.SimplifyDisjunct, univBody)

	// simplify AND-related redundancy before the dispatch.
	w = w.RewriteConclRhs(prop.SimplifyConjunct)

	if isCNF(Rhs(w)) {
		if !univBody.AlphaEquals(Rhs(w)) {
			return w, nil
		}
		return nil, nil
	}

	// Rewrite every AND-decomposed terms respectively.
	if _, _, ok := MatchesAND(Rhs(w)); ok {
		// Check size threshold to avoid excessive computation
		if decomposeANDlen(Rhs(w)) > _CNF_SIZE_THRES ||
			ctx.Err() != nil {
			return nil, errCNF
		}

		ctx, cancel := context.WithCancel(ctx)
		defer cancel()

		w = w.RewriteConclRhs(prop.AssocANDRewrite)

		terms := DecomposesAND(Rhs(w))

		// Process each conjunct in parallel
		thms := make([]*PropWrapper, len(terms))
		fail := make(chan struct{}, 1)
		wg := utils.Tasks{}
		for i := range terms {
			wg.Go(func() {
				var e error
				thms[i], e = cnfRewrite(ctx, terms[i])
				if e != nil {
					utils.TrySend(fail, struct{}{})
					cancel()
				}
			})
		}
		wg.Wait()
		if len(fail) > 0 {
			return nil, errCNF
		}
		u := thms[0]
		if u == nil {
			u = prop.Refl(terms[0])
		}

		// Combine the results back into a conjunction
		for i, thm := range thms[1:] {
			if thm != nil {
				u = u.LeftApply(AND).Apply(thm)
			} else {
				u = u.LeftApply(AND).RightApply(terms[i+1])
			}
		}
		w = w.EqTrans(u)

		// simplify AND-related redundancy after the dispatch.
		// It would be too slow to do this for large term, so
		// we have a size threshold here.
		if decomposeANDlen(Rhs(w)) > _CNF_SIZE_THRES || ctx.Err() != nil {
			return nil, errCNF
		}

		w = w.RewriteConclRhs(prop.SimplifyConjunct)

		if !univBody.AlphaEquals(Rhs(w)) {
			return w, nil
		}
		return nil, nil
	}
	// The real conjunctive rewrite.
	if l, r, ok := MatchesOR(Rhs(w)); ok {
		// Check size thresholds before attempting distributive laws
		if decomposeANDlen(l) > _CNF_SIZE_THRES ||
			decomposeANDlen(r) > _CNF_SIZE_THRES ||
			ctx.Err() != nil {
			return nil, errCNF
		}
		ctx, cancel := context.WithCancel(ctx)
		defer cancel()

		// (ll ∧ lr) ∨ r = (r ∨ ll) ∧ (r ∨ lr)
		// Apply distributive law: OR over AND on the left side
		if _, _, ok := MatchesAND(l); ok {
			w = w.EqTrans(prop.CommuteOR(l, r))
			w = w.EqTrans(prop.DistributeListORAND(Rhs(w)))

			if u, err := cnfRewrite(ctx, Rhs(w)); err != nil {
				return nil, err
			} else if u != nil {
				return w.EqTrans(u), nil
			}
			return w, nil
		}
		// l ∨ (rl ∧ rr) = (l ∨ rl) ∧ (l ∨ rr)
		// Apply distributive law: OR over AND on the right side
		if _, _, ok := MatchesAND(r); ok {
			w = w.EqTrans(prop.DistributeListORAND(Rhs(w)))
			if u, err := cnfRewrite(ctx, Rhs(w)); err != nil {
				return nil, err
			} else if u != nil {
				return w.EqTrans(u), nil
			}
			return w, nil
		}

		// Process both sides of OR in parallel
		var resultL *PropWrapper
		fail := make(chan struct{}, 1)
		left := utils.Tasks{}
		left.Go(func() {
			u, err := cnfRewrite(ctx, l)
			if err != nil {
				utils.TrySend(fail, struct{}{})
			}
			resultL = u
		})
		resultR, errR := cnfRewrite(ctx, r)
		left.Wait()
		if errR != nil || len(fail) > 0 {
			cancel()
			return nil, errCNF
		}

		// Combine the results of both sides
		if resultL != nil && resultR != nil {
			w = w.EqTrans(resultL.LeftApply(ext.OR).Apply(resultR))
		} else if resultR != nil {
			w = w.EqTrans(resultR.LeftApply(ext.Apply(ext.OR, l)))
		} else if resultL != nil {
			w = w.EqTrans(resultL.LeftApply(ext.OR).RightApply(r))
		}

		if !univBody.AlphaEquals(Rhs(w)) {
			if decomposeANDlen(Rhs(w)) > _CNF_SIZE_THRES {
				return nil, errCNF
			}

			// Recursively apply CNF rewrite to the result
			if u, err := cnfRewrite(ctx, Rhs(w)); err != nil {
				return nil, err
			} else if u != nil {
				return w.EqTrans(u), nil
			}
			return w, nil
		}
	}

	if !univBody.AlphaEquals(Rhs(w)) {
		return w, nil
	}
	return nil, nil
}

// Wrapper for cnfRewrite that adds a timeout context
// This prevents CNF conversion from taking excessive time on complex formulas.
//
// parentCtx is used as the base for the WithTimeout wrap so an agent-supplied
// deadline (probe / apply budget_ms) shortens this cap when it is tighter
// than _CNF_REWRITE_TIMEOUT. Pass context.Background() at non-agent call
// sites; the behaviour matches the pre-ctx wrapper.
func cnfRewriteWithTimeout(parentCtx context.Context, t Term) (*PropWrapper, error) {
	ctx, cancel := context.WithTimeout(parentCtx, _CNF_REWRITE_TIMEOUT)
	defer cancel()

	return cnfRewrite(ctx, t)
}

// Normalizes each disjunctive clause in the cnf.
// This performs clause-specific normalizations after the basic CNF structure is established.
func clauseWiseNormalizationRewrite(t Term) (w *PropWrapper) {
	defer func() {
		if w != nil {
			Assert(t.Equals(Lhs(w)) && w.NumHyps() == 0)
		}
	}()
	_, body := DecomposesEXISTS(t)

	clauses := DecomposesAND(body)

	// we use universalPrenexRewrite after normalization because
	// we want each clause to have universal quantifiers in the outmost level.
	normalizations := utils.MapSlice(
		clauses,
		func(c Term) *PropWrapper {
			if u := normalizeClause(c); u != nil {
				return u.RewriteConclRhs(prop.DeepUniversalPrenexRewrite)
			}
			return nil
		})

	// Combine the normalized clauses back into a conjunction
	normalization := normalizations[0]
	if normalization == nil {
		normalization = prop.Refl(clauses[0])
	}
	for i, u := range normalizations[1:] {
		if u != nil {
			normalization = normalization.LeftApply(AND).Apply(u)
		} else {
			normalization = normalization.LeftApply(AND).RightApply(clauses[i+1])
		}
	}
	normalization = prop.RewriteOrRefl(prop.AssocANDRewrite, body).
		EqTrans(normalization).
		RewriteConclRhs(prop.MergeANDRewrite)
	return prop.EqReplacementRewrite(normalization)(t)
}

// Uses denote rewrite to take out quantifiers inside a term,
// e.g. ∃y.P(∀x.Q(x), y) = ∃α.(α = ∀x.Q(x) ∧ ∃y.P(α, y))
// If there are multiple terms with quantifiers inside, this rewrite will only take the first
// one at a time.
// It should only be done after prenex rewrites so Existential quantifiers and
// universal quantifiers are taken out as much as possible.
//
// The unifications that fold the instances of the denoted term end with
// ctx (prop.ExistsDenoteRewriteUnder), each under its own work budget as
// without one: on a term whose folds run those budgets out, the caller's
// deadline is what ends the stage. A result produced past the end of ctx
// is not a normal form — cnfNormalizeWorkFlowTail reads ctx before it.
func insideDenoteRewrite(ctx context.Context) prop.Rewrite {
	return func(t Term) (w *PropWrapper) {
		defer func() {
			if w != nil {
				Assert(t.AlphaEquals(Lhs(w)) && !t.AlphaEquals(Rhs(w)) && w.NumHyps() == 0)
			}
		}()
		if s := ext.InsideQuantifierBoolOp(t); s != nil {
			return prop.ExistsDenoteRewriteUnder(ctx, s)(t)
		}
		return nil
	}
}

// Deals with nested quantifiers by extracting them using denote rewrite.
// One round of cnfNormalizeWorkFlowTail's denoting stage, for the
// non-prenexable nested quantifiers that survive the initial prelude+middle
// stages: it denotes one such quantifier, then re-runs the prelude+middle to
// renormalize the result.
func rewriteWorkflow(ctx context.Context) prop.Rewrite {
	return prop.ChainRewrites(
		insideDenoteRewrite(ctx),
		prop.NormalizeRewriteWorkflow,
	)
}

// denoteRounds is the denoting stage: it runs round on w's right-hand
// side until round leaves it alone, and returns nil once ctx is done. A
// round takes out one nested quantifier or connective and renormalizes
// what is left; the number of rounds is the number of such terms the
// renormalizations leave, which the input's size does not bound, so ctx
// is read before each round, the stage's unit of work. It is read after
// the last as well: a round whose unifications ctx ended answers "nothing
// left" of a term it did not finish reading.
func denoteRounds(ctx context.Context, w *PropWrapper, round prop.Rewrite) *PropWrapper {
	for {
		if err := ctx.Err(); err != nil {
			return nil
		}
		u := round(Rhs(w))
		if u == nil {
			break
		}
		w = w.EqTrans(u)
	}
	if err := ctx.Err(); err != nil {
		return nil
	}
	return w
}

// Final stage of rewrite workflow.
// Performs final normalization and cleanup of the CNF structure (per-clause).
var finalRewriteWorkflow = prop.ChainRewrites(
	prop.BasicRewritesWith(prop.ForAllANDRewrite),
	clauseWiseNormalizationRewrite,
	prop.BasicRewritesWith(prop.AssocANDRewrite, prop.AssocORRewrite),
)

// cnfNormalizeWorkFlow is the main entry point for CNF normalization on a raw
// input term. Runs the full prelude → middle → tail pipeline:
//
//   - prelude+middle: prop.NormalizeRewriteWorkflow (TrivialNormalize +
//     SkolemRewriteWorkflow + DeepUniversalPrenexRewrite). TrivialNormalize
//     overlaps with prop.Normalize; SkolemRewriteWorkflow is refuter-only.
//   - tail: recursive denoting + cnfRewrite + finalRewriteWorkflow.
//
// Not ctx-aware on the raw entry — only the FromPreNormalized variant is
// reachable from the agent's budgeted auto / probe path. Internal callers
// (NegateGoalCNF, makeConclDisjunct) use Background ctx via the tail.
func cnfNormalizeWorkFlow(t Term) *PropWrapper {
	w := prop.Refl(t)
	w = w.RewriteConclRhs(prop.NormalizeRewriteWorkflow)
	return cnfNormalizeWorkFlowTail(context.Background(), w)
}

// cnfNormalizeWorkFlowFromPreNormalized runs the refuter-only stages from an
// input that has already passed prop.PreCNFNormalizeRewrite (or equivalent).
//
// PreCNF intentionally preserves a few shapes that are useful to rewrite
// tactics but must still be eliminated before CNF refutation. If one of those
// gap shapes is present, we run TrivialNormalize; otherwise the input has
// already received the identity-layer prelude rewrites. SkolemRewriteWorkflow
// still includes ExistentialPrenexRewrite because TrivialNormalize and
// Skolemization can expose fresh existential-prenex opportunities after the
// prelude has finished.
//
// ctx is checked between stages (Trivial → Skolem → DeepUniversal → tail) and
// returns nil on cancellation. Each individual stage rewrite is a tree-walk
// combinator that is not interrupted mid-traversal; the assumption is that a
// single stage finishes well within a budget tick. Pre-iter-#24 pathological
// goals (ε-Skolemized list_member/PAIRWISE) could spend tens of seconds in this
// function with no budget cap — that's what this ctx threading fixes.
func cnfNormalizeWorkFlowFromPreNormalized(ctx context.Context, t Term) *PropWrapper {
	if err := ctx.Err(); err != nil {
		return nil
	}
	w := prop.Refl(t)
	if hasPreCNFGapShape(t) {
		w = w.RewriteConclRhs(prop.TrivialNormalize)
		if err := ctx.Err(); err != nil {
			return nil
		}
	}
	// Middle (refuter-only): independent ∃ above ∀, Skolem, ExistentialPrenex.
	w = w.RewriteConclRhs(prop.SkolemRewriteWorkflow)
	if err := ctx.Err(); err != nil {
		return nil
	}
	// Re-prenex universals exposed by Trivial/Skolem.
	w = w.RewriteConclRhs(prop.DeepUniversalPrenexRewrite)
	return cnfNormalizeWorkFlowTail(ctx, w)
}

// hasPreCNFGapShape returns true if a pre-CNF term contains a shape that
// PreCNFNormalize deliberately preserves but CNF preprocessing still needs
// TrivialNormalize to eliminate.
//
// Implementation note: ext.SubTerms re-wraps abs bodies as the enclosing
// abstraction and filters self-equivalents, so it doesn't expose patterns
// like `λi. (num(i) ⇔ ...)` as a free-standing IFF subterm. We therefore
// walk the term ourselves with a plain recursive descent.
func hasPreCNFGapShape(t Term) bool {
	if isPreCNFGapNode(t) {
		return true
	}
	switch t := t.Core().(type) {
	case core.VarTerm, core.ConstTerm:
		return false
	case core.AppliedTerm:
		return hasPreCNFGapShape(t.Fun()) ||
			hasPreCNFGapShape(t.Arg())
	case core.AbsTerm:
		return hasPreCNFGapShape(t.Body())
	}
	panic("Wrong term type.")
}

// isPreCNFGapNode checks the pre-CNF gap patterns at a single node.
func isPreCNFGapNode(s Term) bool {
	if _, _, ok := ext.MatchesIFF(s); ok {
		return true
	}
	if !ext.MatchesUNIQUE(s).IsZero() {
		return true
	}
	if _, _, _, ok := ext.MatchesCond(s); ok {
		return true
	}
	if !core.MatchesHilbert(s).IsZero() {
		return true
	}
	if l, _, ok := ext.MatchesEQ(s); ok {
		if types := ext.MatchesFun(l.Type()); len(types) > 1 {
			return true
		}
	}
	return false
}

// cnfNormalizeWorkFlowTail runs the tail stage of CNF preprocessing:
// recursive denoting for nested non-prenexable quantifiers, the distribute
// step (with timeout), and per-clause normalization.
//
// ctx is checked at the major stage boundaries (entry, before each round
// of the denoting stage, after cnfRewrite), ends the denoting stage's
// unifications (rewriteWorkflow), and is threaded into
// cnfRewriteWithTimeout so the agent's budget shortens the distribute-step
// cap when it is tighter than the hard-coded _CNF_REWRITE_TIMEOUT. Returns
// nil on cancellation, which the caller (perHyp closure /
// cnfNormalizeWorkFlow) propagates as errCNF: a stage that ran into the
// end of ctx has produced nothing to keep.
func cnfNormalizeWorkFlowTail(ctx context.Context, w *PropWrapper) *PropWrapper {
	w = denoteRounds(ctx, w, rewriteWorkflow(ctx))
	if w == nil {
		return nil
	}
	// Apply the core CNF conversion with timeout protection.
	u, err := cnfRewriteWithTimeout(ctx, Rhs(w))
	if err != nil {
		return nil
	}
	if u != nil {
		w = w.EqTrans(u)
	}
	if err := ctx.Err(); err != nil {
		return nil
	}
	// Apply final per-clause normalization.
	return w.RewriteConclRhs(finalRewriteWorkflow)
}
