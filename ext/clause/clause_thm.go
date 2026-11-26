/**
 * File: clause_thm.go
 *
 * Implements theorem representation and operations using disjunctive clauses.
 *
 * Key structure:
 * - ClauseThm: Represents a theorem in clause form
 *   Fields:
 *   - Thm: Embedded Thm structure for core theorem properties
 *   - conclusion: The conclusion clause
 *   - hypClauses: Clauses representing hypotheses
 *
 * Main functions:
 * - makeClauseThm(t Thm, conclClause *Clause, hypClauses ...*Clause): Creates a ClauseThm
 * - (t *ClauseThm).IsRefuted(): Checks if theorem has contradiction as conclusion
 * - (t *ClauseThm).ConclClause(): Returns conclusion clause
 * - (t *ClauseThm).HypClauseIter(): Iterates over hypothesis clauses
 * - (t *ClauseThm).DeriveHypFrom(s *ClauseThm): Applies one theorem to derive a hypothesis
 * - (t *ClauseThm).AlignHyps(f func(*Clause) *Clause): Transforms hypothesis clauses
 * - findHypClause(t *ClauseThm, hyp Term): Finds clause matching a given hypothesis term
 * - weakenTo(clauseThm *ClauseThm, concl *Clause): Converts refutation to conclusion
 * - conclMatch(clauseThm *ClauseThm, concl *Clause): Adjusts theorem for equivalent conclusions
 *
 * Auxiliary functions:
 * - compareClauseBodies(c0, c1 *Clause): Compares clauses by body terms
 */

package clause

import (
	"iter"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

// A thm whose hyps and conclusion are all disjuctive clauses.
type ClauseThm struct {
	Thm

	conclusion *Clause
	// The order of hyp clauses is identical to the order of hyp terms.
	hypClauses []*Clause

	// Optional provenance: how this clause thm was found by an expensive
	// (unification-based) inference during proof search. Set by the producers
	// in deduce.go and carried through to serialization so replay can reproduce
	// the inference without re-searching. nil for clause thms that were not
	// produced by a recorded inference (e.g. cheap contradiction/simplification
	// steps, or any thm derived by transforming another).
	recipe *deduceRecipe
}

func compareClauseBodies(c0, c1 *Clause) int { return c0.Term().Compare(c1.Term()) }

// Make a clause thm from its thm form.
// The clauses of the conclusion and hyps are also given as inputs
// This is because in practice these clauses are usually already built somewhere.
// It would be not efficient to build them again from the terms.
// The order of input hyp clauses can be different from the hyp terms, but
// they should be same after sorting, otherwise it panics.
// It assumes that the hyps and conclusion are all disjuctive clauses.
// Otherwise it panics.
func MakeClauseThm(t Thm, conclClause *Clause, hypClauses ...*Clause) *ClauseThm {
	slices.SortFunc(hypClauses, compareClauseBodies)
	hyps := utils.MapSlice(hypClauses, (*Clause).Term)
	Assert(len(hypClauses) == t.NumHyps())
	for i := range hypClauses {
		Assert(hyps[i].AlphaEquals(t.Hyp(i)))
	}
	Assert(conclClause.Term().AlphaEquals(t.Conclusion()))
	return &ClauseThm{Thm: t, conclusion: conclClause, hypClauses: hypClauses}
}

// withRecipe attaches inference provenance to a freshly produced clause thm and
// returns it (for fluent use at the producer site). The recipe is metadata only
// — it never affects the theorem itself, just how replay reconstructs it.
func (t *ClauseThm) withRecipe(r *deduceRecipe) *ClauseThm {
	t.recipe = r
	return t
}

// External method. Should only be used in tests.
func TestClauseThm(t Thm, conclClause *Clause, hypClauses ...*Clause) *ClauseThm {
	return MakeClauseThm(t, conclClause, hypClauses...)
}

func (t *ClauseThm) IsRefuted() bool { return t.conclusion.Term().Equals(F) }

// FunextSources is the clauses a FUNEXT derivation contracted (funext.go):
// the pointwise clause of a unit equality, the two clauses of an iff
// pair. Nil for every other clause thm.
func (t *ClauseThm) FunextSources() []*Clause {
	if t.recipe == nil || t.recipe.rule != _RuleFunext {
		return nil
	}
	return t.recipe.inputs
}

func (t *ClauseThm) ConclClause() *Clause { return t.conclusion }

func (t *ClauseThm) HypClauseIter() iter.Seq[*Clause] { return slices.Values(t.hypClauses) }

func (t *ClauseThm) HypClause(i int) *Clause { return t.hypClauses[i] }

func (t *ClauseThm) AllHypClause(f utils.Predicate[*Clause]) bool {
	return utils.All(t.hypClauses, f)
}

func (t *ClauseThm) HasHypClause(c *Clause) bool {
	return utils.Any(t.hypClauses, c.Equivalent)
}

func (t *ClauseThm) DeriveHypFrom(s *ClauseThm) *ClauseThm {
	var hyp *Clause
	for h := range t.HypClauseIter() {
		if h.Equivalent(s.ConclClause()) {
			hyp = h
			break
		}
	}
	Assert(hyp != nil)
	stepThm := WrapProp(s.AsThmCert())
	// It is possible that the conclusion of the thm in step
	// is just equivalent to h, but not α-equal.
	// Needs an equality to bridge.
	if !hyp.Term().AlphaEquals(stepThm.Conclusion()) {
		bridgeThm := clauseEquivalentEq(stepThm.Conclusion(), hyp.Term())
		Assert(bridgeThm != nil)
		stepThm = bridgeThm.EqMP(stepThm)
	}
	stepThm = stepThm.DeriveTrans(t.AsThmCert())

	// Find the clauses with regarding to the hyps of stepThm
	// from hyps of t and s so we don't need to make clauses for them.
	allHypClauses := utils.ConcatIter(t.HypClauseIter(), s.HypClauseIter())
	stepThmHypClauses := make([]*Clause, 0, stepThm.NumHyps())
	for h := range stepThm.HypIter() {
		for c := range allHypClauses {
			if c.Term().AlphaEquals(h) {
				stepThmHypClauses = append(stepThmHypClauses, c)
				break
			}
		}
	}
	Assert(len(stepThmHypClauses) == stepThm.NumHyps())

	return MakeClauseThm(
		stepThm.AsThmCert(),
		t.ConclClause(),
		stepThmHypClauses...)
}

// Given a callback that transform a clause to another with the same key
// adjust the hyps of the thm so that the hyps are transformed by the callback.
func (t *ClauseThm) AlignHyps(f func(*Clause) *Clause) *ClauseThm {
	clauseThm := t
	for hypClause := range t.HypClauseIter() {
		bridgedHypClause := f(hypClause)
		Assert(bridgedHypClause != nil)
		if hypClause.Term().AlphaEquals(bridgedHypClause.Term()) {
			continue
		}
		bridgeThm := clauseEquivalentEq(bridgedHypClause.Term(), hypClause.Term())
		Assert(bridgeThm != nil)
		bridgeThm = bridgeThm.
			EqMP(core.Assume(bridgedHypClause.Term())).
			DeriveTrans(clauseThm.AsThmCert())

		hypClauses := make([]*Clause, 0, bridgeThm.NumHyps())
		for h := range bridgeThm.HypIter() {
			if h.AlphaEquals(bridgedHypClause.Term()) {
				hypClauses = append(hypClauses, bridgedHypClause)
			} else {
				c := findHypClause(clauseThm, h)
				Assert(c != nil)
				hypClauses = append(hypClauses, c)
			}
		}

		clauseThm = MakeClauseThm(
			bridgeThm.AsThmCert(),
			clauseThm.ConclClause(), hypClauses...)
	}
	return clauseThm
}

// AddHyps weakens the theorem by adding extra hypothesis clauses.
func (t *ClauseThm) AddHyps(extra ...*Clause) *ClauseThm {
	hyps, hypClauses := t.Hyps(), utils.Clone(t.hypClauses)
	for _, c := range extra {
		if utils.None(hypClauses, c.Equivalent) {
			hyps = append(hyps, c.Term())
			hypClauses = append(hypClauses, c)
		}
	}
	weakened := prop.WeakenTo(
		t.AsThmCert(),
		core.MakeProp(t.Conclusion(), hyps...))
	Assert(weakened != nil)
	return MakeClauseThm(weakened.AsThmCert(), t.ConclClause(), hypClauses...)
}

func findHypClause(t *ClauseThm, hyp Term) *Clause {
	// notice that the hyp clauses are sorted by their bodies with Term.Compare.
	if i, found := slices.BinarySearchFunc(
		t.hypClauses, hyp, func(c *Clause, hyp Term) int {
			return c.Term().Compare(hyp)
		}); found {
		return t.hypClauses[i]
	}
	return nil
}

// If the clause thm is refuted, weaken it to a given conclusion.
func weakenTo(clauseThm *ClauseThm, concl *Clause) *ClauseThm {
	Assert(clauseThm.IsRefuted())
	if concl.Term().Equals(F) {
		return clauseThm
	}
	// Carry provenance through the weakening so a reconstructed refutation stays
	// self-describing (see conclMatch / the migration in proto.go).
	return MakeClauseThm(
		core.DeriveTrans(clauseThm.Thm, prop.FalseDerives(concl.Term())).AsThmCert(),
		concl, clauseThm.hypClauses...).withRecipe(clauseThm.recipe)
}

// If the conclusion of a given clause thm has the same key as a given clause
// returns a thm that makes them exactly match.
func conclMatch(clauseThm *ClauseThm, concl *Clause) *ClauseThm {
	matched := conclMatchImpl(clauseThm, concl)
	if matched != nil {
		// Carry the inference provenance through the conclusion adjustment so the
		// reconstructed thm stays self-describing. This lets a fallback (search)
		// reconstruction expose the rediscovered recipe on its result — the basis
		// for the offline recipe-less → recipe certificate migration.
		matched.recipe = clauseThm.recipe
	}
	return matched
}

func conclMatchImpl(clauseThm *ClauseThm, concl *Clause) *ClauseThm {
	if clauseThm.IsRefuted() {
		return weakenTo(clauseThm, concl)
	}
	if concl.Equivalent(clauseThm.ConclClause()) {
		if concl.Term().AlphaEquals(clauseThm.Conclusion()) {
			return clauseThm
		}
		return MakeClauseThm(
			clauseEquivalentEq(clauseThm.Conclusion(), concl.Term()).
				EqMP(clauseThm.Thm).AsThmCert(),
			concl, clauseThm.hypClauses...)
	}
	return nil
}
