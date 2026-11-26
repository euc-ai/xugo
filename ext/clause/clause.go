/**
 * File: clause.go
 *
 * Implements disjunctive clause representation and manipulation for theorem proving.
 *
 * Key structures:
 * - Clause: Represents a disjunctive clause, such as ∀x.∀y.(P(x) ∨ Q(y) ∨ R(x, y))
 *   Fields:
 *   - originalTerm: The term that is used to create the clause.
 *   - leftAssocBody: Complete term with quantifiers in left-associated form
 *   - leftAssocLits: Inner body without quantifiers
 *   - literals: Individual terms in the disjunction
 *   - univBoundVars: Universally quantified variables
 *   - key: Identifier for clause. Clauses that are α-equal after normalization
 *     have the same key.
 *   - components: Independent components for divisible clauses, this is not the same as
 *     literals. For example, ∀x.∀y.(P(x) ∨ Q(x, y)) has only 1 component
 *     because it's not divisible, while ∀x.∀y.(P(x) ∨ Q(y)) has 2 components:
 *     ∀x.P(x) and ∀y.Q(y) because ∀x.∀y.(P(x) ∨ Q(y)) = ∀x.P(x) ∨ ∀y.Q(y) after normalization.
 *   - normalizationThm: Theorem relating body to components, for example,
 *     ⊢ ∀x.∀y.(P(x) ∨ Q(y)) = ∀x.P(x) ∨ ∀y.Q(y).
 *   - equivalentClause: The simplified clause that is equivalent to the original clause.
 *   - simplificationThm: The thm that connects the simplified clause to the original clause.
 *   - absEq: The abs equality of the clause if it has only 1 effective literal.
 *
 * - ClauseDivision: Division of clause for divide-and-conquer proof
 *   Fields:
 *   - DivisibleClause: Original clause being divided
 *   - DividedClauses: Resulting smaller clauses
 *   - Merge: Function to recombine subproofs that refute the divided clauses respectively
 *   - RefutingThm: Theorem that negating all components while assuming the disjunction
 *     leads to contradiction
 */

// Package clause is clausal form: the disjunctive clause, the
// conjunctive normal form of a statement, and the deduction rules
// between clauses that the refuter saturates with.
//
// NegateGoalCNF takes a goal to the clause set of its negation
// (cnf_rewrite.go, in three stages: the normalizing prelude,
// Skolemization, and the distribution of ∨ over ∧). A Clause
// (clause.go) and a CNFClauses (cnf.go) are the clause and the set; a
// ClauseThm (clause_thm.go) is a theorem in clause form. deduce.go
// holds the rules — a clause contradicting itself or another,
// factoring, one clause simplifying another, resolution — and each
// yields the clause it derives as a theorem.
package clause

import (
	"cmp"
	"slices"
	"strconv"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

type ClauseKey string

// A disjunctive clause looks like ∀x.∀y.(P(x) ∨ Q(y) ∨ R(x, y))
// It may have universal quantifiers and cannot have existential quantifiers.
// The inner body (inside the quantifiers) has to be
// either one term or a disjunction of terms without conjunctions.
type Clause struct {
	// the term that is used to create the clause.
	// not necessarily the same as leftAssocWithUniv, because
	// the original term might not be in the left associated form.
	originalTerm Term

	// the body with ∀ quantifiers in the left associated form.
	leftAssocWithUniv Term

	// the body without ∀ quantifiers in the left associated form.
	leftAssocLits Term

	// the disjuctive terms of the inner body.
	literals []Term

	// The ∀ bound vars from the most outside to the most inside.
	univBoundVars VarList

	// Key modulo equivalency, it is not same as the alpha key of the body.
	key ClauseKey

	// Sorted divisible components (not literals).
	// For example, ∀x.∀y.∀z.(P(x) ∨ P(y) ∨ Q(x, z)) has 3 literals,
	// but it has 2 divisible components: ∀x.∀z.(P(x) ∨ Q(x, z)) and ∀y.P(y).
	// Components are after being processed with basic rewrites.
	// For example, ∀x.∀y.(P(x) ∨ P(y)) has only 1 component ∀x.P(x)
	// because the other one is same and merged.
	// ∀x.(P(x) ∨ ¬P(x)) has 1 component, which is ⊤.
	components []Term

	// a thm says the body equals the disjunction of the components.
	// if it's nil, then it's trivial (body = body)
	divisionThm Thm

	// the simplified clause that is equivalent to the original clause.
	equivalentClause *Clause

	// the thm that connects the simplified clause to the original clause.
	simplificationThm Thm

	// if there is only 1 effective literal, we precalculate
	// the abs equality of the clause so it can be used to
	// simplify other clauses.
	absEq *PropWrapper
}

type ClauseMap = map[ClauseKey]*Clause

func (c *Clause) Lits() []Term { return utils.Clone(c.literals) }

func (c *Clause) EffectiveLits() []Term {
	if c.equivalentClause != nil {
		return utils.Clone(c.equivalentClause.literals)
	}
	return utils.Clone(c.literals)
}

func (c *Clause) EffectiveNumLits() int {
	if c.equivalentClause != nil {
		return len(c.equivalentClause.literals)
	}
	return len(c.literals)
}

// If there is only 1 effective literal, returns it.
// Otherwise panics.
func (c *Clause) EffectiveLit() Term {
	if c.equivalentClause != nil {
		Assert(len(c.equivalentClause.literals) == 1)
		return c.equivalentClause.literals[0]
	}
	Assert(len(c.literals) == 1)
	return c.literals[0]
}

func (c *Clause) Size() int {
	return utils.Foldl(func(s int, t Term) int {
		return s + t.Size()
	}, 0, c.components)
}

func (c *Clause) Term() Term { return c.leftAssocWithUniv }

func (c *Clause) EffectiveTerm() Term {
	if c.equivalentClause != nil {
		return c.equivalentClause.leftAssocWithUniv
	}
	return c.leftAssocWithUniv
}

func (c *Clause) EffectiveBody() Term {
	if c.equivalentClause != nil {
		return c.equivalentClause.leftAssocLits
	}
	return c.leftAssocLits
}

func (c *Clause) Key() ClauseKey { return c.key }

// effectiveUnivBoundVarCount is the ∀-binder count of the clause the
// deduction rules actually operate on (the simplified equivalent when
// one exists, mirroring EffectiveBody/EffectiveTerm).
func (c *Clause) effectiveUnivBoundVarCount() int {
	if c.equivalentClause != nil {
		return c.equivalentClause.univBoundVars.Size()
	}
	return c.univBoundVars.Size()
}

// Key equal doesn't mean they are exactly equal, but they are equivalent
// and an equation can be built by clauseEquivalentEq.
func (c *Clause) Equivalent(c0 *Clause) bool { return c.key == c0.key }

// Whether the clause has 1 effective literal
// and its body is a negation of an equality.
// E.g. ∀x.(P(x) ≠ Q(x))
func (c *Clause) IsNeq() bool {
	body := c.leftAssocLits
	if c.equivalentClause != nil {
		body = c.equivalentClause.leftAssocLits
	}
	if n := MatchesNOT(body); n != nil {
		l, _, ok := MatchesEQ(n)
		Assert(!ok || !IsBool(l))
		return ok
	}
	return false
}

func (c *Clause) Divisible() bool { return len(c.components) > 1 }

// ClauseDivision represents a division of a clause into multiple smaller clauses.
// It contains all the information needed for a divide-and-conquer approach to theorem proving.
// When a clause can be divided into independent components, proving each component separately
// and then merging the results is often more efficient than proving the original clause directly.
type ClauseDivision struct {
	// The original divisible clause t = x ∨ y ∨ ...
	DivisibleClause *Clause
	// The list of clauses resulting from dividing the original clause
	DividedClauses []*Clause

	// A callback function that merges theorems that negate the divided clauses
	// back into a proof of the original goal. This is used after all divided clauses
	// have been refuted to construct the final proof.
	Merge func([]*ClauseThm) *ClauseThm

	// Theorem stating ¬x, ¬y, ..., t ⊢ ⊥
	// This theorem enables the recombination of individual proofs into a complete proof
	RefutingThm Thm
}

// Division creates a ClauseDivision structure for this clause if it's divisible.
// Returns nil if the clause cannot be divided (has only one component).
// The division includes:
// 1. The original clause
// 2. The divided smaller clauses
// 3. A merge function to recombine proofs
// 4. A theorem that connects the divided clauses back to the original
// This is a key part of the divide-and-conquer strategy in automated theorem proving,
// allowing complex proofs to be broken into simpler subproblems.
func (c *Clause) Division() *ClauseDivision {
	// If the clause has only one component, it cannot be divided
	if len(c.components) == 1 {
		return nil
	}

	// Create a theorem that relates the clause body to its components
	// componentThm is in the form: c.body ⊢ ∨ {c.components}
	// This establishes that the clause body entails the disjunction of its components
	componentThm := prop.Assume(c.Term())
	if !c.divisionThm.IsZero() {
		// Apply normalization if available to transform the body to standard form
		componentThm = WrapProp(c.divisionThm).EqMP(componentThm)
	}
	// Verify the correctness of the component theorem
	Assert(componentThm.NumHyps() == 1 &&
		componentThm.HasHyp(c.Term()) &&
		Or(c.components...).AlphaEquals(componentThm.Conclusion()))

	// Create clauses from each component
	// This transforms each component term into a proper Clause object
	dividedClauses := utils.MapSlice(c.components, MakeClause)

	// Create a theorem that establishes the relationship between the components and contradiction
	// divideThm demonstrates that negating all components while assuming the disjunction leads to contradiction
	// The form is: ¬component0, ¬component1, ..., ∨ {c.components} ⊢ ⊥
	divideThm := prop.ContradictRecursive(c.components...)
	Assert(divideThm.Conclusion().Equals(F))

	// Transform the theorem to use the original clause body instead of the explicit disjunction
	// New form: ¬component0, ¬component1, ..., c.body ⊢ ⊥
	divideThm = componentThm.DeriveTrans(divideThm)
	Assert(divideThm.NumHyps() == len(c.components)+1 &&
		divideThm.HasHyp(c.Term()))

	// Define the merge function that will combine proofs from subproblems
	// This function takes theorems that negate each divided clause and combines them
	// to produce a theorem that refutes the original clause
	merge := func(clauseThms []*ClauseThm) *ClauseThm {
		// Start with the divide theorem
		mergeThm := divideThm

		// For each divided clause, use its refutation theorem to eliminate
		// the corresponding negated component from the hypothesis list
		for i, dividedClause := range dividedClauses {
			// Verify that each input theorem properly refutes its divided clause
			Assert(clauseThms[i] != nil &&
				clauseThms[i].IsRefuted() &&
				clauseThms[i].HasHypClause(dividedClause))

			// Use the refutation theorem to derive away the negated hypothesis
			ti := WrapProp(clauseThms[i].AsThmCert())
			mergeThm = mergeThm.DeriveHypFrom(ti.NegHyp(dividedClause.Term()))
		}

		// Construct the list of clauses that appear in the final theorem's hypotheses
		// This maintains the connection between terms and their source clauses
		hypClauses := make([]*Clause, 0, mergeThm.NumHyps())
		for h := range mergeThm.HypIter() {
			if h.AlphaEquals(c.Term()) {
				// If the hypothesis is the original clause body, use the original clause
				hypClauses = append(hypClauses, c)
			} else {
				// Otherwise, find which input theorem contains this hypothesis
				for _, clauseThm := range clauseThms {
					if c := findHypClause(clauseThm, h); c != nil {
						hypClauses = append(hypClauses, c)
						break
					}
				}
			}
		}
		// Verify that we've accounted for all hypotheses
		Assert(len(hypClauses) == mergeThm.NumHyps())

		// Create and return the final merged theorem with its associated clauses
		return MakeClauseThm(mergeThm.AsThmCert(), FClause, hypClauses...)
	}

	// Verify that all components are valid before returning the division
	Assert(divideThm.Proved() && len(dividedClauses) > 0 && merge != nil)

	// Return the complete division structure with all necessary components
	return &ClauseDivision{
		DivisibleClause: c,
		DividedClauses:  dividedClauses,
		Merge:           merge,
		RefutingThm:     divideThm.AsThmCert(),
	}
}

// BoolVarDivision creates a ClauseDivision for case-splitting on a boolean variable.
// For a bool variable b, the excluded middle gives ⊢ b ∨ ¬b, so we can split
// any problem into two sub-problems: one assuming b (i.e. b = ⊤) and one assuming ¬b (i.e. b = ⊥).
// Since the excluded middle is a tautology (no hypotheses), the divisible clause
// never appears as a hypothesis in the merged proof.
func BoolVarDivision(b VarTerm) *ClauseDivision {
	Assert(IsBool(b))
	nb := Not(b)
	dividedClauses := []*Clause{MakeClause(b), MakeClause(nb)}
	divisibleClause := MakeClause(Or(b, nb))

	// ¬b, ¬(¬b) ⊢ ⊥
	divideThm := prop.Contradict(nb)
	merge := func(clauseThms []*ClauseThm) *ClauseThm {
		mergeThm := divideThm
		for i, dividedClause := range dividedClauses {
			Assert(clauseThms[i] != nil &&
				clauseThms[i].IsRefuted() &&
				clauseThms[i].HasHypClause(dividedClause))

			ti := WrapProp(clauseThms[i].AsThmCert())
			mergeThm = mergeThm.DeriveHypFrom(ti.NegHyp(dividedClause.Term()))
		}

		// All remaining hypotheses come from the sub-proofs
		// (the divisible clause is a tautology so it's never a hypothesis).
		hypClauses := make([]*Clause, 0, mergeThm.NumHyps())
		for h := range mergeThm.HypIter() {
			for _, clauseThm := range clauseThms {
				if c := findHypClause(clauseThm, h); c != nil {
					hypClauses = append(hypClauses, c)
					break
				}
			}
		}
		Assert(len(hypClauses) == mergeThm.NumHyps())
		return MakeClauseThm(mergeThm.AsThmCert(), FClause, hypClauses...)
	}

	return &ClauseDivision{
		DivisibleClause: divisibleClause,
		DividedClauses:  dividedClauses,
		Merge:           merge,
		RefutingThm:     divideThm.AsThmCert(),
	}
}

// In some case, the clause itself is not ⊤ but essentially equals ⊤.
// E.g. ∀x.(P(x) ∨ ¬P(x)), which is a valid disjunctive clause.
func (c *Clause) EquatesT() bool {
	return c.EffectiveBody().Equals(T)
}

// Replaces univ vars in the clause to avoid vars in another clause
// and any extra vars that should be avoided.
func (c *Clause) AvoidVarsCollision(other *Clause) *Clause {
	newClause := c.clone()
	for v := range c.univBoundVars.Iter() {
		if !other.Term().HasName(v.Name()) {
			continue
		}
		vp := v
		for newClause.Term().HasName(vp.Name()) ||
			other.Term().HasName(vp.Name()) {
			vp = vp.Rename()
		}
		newClause = newClause.rename(v, vp)
	}
	return newClause
}

func (c *Clause) clone() *Clause {
	return &Clause{
		c.originalTerm,
		c.leftAssocWithUniv,
		c.leftAssocLits,
		utils.Clone(c.literals),
		c.univBoundVars.Clone(),
		c.key,
		utils.Clone(c.components),
		c.divisionThm,
		c.equivalentClause,
		c.simplificationThm,
		c.absEq}
}

// The disjuctive components (not literals) of c0 is a subset of c1.
// For example,  ∀x.P(x) divides ∀x.P(x) ∨ ∀y.Q(y)
// but ∀x.P(x) does not divide ∀x.(P(x) ∨ Q(x))
func (c0 *Clause) divides(c1 *Clause) bool {
	return len(c0.components) < len(c1.components) &&
		utils.IsSubset(c0.components, c1.components, Term.AlphaEquals)
}

// Whether c0 trivially subsumes c1.
// E.g. ∀y.P(y) trivially subsumes ∀x.∀y.P(x) ∨ Q(x, y).
func (c0 *Clause) TriviallySubsumes(c1 *Clause) bool {
	if c0.Equivalent(c1) {
		return false
	}
	if c0.divides(c1) {
		return true
	}
	if c0.EffectiveNumLits() != 1 ||
		c1.univBoundVars.Size() < c0.univBoundVars.Size() {
		return false
	}
	s := c0.EffectiveLit()
	for _, t := range c1.EffectiveLits() {
		if s.Size() != t.Size() {
			continue
		}
		env := make([]core.VarPair, 0, c0.univBoundVars.Size())
		tooManyFreeVars := false
		for v := range c1.univBoundVars.Iter() {
			if t.HasFree(v) {
				if len(env) == c0.univBoundVars.Size() {
					tooManyFreeVars = true
					break
				}
				env = append(env, core.VarPair{
					V0: c0.univBoundVars.Ind(len(env)),
					V1: v})
			}
		}
		if tooManyFreeVars || len(env) != c0.univBoundVars.Size() {
			continue
		}
		if s.AlphaEqualsWithEnv(t, env) {
			return true
		}
	}
	return false
}

// Specialize instantiates the ∀-binders of the clause the deduction rules
// work on, each by itself, and applies substs: c.Term() ⊢ body[substs].
// Those binders are the simplified equivalent's where the clause has one,
// and the clause's own say nothing about them: ¬P(y, εx.P(y, x)) binds
// nothing and is read as ∀x.¬P(y, x). A clause read with no binder is
// returned as it is read, substs not applied.
func (c *Clause) Specialize(substs TermSubstsGroup) *PropWrapper {
	if c.effectiveUnivBoundVarCount() == 0 {
		if !c.simplificationThm.IsZero() {
			return WrapProp(c.simplificationThm).LeftAssume()
		}
		return prop.Assume(c.Term())
	}
	var thm *PropWrapper
	if !c.simplificationThm.IsZero() {
		thm = WrapProp(c.simplificationThm).LeftAssume()
		for v := range c.equivalentClause.univBoundVars.Iter() {
			thm = thm.ConclForAllInst(v)
		}
	} else {
		for v := range c.univBoundVars.Iter() {
			if thm == nil {
				thm = prop.InstForAll(c.Term(), v)
			} else {
				thm = thm.ConclForAllInst(v)
			}
		}
	}
	Assert(thm.HasHyp(c.Term()))
	return thm.TermInst(substs...).RewriteConcl(prop.DeepBetaEta)
}

func CompareClauses(c0, c1 *Clause) int {
	if c0.Equivalent(c1) {
		return 0
	}
	if c := cmp.Compare(c0.Size(), c1.Size()); c != 0 {
		return c
	}
	return slices.CompareFunc(c0.components, c1.components, Term.Compare)
}

// Replaces univ vars v0 to v1.
func (c *Clause) rename(v0, v1 VarTerm) *Clause {
	leftAssocBody := c.leftAssocWithUniv
	Assert(c.univBoundVars.HasNo(v1))

	for i, t := range c.literals {
		if t.HasFree(v0) {
			c.literals[i] = t.Substitute(ext.MakeTermSubst(v0, v1))
		}
	}
	replaced := c.univBoundVars.Replace(v0, v1)
	Assert(replaced)

	c.leftAssocLits = Or(c.literals...)
	t := c.leftAssocLits
	for _, v := range c.univBoundVars.Backward() {
		t = ForAll(v)(t)
	}
	c.leftAssocWithUniv = t
	Assert(leftAssocBody.AlphaEquals(c.leftAssocWithUniv))
	// We don't rename the univ vars of the components as they are only used
	// as a whole term modulo α-equal.
	return c
}

// Make a disjunctive DisjunctiveClause.
// The input term should be actually disjunctive,
// i.e. this is not transforming an arbitrary term to disjuctive clause.
// It assumes the input term is in left associated form.
// If it's not, it cannot be recovered from the DisjunctiveClause.
func MakeClause(t Term) *Clause {
	// The F and T clauses are very common cases.
	if t.Equals(F) {
		return FClause
	}
	if t.Equals(T) {
		return TClause
	}

	term, body, literals, univBoundVars := prepareClause(t)
	components, key, divisionThm, simplificationThm := getEquivalentClause(term)

	var equivalentClause *Clause
	var absEq *PropWrapper // of the original clause
	if !simplificationThm.IsZero() {
		if Rhs(simplificationThm).Equals(F) {
			equivalentClause = FClause
		} else if Rhs(simplificationThm).Equals(T) {
			equivalentClause = TClause
		} else {
			term, body, literals, univBoundVars := prepareClause(
				Rhs(simplificationThm))
			var equivalentAbsEq *PropWrapper
			if len(literals) == 1 {
				equivalentAbsEq = prop.ContextAbsEq(term)
				absEq = WrapProp(simplificationThm).
					LeftAssume().
					DeriveTrans(equivalentAbsEq)
			}
			// Reuse the original clause's components and key when they
			// still match the equivalentClause's term (common case).
			// Prenex rewrite can change disjunctive structure (e.g.
			// ∀x.(A(x) ∨ ∀y.B(y)) → ∀x.∀y.(A(x) ∨ B(y))), making
			// the original components incompatible. In that case,
			// recompute via normalizeClause.
			eqComponents := components
			eqKey := key
			termComponents := DecomposesOR(term)
			var eqDivisionThm Thm
			if !slices.EqualFunc(eqComponents, termComponents, Term.AlphaEquals) {
				eqComponents = termComponents
				if u := normalizeClause(term); u != nil {
					eqDivisionThm = u.AsThmCert()
					eqComponents = DecomposesOR(Rhs(u))
				}
				eqKey = ClauseKey(_DISJUNCTIVE_TERM_PREFIX +
					utils.GenerateHash(utils.MapSlice(
						eqComponents, Term.AlphaKey)...))
			}
			equivalentClause = &Clause{
				originalTerm:      Rhs(simplificationThm),
				leftAssocWithUniv: term,
				leftAssocLits:     body,
				literals:          literals,
				univBoundVars:     univBoundVars,
				key:               eqKey,
				components:        eqComponents,
				divisionThm:       eqDivisionThm,
				absEq:             equivalentAbsEq,
			}
			Assert(equivalentClause.leftAssocWithUniv.
				AlphaEquals(Rhs(simplificationThm)))
		}
	}

	if absEq == nil &&
		equivalentClause == nil &&
		len(literals) == 1 {
		absEq = prop.ContextAbsEq(term)
	}

	return &Clause{
		originalTerm:      t,
		leftAssocWithUniv: term,
		leftAssocLits:     body,
		literals:          literals,
		univBoundVars:     univBoundVars,
		key:               key,
		components:        components,
		divisionThm:       divisionThm,
		equivalentClause:  equivalentClause,
		simplificationThm: simplificationThm,
		absEq:             absEq,
	}
}

var FClause = &Clause{
	originalTerm:      F,
	leftAssocWithUniv: F,
	leftAssocLits:     F,
	literals:          []Term{F},
	key:               ClauseKey(_DISJUNCTIVE_TERM_PREFIX + F.AlphaKey()),
	components:        []Term{F},
}

var TClause = &Clause{
	originalTerm:      T,
	leftAssocWithUniv: T,
	leftAssocLits:     T,
	literals:          []Term{T},
	key:               ClauseKey(_DISJUNCTIVE_TERM_PREFIX + T.AlphaKey()),
	components:        []Term{T},
}

func prepareClause(t Term) (Term, Term, []Term, VarList) {
	Assert(ext.IsDisjunctive(t))
	originalTerm := t
	// Clause should not contain numerical free vars.
	Assert(t.AllFree(func(v VarTerm) bool {
		_, err := strconv.Atoi(string(v.Name()))
		return err != nil
	}))

	univBoundVars, t := DecomposesFORALL(t)

	// This is to avoid edge cases like ∀u.⊤.
	Assert(univBoundVars.AllFreeIn(t))

	literals := DecomposesOR(t)
	body := Or(literals...)
	if body.AlphaEquals(t) {
		return originalTerm, t, literals, univBoundVars
	}

	term := body
	for _, v := range univBoundVars.Backward() {
		term = ForAll(v)(term)
	}
	return term, body, literals, univBoundVars
}

var initClauseRewrite = prop.ChainRewrites(
	prop.ClauseFactorRewrite,
	univHilbertRewrite,
	prop.ForAllORRewrite,
)

// Sometimes the conclusion contains a Hilbert term
// that can be rewritten as a univeral term.
// E.g. ¬P(y, εx.P(y, x)) = (∀x.¬P(y, x))
// If so, we should rewrite it.
// This rewrite can work within universal quantifiers.
var univHilbertRewrite = func(t Term) *PropWrapper {
	// we don't chain them together because
	// if HilbertExistsRewrite is not applicable
	// no need to do the rest.
	if u := prop.HilbertExistsRewrite(t); u != nil {
		u = u.RewriteConclRhs(BasicRewrite)
		u = u.RewriteConclRhs(prop.DeepUniversalPrenexRewrite)
		if ext.IsDisjunctive(Rhs(u)) {
			return u
		}
	}
	return nil
}

// We do these things in order to normalize a clause:
// 1. decompose the body to divisible disjunctive components if possible.
// 2. rewrite each component using DisjunctNormalizeRewrite.
// 3. reorder the components using DisjunctSortRewrite.
func normalizeClause(s Term) *PropWrapper {
	_s, w := s, initClauseRewrite(s)
	if w != nil {
		_s = Rhs(w)
	}
	components := DecomposesOR(_s)

	normalizations := utils.MapSlice(components, prop.DisjunctNormalizeRewrite)

	normalization := normalizations[0]
	if normalization == nil {
		normalization = prop.Refl(components[0])
	}
	for i, u := range normalizations[1:] {
		if u != nil {
			normalization = normalization.LeftApply(ext.OR).Apply(u)
		} else {
			normalization = normalization.LeftApply(ext.OR).RightApply(components[i+1])
		}
	}
	if w == nil {
		w = normalization
	} else {
		w = w.EqTrans(normalization)
	}

	if len(components) > 1 {
		w = w.RewriteConclRhs(prop.DisjunctSortRewrite)
	}

	Assert(s.AlphaEquals(Lhs(w)) && w.NumHyps() == 0)
	if !s.AlphaEquals(Rhs(w)) {
		return w
	}

	return nil
}

// Returns the equality t = s if t and s have same normalized form.
var clauseEquivalentEq = prop.EqualityFromRewrite(normalizeClause)

// Calculates the components of the disjuctive clause modulo equivalency.
// and the thm in the form ⊢ term = ∨ {components}
func getEquivalentClause(s Term) ([]Term, ClauseKey, Thm, Thm) {
	Assert(ext.IsDisjunctive(s))

	size := disjunctiveComponentSize(s)

	var divisionThm, simplificationThm Thm
	var simplification *PropWrapper
	u := normalizeClause(s)

	if u != nil {
		divisionThm = u.AsThmCert()
		s = Rhs(u)
	}
	components := DecomposesOR(s)
	Assert(slices.IsSortedFunc(components, Term.Compare))
	Assert(Or(components...).AlphaEquals(s))

	newSize := 0
	for _, component := range components {
		newSize = newSize + disjunctiveComponentSize(component)
	}

	if u != nil &&
		(Rhs(u).Equals(T) || Rhs(u).Equals(F) || newSize < size) {
		simplification = u.
			RewriteConclRhs(prop.DeepUniversalPrenexRewrite)
		vars, _s := DecomposesFORALL(Rhs(simplification))
		w := prop.AssocORRewrite(_s)
		// All order problems must be because prenex rewrite.
		Assert(!vars.Empty() || w == nil)
		if w != nil {
			simplification = simplification.RewriteConclRhs(
				prop.EqReplacementRewrite(w))
		}
		simplificationThm = simplification.AsThmCert()
	}

	key := ClauseKey(_DISJUNCTIVE_TERM_PREFIX +
		utils.GenerateHash(utils.MapSlice(components, Term.AlphaKey)...))
	return components, key, divisionThm, simplificationThm
}
