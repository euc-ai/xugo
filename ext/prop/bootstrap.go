/**
* File: bootstrap.go
*
* Bootstrap proofs for basic theorems
* The proofs can be found in the bootstrap_proofs.go file.
* The theorems are:
*
* ⊤ is true
* ⊥ derives everything
* ¬⊤ ⇔ ⊥
* ¬⊥ ⇔ ⊤
* ¬p, p ⊢ ⊥
* (p ⇔ ⊥) ⇔ ¬p
* (p ⇒ ⊥) ⇔ ¬p
* p ∧ q ⊢ p, p ∧ q ⊢ q
* p0 ∧ p1 ∧ ... ∧ pn ⊢ pi
* p, q ⊢ p ∧ q
* p ⊢ p ∨ q, q ⊢ p ∨ q
* p ∨ q, p ⇒ c, q ⇒ c ⊢ c
* p0, p1, ..., pn ⊢ p0 ∧ p1 ∧ ... ∧ pn
* ¬p0, ¬p1, ..., ¬pn, p0 ∨ p1 ∨ ... ∨ pn ⊢ ⊥
* p0 ∨ p1 ∨ ..., p0 ⇒ c, p1 ⇒ c, ...  ⊢ c
*
* Modus Ponens: p, p ⇒ q ⊢ q
* Excluded middle: p ∨ ¬p
* Boolean induction: S(⊤), S(⊥) ⊢ S(p)
* Boolean forall: ∀p.S(p) ⇔ S(⊤) ∧ S(⊥) for boolean p
* Boolean exists: ∃p.S(p) ⇔ S(⊤) ∨ S(⊥) for boolean p
* Double negation: ¬¬p ⇔ p
* Commute =: (x = y) ⇔ (y = x)
* Commute ∧: (p ∧ q) ⇔ (q ∧ p)
* Commute ∨: (p ∨ q) ⇔ (q ∨ p)
*
* Boolean equalities:
* (p ⇔ ⊤) ⇔ p, (p ⇔ ⊥) ⇔ ¬p
* (⊤ ⇔ p) ⇔ p, (⊥ ⇔ p) ⇔ ¬p
* (p ⇔ p) ⇔ ⊤, (p ⇔ ¬p) ⇔ ⊥
* boolean and:
* (p ∧ ⊤) ⇔ p, (p ∧ ⊥) ⇔ ⊥
* (⊤ ∧ p) ⇔ p, (⊥ ∧ p) ⇔ ⊥
* (p ∧ p) ⇔ p, (p ∧ ¬p) ⇔ ⊥
* Boolean or:
* (p ∨ ⊤) ⇔ ⊤, (p ∨ ⊥) ⇔ p
* (⊤ ∨ p) ⇔ ⊤, (⊥ ∨ p) ⇔ p
* (p ∨ p) ⇔ p, (p ∨ ¬p) ⇔ ⊤
* Boolean implication:
* (p ⇒ ⊤) ⇔ ⊤, (p ⇒ ⊥) ⇔ ¬p
* (⊤ ⇒ p) ⇔ p, (⊥ ⇒ p) ⇔ ⊤
* (p ⇒ p) ⇔ ⊤, (p ⇒ ¬p) ⇔ ⊥
*
* Binary theorems:
* (¬p ⇔ ¬q) ⇔ (p ⇔ q)
* (p ⇒ q) ⇔ (¬p ∨ q)
* (p ∨ q) ⇔ (¬p ⇒ q)
* ¬(p ∧ q) ⇔ (¬p ∨ ¬q)
* ¬(p ∨ q) ⇔ (¬p ∧ ¬q)
* ¬(p ⇒ q) ⇔ (p ∧ ¬q)
* (p ⊕ q) ⇔ (¬p ⇔ q)
* p ∧ (p ∨ q) ⇔ p
* p ∨ (p ∧ q) ⇔ p
* (p ⇔ q) ⇔ ((p ∧ q) ∨ (¬p ∧ ¬q))
* (p ⊕ q) ⇔ ((p ∨ q) ∧ (¬p ∨ ¬q))
*
* Associativity and Distributivity:
* ((p ⇔ q) ⇔ r) ⇔ (p ⇔ (q ⇔ r))
* ((p ∧ q) ∧ r) ⇔ (p ∧ (q ∧ r))
* ((p ∨ q) ∨ r) ⇔ (p ∨ (q ∨ r))
* (p ∧ (q ∨ r)) ⇔ ((p ∧ q) ∨ (p ∧ r))
* (p ∨ (q ∧ r)) ⇔ ((p ∨ q) ∧ (p ∨ r))
*
* Monoticity:
* p ⇒ q, p ∧ r ⊢ q ∧ r
* p ⇒ q, p ∨ r ⊢ q ∨ r
*
* Cond Clause:
* ⊢ Cond(c, x, x) = x
* ⊢ Cond(⊤, x, y) = x
* ⊢ Cond(⊥, x, y) = y
*
* Quantifier theorems:
* ∀x.P(x) ⊢ P(t)
* ¬(∀x.P(x)) ⇔ ∃x.¬P(x)
* ∀x.(P(x) ∧ Q(x)) ⇔ (∀x.P(x) ∧ ∀x.Q(x))
* ∀x.(P(x) ⇒ Q(x)), ∀x.P(x) ⊢ ∀x.Q(x)
* ∀x.q ⇔ Q (given x not in Q)
* t0 ⇔ t1 where t0 and t1 have the same body
*		and the same univ quantifiers with different order
* (λx.f(x) = λx.g(x)) ⇔ ∀x.(f(x) = g(x))
* P(t) ⊢ ∃x.P(x)
* ∃x.P(x) ⊢ P(εx.P(x))
* ¬∃x.P(x) ⇔ ∀x.¬P(x)
* ∃x.(P(x) ∧ Q(x)) ⊢ ∃x.P(x) ∧ ∃x.Q(x)
* ∃x.(P(x) ∨ Q(x)) ⇔ (∃x.P(x) ∨ ∃x.Q(x))
* ∀x.(P(x) ⇒ Q(x)), ∃x.P(x) ⊢ ∃x.Q(x)
* ∃x.q ⇔ Q (given x not in Q)
* t0 = t1 where t0 and t1 have the same body
*		and the same existential quantifiers with different order
*
* Prenex normal form:
* (∀x.P(x)) ∧ q ⇔ ∀x.(P(x) ∧ Q)
* Q ∧ ∀x.P(x) ⇔ ∀x.(Q ∧ P(x))
* (∃x.P(x)) ∧ q ⇔ ∃x.(P(x) ∧ Q)
* Q ∧ ∃x.P(x) ⇔ ∃x.(Q ∧ P(x))
* (∀x.P(x)) ∨ q ⇔ ∀x.(P(x) ∨ Q)
* Q ∨ ∀x.P(x) ⇔ ∀x.(Q ∨ P(x))
* (∃x.P(x)) ∨ q ⇔ ∃x.(P(x) ∨ Q)
* Q ∨ ∃x.P(x) ⇔ ∃x.(Q ∨ P(x))
* (∀x.P(x)) ⇒ q ⇔ ∃x.(P(x) ⇒ Q)
* Q ⇒ ∀x.P(x) ⇔ ∀x.(Q ⇒ P(x))
* (∃x.P(x)) ⇒ q ⇔ ∀x.(P(x) ⇒ Q)
* Q ⇒ ∃x.P(x) ⇔ ∃x.(Q ⇒ P(x))
*
* Denote theorems:
* P(s) ⇔ ∀x.((x = s) ⇒ P(x))
* P(s) ⇔ ∃x.((x = s) ∧ P(x))
*
* Skolemization:
* ∀x.∃z.R(x, z) ⇔ ∃f.∀x.R(x, f(x))
*
* Alternative definition of unique existence:
* ∃!x.P(x) ⇔ ∃x.P(x) ∧ ∀x.∀y.((P(x) ∧ P(y)) ⇒ (x = y))
*
* Unique existence at a witness:
* ∃!x.P(x) ⇔ ∃x.(P(x) ∧ ∀y.(P(y) ⇒ (y = x)))
*
* Skolemization of unique existence:
* ∀x.∃!z.R(x, z) = ∃f.∀x.∀z.(R(x, z) ⇔ (f(x) = z))
*
* Alternative Skolemization of unique existence:
* ∀x.∃!z.R(x, z) ⇔ ∃!f.∀x.R(x, f(x))
 */

package prop

// ⊢ ⊤
var DerivesTrue = derivesTrueProof()

// ⊥ ⊢ p
var FalseDerives = falseDerivesProof()

// ¬⊤ ⇔ ⊥
var NotTrue = notTrueProof()

// ¬⊥ ⇔ ⊤
var NotFalse = notFalseProof()

// ¬p, p ⊢ ⊥
var Contradict = contradictProof()

// ⊢ (p ⇔ ⊥) ⇔ ¬p
var EqualsFalse = equalsFalseProof()

// ⊢ (p ⇒ ⊥) ⇔ ¬p
var ImpliesFalse = impliesFalseProof()

// p ∧ q ⊢ p,
// p ∧ q ⊢ q
var HypAND0, HypAND1 = hypANDProof()

// p0 ∧ p1 ∧ ... ∧ pn ⊢ pi
var HypANDRecursive = hypANDRecursiveProof

// p, q ⊢ p ∧ q
var ConclAND = conclANDProof()

// p0, p1, ..., pn ⊢ p0 ∧ p1 ∧ ... ∧ pn
var ConclANDRecursive = conclANDRecursiveProof

// c, p, q:
// p ∨ q, p ⇒ c, q ⇒ c ⊢ c
var ByCases = byCasesProof()

// c, p0, p1, ...:
// p0 ∨ p1 ∨ ..., p0 ⇒ c, p1 ⇒ c, ...  ⊢ c
var ByCasesRecursive = byCasesRecursiveProof

// p ⊢ p ∨ q,
// q ⊢ p ∨ q
var ConclOR0, ConclOR1 = conclORProof()

// ¬p0, ¬p1, ..., ¬pn, p0 ∨ p1 ∨ ... ∨ pn ⊢ ⊥
var ContradictRecursive = contradictRecursiveProof

// p, p ⇒ q ⊢ q
var ModusPonens = modusPonensProof()

// ⊢ (x = y) ⇔ (y = x)
var CommuteEQ = commuteEQProof()

// ⊢ (p ∧ q) ⇔ (q ∧ p)
var CommuteAND = commuteANDProof()

// ⊢ (p ∨ q) ⇔ (q ∨ p)
var CommuteOR = commuteORProof()

// ⊢ p ∨ ¬p
var ExcludedMiddle = excludedMiddleProof()

// λp.S(p) for boolean p:
// S(⊤), S(⊥) ⊢ S(p)
var BoolInduct = boolInductProof()

// λp.S(p) for boolean p:
// ⊢ ∀p.S(p) ⇔ S(⊤) ∧ S(⊥)
var BoolForAll = boolForAllProof()

// λp.S(p) for boolean p:
// ⊢ ∃p.S(p) ⇔ S(⊤) ∨ S(⊥)
var BoolExists = boolExistsProof()

// ⊢ ¬¬p ⇔ p
var DoubleNeg = doubleNegProof()

// (p ⇔ ⊤) ⇔ p, (p ⇔ ⊥) ⇔ ¬p,
// (⊤ ⇔ p) ⇔ p, (⊥ ⇔ p) ⇔ ¬p,
// (p ⇔ p) ⇔ ⊤, (p ⇔ ¬p) ⇔ ⊥,
// (p ∧ ⊤) ⇔ p, (p ∧ ⊥) ⇔ ⊥,
// (⊤ ∧ p) ⇔ p, (⊥ ∧ p) ⇔ ⊥,
// (p ∧ p) ⇔ p, (p ∧ ¬p) ⇔ ⊥,
// (p ∨ ⊤) ⇔ ⊤, (p ∨ ⊥) ⇔ p,
// (⊤ ∨ p) ⇔ ⊤, (⊥ ∨ p) ⇔ p,
// (p ∨ p) ⇔ p, (p ∨ ¬p) ⇔ ⊤,
// (p ⇒ ⊤) ⇔ ⊤, (p ⇒ ⊥) ⇔ ¬p,
// (⊤ ⇒ p) ⇔ p, (⊥ ⇒ p) ⇔ ⊤,
// (p ⇒ p) ⇔ ⊤, (p ⇒ ¬p) ⇔ ⊥
var BooleanThms = booleanThmsProof()

// (¬p ⇔ ¬q) ⇔ (p ⇔ q)
// (p ⇒ q) ⇔ (¬p ∨ q)
// (p ∨ q) ⇔ (¬p ⇒ q)
// ¬(p ∧ q) ⇔ (¬p ∨ ¬q)
// ¬(p ∨ q) ⇔ (¬p ∧ ¬q)
// ¬(p ⇒ q) ⇔ (p ∧ ¬q)
// (p ⊕ q) ⇔ (¬p ⇔ q)
// p ∧ (p ∨ q) ⇔ p
// p ∨ (p ∧ q) ⇔ p
// (p ⇔ q) ⇔ ((p ∧ q) ∨ (¬p ∧ ¬q))
// (p ⊕ q) ⇔ ((p ∨ q) ∧ (¬p ∨ ¬q))
var BinaryThms = binaryThmsProof()

// ((p ∧ q) ∧ r) ⇔ (p ∧ (q ∧ r))
// ((p ∨ q) ∨ r) ⇔ (p ∨ (q ∨ r))
// ((p ⇔ q) ⇔ r) ⇔ (p ⇔ (q ⇔ r))
// (p ∧ (q ∨ r)) ⇔ ((p ∧ q) ∨ (p ∧ r))
// (p ∨ (q ∧ r)) ⇔ ((p ∨ q) ∧ (p ∨ r))
// p ⇒ q, p ∧ r ⊢ q ∧ r
// p ⇒ q, p ∨ r ⊢ q ∨ r
// (p ⇒ r) ∧ (q ⇒ r) ⇔ ((p ∨ q) ⇒ r)
var TernaryThms = ternaryThmsProof()

// c, x:
// ⊢ Cond(c, x, x) = x
var CondId = condIdProof()

// x, y:
// ⊢ Cond(⊤, x, y) = x
// ⊢ Cond(⊥, x, y) = y
var CondClauseT, CondClauseF = condClauseProof()

// ∀x.P(x), t:
// ∀x.P(x) ⊢ P(t)
var InstForAll = instForAllProof()

// λx.P(x):
// ⊢ ¬(∀x.P(x)) ⇔ ∃x.¬P(x)
var NegForAll = negForAllProof()

// λx.P(x), λx.Q(x):
// ⊢ ∀x.(P(x) ∧ Q(x)) ⇔ (∀x.P(x) ∧ ∀x.Q(x))
var ForAllAND = forAllANDProof()

// λx.P(x), λx.Q(x):
// ∀x.(P(x) ⇒ Q(x)), ∀x.P(x) ⊢ ∀x.Q(x)
var ForAllIMPLY = forAllIMPLYProof()

// x, Q:
// ⊢ ∀x.q ⇔ Q (given x not in Q)
var MootForAll = mootForAllProof()

// t0 and t1 are alpha-equivalent universally quantified terms:
// they may differ by the order of outer ∀ binders and/or by binder renaming.
// ⊢ t0 ⇔ t1
var ReorderForAll = reorderForAllProof()

// λx.f(x), λx.g(x):
// ⊢ (λx.f(x) = λx.g(x)) ⇔ ∀x.(f(x) = g(x))
var FunEq = funEqProof()

// ∃x.P(x), t:
// P(t) ⊢ ∃x.P(x)
var InstExists = instExistsProof()

// λx.P(x):
// ∃x.P(x) ⊢ P(εx.P(x))
var SelectExists = selectExistsProof()

// λx.P(x):
// ⊢ ¬∃x.P(x) ⇔ ∀x.¬P(x)
var NegExists = negExistsProof()

// λx.P(x), λx.Q(x):
// ∃x.(P(x) ∧ Q(x)) ⊢ ∃x.P(x) ∧ ∃x.Q(x)
var ExistsAND = existsANDProof()

// λx.P(x), λx.Q(x):
// ⊢ ∃x.(P(x) ∨ Q(x)) ⇔ (∃x.P(x) ∨ ∃x.Q(x))
var ExistsOR = existsORProof()

// λx.P(x), λx.Q(x):
// ∀x.(P(x) ⇒ Q(x)), ∃x.P(x) ⊢ ∃x.Q(x)
var ExistsIMPLY = existsIMPLYProof()

// x, Q:
// ⊢ ∃x.q ⇔ Q (given x not in Q)
var MootExists = mootExistsProof()

// t0 and t1 are alpha-equivalent universally quantified terms:
// they may differ by the order of outer ∀ binders and/or by binder renaming.
// ⊢ t0 ⇔ t1
var ReorderExists = reorderExistsProof

// λx.P(x), Q:
// (∀x.P(x)) ∧ q ⇔ ∀x.(P(x) ∧ Q)
// Q ∧ ∀x.P(x) ⇔ ∀x.(Q ∧ P(x))
// (∃x.P(x)) ∧ q ⇔ ∃x.(P(x) ∧ Q)
// Q ∧ ∃x.P(x) ⇔ ∃x.(Q ∧ P(x))
// (∀x.P(x)) ∨ q ⇔ ∀x.(P(x) ∨ Q)
// Q ∨ ∀x.P(x) ⇔ ∀x.(Q ∨ P(x))
// (∃x.P(x)) ∨ q ⇔ ∃x.(P(x) ∨ Q)
// Q ∨ ∃x.P(x) ⇔ ∃x.(Q ∨ P(x))
// (∀x.P(x)) ⇒ q ⇔ ∃x.(P(x) ⇒ Q)
// Q ⇒ ∀x.P(x) ⇔ ∀x.(Q ⇒ P(x))
// (∃x.P(x)) ⇒ q ⇔ ∀x.(P(x) ⇒ Q)
// Q ⇒ ∃x.P(x) ⇔ ∃x.(Q ⇒ P(x))
var PrenexThms = prenexThmsProof()

// x, s, λx.P(x):
// ⊢ P(s) ⇔ ∀x.((x = s) ⇒ P(x))
var ForAllDenote = forAllDenoteProof()

// x, s, λx.P(x):
// ⊢ P(s) ⇔ ∃x.((x = s) ∧ P(x))
var ExistsDenote = existsDenoteProof()

// f, λx.λz.R(x, z):
// ∀x.∃z.R(x, z) ⇔ ∃f.∀x.R(x, f(x))
var Skolem = skolemProof()

// λx.P(x):
// ∃!x.P(x) ⇔ ∃x.P(x) ∧ ∀x.∀y.((P(x) ∧ P(y)) ⇒ (x = y))
var AltUnique = altUniqueProof()

// λx.P(x):
// ∃!x.P(x) ⇔ ∃x.(P(x) ∧ ∀y.(P(y) ⇒ (y = x)))
var WitnessUnique = witnessUniqueProof()

// f, λx.λz.R(x, z):
// ∀x.∃!z.R(x, z) ⇔ ∃f.∀x.∀z.(R(x, z) ⇔ (f(x) = z))
var SkolemUnique = skolemUniqueProof()

// f, λx.λz.R(x, z):
// ∀x.∃!z.R(x, z) ⇔ ∃!f.∀x.R(x, f(x))
var SkolemAltUnique = skolemAltUniqueProof()
