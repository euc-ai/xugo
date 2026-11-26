// Package unify is higher-order unification of terms: pattern
// unification where it decides the problem, Huet's algorithm for the
// rest, and type unification carried along.
//
// Unify unifies two terms and their types together, and UnifyTerms the
// terms alone. TermMatch is the one-sided problem: a pattern, whose
// named variables may be instantiated, against a closed target.
//
// The pattern fragment includes its base case, a bare meta-variable
// against any term — the shape a first-order rewrite rule's variables
// take here (a projection law `re(complex(a, b)) = a` against
// `re(complex(X, Y))`): such a pair commits `M ↦ t` directly and never
// enters imitation. Terms are β-η normalized as the search runs,
// substitution avoids capture, and an occurs check refuses a circular
// binding.
//
// Where the caller's context carries no deadline the search runs
// sequentially under a work budget (DefaultUnifyBudget), so Unify is a
// function of its two terms: the same result on any machine, which is
// what the replay of a recorded lemma step rests on. A caller that sets
// a deadline keeps wall-clock semantics, the branches of the search
// tree explored concurrently against it.
package unify
