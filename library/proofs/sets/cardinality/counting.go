// counting.go — the chapter: counting a finite set, and how counts compose.
//
// Six parts, marked by banners:
//
// - Where counting comes from
// - The counting calculus
// - has_size: the size of a finite set, as a relation
// - Comparing two counts
// - Counts under union and difference
// - Counting a union of a family

package cardinality

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/internal/setvocab"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Where counting comes from
// ---------------------------------------------------------------------------
//
// card is not defined by a recursion; it is defined by a CHOICE. To fold
// a step function over a set you must visit the elements in some order,
// and a set has no order, so the fold is introduced as an arbitrary
// function that happens to satisfy the two clauses one wants — set_fold is
// Hilbert's ε over exactly that specification, and card is that fold
// taken at the step that adds one.
//
// A definition by choice says nothing until something is there to
// choose from, and supplying that is the first member here. The next
// reads that fold from another side: what it is at a DELETION rather
// than at an insertion. Then the recursion is carried to a step that is
// closed and left-commutative only on a set K, as a module's addition is
// on its carrier, and with it what the fold does NOT depend on — a
// step's values away from the set being folded: on K first, and then,
// read at K = 𝕌, for any step that commutes. The last reads the fold at
// the one step counting is, and so gives card the clauses the rest of
// the chapter computes with.

// FiniteRecursion — a fold over the finite sets really does compute what
// its clauses say: it starts at b, and enlarging a set by one element
// applies the step function once, unless the element was already there.
//
// The one thing asked of the step is that its two arguments do not
// interfere — feeding in x then y gives what feeding in y then x gives.
// That is what makes the answer independent of the order the elements
// are visited in, and without it there is nothing for set_fold to choose.
//
// The proof is two sentences. A fold with these clauses EXISTS — that
// is finite_set.FoldExists, and the commuting hypothesis is its whole
// input. And set_fold(f, ·, b) is by definition a choice among the
// functions that have them, so unfolding the definition leaves the
// ε-term facing its own specification, which the existence fact
// discharges.
//
// Note what is NOT here: no induction over the set, and no order of
// visits. Both live beneath FoldExists, which is where the
// well-definedness of the fold is actually established.
//
// The fold it justifies is not card's alone — every iteration over a
// finite set is taken through this theorem, so it is the surface a later
// iteration chapter reads rather than an implementation detail of
// counting. The well-definedness beneath it — that the fold's value does
// not depend on the order the elements are visited in — is finite_set's
// part on folding over a finite set, and FoldExists is its exit.
var FiniteRecursion = finiteRecursionThm{family.Add(registry.ProofEntry{
	Name: "FiniteRecursion",
	Key:  "prop_69e737f6a3242da6",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B → B). ∀b:B.",
			Hypotheses: []string{
				"∀x y:A. ∀z:B. x ≠ y ⇒ f(x, f(y, z)) = f(y, f(x, z))",
			},
			Conclusion: "set_fold(f, ∅, b) = b ∧ " +
				"(∀x:A. ∀s:set(A). " +
				"    finite(s) ⇒ " +
				"    set_fold(f, insert(x, s), b) = COND(x ∈ s, set_fold(f, s, b), f(x, set_fold(f, s, b))))",
		},
		func(a *Argument, f, b Term, commutes Fact) {
			// The clauses said of a nameless g rather than of set_fold. That
			// is what keeps the ε out of this file: the whole argument is
			// about WHICH functions satisfy them, never about which one
			// gets chosen.
			a.Have(
				"some fold does start at b and step by f — that is FoldExists, and commuting is all it asks of f",
				"∃g:(set(A) → B). "+
					"    g(∅) = b ∧ (∀x:A. ∀s:set(A). finite(s) ⇒ g(insert(x, s)) = COND(x ∈ s, g(s), f(x, g(s))))",
				// One witness pair, in the lemma's own stated order (the
				// step, then the starting value). Only those two are given:
				// they are the slots the closer cannot invent, and the set
				// and the element match off the goal. Left BARE this cite
				// does not close at all.
				By(commutes, At(finite_set.FoldExists, f, b)))

			// ↦ the same clauses with the ε-term standing where g stood.
			// The existence just established is the ε-axiom's premise, so
			// the unfold closes rather than opening a goal — which is the
			// whole of what "set_fold is defined by a choice" means. The
			// existence is consumed from the context rather than by a
			// premise list, because an unfold takes none; withhold it and
			// the same unfold leaves the ε-goal standing.
			a.Show(
				"and set_fold(f, ·, b) is chosen among those folds, so it is one of them",
				Unfold(SetFoldDef))
		}),
})}

// FiniteRecursionDelete — the same fold read at a DELETION instead of
// at an insertion: what a set's fold is, in terms of the fold of that
// set with one element taken out.
//
// The two forms are one theorem seen from two sides. The insertion
// form answers "what does putting an element in cost", and its answer
// is conditional on the element being new. This one answers "what is
// the fold of s, given the fold of s without x", and it asks nothing
// in return: both branches of the conditional are stated, so whichever
// way membership falls the equation holds. That is what a consumer
// walking a set DOWN wants — name any point of it and get the fold of
// the remainder, with no side condition to discharge first.
//
// One branch, one law. Where x is in s, putting x back into the
// remainder recovers s, so the insertion clause read AT the remainder
// is already the goal — and the side condition that clause turns on
// costs nothing here, because x is exactly what the remainder no
// longer holds. Where x is not in s, deleting it changes nothing, both
// sides fold the same set, and no recursion is spent at all.
//
// The commuting hypothesis is not used by the argument here: it is
// carried through to the insertion form, which is the only thing in
// this proof that asks for it.
var FiniteRecursionDelete = finiteRecursionDeleteThm{family.Add(registry.ProofEntry{
	Name: "FiniteRecursionDelete",
	Key:  "prop_5cce0305093d71f5",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B → B). ∀b:B.",
			Hypotheses: []string{
				"∀x y:A. ∀z:B. x ≠ y ⇒ f(x, f(y, z)) = f(y, f(x, z))",
			},
			Conclusion: "set_fold(f, ∅, b) = b ∧ " +
				"(∀x:A. ∀s:set(A). " +
				"    finite(s) ⇒ " +
				"    set_fold(f, s, b) = " +
				"    COND(x ∈ s, f(x, set_fold(f, delete(s, x), b)), set_fold(f, delete(s, x), b)))",
		},
		func(a *Argument, f, b Term, commutes Fact) {
			a.Do(SplitConj(
				Case(
					"at ∅ nothing has been folded in, so the value is the one the fold started at",
					By(commutes, At(FiniteRecursion, f, b))),
				Case(
					"and a finite set is its own remainder at x, with x folded back in exactly when it was there",
					Derive(func(a *Argument) {
						x := a.Fix()
						s := a.Fix()
						finite := a.Assume()

						a.Cases(a.Term("x ∈ s"))
						a.When(
							"x ∈ s: putting x back into the remainder recovers s, and the insertion form answers there",
							func(a *Argument, member Fact) {
								step := a.Have(
									"the insertion form read at the remainder, which is finite and lacks x, folds x in once",
									"set_fold(f, insert(x, delete(s, x)), b) = f(x, set_fold(f, delete(s, x), b))",
									By(
										finite,
										At(finite_set.FiniteDelete, s, x),
										At(set_basic.InDelete, s, x, x),
										commutes,
										At(FiniteRecursion, f, b)))
								a.Show(
									"and the set x is put back into is s itself",
									By(step, member, At(set_algebra.InsertDelete, s, x)))
							})
						a.Otherwise(
							"x ∉ s: the remainder is s, so the branch to prove is the one that folds nothing back in",
							func(a *Argument, absent Fact) {
								a.Show(
									"deleting an element a set never held leaves the "+
										"set, and the fold of one set is the fold of the other",
									// x ∉ s ⇔ delete(s, x) = s — an installed
									// set law, so `vocab.go`'s pointwise fold
									// applies. Checked by removal: without
									// `Normalized` the law reaches the refuter
									// spread over points, where the set standing
									// inside the fold is opaque to it.
									By(Normalized, absent, At(set_algebra.DeleteNonElement, s, x)))
							})
					})),
			))
		}),
})}

// FiniteRecursionWithin — FiniteRecursion for a step that is closed and
// left-commutative only on a set K, folded from a start in K: the fold
// still starts at b and takes one step of f at each fresh point.
//
// FiniteRecursion does not apply to f itself, whose two orders need
// only agree inside K. The step guarded by K — f inside K, standing
// still outside it — commutes everywhere, so FiniteRecursion gives it a
// fold. That fold never leaves K on a finite set, by induction, so each
// step it takes is a step of f, and it has f's own clauses: the witness
// the choice behind set_fold(f, ·, b) needs, as FoldExists is for
// FiniteRecursion.
var FiniteRecursionWithin = finiteRecursionWithinThm{family.Add(registry.ProofEntry{
	Name: "FiniteRecursionWithin",
	Key:  "prop_c79d049cf5989dcb",
	Build: family.Theorem(Statement{
		Binders: "∀f:(A → B → B). ∀b:B. ∀K:set(B).",
		Hypotheses: []string{
			"b ∈ K",
			"∀x:A. ∀z:B. z ∈ K ⇒ f(x, z) ∈ K",
			"∀x y:A. ∀z:B. x ≠ y ∧ z ∈ K ⇒ f(x, f(y, z)) = f(y, f(x, z))",
		},
		Conclusion: "set_fold(f, ∅, b) = b ∧ " +
			"(∀x:A. ∀s:set(A). " +
			"    finite(s) ⇒ " +
			"    set_fold(f, insert(x, s), b) = COND(x ∈ s, set_fold(f, s, b), f(x, set_fold(f, s, b))))",
	},
		func(a *Argument, f *Arrow2[A, B, B], b *Expr[B], K *Expr[Set[B]], given Fact) {
			parts := a.Conjuncts(
				given,
				"b lies in K",
				"a step of f from a point of K stays in K",
				"and f's two orders agree at the points of K")
			start, closed, commutesInK := parts[0], parts[1], parts[2]

			fGuarded, guardedDef := a.LetAs[Fun2[A, B, B]]("f'", "λx:A. λz:B. COND(z ∈ K, f(x, z), z)")
			guarded := a.Have(
				"f' steps by f from a point of K and stands still anywhere else",
				"∀x:A. ∀z:B. f'(x, z) = COND(z ∈ K, f(x, z), z)",
				By(Normalized, guardedDef))

			commutes := a.Have(
				"f' left-commutes everywhere, inside K or not",
				"∀x y:A. ∀z:B. x ≠ y ⇒ f'(x, f'(y, z)) = f'(y, f'(x, z))",
				Derive(func(a *Argument) {
					x := a.FixAs[A]("x")
					y := a.FixAs[A]("y")
					z := a.FixAs[B]("z")
					distinct := a.Assume()
					a.Cases(a.Term("z ∈ K"))
					a.When(
						"z ∈ K: either order is two steps of f through K, and f's orders agree there",
						func(a *Argument, inK Fact) {
							stepsStay := a.Have(
								"one step of f from z stays in K, at x and at y alike",
								"f(x, z) ∈ K ∧ f(y, z) ∈ K",
								By(inK, closed))
							a.Show(
								"so, unfolding f', both orders are f's, which agree",
								guardedDef.Rw(),
								By(inK, stepsStay, distinct, commutesInK.At(x, y, z)))
						})
					a.Otherwise(
						"z ∉ K: neither order moves z",
						func(a *Argument, outside Fact) {
							a.Show(
								"f' stands still at z, whichever point it takes",
								By(Normalized, outside, guarded.At(x, z), guarded.At(y, z)))
						})
				}))

			recursion := a.Have(
				"so FiniteRecursion applies to f', and its fold has the two clauses",
				"set_fold(f', ∅, b) = b ∧ "+
					"(∀x:A. ∀s:set(A). "+
					"    finite(s) ⇒ "+
					"    set_fold(f', insert(x, s), b) = COND(x ∈ s, set_fold(f', s, b), f'(x, set_fold(f', s, b))))",
				By(commutes, FiniteRecursion.At(fGuarded, b)))
			clauses := a.Conjuncts(
				recursion,
				"the fold of f' starts at b",
				"and takes one step of f' at each fresh point of a finite set")
			foldEmpty, foldInsert := clauses[0], clauses[1]

			stays := a.Have(
				"that fold never leaves K on a finite set",
				"∀s:set(A). finite(s) ⇒ set_fold(f', s, b) ∈ K",
				Derive(func(a *Argument) {
					a.FixAs[Set[A]]("s")
					finite := a.Assume()
					a.Show(
						"by induction on the finite set s",
						ByInduction(finite_set.FiniteInductFresh, finite,
							Case(
								"∅: the fold has not moved from b, which lies in K",
								By(Normalized, foldEmpty, start)),
							Case(
								"insert: a fresh point costs one step of f' from a point of K, a step of f, which stays in K",
								Derive(func(a *Argument) {
									x := a.FixAs[A]("x")
									u := a.FixAs[Set[A]]("u")
									carried := a.Assume() // the fold over u lies in K, x ∉ u, and u is finite
									fold := a.TermAs[B]("set_fold(f', u, b)")
									step := a.Have(
										"the fold over insert(x, u) is one step of f from the fold over u",
										"set_fold(f', insert(x, u), b) = f(x, set_fold(f', u, b))",
										CalcEq(
											Leg(
												a.Term("f'(x, set_fold(f', u, b))"),
												"x is fresh, so the fold steps once by f'",
												By(carried, foldInsert.At(x, u))),
											FinalLeg(
												"and the fold over u lies in K, where f' is f",
												By(carried, guarded.At(x, fold)))))
									a.Show(
										"and a step of f from a point of K stays in K",
										step.Rw(),
										By(carried, closed.At(x, fold)))
								}))))
				}))

			meets := a.Have(
				"so the fold of f' takes f's own step at each fresh "+
					"point: it steps from a point of K, where f' is f",
				Statement{
					Binders: "∀x:A. ∀s:set(A).",
					Hypotheses: []string{
						"finite(s)",
					},
					Conclusion: "set_fold(f', insert(x, s), b) = " +
						"COND(x ∈ s, set_fold(f', s, b), f(x, set_fold(f', s, b)))",
				},
				Derive(func(a *Argument) {
					x := a.FixAs[A]("x")
					s := a.FixAs[Set[A]]("s")
					finite := a.Assume()
					fold := a.TermAs[B]("set_fold(f', s, b)")
					atFold := a.Have(
						"the fold over s lies in K, so f' is f there",
						"f'(x, set_fold(f', s, b)) = f(x, set_fold(f', s, b))",
						By(finite, stays.At(s), guarded.At(x, fold)))
					a.Show(
						"so f's step at x is the one the fold of f' takes",
						atFold.RwRev(),
						By(finite, foldInsert.At(x, s)))
				}))

			a.Have(
				"so some fold has f's own clauses: the fold of f'",
				"∃g:(set(A) → B). "+
					"    g(∅) = b ∧ (∀x:A. ∀s:set(A). finite(s) ⇒ g(insert(x, s)) = COND(x ∈ s, g(s), f(x, g(s))))",
				Derive(func(a *Argument) {
					a.Take(a.Term("λs:set(A). set_fold(f', s, b)"))
					a.Show(
						"it starts at b and takes f's step at each fresh point",
						By(foldEmpty, meets))
				}))

			// set_fold(f, ·, b) is a choice among the folds with f's
			// clauses; the existence just shown is the ε-axiom's premise,
			// consumed from the context, so the unfold closes.
			a.Show(
				"and set_fold(f, ·, b) is chosen among those folds, so it is one of them",
				Unfold(SetFoldDef))
		}),
})}

// FoldOfAgreeingStepsWithin — two steps agreeing on the indices of s,
// each closed and left-commutative on K, fold alike over s from a
// start in K.
//
// K is spent once, at the start. Each step is closed and
// left-commutative on K, and both folds start in K, so
// FiniteRecursionWithin gives each fold its two clauses — and those
// clauses speak of every finite set, with K nowhere in them.
//
// The induction then runs on the set, at the property "if f and g agree
// on THIS set, their folds of it are equal". The agreement has to be
// carried inside the property rather than assumed once outside: it is a
// statement about the set, so it changes as the set grows, and the sets
// the induction passes through are not subsets of s — each arrives with
// an agreement of its own.
//
// The fresh induction supplies what the step needs and nothing more:
// the point laid in is outside the set it is laid into, which is what
// decides the recursion clause's conditional, and that set is finite,
// which is what the clause asks for. Both folds then take their step at
// the new point; the agreement there splits off from the agreement on
// the rest, which is what the induction hypothesis consumes to equate
// the two values the steps are applied to. At ∅ neither fold has been
// given anything to do, and both are the value they started at.
var FoldOfAgreeingStepsWithin = foldOfAgreeingStepsWithinThm{family.Add(registry.ProofEntry{
	Name: "FoldOfAgreeingStepsWithin",
	Key:  "prop_172122f1994ab0b4",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀f g:(A → B → B). ∀b:B. ∀K:set(B).",
		Hypotheses: []string{
			"finite(s)",
			"b ∈ K",
			"∀x:A. x ∈ s ⇒ f(x) = g(x)",
			"∀x:A. ∀z:B. z ∈ K ⇒ f(x, z) ∈ K",
			"∀x y:A. ∀z:B. x ≠ y ∧ z ∈ K ⇒ f(x, f(y, z)) = f(y, f(x, z))",
			"∀x:A. ∀z:B. z ∈ K ⇒ g(x, z) ∈ K",
			"∀x y:A. ∀z:B. x ≠ y ∧ z ∈ K ⇒ g(x, g(y, z)) = g(y, g(x, z))",
		},
		Conclusion: "set_fold(f, s, b) = set_fold(g, s, b)",
	},
		func(a *Argument, s *Expr[Set[A]], f, g *Arrow2[A, B, B], b *Expr[B], K *Expr[Set[B]], given Fact) {
			// Each fold is well defined for its own reason, so the two
			// recursions are read apart: below, each fold is computed by
			// its own clauses only.
			fClauses := a.Conjuncts(
				a.Have(
					"f is closed and left-commutative on K, which holds b, so its fold has the recursion's two clauses",
					"set_fold(f, ∅, b) = b ∧ "+
						"(∀x:A. ∀t:set(A). "+
						"    finite(t) ⇒ "+
						"    set_fold(f, insert(x, t), b) = COND(x ∈ t, set_fold(f, t, b), f(x, set_fold(f, t, b))))",
					By(given, FiniteRecursionWithin.At(f, b, K))),
				"f's fold starts at b",
				"and takes one step of f at each fresh point of a finite set")
			fStart, fInsert := fClauses[0], fClauses[1]
			gClauses := a.Conjuncts(
				a.Have(
					"and so is g, so its fold has them too",
					"set_fold(g, ∅, b) = b ∧ "+
						"(∀x:A. ∀t:set(A). "+
						"    finite(t) ⇒ "+
						"    set_fold(g, insert(x, t), b) = COND(x ∈ t, set_fold(g, t, b), g(x, set_fold(g, t, b))))",
					By(given, FiniteRecursionWithin.At(g, b, K))),
				"g's fold starts at b",
				"and takes one step of g at each fresh point of a finite set")
			gStart, gInsert := gClauses[0], gClauses[1]

			// The property the induction is run on: it carries the
			// agreement as its own hypothesis, so that every set the
			// induction passes through arrives with one.
			agreeingFolds := a.TermAs[Set[Set[A]]](
				"λu:set(A). (∀x:A. x ∈ u ⇒ f(x) = g(x)) ⇒ set_fold(f, u, b) = set_fold(g, u, b)")

			a.Show(
				"so the property reaches every finite set, and s is one of them",
				ByInduction(finite_set.FiniteInductFresh.At(agreeingFolds, s),
					// `given` supplies the finiteness the principle's own
					// guard asks for and the agreement on s.
					given,
					Case(
						"at ∅ neither fold has been given anything to do, so both are b",
						By(Normalized, fStart, gStart)),
					Case(
						"across an enlargement the new point is known absent, so both folds take their step at it",
						Derive(func(a *Argument) {
							x := a.FixAs[A]("x")
							// The principle's own set binder is `s`, which the
							// section holds — so the set laid into is NAMED.
							t := a.FixAs[Set[A]]("t")
							carried := a.Assume() // the property at t, x ∉ t, and finite(t)
							agree := a.Assume()   // f and g agree on insert(x, t)

							split := a.Have(
								"the agreement on the enlarged set is agreement at x together with agreement on t",
								"f(x) = g(x) ∧ (∀y:A. y ∈ t ⇒ f(y) = g(y))",
								By(agree, set_basic.InInsert))
							inner := a.Have(
								"so the property does apply at t, and the two folds of t are one value",
								"set_fold(f, t, b) = set_fold(g, t, b)",
								By(split, carried))

							// x ∉ t settles the insert clause's conditional,
							// and finite(t) is what the clause asks for: both
							// are in `carried`.
							stepF := a.Have(
								"f's fold of the enlarged set is one step of f on f's fold of t",
								"set_fold(f, insert(x, t), b) = f(x, set_fold(f, t, b))",
								By(carried, fInsert.At(x, t)))
							stepG := a.Have(
								"and g's fold of it is one step of g on g's fold of t",
								"set_fold(g, insert(x, t), b) = g(x, set_fold(g, t, b))",
								By(carried, gInsert.At(x, t)))

							a.Show(
								"and those two steps agree: the same step at x, applied to the same value",
								By(stepF, stepG, inner, split))
						})),
				))
		}),
})}

// FoldOfAgreeingSteps — a fold reads its step function only at the
// points of the set it folds, so two steps that agree on those points
// fold the set to the same value, whatever either of them does
// elsewhere.
//
// Both steps are asked to commute. That is not a convenience of the
// proof: it is what makes either fold well defined at all, so neither
// side of the equation says anything without it.
//
// It is FoldOfAgreeingStepsWithin read at K = 𝕌: every start lies in 𝕌
// and every step stays there, and a step that commutes everywhere
// commutes at the points of 𝕌.
var FoldOfAgreeingSteps = foldOfAgreeingStepsThm{family.Add(registry.ProofEntry{
	Name: "FoldOfAgreeingSteps",
	Key:  "prop_928aa416bfd1dddb",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f g:(A → B → B). ∀b:B.",
			Hypotheses: []string{
				"finite(s)",
				"∀x:A. x ∈ s ⇒ f(x) = g(x)",
				"∀x y:A. ∀z:B. x ≠ y ⇒ f(x, f(y, z)) = f(y, f(x, z))",
				"∀x y:A. ∀z:B. x ≠ y ⇒ g(x, g(y, z)) = g(y, g(x, z))",
			},
			Conclusion: "set_fold(f, s, b) = set_fold(g, s, b)",
		},
		func(a *Argument, s *Expr[Set[A]], f, g *Arrow2[A, B, B], b *Expr[B], given Fact) {
			everything := a.TermAs[Set[B]]("𝕌")
			a.Show(
				"within 𝕌 every start and every step lies inside, and "+
					"commuting everywhere is commuting there, so the folds agree",
				By(given, FoldOfAgreeingStepsWithin.At(s, f, g, b, everything), set_basic.InUniv))
		}),
})}

// CardClauses — how a count reacts to the two ways of naming a set: the
// empty set has none, and putting an element into a set raises the
// count by one, unless the element was already in it.
//
// card is the fold that forgets the element and adds one, started at 0,
// so these are FiniteRecursion's own clauses read at that step — one
// instance, nothing more. What an instance costs is the side condition,
// and here it costs nothing: a step that ignores its element cannot
// tell in which order two of them arrived, so both orders reduce to
// adding one twice.
var CardClauses = cardClausesThm{family.Add(registry.ProofEntry{
	Name: "CardClauses",
	Key:  "prop_58edfd62c7397e0d",
	Build: family.Theorem(
		"card(∅) = 0 ∧ "+
			"(∀x:A. ∀s:set(A). finite(s) ⇒ card(insert(x, s)) = COND(x ∈ s, card(s), suc(card(s))))",
		func(a *Argument) {
			// The step card folds with: one more, whoever the element was.
			addOne := a.Term("λx:A. λn:num. suc(n)")

			a.Do(Unfold(CardDef)) // ↦ both clauses stated of set_fold(addOne, ·, 0)

			// The step is the only witness given. Its slot is the one the
			// closer could not have filled: a function variable it has no
			// way to invent, where the set, the start and the element are
			// first-order and match off the goal. The side condition
			// disappears when the close β-reduces the two applications of
			// addOne to the same suc(suc(·)), which is this proof's one
			// piece of arithmetic. Both clauses then fall out of the one
			// instance.
			a.Show(
				"so both clauses are the recursion's own, read at the step that adds one",
				By(At(FiniteRecursion, addOne)))
		}),
})}

// ---------------------------------------------------------------------------
// The counting calculus
// ---------------------------------------------------------------------------
//
// the counting calculus: what a count does at ∅, at a point added or
// removed, and across a disjoint union.
//
// The part above gives card its two clauses; these members spend them.
// They are one arc, from what a count can say about a set to what it
// says about a construction.
//
// A count is a lossy summary: how many elements there are says almost
// nothing about which ones. At a single value it says everything, and
// that is where the arc starts — counted 0 pins a set down to ∅, and
// read against that same value as a bound, counting anything at all is
// holding a point. Then the smallest computation, a one-point set, and
// after it the recursion clause read forwards and backwards: what a new
// element costs when it is put in, and what one already there is worth
// when it is taken out.
// And then the step that changes the subject: laid alongside a set it
// shares nothing with, a set costs exactly what it costs alone. That is
// the first statement in the chapter where counting becomes ARITHMETIC
// — the count of a construction as an expression in the counts of its
// parts — and disjointness is precisely the price of the `+`.
//
// Alongside the arc sit statements of another sort. They are not a list
// to be counted but a handful of kinds. One PROJECTS the counting clause,
// whose answer at an insertion is conditional on whether the element
// was already there: InsertCountsOneMore takes the branch where it was
// not — and CountsOneMore, which reads a count off a deletion, is that
// same statement taken at a remainder rather than a second projection.
// Two say how a count SPLITS: countsSubsetAndRest at a whole subset,
// countsLeftAndSurplus at a union's left operand. One splits nothing —
// countsAtLeastOne reads the count against the set in the other
// direction, turning a bound on the number into a point of the set. And
// one BOUNDS instead of computing: InsertCountsAtMostOneMore keeps both
// branches of the insertion clause and holds each against the bound,
// which is what a consumer that only needs "no more than" wants. Each is
// a clause or a law of this file spent into the shape the rest of the
// chapter reads it in. The entries below are in dependency order, which
// is where each of them falls out — nothing here refers to anything
// declared under it.

// CardEqZero — a finite set is counted 0 exactly when it is empty.
//
// One direction is card's own first clause read along an equation, and
// spends no finiteness at all.
//
// The other direction carries the content, and it is an induction that
// never uses its hypothesis. The property carried is "counting 0 forces
// emptiness", and it survives an insertion vacuously: a set just
// enlarged by an element it did not already hold counts one more than
// something, and no successor is 0, so the property's antecedent never
// arises and there is nothing left to conclude. What the induction
// actually supplies is only that every finite set is reached from ∅ by
// such insertions — and the strong rule is what grants that the element
// inserted is new, which is exactly the side condition card's recursion
// clause turns on.
//
// Two things a reader might expect never appear in the premise lists
// below. The induction hypothesis is one. That an insertion is a
// nonempty set is the other — the count rules an insertion out before
// emptiness is ever consulted, so no law about insert and ∅ is needed
// and none is claimed.
var CardEqZero = cardEqZeroThm{family.Add(registry.ProofEntry{
	Name: "CardEqZero",
	Key:  "prop_67fdad36030b4a6c",
	Build: family.Sections(
		Statement{
			Binders: "∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "card(s) = 0 ⇔ s = ∅",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// insertCountsNonzero — putting into a finite set an element it
			// does not already hold leaves it counted above 0.
			//
			// card's recursion clause is conditional on membership: it
			// leaves the count alone when the element is already there and
			// raises it by one otherwise. The hypothesis picks the second
			// branch, so the count is a successor, and no successor is 0.
			insertCountsNonzero := ctx.Lemma(
				Statement{
					Binders: "∀x:A. ∀t:set(A).",
					Hypotheses: []string{
						"x ∉ t",
						"finite(t)",
					},
					Conclusion: "¬(card(insert(x, t)) = 0)",
				},
				func(a *Argument, x, t Term, fresh Fact) {
					a.Show(
						"the recursion counts up by one at an element the set did not have, and 0 is no successor",
						// card(insert(x, t)) = COND(x ∈ t, card(t), suc(card(t)))
						// once t is finite, and x ∉ t picks the right branch.
						// The clauses bind the point before the set, so the
						// witnesses read (x, t).
						By(fresh, At(CardClauses, x, t), peano.SucNotZero))
				})

			return ctx.Theorem(headline, func(a *Argument, s Term, finite Fact) {
				a.Iff()
				a.Forward(
					"and no other set does — by induction over the finite "+
						"sets, at the property that counting 0 forces emptiness",
					func(b *Argument, counted Fact) {
						// The property the induction carries, written once.
						onlyEmptyCountsZero := b.Ctx().TermText("λu:set(A). card(u) = 0 ⇒ u = ∅")

						// The principle is spent by a plain `By` here and by
						// `ByInduction` in CardUnion below. The verb needs its
						// case obligations to survive prenex normalization as
						// first-order clauses, and this property carries a SET
						// EQUALITY (`u = ∅`) — which normalization spreads
						// pointwise, doubling each obligation into
						// quantifier-alternating clauses the refuter will not
						// apply. Naming the one fact the induction spends is
						// both the way round it and the shorter proof.
						b.Show(
							"trivial at ∅, vacuous at an insertion whose count is "+
								"already above 0 — so it reaches s and reads off its count",
							// The lemma stays UNGROUND: the element and the
							// set its step speaks of are the induction's own,
							// and nothing here names them.
							By(finite, counted, insertCountsNonzero, At(finite_set.FiniteInductFresh, onlyEmptyCountsZero, s)))
					})
				a.Backward(
					"a set that IS ∅ counts 0, and this half spends no finiteness",
					func(b *Argument, empty Fact) {
						b.Show(
							"card's zero clause carried to s along the equation that says s is ∅",
							By(Normalized, empty, CardClauses))
					})
			})
		}),
})}

// countsAtLeastOne — a finite set counts at least one exactly when it
// has a point.
//
// CardEqZero read against a bound rather than against a value. That
// changes nothing about what is known and everything about what can be
// done with it: a proof that has just bounded a count from below is
// holding a NUMBER, and what it wants next is a POINT. This is the step
// across, and all three members of maps.go that take it take it
// here.
//
// Neither half of the crossing is set-theoretic on its own. On the
// number side, at least one, positive, and not zero are one condition,
// and the two laws relating those three faces are all this member
// borrows from outside the set layer. On the set side, counted 0 is
// being empty and being empty is having no point — CardEqZero met with
// the parent chapter's emptiness law. Finiteness is asked once, by
// CardEqZero, and for nothing else: an infinite set's count says
// nothing about its points.
//
// Stated at card and nowhere wider. Taking a point out of a set known
// to be non-empty is already routine — the has_size part does it at two
// sites, from the emptiness law directly — so what is new here is the
// bridge from the COUNT, and only that is stated.
var countsAtLeastOne = countsAtLeastOneThm{family.Add(registry.ProofEntry{
	Name: "countsAtLeastOne",
	Key:  "prop_100da639498f71a6",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "1 ≤ card(s) ⇔ ∃x:A. x ∈ s",
		},
		func(a *Argument, s Term, finite Fact) {
			count := ops(a.Ctx()).Card.Apply(s)

			// Four equivalences laid end to end, so nothing here is
			// refutation: `Normalized` is what composes them, and the `By`
			// diagnostic says as much — without it the same five premises
			// fall through to the refuter on a leaf one Basic() settles.
			a.Show(
				"at least one, positive and not zero are one condition, and "+
					"the finite set counted zero is the one with no point in it",
				By(
					Normalized,
					finite,
					// Bare, where every other premise here is ground, and
					// measured that way: handed the count as a witness it
					// does not materialize. It is also the one premise whose
					// statement the goal's own left side already matches.
					nat_order.OneLessEqIffPos,          // 1 ≤ card(s) ⇔ 0 < card(s)
					At(nat_order.PosIffNonzero, count), // card(s) ≠ 0 ⇔ 0 < card(s)
					At(CardEqZero, s),                  // card(s) = 0 ⇔ s = ∅
					At(set_basic.MemberNotEmpty, s)))   // (∃x. x ∈ s) ⇔ ¬(s = ∅)
		}),
})}

// CardSing — a one-point set has one element.
//
// The smallest thing the recursion computes, and the first member that
// uses the clauses to produce a number rather than to characterize one.
// A one-point set is the empty set with that point laid into it, so the
// insertion clause applies at exactly one step. Its side condition asks
// that the set stepped from be finite, and here that set is ∅, which is
// the one finiteness rule carrying no premise of its own. Its answer is
// conditional on whether the point was already present, and nothing is
// present in ∅, so the count rises rather than stays — off the zero the
// other clause gives, to the successor of zero. That successor is the
// numeral, since 1 is what suc(0) is written as.
var CardSing = cardSingThm{family.Add(registry.ProofEntry{
	Name: "CardSing",
	Key:  "prop_d1db230d2de9c725",
	Build: family.Theorem("∀a:A. card({a}) = 1",
		func(arg *Argument, a Term) {
			// ∅ is nullary, so it has no argument to read an element type
			// from and is pinned at the build site; `{a}` is that same ∅
			// with a laid in, and the statement spells it.
			empty := setvocab.Pinned(arg.Ctx(), "empty_set")

			// `Normalized` is not decoration here, it is the entire close:
			// the clauses arrive with their side conditions spread into
			// disjunctions and the empty count written the other way round,
			// and straightening that out settles the leaf outright. Drop it
			// and the same four premises no longer meet.
			arg.Show(
				"laying a into ∅ steps the count up by one, and one step up from none is the numeral",
				By(
					Normalized,
					// card({a}) = COND(a ∈ ∅, card(∅), suc(card(∅))), together
					// with card(∅) = 0 — one instance, named at the point and
					// at the set it is laid into, carries both clauses.
					At(CardClauses, a, empty),
					// finite(∅), the insertion clause's side condition. Bare
					// because the conjunct read binds nothing: witnesses here
					// would name an instance of the enlargement rule beside
					// it, which this proof never reaches for.
					finite_set.FiniteRules,
					// a ∉ ∅ — the point is not already there, so the COND
					// takes its counting branch rather than leaving the count
					// alone.
					At(set_basic.NotInEmpty, a),
					// 1 = suc(0), which is the count just arrived at.
					nat_arith.OneIsSucZero))
		}),
})}

// InsertCountsOneMore — putting into a finite set an element it does
// not already hold raises the count by exactly one.
//
// Exported: the listing correspondence (sets/listing) counts
// a list's set by laying its head into the set of its tail, which is
// exactly this law, and a theorem cited across a family boundary is
// chapter API (constitution §"Inventory and names").
//
// The counting clause answers at an insertion with a CONDITION: the
// count stays where it was if the element was already present, and
// rises by one if it was not. A proof that has just laid in a point the
// set did not have knows which side of that condition it is on before
// it asks, and what it wants back is that side alone, as an equation.
// This is that side, projected once and not re-derived. A proof that
// does NOT know stays with the clause and should — CardImageLe splits
// on exactly this condition, and reads both answers off it.
//
// CountsOneMore below is this statement read at a REMAINDER: hand it
// the set a deletion leaves and the enlargement it counts is the
// original set back again. So the deletion direction is not a second
// projection of the clause but a consequence of this one. Between them
// they are the whole of what the clause has to say about a count that
// changes, and this is the only end of the pair that touches the clause
// at all.
//
// The proof is that projection and nothing besides. The finiteness is
// what the clause asks of the set stepped at, and it is asked for
// nothing else.
var InsertCountsOneMore = insertCountsOneMoreThm{family.Add(registry.ProofEntry{
	Name: "InsertCountsOneMore",
	Key:  "prop_4cdf57c80b136d8b",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀x:A.",
			Hypotheses: []string{
				"finite(s)",
				"x ∉ s",
			},
			Conclusion: "card(insert(x, s)) = suc(card(s))",
		},
		func(a *Argument, s, x Term, given Fact) {
			a.Show(
				"the clause read at this point and this set, in the branch the hypothesis picks",
				// card(insert(x, s)) = COND(x ∈ s, card(s), suc(card(s)))
				// once s is finite. The clauses bind the point before the
				// set, so the witnesses read (x, s).
				By(given, At(CardClauses, x, s)))
		}),
})}

// CountsOneMore — a finite set counts one more than what remains when
// one of its members is removed.
//
// This is InsertCountsOneMore above, read at the remainder: a set is
// its own remainder with the member put back, so the enlargement that
// law counts IS the set, and the count it raises is the remainder's.
// Nothing about the recursion is re-derived here and the counting
// clause is not consulted at all. What is left to check is the two
// halves of "the deletion really did remove it" — the remainder does
// not hold the member, and inserting it returns the set — which are
// exactly what the insertion law asks of its own set and what carries
// its answer back to s.
//
// Stated as a SUCCESSOR rather than as a difference, and that is the
// reason it exists apart from CardDelete below, which states the same
// computation in truncated subtraction. Subtraction says as much only
// once the set is known to hold something, so every consumer that
// wants to count upwards would have to argue back from `n - 1` to a
// successor. Stating the successor form once means CardDelete makes
// that conversion in the single place where the difference is wanted,
// and the size clauses of the has_size part make it nowhere.
var CountsOneMore = countsOneMoreThm{family.Add(registry.ProofEntry{
	Name: "CountsOneMore",
	Key:  "prop_d9456f0394c489e0",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀a:A.",
			Hypotheses: []string{
				"finite(s)",
				"a ∈ s",
			},
			Conclusion: "card(s) = suc(card(delete(s, a)))",
		},
		func(arg *Argument, s, a Term, given Fact) {
			rest := ops(arg.Ctx()).Delete.Apply(s, a) // what is left of s once a goes

			arg.Show(
				"s is the remainder, finite and without a, with a put back, and that costs the count exactly one",
				// The law that rebuilds s states an equality of SETS and the
				// count has to be carried across it — `vocab.go`'s pointwise
				// fold. Checked by removal: without `Normalized` these same
				// five premises do not meet at all.
				By(
					Normalized,
					given,
					finite_set.FiniteDelete,
					At(set_basic.InDelete, s, a, a),
					At(set_algebra.InsertDelete, s, a), // a ∈ s ⇒ insert(a, delete(s, a)) = s
					At(InsertCountsOneMore, rest, a)))  // card(insert(a, rest)) = suc(card(rest))
		}),
})}

// InsertCountsAtMostOneMore — laying a point into a finite set raises
// the count by at most one, whether or not the point is new.
//
// InsertCountsOneMore above says by exactly how much, and pays for the
// exactness by having to be told that the point was not already there.
// A counting induction is rarely in a position to say so: the point it
// lays in arrives from wherever the induction found it, and whether the
// set already holds it is not something the induction controls. Such a
// proof carries a bound and wants a bound back, and for that the
// inexact answer is the usable one — this is the form a count that
// grows one point at a time is actually bounded in.
//
// So the proof does not assume the condition away, it splits on it, and
// the counting clause answers on both sides of the split. Neither side
// computes: one reads the count unchanged and the other reads it one
// higher, and each answer is then held against the bound by the order
// law that fits it.
//
// Finiteness takes no part in that split — a set does not stop being
// finite for one more point and does not ask whether it already had it
// — so the conjunction is separated first and its finiteness half
// settled once, for both branches at once.
var InsertCountsAtMostOneMore = insertCountsAtMostOneMoreThm{family.Add(registry.ProofEntry{
	Name: "InsertCountsAtMostOneMore",
	Key:  "prop_763e70ca74c8d4fd",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀x:A. ∀n:num.",
			Hypotheses: []string{
				"finite(s)",
				"card(s) ≤ n",
			},
			Conclusion: "finite(insert(x, s)) ∧ card(insert(x, s)) ≤ suc(n)",
		},
		func(a *Argument, s, x, n Term, given Fact) {
			count := ops(a.Ctx()).Card.Apply(s)

			// Nothing below is a refutation. Every premise here is an
			// equivalence or an equation and every close lays them against
			// a hypothesis, so all three leaves settle without the refuter,
			// and the member records no refuter key at all.
			a.Do(SplitConj(
				Case(
					"finiteness is unconditional: one more point cannot make a finite set infinite",
					// finite(insert(x, s)) ⇔ finite(s), whose right side the
					// antecedent already holds. The point is a witness here
					// and never a case: the equivalence says nothing about
					// whether s was holding it.
					By(given, At(finite_set.FiniteInsert, x, s))),

				Case(
					"the count is where the two answers part, so split on whether the point was already there",
					ByCaseStep(a.Term("x ∈ s"),

						Case(
							"x ∈ s: the clause leaves the count where it was",
							Given(func(b *Argument, member Fact) {
								b.Show(
									"so the bound it was under carries over, one step wider than it needs to be",
									By(
										Normalized,
										member,
										given,
										// card(insert(x, s)) = COND(x ∈ s, card(s), suc(card(s)))
										// once s is finite — the clause's answer at
										// this point and this set, condition and all.
										At(CardClauses, x, s),
										// card(s) ≤ suc(n) ⇔ card(s) ≤ n ∨ card(s) = suc(n),
										// whose left disjunct is the antecedent's bound.
										At(nat_order.LessEqSucClause, count, n)))
							})),

						Case(
							"x ∉ s: the clause raises the count by one",
							Given(func(b *Argument, fresh Fact) {
								b.Show(
									"and suc carries the bound up beside it, so the raised count is under the raised bound",
									By(
										Normalized,
										fresh,
										given,
										// The same clause, read in its other branch.
										At(CardClauses, x, s),
										// suc(card(s)) ≤ suc(n) ⇔ card(s) ≤ n — the
										// antecedent's bound, one step up on both sides.
										At(nat_order.SucLessEqSucIff, count, n)))
							})),
					)),
			))
		}),
})}

// CardDelete — removing an element from a finite set costs the count
// exactly one when the set held it, and nothing when it did not.
//
// The two branches are not two cases of one argument. Where the set
// held the element, the count is settled already by CountsOneMore
// above, and the only work left is arithmetic: this member states the
// cost as a difference, and one taken back off a successor returns what
// that successor succeeds. Where the set never held it, there is no
// recursion at all — the deletion is the identity, and equal sets count
// the same.
//
// No induction either way, and no finiteness spent in the second
// branch: a set that does not hold x loses nothing when x is deleted
// however large it is.
var CardDelete = cardDeleteThm{family.Add(registry.ProofEntry{
	Name: "CardDelete",
	Key:  "prop_12501ae1fb474b0d",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀x:A.",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "card(delete(s, x)) = COND(x ∈ s, card(s) - 1, card(s))",
		},
		func(a *Argument, s, x Term, finite Fact) {
			rest := ops(a.Ctx()).Delete.Apply(s, x) // what is left of s once x goes

			a.Cases(a.Term("x ∈ s"))
			a.When(
				"x ∈ s: the count above the remainder is settled, and only the subtraction is left",
				func(b *Argument, member Fact) {
					oneMore := b.Have(
						"so s counts one more than its remainder — x is there to be "+
							"taken out, which is all that is asked beyond the finiteness",
						"card(s) = suc(card(delete(s, x)))",
						By(finite, member, At(CountsOneMore, s, x)))

					// The count the successor law is read at, and the
					// quantity the theorem states.
					restCount := ops(b.Ctx()).Card.Apply(rest)
					b.Show(
						"and taking that one back off a successor returns what it succeeds",
						// `oneMore` and the successor law are both
						// EQUATIONS between counts, and closing here means
						// composing them into the branch the membership
						// picks — rewriting, not refutation: `vocab.go`'s
						// fold at an equation rather than at a set law.
						// Checked by removal: without
						// `Normalized` these facts reach the refuter
						// instead.
						By(
							Normalized,
							oneMore,
							member,
							At(nat_monus.SucSubOne, restCount))) // suc(card(rest)) - 1 = card(rest)
				})
			a.Otherwise(
				"x ∉ s: the deletion returns s itself, so the count has nothing to lose",
				func(b *Argument, absent Fact) {
					b.Show(
						"removing an element a set never held leaves the set, and equal sets count the same",
						// x ∉ s ⇔ delete(s, x) = s — an installed set
						// law, so `vocab.go`'s pointwise fold applies.
						// Checked by removal: without `Normalized` the
						// two premises do not meet.
						By(Normalized, absent, At(set_algebra.DeleteNonElement, s, x)))
				})
		}),
})}

// CardUnion — two finite sets that share no element are counted by
// adding their counts.
//
// Induction on the left set, at the property "laid alongside t, this
// set's count adds". The strong rule is what the argument needs and
// all it needs: at the step it grants that the element being added is
// outside the set it is added to, and that that set is already finite
// — which are exactly the two things the insertion law asks before it
// will raise a count, and the first does double duty as half of the
// disjointness bookkeeping.
//
// Only the base case reads the counting clause, for the count at ∅;
// both counts the step raises are the insertion law, once over the
// union and once over the left set alone. Which branch of the clause
// applies is therefore never argued here — it is settled inside the law.
//
// The property carries the disjointness as its own hypothesis rather
// than assuming it once outside. It has to: the induction walks the
// left set down to ∅, and each smaller set inherits a disjointness of
// its own that the next case has to be handed.
var CardUnion = cardUnionThm{family.Add(registry.ProofEntry{
	Name: "CardUnion",
	Key:  "prop_3da3b124a50047b3",
	Build: family.Sections(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
				"s ∩ t = ∅",
			},
			Conclusion: "card(s ∪ t) = card(s) + card(t)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// What an enlarged set passes back to the set it grew out
			// of. Both halves are about the constructors alone — neither
			// a count nor a finiteness appears — so the set driver is the
			// complete method here, and they are proved together because
			// the step consumes them together.
			//
			// The second half is what the induction cannot do without:
			// the property being carried is a statement ABOUT a
			// disjointness, so every smaller set must arrive with one of
			// its own. The first half is what upgrades "x is new to s"
			// to the "x is new to s ∪ t" a counting clause asks for, and
			// it is the only place the disjointness is spent.
			disjointDescends := ctx.Lemma(
				Statement{
					Binders: "∀s t:set(A). ∀x:A.",
					Hypotheses: []string{
						"insert(x, s) ∩ t = ∅",
						"x ∉ s",
					},
					Conclusion: "x ∉ s ∪ t ∧ s ∩ t = ∅",
				},
				BySets())

			return ctx.Theorem(headline, func(a *Argument, s, t Term, finiteS, finiteT, disjoint Fact) {
				union := ops(a.Ctx()).Union

				a.Show(
					"so the property reaches every finite set, and s is one of them",
					ByInduction(finite_set.FiniteInductFresh, finiteS, Generalizing(disjoint),
						Case(
							"∅ contributes nothing to count: the union is t itself, and 0 heads the sum",
							By(
								Normalized,
								At(set_algebra.UnionEmpty, t), // ∅ ∪ t = t
								CardClauses,                   // card(∅) = 0, the clause that binds nothing
								nat_arith.Add)),               // 0 + n = n

						Case(
							"one more element on the left is one more on both counts, because it is new to the union too",
							Derive(func(b *Argument) {
								// The principle's own set binder is `s`, which the
								// section holds — so the induction set is NAMED.
								x, u := b.Fix(), b.Fix("u")
								carried := b.Assume()       // the property at u, x ∉ u, and finite(u)
								grownDisjoint := b.Assume() // insert(x, u) ∩ t = ∅
								join := union.Apply(u, t)

								inherited := b.Have(
									"the smaller set is disjoint from t in its turn, and x lies outside their union",
									"x ∉ u ∪ t ∧ u ∩ t = ∅",
									By(grownDisjoint, carried, disjointDescends))

								counted := b.Have(
									"so the property does apply at u, and the joint count is settled there",
									"card(u ∪ t) = card(u) + card(t)",
									By(inherited, carried))

								enlarged := b.Have(
									"and x raises the joint count by one, lying outside a union that is finite",
									"card(insert(x, u) ∪ t) = suc(card(u ∪ t))",
									// The insertion law asks that the set stepped at be
									// finite and that x be new to it: `inherited` is what
									// says x is new to the union, and the union's
									// finiteness is assembled from finite(t) and
									// finite(u) in `carried`.
									By(
										Normalized,
										finiteT,
										inherited,
										carried,
										At(set_algebra.InsertUnionEq, u, t, x), // insert(x, u ∪ t) = insert(x, u) ∪ t
										At(finite_set.FiniteUnionImp, u, t),    // finite(u) ∧ finite(t) ⇒ finite(u ∪ t)
										At(InsertCountsOneMore, join, x)))      // card(insert(x, u ∪ t)) = suc(card(u ∪ t))

								b.Show(
									"while the left count rises by one for the same reason, "+
										"and one carried out of a sum is the recursion equation of +",
									// The same law over the left set alone, where both
									// its hypotheses are `carried`'s own.
									By(
										Normalized,
										counted,
										enlarged,
										carried,
										At(InsertCountsOneMore, u, x), // card(insert(x, u)) = suc(card(u))
										nat_arith.Add))                // suc(m) + n = suc(m + n)
							})),
					))
			})
		}),
})}

// countsSubsetAndRest — a finite set's count splits at any subset into
// that subset's count and the count of what the subset leaves.
//
// The disjoint-union count above, read at the one decomposition every
// subset supplies for free. A subset and the part of the set outside it
// cover the set between them and meet nowhere, so the two hypotheses
// the union count asks about its operands are supplied by the SPLIT
// itself rather than assumed — which is what turns a statement about
// two unrelated sets into a statement about one set and a subset of it.
//
// Both halves of the split are about the constructors alone, with no
// count in either, so the set driver settles them and no set law is
// cited. The finiteness of the two parts is not part of the split and
// arrives from the parent chapter by two different routes: the subset
// is finite because it is INSIDE a finite set, and the remainder
// because a subtraction only ever removes from one.
//
// Stated with the subset's count leading the sum, which is the reading
// the comparison part wants — a count and what stands between it and
// the whole. The reversed sum is the same theorem and is not stated.
//
// Stated `(subset, superset)` and installed the other way round, the
// statement normalizing to `∀t s`.
var countsSubsetAndRest = countsSubsetAndRestThm{family.Add(registry.ProofEntry{
	Name: "countsSubsetAndRest",
	Key:  "prop_8fb0ce695120b67a",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(t)",
				"s ⊆ t",
			},
			Conclusion: "card(t) = card(s) + card(t ∖ s)",
		},
		func(a *Argument, s, t Term, given Fact) {
			rest := ops(a.Ctx()).SetDifference.Apply(t, s) // what s leaves of t

			// The two halves of the split spend different facts: the cover
			// spends s ⊆ t, which `given` carries, and the disjointness
			// spends nothing at all — a set and what lies outside it are
			// disjoint whatever the two are.
			cover := a.Have(
				"s and what it leaves cover t between them",
				"s ∪ (t ∖ s) = t",
				BySets(given))

			apart := a.Have(
				"and they overlap nowhere",
				"s ∩ (t ∖ s) = ∅",
				BySets())

			a.Show(
				"so the two counts add, and what they add to is t's own",
				// A count crosses the set equation `cover` here, and
				// `Normalized` folds it across. Checked by removal: without
				// it the leaf reaches the refuter and records a key.
				By(
					Normalized,
					cover,
					apart,
					given,
					At(finite_set.FiniteSubset, s, t), // finite(t) ∧ s ⊆ t ⇒ finite(s)
					At(finite_set.FiniteDiff, t, s),   // finite(t) ⇒ finite(t ∖ s)
					// card(s ∪ (t ∖ s)) = card(s) + card(t ∖ s); the three
					// conditions the union count asks for are the finiteness
					// of each operand and their disjointness, and `cover` is
					// the fourth fact — what turns its left side into card(t).
					At(CardUnion, s, rest)))
		}),
})}

// countsLeftAndSurplus — a union's count splits at its left operand,
// and the surplus came from the right one.
//
// The subset split above, read at the one subset a union supplies for
// free: a set lies inside any union it is an operand of. So neither
// condition that split asks about the set it splits has to be ASSUMED
// here — the containment holds of any two sets, and the union's
// finiteness follows from the operands' — though neither is free of a
// law: `set_order.SubsetUnion` and `finite_set.FiniteUnionImp` are both
// in the dep list below, and both are spent here so that no consumer
// spends them. What the split leaves acquires a name of its own: the
// surplus the union holds beyond s.
//
// The containment is stated with the count because the count alone says
// nothing about t. It reports how much of the union lies outside s, and
// only knowing that much to lie inside t turns the number into
// information about the two original sets rather than about one derived
// one — which is what makes a statement about `s ∪ t` two statements,
// about s and about t. That half is about the constructors alone, so
// the set driver settles it and carrying it costs the split nothing.
//
// Every additive member that weakens the disjoint-union count to a
// bound, closes that bound into an equivalence, or corrects the sum by
// the overlap starts from exactly here, and none of them repeats the
// derivation. Each claims the two halves as facts of its own, under
// separate names and one cite of this entry apiece; the entry cited
// WHOLE closes those leaves too, so claiming them apart is a labelling
// choice rather than a requirement.
//
// A ground cite writes `(s, t)` — here also the order installed at,
// since the antecedent mentions s first and neither half of the
// conclusion spreads pointwise.
var countsLeftAndSurplus = countsLeftAndSurplusThm{family.Add(registry.ProofEntry{
	Name: "countsLeftAndSurplus",
	Key:  "prop_77bfd1364affb516",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
			},
			Conclusion: "card(s ∪ t) = card(s) + card(s ∪ t ∖ s) ∧ s ∪ t ∖ s ⊆ t",
		},
		func(a *Argument, s, t Term, given Fact) {
			joined := ops(a.Ctx()).Union.Apply(s, t) // s ∪ t

			a.Do(SplitConj(
				Case(
					"s lies inside the union, so the union's count is s's own plus what s leaves of it",
					By(
						given,
						At(finite_set.FiniteUnionImp, s, t), // finite(s) ∧ finite(t) ⇒ finite(s ∪ t)
						At(set_order.SubsetUnion, s, t),     // s ⊆ s ∪ t
						// card(s ∪ t) = card(s) + card((s ∪ t) ∖ s), the split
						// stated at the subset that costs nothing to find.
						At(countsSubsetAndRest, s, joined))),

				Case(
					"and what s leaves came from t — the finiteness is not "+
						"consulted, since this half holds of any two sets whatever",
					BySets()),
			))
		}),
})}

// ---------------------------------------------------------------------------
// has_size: the size of a finite set, as a relation
// ---------------------------------------------------------------------------
//
// `card` is a function: it answers for every set, finite or not,
// because it is a fold defined by a choice, and a choice is always
// made. `has_size` is a relation, and a set may stand in it to one
// number or to no number at all. Which sets it holds of, and what it
// does when they grow and shrink, is this file.
//
// It abbreviates rather than characterizes — `has_size(s, n)` IS
// `finite(s) ∧ card(s) = n` — which every member below takes as given
// rather than restating. The reward is that the recursion the calculus above
// proved once is not re-proved: the size clauses cite the counting
// calculus instead of re-running its induction.
//
// FiniteHasSize says which sets have a size at all, and is the one
// member that reaches for nothing this chapter proved — it is the
// abbreviation read back. The other three say what a size does when a
// set changes by one element, and they come in BOTH directions, which
// is why the file holds two theorems that look like the same clause.
// HasSizeZero and HasSizeSuc state the shrinking form, over DELETION:
// a sized set can be taken apart, and the taking apart may start
// anywhere, since every member is a legitimate first step and each
// leaves the same size behind. HasSizeClauses states the growing form,
// over insert: a set of size suc n IS a set of size n with one new
// element in it. Neither comes cheaply from the other — recovering the
// insertion form from the deletion one would mean supplying the
// deletion fact for every member at once, which is the theorem again.
//
// HasSizePair, last, reads a size off a listed set: two distinct points
// make a set of two.

// FiniteHasSize — a set has its own count as a size exactly when it is
// finite.
//
// So the relation is inhabited on precisely the finite sets, and where
// it is inhabited the function is what inhabits it — which is what
// entitles the rest of the chapter to compute with `card` and state
// its results either way. Read right to left the theorem says a count
// is no evidence of anything: `card(s)` is a number whatever s is, and
// a set does not become finite by having one read off it.
//
// The theorem is definitional rather than substantive, and it is worth
// saying which definition does the work. `has_size(s, n)` IS
// `finite(s) ∧ card(s) = n` — not a characterization established
// somewhere, but what the constant abbreviates. Taken at the number the
// set's own count supplies, the second conjunct compares `card(s)` with
// itself and so holds of every set whatever; what survives is the
// first, which is the other side of the equivalence already. So the
// theorem is about the packaging: nothing about counting is used, no
// clause of the recursion is consulted, and it reaches for nothing this
// chapter proved.
var FiniteHasSize = finiteHasSizeThm{family.Add(registry.ProofEntry{
	Name: "FiniteHasSize",
	Key:  "prop_abbfd7da36099768",
	Build: family.Theorem("∀s:set(A). finite(s) ⇔ has_size(s, card(s))",
		// The set is never named: the unfold reaches has_size under the
		// binder, so there is nothing a bound term would be used for.
		func(a *Argument) {
			a.Show(
				"has_size abbreviates finiteness together with a count, "+
					"and the count it is asked for here is the one already there",
				// ↦ closes. What the unfold leaves facing finite(s) is
				// finite(s) beside card(s) = card(s), and the composite's
				// own simplification discharges the reflexive half.
				Unfold(HasSizeDef))
		}),
})}

// CardOfSized — a set that has a size is counted by it.
//
// Half of the abbreviation, read out. What the hypothesis supplies is
// a finiteness and a count, and the count is already standing at the
// number the headline asks for, with the finiteness this headline has
// no use for falling away beside it. Nothing is established, because
// the size is given rather than proved: the division is the whole
// theorem.
//
// It is worth a name because it is the shortest move available to a
// reader who holds a size and wants a count, and because the chapter
// keeps making that move: CardFunspace and FiniteFunspace divide one
// funspace size between them, CardBool and FiniteBool one universe's,
// CardFunspaceUniv and FiniteFunspaceUniv another's, and CardProduct
// and CardPowerset take the counting half of a rectangle's size and a
// powerset's and leave the rest. Each of those divides a size it has
// just proved; this one divides any size at all.
//
// The counting halves cite it. The three that keep the FINITENESS
// cannot — that half of the abbreviation has no member of its own —
// so each of them reads its size apart in place.
var CardOfSized = cardOfSizedThm{family.Add(registry.ProofEntry{
	Name: "CardOfSized",
	Key:  "prop_70b2b97ff2ebc690",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀n:num.",
		Hypotheses: []string{
			"has_size(s, n)",
		},
		Conclusion: "card(s) = n",
	},
		// Neither the set nor the number is named: the unfold reaches
		// has_size under both binders, so there is nothing a bound term
		// would be used for.
		func(a *Argument) {
			a.Show(
				"a size is finiteness together with a count, and the count it carries is the one asked for",
				// What the unfold leaves is a conjunction implying its
				// own second half. No premise settles that — it is a
				// tautology, and the normalizer is all it takes.
				Unfold(HasSizeDef),
				TrivialNormalized())
		}),
})}

// HasSizeZero — a set has size 0 exactly when it is empty.
//
// Having a size is finiteness together with a count, so at 0 there are
// two things to settle and only one of them is about counting. That one
// is settled already: among the finite sets, counting 0 is being empty.
//
// What is left is that at 0 the finiteness costs nothing, and the two
// directions meet it differently. Read forwards there is nothing to do:
// the definition hands the finiteness over as its own left half. Read
// backwards it is the only thing to do, and ∅ is finite by finite's
// base rule, so a set equal to ∅ is finite too.
//
// That second direction is what this member adds over CardEqZero,
// which conditions on finiteness throughout and so can never conclude
// it. Here emptiness is enough on its own: a set is not asked to be
// finite before it can be recognized as having size 0, because being
// empty already carries the finiteness that having a size demands.
//
// The count at ∅ is never quoted, though a reader might expect it in
// the backwards direction. It does not have to be: once the finiteness
// is in hand, the same equivalence run the other way turns emptiness
// back into the count, and one equivalence does both directions.
//
// No induction. The induction that makes counting 0 force emptiness
// lives in CardEqZero.
var HasSizeZero = hasSizeZeroThm{family.Add(registry.ProofEntry{
	Name: "HasSizeZero",
	Key:  "prop_e8c905fefbdd83db",
	Build: family.Theorem("∀s:set(A). has_size(s, 0) ⇔ s = ∅",
		func(a *Argument, s Term) {
			// ↦ finite(s) ∧ card(s) = 0 ⇔ s = ∅. The closer treats
			// has_size as opaque — no premise below says what a size is —
			// so without this the count is out of reach.
			a.Do(Unfold(HasSizeDef))

			// `Normalized` answers the residual signal here, and was
			// checked by removal.
			//
			// CardEqZero arrives with its set equation spread POINTWISE
			// — the two sides compared at an element — while the goal
			// is about the sets themselves, and folding one back into the
			// other is extensionality, which Basic does between the
			// installs and the refuter does not. Without
			// `Normalized` the close fails having cleared nothing: the
			// facts are all present, in the wrong shape.
			//
			// That same normalization then decomposes the ⇔ into its
			// separate clause obligations, each closed by the same
			// refutation from the same two facts.
			a.Show(
				"so size 0 is emptiness: the count says so wherever "+
					"finiteness holds, and at ∅ finiteness holds for free",
				By(
					Normalized,
					// card(s) = 0 ⇔ s = ∅ once s is finite. Both
					// directions of the goal are this one instance, read
					// the two ways round.
					At(CardEqZero, s),
					// finite(∅). Bare because the conjunct read binds
					// nothing: witnesses here would name an instance of
					// the enlargement rule beside it, which this proof
					// never reaches for.
					finite_set.FiniteRules))
		}),
})}

// HasSizeSuc — a set has size one more than n exactly when it has a
// member to lose and every member it loses leaves size n behind.
//
// Both directions are one fact read in opposite orders, and that fact
// is CountsOneMore: a finite set counts one more than what is left when
// a member of it is taken out. Forwards it turns a count of suc n into
// a count of n at every remainder; backwards it turns a count of n at a
// SINGLE remainder into suc n at the set.
//
// That asymmetry is the shape of the theorem. The right-hand side
// speaks about every member, but rebuilding the count needs only one —
// so the ⇐ direction spends the non-emptiness to produce a member and
// never looks at the others, while the ⇒ direction has to answer for
// all of them, and can, because CountsOneMore is stated at an arbitrary
// one.
//
// Non-emptiness costs no set theory at all: a set counting a successor
// cannot count 0, and 0 is what card's first clause gives the empty
// set. Nothing here is by induction, and nothing here is arithmetic —
// the two facts about suc that the proof spends are that it misses 0
// and that it cancels.
var HasSizeSuc = hasSizeSucThm{family.Add(registry.ProofEntry{
	Name: "HasSizeSuc",
	Key:  "prop_4a8ce99435601330",
	Build: family.Theorem(
		"∀s:set(A). ∀n:num. has_size(s, suc(n)) ⇔ s ≠ ∅ ∧ (∀a:A. a ∈ s ⇒ has_size(delete(s, a), n))",
		func(arg *Argument, s, n Term) {
			// ↦ finite ∧ card = ·, at s and at every remainder. Both
			// sides of the equivalence mention a size, and neither half
			// of what a size packs travels by the other's laws, so they
			// are separated once here rather than twice below.
			arg.Do(Unfold(HasSizeDef))

			arg.Iff()
			arg.Forward(
				"and it is enough for every member: each deletion drops the count from suc n to n",
				func(b *Argument, sized Fact) {
					b.Do(SplitConj(
						// No set law is spent here and none is needed:
						// the count rules s out before emptiness is
						// ever consulted.
						Case(
							"s is not empty, since it counts a successor and the empty set counts 0",
							By(
								sized,
								CardClauses,               // card(∅) = 0 — the clause that binds nothing
								At(peano.SucNotZero, n))), // suc(n) ≠ 0

						Case(
							"and removing any member leaves a set of size n",
							Derive(func(b *Argument) {
								a := b.Fix()         // an arbitrary point…
								member := b.Assume() // …assumed to lie in s
								// What is left of s once a goes — built
								// only so the successor law below can be
								// read at its count.
								rest := ops(b.Ctx()).Delete.Apply(s, a)

								b.Do(SplitConj(
									Case(
										"the remainder is finite because s is",
										By(sized, finite_set.FiniteDelete)),

									Case(
										"and it counts n, since s counts one above it and successors cancel",
										By(
											Normalized,
											member,
											sized,
											At(CountsOneMore, s, a), // card(s) = suc(card(rest))
											// suc(card(rest)) = suc(n) ⇔ card(rest) = n.
											// The remainder's count is the witness the
											// successor law is read at, so it is built —
											// which is the one thing `card` is ever a
											// handle for.
											At(peano.SucInjective,
												ops(b.Ctx()).Card.Apply(rest), n))),
								))
							})),
					))
				})
			arg.Backward(
				"one member is enough: rebuild s's count from the remainder that member leaves",
				func(b *Argument, presented Fact) {
					// Any member will do, and the hypothesis offers no
					// way to prefer one — non-emptiness is all that is
					// spent to get it.
					x, member := b.Obtain(
						"a set that is not empty has a member",
						"∃x:A. x ∈ s",
						By(presented, At(set_basic.MemberNotEmpty, s))) // (∃x. x ∈ s) ⇔ ¬(s = ∅)

					// The size assumed at the remainder carries
					// finiteness back UP across the deletion, which is
					// the direction the deletion law's equivalence
					// supplies and its implication form would not.
					finite := b.Have(
						"s is finite because what is left of it once x goes is",
						"finite(s)",
						By(presented, member, finite_set.FiniteDelete))

					b.Show(
						"and s counts one above that remainder, whose count is n",
						By(Normalized, finite, member, presented, At(CountsOneMore, s, x)))
				})
		}),
})}

// HasSizeClauses — the recursion clauses of has_size, each read as a
// characterization of the sets of that size.
//
// The zero clause is immediate — both sides say the set has nothing in
// it, and the zero clause above is taken whole. The suc clause is the
// content, and it is two separate facts, one per direction, which is
// how the two
// sections below are organized: splitting an element OFF a counted set,
// and putting one BACK. They travel by different routes. Splitting off
// is set surgery, done with delete and its membership laws, and the
// count comes along by the deletion form of the same recursion step.
// Putting back never touches the set laws at all: it is finite's own
// closure rule beside the counting calculus's insertion law, which is
// already stated at an element the set did not hold — so the assumption
// that it was absent is not something this section argues from, it is
// the law's own hypothesis handed straight over.
//
// Nothing here is by induction: both directions move a single element
// across the boundary between a set and its count, and one element is
// all the recursion step is about.
var HasSizeClauses = hasSizeClausesThm{family.Add(registry.ProofEntry{
	Name: "HasSizeClauses",
	Key:  "prop_5aae73079fb5d440",
	Build: family.Sections(
		"∀s:set(A). ∀n:num. "+
			"    (has_size(s, 0) ⇔ s = ∅) ∧ "+
			"    (has_size(s, suc(n)) ⇔ ∃a:A. ∃t:set(A). has_size(t, n) ∧ a ∉ t ∧ s = insert(a, t))",
		func(ctx *Script, headline string) *GoalStackNode {
			// delete is the one construction either section BUILDS a term
			// with; insert and the counting names are stated, never applied.
			del := ops(ctx).Delete

			// Almost every close below names its premises and then asks for
			// nothing beyond normalization, which is what `Normalized`
			// supplies: the claims are stated as mathematics while the laws
			// they lean on arrive with set equality spelled pointwise and
			// implications spread into clauses, and folding the two back
			// together is bookkeeping rather than search. The two closes
			// without it are the two whose CLAIM has no set equation to
			// fold: drawing a member out of non-emptiness, where the same
			// non-emptiness is the premise, and reading the remainder's
			// size off the recursion law, where what is claimed is a size.
			// (The recursion law itself does mention ∅ — it is the claim,
			// not the law, that decides whether there is anything to fold.)

			// splitOff — a set of size suc n has an element to spare, and
			// what is left when it goes has size n.
			//
			// The remainder is not a second choice: once the element a is
			// picked it can only be delete(s, a), so the clause's two
			// witnesses are really one. Picking a needs no more than that s
			// is not empty, and that is the first thing the deletion clause
			// says about a set of size suc n; the second thing it says is that
			// deleting a member drops the size to n, which is the
			// remainder's size. What is left to check is that delete really
			// undoes insert here — that the element is gone, and that
			// putting it back returns s.
			splitOff := ctx.Lemma(
				Statement{
					Binders: "∀s:set(A). ∀n:num.",
					Hypotheses: []string{
						"has_size(s, suc(n))",
					},
					Conclusion: "∃a:A. ∃t:set(A). has_size(t, n) ∧ a ∉ t ∧ s = insert(a, t)",
				},
				func(arg *Argument, s, n Term, sized Fact) {
					nonempty := arg.Have(
						"a set of size suc n cannot be empty",
						"¬(s = ∅)",
						// has_size(s, suc n) ⇔ s ≠ ∅ ∧ every member of s
						// deletes to a set of size n — both halves of this
						// section come from that one instance.
						By(sized, At(HasSizeSuc, s, n)))

					a, member := arg.Obtain(
						"so it has a member, and that is the element to split off",
						"∃a:A. a ∈ s",
						By(nonempty, At(set_basic.MemberNotEmpty, s))) // (∃x. x ∈ s) ⇔ ¬(s = ∅)

					rest := del.Apply(s, a) // what is left of s once a goes

					restSized := arg.Have(
						"removing a member of a set of size suc n leaves size n",
						"has_size(delete(s, a), n)",
						By(sized, member, At(HasSizeSuc, s, n)))
					whole := arg.Have(
						"and putting it back reassembles s",
						"s = insert(a, delete(s, a))",
						By(Normalized, member, At(set_algebra.InsertDelete, s, a))) // a ∈ s ⇒ insert(a, delete(s, a)) = s

					arg.Take(a)
					arg.Take(rest)
					arg.Show(
						"so that element, which the remainder no longer holds, "+
							"and that remainder are the split the clause asks for",
						By(restSized, At(set_basic.InDelete, s, a, a), whole))
				})

			// enlarge — adding a NEW element to a set of size n gives a set
			// of size suc n.
			//
			// Here has_size is worth unfolding, because its two halves
			// travel by different laws: finiteness by finite's own insert
			// rule, the count by the insertion law of the counting calculus.
			// That law is stated at precisely the hypothesis this section
			// is handed — an element the set did not already hold — so
			// nothing here has to argue about which branch of the counting
			// recursion applies.
			enlarge := ctx.Lemma(
				Statement{
					Binders: "∀a:A. ∀t:set(A). ∀n:num.",
					Hypotheses: []string{
						"has_size(t, n)",
						"a ∉ t",
					},
					Conclusion: "has_size(insert(a, t), suc(n))",
				},
				// The antecedent is bound and then immediately taken apart by
				// the unfolding below, which replaces it with the three facts
				// it packs; those are what the two branches name. There is no
				// verb that hands those three back as values — `Unfold` is a
				// goal-surface move — so they are re-named by content.
				func(arg *Argument, a, t, n Term, _ Fact) {
					arg.Do(Unfold(HasSizeDef)) // ↦ finite ∧ card = ·, on both sides
					finite := arg.Hyp("finite(t)")
					fresh := arg.Hyp("a ∉ t")
					counted := arg.Hyp("card(t) = n")

					arg.Do(SplitConj(
						Case(
							"the enlarged set is still finite: finite's insert rule, whose one premise is the finiteness of t",
							By(finite, At(finite_set.FiniteRules, a, t))),
						Case(
							"and its count is one more, which is what the "+
								"insertion law says of an element the set did not have",
							// card(insert(a, t)) = suc(card(t)) — the law's two
							// hypotheses are `finite` and `fresh`, and `counted`
							// is what turns suc(card(t)) into suc(n).
							By(Normalized, finite, fresh, counted, At(InsertCountsOneMore, t, a))),
					))
				})

			return ctx.Theorem(headline, func(arg *Argument, s, n Term) {
				arg.Do(SplitConj(
					Case(
						"size 0: a set counts none exactly when it is empty, which is this clause",
						Cite(HasSizeZero)),
					Case(
						"size suc n: one direction per section",
						SplitIff(
							Forward(
								"and every set of size suc n can be presented that way",
								Cite(splitOff)),
							Backward(
								"a set presented as one new element beside a set of size n has size suc n",
								Given(func(arg *Argument, split Fact) {
									a, t, parts := arg.Unpack2(split)
									arg.Show(
										"enlarge at that element and that set, carried to s along the equation the clause supplies",
										By(Normalized, parts, At(enlarge, a, t, n)))
								})),
						)),
				))
			})
		}),
})}

// HasSizePair — two distinct points make a set of two elements: {a, b} is
// the singleton {b} with the point a added, which lies outside it, so the
// set is finite and one larger than the singleton.
var HasSizePair = hasSizePairThm{family.Add(registry.ProofEntry{
	Name: "HasSizePair",
	Key:  "prop_7c674f804f564204",
	Build: family.Theorem(Statement{
		Binders:    "∀a b:A.",
		Hypotheses: []string{"a ≠ b"},
		Conclusion: "has_size({a, b}, 2)",
	}, func(arg *Argument, a, b *Expr[A], distinct Fact) {
		singleton := arg.TermAs[Set[A]]("{b}")
		outside := arg.Have(
			"a lies outside the singleton {b}",
			"a ∉ {b}",
			BySets(distinct))
		arg.Show(
			"adding a to the finite singleton {b} adds one point",
			ByArith(
				outside,
				HasSizeDef.At(arg.TermAs[Set[A]]("{a, b}"), arg.TermAs[Nat]("2")),
				finite_set.FiniteInsert.At(a, singleton),
				finite_set.FiniteSing.At(b),
				InsertCountsOneMore.At(singleton, a),
				CardSing.At(b)))
	}),
})}

// ---------------------------------------------------------------------------
// Comparing two counts
// ---------------------------------------------------------------------------
//
// the comparison part: what containment does to a count, and what a count
// does back.
//
// Everything in the counting calculus reads a count off one set. These read two
// counts against each other. The file has two strands.
//
// The CONTAINMENT strand rests on the subset split the calculus states:
// a subset and what it leaves cover the containing set between them and
// meet nowhere, so their counts add to the whole's. Containment bounding
// a count is then a summand not running past its sum; a subset carrying
// the whole count has nothing left to be smaller by; and those two
// close into an equivalence.
//
// The STRICT strand turns containment into proper containment and back,
// and those two likewise close into an equivalence; the two directions
// cost wildly different things. Getting `s ⊊ t` OUT of disagreeing
// counts is congruence — no finiteness, no counting law, nothing this
// chapter proved. Getting a count inequality out of `s ⊊ t` means
// actually counting, so finiteness and the containment strand both come
// back.
//
// A third, much shorter strand sits at the bottom of the scale. A count
// is lossy almost everywhere — how many elements a set has says nothing
// about which — but at nothing, or one thing, the loss vanishes and the
// number determines the set up to the choice of a point.
//
// One note bites here, and its single home is `CardSubsetEq`'s godoc
// below: that entry and `CardSubset` state their binders identically and
// take OPPOSITE ground tuples, because only `CardSubsetEq` concludes a
// set equality — which normalization spreads pointwise, opening an
// install slot the statement never bound. Sites that depart from the stated
// order point at that godoc rather than re-deriving it; a site taking
// the stated order says nothing, that being the default.

// CardSubset — containment bounds a count: a subset of a finite set has
// no more elements than the set does.
//
// The bound comes out of an EQUATION, not out of comparing the two sets
// element by element: once the split above is stated the comparison is
// already settled, because a summand never runs past its sum. So there
// is no induction here and no case on how the two sets sit — and
// nothing about ≤ beyond one named law of +.
//
// Both of the theorem's hypotheses go into the split and neither is
// used again. That the split states the subset's count LEADING the sum
// is what makes the last step a reading rather than a rearrangement:
// the remainder is exactly what stands between the two counts, and
// `m ≤ m + n` comes off it directly.
//
// A consumer's ground cite of this entry writes (subset, superset) —
// the order stated below, which is not the order it normalizes to.
// Worth saying because both slots are sets of the same type, so a
// reversed tuple is type-correct and fails only at the refuter.
var CardSubset = cardSubsetThm{family.Add(registry.ProofEntry{
	Name: "CardSubset",
	Key:  "prop_2d9334ed7dc51525",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(t)",
				"s ⊆ t",
			},
			Conclusion: "card(s) ≤ card(t)",
		},
		func(a *Argument, s, t Term, given Fact) {
			countOf := ops(a.Ctx()).Card
			rest := ops(a.Ctx()).SetDifference.Apply(t, s) // what s leaves of t

			// Both premises are ground, and between them they spell the
			// quantity the argument turns on — the sum — so nothing about
			// it is left to be searched for.
			//
			// `Normalized` here is NOT `vocab.go`'s set-law fold — no set
			// law is installed. It is the same move one level down: the
			// split arrives packed in a clause behind its two hypotheses,
			// and discharging that guard to substitute the freed equation
			// into the order fact is equality work rather than search.
			// Measured both ways: without it the close fails naming
			// `Basic` as the fix, and with it the leaf records no key.
			a.Show(
				"t's count is s's plus what s leaves, and a summand never runs past its sum",
				By(
					Normalized,
					given,
					// card(t) = card(s) + card(t ∖ s)
					At(countsSubsetAndRest, s, t),
					// card(s) ≤ card(s) + card(t ∖ s)
					At(nat_order.LessEqAdd, countOf.Apply(s), countOf.Apply(rest))))
		}),
})}

// BoundedFiniteSubsets — a set all of whose finite subsets have at most n points is
// finite with at most n points. By induction on n: a member x of the set puts every
// finite subset off x inside one point more, so the set less x is finite with at
// most n - 1 points.
var BoundedFiniteSubsets = boundedFiniteSubsetsThm{family.Add(registry.ProofEntry{
	Name: "BoundedFiniteSubsets",
	Key:  "prop_d71d92ddf9fbde6d",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num. ∀Z:set(A).",
		Hypotheses: []string{"∀S:set(A). finite(S) ∧ S ⊆ Z ⇒ card(S) ≤ n"},
		Conclusion: "finite(Z) ∧ card(Z) ≤ n",
	},
		func(a *Argument) {
			a.Induct("n")
			a.Base(
				"with no room, the set has no member",
				func(b *Argument) {
					Z := b.FixAs[Set[A]]("Z")
					bounded := b.Assume()
					noMember := b.Have(
						"a member would be a subset of one point",
						"∀x:A. x ∉ Z",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							member := c.SupposeNot()
							single := c.TermAs[Set[A]]("{x}")
							inside := c.Have(
								"the point lies in Z",
								"{x} ⊆ Z",
								BySets(member))
							counted := c.Have(
								"so it counts at most zero",
								"card({x}) ≤ 0",
								By(bounded.At(single), inside, finite_set.FiniteSing.At(x)))
							c.Show(
								"but it counts one",
								ByArith(counted, CardSing.At(x)))
						}))
					empty := b.Have(
						"so the set is empty",
						"Z = ∅",
						By(noMember, set_basic.MemberNotEmpty.At(Z)))
					b.Do(empty.Rw())
					b.Show(
						"the empty set is finite, with no points",
						By(Normalized, finite_set.FiniteRules, CardClauses, nat_order.LessEqRefl.At(b.TermAs[Nat]("0"))))
				})
			a.Step(
				"a member x leaves a set with one point less",
				func(b *Argument, ih Fact) {
					Z := b.FixAs[Set[A]]("Z")
					bounded := b.Assume()
					b.Cases(b.Term("Z = ∅"))
					b.When(
						"the empty set is finite, with no points",
						func(c *Argument, empty Fact) {
							c.Do(empty.Rw())
							c.Do(Simp(Fwd(finite_set.FiniteRules), Fwd(CardClauses)))
							c.Show(
								"no points is at most n + 1",
								ByArith())
						})
					b.Otherwise(
						"a member x leaves room for at most n points",
						func(c *Argument, nonempty Fact) {
							x, member := c.ObtainAs[A](
								"the set has a member x",
								"∃x:A. x ∈ Z",
								By(nonempty, set_basic.MemberNotEmpty.At(Z)))
							rest := c.TermAs[Set[A]]("delete(Z, x)")
							fewer := c.Have(
								"a finite subset off x has at most n points",
								"∀S:set(A). finite(S) ∧ S ⊆ delete(Z, x) ⇒ card(S) ≤ n",
								Derive(func(e *Argument) {
									S := e.FixAs[Set[A]]("S")
									assumed := e.Conjuncts(
										e.Assume(),
										"S is finite",
										"and lies off x, in Z")
									finiteS, inside := assumed[0], assumed[1]
									extended := e.TermAs[Set[A]]("insert(x, S)")
									placed := e.Have(
										"x is a new point of S, inside Z",
										"x ∉ S ∧ insert(x, S) ⊆ Z",
										BySets(inside, member))
									larger := e.Have(
										"so S with x is finite, with one point more",
										"finite(insert(x, S)) ∧ card(insert(x, S)) = suc(card(S))",
										By(finiteS, placed, finite_set.FiniteInsert.At(x, S), InsertCountsOneMore.At(S, x)))
									limit := e.Have(
										"and it counts at most n + 1",
										"card(insert(x, S)) ≤ suc(n)",
										By(bounded.At(extended), larger, placed))
									e.Show(
										"so S counts at most n",
										ByArith(limit, larger))
								}))
							counted := c.Have(
								"the set less x is finite with at most n points",
								"finite(delete(Z, x)) ∧ card(delete(Z, x)) ≤ n",
								By(ih.At(rest), fewer))
							restored := c.Have(
								"putting x back adds at most one point",
								"finite(insert(x, delete(Z, x))) ∧ card(insert(x, delete(Z, x))) ≤ suc(n)",
								By(counted, InsertCountsAtMostOneMore.At(rest, x, c.TermAs[Nat]("n"))))
							c.Show(
								"and gives the set back",
								By(Normalized, restored, member, set_algebra.InsertDelete.At(Z, x)))
						})
				})
		}),
})}

// CardSubsetEq — a subset carrying the whole of a finite set's count IS
// that set.
//
// A count is a lossy summary: how many elements a set has says almost
// nothing about which ones. This is where that stops being true. Laid
// inside a set it is exactly as large as, a subset has nothing left to
// be smaller by, and a set is nothing but the elements it admits.
//
// The argument spends the subset split once and then reads it off: if
// the subset already carries the whole count, the remainder carries
// nothing, and a finite set counted 0 is empty.
//
// The finiteness is spent twice and is never assumed of the remainder.
// The split asks it of the containing set, which the hypothesis gives,
// and reading emptiness off a count asks it of the remainder, which the
// parent chapter supplies because a subtraction only ever removes.
//
// The arithmetic is a cancellation on the left and nothing else.
// Substituting the equal counts leaves the same count standing on both
// sides of the split, so what is added to it there cancels away to 0 —
// once the trivial sum on the other side is written as a sum at all.
// Those two laws are all this member borrows from outside the set
// layer.
//
// A ground cite of this entry writes (superset, subset) — the list_reverse
// of its neighbour `CardSubset` above, whose binders it otherwise
// states identically. The cause is the conclusion: `s = t` is an
// equality of SETS, which normalization spreads pointwise over an `ẋ`
// the statement never bound, so the install prefix is `[t, s, ẋ]` —
// three slots against two stated names. No name map can be total, and
// a tuple short of the full prefix binds POSITIONALLY, leading with
// the containing set.
//
// Both slots are sets of the same type, so a reversed tuple is
// type-correct and fails only at the refuter; the tell is
// `XUGO_WITNESS_PROBE_DEP=cardinality.CardSubsetEq` printing more
// install slots than the headline has binders. Any entry here
// concluding a set equality behaves the same way.
var CardSubsetEq = cardSubsetEqThm{family.Add(registry.ProofEntry{
	Name: "CardSubsetEq",
	Key:  "prop_5e1c36ae0891f254",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(t)",
				"s ⊆ t",
				"card(s) = card(t)",
			},
			Conclusion: "s = t",
		},
		func(a *Argument, s, t Term, given Fact) {
			rest := ops(a.Ctx()).SetDifference.Apply(t, s) // what s leaves of t

			// The two counts the cancellation is read at.
			subsetCount := ops(a.Ctx()).Card.Apply(s)
			restCount := ops(a.Ctx()).Card.Apply(rest)

			split := a.Have(
				"t's count splits at s into s's own and what the remainder costs",
				"card(t) = card(s) + card(t ∖ s)",
				By(given, At(countsSubsetAndRest, s, t)))

			nothingLeft := a.Have(
				"so the remainder costs nothing — s already carries the whole count",
				"card(t ∖ s) = 0",
				By(
					split,
					given,
					// card(s) + 0 = card(s) + card(t ∖ s) ⇔ 0 = card(t ∖ s),
					// the split with the equal counts substituted on the left.
					At(nat_arith.AddEqLCancel, subsetCount, a.Ctx().Numeral(0), restCount),
					nat_arith.AddZero))

			restEmpty := a.Have(
				"so nothing of t lies outside s at all",
				"t ∖ s = ∅",
				By(
					given,
					At(finite_set.FiniteDiff, t, s), // finite(t) ⇒ finite(t ∖ s)
					nothingLeft,
					At(CardEqZero, rest)))

			// The facts it consumes: the emptiness just established, and
			// `s ⊆ t` out of `given`. The counts say nothing to the driver,
			// which has no notion of card, so none of them is handed over.
			a.Show(
				"an empty remainder is t admitting nothing beyond s, and s was inside t to begin with",
				BySets(restEmpty, given))
		}),
})}

// CardSubsetLe — a subset of a finite set whose count does not fall
// short of the whole set's IS that set.
//
// This is `CardSubsetEq` with its hypothesis weakened, and the weakening
// is free. Containment already bounds the subset's count ABOVE by the
// set's, so a count assumed to be no SMALLER is pinned between two
// bounds and the two agree — at which point the earlier member takes
// over and there is nothing left to prove. What reads as the stronger
// theorem, one inequality where its neighbour asks an equality, is the
// same theorem asked against a bound that was there all along.
//
// So this member says nothing about sets that `CardSubsetEq` had not
// already settled, and nothing about counts beyond antisymmetry: it is a
// hypothesis-weakening, and its whole content is that the missing half
// of the equality is a theorem rather than an assumption. That is why
// there is no induction here, no case on how the sets sit, and no set
// law of its own — the two steps below are the two halves of that
// sentence, in that order.
var CardSubsetLe = cardSubsetLeThm{family.Add(registry.ProofEntry{
	Name: "CardSubsetLe",
	Key:  "prop_c2a3dcc45977084c",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(t)",
				"s ⊆ t",
				"card(t) ≤ card(s)",
			},
			Conclusion: "s = t",
		},
		func(a *Argument, s, t Term, given Fact) {
			countOf := ops(a.Ctx()).Card

			counts := a.Have(
				"containment bounds s's count above by t's and the hypothesis bounds it below, so the two agree",
				"card(s) = card(t)",
				By(
					given,
					// card(s) ≤ card(t) — the bound containment gives for
					// free, and the whole reason the hypothesis is allowed
					// to be an inequality rather than the equality wanted.
					At(CardSubset, s, t),
					// card(s) = card(t) ⇔ the two inequalities, read at the
					// two counts: the law that spends them.
					At(nat_order.LessEqAntisym, countOf.Apply(s), countOf.Apply(t))))

			a.Show(
				"and a containment whose counts agree is CardSubsetEq's hypothesis exactly",
				By(
					counts,
					given,
					// (superset, subset) here — the reverse of the cite one
					// step up, per `CardSubsetEq`'s godoc.
					At(CardSubsetEq, s, t)))
		}),
})}

// SubsetEqIffSameCount — for a subset of a finite set, carrying the
// whole count and BEING the set are the same condition.
//
// The interest is in how unevenly the two directions are paid for, and
// that is the only reason to state the equivalence rather than leave it
// as its halves. One direction is `CardSubsetEq`, and everything this
// chapter knows goes into it: the finiteness, the containment, the
// split of the containing set at the subset, and a cancellation on the
// counts. The other spends nothing whatever. `card` is a function, so
// it cannot tell two equal sets apart — no law of counting is cited,
// neither hypothesis is touched, and finiteness is beside the point.
//
// So the expensive implication turns out to be reversible for free —
// which is what the equivalence records: against a fixed finite
// container, the lossiness `CardSubsetEq` bounds vanishes entirely.
//
// The two arms below are shaped by that unevenness rather than merely
// described by it. The expensive one carries no argument at all — after
// the split its whole sequent IS the theorem it names. The cheap one
// names one premise, and since `By` clears every hypothesis it does not
// name, that naming is a checked claim that the finiteness and the
// containment go unspent on that side; a false one would not close.
var SubsetEqIffSameCount = subsetEqIffSameCountThm{family.Add(registry.ProofEntry{
	Name: "SubsetEqIffSameCount",
	Key:  "prop_df47d1e20dedcaa7",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(t)",
				"s ⊆ t",
			},
			Conclusion: "card(s) = card(t) ⇔ s = t",
		},
		// The slots are bound only to reach the ⇔ underneath them:
		// neither arm grounds a cite, so nothing below is handed a set
		// or the antecedent.
		func(a *Argument, s, t Term, _ Fact) {
			a.Iff()
			a.Forward(
				"a subset already carrying the whole count has nothing left to be smaller by",
				// ↦ closes, bare and without witnesses. Nothing is
				// deduced FROM CardSubsetEq here: the split hands this
				// arm a sequent that IS that theorem, hypotheses and
				// conclusion together, so the cite matches the leaf
				// rather than installing a fact to refute against.
				Cite(CardSubsetEq))
			a.Backward(
				"the sets are the same set, so there is nothing for two counts to disagree about",
				func(b *Argument, sameSet Fact) {
					b.Show(
						"congruence, and neither the finiteness nor the containment is asked for",
						// `vocab.go`'s shaping at its second case: no set law
						// is installed here at all, and substituting one set
						// for the other under `card` is rewriting rather than
						// refutation. Measured by removal — without it the
						// close fails naming `Basic` as the fix.
						By(Normalized, sameSet))
				})
		}),
})}

// PsubsetOfDifferentCount — a set contained in another is contained
// STRICTLY as soon as the two counts fail to agree.
//
// The chapter's comparisons condition on finiteness because they read
// counts off sets and compute with them. This one carries no such
// hypothesis, and the reason is that it never counts anything. `card`
// occurs below only as a function: equal sets have equal counts, so
// counts that differ belong to sets that differ, and the inequality of
// the two sets follows by congruence alone. Whether either count is the
// NUMBER OF ELEMENTS of its set — which is precisely what finiteness
// would buy, and what CardClauses and its consequences are about — is
// never asked. Over an infinite set the count is whatever the choice
// made it, and the theorem holds of that too.
//
// What is left is definitional. Strict containment abbreviates
// containment together with inequality; the containment is the
// hypothesis handed straight back, and the inequality is the
// disagreement of counts read contrapositively. So unfolding the
// abbreviation leaves both halves already in hand — no counting law is
// cited, nothing is inducted over, and the member reaches for nothing
// this chapter proved.
//
// The converse is a different theorem and a far more expensive one:
// extracting a disagreement of counts FROM strict containment means
// actually counting both sets, and that is where finiteness, the
// disjoint-union law and the pigeonhole all come back in.
var PsubsetOfDifferentCount = psubsetOfDifferentCountThm{family.Add(registry.ProofEntry{
	Name: "PsubsetOfDifferentCount",
	Key:  "prop_947bd183ea0a33f2",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"s ⊆ t",
			"card(s) ≠ card(t)",
		},
		Conclusion: "s ⊊ t",
	},
		// There is no cite to ground: the antecedent is the whole premise
		// list. The slots keep the statement's names rather than `_`,
		// because binding is positional and a blank would hide whether
		// the order is right.
		func(a *Argument, s, t Term, given Fact) {
			a.Show(
				"strict containment abbreviates containment with inequality, "+
					"and sets whose counts differ are not the same set",
				// What the unfold leaves is the containment beside `s ≠ t`
				// — the first is the hypothesis verbatim, the second is
				// what the counts' disagreement forces.
				Simp(Fwd(set_basic.ProperSubsetDef)),
				By(Normalized, given))
		}),
})}

// CardPsubset — a set laid strictly inside a finite one is strictly
// smaller.
//
// This is the converse of PsubsetOfDifferentCount, and the pair is worth
// reading together because the two directions cost entirely different
// things. That one compares counts without ever reading one, so it asks
// for no finiteness and cites nothing this chapter proved. This one has
// to read both counts before it can compare them — so finiteness comes
// back, and with it CardSubset, CardSubsetEq and the subset split they
// both rest on.
//
// The abbreviation is still where the set-theoretic content ends, but
// here its two halves go to different places. Containment gives the
// bound. Inequality is what rules that bound's equality case out, and it
// does so through CardSubsetEq read BACKWARDS: a subset carrying the
// whole count would be the set itself, so a subset that is not the set
// carries less. That contrapositive is the whole of the argument's
// cleverness, and it is why the expensive member is this direction
// rather than the other.
//
// What is left mentions no set at all — a count no larger than another
// and not equal to it is smaller. The seed settled that with the
// arithmetic decision procedure; naming the law instead is what takes
// this member's capability to nothing.
var CardPsubset = cardPsubsetThm{family.Add(registry.ProofEntry{
	Name: "CardPsubset",
	Key:  "prop_70025fa5821395ce",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(t)",
				"s ⊊ t",
			},
			Conclusion: "card(s) < card(t)",
		},
		// The antecedent is bound only to put it in the context, where
		// the unfold below reads it — as in PsubsetOfDifferentCount. It
		// is not named, because the unfold replaces it: what the three
		// steps go on to use are its pieces, not it.
		func(a *Argument, s, t Term, _ Fact) {
			// No verb for this one: unfolding an abbreviation is a move
			// on the goal's surface, not a deduction. It is also the
			// only such move here.
			a.Do(Unfold(set_basic.ProperSubsetDef))

			// The pieces the unfold leaves standing. They are named
			// separately rather than carried as one packed hypothesis
			// because the three steps below draw on different ones of
			// them — two, then all three, then none at all — and the
			// premise lists are where that shows.
			finite := a.Hyp("finite(t)")
			differ := a.Hyp("s ≠ t")
			inside := a.Hyp("s ⊆ t")

			countOf := ops(a.Ctx()).Card

			bound := a.Have(
				"laid inside t, s counts no more than t does",
				"card(s) ≤ card(t)",
				// finite(t₀) ∧ s₀ ⊆ t₀ ⇒ card(s₀) ≤ card(t₀)
				By(finite, inside, At(CardSubset, s, t)))

			// The contrapositive step: CardSubsetEq lands `s = t` from
			// the counts agreeing, so `s ≠ t` is what forbids them to.
			//
			// The tuple is (t, s) where the cite above takes (s, t) —
			// the reversal `CardSubsetEq`'s godoc explains. Measured by
			// deliberate failure here: (s, t) installs `t₀ ⊆ s₀`.
			countsDiffer := a.Have(
				"and it counts no fewer only if it IS t, which it is not",
				"card(s) ≠ card(t)",
				// finite(t₀) ∧ s₀ ⊆ t₀ ∧ card(t₀) = card(s₀) ⇒ t₀ = s₀
				By(finite, differ, inside, At(CardSubsetEq, s, t)))

			// Nothing set-theoretic survives into this leaf: the two
			// counts are opaque numbers and the finiteness, containment
			// and inequality are all spent. `By` clears them.
			a.Show(
				"a bound with its equality case ruled out is the strict order",
				By(
					bound,
					countsDiffer,
					// card(s₀) ≤ card(t₀) ⇔ card(s₀) < card(t₀) ∨ card(s₀) = card(t₀)
					At(nat_order.LessEqSplit, countOf.Apply(s), countOf.Apply(t))))
		}),
})}

// PsubsetIffFewerElements — inside a fixed finite container, counting
// fewer elements and lying strictly within are the same condition.
//
// Both implications stand above — CardPsubset one way and
// PsubsetOfDifferentCount the other — so what the equivalence adds is
// not a new fact but the right to read either comparison off the other.
// Set beside SubsetEqIffSameCount that completes a correspondence: for a
// subset of a finite set, equal counts mean equal sets and a smaller
// count means strict containment, so the order between the two numbers
// reproduces how the two sets sit. A count that the containment strand
// could only use as a bound is here a faithful summary.
//
// The hypothesis is the join of what the two directions separately ask,
// and neither asks both. Finiteness is what makes a count worth
// comparing at all, so only the direction that has to read the counts
// off the sets wants it; the other never counts. Containment is stated
// for the opposite reason — the direction that starts from the numbers
// has no other way to know the sets are nested, while the direction that
// starts from strict containment already carries it.
//
// One law of ordering is spent, and on a mismatch of statements rather
// than on anything about sets: the equivalence compares counts strictly,
// where the converse is stated at a DISAGREEMENT of counts.
// Irreflexivity reconciles the two, since counts that were equal would
// put a number strictly below itself.
var PsubsetIffFewerElements = psubsetIffFewerElementsThm{family.Add(registry.ProofEntry{
	Name: "PsubsetIffFewerElements",
	Key:  "prop_8f5ef1e8c7def1d5",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(t)",
				"s ⊆ t",
			},
			Conclusion: "card(s) < card(t) ⇔ s ⊊ t",
		},
		func(a *Argument, s, t Term, given Fact) {
			countOf := ops(a.Ctx()).Card

			a.Iff()
			a.Forward(
				"counts standing in a strict order disagree, and a containment whose counts disagree is proper",
				func(b *Argument, fewer Fact) {
					b.Show(
						"irreflexivity is what turns the strict order into the disagreement the converse asks for",
						By(
							fewer,
							given,
							// s₀ ⊆ t₀ ∧ card(s₀) ≠ card(t₀) ⇒ s₀ ⊊ t₀ — the
							// containment comes out of `given`, whose
							// finiteness half this side leaves untouched.
							At(PsubsetOfDifferentCount, s, t),
							// ¬(card(s₀) < card(s₀)) — what the hypothesis
							// would collapse to if the counts agreed.
							At(nat_order.LessThanIrrefl, countOf.Apply(s))))
				})
			a.Backward(
				"proper containment forces the strict comparison — the direction that reads both counts",
				func(b *Argument, strict Fact) {
					b.Show(
						"strictness carries its own containment, so this side "+
							"needs nothing from the antecedent but its finiteness",
						// finite(t₀) ∧ s₀ ⊊ t₀ ⇒ card(s₀) < card(t₀)
						By(strict, given, At(CardPsubset, s, t)))
				})
		}),
})}

// AtMostOneIffInSingleton — a finite set counting at most one element and
// a set lying inside some singleton are the same condition.
//
// The two sides are different kinds of statement, which is what makes the
// equivalence worth having: one is a number read off the whole set, the
// other a fact about each of its elements. Below two they say the same
// thing.
//
// The direction that must produce the singleton splits on whether the
// count is zero, and the two cases reach their point in opposite ways.
// At zero the set is empty, and the empty set lies inside EVERY
// singleton — so the containment holds of whatever point is named, and
// this branch never has to name one. Above zero the bound leaves exactly
// one, and a set of size one is a point put into a set of size none: the
// point drops out of the set itself, and the remainder is empty because
// nothing else counts zero.
//
// The converse spends no counting law that is not already a bound. A
// singleton is finite and containment carries finiteness downwards, so
// the finiteness comes for free; and a subset counts no more than its
// container, which here counts one.
//
// The arithmetic is one sentence — at most one and not none is exactly
// one — and it is spelled out rather than decided, so this member reaches
// for no decision procedure. The successor form it lands in is not a
// detour either: it is the form the size clauses are stated in, and the
// step after it consumes exactly that.
var AtMostOneIffInSingleton = atMostOneIffInSingletonThm{family.Add(registry.ProofEntry{
	Name: "AtMostOneIffInSingleton",
	Key:  "prop_7c1a7bfce8c3e148",
	// The context is `arg` rather than the usual `a` because the statement
	// binds `a` for the singleton's point, and the point keeps that name
	// where the proof produces it.
	Build: family.Theorem(
		"∀s:set(A). finite(s) ∧ card(s) ≤ 1 ⇔ ∃a:A. s ⊆ {a}",
		func(arg *Argument, s Term) {
			count := ops(arg.Ctx()).Card.Apply(s)
			zero := arg.Ctx().Numeral(0)

			arg.Iff()
			arg.Forward(
				"a count of at most one leaves the set empty or a single point, and both sit inside a singleton",
				func(b *Argument, given Fact) {
					b.Cases(count.Eq(zero))
					b.When(
						"card(s) = 0: the set is empty, and ∅ lies inside every singleton",
						func(c *Argument, isZero Fact) {
							empty := c.Have(
								"a finite set counted zero admits nothing",
								"s = ∅",
								// finite(s) ⇒ (card(s) = 0 ⇔ s = ∅), whose
								// finiteness the antecedent supplies and
								// whose count the branch does.
								By(isZero, given, At(CardEqZero, s)))

							// The driver settles the existential itself:
							// nothing is inside ∅, so the containment
							// holds of any point at all and none has to
							// be produced. The emptiness just proved is
							// the one fact it consumes; the counts say
							// nothing to a driver with no notion of card
							// and are not handed over.
							c.Show(
								"so the containment holds whatever the singleton is",
								BySets(empty))
						})
					b.Otherwise(
						"card(s) ≠ 0: the bound leaves exactly one, and a set of size one is a point put into nothing",
						func(c *Argument, notZero Fact) {
							one := c.Have(
								"at most one and not none is one — written as a successor, the form the size clauses are stated in",
								"card(s) = suc(0)",
								By(
									Normalized,
									notZero,
									given,
									// 1 = suc(0), which is what puts the
									// bound into successor form.
									nat_arith.OneIsSucZero,
									// card(s) ≤ suc(0) ⇔ card(s) ≤ 0 ∨ card(s) = suc(0)
									At(nat_order.LessEqSucClause, count, zero),
									// card(s) ≤ 0 ⇔ card(s) = 0 — the
									// disjunct the hypothesis rules out.
									At(nat_order.LessEqZeroClause, count)))

							// Having a size is being finite and counting it:
							// the finiteness is the antecedent's, the count the
							// one just established.
							sized := c.Have(
								"counting one IS having size one",
								"has_size(s, suc(0))",
								Simp(Fwd(HasSizeDef)),
								By(given, one))

							point, rest, decomp := c.Obtain2(
								"a set of size suc n is a point put into a set of size n — here n is 0",
								"∃a:A. ∃t:set(A). has_size(t, 0) ∧ s = insert(a, t)",
								// The clauses read at s and 0. Only the
								// successor one is spent: has_size(s, suc(0))
								// ⇔ s is a point put into a set of size 0.
								By(sized, At(HasSizeClauses, s, zero)))

							c.Take(point)

							// What the driver consumes: s is the point
							// inserted into the remainder, and has_size(t, 0)
							// ⇔ t = ∅ at that remainder.
							c.Show(
								"what is left over has size 0, so it is empty: s is that one point "+
									"and nothing else, which is the singleton it was to sit inside",
								BySets(decomp, At(HasSizeZero, rest)))
						})
				})
			arg.Backward(
				"a set inside a singleton is finite and counts no more than the singleton does",
				func(b *Argument, inSingleton Fact) {
					// The point the containment is stated at. Naming it is
					// what lets the three laws below be read at one
					// instance rather than left to be matched up.
					a, inside := b.Unpack(inSingleton) // s ⊆ {a}
					sing := b.Term("{a}")

					b.Show(
						"both halves come off the containment: finiteness travels down "+
							"it, and so does the count, which the singleton fixes at one",
						By(
							inside,
							// finite({a}) — the container, which the two
							// laws below both ask for.
							At(finite_set.FiniteSing, a),
							// finite({a}) ∧ s ⊆ {a} ⇒ finite(s)
							At(finite_set.FiniteSubset, s, sing),
							// finite({a}) ∧ s ⊆ {a} ⇒ card(s) ≤ card({a})
							At(CardSubset, s, sing),
							CardSing))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Counts under union and difference
// ---------------------------------------------------------------------------
//
// The counting calculus proves that counts add over a union of sets that meet
// nowhere. This part is that one fact spent nine ways; each member's
// own doc makes its argument, and this is only the map.
//
// Six readings keep the union. `CardOfDisjointParts` reads the law as a
// DECOMPOSITION, for a set that arrives already in two disjoint pieces,
// and `HasSizeUnion` is that same statement packaged with the finiteness
// it travels with. `CardUnionLe` drops the disjointness and weakens to a
// BOUND; `OverlapOfShortUnion` reads that bound CONTRAPOSITIVELY; and
// `DisjointIffCountsAdd` closes those two into the EQUIVALENCE they were
// always the halves of. `CardUnionMinusOverlap` stops weakening and
// corrects instead — the sum overshoots by exactly the overlap.
//
// `CardLeDiffAdd` reads `CardUnionLe`'s bound at a cover.
//
// Two drop the union and keep the split. `CardDiff` solves it for the
// remainder, and `HasSizeDiff` is again the size-carrying package.
//
// Two things hold file-wide. No induction appears below: all of it is
// in `CardUnion`, and a member that does not cite it reaches it through
// one of the calculus's split entries — `countsLeftAndSurplus` for the
// three that take a union apart at its left operand,
// `countsSubsetAndRest` for the two that split a set at a subset — or
// through a member that does.
//
// **No member subtracts.** Three of them STATE a numeric difference,
// and all three reach it the same way: present the whole as a sum
// ending in the count to be taken away, then let the cancellation that
// inverts addition take it back. On ℕ that is not fastidiousness —
// `m - n` behaves only once `n` is known not to run past `m`, so a proof
// that FORMS a difference owes a guard. A proof that never forms one owes
// nothing, and none of the three does: the difference each states is
// built by its own headline and nowhere else. The equivalence goes
// further and avoids stating one at all, where its obvious route runs
// through inclusion–exclusion.

// CardOfDisjointParts — a finite set presented as two pieces that meet
// nowhere is counted by adding the two pieces' counts.
//
// This is `CardUnion` restated for a set already known to come apart.
// There the union is BUILT and then counted; here a set arrives with a
// name of its own together with a decomposition of it, which is the
// form the law is actually cited in — the set under study is the
// subject, and the two parts are what some case distinction produced.
//
// Nothing about counting is added, and the two steps below are the
// whole of the difference. `CardUnion` asks finiteness of each part
// while the hypothesis grants it only of the whole, so the finiteness
// has to travel down the decomposition — and the parent chapter's
// `finite_set.FiniteUnion` carries it the whole way in one cite.
//
// The decomposition is therefore spent twice, and in opposite
// directions, which is the one thing here worth reading twice. Going
// down it carries the finiteness from u to the parts. Coming back up it
// is a substitution: what `CardUnion` counts is the union, and counting
// u is counting the union because they are the same set.
//
// Transporting the finiteness out of containment instead — `s ⊆ s ∪ t`
// then `finite_set.FiniteSubset`, once per part — arrives the long way
// round: those two are exactly what the parent chapter builds
// `finite_set.FiniteUnion` out of.
var CardOfDisjointParts = cardOfDisjointPartsThm{family.Add(registry.ProofEntry{
	Name: "CardOfDisjointParts",
	Key:  "prop_4db96c6f7af926aa",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t u:set(A).",
			Hypotheses: []string{
				"finite(u)",
				"s ∪ t = u ∧ s ∩ t = ∅",
			},
			Conclusion: "card(u) = card(s) + card(t)",
		},
		// The inner parentheses group the two SET equalities — the
		// decomposition of u — against the finiteness, for the reader:
		// the association of `∧` does not move the statement.
		//
		// `u` is bound but handed nowhere: neither cite is grounded at the
		// whole, and everything the two steps know about it arrives
		// through `given`. It keeps the statement's name because binding
		// is positional and a blank would hide whether the order is right.
		func(a *Argument, s, t, u Term, given Fact) {
			parts := a.Have(
				"u comes apart into s and t, so being finite is something the two parts inherit from it",
				"finite(s) ∧ finite(t)",
				// This is where the decomposition is read downwards: it is
				// what lets the finiteness given of u be read at the union
				// instead, and the equivalence then splits it. The
				// disjointness sits in `given` unspent — finiteness does not
				// care how the parts overlap.
				By(given, finite_set.FiniteUnion))

			a.Show(
				"and two finite parts meeting nowhere are counted by "+
					"adding, which is a count of u because that union IS u",
				// `vocab.go`'s pointwise fold, at the counting law's
				// disjointness guard meeting the decomposition — both spread
				// the same way. Checked by removal: without it the leaf falls
				// through to the refuter.
				By(
					Normalized,
					parts,
					given,
					// finite(s₀) ∧ finite(t₀) ∧ s₀ ∩ t₀ = ∅ ⇒
					// card(s₀ ∪ t₀) = card(s₀) + card(t₀). `given` carries both
					// the disjointness and the decomposition, the latter read
					// upwards this time.
					At(CardUnion, s, t)))
		}),
})}

// CardOfPredicateParts counts a finite set by partitioning it according to a predicate.
var CardOfPredicateParts = cardOfPredicatePartsThm{family.Add(registry.ProofEntry{
	Name: "CardOfPredicateParts",
	Key:  "prop_38a8efa869e984c5",
	Build: family.Theorem(Statement{
		Binders:    "∀T:set(A). ∀P:(A → bool).",
		Hypotheses: []string{"finite(T)"},
		Conclusion: "card(«Yes») + card(«No») = card(T)",
		Abbrev: Abbrev{
			{Name: "Yes", Text: "{x:A | x ∈ T ∧ P(x)}"},
			{Name: "No", Text: "{x:A | x ∈ T ∧ ¬P(x)}"},
		},
	},
		func(a *Argument, T *Expr[Set[A]], P *Arrow[A, Bool], finite Fact) {
			parts := a.Have(
				"the two answers partition T",
				"«Yes» ∪ «No» = T ∧ «Yes» ∩ «No» = ∅",
				BySets())
			a.Show(
				"add the sizes of the two parts",
				By(finite, parts, CardOfDisjointParts.At(a.TermAs[Set[A]]("«Yes»"), a.TermAs[Set[A]]("«No»"), T)))
		}),
})}

// HasSizeUnion — sizes add over a union of two sets that share no
// element.
//
// Having a size is finiteness together with a count, and the theorem
// splits along that seam: the union of two finite sets is finite, and a
// union of disjoint sets counts by adding. Neither half is proved here.
// The first is finite_set.FiniteUnionImp and the second is CardUnion,
// which is where the induction is — so what this member does is take
// the sizes apart and hand each half to the law that already answers
// it.
//
// The hypothesis needs one translation on the way. The theorem states
// disjointness as disjoint while the counting law asks for the
// intersection to be empty, and those are the same thing by definition
// — so a second unfold is the whole of the bridge, and no set-theoretic
// argument is made where a definition suffices.
var HasSizeUnion = hasSizeUnionThm{family.Add(registry.ProofEntry{
	Name: "HasSizeUnion",
	Key:  "prop_6b582866d5a41bdd",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A). ∀m n:num.",
			Hypotheses: []string{
				"has_size(s, m)",
				"has_size(t, n)",
				"disjoint(s, t)",
			},
			Conclusion: "has_size(s ∪ t, m + n)",
		},
		// The antecedent is bound and then dismantled by the two unfoldings
		// below, which put the facts it packs in the context under their
		// own names; nothing ever uses it whole.
		func(a *Argument, s, t, m, n Term, _ Fact) {
			// ↦ finite ∧ card = ·, on all three occurrences at once: four
			// facts assumed, two obligations claimed.
			a.Do(Unfold(HasSizeDef))

			// ↦ (s ∩ t) = ∅, which is what disjoint abbreviates.
			a.Do(Unfold(set_basic.DisjointDef))

			finiteS := a.Hyp("finite(s)")
			finiteT := a.Hyp("finite(t)")
			apart := a.Hyp("s ∩ t = ∅")
			countS := a.Hyp("card(s) = m")
			countT := a.Hyp("card(t) = n")

			a.Do(SplitConj(
				Case(
					"the union is finite, which is all a size asks for besides the count",
					// finite(s) ∧ finite(t) ⇒ finite(s ∪ t). The sizes
					// assumed carry the two premises, and the disjointness
					// is not among them: joining two finite sets stays
					// finite however much they overlap.
					By(finiteS, finiteT, At(finite_set.FiniteUnionImp, s, t))),

				Case(
					"and the count is the sum, nothing lying in both sets to be counted twice",
					// card(s ∪ t) = card(s) + card(t) at these two
					// operands; the two counts assumed are what carry its
					// right-hand side to m + n.
					//
					// `vocab.go`'s fold, at the union count's disjointness
					// condition meeting `apart`. Checked by removal: without
					// it the same premises fail to meet in clause form and
					// the leaf falls through to a refutation it never wanted.
					By(Normalized, finiteS, finiteT, apart, countS, countT, At(CardUnion, s, t))),
			))
		}),
})}

// CardUnionLe — joining two finite sets never costs more than counting
// them apart.
//
// This is CardUnion with its disjointness hypothesis dropped and its
// equation weakened to a bound, and the two changes are the same
// change: an element of both sets is paid for twice on the right and
// once on the left, so the sum runs ahead of the union by exactly the
// overlap. Dropping the hypothesis is what turns an equation into an
// inequality, and the overlap is never measured — it is precisely what
// the inequality allows to go to waste.
//
// So there is no induction here, no case on how the two sets meet, and
// no appeal to CardUnion. The chapter's union split already does the
// work, and does the whole of it: the union's count is s's own plus the
// count of the surplus it holds beyond s, and that surplus lies inside
// t. Everything after that is a comparison of numbers — the surplus is
// bounded by t's count, and adding s's count back leaves the bound
// standing.
//
// The two finiteness hypotheses are spent unequally, and the split is
// where the asymmetry starts: it asks both, being a statement about the
// union. Nothing after it asks s's again — `CardSubset` wants finiteness
// of the containing set alone, and the containing set from there on is
// t. The antecedent is never taken apart, so the premise lists below
// hand the pair undivided; the asymmetry is in the cited statements
// rather than in them.
//
// Splitting at `t ∖ s` instead would mean rebuilding the cover, the
// disjointness, the remainder's finiteness and the disjoint-union count
// in place — which is what `countsSubsetAndRest` already is. Taking the
// split at `s` INSIDE the union is what `countsLeftAndSurplus` packages,
// and asking it for both facts at once is the whole set-theoretic
// content of this member.
var CardUnionLe = cardUnionLeThm{family.Add(registry.ProofEntry{
	Name: "CardUnionLe",
	Key:  "prop_15be226e4846bcb4",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
			},
			Conclusion: "card(s ∪ t) ≤ card(s) + card(t)",
		},
		func(a *Argument, s, t Term, given Fact) {
			countOf := ops(a.Ctx()).Card
			joined := ops(a.Ctx()).Union.Apply(s, t)               // s ∪ t
			outside := ops(a.Ctx()).SetDifference.Apply(joined, s) // what the union holds beyond s

			// The split's two halves, claimed apart because they are
			// consumed apart; see the entry for why that is presentation
			// and not necessity.
			split := a.Have(
				"s lies inside the union, so the union's count is s's own plus what it holds beyond s",
				"card(s ∪ t) = card(s) + card(s ∪ t ∖ s)",
				By(given, At(countsLeftAndSurplus, s, t)))

			fromT := a.Have(
				"and everything it holds beyond s came from t",
				"s ∪ t ∖ s ⊆ t",
				By(given, At(countsLeftAndSurplus, s, t)))

			bound := a.Have(
				"so what lies beyond s counts no more than t itself does",
				"card(s ∪ t ∖ s) ≤ card(t)",
				// finite(t) ∧ (s ∪ t) ∖ s ⊆ t ⇒ card((s ∪ t) ∖ s) ≤ card(t)
				By(given, fromT, At(CardSubset, outside, t)))

			a.Show(
				"and a bound survives having the same count added on its left",
				By(
					split,
					bound,
					// card(s) + card((s ∪ t) ∖ s) ≤ card(s) + card(t)
					// ⇔ card((s ∪ t) ∖ s) ≤ card(t)
					At(nat_order.LessEqAddCancel,
						countOf.Apply(s), countOf.Apply(outside), countOf.Apply(t))))
		}),
})}

// CardLeDiffAdd — a set whose remainder after deleting a finite set is
// finite was finite itself, and counts at most the remainder's count
// plus the deleted set's.
//
// Nothing asks the deleted set to lie inside the first, which is what
// makes this a bound and not `CardDiff`'s equation: the part of t
// outside s is counted on the right and was never in s. Putting t back
// beside the remainder covers s, that cover is a union of two finite
// sets, so s is finite as a subset of it, and `CardUnionLe` bounds the
// cover's count by the two counts.
var CardLeDiffAdd = cardLeDiffAddThm{family.Add(registry.ProofEntry{
	Name: "CardLeDiffAdd",
	Key:  "prop_d742bbf8e31d1b43",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(t)",
				"finite(s ∖ t)",
			},
			Conclusion: "finite(s) ∧ card(s) ≤ card(s ∖ t) + card(t)",
		},
		func(a *Argument, s, t *Expr[Set[A]], finiteT, finiteRest Fact) {
			rest := a.TermAs[Set[A]]("s ∖ t")
			cover := a.TermAs[Set[A]]("(s ∖ t) ∪ t")
			covered := a.Have(
				"putting the deleted set back covers s",
				"s ⊆ (s ∖ t) ∪ t",
				BySets())
			finiteCover := a.Have(
				"the cover is finite",
				"finite((s ∖ t) ∪ t)",
				By(finiteRest, finiteT, finite_set.FiniteUnionImp.At(rest, t)))
			coverBound := a.Have(
				"the cover has at least as many points as s",
				"card(s) ≤ card((s ∖ t) ∪ t)",
				By(covered, finiteCover, CardSubset.At(s, cover)))
			sumBound := a.Have(
				"the cover has at most the sum of the two counts",
				"card((s ∖ t) ∪ t) ≤ card(s ∖ t) + card(t)",
				By(finiteRest, finiteT, CardUnionLe.At(rest, t)))
			a.Show(
				"s is finite and deleting t loses at most its count",
				SplitConj(
					Case(
						"s lies inside the finite cover",
						By(covered, finiteCover, finite_set.FiniteSubset.At(s, cover))),
					Case(
						"the two bounds give the cardinality inequality",
						ByArith(coverBound, sumBound)),
				),
			)
		}),
})}

// OverlapOfShortUnion — two finite sets whose union counts less than
// their counts together must share an element.
//
// This is the disjoint-union count read contrapositively, and there is
// no second phenomenon in it. Counting adds over a union exactly when
// the two sets meet nowhere, so a union falling SHORT of the sum has
// already ruled that out. How far short it falls is never asked — one
// element counted twice and a thousand are the same news here — which
// is why the conclusion is a bare non-emptiness rather than a bound.
//
// The argument is one sentence, and by contradiction only in the sense
// that the goal's own negation is the disjointness `CardUnion` wants:
// meeting nowhere, the two sets would count over their union exactly
// the sum, and the hypothesis puts that same sum strictly below itself.
// Irreflexivity is the whole of what is borrowed from the order — no
// bound is compared and nothing is subtracted — and the finiteness is
// spent entirely inside `CardUnion`, which is the only place a count
// gets read off a set at all.
//
// Reaching this through `DisjointIffCountsAdd` — the equivalence whose
// two halves are the union count and this member — would be a detour:
// the equivalence is what those two assemble INTO, so deriving one back
// out of it goes through a statement that already contains it. Going at
// `CardUnion` directly is what lets this member stand beside the
// equivalence rather than behind it.
var OverlapOfShortUnion = overlapOfShortUnionThm{family.Add(registry.ProofEntry{
	Name: "OverlapOfShortUnion",
	Key:  "prop_60502abc53350ffd",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
				"card(s ∪ t) < card(s) + card(t)",
			},
			Conclusion: "s ∩ t ≠ ∅",
		},
		func(a *Argument, s, t Term, given Fact) {
			a.Show(
				"were the sets disjoint their union would count exactly "+
					"the sum, which the hypothesis puts strictly below itself",
				By(
					given,
					// finite(s₀) ∧ finite(t₀) ∧ (s₀ ∩ t₀) = ∅
					// ⇒ card(s₀ ∪ t₀) = card(s₀) + card(t₀)
					At(CardUnion, s, t),
					nat_order.LessThanIrrefl))
		}),
})}

// DisjointIffCountsAdd — two finite sets are counted together by adding
// their counts exactly when they share no element.
//
// One direction is `CardUnion` and nothing besides: meeting nowhere is
// the condition that law asks for, and the sum is what it returns.
//
// The other is where the equivalence earns its statement, and it turns
// on a count being FAITHFUL in exactly one situation. The union splits
// at s, so its count is s's own plus the count of the surplus it holds
// beyond s. The hypothesis says that same count is s's plus t's, so
// cancelling s's leaves the surplus counting exactly as much as t. The
// same split also puts the surplus inside t — and a subset of a finite
// set carrying the whole of that set's count IS the set. So the surplus
// is all of t: everything t contributes to the union already lies
// outside s, which is to say the two sets meet nowhere.
//
// That step is the only one where a count is asked to determine a set,
// and it is why the theorem is stated of a fixed pair of finite sets
// rather than as a law about numbers. Everywhere else a count forgets
// which elements it counted, and forgetting is harmless here precisely
// because the two sets being compared are nested.
//
// The equivalence is not read off `CardUnionMinusOverlap`, which
// measures the overlap and would reach this conclusion too. The surplus
// beyond s carries the same information and states no difference at
// all, being reached by splitting rather than by subtracting.
var DisjointIffCountsAdd = disjointIffCountsAddThm{family.Add(registry.ProofEntry{
	Name: "DisjointIffCountsAdd",
	Key:  "prop_142b7d31995bd903",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
			},
			Conclusion: "s ∩ t = ∅ ⇔ card(s ∪ t) = card(s) + card(t)",
		},
		func(a *Argument, s, t Term, given Fact) {
			countOf := ops(a.Ctx()).Card
			joined := ops(a.Ctx()).Union.Apply(s, t)               // s ∪ t
			surplus := ops(a.Ctx()).SetDifference.Apply(joined, s) // what the union holds beyond s

			a.Iff()
			a.Forward(
				"meeting nowhere is the disjoint-union count's own hypothesis, and the sum is what it returns",
				func(b *Argument, apart Fact) {
					b.Show(
						"one cite: nothing lies in both sets to be counted twice, so the union counts the two together",
						// finite(s) ∧ finite(t) ∧ s ∩ t = ∅
						// ⇒ card(s ∪ t) = card(s) + card(t)
						//
						// `vocab.go`'s pointwise fold, at the union count's
						// disjointness guard meeting `apart` — both spread
						// the same way. Checked by removal: the leaf closes
						// either way, but without the fold it closes through
						// a refutation, which costs this member a key.
						By(apart, given, At(CardUnion, s, t)))
				})
			a.Backward(
				"a sum the union reproduces exactly pins how much "+
					"of t lies outside s, and there the count is faithful",
				func(b *Argument, countsAdd Fact) {
					// The split's two halves, claimed apart because they are
					// consumed apart — the equation by the cancellation
					// just below, the containment by the faithfulness step
					// two after it; the entry says why that is
					// presentation and not necessity.
					split := b.Have(
						"s lies inside the union, so the union's count is s's own plus its surplus beyond s",
						"card(s ∪ t) = card(s) + card(s ∪ t ∖ s)",
						By(given, At(countsLeftAndSurplus, s, t)))

					surplusCount := b.Have(
						"the hypothesis reads that same count as s's plus t's, so "+
							"cancelling s's leaves the surplus counting as much as t",
						"card(s ∪ t ∖ s) = card(t)",
						// card(s) + card((s ∪ t) ∖ s) = card(s) + card(t)
						// ⇔ card((s ∪ t) ∖ s) = card(t)
						By(
							countsAdd,
							split,
							At(nat_arith.AddEqLCancel,
								countOf.Apply(s), countOf.Apply(surplus), countOf.Apply(t))))

					surplusInT := b.Have(
						"and the surplus came from t",
						"s ∪ t ∖ s ⊆ t",
						By(given, At(countsLeftAndSurplus, s, t)))

					surplusIsT := b.Have(
						"so the surplus is a subset of t carrying t's whole count, and such a subset IS the set",
						"s ∪ t ∖ s = t",
						// finite(t) ∧ (s ∪ t) ∖ s ⊆ t ∧ card((s ∪ t) ∖ s) = card(t)
						// ⇒ (s ∪ t) ∖ s = t.
						//
						// The tuple is (superset, subset), the list_reverse of the
						// two cites above and of the order this entry
						// states; `CardSubsetEq`'s godoc has the reason.
						By(surplusCount, surplusInT, given, At(CardSubsetEq, surplus, t)))

					// What this spends is the equation just established and
					// only it: a set whose join with s loses exactly s is a
					// set s meets nowhere. Over two arbitrary sets that
					// equation alone closes this goal under the driver —
					// the counts say nothing to a driver with no notion of
					// card, so none of them is handed over.
					b.Show(
						"so all of t lies outside s, which is what meeting nowhere says",
						BySets(surplusIsT))
				})
		}),
})}

// CardUnionMinusOverlap — two finite sets are counted together by adding
// their counts and taking the overlap away once.
//
// The overlap is exactly what the sum counts twice: an element of both
// sets is paid for on the left and again on the right of the sum, while
// the union holds it once. `CardUnionLe` throws that surplus away and
// keeps a bound; here it is measured, and measuring it is the whole
// difference between the two members.
//
// The set-theoretic content is one splitting read at two places, and
// the second place is chosen so that the first place's leftover is what
// splits it. The union splits at s, so its count is s's own plus the
// count of the surplus it holds beyond s. That surplus lies inside t,
// and what it leaves of t is precisely the overlap. So t splits at the
// surplus, and t's count is the surplus's plus the overlap's. The
// second fact about the surplus — that removing it from t leaves the
// overlap — is about the constructors alone, and is the one leaf here
// the set driver takes.
//
// Adding the two splits therefore cancels the surplus, which is the
// only quantity they have in common, and leaves inclusion and exclusion
// with nothing subtracted: the overlap's count together with the
// union's is the two sets' counts together. That identity is the last
// place the argument is about sets, and everything after it is
// arithmetic on four opaque numbers.
//
// It is also all the arithmetic there is, which is `CardDiff`'s
// situation exactly: the identity presents the sum as something the
// overlap's count was ADDED to, so no bound on the overlap is ever
// established and the difference appears only in the headline, as the
// thing the unguarded cancellation names.
//
// Citation style below departs from the chapter's ground-witness
// default at one site, where associativity and commutativity are taken
// bare. That step has already put its two splits in as goal rewrites —
// substituting a count for a count is computation, not deduction — so
// what the two laws stand over is an identity between three numbers
// about which nothing whatever is known, and naming them plainly says
// more there than spelled-out instances would.
var CardUnionMinusOverlap = cardUnionMinusOverlapThm{family.Add(registry.ProofEntry{
	Name: "CardUnionMinusOverlap",
	Key:  "prop_b4ae23724a5857bf",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
			},
			Conclusion: "card(s ∪ t) = card(s) + card(t) - card(s ∩ t)",
		},
		func(a *Argument, s, t Term, given Fact) {
			v := ops(a.Ctx())

			joined := v.Union.Apply(s, t)               // s ∪ t
			surplus := v.SetDifference.Apply(joined, s) // what the union holds beyond s
			overlap := v.Intersection.Apply(s, t)       // what both sets hold, counted twice by the sum

			split := a.Have(
				"s lies inside the union, so the union's count is s's own plus its surplus beyond s",
				"card(s ∪ t) = card(s) + card(s ∪ t ∖ s)",
				By(given, At(countsLeftAndSurplus, s, t)))

			surplusInT := a.Have(
				"and the surplus came from t",
				"s ∪ t ∖ s ⊆ t",
				By(given, At(countsLeftAndSurplus, s, t)))

			// This consumes no fact: removing from t everything the union
			// holds beyond s can only leave what both sets held, whatever
			// the two sets are, so the driver is handed nothing.
			leavesOverlap := a.Have(
				"and what the surplus leaves of t is exactly the overlap",
				"t ∖ (s ∪ t ∖ s) = s ∩ t",
				BySets())

			splitT := a.Have(
				"so t splits at the surplus: t's count is the surplus's plus the overlap's",
				"card(t) = card(s ∪ t ∖ s) + card(s ∩ t)",
				// `vocab.go`'s pointwise fold: the set equation above and the
				// split's equation between counts have to meet, and
				// substituting the one into the other is equality work
				// rather than refutation. Checked by removal — without it
				// the close fails naming `Basic` as the fix.
				By(
					Normalized,
					given,
					surplusInT,
					leavesOverlap,
					// The same splitting as above, read at the surplus. Its
					// remainder is what the surplus leaves of t, which the
					// fact above has just identified with the overlap.
					At(countsSubsetAndRest, surplus, t)))

			together := a.Have(
				"adding the two splits cancels the surplus they share",
				"card(s ∩ t) + card(s ∪ t) = card(s) + card(t)",
				splitT.Rw(), // card(t) ↦ card((s ∪ t) ∖ s) + card(s ∩ t)
				split.Rw(),  // card(s ∪ t) ↦ card(s) + card((s ∪ t) ∖ s)
				By(nat_arith.AddAssoc, nat_arith.AddSym))

			// Nothing set-theoretic survives past here: the four counts are
			// opaque numbers, and the finiteness, the containment and the
			// surplus are all spent.
			a.Show(
				"the sum is the union's count with the overlap's added "+
					"on, and monus takes back exactly what addition added",
				// `vocab.go`'s fold at its equation case, as at `CardDiff`'s
				// matching close: everything standing here is an equation
				// between opaque counts, and grounding the two laws is what
				// puts them within reach of substitution.
				By(
					together,
					// card(s ∪ t) + card(s ∩ t) - card(s ∩ t) = card(s ∪ t).
					// Nothing is asked about the size of either summand,
					// which is why no bound on the overlap appears anywhere
					// in this proof.
					At(nat_monus.AddSubCancel, v.Card.Apply(joined), v.Card.Apply(overlap)),
					// card(s ∩ t) + card(s ∪ t) = card(s ∪ t) + card(s ∩ t),
					// which reads the identity above as a sum ending in the
					// count to be taken away.
					At(nat_arith.AddSym, v.Card.Apply(overlap), v.Card.Apply(joined))))
		}),
})}

// CardDiff — what a subset leaves is counted by taking the subset's
// count away from the whole's.
//
// The set-theoretic content is entirely the subset split this chapter
// already states, so nothing here decomposes a set, and no law about
// ∪ or ∩ is cited: the split gives the whole's count as the subset's
// plus the remainder's, and the theorem is that equation read the
// other way round.
//
// Reading it the other way round is where the work is, because on ℕ
// subtraction truncates. `card(s) - card(t)` is a well-behaved quantity
// only once `card(t)` is known not to run past `card(s)`, and that is
// exactly what containment buys. Drop the hypothesis and the two sides
// genuinely part: over s = {1, 2} and t = {2, 3, 4} the difference
// truncates to 0 while the remainder is still inhabited.
//
// But the containment is spent ONCE, on the split, and the guard is
// never established as a fact of its own — the split already presents
// s's count as something t's count was ADDED to. So the containment
// does its work by making the split available, and the difference the
// theorem states is formed only in the headline.
//
// Two consequences worth stating. The disjoint-union count is not
// cited: this chapter's split already carries it, one layer down. And
// the remainder's finiteness is never asked for here either — the split
// asks it internally, of the parent chapter, and the caller never sees
// it.
//
// Naming the two arithmetic laws — the unguarded inverse and
// commutativity — rather than leaving them to the decision procedure is
// what takes this member's capability to nothing.
var CardDiff = cardDiffThm{family.Add(registry.ProofEntry{
	Name: "CardDiff",
	Key:  "prop_3a61a0a5ba044369",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(s)",
				"t ⊆ s",
			},
			Conclusion: "card(s ∖ t) = card(s) - card(t)",
		},
		func(a *Argument, s, t Term, given Fact) {
			countOf := ops(a.Ctx()).Card
			rest := ops(a.Ctx()).SetDifference.Apply(s, t) // what t leaves of s

			// Stated with t's count leading, the order the split returns
			// it in. All the close wants of it is that s's count is a sum
			// with t's as one summand.
			split := a.Have(
				"t and what it leaves cover s between them, so their counts add to s's",
				"card(t) + card(s ∖ t) = card(s)",
				// card(s) = card(t) + card(s ∖ t)
				By(given, At(countsSubsetAndRest, t, s)))

			// Nothing set-theoretic survives into this leaf: the two counts
			// are opaque numbers, and the finiteness and the containment
			// are spent.
			a.Show(
				"s's count is the remainder's with t's added on, and monus takes back exactly what addition added",
				// `vocab.go`'s fold at its equation case: three equations
				// between opaque counts, composed by substitution. Grounding
				// the two laws is what puts them within reach of it —
				// measured, since the same close left UNGROUND reaches the
				// refuter instead and records a key.
				By(
					Normalized,
					split,
					// card(s ∖ t) + card(t) - card(t) = card(s ∖ t), with
					// nothing asked about the size of either summand — which
					// is the whole reason no guard is needed.
					At(nat_monus.AddSubCancel, countOf.Apply(rest), countOf.Apply(t)),
					// card(t) + card(s ∖ t) = card(s ∖ t) + card(t), which
					// moves the count to be taken away to where the
					// cancellation reads it.
					At(nat_arith.AddSym, countOf.Apply(t), countOf.Apply(rest))))
		}),
})}

// HasSizeDiff — removing a subset from a sized set leaves a set whose
// size is the two sizes' difference.
//
// Having a size is finiteness together with a count, and this theorem
// says nothing that is not already one or the other. Unfolding along
// that seam is therefore the whole of the argument: the two sizes
// assumed become four facts, the size claimed becomes two obligations,
// and each obligation is a law of the set difference — the finiteness is
// `finite_set.FiniteDiff`, that a finite set less anything is finite, and
// the count is `CardDiff`, that a finite set less a subset counts the
// difference of the two counts. Neither half is proved here and the two
// never meet.
//
// Two things the unfolding makes visible that the statement hides.
//
// The first is that t's FINITENESS is never spent. Both laws ask
// finiteness only of s, and the premise lists below show it: neither
// names `finite(t₀)`, which sits resident and cleared. That is not an
// economy but the mathematics — t lies inside a finite s, so its
// finiteness was never independent information, and the second size
// hypothesis is present entirely for its COUNT.
//
// The second is that nothing here subtracts. The licence for the
// conclusion's difference not to truncate is the containment, and that
// licence is spent one layer down, inside `CardDiff`, which hands the
// difference back already established. What reaches this file is an
// equation between opaque numbers whose two operands the assumed
// counts merely rename, and the containment appears only to discharge
// `CardDiff`'s own hypothesis.
var HasSizeDiff = hasSizeDiffThm{family.Add(registry.ProofEntry{
	Name: "HasSizeDiff",
	Key:  "prop_d0d931d53b86501",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A). ∀m n:num.",
			Hypotheses: []string{
				"has_size(s, m)",
				"has_size(t, n)",
				"t ⊆ s",
			},
			Conclusion: "has_size(s ∖ t, m - n)",
		},
		// The antecedent is bound and then taken apart by the unfolding
		// below, which puts the facts it packs into the context under
		// their own names; nothing uses it whole.
		func(a *Argument, s, t, m, n Term, _ Fact) {
			// ↦ finite ∧ card = ·, on all three occurrences at once.
			a.Do(Unfold(HasSizeDef))

			finiteS := a.Hyp("finite(s)")
			countS := a.Hyp("card(s) = m")
			countT := a.Hyp("card(t) = n")
			inside := a.Hyp("t ⊆ s")

			a.Do(SplitConj(
				Case(
					"what a subtraction leaves is still finite, and s's "+
						"finiteness alone says so — nothing is asked of what is removed",
					// finite(s₀) ⇒ finite(s₀ ∖ t₀). The containment is not
					// among the premises either: a difference only ever
					// removes, so it stays inside s however t and s lie.
					//
					// The shaping's delta here is the CLOSE it picks: this leaf
					// is one implication discharged against its own antecedent,
					// and Basic does that between the installs. Measured by
					// removal — without it the leaf still closes, by falling
					// through to a refutation of a modus ponens.
					By(finiteS, At(finite_set.FiniteDiff, s, t))),

				Case(
					"and its count is s's less t's, which the two assumed counts rename to m - n",
					// finite(s₀) ∧ t₀ ⊆ s₀ ⇒
					// card(s₀ ∖ t₀) = card(s₀) - card(t₀). The finiteness
					// and the containment discharge its hypothesis; the two
					// counts carry its right-hand side to the size claimed.
					//
					// `vocab.go`'s fold at its equation case: renaming the
					// installed difference's two operands is rewriting with
					// the assumed counts, not refutation, and the monus keeps
					// both apart as opaque atoms until it happens. Measured by
					// removal — without the shaping the leaf falls through to
					// the refuter, which reports the premise list already
					// complete and names Basic as the repair.
					By(Normalized, finiteS, inside, countS, countT, At(CardDiff, s, t))),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Counting a union of a family
// ---------------------------------------------------------------------------
//
// The part above counts a union of TWO sets. This part counts the
// union of a whole finite family of them, provided they come as blocks of
// one size that meet pairwise nowhere.
//
// The two-set law is spent once per block, and how many blocks there are
// is not known in advance, so the one member here is an induction on the
// family.

// HasSizeUnions — a finite family of pairwise disjoint sets, each with m
// elements, has a union of m · card(P) elements: m for every block.
//
// The induction runs over the SUB-FAMILIES of P, one block at a time:
// every finite Q ⊆ P has a union of m · card(Q) elements, and P is a
// sub-family of itself. Carrying the inclusion, rather than the two
// hypotheses on the blocks, is what keeps those hypotheses fixed: they
// are facts about P, read at whichever blocks the step meets, and never
// restated for a smaller family.
//
// With no blocks the union is empty and so is the count, and m copies of
// nothing are nothing. The step lays a new block c into Q. Both lie in P,
// so c has m elements and the induction hypothesis sizes the union of Q.
// Every block of Q is a block of P other than c — c is new to Q — so it
// meets c nowhere, and c therefore meets nothing in the union of Q. That
// union joined to c is the union of insert(c, Q), so `HasSizeUnion` adds
// the two sizes to m + m · card(Q); and a new block counts one more, which
// is what makes that sum m · card(insert(c, Q)).
var HasSizeUnions = hasSizeUnionsThm{family.Add(registry.ProofEntry{
	Name: "HasSizeUnions",
	Key:  "prop_f0a8f8ad44be36a9",
	Build: family.Theorem(
		Statement{
			Binders: "∀P:set(set(A)). ∀m:num.",
			Hypotheses: []string{
				"finite(P)",
				"∀c:set(A). c ∈ P ⇒ has_size(c, m)",
				"∀c d:set(A). c ∈ P ∧ d ∈ P ∧ c ≠ d ⇒ disjoint(c, d)",
			},
			Conclusion: "has_size(⋃P, m * card(P))",
		},
		func(a *Argument, P *Expr[Set[Set[element]]], m *Expr[Nat], given Fact) {
			// The property the induction carries: a sub-family of P has a
			// union of m elements per block.
			sizedWithin := a.TermAs[Fun[Set[Set[element]], Bool]](
				"λQ:set(set(A)). Q ⊆ P ⇒ has_size(⋃Q, m * card(Q))")

			a.Show(
				"so every finite sub-family of P has m elements per "+
					"block in its union, and P is a sub-family of itself",
				ByInduction(finite_set.FiniteInductFresh.At(sizedWithin, P), given, set_order.SubsetRefl.At(P),

					Case(
						"∅: no blocks — the union is empty, the count is zero, and m copies of nothing are nothing",
						// Read at families: card here counts blocks, not points.
						Simp(
							Fwd(set_algebra.UnionsEmpty),
							Fwd(CardClauses.Inst[Set[element]]()),
							Fwd(nat_arith.MulZero),
							Fwd(HasSizeZero)),
						TrivialNormalized()),

					Case(
						"insert: a new block c laid into Q brings m more elements, none of them already in the union of Q",
						Derive(func(b *Argument) {
							c := b.FixAs[Set[element]]("c")
							Q := b.FixAs[Set[Set[element]]]("Q")
							carried := b.Assume() // the property at Q, c ∉ Q, and finite(Q)
							inside := b.Assume()  // insert(c, Q) ⊆ P

							unionOfQ := b.TermAs[Set[element]]("⋃Q")
							sizeOfUnionOfQ := b.TermAs[Nat]("m * card(Q)")

							placed := b.Have(
								"c is a block of P, and Q is still a sub-family of it",
								"c ∈ P ∧ Q ⊆ P",
								By(inside, set_order.InsertSubset.At(Q, P, c)))

							rest := b.Have(
								"so the induction hypothesis sizes the union of Q",
								"has_size(⋃Q, m * card(Q))",
								By(carried, placed))

							block := b.Have(
								"and c, a block of P, has m elements",
								"has_size(c, m)",
								By(given, placed))

							eachApart := b.Have(
								"every block of Q meets c nowhere: it is a block of P, and not c, which is new to Q",
								"∀d:set(A). d ∈ Q ⇒ disjoint(d, c)",
								Derive(func(e *Argument) {
									e.FixAs[Set[element]]("d") // a block of Q, named by the claims below
									inQ := e.Assume()
									inP := e.Have(
										"d is a block of P, Q being a sub-family of it",
										"d ∈ P",
										By(inQ, placed, set_basic.SubsetDef.At(Q, P)))
									e.Show(
										"d is not c, being in Q where c is not, and two different blocks of P meet nowhere",
										By(given, inP, placed, inQ, carried))
								}))

							apart := b.Have(
								"so c meets nothing in the union of Q",
								"disjoint(c, ⋃Q)",
								BySets(eachApart))

							split := b.Have(
								"the union of insert(c, Q) splits at c",
								"⋃insert(c, Q) = c ∪ ⋃Q",
								Cite(set_algebra.UnionsInsert))

							count := b.Have(
								"and a new block counts one more",
								"card(insert(c, Q)) = suc(card(Q))",
								By(carried, InsertCountsOneMore.At(Q, c)))

							b.Show(
								"so the two disjoint pieces add to m + m · card(Q) elements, which is m · suc(card(Q))",
								split.Rw(),                  // ⋃insert(c, Q) ↦ c ∪ ⋃Q
								count.Rw(),                  // card(insert(c, Q)) ↦ suc(card(Q))
								Simp(Fwd(nat_arith.MulSuc)), // m * suc(card(Q)) ↦ m + m * card(Q)
								By(block, rest, apart, HasSizeUnion.At(c, unionOfQ, m, sizeOfUnionOfQ)))
						}))))
		}),
})}

// TaggedCopySize — tagging a sized set by a fixed boolean keeps its size: the
// tagged pairs are the image of the set under an injective pairing.
var TaggedCopySize = taggedCopySizeThm{family.Add(registry.ProofEntry{
	Name: "TaggedCopySize",
	Key:  "prop_f0c498624d997f7",
	Build: family.Theorem(Statement{
		Binders:    "∀b:bool. ∀Z:set(B). ∀n:num.",
		Hypotheses: []string{"has_size(Z, n)"},
		Conclusion: "has_size(«tagged», n)",
		Abbrev: Abbrev{
			{Name: "tagged", Text: "{p:prod(bool, B) | (fst(p) ⇔ b) ∧ snd(p) ∈ Z}"},
		},
	},
		func(a *Argument, b *Expr[Bool], Z *Expr[Set[B]], n *Expr[Nat], sized Fact) {
			tagging := a.TermAs[Fun[B, Prod[Bool, B]]]("λx:B. (b, x)")
			injective := a.Have(
				"tagging by b is injective",
				"injective_on(Z, λx:B. (b, x))",
				Unfold(functions.InjectiveOnDef),
				By(pairs.PairEq))
			image := a.Have(
				"the tagged pairs are the image of Z",
				"«tagged» = image(λx:B. (b, x), Z)",
				Derive(func(c *Argument) {
					c.Do(Simp(Fwd(set_basic.Extension)))
					p := c.FixAs[Prod[Bool, B]]("p")
					member := set_basic.InImage.At(tagging, Z, p)
					c.Iff()
					c.Forward(
						"a pair is its tag and value",
						func(e *Argument, tagged Fact) {
							written := e.Have(
								"p is the tagged element at its own value",
								"∃x:B. p = (b, x) ∧ x ∈ Z",
								Witness(e.TermAs[B]("snd(p)")),
								By(Normalized, tagged, pairs.PairEta.At(p)))
							e.Show(
								"so it lies in the image",
								By(written, member))
						})
					c.Backward(
						"a tagged element has that tag and value",
						func(e *Argument, tagged Fact) {
							_, written := e.ObtainAs[B](
								"p is a tagged element of Z",
								"∃x:B. p = (b, x) ∧ x ∈ Z",
								By(tagged, member))
							e.Show(
								"the projections read it off",
								By(Normalized, written, pairs.Fst, pairs.Snd))
						})
				}))
			a.Show(
				"the image of an injective map has the size of its source",
				By(image, sized, injective, HasSizeImageInj.At(tagging, Z, n)))
		}),
})}

// TaggedUnionCount — tagging two finite sets by false and by true gives a
// finite set whose size is the sum: each tagged copy has the size of its set,
// and the two copies are disjoint.
var TaggedUnionCount = taggedUnionCountThm{family.Add(registry.ProofEntry{
	Name: "TaggedUnionCount",
	Key:  "prop_14042b94f0d3c858",
	Build: family.Theorem(Statement{
		Binders: "∀X Y:set(B).",
		Hypotheses: []string{
			"finite(X)",
			"finite(Y)",
		},
		Conclusion: "finite(«tagged») ∧ card(«tagged») = card(X) + card(Y)",
		Abbrev: Abbrev{
			{Name: "tagged", Text: "{p:prod(bool, B) | (¬fst(p) ∧ snd(p) ∈ X) ∨ (fst(p) ∧ snd(p) ∈ Y)}"},
			{Name: "copy", Text: "λb:bool. λZ:set(B). {p:prod(bool, B) | (fst(p) ⇔ b) ∧ snd(p) ∈ Z}"},
		},
	},
		func(a *Argument, X, Y *Expr[Set[B]], finiteX, finiteY Fact) {
			tagFalse := a.TermAs[Bool]("⊥")
			tagTrue := a.TermAs[Bool]("⊤")
			copyOfX := a.TermAs[Set[Prod[Bool, B]]]("«copy»(⊥, X)")
			copyOfY := a.TermAs[Set[Prod[Bool, B]]]("«copy»(⊤, Y)")
			sizeOfX := a.TermAs[Nat]("card(X)")
			sizeOfY := a.TermAs[Nat]("card(Y)")
			sizes := a.Have(
				"each tagged copy is finite, of the size of its set",
				"finite(«copy»(⊥, X)) ∧ "+
					"card(«copy»(⊥, X)) = card(X) ∧ "+
					"finite(«copy»(⊤, Y)) ∧ "+
					"card(«copy»(⊤, Y)) = card(Y)",
				By(
					finiteX,
					finiteY,
					HasSizeDef.At(X, sizeOfX),
					HasSizeDef.At(Y, sizeOfY),
					TaggedCopySize.At(tagFalse, X, sizeOfX),
					TaggedCopySize.At(tagTrue, Y, sizeOfY),
					HasSizeDef.At(copyOfX, sizeOfX),
					HasSizeDef.At(copyOfY, sizeOfY)))
			disjoint := a.Have(
				"the two copies are disjoint, their tags differing",
				"«copy»(⊥, X) ∩ «copy»(⊤, Y) = ∅",
				BySets())
			union := a.Have(
				"the tagged set is the union of the copies",
				"«tagged» = «copy»(⊥, X) ∪ «copy»(⊤, Y)",
				BySets())
			a.Show(
				"the sizes of disjoint finite sets add",
				union.Rw(),
				By(
					Normalized,
					sizes,
					disjoint,
					finite_set.FiniteUnionImp.At(copyOfX, copyOfY),
					CardUnion.At(copyOfX, copyOfY)))
		}),
})}
