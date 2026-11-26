// finite_set.go — the chapter: finiteness.
//
// Seven parts, marked by banners:
//
// - Finiteness of the families a set carries
// - The finite predicate, and the principles the definition comes with
// - Finiteness and the subset order
// - Induction over finitely supported functions
// - Finiteness survives the set constructions
// - Finiteness travels along a map
// - The chapter read the other way round

package finite_set

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/internal/setvocab"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Finiteness of the families a set carries
// ---------------------------------------------------------------------------
//
// Two strands, read as one file. The first is about sets written
// `{… | …}` over a finite `s`, and its members divide by what the
// builder ranges over — which is the whole difference between them.
// The second drops the builder and keeps only the second type level:
// there the subject is a family of sets ordered by inclusion, and what
// finiteness buys is an element at either end of that order.
//
// The file opens below either strand, with a statement carrying no
// finiteness at all: PowersetClauses, which says how the collection of
// subsets is BUILT — nothing lies inside ∅ but ∅, and enlarging a set
// by a point doubles its subsets, the new half being the old one with
// that point put in. It sits in this chapter because what it describes
// is what the strand's first member counts.
//
// A builder ranging over the POINTS of `s` can only ever thin it out,
// so it is bounded by `s` before anything is proved: that is
// FiniteRestrict, and it is three lines. A builder ranging over the
// SUBSETS of `s` manufactures sets `s` never contained, so there is no
// ambient collection to bound it by and one has to be BUILT. That is
// FinitePowerset, whose induction step IS the doubling above read at a
// finite set, and which is the first theorem in this chapter to live at
// two type levels at once — its subject is a collection of sets while
// its induction runs over a set of points.
//
// Once the powerset exists it is the bound wherever a member of THIS
// strand needs one: it bounds a family of subsets cut down by any
// condition at all (FiniteRestrictedSubsets), and it bounds the family
// generating a union (the forward half of FiniteUnions).
// FinitePowersetEq is the odd one out — its ⇒ half is FinitePowerset,
// but its ⇐ half does not use the powerset at all, deriving the
// converse from the singleton embedding instead. FiniteFiniteUnions
// spends no powerset either: it is FiniteUnions read under the extra
// hypothesis that the family is finite, and the passage between them is
// propositional. Neither does the chain strand, which never bounds a
// family by a collection at all.
//
// Read another way, this strand is the constructions part's one move — exhibit an
// inclusion and let FiniteSubset finish — carried out one type level
// up, four more times. The difference is that at collections the
// bounding set is not lying around: it has to be built, and building
// it is what FinitePowerset is for.
//
// The two type levels stay visible throughout. Reading one of this
// chapter's own laws one level up is what the typed wrappers' `Inst`
// does at the collection type; an INDUCTION needs the same instance in
// a second shape, the law as its own file states it, which is the form
// obligations are read off and the form an assembly does modus ponens
// with, and `ByInduction` installs its principle in that form at
// whichever instance the cite names.
//
// FiniteTransitivityChain is the one member here with no set-builder
// and no second type level in it: its subject is a finite set carrying
// a relation. It reads against the builder strand as the case where
// what the induction carries is not a finiteness claim at all.
//
// The chain strand turns the level story the other way round: its
// subject is a family, and what it produces is a SET or a member of the
// family rather than a finiteness claim. FiniteSubsetUnions extracts a
// finite subfamily from an arbitrary one, spending the covered set's
// finiteness and nothing else; UnionsInChain and IntersInChain are duals
// saying that a non-empty finite chain has a largest and a smallest
// member and that those are exactly its ⋃ and its ⋂. The covering theorem
// inducts over the covered set. The chain theorems apply
// FiniteTransitivityChain to strict inclusion and its reverse, obtaining
// an extremal member which comparability identifies with ⋃ or ⋂.
//
// FiniteSubsetUnionsChain closes that strand by spending two of them at
// once: the finiteness it needs has already been made into a finite subfamily by
// the first, and the largest member of a chain is what the second hands
// back. What is left for it to do is the case the two leave between
// them, where the subfamily comes back empty.
//
// The two product members at the end range over neither the points of a
// set nor its subsets but over PAIRS of points drawn from two sets at
// once, and they carry the file's level story to a third type.
// FiniteProductDependent's map lands in a type independent of both its
// arguments'; FiniteProduct's is the pairing, which lands in one BUILT
// from them. Between them they settle what the cross-type machinery is
// actually for: **whether the landing type is named or built is what
// decides**, not how many levels a statement spans. The two sites carry
// the derivation.
//
// Each member's own argument is in its entry doc; the sections are
// documented where they are defined.

// PowersetClauses — the collection of subsets of a set, read
// recursively.
//
// Both clauses are set identities, and the step one is a mutual
// inclusion. Its hard half turns on whether a subset of the enlarged
// set holds the new point: one that misses it keeps nothing outside the
// old set, and one that holds it is its own deletion of that point — a
// subset of the old set — with the point put back. The other half asks
// nothing: a subset of the old set, and one of those with the point
// inserted, are both subsets of the enlarged set.
//
// The case analysis names the smaller subset EXISTENTIALLY rather than
// as the term `delete(u, a)`, and that is what leaves the first
// inclusion one call to the set driver: existentially named, the second
// disjunct IS a membership in the image and the driver reads it off the
// shape. Spelled as the deletion the driver would instead have to
// re-derive `insert(a, delete(u, a)) = u` — which is InsertDelete,
// cited inside the case analysis, and not something the driver produces
// for itself.
//
// The two clauses stand at INDEPENDENT element types, and that is the
// theorem and not a slip: the base clause names no set the step clause
// names, so nothing ties its element type to the step's.
var PowersetClauses = powersetClausesThm{family.Add(registry.ProofEntry{
	Name: "PowersetClauses",
	Key:  "prop_c3903489351acded",
	Build: family.Theorem(
		"{t:set(B) | t ⊆ ∅⟨A:B⟩} = {∅⟨A:B⟩} ∧ "+
			"(∀a:A. ∀s:set(A). "+
			"    {t:set(A) | t ⊆ insert(a, s)} = "+
			"    {t:set(A) | t ⊆ s} ∪ image(λt:set(A). insert(a, t), {t:set(A) | t ⊆ s}))",
		func(arg *Argument) {
			arg.Do(SplitConj(
				Case(
					"at ∅: nothing is below ∅ but ∅ itself, so ∅ carries exactly one subset",
					BySets()),

				Case(
					"across insert: whether a subset holds the new point decides which "+
						"half it belongs to, and the two halves are the whole collection",
					Derive(func(b *Argument) {
						a, s := b.Fix(), b.Fix()

						enlargedSubsets := b.Term("{t:set(A) | t ⊆ insert(a, s)}")
						halves := b.Term("{t:set(A) | t ⊆ s} ∪ image(λt:set(A). insert(a, t), {t:set(A) | t ⊆ s})")

						split := b.Have(
							"a subset of the enlarged set either misses a, and is "+
								"then one of s's own, or is one of s's own with a put in",
							"∀u:set(A). u ⊆ insert(a, s) ⇒ u ⊆ s ∨ (∃v:set(A). v ⊆ s ∧ u = insert(a, v))",
							Derive(func(c *Argument) {
								u := c.Fix()
								below := c.Assume()

								holds := c.Assuming(
									c.Term("a ∈ u"),
									"a subset that misses a keeps nothing outside s, so it is one of s's own",
									Given(func(d *Argument, misses Fact) {
										d.Do(BySets(below, misses))
									}))

								c.Show(
									"and one that holds a is u without a, which sits inside s, with a put back",
									By(
										below,
										holds,
										// Each in its own dep's stated order,
										// which puts the subset first and the
										// point last.
										At(set_order.SubsetInsertDelete, u, s, a),
										At(set_algebra.InsertDelete, u, a)))
							}))

						lands := b.Have(
							"so the subsets of the enlarged set all lie in the union of the two halves",
							"{t:set(A) | t ⊆ insert(a, s)} ⊆ "+
								"{t:set(A) | t ⊆ s} ∪ image(λt:set(A). insert(a, t), {t:set(A) | t ⊆ s})",
							BySets(split))

						covers := b.Have(
							"and that union holds nothing else, since a subset of s and "+
								"one of those with a put in are both subsets of the enlarged set",
							"{t:set(A) | t ⊆ s} ∪ image(λt:set(A). insert(a, t), {t:set(A) | t ⊆ s}) ⊆ "+
								"{t:set(A) | t ⊆ insert(a, s)}",
							BySets())

						b.Show(
							"so the two collections include each other, and a set is nothing but what it admits",
							By(
								lands,
								covers,
								// Stated order: the identity's two sides, left
								// first. Both are collections at one type, so a
								// swap would type-check and pair each inclusion
								// with the wrong side.
								At(set_order.SubsetAntisym, enlargedSubsets, halves)))
					})),
			))
		}),
})}

// FinitePowerset — a finite set has finitely many subsets.
//
// Induction on `s`, at the property "this set has a finite powerset".
// Each case is one clause of PowersetClauses above, read as a rewrite of
// the collection standing under finite, and what is left is a finiteness
// fact about what the clause put there. Below ∅ there is nothing but ∅,
// so the collection of subsets is the empty collection with one
// insertion and finite's own two rules reach it. Enlarging a set by `x`
// replaces its collection of subsets by the union of the old collection
// with the image of that collection under `v ↦ insert(x, v)`, and
// finiteness survives an image and survives a union of two.
//
// Nothing here assumes `x` was outside `s`: the clause holds either way,
// and if `x` was in `s` the two halves simply overlap. That is why the
// plain induction principle is enough and the strong one, which hands
// over `x ∉ s`, is not needed.
var FinitePowerset = finitePowersetThm{family.Add(registry.ProofEntry{
	Name: "FinitePowerset",
	Key:  "prop_166b62093b1c8b79",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "finite({t:set(A) | t ⊆ s})",
		},
		func(a *Argument, s Term, finiteS Fact) {
			// Both cases rewrite by a clause, and both want it as the
			// chapter STATES it — an equation between COLLECTIONS, which
			// is what stands under finite here. A set equation's canonical
			// rewriting form is the same fact read pointwise, and a
			// membership equivalence rewrites no collection. The two
			// clauses stand at independent element types, so neither is
			// pinned by the other: both are named, and both are this
			// chapter's points.
			clauses := PowersetClauses.Inst(TypeBinder.BindA[element](), TypeBinder.BindB[element]())

			a.Show(
				"so the induction carries the property to every finite set, and s is one of them",
				ByInduction(FiniteInduct, finiteS,
					Case(
						"at ∅: nothing lies below ∅ but ∅ itself, so the collection "+
							"of subsets is the empty collection with one insertion",
						Derive(func(b *Argument) {
							// ↦ finite({∅})
							b.Do(Simp(Fwd(clauses)))

							// ∅ is nullary, so a use site has nothing to read
							// an instance from, and this leaf needs it at
							// BOTH levels at once: the empty set of points,
							// which {∅} holds, and the empty collection of
							// sets, which {∅} inserts into.
							noPointsTerm := setvocab.Pinned(b.Ctx(), "empty_set")
							noFamilyTerm := setvocab.PinnedAt(b.Ctx(), "empty_set", setType())

							b.Show(
								"and finite's own two rules reach that collection",
								// finite(∅ₛₑₜₛ), and finite(∅ₛₑₜₛ) ⇒
								// finite(insert(∅ₚₒᵢₙₜₛ, ∅ₛₑₜₛ)) = finite({∅}).
								// FiniteRules' stated `∀x:A. ∀s:set(A)`
								// order: noPointsTerm fills the `x` slot,
								// noFamilyTerm the `s` slot.
								By(FiniteRules.Inst[elementSet]().At(noPointsTerm, noFamilyTerm)))
						})),
					Case(
						"across insert: the enlarged set's subsets are the counted ones "+
							"together with their x-augmentations, and each half is finite",
						Derive(func(b *Argument) {
							// The principle's own set binder is `s`, which
							// the section holds — so the induction set is
							// NAMED. Both fixes are spelled by name in the
							// terms below.
							b.Fix()               // x, the point the step adds
							b.Fix("u")            // the set it is added to
							counted := b.Assume() // finite({t | t ⊆ u})

							oldTerm := b.Term("{t:set(A) | t ⊆ u}")
							augmentedTerm := b.Term("image(λv:set(A). insert(x, v), {t:set(A) | t ⊆ u})")

							// ↦ finite({t | t ⊆ u} ∪ image(λv. insert(x, v), {t | t ⊆ u}))
							b.Do(Simp(Fwd(clauses)))

							b.Show(
								"both halves are finite — the counted subsets by the hypothesis, "+
									"their x-augmentations as an image of those — and so is their union",
								By(
									counted,
									// FiniteImage's stated `∀f. ∀s` order:
									// the augmentation map first, then the
									// counted subsets it carries.
									FiniteImage.Inst(TypeBinder.BindA[elementSet](), TypeBinder.BindB[elementSet]()).
										At(b.Term("λv:set(A). insert(x, v)"), oldTerm),
									// Positional; both operands have the same
									// type, so the order is the only thing
									// distinguishing left from right.
									FiniteUnionImp.Inst[elementSet]().
										At(oldTerm, augmentedTerm)))
						}))))
		}),
})}

// noPoints spells the empty set of points, the element level of the two
// levels the members below live on. How to read the `⟨A:τ⟩` annotation
// is in vocab.go, beside the two type functions.
//
// It is text and not a pin because the chapter's usual answer, pinning
// the name at a chosen type, cannot serve here. It answers at ONE level
// — whichever was asked for first — and the members below state both: an
// induction principle over families reads P(∅) at the collection level
// while the property it carries reads ∅ at the element level.
//
// A member wanting the empty set as a TERM at either level names it
// `noFamilyTerm` / `noPointsTerm`, so that one object keeps one name
// across both kinds.
const (
	noPoints = "∅⟨A:A⟩"
)

// FinitePowersetEq — a set is finite exactly when its powerset is.
//
// One direction is FinitePowerset above. The other is the reason the
// equivalence is worth stating: a collection of subsets can be finite
// for no better reason than that there are few subsets to have, so it
// has to be shown that a small powerset leaves no room for a large `s`.
//
// The witness is the singleton map `x ↦ {x}`. It sends `s` into the
// powerset — a singleton drawn from `s` is one of `s`'s subsets — so
// the singletons form a finite collection; and it separates the points
// of `s`, since a one-element set determines its element. A map that
// separates points neither creates nor destroys finiteness, so `s` is
// as finite as its singletons are.
var FinitePowersetEq = finitePowersetEqThm{family.Add(registry.ProofEntry{
	Name: "FinitePowersetEq",
	Key:  "prop_5444c161a8704525",
	Build: family.Theorem(
		"∀s:set(A). finite({t:set(A) | t ⊆ s}) ⇔ finite(s)",
		func(a *Argument, s Term) {
			a.Iff()
			a.Forward(
				"and a finite powerset leaves room for only finitely "+
					"many points, since each of them is a subset on its own",
				func(b *Argument, finitePowerset Fact) {
					// The singleton map's image — `s` copied one point at
					// a time into the collection level, which is where
					// the powerset lives and `s` itself does not.
					within := b.Have(
						"a singleton drawn from s is one of s's subsets, so the singletons all lie in the powerset",
						"image(λx:A. {x}, s) ⊆ {t:set(A) | t ⊆ s}",
						BySets())

					spread := b.Have(
						"so there are only finitely many of them",
						"finite(image(λx:A. {x}, s))",
						By(
							finitePowerset,
							within,
							// Positional: the install prefix takes the SMALL
							// collection first, then the bounding one — here
							// the singletons inside the powerset. Both are
							// collections of sets, so a swap would type-check
							// and state the converse.
							FiniteSubset.Inst[elementSet]().
								At(b.Term("image(λx:A. {x}, s)"), b.Term("{t:set(A) | t ⊆ s}"))))

					distinct := b.Have(
						"and no two points share a singleton, a one-element set being determined by its element",
						"injective_on(s, λx:A. {x})",
						Simp(
							Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[element](), TypeBinder.BindB[elementSet]()))),
						BySets())

					b.Show(
						"so s has exactly as many points as its singletons have, and finitely many of those",
						By(
							spread,
							distinct,
							// Also cross-level, though only half of it is:
							// FiniteImageInjEq already states two element
							// types, and it is the TARGET one that lands at
							// the collection level here — its type arguments
							// are (source, target) in that order.
							//
							// The law's stated `∀f. ∀s` order: the
							// singleton map first, then the set.
							FiniteImageInjEq.Inst(TypeBinder.BindA[element](), TypeBinder.BindB[elementSet]()).
								At(b.Term("λx:A. {x}"), s)))
				})
			a.Backward(
				"a finite set has only finitely many subsets — the induction above",
				func(b *Argument, finiteS Fact) {
					b.Show(
						"FinitePowerset at s",
						By(finiteS, At(FinitePowerset, s)))
				})
		}),
})}

// FiniteRestrict — cutting a finite set down by any condition at all
// leaves a finite set.
//
// Nothing is assumed about the condition, and nothing needs to be: a
// restriction only ever removes points, so what survives it is bounded
// by the set it was cut from. This is the constructions part's move — exhibit the
// inclusion, and FiniteSubset finishes — read at the inclusion a
// set-builder gives rather than at one of the set operations.
var FiniteRestrict = finiteRestrictThm{family.Add(registry.ProofEntry{
	Name: "FiniteRestrict",
	Key:  "prop_c3904fe36af4c9bc",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀P:(A → bool).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "finite({x:A | x ∈ s ∧ P(x)})",
		},
		func(a *Argument, s, P Term, finiteS Fact) {
			within := a.Have(
				"what the condition keeps was in s to begin with",
				"{x:A | x ∈ s ∧ P(x)} ⊆ s",
				BySets())

			a.Show(
				"so the restriction is bounded by s, which is finite",
				By(finiteS, within, At(FiniteSubset, a.Term("{x:A | x ∈ s ∧ P(x)}"), s)))
		}),
})}

// FiniteRestrictedSubsets — imposing any condition at all on the
// subsets of a finite set leaves finitely many of them.
//
// This is FiniteRestrict's argument read one level up, and the two are
// worth reading together: both cut a collection down by a condition
// nothing is assumed about, and both are settled by naming the thing
// the survivors were drawn from. What changes with the level is that
// the ambient collection is no longer given. A restriction of `s`
// lands inside `s`; a restriction of `s`'s subsets lands inside `s`'s
// powerset, which is finite only because FinitePowerset above says so.
// The two proofs are the same three lines against different bounds,
// and at different types, so neither is a case of the other.
var FiniteRestrictedSubsets = finiteRestrictedSubsetsThm{family.Add(registry.ProofEntry{
	Name: "FiniteRestrictedSubsets",
	Key:  "prop_17a8da2fcba162a7",
	Build: family.Theorem(
		Statement{
			Binders: "∀P:(set(A) → bool). ∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "finite({t:set(A) | P(t) ∧ t ⊆ s})",
		},
		func(a *Argument, P, s Term, finiteS Fact) {
			within := a.Have(
				"whatever the condition keeps was a subset of s to begin with",
				"{t:set(A) | P(t) ∧ t ⊆ s} ⊆ {t:set(A) | t ⊆ s}",
				BySets())

			all := a.Have(
				"and s, being finite, has only finitely many subsets in all",
				"finite({t:set(A) | t ⊆ s})",
				By(finiteS, At(FinitePowerset, s)))

			a.Show(
				"so the survivors are bounded by a finite collection",
				By(
					all,
					within,
					// Stated `∀s. ∀t` order: the SMALL collection first, then
					// the bounding one — the survivors inside the powerset.
					FiniteSubset.Inst[elementSet]().
						At(a.Term("{t:set(A) | P(t) ∧ t ⊆ s}"), a.Term("{t:set(A) | t ⊆ s}"))))
		}),
})}

// FiniteUnions — a union over a family of sets is finite exactly when
// the family is finite and so is every set in it.
//
// Both conditions are needed and neither is free, so the two directions
// are separate arguments.
//
// Backwards is the constructive one, and the only induction in this
// file running over a family rather than over a set: the union of
// nothing is nothing, and one more member adds exactly its own points,
// so a family assembled by finitely many INSERTs has a union assembled
// by finitely many UNIONs.
//
// Forwards needs no induction at all, only the observation that every
// member of a family is contained in that family's union — which is
// what a union is. Each member is then finite for the same reason the
// union is; and the family, being a collection of subsets of the
// union, sits inside the union's powerset.
//
// That last step is the one worth pausing on. It bounds the family by
// a collection the family is not a member of and has no evident
// relation to, and the powerset is the only construction in this
// chapter supplying such a bound at all.
var FiniteUnions = finiteUnionsThm{family.Add(registry.ProofEntry{
	Name: "FiniteUnions",
	Key:  "prop_1c64d6ef2ce734f3",
	Build: family.Sections(
		"∀s:set(set(A)). finite(⋃s) ⇔ finite(s) ∧ (∀t:set(A). t ∈ s ⇒ finite(t))",
		func(ctx *Script, headline string) *GoalStackNode {
			// The whole of the backward direction, and a section of its own
			// because it is an induction and the equivalence's other half is
			// not: folding the two together would put an induction principle
			// in the way of an argument three citations long.
			//
			// The induction runs over the FAMILY, so the finiteness being
			// consumed is at the collection level while the finiteness being
			// produced is at the element level — the two ends of ⋃.
			unionsOfFinite := ctx.Lemma(
				"∀s:set(set(A)). finite(s) ⇒ (∀t:set(A). t ∈ s ⇒ finite(t)) ⇒ finite(⋃s)",
				func(a *Argument, s Term, finiteS, finiteMembers Fact) {
					a.Show(
						"so the induction carries the property to every finite family, and s is one of them",
						ByInduction(FiniteInduct, finiteS, Generalizing(finiteMembers),
							Case(
								"at ∅: no member contributes a point, so the union is ∅ — and ∅ is finite",
								// Both bare: set_algebra.UnionsEmpty binds nothing,
								// and the clause of FiniteRules in play here is the
								// ∅ one, which binds nothing either.
								By(set_algebra.UnionsEmpty, FiniteRules)),
							Case(
								"across insert: the new member contributes exactly its own "+
									"points, and it is finite like the ones already collected",
								Derive(func(b *Argument) {
									// The principle's own family binder is `s`,
									// which the section holds — so the induction
									// family is NAMED.
									x, u := b.Fix(), b.Fix("u")
									carried := b.Assume() // the IH, itself conditional
									// The enlarged family's members are all finite.
									allFinite := b.Assume()

									newOne := b.Have(
										"the new member is finite, the enlarged family holding it",
										"finite(x)",
										BySets(allFinite))

									oldOnes := b.Have(
										"and so is each member the family already had, the enlarged family holding those too",
										"∀t:set(A). t ∈ u ⇒ finite(t)",
										BySets(allFinite))

									b.Show(
										"so the enlarged union is the new member joined to the "+
											"old union, and a union of two finite sets is finite",
										By(
											newOne,
											oldOnes,
											carried,
											At(set_algebra.UnionsInsert, u, x), // ⋃insert(x, u) = x ∪ ⋃u
											At(FiniteUnionImp, x, b.Term("⋃u"))))
								}))))
				})

			return ctx.Theorem(headline, func(a *Argument, s Term) {
				unionTerm := a.Term("⋃s")

				a.Iff()
				a.Forward(
					"and a finite union bounds the family and each of its members at once",
					func(b *Argument, finiteUnion Fact) {
						below := b.Have(
							"a member of the family is contained in the union it helps make",
							"∀t:set(A). t ∈ s ⇒ t ⊆ ⋃s",
							By(set_order.MemberSubsetUnions))

						b.Do(SplitConj(
							Case(
								"the family is finite: its members being subsets of the union, it sits inside the union's powerset",
								Derive(func(c *Argument) {
									within := c.Have(
										"which is to say the family is one of the collections of subsets of the union",
										"s ⊆ {t:set(A) | t ⊆ ⋃s}",
										BySets())

									all := c.Have(
										"and there are finitely many of those, the union being finite",
										"finite({t:set(A) | t ⊆ ⋃s})",
										By(finiteUnion, At(FinitePowerset, unionTerm)))

									c.Show(
										"so the family is bounded by a finite collection",
										By(
											all,
											within,
											// Positional: the install prefix
											// takes the SMALL collection
											// first — the family inside the
											// powerset.
											FiniteSubset.Inst[elementSet]().
												At(s, c.Term("{t:set(A) | t ⊆ ⋃s}"))))
								})),
							Case(
								"and each member is finite, being one of those subsets",
								Derive(func(c *Argument) {
									t := c.Fix()
									inFamily := c.Assume()
									c.Show(
										"so t is bounded by the finite union",
										By(finiteUnion, inFamily, below.At(t), At(FiniteSubset, t, unionTerm)))
								})),
						))
					})
				a.Backward(
					"a finite family of finite sets has a finite union — the induction above",
					func(b *Argument, both Fact) {
						b.Show(
							"which is what the induction concluded",
							By(both, unionsOfFinite))
					})
			})
		}),
})}

// FiniteFiniteUnions — for a family already known finite, the union is
// finite exactly when every member of it is.
//
// FiniteUnions settles the same question without assuming anything
// about the family, and asks two things of it in return. Grant the
// first of those two up front and the equivalence keeps only the
// second: a conjunct known to hold is discharged wherever it stands,
// and here it stands on the side of the equivalence that speaks about
// the family. So this member is its sibling read under an extra
// hypothesis, the passage between them is propositional, and nothing
// about unions is proved a second time.
//
// There is an independent route, and it is worth knowing it exists: the
// equivalence can be carried over the family by induction directly,
// from the introduction rules and the two clauses saying what one more
// member contributes. That route needs no powerset — which is the one
// construction the sibling's forward half is built on — because the
// family's finiteness is granted here rather than concluded. It is not
// redundant, merely longer, and the citation above is preferred for
// being the same fact said once.
var FiniteFiniteUnions = finiteFiniteUnionsThm{family.Add(registry.ProofEntry{
	Name: "FiniteFiniteUnions",
	Key:  "prop_bb4d7a6d79f3c062",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(set(A)).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "finite(⋃s) ⇔ ∀t:set(A). t ∈ s ⇒ finite(t)",
		},
		func(a *Argument, s Term, finiteS Fact) {
			a.Show(
				"FiniteUnions at s, whose family conjunct this hypothesis supplies "+
					"— the ⇐ direction asks for it, the ⇒ drops it by weakening",
				By(finiteS, At(FiniteUnions, s)))
		}),
})}

// FiniteSubsetUnions — a finite set covered by a family is already
// covered by finitely many of that family's members.
//
// The family itself is arbitrary — it may be uncountable, and no member
// of it need be finite. What the theorem extracts is a finite SUBFAMILY,
// and the finiteness it spends to do so is the covered set's.
//
// Induction on that set, at the property "whatever this set is covered
// by, finitely many members of f cover it". Over ∅ there is nothing to
// cover and the empty subfamily will do. One more point is covered by
// the family, so it lies in SOME member of it; adjoin that member to
// the subfamily the induction hypothesis supplies and the enlarged
// subfamily is finite by the introduction rule, still drawn from f, and
// covers one point more.
//
// The induction rather than a choice function is what makes this a
// theorem about finiteness rather than about selection. Choosing a
// member of f for every point of s at once needs a choice principle and
// yields a subfamily indexed by s; taking the points one at a time needs
// nothing beyond the rules of finite, and the same induction that
// licenses the construction is what bounds the result.
var FiniteSubsetUnions = finiteSubsetUnionsThm{family.Add(registry.ProofEntry{
	Name: "FiniteSubsetUnions",
	Key:  "prop_44d87e5448f7e0c3",
	Build: family.Sections(
		Statement{
			Binders: "∀f:set(set(A)). ∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
				"s ⊆ ⋃f",
			},
			Conclusion: "∃g:set(set(A)). finite(g) ∧ g ⊆ f ∧ s ⊆ ⋃g",
			Abbrev: Abbrev{
				{Name: "noPoints", Text: "∅⟨A:A⟩"},
			},
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// The two facts the induction step turns on: what a cover
			// still gives when a point is set aside, and what it regains
			// when a member holding that point is adjoined. Neither
			// mentions finiteness.
			//
			// Both are sections rather than claims inside the step: each is
			// a fact about covers alone, and the step spends them at an
			// instance apiece.
			splits := ctx.Lemma(
				Statement{
					Binders: "∀f:set(set(A)). ∀u:set(A). ∀x:A.",
					Hypotheses: []string{
						"insert(x, u) ⊆ ⋃f",
					},
					Conclusion: "u ⊆ ⋃f ∧ x ∈ ⋃f",
				},
				BySets())

			grows := ctx.Lemma(
				Statement{
					Binders: "∀f g:set(set(A)). ∀t u:set(A). ∀x:A.",
					Hypotheses: []string{
						"t ∈ f",
						"g ⊆ f",
						"x ∈ t",
						"u ⊆ ⋃g",
					},
					Conclusion: "insert(t, g) ⊆ f ∧ insert(x, u) ⊆ ⋃insert(t, g)",
				},
				func(a *Argument, f, g, t, u, x Term, given Fact) {
					a.Do(SplitConj(
						// The set driver does not reach this half. Membership
						// in a family enlarged by t leaves the alternative
						// "is t" as an equation between SETS, and carrying f
						// across it is extensionality rather than clause work.
						Case(
							"the enlarged cover draws on f alone, the member adjoined being one of f's own",
							// Positional: the install prefix takes the
							// collection being enlarged, then the one it must
							// fit inside, then the member adjoined.
							By(given, set_order.InsertSubset.Inst[elementSet]())),
						Case(
							"and it covers the new point, which that member holds, along with everything covered before",
							BySets(given)),
					))
				})

			return ctx.Theorem(headline, func(a *Argument, f, s Term) {
				noFamilyTerm := a.Term("«noFamily»")
				assumptions := a.Assume() // s is finite, and f covers it

				// The property the induction carries — "finitely many
				// members of f cover this set, if anything in f does" —
				// read at each set the induction meets. The theorem's own
				// two assumptions are finite(s) and this property's
				// antecedent at s, which is how the induction's conclusion
				// becomes the theorem's.
				coveredFinitely := a.Term("λv:set(A). v ⊆ ⋃f ⇒ (∃g:set(set(A)). finite(g) ∧ g ⊆ f ∧ v ⊆ ⋃g)")

				a.Show(
					"so the induction carries the property to every finite set; and s is finite, and f does cover it",
					ByInduction(At(FiniteInduct, coveredFinitely, s), assumptions,
						Case(
							"at ∅ there is nothing to cover, and the empty subfamily covers nothing",
							Derive(func(b *Argument) {
								b.Assume() // ∅ is covered, which asks nothing
								b.Take(noFamilyTerm)

								below := b.Have(
									"nothing is inside everything — the empty subfamily "+
										"lies in f, and ∅ in what that subfamily collects",
									"«noFamily» ⊆ f ∧ «noPoints» ⊆ big_union(«noFamily»)",
									BySets())

								b.Show(
									"and the empty subfamily is finite outright",
									// FiniteRules bare of necessity: finite(∅) is its
									// left conjunct, which binds nothing.
									By(below, FiniteRules.Inst[elementSet]()))
							})),
						Case(
							"one more point lies in one member of f, and adjoining "+
								"that member to the cover the induction supplies covers it",
							Derive(func(b *Argument) {
								x, u := b.Fix(), b.Fix("u")
								carried := b.Assume() // the IH, itself conditional
								covered := b.Assume() // the enlarged set is covered by f

								split := b.Have(
									"so the rest is covered too, and the new point lies somewhere in the family",
									"u ⊆ ⋃f ∧ x ∈ ⋃f",
									By(covered, splits))

								g, small := b.Obtain(
									"the induction hypothesis covers the rest with finitely many members",
									"∃g:set(set(A)). finite(g) ∧ g ⊆ f ∧ u ⊆ ⋃g",
									By(carried, split))

								t, holds := b.Obtain(
									"and to lie in the family's union is to lie in one of its members",
									"∃t:set(A). t ∈ f ∧ x ∈ t",
									By(split, set_basic.InUnions))

								b.Take(b.Term("insert(t, g)"))
								b.Show(
									"that member adjoined to the cover: finite by the introduction "+
										"rule, still drawn from f, and covering one point more",
									By(
										small,
										holds,
										// FiniteRules' stated `∀x:A. ∀s` order: the
										// member adjoined first, then the collection.
										FiniteRules.Inst[elementSet]().At(t, g),
										At(grows, f, g, t, u, x)))
							}))))
			})
		}),
})}

// UnionsInChain — a non-empty finite chain of sets holds its own union.
// Strict inclusion cannot continue from every member of a non-empty finite
// family. A maximal member therefore exists, and comparability makes it the
// union of the family.
var UnionsInChain = unionsInChainThm{family.Add(registry.ProofEntry{
	Name: "UnionsInChain",
	Key:  "prop_f0b1ed0e15e1bf48",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:set(set(A)).",
			Hypotheses: []string{
				"finite(f)",
				"¬(f = ∅)",
				"∀s t:set(A). s ∈ f ∧ t ∈ f ⇒ s ⊆ t ∨ t ⊆ s",
			},
			Conclusion: "⋃f ∈ f",
		},
		func(a *Argument, f *Expr[Set[Set[A]]], assumptions Fact) {
			_, maximal := a.ObtainAs[Set[A]](
				"the finite family has a maximal member",
				"∃m:set(A). m ∈ f ∧ (∀u:set(A). u ∈ f ⇒ ¬(m ⊆ u ∧ ¬(u ⊆ m)))",
				Named("m"),
				Derive(func(b *Argument) {
					noMaximal := b.SupposeNot()
					transitive := b.Have(
						"strict inclusion is transitive",
						"∀u v w:set(A). u ⊆ v ∧ ¬(v ⊆ u) ∧ (v ⊆ w ∧ ¬(w ⊆ v)) ⇒ u ⊆ w ∧ ¬(w ⊆ u)",
						BySets())
					empty := b.Have(
						"without a maximal member strict inclusion would continue throughout the family",
						"f = «noFamily»",
						By(
							noMaximal,
							transitive,
							assumptions,
							FiniteTransitivityChain.At(
								b.TermAs[Fun2[Set[A], Set[A], Bool]]("λu:set(A). λv:set(A). u ⊆ v ∧ ¬(v ⊆ u)"),
								f)))
					b.Show(
						"the family is non-empty",
						By(Normalized, empty, assumptions))
				}))
			realizes := a.Have(
				"comparability makes the maximal member the union",
				"⋃f = m",
				BySets(maximal, assumptions))
			a.Show(
				"the union is a member of the family",
				By(Normalized, realizes, maximal))
		}),
})}

// IntersInChain — a non-empty finite chain of sets holds its own intersection.
// Strict reverse inclusion cannot continue throughout a non-empty finite
// family. A minimal member therefore exists, and comparability makes it the
// intersection of the family.
var IntersInChain = intersInChainThm{family.Add(registry.ProofEntry{
	Name: "IntersInChain",
	Key:  "prop_e14ed33e9d067350",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:set(set(A)).",
			Hypotheses: []string{
				"finite(f)",
				"¬(f = ∅)",
				"∀s t:set(A). s ∈ f ∧ t ∈ f ⇒ s ⊆ t ∨ t ⊆ s",
			},
			Conclusion: "⋂f ∈ f",
		},
		func(a *Argument, f *Expr[Set[Set[A]]], assumptions Fact) {
			_, minimal := a.ObtainAs[Set[A]](
				"the finite family has a minimal member",
				"∃m:set(A). m ∈ f ∧ (∀u:set(A). u ∈ f ⇒ ¬(u ⊆ m ∧ ¬(m ⊆ u)))",
				Named("m"),
				Derive(func(b *Argument) {
					noMinimal := b.SupposeNot()
					transitive := b.Have(
						"strict reverse inclusion is transitive",
						"∀u v w:set(A). v ⊆ u ∧ ¬(u ⊆ v) ∧ (w ⊆ v ∧ ¬(v ⊆ w)) ⇒ w ⊆ u ∧ ¬(u ⊆ w)",
						BySets())
					empty := b.Have(
						"without a minimal member strict reverse inclusion would continue throughout the family",
						"f = «noFamily»",
						By(
							noMinimal,
							transitive,
							assumptions,
							FiniteTransitivityChain.At(
								b.TermAs[Fun2[Set[A], Set[A], Bool]]("λu:set(A). λv:set(A). v ⊆ u ∧ ¬(u ⊆ v)"),
								f)))
					b.Show(
						"the family is non-empty",
						By(Normalized, empty, assumptions))
				}))
			realizes := a.Have(
				"comparability makes the minimal member the intersection",
				"⋂f = m",
				BySets(minimal, assumptions))
			a.Show(
				"the intersection is a member of the family",
				By(Normalized, realizes, minimal))
		}),
})}

// FiniteSubsetUnionsChain — a finite set covered by a non-empty chain of
// sets already lies inside a single member of the chain.
//
// Being covered by the chain says only that each point of s lies in SOME
// member; the conclusion says one member holds them all. Finiteness is
// what closes that gap, and the two theorems above close it between
// them. FiniteSubsetUnions cuts the family down to finitely many of its
// members still covering s — the one place s's finiteness is spent — and
// a subfamily of a chain is a chain, so UnionsInChain hands back the
// largest of those finitely many. It covers s because they all did
// together, and it is drawn from f because they were.
//
// The subfamily may be empty, and that is the one case the two theorems
// leave open: a chain has no largest member when it has no members.
// There s is covered by nothing and so is empty, and f — non-empty by
// hypothesis — has a member for it to sit inside vacuously. That is
// where the non-emptiness of f is spent, and it is spent nowhere else:
// once the subfamily has a member, f inherits one from it.
var FiniteSubsetUnionsChain = finiteSubsetUnionsChainThm{family.Add(registry.ProofEntry{
	Name: "FiniteSubsetUnionsChain",
	Key:  "prop_ecbb0d8a2388f301",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:set(set(A)). ∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
				"s ⊆ ⋃f ∧ (¬(f = ∅) ∧ (∀t u:set(A). t ∈ f ∧ u ∈ f ⇒ t ⊆ u ∨ u ⊆ t))",
			},
			Conclusion: "∃t:set(A). t ∈ f ∧ s ⊆ t",
		},
		func(a *Argument, f, s Term, given Fact) {
			g, small := a.Obtain(
				"finitely many members of f already cover s",
				"∃g:set(set(A)). finite(g) ∧ g ⊆ f ∧ s ⊆ ⋃g",
				By(given, At(FiniteSubsetUnions, f, s)))

			remains := a.Unless(
				g.Eq(a.Term("«noFamily»")),
				"when nothing of f was needed, s is covered by nothing and "+
					"so is empty, and any member of f — which has one — holds it",
				Given(func(a *Argument, isEmpty Fact) {
					a.Do(BySets(isEmpty, small, given))
				}))

			// Two members of the subfamily are two members of f, which the
			// chain condition compares.
			chained := a.Have(
				"what was kept of the chain is a chain",
				"∀p q:set(A). p ∈ g ∧ q ∈ g ⇒ p ⊆ q ∨ q ⊆ p",
				BySets(given, small))

			collected := a.Have(
				"so, being finite and with something in it, the subfamily holds its own union",
				"⋃g ∈ g",
				// Read at the subfamily, not at f: f need not be finite.
				By(small, remains, chained, At(UnionsInChain, g)))

			a.Take(a.Term("⋃g"))
			a.Show(
				"and that union is the member wanted — it is one of f's own, being "+
					"one of the subfamily's, and it covers s because the subfamily did",
				BySets(collected, small))
		}),
})}

// FiniteTransitivityChain — a finite set on which a strict order is
// everywhere continuable is empty.
//
// Read the relation as "comes strictly later". The hypotheses say no
// point comes after itself, that coming after is transitive, and that
// every point of the set is followed by another point OF THE SET. A
// finite set cannot support all three: following the successors would
// have to revisit a point eventually, and by transitivity a revisited
// point comes after itself.
//
// The proof does not build the revisiting chain, which would need a
// counting argument. It runs the induction that the finiteness is
// there to license, and the whole content is in the step. Suppose one
// more point x is added to u and every point of the enlarged set is
// still followed inside it. Then x's own successor cannot be x, so it
// already lies in u; and a point of u whose successor was x can follow
// x's step instead, transitivity closing the two moves into one — so u
// too is everywhere continuable, and the induction hypothesis empties
// it. But x's successor was in u, and there is nothing in ∅. So the
// step case never arises at all; and at ∅, where the induction starts,
// there was nothing to prove in the first place.
//
// Nothing in that argument asks x to be NEW to u, and the step could
// not use freshness if it were offered: it reads the added point only
// through the continuation hypothesis at x, and what puts x's
// successor inside u is irreflexivity, not novelty. Each branch of the
// membership split yields SOME successor lying in u and the argument
// never cares which. So the plain induction principle is enough and
// the strong one is not needed.
var FiniteTransitivityChain = finiteTransitivityChainThm{family.Add(registry.ProofEntry{
	Name: "FiniteTransitivityChain",
	Key:  "prop_8494e02809f7e966",
	Build: family.Theorem(
		Statement{
			Binders: "∀R:(A → A → bool). ∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
				"(∀x:A. ¬R(x, x)) ∧ " +
					"((∀x y z:A. R(x, y) ∧ R(y, z) ⇒ R(x, z)) ∧ (∀x:A. x ∈ s ⇒ ∃y:A. y ∈ s ∧ R(x, y)))",
			},
			Conclusion: "s = ∅",
		},
		func(a *Argument, R, s Term, assumptions Fact) {
			// The property the induction carries — "every point of v is
			// followed by another point of v, so v is empty" — read at
			// each set the induction meets. The last of the theorem's four
			// assumptions is that property's antecedent at s, which is how
			// the induction's conclusion becomes its own.
			emptiedIfContinuable := a.Term("λv:set(A). (∀p:A. p ∈ v ⇒ (∃q:A. q ∈ v ∧ R(p, q))) ⇒ v = ∅")

			a.Show(
				"so the induction carries the property to s, which is "+
					"finite; and s IS continuable, which leaves it empty",
				ByInduction(At(FiniteInduct, emptiedIfContinuable, s), assumptions,
					Case(
						"at ∅ there is nothing to continue, and nothing to prove either",
						// No premises to name and none to be had: the consequent
						// is ∅ = ∅ whatever the antecedent says.
						Basic()),
					Case(
						"a new point cannot be continued out of the set it joins, so "+
							"that set is continuable too — and is then emptied from under it",
						Derive(func(b *Argument) {
							x := b.Fix()
							b.Fix("u")            // the claims below spell it by name
							carried := b.Assume() // u is empty if continuable
							chained := b.Assume() // every point of insert(x, u) is continued inside it

							// set_basic.InInsert is bare at both sites below, and
							// deliberately: each leaf reads it at more than one
							// member — at the point being continued and at the
							// successor the refuter names — so there is no single
							// instance for a ground cite to carry.
							xNext := b.Have(
								"x's own successor cannot be x, no point being its own, so it lies in u",
								"∃q:A. q ∈ u ∧ R(x, q)",
								By(assumptions, chained.At(x), set_basic.InInsert))

							inU := b.Have(
								"and a point of u continued only as far as x can follow x's "+
									"step instead, transitivity closing the two moves into one",
								"∀p:A. p ∈ u ⇒ ∃q:A. q ∈ u ∧ R(p, q)",
								By(assumptions, chained, xNext, set_basic.InInsert))

							emptied := b.Have(
								"so the induction hypothesis empties u",
								"u = ∅",
								By(carried, inU))

							b.Show(
								"leaving x's successor nowhere to be — so a set with a "+
									"point added is never continuable, and the case is vacuous",
								By(xNext, emptied, set_basic.NotInEmpty))
						}))))
		}),
})}

// FiniteProductDependent — the values of a map on a finite base with finite
// fibres form a finite set: each fibre image is finite, and their finite
// family has a finite union.
var FiniteProductDependent = finiteProductDependentThm{family.Add(registry.ProofEntry{
	Name: "FiniteProductDependent",
	Key:  "prop_d56f8bba02b0da3a",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B → C). ∀s:set(A). ∀t:(A → set(B)).",
			Hypotheses: []string{
				"finite(s)",
				"∀x:A. x ∈ s ⇒ finite(t(x))",
			},
			Conclusion: "finite({f(x, y) | x:A, y:B | x ∈ s ∧ y ∈ t(x)})",
			Abbrev: Abbrev{
				{Name: "FibreImage", Text: "λx:A. image(f(x), t(x))"},
				{Name: "FibreImages", Text: "image(«FibreImage», s)"},
			},
		},
		func(
			a *Argument,
			f *Arrow2[A, B, C],
			s *Expr[Set[A]],
			t *Arrow[A, Set[B]],
			finiteS, finiteFibres Fact,
		) {
			collected := a.Have(
				"the values are the union of the fibre images",
				"{f(x, y) | x:A, y:B | x ∈ s ∧ y ∈ t(x)} = ⋃«FibreImages»",
				BySets())
			finiteFamily := a.Have(
				"a finite base indexes only finitely many fibre images",
				"finite(«FibreImages»)",
				By(finiteS, FiniteImage.At(a.TermAs[Fun[A, Set[C]]]("«FibreImage»"), s)))
			imagesFinite := a.Have(
				"each fibre image is finite",
				"∀x:A. x ∈ s ⇒ finite(image(f(x), t(x)))",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					inS := b.Assume()
					b.Show(
						"the finite fibre has a finite image",
						By(inS, finiteFibres.At(x), FiniteImage.At(b.TermAs[Fun[B, C]]("f(x)"), t.Apply(x))))
				}))
			membersFinite := a.Have(
				"every member of the image family is finite",
				"∀u:set(C). u ∈ «FibreImages» ⇒ finite(u)",
				Derive(func(b *Argument) {
					u := b.FixAs[Set[C]]("u")
					inFamily := b.Assume()
					x, fibre := b.ObtainAs[A](
						"a member is the image of a fibre over the base",
						"∃x:A. u = image(f(x), t(x)) ∧ x ∈ s",
						By(inFamily, set_basic.InImage.At(b.TermAs[Fun[A, Set[C]]]("«FibreImage»"), s, u)))
					b.Show(
						"that fibre image is finite",
						By(Normalized, fibre, imagesFinite.At(x)))
				}))
			a.Show(
				"a finite family of finite sets has a finite union",
				By(collected, finiteFamily, membersFinite, FiniteUnions.At(a.TermAs[Set[Set[C]]]("«FibreImages»"))))
		}),
})}

// FiniteProduct — a product of two finite sets is finite.
//
// This is FiniteProductDependent read where the fibre does not vary and
// the map is the pairing: opened, set_cross(s, t) pairs every point of
// `s` with every point of the one second-coordinate set `t`, and what
// the pairs are collected INTO is the pair itself rather than some
// value computed from it. Nothing about products is proved here that
// was not proved there — a rectangle is the case of a dependent product
// whose fibres happen to coincide.
var FiniteProduct = finiteProductThm{family.Add(registry.ProofEntry{
	Name: "FiniteProduct",
	Key:  "prop_8673f8c8e582cbbc",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
			},
			Conclusion: "finite(set_cross(s, t))",
		},
		Opening(Unfold(set_product.SetCrossDef), func(a *Argument, s, t Term, bothFinite Fact) {
			// The sibling read at prod(A, B): the values collected here ARE
			// the pairs, so its third type variable lands on a type this
			// statement BUILDS rather than one it names.
			//
			// Which is what decides the cite's form, and it is worth stating
			// against the sibling's own cross-type cite. There, FiniteImage's
			// two type variables land on B and C — variables of the statement
			// doing the citing — and an ordinary ground cite carries them. A
			// BUILT landing type is not carried: the ordinary cite installs
			// here but leaves a residue for the refuter, and the shaping that
			// would settle that residue leaves the sibling's own reproduction
			// obligation at a type its certificate does not cover.
			// Instantiating first settles both, and it is the same move
			// FinitePowerset makes one type level up, where FiniteImage is
			// instantiated at the built type `set(A)`.
			//
			// The instance is keyed by the sibling's own letters: its C —
			// where `f`'s results land — is the pair type this statement
			// builds. The witnesses go in the sibling's own stated
			// `∀f. ∀s. ∀t.` order, like any other ground cite.
			sibling := FiniteProductDependent.Inst(
				TypeBinder.BindA[element](), TypeBinder.BindB[B](), TypeBinder.BindC[Prod[element, B]]())

			a.Show(
				"the sibling at the fibre that does not vary and at "+
					"the pairing map, which collects each pair as itself",
				// No shaping: where the sibling applies its fibre and its map,
				// the instantiation itself β-reduces them — `(λx. t)(x)` to
				// `t`, `(λx y. (x, y))(x, y)` to `(x, y)` — so the instance's
				// conclusion is this goal as it stands.
				By(
					bothFinite,
					At(sibling,
						a.Term("λx:A. λy:B. (x, y)"), // the map, which pairs
						s,                            // the base
						a.Term("λx:A. t"))))          // the fibre, constantly t
		})),
})}

// FiniteImagePair — two maps with finitely many values on s take finitely
// many pairs of values together there: each pair is a value of the one
// beside a value of the other, a point of the finite rectangle of the two
// images.
var FiniteImagePair = finiteImagePairThm{family.Add(registry.ProofEntry{
	Name: "FiniteImagePair",
	Key:  "prop_74bc4ec0a48ee943",
	Build: family.Theorem(Statement{
		Binders: "∀f:(A → B). ∀g:(A → C). ∀s:set(A).",
		Hypotheses: []string{
			"finite(image(f, s))",
			"finite(image(g, s))",
		},
		Conclusion: "finite(image(λx:A. (f(x), g(x)), s))",
	}, func(a *Argument, f *Arrow[A, B], g *Arrow[A, C], s *Expr[Set[A]], finiteF, finiteG Fact) {
		inside := a.Have(
			"each pair of values is a value of f beside a value of g",
			"image(λx:A. (f(x), g(x)), s) ⊆ set_cross(image(f, s), image(g, s))",
			Unfold(set_product.SetCrossDef),
			BySets())
		a.Show(
			"and the rectangle of the two finite images is finite",
			By(finiteF, finiteG, inside, FiniteProduct, FiniteSubset))
	}),
})}

// ---------------------------------------------------------------------------
// The finite predicate, and the principles the definition comes with
// ---------------------------------------------------------------------------
//
// The four entries below are finite's own, as the definition
// (definitions.go) hands them over: the introduction rules, rule
// induction, its strengthened form, the case analysis. Every member of
// the chapter cites one of them — the closure form the constant is
// minted with never enters a proof, Unfold refusing it. The induction
// principles proved beside them are each named for what they add on
// top: FiniteInductFresh, that the element is new; FiniteInductFreshOn,
// that the element and the set's members satisfy a guard;
// FiniteInductProperSubset, a walk down along ⊊ instead of up along
// insert; FiniteInductDelete, a walk by removal instead of insertion.
// The README carries why that is the chapter's whole method.
//
// The set-membership driver cannot see finite at all, the predicate
// having no membership reading; what it does close here are the side
// facts about ⊆, ⊊, insert and delete that the descent argument turns
// on, where the subject is a set constructor and not the predicate.
//
// (The ∅ rule on its own is deliberately not a member: nothing cites
// it, and a reader who wants it has it as FiniteRules' left conjunct.)

// FiniteRules — the two introduction rules of finite: the empty set is
// finite, and adding one element to a finite set leaves it finite: the
// definition's rule set, registered verbatim as its Rules theorem.
var FiniteRules = finiteRulesThm{finite.Rules}

// FiniteInduct — induction over finite sets: a property that holds of ∅
// and survives adding one element holds of every finite set.
//
// "Smallest" read as a principle: finite(t) says t lies in every
// predicate closed under the two rules, and the hypothesis says P is
// one. This is the weak form — the step receives P(s) alone — which
// the sites below cite through ByInduction.
//
// A site that runs it at a λ — written, or read from the goal — and at
// the set it concludes about may have to shape the induction `Normalized`. What the principle
// delivers there is the λ APPLIED — at the set, and inside the rules it
// is discharged by — where the goal states the property the λ
// abbreviates; where the closer does not read through those
// applications by itself the shaping reduces them, and once they are
// reduced the close is one modus ponens. The sites below that carry the
// marker need it; the others close without it.
var FiniteInduct = finiteInductThm{finite.Induct}

// FiniteInductStrong — the definition's strengthened induction: the
// step may assume the set it enlarges is finite, alongside the property
// it carries.
var FiniteInductStrong = finiteInductStrongThm{finite.InductStrong}

// FiniteInductFresh — the strengthened induction sharpened once more:
// the element being added is NEW to the set.
//
// Freshness is not obtained from the definition but DISPATCHED. If x
// already lies in s then insert(x, s) is s and the step has nothing
// left to prove, so a rule stated for a fresh x is enough to run the
// induction for every x. The finiteness half comes from the
// strengthened principle above and costs nothing here.
var FiniteInductFresh = finiteInductFreshThm{family.Add(registry.ProofEntry{
	Name: "FiniteInductFresh",
	Key:  "prop_d7a990303665c76d",
	// The rules are bound as one fact; s stays in the goal, where the
	// strengthened induction concludes it.
	Build: family.Theorem(
		Statement{
			Binders: "∀P:(set(A) → bool). ∀s:set(A).",
			Hypotheses: []string{
				"P(∅)",
				"∀x:A. ∀s:set(A). P(s) ∧ x ∉ s ∧ finite(s) ⇒ P(insert(x, s))",
				"finite(s)",
			},
			Conclusion: "P(s)",
		},
		// fresh: P(∅), and P crosses insert for a new x and a finite s.
		func(a *Argument, P Term, fresh Fact) {
			a.Show(
				"the strengthened induction hands the step its finite(s); which rule carries P across depends on x",
				ByInduction(FiniteInductStrong,
					Case(
						"at ∅: the base rule outright",
						By(fresh)),
					Case(
						"across insert, with s finite and P(s) carried",
						Derive(func(b *Argument) {
							b.Fix()               // x, the element added
							b.Fix()               // s, the set it is added to
							carried := b.Assume() // finite(s) ∧ P(s)
							b.Do(ByCaseStep(b.Term("x ∈ s"),
								Case(
									"x was already in s, so the enlarged set is s and there is nothing new to prove",
									Derive(func(c *Argument) {
										absorbed := c.Have(
											"insert puts back an element s already has",
											"insert(x, s) = s",
											// ↦ x ∈ s, this branch's own assumption.
											Cite(set_algebra.InsertAbsorb))
										c.Show(
											"so the goal is the P the induction carries",
											By(Normalized, absorbed, carried))
									})),
								Case(
									"x is new to s, which is the case the rule was stated for",
									Given(func(c *Argument, isNew Fact) {
										c.Show(
											"the rule's three premises are the carried P(s) and finite(s) plus this branch's x ∉ s",
											By(isNew, carried, fresh))
									})),
							))
						}))))
		}),
})}

// FiniteInductFreshOn — the fresh induction over the finite sets whose
// members satisfy Q: the step meets a new x with Q(x), added to a finite s
// all of whose members satisfy Q.
//
// It is FiniteInductFresh run at the guarded property "if every member
// satisfies Q, then P": at ∅ that is P(∅), and across a fresh x the guard
// on insert(x, t) is Q(x) together with the guard on t, which lets the
// property carried at t give P(t) and hands the rule its Q(x).
var FiniteInductFreshOn = finiteInductFreshOnThm{family.Add(registry.ProofEntry{
	Name: "FiniteInductFreshOn",
	Key:  "prop_5f87f494a8c88609",
	Build: family.Theorem(Statement{
		Binders: "∀P:(set(A) → bool). ∀Q:(A → bool). ∀s:set(A).",
		Hypotheses: []string{
			"P(∅)",
			"∀x:A. ∀t:set(A). P(t) ∧ x ∉ t ∧ finite(t) ∧ Q(x) ∧ (∀y:A. y ∈ t ⇒ Q(y)) ⇒ P(insert(x, t))",
			"finite(s) ∧ ∀y:A. y ∈ s ⇒ Q(y)",
		},
		Conclusion: "P(s)",
	},
		func(a *Argument, P *Expr[Set[Set[A]]], Q *Expr[Set[A]], rules Fact, s *Expr[Set[A]], given Fact) {
			guarded := a.TermAs[Set[Set[A]]]("λu:set(A). (∀y:A. y ∈ u ⇒ Q(y)) ⇒ P(u)")
			a.Show(
				"the guarded property reaches every finite set, and s is one whose members satisfy Q",
				ByInduction(FiniteInductFresh.At(guarded, s),
					// `given` supplies the principle's finite(s) and the guard on s.
					given,
					Case(
						"at ∅ the property is P(∅), whatever the guard",
						By(rules)),
					Case(
						"across a fresh x, the guard on insert(x, t) carries both the guard on t and Q(x)",
						Derive(func(b *Argument) {
							b.Fix("x")
							// The principle's own set binder is `s`, which the
							// section holds — so the set laid into is NAMED.
							b.Fix("t")
							carried := b.Assume() // the property at t, x ∉ t, and finite(t)
							inside := b.Assume()  // every member of insert(x, t) satisfies Q
							split := b.Have(
								"a member of insert(x, t) is x or a member of t",
								"Q(x) ∧ (∀y:A. y ∈ t ⇒ Q(y))",
								BySets(inside))
							b.Show(
								"so the property at t gives P(t), and the rule adds the fresh x",
								By(split, carried, rules))
						}))))
		}),
})}

// FiniteCases — the two introduction rules are not only sound but
// EXHAUSTIVE: a finite set either IS ∅ or IS an insertion into a
// smaller finite set, and nothing else — the definition's case
// analysis.
var FiniteCases = finiteCasesThm{finite.Cases}

// FiniteInductProperSubset — induction over finite sets run DOWNWARD:
// a property that holds at every finite set whose proper subsets all
// carry it holds at every finite set.
//
// Every induction above walks a finite set up from ∅ along insert.
// This one walks it down along ⊊, and what makes the walk terminate is
// that below a finite set there is no infinite descending chain. The
// usual route to that goes through wellfoundedness, induction along ⊊
// being an instance of the general principle for wellfounded relations.
// This chapter has no such principle and does not want one for a single
// member, so it proves the finite case directly: ordinary induction
// carries the RELATIVIZED statement — "every descending property
// reaches every subset of this set" — to every finite set, and the
// headline reads it at the set itself, inclusion being reflexive.
//
// Relativizing is not on its own enough. A step adds a point x to v,
// and the subsets of insert(x, v) that CONTAIN x are not subsets of v,
// so the induction hypothesis says nothing about them. The repair is
// to quantify the descending property INSIDE the relativized
// statement, so that the step may apply its own hypothesis at a
// SHIFTED property — P at a set together with P at that set with x
// added. Read at the subsets of v, the shifted property's right half
// is exactly P at the subsets of insert(x, v) that contain x. What
// makes that application legitimate is the lemma that shifting
// preserves descent: the shift of a descending property descends.
var FiniteInductProperSubset = finiteInductProperSubsetThm{family.Add(registry.ProofEntry{
	Name: "FiniteInductProperSubset",
	Key:  "prop_27de1f56407bcf48",
	Build: family.Sections(
		Statement{
			Binders: "∀P:(set(A) → bool). ∀s:set(A).",
			Hypotheses: []string{
				"∀s:set(A). finite(s) ∧ (∀t:set(A). t ⊊ s ⇒ P(t)) ⇒ P(s)",
				"finite(s)",
			},
			Conclusion: "P(s)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			empty := setvocab.Pinned(ctx, "empty_set")
			insert, remove := ops(ctx).Insert, ops(ctx).Delete

			// The SHIFTED property — the predicate at a set, and at that
			// set with the point added — is what descent is asked of here
			// beside P itself: shifting is what buys the step its reach.
			shiftKeepsDescent := ctx.Lemma(
				"∀P:(set(A) → bool). ∀x:A. "+
					"    (∀u:set(A). finite(u) ∧ (∀t:set(A). t ⊊ u ⇒ P(t)) ⇒ P(u)) ⇒ "+
					"    ∀u:set(A). finite(u) ∧ (∀t:set(A). t ⊊ u ⇒ P(t) ∧ P(insert(x, t))) ⇒ P(u) ∧ P(insert(x, u))",
				func(a *Argument, P *TermWrapper, x Term) {
					// Where a proper subset of an enlarged set sits, by
					// whether it has the new point. One claim, proved
					// SEPARATELY — hence the strip and the split — because
					// one refute over both at once does not close either.
					sits := a.Have(
						"where a proper subset of an enlarged set sits, according to whether it has the new point",
						"∀c d:set(A). ∀y:A. "+
							"    (y ∈ c ∧ c ⊊ insert(y, d) ⇒ delete(c, y) ⊊ d) ∧ (y ∉ c ∧ c ⊊ insert(y, d) ⇒ c = d ∨ c ⊊ d)",
						StripQuant(),
						SplitConj(
							Case(
								"having the point, it drops properly inside the smaller set once that point goes",
								BySets()),
							Case(
								"missing it, it is the smaller set itself or lies properly inside it",
								BySets()),
						))

					descending := a.Assume()   // P descends
					u := a.Fix()               // an arbitrary set
					carriedBelow := a.Assume() // u is finite, and both halves hold below u

					atU := a.Have(
						"P holds at u — descent asks only about u's proper subsets, and each carries P as its left half",
						MakeProp(P.Apply(u)),
						By(carriedBelow, descending.At(u)))
					carried := a.Have(
						"name what those proper subsets carry: both halves are used below, and at different sets",
						"∀t:set(A). t ⊊ u ⇒ P(t) ∧ P(insert(x, t))",
						By(carriedBelow))

					reach := a.Have(
						"P holds at every proper subset of the enlarged set — the reach the shift buys",
						"∀w:set(A). w ⊊ insert(x, u) ⇒ P(w)",
						Derive(func(b *Argument) {
							w := b.Fix()
							proper := b.Assume() // w ⊊ insert(x, u)
							b.Cases(b.Term("x ∈ w"))
							b.When(
								"w has x: dropping it lands properly inside u, and putting it back rebuilds w",
								func(c *Argument, hasX Fact) {
									c.Show(
										"so the right half carried at w minus x IS P(w)",
										By(
											Normalized,
											carried,
											hasX,
											proper,
											At(sits, w, u, x),                   // delete(w, x) ⊊ u, x being in w
											At(set_algebra.InsertDelete, w, x))) // insert(x, delete(w, x)) = w
								})
							b.Otherwise(
								"w misses x: then w is u itself, or lies properly inside it",
								func(c *Argument, missesX Fact) {
									// Normalized draws the alternative OUT of sits:
									// its second reading asks for x ∉ w and the
									// proper inclusion, both in hand, and what it
									// then says is a disjunction. Its two sides
									// close the same way, one by P at u and one by
									// P below u, so neither needs its own case.
									c.Show(
										"P at u was just shown, and P properly inside u is the left half carried there",
										By(Normalized, atU, missesX, carried, proper, At(sits, w, u, x))) // w = u ∨ w ⊊ u, x missing from w
								})
						}))

					a.Show(
						"so the shifted property holds at u: P(u) outright, and P at the "+
							"enlarged set by descent, whose proper subsets are now covered",
						By(
							atU,
							reach,
							descending.At(insert.Apply(x, u)),
							carriedBelow,
							At(FiniteRules, x, u))) // finite(u) ⇒ finite(insert(x, u))
				})

			// "every descending property reaches every subset of s" — what
			// the induction below carries, read at each set it meets. The
			// ∀P sits INSIDE, and that is the whole device: it is what
			// lets the step reach for its own hypothesis at the shifted
			// property rather than at P.
			reachesBelow := ctx.Lemma(
				"∀s:set(A). "+
					"    finite(s) ⇒ "+
					"    ∀P:(set(A) → bool). "+
					"        (∀u:set(A). finite(u) ∧ (∀t:set(A). t ⊊ u ⇒ P(t)) ⇒ P(u)) ⇒ ∀t:set(A). t ⊆ s ⇒ P(t)",
				func(a *Argument, s Term) {
					// This is set_order.SubsetInsertDelete — the law the
					// sibling branch below cites — at a point the subset does
					// not have, where the deletion it speaks of does nothing.
					// Going through the law here would mean adding that no-op
					// as a second fact (set_algebra.DeleteNonElement) and then
					// folding its equation of sets back from the pointwise
					// form, which is the work the branch below has to do. The
					// driver settles the composite in one claim instead.
					staysInside := a.Have(
						"a subset of an enlarged set that misses the new point was already a subset of the smaller one",
						"∀c d:set(A). ∀y:A. y ∉ c ∧ c ⊆ insert(y, d) ⇒ c ⊆ d",
						BySets())
					finiteS := a.Assume()

					a.Show(
						"so ordinary induction carries the relativized statement to every finite set, and s is one of them",
						ByInduction(FiniteInduct, finiteS,
							Case(
								"∅ has nothing below it, so descent gives P there "+
									"with nothing to ask — and ∅ is its own only subset",
								Derive(func(b *Argument) {
									P := b.Fix()             // an arbitrary property
									descending := b.Assume() // … which descends
									t := b.Fix()
									inEmpty := b.Assume() // t ⊆ ∅
									atEmpty := b.Have(
										"P holds at ∅: it is finite, and descent asks about proper subsets it has none of",
										MakeProp(P.Apply(empty)),
										// FiniteRules bare of necessity: finite(∅) is
										// its left conjunct, which binds nothing.
										By(descending.At(empty), FiniteRules, set_order.NotProperSubsetEmpty))
									b.Show(
										"and a subset of ∅ IS ∅, so t is where P was just shown to hold",
										// Normalized: SubsetEmpty arrives with its equation
										// spelled pointwise, and folding `∀ẋ. t ẋ ⇔ ∅ ẋ`
										// back into t = ∅ — which is what carries P from ∅
										// to t — is extensionality, not clause work.
										By(Normalized, atEmpty, inEmpty, At(set_order.SubsetEmpty, t)))
								})),
							Case(
								"a set that carries the statement keeps it when a point is "+
									"added — via its own hypothesis read at the SHIFTED property",
								Derive(func(b *Argument) {
									x, v := b.Fix(), b.Fix("v")
									reachesBelowV := b.Assume() // every descending property reaches every subset of v
									b.Fix()                     // P — an arbitrary property; the claims below spell it by name
									descending := b.Assume()    // … which descends

									shifted := b.TermAs[Set[Set[A]]]("λw:set(A). P(w) ∧ P(insert(x, w))")
									pairs := b.Have(
										"the shifted property — P at a set and at that set with x "+
											"added — descends with P, so it reaches every subset of v",
										"∀t:set(A). t ⊆ v ⇒ P(t) ∧ P(insert(x, t))",
										By(descending, reachesBelowV.At(shifted), shiftKeepsDescent))

									t := b.Fix()
									inserted := b.Assume() // t ⊆ insert(x, v)
									b.Cases(b.Term("x ∈ t"))
									b.When(
										"t has x: dropping it leaves a subset of v, and putting it back rebuilds t",
										func(c *Argument, hasX Fact) {
											c.Show(
												"so the right half of the pair carried at t minus x IS P(t)",
												// Normalized: the equation InsertDelete
												// supplies arrives spelled pointwise,
												// and this leaf needs it folded back
												// into an equation of sets before P at
												// the rebuilt t reads as P(t).
												By(
													Normalized,
													pairs.At(remove.Apply(t, x)),
													hasX,
													inserted,
													At(set_order.SubsetInsertDelete, t, v, x), // t ⊆ insert(x, v) ⇔ delete(t, x) ⊆ v
													At(set_algebra.InsertDelete, t, x)))       // insert(x, delete(t, x)) = t
										})
									b.Otherwise(
										"t misses x: then t already sits inside v, where P is the pair's left half",
										func(c *Argument, missesX Fact) {
											c.Show(
												"so the pair read at t itself gives P(t)",
												By(missesX, pairs.At(t), inserted, At(staysInside, t, v, x))) // t ⊆ v
										})
								}))))
				})

			return ctx.Theorem(headline, func(a *Argument, P, s Term, descending, finiteS Fact) {
				a.Show(
					"descent reaches every subset of s, and s is one of its own subsets",
					By(finiteS, descending, At(reachesBelow, s), At(set_order.SubsetRefl, s)))
			})
		}),
})}

// FiniteInductDelete — induction over finite sets by REMOVAL: a
// property holding at ∅, and inherited by any non-empty finite set
// from at least one of its one-point deletions, holds at every finite
// set.
//
// The rule is unusual in what it lets the caller choose. It does not
// have to survive removing an arbitrary point — only SOME point of its
// own choosing, named after seeing the set. That is what makes it the
// natural rule for a property carried by a distinguished element (a
// maximum, a first coordinate) rather than by an arbitrary one.
//
// Removal shrinks, so the rule is descent, and the whole content is
// FiniteInductProperSubset read at P. What descent hands the step is
// that every PROPER SUBSET of s already carries P; the point the
// hypothesis names deletes s to one of them.
var FiniteInductDelete = finiteInductDeleteThm{family.Add(registry.ProofEntry{
	Name: "FiniteInductDelete",
	Key:  "prop_7a1610daab264142",
	Build: family.Theorem(
		Statement{
			Binders: "∀P:(set(A) → bool). ∀s:set(A).",
			Hypotheses: []string{
				"P(∅)",
				"∀s:set(A). finite(s) ∧ ¬(s = ∅) ⇒ ∃x:A. x ∈ s ∧ (P(delete(s, x)) ⇒ P(s))",
				"finite(s)",
			},
			Conclusion: "P(s)",
		},
		// atEmpty: P(∅); removable: each non-empty finite set offers a point.
		func(a *Argument, P *TermWrapper, atEmpty, removable Fact) {
			empty := setvocab.Pinned(a.Ctx(), "empty_set")

			shrinks := a.Have(
				"removing a point a set has leaves a proper subset of it",
				"∀c:set(A). ∀y:A. y ∈ c ⇒ delete(c, y) ⊊ c",
				BySets())

			obligation := a.Have(
				"P descends along ⊊: a finite set all of whose proper subsets carry P carries it too",
				"∀u:set(A). finite(u) ∧ (∀t:set(A). t ⊊ u ⇒ P(t)) ⇒ P(u)",
				Derive(func(b *Argument) {
					u := b.Fix()
					below := b.Assume() // u is finite, and everything properly inside it carries P

					b.Cases(u.Eq(empty))
					b.When(
						"u is ∅, where P holds outright",
						func(c *Argument, isEmpty Fact) {
							c.Show(
								"P(∅), carried along the equation",
								By(Normalized, isEmpty, atEmpty))
						})
					b.Otherwise(
						"u is not ∅, so it offers a point, and deleting that point lands properly inside u",
						func(c *Argument, nonempty Fact) {
							c.Show(
								"which is a set P already carries, and surviving that deletion is what the offer promises",
								By(below, nonempty, removable.At(u), shrinks.At(u)))
						})
				}))

			// Descent states the same finite(s) guard this statement does,
			// so the two meet without reaching a refuter.
			a.Show(
				"so descent along ⊊ carries P to every finite set",
				By(obligation, At(FiniteInductProperSubset, P)))
		}),
})}

// ---------------------------------------------------------------------------
// Finiteness and the subset order
// ---------------------------------------------------------------------------
//
// The part above states the rules and the principles finite comes with.
// This one asks the first question they do not answer by themselves:
// how does finiteness sit under `⊆`? Two facts settle it, and they are
// one pair rather than two members.
//
// The first is that finiteness DESCENDS: a subset of a finite set is
// finite. The second is that insert does not change it at all — and
// that one is the first read at a single inclusion, which is why the
// two belong together rather than in separate files.
//
// What they buy is the rest of the chapter. Every later construction is
// shown finite without running the induction again: bound it by
// something already finite, or build it up by insertions.

// FiniteSubset — a subset of a finite set is finite.
//
// The induction is on the CONTAINING set, at the predicate "every
// subset of u is finite" — a subset has no structure of its own to
// induct on, and the containing set has all of it. At ∅ the predicate
// says nothing new, because ∅'s only subset is ∅. Across insert the
// work is done by set_order.ForallSubsetInsert, the observation that
// enlarging a set by one element enlarges its subsets in exactly one
// way: each is either already a subset, or one such with the new
// element added. Finiteness survives both, the first by the induction
// hypothesis and the second by finite's insert rule.
var FiniteSubset = finiteSubsetThm{family.Add(registry.ProofEntry{
	Name: "FiniteSubset",
	Key:  "prop_c73d0fc139b1a8de",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(t)",
				"s ⊆ t",
			},
			Conclusion: "finite(s)",
		},
		func(a *Argument, s, t Term, boundedByT Fact) {
			// The predicate the induction actually proves — the statement
			// with its subset generalized away. finite itself is the
			// predicate ForallSubsetInsert is read at below, and both
			// resolve out of the chapter's ParseScope.
			everySubsetFinite := a.Ctx().TermText("λu:set(A). ∀v:set(A). v ⊆ u ⇒ finite(v)")
			finite := a.Ctx().TermText("finite")

			a.Show(
				"so every subset of t is finite — s among them",
				// The principle at that predicate and at nothing else:
				// base ∧ step ⇒ ∀u. finite(u) ⇒ ∀v. v ⊆ u ⇒ finite(v).
				// The set it is read at stays universal, and boundedByT is
				// what picks t out of it.
				ByInduction(At(FiniteInduct, everySubsetFinite), boundedByT,
					Case(
						"at ∅: nothing is below ∅ but ∅, and ∅ is finite",
						Derive(func(b *Argument) {
							v := b.Fix()
							below := b.Assume() // v ⊆ ∅
							isEmpty := b.Have(
								"a set with nowhere to keep an element IS ∅",
								"v = ∅",
								By(below, At(set_order.SubsetEmpty, v))) // v ⊆ ∅ ⇔ v = ∅
							b.Do(isEmpty.Rw()) // ↦ finite(∅)
							b.Show(
								"which is finite's base rule",
								Cite(FiniteRules))
						})),
					Case(
						"across insert: the subsets of insert(x, s) are the subsets of s and their x-augmentations",
						Derive(func(b *Argument) {
							x, u := b.Fix(), b.Fix()
							subsetsFinite := b.Assume() // every subset of u is finite
							b.Show(
								"the subsets of u are finite by that, their x-augmentations by finite's insert rule",
								By(
									subsetsFinite,
									// (∀v. v ⊆ insert(x,u) ⇒ finite(v)) ⇔ (∀v. v ⊆ u ⇒ finite(v) ∧ finite(insert(x,v)))
									At(set_order.ForallSubsetInsert, finite, u, x),
									// Bare of necessity, not oversight: the instance the
									// label names sits at a v bound inside that ⇔, so there
									// is no Go term to ground it at.
									FiniteRules))
						}))))
		}),
})}

// FiniteInsert — adding one element changes nothing about finiteness.
//
// Backwards it is finite's own insert rule. Forwards it is FiniteSubset
// read at the one inclusion insert always gives, `s ⊆ insert(x, s)`:
// the enlarged set is finite, so everything inside it is, and s is.
var FiniteInsert = finiteInsertThm{family.Add(registry.ProofEntry{
	Name: "FiniteInsert",
	Key:  "prop_fc48881957680541",
	Build: family.Sections(
		"∀x:A. ∀s:set(A). finite(insert(x, s)) ⇔ finite(s)",
		func(ctx *Script, headline string) *GoalStackNode {
			insert := ops(ctx).Insert

			// The one inclusion the chapter needs and does not have: insert
			// only ever adds, so nothing leaves s. This is a pure statement
			// about the constructors, which is why the set driver — which
			// cannot see finite, and so is unused everywhere else here — is
			// the complete method for it.
			belowInsert := ctx.Lemma("∀x:A. ∀s:set(A). s ⊆ insert(x, s)",
				BySets())

			return ctx.Theorem(headline, func(a *Argument, x, s Term) {
				a.Iff()
				a.Forward(
					"and it descends back, because s sits inside the enlarged set",
					func(b *Argument, finiteEnlarged Fact) {
						b.Show(
							"FiniteSubset at that inclusion",
							By(
								finiteEnlarged,
								At(belowInsert, x, s),                    // s ⊆ insert(x, s)
								At(FiniteSubset, s, insert.Apply(x, s)))) // finite(insert(x,s)) ∧ s ⊆ insert(x,s) ⇒ finite(s)
					})
				a.Backward(
					"finiteness survives the insertion — one of the two rules it is closed under",
					func(b *Argument, finiteS Fact) {
						b.Show(
							"finite's insert rule at x and s",
							By(finiteS, At(FiniteRules, x, s)))
					})
			})
		}),
})}

// ---------------------------------------------------------------------------
// Induction over finitely supported functions
// ---------------------------------------------------------------------------
//
// This part sits after the subset order because that is what its
// induction spends: a function inside a finite bound has a finite
// support.

// FiniteInductSupport — induction over the finitely supported functions
// into num: a property that holds of the zero function, and passes to a
// function from the same function with one of its nonzero coordinates
// cleared to 0, holds of every function of finite support.
//
// It is the induction for a property of a finitely supported vector,
// proved by removing one supported coordinate at a time, and it is the
// bounding-set induction done once: FiniteInductFresh runs on a finite
// set E at "every function supported in E has the property". Supported
// in ∅, a function is zero. Across a new point a, a function supported
// in insert(a, E) either vanishes at a, and E already bounds it, or
// clearing a leaves a function E bounds, and the rule puts the
// coordinate back — the support it needs finite lies inside the finite
// insert(a, E). The support of v then bounds v itself.
var FiniteInductSupport = finiteInductSupportThm{family.Add(registry.ProofEntry{
	Name: "FiniteInductSupport",
	Key:  "prop_8d0a2cb344af0cfe",
	Build: family.Theorem(Statement{
		Binders: "∀P:((A → num) → bool). ∀v:(A → num).",
		Hypotheses: []string{
			"P(λx:A. 0)",
			"∀u:(A → num). ∀a:A. P(λx:A. COND(x = a, 0, u(x))) ∧ u(a) ≠ 0 ∧ finite(fun_support(0, u)) ⇒ P(u)",
			"finite(fun_support(0, v))",
		},
		Conclusion: "P(v)",
		Abbrev: Abbrev{
			{Name: "Bounded", Text: "λE:set(A). ∀u:(A → num). fun_support(0, u) ⊆ E ⇒ P(u)"},
		},
	},
		// atZero: P at the zero function; restore: P passes back across
		// one cleared coordinate.
		func(
			a *Argument,
			P *Expr[Set[Fun[A, Nat]]],
			atZero, restore Fact,
			v *Arrow[A, Nat],
			finiteSupport Fact,
		) {
			everyBound := a.Have(
				"on every finite set E, each function supported in E has P",
				"∀E:set(A). finite(E) ⇒ «Bounded»(E)",
				ByInduction(FiniteInductFresh,
					Case(
						"at ∅: a function supported nowhere is zero, where P holds outright",
						Derive(func(b *Argument) {
							b.FixAs[Fun[A, Nat]]("u")
							nowhere := b.Assume() // {x | u(x) ≠ 0} ⊆ ∅
							vanishes := b.Have(
								"u vanishes everywhere",
								"u = (λx:A. 0)",
								BySets(nowhere))
							b.Show(
								"so P(u) is P at the zero function",
								vanishes.Rw(),
								By(atZero))
						})),
					Case(
						"across a new point a: clear u's a-coordinate, or find it already zero",
						Derive(func(b *Argument) {
							point := b.FixAs[A]("a")
							E := b.FixAs[Set[A]]("E")
							previous := b.Conjuncts(
								b.Assume(),
								"every function supported in E has P",
								"a is new to E",
								"E is finite")
							u := b.FixAs[Fun[A, Nat]]("u")
							inInsert := b.Assume() // {x | u(x) ≠ 0} ⊆ insert(a, E)
							nonzero := b.Unless(
								b.Term("u(a) = 0"),
								"vanishing at a, u is already supported in E",
								Given(func(c *Argument, vanishesAtA Fact) {
									inE := c.Have(
										"E bounds the support of u",
										"fun_support(0, u) ⊆ E",
										BySets(vanishesAtA, inInsert))
									c.Show(
										"so the bound at E gives P(u)",
										By(inE, previous[0].At(u)))
								}))
							cleared := b.TermAs[Fun[A, Nat]]("λx:A. COND(x = a, 0, u(x))")
							clearedInE := b.Have(
								"clearing the a-coordinate leaves a function supported in E",
								"fun_support(0, λx:A. COND(x = a, 0, u(x))) ⊆ E",
								BySets(inInsert))
							clearedP := b.Have(
								"so P holds of it",
								"P(λx:A. COND(x = a, 0, u(x)))",
								By(clearedInE, previous[0].At(cleared)))
							support := b.TermAs[Set[A]]("fun_support(0, u)")
							inserted := b.TermAs[Set[A]]("insert(a, E)")
							finiteU := b.Have(
								"u's support lies inside the finite insert(a, E), so it is finite",
								"finite(fun_support(0, u))",
								By(inInsert, previous[2], FiniteInsert.At(point, E), FiniteSubset.At(support, inserted)))
							b.Show(
								"and the rule puts the a-coordinate back",
								By(clearedP, nonzero, finiteU, restore.At(u, point)))
						}))))
			support := a.TermAs[Set[A]]("fun_support(0, v)")
			a.Show(
				"the support of v is a finite set bounding v",
				By(finiteSupport, everyBound.At(support), set_order.SubsetRefl.At(support)))
		}),
})}

// ---------------------------------------------------------------------------
// Finiteness survives the set constructions
// ---------------------------------------------------------------------------
//
// The finite part says what finiteness IS: a set is finite when it is reached
// from ∅ by finitely many INSERTs. This one says what it SURVIVES, and
// every argument here reads that definition as a recipe.
//
// Which shape a construction takes is decided by whether it can GROW a
// set. Union can, so it is proved by induction on the growing operand:
// the union with ∅ has to land somewhere already known finite, and one
// more insert on the input must cost at most one more insert on the
// output. That second obligation is where the constructor identities
// live — an insertion moved across the operation — and those are
// set_algebra's subject, cited here rather than re-derived.
//
// Intersection, difference and delete cannot grow a set at all: each
// lands inside one of its own inputs. So none of them inducts. Each is
// instead exhibited INSIDE something already known finite, and
// FiniteSubset does the rest — one citation of it per member, at that
// member's own inclusion, which set_order states and this file does not
// re-derive. The reverse halves of the two equivalences here go the
// same way: an operand is bounded by the union it helped build, and a
// set is bounded by its own deletion with the deleted element put back.
//
// That leaves one member which neither grows nor shrinks anything.
// FiniteSing is the definition read at its shortest: a singleton is ∅
// with one element inserted, so both introduction rules fire once and
// nothing else is needed.
//
// insert itself would be the first case by that classification and is
// deliberately not here: it is the definition's own second rule read as
// an equivalence, so it lives beside ⊆ in the subset part above, where its harder
// direction — FiniteSubset at s ⊆ insert(x, s) — actually comes from.

// FiniteUnionImp — a union of two finite sets is finite.
//
// Induction on the left operand, at the property "joining t leaves a
// finite set". Joining t to ∅ gives t back, which is finite by
// assumption. Joining t to one more element gives the same set as
// adding that element to the join — so the insert rule carries
// finiteness across the step, and every set reached by finitely many
// INSERTs joins t finitely.
var FiniteUnionImp = finiteUnionImpThm{family.Add(registry.ProofEntry{
	Name: "FiniteUnionImp",
	Key:  "prop_fe026ffd3c4eb30e",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
			},
			Conclusion: "finite(s ∪ t)",
		},
		func(a *Argument, s, t Term, finite Fact) {
			union := ops(a.Ctx()).Union

			a.Show(
				"so the induction delivers the property at every finite set, and s is one of them",
				// `finite` names the set the property is read at.
				ByInduction(FiniteInduct, finite,
					Case(
						"∅ contributes no element, so the join is t itself — and t is finite",
						By(Normalized, finite, At(set_algebra.UnionEmpty, t))), // ∅ ∪ t = t
					Case(
						"one more element on the left is one more element on the join",
						Derive(func(b *Argument) {
							x, u := b.Fix(), b.Fix()
							joined := b.Assume() // finite(u ∪ t)
							b.Show(
								"adding the element to the join gives the same set, and the insert rule keeps that finite",
								By(
									Normalized,
									joined,
									At(set_algebra.InsertUnionEq, u, t, x), // insert(x, u ∪ t) = insert(x, u) ∪ t
									At(FiniteRules, x, union.Apply(u, t)))) // finite(u ∪ t) ⇒ finite(insert(x, u ∪ t))
						}))))
		}),
})}

// FiniteUnion — a union is finite exactly when both of its operands
// are.
//
// Forwards is FiniteUnionImp, the induction just above. Backwards needs
// no induction at all: a union is at least as large as either operand,
// so each operand is bounded by a set already known finite. The two
// operands are the same argument twice, differing only in which side of
// set_order.SubsetUnion they are read on.
var FiniteUnion = finiteUnionThm{family.Add(registry.ProofEntry{
	Name: "FiniteUnion",
	Key:  "prop_a3511c2099c5c440",
	Build: family.Theorem(
		"∀s t:set(A). finite(s ∪ t) ⇔ finite(s) ∧ finite(t)",
		func(a *Argument, s, t Term) {
			joined := ops(a.Ctx()).Union.Apply(s, t)

			a.Iff()
			a.Forward(
				"and each comes back finite, being bounded by the union it helped build",
				func(b *Argument, finiteJoin Fact) {
					b.Do(SplitConj(
						Case(
							"s, sitting on the left of the union",
							By(
								finiteJoin,
								At(set_order.SubsetUnion, s, t), // s ⊆ s ∪ t
								At(FiniteSubset, s, joined))),
						Case(
							"t, which the same law reaches by exchanging the two operands",
							By(
								finiteJoin,
								At(set_order.SubsetUnion, t, s), // t ⊆ s ∪ t, the second of that law's two readings
								At(FiniteSubset, t, joined))),
					))
				})
			a.Backward(
				"two finite sets join to a finite one — the induction above, at these operands",
				func(b *Argument, both Fact) {
					b.Show(
						"FiniteUnionImp at s and t",
						By(both, At(FiniteUnionImp, s, t)))
				})
		}),
})}

// FiniteInter — an intersection is finite as soon as EITHER of the two
// sets it is taken over is.
//
// One finite side is enough because the meet is bounded by each side
// separately: whichever one is known finite is the one that bounds it.
// So the disjunction in the hypothesis is not weakened on the way in —
// it is the case analysis, and the two branches are the same argument
// read at the two sides.
var FiniteInter = finiteInterThm{family.Add(registry.ProofEntry{
	Name: "FiniteInter",
	Key:  "prop_f3f20f8340a77eda",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(s) ∨ finite(t)",
			},
			Conclusion: "finite(s ∩ t)",
		},
		func(a *Argument, s, t Term, eitherFinite Fact) {
			met := ops(a.Ctx()).Intersection.Apply(s, t)

			a.Do(eitherFinite.SplitDisj(
				LeftHolds(
					"s is the finite one, and the meet admits only what s does",
					Given(func(b *Argument, finiteS Fact) {
						b.Show(
							"so the meet is bounded by s",
							By(
								finiteS,
								At(set_order.InterSubset, s, t), // s ∩ t ⊆ s
								At(FiniteSubset, met, s)))
					})),
				RightHolds(
					"t is, and the very same meet is bounded by t just as tightly",
					Given(func(b *Argument, finiteT Fact) {
						b.Show(
							"so the meet is bounded by t",
							By(
								finiteT,
								At(set_order.InterSubset, t, s), // s ∩ t ⊆ t, the second of that law's two readings
								At(FiniteSubset, met, t)))
					})),
			))
		}),
})}

// FiniteDiff — subtracting anything at all from a finite set leaves a
// finite set.
//
// Nothing is assumed about what is subtracted, and nothing needs to be:
// a difference only ever removes, so it is bounded by its left operand
// whatever the right one is.
var FiniteDiff = finiteDiffThm{family.Add(registry.ProofEntry{
	Name: "FiniteDiff",
	Key:  "prop_ce08fb31c2b59fa4",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "finite(s ∖ t)",
		},
		func(a *Argument, s, t Term, finiteS Fact) {
			remainder := ops(a.Ctx()).SetDifference.Apply(s, t)

			a.Show(
				"what a subtraction leaves is bounded by what it started from",
				By(
					finiteS,
					At(set_order.SubsetDiff, s, t), // s ∖ t ⊆ s
					At(FiniteSubset, remainder, s)))
		}),
})}

// FiniteSing — a one-element set is finite.
//
// The shortest possible reading of the definition. A singleton IS ∅
// with one element inserted, so FiniteRules' two clauses fire once
// each — the base clause on ∅, the insert clause on the element — and
// there is no third thing to check. This is the one member of the tier
// that neither bounds nor inducts.
var FiniteSing = finiteSingThm{family.Add(registry.ProofEntry{
	Name: "FiniteSing",
	Key:  "prop_ff6d73634643b086",
	// The context is `arg` rather than the usual `a` because the statement
	// binds `a` itself, and the closure parameter must be spelled like the
	// binder it takes.
	Build: family.Theorem(
		"∀a:A. finite({a})",
		func(arg *Argument, a Term) {
			// ∅ is nullary, so it carries no argument to read an instance
			// from and is pinned at the build site (the finite part says the rest).
			empty := setvocab.Pinned(arg.Ctx(), "empty_set")

			arg.Show(
				"both introduction rules, applied once each to reach {a} from ∅",
				By(At(FiniteRules, a, empty))) // finite(∅), and finite(∅) ⇒ finite(insert(a, ∅))
		}),
})}

// FiniteDeleteImp — removing an element from a finite set leaves a
// finite set.
//
// A deletion only ever removes, so it is bounded by the set it deletes
// from — the same shape as FiniteDiff, at the inclusion delete gives
// rather than the one ∖ gives.
var FiniteDeleteImp = finiteDeleteImpThm{family.Add(registry.ProofEntry{
	Name: "FiniteDeleteImp",
	Key:  "prop_2a8ab3deb091d7ab",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀x:A.",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "finite(delete(s, x))",
		},
		func(a *Argument, s, x Term, finiteS Fact) {
			lessX := ops(a.Ctx()).Delete.Apply(s, x)

			a.Show(
				"what a deletion leaves is bounded by the set it was taken from",
				By(
					finiteS,
					At(set_order.DeleteSubset, s, x), // delete(s, x) ⊆ s
					At(FiniteSubset, lessX, s)))
		}),
})}

// FiniteDelete — deleting an element changes nothing about finiteness,
// in either direction.
//
// Forwards is FiniteDeleteImp. Backwards looks like it should need to
// know whether x was in s at all, and does not: putting x back into the
// deletion always recovers a set containing s, whether or not s ever
// held x. That set is one insert away from a finite one, so it is
// finite, and s is bounded by it. The case analysis the statement seems
// to invite is what the inclusion avoids.
var FiniteDelete = finiteDeleteThm{family.Add(registry.ProofEntry{
	Name: "FiniteDelete",
	Key:  "prop_72b02cb6b3aecfa4",
	Build: family.Theorem(
		"∀s:set(A). ∀x:A. finite(delete(s, x)) ⇔ finite(s)",
		func(a *Argument, s, x Term) {
			lessX := ops(a.Ctx()).Delete.Apply(s, x)
			restored := ops(a.Ctx()).Insert.Apply(x, lessX) // insert(x, delete(s, x))

			a.Iff()
			a.Forward(
				"and it was finite to begin with, because putting x back recovers a bound for s",
				func(b *Argument, finiteLessX Fact) {
					below := b.Have(
						"nothing of s escapes both the deletion and the insertion that undoes it",
						"s ⊆ insert(x, delete(s, x))",
						// The adjoint law turns that inclusion into
						// delete(s, x) ⊆ delete(s, x), which asks nothing.
						By(At(set_order.SubsetInsertDelete, s, lessX, x), set_order.SubsetRefl))

					bound := b.Have(
						"and that bound is finite: it is one insertion on a finite set",
						"finite(insert(x, delete(s, x)))",
						By(finiteLessX, At(FiniteRules, x, lessX)))

					b.Show(
						"so s, bounded by it, is finite too",
						By(bound, below, At(FiniteSubset, s, restored)))
				})
			a.Backward(
				"a finite set stays finite when an element is taken out",
				func(b *Argument, finiteS Fact) {
					b.Show(
						"FiniteDeleteImp at s and x",
						By(finiteS, At(FiniteDeleteImp, s, x)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Finiteness travels along a map
// ---------------------------------------------------------------------------
//
// A map cannot manufacture points: everything in the image of a set is
// the value of something already in it. So an image is never larger
// than its source, and finiteness ought to survive being mapped.
//
// "Never larger" is not an argument this chapter can make directly,
// though, because it has no notion of size to compare with — only the
// induction principle, which says a finite set is one REACHED from ∅ by
// finitely many insertions. So the comparison has to be replayed as a
// construction: build the image the same way the source was built, and
// show each construction step costs at most one step on the image.
//
// The replay is possible because image is computed by recursion on
// precisely the two constructions finite is closed under.
//
// FiniteImageExpand is that theorem with the image spelled out as the
// comprehension image abbreviates. It costs a set identity and no
// second induction, and it is here because a consumer meets the image
// under both spellings.
//
// FiniteImageInjGeneral and FiniteImageInjEq travel the map BACKWARDS,
// which no map does in general, so both assume f separates the points
// of s. The first carries that argument; the second is it read at
// t := image(f, s). So those three are one theorem, its converse under
// a separation hypothesis, and the two combined — and each member's own
// doc gives its argument.
//
// The ExistsFiniteSubset… / ForallFiniteSubset… group says ONE further
// thing, four times over:
// a finite subset of an image is the image of a finite subset. That is
// an exchange between the two sides of f, and the statements differ
// only in how the exchanged set is quantified (∃ or ∀) and in whether
// they also promise f does not fold it. The ∃/INJ form is the one with
// content; the other three are it weakened, dualized, or both.
//
// The last four members say the same thing a fifth way, and what
// changes is the property. Rather than carry an arbitrary P across the
// exchange they FIX it to "being this particular set", which leaves
// each side's ∃ a single candidate and so turns the transfer into a
// statement about a named t. That is FiniteSubsetImage; of the other
// three, one weakens its equation to an inclusion and two read it at
// t := image(f, s) — the injective one of those reaching back to the
// ∃/INJ transfer for its instance, no injective twin of
// FiniteSubsetImage being stated.
//
// One chapter rule does NOT extend to image: nothing unfolds finite —
// the door refuses it — but members below do unfold image, at the leaves where
// the set driver reaches through it — a containment, or the
// identification of an image with the comprehension it abbreviates.

// FiniteImage — the image of a finite set is finite, under any map at
// all.
//
// Induction on the source, at the property "f sends this set to a
// finite one". Each case is one recursion clause of image followed by
// the introduction rule of finite that matches it: at ∅ the image is ∅,
// which is finite outright; at one more point the image gains exactly
// that point's value, which the insert rule absorbs. Nothing is assumed
// about f — a map that collapses points only makes the image smaller,
// and the induction never counts.
var FiniteImage = finiteImageThm{family.Add(registry.ProofEntry{
	Name: "FiniteImage",
	Key:  "prop_db7b9fb5a43038a",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "finite(image(f, s))",
		},
		func(a *Argument, f *TermWrapper, s Term, finiteS Fact) {
			// ∅ is nullary, so a use site has nothing to read an instance
			// from, and this claim needs it at BOTH element types at once:
			// the empty source, whose instance f's own type pins, and the
			// empty image, which sits in no argument position and so
			// carries the `⟨A:τ⟩` annotation (vocab.go reads it once).
			noPoints := a.Have(
				"a map carries nothing out of the empty set",
				"image(f, ∅) = ∅⟨A:B⟩",
				// Bare of necessity: the pair is recorded POINTWISE, so its
				// binder list carries the point the two sides are compared
				// at, which no term here names. The claim states the
				// instance the cite is used at.
				By(set_image.ImageClauses))

			a.Show(
				"so the induction carries the property to every finite set, and s is one of them",
				// finiteS names the set the property is read at.
				ByInduction(FiniteInduct, finiteS,
					Case(
						"at ∅: the image is that empty set, which is finite outright",
						// Bare of necessity: the ∅ rule is FiniteRules' left
						// conjunct, which binds nothing, and the pack's two
						// slots belong to the insert conjunct.
						By(noPoints, FiniteRules)),
					Case(
						"across insert: one more point in the source is one more point in the image",
						Derive(func(b *Argument) {
							// The principle's own set binder is `s`, which the
							// section holds — so the induction set is NAMED.
							x := b.Fix()
							b.Fix("t")                // t — the claims below spell it by name
							imageFinite := b.Assume() // finite(image(f, t))

							onePointMore := b.Have(
								"the enlarged source contributes exactly the new point's value",
								"image(f, insert(x, t)) = insert(f(x), image(f, t))",
								// Bare for the same reason as the ∅ clause
								// above: the pack is recorded pointwise, so no
								// term here names the slot a ground cite would
								// have to fill.
								By(set_image.ImageClauses))
							b.Do(onePointMore.Rw()) // ↦ finite(insert(f(x), image(f, t)))

							b.Show(
								"and one more insertion on a finite set leaves it finite",
								By(
									imageFinite,
									// finite(image(f,t)) ⇒ finite(insert(f(x), image(f,t)))
									At(FiniteRules, f.Apply(x), b.Term("image(f, t)"))))
						}))))
		}),
})}

// FiniteImageExpand — FiniteImage said with the image written out: the
// set of values a map takes on a finite set is finite.
//
// `image(f, s)` ABBREVIATES that comprehension — the two are one set by
// the constant's own definition — so identifying them is a question
// about the set constructors and carries no finiteness at all. Once the
// set at issue is named as an image, FiniteImage is the whole theorem,
// and its induction is not run a second time.
var FiniteImageExpand = finiteImageExpandThm{family.Add(registry.ProofEntry{
	Name: "FiniteImageExpand",
	Key:  "prop_d2a7dfba4dfbf279",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "finite({y:B | ∃x:A. y = f(x) ∧ x ∈ s})",
		},
		func(a *Argument, f, s Term, finiteS Fact) {
			asImage := a.Have(
				"the values f takes on s are exactly the image of s",
				"{y:B | ∃x:A. y = f(x) ∧ x ∈ s} = image(f, s)",
				BySets())

			a.Show(
				"and the image of a finite set is finite",
				By(finiteS, asImage, At(FiniteImage, f, s)))
		}),
})}

// FiniteImageInjGeneral — a map that separates the points of `s` cannot
// fold infinitely many of them into a finite `t`: the part of `s` that
// `f` sends into `t` is finite whenever `t` is.
//
// The theorem is a containment and nothing else. Separating the points
// of `s` is the same as being undoable there, so fix a `g` that undoes
// `f` on `s`. Then every `x` of `s` whose value lands in `t` is `g`'s
// value AT that landing point, which exhibits it as a point of
// `image(g, t)`. That image is finite because `t` is, and finiteness
// descends along `⊆`.
//
// Injectivity is spent once, in producing `g`; after that the argument
// is about a plain image, where FiniteImage already applies.
var FiniteImageInjGeneral = finiteImageInjGeneralThm{family.Add(registry.ProofEntry{
	Name: "FiniteImageInjGeneral",
	Key:  "prop_4769a095e927a481",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A). ∀t:set(B).",
			Hypotheses: []string{
				"injective_on(s, f)",
				"finite(t)",
			},
			Conclusion: "finite(preimage_on(s, f, t))",
		},
		func(a *Argument, f, s, t Term, injectiveAndFiniteT Fact) {
			g, undoes := a.Obtain(
				"f separates the points of s, so some g undoes it there",
				"∃g:(B → A). ∀x:A. x ∈ s ⇒ g(f(x)) = x",
				// Bare of necessity: read against the resident injectivity,
				// the cited ⇔ CLOSES this claim rather than installing a
				// hypothesis, leaving nothing for witnesses to ground.
				Cite(functions.InjectiveOnLeftInverse))

			// The part of s that f sends into t, and g's image of t — the
			// containment's two sides, as the typed witnesses the closing
			// cite takes.
			sentIntoSet := a.Term("preimage_on(s, f, t)")
			imageSet := a.Term("image(g, t)")

			// A claim about the set constructors and nothing else, which is
			// the leaf shape the set driver settles — from the left-inverse
			// equation, which exhibits each such x as g's value at f(x).
			within := a.Have(
				"such an x is g's value at f(x), and f(x) is a point of t — so the part sits inside g's image of t",
				"preimage_on(s, f, t) ⊆ image(g, t)",
				BySets(undoes))

			// injectiveAndFiniteT names the stripped conjunction whole;
			// only its finite(t) half is live here, injectivity having
			// been spent on g above.
			a.Show(
				"t is finite, so g's image of it is, and the part inside that image is too",
				By(
					injectiveAndFiniteT,
					within,
					At(FiniteImage, g, t), // finite(t) ⇒ finite(image(g, t))
					// finite(image(g, t)) ∧ sentInto ⊆ image(g, t) ⇒ finite(sentInto)
					At(FiniteSubset, sentIntoSet, imageSet)))
		}),
})}

// FiniteImageInjEq — a map that separates the points of `s` neither
// creates nor destroys finiteness there: `image(f, s)` is finite exactly
// when `s` is.
//
// One direction holds of every map and is FiniteImage. The other is
// FiniteImageInjGeneral read at `t := image(f, s)`, once `s` is
// recognized as a preimage: a point of `s` has its value in `image(f, s)`
// for no reason at all, so `s` lies inside the part of `s` that `f` sends
// there — and that part is finite because the image is.
var FiniteImageInjEq = finiteImageInjEqThm{family.Add(registry.ProofEntry{
	Name: "FiniteImageInjEq",
	Key:  "prop_f9617c51293e05bd",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A).",
			Hypotheses: []string{
				"injective_on(s, f)",
			},
			Conclusion: "finite(image(f, s)) ⇔ finite(s)",
		},
		func(a *Argument, f, s Term, separates Fact) {
			a.Iff()
			a.Forward(
				"and back, by recognizing s as a preimage of its own image",
				func(b *Argument, finiteImage Fact) {
					// The part of s that f sends into the whole image. It
					// is all of s, but only the one inclusion below is
					// needed.
					imageSet := b.Term("image(f, s)")
					selfPartSet := b.Term("preimage_on(s, f, image(f, s))")

					// The set driver again, and here it needs nothing
					// from the context: a point of s has its value in
					// image(f, s) by what image means.
					within := b.Have(
						"every point of s sends its value into image(f, s), so s lies inside that part",
						"s ⊆ preimage_on(s, f, image(f, s))",
						BySets())

					bounded := b.Have(
						"and the part is finite, being what an f injective on s sends into the finite image(f, s)",
						"finite(preimage_on(s, f, image(f, s)))",
						// (∀x y. …) ∧ finite(image(f,s)) ⇒ finite(selfPart),
						By(separates, finiteImage, At(FiniteImageInjGeneral, f, s, imageSet)))

					b.Show(
						"so s is inside a finite set",
						// finite(selfPart) ∧ s ⊆ selfPart ⇒ finite(s),
						By(bounded, within, At(FiniteSubset, s, selfPartSet)))
				})
			a.Backward(
				"from s finite to its image finite, which holds of any map — injectivity is idle here",
				func(b *Argument, finiteS Fact) {
					b.Show(
						"FiniteImage at f and s",
						By(finiteS, At(FiniteImage, f, s)))
				})
		}),
})}

// carriedForward is the ⇐ half of both ∃-members below, and it is the
// half that holds of every map: a finite u inside s is exchanged for
// image(f, u), which is finite because u is and which lies inside
// image(f, s) because u lies inside s. The property P is asked of
// image(f, u) on the one side and of the witness on the other, so it
// arrives already proved.
//
// Injectivity never enters, which is why the member that promises it
// and the member that does not run the same three lines here. The
// caller supplies the Case label, because the two reach this arm from
// hypotheses of different strength.
func carriedForward(f, s Term) Action {
	return Given(func(a *Argument, inside Fact) {
		u, small := a.Unpack(inside)
		a.Take(a.Term("image(f, u)"))
		a.Show(
			"so image(f, u) is the B-side witness, and P was assumed of exactly that set",
			By(
				small,
				At(set_image.ImageSubset, f, u, s), // u ⊆ s ⇒ image(f, u) ⊆ image(f, s)
				At(FiniteImage, f, u)))             // finite(u) ⇒ finite(image(f, u))
	})
}

// ExistsFiniteSubsetImageInj — every finite subset of an image is the
// image of a finite subset, and that subset can be chosen so that f
// does not fold it. Stated against an arbitrary property P of the
// B-side set, so that whatever was wanted of the subset survives the
// exchange.
//
// Neither direction argues about finiteness directly. ⇐ hands the
// finiteness over to FiniteImage. ⇒ borrows set_image.SubsetImageInj,
// which already knows how to choose a preimage f does not fold, and
// then reads finiteness BACK along f — a step only that choice makes
// legal, and FiniteImageInjEq is where its legality lives.
//
// So the theorem carries no argument of its own about finite at all:
// it is set_image.SubsetImageInj — the same exchange with no finiteness
// in it — threaded through FiniteImage and FiniteImageInjEq, which are
// where this file already settled how finiteness and image interact.
var ExistsFiniteSubsetImageInj = existsFiniteSubsetImageInjThm{family.Add(registry.ProofEntry{
	Name: "ExistsFiniteSubsetImageInj",
	Key:  "prop_26843f2615549b08",
	Build: family.Theorem(
		"∀P:(set(B) → bool). ∀f:(A → B). ∀s:set(A). "+
			"    (∃t:set(B). finite(t) ∧ t ⊆ image(f, s) ∧ P(t)) ⇔ "+
			"    ∃u:set(A). finite(u) ∧ u ⊆ s ∧ injective_on(u, f) ∧ P(image(f, u))",
		func(a *Argument, P, f, s Term) {
			a.Iff()
			a.Forward(
				"from a finite t ⊆ image(f, s): choose a preimage f "+
					"does not fold, then read its finiteness back through f",
				func(b *Argument, covered Fact) {
					// `carries` holds BOTH what this arm needs from the
					// hypothesis: t's finiteness, and P(t). The t it
					// unpacks is spelled by name in the claim below.
					_, carries := b.Unpack(covered)

					u, chosen := b.Obtain(
						"t lies inside the image, so it IS the image of some u ⊆ s that f does not fold",
						"∃u:set(A). u ⊆ s ∧ t = image(f, u) ∧ injective_on(u, f)",
						// set_image.SubsetImageInj at (f, t, s), whose left
						// side is the containment finiteInside carries and
						// whose right side is the claim above. The tuple
						// reads crossed because that member's binders run
						// the other way round: its `s` is the B-side set
						// and its `t` the A-side ambient one.
						By(carries, set_image.SubsetImageInj))

					b.Take(u)
					// Four conjuncts are discharged here, not one: u ⊆ s and
					// the folding clause come from `chosen`, finite(u) from
					// the cited ⇔, and P(image(f, u)) transfers because
					// `chosen` says t IS image(f, u) while `carries` holds
					// P(t).
					b.Show(
						"and f not folding u makes u finite exactly when image(f, u) is — which it is, being t",
						// (∀x y. …) ⇒ (finite(image(f, u)) ⇔ finite(u))
						By(Normalized, carries, chosen, At(FiniteImageInjEq, f, u)))
				})
			a.Backward(
				"from a finite u ⊆ s that f does not fold — the folding "+
					"is idle here, only u ⊆ s and finite(u) are spent",
				carriedForward(f, s))
		}),
})}

// ForallFiniteSubsetImageInj — the same exchange read universally: a
// property holds of every finite subset of the image exactly when it
// holds of the image of every finite subset of s that f does not fold.
//
// It is ExistsFiniteSubsetImageInj and nothing else. "P holds of every
// t" is "¬P holds of no t", so the ∃-member read at ¬P is this
// statement with both sides negated — one instance, no argument.
var ForallFiniteSubsetImageInj = forallFiniteSubsetImageInjThm{family.Add(registry.ProofEntry{
	Name: "ForallFiniteSubsetImageInj",
	Key:  "prop_e2042ea3bcef3b7e",
	Build: family.Theorem(
		"∀P:(set(B) → bool). ∀f:(A → B). ∀s:set(A). "+
			"    (∀t:set(B). finite(t) ∧ t ⊆ image(f, s) ⇒ P(t)) ⇔ "+
			"    ∀u:set(A). finite(u) ∧ u ⊆ s ∧ injective_on(u, f) ⇒ P(image(f, u))",
		func(a *Argument, P, f, s Term) {
			a.Show(
				"both sides are ExistsFiniteSubsetImageInj's, negated: no finite "+
					"unfolded subset escapes P here exactly when none does there",
				// Normalized + Broadcast — what instantiating the ∀P slot at
				// a λ costs: the shaping reduces the application the λ
				// introduces (the chapter's third reason for it, distinct
				// from the set-builder and the extensionality cases), and
				// that reduction fans the leaf, so Broadcast runs the one
				// close on each piece.
				By(Normalized, Broadcast, At(ExistsFiniteSubsetImageInj, a.Term("λt:set(B). ¬P(t)"), f, s)))
		}),
})}

// ExistsFiniteSubsetImage — the same exchange with the folding clause
// dropped from the right-hand side.
//
// Dropping a conjunct weakens that side, so the two halves inherit
// differently. ⇒ inherits: the INJ member hands back a subset f does
// not fold, and this statement asks for less. ⇐ cannot inherit, since
// a bare finite u ⊆ s does not meet the INJ member's right-hand side —
// but ⇐ never used the folding clause, so the identical carry-forward
// serves it against the weaker hypothesis.
var ExistsFiniteSubsetImage = existsFiniteSubsetImageThm{family.Add(registry.ProofEntry{
	Name: "ExistsFiniteSubsetImage",
	Key:  "prop_ccd84e0cda07d5b6",
	Build: family.Theorem(
		"∀P:(set(B) → bool). ∀f:(A → B). ∀s:set(A). "+
			"    (∃t:set(B). finite(t) ∧ t ⊆ image(f, s) ∧ P(t)) ⇔ "+
			"    ∃u:set(A). finite(u) ∧ u ⊆ s ∧ P(image(f, u))",
		func(a *Argument, P, f, s Term) {
			a.Iff()
			a.Forward(
				"the INJ member exchanges the same t for a subset f "+
					"does not fold; this statement simply asks for less",
				func(b *Argument, covered Fact) {
					b.Show(
						"so its right-hand side, forgetting the folding clause, is this one's",
						By(covered, At(ExistsFiniteSubsetImageInj, P, f, s)))
				})
			a.Backward(
				"the carry-forward again, and it is word for word the INJ member's: injectivity was idle there too",
				carriedForward(f, s))
		}),
})}

// ForallFiniteSubsetImage — the universal reading of the exchange with
// no folding clause: a property holds of every finite subset of the
// image exactly when it holds of the image of every finite subset of s.
//
// ExistsFiniteSubsetImage at ¬P, negated on both sides — the same one
// move that takes ExistsFiniteSubsetImageInj to its own ∀-twin.
var ForallFiniteSubsetImage = forallFiniteSubsetImageThm{family.Add(registry.ProofEntry{
	Name: "ForallFiniteSubsetImage",
	Key:  "prop_b6ef8fb85910bd70",
	Build: family.Theorem(
		"∀P:(set(B) → bool). ∀f:(A → B). ∀s:set(A). "+
			"    (∀t:set(B). finite(t) ∧ t ⊆ image(f, s) ⇒ P(t)) ⇔ "+
			"    ∀u:set(A). finite(u) ∧ u ⊆ s ⇒ P(image(f, u))",
		func(a *Argument, P, f, s Term) {
			a.Show(
				"both sides are ExistsFiniteSubsetImage's, negated: no "+
					"finite subset escapes P here exactly when none does there",
				// Normalized + Broadcast: instantiating the ∀P slot at a λ —
				// ForallFiniteSubsetImageInj's close says why the pair.
				By(Normalized, Broadcast, At(ExistsFiniteSubsetImage, a.Term("λt:set(B). ¬P(t)"), f, s)))
		}),
})}

// FiniteSubsetImage — a set t is a finite subset of image(f, s) exactly
// when it IS the image of some finite subset of s.
//
// The property it is read at, `λv. v = t` — "being exactly this set" —
// is what the whole group below is built on: read at it, either
// ∃-transfer member above stops quantifying over an arbitrary set and
// starts talking about t, each side's ∃ being left with one candidate —
// on the B side t itself, on the A side a u whose image is t. So the
// property is not a device for reusing those members: it is what turns
// a statement quantified over a property into one about a set.
//
// ExistsFiniteSubsetImage at "being t". That member exchanges a finite
// subset of the image satisfying P for a finite subset of s whose image
// satisfies P; at this property each of its two ∃s has exactly one
// candidate to consider, so the B-side one says of t what it would
// otherwise say of an arbitrary member — which is this statement's left
// side — while the A-side one is this statement's right side, up to the
// order its conjuncts are written in. One instance, and no direction
// left to argue on its own.
var FiniteSubsetImage = finiteSubsetImageThm{family.Add(registry.ProofEntry{
	Name: "FiniteSubsetImage",
	Key:  "prop_100cbc7085241915",
	Build: family.Theorem(
		"∀f:(A → B). ∀s:set(A). ∀t:set(B). "+
			"    finite(t) ∧ t ⊆ image(f, s) ⇔ ∃u:set(A). finite(u) ∧ t = image(f, u) ∧ u ⊆ s",
		func(a *Argument, f, s, t Term) {
			a.Show(
				"at the property of being t, each exchanged ∃ has a single candidate: "+
					"t on the B side, and on the A side the u this statement asks for",
				// Normalized + Broadcast: the ∀P slot filled with a λ again —
				// ForallFiniteSubsetImageInj's close says why the pair.
				By(Normalized, Broadcast, At(ExistsFiniteSubsetImage, a.Term("λv:set(B). v = t"), f, s)))
		}),
})}

// FiniteSubsetImageImp — the exchange with its conclusion weakened from
// an equation to an inclusion, and only in the direction that spends
// it.
//
// FiniteSubsetImage hands back a u whose image IS t; this statement
// asks only that the image CONTAIN t. Reflexivity of ⊆ is the whole
// difference between the two.
var FiniteSubsetImageImp = finiteSubsetImageImpThm{family.Add(registry.ProofEntry{
	Name: "FiniteSubsetImageImp",
	Key:  "prop_a7b19fd7c112c432",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A). ∀t:set(B).",
			Hypotheses: []string{
				"finite(t)",
				"t ⊆ image(f, s)",
			},
			Conclusion: "∃u:set(A). finite(u) ∧ u ⊆ s ∧ t ⊆ image(f, u)",
		},
		func(a *Argument, f, s, t Term, covered Fact) {
			// The bare cite CLOSES the claim rather than installing anything
			// to be grounded: the claim is already the instance of
			// SubsetRefl that is wanted, so no ∀-source survives the cite
			// for witnesses to fill. And it is a named fact rather than an
			// `At(…)` entry in the premise list because SubsetRefl is stated
			// over the A-side element type while this use is at a B-side
			// set, and a CROSS-TYPE ground cite does not survive as a `By`
			// premise: the close path type-matches where the premise path
			// demands equality. (The two members below pay the same
			// reflexivity at image(f, s), for the same two reasons.)
			reflexive := a.Have(
				"the set contains itself",
				"t ⊆ t",
				Cite(set_order.SubsetRefl))

			a.Show(
				"the exchange returns an equation where this statement "+
					"wants an inclusion, and t ⊆ t carries it across",
				// Normalized, and for the chapter's extensionality reason
				// rather than the λ-instantiation one: the exchanged equation arrives
				// POINTWISE, and folding `∀ẋ. t ẋ ⇔ image(f, u) ẋ` back into
				// t = image(f, u) is what the shaping does and the refuter
				// does not.
				By(
					Normalized,
					covered,
					reflexive,
					// t finite inside image(f,s) ⇔ ∃u ⊆ s finite with t = image(f, u)
					At(FiniteSubsetImage, f, s, t)))
		}),
})}

// FiniteImageEq — an image is finite exactly when it is already the
// image of a finite piece of its source: a finite image needs only
// finitely much of s to be produced.
//
// FiniteSubsetImage at t := image(f, s). The containment that instance
// asks of t is then image(f, s) ⊆ image(f, s), which is reflexivity, so
// nothing survives on the left but the finiteness — and the right side
// is this statement's, its conjuncts in another order.
var FiniteImageEq = finiteImageEqThm{family.Add(registry.ProofEntry{
	Name: "FiniteImageEq",
	Key:  "prop_f21537b06a5827e4",
	Build: family.Theorem(
		"∀f:(A → B). ∀s:set(A). "+
			"    finite(image(f, s)) ⇔ ∃u:set(A). finite(u) ∧ u ⊆ s ∧ image(f, s) = image(f, u)",
		func(a *Argument, f, s Term) {
			// Named fact, bare cite — FiniteSubsetImageImp's reflexive Have
			// says why, and both reasons hold at this B-side set too.
			reflexive := a.Have(
				"the set contains itself",
				"image(f, s) ⊆ image(f, s)",
				Cite(set_order.SubsetRefl))

			// No shaping, alone among the last four: this cites
			// FiniteSubsetImage in its natural form rather than
			// instantiating a predicate, so no application survives to
			// reduce and no equation arrives pointwise.
			a.Show(
				"FiniteSubsetImage at t := image(f, s), where the containment it asks for is reflexivity",
				By(
					reflexive,
					// image(f,s) finite and inside itself ⇔ ∃u ⊆ s finite with image(f,s) = image(f,u)
					FiniteSubsetImage))
		}),
})}

// FiniteImageEqInj — the same reading, with the piece chosen so that f
// does not fold it.
//
// FiniteSubsetImage has no injective twin in this file, so this member
// reaches past it to ExistsFiniteSubsetImageInj and takes there the
// kind of instance FiniteSubsetImage is made of — the property of being
// a given set — read at image(f, s), which carries the folding clause
// along untouched. The containment that instance leaves on the left is
// the same reflexivity FiniteImageEq pays, so the two members differ in
// which transfer they read and in nothing mathematical besides.
var FiniteImageEqInj = finiteImageEqInjThm{family.Add(registry.ProofEntry{
	Name: "FiniteImageEqInj",
	Key:  "prop_37bd154bab1d5ec2",
	Build: family.Theorem(
		"∀f:(A → B). ∀s:set(A). "+
			"    finite(image(f, s)) ⇔ "+
			"    ∃u:set(A). finite(u) ∧ (u ⊆ s ∧ (image(f, s) = image(f, u) ∧ injective_on(u, f)))",
		func(a *Argument, f, s Term) {
			// Named fact, bare cite — FiniteSubsetImageImp's reflexive Have
			// says why, and both reasons hold at this B-side set too.
			reflexive := a.Have(
				"the set contains itself",
				"image(f, s) ⊆ image(f, s)",
				Cite(set_order.SubsetRefl))

			a.Show(
				"ExistsFiniteSubsetImageInj at the property of being "+
					"image(f, s), whose containment side is again reflexivity",
				// Normalized + Broadcast: the ∀P slot filled with a λ again —
				// ForallFiniteSubsetImageInj's close says why the pair.
				By(
					Normalized,
					Broadcast,
					reflexive,
					At(ExistsFiniteSubsetImageInj,
						a.Term("λv:set(B). v = image(f, s)"), f, s)))
		}),
})}

// ---------------------------------------------------------------------------
// The chapter read the other way round
// ---------------------------------------------------------------------------
//
// Unfolding infinite reaches ¬finite, and that is no change of subject:
// it is the entire content of the word. So when a member's statement is
// an implication with infinite in its conclusion, unfolding leaves a
// finite-side statement standing — and usually the work is then only to
// name the theorem that statement already is. finite is the opposite:
// it cannot be unfolded at all — the door refuses its closure form —
// and every member cites its rules, its induction or its cases instead.
//
// Four of the five members below unfold, and not one of those four binds
// anything at the boundary of the section that does the unfolding. The
// unfolding discharges the antecedent of an implication once that
// implication is exposed, so a boundary that has already taken the
// ∀-prefix leaves the assumption after it with nothing to take. The
// member that does not unfold binds normally, and so does the internal
// lemma of the last.
//
// Membership here is the notion, not the duality — a statement about
// infinite sets need not have a partner on the finite side. The first
// three name a finite-side theorem; the fourth reaches that side through
// the third. The last names nothing: what stands after its unfolding is
// a counting argument about fibres that nothing else in the chapter
// needed, so the file proves it. It is the first member the rule admits
// that has no partner to name.

// InfiniteSuperset — a set containing an infinite set is infinite.
//
// The contrapositive of FiniteSubset across its two finiteness claims,
// and nothing more. Contraposition does not disturb the clause an
// implication normalizes to, so once infinite is out of the way the two
// statements are the same clause.
var InfiniteSuperset = infiniteSupersetThm{family.Add(registry.ProofEntry{
	Name: "InfiniteSuperset",
	Key:  "prop_2d9c8786cac17776",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"infinite(s)",
				"s ⊆ t",
			},
			Conclusion: "infinite(t)",
		},
		// The ∀-prefix left standing is also what leaves FiniteSubset
		// whole, so the citation is at the theorem and not at an instance.
		func(a *Argument) {
			a.Do(Unfold(InfiniteDef)) // ↦ ¬finite(s) ∧ s ⊆ t ⇒ ¬finite(t)
			a.Show(
				"which is FiniteSubset, contraposed",
				Cite(FiniteSubset))
		}),
})}

// InfiniteDiffFinite — taking a finite set away from an infinite one
// leaves an infinite set.
//
// Nothing about what is taken away matters except its finiteness. If the
// remainder were finite, putting t back would exhibit a finite set
// containing s: the remainder and t are both finite, so their join is.
var InfiniteDiffFinite = infiniteDiffFiniteThm{family.Add(registry.ProofEntry{
	Name: "InfiniteDiffFinite",
	Key:  "prop_ea8b61e17f5dc2c6",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"infinite(s)",
				"finite(t)",
			},
			Conclusion: "infinite(s ∖ t)",
		},
		// ↦ ¬finite(s) ∧ finite(t) ⇒ ¬finite(s ∖ t)
		Opening(Unfold(InfiniteDef), func(a *Argument, s, t *Expr[Set[A]], infiniteSFiniteT Fact) {
			remainder := ops(a.Ctx()).SetDifference.Apply(s, t)
			// s with t taken out and then put back — the set the whole
			// argument is built around.
			restored := ops(a.Ctx()).Union.Apply(remainder, t)

			within := a.Have(
				"a point of s either survived the removal or was what was removed",
				"s ⊆ s ∖ t ∪ t",
				BySets())

			a.Show(
				"so a finite remainder would leave s inside a finite set",
				By(
					infiniteSFiniteT,
					within,
					At(FiniteUnionImp, remainder, t), // finite(s ∖ t) ∧ finite(t) ⇒ finite((s ∖ t) ∪ t)
					At(FiniteSubset, s, restored)))   // finite((s ∖ t) ∪ t) ∧ s ⊆ (s ∖ t) ∪ t ⇒ finite(s)
		})),
})}

// InfiniteImage — a map that separates the points of an infinite set
// carries it to an infinite one.
//
// FiniteImageInjEq settles both directions at once for such a map: the
// image is finite exactly when the set is. An equivalence is as good
// backwards as forwards, so it reports the failure of finiteness on one
// side as the failure of finiteness on the other, and that is the whole
// theorem.
var InfiniteImage = infiniteImageThm{family.Add(registry.ProofEntry{
	Name: "InfiniteImage",
	Key:  "prop_e3d9be230324aea1",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A).",
			Hypotheses: []string{
				"infinite(s)",
				"injective_on(s, f)",
			},
			Conclusion: "infinite(image(f, s))",
		},
		// ↦ ¬finite(s) ∧ injective_on(s, f)
		// ⇒ ¬finite(image(f, s))
		Opening(Unfold(InfiniteDef), func(a *Argument, f *Arrow[A, B], s *Expr[Set[A]],
			infiniteAndSeparating Fact) {
			a.Show(
				"an equivalence carries a failure as far as it carries the property",
				// injective_on(s, f) ⇒ (finite(image(f, s)) ⇔ finite(s))
				By(infiniteAndSeparating, At(FiniteImageInjEq, f, s)))
		})),
})}

// InfiniteImageInj — an injective map carries every infinite set to an
// infinite one.
//
// The member above asks only that f separate the points of s, which an
// injective map does at every pair and so in particular at pairs drawn
// from s. Nothing else changes, and nothing needs unfolding: the theorem
// being weakened is already stated of infinite.
var InfiniteImageInj = infiniteImageInjThm{family.Add(registry.ProofEntry{
	Name: "InfiniteImageInj",
	Key:  "prop_749e012987b47d5d",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A).",
			Hypotheses: []string{
				"injective_on(𝕌, f)",
				"infinite(s)",
			},
			Conclusion: "infinite(image(f, s))",
		},
		func(a *Argument, f, s Term, injective, infinite Fact) {
			a.Show(
				"InfiniteImage at f and s, whose separation hypothesis is injectivity on 𝕌 restricted to s",
				By(injective, infinite, At(InfiniteImage, f, s), functions.InjectiveOnSubset, set_order.SubsetUniv))
		}),
})}

// FiniteImageInfinite — a map taking only finitely many values on an
// infinite set takes one of them infinitely often.
//
// Suppose none were taken infinitely often: every fibre {x ∈ s | f(x) =
// f(a)} would then be finite. The fibres cover s, since each point lies
// in the one over its own value; and there are only as many fibres as
// there are values, which is finitely many by hypothesis. So s would be
// a union of finitely many finite sets, hence finite — which it is not.
//
// Indexing the fibres by the VALUES rather than by the points is where
// the hypothesis is spent. Either index gives the same collection of
// fibres — a fibre met at one of its points is the fibre over that
// point's value — but only the one presents that collection as the image
// of a finite set, and that presentation is the whole use the finiteness
// of the image is put to.
var FiniteImageInfinite = finiteImageInfiniteThm{family.Add(registry.ProofEntry{
	Name: "FiniteImageInfinite",
	Key:  "prop_1feae994e8842e37",
	Build: family.Sections(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A).",
			Hypotheses: []string{
				"infinite(s)",
				"finite(image(f, s))",
			},
			Conclusion: "∃a:A. a ∈ s ∧ infinite({x:A | x ∈ s ∧ f(x) = f(a)})",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// The headline contraposed, and where all of the work is: read
			// forwards it is a counting statement with no negation in it.
			pigeonhole := ctx.Lemma(
				"∀f:(A → B). ∀s:set(A). "+
					"    finite(image(f, s)) ⇒ (∀a:A. a ∈ s ⇒ finite({x:A | x ∈ s ∧ f(x) = f(a)})) ⇒ finite(s)",
				func(a *Argument, f, s Term, valuesFinite, fibresFinite Fact) {
					// The family of fibres, indexed by the values f takes on
					// s — the subject of every claim below, and the one term
					// worth a Go name here, being what the close is denoted at.
					fibresTerm := a.Term("image(λy:B. {x:A | x ∈ s ∧ f(x) = y}, image(f, s))")

					cover := a.Have(
						"every point of s lies in the fibre over its own value, so the fibres leave nothing of s out",
						"s = ⋃image(λy:B. {x:A | x ∈ s ∧ f(x) = y}, image(f, s))",
						BySets())

					// The fibres are collected by the values, so however
					// many points share one they are counted once.
					finitelyManyFibres := a.Have(
						"and there are no more fibres than values, which the hypothesis says are finitely many",
						"finite(image(λy:B. {x:A | x ∈ s ∧ f(x) = y}, image(f, s)))",
						By(
							valuesFinite,
							// finite(image(f, s)) ⇒ finite(image(λy. fibre(y), image(f, s))),
							// instantiated one level up because the fibres are
							// a collection of sets: the law's A is the values'
							// element type, its B the fibres'. Witnesses in
							// FiniteImage's stated `∀f. ∀s` order: the cutting
							// map, then the values.
							FiniteImage.Inst(TypeBinder.BindA[B](), TypeBinder.BindB[elementSet]()).
								At(a.Term("λy:B. {x:A | x ∈ s ∧ f(x) = y}"),
									a.Term("image(f, s)"))))

					// The hypothesis speaks about the POINTS of s, so a
					// fibre has to be traced back to one. It can be: the
					// family is cut at values f actually takes on s, and a
					// value taken at a point is that point's own.
					throughAPoint := a.Have(
						"a fibre in the family is the one through a point of s, the value it was cut at being taken there",
						Statement{
							Binders: "∀t:set(A).",
							Hypotheses: []string{
								"t ∈ image(λy:B. {x:A | x ∈ s ∧ f(x) = y}, image(f, s))",
							},
							Conclusion: "∃a:A. a ∈ s ∧ t = {x:A | x ∈ s ∧ f(x) = f(a)}",
						},
						BySets())

					fibresAllFinite := a.Have(
						"so the hypothesis reaches every member of the family, each being a fibre through some point",
						"∀t:set(A). t ∈ image(λy:B. {x:A | x ∈ s ∧ f(x) = y}, image(f, s)) ⇒ finite(t)",
						Derive(func(b *Argument) {
							t := b.Fix()
							collected := b.Assume()

							pt, cutThere := b.Obtain(
								"a point of s the fibre passes through",
								"∃a:A. a ∈ s ∧ t = {x:A | x ∈ s ∧ f(x) = f(a)}",
								By(collected, throughAPoint.At(t)))

							b.Show(
								"and the fibre through a point of s is finite",
								By(cutThere, fibresFinite.At(pt)))
						}))

					// The family stands under a ⋃, under a finite and under a
					// membership, and the union law relates those three
					// readings of one and the same collection.
					a.Show(
						"so s is a union of finitely many finite sets",
						By(cover, finitelyManyFibres, fibresAllFinite, At(FiniteUnions, fibresTerm)))
				})

			return ctx.Theorem(headline, func(a *Argument) {
				// ↦ ¬finite(s) ∧ finite(image(f, s))
				// ⇒ ∃a. a ∈ s ∧ ¬finite({x | x ∈ s ∧ f(x) = f(a)})
				a.Do(Unfold(InfiniteDef))
				a.Show(
					"which is the lemma above, contraposed",
					Cite(pigeonhole))
			})
		}),
})}
