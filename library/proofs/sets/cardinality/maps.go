// maps.go — counting through a map.
//
// Three parts, marked by banners:
//
// - Counting by matching: what a shared count and a map force on each
// other
// - Counting under a map: what a map does to a count
// - Bounding a count

package cardinality

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/internal/setvocab"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Counting by matching: what a shared count and a map force on each other
// ---------------------------------------------------------------------------
//
// Everywhere else in the chapter a count is read OFF a set. Here a
// count is SPENT, on four arguments, each followed by whatever reads it
// — which is the order below.
//
// The CONSTRUCTION matches two finite sets that count the same, point
// for point, and the matching is built rather than found; its reader
// exhibits the map back. The LAYING-IN buys the weaker thing off a
// bound rather than an equality: a map putting one set inside the other
// without reaching all of it. The TRANSPORT carries a size along a
// matching already in hand, and its two readers close that into an
// equivalence and read it at counts. And the PIGEONHOLE says that
// between sets of the same count a map has no room left to choose —
// reaching all of the target and separating the points of the source
// become one condition — with two readers: the self-map case, and the
// image LAW for a map given as landing exactly on its target, which
// has a self-map case of its own.
// Ten members connect these constructions and their consequences.
//
// The construction and the pigeonhole are CONVERSES, and that is why
// the ten belong in one file. Both ask what a shared count forces
// about a map: the construction answers by producing one, the
// pigeonhole by constraining every one there is.
//
// The construction builds a matching by induction over finite sets.
// The laying-in selects a target subset of the source's size and uses
// that matching. The transport carries a size through an injective
// image, and the pigeonhole uses the image count to rule out a merged
// pair. The image law then reads the pigeonhole at an exact image.

// CardEqBijection — two finite sets of the same size can be paired off
// point for point.
//
// By induction on the source set, pairing off one element at a time.
//
// Nothing is matched with ∅ except ∅, and a set counting what ∅ counts
// counts nothing, so at the base both sides are empty and any map at all
// serves: all three claims are about points that do not exist.
//
// At each step one more point p joins the source. The enlarged source
// counts one more than before, so the target counts a successor; a
// successor is at least one, and a set counting at least one has a
// point — take one, call it the partner, and remove it. What is left of
// the target is finite and counts exactly what the smaller source
// counts, so the induction hypothesis matches those two, and the
// matching grows by the pair (p, partner).
//
// One leaf is arithmetic and it is the only one: a target counting
// suc(n) counts n once a point is taken out. The law that does the
// removing states the remainder as a DIFFERENCE, so what has to be
// computed there is a successor's predecessor — the whole of what
// `arith:nat` is spent on here, and the leaf was measured not to close
// without it.
var CardEqBijection = cardEqBijectionThm{family.Add(registry.ProofEntry{
	Name: "CardEqBijection",
	Key:  "prop_e5df3ba593565482",
	Build: family.Sections(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
				"card(s) = card(t)",
			},
			Conclusion: "∃f:(A → B). " +
				"    (∀x:A. x ∈ s ⇒ f(x) ∈ t) ∧ ((∀y:B. y ∈ t ⇒ ∃x:A. x ∈ s ∧ f(x) = y) ∧ injective_on(s, f))",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			countOf := ops(ctx).Card

			// The four laws about the TARGET's points, read at that
			// element type. This member counts on both sides of a map
			// between two element types, and each of these is stated over
			// a single one; unqualified they arrive at the source's.
			targetIsEmpty := CardEqZero.Inst[value]() // card(t) = 0 ⇔ t = ∅
			targetHasAPoint := countsAtLeastOne.Inst[value]()
			countAfterRemoval := CardDelete.Inst[value]()
			finiteAfterRemoval := finite_set.FiniteDelete.Inst[value]()

			// growsByOnePair — a matching of w with v minus one of its
			// points grows to a matching of w together with a new point.
			//
			// This is where the construction actually happens, and it is
			// pure membership: no count appears, so the set driver settles
			// all three claims and the counting is left to the induction
			// that cites this.
			//
			// The map is the obvious extension of h — the new point q goes
			// to the spare point, everything already in w keeps the value
			// h gave it. That q is outside w is what makes the two halves
			// of that description consistent, and that the spare point was
			// REMOVED from the target before h was asked to reach it is
			// what keeps the extension separating: no point of w can be
			// sent to the spare one, so nothing collides with q.
			//
			// The letters are w, v, q, spare, h — NOT the induction's own
			// p, u, t, partner, g: a statement binder claims its spelling
			// for the whole script, and the induction below is where those
			// five names must remain spellable in claim text.
			growsByOnePair := ctx.Lemma(
				Statement{
					Binders: "∀w:set(A). ∀v:set(B). ∀q:A. ∀spare:B. ∀h:(A → B).",
					Hypotheses: []string{
						"q ∉ w",
						"spare ∈ v",
						"(∀x:A. x ∈ w ⇒ h(x) ∈ delete(v, spare)) ∧ " +
							"((∀y:B. y ∈ delete(v, spare) ⇒ ∃x:A. x ∈ w ∧ h(x) = y) ∧ " +
							"    (∀x y:A. x ∈ w ∧ y ∈ w ∧ h(x) = h(y) ⇒ x = y))",
					},
					Conclusion: "∃f:(A → B). " +
						"    (∀x:A. x ∈ insert(q, w) ⇒ f(x) ∈ v) ∧ " +
						"    ((∀y:B. y ∈ v ⇒ ∃x:A. x ∈ insert(q, w) ∧ f(x) = y) ∧ " +
						"        (∀x y:A. x ∈ insert(q, w) ∧ y ∈ insert(q, w) ∧ f(x) = f(y) ⇒ x = y))",
				},
				// Each of the three hypotheses is handed to the set driver
				// at the cases that spend it; the Case comments say which
				// clause of the matching does the work there.
				func(a *Argument, w, v, q, spare, h Term, qOutside, inTarget, matched Fact) {
					a.Take(a.Term("λr:A. COND(r = q, spare, h(r))"))

					a.Do(SplitConjAll(
						// Spends spare ∈ v and h's first clause: q lands on
						// the spare point, which is a point of v, and every
						// other point of insert(q, w) is a point of w, which h
						// sends into v with the spare point deleted — hence
						// into v.
						Case(
							"into: the new point goes to the spare one, and the rest go where h sent them",
							BySets(inTarget, matched)),
						// Spends h's second clause and — the only place it is
						// spent — that q lies outside w: the spare point is
						// reached through q, and every other point of v
						// survives the deletion, so h reaches it from some
						// point of w, which is not q and therefore keeps the
						// value h gave it.
						Case(
							"onto: the spare point is reached through the new "+
								"point, and the rest of v was already reached by h",
							BySets(qOutside, matched)),
						// Spends h's third clause and its first: two points of
						// w are separated by h, and q is separated from all of
						// them because f sends it to the spare point while h's
						// values, being points of v with that point deleted,
						// avoid it.
						Case(
							"separating: h separates the old points, and the new one is the only thing sent to the spare one",
							BySets(matched)),
					))
				})

			// everyFiniteSetMatchesEverySameSize — the induction, stated
			// in the shape the principle concludes in: one set quantified,
			// its finiteness a hypothesis, and the property read at it —
			// matched with EVERY finite set of its own size. The property
			// has to quantify the target, because the induction reaches s
			// through sets whose targets are not the one the theorem was
			// asked about.
			//
			// That shape is what makes the last step of this section a
			// citation rather than an argument. The headline says the same
			// thing with its three hypotheses gathered into one — the two
			// are one proposition, and the section below is where the work
			// is.
			everyFiniteSetMatchesEverySameSize := ctx.Lemma(
				"∀s:set(A). "+
					"    finite(s) ⇒ "+
					"    ∀t:set(B). "+
					"        finite(t) ∧ card(s) = card(t) ⇒ "+
					"        ∃f:(A → B). "+
					"            (∀x:A. x ∈ s ⇒ f(x) ∈ t) ∧ "+
					"            ((∀y:B. y ∈ t ⇒ ∃x:A. x ∈ s ∧ f(x) = y) ∧ "+
					"                (∀x y:A. x ∈ s ∧ y ∈ s ∧ f(x) = f(y) ⇒ x = y))",
				// Nothing is bound: the induction is run ON s, so the
				// principle needs it standing.
				func(a *Argument) {
					// Both obligations below are consumed by the citation
					// that ends the section, which reads them off the
					// context rather than taking a premise list, so neither
					// is named.
					a.Have(
						"at ∅ there is nothing to pair off, and a set counting what ∅ counts is ∅ too",
						// The source's ∅, at the chapter's own element type,
						// which card's declaration pins — no annotation, as
						// against the target's ∅ a few lines down. The
						// target binder is r, not the property's own t: the
						// step below is where t must remain spellable, and
						// this case's strip would otherwise claim it.
						Statement{
							Binders: "∀r:set(B).",
							Hypotheses: []string{
								"finite(r)",
								"card(∅) = card(r)",
							},
							Conclusion: "∃f:(A → B). " +
								"    (∀x:A. x ∈ ∅ ⇒ f(x) ∈ r) ∧ " +
								"    ((∀y:B. y ∈ r ⇒ ∃x:A. x ∈ ∅ ∧ f(x) = y) ∧ (∀x y:A. x ∈ ∅ ∧ y ∈ ∅ ∧ f(x) = f(y) ⇒ x = y))",
						},
						Derive(func(b *Argument) {
							r := b.Fix()
							sized := b.Assume() // finite(r), and card(∅) = card(r)

							// Spent by the set driver below: it is what leaves
							// r no point for the onto clause to reach.
							targetEmpty := b.Have(
								"r counts nothing, and a finite set counting nothing is empty",
								// The target's ∅, at the chapter's SECOND element
								// type. Measured, the equation pins it unaided;
								// the annotation is for the reader, ∅ being
								// nullary and so naming no type of its own.
								// Ascription and not `setvocab.PinnedAt` because
								// this is claim TEXT — the pinned form yields a
								// TERM, which serves a Prop built programmatically
								// (the image part's base case).
								"r = ∅⟨A:B⟩",
								// CardClauses bare — the clause wanted is
								// card(∅) = 0, which binds nothing.
								By(Normalized, sized, CardClauses, At(targetIsEmpty, r)))

							// Any map at all serves; neither set has a point
							// to place, so nothing about it is ever asked.
							//
							// The ε is only how one is written down. It is a
							// TERM and not a principle: `εy:B. ⊤` NAMES an
							// arbitrary point of B, every type being
							// inhabited, and nothing below reads a property
							// off it. Nothing is cited for it.
							b.Take(b.Term("λx:A. εy:B. ⊤"))
							b.Show(
								"so all three claims are about points that do not exist",
								BySets(targetEmpty))
						}))

					a.Have(
						"and one more point on the source is one more point matched, the target having one to spare",
						Statement{
							Binders: "∀p:A. ∀u:set(A).",
							Hypotheses: []string{
								"∀t:set(B). " +
									"    finite(t) ∧ card(u) = card(t) ⇒ " +
									"    ∃f:(A → B). " +
									"        (∀x:A. x ∈ u ⇒ f(x) ∈ t) ∧ " +
									"        ((∀y:B. y ∈ t ⇒ ∃x:A. x ∈ u ∧ f(x) = y) ∧ (∀x y:A. x ∈ u ∧ y ∈ u ∧ f(x) = f(y) ⇒ x = y))",
								"p ∉ u",
								"finite(u)",
							},
							Conclusion: "∀t:set(B). " +
								"    finite(t) ∧ card(insert(p, u)) = card(t) ⇒ " +
								"    ∃f:(A → B). " +
								"        (∀x:A. x ∈ insert(p, u) ⇒ f(x) ∈ t) ∧ " +
								"        ((∀y:B. y ∈ t ⇒ ∃x:A. x ∈ insert(p, u) ∧ f(x) = y) ∧ " +
								"            (∀x y:A. x ∈ insert(p, u) ∧ y ∈ insert(p, u) ∧ f(x) = f(y) ⇒ x = y))",
						},
						Derive(func(b *Argument) {
							p, u := b.Fix(), b.Fix()
							carried := b.Assume() // the property at u, p ∉ u, and finite(u)
							t := b.Fix()
							sized := b.Assume() // finite(t), and t counts what the enlarged source counts

							grown := b.Have(
								"laying in a point the source has not got raises its count by one",
								"card(insert(p, u)) = suc(card(u))",
								// `carried` is where both of the enlargement count's
								// conditions come from: it carries finite(u), and the
								// p ∉ u that says the point laid in is new.
								By(carried, At(InsertCountsOneMore, u, p)))

							partner, inTarget := b.Obtain(
								"so t counts a successor, and a successor is at least one: t has a point to spare",
								// The witness is called partner in the claim —
								// not the y a bare point would get — because the
								// matching claims below splice delete(t, partner)
								// under their own ∀y binder.
								"∃partner:B. partner ∈ t",
								// Equations and equivalences laid end to end, so
								// what composes them is the shaping and not the
								// refuter. Checked by removal: without it these
								// premises reach the refuter, which reports the
								// leaf as one Basic() settles.
								By(
									Normalized,
									grown,
									sized,
									// 0 < suc(card(u)), and 1 ≤ card(t) ⇔ 0 < card(t)
									// — between them, the successor that `grown` and
									// `sized` put under card(t) makes it at least
									// one. The target's count is reached through the
									// parser rather than built: the chapter's Card
									// handle is pinned at the SOURCE's element type
									// (see vocab.go).
									At(nat_order.ZeroLessThanSuc, countOf.Apply(u)),
									At(nat_order.OneLessEqIffPos,
										b.Term("card(t)")),
									// 1 ≤ card(t) ⇔ ∃y. y ∈ t — the bridge from the
									// count to a point, which is the whole of what
									// is wanted here.
									At(targetHasAPoint, t)))

							// t with the partner taken out. Reached through the
							// parser rather than built: the chapter's Delete
							// handle is pinned at the SOURCE's element type, and
							// this is a set of target points (see vocab.go).
							rest := b.Term("delete(t, partner)")

							restCount := b.Have(
								"taking that point out leaves exactly the smaller source's count",
								"card(delete(t, partner)) = card(u)",
								// card(delete(t, partner)) = card(t) - 1 once t is
								// finite and the partner is one of its points; the
								// count above makes card(t) a successor, and this
								// is the one leaf where a successor's predecessor
								// has to be computed.
								//
								// The removal law answers with a COND on
								// membership, and the branch has to be picked
								// before there is a difference to compute at all —
								// `vocab.go`'s fold one level down, between COUNTS.
								// Checked by removal: without it the arith close
								// fails outright.
								ByArith(Normalized, grown, inTarget, sized, At(countAfterRemoval, t, partner)))

							// The property arrives as one conjunct of what the
							// induction hands down, and taking it out of that
							// conjunction is propositional.
							property := b.Have(
								"the property at the smaller source, which is what the induction hands down",
								Statement{
									Binders: "∀t:set(B).",
									Hypotheses: []string{
										"finite(t)",
										"card(u) = card(t)",
									},
									Conclusion: "∃f:(A → B). " +
										"    (∀x:A. x ∈ u ⇒ f(x) ∈ t) ∧ " +
										"    ((∀y:B. y ∈ t ⇒ ∃x:A. x ∈ u ∧ f(x) = y) ∧ (∀x y:A. x ∈ u ∧ y ∈ u ∧ f(x) = f(y) ⇒ x = y))",
								},
								By(carried))

							g, matchesRest := b.Obtain(
								"so the smaller source is matched with what is left of t",
								"∃g:(A → B). "+
									"    (∀x:A. x ∈ u ⇒ g(x) ∈ delete(t, partner)) ∧ "+
									"    ((∀y:B. y ∈ delete(t, partner) ⇒ ∃x:A. x ∈ u ∧ g(x) = y) ∧ "+
									"        (∀x y:A. x ∈ u ∧ y ∈ u ∧ g(x) = g(y) ⇒ x = y))",
								// The property is read AT what is left of t, which
								// is the one instance of it this proof ever needs.
								// That instance asks two things of its target,
								// and the rest of the list is exactly those: the
								// count, from the line above, and the finiteness,
								// which the deletion law carries over from t.
								By(property.At(rest), restCount, sized, finiteAfterRemoval))

							b.Show(
								"and a matching grows by one pair — the new point takes the one that was left over",
								// At (u, t, p, partner, g) the instance pairs the
								// new point with the spare one and extends the
								// matching just obtained. Its three antecedents
								// are exactly the three facts standing here, so
								// the close is three detachments.
								By(inTarget, matchesRest, carried, At(growsByOnePair, u, t, p, partner, g)))
						}))

					a.Show(
						"so the property holds of ∅ and survives an insertion, which is all the induction asks",
						// The principle in its RAW form: what follows is the
						// modus ponens that puts the two obligations standing
						// here into it, and that needs the implication the row
						// states, not the clause form it normalizes to.
						Cite(finite_set.FiniteInductFresh,
							ctx.TermText("λu:set(A). ∀t:set(B). "+
								"    finite(t) ∧ card(u) = card(t) ⇒ "+
								"    ∃f:(A → B). "+
								"        (∀x:A. x ∈ u ⇒ f(x) ∈ t) ∧ "+
								"        ((∀y:B. y ∈ t ⇒ ∃x:A. x ∈ u ∧ f(x) = y) ∧ "+
								"            (∀x y:A. x ∈ u ∧ y ∈ u ∧ f(x) = f(y) ⇒ x = y))")),
						Basic())
				})

			return ctx.Theorem(headline, func(a *Argument) {
				a.Show(
					"so two finite sets of the same size are matched point for point "+
						"— the section above, with its three hypotheses gathered into one",
					// The separation opened onto the clause the induction
					// carries.
					Simp(Fwd(functions.InjectiveOnDef)),
					Cite(everyFiniteSetMatchesEverySameSize))
			})
		}),
})}

// CardEqMutualInverses — two finite sets of the same size carry a map
// and a map back, each undoing the other where it starts.
//
// The map is not built here. Equal counts already pair the two sets off
// point for point, and all that pairing leaves to do is exhibit the
// inverse — which is not a construction either, because being onto and
// being separating are together a pointwise definition of it. Onto says
// that at every point of t there IS a point of s landing on it;
// separating says there is at most one. So "the point f sends here"
// already names a value at each point of t, and a map back is nothing
// but a choice of one such value at each.
//
// The whole of the work is moving the existential out from under the
// membership test. Read as "for each point of B there is a source point
// that serves whenever that point lies in t", the preimage becomes a
// TOTAL assignment on B — and a total assignment is a function. Outside
// t nothing is asked of it, which is why no point of B has to be
// excluded to get one.
//
// Both round trips then come for free, and neither needs a count. A
// point of t is f of the point named at it, which is the assignment
// read forwards. And a point x of s has f(x) in t, so the point named
// at f(x) is a point of s that f sends where x goes — separating says
// that point is x.
//
// Nothing below builds the map, and that is the whole of the point: a
// standing "for each … there is …" is gathered into a single function
// at clause conversion, so the assignment is asserted once, whole, and
// that one statement IS the return map. No choice is made point by
// point and no choice principle is cited.
var CardEqMutualInverses = cardEqMutualInversesThm{family.Add(registry.ProofEntry{
	Name: "CardEqMutualInverses",
	Key:  "prop_b311dc8eeebb7162",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
				"card(s) = card(t)",
			},
			Conclusion: "∃f:(A → B). ∃g:(B → A). " +
				"    (∀x:A. x ∈ s ⇒ f(x) ∈ t ∧ g(f(x)) = x) ∧ (∀y:B. y ∈ t ⇒ g(y) ∈ s ∧ f(g(y)) = y)",
		},
		func(a *Argument, s, t Term, sized Fact) {
			f, matched := a.Obtain(
				"the two counts alone match s with t point for point",
				"∃f:(A → B). "+
					"    (∀x:A. x ∈ s ⇒ f(x) ∈ t) ∧ ((∀y:B. y ∈ t ⇒ ∃x:A. x ∈ s ∧ f(x) = y) ∧ injective_on(s, f))",
				// The instance at (s, t) is the whole justification, and
				// its antecedent is the hypothesis standing here: one
				// detachment.
				By(sized, At(CardEqBijection, s, t)))

			// That matching is the theorem's forward map; only the way
			// back is still owed.
			a.Take(f)

			preimages := a.Have(
				"and a source point can be named at every point of B at "+
					"once — what f reaches it from inside t, anything outside",
				"∀y:B. ∃x:A. y ∈ t ⇒ x ∈ s ∧ f(x) = y",
				// Onto is the only clause spent: it names a preimage at
				// each point of t, and off t the implication asks
				// nothing, so the assignment extends to all of B.
				By(matched))

			a.Show(
				"so the return map is that assignment, and both round "+
					"trips hold — the second because f separates the points of s",
				By(preimages, a.Unfolded(matched, functions.InjectiveOnDef)))
		}),
})}

// CardLeInj — a finite set no larger than another admits an injection
// into it. Choose a subset of the target with the source's size, match
// the source bijectively with that subset, then include it in the target.
var CardLeInj = cardLeInjThm{family.Add(registry.ProofEntry{
	Name: "CardLeInj",
	Key:  "prop_7ff24466083b5ae1",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
				"card(s) ≤ card(t)",
			},
			Conclusion: "∃f:(A → B). image(f, s) ⊆ t ∧ injective_on(s, f)",
		},
		func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]], given Fact) {
			u, chosen := a.ObtainAs[Set[B]](
				"choose a subset of t with the size of s",
				"∃u:set(B). u ⊆ t ∧ has_size(u, card(s))",
				By(given, ChooseSubset.At(t, a.TermAs[Nat]("card(s)"))))
			sized := a.Unfolded(chosen, HasSizeDef)
			f, bijection := a.ObtainAs[Fun[A, B]](
				"match s bijectively with the chosen subset",
				"∃f:(A → B). "+
					"    (∀x:A. x ∈ s ⇒ f(x) ∈ u) ∧ ((∀y:B. y ∈ u ⇒ ∃x:A. x ∈ s ∧ f(x) = y) ∧ injective_on(s, f))",
				By(given, sized, CardEqBijection.At(s, u)))
			a.Take(f)
			a.Show(
				"the injection into u also lands in t",
				BySets(sized, bijection))
		}),
})}

// MutualInversesHasSize — a size crosses a pair of maps that undo each
// other: if f carries s into t and g carries t back into s, each
// returning the other's values to where they came from, then t has
// whatever size s has.
//
// The hypothesis does two quite different jobs, and separating them is
// the whole proof.
//
// Read forwards it IDENTIFIES t. Every value f takes on s lies in t, and
// every point of t is f's value at the point g sends it to — so t is
// exactly the image of s under f, and no count and no finiteness is
// consulted to see it.
//
// Read backwards it makes f INJECTIVE on s. Since g returns each point
// of s to itself, two points of s sharing an f-value are returned to the
// same place, which is to say they were the same point.
//
// After that there is nothing left to argue. HasSizeImageInj is the law
// that carries a size along an injective map's image, and it is cited
// once, at this map and this set.
//
// The shape below is the image part's CardOfUniquePreimages run one level up,
// at has_size rather than at card: the same image named, the same two
// claims made about it — t is what f makes of s, and f merges nothing —
// the same rewrite of the goal onto the image, and one cite of a
// counting law to finish. What differs is where the two claims come
// from. There it is a unique preimage over every point of t, split into
// its existence and its uniqueness; here it is the map back, split into
// its two directions.
var MutualInversesHasSize = mutualInversesHasSizeThm{family.Add(registry.ProofEntry{
	Name: "MutualInversesHasSize",
	Key:  "prop_16b425a4b261f77d",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B). ∀f:(A → B). ∀g:(B → A). ∀n:num.",
			Hypotheses: []string{
				"∀x:A. x ∈ s ⇒ f(x) ∈ t ∧ g(f(x)) = x",
				"∀y:B. y ∈ t ⇒ g(y) ∈ s ∧ f(g(y)) = y",
				"has_size(s, n)",
			},
			Conclusion: "has_size(t, n)",
		},
		// has_size stays folded throughout. The law cited at the end is
		// already stated at a size, so there is nothing for an unfold to
		// reach: it would take both sides apart into a finiteness and a
		// count only for the law to put them back together.
		//
		// g is bound because the statement binds it and the size after it
		// has to be reached; no step below names it. What g does is the
		// backward half of the hypothesis, and that half is spent by the
		// set driver.
		func(a *Argument, s, t, f, g, n Term, mutual Fact) {
			// What the driver spends is the two halves of the hypothesis:
			// the forward half keeps f's values on s inside t, and the
			// backward half puts g(y) in s under each point y of t, where
			// f returns it to y. The size riding along in `mutual` is
			// inert to a driver with no notion of has_size.
			isImage := a.Have(
				"t is exactly what f makes of s: no value of f on s "+
					"escapes it, and every one of its points is reached from g",
				"t = image(f, s)",
				BySets(mutual))

			separates := a.Have(
				"and f merges no two points of s: g returns each of "+
					"them to itself, so a shared value returns to both",
				"injective_on(s, f)",
				Simp(Fwd(functions.InjectiveOnDef)),
				By(mutual))

			// The two sets being one, it is the image whose size is asked
			// for — and the rewrite is also what pins the map's two
			// element types, which the cited law states over its own
			// variables and cannot read off a goal naming only t.
			// ↦ has_size(image(f, s), n)
			a.Do(isImage.Rw())

			a.Show(
				"and an image under a map that folds nothing together carries its source's size",
				// At (f, s, n) the instance is (f separates s) ∧
				// has_size(s, n) ⇒ has_size(image(f, s), n) — the map
				// first, which is the order HasSizeImageInj states.
				// `separates` and the size in `mutual` are exactly its
				// antecedent.
				By(separates, mutual, At(HasSizeImageInj, f, s, n)))
		}),
})}

// MutualInversesHasSizeEq — two sets joined by a pair of maps that undo
// each other have exactly the same sizes.
//
// The hypothesis is what makes this cost nothing beyond the one-way
// law. It asks of (s, f) and (t, g) exactly what it asks of (t, g) and
// (s, f): each map lands inside the other's set, and each returns the
// other's values to where they came from. Trading the two halves leaves
// it standing.
//
// So `MutualInversesHasSize`, which carries a size from the source to
// the target, is read twice — once as it stands, once with the two sets
// exchanged, which is the same theorem the other way round. Those two
// readings are the two halves of the equivalence, and there is nothing
// else to prove. Exchanging the sets exchanges the element types they
// are drawn from, and that is the whole of what the second reading says
// beyond the first.
var MutualInversesHasSizeEq = mutualInversesHasSizeEqThm{family.Add(registry.ProofEntry{
	Name: "MutualInversesHasSizeEq",
	Key:  "prop_4f71e0c2135d80df",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B). ∀f:(A → B). ∀g:(B → A). ∀n:num.",
			Hypotheses: []string{
				"∀x:A. x ∈ s ⇒ f(x) ∈ t ∧ g(f(x)) = x",
				"∀y:B. y ∈ t ⇒ g(y) ∈ s ∧ f(g(y)) = y",
			},
			Conclusion: "has_size(s, n) ⇔ has_size(t, n)",
		},
		// has_size stays folded. The law cited below is itself stated at
		// a size, so unfolding would take both sides of the equivalence
		// apart into a finiteness and a count only for the law to put
		// them back together — and would put a second element type's
		// count in play on the way.
		//
		// The size is bound because the two citations are read at it;
		// nothing else below looks at a particular size.
		func(a *Argument, s, t, f, g, n Term, mutual Fact) {
			// The two readings are taken at the two pairs of element
			// types, and each says which, because the goal names both
			// and an install left to it cannot choose between them.
			// The law's own letters: its A is the SOURCE the size is
			// known at, its B the TARGET it is carried to.
			// A's to B's
			alongF := MutualInversesHasSize.Inst(TypeBinder.BindA[element](), TypeBinder.BindB[value]())
			// B's to A's
			alongG := MutualInversesHasSize.Inst(TypeBinder.BindA[value](), TypeBinder.BindB[element]())

			a.Show(
				"a size crosses the pair whichever way it is asked for: "+
					"the law read along f, and the same law read along g",
				By(
					mutual,
					// Source, target, forward map, inverse, size — the
					// order the law states its binders in. Given the
					// pair, this instance carries a size forward:
					// has_size(s, n) ⇒ has_size(t, n).
					At(alongF, s, t, f, g, n),
					// The same tuple transposed, carrying one back:
					// has_size(t, n) ⇒ has_size(s, n). What it asks of
					// the pair is the standing hypothesis with its two
					// halves read in the other order, which is why
					// nothing has to be established for it.
					At(alongG, t, s, g, f, n)))
		}),
})}

// MutualInversesCard — two sets joined by a pair of maps that undo each
// other count the same: when the source is finite, so is the target,
// and it counts what the source counts. Read at counts, this is the
// converse of CardEqMutualInverses.
//
// A finite set has the size it counts, MutualInversesHasSize carries
// that size across the pair, and a size at the target is its finiteness
// together with its count — the two halves the conclusion asks for.
var MutualInversesCard = mutualInversesCardThm{family.Add(registry.ProofEntry{
	Name: "MutualInversesCard",
	Key:  "prop_b5cb23f168c95647",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B). ∀f:(A → B). ∀g:(B → A).",
			Hypotheses: []string{
				"∀x:A. x ∈ s ⇒ f(x) ∈ t ∧ g(f(x)) = x",
				"∀y:B. y ∈ t ⇒ g(y) ∈ s ∧ f(g(y)) = y",
				"finite(s)",
			},
			Conclusion: "finite(t) ∧ card(t) = card(s)",
		},
		func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]], f *Arrow[A, B], g *Arrow[B, A], mutual Fact) {
			count := a.TermAs[Nat]("card(s)")
			carried := a.Have(
				"s has the size it counts, and the pair of maps carries that size across to t",
				"has_size(t, card(s))",
				By(mutual, FiniteHasSize.At(s), MutualInversesHasSize.At(s, t, f, g, count)))
			a.Show(
				"and a size is a finiteness together with a count",
				By(carried, HasSizeDef.At(t, count)))
		}),
})}

// SurjectiveIffInjectiveGen — between finite sets of equal size, a map
// that stays inside its target reaches all of it exactly when it
// separates the points of its source.
//
// Both halves are counting arguments and they count in opposite
// directions.
//
// Onto, from separating: a map that separates the points of s produces
// an image with exactly s's count. The target has that count too and
// holds the image, and a subset carrying the full count is the whole
// set — so the image IS the target, and every point of it is a value f
// takes on s.
//
// Separating, from onto: if f folded two points of s together, one of
// them could be dropped without losing anything — the map would still
// reach every point of the target from the smaller set. But the smaller
// set is one point short of s, hence one short of the target, and no
// set is reached from fewer points than it has.
//
// Neither half needs all four of the standing hypotheses, and the two
// sections below take only what they spend.
var SurjectiveIffInjectiveGen = surjectiveIffInjectiveGenThm{family.Add(registry.ProofEntry{
	Name: "SurjectiveIffInjectiveGen",
	Key:  "prop_dcb11f439793dd7b",
	Build: family.Sections(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B). ∀f:(A → B).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
				"card(s) = card(t)",
				"image(f, s) ⊆ t",
			},
			Conclusion: "(∀y:B. y ∈ t ⇒ ∃x:A. x ∈ s ∧ f(x) = y) ⇔ injective_on(s, f)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			imageOf, without := ops(ctx).Image, ops(ctx).Delete

			// ontoFromSeparating — a separating map between finite sets of
			// equal size reaches every point of the target.
			//
			// The point of the target this section fixes is called z, not
			// the headline's y: the separating hypothesis standing beside it
			// already binds an x and a y over the SOURCE, and one statement
			// should not spell two different things y.
			ontoFromSeparating := ctx.Lemma(
				"∀s:set(A). ∀t:set(B). ∀f:(A → B). "+
					"    finite(s) ⇒ "+
					"    finite(t) ⇒ "+
					"    card(s) = card(t) ⇒ "+
					"    image(f, s) ⊆ t ⇒ "+
					"    injective_on(s, f) ⇒ "+
					"    ∀z:B. z ∈ t ⇒ ∃x:A. x ∈ s ∧ f(x) = z",
				func(
					a *Argument,
					s, t, f Term,
					finiteS, finiteT, sameSize, inside, separates Fact,
					z Term,
					inTarget Fact,
				) {
					image := imageOf.Apply(f, s)

					// The law this direction turns on, named here at the
					// TARGET's element type. Both the naming and the type are
					// forced: the law is stated over a single element type
					// while this proof speaks at two, and its set witnesses
					// cannot pin which, since normalization spreads its
					// equation pointwise and leaves the element the two sides
					// are compared at as a binder with no term here to fill
					// it. Naming it also keeps it out of the premise list
					// below, where it would be installed afresh and its
					// element type re-read off a goal mentioning both.
					fullCountIsAll := a.Have(
						"a subset carrying the whole of a finite set's count is that set",
						"∀u v:set(B). finite(v) ∧ card(u) = card(v) ∧ u ⊆ v ⇒ u = v",
						By(CardSubsetEq.Inst[value]()))

					sameCount := a.Have(
						"a map that separates the points of s merges none of them, so the image carries s's count",
						"card(s) = card(image(f, s))",
						By(finiteS, separates, At(CardImageInj, f, s)))

					isAll := a.Have(
						"t carries that count too and holds the image, so the image is all of t",
						"image(f, s) = t",
						// Normalized: the law's set equation arrives POINTWISE,
						// and folding a pointwise equivalence back into an
						// equation of sets is extensionality.
						By(Normalized, finiteT, sameSize, sameCount, inside, fullCountIsAll.At(image, t)))

					a.Show(
						"so a point of t is a point of the image, which is to say a value f takes somewhere on s",
						By(isAll, inTarget, set_basic.InImage))
				})

			// separatingFromOnto — the pigeonhole. A map reaching all of a
			// target of the same size cannot fold two points of its source
			// together.
			//
			// Neither the target's finiteness nor the containment appears:
			// what makes the smaller image finite is the source, and what
			// bounds the target's count is being reached from that image.
			separatingFromOnto := ctx.Lemma(
				"∀s:set(A). ∀t:set(B). ∀f:(A → B). "+
					"    finite(s) ⇒ "+
					"    card(s) = card(t) ⇒ "+
					"    (∀y:B. y ∈ t ⇒ ∃x:A. x ∈ s ∧ f(x) = y) ⇒ "+
					"    ∀x y:A. x ∈ s ∧ y ∈ s ∧ f(x) = f(y) ⇒ x = y",
				func(a *Argument, s, t, f Term, finiteS, sameSize, onto Fact, x, y Term, folded Fact) {
					smaller := without.Apply(s, y)
					image := imageOf.Apply(f, smaller)

					// Suppose x and y are distinct. Its only reader is the set
					// driver just below.
					distinct := a.SupposeNot()

					// The crux of the pigeonhole. The set driver spends three
					// facts. `onto` puts some point of s over every point of
					// t. When that point is y, `folded` supplies both x ∈ s
					// and f(x) = f(y), so x lies over it instead. And x
					// survives the deletion because the supposition makes it
					// distinct from y. `onto` is spent here and nowhere else
					// in the section.
					covered := a.Have(
						"dropping y costs the target nothing: whatever f reached "+
							"through y it reaches through x, which survives the deletion",
						"t ⊆ image(f, delete(s, y))",
						BySets(onto, folded, distinct))

					finiteSmaller := a.Have(
						"the smaller set is still finite",
						"finite(delete(s, y))",
						By(finiteS, finite_set.FiniteDelete))

					// The count now runs down that covering, in three steps.
					belowImage := a.Have(
						"t is reached from the image, so it counts no more",
						"card(t) ≤ card(image(f, delete(s, y)))",
						// At (t, image) the instance is finite(image) ∧
						// t ⊆ image ⇒ card(t) ≤ card(image): the subset first,
						// then the set containing it, which is the order
						// CardSubset states.
						By(finiteSmaller, At(finite_set.FiniteImage, f, smaller), covered, At(CardSubset, t, image)))
					belowSmaller := a.Have(
						"and a map makes no new points, so the image counts no more than its source",
						"card(image(f, delete(s, y))) ≤ card(delete(s, y))",
						// At (f, smaller) the instance is finite(smaller) ⇒
						// card(image(f, smaller)) ≤ card(smaller) — the map first,
						// the order CardImageLe states.
						By(finiteSmaller, At(CardImageLe, f, smaller)))
					oneFewer := a.Have(
						"while dropping a point that s really has costs exactly one",
						"card(delete(s, y)) = card(s) - 1",
						By(finiteS, folded, At(CardDelete, s, y)))

					// The chain would be vacuous at count 0, where subtracting
					// one takes nothing away; y is the point that rules it out.
					atLeastOne := a.Have(
						"and s does have a point to drop, so its count is at least one",
						"1 ≤ card(s)",
						// `folded` is where the point comes from: it puts y in
						// s. Everything between that point and the bound is
						// countsAtLeastOne, cited whole — and with the bridge
						// named rather than rebuilt here the step stops being
						// arithmetic: re-measured against this premise list, a
						// plain `By` closes where the old one needed the gated
						// closer. The shaping stays, one detachment and one
						// equivalence being Basic()'s work rather than the
						// refuter's; checked by removal, which sends the leaf
						// to the refuter.
						By(Normalized, finiteS, folded, At(countsAtLeastOne, s)))

					a.Show(
						"so t counts at most one less than s — that is, one less than itself",
						ByArith(atLeastOne, belowImage, belowSmaller, oneFewer, sameSize))
				})

			return ctx.Theorem(headline, func(a *Argument, s, t, f Term, sized Fact) {
				a.Iff()
				// The pigeonhole assumes strictly less than stands here,
				// so this branch is weaker than its section and the cite
				// has to be discharged against what it does assume.
				a.Forward(
					"onto ⇒ separating, by the pigeonhole — which spends "+
						"neither the target's finiteness nor the containment",
					func(b *Argument, reaches Fact) {
						b.Show(
							"a map reaching all of a target that counts what s counts folds no two points of s together",
							// Source, target, map — the order the pigeonhole
							// states its binders in. `sized` carries the
							// source's finiteness and the equal counts, which
							// with `reaches` are the whole of what it asks;
							// the separation it concludes is the claim
							// opened at its points.
							Simp(Fwd(functions.InjectiveOnDef)),
							By(reaches, sized, At(separatingFromOnto, s, t, f)))
					})
				// This branch and that section are one proposition — the
				// section's premises are exactly what stands here — so the
				// cite closes rather than installing.
				a.Backward(
					"separating ⇒ onto, which is the first section and nothing more",
					Cite(ontoFromSeparating))
			})
		}),
})}

// SurjectiveIffInjective — a map of a finite set into itself reaches all
// of it exactly when it separates its points.
//
// A map of a finite set into itself has nowhere to put a repetition: it
// is sending as many points as it has places to fill, so folding two of
// them together would leave a place empty, and leaving a place empty
// would mean two points had shared one.
//
// This is the two-set law with the target taken to be the source, and
// that choice is what leaves so little to prove: two of the general
// law's four hypotheses discharge themselves. Its equal-count
// hypothesis becomes reflexivity of equality on a single count, and the
// finiteness it asks of the target is the finiteness of the source,
// already standing. What is left over — the source finite, the map
// staying inside it — is exactly what this statement assumes.
var SurjectiveIffInjective = surjectiveIffInjectiveThm{family.Add(registry.ProofEntry{
	Name: "SurjectiveIffInjective",
	Key:  "prop_3a7cb94102de85f",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → A).",
			Hypotheses: []string{
				"finite(s)",
				"image(f, s) ⊆ s",
			},
			Conclusion: "(∀y:A. y ∈ s ⇒ ∃x:A. x ∈ s ∧ f(x) = y) ⇔ injective_on(s, f)",
		},
		func(a *Argument, s, f Term, finiteSelfMap Fact) {
			a.Show(
				"the general law with s standing for both of its sets: what "+
					"it asks about the target, the source has already answered",
				// The general law at (s, s, f) — its target slot filled
				// by the source. Stated ∀s. ∀t. ∀f., so the tuple runs
				// source, target, map, and the first two coincide.
				//
				// The equivalence is not taken apart: the arms of the
				// instance are the two standing here, so one citation
				// answers both directions at once.
				By(finiteSelfMap, At(SurjectiveIffInjectiveGen, s, s, f)))
		}),
})}

// ImageImpInjectiveGen — a map that carries a finite set exactly onto a
// set of the same size cannot fold two of its points together.
//
// Nothing is counted here. SurjectiveIffInjectiveGen counts, and it asks
// four things of the pair: each set finite, the two counts equal, and f's
// values on s lying inside t. The standing hypothesis hands over the
// source's finiteness and the equal counts and stops there. Everything
// else — the other two hypotheses, and the side of the equivalence that
// must be standing before the far side can be read off — comes out of the
// image condition alone.
//
// So that one equality is read three ways. Rightwards it makes t the
// image of a finite set, which is finite. Leftwards it says every point
// of t is a value f takes on s, and being reached everywhere is exactly
// what the equivalence trades for separating points. Weakened from an
// equality to a containment it puts those values back inside t.
//
// With the four hypotheses met and the reaching side standing, the
// separating side falls out, and it is the claim.
var ImageImpInjectiveGen = imageImpInjectiveGenThm{family.Add(registry.ProofEntry{
	Name: "ImageImpInjectiveGen",
	Key:  "prop_1c76b4ed455258da",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B). ∀f:(A → B).",
			Hypotheses: []string{
				"finite(s)",
				"card(s) = card(t)",
				"image(f, s) = t",
			},
			Conclusion: "injective_on(s, f)",
		},
		func(a *Argument, s, t, f Term, given Fact) {
			finiteT := a.Have(
				"t is finite, being what f makes of a finite set",
				"finite(t)",
				// vocab.go's pointwise fold. The cited law finds the image
				// finite and the claim asks it of t, so the two meet only
				// once the set equation is folded back from the pointwise
				// form an install spreads it into. Checked by removal:
				// without it these premises reach the refuter, which reports
				// the leaf as one Basic() settles.
				By(Normalized, given, At(finite_set.FiniteImage, f, s)))

			reaches := a.Have(
				"and f reaches every point of t from s, t being exactly the values it takes there",
				"∀y:B. y ∈ t ⇒ ∃x:A. x ∈ s ∧ f(x) = y",
				// Bare of necessity: the membership law is recorded
				// pointwise, so its binders carry the point of t being
				// tested, and this claim quantifies that point rather than
				// naming it. The claim states the instance the law is used
				// at.
				By(Normalized, given, set_basic.InImage))

			inside := a.Have(
				"while none of those values escapes t: they are t, and a set contains itself",
				"image(f, s) ⊆ t",
				By(given, set_order.SubsetRefl))

			a.Show(
				"so the equivalence stands at s, t and f, and its separating side is the claim",
				// Source, target, map — the order the equivalence states its
				// binders in, which is not the map-first order
				// finite_set.FiniteImage takes above.
				By(given, finiteT, reaches, inside, At(SurjectiveIffInjectiveGen, s, t, f)))
		}),
})}

// ImageImpInjective — a map that carries a finite set exactly onto
// itself folds no two of its points together.
//
// The map has as many points to place as it has places to fill, and it
// is given as filling all of them. Two points sent to one would leave
// a place unfilled, and there is no third point left over to fill it.
//
// That is the two-set law with the target taken to be the source, and
// the choice is the whole proof. Of the three things the law asks —
// the source finite, the two counts equal, the image exactly the
// target — two are this statement's own hypothesis, and the third has
// become a count compared with itself.
var ImageImpInjective = imageImpInjectiveThm{family.Add(registry.ProofEntry{
	Name: "ImageImpInjective",
	Key:  "prop_ed716a000a603d9",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → A).",
			Hypotheses: []string{
				"finite(s)",
				"image(f, s) = s",
			},
			Conclusion: "injective_on(s, f)",
		},
		func(a *Argument, s, f Term, given Fact) {
			a.Show(
				"the general law with s standing for both of its "+
					"sets, where the two counts it compares are one count",
				// Source, target, map — the order the general law states
				// its binders in, with the first two coincident. Its
				// middle hypothesis instantiates to card(s) = card(s),
				// so the standing hypothesis is the entire premise list:
				// there is no third fact to supply.
				By(given, At(ImageImpInjectiveGen, s, s, f)))
		}),
})}

// ---------------------------------------------------------------------------
// Counting under a map: what a map does to a count
// ---------------------------------------------------------------------------
//
// `counting.go` spends card's clauses at ∅ and at a point added or removed;
// this file spends them across a list_map, where a count can only fall — and
// falls exactly where the map identifies two points. Each member's own
// doc makes its argument, and this is only the map.
//
// `CardImageInj` counts an injective image by induction over finite
// sets. `CardImageLe` chooses a finite subset with the same image on
// which the map is injective, then bounds that subset's count by the
// source's. The remaining members read these two counting laws.
//
// The five that follow are that equation repackaged. `HasSizeImageInj`
// and `HasSizeImageInjEq` ask it at has_size rather than at card — the
// chapter's cheapest move — the first in one direction and the second as
// the equivalence. `CardOfUniquePreimages` reaches the equation from a
// hypothesis stated about a TARGET set rather than about the map, and
// spends the two halves of a unique-preimage condition separately to get
// there. `SameCountIffInjective` closes the loop, making the equation
// itself the test for separation; its hard direction squeezes a merged
// pair through the inequality above. `CardImageSameFibres` compares two
// maps that identify the same points: one factors through the other by a
// map that separates the other's values, so the two images count the same.
//
// The last FOUR stand slightly apart and form a strand of their own.
// They are not about what an image counts but about EXCHANGING a subset
// of an image for a subset of the source — the parent chapter's law —
// with a count bound riding along on both sides. Members whose SUBJECT
// is the bound, a count standing under or over a given number, are in
// the bounding part below; here it only rides. Across the strand the A-side set is
// called `u`, both binders being `t` otherwise and one proof-level name
// carrying one type.
//
// The strand is a 2×2. `ExistsSmallSubsetImageInj` demands the map
// separate the points it is handed back, and pays for that by reading
// the equation above in each direction; `ExistsSmallSubsetImage` asks
// nothing of the map, and pays instead in arithmetic — it is the one
// member of this file that spends a capability. The two `Forall…`
// members are those two read at a negated property.

// CardImageInj — a map that separates the points of a finite set sends
// it to a set of the same size.
//
// Induction on the set, at the property "f, if it separates this set's
// points, counts it exactly". The property carries the separation as
// its own hypothesis rather than assuming it once outside, and it has
// to: the induction reaches s through sets that are not subsets of s,
// so each of them arrives with a separation hypothesis of its own and
// the step's job is to pass one down.
//
// The strong rule supplies exactly what the step needs and nothing
// more: the point being added is outside the set it is added to, and
// that set is already finite. The first is what makes the added point's
// value NEW to the image — this is where separation is spent, and it is
// the whole content of the theorem. The second is what lets card's
// recursion clause fire at all, on both sides.
//
// With that, the step is two count computations and one substitution.
// Both counts rise by one — the source's because the point is new to
// it, the image's because the value is new to the image — off counts
// the induction hypothesis has already equated.
//
// The hypothesis the property carries also settles how the induction is
// assembled: under a NAME. Spelled out, that hypothesis comes back
// re-quantified under every binder the principle introduces, one
// alternation per case and none of it mathematics. Named, the property
// is a single atom — the cases say it holds of ∅ and survives an
// insertion, the principle says that much reaches every finite set, and
// putting the three together never looks inside it.
var CardImageInj = cardImageInjThm{family.Add(registry.ProofEntry{
	Name: "CardImageInj",
	Key:  "prop_f4383e938553d9a4",
	Build: family.Sections(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A).",
			Hypotheses: []string{
				"injective_on(s, f)",
				"finite(s)",
			},
			Conclusion: "card(image(f, s)) = card(s)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// What an enlarged set passes back to the set it grew out of.
			// Both halves are about the constructors alone — no count and
			// no finiteness appears — so the set driver is the complete
			// method here, and they are proved together because the step
			// consumes them together.
			//
			// The second half is the bookkeeping that lets the induction
			// run at all: the property being carried is a statement ABOUT
			// a separation, so every smaller set must arrive with one of
			// its own. The first half is the theorem's actual content, and
			// the only place the separation is spent for anything but its
			// own descent — a value the image of t already had would have
			// a source in t, which f cannot send to p while keeping p
			// apart from every point of t.
			//
			// The separation is opened at its points here and only here:
			// both halves are read off pairs of points.
			injectivityDescends := ctx.Lemma(
				Statement{
					Binders: "∀f:(A → B). ∀p:A. ∀t:set(A).",
					Hypotheses: []string{
						"injective_on(insert(p, t), f)",
						"p ∉ t",
					},
					Conclusion: "f(p) ∉ image(f, t) ∧ injective_on(t, f)",
				},
				Chain(Unfold(functions.InjectiveOnDef), BySets()))

			return ctx.Theorem(headline, func(a *Argument, f *TermWrapper, s Term, injective, finite Fact) {
				image := ops(a.Ctx()).Image

				// The two counting laws this proof spends, read at the type
				// of f's VALUES. The theorem counts on both sides of a map,
				// so every count it states is one of two different instances
				// of card and each law is wanted at both: unqualified below
				// they arrive at the source type. The base case reads the
				// empty clause off the first, the step the enlargement count
				// off the second.
				valueCounts := CardClauses.Inst[value]()
				valueCountsOneMore := InsertCountsOneMore.Inst[value]()

				// ∅ is nullary, so no use site can read an instance off its
				// argument, and the base case needs it at BOTH element types
				// at once: the empty source, and the empty image it is
				// carried to.
				emptySource := setvocab.PinnedAt(a.Ctx(), "empty_set", elemType())
				emptyImage := setvocab.PinnedAt(a.Ctx(), "empty_set", valueType())

				a.Show(
					"so the property reaches every finite set, and s is one of them",
					ByInduction(finite_set.FiniteInductFresh, finite, Generalizing(injective),
						Case(
							"∅ has nothing to send anywhere: both sides count the empty set",
							Derive(func(b *Argument) {
								noPoints := b.Have(
									"a map carries nothing out of the empty set",
									MakeProp(image.Apply(f, emptySource).Eq(emptyImage)),
									// Bare of necessity: the clauses are recorded
									// POINTWISE, so their binder list carries the
									// point the two sides are compared at, which no
									// term here names. The claim states the instance
									// the cite is used at.
									By(set_image.ImageClauses))

								// The separation assumed of ∅ is never consulted: no
								// two points of ∅ can be confused because it has
								// none, so this half of the induction spends the
								// hypothesis nowhere.
								b.Show(
									"and the empty set counts 0 whichever type its points would have had",
									By(Normalized, noPoints, CardClauses, valueCounts))
							})),

						Case(
							"one more point on the source is one more value in "+
								"the image, because f keeps it apart from the rest",
							Derive(func(b *Argument) {
								// The principle's own set binder is `s`, which the
								// section holds — so the induction set is NAMED.
								x, t := b.Fix(), b.Fix("t")
								carried := b.Assume()  // the property at t, x ∉ t, and finite(t)
								apartOnT := b.Assume() // f separates the points of insert(x, t)

								imageT := image.Apply(f, t)

								inherited := b.Have(
									"the separation descends to t, and on the way says x's value is one the image of t has not got",
									"f(x) ∉ image(f, t) ∧ injective_on(t, f)",
									By(apartOnT, carried, injectivityDescends))

								counted := b.Have(
									"so the property does apply at t, and the two counts are settled there",
									"card(image(f, t)) = card(t)",
									By(inherited, carried))

								sourceCount := b.Have(
									"adding a point t did not have raises t's count by one",
									"card(insert(x, t)) = suc(card(t))",
									// `carried` carries both of the conditions the
									// enlargement count asks for: finite(t), and the
									// x ∉ t that says the point laid in is new.
									By(carried, At(InsertCountsOneMore, t, x)))

								imageInsert := b.Have(
									"the enlarged source's image is the image of t with x's value laid in",
									"image(f, insert(x, t)) = insert(f(x), image(f, t))",
									// Bare for the reason the ∅ clause above is bare.
									By(set_image.ImageClauses))

								imageCount := b.Have(
									"and that value raises the image's count by one in its turn, the image of t being finite too",
									"card(image(f, insert(x, t))) = suc(card(image(f, t)))",
									// The same count read at the image, and it takes one
									// premise the source side does not: `imageInsert`
									// is what makes the enlarged image an insertion
									// for the count to apply to at all. The other two
									// are the count's own conditions — `inherited`
									// says the value laid in is new, and the image of
									// a finite set being finite is what the set laid
									// into must be.
									//
									// That extra premise is also why the shaping
									// survives here where the source side wants none:
									// composing an equation between IMAGES with one
									// between counts is rewriting — `vocab.go`'s fold,
									// one level down from a set law — and the two
									// never meet in clause form. Checked by removal.
									By(
										Normalized,
										imageInsert,
										inherited,
										carried,
										At(finite_set.FiniteImage, f, t),
										At(valueCountsOneMore, imageT, f.Apply(x))))

								b.Show(
									"so both counts rise by one off counts already equal, and stay equal",
									By(Normalized, counted, sourceCount, imageCount))
							})),
					))
			})
		}),
})}

// CardImageLe — a map never sends a finite set onto more points than
// the set has. Choose a finite subset with the same image on which the
// map is injective. Its image has its size, bounded by the source's size.
var CardImageLe = cardImageLeThm{family.Add(registry.ProofEntry{
	Name: "CardImageLe",
	Key:  "prop_5214a4ae38a9d813",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "card(image(f, s)) ≤ card(s)",
		},
		func(a *Argument, f *Arrow[A, B], s *Expr[Set[A]], finite Fact) {
			u, representatives := a.ObtainAs[Set[A]](
				"choose one representative for each image point inside s",
				"∃u:set(A). finite(u) ∧ (u ⊆ s ∧ (image(f, s) = image(f, u) ∧ injective_on(u, f)))",
				By(finite, finite_set.FiniteImage.At(f, s), finite_set.FiniteImageEqInj.At(f, s)))
			a.Show(
				"the image counts u, and u counts no more than s",
				By(finite, representatives, CardImageInj.At(f, u), CardSubset.At(u, s)))
		}),
})}

// HasSizeImageInj — a map that separates the points of a set of a given
// size carries it to a set of that same size.
//
// Having a size is finiteness together with a count, and the two come
// apart here and never meet again. An image is finite whatever the map
// does to the points, so that half spends nothing but the source's
// finiteness, and the parent chapter's finite_set.FiniteImage is the
// whole of it. Losing none of the count is the other half, and there
// the content of the theorem sits: a map that folds no two points of
// its source together reaches exactly as many.
var HasSizeImageInj = hasSizeImageInjThm{family.Add(registry.ProofEntry{
	Name: "HasSizeImageInj",
	Key:  "prop_d028cb0096c0aa08",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A). ∀n:num.",
			Hypotheses: []string{
				"injective_on(s, f)",
				"has_size(s, n)",
			},
			Conclusion: "has_size(image(f, s), n)",
		},
		// The antecedent is bound and then dismantled by the unfold
		// below, which puts the facts it packs in the context under the
		// names the two cases spend; nothing reads it whole.
		func(a *Argument, f, s, n Term, _ Fact) {
			// ↦ finite ∧ card = ·, on both sides at once — and at both
			// ELEMENT types at once, since the size assumed and the size
			// claimed are sizes of sets of different things.
			a.Do(Unfold(HasSizeDef))

			finiteS := a.Hyp("finite(s)")
			separates := a.Hyp("injective_on(s, f)")
			countS := a.Hyp("card(s) = n")

			a.Do(SplitConj(
				Case(
					"the image of a finite set is finite, and how the map treats the points does not enter",
					// finite(s) ⇒ finite(image(f, s)). The separating
					// hypothesis is not among the premises — folding points
					// together only makes an image smaller.
					By(finiteS, At(finite_set.FiniteImage, f, s))),

				Case(
					"and it carries the whole count, no two points of s being sent to one",
					Derive(func(b *Argument) {
						sameCount := b.Have(
							"a map that separates the points of s folds none of them together, so its image has just as many",
							"card(image(f, s)) = card(s)",
							// Finiteness is spent here too, not only in the
							// half above: the counting law asks it of the
							// source before it will say anything.
							By(finiteS, separates, At(CardImageInj, f, s)))

						b.Show(
							"so what counts s counts the image, and s was assumed to count n",
							// vocab.go's fold, one level down from a set law:
							// what meets here is two equations between
							// COUNTS, and the shaping rewrites with them
							// rather than refuting. Checked by removal —
							// without it the leaf falls through to a
							// refutation it never wanted.
							By(Normalized, sameCount, countS))
					})),
			))
		}),
})}

// HasSizeImageInjEq — a map that separates the points of a set neither
// gains nor loses size there: the image has a given size exactly when
// the set has it.
//
// Having a size is finiteness together with a count, so there are two
// things to carry across the map and neither of them is proved here.
// Finiteness is carried by finite_set.FiniteImageInjEq, which is already
// an equivalence. The count is carried by CardImageInj, which is an
// equation between the two counts.
//
// That both come in symmetric form is why nothing below splits into
// cases. An equation has no direction: once the two counts are known
// equal, whichever of them is the stated size makes the other one that
// size too — so a single instance answers both halves of the goal, where
// a case split would cite it twice and pay a second refutation for the
// privilege.
//
// The count law does ask for the SET to be finite, and in one direction
// only the image is known to be. Supplying it there is the second thing
// the finiteness equivalence does.
var HasSizeImageInjEq = hasSizeImageInjEqThm{family.Add(registry.ProofEntry{
	Name: "HasSizeImageInjEq",
	Key:  "prop_72ff1256a4ce3f12",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A). ∀n:num.",
			Hypotheses: []string{
				"injective_on(s, f)",
			},
			Conclusion: "has_size(image(f, s), n) ⇔ has_size(s, n)",
		},
		// The size is bound because the statement binds it, and no step
		// below names it: neither cited law mentions a size at all, and n
		// enters only as the number the two counts are compared against.
		func(a *Argument, f, s, n Term, separates Fact) {
			// ↦ finite ∧ card = ·, on both sides of the equivalence at
			// once — and at both element types, the image being a set of
			// B's where s is a set of A's. From here the finiteness and
			// the count travel by their own laws.
			a.Do(Unfold(HasSizeDef))

			a.Show(
				"so a size crosses the map both ways: the finiteness by an equivalence, "+
					"the count by an equation read whichever way round is wanted",
				By(
					Normalized,
					separates,
					// finite(image(f, s)) ⇔ finite(s). Stated ∀f. ∀s., so
					// the tuple is map-first.
					At(finite_set.FiniteImageInjEq, f, s),
					// finite(s) ⇒ card(image(f, s)) = card(s), the count
					// half; the finiteness it asks for is what the
					// equivalence beside it supplies.
					At(CardImageInj, f, s)))
		}),
})}

// CardOfUniquePreimages — a map under which every point of a target has
// exactly one preimage in a finite set makes the two sets count the
// same.
//
// The unique-preimage hypothesis does double duty, and separating its
// two halves is the whole argument.
//
// EXISTENCE puts a point of s over every point of t, so t lies inside
// what f makes of s; the containment hypothesis puts every value f takes
// on s back inside t, so that image lies inside t. The two sets are
// therefore one set, and nothing but membership was consulted to see it.
//
// UNIQUENESS is separation on s read directly: two points of s sharing a
// value are both preimages of it, that value is a point of t by the
// containment, and over a point of t there is room for only one.
//
// What is left is not argued here but cited — a map that merges no two
// points of a finite set makes an image carrying that set's count. The
// count of t is that count, because t is that image.
var CardOfUniquePreimages = cardOfUniquePreimagesThm{family.Add(registry.ProofEntry{
	Name: "CardOfUniquePreimages",
	Key:  "prop_31acf7154308c59f",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A). ∀t:set(B).",
			Hypotheses: []string{
				"finite(s)",
				"(∀x:A. x ∈ s ⇒ f(x) ∈ t) ∧ (∀y:B. y ∈ t ⇒ ∃!x:A. x ∈ s ∧ f(x) = y)",
			},
			Conclusion: "card(t) = card(s)",
		},
		func(a *Argument, f, s, t Term, given Fact) {
			// The set driver settles this from `given`, and what it spends
			// of it is the EXISTENCE half of the hypothesis, which finds a
			// preimage in s over every point of t, and the containment,
			// which returns f's values on s to t. Uniqueness is not
			// consulted — one preimage or a dozen, the two sets have the
			// same points either way.
			isImage := a.Have(
				"t is exactly what f makes of s: each of its points is reached, and no value of f on s escapes it",
				"t = image(f, s)",
				BySets(given))

			// The driver again, and now it is UNIQUENESS that is spent,
			// together with the containment that carries the shared value
			// into t where uniqueness can be read at it. The finiteness
			// riding along in `given` is inert, as it is to the driver
			// generally.
			separates := a.Have(
				"and f merges no two points of s: both would be "+
					"preimages of their common value, which admits only one",
				"injective_on(s, f)",
				Simp(Fwd(functions.InjectiveOnDef)),
				BySets(given))

			// The two sets being one, it is the image whose count is asked
			// for. ↦ card(image(f, s)) = card(s)
			a.Do(isImage.Rw())

			a.Show(
				"and a separating map's image carries the count of its source",
				// At (f, s) the instance is finite(s) ∧ (f separates s) ⇒
				// card(image(f, s)) = card(s) — the map first, which is the
				// order CardImageInj states.
				By(given, separates, At(CardImageInj, f, s)))
		}),
})}

// SameCountIffInjective — the image of a finite set counts as much as
// the set exactly when the map separates the set's points.
//
// The two directions are paid for very unevenly, and the file shows it:
// one is a citation and the other is the theorem.
//
// Separating ⇒ equal counts is a law of counting under a map, and this
// arm's whole sequent IS that law, so there is nothing left to argue.
//
// Equal counts ⇒ separating is the content, by contradiction. Suppose f
// sent two distinct points x and y of s to one value. Then y is
// redundant: everything f reached through y it still reaches through x,
// which survives the deletion, so dropping y leaves the image exactly
// as it was. The image of the smaller set counts no more than that set,
// and the image is what carries s's count — so s counts no more than
// what is left of s when a point is taken out. But a subset of a finite
// set whose count does not fall short is that set, so the deletion gave
// s back, and y is then a point of s that s does not admit.
//
// No law of numbers appears in the premise lists below, and none is
// needed: the count squeeze never forms a difference of counts, because
// the antisymmetry that would settle one is already inside CardSubsetLe,
// and what finally contradicts is a set equation against a membership.
var SameCountIffInjective = sameCountIffInjectiveThm{family.Add(registry.ProofEntry{
	Name: "SameCountIffInjective",
	Key:  "prop_9265814a2359a32",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "card(image(f, s)) = card(s) ⇔ injective_on(s, f)",
		},
		func(a *Argument, f, s Term, finite Fact) {
			a.Iff()
			a.Forward(
				"a merged pair leaves one of its points redundant, and s "+
					"is not as large as what remains when a point is dropped",
				func(b *Argument, sameCount Fact) {
					// The separation is claimed of pairs of points.
					b.Do(Simp(Fwd(functions.InjectiveOnDef)))
					// x is fixed but never built with — the set driver
					// below reads it out of `merged` and out of the
					// SupposeNot, and nothing else mentions it.
					_, y := b.Fix(), b.Fix()
					merged := b.Assume()
					// Suppose the two points are distinct. Its only
					// reader is that same driver — see there.
					distinct := b.SupposeNot()

					smaller := ops(b.Ctx()).Delete.Apply(s, y)

					collapse := b.Have(
						"y is redundant: what f reached through y it still reaches through x, and x survives the deletion",
						"image(f, s) = image(f, delete(s, y))",
						// The driver spends two facts: `merged` puts x in
						// s at f's value on y, and the supposition makes
						// x distinct from y. The counts are inert to a
						// driver with no notion of card, so they are not
						// handed over.
						BySets(merged, distinct))

					notFewer := b.Have(
						"so s counts no more than what is left of it: s's count is the "+
							"image's, the image is the smaller set's, and a map makes no new points",
						"card(s) ≤ card(delete(s, y))",
						// At (f, smaller) the instance is finite(smaller) ⇒
						// card(image(f, smaller)) ≤ card(smaller) — the map
						// first, the order CardImageLe states.
						//
						// Normalized: the two equations being carried
						// across the bound are equations between COUNTS,
						// so composing them is rewriting rather than
						// refutation — vocab.go's fold one level down from
						// a set law. Checked by removal: without it these
						// premises reach the refuter instead.
						By(
							Normalized,
							sameCount,
							collapse,
							finite,
							At(finite_set.FiniteDeleteImp, s, y),
							At(CardImageLe, f, smaller)))

					isAll := b.Have(
						"and what is left is a subset of a finite set whose count does "+
							"not fall short, which IS that set — so dropping y gave s back",
						"delete(s, y) = s",
						// The law's three antecedents are the three premises
						// ahead of it. (superset, subset) — the
						// positional order, per CardSubsetEq's godoc,
						// which is this chapter's single home for the note:
						// a set-equality conclusion spreads pointwise and
						// opens an install slot no stated-order tuple can
						// fill.
						By(finite, set_order.DeleteSubset, notFewer, At(CardSubsetLe, smaller, s)))

					b.Show(
						"yet y is a point of s, and no point of s survives its own deletion",
						// y ∈ delete(s, y) ⇔ y ∈ s ∧ ¬(y = y) — the right
						// side is false, so `isAll` leaves y a point of s
						// that s does not admit.
						By(Normalized, isAll, merged, At(set_basic.InDelete, s, y, y)))
				})
			a.Backward(
				"a map that separates s's points merges none of "+
					"them, and this arm's sequent IS the law that says so",
				// Cited bare, since the arm and the law are one
				// proposition: there is no instance to name.
				Cite(CardImageInj))
		}),
})}

// CardImageSameFibres — two maps with the same fibres on a finite set have
// images of one size. f is constant on each fibre of g, so it factors
// through g as f = φ ∘ g on s, and φ is one-to-one on the image of g:
// the image of f is the image of g carried one-to-one by φ.
var CardImageSameFibres = cardImageSameFibresThm{family.Add(registry.ProofEntry{
	Name: "CardImageSameFibres",
	Key:  "prop_55b93f2ff47a7bc7",
	Build: family.Theorem(Statement{
		Binders: "∀f:(A → B). ∀g:(A → C). ∀s:set(A).",
		Hypotheses: []string{
			"finite(s)",
			"∀x y:A. x ∈ s ∧ y ∈ s ⇒ (f(x) = f(y) ⇔ g(x) = g(y))",
		},
		Conclusion: "card(image(f, s)) = card(image(g, s))",
	},
		func(a *Argument, f *Arrow[A, B], g *Arrow[A, C], s *Expr[Set[A]], finite, fibres Fact) {
			_, factors := a.Obtain(
				"f is constant on each fibre of g in s, so it factors through g",
				"∃φ:(C → B). ∀x:A. x ∈ s ⇒ f(x) = φ(g(x))",
				Derive(func(b *Argument) {
					b.Take(b.Term("λz:C. f(εy:A. y ∈ s ∧ g(y) = z)"))
					b.Show(
						"a point y of s with g(y) = g(x) has f(y) = f(x)",
						By(fibres))
				}))
			through := a.Have(
				"so the image of f is the image under φ of the image of g",
				"image(f, s) = image(φ, image(g, s))",
				BySets(factors))
			separates := a.Have(
				"φ separates the values of g on s: φ(g(x)) = φ(g(y)) is f(x) = f(y), which is g(x) = g(y)",
				"injective_on(image(g, s), φ)",
				Unfold(functions.InjectiveOnDef),
				BySets(fibres, factors))
			a.Show(
				"so the image of f is as large as the image of g, which is finite as the image of the finite s",
				through.Rw(),
				By(CardImageInj, separates, finite_set.FiniteImage, finite))
		}),
})}

// ExistsSmallSubsetImageInj — a set of fewer than n points inside an
// image, with a property P, is the image of a set of fewer than n
// points that f does not fold.
//
// The parent chapter's `finite_set.ExistsFiniteSubsetImageInj` already
// exchanges a finite subset of the image for a finite subset of the
// source, carrying an arbitrary property P of the B-side set across
// with it. So the bound is not a second thing to transport: read that
// exchange at the property "P, and with fewer than n points" and the
// bound travels as part of P, by the one instance.
//
// What that instance hands back is a bound on the count of image(f, u)
// rather than of u — the property is a property of B-side sets, and on
// the A side the exchange applies it to u's image. `CardImageInj` is
// the whole of the remaining work, and it applies exactly because of
// the clause the INJ member adds: the u it hands back is one f does not
// fold, and a map that separates a finite set's points counts it
// exactly. So the two counts coincide and either bound is the other.
//
// Both directions are those same two facts in opposite orders: ⇐ knows
// u's count and pushes it forward to the image before citing the
// exchange, ⇒ cites the exchange first and reads the image's count back
// onto u.
var ExistsSmallSubsetImageInj = existsSmallSubsetImageInjThm{family.Add(registry.ProofEntry{
	Name: "ExistsSmallSubsetImageInj",
	Key:  "prop_9dfeb4e2fda27e40",
	Build: family.Theorem(
		"∀n:num. ∀P:(set(B) → bool). ∀s:set(A). ∀f:(A → B). "+
			"    (∃t:set(B). t ⊆ image(f, s) ∧ (P(t) ∧ (finite(t) ∧ card(t) < n))) ⇔ "+
			"    (∃u:set(A). u ⊆ s ∧ ((injective_on(u, f) ∧ P(image(f, u))) ∧ (finite(u) ∧ card(u) < n)))",
		func(a *Argument, n, P, s, f Term) {
			// The property both directions read the exchange at. Taking
			// it is the whole of the reduction: the exchange quantifies
			// over an arbitrary property of B-side sets, and "P, and
			// with fewer than n points" is one.
			pAndSmall := a.Term("λt:set(B). P(t) ∧ (card(t) < n)")

			a.Iff()
			a.Forward(
				"the exchange hands back an unfolded u; read the bound it carries back onto u",
				func(b *Argument, covered Fact) {
					u, chosen := b.Obtain(
						"the small set inside the image comes back as a u ⊆ s "+
							"that f does not fold, the bound now sitting on u's image",
						// The headline's right-hand side, conjunct by
						// conjunct, with ONE substitution: its last clause
						// bounds card(u), and what comes back bounds
						// card(image(f, u)).
						"∃u:set(A). u ⊆ s ∧ ((injective_on(u, f) ∧ P(image(f, u))) ∧ (finite(u) ∧ card(image(f, u)) < n))",
						// The same instance as the other arm, used in
						// its other direction; the bound sits on the
						// image because P-and-small is a property of
						// B-side sets.
						By(Normalized, Broadcast, covered, At(finite_set.ExistsFiniteSubsetImageInj, pAndSmall, f, s)))

					b.Take(u)
					b.Show(
						"and the image of an unfolded u has u's own count, so the bound is u's",
						By(Normalized, chosen, At(CardImageInj, f, u)))
				})
			a.Backward(
				"push u's bound forward onto its image, and the exchange has its B-side set",
				func(b *Argument, inside Fact) {
					u, small := b.Unpack(inside)

					counted := b.Have(
						"f keeps u's points apart, so its image has exactly as many",
						"card(image(f, u)) = card(u)",
						// CardImageInj at (f, u) takes both of its
						// conditions from `small`: the ⇒ direction of
						// its separation, and the finite(u) beside it.
						By(small, At(CardImageInj, f, u)))

					b.Show(
						"so image(f, u) is under n too, and that is the exchange's A-side, read at P-and-small",
						// Normalized + Broadcast: the exchange is
						// taken at a λ, and reducing that application
						// fans the leaf — the same pair every
						// property-instance site in the parent's
						// group pays.
						By(
							Normalized,
							Broadcast,
							counted,
							small,
							At(finite_set.ExistsFiniteSubsetImageInj, pAndSmall, f, s)))
				})
		}),
})}

// ExistsSmallSubsetImage — a set of fewer than n points inside an
// image, with a property P, is exactly the image of a set of fewer than
// n points inside the source.
//
// This is `ExistsSmallSubsetImageInj` with the folding clause dropped
// from the right-hand side — and, less visibly, with the conjuncts of
// BOTH sides reordered and regrouped: the INJ member reads
// `t ⊆ image ∧ (P ∧ (finite ∧ card < n))` where this one reads
// `finite ∧ (card < n ∧ (t ⊆ image ∧ P))`. The two `Forall…` members
// below are the contrast — their left-hand sides are the same text
// character for character, so nothing there has to be regrouped.
//
// Dropping a conjunct weakens the right-hand side, so the two halves
// inherit differently — the same split the parent chapter's unbounded
// pair makes.
//
// ⇒ inherits outright: the INJ member exchanges the same t for a subset
// f does not fold, and this statement asks for less.
//
// ⇐ cannot inherit, because a bare u ⊆ s does not meet the INJ member's
// right-hand side. But ⇐ never wanted the folding clause. Its witness is
// image(f, u) itself, which is finite because u is, lies inside
// image(f, s) because u lies inside s, and satisfies P because P was
// assumed of exactly that set. Only the count is left to argue, and it
// is the one thing here that is computed rather than carried: f may
// merge points of u but can never split them, so the image is at most as
// large as u, and u was already under n.
//
// That last step is where this member and its INJ sibling part company,
// and it is why this one spends `arith:nat` where that one spends
// nothing. There the count fact is an EQUATION — a map that folds
// nothing counts its image exactly — which the closer can substitute
// with. Here it is an INEQUALITY, and composing `card(image(f, u)) ≤
// card(u)` with `card(u) < n` is order reasoning the closer does not do:
// ≤ and < are opaque predicates to it. So the composite is stated as a
// fact of its own and closed by the gated arithmetic closer, on the
// file's one arithmetic leaf.
var ExistsSmallSubsetImage = existsSmallSubsetImageThm{family.Add(registry.ProofEntry{
	Name: "ExistsSmallSubsetImage",
	Key:  "prop_b498b025059a3c33",
	Build: family.Theorem(
		"∀n:num. ∀P:(set(B) → bool). ∀s:set(A). ∀f:(A → B). "+
			"    (∃t:set(B). finite(t) ∧ (card(t) < n ∧ (t ⊆ image(f, s) ∧ P(t)))) ⇔ "+
			"    (∃u:set(A). finite(u) ∧ (card(u) < n ∧ (u ⊆ s ∧ P(image(f, u)))))",
		func(a *Argument, n, P, s, f Term) {
			a.Iff()
			a.Forward(
				"the INJ member exchanges the same t for a subset f does not fold; this statement asks for less",
				func(b *Argument, covered Fact) {
					b.Show(
						"so its right-hand side, forgetting the folding clause and regrouped, is this one's",
						// This one line does both things the doc names:
						// it forgets the folding clause AND regroups the
						// conjuncts on each side, the INJ member's
						// grouping not being this statement's. Both are
						// propositional, so one close covers them.
						By(covered, At(ExistsSmallSubsetImageInj, n, P, s, f)))
				})
			a.Backward(
				"the image of a small u is itself small and sits inside image(f, s), so it is the B-side set",
				func(b *Argument, inside Fact) {
					u, small := b.Unpack(inside)

					// The witness, and the only set this arm ever
					// names: everything below is a statement about it.
					b.Take(b.Term("image(f, u)"))

					atMost := b.Have(
						"f may merge points of u but never splits one, so its image has no more of them",
						"card(image(f, u)) ≤ card(u)",
						// CardImageLe at (f, u) takes its one condition,
						// finite(u), from `small`.
						By(small, At(CardImageLe, f, u)))

					under := b.Have(
						"and u was under n already, so the image is under n too",
						"card(image(f, u)) < n",
						// `small` is here only for the card(u) < n it
						// carries.
						ByArith(atMost, small))

					b.Show(
						"finite, under n, inside image(f, s), and P was assumed of it — the four clauses in order",
						By(
							under,
							small,
							At(finite_set.FiniteImage, f, u),    // finite(u) ⇒ finite(image(f, u))
							At(set_image.ImageSubset, f, u, s))) // u ⊆ s ⇒ image(f, u) ⊆ image(f, s)
				})
		}),
})}

// ForallSmallSubsetImageInj — a property holds of every small subset of
// an image exactly when it holds of the image of every small subset of
// the source that f does not fold. "Small" is the same bound on both
// sides: fewer than n points.
//
// It is ExistsSmallSubsetImageInj and nothing else, by the move the
// parent chapter already makes at the unbounded exchange in its own
// ForallFiniteSubsetImageInj. "P holds of every t" is "¬P holds of no
// t", so reading the ∃-member at the property ¬P gives this statement
// with both sides negated — one instance, and no argument beyond
// naming the instance.
//
// In particular the bound is not transported a second time here. The
// ∃-member already carries an arbitrary property of B-side sets, and
// its own proof is that "fewer than n points" travels inside that
// slot; negating the property leaves that untouched, so nothing about
// card or finite is reasoned with on this page.
var ForallSmallSubsetImageInj = forallSmallSubsetImageInjThm{family.Add(registry.ProofEntry{
	Name: "ForallSmallSubsetImageInj",
	Key:  "prop_4f72f87a057b59df",
	Build: family.Theorem(
		"∀n:num. ∀P:(set(B) → bool). ∀s:set(A). ∀f:(A → B). "+
			"    (∀t:set(B). finite(t) ∧ (card(t) < n ∧ t ⊆ image(f, s)) ⇒ P(t)) ⇔ "+
			"    (∀u:set(A). finite(u) ∧ (card(u) < n ∧ (u ⊆ s ∧ injective_on(u, f))) ⇒ P(image(f, u)))",
		func(a *Argument, n, P, s, f Term) {
			// The property the ∃-member is read at: failing P. On the B
			// side nothing small inside the image has it, on the A side
			// no unfolded subset of s does — one side of this statement
			// apiece, denied.
			failsP := a.Term("λt:set(B). ¬P(t)")

			a.Show(
				"ExistsSmallSubsetImageInj negated on both sides: no small subset of "+
					"the image escapes P exactly when no small unfolded u sends one out",
				// Both shapings are load-bearing and each was measured
				// by removal at this leaf. Read at a λ, the ∃-member
				// installs with an unreduced β-redex standing where its
				// own property is — the premise is present but not in
				// the shape the close meets it in, and Normalized is
				// what reduces it. Reducing then fans the leaf in two,
				// one per direction of the equivalence, and without
				// Broadcast only one of them is closed.
				By(Normalized, Broadcast, At(ExistsSmallSubsetImageInj, n, failsP, s, f)))
		}),
})}

// ForallSmallSubsetImage — a property of B-side sets holds of every
// subset of image(f, s) with fewer than n points exactly when it holds
// of the image of every subset of s with fewer than n points. Nothing
// is asked of f: it may fold points of s together.
//
// ForallSmallSubsetImageInj's proof read at the other ∃-law: the same
// negation move, taken at ExistsSmallSubsetImage, which asks nothing of
// the map. The delta is what the close wants — the sibling needs both
// shapings and this one needs neither, each measured at its own leaf.
var ForallSmallSubsetImage = forallSmallSubsetImageThm{family.Add(registry.ProofEntry{
	Name: "ForallSmallSubsetImage",
	Key:  "prop_257419826daa2e05",
	Build: family.Theorem(
		"∀n:num. ∀P:(set(B) → bool). ∀s:set(A). ∀f:(A → B). "+
			"    (∀t:set(B). finite(t) ∧ (card(t) < n ∧ t ⊆ image(f, s)) ⇒ P(t)) ⇔ "+
			"    (∀u:set(A). finite(u) ∧ (card(u) < n ∧ u ⊆ s) ⇒ P(image(f, u)))",
		func(a *Argument, n, P, s, f Term) {
			// The property to read ExistsSmallSubsetImage at: P fails.
			failsP := a.Term("λt:set(B). ¬P(t)")

			a.Show(
				"ExistsSmallSubsetImage at the failing property: on each "+
					"side, every small set having P is no small set escaping it",
				// Shaping measured, not inherited: none is wanted. The
				// premise installs with an application left standing
				// where the ∃-member's own property is, and the single
				// refutation takes it in stride. Declaring Normalized
				// instead reduces it up front and fans the leaf one way
				// per direction of the equivalence, which then closes
				// only under Broadcast as well.
				By(At(ExistsSmallSubsetImage, n, failsP, s, f)))
		}),
})}

// ---------------------------------------------------------------------------
// Bounding a count
// ---------------------------------------------------------------------------
//
// the bounding part: a numeric bound on a count, and the subset that
// realizes one.
//
// `counting.go` relates two counts to each other. This file relates a
// count to a NUMBER standing over it, which is the form a consumer
// carries a finite set around in: shown finite once, counted under some
// n, and then used at whatever sits inside it or is reached from it.
// That is what holds the six together, and it is what no other file in
// the chapter takes as its subject: every statement below stands a
// number on one side of a count — `card(s) ≤ n`, or `n ≤ card(s)` —
// where `counting.go` sets a count against a count, `counting.go` reads a
// count at a constructor, and `counting.go` counts a construction.
//
// A bound can also ride along on a statement whose subject is something
// else, and it is then filed with that subject rather than here: the
// last four members of the image part exchange a subset of an image for a
// subset of the source and carry "fewer than n points" across inside
// the property being exchanged.
//
// The file has two halves and they run in opposite directions.
//
// The first two members carry a bound DOWNWARD — nothing about n is
// recomputed, it simply travels along a containment or across a map, and
// in each case the finiteness and the ceiling cross by separate laws and
// meet nowhere.
//
// The remaining four go the other way: a bound is not merely inherited
// but REALIZED, by a subset of exactly the size asked for.
// `ChooseSubsetStrong` is the induction that does it, and it and its
// internal lemma are stated so that a set with NO count is covered —
// the size bound is an implication rather than a conjunction, so an
// infinite set discharges it vacuously and is asked for a subset of
// every size at once. That is what makes it the strong form, and also
// what makes it awkward to cite, which is why the three that follow
// exist. `ChooseSubset` reads it at a set that HAS a count, the form a
// consumer asks for. `SubsetOfSizeIffLargeEnough` closes the two
// directions into one equivalence, turning the realization from a
// sufficient construction into an exact characterization.
// `ChooseSubsetBetween` is asked for the same size with a set already in
// hand that the answer must contain, so the choosing happens not in u
// but in what u holds beyond s, and the answer is assembled rather than
// merely found.

// BoundedCountOfSubset — a set lying inside a finite set counted at most
// n is itself finite and counted at most n.
//
// The count half takes one step more than the finiteness half, and it
// is a composition rather than a count. Containment already bounds s's
// count by t's; the hypothesis bounds t's by n; so all that is left is
// for ≤ to carry the one across the other. Nothing here counts
// anything, nothing is taken apart, and the only numeric law spent is
// transitivity.
var BoundedCountOfSubset = boundedCountOfSubsetThm{family.Add(registry.ProofEntry{
	Name: "BoundedCountOfSubset",
	Key:  "prop_68274a4d7dd16487",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A). ∀n:num.",
			Hypotheses: []string{
				"s ⊆ t",
				"finite(t) ∧ card(t) ≤ n",
			},
			Conclusion: "finite(s) ∧ card(s) ≤ n",
		},
		func(a *Argument, s, t, n Term, given Fact) {
			countOf := ops(a.Ctx()).Card

			a.Do(SplitConj(
				Case(
					"s is finite by inheritance — it lies inside a finite set, and the bound is not consulted",
					// finite(t) ∧ s ⊆ t ⇒ finite(s)
					By(given, At(finite_set.FiniteSubset, s, t))),

				Case(
					"and its count runs no further than t's, which the hypothesis already holds under n",
					By(
						given,
						// finite(t) ∧ s ⊆ t ⇒ card(s) ≤ card(t)
						At(CardSubset, s, t),
						// card(s) ≤ card(t) ∧ card(t) ≤ n ⇒ card(s) ≤ n
						At(nat_order.LessEqTrans, countOf.Apply(s), countOf.Apply(t), n))),
			))
		}),
})}

// BoundedCountOfImage — a map carries a finite set under a count bound to
// a finite set under that same bound.
//
// The ceiling crosses in two steps, neither of them an assumption about
// the map. A map makes no new points, so the image counts at most what
// the source counts; the source counts at most n by hypothesis; and ≤
// composes. The middle inequality is nowhere in the statement — it is
// the instance CardImageLe is read at, and the transitivity is grounded
// at the three numbers it composes, so the chain stands in the checked
// layer rather than in this comment.
var BoundedCountOfImage = boundedCountOfImageThm{family.Add(registry.ProofEntry{
	Name: "BoundedCountOfImage",
	Key:  "prop_79c7bda265add555",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A). ∀n:num.",
			Hypotheses: []string{
				"finite(s)",
				"card(s) ≤ n",
			},
			Conclusion: "finite(image(f, s)) ∧ card(image(f, s)) ≤ n",
		},
		func(a *Argument, f, s, n Term, given Fact) {
			countOf := ops(a.Ctx()).Card

			// The image's count, through the parser — `vocab.go`'s note on
			// the Card field. It is the low end of the chain below.
			imageCount := a.Term("card(image(f, s))")

			a.Do(SplitConj(
				Case(
					"the image of a finite set is finite, and what the map does to the points does not enter",
					By(given, At(finite_set.FiniteImage, f, s))),

				Case(
					"and its count, which a map can only have lowered, stays under the ceiling the source was under",
					By(
						given,
						// finite(s) ⇒ card(image(f, s)) ≤ card(s)
						At(CardImageLe, f, s),
						// card(image(f, s)) ≤ card(s) ∧ card(s) ≤ n
						// ⇒ card(image(f, s)) ≤ n
						At(nat_order.LessEqTrans, imageCount, countOf.Apply(s), n))),
			))
		}),
})}

// ChooseSubsetStrong — a set has a subset of any size its count leaves
// room for, and a set without a count has one of every size.
//
// By induction on the size asked for. At 0 the empty set is already the
// answer. Each step takes one point out of s, hands what is left to the
// induction — which returns a subset one element short — and puts the
// point back. Putting it back is what makes the two halves of the
// conclusion travel by different laws: containment by the constructor
// laws for insert and delete, the size by the recursion clause of
// has_size, which is stated at precisely this shape.
//
// The finiteness split the statement seems to invite never happens: no
// case analysis appears anywhere below except the induction's own base
// and step. What the step needs from s is a point, and guardDescends
// gets one without ever asking whether s has a count.
//
// The counting is CountsOneMore's, which states what a removal costs
// as a SUCCESSOR rather than as a difference. That is what keeps this
// proof clear of arithmetic: both sides of the step's one numeric
// obligation then carry a successor and the order law strips it, where
// the same removal counted downwards would leave a monus to compute and
// a COND branch to pick.
var ChooseSubsetStrong = chooseSubsetStrongThm{family.Add(registry.ProofEntry{
	Name: "ChooseSubsetStrong",
	Key:  "prop_ee56d10a523d1b87",
	Build: family.Sections(
		Statement{
			Binders: "∀n:num. ∀s:set(A).",
			Hypotheses: []string{
				"finite(s) ⇒ n ≤ card(s)",
			},
			Conclusion: "∃t:set(A). t ⊆ s ∧ has_size(t, n)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			del := ops(ctx).Delete
			countOf := ops(ctx).Card

			// guardDescends is the whole of the induction step's work with
			// s, and the only place in this member where a set's
			// finiteness is argued about rather than passed along —
			// `ChooseSubsetBetween` below makes the same move at a union
			// where this makes it at a deletion. Both of guardDescends'
			// outputs are needed together, which is why it is one lemma
			// and not two: the descended bound is stated at delete(s, x)
			// and so cannot be had before the point x is.
			//
			// What rules out the one set with no point is not finiteness
			// but the bound itself: ∅ is finite and counts 0, and no
			// successor sits at or below 0.
			guardDescends := ctx.Lemma(
				Statement{
					Binders: "∀s:set(A). ∀n:num.",
					Hypotheses: []string{
						"finite(s) ⇒ suc(n) ≤ card(s)",
					},
					Conclusion: "∃x:A. x ∈ s ∧ (finite(delete(s, x)) ⇒ n ≤ card(delete(s, x)))",
				},
				func(a *Argument, s, n Term, guard Fact) {
					nonempty := a.Have(
						"a bound at a successor rules the empty set out",
						"¬(s = ∅)",
						// The two clause packs are cited BARE because the
						// clause each is wanted for is the one at ∅, which
						// binds nothing: finite(∅) from the first, card(∅) = 0
						// from the second. The order laws below are the other
						// half of the sentence — a successor at or below a
						// count puts the predecessor strictly below it, and
						// nothing lies strictly below 0.
						//
						// `vocab.go`'s fold at its equation case, card(∅) = 0
						// being what carries the count: each pack installs as
						// a conjunction under binders nothing here uses, with
						// the ∅-clause inside. Checked by removal — without it
						// these same premises meet the refuter at the unfolded
						// leaf, whose key this member does not carry. Both
						// packs are pairs, hence `Broadcast`: the closer has
						// to run on every half.
						By(
							Normalized,
							Broadcast,
							guard,
							finite_set.FiniteRules,
							CardClauses,
							At(nat_order.SucLessEqIffLessThan, n, countOf.Apply(s)), // n < card(s) ⇔ suc(n) ≤ card(s)
							At(nat_order.LessThanZeroClause, n)))                    // ¬(n < 0)

					x, member := a.Obtain(
						"so it has a point, and that is the one to take out",
						"∃x:A. x ∈ s",
						By(nonempty, At(set_basic.MemberNotEmpty, s))) // (∃x. x ∈ s) ⇔ ¬(s = ∅)

					rest := del.Apply(s, x) // what is left of s once x goes

					descended := a.Have(
						"and once it is gone the bound stands one lower, at n",
						"finite(delete(s, x)) ⇒ n ≤ card(delete(s, x))",
						// Three links, one ground cite each. A finite
						// remainder makes s itself finite, which is what
						// unlocks the bound; s counts one more than the
						// remainder; and a successor bounded by a successor
						// is the same bound between the predecessors — no
						// difference is ever formed, which is where the seed
						// spent its arithmetic.
						By(
							Normalized,
							member,
							guard,
							At(finite_set.FiniteDelete, s, x), // finite(delete(s, x)) ⇔ finite(s)
							At(CountsOneMore, s, x),           // card(s) = suc(card(delete(s, x)))
							// suc(n) ≤ suc(card(delete(s, x))) ⇔ n ≤ card(delete(s, x))
							At(nat_order.SucLessEqSucIff, n, countOf.Apply(rest))))

					a.Take(x)
					a.Show(
						"so x is a point of s that the bound survives the loss of",
						By(member, descended))
				})

			return ctx.Theorem(headline, func(a *Argument) {
				// The induction runs on the SIZE, and the set has to stay
				// quantified across it: the step applies the hypothesis to
				// delete(s, x), which is not the s it is proving about. So
				// nothing is bound here and each case fixes its own set.
				//
				// The rule is structural induction on num, and the verb
				// resolves it from n's TYPE rather than from a citation —
				// which is why this is the one induction in the chapter with
				// no principle among its deps. The others run over the finite
				// sets, where the rule is a theorem and is named:
				// finite_set.FiniteInductFresh.
				n := a.Binder("n")

				a.Induct(n)
				a.Base(
					"at size 0 the bound asks for nothing, and ∅ is a subset of every set",
					func(b *Argument) {
						b.Fix()    // the set, which nothing below has to name
						b.Assume() // the bound at 0 is spent nowhere: ∅ answers it for every s

						// ∅ is nullary, so it has no argument to read an
						// element type from and is pinned at the build site.
						empty := setvocab.Pinned(b.Ctx(), "empty_set")

						b.Take(empty)
						b.Show(
							"∅ lies inside every set, and it is the only set of size 0",
							// EmptySubset is bare of necessity — its instance
							// at s is absorbed by the install, leaving nothing
							// to ground. And no fold: measured, these two
							// close the goal as they arrive, which neither of
							// this member's other two closes does.
							By(set_order.EmptySubset, At(HasSizeZero, empty))) // has_size(∅, 0) ⇔ ∅ = ∅
					})
				a.Step(
					"take a point out of s, fill what is left by the hypothesis, and put the point back",
					func(b *Argument, hypothesis Fact) {
						s := b.Fix()
						bound := b.Assume()

						x, taken := b.Obtain(
							"s has a point the bound survives the loss of",
							"∃x:A. x ∈ s ∧ (finite(delete(s, x)) ⇒ n ≤ card(delete(s, x)))",
							By(bound, guardDescends))

						rest := del.Apply(s, x) // what is left of s once x goes

						t, smaller := b.Obtain(
							"so the hypothesis fills what is left, one element short",
							"∃t:set(A). t ⊆ delete(s, x) ∧ has_size(t, n)",
							By(taken, hypothesis.At(rest)))

						// The subset the theorem returns, and the chapter's
						// first BUILT insertion — everywhere else insert is
						// only stated, which is why `vocab.go` gained the
						// handle at this member rather than before it.
						grown := ops(b.Ctx()).Insert.Apply(x, t)

						inside := b.Have(
							"putting the point back keeps the subset inside s: "+
								"x came out of s, and t lies inside what was left",
							"insert(x, t) ⊆ s",
							By(
								taken,
								smaller,
								At(set_order.InsertSubset, t, s, x),  // insert(x, t) ⊆ s ⇔ x ∈ s ∧ t ⊆ s
								At(set_order.SubsetDelete, t, s, x))) // t ⊆ delete(s, x) ⇔ x ∉ t ∧ t ⊆ s

						sized := b.Have(
							"and it goes back as an element t has not got, so the size rises by exactly one",
							"has_size(insert(x, t), suc(n))",
							// `vocab.go`'s pointwise fold, at the successor
							// clause: it states the enlargement as an
							// equivalence between MEMBERSHIPS (`∀ẋ. p ẋ ⇔
							// q ẋ`) and the claim is about the sets.
							// Checked by removal — without it these
							// premises meet the refuter with that
							// equivalence still spread. The clause is a
							// PAIR, hence `Broadcast`; removing that leaves
							// the size-0 half standing.
							By(
								Normalized,
								Broadcast,
								smaller,
								At(set_order.SubsetDelete, t, s, x), // x ∉ t, from t ⊆ delete(s, x)
								At(HasSizeClauses, grown, n)))       // the successor clause, at insert(x, t) and n

						b.Take(grown)
						b.Show(
							"so t with x laid back in is a subset of s of size suc n",
							By(inside, sized))
					})
			})
		}),
})}

// ChooseSubset — the realization law in its everyday form: a set counted
// at or above n contains a set of exactly n points.
//
// All the work is ChooseSubsetStrong's. The only thing between the two
// statements is the shape of what is assumed: the strong form guards
// its conclusion by an IMPLICATION rather than a conjunction, for the
// reason the file header gives, and that is exactly what makes it
// awkward to cite — a consumer holds the bound outright, not under
// finiteness.
//
// So the whole step is that a fact implies the implication it is the
// strong reading of: the guard is discharged without ever being examined.
var ChooseSubset = chooseSubsetThm{family.Add(registry.ProofEntry{
	Name: "ChooseSubset",
	Key:  "prop_9b393c0d44d44114",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀n:num.",
			Hypotheses: []string{
				"n ≤ card(s)",
			},
			Conclusion: "∃t:set(A). t ⊆ s ∧ has_size(t, n)",
		},
		func(a *Argument, s, n Term, given Fact) {
			a.Show(
				"the strong form at n and s, whose guard leads into "+
					"the very bound the hypothesis supplies outright",
				// (finite(s) ⇒ n ≤ card(s)) ⇒ ∃t. t ⊆ s ∧ has_size(t, n).
				// Grounded in ChooseSubsetStrong's OWN binder order, which
				// runs the count before the set — the reverse of this
				// statement's.
				By(given, At(ChooseSubsetStrong, n, s)))
		}),
})}

// SubsetOfSizeIffLargeEnough — a set has a subset of size n exactly when
// its count leaves room for one.
//
// Both halves of `ChooseSubsetStrong` are visible here, and the value of
// stating the equivalence is that they are so unevenly paid for. One
// direction is that theorem entire — an induction on the size, peeling a
// point at a time and putting it back. The other is a reading, and it
// spends one law: a subset of a finite set counts no more than the set.
//
// The guard is the whole of the obstruction, and stating the
// equivalence is what says so: it rules out any further condition
// hiding behind the vacuous case the header describes.
//
// The reading direction never counts anything. `card(t)` is not computed
// from t — it is read off the abbreviation, has_size(t, n) being
// finite(t) together with a count of n — so no clause of the recursion
// is consulted and no set is taken apart. What the containment law asks
// for beyond that is the finiteness of the CONTAINING set, which is
// precisely the guard the statement already hands over.
//
// One order law is spent in all, and no arithmetic. That is a
// consequence of how the size is carried rather than of anything about
// ≤: a size is an EQUATION between n and a count, so the bound
// containment gives on that count becomes the bound on n by
// substitution, and no second inequality is ever formed for
// transitivity to compose. Reading the abbreviation as the equivalence
// it is, rather than weakening it to the bound wanted, is what keeps it
// that way.
var SubsetOfSizeIffLargeEnough = subsetOfSizeIffLargeEnoughThm{family.Add(registry.ProofEntry{
	Name: "SubsetOfSizeIffLargeEnough",
	Key:  "prop_78d057f3e243d95b",
	Build: family.Theorem(
		"∀n:num. ∀s:set(A). (finite(s) ⇒ n ≤ card(s)) ⇔ (∃t:set(A). t ⊆ s ∧ has_size(t, n))",
		func(a *Argument, n, s Term) {
			a.Iff()
			a.Forward(
				"produce the subset — this direction is ChooseSubsetStrong entire, and adds nothing to it",
				// ↦ closes, bare and without witnesses. Nothing is
				// deduced FROM ChooseSubsetStrong: the split hands this
				// arm a sequent that IS that theorem, guard and
				// conclusion together, so the cite matches the leaf
				// rather than installing a fact to refute against.
				Cite(ChooseSubsetStrong))
			a.Backward(
				"a subset of size n puts a count of n inside s, and s counts at least what lies inside it",
				func(b *Argument, hasSubset Fact) {
					// The guard, taken first: the containment law below
					// asks for it, and it is all this direction wants
					// from the left-hand side.
					finite := b.Assume()

					t, inside := b.Unpack(hasSubset) // t ⊆ s ∧ has_size(t, n)

					sized := b.Have(
						"having a size is being finite and counting it, which is all has_size abbreviates",
						"has_size(t, n) ⇔ finite(t) ∧ card(t) = n",
						// ↦ closes. The unfold reaches the constant on the
						// left and leaves the right-hand side facing
						// itself. The closer treats has_size as opaque —
						// no premise below says what a size is — so
						// without this the count inside t is out of reach.
						Unfold(HasSizeDef))

					b.Show(
						"so n IS t's count, and lying inside s puts that count under s's",
						By(
							Normalized,
							finite,
							inside,
							sized,
							// finite(s) ∧ t ⊆ s ⇒ card(t) ≤ card(s)
							At(CardSubset, t, s)))
				})
		}),
})}

// ChooseSubsetBetween — between a small set and a big one there is a set
// of any size the two leave room for.
//
// s is inside u and counts at most n, and u — if it can be counted at
// all — counts at least n. The answer is s together with enough of what
// lies outside it, and the whole proof is the two words "enough of":
// how many points are wanted, and that u ∖ s has that many to give.
//
// How many is the SHORTFALL, and it is taken as a WITNESS rather than
// computed: s's bound is spent once, at the very start, for a d with
// n = card(s) + d, and no comparison is made again. That is what keeps
// the proof clear of arithmetic. Written the obvious way the shortfall
// is n - card(s), and then every later step carries a truncating
// difference the closer holds as an opaque atom, and the final size is
// a subtraction that has to be added back under a guard saying it did
// not truncate. Named as a summand instead, the quantity needs no guard
// and the final size is the sum the union law already produces. Two
// numeric laws are spent in the whole member — the one that names the
// shortfall and the one that cancels it.
//
// The other half is that u ∖ s really has d points to give, and it is
// the only place u's ceiling is used. `ChooseSubsetStrong` asks for it
// in the form that covers a u with no count at all, so what has to be
// produced is an implication: IF the outside is finite, THEN it holds
// at least d. Under that assumption u is finite too, because s and the
// outside cover it — and a finite u is exactly the case its ceiling
// speaks about. The chapter's subset split then reads card(u) as
// card(s) + card(u ∖ s) while the shortfall reads n as card(s) + d, so
// cancelling the card(s) both carry leaves d against the outside's
// count.
//
// Nothing case-splits, and the finite/infinite distinction the statement
// invites is never made: the two implications simply compose.
var ChooseSubsetBetween = chooseSubsetBetweenThm{family.Add(registry.ProofEntry{
	Name: "ChooseSubsetBetween",
	Key:  "prop_b606ae9eeecdda76",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num. ∀s u:set(A).",
			Hypotheses: []string{
				"finite(s)",
				"card(s) ≤ n",
				"s ⊆ u",
				"finite(u) ⇒ n ≤ card(u)",
			},
			Conclusion: "∃t:set(A). s ⊆ t ∧ (t ⊆ u ∧ has_size(t, n))",
		},
		func(a *Argument, n, s, u Term, given Fact) {
			countOf := ops(a.Ctx()).Card
			outside := ops(a.Ctx()).SetDifference.Apply(u, s) // what u holds beyond s

			d, shortfall := a.Obtain(
				"how many points short of n the set in hand is",
				"∃d:num. n = card(s) + d",
				// The bound is spent here and nowhere else; from this line on
				// the shortfall is a number in its own right and no
				// comparison is made again.
				By(given, nat_order.LessEqExists))

			// What the driver spends of `given` is s ⊆ u; the count riding
			// along in it is inert to a driver with no notion of card.
			cover := a.Have(
				"s and what u holds beyond it cover u between them",
				"s ∪ (u ∖ s) = u",
				BySets(given))

			countable := a.Have(
				"so u can be counted as soon as that outside part can",
				"finite(u ∖ s) ⇒ finite(u)",
				// finite(s) ∧ finite(u ∖ s) ⇒ finite(s ∪ (u ∖ s)),
				// which `cover` reads as finite(u).
				By(Normalized, given, cover, At(finite_set.FiniteUnionImp, s, outside)))

			available := a.Have(
				"and then it has the shortfall to give: u's ceiling less s's own count",
				"finite(u ∖ s) ⇒ d ≤ card(u ∖ s)",
				// Three ground links and no case split. Finiteness of the
				// outside part unlocks u's ceiling through `countable`; the
				// split reads that ceiling as a sum over s and the outside;
				// `shortfall` reads n as a sum over s and d; and cancelling
				// the card(s) both sums carry leaves the comparison the
				// claim states. The cover is not among the premises — it
				// did its work inside `countable`.
				By(
					Normalized,
					given,
					shortfall,
					countable,
					// finite(u) ∧ s ⊆ u ⇒ card(u) = card(s) + card(u ∖ s)
					At(countsSubsetAndRest, s, u),
					// card(s) + d ≤ card(s) + card(u ∖ s) ⇔ d ≤ card(u ∖ s)
					At(nat_order.LessEqAddCancel, countOf.Apply(s), d, countOf.Apply(outside))))

			v, chosen := a.Obtain(
				"so choose that many of them",
				"∃v:set(A). v ⊆ u ∖ s ∧ has_size(v, d)",
				// (finite(u ∖ s) ⇒ d ≤ card(u ∖ s)) ⇒
				// ∃t. t ⊆ u ∖ s ∧ has_size(t, d).
				// Its hypothesis is `available` verbatim, which is why that
				// fact was stated as an implication rather than proved under
				// an assumption: the strong form asks for exactly this, and
				// so covers a u with no count at all.
				By(available, At(ChooseSubsetStrong, d, outside)))

			grown := ops(a.Ctx()).Union.Apply(s, v) // the answer

			// Consumed by the driver: `chosen`'s containment alone, the size
			// beside it being inert. Disjointness is what the choosing was
			// done outside s FOR, and it is the hypothesis the size below
			// cannot do without.
			apart := a.Have(
				"and they meet s nowhere, having been chosen outside it",
				"disjoint(s, v)",
				BySets(chosen))

			sized := a.Have(
				"so laying them alongside s makes a set of exactly n points",
				"has_size(s ∪ v, n)",
				By(
					Normalized,
					given,
					apart,
					chosen,
					shortfall,
					// finite(s) ⇔ has_size(s, card(s)) — the assumed
					// finiteness of s read as the size the union law wants.
					At(FiniteHasSize, s),
					// has_size(s, card(s)) ∧ has_size(v, d) ∧ disjoint(s, v)
					// ⇒ has_size(s ∪ v, card(s) + d), whose sum
					// `shortfall` renames to n. No difference is ever formed
					// and no guard is needed for one.
					At(HasSizeUnion, s, v, countOf.Apply(s), d)))

			// Consumed by the driver: s ⊆ u from `given` for the second half,
			// and `chosen`'s containment for it too — what was chosen lies
			// outside s but still inside u. The first half holds of any two
			// sets whatever.
			between := a.Have(
				"and it lies between the two: s is one of its parts, and both parts lie in u",
				"s ⊆ s ∪ v ∧ s ∪ v ⊆ u",
				BySets(given, chosen))

			a.Take(grown)
			a.Show(
				"so s with the chosen points laid in is the set the theorem asks for",
				// Nothing is deduced here: these two facts ARE the conclusion,
				// grouped the other way round. They are named rather than left
				// ambient so that the last line says which of the facts above
				// the theorem actually hands back.
				By(between, sized))
		}),
})}
