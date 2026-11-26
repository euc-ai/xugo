// well_founded.go — the well-founded relation chapter.
//
// `wellfounded` is defined by the minimal-element reading: every inhabited
// predicate has a P-minimal point — one with no OTHER point of the
// predicate below it. The chapter opens with that definition and the
// measure relation's, trades the definition for the induction reading
// — the form the chapter's arguments run on — and then builds the
// recursion theorem and the inverse-image/measure route on top of it.

package well_founded

import (
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/relations/closure"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// WellfoundedDef — a relation is well-founded when every inhabited predicate has
// a minimal point: one holding, with nothing below it holding.
var WellfoundedDef = wellfoundedDefThm{family.Define(registry.DefEntry{
	Name:  "WellfoundedDef",
	Key:   "prop_c1ff1f97e77e1d89",
	Const: "wellfounded",
	Type:  "(A → A → bool) → bool",
	Equations: []string{
		"∀R:(A → A → bool). " +
			"    wellfounded(R) ⇔ ∀P:(A → bool). (∃x:A. P(x)) ⇒ ∃x:A. P(x) ∧ ∀y:A. R(y, x) ⇒ ¬P(y)",
	},
})}

// MeasureLessDef — the relation a ℕ-valued measure induces: x below y when
// the measure says so.
var MeasureLessDef = measureLessDefThm{family.Define(registry.DefEntry{
	Name:      "MeasureLessDef",
	Key:       "prop_ebdce298a94a8c94",
	Const:     "measure_less",
	Type:      "(A → num) → A → A → bool",
	Equations: []string{"∀m:(A → num). ∀x y:A. measure_less(m, x, y) ⇔ m(x) < m(y)"},
})}

// accessible — the constructive face of well-foundedness: a point is
// ACCESSIBLE when every point below it is. One rule, whose premise
// ranges over the whole of R's field below x — an infinitary premise,
// a premise under ∀ and a guard. The theorems it comes with are the
// four faces below, and `Accessibility` is what makes this predicate
// the same notion as wellfounded.
var accessible = family.DefineInductive(registry.InductiveEntry{
	Name: "Accessible",
	Keys: registry.InductiveKeys{
		Rules:        "prop_d7ff9db0fc9267f3",
		Induct:       "prop_cae49efbac37f1a7",
		Cases:        "prop_417554b539af6d49",
		InductStrong: "prop_6c425f770b380fb7",
	},
	Const:  "accessible",
	Type:   "(A → A → bool) → A → bool",
	Params: []string{"R"},
	Rules: []string{
		"∀x:A. (∀y:A. R(y, x) ⇒ accessible(R, y)) ⇒ accessible(R, x)",
	},
})

// AccessibleRules — a point whose every predecessor is accessible is
// accessible: the definition's one rule, registered verbatim.
var AccessibleRules = accessibleRulesThm{accessible.Rules}

// AccessibleInduct — induction along accessibility: a property that a
// point has whenever every predecessor has it holds at every accessible
// point.
var AccessibleInduct = accessibleInductThm{accessible.Induct}

// AccessibleInductStrong — the same induction, with the step told that
// the predecessors it reasons from are themselves accessible.
var AccessibleInductStrong = accessibleInductStrongThm{accessible.InductStrong}

// AccessibleCases — the one rule is exhaustive: an accessible point is
// exactly one all of whose predecessors are accessible.
var AccessibleCases = accessibleCasesThm{accessible.Cases}

// Induction — well-foundedness is exactly the licence to do induction
// along the relation. Both directions are one instantiation at the
// complement predicate: a minimal ¬P-point is precisely a point where
// the induction closure fails, so each reading, applied at ¬P, refutes
// the failure of the other.
var Induction = inductionThm{family.Add(registry.ProofEntry{
	Name: "Induction",
	Key:  "prop_25eba7383747b831",
	Build: family.Theorem("∀R:(A → A → bool). "+
		"    wellfounded(R) ⇔ ∀P:(A → bool). (∀x:A. (∀y:A. R(y, x) ⇒ P(y)) ⇒ P(x)) ⇒ ∀x:A. P(x)",
		func(a *Argument, R Term) {
			ctx := a.Ctx()
			P := ctx.Var("P_0", MakeFun(MakeVarType("A"), TypeBool))
			x := ctx.Var("x", MakeVarType("A"))
			notP := x.To(Not(P.Apply(x)))

			a.Do(
				Unfold(WellfoundedDef),
				SplitIff(
					Forward(
						"minimal points yield induction: a minimal ¬P-point is exactly a "+
							"point where the closure fails, so under the closure ¬P is uninhabited",
						StripQuant(),
						By(At(ResidentHyp(ctx.MakePropText(
							"∀P:(A → bool). (∃x:A. P(x)) ⇒ ∃x:A. P(x) ∧ (∀y:A. R₀(y, x) ⇒ ¬P(y))")),
							notP)),
					),
					Backward(
						"induction yields minimal points: were P inhabited with no minimal "+
							"point, ¬P would satisfy the closure, and induction at ¬P would empty P",
						StripQuant(),
						By(At(ResidentHyp(ctx.MakePropText(
							"∀P:(A → bool). (∀x:A. (∀y:A. R₀(y, x) ⇒ P(y)) ⇒ P(x)) ⇒ ∀x:A. P(x)")),
							notP)),
					),
				),
			)
		}),
})}

// Accessibility — both directions spend Induction, the reading of wellfounded
// this chapter's arguments run on, against one face of the accessible
// predicate. Forwards, the licence to induct along R, read at
// accessibility itself, leaves only the demand that accessibility be
// closed under passing to a predecessor — which is the introduction
// rule. Backwards, rule induction along accessibility carries a
// relation-closed property to every accessible point; every point being
// accessible, that is the induction licence, and Induction reads
// well-foundedness back off it.
var Accessibility = accessibilityThm{family.Add(registry.ProofEntry{
	Name: "Accessibility",
	Key:  "prop_9062ec517177c008",
	Build: family.Theorem("∀R:(A → A → bool). wellfounded(R) ⇔ ∀x:A. accessible(R, x)",
		func(a *Argument, R *Arrow2[A, A, Bool]) {
			a.Iff()
			a.Forward(
				"a well-founded relation makes every point accessible",
				func(b *Argument, wellFounded Fact) {
					licence := b.Have(
						"well-foundedness is the licence to induct along R",
						"∀P:(A → bool). (∀x:A. (∀y:A. R(y, x) ⇒ P(y)) ⇒ P(x)) ⇒ ∀x:A. P(x)",
						By(wellFounded, Induction))
					b.Show(
						"induct at accessibility itself: the induction step it asks for is the introduction rule",
						By(licence.At(b.Term("λx:A. accessible(R, x)")), AccessibleRules))
				})
			a.Backward(
				"a relation whose every point is accessible is well-founded",
				func(b *Argument, everyPointAccessible Fact) {
					licence := b.Have(
						"a property closed under R's predecessors reaches every "+
							"ACCESSIBLE point, by rule induction along accessibility",
						"∀P:(A → bool). (∀x:A. (∀y:A. R(y, x) ⇒ P(y)) ⇒ P(x)) ⇒ ∀x:A. accessible(R, x) ⇒ P(x)",
						By(AccessibleInduct))
					b.Show(
						"and every point is accessible, so that licence is "+
							"unconditional — which is what well-foundedness says",
						By(licence, everyPointAccessible, Induction))
				})
		}),
})}

// InverseImage — well-foundedness pulls back along any map: if R is
// well-founded on the target, so is the relation m induces on the
// source. Reading both WFs through Induction, the argument is one
// change of variable: to establish P everywhere on the source, induct
// over the target on "every point mapping here satisfies P" — the
// pullback relation's induction step is exactly that predicate's
// inductive step.
var InverseImage = inverseImageThm{family.Add(registry.ProofEntry{
	Name: "InverseImage",
	Key:  "prop_c57d7dd120310fb4",
	Build: family.Theorem(Statement{
		Binders: "∀R:(B → B → bool). ∀m:(A → B).",
		Hypotheses: []string{
			"wellfounded(R)",
		},
		Conclusion: "wellfounded(λx:A. λy:A. R(m(x), m(y)))",
	},
		func(a *Argument, R *Arrow2[B, B, Bool], m *Arrow[A, B], wf Fact) {
			// Trade wellfounded of the pullback for its induction reading over the
			// source: Induction as a rewrite rule, read as its entry states
			// it. The residual is worked in, not closed.
			a.Do(Simp(Fwd(Induction.Inst[A]())))
			a.Fix()            // P — the property to establish everywhere on the source
			step := a.Assume() // P's induction step along the pullback
			rInd := a.Have(
				"R licenses induction over its own type",
				"∀Q:(B → bool). (∀x:B. (∀y:B. R(y, x) ⇒ Q(y)) ⇒ Q(x)) ⇒ ∀x:B. Q(x)",
				By(wf, Induction.Inst[B]()))
			a.Show(
				"induct over B on \"everything mapping to b satisfies "+
					"P\": its inductive step is exactly the pullback's",
				By(step, rInd.At(a.Term("λb:B. ∀x:A. m(x) = b ⇒ P(x)"))))
		}),
})}

// Subrelation — well-foundedness is inherited downwards: a relation
// contained in a well-founded one is itself well-founded. This is the
// chapter's transport along a containment, and like its transport
// along a map it spends Induction on both sides: a property closed
// under R's predecessors is closed under S's, every R-predecessor
// being an S-predecessor, so S's licence to induct passes to R — and
// holding that licence is what R's well-foundedness says.
var Subrelation = subrelationThm{family.Add(registry.ProofEntry{
	Name: "Subrelation",
	Key:  "prop_c9b3d0d3f9a64aa4",
	Build: family.Theorem(Statement{
		Binders: "∀R S:(A → A → bool).",
		Hypotheses: []string{
			"∀x y:A. R(x, y) ⇒ S(x, y)",
			"wellfounded(S)",
		},
		Conclusion: "wellfounded(R)",
	},
		func(a *Argument, R, S *Arrow2[A, A, Bool], containedInWellFounded Fact) {
			licence := a.Have(
				"well-foundedness is the licence to induct along S",
				"∀P:(A → bool). (∀x:A. (∀y:A. S(y, x) ⇒ P(y)) ⇒ P(x)) ⇒ ∀x:A. P(x)",
				By(containedInWellFounded, Induction))
			transported := a.Have(
				"R licenses induction too: a property closed under R's predecessors "+
					"is closed under S's, every R-predecessor being an S-predecessor",
				"∀P:(A → bool). (∀x:A. (∀y:A. R(y, x) ⇒ P(y)) ⇒ P(x)) ⇒ ∀x:A. P(x)",
				By(licence, containedInWellFounded))
			a.Show(
				"and holding that licence is what R's well-foundedness says",
				By(transported, Induction))
		}),
})}

// TransitiveClosureWellFounded — taking the transitive closure neither
// creates nor destroys well-foundedness, and the two directions run
// along the chapter's two readings of the notion. Downwards it is
// containment: a single step of R is a step of its closure, so the
// closure's well-foundedness is inherited.
//
// Upwards the argument is about accessibility. Take a point all of
// whose R-predecessors are accessible along both relations, and let
// some point reach it in the closure. That stretch either is a single
// R-step, and the hypothesis speaks of its source; or it makes a last
// move out of a point the closure already reaches — a point the
// hypothesis makes accessible along the closure, from which
// accessibility travels back down the stretch. So every
// closure-predecessor is accessible and the introduction rule places
// the point itself. Strong rule induction along accessibility then
// carries "accessible along the closure" to every point R makes
// accessible — which, R being well-founded, is every point.
//
// The minimal-element reading proves the same direction, applying R's
// minimality to the points the closure reaches from a predicate; it
// costs an unfolding of wellfounded, which no other member of the chapter does,
// and argues about a minimal point where this argument argues about
// the relation.
var TransitiveClosureWellFounded = transitiveClosureWellFoundedThm{family.Add(registry.ProofEntry{
	Name: "TransitiveClosureWellFounded",
	Key:  "prop_cd83a7fa8f87d123",
	Build: family.Theorem("∀R:(A → A → bool). wellfounded(transitive_closure(R)) ⇔ wellfounded(R)",
		func(a *Argument, R *Arrow2[A, A, Bool]) {
			a.Iff()

			a.Forward(
				"the closure's well-foundedness is inherited by R, which it contains",
				func(b *Argument, closureWellFounded Fact) {
					b.Show(
						"a step of R is a step of its closure, and well-foundedness passes down a containment",
						By(closureWellFounded, closure.TransitiveClosureRules.At(R), Subrelation))
				})

			a.Backward(
				"a well-founded relation makes every point accessible along its closure as well",
				func(b *Argument, wellFounded Fact) {
					closureRelation := b.TermAs[Fun2[A, A, Bool]]("transitive_closure(R)")
					accessibleInClosure := b.TermAs[Fun[A, Bool]]("λu:A. accessible(transitive_closure(R), u)")

					everyPointAccessible := b.Have(
						"well-foundedness is accessibility at every point",
						"∀x:A. accessible(R, x)",
						By(wellFounded, Accessibility))

					step := b.Have(
						"a point whose R-predecessors are accessible along both relations is accessible along the closure",
						Statement{
							Binders: "∀x:A.",
							Hypotheses: []string{
								"∀y:A. R(y, x) ⇒ accessible(R, y) ∧ accessible(transitive_closure(R), y)",
							},
							Conclusion: "accessible(transitive_closure(R), x)",
						},
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							predecessors := c.Assume()

							reaching := c.Have(
								"every point that reaches x in the closure is accessible along it",
								"∀z:A. transitive_closure(R, z, x) ⇒ accessible(transitive_closure(R), z)",
								Derive(func(d *Argument) {
									z := d.FixAs[A]("z")
									reaches := d.Assume()

									lastMove := d.Have(
										"the stretch from z to x is a single R-step, or makes "+
											"its last move out of a point the closure reaches",
										"R(z, x) ∨ (∃y:A. transitive_closure(R, z, y) ∧ R(y, x))",
										By(reaches, At(closure.CasesLeft, R, z, x)))

									d.Do(lastMove.SplitDisj(
										LeftHolds(
											"z is itself an R-predecessor of x",
											Given(func(e *Argument, direct Fact) {
												e.Show(
													"the hypothesis makes it accessible along the closure",
													By(direct, predecessors.At(z)))
											})),
										RightHolds(
											"the last move leaves a point that z reaches in the closure",
											Given(func(e *Argument, throughPoint Fact) {
												w, legs := e.UnpackAs[A](throughPoint) // the point the last move leaves
												// The unpacked point carries no phantom, so the typed
												// cite is told its type; the untyped one beside it reads
												// the same witness with no annotation.
												e.Show(
													"that point is an R-predecessor of x, hence accessible along the "+
														"closure, and accessibility travels back down the stretch to z",
													By(legs, predecessors.At(w), AccessibleCases.At(closureRelation, w)))
											})),
									))
								}))

							c.Show(
								"its closure-predecessors being accessible, the introduction rule places x",
								By(reaching, AccessibleRules.At(closureRelation, x)))
						}))

					carried := b.Have(
						"accessibility along R carries to the closure",
						"∀x:A. accessible(R, x) ⇒ accessible(transitive_closure(R), x)",
						By(step, At(AccessibleInductStrong, R, accessibleInClosure)))

					b.Show(
						"every point is accessible along the closure, which is the closure's well-foundedness",
						By(everyPointAccessible, carried, Accessibility))
				})
		}),
})}

// EmptyRelation — the empty relation is well-founded, vacuously. `⊥`
// relates no pair, so the minimality demand on a candidate point is
// empty, and wellfounded's defining condition degenerates to the tautology
// "P inhabited ⇒ P inhabited".
var EmptyRelation = emptyRelationThm{family.Add(registry.ProofEntry{
	Name: "EmptyRelation",
	Key:  "prop_c9ce51cbaa4fd3da",
	Build: family.Theorem(Statement{
		Conclusion: "«emptyRelationStatement»",
		Abbrev: Abbrev{
			{Name: "emptyRelationStatement", Text: "wellfounded(λx:A. λy:A. ⊥)"},
		},
	},
		func(a *Argument) {
			a.Show(
				"nothing is below anything, so a witness for P is already P-minimal",
				Unfold(WellfoundedDef))
		}),
})}

// NatLess — `<` on ℕ is well-founded: nat_order's course-of-values
// induction is exactly the induction reading of wellfounded at ℕ, so rewriting
// through the characterization leaves nothing but that theorem.
var NatLess = natLessThm{family.Add(registry.ProofEntry{
	Name: "NatLess",
	Key:  "prop_79633ec6b9502354",
	Build: family.Theorem(Statement{
		Conclusion: "wellfounded(<)",
	},
		func(a *Argument) {
			a.Do(
				Simp(Fwd(Induction.Inst[Nat]())),
				Cite(nat_order.StrongInduction),
			)
		}),
})}

// Measure — the relation a ℕ-valued measure induces is well-founded.
// measure_less(m) unfolds to the pullback of < along m, so InverseImage at
// the target ℕ, fed with NatLess, is the whole proof.
var Measure = measureThm{family.Add(registry.ProofEntry{
	Name:     "Measure",
	Key:      "prop_15eb228fd1e5a7d6",
	ServesAs: "wellfounded_measure_less",
	Build: family.Theorem("∀m:(A → num). wellfounded(measure_less(m))",
		func(a *Argument, m *Arrow[A, Nat]) {
			a.Do(Unfold(MeasureLessDef))
			a.Show(
				"the pullback of < along m is well-founded: InverseImage fed with NatLess",
				By(NatLess, InverseImage.At(ext.As[Fun2[Nat, Nat, Bool]](dsl.NatLtMeta.Term()), m)))
		}),
})}

// FinitePredecessors — a transitive irreflexive relation under which
// every point has only finitely many points below it is well-founded.
//
// Counting is what leaves no room for an infinite descent. Transitivity
// puts everything below x below whatever x is itself below, so passing
// down R can only shrink the set of points below; irreflexivity makes
// the shrinking strict, x belonging to the larger set and not to its
// own; and a proper subset of a finite set is counted strictly smaller.
// So the count of points below is a ℕ-valued measure that strictly
// drops along R.
//
// "Has fewer points below" is therefore < pulled back along that count,
// and so well-founded of its own accord. R refines it, which turns an
// induction step along R into an induction step along the count — and
// the induction the count licenses is the induction R was to be shown
// to license.
//
// The criterion is stated here because finiteness declines to speak of
// well-foundedness — the counting chapter proves descent below a finite
// set without the notion — so this chapter speaks about finiteness.
var FinitePredecessors = finitePredecessorsThm{family.Add(registry.ProofEntry{
	Name: "FinitePredecessors",
	Key:  "prop_d7cca17fbee21f7b",
	Build: family.Theorem(Statement{
		Binders: "∀R:(A → A → bool).",
		Hypotheses: []string{
			"∀x:A. ¬R(x, x)",
			"∀x y z:A. R(x, y) ∧ R(y, z) ⇒ R(x, z)",
			"∀x:A. finite({y:A | R(y, x)})",
		},
		Conclusion: "wellfounded(R)",
	},
		func(a *Argument, R *Arrow2[A, A, Bool], irreflexive, transitive, predecessorsFinite Fact) {
			// The measure the argument runs on: how many points lie below
			// a given one.
			count := a.Term("λu:A. card({z:A | R(z, u)})")

			refines := a.Have(
				"R refines the count: a point below another has strictly fewer points below it",
				"∀x y:A. R(x, y) ⇒ card({z:A | R(z, x)}) < card({z:A | R(z, y)})",
				Derive(func(b *Argument) {
					x := b.Fix()
					y := b.Fix()
					xBelowY := b.Assume()
					proper := b.Have(
						"the points below x lie properly inside those below y, x itself separating them",
						"{z:A | R(z, x)} ⊊ {z:A | R(z, y)}",
						BySets(irreflexive.At(x), transitive, xBelowY))
					b.Show(
						"and a proper subset of a finite set is counted strictly smaller",
						By(predecessorsFinite.At(y), proper, cardinality.CardPsubset))
				}))

			// Trading wellfounded for the induction reading leaves an induction to
			// run — and it will be run along the count, not along R. The
			// rule is Induction read as its entry states it.
			a.Do(Simp(Fwd(Induction.Inst[A]())))
			a.Fix()                  // P — the property to establish everywhere
			stepAlongR := a.Assume() // P's induction step along R

			// The relation the induction will actually run along.
			fewerBelow := a.TermAs[Fun2[A, A, Bool]](
				"λu:A. λv:A. card({z:A | R(z, u)}) < card({z:A | R(z, v)})")
			fewerIsWellFounded := a.Have(
				"having fewer points below is well-founded, being < pulled back along the count",
				"wellfounded(λu:A. λv:A. card({z:A | R(z, u)}) < card({z:A | R(z, v)}))",
				By(NatLess, Where(InverseImage, "m", count)))

			a.Show(
				"so induct along the count: refinement turns R's induction step into the count's",
				By(fewerIsWellFounded, refines, stepAlongR, Induction.At(fewerBelow)))
		}),
})}

// ProperSubsetBelow — a subset of a finite set cannot be shrunk
// forever: proper inclusion, confined below a finite set, is
// well-founded.
//
// This is the finite-predecessor criterion applied, and the relation
// meets its three demands. Proper inclusion is irreflexive and
// transitive of its own accord, and the guard — which names the larger
// of the two sets — obstructs neither: irreflexivity never asks for
// it, and transitivity's conclusion guards the same set its second
// link guards. What remains is the count. A set standing below t is
// properly inside t, and the guard puts t inside s, so it is one of
// s's subsets; those form a finite collection because s is finite, and
// a subcollection of a finite collection is finite.
var ProperSubsetBelow = properSubsetBelowThm{family.Add(registry.ProofEntry{
	Name: "ProperSubsetBelow",
	Key:  "prop_c4f18482843cb661",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "wellfounded(λt₁:set(A). λt₂:set(A). t₁ ⊊ t₂ ∧ t₂ ⊆ s)",
	},
		func(a *Argument, s *Arrow[A, Bool], finite Fact) {
			// The relation the criterion is read at: pass from a subset of
			// s to a proper subset of it.
			shrinking := a.Term("λt₁:set(A). λt₂:set(A). t₁ ⊊ t₂ ∧ t₂ ⊆ s")

			irreflexive := a.Have(
				"no set is properly inside itself, so the guard is never reached",
				"∀t:set(A). ¬(t ⊊ t ∧ t ⊆ s)",
				By(set_order.ProperSubsetIrrefl))

			transitive := a.Have(
				"proper inclusion composes, and the second link already guards the set the conclusion guards",
				"∀t₁ t₂ t₃:set(A). (t₁ ⊊ t₂ ∧ t₂ ⊆ s) ∧ (t₂ ⊊ t₃ ∧ t₃ ⊆ s) ⇒ t₁ ⊊ t₃ ∧ t₃ ⊆ s",
				By(set_order.ProperSubsetTrans))

			predecessorsFinite := a.Have(
				"below any t stand only finitely many sets",
				"∀t:set(A). finite({u:set(A) | u ⊊ t ∧ t ⊆ s})",
				Derive(func(b *Argument) {
					b.Fix()
					below := b.Term("{u:set(A) | u ⊊ t ∧ t ⊆ s}")
					subsetsOfS := b.Term("{v:set(A) | v ⊆ s}")

					powersetFinite := b.Have(
						"s being finite, its subsets form a finite collection",
						"finite({v:set(A) | v ⊆ s})",
						By(finite, finite_set.FinitePowerset))
					among := b.Have(
						"and every set below t is one of them: properly inside t, which the guard puts inside s",
						"{u:set(A) | u ⊊ t ∧ t ⊆ s} ⊆ {v:set(A) | v ⊆ s}",
						BySets())
					b.Show(
						"so they are finite in number, being a subcollection of a finite collection",
						By(At(finite_set.FiniteSubset, below, subsetsOfS), powersetFinite, among))
				}))

			a.Show(
				"irreflexive, transitive, and finite below each point — the finiteness criterion applies",
				By(At(FinitePredecessors, shrinking), irreflexive, transitive, predecessorsFinite))
		}),
})}

// Recursion — the well-founded recursion theorem: on a well-founded
// relation, a recursive description whose value at x depends only on
// values strictly below x pins down a function. The construction is
// the classical one, carried out on the recursion GRAPH — the least
// relation closed under "if f is already forced below x, then x is
// forced to H(f, x)". The two lemma sections are ∀G-generalized: for
// any closed and least G, every G-point is a rule value (inversion),
// and well-foundedness makes G total and single-valued (unique
// existence, by induction along R). The assembly then spells the
// graph impredicatively — as what every rule-closed predicate must
// contain — proves THAT G closed and least, instantiates both
// lemmas at it, and shows the function choosing each point's graph
// value satisfies the recursion equation.
//
// This is the invariant-carrying schema below read at the trivial
// invariant, and the chapter proves the two in that order rather than
// the other way round: the graph construction is what needs writing
// out, and once it is written the general form follows by guarding a
// description with its invariant, which is a reduction and not a
// second construction.
var Recursion = recursionThm{family.Add(registry.ProofEntry{
	Name:     "Recursion",
	Key:      "prop_ea4e014b1671032e",
	ServesAs: "wellfounded_recursion",
	Build: family.Sections(Statement{
		Binders: "∀H:((A → B) → A → B). ∀R:(A → A → bool).",
		Hypotheses: []string{
			"wellfounded(R)",
			"∀f g:(A → B). ∀x:A. (∀z:A. R(z, x) ⇒ f(z) = g(z)) ⇒ H(f, x) = H(g, x)",
		},
		Conclusion: "∃f:(A → B). ∀x:A. f(x) = H(f, x)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// The variables the Go-built terms and the texts spell: the
			// Skolems the strips mint (H₀ and R₀ are every section's ∀H ∀R)
			// and the binders of the built λs.
			vG_0 := ctx.Var("G_0", MakeFun(MakeVarType("A"), MakeFun(MakeVarType("B"), TypeBool)))
			vH := ctx.Var(
				"H_0",
				MakeFun(MakeFun(MakeVarType("A"), MakeVarType("B")), MakeFun(MakeVarType("A"), MakeVarType("B"))))
			vQ := ctx.Var("Q", MakeFun(MakeVarType("A"), MakeFun(MakeVarType("B"), TypeBool)))
			vR := ctx.Var("R_0", MakeFun(MakeVarType("A"), MakeFun(MakeVarType("A"), TypeBool)))
			vS := ctx.Var("S", MakeFun(MakeVarType("A"), MakeFun(MakeVarType("B"), TypeBool)))
			va := ctx.Var("a", MakeVarType("A"))
			vb := ctx.Var("b", MakeVarType("B"))
			vf := ctx.Var("f", MakeFun(MakeVarType("A"), MakeVarType("B")))
			vfʹ := ctx.Var("fʹ", MakeFun(MakeVarType("A"), MakeVarType("B")))
			vx := ctx.Var("x", MakeVarType("A"))
			vx_0 := ctx.Var("x_0", MakeVarType("A"))
			vxʹ := ctx.Var("xʹ", MakeVarType("A"))
			vy := ctx.Var("y", MakeVarType("B"))
			vy_1 := ctx.Var("y_1", MakeVarType("B"))
			vy_2 := ctx.Var("y_2", MakeVarType("B"))
			vyᐸBᐳ := ctx.Var("yᐸBᐳ", MakeVarType("B"))
			vz := ctx.Var("z", MakeVarType("A"))
			vz_0 := ctx.Var("z_0", MakeVarType("A"))
			vzʹ := ctx.Var("zʹ", MakeVarType("A"))
			ctx.Var("f_0", MakeFun(MakeVarType("A"), MakeVarType("B")))
			ctx.Var("y_0", MakeVarType("B"))
			ctx.Var("Q_0", MakeFun(MakeVarType("A"), MakeFun(MakeVarType("B"), TypeBool)))
			ctx.Var("α_0", MakeFun(MakeFun(MakeVarType("A"), MakeFun(MakeVarType("B"), TypeBool)), TypeBool))
			ctx.Var("α_1", MakeVarType("B"))
			// The rule-closure predicate-transformer — the subterm every
			// α₀ abbreviation in the assembly texts names.
			clo := vQ.To(ForAll(
				vf,
				vx)(ForAll(vz)(vR.Apply(vz, vx).Imply(vQ.Apply(vz, vf.Apply(vz)))).Imply(
				vQ.Apply(vx, vH.Apply(vf, vx)))))

			inversion := ctx.Lemma("∀H:((A → B) → A → B). ∀R:(A → A → bool). "+
				"    ∀G:(A → (B → bool)).((∀f:(A → B).∀x:A.((∀z:A.(R(z, x) ⇒ G(z, f(z)))) ⇒ G(x, H(f, x)))) ⇒ "+
				"        ((∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.( "+
				"                            (∀z:A.(R(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H(f, x)))) ⇒ "+
				"                    (∀x:A.∀y:B.(G(x, y) ⇒ Q(x, y))))) ⇒ "+
				"            (∀x:A.∀y:B.( "+
				"                    G(x, y) ⇒ (∃f:(A → B).((∀z:A.(R(z, x) ⇒ G(z, f(z)))) ∧ (y = H(f, x))))))))",
				func(arg *Argument, H, R Term) {
					arg.Do(StripQuant())
					arg.Do(StripImp())
					arg.Do(StripImp())
					arg.Do(AssertStep(ctx.MakePropText(
						"∀f:(A → B).∀x:A.((∀z:A.( "+
							"            R₀(z, x) ⇒ (∃g:(A → B).((∀w:A.(R₀(w, z) ⇒ G₀(w, g(w)))) ∧ (f(z) = H₀(g, z)))))) ⇒ "+
							"    (∃g:(A → B).((∀w:A.(R₀(w, x) ⇒ G₀(w, g(w)))) ∧ (H₀(f, x) = H₀(g, x)))))"),
						Case(
							"rule-values form a rule-closed predicate — the witness is f itself, in the graph by closedness",
							By(ResidentHyp(ctx.MakePropText(
								"∀f₀:(A → B).∀x₀:A.((∀z₀:A.(R₀(z₀, x₀) ⇒ G₀(z₀, f₀(z₀)))) ⇒ G₀(x₀, H₀(f₀, x₀)))"))),
						),
						Case(
							"leastness at the rule-value predicate — every graph point is a rule value",
							GroundHyp(
								ctx.MakePropText(
									"∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.((∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
										"    (∀x:A.∀y:B.(G₀(x, y) ⇒ Q(x, y))))"),
								vx.To(vy.To(Exists(vf)(
									ForAll(vz)(vR.Apply(vz, vx).Imply(vG_0.Apply(vz, vf.Apply(vz)))).And(vy.Eq(vH.Apply(vf, vx))))))),
							Basic(),
						),
					))

				})

			goalAfter := func() Action {
				return Chain(
					GroundHyp(
						ctx.MakePropText("∀P:(A → bool).((∀x:A.((∀z:A.(R₀(z, x) ⇒ P(z))) ⇒ P(x))) ⇒ (∀x:A.P(x)))"),
						vx.To(Exists(vyᐸBᐳ)(vG_0.Apply(vx, vyᐸBᐳ)).And(
							ForAll(vy_1, vy_2)(vG_0.Apply(vx, vy_1).Imply(vG_0.Apply(vx, vy_2).Imply(vy_1.Eq(vy_2))))))),
					AssertStep(ctx.MakePropText(
						"∀x:A.((∀z:A.(R₀(z, x) ⇒ "+
							"            ((∃y:B.G₀(z, y)) ∧ (∀y₁:B.∀y₂:B.(G₀(z, y₁) ⇒ (G₀(z, y₂) ⇒ (y₁ = y₂))))))) ⇒ "+
							"    ((∃y:B.G₀(x, y)) ∧ (∀y₁:B.∀y₂:B.(G₀(x, y₁) ⇒ (G₀(x, y₂) ⇒ (y₁ = y₂))))))"),
						Case(
							"existence and uniqueness of the graph value below x yield them at x",
							StripQuant(),
							StripImp(),
							SplitConj(
								Case(
									"existence — the ε-chooser of values below x steps through the rule to a value at x",
									By(
										ResidentHyp(ctx.MakePropText(
											"∀z₀:A.(R₀(z₀, x₀) ⇒ ((∃y:B.G₀(z₀, y)) ∧ (∀y₁:B.∀y₂:B.(G₀(z₀, y₁) ⇒ (G₀(z₀, y₂) ⇒ (y₁ = y₂))))))")),
										ResidentHyp(ctx.MakePropText(
											"∀f₀:(A → B).∀x₀:A.((∀z₀:A.(R₀(z₀, x₀) ⇒ G₀(z₀, f₀(z₀)))) ⇒ G₀(x₀, H₀(f₀, x₀)))"))),
								),
								Case(
									"uniqueness — invert y₁ and y₂; below x the decompositions agree, so continuity equates them",
									StripQuant(),
									StripImp(),
									StripImp(),
									Derive(func(a *Argument) {
										a.Have(
											"decompose y₁: some f forces it at x₀",
											ctx.MakePropText("∃f:(A → B).((∀z:A.(R₀(z, x₀) ⇒ G₀(z, f(z)))) ∧ (y₁ = H₀(f, x₀)))"),
											By(
												At(
													ResidentHyp(ctx.MakePropText(
														"∀x₀:A.∀y₀:B.( "+
															"    G₀(x₀, y₀) ⇒ (∃f:(A → B).((∀z₀:A.(R₀(z₀, x₀) ⇒ G₀(z₀, f(z₀)))) ∧ (y₀ = H₀(f, x₀)))))")),
													vx_0,
													vy_1),
												ResidentHyp(ctx.MakePropText("G₀(x₀, y₁)"))),
										)
										a.Have(
											"decompose y₂ the same way",
											ctx.MakePropText("∃f:(A → B).((∀z:A.(R₀(z, x₀) ⇒ G₀(z, f(z)))) ∧ (y₂ = H₀(f, x₀)))"),
											By(
												At(
													ResidentHyp(ctx.MakePropText(
														"∀x₀:A.∀y₀:B.( "+
															"    G₀(x₀, y₀) ⇒ (∃f:(A → B).((∀z₀:A.(R₀(z₀, x₀) ⇒ G₀(z₀, f(z₀)))) ∧ (y₀ = H₀(f, x₀)))))")),
													vx_0,
													vy_2),
												ResidentHyp(ctx.MakePropText("G₀(x₀, y₂)"))),
										)
										a.Show(
											"with both decompositions resident, continuity and the below-x uniqueness close y₁ = y₂",
											By(
												ResidentHyp(ctx.MakePropText(
													"∀z₀:A.(R₀(z₀, x₀) ⇒ ((∃y:B.G₀(z₀, y)) ∧ (∀y₁:B.∀y₂:B.(G₀(z₀, y₁) ⇒ (G₀(z₀, y₂) ⇒ (y₁ = y₂))))))")),
												ResidentHyp(ctx.MakePropText(
													"∀f:(A → B).∀g:(A → B).∀x:A.((∀z:A.(R₀(z, x) ⇒ (f(z) = g(z)))) ⇒ (H₀(f, x) = H₀(g, x)))")),
												ResidentHyp(ctx.MakePropText("∃f:(A → B).((∀z:A.(R₀(z, x₀) ⇒ G₀(z, f(z)))) ∧ (y₁ = H₀(f, x₀)))")),
												ResidentHyp(ctx.MakePropText("∃f:(A → B).((∀z:A.(R₀(z, x₀) ⇒ G₀(z, f(z)))) ∧ (y₂ = H₀(f, x₀)))"))),
										)
									}),
								),
							),
						),
						Case(
							"the principle, grounded at the compound, fires on the proved step",
							Basic(),
						),
					),
				)
			}

			uniqueExistence := ctx.Lemma("∀H:((A → B) → A → B). ∀R:(A → A → bool). "+
				"    wellfounded(R) ⇒ "+
				"    (∀f:(A → B).∀g:(A → B).∀x:A.((∀z:A.(R(z, x) ⇒ (f(z) = g(z)))) ⇒ (H(f, x) = H(g, x)))) ⇒ "+
				"    ∀G:(A → (B → bool)).((∀f:(A → B).∀x:A.((∀z:A.(R(z, x) ⇒ G(z, f(z)))) ⇒ G(x, H(f, x)))) ⇒ "+
				"        ((∀x:A.∀y:B.(G(x, y) ⇒ (∃f:(A → B).((∀z:A.(R(z, x) ⇒ G(z, f(z)))) ∧ (y = H(f, x)))))) ⇒ "+
				"            (∀x:A.((∃y:B.G(x, y)) ∧ (∀y₁:B.∀y₂:B.(G(x, y₁) ⇒ (G(x, y₂) ⇒ (y₁ = y₂))))))))",
				func(arg *Argument, H, R Term, wf, continuity Fact) {
					arg.Do(StripQuant())
					arg.Do(StripImp())
					arg.Do(StripImp())
					arg.Do(AssertStep(ctx.MakePropText(
						"∀P:(A → bool).((∀x:A.((∀z:A.(R₀(z, x) ⇒ P(z))) ⇒ P(x))) ⇒ (∀x:A.P(x)))"),
						Case(
							"wellfounded(R) is the licence to induct along R (Induction at A)",
							By(wf, Induction.Inst[A]()),
						),
						Case(
							"induction along R proves existence and uniqueness of the graph value at every point",
							goalAfter(),
						),
					))

				})

			// The headline: the graph, proved closed and least, instantiates
			// both lemmas, and the function choosing each point's graph value
			// satisfies the recursion equation.
			return ctx.Theorem(headline,
				func(arg *Argument, H, R Term, wf, continuity Fact) {
					arg.Do(Derive(func(a *Argument) {
						a.Have(
							"the graph — the intersection of all rule-closed predicates — is itself rule-closed",
							ctx.MakePropText(
								"∀f:(A → B).∀x:A.((∀z:A.(R₀(z, x) ⇒ "+
									"            (∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.( "+
									"                            (∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
									"                    Q(z, f(z)))))) ⇒ "+
									"    (∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.((∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
									"            Q(x, H₀(f, x)))))"),
							StripQuant(),
							StripImp(),
							StripQuant(),
							StripImp(),
							By(
								ResidentHyp(ctx.MakePropText(
									"∀z₀:A.(R₀(z₀, x₀) ⇒ "+
										"    (∀Q₀:(A → (B → bool)).((∀f₁:(A → B).∀x₁:A.( "+
										"                    (∀z₁:A.(R₀(z₁, x₁) ⇒ Q₀(z₁, f₁(z₁)))) ⇒ Q₀(x₁, H₀(f₁, x₁)))) ⇒ "+
										"            Q₀(z₀, f₀(z₀)))))")),
								ResidentHyp(ctx.MakePropText(
									"∀f₁:(A → B).∀x₁:A.((∀z₀:A.(R₀(z₀, x₁) ⇒ Q₀(z₀, f₁(z₀)))) ⇒ Q₀(x₁, H₀(f₁, x₁)))"))),
						)
						a.Have(
							"the graph is least: it implies every rule-closed predicate",
							ctx.MakePropText(
								"∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.((∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
									"    (∀x:A.∀y:B.((∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.( "+
									"                            (∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
									"                    Q(x, y))) ⇒ "+
									"            Q(x, y))))"),
							StripQuant(),
							StripImp(),
							StripQuant(),
							StripImp(),
							By(
								ResidentHyp(ctx.MakePropText(
									"∀Q₁:(A → (B → bool)).((∀f₀:(A → B).∀x₁:A.( "+
										"            (∀z₀:A.(R₀(z₀, x₁) ⇒ Q₁(z₀, f₀(z₀)))) ⇒ Q₁(x₁, H₀(f₀, x₁)))) ⇒ "+
										"    Q₁(x₀, y₀))")),
								ResidentHyp(ctx.MakePropText(
									"∀f₀:(A → B).∀x₀:A.((∀z₀:A.(R₀(z₀, x₀) ⇒ Q₀(z₀, f₀(z₀)))) ⇒ Q₀(x₀, H₀(f₀, x₀)))"))),
						)
						// Both cites ground the sibling section at (H₀, R₀) and the
						// graph predicate.
						a.Have(
							"inversion at the graph",
							ctx.MakePropText(
								"∀x:A.∀y:B.((∀Q:(A → (B → bool)).( "+
									"            (∀f:(A → B).∀x:A.((∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ Q(x, y))) ⇒ "+
									"    (∃f:(A → B).((∀z:A.(R₀(z, x) ⇒ "+
									"                    (∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.( "+
									"                                    (∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
									"                            Q(z, f(z)))))) ∧ "+
									"            (y = H₀(f, x)))))"),
							Cite(
								inversion,
								vH,
								vR,
								va.To(vb.To(ForAll(vQ)(ForAll(
									vf,
									vx)(ForAll(vz)(vR.Apply(vz, vx).Imply(vQ.Apply(vz, vf.Apply(vz)))).Imply(
									vQ.Apply(vx, vH.Apply(vf, vx)))).Imply(
									vQ.Apply(va, vb)))))),
							Basic(),
						)
						a.Have(
							"the graph is total and single-valued",
							ctx.MakePropText(
								"∀x:A.((∃y:B.∀Q:(A → (B → bool)).( "+
									"            (∀f:(A → B).∀x:A.((∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ Q(x, y))) ∧ "+
									"    (∀y₁:B.∀y₂:B.((∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.( "+
									"                            (∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
									"                    Q(x, y₁))) ⇒ "+
									"            ((∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.( "+
									"                                (∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
									"                        Q(x, y₂))) ⇒ "+
									"                (y₁ = y₂)))))"),
							Cite(
								uniqueExistence,
								vH,
								vR,
								va.To(vb.To(ForAll(vQ)(ForAll(
									vf,
									vx)(ForAll(vz)(vR.Apply(vz, vx).Imply(vQ.Apply(vz, vf.Apply(vz)))).Imply(
									vQ.Apply(vx, vH.Apply(vf, vx)))).Imply(
									vQ.Apply(va, vb)))))),
							Basic(),
						)
						a.Show(
							"the function choosing each point's graph value satisfies the recursion equation",
							Witness(va.To(vb.SuchThat(ForAll(vQ)(ForAll(
								vf,
								vx)(ForAll(vz)(vR.Apply(vz, vx).Imply(vQ.Apply(vz, vf.Apply(vz)))).Imply(
								vQ.Apply(vx, vH.Apply(vf, vx)))).Imply(
								vQ.Apply(va, vb)))))),
							StripQuant(),
							Derive(func(b *Argument) {
								b.Have(
									"pointwise, the chosen value is a graph value",
									ctx.MakePropText(
										"∀z:A.∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.((∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
											"    Q(z, "+
											"        εb:B.∀S:(A → (B → bool)).((∀fʹ:(A → B).∀xʹ:A.( "+
											"                    (∀zʹ:A.(R₀(zʹ, xʹ) ⇒ S(zʹ, fʹ(zʹ)))) ⇒ S(xʹ, H₀(fʹ, xʹ)))) ⇒ "+
											"            S(z, b))))"),
									AssertStep(ctx.MakePropText(
										"∀z:A.∃y:B.∀Q:(A → (B → bool)).( "+
											"    (∀f:(A → B).∀x:A.((∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ Q(z, y))"),
										Case(
											"totality gives a graph value at every z",
											StripQuant(),
											GroundHypKeep(
												ctx.MakePropText(
													"∀x:A.((∃y:B.∀Q:(A → (B → bool)).( "+
														"            (∀f:(A → B).∀x:A.((∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ Q(x, y))) ∧ "+
														"    (∀y₁:B.∀y₂:B.((∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.( "+
														"                            (∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
														"                    Q(x, y₁))) ⇒ "+
														"            ((∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.( "+
														"                                (∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
														"                        Q(x, y₂))) ⇒ "+
														"                (y₁ = y₂)))))"),
												vz_0),
											Basic(),
										),
										Case(
											"the ε of an inhabited graph column is in the graph",
											TrivialNormalized(),
										),
									),
								)
								b.Have(
									"H of the chooser is a graph value at x₀",
									ctx.MakePropText(
										"∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.((∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
											"    Q(x₀, "+
											"        H₀(λa:A.(εb:B.∀S:(A → (B → bool)).((∀fʹ:(A → B).∀xʹ:A.( "+
											"                            (∀zʹ:A.(R₀(zʹ, xʹ) ⇒ S(zʹ, fʹ(zʹ)))) ⇒ S(xʹ, H₀(fʹ, xʹ)))) ⇒ "+
											"                    S(a, b))), "+
											"            x₀)))"),
									GroundHypKeep(
										ctx.MakePropText(
											"∀f:(A → B).∀x:A.((∀z:A.(R₀(z, x) ⇒ "+
												"            (∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.( "+
												"                            (∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
												"                    Q(z, f(z)))))) ⇒ "+
												"    (∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.((∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
												"            Q(x, H₀(f, x)))))"),
										va.To(vb.SuchThat(ForAll(vQ)(ForAll(
											vf,
											vx)(ForAll(vz)(vR.Apply(vz, vx).Imply(vQ.Apply(vz, vf.Apply(vz)))).Imply(
											vQ.Apply(vx, vH.Apply(vf, vx)))).Imply(
											vQ.Apply(va, vb))))),
										vx_0),
									StripQuant(),
									StripImp(),
									Derive(func(c *Argument) {
										c.Have(
											"below x₀ the chooser's values are graph values",
											ctx.MakePropText(
												"∀z:A.(R₀(z, x₀) ⇒ "+
													"    (∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.((∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
													"            Q(z, "+
													"                εb:B.∀S:(A → (B → bool)).((∀fʹ:(A → B).∀xʹ:A.( "+
													"                            (∀zʹ:A.(R₀(zʹ, xʹ) ⇒ S(zʹ, fʹ(zʹ)))) ⇒ S(xʹ, H₀(fʹ, xʹ)))) ⇒ "+
													"                    S(z, b))))))"),
											StripQuant(),
											StripImp(),
											GroundHypKeep(
												ctx.MakePropText(
													"∀z:A.∀Q:(A → (B → bool)).((∀f:(A → B).∀x:A.((∀z:A.(R₀(z, x) ⇒ Q(z, f(z)))) ⇒ Q(x, H₀(f, x)))) ⇒ "+
														"    Q(z, "+
														"        εb:B.∀S:(A → (B → bool)).((∀fʹ:(A → B).∀xʹ:A.( "+
														"                    (∀zʹ:A.(R₀(zʹ, xʹ) ⇒ S(zʹ, fʹ(zʹ)))) ⇒ S(xʹ, H₀(fʹ, xʹ)))) ⇒ "+
														"            S(z, b))))"),
												vz_0),
											TrivialNormalized(),
										)
										c.Do(GroundHypKeep(
											ctx.MakePropText("∀f₀:(A → B).∀x₁:A.((∀z₀:A.(R₀(z₀, x₁) ⇒ Q₀(z₀, f₀(z₀)))) ⇒ Q₀(x₁, H₀(f₀, x₁)))"),
											va.To(vb.SuchThat(ForAll(vS)(ForAll(
												vfʹ,
												vxʹ)(ForAll(vzʹ)(vR.Apply(vzʹ, vxʹ).Imply(vS.Apply(vzʹ, vfʹ.Apply(vzʹ)))).Imply(
												vS.Apply(vxʹ, vH.Apply(vfʹ, vxʹ)))).Imply(
												vS.Apply(va, vb))))),
											vx_0))
										c.Have(
											"Q₀ — an arbitrary rule-closed predicate — holds of the chooser's values below x₀",
											ctx.MakePropText(
												"∀z:A.(R₀(z, x₀) ⇒ "+
													"    Q₀(z, "+
													"        (λa:A.(εb:B.∀S:(A → (B → bool)).((∀fʹ:(A → B).∀xʹ:A.( "+
													"                            (∀zʹ:A.(R₀(zʹ, xʹ) ⇒ S(zʹ, fʹ(zʹ)))) ⇒ S(xʹ, H₀(fʹ, xʹ)))) ⇒ "+
													"                    S(a, b))))(z)))"),
											StripQuant(),
											StripImp(),
											Expect(Basic(),
												Case(
													"first Basic residual: the ε at z₀ satisfies Q₀ — "+
														"the pointwise graph fact meets the ε-characterization",
													DenoteTerm("α_0", clo),
													HilbertDenote(),
													TrivialSimplify(),
													By(
														ResidentHyp(ctx.MakePropText(
															"∀z:A.∀Q:(A → (B → bool)).(α₀(Q) ⇒ Q(z, εb:B.∀S:(A → (B → bool)).(α₀(S) ⇒ S(z, b))))")),
														ResidentHyp(ctx.MakePropText("α₀(Q₀)")),
														ResidentHyp(ctx.MakePropText(
															"(∃b:B.∀S₀:(A → (B → bool)).(α₀(S₀) ⇒ S₀(z₀, b))) ⇒ "+
																"(∀S₀:(A → (B → bool)).(α₀(S₀) ⇒ S₀(z₀, α₁)))"))),
												),
												Case(
													"second Basic residual: the same discharge (Basic splits the leaf in two; both close identically)",
													DenoteTerm("α_0", clo),
													HilbertDenote(),
													TrivialSimplify(),
													By(
														ResidentHyp(ctx.MakePropText(
															"∀z:A.∀Q:(A → (B → bool)).(α₀(Q) ⇒ Q(z, εb:B.∀S:(A → (B → bool)).(α₀(S) ⇒ S(z, b))))")),
														ResidentHyp(ctx.MakePropText("α₀(Q₀)")),
														ResidentHyp(ctx.MakePropText(
															"(∃b:B.∀S₀:(A → (B → bool)).(α₀(S₀) ⇒ S₀(z₀, b))) ⇒ "+
																"(∀S₀:(A → (B → bool)).(α₀(S₀) ⇒ S₀(z₀, α₁)))"))),
												),
											),
										)
										c.Show(
											"the grounded step premise fires — Q₀ at H(chooser, x₀)",
											CondRewrite(),
											Basic(),
										)
									}),
								)
								b.Show(
									"at x₀ the chosen value and H(chooser, x₀) are both graph values; single-valuedness equates them",
									DenoteTerm("α_0", clo),
									HilbertDenote(),
									TrivialSimplify(),
									GroundHypKeep(
										ctx.MakePropText(
											"∀x:A.((∃y:B.∀Q:(A → (B → bool)).(α₀(Q) ⇒ Q(x, y))) ∧ "+
												"    (∀y₁:B.∀y₂:B.((∀Q:(A → (B → bool)).(α₀(Q) ⇒ Q(x, y₁))) ⇒ "+
												"            ((∀Q:(A → (B → bool)).(α₀(Q) ⇒ Q(x, y₂))) ⇒ (y₁ = y₂)))))"),
										vx_0),
									GroundHypKeep(
										ctx.MakePropText(
											"∀z:A.∀Q:(A → (B → bool)).(α₀(Q) ⇒ Q(z, εb:B.∀S:(A → (B → bool)).(α₀(S) ⇒ S(z, b))))"),
										vx_0),
									AssertStep(ctx.MakePropText(
										"∀y₁:B.∀y₂:B.((∀Q:(A → (B → bool)).(α₀(Q) ⇒ Q(x₀, y₁))) ⇒ "+
											"    ((∀Q:(A → (B → bool)).(α₀(Q) ⇒ Q(x₀, y₂))) ⇒ (y₁ = y₂)))"),
										Case(
											"single-valuedness at x₀, from the pointwise compound",
											By(ResidentHyp(ctx.MakePropText(
												"(∃y:B.∀Q:(A → (B → bool)).(α₀(Q) ⇒ Q(x₀, y))) ∧ "+
													"(∀y₁:B.∀y₂:B.((∀Q:(A → (B → bool)).(α₀(Q) ⇒ Q(x₀, y₁))) ⇒ "+
													"        ((∀Q:(A → (B → bool)).(α₀(Q) ⇒ Q(x₀, y₂))) ⇒ (y₁ = y₂))))"))),
										),
										Case(
											"single-valuedness at the two graph values is the recursion equation at x₀",
											GroundHyp(
												ctx.MakePropText(
													"∀y₁:B.∀y₂:B.((∀Q:(A → (B → bool)).(α₀(Q) ⇒ Q(x₀, y₁))) ⇒ "+
														"    ((∀Q:(A → (B → bool)).(α₀(Q) ⇒ Q(x₀, y₂))) ⇒ (y₁ = y₂)))"),
												vb.SuchThat(ForAll(vS)(ForAll(
													vfʹ,
													vxʹ)(ForAll(vzʹ)(vR.Apply(vzʹ, vxʹ).Imply(vS.Apply(vzʹ, vfʹ.Apply(vzʹ)))).Imply(
													vS.Apply(vxʹ, vH.Apply(vfʹ, vxʹ)))).Imply(
													vS.Apply(vx_0, vb)))),
												vH.Apply(
													va.To(vb.SuchThat(ForAll(vS)(ForAll(
														vfʹ,
														vxʹ)(ForAll(vzʹ)(vR.Apply(vzʹ, vxʹ).Imply(vS.Apply(vzʹ, vfʹ.Apply(vzʹ)))).Imply(
														vS.Apply(vxʹ, vH.Apply(vfʹ, vxʹ)))).Imply(
														vS.Apply(va, vb))))),
													vx_0)),
											Basic(),
											// The grounding above re-introduces LITERAL instances of the
											// already-abbreviated closure (inside the ε and H witnesses);
											// the search denote re-folds them under a fresh name — an
											// explicit DenoteTerm cannot reuse the resident α₀.
											proof.Denote(),
											HilbertDenote(),
											Basic(),
											CnfRefute(),
										),
									),
								)
							}),
						)
					}))

				})

		}),
})}

// RecursionUnique — the uniqueness half of well-founded recursion:
// two functions satisfying one admissible recursive description
// coincide. Recursion above produces such a function; this says there
// is no second one. The argument is a single induction along R on
// "the two functions agree here". The induction hypothesis at a point
// is agreement everywhere strictly below it — exactly what
// admissibility asks for before equating the two recursive values,
// which the recursion equations read back as the functions' own
// values. Agreeing at every point, the functions are equal.
var RecursionUnique = recursionUniqueThm{family.Add(registry.ProofEntry{
	Name: "RecursionUnique",
	Key:  "prop_5739f6ee11990aeb",
	Build: family.Theorem(Statement{
		Binders: "∀H:((A → B) → A → B). ∀R:(A → A → bool). ∀f g:(A → B).",
		Hypotheses: []string{
			"wellfounded(R)",
			"∀f' g':(A → B). ∀x:A. (∀z:A. R(z, x) ⇒ f'(z) = g'(z)) ⇒ H(f', x) = H(g', x)",
			"∀x:A. f(x) = H(f, x) ∧ ∀x:A. g(x) = H(g, x)",
		},
		Conclusion: "f = g",
	},
		func(
			a *Argument,
			H *Arrow2[Fun[A, B], A, B],
			R *Arrow2[A, A, Bool],
			f, g *Arrow[A, B],
			wf, admissible, recursionEquations Fact,
		) {
			induct := a.Have(
				"R licenses induction along itself",
				"∀P:(A → bool). (∀x:A. (∀y:A. R(y, x) ⇒ P(y)) ⇒ P(x)) ⇒ ∀x:A. P(x)",
				By(wf, Induction.Inst[A]()))
			agreeAt := a.Have(
				"agreement below x forces agreement at x — admissibility equates "+
					"the recursive values, the recursion equations read them back",
				"∀x:A. (∀y:A. R(y, x) ⇒ f(y) = g(y)) ⇒ f(x) = g(x)",
				By(admissible, recursionEquations))
			a.Show(
				"induct along R on \"f and g agree here\"; agreeing everywhere, they are equal",
				By(induct.At(a.Term("λx:A. f(x) = g(x)")), agreeAt))
		}),
})}

// NatRecursion — course-of-values recursion on ℕ: the recursion
// theorem read at ℕ's canonical well-founded relation. Since `<` is
// well-founded, the well-foundedness premise is discharged once and
// for all, and what a function defined by strong recursion on a
// natural has to supply is only the admissibility of its recursive
// description — that the value at n depends on the argument function
// below n alone.
var NatRecursion = natRecursionThm{family.Add(registry.ProofEntry{
	Name: "NatRecursion",
	Key:  "prop_e3e86067e2bbf2ce",
	Build: family.Theorem(Statement{
		Binders: "∀H:((num → B) → num → B).",
		Hypotheses: []string{
			"∀f g:(num → B). ∀n:num. (∀m:num. m < n ⇒ f(m) = g(m)) ⇒ H(f, n) = H(g, n)",
		},
		Conclusion: "∃f:(num → B). ∀n:num. f(n) = H(f, n)",
	},
		func(a *Argument, H *Arrow2[Fun[Nat, B], Nat, B], admissible Fact) {
			a.Show(
				"< is well-founded, so the recursion theorem applies at it",
				By(admissible, NatLess, Recursion.At(H, ext.As[Fun2[Nat, Nat, Bool]](dsl.NatLtMeta.Term()))))
		}),
})}

// RecursionInvariant — well-founded recursion carrying an invariant
// along. The recursive description need only be admissible on argument
// functions that already satisfy S strictly below the point, and in
// exchange the function it defines satisfies S everywhere: a definition
// and a property of the defined function come out of one induction
// instead of two. Recursion above is the case S ≡ ⊤, and is what the
// proof below runs on.
//
// The proof guards the description by the invariant: the guarded
// description agrees with H at a point whose argument function
// satisfies S below it, and elsewhere returns one fixed value carrying
// no information. Since the guard reads the argument below the point
// only, the guarded description is admissible in the plain sense —
// which H's own need not be — so Recursion gives it a fixed point.
// Induction along R then puts the invariant at every point of that
// fixed point: the induction hypothesis at x IS the guard, so there the
// fixed point takes the described value and the description hands S
// back with it. With the guard met everywhere the guarded fixed point
// is a fixed point of the description itself.
var RecursionInvariant = recursionInvariantThm{family.Add(registry.ProofEntry{
	Name: "RecursionInvariant",
	Key:  "prop_ddbf9bcdcaa35016",
	Build: family.Theorem(Statement{
		Binders: "∀H:((A → B) → A → B). ∀S:(A → B → bool). ∀R:(A → A → bool).",
		Hypotheses: []string{
			"wellfounded(R)",
			"∀f g:(A → B). ∀x:A. " +
				"    (∀z:A. R(z, x) ⇒ S(z, f(z)) ∧ f(z) = g(z)) ⇒ H(f, x) = H(g, x) ∧ S(x, H(f, x))",
		},
		Conclusion: "∃f:(A → B). ∀x:A. f(x) = H(f, x)",
	},
		func(a *Argument, H *Arrow2[Fun[A, B], A, B], S *Arrow2[A, B, Bool], R *Arrow2[A, A, Bool],
			wf Fact, admissible Fact) {
			guarded := a.TermAs[Fun2[Fun[A, B], A, B]](
				"λf:(A → B). λx:A. COND((∀z:A. R(z, x) ⇒ S(z, f(z))), H(f, x), (εb:B. ⊤))")

			guardedAdmissible := a.Have(
				"the guarded description reads its argument below x alone",
				Statement{
					Binders: "∀f g:(A → B). ∀x:A.",
					Hypotheses: []string{
						"∀z:A. R(z, x) ⇒ f(z) = g(z)",
					},
					Conclusion: "COND(∀z:A. R(z, x) ⇒ S(z, f(z)), H(f, x), εb:B. ⊤) = " +
						"COND(∀z:A. R(z, x) ⇒ S(z, g(z)), H(g, x), εb:B. ⊤)",
				},
				Derive(func(b *Argument) {
					b.Fix() // f
					b.Fix() // g
					b.Fix() // x
					agree := b.Assume()
					sameGuard := b.Have(
						"agreeing below x, f and g satisfy the invariant below x together",
						"(∀z:A. R(z, x) ⇒ S(z, f(z))) ⇔ (∀z:A. R(z, x) ⇒ S(z, g(z)))",
						By(agree))
					sameValue := b.Have(
						"under that guard the description's own hypothesis is met, so its two values agree",
						"(∀z:A. R(z, x) ⇒ S(z, f(z))) ⇒ H(f, x) = H(g, x)",
						By(agree, admissible))
					b.Show(
						"the guards agree, and where they hold so do the values they select",
						By(sameGuard, sameValue))
				}))

			guardedFix := a.Have(
				"the guarded description is plainly admissible, so it has a fixed point",
				"∃u:(A → B). ∀x:A. u(x) = COND((∀z:A. R(z, x) ⇒ S(z, u(z))), H(u, x), (εb:B. ⊤))",
				By(wf, guardedAdmissible, Recursion.At(guarded, R)))
			u, recEq := a.Unpack(guardedFix)

			step := a.Have(
				"where the invariant holds below x the guard is met, so u(x) is "+
					"the described value and the description returns it satisfying S",
				"∀x:A. (∀y:A. R(y, x) ⇒ S(y, u(y))) ⇒ S(x, u(x))",
				By(recEq, admissible))
			induct := a.Have(
				"R licenses induction along itself",
				"∀P:(A → bool). (∀x:A. (∀y:A. R(y, x) ⇒ P(y)) ⇒ P(x)) ⇒ ∀x:A. P(x)",
				By(wf, Induction.Inst[A]()))
			invariant := a.Have(
				"induct along R: the guarded fixed point satisfies the invariant everywhere",
				"∀x:A. S(x, u(x))",
				By(induct.At(a.Term("λx:A. S(x, u(x))")), step))

			a.Take(u)
			a.Show(
				"the guard now holds everywhere, so the guarded fixed "+
					"point is a fixed point of the description itself",
				By(Normalized, invariant, recEq))
		}),
})}

// RecursionExists — well-founded recursion for a description that does
// not compute. In place of a body returning the value at x stands a
// predicate saying which values are ACCEPTABLE there; provided
// acceptability at x reads the argument function below x alone, and
// provided an acceptable value exists at x whenever every value below
// x is acceptable, there is a function acceptable everywhere. It is
// the form a definition wants when the recursion leaves a choice open
// at each point.
//
// So make the choice: let the description return εy. Q(f, x, y), some
// value acceptable at x if any is. That description is admissible in
// the plain sense, because ε is a function of the predicate it
// chooses from and the congruence premise, read pointwise, says that
// functions agreeing below x leave one and the same predicate
// acceptable there. So the recursion theorem hands back a fixed point
// of the choice, and induction along R turns "an acceptable value
// exists" into "the chosen one is acceptable": below x the chosen
// values are acceptable by the induction hypothesis, which is what
// realizability asks for before it yields an acceptable value at x —
// and what ε takes from an inhabited predicate lies in it.
var RecursionExists = recursionExistsThm{family.Add(registry.ProofEntry{
	Name: "RecursionExists",
	Key:  "prop_84387db243e2dd92",
	Build: family.Theorem(Statement{
		Binders: "∀Q:((A → B) → A → B → bool). ∀R:(A → A → bool).",
		Hypotheses: []string{
			"wellfounded(R)",
			"∀f g:(A → B). ∀x:A. ∀y:B. (∀z:A. R(z, x) ⇒ f(z) = g(z)) ⇒ (Q(f, x, y) ⇔ Q(g, x, y))",
			"∀f:(A → B). ∀x:A. (∀z:A. R(z, x) ⇒ Q(f, z, f(z))) ⇒ ∃y:B. Q(f, x, y)",
		},
		Conclusion: "∃f:(A → B). ∀x:A. Q(f, x, f(x))",
	},
		func(a *Argument, Q Term, R *Arrow2[A, A, Bool], wf Fact, congruent Fact, realizable Fact) {
			chooser := a.TermAs[Fun2[Fun[A, B], A, B]]("λf:(A → B). λx:A. εy:B. Q(f, x, y)")

			chooserAdmissible := a.Have(
				"the chooser reads its argument below x alone",
				"∀f g:(A → B). ∀x:A. (∀z:A. R(z, x) ⇒ f(z) = g(z)) ⇒ (εy:B. Q(f, x, y)) = εy:B. Q(g, x, y)",
				Derive(func(b *Argument) {
					b.Fix() // f
					b.Fix() // g
					b.Fix() // x
					agree := b.Assume()
					samePredicate := b.Have(
						"agreeing below x, f and g leave the same values acceptable at x",
						"(λy:B. Q(f, x, y)) = λy:B. Q(g, x, y)",
						Funext(),
						By(agree, congruent))
					b.Show(
						"ε depends on the predicate alone, so it takes one value at both",
						By(Normalized, samePredicate))
				}))

			chosen := a.Have(
				"the chooser is plainly admissible, so it has a fixed point",
				"∃u:(A → B). ∀x:A. u(x) = εy:B. Q(u, x, y)",
				By(wf, chooserAdmissible, Recursion.At(chooser, R)))
			u, chosenAt := a.Unpack(chosen)

			step := a.Have(
				"acceptability below x buys an acceptable value at x, "+
					"and u(x) is ε of the predicate just shown inhabited",
				"∀x:A. (∀y:A. R(y, x) ⇒ Q(u, y, u(y))) ⇒ Q(u, x, u(x))",
				By(chosenAt, realizable))
			induct := a.Have(
				"R licenses induction along itself",
				"∀P:(A → bool). (∀x:A. (∀y:A. R(y, x) ⇒ P(y)) ⇒ P(x)) ⇒ ∀x:A. P(x)",
				By(wf, Induction.Inst[A]()))

			a.Take(u)
			a.Show(
				"induct along R: the fixed point of the chooser is acceptable everywhere",
				By(induct.At(a.Term("λx:A. Q(u, x, u(x))")), step))
		}),
})}
