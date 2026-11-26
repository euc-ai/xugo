// supremum.go — suprema and infima in ⟦0, ∞⟧: the order is complete, so
// every set has a least upper bound and a greatest lower bound.
//
// Three parts, marked by banners:
//
// - Completeness: the bounds exist, and what they are
// - Approximation
// - Suprema of sequences
//
// The supremum is a chosen least upper bound, and SupExists is what
// licenses the choice: a set with no finite upper bound has ∞ as its
// least one, and otherwise its finite values, with 0, are a bounded set
// of reals whose supremum embeds as the least upper bound. The infimum is
// the supremum of the lower bounds. Every later law reads the two
// through their bound properties alone.
//
// In the labels, tx is the finite value extended_to_real(x) of an
// extended value x, and ty, tz those of y and z.

package extended_nonneg_real

import (
	. "github.com/euc-ai/xugo/library/authoring"

	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Completeness: the bounds exist, and what they are
// ---------------------------------------------------------------------------

// ExtendedSupDef — the supremum of a set: a chosen least upper bound.
var ExtendedSupDef = extendedSupDefThm{family.Define(registry.DefEntry{
	Name:  "ExtendedSupDef",
	Key:   "prop_b9c82e82857d5a12",
	Const: "extended_sup",
	Type:  "set(extended_nonneg_real) → extended_nonneg_real",
	Equations: []string{"∀s:set(extended_nonneg_real). " +
		"    extended_sup(s) = " +
		"    εa:extended_nonneg_real. " +
		"        (∀x:extended_nonneg_real. x ∈ s ⇒ x ≤ a) ∧ " +
		"        ∀b:extended_nonneg_real. (∀x:extended_nonneg_real. x ∈ s ⇒ x ≤ b) ⇒ a ≤ b"},
	Deps: []registry.EntryLike{ExtendedLeDef},
})}

// ExtendedInfDef — the infimum of a set: a chosen greatest lower bound.
var ExtendedInfDef = extendedInfDefThm{family.Define(registry.DefEntry{
	Name:  "ExtendedInfDef",
	Key:   "prop_5cccfdbab43553bb",
	Const: "extended_inf",
	Type:  "set(extended_nonneg_real) → extended_nonneg_real",
	Equations: []string{"∀s:set(extended_nonneg_real). " +
		"    extended_inf(s) = " +
		"    εa:extended_nonneg_real. " +
		"        (∀x:extended_nonneg_real. x ∈ s ⇒ a ≤ x) ∧ " +
		"        ∀b:extended_nonneg_real. (∀x:extended_nonneg_real. x ∈ s ⇒ b ≤ x) ⇒ b ≤ a"},
	Deps: []registry.EntryLike{ExtendedLeDef},
})}

// SupExists — ⟦0, ∞⟧ is a complete lattice: every set has a least upper
// bound. A set with no finite upper bound has ∞ as its only upper bound.
// Otherwise its finite values, with 0, form a nonempty set of reals
// bounded by the value of a finite upper bound, and the image of their
// real supremum is the least upper bound: it lies above every point, and
// below every finite upper bound, whose value bounds those reals too.
var SupExists = supExistsThm{family.Add(registry.ProofEntry{
	Name: "SupExists",
	Key:  "prop_d41408f658453dd5",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(extended_nonneg_real).",
		Conclusion: "∃a:extended_nonneg_real. " +
			"    (∀x:extended_nonneg_real. x ∈ s ⇒ x ≤ a) ∧ " +
			"    (∀b:extended_nonneg_real. (∀x:extended_nonneg_real. x ∈ s ⇒ x ≤ b) ⇒ a ≤ b)",
		Abbrev: Abbrev{
			{Name: "values", Text: "{r:real | " +
				"    r = &0 ∨ ∃x:extended_nonneg_real. x ∈ s ∧ r = extended_to_real(x)}"},
		},
	}, func(a *Argument, s *Expr[Set[ExtendedNonnegReal]]) {
		a.Cases(
			a.Term("∃c:extended_nonneg_real. c ≠ extended_infinity ∧ (∀x:extended_nonneg_real. x ∈ s ⇒ x ≤ c)"))
		a.Otherwise(
			"s has no finite upper bound, so ∞ is its only one",
			func(b *Argument, unbounded Fact) {
				b.Take(b.TermAs[ExtendedNonnegReal]("extended_infinity"))
				b.Show(
					"∞ lies above everything, and an upper bound of s is ∞",
					By(unbounded, LeInfinity, LeRefl))
			})
		a.When(
			"s has a finite upper bound c: its finite values, with 0, are bounded reals",
			func(b *Argument, bounded Fact) {
				c, cBound := b.UnpackAs[ExtendedNonnegReal](bounded, "c")
				valuesBelow := b.Have(
					"a finite upper bound of s bounds «values» by its value",
					"∀d:extended_nonneg_real. "+
						"    d ≠ extended_infinity ∧ (∀x:extended_nonneg_real. x ∈ s ⇒ x ≤ d) ⇒ "+
						"    ∀r:real. r ∈ «values» ⇒ r ≤ extended_to_real(d)",
					By(ExtendedLeDef, ToRealNonneg))
				nonempty := b.Have(
					"0 lies in «values»",
					"«values» ≠ ∅",
					BySets())
				boundedValues := b.Have(
					"the value of c bounds «values»",
					"∃r₀:real. ∀r:real. r ∈ «values» ⇒ r ≤ r₀",
					Derive(func(d *Argument) {
						d.Take(d.TermAs[Real]("extended_to_real(c)"))
						d.Show(
							"c is a finite upper bound of s",
							By(cBound, valuesBelow.At(c)))
					}))
				supValues := b.Have(
					"so «values» has a real supremum",
					"(∀r:real. r ∈ «values» ⇒ r ≤ sup(«values»)) ∧ "+
						"(∀r₀:real. (∀r:real. r ∈ «values» ⇒ r ≤ r₀) ⇒ sup(«values») ≤ r₀)",
					By(nonempty, boundedValues, real_sup_inf.SupLeastUpperBound.At(b.TermAs[Set[Real]]("«values»"))))
				parts := b.Conjuncts(
					supValues,
					"the supremum bounds «values»",
					"and lies below every bound of it")
				above, least := parts[0], parts[1]
				supReal := b.TermAs[Real]("sup(«values»)")
				b.Take(b.TermAs[ExtendedNonnegReal]("extended_of_real(sup(«values»))"))
				upper := b.Have(
					"every point of s lies below the image of the supremum",
					"∀x:extended_nonneg_real. x ∈ s ⇒ x ≤ extended_of_real(sup(«values»))",
					Derive(func(d *Argument) {
						x := d.FixAs[ExtendedNonnegReal]()
						inS := d.Assume()
						d.Show(
							"x is finite below c, and its value lies in «values», below the nonnegative supremum",
							By(
								inS,
								cBound,
								above.At(d.TermAs[Real]("extended_to_real(x)")),
								above.At(d.TermAs[Real]("&0")),
								ExtendedLeDef.At(x, c),
								OfRealToReal.At(x),
								OfRealLe.At(d.TermAs[Real]("extended_to_real(x)"), supReal)))
					}))
				leastUpper := b.Have(
					"and below every upper bound of s",
					Statement{
						Binders:    "∀d:extended_nonneg_real.",
						Hypotheses: []string{"∀x:extended_nonneg_real. x ∈ s ⇒ x ≤ d"},
						Conclusion: "extended_of_real(sup(«values»)) ≤ d",
					},
					Derive(func(d *Argument) {
						bound := d.FixAs[ExtendedNonnegReal]("d")
						boundsS := d.Assume()
						d.Cases(d.Term("d = extended_infinity"))
						d.When(
							"∞ lies above everything",
							func(e *Argument, atInfinity Fact) {
								e.Do(atInfinity.Rw())
								e.Show(
									"the image lies below ∞",
									Cite(LeInfinity))
							})
						d.Otherwise(
							"a finite d bounds «values» by its value, so the supremum lies below it",
							func(e *Argument, finite Fact) {
								value := e.TermAs[Real]("extended_to_real(d)")
								e.Show(
									"the image of the supremum lies below the image of the value of d, which is d",
									By(
										finite,
										boundsS,
										valuesBelow.At(bound),
										least.At(value),
										OfRealToReal.At(bound),
										ToRealNonneg.At(bound),
										OfRealLe.At(supReal, value)))
							})
					}))
				b.Show(
					"the image of the supremum is the least upper bound",
					By(upper, leastUpper))
			})
	}),
})}

// SupUpper — the supremum lies above every point of the set.
var SupUpper = supUpperThm{family.Add(registry.ProofEntry{
	Name: "SupUpper",
	Key:  "prop_f23ecc2155f343e1",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(extended_nonneg_real). ∀x:extended_nonneg_real.",
		Hypotheses: []string{"x ∈ s"},
		Conclusion: "x ≤ extended_sup(s)",
	}, func(a *Argument, s *Expr[Set[ExtendedNonnegReal]], x *Expr[ExtendedNonnegReal], inS Fact) {
		a.Do(Unfold(ExtendedSupDef))
		a.Show(
			"the chosen value is a least upper bound, one existing",
			By(inS, SupExists.At(s)))
	}),
})}

// SupLeast — the supremum lies below every upper bound of the set.
var SupLeast = supLeastThm{family.Add(registry.ProofEntry{
	Name: "SupLeast",
	Key:  "prop_1b936570efa6e201",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(extended_nonneg_real). ∀z:extended_nonneg_real.",
		Hypotheses: []string{"∀x:extended_nonneg_real. x ∈ s ⇒ x ≤ z"},
		Conclusion: "extended_sup(s) ≤ z",
	}, func(a *Argument, s *Expr[Set[ExtendedNonnegReal]], z *Expr[ExtendedNonnegReal], bound Fact) {
		a.Do(Unfold(ExtendedSupDef))
		a.Show(
			"the chosen value is a least upper bound, one existing",
			By(bound, SupExists.At(s)))
	}),
})}

// InfExists — every set has a greatest lower bound: the supremum of its
// lower bounds. Each point of the set bounds the lower bounds from
// above, so the supremum lies below it; and every lower bound is one of
// them, so it lies below the supremum.
var InfExists = infExistsThm{family.Add(registry.ProofEntry{
	Name: "InfExists",
	Key:  "prop_24e582a4e2da6429",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(extended_nonneg_real).",
		Conclusion: "∃a:extended_nonneg_real. " +
			"    (∀x:extended_nonneg_real. x ∈ s ⇒ a ≤ x) ∧ " +
			"    (∀b:extended_nonneg_real. (∀x:extended_nonneg_real. x ∈ s ⇒ b ≤ x) ⇒ b ≤ a)",
	}, func(a *Argument, s *Expr[Set[ExtendedNonnegReal]]) {
		a.Take(a.TermAs[ExtendedNonnegReal](
			"extended_sup({b:extended_nonneg_real | ∀x:extended_nonneg_real. x ∈ s ⇒ b ≤ x})"))
		a.Show(
			"the supremum of the lower bounds is one, and lies above each",
			By(SupUpper, SupLeast))
	}),
})}

// InfLower — the infimum lies below every point of the set.
var InfLower = infLowerThm{family.Add(registry.ProofEntry{
	Name: "InfLower",
	Key:  "prop_fc050d567189fef0",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(extended_nonneg_real). ∀x:extended_nonneg_real.",
		Hypotheses: []string{"x ∈ s"},
		Conclusion: "extended_inf(s) ≤ x",
	}, func(a *Argument, s *Expr[Set[ExtendedNonnegReal]], x *Expr[ExtendedNonnegReal], inS Fact) {
		a.Do(Unfold(ExtendedInfDef))
		a.Show(
			"the chosen value is a greatest lower bound, one existing",
			By(inS, InfExists.At(s)))
	}),
})}

// InfGreatest — the infimum lies above every lower bound of the set.
var InfGreatest = infGreatestThm{family.Add(registry.ProofEntry{
	Name: "InfGreatest",
	Key:  "prop_116783d5667b5f0f",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(extended_nonneg_real). ∀z:extended_nonneg_real.",
		Hypotheses: []string{"∀x:extended_nonneg_real. x ∈ s ⇒ z ≤ x"},
		Conclusion: "z ≤ extended_inf(s)",
	}, func(a *Argument, s *Expr[Set[ExtendedNonnegReal]], z *Expr[ExtendedNonnegReal], bound Fact) {
		a.Do(Unfold(ExtendedInfDef))
		a.Show(
			"the chosen value is a greatest lower bound, one existing",
			By(bound, InfExists.At(s)))
	}),
})}

// SupEmpty — the empty set's supremum is 0: every value bounds the empty
// set, 0 among them.
var SupEmpty = supEmptyThm{family.Add(registry.ProofEntry{
	Name: "SupEmpty",
	Key:  "prop_8ff0338d07781be9",
	Build: family.Theorem("extended_sup(∅) = &0",
		func(a *Argument) {
			empty := a.TermAs[Set[ExtendedNonnegReal]]("∅")
			zero := a.TermAs[ExtendedNonnegReal]("&0")
			a.Show(
				"0 bounds ∅, so the supremum lies below 0, the least value",
				By(
					Normalized,
					SupLeast.At(empty, zero),
					ZeroLe.At(a.TermAs[ExtendedNonnegReal]("extended_sup(∅)")),
					LeAntisym,
					set_basic.NotInEmpty))
		}),
})}

// InfEmpty — the empty set's infimum is ∞: every value lies below the
// points of the empty set, ∞ among them.
var InfEmpty = infEmptyThm{family.Add(registry.ProofEntry{
	Name: "InfEmpty",
	Key:  "prop_e8e4c7298d39b5b3",
	Build: family.Theorem("extended_inf(∅) = extended_infinity",
		func(a *Argument) {
			empty := a.TermAs[Set[ExtendedNonnegReal]]("∅")
			infinity := a.TermAs[ExtendedNonnegReal]("extended_infinity")
			a.Show(
				"∞ is a lower bound of ∅, so the infimum lies above ∞, the greatest value",
				By(
					Normalized,
					InfGreatest.At(empty, infinity),
					LeInfinity.At(a.TermAs[ExtendedNonnegReal]("extended_inf(∅)")),
					LeAntisym,
					set_basic.NotInEmpty))
		}),
})}

// SupMono — a larger set has a larger supremum: the supremum of the
// larger set bounds the smaller one.
var SupMono = supMonoThm{family.Add(registry.ProofEntry{
	Name: "SupMono",
	Key:  "prop_7955d987bd3618bc",
	Build: family.Theorem(Statement{
		Binders:    "∀s t:set(extended_nonneg_real).",
		Hypotheses: []string{"s ⊆ t"},
		Conclusion: "extended_sup(s) ≤ extended_sup(t)",
	}, func(a *Argument, s, t *Expr[Set[ExtendedNonnegReal]], within Fact) {
		a.Show(
			"every point of s lies in t, below its supremum",
			By(
				within,
				SupLeast.At(s, a.TermAs[ExtendedNonnegReal]("extended_sup(t)")),
				At(SupUpper, t),
				set_basic.SubsetDef))
	}),
})}

// InfAntitone — a larger set has a smaller infimum: the infimum of the
// larger set is a lower bound of the smaller one.
var InfAntitone = infAntitoneThm{family.Add(registry.ProofEntry{
	Name: "InfAntitone",
	Key:  "prop_8ccfce605672e528",
	Build: family.Theorem(Statement{
		Binders:    "∀s t:set(extended_nonneg_real).",
		Hypotheses: []string{"s ⊆ t"},
		Conclusion: "extended_inf(t) ≤ extended_inf(s)",
	}, func(a *Argument, s, t *Expr[Set[ExtendedNonnegReal]], within Fact) {
		a.Show(
			"every point of s lies in t, above its infimum",
			By(
				within,
				InfGreatest.At(s, a.TermAs[ExtendedNonnegReal]("extended_inf(t)")),
				At(InfLower, t),
				set_basic.SubsetDef))
	}),
})}

// ---------------------------------------------------------------------------
// Approximation
// ---------------------------------------------------------------------------

// SupApprox — a value strictly below the supremum is strictly below a
// point of the set: were every point at most the value, so would be the
// supremum.
var SupApprox = supApproxThm{family.Add(registry.ProofEntry{
	Name: "SupApprox",
	Key:  "prop_61c00ff34b3bb7ed",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(extended_nonneg_real). ∀x:extended_nonneg_real.",
		Hypotheses: []string{"x < extended_sup(s)"},
		Conclusion: "∃y:extended_nonneg_real. y ∈ s ∧ x < y",
	}, func(a *Argument, s *Expr[Set[ExtendedNonnegReal]], x *Expr[ExtendedNonnegReal], below Fact) {
		a.Show(
			"otherwise x bounds s, and the supremum lies below x",
			By(below, SupLeast.At(s, x), LtIffNotLe))
	}),
})}

// InfApprox — a value strictly above the infimum is strictly above a
// point of the set: were every point at least the value, so would be the
// infimum.
var InfApprox = infApproxThm{family.Add(registry.ProofEntry{
	Name: "InfApprox",
	Key:  "prop_bd13320d59ca9d10",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(extended_nonneg_real). ∀x:extended_nonneg_real.",
		Hypotheses: []string{"extended_inf(s) < x"},
		Conclusion: "∃y:extended_nonneg_real. y ∈ s ∧ y < x",
	}, func(a *Argument, s *Expr[Set[ExtendedNonnegReal]], x *Expr[ExtendedNonnegReal], above Fact) {
		a.Show(
			"otherwise x is a lower bound of s, and the infimum lies above x",
			By(above, InfGreatest.At(s, x), LtIffNotLe))
	}),
})}

// SupScale — a factor c in ⟦0, ∞⟧ moves through the supremum of a set:
// c · sup(T) is the supremum of the c·x for x in T. Each c·x lies below
// c · sup(T). For the other bound: at c = 0, c · sup(T) is 0; at c = ∞,
// either sup(T) is 0, or some x in T lies above 0 and c·x is already ∞;
// at a real c = r > 0, each x in T is 1/r times r·x, so sup(T) lies below
// 1/r times the scaled supremum, and r times that is the scaled supremum.
// The empty set has supremum 0 on both sides.
var SupScale = supScaleThm{family.Add(registry.ProofEntry{
	Name: "SupScale",
	Key:  "prop_15d8414b51928fcb",
	Build: family.Theorem(Statement{
		Binders:    "∀c:extended_nonneg_real. ∀T:set(extended_nonneg_real).",
		Conclusion: "c * extended_sup(T) = extended_sup(image(λx:extended_nonneg_real. c * x, T))",
		Abbrev: Abbrev{
			{Name: "scaled", Text: "image(λx:extended_nonneg_real. c * x, T)"},
		},
	}, func(arg *Argument, c *Expr[ExtendedNonnegReal], T *Expr[Set[ExtendedNonnegReal]]) {
		scaled := arg.TermAs[Set[ExtendedNonnegReal]]("«scaled»")
		supT := arg.TermAs[ExtendedNonnegReal]("extended_sup(T)")
		supScaled := arg.TermAs[ExtendedNonnegReal]("extended_sup(«scaled»)")
		above := arg.Have(
			"each c·x lies below c · sup(T), and so does their supremum",
			"extended_sup(«scaled») ≤ c * extended_sup(T)",
			Derive(func(b *Argument) {
				each := b.Have(
					"a member c·x of the scaled set lies below c · sup(T), x lying below sup(T)",
					"∀y:extended_nonneg_real. y ∈ «scaled» ⇒ y ≤ c * extended_sup(T)",
					Derive(func(d *Argument) {
						d.FixAs[ExtendedNonnegReal]("y")
						x, parts := d.UnpackAs[ExtendedNonnegReal](
							d.Simplified(d.Assume(), Fwd(set_basic.InImage)), "x")
						d.Show(
							"multiplying by c keeps the order",
							By(Normalized, parts, SupUpper.At(T, x), MulLeMono.At(x, supT, c)))
					}))
				b.Show(
					"a bound of the scaled set bounds its supremum",
					By(each, SupLeast.At(scaled, b.TermAs[ExtendedNonnegReal]("c * extended_sup(T)"))))
			}))
		below := arg.Have(
			"c · sup(T) lies below the supremum of the c·x",
			"c * extended_sup(T) ≤ extended_sup(«scaled»)",
			Derive(func(b *Argument) {
				b.Cases(b.Term("c = &0"))
				b.When(
					"at c = 0, c · sup(T) is 0, the least value",
					func(d *Argument, zero Fact) {
						d.Show(
							"0 times anything is 0",
							By(zero, MulComm.At(c, supT), MulZero.At(supT), ZeroLe))
					})
				b.Otherwise(
					"c ≠ 0",
					func(d *Argument, nonzero Fact) {
						d.Cases(d.Term("c = extended_infinity"))
						d.When(
							"at c = ∞, either sup(T) is 0, or some x in T lies above 0 and c·x is ∞",
							func(e *Argument, infinite Fact) {
								e.Cases(e.Term("extended_sup(T) = &0"))
								e.When(
									"sup(T) = 0, so c · sup(T) is 0",
									func(g *Argument, flat Fact) {
										g.Show(
											"c times 0 is 0",
											By(flat, MulZero.At(c), ZeroLe))
									})
								e.Otherwise(
									"sup(T) lies above 0, so some member of T does",
									func(g *Argument, raised Fact) {
										zero := g.TermAs[ExtendedNonnegReal]("&0")
										_, witness := g.ObtainAs[ExtendedNonnegReal](
											"some x in T lies above 0",
											"∃x:extended_nonneg_real. x ∈ T ∧ &0 < x",
											By(
												Normalized,
												raised,
												ZeroLe.At(supT),
												LtIffNotLe.At(zero, supT),
												LeAntisym.At(supT, zero),
												SupApprox.At(T, zero)))
										reached := g.Have(
											"c·x is ∞, and it is a member of the scaled set",
											"extended_infinity ∈ «scaled»",
											By(witness, infinite, LtIffNotLe, LeRefl, MulInfinity, MulComm, set_basic.InImage))
										top := g.TermAs[ExtendedNonnegReal]("extended_infinity")
										g.Show(
											"so the scaled supremum is ∞, and everything lies below it",
											By(
												reached,
												SupUpper.At(scaled, top),
												LeInfinity.At(g.TermAs[ExtendedNonnegReal]("c * extended_sup(T)")),
												LeTrans))
									})
							})
						d.Otherwise(
							"a finite c ≠ 0 is a real r > 0, and each x in T is 1/r times r·x",
							func(e *Argument, finite Fact) {
								r, value := e.ObtainAs[Real](
									"c is a real r ≥ 0",
									"∃r:real. &0 ≤ r ∧ c = extended_of_real(r)",
									By(finite, ExtendedCases.At(c)))
								positive := e.Have(
									"r is not 0, as c is not",
									"r ≠ &0 ∧ &0 ≤ real_inv(r)",
									By(Normalized, nonzero, value, real_order_field.InvNonneg.At(r)))
								inverse := e.TermAs[ExtendedNonnegReal]("extended_of_real(real_inv(r))")
								one := e.TermAs[ExtendedNonnegReal]("&1")
								unit := e.Have(
									"1/r times c is 1",
									"extended_of_real(real_inv(r)) * c = &1",
									By(
										Normalized,
										positive,
										value,
										OfRealMul.At(e.TermAs[Real]("real_inv(r)"), r),
										real_construction.MulLeftInverse.At(r)))
								membersBelow := e.Have(
									"each x in T lies below 1/r times the scaled supremum",
									"∀x:extended_nonneg_real. x ∈ T ⇒ x ≤ extended_of_real(real_inv(r)) * extended_sup(«scaled»)",
									Derive(func(g *Argument) {
										x := g.FixAs[ExtendedNonnegReal]("x")
										member := g.Assume()
										term := g.TermAs[ExtendedNonnegReal]("c * x")
										inScaled := g.Have(
											"c·x is a member of the scaled set",
											"c * x ∈ «scaled»",
											By(member, set_basic.InImage))
										g.Show(
											"x is 1/r times c·x, which lies below the scaled supremum",
											By(
												unit,
												inScaled,
												SupUpper.At(scaled, term),
												MulLeMono.At(term, supScaled, inverse),
												MulAssoc.At(inverse, c, x),
												MulComm.At(one, x),
												MulOne.At(x)))
									}))
								bound := e.TermAs[ExtendedNonnegReal]("extended_of_real(real_inv(r)) * extended_sup(«scaled»)")
								e.Show(
									"so sup(T) lies below 1/r times the scaled supremum, and c times that is the scaled supremum",
									By(
										unit,
										membersBelow,
										SupLeast.At(T, bound),
										MulLeMono.At(supT, bound, c),
										MulAssoc.At(c, inverse, supScaled),
										MulComm.At(c, inverse),
										MulComm.At(one, supScaled),
										MulOne.At(supScaled)))
							})
					})
			}))
		arg.Show(
			"each side lies below the other",
			By(above, below, LeAntisym.At(arg.TermAs[ExtendedNonnegReal]("c * extended_sup(T)"), supScaled)))
	}),
})}

// ---------------------------------------------------------------------------
// Suprema of sequences
// ---------------------------------------------------------------------------

// SupSequenceUpper — every term of a sequence lies below the supremum of
// its values.
var SupSequenceUpper = supSequenceUpperThm{family.Add(registry.ProofEntry{
	Name: "SupSequenceUpper",
	Key:  "prop_557e9abf9ed8a662",
	Build: family.Theorem("∀a:(num → extended_nonneg_real). ∀n:num. a(n) ≤ extended_sup(image(a, 𝕌))",
		func(arg *Argument, a *Arrow[Nat, ExtendedNonnegReal], n *Expr[Nat]) {
			naturals := arg.TermAs[Set[Nat]]("𝕌")
			arg.Show(
				"a(n) is one of the values",
				By(
					SupUpper.At(arg.TermAs[Set[ExtendedNonnegReal]]("image(a, 𝕌)"), a.Apply(n)),
					set_image.FunInImage.At(a, naturals, n),
					set_basic.InUniv.At(n)))
		}),
})}

// SupSequenceLeast — a value above every term of a sequence lies above
// the supremum of its values.
var SupSequenceLeast = supSequenceLeastThm{family.Add(registry.ProofEntry{
	Name: "SupSequenceLeast",
	Key:  "prop_260ad143ce115fe2",
	Build: family.Theorem(Statement{
		Binders:    "∀a:(num → extended_nonneg_real). ∀z:extended_nonneg_real.",
		Hypotheses: []string{"∀n:num. a(n) ≤ z"},
		Conclusion: "extended_sup(image(a, 𝕌)) ≤ z",
	}, func(arg *Argument, a *Arrow[Nat, ExtendedNonnegReal], z *Expr[ExtendedNonnegReal], bound Fact) {
		arg.Show(
			"z bounds every value, the values being the terms",
			By(
				bound,
				SupLeast.At(arg.TermAs[Set[ExtendedNonnegReal]]("image(a, 𝕌)"), z),
				set_image.ForallInImage.At(
					a,
					arg.TermAs[Set[Nat]]("𝕌"),
					arg.TermAs[Set[ExtendedNonnegReal]]("λy:extended_nonneg_real. y ≤ z")),
				set_basic.InUniv))
	}),
})}

// IncreasingLe — a sequence that rises at each step rises across any
// stretch: the preorder interval law composes its adjacent comparisons.
var IncreasingLe = increasingLeThm{family.Add(registry.ProofEntry{
	Name: "IncreasingLe",
	Key:  "prop_c7009607cff2b84d",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → extended_nonneg_real). ∀m n:num.",
		Hypotheses: []string{
			"∀k:num. a(k) ≤ a(k + 1)",
			"m ≤ n",
		},
		Conclusion: "a(m) ≤ a(n)",
	}, func(arg *Argument, a *Arrow[Nat, ExtendedNonnegReal], m, n *Expr[Nat], adjacent, ordered Fact) {
		preorder := arg.Have(
			"the extended order is reflexive and transitive",
			"preorder(λx:extended_nonneg_real. λy:extended_nonneg_real. x ≤ y)",
			order.Preorder.Intro(
				Case(
					"each value is below itself",
					Unfold(equivalence.ReflexiveDef),
					Cite(LeRefl)),
				Case(
					"two comparisons compose",
					Unfold(equivalence.TransitiveDef),
					Cite(LeTrans))))
		arg.Show(
			"the adjacent steps compose across the interval from m to n",
			By(adjacent, ordered, order.MonotoneOnNatInterval.Read(preorder).At(a, m, n)))
	}),
})}

// SupAddLe — a bound on every x + y, x running over a nonempty set,
// bounds sup(s) + y. A finite bound z makes y finite and puts every x
// below the image of tz − ty, hence also the supremum; adding y back
// gives z.
var SupAddLe = supAddLeThm{family.Add(registry.ProofEntry{
	Name: "SupAddLe",
	Key:  "prop_de261fb960a0cf5c",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(extended_nonneg_real). ∀y z:extended_nonneg_real.",
		Hypotheses: []string{
			"s ≠ ∅",
			"∀x:extended_nonneg_real. x ∈ s ⇒ x + y ≤ z",
		},
		Conclusion: "extended_sup(s) + y ≤ z",
		Abbrev: Abbrev{
			{Name: "gap", Text: "extended_of_real(extended_to_real(z) - extended_to_real(y))"},
		},
	}, func(
		a *Argument,
		s *Expr[Set[ExtendedNonnegReal]],
		y, z *Expr[ExtendedNonnegReal],
		nonempty, bound Fact,
	) {
		a.Cases(a.Term("z = extended_infinity"))
		a.When(
			"∞ lies above everything",
			func(b *Argument, atInfinity Fact) {
				b.Do(atInfinity.Rw())
				b.Show(
					"sup(s) + y lies below ∞",
					Cite(LeInfinity))
			})
		a.Otherwise(
			"z is finite: every point of s lies below the image of tz − ty",
			func(b *Argument, finiteZ Fact) {
				p, pIn := b.ObtainAs[ExtendedNonnegReal](
					"s has a point p",
					"∃p:extended_nonneg_real. p ∈ s",
					By(nonempty, set_basic.MemberNotEmpty))
				pFinite := b.Have(
					"p + y lies below the finite z, so p and y are finite",
					"p ≠ extended_infinity ∧ y ≠ extended_infinity ∧ extended_to_real(p + y) ≤ extended_to_real(z)",
					By(
						finiteZ,
						pIn,
						bound.At(p),
						ExtendedLeDef.At(b.TermAs[ExtendedNonnegReal]("p + y"), z),
						AddEqInfinity.At(p, y)))
				yBelow := b.Have(
					"so y is finite with value at most that of z",
					"y ≠ extended_infinity ∧ extended_to_real(y) ≤ extended_to_real(z)",
					ByArith(pFinite, ToRealAdd.At(p, y), ToRealNonneg.At(p)))
				pointsBelow := b.Have(
					"every point x of s has tx + ty ≤ tz, so lies below «gap»",
					"∀x:extended_nonneg_real. x ∈ s ⇒ x ≤ «gap»",
					Derive(func(c *Argument) {
						x := c.FixAs[ExtendedNonnegReal]()
						xIn := c.Assume()
						xFinite := c.Have(
							"x + y lies below the finite z, so x is finite",
							"x ≠ extended_infinity ∧ extended_to_real(x + y) ≤ extended_to_real(z)",
							By(
								finiteZ,
								xIn,
								bound.At(x),
								ExtendedLeDef.At(c.TermAs[ExtendedNonnegReal]("x + y"), z),
								AddEqInfinity.At(x, y)))
						c.Show(
							"tx ≤ tz − ty, and x is the image of tx",
							ByArith(
								xFinite,
								yBelow,
								ToRealAdd.At(x, y),
								OfRealToReal.At(x),
								OfRealLe.At(
									c.TermAs[Real]("extended_to_real(x)"),
									c.TermAs[Real]("extended_to_real(z) - extended_to_real(y)"))))
					}))
				values := b.Have(
					"tz − ty is nonnegative, and adding ty to it gives tz",
					"&0 ≤ extended_to_real(z) - extended_to_real(y) ∧ "+
						"extended_to_real(z) - extended_to_real(y) + extended_to_real(y) = extended_to_real(z)",
					ByArith(yBelow))
				recombined := b.Have(
					"«gap» added to y is z",
					"«gap» + y = z",
					By(
						finiteZ,
						yBelow,
						values,
						OfRealAdd.At(
							b.TermAs[Real]("extended_to_real(z) - extended_to_real(y)"),
							b.TermAs[Real]("extended_to_real(y)")),
						OfRealToReal.At(y),
						OfRealToReal.At(z),
						ToRealNonneg.At(y)))
				gap := b.TermAs[ExtendedNonnegReal]("«gap»")
				b.Show(
					"the supremum lies below «gap», so sup(s) + y lies below «gap» + y = z",
					By(
						pointsBelow,
						recombined,
						SupLeast.At(s, gap),
						AddLeMono.At(b.TermAs[ExtendedNonnegReal]("extended_sup(s)"), gap, y)))
			})
	}),
})}

// SupSequenceAdd — for rising sequences the supremum of the sums is the
// sum of the suprema. Each sum of terms lies below the sum of the
// suprema; and any a(m) + b(k) lies below a(m + k) + b(m + k), so below
// the supremum of the sums, which SupAddLe lifts first to sup(a) + b(k)
// and then to sup(a) + sup(b).
var SupSequenceAdd = supSequenceAddThm{family.Add(registry.ProofEntry{
	Name: "SupSequenceAdd",
	Key:  "prop_33af67f825118475",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → extended_nonneg_real).",
		Hypotheses: []string{
			"∀n:num. a(n) ≤ a(n + 1)",
			"∀n:num. b(n) ≤ b(n + 1)",
		},
		Conclusion: "extended_sup(image(λn:num. a(n) + b(n), 𝕌)) = " +
			"extended_sup(image(a, 𝕌)) + extended_sup(image(b, 𝕌))",
		Abbrev: Abbrev{
			{Name: "supSum", Text: "extended_sup(image(λn:num. a(n) + b(n), 𝕌))"},
			{Name: "supA", Text: "extended_sup(image(a, 𝕌))"},
			{Name: "supB", Text: "extended_sup(image(b, 𝕌))"},
		},
	}, func(arg *Argument, a, b *Arrow[Nat, ExtendedNonnegReal], aRising, bRising Fact) {
		sums := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. a(n) + b(n)")
		supSum := arg.TermAs[ExtendedNonnegReal]("«supSum»")
		supA := arg.TermAs[ExtendedNonnegReal]("«supA»")
		supB := arg.TermAs[ExtendedNonnegReal]("«supB»")
		pairs := arg.Have(
			"a(m) + b(k) lies below the supremum of the sums, both sequences rising to index m + k",
			"∀m k:num. a(m) + b(k) ≤ «supSum»",
			Derive(func(c *Argument) {
				m := c.FixAs[Nat]()
				k := c.FixAs[Nat]()
				far := c.TermAs[Nat]("m + k")
				c.Show(
					"a(m) + b(k) lies below a(m + k) + b(m + k), a term of the sums",
					By(
						aRising,
						bRising,
						IncreasingLe.At(a, m, far),
						IncreasingLe.At(b, k, far),
						nat_order.LessEqAdd.At(m, k),
						nat_order.LessEqAddLeft.At(m, k),
						AddLeAdd.At(a.Apply(m), b.Apply(k), a.Apply(far), b.Apply(far)),
						SupSequenceUpper.At(sums, far),
						LeTrans.At(
							c.TermAs[ExtendedNonnegReal]("a(m) + b(k)"),
							c.TermAs[ExtendedNonnegReal]("a(m + k) + b(m + k)"),
							supSum)))
			}))
		nonemptyA := arg.Have(
			"a(0) is a value of a",
			"image(a, 𝕌) ≠ ∅",
			BySets())
		nonemptyB := arg.Have(
			"b(0) is a value of b",
			"image(b, 𝕌) ≠ ∅",
			BySets())
		addB := arg.Have(
			"sup(a) + b(k) lies below the supremum of the sums, for every k",
			"∀k:num. «supA» + b(k) ≤ «supSum»",
			Derive(func(c *Argument) {
				k := c.FixAs[Nat]()
				valuesA := c.Have(
					"each value of a, plus b(k), lies below the supremum of the sums",
					"∀x:extended_nonneg_real. x ∈ image(a, 𝕌) ⇒ x + b(k) ≤ «supSum»",
					By(pairs, set_basic.InImage))
				c.Show(
					"so sup(a) + b(k) does",
					By(
						nonemptyA,
						valuesA,
						SupAddLe.At(c.TermAs[Set[ExtendedNonnegReal]]("image(a, 𝕌)"), b.Apply(k), supSum)))
			}))
		valuesB := arg.Have(
			"each value of b, plus sup(a), lies below the supremum of the sums",
			"∀y:extended_nonneg_real. y ∈ image(b, 𝕌) ⇒ y + «supA» ≤ «supSum»",
			By(addB, set_basic.InImage, AddComm))
		below := arg.Have(
			"each sum of terms lies below the sum of the suprema",
			"«supSum» ≤ «supA» + «supB»",
			Derive(func(c *Argument) {
				termsBelow := c.Have(
					"a(n) + b(n) lies below sup(a) + sup(b)",
					"∀n:num. a(n) + b(n) ≤ «supA» + «supB»",
					Derive(func(d *Argument) {
						n := d.FixAs[Nat]()
						d.Show(
							"each term lies below its supremum",
							By(
								AddLeAdd.At(a.Apply(n), b.Apply(n), supA, supB),
								SupSequenceUpper.At(a, n),
								SupSequenceUpper.At(b, n)))
					}))
				c.Show(
					"so their supremum does",
					By(termsBelow, SupSequenceLeast.At(sums, c.TermAs[ExtendedNonnegReal]("«supA» + «supB»"))))
			}))
		arg.Show(
			"each side lies below the other",
			By(
				nonemptyB,
				valuesB,
				below,
				SupAddLe.At(arg.TermAs[Set[ExtendedNonnegReal]]("image(b, 𝕌)"), supA, supSum),
				AddComm.At(supB, supA),
				LeAntisym.At(supSum, arg.TermAs[ExtendedNonnegReal]("«supA» + «supB»"))))
	}),
})}

// SupSequenceScale — a nonnegative real factor moves through the
// supremum of a sequence. Each scaled term lies below c times the
// supremum; conversely, for c ≠ 0 each term is 1/c times its scaled self,
// so the supremum lies below 1/c times the scaled supremum, and c times
// that is the scaled supremum.
var SupSequenceScale = supSequenceScaleThm{family.Add(registry.ProofEntry{
	Name: "SupSequenceScale",
	Key:  "prop_473f3e319ceb7850",
	Build: family.Theorem(Statement{
		Binders:    "∀c:real. ∀a:(num → extended_nonneg_real).",
		Hypotheses: []string{"&0 ≤ c"},
		Conclusion: "extended_sup(image(λn:num. extended_of_real(c) * a(n), 𝕌)) = " +
			"extended_of_real(c) * extended_sup(image(a, 𝕌))",
		Abbrev: Abbrev{
			{Name: "supScaled", Text: "extended_sup(image(λn:num. extended_of_real(c) * a(n), 𝕌))"},
			{Name: "supA", Text: "extended_sup(image(a, 𝕌))"},
		},
	}, func(arg *Argument, c *Expr[Real], a *Arrow[Nat, ExtendedNonnegReal], nonneg Fact) {
		scaled := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_of_real(c) * a(n)")
		factor := arg.TermAs[ExtendedNonnegReal]("extended_of_real(c)")
		supScaled := arg.TermAs[ExtendedNonnegReal]("«supScaled»")
		supA := arg.TermAs[ExtendedNonnegReal]("«supA»")
		scaledBelow := arg.Have(
			"c · a(n) lies below c · sup(a), a(n) lying below sup(a)",
			"∀n:num. extended_of_real(c) * a(n) ≤ extended_of_real(c) * «supA»",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]()
				b.Show(
					"multiplying by c keeps the order",
					By(SupSequenceUpper.At(a, n), MulLeMono.At(a.Apply(n), supA, factor)))
			}))
		above := arg.Have(
			"so the supremum of the scaled terms lies below c · sup(a)",
			"«supScaled» ≤ extended_of_real(c) * «supA»",
			By(
				scaledBelow,
				SupSequenceLeast.At(scaled, arg.TermAs[ExtendedNonnegReal]("extended_of_real(c) * «supA»"))))
		below := arg.Have(
			"c · sup(a) lies below the supremum of the scaled terms",
			"extended_of_real(c) * «supA» ≤ «supScaled»",
			Derive(func(b *Argument) {
				b.Cases(b.Term("c = &0"))
				b.When(
					"c = 0: c · sup(a) is 0, the least value",
					func(d *Argument, zero Fact) {
						d.Do(zero.Rw())
						zeroFactor := d.TermAs[ExtendedNonnegReal]("&0")
						d.Show(
							"0 · sup(a) is 0",
							By(MulComm.At(zeroFactor, supA), MulZero.At(supA), ZeroLe))
					})
				b.Otherwise(
					"c ≠ 0: each term is 1/c times its scaled self",
					func(d *Argument, nonzero Fact) {
						inverse := d.TermAs[ExtendedNonnegReal]("extended_of_real(real_inv(c))")
						one := d.TermAs[ExtendedNonnegReal]("&1")
						unit := d.Have(
							"1/c times c is 1",
							"extended_of_real(real_inv(c)) * extended_of_real(c) = &1",
							By(
								Normalized,
								nonzero,
								nonneg,
								OfRealMul.At(d.TermAs[Real]("real_inv(c)"), c),
								real_order_field.InvNonneg.At(c),
								real_construction.MulLeftInverse.At(c)))
						termsBelow := d.Have(
							"each term lies below 1/c times the supremum of the scaled terms",
							"∀n:num. a(n) ≤ extended_of_real(real_inv(c)) * «supScaled»",
							Derive(func(e *Argument) {
								n := e.FixAs[Nat]()
								term := e.TermAs[ExtendedNonnegReal]("extended_of_real(c) * a(n)")
								e.Show(
									"a(n) is 1/c times c · a(n), which lies below the scaled supremum",
									By(
										unit,
										SupSequenceUpper.At(scaled, n),
										MulLeMono.At(term, supScaled, inverse),
										MulAssoc.At(inverse, factor, a.Apply(n)),
										MulComm.At(one, a.Apply(n)),
										MulOne.At(a.Apply(n))))
							}))
						bound := d.TermAs[ExtendedNonnegReal]("extended_of_real(real_inv(c)) * «supScaled»")
						d.Show(
							"so sup(a) lies below 1/c times the scaled supremum, and c times that is the scaled supremum",
							By(
								unit,
								termsBelow,
								SupSequenceLeast.At(a, bound),
								MulLeMono.At(supA, bound, factor),
								MulAssoc.At(factor, inverse, supScaled),
								MulComm.At(factor, inverse),
								MulComm.At(one, supScaled),
								MulOne.At(supScaled)))
					})
			}))
		arg.Show(
			"each side lies below the other",
			By(
				above,
				below,
				LeAntisym.At(supScaled, arg.TermAs[ExtendedNonnegReal]("extended_of_real(c) * «supA»"))))
	}),
})}

// SupSequenceScaleExtended — a factor c in ⟦0, ∞⟧, ∞ included, moves
// through the supremum of a sequence: the c·a(n) are the c·x for x among
// the a(n), so this is SupScale at the set of values of the sequence. No
// monotonicity is needed; at c = ∞ both sides are 0 exactly when every a(n)
// is 0, under 0 · ∞ = 0.
var SupSequenceScaleExtended = supSequenceScaleExtendedThm{family.Add(registry.ProofEntry{
	Name: "SupSequenceScaleExtended",
	Key:  "prop_d3fe92566c4f116b",
	Build: family.Theorem("∀c:extended_nonneg_real. ∀a:(num → extended_nonneg_real). "+
		"    c * extended_sup(image(a, 𝕌)) = extended_sup(image(λn:num. c * a(n), 𝕌))",
		func(arg *Argument, c *Expr[ExtendedNonnegReal], a *Arrow[Nat, ExtendedNonnegReal]) {
			values := arg.Have(
				"the c·a(n) are the c·x for x among the a(n)",
				"image(λx:extended_nonneg_real. c * x, image(a, 𝕌)) = image(λn:num. c * a(n), 𝕌)",
				BySets())
			arg.Show(
				"so the factor moves through the supremum of the values",
				By(values, SupScale.At(c, arg.TermAs[Set[ExtendedNonnegReal]]("image(a, 𝕌)"))))
		}),
})}

// SupSequenceSum — for finitely many rising sequences,
// the supremum of their sum is the sum of their suprema. By induction over
// the finite index set: a new index x brings one more rising sequence, the
// sums over the earlier indices rise as well, and the supremum of the sum of
// two rising sequences is the sum of their suprema.
var SupSequenceSum = supSequenceSumThm{family.Add(registry.ProofEntry{
	Name: "SupSequenceSum",
	Key:  "prop_8b702ccfa0064e9c",
	Build: family.Theorem(Statement{
		Binders: "∀a:(A → num → extended_nonneg_real). ∀k:set(A).",
		Hypotheses: []string{
			"finite(k)",
			"∀i:A. ∀n:num. i ∈ k ⇒ a(i)(n) ≤ a(i)(n + 1)",
		},
		Conclusion: "extended_sup(image(λn:num. Σ_{i∈k} a(i)(n), 𝕌)) = " +
			"Σ_{i∈k} extended_sup(image(a(i), 𝕌))",
	}, func(
		arg *Argument,
		a *Arrow2[A, Nat, ExtendedNonnegReal],
		k *Expr[Set[A]],
		finite, rising Fact,
	) {
		arg.Show(
			"the supremum splits over every finite index set of rising sequences, and k is one",
			ByInduction(finite_set.FiniteInductFresh, finite, Generalizing(rising),
				Case(
					"over ∅ every sum is 0, and so is the supremum of the zero sequence",
					Simp(Fwd(SumClauses)),
					By(
						SupSequenceLeast.At(
							arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. &0"),
							arg.TermAs[ExtendedNonnegReal]("&0")),
						LeRefl,
						ZeroLe,
						LeAntisym)),
				Case(
					"a new index x brings one more rising sequence, and the supremum of the two sums splits",
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						u := b.FixAs[Set[A]]("u")
						previous := b.Assume()
						onInsert := b.Assume()
						parts := b.Conjuncts(
							previous,
							"the supremum splits over u once its sequences rise",
							"x is not in u",
							"u is finite")
						ih, fresh, finiteU := parts[0], parts[1], parts[2]
						earlier := b.Have(
							"the sequences indexed by u rise, so the supremum splits over u",
							"extended_sup(image(λn:num. Σ_{i∈u} a(i)(n), 𝕌)) = Σ_{i∈u} extended_sup(image(a(i), 𝕌))",
							By(ih, onInsert, set_basic.InInsert))
						newRising := b.Have(
							"the sequence at x rises",
							"∀n:num. a(x)(n) ≤ a(x)(n + 1)",
							By(onInsert, set_basic.InInsert))
						restRising := b.Have(
							"and so do the sums over u",
							"∀n:num. Σ_{i∈u} a(i)(n) ≤ Σ_{i∈u} a(i)(n + 1)",
							Derive(func(c *Argument) {
								c.FixAs[Nat]("n")
								c.Show(
									"term by term",
									By(
										finiteU,
										onInsert,
										set_basic.InInsert,
										SumMono.At(
											c.TermAs[Fun[A, ExtendedNonnegReal]]("λi:A. a(i)(n)"),
											c.TermAs[Fun[A, ExtendedNonnegReal]]("λi:A. a(i)(n + 1)"),
											u)))
							}))
						peel := b.Have(
							"each sum over insert(x, u) is the term at x plus the sum over u",
							"∀n:num. Σ_{i∈insert(x, u)} a(i)(n) = a(x)(n) + Σ_{i∈u} a(i)(n)",
							By(fresh, finiteU, SumClauses))
						b.Do(Simp(Fwd(SumClauses), Fwd(peel)))
						b.Show(
							"the supremum of the sum of the two rising sequences is the sum of their suprema",
							By(
								newRising,
								restRising,
								earlier,
								SupSequenceAdd.At(
									b.TermAs[Fun[Nat, ExtendedNonnegReal]]("a(x)"),
									b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. Σ_{i∈u} a(i)(n)"))))
					}))))
	}),
})}

// InfSequenceGreatest — a value below every term of a
// sequence lies below the infimum of its values.
var InfSequenceGreatest = infSequenceGreatestThm{family.Add(registry.ProofEntry{
	Name: "InfSequenceGreatest",
	Key:  "prop_41f62315225aae07",
	Build: family.Theorem(Statement{
		Binders:    "∀a:(num → extended_nonneg_real). ∀z:extended_nonneg_real.",
		Hypotheses: []string{"∀n:num. z ≤ a(n)"},
		Conclusion: "z ≤ extended_inf(image(a, 𝕌))",
	}, func(arg *Argument, a *Arrow[Nat, ExtendedNonnegReal], z *Expr[ExtendedNonnegReal], bound Fact) {
		arg.Show(
			"z lies below every value, the values being the terms",
			By(
				bound,
				InfGreatest.At(arg.TermAs[Set[ExtendedNonnegReal]]("image(a, 𝕌)"), z),
				set_image.ForallInImage.At(
					a,
					arg.TermAs[Set[Nat]]("𝕌"),
					arg.TermAs[Set[ExtendedNonnegReal]]("λy:extended_nonneg_real. z ≤ y")),
				set_basic.InUniv))
	}),
})}

// SupSequenceOfReal — a rising sequence of nonnegative reals tends to l ≥ 0
// exactly when the image of l in ⟦0, ∞⟧ is the supremum of the images of its
// terms. A limit m lies above every term, so its image bounds the images;
// and where their supremum is finite, its value bounds every term, hence
// also m. Conversely, every term then lies below l, so the sequence, rising
// and bounded, converges to its real supremum, whose image is the supremum
// of the images too, so it is l.
var SupSequenceOfReal = supSequenceOfRealThm{family.Add(registry.ProofEntry{
	Name: "SupSequenceOfReal",
	Key:  "prop_6d690e5e6cbf96dd",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀l:real.",
		Hypotheses: []string{
			"∀n:num. &0 ≤ a(n)",
			"∀n:num. a(n) ≤ a(n + 1)",
			"&0 ≤ l",
		},
		Conclusion: "a ⟶ l ⇔ «supImages» = extended_of_real(l)",
		Abbrev: Abbrev{
			{Name: "supImages", Text: "extended_sup(image(λn:num. extended_of_real(a(n)), 𝕌))"},
		},
	}, func(arg *Argument, a *Arrow[Nat, Real], l *Expr[Real], nonneg, rising, lNonneg Fact) {
		images := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_of_real(a(n))")
		supImages := arg.TermAs[ExtendedNonnegReal]("«supImages»")
		value := arg.TermAs[Real]("extended_to_real(«supImages»)")
		zero := arg.TermAs[Nat]("0")
		limitSup := arg.Have(
			"a limit m of the sequence is nonnegative, and its image is the supremum of the images",
			"∀m:real. a ⟶ m ⇒ &0 ≤ m ∧ «supImages» = extended_of_real(m)",
			Derive(func(b *Argument) {
				m := b.FixAs[Real]("m")
				converges := b.Assume()
				mImage := b.TermAs[ExtendedNonnegReal]("extended_of_real(m)")
				below := b.Have(
					"every term lies below m, the terms rising to it",
					"∀n:num. a(n) ≤ m",
					Derive(func(c *Argument) {
						n := c.FixAs[Nat]("n")
						term := a.Apply(n)
						c.Show(
							"from n on the terms are at least a(n), and they tend to m",
							By(
								rising,
								converges,
								At(real_sequences.IncreasingLessEq, a),
								real_sequences.LimitConst.At(term),
								real_sequences.LimitLessEq.At(c.TermAs[Fun[Nat, Real]]("λk:num. a(n)"), a, term, m, n)))
					}))
				mNonneg := b.Have(
					"so m lies above the first term, which is nonnegative",
					"&0 ≤ m",
					ByArith(below.At(zero), nonneg.At(zero)))
				above := b.Have(
					"the image of m bounds the images of the terms, so their supremum",
					"«supImages» ≤ extended_of_real(m)",
					By(below, mNonneg, SupSequenceLeast.At(images, mImage), OfRealLe))
				reach := b.Have(
					"and the image of m lies below the supremum",
					"extended_of_real(m) ≤ «supImages»",
					Derive(func(c *Argument) {
						c.Cases(c.Term("«supImages» = extended_infinity"))
						c.When(
							"an infinite supremum lies above everything",
							func(d *Argument, infinite Fact) {
								d.Show(
									"the image of m lies below ∞",
									By(infinite, LeInfinity))
							})
						c.Otherwise(
							"a finite supremum has a value t, which bounds every term, hence their limit m",
							func(d *Argument, finite Fact) {
								termsBelow := d.Have(
									"every term lies below t, its image lying below the supremum, the image of t",
									"∀n:num. a(n) ≤ extended_to_real(«supImages»)",
									Derive(func(e *Argument) {
										n := e.FixAs[Nat]("n")
										e.Show(
											"t is nonnegative, so the embedding compares a(n) and t as reals",
											By(
												finite,
												SupSequenceUpper.At(images, n),
												OfRealToReal.At(supImages),
												ToRealNonneg.At(supImages),
												OfRealLe.At(a.Apply(n), value)))
									}))
								limitBound := d.Have(
									"so their limit m lies below t",
									"m ≤ extended_to_real(«supImages»)",
									By(
										termsBelow,
										converges,
										real_sequences.LimitConst.At(value),
										real_sequences.LimitLessEq.At(
											a,
											d.TermAs[Fun[Nat, Real]]("λn:num. extended_to_real(«supImages»)"),
											m,
											value,
											zero)))
								d.Show(
									"the image of m lies below the image of t, which is the supremum",
									By(
										finite,
										limitBound,
										OfRealToReal.At(supImages),
										ToRealNonneg.At(supImages),
										OfRealLe.At(m, value)))
							})
					}))
				b.Show(
					"each lies below the other",
					By(mNonneg, reach, above, LeAntisym.At(supImages, mImage)))
			}))
		arg.Iff()
		arg.Forward(
			"a limit's image is the supremum",
			func(b *Argument, converges Fact) {
				b.Show(
					"l is a limit",
					By(converges, limitSup.At(l)))
			})
		arg.Backward(
			"a sequence below l converges, to a limit whose image is the image of l",
			func(b *Argument, equal Fact) {
				bounded := b.Have(
					"every term lies below l, its image lying below the supremum, the image of l",
					"∀n:num. a(n) ≤ l",
					Derive(func(c *Argument) {
						n := c.FixAs[Nat]("n")
						c.Show(
							"l is nonnegative, so the embedding compares a(n) and l as reals",
							By(Normalized, equal, lNonneg, SupSequenceUpper.At(images, n), OfRealLe.At(a.Apply(n), l)))
					}))
				realSup := b.TermAs[Real]("sup(image(a, 𝕌))")
				converges := b.Have(
					"rising and bounded, the sequence converges to its real supremum",
					"a ⟶ sup(image(a, 𝕌))",
					By(bounded, rising, real_sequences.IncreasingBoundedConvergesToSup.At(a, l)))
				b.Show(
					"whose image is the supremum, the image of l, so it is l",
					By(Normalized, converges, limitSup.At(realSup), equal, lNonneg, OfRealInjective.At(realSup, l)))
			})
	}),
})}
