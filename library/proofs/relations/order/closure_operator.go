// closure_operator.go — closure operators on a partially ordered carrier.

package order

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ClosureOperatorOn — a closure operator preserves its partially ordered carrier, is extensive and monotone, and is idempotent.
var ClosureOperatorOn = closureOperatorOnThm{family.DefineStructure(registry.DefEntry{
	Name:    "ClosureOperatorOn",
	Key:     "prop_1da7b24c1432c225",
	Const:   "closure_operator_on",
	Subject: "c",
	Type:    "set(A) → (A → A → bool) → (A → A) → bool",
	Equations: []string{
		"∀c:set(A). ∀R:(A → A → bool). ∀cl:(A → A). " +
			"    closure_operator_on(c, R, cl) ⇔ " +
			"    partial_order_on(c, R) ∧ " +
			"    (∀x:A. x ∈ c ⇒ cl(x) ∈ c) ∧ " +
			"    (∀x:A. x ∈ c ⇒ R(x, cl(x))) ∧ " +
			"    (∀x y:A. x ∈ c ∧ y ∈ c ∧ R(x, y) ⇒ R(cl(x), cl(y))) ∧ " +
			"    (∀x:A. x ∈ c ⇒ cl(cl(x)) = cl(x))",
	},
	Deps: []registry.EntryLike{PartialOrderOn},
})}

// ClosureOperatorOnPartialOrder — the relation of a closure operator is a partial order on its carrier.
var ClosureOperatorOnPartialOrder = closureOperatorOnPartialOrderThm{family.Add(registry.ProofEntry{
	Name:  "ClosureOperatorOnPartialOrder",
	Key:   "prop_ea7cac67ba9c4a24",
	Build: ClosureOperatorOn.Axiom("partial_order_on(c, R)"),
})}

// ClosureOnIn — closure takes carrier points to carrier points.
var ClosureOnIn = closureOnInThm{family.Add(registry.ProofEntry{
	Name: "ClosureOnIn",
	Key:  "prop_180985af865c43b7",
	Build: ClosureOperatorOn.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ c",
		},
		Conclusion: "cl(x) ∈ c",
	}),
})}

// ClosureExtensive — a carrier point lies below its closure.
var ClosureExtensive = closureExtensiveThm{family.Add(registry.ProofEntry{
	Name: "ClosureExtensive",
	Key:  "prop_51681048b7a34c42",
	Build: ClosureOperatorOn.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ c",
		},
		Conclusion: "R(x, cl(x))",
	}),
})}

// ClosureMonotone — closure preserves the order between carrier points.
var ClosureMonotone = closureMonotoneThm{family.Add(registry.ProofEntry{
	Name: "ClosureMonotone",
	Key:  "prop_6d37e0fb6266494a",
	Build: ClosureOperatorOn.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ c",
			"y ∈ c",
			"R(x, y)",
		},
		Conclusion: "R(cl(x), cl(y))",
	}),
})}

// ClosureIdempotent — closing a carrier point twice has the same value as closing it once.
var ClosureIdempotent = closureIdempotentThm{family.Add(registry.ProofEntry{
	Name: "ClosureIdempotent",
	Key:  "prop_ad8f816c4024189f",
	Build: ClosureOperatorOn.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ c",
		},
		Conclusion: "cl(cl(x)) = cl(x)",
	}),
})}

// ClosureFromLeast — selecting the least point of F above each carrier point gives a closure operator:
// transitivity gives monotonicity, and leastness at a closed point gives idempotence.
var ClosureFromLeast = closureFromLeastThm{family.Add(registry.ProofEntry{
	Name: "ClosureFromLeast",
	Key:  "prop_bb6d98d253c2c68e",
	Build: family.Theorem(Statement{
		Binders: "∀R:(A → A → bool). ∀cl:(A → A). ∀c F:set(A).",
		Hypotheses: []string{
			"partial_order_on(c, R)",
			"F ⊆ c",
			"∀x:A. x ∈ c ⇒ cl(x) ∈ F ∧ R(x, cl(x)) ∧ (∀y:A. y ∈ F ∧ R(x, y) ⇒ R(cl(x), y))",
		},
		Conclusion: "closure_operator_on(c, R, cl)",
	},
		func(a *Argument, R *Arrow2[A, A, Bool], cl *Arrow[A, A], c, F *Expr[Set[A]], hypotheses Fact) {
			assumptions := a.Conjuncts(
				hypotheses,
				"the carrier is partially ordered",
				"the selected family lies in the carrier",
				"each image is the least family point above its argument")
			partialOrder, within, least := assumptions[0], assumptions[1], assumptions[2]
			preorder := PartialOrderOnPreorder.Read(partialOrder)
			closed := a.Have(
				"selected points stay in the carrier",
				"∀x:A. x ∈ c ⇒ cl(x) ∈ c",
				By(least, within, set_basic.SubsetDef))
			extensive := a.Have(
				"each point lies below its selected point",
				"∀x:A. x ∈ c ⇒ R(x, cl(x))",
				By(least))
			monotone := a.Have(
				"leastness respects the order",
				"∀x y:A. x ∈ c ∧ y ∈ c ∧ R(x, y) ⇒ R(cl(x), cl(y))",
				Derive(func(b *Argument) {
					x, y := b.FixAs[A](), b.FixAs[A]()
					ordered := b.Assume()
					above := b.Have(
						"the second closure bounds the first point",
						"R(x, cl(y))",
						By(
							extensive.At(y),
							closed.At(y),
							ordered,
							TransitiveOn.Read(preorder).AsFact().At(x, y, cl.Apply(y))))
					b.Show(
						"the first closure is least among these bounds",
						By(least.At(x), least.At(y), above, ordered))
				}))
			idempotent := a.Have(
				"a selected point is fixed by closure",
				"∀x:A. x ∈ c ⇒ cl(cl(x)) = cl(x)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					inCarrier := b.Assume()
					members := b.Have(
						"both closures lie in the carrier",
						"cl(x) ∈ c ∧ cl(cl(x)) ∈ c",
						By(closed, inCarrier))
					below := b.Have(
						"the first closure bounds its own closure",
						"R(cl(cl(x)), cl(x))",
						By(ReflexiveOn.Read(preorder), least.At(x), least.At(cl.Apply(x)), inCarrier, members))
					b.Show(
						"antisymmetry identifies the two closures",
						By(AntisymmetricOn.Read(partialOrder), extensive.At(cl.Apply(x)), below, members))
				}))
			a.Show(
				"the closure laws hold on the carrier",
				Unfold(ClosureOperatorOn),
				By(partialOrder, closed, extensive, monotone, idempotent))
		}),
})}

// ClosureFixedPointsCompleteLattice — the fixed points of a closure operator form a complete lattice:
// close the ambient supremum, while monotonicity and antisymmetry show that the ambient infimum is fixed.
var ClosureFixedPointsCompleteLattice = closureFixedPointsCompleteLatticeThm{family.Add(registry.ProofEntry{
	Name: "ClosureFixedPointsCompleteLattice",
	Key:  "prop_ee374059aa862fa8",
	Build: family.Theorem(Statement{
		Binders: "∀R:(A → A → bool). ∀sup inf:(set(A) → A). ∀c:set(A). ∀cl:(A → A).",
		Hypotheses: []string{
			"complete_lattice_on(c, R, sup, inf)",
			"closure_operator_on(c, R, cl)",
		},
		Conclusion: "complete_lattice_on({x:A | x ∈ c ∧ cl(x) = x}, R, λs:set(A). cl(sup(s)), inf)",
	},
		func(
			a *Argument,
			R *Arrow2[A, A, Bool],
			sup, inf *Arrow[Set[A], A],
			c *Expr[Set[A]],
			cl *Arrow[A, A],
			hypotheses Fact,
		) {
			assumptions := a.Conjuncts(
				hypotheses,
				"the ambient carrier is a complete lattice",
				"the map is a closure operator")
			lattice, closure := assumptions[0], assumptions[1]
			partialOrder := a.Have(
				"the ambient relation is a partial order",
				"partial_order_on(c, R)",
				By(CompleteLatticeOnPartialOrder.Read(lattice)))
			preorder := a.Have(
				"the ambient relation is a preorder",
				"preorder_on(c, R)",
				By(PartialOrderOnPreorder.Read(partialOrder)))
			fixedOrder := a.Have(
				"the partial order restricts to the fixed points",
				"partial_order_on({x:A | x ∈ c ∧ cl(x) = x}, R)",
				Simp(Fwd(PartialOrderOn), Fwd(PreorderOn)),
				BySets(ReflexiveOn.Read(preorder), TransitiveOn.Read(preorder), AntisymmetricOn.Read(partialOrder)))

			suprema := a.Have(
				"closing each ambient supremum gives the fixed-point supremum",
				Statement{
					Binders: "∀s:set(A).",
					Hypotheses: []string{
						"s ⊆ {x:A | x ∈ c ∧ cl(x) = x}",
					},
					Conclusion: "has_sup_on({x:A | x ∈ c ∧ cl(x) = x}, R, s, cl(sup(s)))",
				},
				Derive(func(b *Argument) {
					s := b.FixAs[Set[A]]()
					subset := b.Assume()
					within := b.Have(
						"the subset lies in the ambient carrier",
						"s ⊆ c",
						BySets(subset))
					ambient := b.Have(
						"the ambient supremum has its universal property",
						"has_sup_on(c, R, s, sup(s))",
						By(SupHasSupOn.Read(lattice), within))
					bounds := b.Unfolded(ambient, HasSupOnDef)
					supPoint := sup.Apply(s)
					fixed := b.Have(
						"the closed supremum is a fixed carrier point",
						"cl(sup(s)) ∈ {x:A | x ∈ c ∧ cl(x) = x}",
						BySets(
							bounds,
							ClosureOnIn.Read(closure).AsFact().At(supPoint),
							ClosureIdempotent.Read(closure).AsFact().At(supPoint)))
					upper := b.Have(
						"the closed supremum bounds every member",
						"upper_bound(R, s, cl(sup(s)))",
						Simp(Fwd(UpperBoundDef)),
						Derive(func(d *Argument) {
							x := d.FixAs[A]()
							inSubset := d.Assume()
							ordered := d.Have(
								"a fixed member lies below the ambient supremum",
								"x ∈ c ∧ cl(x) = x ∧ sup(s) ∈ c ∧ R(x, sup(s))",
								BySets(inSubset, subset, bounds, UpperBoundDef))
							d.Show(
								"monotonicity bounds the fixed member by the closed supremum",
								By(Normalized, ordered, ClosureMonotone.Read(closure).AsFact().At(x, supPoint)))
						}))
					least := b.Have(
						"the closed supremum lies below every fixed upper bound",
						"∀y:A. y ∈ {x:A | x ∈ c ∧ cl(x) = x} ∧ upper_bound(R, s, y) ⇒ R(cl(sup(s)), y)",
						Derive(func(d *Argument) {
							y := d.FixAs[A]()
							fixedBound := d.Assume()
							ordered := d.Have(
								"a fixed upper bound also bounds the ambient supremum",
								"y ∈ c ∧ cl(y) = y ∧ sup(s) ∈ c ∧ R(sup(s), y)",
								BySets(bounds, fixedBound))
							d.Show(
								"monotonicity preserves the comparison with the fixed bound",
								By(Normalized, ordered, ClosureMonotone.Read(closure).AsFact().At(supPoint, y)))
						}))
					b.Show(
						"the closed supremum has the required universal property",
						By(subset, fixed, upper, least, HasSupOnDef))
				}))

			infima := a.Have(
				"each ambient infimum is the fixed-point infimum",
				"∀s:set(A). s ⊆ {x:A | x ∈ c ∧ cl(x) = x} ⇒ has_inf_on({x:A | x ∈ c ∧ cl(x) = x}, R, s, inf(s))",
				Derive(func(b *Argument) {
					s := b.FixAs[Set[A]]()
					subset := b.Assume()
					within := b.Have(
						"the subset lies in the ambient carrier",
						"s ⊆ c",
						BySets(subset))
					ambient := b.Have(
						"the ambient infimum has its universal property",
						"has_inf_on(c, R, s, inf(s))",
						By(InfHasInfOn.Read(lattice), within))
					bounds := b.Unfolded(ambient, HasInfOnDef)
					infPoint := inf.Apply(s)
					lower := b.Have(
						"closing the infimum still gives a lower bound",
						"lower_bound(R, s, cl(inf(s)))",
						Simp(Fwd(LowerBoundDef)),
						Derive(func(d *Argument) {
							x := d.FixAs[A]()
							inSubset := d.Assume()
							ordered := d.Have(
								"the ambient infimum lies below each fixed member",
								"x ∈ c ∧ cl(x) = x ∧ inf(s) ∈ c ∧ R(inf(s), x)",
								BySets(inSubset, subset, bounds, LowerBoundDef))
							d.Show(
								"monotonicity keeps the closed infimum below the fixed member",
								By(Normalized, ordered, ClosureMonotone.Read(closure).AsFact().At(infPoint, x)))
						}))
					closedIn := b.Have(
						"the closed infimum belongs to the ambient carrier",
						"cl(inf(s)) ∈ c",
						By(ClosureOnIn.Read(closure), bounds))
					below := b.Have(
						"greatestness places the closed infimum below the infimum",
						"R(cl(inf(s)), inf(s))",
						By(bounds, closedIn, lower))
					fixed := b.Have(
						"extensivity and antisymmetry fix the ambient infimum",
						"cl(inf(s)) = inf(s)",
						By(
							AntisymmetricOn.Read(partialOrder),
							bounds,
							closedIn,
							below,
							ClosureExtensive.Read(closure).AsFact().At(infPoint)))
					fixedPoints := b.TermAs[Set[A]]("{x:A | x ∈ c ∧ cl(x) = x}")
					b.Show(
						"the ambient infimum retains its universal property among fixed points",
						BySets(bounds, fixed, subset, HasInfOnDef.At(fixedPoints, R, s, infPoint)))
				}))
			a.Show(
				"the fixed points form a complete lattice",
				By(fixedOrder, suprema, infima, CompleteLatticeOn))
		}),
})}
