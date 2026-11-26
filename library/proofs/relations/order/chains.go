// chains.go — the laws of chains and of maximal points, and inclusion
// as an order: what a chain is closed under, what maximality means
// once the relation is antisymmetric, the instances the chapter keeps,
// and the sequences of sets nested one step at a time, which are nested
// all the way.

package order

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Chains
// ---------------------------------------------------------------------------

// ChainSubset — a part of a chain is a chain: two of its points are
// two points of the chain, and those are comparable.
var ChainSubset = chainSubsetThm{family.Add(registry.ProofEntry{
	Name: "ChainSubset",
	Key:  "prop_5bce4598681bf5f1",
	Build: family.Theorem(
		Statement{
			Binders: "∀R:(A → A → bool). ∀c d:set(A).",
			Hypotheses: []string{
				"chain(R, c)",
				"d ⊆ c",
			},
			Conclusion: "chain(R, d)",
		},
		Opening(Unfold(
			ChainDef), func(a *Argument, R *Arrow2[A, A, Bool], c, d *Expr[Set[A]], chainAndPart Fact) {
			a.Show(
				"two points of d are two points of c, and any two points of c are comparable",
				BySets(chainAndPart))
		})),
})}

// ChainInsert — what one more point asks of a chain: the point is
// below itself and comparable with every point already there. Both
// directions read the two points of the larger set as the new point or
// an old one.
var ChainInsert = chainInsertThm{family.Add(registry.ProofEntry{
	Name: "ChainInsert",
	Key:  "prop_fe8148962f46ad25",
	Build: family.Theorem(
		"∀R:(A → A → bool). ∀c:set(A). ∀x:A. "+
			"    chain(R, insert(x, c)) ⇔ chain(R, c) ∧ R(x, x) ∧ (∀y:A. y ∈ c ⇒ R(x, y) ∨ R(y, x))",
		Opening(Unfold(ChainDef), func(a *Argument, R *Arrow2[A, A, Bool], c *Expr[Set[A]], x *Expr[A]) {
			a.Iff()
			a.Forward(
				"two old points, the new point twice, and the new point "+
					"with an old one are each two points of the larger chain",
				func(b *Argument, larger Fact) { b.Do(BySets(larger)) })
			a.Backward(
				"each of two points of the larger set is the new point "+
					"or an old one, and the three clauses cover the four cases",
				func(b *Argument, clauses Fact) { b.Do(BySets(clauses)) })
		})),
})}

// ChainUnions — the union of a family of chains that is itself a chain
// under inclusion is a chain: two points of the union lie in two
// members of the family, one of which contains the other, and so both
// lie in one chain.
var ChainUnions = chainUnionsThm{family.Add(registry.ProofEntry{
	Name: "ChainUnions",
	Key:  "prop_3e0fa1b2a98544ac",
	Build: family.Theorem(
		Statement{
			Binders: "∀R:(A → A → bool). ∀F:set(set(A)).",
			Hypotheses: []string{
				"∀c:set(A). c ∈ F ⇒ chain(R, c)",
				"∀c d:set(A). c ∈ F ∧ d ∈ F ⇒ c ⊆ d ∨ d ⊆ c",
			},
			Conclusion: "chain(R, ⋃F)",
		},
		Opening(Unfold(
			ChainDef), func(a *Argument, R *Arrow2[A, A, Bool], F *Expr[Set[Set[A]]], chainsInChain Fact) {
			a.Show(
				"two points of the union lie in two members, the larger of which holds both and is a chain",
				BySets(chainsInChain))
		})),
})}

// MonotoneOnNatInterval — consecutive steps in a preorder compose across a
// finite interval. Induction on the gap starts with reflexivity and appends
// each adjacent step by transitivity.
var MonotoneOnNatInterval = monotoneOnNatIntervalThm{family.Add(registry.ProofEntry{
	Name: "MonotoneOnNatInterval",
	Key:  "prop_babbb4a3f4367f7a",
	Build: family.Theorem(Preorder.Statement(Statement{
		Binders: "∀a:(num → A). ∀m n:num.",
		Hypotheses: []string{
			"∀k:num. m ≤ k ∧ k < n ⇒ R(a(k), a(k + 1))",
			"m ≤ n",
		},
		Conclusion: "R(a(m), a(n))",
	}), func(
		arg *Argument,
		R *Arrow2[A, A, Bool],
		preorder Fact,
		a *Arrow[Nat, A],
		m, n *Expr[Nat],
		adjacent, ordered Fact,
	) {
		gap := arg.Have(
			"each gap inside the interval joins its endpoints",
			"∀d:num. m + d ≤ n ⇒ R(a(m), a(m + d))",
			Derive(func(g *Argument) {
				g.Induct("d")
				g.Base(
					"a zero gap compares a point with itself",
					By(Normalized, nat_arith.AddZero.At(m), Reflexive.Read(preorder)))
				g.Step(
					"append the next adjacent step while its endpoint remains in the interval",
					func(b *Argument, ih Fact) {
						within := b.Assume()
						index := b.TermAs[Nat]("m + d")
						next := b.TermAs[Nat]("m + suc(d)")
						oneMore := b.Have(
							"the adjacent step stays inside the interval",
							"R(a(m + d), a(m + suc(d)))",
							Simp(Fwd(nat_arith.AddSuc), Fwd(nat_arith.Add1)),
							ByArith(adjacent.At(index), within))
						b.Show(
							"the two steps compose",
							ByArith(
								ih,
								within,
								oneMore,
								Transitive.Read(preorder).At(a.Apply(m), a.Apply(index), a.Apply(next))))
					})
			}))
		d, reaches := arg.ObtainAs[Nat](
			"the ordered endpoints differ by a natural gap",
			"∃d:num. n = m + d",
			By(ordered, nat_order.LessEqExists.At(n, m)))
		arg.Show(
			"the interval's gap reaches its final endpoint",
			ByArith(reaches, gap.At(d)))
	}),
})}

// ---------------------------------------------------------------------------
// Maximal points
// ---------------------------------------------------------------------------

// MaximalIff — under a partial order a maximal point is one that
// nothing else of the set is above. Of the order's axioms the proof
// spends antisymmetry alone: the point it is below, being below it in
// turn, is equal to it; and conversely a point it is below that is
// equal to it is below it by that same step, read at the equation.
var MaximalIff = maximalIffThm{family.Add(registry.ProofEntry{
	Name: "MaximalIff",
	Key:  "prop_8ebb546ba6356b05",
	Build: PartialOrder.Law("∀s:set(A). ∀m:A. "+
		"    maximal(R, s, m) ⇔ m ∈ s ∧ (∀x:A. x ∈ s ∧ R(m, x) ⇒ x = m)",
		func(a *Argument, R *Arrow2[A, A, Bool], partial Fact, s *Expr[Set[A]], m *Expr[A]) {
			a.Do(Unfold(MaximalDef))
			a.Iff()
			a.Forward(
				"a point of s that m is below is below m in turn, and antisymmetry makes the two equal",
				func(b *Argument, isMaximal Fact) {
					b.Show(
						"each of the two is below the other",
						By(isMaximal, Antisymmetric.Read(partial)))
				})
			a.Backward(
				"a point of s that m is below is m, and with m written for it the step from m is the step to m",
				func(b *Argument, nothingAbove Fact) { b.Do(By(nothingAbove)) })
		}),
})}

// ---------------------------------------------------------------------------
// Inclusion
// ---------------------------------------------------------------------------
//
// The instances the chapter keeps for itself, the set chapters lying
// below every chapter of relations (the README says why), and what the
// interval law says at them about sequences of sets.

// SubsetPreorder — inclusion is a preorder.
var SubsetPreorder = subsetPreorderThm{family.Add(registry.ProofEntry{
	Name: "SubsetPreorder",
	Key:  "prop_24f8ad63f507021d",
	Build: family.Instance(Preorder, "preorder(λs:set(A). λt:set(A). s ⊆ t)",
		Case(
			"reflexive: a set is included in itself",
			Unfold(equivalence.ReflexiveDef),
			Cite(set_order.SubsetRefl)),
		Case(
			"transitive: two inclusions through a common set compose",
			Unfold(equivalence.TransitiveDef),
			Cite(set_order.SubsetTrans))),
})}

// SupersetPreorder — reversed inclusion is a preorder, the one a
// decreasing sequence of sets climbs.
var SupersetPreorder = supersetPreorderThm{family.Add(registry.ProofEntry{
	Name: "SupersetPreorder",
	Key:  "prop_545d1a095ee6b88b",
	Build: family.Instance(Preorder, "preorder(λs:set(A). λt:set(A). t ⊆ s)",
		Case(
			"reflexive: a set is included in itself",
			Unfold(equivalence.ReflexiveDef),
			Cite(set_order.SubsetRefl)),
		Case(
			"transitive: two inclusions through a common set compose",
			Unfold(equivalence.TransitiveDef),
			BySets())),
})}

// IncreasingFromSteps — each set of a sequence that lies in the next one,
// from m on below n, lies in the n-th: MonotoneOnNatInterval read at
// inclusion.
var IncreasingFromSteps = increasingFromStepsThm{family.Add(registry.ProofEntry{
	Name: "IncreasingFromSteps",
	Key:  "prop_b7018c0e58a50ce1",
	Build: family.Theorem(Statement{
		Binders: "∀s:(num → set(A)). ∀m n:num.",
		Hypotheses: []string{
			"∀k:num. m ≤ k ∧ k < n ⇒ s(k) ⊆ s(k + 1)",
			"m ≤ n",
		},
		Conclusion: "s(m) ⊆ s(n)",
	},
		func(a *Argument, s *Arrow[Nat, Set[A]], m, n *Expr[Nat], steps, ordered Fact) {
			a.Show(
				"inclusion is a preorder, whose steps compose across the interval from m to n",
				By(steps, ordered, MonotoneOnNatInterval.Read(SubsetPreorder).At(s, m, n)))
		}),
})}

// DecreasingFromSteps — each set of a sequence that holds the next one,
// from m on below n, holds the n-th: MonotoneOnNatInterval read at
// reversed inclusion.
var DecreasingFromSteps = decreasingFromStepsThm{family.Add(registry.ProofEntry{
	Name: "DecreasingFromSteps",
	Key:  "prop_a3a4d13a1e2279c4",
	Build: family.Theorem(Statement{
		Binders: "∀s:(num → set(A)). ∀m n:num.",
		Hypotheses: []string{
			"∀k:num. m ≤ k ∧ k < n ⇒ s(k + 1) ⊆ s(k)",
			"m ≤ n",
		},
		Conclusion: "s(n) ⊆ s(m)",
	},
		func(a *Argument, s *Arrow[Nat, Set[A]], m, n *Expr[Nat], steps, ordered Fact) {
			a.Show(
				"reversed inclusion is a preorder, whose steps compose across the interval from m to n",
				By(steps, ordered, MonotoneOnNatInterval.Read(SupersetPreorder).At(s, m, n)))
		}),
})}

// SubsetPartialOrder — inclusion is a partial order: the preorder
// above, and two sets each included in the other are equal.
var SubsetPartialOrder = subsetPartialOrderThm{family.Add(registry.ProofEntry{
	Name: "SubsetPartialOrder",
	Key:  "prop_9499ef8f42db39a4",
	Build: family.Instance(PartialOrder, "partial_order(λs:set(A). λt:set(A). s ⊆ t)",
		Case(
			"inclusion is a preorder",
			Cite(SubsetPreorder)),
		Case(
			"antisymmetric: two sets each included in the other are equal",
			Unfold(AntisymmetricDef),
			Cite(set_order.SubsetAntisym))),
})}
