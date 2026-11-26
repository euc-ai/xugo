// permutation.go — the chapter's permutation part: when two lists hold
// the same elements, each as often, in some order.
//
// The relation is defined by the moves a rearrangement is made of, so
// what it comes with first is rule induction: a property that holds of
// the empty pair, survives putting a common head in front, holds of
// every swap of the first two elements, and composes, holds of every
// pair of permutations. The file reads it one way throughout:
// `ByInduction(ListPermutationInduct, perm, …)`, where `perm` is the
// permutation the induction runs along, the property is the goal read at
// its pair, and the four Cases are the four moves in the definition's order — the empty pair, a
// common head, a swap, composition. A law that starts from a
// permutation is proved this way; a law that produces one inducts on
// the list instead.

package list

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/registry"
)

// ListPermutationRules — the four moves: the empty list is a permutation
// of itself, a common head extends a permutation, the first two
// elements trade places, and two permutations compose.
var ListPermutationRules = listPermutationRulesThm{listPermutation.Rules}

// ListPermutationInduct — rule induction along the relation: a property
// every move preserves holds of every permutation.
var ListPermutationInduct = listPermutationInductThm{listPermutation.Induct}

// ListPermutationInductStrong — the same induction, each move also told
// that the pairs it extends or composes are related by permutation, not
// only that they carry the property.
var ListPermutationInductStrong = listPermutationInductStrongThm{listPermutation.InductStrong}

// ListPermutationCases — the four moves are exhaustive: a permutation is
// the empty pair, a common head in front of a permutation, a swap of
// the first two elements, or two permutations in a row.
var ListPermutationCases = listPermutationCasesThm{listPermutation.Cases}

// The four moves, each a member read off the rule set, so that a
// proof names the move it makes.

// PermutationNil — the empty pair: nil is a permutation of itself.
var PermutationNil = permutationNilThm{family.Add(registry.ProofEntry{
	Name:  "PermutationNil",
	Key:   "prop_7e8818f0039b4022",
	Build: family.Theorem("list_permutation(nil, nil)", Cite(ListPermutationRules)),
})}

// PermutationCons — a common head put in front of a permutation keeps it one.
var PermutationCons = permutationConsThm{family.Add(registry.ProofEntry{
	Name: "PermutationCons",
	Key:  "prop_d6af5da4bfeab065",
	Build: family.Theorem(Statement{
		Binders: "∀x:A. ∀l m:list(A).",
		Hypotheses: []string{
			"list_permutation(l, m)",
		},
		Conclusion: "list_permutation(cons(x, l), cons(x, m))",
	},
		Cite(ListPermutationRules)),
})}

// PermutationSwap — the first two elements trade places.
var PermutationSwap = permutationSwapThm{family.Add(registry.ProofEntry{
	Name: "PermutationSwap",
	Key:  "prop_5496045d83e438b9",
	Build: family.Theorem(
		"∀x y:A. ∀l:list(A). list_permutation(cons(x, cons(y, l)), cons(y, cons(x, l)))",
		Cite(ListPermutationRules)),
})}

// PermutationTrans — two permutations in a row are one.
var PermutationTrans = permutationTransThm{family.Add(registry.ProofEntry{
	Name: "PermutationTrans",
	Key:  "prop_e5f6c90a792db12f",
	Build: family.Theorem(Statement{
		Binders: "∀l m n:list(A).",
		Hypotheses: []string{
			"list_permutation(l, m)",
			"list_permutation(m, n)",
		},
		Conclusion: "list_permutation(l, n)",
	},
		Cite(ListPermutationRules)),
})}

// PermutationRefl — every list is a permutation of itself. By induction
// on the list: the empty pair at nil, and at cons the common head put in
// front of both sides of the tail's permutation of itself.
var PermutationRefl = permutationReflThm{family.Add(registry.ProofEntry{
	Name: "PermutationRefl",
	Key:  "prop_499b5c1492146bd4",
	Build: family.Theorem("∀l:list(A). list_permutation(l, l)",
		func(a *Argument, l *Expr[List[A]]) {
			a.Induct(l)
			a.Base(
				"l = nil: the empty list is a permutation of itself",
				By(PermutationNil))
			a.Step(
				"l = cons(h, t): the head is put in front of both sides of the tail's permutation of itself",
				func(b *Argument, ih Fact) {
					b.Show(
						"a common head extends the hypothesis",
						By(ih, PermutationCons))
				})
		}),
})}

// PermutationSym — a permutation read backwards is one. Rule induction,
// carrying "the pair read backwards is a permutation" along the
// relation: each move undone is a move of the same kind. The empty pair
// is its own reverse, a common head stays in front of the reversed
// tails, a swap undoes itself, and two permutations composed in one
// order compose in the other.
var PermutationSym = permutationSymThm{family.Add(registry.ProofEntry{
	Name: "PermutationSym",
	Key:  "prop_4a2e9d025d34ba47",
	Build: family.Theorem(Statement{
		Binders: "∀l m:list(A).",
		Hypotheses: []string{
			"list_permutation(l, m)",
		},
		Conclusion: "list_permutation(m, l)",
	},
		func(a *Argument, l, m *Expr[List[A]], perm Fact) {
			a.Show(
				"rule induction along the permutation, carrying the "+
					"property that the pair read backwards is one too",
				ByInduction(ListPermutationInduct, perm,
					Case(
						"the empty pair is its own reverse",
						By(PermutationNil)),
					Case(
						"a common head stays in front of the reversed tails",
						By(PermutationCons)),
					Case(
						"a swap of the first two elements is undone by swapping them back",
						By(PermutationSwap)),
					Case(
						"two permutations composed one way, read backwards, compose the other way",
						By(PermutationTrans))))
		}),
})}

// PermutationMember — a rearrangement loses no element and gains none.
// Rule induction, carrying "x is in the one list exactly when it is in
// the other" along the relation, x held fixed throughout. At the empty
// pair the two sides are one statement. A common head in front: list_member's
// clause at the head puts "x is that head" on both sides, beside tails
// that agree. A swap: unfolding list_member twice lists the same two first
// elements and the same rest on both sides, in the other order. Two
// permutations composed: the two equivalences chain through the list
// in the middle.
var PermutationMember = permutationMemberThm{family.Add(registry.ProofEntry{
	Name: "PermutationMember",
	Key:  "prop_303e8946615abbd2",
	Build: family.Theorem(Statement{
		Binders: "∀x:A. ∀l m:list(A).",
		Hypotheses: []string{
			"list_permutation(l, m)",
		},
		Conclusion: "list_member(x, l) ⇔ list_member(x, m)",
	},
		func(a *Argument, x *Expr[A], l, m *Expr[List[A]], perm Fact) {
			a.Show(
				"rule induction along the permutation, carrying the property "+
					"that x is in one list exactly when it is in the other",
				ByInduction(ListPermutationInduct, perm,
					Case(
						"the empty pair is one list on both sides",
						TrivialNormalized()),
					Case(
						"a common head: x is that head on both sides, or in tails that hold it alike",
						Derive(func(c *Argument) {
							c.FixAs[A]("h")
							c.FixAs[List[A]]("u")
							c.FixAs[List[A]]("v")
							tailsAgree := c.Assume()
							c.Show(
								"list_member's clause at h on each side, then the tails' agreement",
								Simp(Fwd(ListMemberDef)),
								By(Normalized, tailsAgree))
						})),
					Case(
						"a swap: both sides unfold to x being one of the same two first elements or in the same rest",
						Simp(Fwd(ListMemberDef)),
						TrivialNormalized()),
					Case(
						"two permutations composed: the equivalences chain through the list in the middle",
						Derive(func(c *Argument) {
							c.FixAs[List[A]]("u")
							c.FixAs[List[A]]("v")
							c.FixAs[List[A]]("w")
							throughTheMiddle := c.Assume()
							c.Show(
								"so x is in u exactly when it is in w",
								By(Normalized, throughTheMiddle))
						}))))
		}),
})}

// PermutationListProduct — a rearrangement leaves a product unchanged.
// Rule induction, carrying "the two lists have the same product" along
// the relation. At the empty pair the two sides are one product. A
// common head in front: each product is that head times its tail's, and
// the tails' products agree. A swap: associativity regroups
// x·(y·list_product(t)) as (x·y)·list_product(t) and the other side as
// (y·x)·list_product(t), and commutativity of multiplication makes the
// two one. Two permutations composed: the equations chain through the
// list in the middle — a Calc here, where PermutationMember's chain of
// equivalences closes as it stands.
var PermutationListProduct = permutationListProductThm{family.Add(registry.ProofEntry{
	Name: "PermutationListProduct",
	Key:  "prop_f7e24718498aa6db",
	Build: family.Theorem(Statement{
		Binders: "∀l m:list(num).",
		Hypotheses: []string{
			"list_permutation(l, m)",
		},
		Conclusion: "list_product(l) = list_product(m)",
	},
		func(a *Argument, l, m *Expr[List[Nat]], perm Fact) {
			a.Show(
				"rule induction along the permutation, carrying the "+
					"property that the two lists have the same product",
				ByInduction(ListPermutationInduct, perm,
					Case(
						"the empty pair is one product on both sides",
						TrivialNormalized()),
					Case(
						"a common head: each side is that head times its tail's product, and the tails' products agree",
						Derive(func(c *Argument) {
							c.FixAs[Nat]("h")
							c.FixAs[List[Nat]]("u")
							c.FixAs[List[Nat]]("v")
							tailsAgree := c.Assume()
							c.Show(
								"the product's clause at h on each side, then the tails' agreement",
								Simp(Fwd(ListProductClauses)),
								By(Normalized, tailsAgree))
						})),
					Case(
						"a swap: the first two factors trade places, and multiplication commutes",
						Derive(func(c *Argument) {
							x := c.FixAs[Nat]()
							y := c.FixAs[Nat]()
							c.FixAs[List[Nat]]("t")
							c.Show(
								"unfolded twice and regrouped, the sides are (x * y) * "+
									"list_product(t) and (y * x) * list_product(t), and x * y = y * x",
								Simp(Fwd(ListProductClauses), Fwd(nat_arith.MulAssoc)),
								By(Normalized, nat_arith.MulSym.At(x, y)))
						})),
					Case(
						"two permutations composed: the equations chain through the list in the middle",
						Derive(func(c *Argument) {
							c.FixAs[List[Nat]]("u")
							c.FixAs[List[Nat]]("v")
							c.FixAs[List[Nat]]("w")
							productsAgree := c.Assume()
							c.Show(
								"list_product(u) = list_product(v) = list_product(w)",
								CalcEq(
									Leg(
										c.TermAs[Nat]("list_product(v)"),
										"across the first permutation, by the hypothesis",
										By(productsAgree)),
									FinalLeg(
										"across the second, by the hypothesis",
										By(productsAgree))))
						}))))
		}),
})}

// PermutationMoveToFront — a member of a list can be brought to its
// front, the rest of the list following behind it in some order. By
// induction on the list, x held fixed and its membership carried along.
// The empty list has no members. At a head in front, list_member's clause makes
// x that head or a member of the tail. If x is the head, the rest is the
// tail itself, and the list is a permutation of itself. Otherwise the
// hypothesis brings x to the front of the tail, a permutation of
// cons(x, r), and the rest is h in front of r: the common head extends
// the tail's permutation, a swap then trades h and x, and the two
// permutations compose.
var PermutationMoveToFront = permutationMoveToFrontThm{family.Add(registry.ProofEntry{
	Name: "PermutationMoveToFront",
	Key:  "prop_f2b999027911e9d4",
	Build: family.Theorem(Statement{
		Binders: "∀x:A. ∀m:list(A).",
		Hypotheses: []string{
			"list_member(x, m)",
		},
		Conclusion: "∃r:list(A). list_permutation(m, cons(x, r))",
	},
		func(a *Argument, x *Expr[A], m *Expr[List[A]]) {
			a.Induct(m)
			a.Base(
				"m = nil: nothing is a member of the empty list",
				By(ListMemberDef))
			a.Step(
				"m = cons(h, t): x is the head, or it is in the tail, where the hypothesis brings it to the front",
				func(b *Argument, ih Fact) {
					args := b.StepArgs("h", "t")
					head, tail := ext.As[A](args[0]), ext.As[List[A]](args[1])
					whole := b.TermAs[List[A]]("cons(h, t)")
					member := b.Assume()
					b.Cases(b.Term("x = h"))
					b.When(
						"x is the head: the rest is the tail, and the list is a permutation of itself",
						func(c *Argument, isHead Fact) {
							c.Take(tail)
							c.Show(
								"with x = h, cons(x, t) is cons(h, t) itself",
								isHead.Rw(),
								Cite(PermutationRefl, whole))
						})
					b.Otherwise(
						"x is in the tail: the rest is h in front of what the hypothesis leaves behind x there",
						func(c *Argument, notHead Fact) {
							rest, rearranged := c.ObtainAs[List[A]](
								"x is not the head, so list_member's clause puts it in "+
									"the tail, and the hypothesis brings it to the front there",
								"∃r:list(A). list_permutation(t, cons(x, r))",
								By(ih, member, notHead, ListMemberDef))
							c.Take(c.TermAs[List[A]]("cons(h, r)"))
							headInFront := c.TermAs[List[A]]("cons(h, cons(x, r))")
							extended := c.Have(
								"the common head h extends the tail's permutation",
								"list_permutation(cons(h, t), cons(h, cons(x, r)))",
								By(rearranged, PermutationCons.At(head, tail, c.TermAs[List[A]]("cons(x, r)"))))
							c.Show(
								"a swap then trades h and x, and the two permutations compose",
								By(
									extended,
									PermutationSwap.At(head, x, rest),
									PermutationTrans.At(whole, headInFront, c.TermAs[List[A]]("cons(x, cons(h, r))"))))
						})
				})
		}),
})}
