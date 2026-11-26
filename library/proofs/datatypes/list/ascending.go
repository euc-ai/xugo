// ascending.go — the ordered listing of a set of naturals below a
// bound. `ascending_list(n, P)` lists the numbers from 0 to n that
// satisfy P in increasing order, built by recursion on n; a list is
// ascending when every member is below every later one. The listing is
// the only ascending list with those members.

package list

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ListAscendingDef — `list_ascending(l)`: every member of l is below
// every member after it.
var ListAscendingDef = listAscendingDefThm{family.Define(registry.DefEntry{
	Name:  "ListAscendingDef",
	Key:   "prop_4134833a1477c37c",
	Const: "list_ascending",
	Type:  "list(num) → bool",
	Equations: []string{
		"∀l:list(num). " +
			"    list_ascending(l) ⇔ " +
			"    ∀l₁ l₂:list(num). ∀i j:num. l = list_append(l₁, cons(i, l₂)) ∧ list_member(j, l₂) ⇒ i < j",
	}, Deps: []registry.EntryLike{ListAppendDef, ListMemberDef},
})}

// AscendingListDef — `ascending_list(n, P)`: the numbers from 0 to n
// satisfying P, in increasing order.
var AscendingListDef = ascendingListDefThm{family.Define(registry.DefEntry{
	Name:  "AscendingListDef",
	Key:   "prop_1552bc79ce04796f",
	Const: "ascending_list",
	Type:  "num → (num → bool) → list(num)",
	Equations: []string{
		"∀P:(num → bool). ascending_list(0, P) = COND(P(0), cons(0, nil), nil)",
		"∀n:num. ∀P:(num → bool). " +
			"    ascending_list(suc(n), P) = " +
			"    list_append(ascending_list(n, P), COND(P(suc(n)), cons(suc(n), nil), nil))",
	}, Deps: []registry.EntryLike{ListAppendDef},
})}

// ListAscendingCons — an ascending list has an ascending tail and its
// head is below every member of that tail. In a prefix decomposition,
// either the prefix is empty and the comparison starts at the head,
// or deleting its first element leaves a decomposition of the tail.
var ListAscendingCons = listAscendingConsThm{family.Add(registry.ProofEntry{
	Name: "ListAscendingCons",
	Key:  "prop_4fb8bd2a252f53b8",
	Build: family.Theorem("∀h:num. ∀t:list(num). "+
		"    list_ascending(cons(h, t)) ⇔ list_ascending(t) ∧ (∀j:num. list_member(j, t) ⇒ h < j)",
		func(a *Argument, h *Expr[Nat], t *Expr[List[Nat]]) {
			a.Iff()
			a.Forward(
				"the head precedes the tail, whose own comparisons are comparisons of the whole list",
				func(b *Argument, ascending Fact) {
					b.Show(
						"the empty prefix compares the head, and a prefix beginning with h compares within the tail",
						By(ascending, ListAscendingDef, ListAppendDef))
				})
			a.Backward(
				"every comparison begins at the head or lies within the ascending tail",
				func(b *Argument, orderedTail Fact) {
					b.Do(Simp(Fwd(ListAscendingDef)))
					prefix := b.FixAs[List[Nat]]("l₁")
					b.FixAs[List[Nat]]("l₂")
					b.FixAs[Nat]("i")
					b.FixAs[Nat]("j")
					decomposition := b.Assume()
					b.Show(
						"an empty prefix uses the head bound; a nonempty prefix leaves a tail comparison",
						By(
							orderedTail,
							decomposition,
							Cases.At(prefix),
							ListAppendDef,
							ConsInjective,
							ListAscendingDef.At(t)))
				})
		}),
})}

// ListAscendingExt — ascending lists with the same members are equal.
// Their heads are both least among the common members, so strict order
// makes those heads equal. Removing that common head leaves ascending
// tails with the same members, to which induction applies.
var ListAscendingExt = listAscendingExtThm{family.Add(registry.ProofEntry{
	Name: "ListAscendingExt",
	Key:  "prop_bd30eb238cc40890",
	Build: family.Theorem(Statement{
		Binders: "∀l m:list(num).",
		Hypotheses: []string{
			"list_ascending(l)",
			"list_ascending(m)",
			"∀i:num. list_member(i, l) ⇔ list_member(i, m)",
		},
		Conclusion: "l = m",
	}, func(a *Argument) {
		a.Induct("l")
		a.Base(
			"a list sharing no member with the empty list must itself be empty",
			func(b *Argument) {
				m := b.FixAs[List[Nat]]("m")
				b.Show(
					"a nonempty list would contribute its head as a member",
					By(Cases.At(m), ListMemberDef))
			})
		a.Step(
			"the common least member is the head of both lists",
			func(b *Argument, ih Fact) {
				b.StepArgs("h", "l")
				h := b.TermAs[Nat]("h")
				tail := b.TermAs[List[Nat]]("l")
				m := b.FixAs[List[Nat]]("m")
				orderedAndShared := b.Assume()
				k, u, asCons := b.Obtain2As[Nat, List[Nat]](
					"the shared head makes the other list nonempty",
					"∃k:num. ∃u:list(num). m = cons(k, u)",
					By(orderedAndShared, Cases.At(m), ListMemberDef))
				heads := b.Have(
					"neither shared least member can lie above the other",
					"h = k",
					By(
						asCons,
						orderedAndShared,
						ListAscendingCons.At(h, tail),
						ListAscendingCons.At(k, u),
						ListMemberDef,
						nat_order.LessThanAsym.At(h, k)))
				tailMembers := b.Have(
					"deleting the common head leaves exactly the same members",
					"∀i:num. list_member(i, l) ⇔ list_member(i, u)",
					By(
						asCons,
						heads,
						orderedAndShared,
						ListAscendingCons.At(h, tail),
						ListAscendingCons.At(k, u),
						ListMemberDef,
						nat_order.LessThanIrrefl.At(h)))
				tails := b.Have(
					"induction identifies the two ascending tails",
					"l = u",
					By(
						ih.At(u),
						tailMembers,
						asCons,
						orderedAndShared,
						ListAscendingCons.At(h, tail),
						ListAscendingCons.At(k, u)))
				b.Show(
					"equal heads and equal tails give equal lists",
					Simp(Fwd(tails), Fwd(asCons), Fwd(heads)),
					Refl())
			})
	}),
})}

// AscendingListMember — the members of the listing are the numbers up
// to the bound that satisfy P. Induct on the bound: the listing at zero
// contains just zero when P holds there, and each successor adds just
// that endpoint when it satisfies P.
var AscendingListMember = ascendingListMemberThm{family.Add(registry.ProofEntry{
	Name: "AscendingListMember",
	Key:  "prop_f75acdfa0b3098bb",
	Build: family.Theorem("∀n:num. ∀P:(num → bool). ∀i:num. "+
		"    list_member(i, ascending_list(n, P)) ⇔ i ≤ n ∧ P(i)",
		func(a *Argument) {
			a.Induct("n")
			a.Base(
				"the bound zero leaves only its endpoint to consider",
				func(b *Argument) {
					b.FixAs[Fun[Nat, Bool]]("P")
					b.FixAs[Nat]("i")
					b.Cases(b.TermAs[Bool]("P(0)"))
					b.When(
						"zero satisfies P, so the listing is the singleton zero",
						func(c *Argument, atZero Fact) {
							c.Show(
								"membership and the bound both force i to be zero",
								Simp(Fwd(AscendingListDef), Fwd(nat_order.LessEq), Fwd(ListMemberDef)),
								By(Normalized, atZero))
						})
					b.Otherwise(
						"zero fails P, so the listing is empty",
						func(c *Argument, notAtZero Fact) {
							c.Show(
								"neither membership nor a point satisfying the bound and P is possible",
								Simp(Fwd(AscendingListDef), Fwd(nat_order.LessEq), Fwd(ListMemberDef)),
								By(Normalized, notAtZero))
						})
				})
			a.Step(
				"the next listing adds its endpoint exactly when P holds there",
				func(b *Argument, ih Fact) {
					b.FixAs[Fun[Nat, Bool]]("P")
					b.FixAs[Nat]("i")
					b.Cases(b.TermAs[Bool]("P(suc(n))"))
					b.When(
						"the endpoint satisfies P and is appended to the previous listing",
						func(c *Argument, atEndpoint Fact) {
							c.Show(
								"a member is the endpoint or one of the previous members",
								Simp(Fwd(AscendingListDef), Fwd(nat_order.LessEq), Fwd(ih), Fwd(MemberAppend), Fwd(ListMemberDef)),
								By(Normalized, atEndpoint))
						})
					b.Otherwise(
						"the endpoint fails P and contributes no member",
						func(c *Argument, notAtEndpoint Fact) {
							c.Show(
								"the old members are exactly those satisfying P within the new bound",
								Simp(Fwd(AscendingListDef), Fwd(nat_order.LessEq), Fwd(ih), Fwd(MemberAppend), Fwd(ListMemberDef)),
								By(Normalized, notAtEndpoint))
						})
				})
		}),
})}

// AscendingListSorted — the listing is ascending. Each successor either
// leaves the list alone or appends an endpoint above every old member.
var AscendingListSorted = ascendingListSortedThm{family.Add(registry.ProofEntry{
	Name: "AscendingListSorted",
	Key:  "prop_b46629d87e8dfde7",
	Build: family.Sections("∀n:num. ∀P:(num → bool). list_ascending(ascending_list(n, P))",
		func(ctx *Script, headline string) *GoalStackNode {
			emptyAscending := ctx.Lemma("list_ascending(nil)", func(a *Argument) {
				a.Show(
					"the empty list has no decomposition beginning at an element",
					By(ListAscendingDef, AppendEqNil, NilNotCons))
			})
			appendEndpoint := ctx.Lemma(Statement{
				Binders: "∀l:list(num). ∀k:num.",
				Hypotheses: []string{
					"list_ascending(l)",
					"∀i:num. list_member(i, l) ⇒ i < k",
				},
				Conclusion: "list_ascending(list_append(l, cons(k, nil)))",
			}, func(a *Argument) {
				a.Induct("l")
				a.Base(
					"a singleton inherits the order of its empty tail",
					Simp(Fwd(ListAscendingCons), Fwd(ListAppendDef), Fwd(ListMemberDef)),
					Basic())
				a.Step(
					"the head remains below the tail after its endpoint is appended",
					func(b *Argument, ih Fact) {
						b.StepArgs("h", "l")
						h := b.TermAs[Nat]("h")
						tail := b.TermAs[List[Nat]]("l")
						k := b.FixAs[Nat]("k")
						orderedAndBounded := b.Assume()
						tailExtended := b.Have(
							"the endpoint extends the ascending tail",
							"list_ascending(list_append(l, cons(k, nil)))",
							By(ih.At(k), orderedAndBounded, At(ListAscendingCons, h, tail), ListMemberDef))
						b.Show(
							"the head remains below the old tail and is also below the new endpoint",
							Simp(Fwd(ListAscendingCons), Fwd(ListAppendDef)),
							By(tailExtended, orderedAndBounded, At(ListAscendingCons, h, tail), ListMemberDef, MemberAppend))
					})
			})
			return ctx.Theorem(headline, func(a *Argument) {
				a.Induct("n")
				a.Base(
					"the initial listing is empty or the singleton zero",
					func(b *Argument) {
						b.FixAs[Fun[Nat, Bool]]("P")
						b.Cases(b.TermAs[Bool]("P(0)"))
						b.When(
							"zero satisfies P and forms an ascending singleton",
							Simp(Fwd(AscendingListDef), Fwd(ListAscendingCons), Fwd(ListMemberDef)),
							Cite(emptyAscending))
						b.Otherwise(
							"zero fails P and the listing is empty",
							Simp(Fwd(AscendingListDef)),
							Cite(emptyAscending))
					})
				a.Step(
					"the next endpoint lies above the previous listing",
					func(b *Argument, ih Fact) {
						P := b.FixAs[Fun[Nat, Bool]]("P")
						n := b.TermAs[Nat]("n")
						previous := b.TermAs[List[Nat]]("ascending_list(n, P)")
						next := b.TermAs[Nat]("suc(n)")
						b.Cases(b.TermAs[Bool]("P(suc(n))"))
						b.When(
							"the endpoint satisfies P and is appended above all old members",
							func(c *Argument, _ Fact) {
								below := c.Have(
									"every previous member precedes the endpoint",
									"∀i:num. list_member(i, ascending_list(n, P)) ⇒ i < suc(n)",
									c.ForEach(func(i *Expr[Nat]) Action {
										return By(AscendingListMember.At(n, P, i), nat_order.LessThanSucIffLessEq.At(i, n))
									}))
								c.Show(
									"appending an endpoint above every member preserves ascending order",
									Simp(Fwd(AscendingListDef)),
									By(ih.At(P), below, At(appendEndpoint, previous, next)))
							})
						b.Otherwise(
							"the endpoint fails P and the ascending listing is unchanged",
							Simp(Fwd(AscendingListDef), Fwd(AppendNil)),
							By(ih))
					})
			})
		}),
})}

// AscendingListUnique — an ascending list whose members are exactly the
// numbers up to n satisfying P is the listing: both lists are ascending
// and have the same members, so ListAscendingExt identifies them.
var AscendingListUnique = ascendingListUniqueThm{family.Add(registry.ProofEntry{
	Name: "AscendingListUnique",
	Key:  "prop_fd249823e4a7bf2a",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀P:(num → bool). ∀l:list(num).",
		Hypotheses: []string{
			"list_ascending(l)",
			"∀i:num. list_member(i, l) ⇔ i ≤ n ∧ P(i)",
		},
		Conclusion: "l = ascending_list(n, P)",
	}, func(a *Argument, n *Expr[Nat], P *Arrow[Nat, Bool], l *Expr[List[Nat]], specified Fact) {
		canonical := a.TermAs[List[Nat]]("ascending_list(n, P)")
		a.Show(
			"the candidate and canonical listings are ascending with identical members",
			By(
				Normalized,
				specified,
				At(ListAscendingExt, l, canonical),
				AscendingListSorted.At(n, P),
				At(AscendingListMember, n, P)))
	}),
})}
