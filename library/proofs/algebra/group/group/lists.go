// lists.go — the product of a list of members of a group on a set.

package group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/registry"
)

// FoldIn — the product of a list of points of the carrier lies in the
// carrier: the identity for the empty list, and a product of two points of
// the carrier at each step.
var FoldIn = foldInThm{family.Add(registry.ProofEntry{
	Name: "FoldIn",
	Key:  "prop_cd74aeba27825b86",
	Build: GroupOn.Law(Statement{
		Binders: "∀t:list(A).",
		Hypotheses: []string{
			"∀y:A. list_member(y, t) ⇒ y ∈ G.carrier",
		},
		Conclusion: "list_fold(G.mul, t, G.one) ∈ G.carrier",
	},
		func(a *Argument, grp GroupFact[on.G]) {
			a.Induct("t")
			a.Base(
				"the empty product is G.one",
				By(list.ListFoldDef, OneIn.Read(grp)))
			a.Step(
				"h times the product of the tail, both in G.carrier",
				func(b *Argument, ih Fact) {
					args := b.StepArgs("h", "t")
					b.Do(Simp(Fwd(list.ListFoldDef), Fwd(list.ListMemberDef)))
					entries := b.Assume()
					b.Show(
						"the head and the tail's entries lie in G.carrier",
						By(entries, ih, MulIn.Read(grp).AsFact().At(args[0], b.Term("list_fold(G.mul, t, G.one)"))))
				})
		}),
})}

// FoldShift — folding into b is folding into the identity and then
// multiplying by b on the right: by induction on the list, the left
// identity for the empty list and associativity at each step.
var FoldShift = foldShiftThm{family.Add(registry.ProofEntry{
	Name: "FoldShift",
	Key:  "prop_8c1e630adcd15b92",
	Build: GroupOn.Law(Statement{
		Binders: "∀t:list(A). ∀b:A.",
		Hypotheses: []string{
			"∀y:A. list_member(y, t) ⇒ y ∈ G.carrier",
			"b ∈ G.carrier",
		},
		Conclusion: "list_fold(G.mul, t, b) = list_fold(G.mul, t, G.one) * b",
	},
		func(a *Argument, grp GroupFact[on.G]) {
			a.Induct("t")
			a.Base(
				"the empty fold into b is b, which is G.one * b",
				Simp(Fwd(list.ListFoldDef)),
				By(LeftIdentityOn.Read(grp)))
			a.Step(
				"h times the shifted fold of the tail reassociates",
				func(c *Argument, ih Fact) {
					args := c.StepArgs("h", "t")
					c.Do(Simp(Fwd(list.ListFoldDef), Fwd(list.ListMemberDef)))
					b := c.FixAs[A]("b")
					given := c.Assume()
					tail := c.TermAs[A]("list_fold(G.mul, t, G.one)")
					c.Show(
						"h * (P * b) is (h * P) * b, the tail's product P lying in G.carrier",
						By(given, ih, FoldIn.Read(grp), AssocOn.Read(grp).AsFact().At(args[0], tail, b)))
				})
		}),
})}

// RotateProductOne — moving the head of a list of product G.one to its
// end keeps the product G.one: h times the product P of the tail is G.one,
// so h is the inverse of P and P * h is G.one too, and the product of the
// rotated list is P * h (FoldShift).
var RotateProductOne = rotateProductOneThm{family.Add(registry.ProofEntry{
	Name: "RotateProductOne",
	Key:  "prop_310553fb3d42fc1e",
	Build: GroupOn.Law(Statement{
		Binders: "∀h:A. ∀t:list(A).",
		Hypotheses: []string{
			"h ∈ G.carrier",
			"∀y:A. list_member(y, t) ⇒ y ∈ G.carrier",
			"list_fold(G.mul, cons(h, t), G.one) = G.one",
		},
		Conclusion: "list_fold(G.mul, list_append(t, cons(h, nil)), G.one) = G.one",
	},
		func(
			a *Argument,
			grp GroupFact[on.G],
			h *Expr[A],
			t *Expr[list.List[A]],
			hIn, entries, product Fact,
		) {
			hm := a.MemberOf[on.G](h, hIn)
			tail := a.TermAs[A]("list_fold(G.mul, t, G.one)")
			tailIn := a.MemberOf[on.G](tail, GroupPremises(entries, FoldIn.Read(grp).At(t)))
			unfolded := a.Simplified(product, Fwd(list.ListFoldDef))
			inverse := a.Have(
				"h times the tail's product is G.one, so h is its inverse",
				"h = G.inv(list_fold(G.mul, t, G.one))",
				By(unfolded, InvUniqueOn.Read(grp).At(hm, tailIn)))
			a.Show(
				"the rotated list folds to the tail's product times h, which is G.one",
				CalcEq(
					Leg(
						a.Term("list_fold(G.mul, t, list_fold(G.mul, cons(h, nil), G.one))"),
						"a fold over a concatenation folds the front into the fold of the back",
						By(list.FoldAppend)),
					Leg(
						a.Term("list_fold(G.mul, t, h)"),
						"the one-entry list folds to h * G.one, which is h",
						Simp(Fwd(list.ListFoldDef), Fwd(RightIdentityOn.Read(grp))),
						Refl()),
					Leg(
						a.Term("list_fold(G.mul, t, G.one) * h"),
						"folding into h is folding into G.one and multiplying by h",
						By(entries, hm, FoldShift.Read(grp))),
					FinalLeg(
						"and the tail's product times its inverse is G.one",
						inverse.Rw(),
						By(RightInverseOn.Read(grp).At(tailIn))),
				))
		}),
})}
