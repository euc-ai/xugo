// membership.go — list_member, and when a list repeats nothing.
//
// A member sits at a split of the list, and the other laws here say where
// an element can be found after something has been done to the list:
// concatenated, reversed, mapped. `list_distinct` is stated in terms of
// list_member and closes the file — the one law about it is what the
// listing chapter reads when it counts a list's set.

package list

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// MemberAppend — by induction on the front list. The empty list puts
// nothing in front and holds nothing; a head in front of the list is the
// same head in front of the concatenation, so both sides peel it and the
// tail is the hypothesis.
var MemberAppend = memberAppendThm{family.Add(registry.ProofEntry{
	Name: "MemberAppend",
	Key:  "prop_329dfe924ea50c20",
	Build: family.Theorem("∀x:A. ∀l m:list(A). "+
		"    list_member(x, list_append(l, m)) ⇔ list_member(x, l) ∨ list_member(x, m)",
		func(a *Argument, x *Expr[A], l, m *Expr[List[A]]) {
			a.Induct(l)
			a.Base(
				"the empty list in front of m is m, and nothing is in the empty list",
				By(ListAppendDef, ListMemberDef))
			a.Step(
				"a head in front: x is that head, or it is in the tail's "+
					"concatenation, which the hypothesis splits between the tail and m",
				func(b *Argument, ih Fact) {
					b.Show(
						"both sides peel the same head; the hypothesis decides the rest",
						By(ih, ListAppendDef, ListMemberDef))
				})
		}),
})}

// MemberSplit — a member of a list sits at a split of it: by induction on the list. Nil has no
// member; a member of cons(h, t) is its head, with nothing in front of it, or a member of t, whose
// split grows by h in front.
var MemberSplit = memberSplitThm{family.Add(registry.ProofEntry{
	Name: "MemberSplit",
	Key:  "prop_7cbb9b93e21a07e0",
	Build: family.Theorem(Statement{
		Binders: "∀x:A. ∀l:list(A).",
		Hypotheses: []string{
			"list_member(x, l)",
		},
		Conclusion: "∃l₁ l₂:list(A). l = list_append(l₁, cons(x, l₂))",
	}, func(a *Argument, x *Expr[A]) {
		a.Induct("l")
		a.Base(
			"nil has no member",
			By(ListMemberDef))
		a.Step(
			"a member of cons(h, t) is its head or a member of t",
			func(c *Argument, ih Fact) {
				args := c.StepArgs("h", "t")
				t := args[1]
				member := c.Assume()
				c.Cases(c.Term("x = h"))
				c.When(
					"at the head nothing stands in front of x",
					func(e *Argument, atHead Fact) {
						e.Take(e.TermAs[List[A]]("nil"))
						e.Take(t)
						e.Show(
							"cons(h, t) is nil, then x, then t",
							By(Normalized, atHead, ListAppendDef))
					})
				c.Otherwise(
					"past the head x lies in t, and the split of t grows by h",
					func(e *Argument, notHead Fact) {
						inTail := e.Have(
							"x is a member of t",
							"list_member(x, t)",
							By(notHead, member, ListMemberDef))
						_, back, split := e.Obtain2As[List[A], List[A]](
							"so x sits at a split of t",
							"∃l₁ l₂:list(A). t = list_append(l₁, cons(x, l₂))",
							By(inTail, ih),
							Named("l₁", "l₂"))
						e.Take(e.TermAs[List[A]]("cons(h, l₁)"))
						e.Take(back)
						e.Show(
							"cons(h, t) is cons(h, l₁), then x, then l₂",
							Simp(Fwd(ListAppendDef)),
							By(Normalized, split))
					})
			})
	}),
})}

// MemberReverse — reversal rearranges a list without changing what it
// contains, which is what a reading of a list as a set needs when it
// carries that set across list_reverse. By induction on l: the empty list
// reverses to itself; a head in front of the list goes to the far end
// of the reversal, so membership there splits between the reversed
// tail, where the hypothesis reads it back off the tail itself, and
// the single head at the end.
var MemberReverse = memberReverseThm{family.Add(registry.ProofEntry{
	Name: "MemberReverse",
	Key:  "prop_4c57689ba098499e",
	Build: family.Theorem("∀x:A. ∀l:list(A). list_member(x, list_reverse(l)) ⇔ list_member(x, l)",
		func(a *Argument, x *Expr[A], l *Expr[List[A]]) {
			a.Induct(l)
			a.Base(
				"the empty list reverses to itself, and nothing is in it",
				Simp(Fwd(ListReverseDef)),
				TrivialNormalized())
			a.Step(
				"a head in front: reversal sends it to the far end, behind the reversed tail",
				func(b *Argument, ih Fact) {
					b.Show(
						"x is in the reversed tail — the hypothesis returns that to t — or x is the head at the far end",
						By(ih, ListReverseDef, MemberAppend, ListMemberDef))
				})
		}),
})}

// MemberMap — the image of a list holds exactly the images of its
// elements. By induction on l with f and y fixed. The empty list has
// no image and no element, so neither side holds. With a head in front
// both sides peel it — list_map puts f(h) in front of the tail's image, and
// membership in cons(h, t) splits off the head — and the equivalence
// is then settled one direction at a time, the head accounting for
// y = f(h) and the induction hypothesis for the tail.
var MemberMap = memberMapThm{family.Add(registry.ProofEntry{
	Name: "MemberMap",
	Key:  "prop_8c09752e951597d7",
	Build: family.Theorem("∀f:(A → B). ∀y:B. ∀l:list(A). "+
		"    list_member(y, list_map(f, l)) ⇔ ∃x:A. list_member(x, l) ∧ y = f(x)",
		func(a *Argument, f *Arrow[A, B], y *Expr[B], l *Expr[List[A]]) {
			// The clauses that peel one constructor off each side: list_map's,
			// and list_member's at the image's element type and at l's.
			mapClauses := Fwd(ListMapDef)
			memInImage := Fwd(ListMemberDef.Inst[B]())
			memInList := Fwd(ListMemberDef)

			a.Induct(l)
			a.Base(
				"the empty list has no image and no element, so neither side holds",
				Simp(mapClauses, memInImage, memInList),
				Basic())
			a.Step(
				"a head in front: list_map puts f(h) out front, and membership in cons(h, t) splits off the head",
				func(b *Argument, ih Fact) {
					b.Do(Simp(mapClauses, memInImage, memInList))
					b.Iff()
					b.Forward(
						"y is f of the head, or y is in the tail's image",
						func(c *Argument, inImage Fact) {
							c.Show(
								"the head is an element of cons(h, t) in the first "+
									"case; in the second the hypothesis finds one in the tail",
								By(ih, inImage))
						})
					b.Backward(
						"an element of cons(h, t) that f sends to y is the head, or lies in the tail",
						func(c *Argument, witnessed Fact) {
							c.Show(
								"the head gives y = f(h) outright; from the tail the hypothesis puts y in the tail's image",
								By(witnessed, ih))
						})
				})
		}),
})}

// DistinctAppend — the repetition-free reading of a concatenation, the
// fact the listing correspondence needs when it counts a list's set. By
// induction on the front list: the empty list holds nothing and leaves
// m alone; with a head in front, that head must avoid both its own tail
// and all of m, and what the right side demands of cons(h, t) is
// exactly those two demands together.
var DistinctAppend = distinctAppendThm{family.Add(registry.ProofEntry{
	Name: "DistinctAppend",
	Key:  "prop_aa93b53a949e4ce4",
	Build: family.Sections(
		"∀l m:list(A). "+
			"    list_distinct(list_append(l, m)) ⇔ "+
			"    list_distinct(l) ∧ list_distinct(m) ∧ ∀x:A. list_member(x, l) ⇒ ¬list_member(x, m)",
		func(ctx *Script, headline string) *GoalStackNode {
			// Where the step's content sits: over a list with a head, the
			// condition that nothing in it lies in m separates into the
			// head's own instance and the same condition on the tail.
			// Once it is read that way the two sides of the theorem are
			// the same conjunction.
			avoids := ctx.Lemma(
				"∀h:A. ∀t m:list(A). "+
					"    (∀x:A. list_member(x, cons(h, t)) ⇒ ¬list_member(x, m)) ⇔ "+
					"    ¬list_member(h, m) ∧ ∀x:A. list_member(x, t) ⇒ ¬list_member(x, m)",
				func(a *Argument) {
					a.Show(
						"an element of cons(h, t) is the head or an element of the tail",
						By(ListMemberDef))
				})

			return ctx.Theorem(headline, func(a *Argument, l, m *Expr[List[A]]) {
				a.Induct(l)
				a.Base(
					"the empty list in front of m is m, and holds nothing: both sides say that m is repetition-free",
					Simp(Fwd(ListAppendDef), Fwd(ListDistinctDef), Fwd(ListMemberDef)),
					TrivialNormalized())
				a.Step(
					"a head in front must avoid its own tail and all "+
						"of m, and that is what the right side demands of it",
					func(b *Argument, ih Fact) {
						b.Show(
							"both sides then ask the head to avoid t and m, and "+
								"the hypothesis reads list_append(t, m) as the rest",
							Simp(Fwd(avoids)),
							By(ih, ListAppendDef, ListDistinctDef, MemberAppend))
					})
			})
		}),
})}
