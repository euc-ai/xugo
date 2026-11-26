// nth.go — list_nth, the element at a position, and how positions move
// through the other operations.
//
// A position is a natural number below the length. list_nth reads the
// list at one; these laws say where an element sits after a cons, a map
// or a concatenation, that the members are the elements at positions,
// that a list is fixed by its length and its elements, and that every
// finite sequence is the list of some list's positions.

package list

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/registry"
)

// NthHead — the head is at position 0: there the guard of the
// definition holds, and it answers the head.
var NthHead = nthHeadThm{family.Add(registry.ProofEntry{
	Name: "NthHead",
	Key:  "prop_7a3f132788fa0a77",
	Build: family.Theorem("∀h:A. ∀t:list(A). list_nth(cons(h, t), 0) = h",
		func(a *Argument, h *Expr[A], t *Expr[List[A]]) {
			a.Show(
				"at position 0 the definition answers the head",
				Simp(Fwd(ListNthDef)),
				Basic())
		}),
})}

// NthTail — position suc(i) of cons(h, t) is position i of t: suc(i)
// is not 0, so the definition reads the tail at suc(i) − 1, which is i.
var NthTail = nthTailThm{family.Add(registry.ProofEntry{
	Name: "NthTail",
	Key:  "prop_8c5afac307d878d0",
	Build: family.Theorem("∀h:A. ∀t:list(A). ∀i:num. list_nth(cons(h, t), suc(i)) = list_nth(t, i)",
		func(a *Argument, h *Expr[A], t *Expr[List[A]], i *Expr[Nat]) {
			a.Show(
				"suc(i) is not 0, and one taken off it is i",
				By(Normalized, ListNthDef, peano.SucNotZero, nat_monus.SucSubOne))
		}),
})}

// NthMap — the image has f of the element at every position. By
// induction on l for every position, f fixed: nil has no position; at
// cons(h, t) position 0 holds h, and f(h) in the image, and a later
// position suc(j) is position j of the tail on both sides, where the
// hypothesis applies.
var NthMap = nthMapThm{family.Add(registry.ProofEntry{
	Name: "NthMap",
	Key:  "prop_972fb465c2485959",
	Build: family.Theorem(Statement{
		Binders: "∀f:(A → B). ∀l:list(A). ∀i:num.",
		Hypotheses: []string{
			"i < list_length(l)",
		},
		Conclusion: "list_nth(list_map(f, l), i) = f(list_nth(l, i))",
	}, func(a *Argument, f *Arrow[A, B]) {
		a.Induct("l")
		a.Base(
			"the empty list has no position",
			By(Normalized, ListLengthDef, nat_order.LessThanZeroClause))
		a.Step(
			"at cons(h, t) position 0 holds the head, and every later position is one of the tail's",
			func(b *Argument, ih Fact) {
				b.StepArgs("h", "t")
				i := b.FixAs[Nat]("i")
				bounded := b.Assume()
				b.Cases(b.Term("i = 0"))
				b.When(
					"position 0 holds h, and f(h) in the image",
					func(c *Argument, atHead Fact) {
						c.Do(atHead.Rw())
						c.Show(
							"both sides are f(h)",
							Simp(Fwd(ListMapDef), Fwd(NthHead), Fwd(NthHead.Inst[B]())),
							Refl())
					})
				b.Otherwise(
					"a later position suc(j) is position j of the tail, on both sides",
					func(c *Argument, notHead Fact) {
						j, isSuc := c.ObtainAs[Nat](
							"the position is a successor",
							"∃j:num. i = suc(j)",
							By(Normalized, notHead, peano.Cases.At(i)))
						inTail := c.Have(
							"so j is a position of the tail",
							"j < list_length(t)",
							ByArith(bounded, isSuc, ListLengthDef))
						c.Do(isSuc.Rw())
						c.Show(
							"both sides read the tail at j, where the hypothesis applies",
							Simp(Fwd(ListMapDef), Fwd(NthTail), Fwd(NthTail.Inst[B]())),
							By(ih.At(j), inTail))
					})
			})
	}),
})}

// NthAppendLeft — a position of the front list keeps its element in the
// concatenation. By induction on l for every position, m fixed: nil has
// no position; at cons(h, t) position 0 holds h on both sides, and a
// later position suc(j) is position j of t on both sides, where the
// hypothesis applies.
var NthAppendLeft = nthAppendLeftThm{family.Add(registry.ProofEntry{
	Name: "NthAppendLeft",
	Key:  "prop_865286c6c0c413d3",
	Build: family.Theorem(Statement{
		Binders: "∀l m:list(A). ∀i:num.",
		Hypotheses: []string{
			"i < list_length(l)",
		},
		Conclusion: "list_nth(list_append(l, m), i) = list_nth(l, i)",
	}, func(a *Argument, l, m *Expr[List[A]]) {
		a.Induct(l)
		a.Base(
			"the empty list has no position",
			By(Normalized, ListLengthDef, nat_order.LessThanZeroClause))
		a.Step(
			"at cons(h, t) position 0 holds the head, and every later position is one of the tail's",
			func(c *Argument, ih Fact) {
				c.StepArgs("h", "t")
				i := c.FixAs[Nat]("i")
				bounded := c.Assume()
				c.Cases(c.Term("i = 0"))
				c.When(
					"position 0 holds h on both sides",
					func(d *Argument, atHead Fact) {
						d.Do(atHead.Rw())
						d.Show(
							"both sides are h",
							Simp(Fwd(ListAppendDef), Fwd(NthHead)),
							Refl())
					})
				c.Otherwise(
					"a later position suc(j) is position j of t, on both sides",
					func(d *Argument, notHead Fact) {
						j, isSuc := d.ObtainAs[Nat](
							"the position is a successor",
							"∃j:num. i = suc(j)",
							By(Normalized, notHead, peano.Cases.At(i)))
						inTail := d.Have(
							"so j is a position of t",
							"j < list_length(t)",
							ByArith(bounded, isSuc, ListLengthDef))
						d.Do(isSuc.Rw())
						d.Show(
							"both sides read t at j, t standing in front of m on the left, and the hypothesis applies",
							Simp(Fwd(ListAppendDef), Fwd(NthTail)),
							By(ih.At(j), inTail))
					})
			})
	}),
})}

// NthAppendRight — position i of the back list sits at the length of the
// front plus i in the concatenation. By induction on l, with m and i
// fixed: with nil in front the position is 0 + i, which is i; with
// cons(h, t) in front it is suc(list_length(t) + i), and NthTail moves it
// to the same position of list_append(t, m), which the hypothesis reads.
var NthAppendRight = nthAppendRightThm{family.Add(registry.ProofEntry{
	Name: "NthAppendRight",
	Key:  "prop_ea268113a9f49bf3",
	Build: family.Theorem("∀l m:list(A). ∀i:num. "+
		"    list_nth(list_append(l, m), list_length(l) + i) = list_nth(m, i)",
		func(a *Argument, l, m *Expr[List[A]], i *Expr[Nat]) {
			a.Induct(l)
			a.Base(
				"nil in front leaves m, at position 0 + i, which is i",
				Simp(Fwd(ListAppendDef), Fwd(ListLengthDef), Fwd(nat_arith.AddLeftZeroClause)),
				Refl())
			a.Step(
				"a head in front moves the position up by one, and NthTail moves it back down to list_append(t, m)",
				func(c *Argument, ih Fact) {
					c.Show(
						"the position is suc(list_length(t) + i) of cons(h, list_append(t, m)), which the hypothesis reads",
						Simp(Fwd(ListAppendDef), Fwd(ListLengthDef), Fwd(nat_arith.AddLeftSucClause), Fwd(NthTail)),
						By(ih))
				})
		}),
})}

// MemberNth — the members are the elements at positions. By induction on
// l, x fixed: nil has no member and no position. At cons(h, t) a member
// is the head, at position 0, or a member of t, at some position j of t
// and so at position suc(j) of the list; and the element at a position
// is the head when the position is 0, and the element of t at position j
// when it is suc(j), a member of t by the hypothesis.
var MemberNth = memberNthThm{family.Add(registry.ProofEntry{
	Name: "MemberNth",
	Key:  "prop_c9b4f9e4591f9dbb",
	Build: family.Theorem("∀x:A. ∀l:list(A). "+
		"    list_member(x, l) ⇔ (∃i:num. i < list_length(l) ∧ list_nth(l, i) = x)",
		func(a *Argument, x *Expr[A], l *Expr[List[A]]) {
			a.Induct(l)
			a.Base(
				"the empty list has no member and no position",
				By(ListMemberDef, ListLengthDef, nat_order.LessThanZeroClause))
			a.Step(
				"at cons(h, t) position 0 holds the head, and position suc(j) what position j of t holds",
				func(b *Argument, ih Fact) {
					args := b.StepArgs("h", "t")
					h, t := ext.As[A](args[0]), ext.As[List[A]](args[1])
					b.Iff()
					b.Forward(
						"a member of cons(h, t) sits at a position",
						func(c *Argument, inList Fact) {
							c.Cases(c.Term("x = h"))
							c.When(
								"the head sits at position 0",
								func(d *Argument, isHead Fact) {
									d.Take(d.TermAs[Nat]("0"))
									d.Show(
										"position 0 holds h, and 0 is below the length suc(list_length(t))",
										By(Normalized, isHead, NthHead, ListLengthDef, nat_order.ZeroLessThanSuc))
								})
							c.Otherwise(
								"a member past the head sits at position suc(j), for j its position in t",
								func(d *Argument, notHead Fact) {
									_, at := d.ObtainAs[Nat](
										"past the head x is a member of t, so it sits at a position j of t",
										"∃j:num. j < list_length(t) ∧ list_nth(t, j) = x",
										By(ih, notHead, inList, ListMemberDef))
									d.Take(d.TermAs[Nat]("suc(j)"))
									d.Show(
										"position suc(j) of cons(h, t) is position j of t, and suc(j) is below suc(list_length(t))",
										ByArith(at, NthTail, ListLengthDef))
								})
						})
					b.Backward(
						"the element at a position of cons(h, t) is a member of it",
						func(c *Argument, witnessed Fact) {
							i, at := c.UnpackAs[Nat](witnessed, "i")
							c.Cases(c.Term("i = 0"))
							c.When(
								"position 0 holds the head",
								func(d *Argument, atHead Fact) {
									d.Do(atHead.Rw())
									d.Show(
										"x is h",
										By(at, NthHead, ListMemberDef))
								})
							c.Otherwise(
								"position suc(j) holds the element of t at position j",
								func(d *Argument, notHead Fact) {
									j, isSuc := d.ObtainAs[Nat](
										"the position is a successor",
										"∃j:num. i = suc(j)",
										By(Normalized, notHead, peano.Cases.At(i)))
									inTail := d.Have(
										"so x sits at position j of t",
										"j < list_length(t) ∧ list_nth(t, j) = x",
										ByArith(at, isSuc, NthTail.At(h, t, j), ListLengthDef))
									d.Show(
										"the hypothesis makes x a member of t, and so of cons(h, t)",
										By(ih, inTail, ListMemberDef))
								})
						})
				})
		}),
})}

// NthExtensionality — two lists of one length with the same element at
// every position are equal. By induction on l for every m. A list as long
// as nil is nil. A list as long as cons(h, t) is a cons(h₂, t₂) with t₂ as
// long as t; the two agree at position 0, so h = h₂, and position suc(i)
// of each is position i of its tail, so t and t₂ agree at every position
// of t and the hypothesis makes them equal.
var NthExtensionality = nthExtensionalityThm{family.Add(registry.ProofEntry{
	Name: "NthExtensionality",
	Key:  "prop_cb339535d0d144c9",
	Build: family.Theorem(Statement{
		Binders: "∀l m:list(A).",
		Hypotheses: []string{
			"list_length(l) = list_length(m)",
			"∀i:num. i < list_length(l) ⇒ list_nth(l, i) = list_nth(m, i)",
		},
		Conclusion: "l = m",
	}, func(a *Argument) {
		a.Induct("l")
		a.Base(
			"a list as long as nil is nil",
			func(b *Argument) {
				m := b.FixAs[List[A]]("m")
				given := b.Assume()
				b.Show(
					"m has length 0",
					By(Normalized, given, ListLengthDef, LengthEqNil.At(m)))
			})
		a.Step(
			"a list as long as cons(h, t) is a cons(h₂, t₂) agreeing with it at the head and along the tails",
			func(b *Argument, ih Fact) {
				b.StepArgs("h", "t")
				m := b.FixAs[List[A]]("m")
				given := b.Conjuncts(
					b.Assume(),
					"m is as long as cons(h, t)",
					"and agrees with it at every position")
				agree := given[1]
				_, t2, other := b.Obtain2As[A, List[A]](
					"so m is a head before a tail as long as t",
					"∃h₂:A. ∃t₂:list(A). m = cons(h₂, t₂) ∧ list_length(t₂) = list_length(t)",
					By(Normalized, given[0], ListLengthDef, LengthEqCons.At(m, b.TermAs[Nat]("list_length(t)"))))
				shape := b.Conjuncts(
					other,
					"m is cons(h₂, t₂)",
					"and t₂ is as long as t")
				b.Do(shape[0].Rw())
				heads := b.Have(
					"the heads agree, at position 0",
					"h = h₂",
					By(Normalized, agree.At(b.TermAs[Nat]("0")), ListLengthDef, nat_order.ZeroLessThanSuc, NthHead))
				tails := b.Have(
					"the tails agree at every position of t, one position along both lists",
					"∀i:num. i < list_length(t) ⇒ list_nth(t, i) = list_nth(t₂, i)",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("i")
						inTail := c.Assume()
						c.Show(
							"the lists agree at position suc(i), below suc(list_length(t))",
							ByArith(agree.At(c.TermAs[Nat]("suc(i)")), inTail, ListLengthDef, NthTail))
					}))
				b.Show(
					"the hypothesis makes the tails equal, and with the heads the lists",
					By(Normalized, ih.At(t2), shape[1], tails, heads, ConsInjective))
			})
	}),
})}

// TabulatedList — every sequence of n elements is the list of some list's
// positions. By induction on n for every f: nil tabulates any f at 0. At
// suc(n), a list l tabulating λi. f(suc(i)) at n gives cons(f(0), l), of
// length suc(n), whose position 0 holds f(0) and whose position suc(j)
// holds position j of l, which is f(suc(j)).
var TabulatedList = tabulatedListThm{family.Add(registry.ProofEntry{
	Name: "TabulatedList",
	Key:  "prop_7de35b7ff4dca5cf",
	Build: family.Theorem("∀f:(num → A). ∀n:num. ∃l:list(A). "+
		"    list_length(l) = n ∧ (∀i:num. i < n ⇒ list_nth(l, i) = f(i))",
		func(a *Argument) {
			a.Induct("n")
			a.Base(
				"the empty list has length 0 and no position",
				func(b *Argument) {
					b.FixAs[Fun[Nat, A]]("f")
					b.Take(b.TermAs[List[A]]("nil"))
					b.Show(
						"nil has length 0, and nothing is below 0",
						By(ListLengthDef, nat_order.LessThanZeroClause))
				})
			a.Step(
				"f(0) in front of a list tabulating f one place along tabulates f at suc(n)",
				func(b *Argument, ih Fact) {
					b.FixAs[Fun[Nat, A]]("f")
					_, shifted := b.ObtainAs[List[A]](
						"the hypothesis gives a list l tabulating λi. f(suc(i)) at n",
						"∃l:list(A). list_length(l) = n ∧ (∀i:num. i < n ⇒ list_nth(l, i) = f(suc(i)))",
						By(ih.At(b.TermAs[Fun[Nat, A]]("λi:num. f(suc(i))"))))
					tabulates := b.Conjuncts(
						shifted,
						"l has length n",
						"and position i of l holds f(suc(i))")
					b.Take(b.TermAs[List[A]]("cons(f(0), l)"))
					positions := b.Have(
						"position i of cons(f(0), l) holds f(i) at every i below suc(n)",
						"∀i:num. i < suc(n) ⇒ list_nth(cons(f(0), l), i) = f(i)",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							bounded := c.Assume()
							c.Cases(c.Term("i = 0"))
							c.When(
								"position 0 holds the head f(0)",
								func(d *Argument, atHead Fact) {
									d.Do(atHead.Rw())
									d.Show(
										"the head is at position 0",
										Cite(NthHead))
								})
							c.Otherwise(
								"position suc(j) holds position j of l, which is f(suc(j))",
								func(d *Argument, notHead Fact) {
									j, isSuc := d.ObtainAs[Nat](
										"the position is a successor",
										"∃j:num. i = suc(j)",
										By(Normalized, notHead, peano.Cases.At(i)))
									inRange := d.Have(
										"so j is below n",
										"j < n",
										ByArith(bounded, isSuc))
									d.Do(isSuc.Rw())
									d.Show(
										"NthTail moves the position to l, where it holds f(suc(j))",
										By(tabulates[1].At(j), inRange, NthTail))
								})
						}))
					b.Show(
						"cons(f(0), l) has length suc(n), and holds f at its positions",
						By(Normalized, tabulates[0], positions, ListLengthDef))
				})
		}),
})}
