// cauchy.go — Cauchy's theorem by McKay's counting, the residues mod p
// rotating the p-tuples of product one.

package group_action

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/cyclic_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The residues mod n
// ---------------------------------------------------------------------------

// ResidueAddGroupOn — for n > 0 the residues below n form a group under
// addition mod n, with 0 as identity and n − i reduced as the inverse of
// i. A reduced sum lies below n, addition mod n associates
// (nat_div_mod.ModAddAssoc), 0 + i reduces to i for i below n, and
// (n − i) + i is n, which reduces to 0.
var ResidueAddGroupOn = residueAddGroupOnThm{family.Add(registry.ProofEntry{
	Name: "ResidueAddGroupOn",
	Key:  "prop_7cdcd473a85b817c",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"0 < n",
		},
		Conclusion: "group_on(«residues»(n))",
	},
		func(a *Argument, n *Expr[Nat], positive Fact) {
			a.Do(Unfold(group.GroupOn), SplitConjAll(
				Case(
					"0 is a residue",
					By(positive)),
				Case(
					"a reduced sum is a residue",
					By(positive, nat_order.PosIffNonzero.At(n), nat_div_mod.Division)),
				Case(
					"a reduced n − x is a residue",
					By(positive, nat_order.PosIffNonzero.At(n), nat_div_mod.Division)),
				Case(
					"addition mod n associates",
					By(nat_div_mod.ModAddAssoc)),
				Case(
					"0 + x reduces to x for a residue x",
					By(nat_div_mod.ModLessThan, nat_arith.AddLeftZeroClause)),
				Case(
					"n − x reduced, added to x, reduces to 0: (n − x) + x is n",
					Derive(func(b *Argument) {
						x := b.FixAs[Nat]("x")
						residue := b.Assume()
						difference := b.TermAs[Nat]("n - x")
						refill := b.Have(
							"x lies below n, so n − x + x is n",
							"n - x + x = n",
							ByArith(residue))
						b.Show(
							"reducing n − x first changes no remainder, and n reduces to 0",
							By(refill, nat_div_mod.ModAddModLeft.At(difference, x, n), nat_div_mod.ModRefl.At(n)))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Lists
// ---------------------------------------------------------------------------

// nthExtensionalityAtLength — two lists of length n with one entry at every
// position below n are one list.
var nthExtensionalityAtLength = nthExtensionalityAtLengthThm{family.Add(registry.ProofEntry{
	Name: "nthExtensionalityAtLength",
	Key:  "prop_2ca3b41c011c2e3d",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀l m:list(A).",
		Hypotheses: []string{
			"list_length(l) = n",
			"list_length(m) = n",
			"∀i:num. i < n ⇒ list_nth(l, i) = list_nth(m, i)",
		},
		Conclusion: "l = m",
	},
		func(a *Argument, n *Expr[Nat], l, m *Expr[list.List[A]], lLength, mLength, agree Fact) {
			a.Show(
				"positions below n are the positions of l",
				By(lLength, mLength, agree, list.NthExtensionality.At(l, m)))
		}),
})}

// ---------------------------------------------------------------------------
// Rotating lists
// ---------------------------------------------------------------------------

// RotatedLength — a list rotated by k at length n has length n: a list
// of length n holding at each position i the entry at i + k mod n exists
// (list.TabulatedList), and the rotation chooses one.
var RotatedLength = rotatedLengthThm{family.Add(registry.ProofEntry{
	Name: "RotatedLength",
	Key:  "prop_560f87383cbcbb6b",
	Build: family.Theorem(Statement{
		Binders:    "∀n k:num. ∀l:list(A).",
		Conclusion: "list_length(«rotate»(n, k, l)) = n",
	},
		func(a *Argument, n, k *Expr[Nat], l *Expr[list.List[A]]) {
			a.Show(
				"the rotation chooses a list of length n with the shifted entries, and tabulating them gives one",
				By(list.TabulatedList.At(a.TermAs[Fun[Nat, A]]("λi:num. list_nth(l, rem(i + k, n))"), n)))
		}),
})}

// RotatedEntry — the list l rotated by k holds at each position j below n
// the entry of l at position j + k mod n: the rotation chooses a list
// with those entries, and one exists (list.TabulatedList).
var RotatedEntry = rotatedEntryThm{family.Add(registry.ProofEntry{
	Name: "RotatedEntry",
	Key:  "prop_f16b50e4c6a48fbb",
	Build: family.Theorem(Statement{
		Binders: "∀n k:num. ∀l:list(A). ∀j:num.",
		Hypotheses: []string{
			"j < n",
		},
		Conclusion: "list_nth(«rotate»(n, k, l), j) = list_nth(l, rem(j + k, n))",
	},
		func(a *Argument, n, k *Expr[Nat], l *Expr[list.List[A]], j *Expr[Nat], below Fact) {
			a.Show(
				"the rotation chooses a list holding at j, below n, "+
					"the entry of l at j + k mod n, and tabulating gives one",
				By(below, list.TabulatedList.At(a.TermAs[Fun[Nat, A]]("λi:num. list_nth(l, rem(i + k, n))"), n)))
		}),
})}

// RotationFixesConstant — rotating a list of length n all of whose entries
// are x gives the list back: each entry of the rotated list is an entry of
// the list, so x.
var RotationFixesConstant = rotationFixesConstantThm{family.Add(registry.ProofEntry{
	Name: "RotationFixesConstant",
	Key:  "prop_73b3adf3fa283ccc",
	Build: family.Theorem(Statement{
		Binders: "∀n k:num. ∀x:A. ∀l:list(A).",
		Hypotheses: []string{
			"list_length(l) = n",
			"∀i:num. i < n ⇒ list_nth(l, i) = x",
		},
		Conclusion: "«rotate»(n, k, l) = l",
	},
		func(a *Argument, n, k *Expr[Nat], x *Expr[A], l *Expr[list.List[A]], length, constant Fact) {
			sameEntries := a.Have(
				"each entry of the rotated list is an entry of l, so x, the entry of l at the same position",
				"∀i:num. i < n ⇒ list_nth(«rotate»(n, k, l), i) = list_nth(l, i)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					position := b.Assume()
					b.Show(
						"position i of it is position i + k mod n of l, below n as n is not 0",
						By(
							position,
							nat_order.LessThanZeroClause.At(i),
							nat_div_mod.Division.At(b.TermAs[Nat]("i + k"), n),
							constant.At(b.TermAs[Nat]("rem(i + k, n)")),
							constant.At(i),
							RotatedEntry.At(n, k, l, i)))
				}))
			a.Show(
				"two lists of length n with the same entries are one list",
				By(
					length,
					sameEntries,
					RotatedLength.At(n, k, l),
					nthExtensionalityAtLength.At(n, a.TermAs[list.List[A]]("«rotate»(n, k, l)"), l)))
		}),
})}

// RotationFixedIsConstant — a list every rotation fixes holds its first
// entry at every position: position j is position 0 of the list rotated by
// j.
var RotationFixedIsConstant = rotationFixedIsConstantThm{family.Add(registry.ProofEntry{
	Name: "RotationFixedIsConstant",
	Key:  "prop_22c1d0c03fc8467c",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀l:list(A). ∀j:num.",
		Hypotheses: []string{
			"∀k:num. k < n ⇒ «rotate»(n, k, l) = l",
			"j < n",
		},
		Conclusion: "list_nth(l, j) = list_nth(l, 0)",
	},
		func(a *Argument, n *Expr[Nat], l *Expr[list.List[A]], j *Expr[Nat], fixed, position Fact) {
			positive := a.Have(
				"n is positive, j lying below it",
				"0 < n",
				ByArith(position))
			a.Show(
				"position j of l is position 0 of l rotated by j",
				CalcEq(
					Leg(
						a.Term("list_nth(l, rem(0 + j, n))"),
						"j is 0 + j mod n, j being below n",
						By(Normalized, position, nat_div_mod.ModLessThan.At(j, n), nat_arith.Add)),
					Leg(
						a.Term("list_nth(«rotate»(n, j, l), 0)"),
						"l rotated by j holds at 0 the entry of l at 0 + j mod n",
						By(positive, RotatedEntry.At(n, j, l, a.TermAs[Nat]("0")))),
					FinalLeg(
						"and l rotated by j is l",
						GroupPremises(position, fixed.At(j)).Rw(),
						Basic())))
		}),
})}

// RotationAction — for n > 0 the residues mod n act on the lists of length
// n over G.carrier whose product is G.one, k moving each entry k places
// towards the front, the first ones round to the end. Rotating by k reads
// position i of the rotated list at position i + k mod n of the list
// (RotatedEntry, RotatedLength), so
// rotating by 0 changes nothing and rotating by k and then by j is
// rotating by j + k mod n (nat_div_mod.ModAddAssoc), two lists of length n
// with one entry at every position being one list. Rotating by 1 moves the
// head to the end, which keeps the product G.one
// (group.RotateProductOne), and rotating by k + 1 is rotating by k and
// then by 1.
var RotationAction = rotationActionThm{family.Add(registry.ProofEntry{
	Name: "RotationAction",
	Key:  "prop_256a12f26266d97e",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"0 < n",
		},
		Conclusion: "group_action(«residues»(n), «tuples»(n), «rotate»(n))",
	},
		func(a *Argument, grp group.GroupFact[on.G], n *Expr[Nat], positive Fact) {
			carrier := a.TermAs[Set[A]]("G.carrier")
			zero, one := a.TermAs[Nat]("0"), a.TermAs[Nat]("1")
			rotZero := a.Have(
				"rotating by 0 changes no list of length n",
				"∀l:list(A). list_length(l) = n ⇒ «rotate»(n, 0, l) = l",
				Derive(func(b *Argument) {
					l := b.FixAs[list.List[A]]("l")
					length := b.Assume()
					same := b.Have(
						"at a position i below n the rotated list holds the entry of l at i + 0 mod n, which is i",
						"∀i:num. i < n ⇒ list_nth(«rotate»(n, 0, l), i) = list_nth(l, i)",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							position := c.Assume()
							c.Show(
								"i + 0 reduces to i",
								CalcEq(
									Leg(
										c.Term("list_nth(l, rem(i + 0, n))"),
										"the rotated list holds the entry of l at i + 0 mod n",
										By(position, RotatedEntry.At(n, zero, l, i))),
									FinalLeg(
										"i + 0 is i, below n",
										By(position, nat_div_mod.ModLessThan.At(i, n), nat_arith.AddZero))))
						}))
					b.Show(
						"so the rotated list is l",
						By(
							length,
							same,
							RotatedLength.At(n, zero, l),
							nthExtensionalityAtLength.At(n, b.TermAs[list.List[A]]("«rotate»(n, 0, l)"), l)))
				}))
			rotCompose := a.Have(
				"rotating by k and then by j is rotating by j + k mod n",
				"∀j k:num. ∀l:list(A). «rotate»(n, rem(j + k, n), l) = «rotate»(n, j, «rotate»(n, k, l))",
				Derive(func(b *Argument) {
					j, k := b.FixAs[Nat]("j"), b.FixAs[Nat]("k")
					l := b.FixAs[list.List[A]]("l")
					sum := b.TermAs[Nat]("rem(j + k, n)")
					once := b.TermAs[list.List[A]]("«rotate»(n, k, l)")
					same := b.Have(
						"at i both hold the entry of l at i + (j + k) mod n",
						Statement{
							Binders: "∀i:num.",
							Hypotheses: []string{
								"i < n",
							},
							Conclusion: "list_nth(«rotate»(n, rem(j + k, n), l), i) = " +
								"list_nth(«rotate»(n, j, «rotate»(n, k, l)), i)",
						},
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							position := c.Assume()
							c.Show(
								"the two positions agree mod n",
								CalcEq(
									Leg(
										c.Term("list_nth(l, rem(i + rem(j + k, n), n))"),
										"rotating by (j + k) mod n reads l at i + (j + k) mod n",
										By(position, RotatedEntry.At(n, sum, l, i))),
									Leg(
										c.Term("list_nth(l, rem(rem(i + j, n) + k, n))"),
										"addition mod n associates",
										By(nat_div_mod.ModAddAssoc.At(i, j, k, n))),
									Leg(
										c.Term("list_nth(«rotate»(n, k, l), rem(i + j, n))"),
										"which is what rotating by k holds at i + j mod n, a position below n",
										By(
											positive,
											nat_order.PosIffNonzero.At(n),
											nat_div_mod.Division.At(c.TermAs[Nat]("i + j"), n),
											RotatedEntry.At(n, k, l, c.TermAs[Nat]("rem(i + j, n)")))),
									FinalLeg(
										"which is what rotating that by j holds at i",
										By(position, RotatedEntry.At(n, j, once, i)))))
						}))
					b.Show(
						"so the two rotations agree",
						By(
							same,
							RotatedLength.At(n, sum, l),
							RotatedLength.At(n, j, once),
							nthExtensionalityAtLength.At(
								n,
								b.TermAs[list.List[A]]("«rotate»(n, rem(j + k, n), l)"),
								b.TermAs[list.List[A]]("«rotate»(n, j, «rotate»(n, k, l))"))))
				}))
			rotOne := a.Have(
				"rotating by 1 moves the head of a list of length n to its end",
				Statement{
					Binders: "∀h:A. ∀t:list(A).",
					Hypotheses: []string{
						"list_length(t) + 1 = n",
					},
					Conclusion: "«rotate»(n, 1, cons(h, t)) = list_append(t, cons(h, nil))",
				},
				Derive(func(b *Argument) {
					h, t := b.FixAs[A]("h"), b.FixAs[list.List[A]]("t")
					length := b.Assume()
					whole := b.TermAs[list.List[A]]("cons(h, t)")
					single := b.TermAs[list.List[A]]("cons(h, nil)")
					same := b.Have(
						"at i the rotated list holds the entry of cons(h, t) "+
							"at i + 1 mod n: the tail's at i, or the head at the end",
						Statement{
							Binders: "∀i:num.",
							Hypotheses: []string{
								"i < n",
							},
							Conclusion: "list_nth(«rotate»(n, 1, cons(h, t)), i) = list_nth(list_append(t, cons(h, nil)), i)",
						},
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							position := c.Assume()
							c.Cases(c.Term("i + 1 < n"))
							c.When(
								"before the end the entry is the tail's at i",
								func(d *Argument, inside Fact) {
									short := d.Have(
										"i lies below the length of t",
										"i < list_length(t)",
										ByArith(inside, length))
									d.Show(
										"i + 1 reduces to itself, and position suc(i) of cons(h, t) is position i of t",
										CalcEq(
											Leg(
												d.Term("list_nth(cons(h, t), rem(i + 1, n))"),
												"rotating by 1 reads cons(h, t) at i + 1 mod n",
												By(position, RotatedEntry.At(n, one, whole, i))),
											Leg(
												d.Term("list_nth(cons(h, t), suc(i))"),
												"i + 1 lies below n, so it is its own remainder",
												By(inside, nat_div_mod.ModLessThan.At(d.TermAs[Nat]("i + 1"), n), nat_arith.Add1)),
											Leg(
												d.Term("list_nth(t, i)"),
												"past the head, position suc(i) is position i of t",
												By(list.NthTail.At(h, t, i))),
											FinalLeg(
												"which t keeps in front of h",
												By(short, list.NthAppendLeft.At(t, single, i)))))
								})
							c.Otherwise(
								"at the end the entry is the head",
								func(d *Argument, last Fact) {
									full := d.Have(
										"i + 1 is n",
										"i + 1 = n",
										ByArith(last, position))
									end := d.Have(
										"so i is the length of t",
										"i = list_length(t) + 0",
										ByArith(full, length))
									d.Show(
										"n reduces to 0, where cons(h, t) holds h, and the moved list holds h right after t",
										CalcEq(
											Leg(
												d.Term("list_nth(cons(h, t), rem(i + 1, n))"),
												"rotating by 1 reads cons(h, t) at i + 1 mod n",
												By(position, RotatedEntry.At(n, one, whole, i))),
											Leg(
												d.Term("h"),
												"i + 1 is n, which reduces to 0, the head's position",
												By(Normalized, full, nat_div_mod.ModRefl.At(n), list.NthHead.At(h, t))),
											FinalLeg(
												"position list_length(t) of the moved list is position 0 of cons(h, nil)",
												By(
													Normalized,
													end,
													list.NthAppendRight.At(t, single, zero),
													list.NthHead.At(h, d.TermAs[list.List[A]]("nil"))))))
								})
						}))
					moved := b.Have(
						"the moved list has length n",
						"list_length(list_append(t, cons(h, nil))) = n",
						Simp(Fwd(list.LengthAppend), Fwd(list.ListLengthDef)),
						ByArith(length))
					b.Show(
						"so the rotated list is the moved one",
						By(
							same,
							moved,
							RotatedLength.At(n, one, whole),
							nthExtensionalityAtLength.At(
								n,
								b.TermAs[list.List[A]]("«rotate»(n, 1, cons(h, t))"),
								b.TermAs[list.List[A]]("list_append(t, cons(h, nil))"))))
				}))
			rotOneIn := a.Have(
				"rotating by 1 keeps the lists of length n over G.carrier of product G.one",
				"∀l:list(A). l ∈ «tuples»(n) ⇒ «rotate»(n, 1, l) ∈ «tuples»(n)",
				Derive(func(b *Argument) {
					l := b.FixAs[list.List[A]]("l")
					inTuples := b.Assume()
					parts := b.Conjuncts(
						inTuples,
						"l has length n",
						"its entries lie in G.carrier",
						"its product is G.one")
					longer := b.Have(
						"n is positive, so l has length n − 1 + 1",
						"list_length(l) = suc(n - 1)",
						ByArith(parts[0], positive))
					h, t, split := b.Unpack2As[A, list.List[A]](
						GroupPremises(longer, parts[1], list.LengthEqConsOver.At(carrier, b.TermAs[Nat]("n - 1"), l)))
					pieces := b.Conjuncts(
						split,
						"l is cons(h, t)",
						"t has length n − 1",
						"the head lies in G.carrier",
						"and so do the tail's entries")
					tailLength := b.Have(
						"so the tail's length plus 1 is n",
						"list_length(t) + 1 = n",
						ByArith(pieces[1], positive))
					product := b.Have(
						"cons(h, t) has product G.one",
						"list_fold(G.mul, cons(h, t), G.one) = G.one",
						By(Normalized, pieces[0], parts[2]))
					movedLength := b.Have(
						"t with h at the end has length n",
						"list_length(list_append(t, cons(h, nil))) = n",
						Simp(Fwd(list.LengthAppend), Fwd(list.ListLengthDef)),
						ByArith(tailLength))
					movedEntries := b.Have(
						"its entries are h and the tail's",
						"∀y:A. list_member(y, list_append(t, cons(h, nil))) ⇒ y ∈ G.carrier",
						By(pieces[2], pieces[3], list.MemberAppend, list.ListMemberDef))
					movedProduct := b.Have(
						"and its product is G.one",
						"list_fold(G.mul, list_append(t, cons(h, nil)), G.one) = G.one",
						By(pieces[2], pieces[3], product, group.RotateProductOne.Read(grp)))
					b.Do(pieces[0].Rw(), GroupPremises(tailLength, rotOne.At(h, t)).Rw())
					b.Show(
						"so the rotated list, t with h at the end, is one of the lists",
						By(movedLength, movedEntries, movedProduct))
				}))
			rotClosed := a.Have(
				"rotating by a residue keeps the lists of length n over G.carrier of product G.one",
				"∀k:num. k < n ⇒ ∀l:list(A). l ∈ «tuples»(n) ⇒ «rotate»(n, k, l) ∈ «tuples»(n)",
				Derive(func(b *Argument) {
					b.Induct("k")
					b.Base(
						"rotating by 0 changes nothing",
						func(c *Argument) {
							// 0 < n is resident already: the strip only opens the goal.
							c.Do(StripImp())
							l := c.FixAs[list.List[A]]("l")
							inTuples := c.Assume()
							parts := c.Conjuncts(
								inTuples,
								"l has length n",
								"its entries lie in G.carrier",
								"its product is G.one")
							c.Do(GroupPremises(parts[0], rotZero.At(l)).Rw())
							c.Show(
								"l is one of the lists",
								By(inTuples))
						})
					b.Step(
						"rotating by k + 1 is rotating by k and then by 1",
						func(c *Argument, ih Fact) {
							k := c.TermAs[Nat]("k")
							oneMore := c.Assume()
							l := c.FixAs[list.List[A]]("l")
							inTuples := c.Assume()
							reduced := c.Have(
								"1 + k lies below n, so it is its own remainder, k + 1",
								"rem(1 + k, n) = suc(k)",
								By(
									Normalized,
									oneMore,
									nat_div_mod.ModLessThan.At(c.TermAs[Nat]("1 + k"), n),
									nat_arith.Add1,
									nat_arith.AddSym))
							split := c.Have(
								"rotating by k + 1 is rotating by k and then by 1",
								"«rotate»(n, suc(k), l) = «rotate»(n, 1, «rotate»(n, k, l))",
								reduced.RwRev(),
								By(rotCompose.At(one, k, l)))
							earlier := c.Have(
								"k lies below n, so rotating by k keeps l among the lists",
								"«rotate»(n, k, l) ∈ «tuples»(n)",
								By(
									c.Have(
										"k lies below n",
										"k < n",
										ByArith(oneMore)),
									inTuples,
									ih))
							c.Show(
								"and rotating by 1 keeps it there",
								split.Rw(),
								By(earlier, rotOneIn))
						})
				}))
			a.Do(Unfold(GroupAction), SplitConjAll(
				Case(
					"the residues mod n form a group",
					By(positive, ResidueAddGroupOn)),
				Case(
					"rotating by a residue keeps the lists",
					By(rotClosed)),
				Case(
					"rotating by 0 changes nothing",
					By(rotZero)),
				Case(
					"rotating by a reduced sum is rotating by each in turn",
					By(rotCompose)),
			))
		}),
})}

// ProductOneListsCount — the lists of length n + 1 over the carrier of a
// finite group whose product is G.one number card(G.carrier) ^ n: such a
// list is a list of length n over G.carrier with the inverse of its
// product put in front, and different lists complete to different lists,
// each keeping its list as the tail; there are card(G.carrier) ^ n lists
// of length n (list.ListsCount).
var ProductOneListsCount = productOneListsCountThm{family.Add(registry.ProofEntry{
	Name: "ProductOneListsCount",
	Key:  "prop_2ec35f725fc58d34",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"finite(G.carrier)",
		},
		Conclusion: "has_size(«tuples»(suc(n)), card(G.carrier) ^ n)",
		Abbrev: Abbrev{
			{Name: "carrierLists", Text: "λn:num. " +
				"    {l:list(A) | list_length(l) = n ∧ (∀y:A. list_member(y, l) ⇒ y ∈ G.carrier)}"},
			{Name: "complete", Text: "λm:list(A). cons(G.inv(list_fold(G.mul, m, G.one)), m)"},
		},
	},
		func(a *Argument, grp group.GroupFact[on.G], n *Expr[Nat], finite Fact) {
			count := a.Have(
				"the lists of length n over G.carrier number card(G.carrier) ^ n",
				"has_size(«carrierLists»(n), card(G.carrier) ^ n)",
				By(finite, list.ListsCount))
			completes := a.Have(
				"a list of length n + 1 over G.carrier has product G.one exactly "+
					"when it is a list of length n completed by the inverse of its product",
				"∀l:list(A). l ∈ «tuples»(suc(n)) ⇔ l ∈ image(«complete», «carrierLists»(n))",
				Derive(func(b *Argument) {
					l := b.FixAs[list.List[A]]("l")
					b.Iff()
					b.Forward(
						"the head of such a list is the inverse of the product of its tail",
						func(c *Argument, inTuples Fact) {
							parts := c.Conjuncts(
								inTuples,
								"l has length n + 1",
								"its entries lie in G.carrier",
								"its product is G.one")
							h, t, split := c.Unpack2As[A, list.List[A]](
								GroupPremises(parts[0], parts[1], list.LengthEqConsOver.At(c.TermAs[Set[A]]("G.carrier"), n, l)))
							pieces := c.Conjuncts(
								split,
								"l is cons(h, t)",
								"t has length n",
								"the head lies in G.carrier",
								"and so do the tail's entries")
							hm := c.MemberOf[on.G](h, pieces[2])
							tm := c.MemberOf[on.G](
								c.TermAs[A]("list_fold(G.mul, t, G.one)"),
								GroupPremises(pieces[3], group.FoldIn.Read(grp).At(t)))
							inverse := c.Have(
								"h times the tail's product is G.one, so h is its inverse",
								"h = G.inv(list_fold(G.mul, t, G.one))",
								By(pieces[0], parts[2], list.ListFoldDef, group.InvUniqueOn.Read(grp).At(hm, tm)))
							c.Show(
								"so l is the tail completed",
								BySets(pieces[0], pieces[1], pieces[3], inverse))
						})
					b.Backward(
						"a list of length n completed by the inverse of its product has product G.one",
						func(c *Argument, completed Fact) {
							m, built := c.ObtainAs[list.List[A]](
								"l is some list m of length n over G.carrier, completed",
								"∃m:list(A). l = cons(G.inv(list_fold(G.mul, m, G.one)), m) ∧ m ∈ «carrierLists»(n)",
								By(completed, set_basic.InImage))
							parts := c.Conjuncts(
								built,
								"l is m completed",
								"m is a list of length n over G.carrier")
							pieces := c.Conjuncts(
								parts[1],
								"m has length n",
								"its entries lie in G.carrier")
							product := c.MemberOf[on.G](
								c.TermAs[A]("list_fold(G.mul, m, G.one)"),
								GroupPremises(pieces[1], group.FoldIn.Read(grp).At(m)))
							length := c.Have(
								"l has length n + 1",
								"list_length(l) = suc(n)",
								By(parts[0], pieces[0], list.ListLengthDef))
							entries := c.Have(
								"its entries lie in G.carrier, the head being the inverse of an element",
								"∀y:A. list_member(y, l) ⇒ y ∈ G.carrier",
								By(parts[0], pieces[1], list.ListMemberDef, group.InvIn.Read(grp).At(product)))
							one := c.Have(
								"its product is the inverse of m's product times m's product",
								"list_fold(G.mul, l, G.one) = G.one",
								By(parts[0], list.ListFoldDef, group.LeftInverseOn.Read(grp).At(product)))
							c.Show(
								"so l is a list of length n + 1 over G.carrier with product G.one",
								By(length, entries, one))
						})
				}))
			images := a.Have(
				"so those lists are the completed lists of length n",
				"«tuples»(suc(n)) = image(«complete», «carrierLists»(n))",
				By(completes, set_basic.Extension))
			separates := a.Have(
				"completing keeps the list as the tail, so it separates the lists",
				"injective_on(«carrierLists»(n), «complete»)",
				Unfold(functions.InjectiveOnDef),
				By(list.ConsInjective))
			a.Show(
				"so there are as many as lists of length n",
				images.Rw(),
				By(separates, count, cardinality.HasSizeImageInj))
		}),
})}

// ---------------------------------------------------------------------------
// Cauchy's theorem
// ---------------------------------------------------------------------------

// Cauchy — a finite group whose order a prime p divides has an element of
// order p: p divides the number of p-tuples of product one that every
// rotation fixes, and the tuple of ones is one of them, so another is
// constant at some x ≠ G.one, whose p-th power is G.one.
var Cauchy = cauchyThm{family.Add(registry.ProofEntry{
	Name: "Cauchy",
	Key:  "prop_7b3450f1790ff39c",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"finite(G.carrier)",
			"nat_prime(p)",
			"p ∣ card(G.carrier)",
		},
		Conclusion: "∃x:A. x ∈ G.carrier ∧ group_element_order(G, x) = p",
		Abbrev: Abbrev{
			{Name: "fixed", Text: "λn:num. " +
				"    {l:list(A) | l ∈ «tuples»(n) ∧ (∀k:num. k < n ⇒ «rotate»(n, k, l) = l)}"},
		},
	},
		func(a *Argument, grp group.GroupFact[on.G], p *Expr[Nat], finite, prime, divides Fact) {
			mul, one := a.TermAs[Fun2[A, A, A]]("G.mul"), a.TermAs[A]("G.one")
			atLeastTwo := a.Have(
				"a prime is at least 2",
				"2 ≤ p",
				By(prime, nat_prime.PrimeAtLeastTwo.At(p)))
			positive := a.Have(
				"so p is positive",
				"0 < p",
				ByArith(atLeastTwo))
			predecessor := a.Have(
				"p is one more than p − 1",
				"suc(p - 1) = p",
				ByArith(positive))
			counted := a.Have(
				"the tuples number card(G.carrier) ^ (p − 1)",
				"has_size(«tuples»(p), card(G.carrier) ^ (p - 1))",
				By(predecessor, finite, ProductOneListsCount.Read(grp).At(a.TermAs[Nat]("p - 1"))))
			tuplesDivisible := a.Have(
				"p divides card(G.carrier), so it divides card(G.carrier) ^ (p − 1), the number of tuples",
				"p ∣ card(«tuples»(p))",
				Derive(func(b *Argument) {
					shift := b.Have(
						"p − 1 is one more than p − 2",
						"p - 1 = suc(p - 2)",
						ByArith(atLeastTwo))
					power := b.Have(
						"card(G.carrier) ^ (p − 1) is a multiple of card(G.carrier)",
						"p ∣ card(G.carrier) ^ (p - 1)",
						By(
							shift,
							divides,
							nat_arith.NatPow,
							nat_divides.DividesMul.At(
								p,
								b.TermAs[Nat]("card(G.carrier)"),
								b.TermAs[Nat]("card(G.carrier) ^ (p - 2)"))))
					b.Show(
						"and it is the number of tuples",
						By(
							power,
							counted,
							cardinality.HasSizeDef.At(
								b.TermAs[Set[list.List[A]]]("«tuples»(p)"),
								b.TermAs[Nat]("card(G.carrier) ^ (p - 1)"))))
				}))
			congruent := a.Have(
				"the residues mod p, a group of prime order p, rotate the "+
					"tuples, so mod p the tuples number as many as the rotations fix",
				"card(«tuples»(p)) ≡ card(«fixed»(p)) (mod p)",
				Derive(func(b *Argument) {
					rotation := b.Have(
						"the residues mod p act by rotation on the p-tuples with product G.one",
						"group_action(«residues»(p), «tuples»(p), «rotate»(p))",
						By(positive, RotationAction.Read(grp).At(p)))
					tuplesFinite := b.Have(
						"the tuples are finitely many",
						"finite(«tuples»(p))",
						By(counted, cardinality.HasSizeDef))
					residues := b.Have(
						"there are p residues mod p",
						"finite({i:num | i < p}) ∧ card({i:num | i < p}) = p",
						By(num_segment.HasSizeBelowStrict.At(p), cardinality.HasSizeDef))
					pGroup := b.Have(
						"so the residues form a p-group, a finite group of order p = p ^ 1",
						"p_group(«residues»(p), p)",
						Simp(Fwd(finite_group.PGroupDef)),
						By(positive, residues, nat_arith.PowOne.At(p), ResidueAddGroupOn.At(p)))
					b.Show(
						"a p-group fixes, mod p, as many points as it acts on",
						By(tuplesFinite, prime, pGroup, PrimePowerFixedPoints.Read(rotation).At(p)))
				}))
			tupleCount, fixedCount := a.TermAs[Nat]("card(«tuples»(p))"), a.TermAs[Nat]("card(«fixed»(p))")
			fixedDivisible := a.Have(
				"so p divides the number of tuples the rotations fix, which has the same remainder",
				"p ∣ card(«fixed»(p))",
				By(
					tuplesDivisible,
					congruent,
					nat_congruence.CongDef.At(tupleCount, fixedCount, p),
					nat_divides.DividesMod.At(p, tupleCount),
					nat_divides.DividesMod.At(p, fixedCount)))
			e, ones := a.ObtainAs[list.List[A]](
				"take the tuple e of p entries G.one",
				"∃e:list(A). list_length(e) = p ∧ (∀i:num. i < p ⇒ list_nth(e, i) = G.one)",
				By(list.TabulatedList.At(a.TermAs[Fun[Nat, A]]("λi:num. G.one"), p)))
			onesParts := a.Conjuncts(
				ones,
				"e has length p",
				"its entries are G.one")
			onesFixed := a.Have(
				"e is a tuple every rotation fixes",
				"e ∈ «fixed»(p)",
				Derive(func(b *Argument) {
					entries := b.Have(
						"every member of e is G.one",
						"∀y:A. list_member(y, e) ⇒ y = G.one",
						By(onesParts[0], onesParts[1], list.MemberNth))
					product := b.Have(
						"the product of e is G.one ^ p, which is G.one",
						"list_fold(G.mul, e, G.one) = G.one",
						By(entries, onesParts[0], list.ConstantListFold.At(mul, one, one, e), group.OnePow.Read(grp).At(p)))
					rotated := b.Have(
						"rotating e, a list of entries G.one, gives e back",
						"∀k:num. «rotate»(p, k, e) = e",
						b.ForEach(func(k *Expr[Nat]) Action {
							return By(onesParts[0], onesParts[1], RotationFixesConstant.At(p, k, one, e))
						}))
					b.Show(
						"so e, of length p over G.carrier with product G.one, is one of them",
						By(onesParts[0], entries, product, rotated, group.OneIn.Read(grp)))
				}))
			singletonCount := a.Have(
				"p is at least 2, so it does not divide 1: there is not just one fixed tuple",
				"¬(card(«fixed»(p)) = 1)",
				ByArith(fixedDivisible, atLeastTwo, nat_divides.DividesOne.At(p)))
			notOnlyOnes := a.Have(
				"so the fixed tuples are not e alone",
				"¬(«fixed»(p) = {e})",
				By(singletonCount, cardinality.CardSing.At(e)))
			l, other := a.ObtainAs[list.List[A]](
				"take a fixed tuple l other than e",
				"∃l:list(A). l ∈ «fixed»(p) ∧ ¬(l = e)",
				// Only e ∈ F and F ≠ {e} matter here, not what F's tuples are, so F stays one set.
				BySets(DenotedAs("F", a.Term("«fixed»(p)")), notOnlyOnes, onesFixed))
			otherParts := a.Conjuncts(
				other,
				"l is a tuple every rotation fixes",
				"l is not e")
			fixedParts := a.Conjuncts(
				otherParts[0],
				"l is a tuple",
				"every rotation fixes l")
			lParts := a.Conjuncts(
				fixedParts[0],
				"l has length p",
				"its entries lie in G.carrier",
				"its product is G.one")
			lConstant := a.Have(
				"a list every rotation fixes holds its first entry everywhere",
				"∀i:num. i < p ⇒ list_nth(l, i) = list_nth(l, 0)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return By(fixedParts[1], RotationFixedIsConstant.At(p, l, i))
				}))
			x, xDef := a.LetAs[A]("x", "list_nth(l, 0)")
			notOne := a.Have(
				"x is not G.one, l not being e",
				"¬(x = G.one)",
				By(
					Normalized,
					xDef,
					otherParts[1],
					lConstant,
					lParts[0],
					onesParts[0],
					onesParts[1],
					nthExtensionalityAtLength.At(p, l, e)))
			allX := a.Have(
				"every member of l is x",
				"∀y:A. list_member(y, l) ⇒ y = x",
				By(xDef, lConstant, lParts[0], list.MemberNth))
			xIn := a.Have(
				"x is the entry of l at position 0, a position as p ≥ 2, so a member of l, which lies in G.carrier",
				"x ∈ G.carrier",
				ByArith(xDef, atLeastTwo, lParts[0], lParts[1], list.MemberNth.At(x, l)))
			xm := a.MemberOf[on.G](x, xIn)
			xPower := a.Have(
				"x ^ p is the product of l, which is G.one",
				"monoid_pow(G.mul, G.one, x, p) = G.one",
				By(Normalized, allX, lParts[0], lParts[2], list.ConstantListFold.At(mul, one, x, l)))
			orderDivides := a.Have(
				"so the order of x divides p",
				"group_element_order(G, x) ∣ p",
				By(xPower, cyclic_group.OrderDividesIff.Read(grp).At(xm, p)))
			notTrivial := a.Have(
				"the order of x is not 1, since x ^ 1 = x is not G.one",
				"¬(group_element_order(G, x) = 1)",
				By(notOne, group.PowOne.Read(grp).At(xm), cyclic_group.PowOrderIsOne))
			order := a.Have(
				"so the order of x is the prime p",
				"group_element_order(G, x) = p",
				By(orderDivides, notTrivial, prime, nat_prime.PrimeDef))
			a.Show(
				"x is an element of order p",
				Witness(x),
				By(order, xIn))
		}),
})}
