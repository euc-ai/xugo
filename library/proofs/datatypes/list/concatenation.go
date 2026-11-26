// concatenation.go — list_append, list_length, list_reverse, and what they do to each
// other.
//
// list_append recurses on its FIRST argument. That one fact sets the shape
// of the file: where a law about it inducts at all, it inducts there,
// and the second list rides along untouched. list_length and list_reverse are
// then read through it. Five members never induct: the two emptiness
// laws are read through list_length instead, `AppendRightCancel` is read
// through reversal into its left-hand twin, `LengthEqCons` decomposes its
// list with `Cases` instead, and `LengthEqConsOver` reads `LengthEqCons`
// with the entries kept in a set. The lists of each length are counted
// too: finitely many over bool, and card(s) ^ n over a finite set s.

package list

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// AppendNil — appending nil changes nothing. By induction on l: at nil
// the first clause of list_append reads list_append(nil, nil) = nil outright; at
// cons(h, t) the second clause moves h out front, and the hypothesis
// folds the tail list_append(t, nil) back to t.
var AppendNil = appendNilThm{family.Add(registry.ProofEntry{
	Name: "AppendNil",
	Key:  "prop_e4a58c2b4e048845",
	Build: family.Theorem("∀l:list(A). list_append(l, nil) = l",
		func(a *Argument, l *Expr[List[A]]) {
			a.Induct(l)
			a.Base(
				"at nil: the first clause of list_append leaves nil = nil",
				Simp(Fwd(ListAppendDef)),
				TrivialNormalized())
			a.Step(
				"at cons(h, t): the second clause moves h out front, "+
					"and the hypothesis folds list_append(t, nil) to t",
				func(b *Argument, ih Fact) {
					b.Show(
						"both sides now read cons(h, t)",
						Simp(Fwd(ListAppendDef)),
						ih.Rw(),
						TrivialNormalized())
				})
		}),
})}

// AppendAssoc — concatenation is associative. By induction on the
// first list: the empty list in front of anything is that thing, so
// with nil in front both sides are m in front of n; with a head in
// front, list_append's step clause moves the head out in front on both
// sides, and the induction hypothesis identifies the two tails.
var AppendAssoc = appendAssocThm{family.Add(registry.ProofEntry{
	Name: "AppendAssoc",
	Key:  "prop_290ec8380638ea5d",
	Build: family.Theorem("∀l m n:list(A). "+
		"    list_append(l, list_append(m, n)) = list_append(list_append(l, m), n)",
		func(a *Argument, l, m, n *Expr[List[A]]) {
			a.Induct(l)
			a.Base(
				"l = nil: the empty list in front of anything is that thing, so both sides are list_append(m, n)",
				Simp(Fwd(ListAppendDef)),
				Basic())
			a.Step(
				"l = cons(h, t): list_append's step clause moves the head out in front on both sides",
				func(b *Argument, ih Fact) {
					b.Show(
						"and the two tails, list_append(t, list_append(m, n)) and "+
							"list_append(list_append(t, m), n), are equal by the hypothesis",
						Simp(Fwd(ListAppendDef)),
						By(Normalized, ih))
				})
		}),
})}

// AppendEqNil — a concatenation is empty exactly when both of its parts
// are. Emptiness through length (the README's "Two habits"): a
// concatenation's length is the sum of the two lengths,
// and what is left is arithmetic — a sum of naturals vanishes only when
// both summands do. One rewrite carries all three steps. The sum law is
// fired in the orientation the normalizer gives it, `0 = m + n`,
// because that is how the length rule leaves the sum standing; what
// remains differs from a tautology only by the sides of its equations.
var AppendEqNil = appendEqNilThm{family.Add(registry.ProofEntry{
	Name: "AppendEqNil",
	Key:  "prop_124e0cb1447fa9ea",
	Build: family.Theorem("∀l m:list(A). list_append(l, m) = nil ⇔ l = nil ∧ m = nil",
		func(a *Argument, l, m *Expr[List[A]]) {
			ctx := a.Ctx()
			a.Show(
				"emptiness read as length 0, a concatenation's length "+
					"as the sum: a sum vanishes exactly when both summands do",
				Simp(Rev(LengthEqNil), Fwd(LengthAppend), Fwd(MakeFact(ctx.DepNormalized(nat_arith.AddEqZero)))),
				TrivialNormalized())
		}),
})}

// AppendLeftCancel — a common prefix on the left can be dropped: it
// contributes the same thing to both sides, so what stands behind it
// decides the equation. By induction on the prefix, the two lists
// behind it fixed: the empty prefix contributes nothing at all, and
// cons(h, t) carries h out in front of both sides, where injectivity
// of cons leaves the same head twice and, behind it, the equation the
// hypothesis already decides.
var AppendLeftCancel = appendLeftCancelThm{family.Add(registry.ProofEntry{
	Name: "AppendLeftCancel",
	Key:  "prop_b0ba98a311873e40",
	Build: family.Theorem("∀l m n:list(A). list_append(l, m) = list_append(l, n) ⇔ m = n",
		func(a *Argument, l, m, n *Expr[List[A]]) {
			a.Induct(l)
			a.Base(
				"at nil the prefix contributes nothing: both sides read m = n outright",
				Simp(Fwd(ListAppendDef)),
				Basic())
			a.Step(
				"at cons(h, t) the head moves out in front of both sides, and cons is injective",
				func(b *Argument, ih Fact) {
					b.Show(
						"the two heads are the same h, and behind them the hypothesis reads the concatenations as m = n",
						Simp(Fwd(ListAppendDef), Fwd(ConsInjective)),
						ih.Rw(),
						Basic())
				})
		}),
})}

// AppendRightCancel — a common suffix on the right can be dropped as
// well, and this one is proved without an induction: reversal carries
// a suffix to the front, where a common prefix is already known to
// cancel, and reversal is injective, so the equation it decides there
// transports back unchanged.
var AppendRightCancel = appendRightCancelThm{family.Add(registry.ProofEntry{
	Name: "AppendRightCancel",
	Key:  "prop_fee315434484e9b",
	Build: family.Theorem("∀l m n:list(A). list_append(l, n) = list_append(m, n) ⇔ l = m",
		func(a *Argument, l, m, n *Expr[List[A]]) {
			injective := a.Have(
				"reversal undoes itself, so two lists agree exactly when their reversals do",
				"∀p q:list(A). p = q ⇔ list_reverse(p) = list_reverse(q)",
				By(ReverseReverse))
			reversed := a.Have(
				"reversed, both sides carry the common n out in front, where the left cancel drops it",
				"list_reverse(list_append(l, n)) = list_reverse(list_append(m, n)) ⇔ "+
					"list_reverse(l) = list_reverse(m)",
				Simp(Fwd(ReverseAppend), Fwd(AppendLeftCancel)),
				TrivialNormalized())
			a.Show(
				"injectivity reads that equivalence back at both ends: "+
					"the concatenations on its left, l and m on its right",
				By(injective, reversed))
		}),
})}

// LengthAppend — the length of l in front of m is the sum of the two
// lengths. By induction on l with m fixed: list_append and list_length both
// recurse on their first argument, so each side unfolds one constructor
// at a time, and the clause of addition at that constructor — 0 + n = n
// at nil, suc(m) + n = suc(m + n) at cons — absorbs what the unfolding
// leaves.
var LengthAppend = lengthAppendThm{family.Add(registry.ProofEntry{
	Name: "LengthAppend",
	Key:  "prop_707eacc104c7428c",
	Build: family.Theorem("∀l m:list(A). "+
		"    list_length(list_append(l, m)) = list_length(l) + list_length(m)",
		func(a *Argument, l, m *Expr[List[A]]) {
			a.Induct(l)
			a.Base(
				"the empty list in front of m is m, of length 0 + "+
					"list_length(m) — the left zero clause of addition",
				Simp(Fwd(ListAppendDef), Fwd(ListLengthDef), Fwd(nat_arith.AddLeftZeroClause)),
				Refl())
			a.Step(
				"a head in front adds one to both lengths; the left suc clause of "+
					"addition lifts it out of the sum, and the hypothesis closes the rest",
				func(b *Argument, ih Fact) {
					b.Show(
						"both sides are suc of the tail's concatenation length",
						Simp(Fwd(ListAppendDef), Fwd(ListLengthDef), Fwd(nat_arith.AddLeftSucClause)),
						ih.Rw(),
						TrivialNormalized())
				})
		}),
})}

// LengthEqNil — a list has length zero exactly when it is empty. By
// induction on l, with the hypothesis never needed: each constructor
// decides both sides of the equivalence outright. At nil both hold —
// the length is 0 by list_length's first clause. At cons(h, t) both fail —
// the length is suc(list_length(t)), which is not 0, and a cons is not nil.
var LengthEqNil = lengthEqNilThm{family.Add(registry.ProofEntry{
	Name: "LengthEqNil",
	Key:  "prop_df817e98747b2884",
	Build: family.Theorem("∀l:list(A). list_length(l) = 0 ⇔ l = nil",
		func(a *Argument, l *Expr[List[A]]) {
			a.Induct(l)
			a.Base(
				"at nil both sides hold: the length is 0 by list_length's first clause, and nil = nil",
				Simp(Fwd(ListLengthDef)),
				TrivialNormalized())
			a.Step(
				"at cons(h, t) both sides fail: the length is "+
					"suc(list_length(t)), never 0, and a cons is never nil",
				By(Normalized, ListLengthDef, NilNotCons, peano.SucNotZero))
		}),
})}

// LengthEqCons — a length of suc(n) is exactly a head in front of a
// tail of length n, the fact that turns a numeric hypothesis into a
// structural one. Backwards it is list_length's cons clause read as it
// stands. Forwards the list must first be decomposed: a successor is
// not 0, so the list is no nil, and the case analysis then hands over
// the head and the tail the existential asks for — the list's own —
// with suc coming off both lengths to leave the tail's.
var LengthEqCons = lengthEqConsThm{family.Add(registry.ProofEntry{
	Name: "LengthEqCons",
	Key:  "prop_a8df21d12b7bf7c7",
	Build: family.Theorem("∀l:list(A). ∀n:num. "+
		"    list_length(l) = suc(n) ⇔ ∃h:A. ∃t:list(A). l = cons(h, t) ∧ list_length(t) = n",
		func(a *Argument, l *Expr[List[A]], n *Expr[Nat]) {
			a.Iff()
			a.Forward(
				"l must be a cons, and its own head and tail are the "+
					"witnesses: suc comes off both lengths, leaving the tail's",
				func(b *Argument, counted Fact) {
					head, tail, split := b.Obtain2(
						"no nil has a successor for its length, so the case analysis leaves l only the cons form",
						"∃h:A. ∃t:list(A). l = cons(h, t)",
						By(counted, At(Cases, l), ListLengthDef, peano.SucNotZero))
					b.Take(head)
					b.Take(tail)
					b.Show(
						"suc comes off both sides of the length equation, leaving the tail's at n",
						By(Normalized, split, counted, ListLengthDef, peano.SucInjective))
				})
			a.Backward(
				"the hypothesis hands over a head and a tail of "+
					"length n, and list_length counts that list as one more",
				func(b *Argument, decomposed Fact) {
					_, _, split := b.Unpack2(decomposed)
					b.Show(
						"list_length's cons clause reads the length off the tail: suc of n",
						By(Normalized, split, ListLengthDef))
				})
		}),
})}

// LengthEqConsOver — a list of length suc(n) whose entries lie in s is a
// head in s in front of a tail of length n whose entries lie in s:
// LengthEqCons splits it, and the head and the tail's entries are entries
// of the list.
var LengthEqConsOver = lengthEqConsOverThm{family.Add(registry.ProofEntry{
	Name: "LengthEqConsOver",
	Key:  "prop_aa2d488299e8770e",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀n:num. ∀l:list(A).",
		Hypotheses: []string{
			"list_length(l) = suc(n)",
			"∀y:A. list_member(y, l) ⇒ y ∈ s",
		},
		Conclusion: "∃h:A. ∃t:list(A). " +
			"    l = cons(h, t) ∧ list_length(t) = n ∧ h ∈ s ∧ (∀y:A. list_member(y, t) ⇒ y ∈ s)",
	},
		func(a *Argument, s *Expr[Set[A]], n *Expr[Nat], l *Expr[List[A]], length, entries Fact) {
			h, t, split := a.Obtain2As[A, List[A]](
				"l is a head in front of a tail of length n",
				"∃h:A. ∃t:list(A). l = cons(h, t) ∧ list_length(t) = n",
				By(length, LengthEqCons.At(l, n)))
			parts := a.Conjuncts(
				split,
				"l is cons(h, t)",
				"t has length n")
			a.Take(h)
			a.Take(t)
			a.Show(
				"the head and the tail's entries are entries of l, so they lie in s",
				By(parts[0], parts[1], entries, ListMemberDef))
		}),
})}

// BoolListsOfLengthFinite — there are finitely many boolean lists of each
// length. By induction on the length: the empty list is the one list of
// length zero, and a list of length suc(n) is ⊤ or ⊥ in front of a list
// of length n (LengthEqCons), so those lists are the images of the lists
// of length n under the two conses, a union of two finite images.
var BoolListsOfLengthFinite = boolListsOfLengthFiniteThm{family.Add(registry.ProofEntry{
	Name: "BoolListsOfLengthFinite",
	Key:  "prop_f5d78e4a00561dbf",
	Build: family.Theorem("∀n:num. finite({t:list(bool) | list_length(t) = n})",
		func(a *Argument, n *Expr[Nat]) {
			a.Induct(n)
			a.Base(
				"the empty list is the one list of length zero",
				func(b *Argument) {
					empty := b.Have(
						"a list has length zero exactly when it is nil",
						"{t:list(bool) | list_length(t) = 0} = {nil⟨A:bool⟩}",
						BySets(LengthEqNil))
					b.Show(
						"and a singleton is finite",
						By(empty, finite_set.FiniteSing))
				})
			a.Step(
				"a list of length suc(n) is ⊤ or ⊥ in front of a list of length n",
				func(b *Argument, ih Fact) {
					heads := b.Have(
						"a list has length suc(n) exactly when it is ⊤ or ⊥ in front of a list of length n",
						"∀t:list(bool). "+
							"    list_length(t) = suc(n) ⇔ "+
							"    (∃s:list(bool). list_length(s) = n ∧ t = cons(⊤, s)) ∨ "+
							"    (∃s:list(bool). list_length(s) = n ∧ t = cons(⊥, s))",
						b.ForEach(func(t *Expr[List[Bool]]) Action { return By(LengthEqCons.At(t, n)) }))
					images := b.Have(
						"so the lists of length suc(n) are the images of those of length n under the two conses",
						"{t:list(bool) | list_length(t) = suc(n)} = "+
							"image(λt:list(bool). cons(⊤, t), {t:list(bool) | list_length(t) = n}) ∪ "+
							"image(λt:list(bool). cons(⊥, t), {t:list(bool) | list_length(t) = n})",
						BySets(heads))
					b.Show(
						"a union of two images of a finite set is finite",
						By(ih, images, finite_set.FiniteUnion, finite_set.FiniteImage))
				})
		}),
})}

// ListsCount — the lists of length n with entries in a finite set s
// number card(s) ^ n: only the empty list has length 0, and a list of
// length n + 1 is a point of s in front of a list of length n, the two
// told apart (ConsInjective).
var ListsCount = listsCountThm{family.Add(registry.ProofEntry{
	Name: "ListsCount",
	Key:  "prop_8d70bab7e8c133a8",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀n:num.",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "has_size(«lists»(n), card(s) ^ n)",
		Abbrev: Abbrev{
			{Name: "lists", Text: "λn:num. " +
				"    {l:list(A) | list_length(l) = n ∧ (∀y:A. list_member(y, l) ⇒ y ∈ s)}"},
		},
	},
		func(a *Argument, s *Expr[Set[A]], finite Fact) {
			a.Induct("n")
			a.Base(
				"only the empty list has length 0, and it is one list",
				func(b *Argument) {
					single := b.Have(
						"a list of length 0 is nil, whose entries are none",
						"«lists»(0) = {nil}",
						BySets(LengthEqNil, ListMemberDef))
					nothing := b.TermAs[List[A]]("nil")
					b.Show(
						"a single list, and card(s) ^ 0 is 1",
						single.Rw(),
						By(
							cardinality.HasSizeDef.At(b.TermAs[Set[List[A]]]("{nil}"), b.TermAs[Nat]("card(s) ^ 0")),
							finite_set.FiniteSing.At(nothing),
							cardinality.CardSing.At(nothing),
							nat_arith.NatPow))
				})
			a.Step(
				"a list of length n + 1 is a point of s in front of a list of length n",
				func(b *Argument, ih Fact) {
					length := b.TermAs[Nat]("n")
					heads := b.Have(
						"a list of length n + 1 over s is a head in s in front of a tail of length n over s",
						"∀l:list(A). l ∈ «lists»(suc(n)) ⇔ l ∈ {cons(h, t) | h:A, t:list(A) | h ∈ s ∧ t ∈ «lists»(n)}",
						b.ForEach(func(l *Expr[List[A]]) Action {
							return By(LengthEqCons.At(l, length), ListMemberDef)
						}))
					fronted := b.Have(
						"so the lists of length n + 1 are the conses of a point of s and a list of length n",
						"«lists»(suc(n)) = {cons(h, t) | h:A, t:list(A) | h ∈ s ∧ t ∈ «lists»(n)}",
						By(heads, set_basic.Extension))
					b.Show(
						"cons tells the pairs apart, so there are card(s) times card(s) ^ n of them",
						fronted.Rw(),
						By(
							finite,
							ih,
							cardinality.FiniteHasSize,
							ConsInjective,
							nat_arith.NatPow,
							cardinality.HasSizeProductImage.At(
								b.TermAs[Fun2[A, List[A], List[A]]]("λh:A. λt:list(A). cons(h, t)"),
								s,
								b.TermAs[Set[List[A]]]("«lists»(n)"),
								b.TermAs[Nat]("card(s)"),
								b.TermAs[Nat]("card(s) ^ n"))))
				})
		}),
})}

// LengthReverse — a list and its reversal have the same length. By
// induction on l: at nil reversal leaves the empty list empty, so both
// sides read list_length(nil). At a cons the head travels to the far end,
// so the reversal is the reversed tail with a one-element list behind
// it; LengthAppend splits that length into the two summands, the
// hypothesis folds the first back to the tail's own length, and the
// right-hand clauses of addition read the sum as one more than it.
var LengthReverse = lengthReverseThm{family.Add(registry.ProofEntry{
	Name: "LengthReverse",
	Key:  "prop_38511cab67378c58",
	Build: family.Theorem("∀l:list(A). list_length(list_reverse(l)) = list_length(l)",
		func(a *Argument, l *Expr[List[A]]) {
			a.Induct(l)
			a.Base(
				"at nil: reversal leaves the empty list empty, and both sides read list_length(nil)",
				Simp(Fwd(ListReverseDef)),
				Refl())
			a.Step(
				"at cons: the head goes behind the reversed tail, so LengthAppend "+
					"splits the length into the tail's and the singleton's",
				func(b *Argument, ih Fact) {
					b.Show(
						"both sides read one more than the tail's length, "+
							"the sum through the right-hand clauses of addition",
						Simp(Fwd(ListReverseDef), Fwd(LengthAppend), Fwd(ListLengthDef)),
						ih.Rw(),
						Simp(Fwd(nat_arith.AddSuc), Fwd(nat_arith.AddZero)),
						Refl())
				})
		}),
})}

// ReverseAppend — reversing a concatenation reverses the two parts and
// concatenates them the other way round. By induction on l with m
// fixed. With nil in front, the left side is list_reverse(m) and the right
// side is list_reverse(m) with nil appended, which AppendNil folds back.
// With a head h in front, list_reverse's step clause sends h to the far end
// of each side: on the left behind list_reverse(list_append(t, m)), which the
// hypothesis rewrites to list_append(list_reverse(m), list_reverse(t)); on the right
// behind list_reverse(t), inside list_reverse(m)'s concatenation — and
// AppendAssoc regroups the right side into the left.
var ReverseAppend = reverseAppendThm{family.Add(registry.ProofEntry{
	Name: "ReverseAppend",
	Key:  "prop_1a1670a6a4a03ab5",
	Build: family.Theorem("∀l m:list(A). "+
		"    list_reverse(list_append(l, m)) = list_append(list_reverse(m), list_reverse(l))",
		func(a *Argument, l, m *Expr[List[A]]) {
			a.Induct(l)
			a.Base(
				"l = nil: the left side is list_reverse(m); the right is "+
					"list_reverse(m) with nil appended, which AppendNil folds away",
				Simp(Fwd(ListAppendDef), Fwd(ListReverseDef), Fwd(AppendNil)),
				Refl())
			a.Step(
				"l = cons(h, t): h goes to the far end of both sides; AppendAssoc "+
					"regroups the right side as the reversal of m, then of t, then h",
				func(b *Argument, ih Fact) {
					b.Show(
						"the hypothesis turns the left side's reversal of t followed "+
							"by m into the same regrouped shape, and the two sides coincide",
						Simp(Fwd(ListAppendDef), Fwd(ListReverseDef), Fwd(AppendAssoc)),
						ih.Rw(),
						TrivialNormalized())
				})
		}),
})}

// ReverseReverse — reversing twice restores the list. By induction on l:
// at nil the first clause of list_reverse gives nil on both sides. At
// cons(x, t) the step clause sends x behind list_reverse(t), and ReverseAppend
// turns the outer reverse of that concatenation around, so the reversed
// singleton comes first — and the clauses collapse it back to cons(x, nil),
// putting x out front again. What follows it is list_reverse(list_reverse(t)), which
// the hypothesis folds to t.
var ReverseReverse = reverseReverseThm{family.Add(registry.ProofEntry{
	Name: "ReverseReverse",
	Key:  "prop_23430626d025eb34",
	Build: family.Theorem("∀l:list(A). list_reverse(list_reverse(l)) = l",
		func(a *Argument, l *Expr[List[A]]) {
			a.Induct(l)
			a.Base(
				"at nil: list_reverse(nil) is nil, so both sides read nil",
				Simp(Fwd(ListReverseDef)),
				Refl())
			a.Step(
				"at cons(x, t): the reversed singleton returns x to the "+
					"front, leaving list_reverse(list_reverse(t)) behind it",
				func(b *Argument, ih Fact) {
					b.Show(
						"the hypothesis folds that tail to t, and both sides read cons(x, t)",
						Simp(Fwd(ListReverseDef), Fwd(ReverseAppend), Fwd(ListAppendDef)),
						ih.Rw(),
						TrivialNormalized())
				})
		}),
})}

// ReverseEqNil — a reversal is empty exactly when the list it reverses
// is. Emptiness through length, and reversal keeps the length, so the
// two sides become one and the same condition.
var ReverseEqNil = reverseEqNilThm{family.Add(registry.ProofEntry{
	Name: "ReverseEqNil",
	Key:  "prop_f989da3c078e73f5",
	Build: family.Theorem("∀l:list(A). list_reverse(l) = nil ⇔ l = nil",
		func(a *Argument) {
			a.Show(
				"emptiness read as length 0: reversal keeps the length, so both sides become the same condition",
				Simp(Rev(LengthEqNil), Fwd(LengthReverse)),
				TrivialNormalized())
		}),
})}
