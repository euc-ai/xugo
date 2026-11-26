// fold.go — the chapter's fold part: list_fold, and the sum and product it
// specializes to.
//
// list_fold is the general fold from the right; a list whose entries are
// all x folds to x to the power of its length. `list_sum` is the fold at
// addition, started at 0, and the three laws about it are the recursion a
// consumer computes with, the split over a concatenation, and the fact
// that reversing a list does not change its sum. The last is where the
// chapter spends commutativity of addition, and the only place it does.
// `list_product` is the same fold at multiplication, started at 1, and
// here it has its recursion.

package list

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/registry"
)

// FoldAppend — a fold over a concatenation is the fold over the
// first list started at the fold over the second. By induction on l,
// with f, b and m fixed. The empty list in front of m is m and a fold
// over nil returns its starting value, so at nil both sides are the
// fold over m. At a head in front, list_append's step clause exposes that
// head, list_fold's step clause then puts f(h, …) in front on both sides,
// and the hypothesis identifies the folds standing inside.
var FoldAppend = foldAppendThm{family.Add(registry.ProofEntry{
	Name: "FoldAppend",
	Key:  "prop_5acad73eb893a578",
	Build: family.Theorem("∀f:(A → B → B). ∀b:B. ∀l m:list(A). "+
		"    list_fold(f, list_append(l, m), b) = list_fold(f, l, list_fold(f, m, b))",
		func(a *Argument, f *Arrow2[A, B, B], b *Expr[B], l, m *Expr[List[A]]) {
			a.Induct(l)
			a.Base(
				"l = nil: the concatenation is m and the fold over nil is "+
					"its starting value, so both sides are list_fold(f, m, b)",
				Simp(Fwd(ListAppendDef), Fwd(ListFoldDef)),
				Refl())
			a.Step(
				"l = cons(h, t): both sides put f(h, …) in front, and the hypothesis identifies what stands inside",
				// The branch is `step`, not the usual `b`: the statement's
				// own starting value is bound to that letter here.
				func(step *Argument, ih Fact) {
					step.Show(
						"the inner folds, list_fold(f, list_append(t, m), b) and "+
							"list_fold(f, t, list_fold(f, m, b)), agree by the hypothesis",
						Simp(Fwd(ListAppendDef), Fwd(ListFoldDef)),
						ih.Rw(),
						TrivialNormalized())
				})
		}),
})}

// ConstantListFold — folding a list all of whose entries are x is taking
// x to the power of its length: one factor of x for each entry.
var ConstantListFold = constantListFoldThm{family.Add(registry.ProofEntry{
	Name: "ConstantListFold",
	Key:  "prop_4c077fce63dc000",
	Build: family.Theorem(Statement{
		Binders: "∀op:(A → A → A). ∀e x:A. ∀l:list(A).",
		Hypotheses: []string{
			"∀y:A. list_member(y, l) ⇒ y = x",
		},
		Conclusion: "list_fold(op, l, e) = monoid_pow(op, e, x, list_length(l))",
	},
		func(a *Argument, op *Arrow2[A, A, A], e, x *Expr[A]) {
			a.Induct("l")
			a.Base(
				"the empty list folds to e, which is x to the power 0",
				By(Normalized, ListFoldDef, ListLengthDef, comm_monoid.MonoidPowDef))
			a.Step(
				"one more entry, which is x, is one more factor of x",
				func(b *Argument, ih Fact) {
					b.Show(
						"the head is x and the tail folds to x to its length",
						Simp(Fwd(ListFoldDef), Fwd(ListLengthDef), Fwd(comm_monoid.MonoidPowDef), Fwd(ListMemberDef)),
						By(ih))
				})
		}),
})}

// ListSumClauses — what a consumer of list_sum computes with. The
// definition states it as a fold, which is what makes it the list-side
// twin of Σ over a set; a reader summing a list wants its recursion
// instead. The two are one unfolding apart and no induction is
// involved: the fold already has a clause at nil and a clause at cons,
// and list_sum is that fold at a single operation and a single
// starting element.
var ListSumClauses = listSumClausesThm{family.Add(registry.ProofEntry{
	Name: "ListSumClauses",
	Key:  "prop_835e0b71cd0f767e",
	Build: family.Theorem("list_sum(nil) = 0 ∧ "+
		"∀h:num. ∀t:list(num). list_sum(cons(h, t)) = h + list_sum(t)",
		func(a *Argument) {
			// A sum of a list of naturals folds naturals into a
			// natural, so the fold is read at that one instance.
			foldOfNaturals := ListFoldDef.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]())
			a.Show(
				"each clause is list_fold's own, at addition and started from 0",
				Simp(Fwd(ListSumDef), Fwd(foldOfNaturals)),
				TrivialNormalized())
		}),
})}

// ListSumAppend — a sum over a concatenation splits into the two sums.
// It is the law the listing correspondence reads when it sums over a
// set built from two lists.
//
// By induction on l with m fixed. list_append and list_sum both recurse on
// the first list, so each side peels one constructor at a time, and an
// addition law absorbs what the peeling leaves: the left zero clause at
// nil, associativity at a head in front, where the head has to move
// across the bracket the hypothesis introduces.
var ListSumAppend = listSumAppendThm{family.Add(registry.ProofEntry{
	Name: "ListSumAppend",
	Key:  "prop_18975a49d7d83077",
	Build: family.Theorem("∀l m:list(num). list_sum(list_append(l, m)) = list_sum(l) + list_sum(m)",
		func(a *Argument, l, m *Expr[List[Nat]]) {
			// Only lists of naturals are summed, so concatenation is
			// read at that one instance.
			concatenationOfNaturals := ListAppendDef.Inst[Nat]()

			a.Induct(l)
			a.Base(
				"l = nil: the concatenation is m and the empty list sums "+
					"to 0, which the left zero clause of addition absorbs",
				Simp(Fwd(concatenationOfNaturals), Fwd(ListSumClauses), Fwd(nat_arith.AddLeftZeroClause)),
				Refl())
			a.Step(
				"l = cons(h, t): the head is pulled out of both sums, "+
					"and associativity of addition regroups it with the tail's",
				func(b *Argument, ih Fact) {
					b.Show(
						"the hypothesis replaces list_sum(list_append(t, m)) by "+
							"list_sum(t) + list_sum(m), and only the bracketing then differs",
						Simp(Fwd(concatenationOfNaturals), Fwd(ListSumClauses)),
						ih.Rw(),
						Simp(Fwd(nat_arith.AddAssoc)),
						Refl())
				})
		}),
})}

// ListSumReverse — reversing a list does not change its sum. What makes
// it cheap is that addition commutes: that law is the entire content.
//
// By induction on l. At nil reversal leaves the empty list empty and
// both sides read list_sum(nil). At a cons the head travels to the far
// end, so the reversal is the reversed tail with a one-element list
// behind it; ListSumAppend splits that sum into the two summands, the
// hypothesis folds the first back to the tail's own sum, and the
// singleton contributes its head alone, the right-hand zero clause of
// addition absorbing the empty tail. The head then sits behind the
// tail's sum where the other side has it in front, and commutativity
// of addition is what turns the one into the other.
var ListSumReverse = listSumReverseThm{family.Add(registry.ProofEntry{
	Name: "ListSumReverse",
	Key:  "prop_2f210e4cff2c59db",
	Build: family.Theorem("∀l:list(num). list_sum(list_reverse(l)) = list_sum(l)",
		func(a *Argument, l *Expr[List[Nat]]) {
			// Only lists of naturals are summed, so reversal is read at
			// that one instance.
			reversalOfNaturals := ListReverseDef.Inst[Nat]()

			a.Induct(l)
			a.Base(
				"l = nil: reversal leaves the empty list empty, and both sides read list_sum(nil)",
				Simp(Fwd(reversalOfNaturals)),
				Refl())
			a.Step(
				"l = cons(h, t): the head goes behind the reversed tail, "+
					"and commutativity of addition brings it back in front",
				func(b *Argument, ih Fact) {
					b.Show(
						"the hypothesis folds the reversed tail's sum back, and "+
							"the sides then differ only in the order of the summands",
						Simp(Fwd(reversalOfNaturals), Fwd(ListSumAppend), Fwd(ListSumClauses), Fwd(nat_arith.AddZero)),
						ih.Rw(),
						Simp(Fwd(nat_arith.AddSym)),
						Refl())
				})
		}),
})}

// ListProductClauses — the recursion list_product computes with, read off
// the fold exactly as ListSumClauses reads list_sum's: one unfolding, the
// fold's own clause at nil and at cons, at multiplication and started
// from 1.
var ListProductClauses = listProductClausesThm{family.Add(registry.ProofEntry{
	Name: "ListProductClauses",
	Key:  "prop_bbdd41fafe036a1d",
	Build: family.Theorem("list_product(nil) = 1 ∧ "+
		"∀h:num. ∀t:list(num). list_product(cons(h, t)) = h * list_product(t)",
		func(a *Argument) {
			foldOfNaturals := ListFoldDef.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]())
			a.Show(
				"each clause is list_fold's own, at multiplication and started from 1",
				Simp(Fwd(ListProductDef), Fwd(foldOfNaturals)),
				TrivialNormalized())
		}),
})}
