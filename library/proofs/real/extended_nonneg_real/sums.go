// sums.go — finite sums in ⟦0, ∞⟧: Σ is the fold at extended addition.
//
// Addition with 0 is a commutative monoid on ⟦0, ∞⟧, so the fold
// mechanism of iterate/monoidal applies to it as it does to ℝ's: the
// recursion clauses, the pointwise laws and the comparison of folds are
// the mechanism's own, read at extended addition. What is proper to
// ⟦0, ∞⟧ is that every summand is nonnegative — so a sum only grows as
// its index set does — and that a sum may be ∞, which happens exactly
// when a term is.
//
// Two parts, marked by banners:
//
// - The bridge: extended addition folds
// - Σ on ⟦0, ∞⟧

package extended_nonneg_real

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The bridge: extended addition folds
// ---------------------------------------------------------------------------

// ExtendedSumDef — Σ over ⟦0, ∞⟧ is the fold at extended addition;
// `Σ_{i∈s} f(i)` at an extended body is `extended_sum(s, λi. f(i))`.
var ExtendedSumDef = extendedSumDefThm{family.Define(registry.DefEntry{
	Name:      "ExtendedSumDef",
	Key:       "prop_7804968377c818ac",
	Const:     "extended_sum",
	Type:      "set(A) → (A → extended_nonneg_real) → extended_nonneg_real",
	Overload:  "sum",
	BigOp:     "Σ",
	Equations: []string{"extended_sum = iterated_op⟨A:A, B:extended_nonneg_real⟩(extended_add)"},
	Deps:      []registry.EntryLike{ExtendedAddDef},
})}

// AddMonoid — extended addition, with 0, is a commutative monoid.
var AddMonoid = addMonoidThm{family.Add(registry.ProofEntry{
	Name: "AddMonoid",
	Key:  "prop_a58e8193a585c7ff",
	Build: family.Instance(comm_monoid.CommMonoid, "comm_monoid(extended_add, &0)",
		Case(
			"addition commutes",
			Cite(AddComm)),
		Case(
			"addition associates",
			Cite(AddAssoc)),
		Case(
			"0 is a left identity, being a right one and addition commuting",
			By(Normalized, AddComm, AddZero))),
})}

// MonoidalAdd — extended addition folds: the monoid chapter's bridge,
// read at the additive monoid.
var MonoidalAdd = monoidalAddThm{family.Add(registry.ProofEntry{
	Name:  "MonoidalAdd",
	Key:   "prop_add53542088b1af4",
	Build: family.Theorem("monoidal_op(extended_add)", By(comm_monoid.Monoidal, AddMonoid)),
})}

// NeutralAdd — and it folds from 0.
var NeutralAdd = neutralAddThm{family.Add(registry.ProofEntry{
	Name:  "NeutralAdd",
	Key:   "prop_721417065d8795a3",
	Build: family.Theorem("neutral_elem(extended_add) = &0", By(comm_monoid.Neutral, AddMonoid)),
})}

// ---------------------------------------------------------------------------
// Σ on ⟦0, ∞⟧
// ---------------------------------------------------------------------------

// SumClauses — Σ's recursion: the empty sum is 0, and inserting a point
// either changes nothing, because the point was already there, or adds
// its own value.
var SumClauses = sumClausesThm{family.Add(registry.ProofEntry{
	Name: "SumClauses",
	Key:  "prop_41a6081487751f7d",
	Build: family.Theorem(
		"(∀f:(A → extended_nonneg_real). sum(∅, f) = &0) ∧ "+
			"(∀g:(C → extended_nonneg_real). ∀x:C. ∀s:set(C). "+
			"    finite(s) ⇒ sum(insert(x, s), g) = COND(x ∈ s, sum(s, g), g(x) + sum(s, g)))",
		func(a *Argument) {
			a.Do(Unfold(ExtendedSumDef), By(monoidal.Clauses, MonoidalAdd, NeutralAdd))
		}),
})}

// SumAdd — two summands over one finite index set may be added before
// or after summing.
var SumAdd = sumAddThm{family.Add(registry.ProofEntry{
	Name: "SumAdd",
	Key:  "prop_c09b2a18fe76731a",
	Build: family.Theorem(Statement{
		Binders:    "∀f g:(A → extended_nonneg_real). ∀s:set(A).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "Σ_{i∈s} (f(i) + g(i)) = Σ_{i∈s} f(i) + Σ_{i∈s} g(i)",
	},
		func(a *Argument) {
			a.Do(Unfold(ExtendedSumDef), By(monoidal.Pointwise, MonoidalAdd))
		}),
})}

// SumScale — a factor moves through a finite sum: multiplying by c
// keeps 0 and distributes over addition, so it carries the fold.
var SumScale = sumScaleThm{family.Add(registry.ProofEntry{
	Name: "SumScale",
	Key:  "prop_56a57eb6e614d14d",
	Build: family.Theorem(Statement{
		Binders:    "∀c:extended_nonneg_real. ∀f:(A → extended_nonneg_real). ∀s:set(A).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "c * (Σ_{i∈s} f(i)) = Σ_{i∈s} c * f(i)",
	},
		func(a *Argument) {
			a.Do(Unfold(ExtendedSumDef), By(
				monoidal.Homomorphic,
				MonoidalAdd,
				NeutralAdd,
				MulZero,
				MulAddDistrib))
		}),
})}

// SumMono — a summand nowhere above another sums to no more over a
// finite set: the order survives addition and holds at 0, so the fold
// carries it from the terms to the sums.
var SumMono = sumMonoThm{family.Add(registry.ProofEntry{
	Name: "SumMono",
	Key:  "prop_e289a9d80c5e74a8",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(A → extended_nonneg_real). ∀s:set(A).",
		Hypotheses: []string{
			"finite(s)",
			"∀i:A. i ∈ s ⇒ f(i) ≤ g(i)",
		},
		Conclusion: "Σ_{i∈s} f(i) ≤ Σ_{i∈s} g(i)",
	},
		func(a *Argument, f, g *Arrow[A, ExtendedNonnegReal], s *Expr[Set[A]], finite, pointwise Fact) {
			order := a.TermAs[Fun2[ExtendedNonnegReal, ExtendedNonnegReal, Bool]]("extended_le")
			a.Do(Unfold(ExtendedSumDef))
			a.Show(
				"the fold carries the order from the terms to the sums",
				By(finite, pointwise, AddLeAdd, LeRefl, monoidal.Related.Read(MonoidalAdd).At(order, s, f, g)))
		}),
})}

// SumSubsetLe — a sum of ⟦0, ∞⟧ terms only grows with its index set: the
// larger sum is the smaller one plus the sum over the difference.
var SumSubsetLe = sumSubsetLeThm{family.Add(registry.ProofEntry{
	Name: "SumSubsetLe",
	Key:  "prop_c2f7ee1a3561c643",
	Build: family.Theorem(Statement{
		Binders: "∀f:(A → extended_nonneg_real). ∀s t:set(A).",
		Hypotheses: []string{
			"finite(t)",
			"s ⊆ t",
		},
		Conclusion: "Σ_{i∈s} f(i) ≤ Σ_{i∈t} f(i)",
	},
		func(a *Argument, f *Arrow[A, ExtendedNonnegReal], s, t *Expr[Set[A]], finite, within Fact) {
			a.Do(Unfold(ExtendedSumDef))
			onS := a.TermAs[ExtendedNonnegReal]("iterated_op(extended_add, s, f)")
			onRest := a.TermAs[ExtendedNonnegReal]("iterated_op(extended_add, t ∖ s, f)")
			a.Show(
				"the sum over t is the sum over t ∖ s added to the sum over s",
				By(
					finite,
					within,
					monoidal.Diff.Read(MonoidalAdd).At(t, s, f),
					LeAddRight.At(onS, onRest),
					AddComm.At(onS, onRest)))
		}),
})}

// SumEqInfinity — a finite sum is ∞ exactly when one of its terms is: ∞
// absorbs the rest of the sum, and finite terms add to a finite sum.
var SumEqInfinity = sumEqInfinityThm{family.Add(registry.ProofEntry{
	Name: "SumEqInfinity",
	Key:  "prop_e5c653ee78c7baf2",
	Build: family.Theorem(Statement{
		Binders:    "∀f:(A → extended_nonneg_real). ∀s:set(A).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "Σ_{i∈s} f(i) = extended_infinity ⇔ ∃i:A. i ∈ s ∧ f(i) = extended_infinity",
	},
		func(a *Argument, f *Arrow[A, ExtendedNonnegReal], s *Expr[Set[A]], finite Fact) {
			a.Iff()
			a.Backward(
				"an infinite term is one summand of the sum, and ∞ absorbs the rest",
				func(b *Argument, someInfinite Fact) {
					i, infiniteAt := b.UnpackAs[A](someInfinite)
					parts := b.Conjuncts(
						infiniteAt,
						"i lies in s",
						"f(i) is ∞")
					b.Do(Unfold(ExtendedSumDef))
					b.Show(
						"the sum is f(i) added to the sum over the rest",
						By(finite, parts[0], parts[1], monoidal.Delete.Read(MonoidalAdd).At(s, f, i), AddEqInfinity))
				})
			a.Forward(
				"a sum whose terms are all finite is finite",
				func(b *Argument, infinite Fact) {
					noneInfinite := b.SupposeNot()
					finiteSum := b.Have(
						"0 is finite and finite values add to a finite value, so the sum is finite",
						"Σ_{i∈s} f(i) ≠ extended_infinity",
						Unfold(ExtendedSumDef),
						By(
							noneInfinite,
							monoidal.Closed.Read(MonoidalAdd).At(
								b.TermAs[Set[ExtendedNonnegReal]]("λx:extended_nonneg_real. x ≠ extended_infinity"), s, f),
							NeutralAdd,
							ZeroNotInfinity,
							AddEqInfinity))
					b.Show(
						"which contradicts the sum being ∞",
						By(finiteSum, infinite))
				})
		}),
})}

// SumOfReal — on nonnegative reals the embedding carries a finite sum
// to the sum of the images. By induction over the finite index set:
// a new term's image adds to the image of the old sum, and both are
// nonnegative.
var SumOfReal = sumOfRealThm{family.Add(registry.ProofEntry{
	Name: "SumOfReal",
	Key:  "prop_52fca1216398aa3f",
	Build: family.Theorem(Statement{
		Binders: "∀f:(A → real). ∀s:set(A).",
		Hypotheses: []string{
			"finite(s)",
			"∀i:A. i ∈ s ⇒ &0 ≤ f(i)",
		},
		Conclusion: "Σ_{i∈s} extended_of_real(f(i)) = extended_of_real(Σ_{i∈s} f(i))",
	},
		func(a *Argument, f *Arrow[A, Real], s *Expr[Set[A]], finite, nonneg Fact) {
			a.Show(
				"the embedding carries the sum over every finite set of nonnegative terms, and s is one",
				ByInduction(finite_set.FiniteInductFresh, finite, Generalizing(nonneg),
					Case(
						"over ∅ both sides are 0",
						By(SumClauses, real_sum.Clauses)),
					Case(
						"across insert: the new term's image adds to the image of the old sum",
						Derive(func(b *Argument) {
							x := b.FixAs[A]()
							u := b.FixAs[Set[A]]("u")
							previous := b.Assume()
							nonnegInsert := b.Assume()
							nonnegU := b.Have(
								"the terms over u are nonnegative, u lying inside insert(x, u)",
								"∀i:A. i ∈ u ⇒ &0 ≤ f(i)",
								By(nonnegInsert, set_basic.InInsert))
							b.Show(
								"f(x) and the sum over u are nonnegative, so their images add as the reals do",
								By(
									previous,
									nonnegU,
									nonnegInsert,
									SumClauses,
									real_sum.Clauses,
									OfRealAdd.At(f.Apply(x), b.TermAs[Real]("Σ_{i∈u} f(i)")),
									real_sum.Nonneg.At(u, f),
									set_basic.InInsert))
						}))))
		}),
})}

// SumSegmentZero — the sum over the one-point segment 0 .. 0 is its
// term.
var SumSegmentZero = sumSegmentZeroThm{family.Add(registry.ProofEntry{
	Name: "SumSegmentZero",
	Key:  "prop_6f24d92c014f41d2",
	Build: family.Theorem("∀a:(num → extended_nonneg_real). Σ_{i∈0 .. 0} a(i) = a(0)",
		func(arg *Argument) {
			arg.Do(Unfold(ExtendedSumDef), By(monoidal.IntervalPoint, MonoidalAdd))
		}),
})}

// SumSegmentPeel — the last term of a segment comes off the back of its
// sum: raising the upper bound by one adds the new term.
var SumSegmentPeel = sumSegmentPeelThm{family.Add(registry.ProofEntry{
	Name: "SumSegmentPeel",
	Key:  "prop_9f5c683971ac96a2",
	Build: family.Theorem("∀a:(num → extended_nonneg_real). ∀n:num. "+
		"    Σ_{i∈0 .. n + 1} a(i) = Σ_{i∈0 .. n} a(i) + a(n + 1)",
		func(arg *Argument, a *Arrow[Nat, ExtendedNonnegReal], n *Expr[Nat]) {
			arg.Do(Unfold(ExtendedSumDef))
			arg.Show(
				"the segment's recursion on its upper bound, n + 1 being suc(n)",
				By(monoidal.IntervalClauses, MonoidalAdd, nat_arith.Add1.At(n), nat_order.ZeroLessEq))
		}),
})}

// ExtendedSumZero — a ⟦0, ∞⟧ sum whose terms are 0 on the index set is
// 0: 0 is the neutral element of the fold, and a fold of the neutral
// element is the neutral element.
var ExtendedSumZero = extendedSumZeroThm{family.Add(registry.ProofEntry{
	Name: "ExtendedSumZero",
	Key:  "prop_2962a5051539fa37",
	Build: family.Theorem(Statement{
		Binders:    "∀f:(A → extended_nonneg_real). ∀s:set(A).",
		Hypotheses: []string{"∀i:A. i ∈ s ⇒ f(i) = &0"},
		Conclusion: "Σ_{i∈s} f(i) = &0",
	}, func(a *Argument, f *Arrow[A, ExtendedNonnegReal], s *Expr[Set[A]], vanish Fact) {
		a.Do(Unfold(ExtendedSumDef), Simp(Rev(NeutralAdd)))
		a.Show(
			"every term is the neutral element of the fold, and so is their fold",
			By(vanish, NeutralAdd, monoidal.EqNeutral.Read(MonoidalAdd).At(s, f)))
	}),
})}
