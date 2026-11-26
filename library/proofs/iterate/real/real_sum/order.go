// order.go — Σ read through ℝ's order: a sum is as large as its
// summands make it. A pointwise comparison of summands carries to the
// sums, positivity is inherited from the terms, and a per-term bound
// prices the whole sum by the count of its terms.
//
// In five parts marked by banners:
//
// - Comparing summands
// - Positivity
// - Pricing a sum by its count
// - Comparing index sets
// - The triangle inequality
//
// Closes marked `Normalized` land by simplification once the cited law
// is read at the goal's own point; the marker records that no
// refutation is wanted.

package real_sum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Comparing summands
// ---------------------------------------------------------------------------
//
// Everything in this movement descends from one transfer: a relation
// on ℝ that survives addition and holds of the element the fold starts
// from is carried by the fold from the summands to the sums. At ≤ that
// transfer is Monotone; a strict inequality at one point survives by
// splitting that point off and comparing what remains without it.
//
// The comparisons ask their index sets to be finite. That is not a
// convenience: past finiteness EITHER side can fall back to the
// convention's zero while the other remains a genuine sum, and no
// comparison of the summands says anything about zero.

// Monotone — a summand nowhere above another sums to no more. This is
// the part's one member that talks to the fold mechanism itself: read
// as a fold it is relation transfer, the relation "is at most" carried
// from the two summands to the two folds, and the two obligations the
// transfer asks of the relation are ℝ's to give.
var Monotone = monotoneThm{family.Add(registry.ProofEntry{
	Name: "Monotone",
	Key:  "prop_127fec69a504aac4",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f g:(A → real).",
			Hypotheses: []string{
				"finite(s)",
				"∀x:A. x ∈ s ⇒ f(x) ≤ g(x)",
			},
			Conclusion: "sum(s, f) ≤ sum(s, g)",
		},
		func(a *Argument, s *Expr[Set[A]], f, g *Arrow[A, Real],
			finite, pointwise Fact) {
			a.Do(Unfold(RealSumDef))
			respects := a.Have(
				"the order survives addition",
				"∀x₁ y₁ x₂ y₂:real. x₁ ≤ x₂ ∧ y₁ ≤ y₂ ⇒ x₁ + y₁ ≤ x₂ + y₂",
				By(real_order_ring.LessEqAdd2))
			fixesNeutral := a.Have(
				"and holds of the element the fold starts from",
				"neutral_elem(real_add) ≤ neutral_elem(real_add)",
				By(real_order_ring.LessEqRefl))
			a.Show(
				"so it reaches the two folds",
				By(finite, pointwise, respects, fixesNeutral, real_ring.MonoidalAdd, monoidal.Related))
		}),
})}

// StrictMonotone — a summand nowhere above another and strictly below
// it somewhere sums to strictly less. The strict point is split off:
// each sum is the value there together with the sum over the rest,
// the rests compare by Monotone, and adding a strict inequality to a
// non-strict one is strict.
var StrictMonotone = strictMonotoneThm{family.Add(registry.ProofEntry{
	Name: "StrictMonotone",
	Key:  "prop_17a9a5623dbbf41",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f g:(A → real). ∀a:A.",
			Hypotheses: []string{
				"finite(s)",
				"∀x:A. x ∈ s ⇒ f(x) ≤ g(x)",
				"a ∈ s",
				"f(a) < g(a)",
			},
			Conclusion: "sum(s, f) < sum(s, g)",
		},
		func(arg *Argument, s *Expr[Set[A]], f, g *Arrow[A, Real], a *Expr[A],
			finite, pointwise, inSet, strict Fact) {
			rest := arg.TermAs[Set[A]]("delete(s, a)")

			fSplit := arg.Have(
				"the sum splits at the strict point",
				"sum(s, f) = f(a) + sum(delete(s, a), f)",
				By(Normalized, finite, inSet, Delete.At(s, f, a), real_ring.SubAddLeft))
			gSplit := arg.Have(
				"and so does the other",
				"sum(s, g) = g(a) + sum(delete(s, a), g)",
				By(Normalized, finite, inSet, Delete.At(s, g, a), real_ring.SubAddLeft))
			restsCompare := arg.Have(
				"off that point the two sums compare",
				"sum(delete(s, a), f) ≤ sum(delete(s, a), g)",
				By(finite, pointwise, finite_set.FiniteDelete, set_basic.InDelete, Monotone.At(rest, f, g)))
			arg.Show(
				"and adding the strict inequality at the point keeps it strict",
				By(Normalized, fSplit, gSplit, restsCompare, strict, real_order_ring.LessThanLessEqAdd2))
		}),
})}

// StrictMonotoneAll — where the comparison is strict at every point, a
// single point suffices to invoke it, and a non-empty index set has
// one.
var StrictMonotoneAll = strictMonotoneAllThm{family.Add(registry.ProofEntry{
	Name: "StrictMonotoneAll",
	Key:  "prop_47ef36eec07a4b59",
	Build: family.Theorem(
		Statement{
			Binders: "∀f g:(A → real). ∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
				"s ≠ ∅",
				"∀x:A. x ∈ s ⇒ f(x) < g(x)",
			},
			Conclusion: "sum(s, f) < sum(s, g)",
		},
		func(a *Argument, f, g *Arrow[A, Real], s *Expr[Set[A]],
			finite, nonempty, pointwise Fact) {
			w, wIn := a.ObtainAs[A](
				"a non-empty index set has a point",
				"∃w:A. w ∈ s",
				By(nonempty, set_basic.MemberNotEmpty))
			// Obtain's witness is untyped; adopted at the index type.
			a.Show(
				"at w the comparison is strict, and everywhere it weakens to ≤",
				By(finite, pointwise, wIn, real_order_ring.LessEqOfLessThan, StrictMonotone.At(s, f, g, w)))
		}),
})}

// ---------------------------------------------------------------------------
// Positivity
// ---------------------------------------------------------------------------
//
// Nonnegativity contains the additive neutral and survives addition, so the
// fold's closure theorem carries it to every sum. Strict positivity compares
// against the zero summand and asks for a finite set with a positive term.

// Nonneg — nonnegative summands have a nonnegative sum, without a finiteness
// assumption: nonnegativity contains zero and is closed under addition.
var Nonneg = nonnegThm{family.Add(registry.ProofEntry{
	Name: "Nonneg",
	Key:  "prop_242b7b4f64e34c62",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → real).",
			Hypotheses: []string{
				"∀x:A. x ∈ s ⇒ &0 ≤ f(x)",
			},
			Conclusion: "&0 ≤ sum(s, f)",
		},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real], onSet Fact) {
			a.Show(
				"the fold preserves nonnegativity",
				Unfold(RealSumDef),
				By(
					onSet,
					real_ring.NeutralAdd,
					real_order_ring.LessEqRefl,
					real_order_ring.AddNonneg,
					monoidal.Closed.Read(real_ring.MonoidalAdd).At(
						a.TermAs[Set[Real]]("λx:real. &0 ≤ x"), s, f)))
		}),
})}

// Positive — a sum of nonnegative terms with a positive term somewhere
// is positive: the zero summand is nowhere above and strictly below at
// that point, and its sum is zero.
var Positive = positiveThm{family.Add(registry.ProofEntry{
	Name: "Positive",
	Key:  "prop_f5c5c9713d40ca26",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → real). ∀x:A.",
			Hypotheses: []string{
				"finite(s)",
				"∀i:A. i ∈ s ⇒ &0 ≤ f(i)",
				"x ∈ s",
				"&0 < f(x)",
			},
			Conclusion: "&0 < sum(s, f)",
		},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real], x *Expr[A],
			finite, nonneg, inSet, strict Fact) {
			zeros := a.TermAs[Fun[A, Real]]("λi:A. &0")
			a.Show(
				"the sum of zeros is zero, and it compares strictly against this one",
				By(Normalized, finite, nonneg, inSet, strict, Zero.At(s), StrictMonotone.At(s, zeros, f, x)))
		}),
})}

// PositiveAll — where every term is positive, any point of a non-empty
// index set is a witness for the one strict inequality Positive asks.
var PositiveAll = positiveAllThm{family.Add(registry.ProofEntry{
	Name: "PositiveAll",
	Key:  "prop_dd577d57b1752d62",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → real).",
			Hypotheses: []string{
				"finite(s)",
				"s ≠ ∅",
				"∀i:A. i ∈ s ⇒ &0 < f(i)",
			},
			Conclusion: "&0 < sum(s, f)",
		},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real],
			finite, nonempty, allPos Fact) {
			w, wIn := a.ObtainAs[A](
				"a non-empty index set has a point",
				"∃w:A. w ∈ s",
				By(nonempty, set_basic.MemberNotEmpty))
			a.Show(
				"every term is positive, in particular the one at w",
				By(finite, allPos, wIn, real_order_ring.LessEqOfLessThan, Positive.At(s, f, w)))
		}),
})}

// ---------------------------------------------------------------------------
// Pricing a sum by its count
// ---------------------------------------------------------------------------
//
// A bound b on every term prices the sum at b per member of the index
// set: compare against the constant summand, whose sum the chapter has
// counted as |s| copies of b. The members here are that comparison run
// non-strictly and strictly — the strict form once from one strict
// term and once from all — the average form that divides the price
// back out, and the reverse reading — a bound on a sum of nonnegative
// terms is a bound on each term, since the rest of the sum only helps —
// read once more at the bound zero: a vanishing sum of nonnegative
// terms vanishes termwise.

// Bound — a per-term bound prices the whole sum by the count of its
// terms: the summand is compared with the constant b, and the constant
// sums to one copy of b per member.
var Bound = boundThm{family.Add(registry.ProofEntry{
	Name: "Bound",
	Key:  "prop_58a4d26690044d76",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → real). ∀b:real.",
			Hypotheses: []string{
				"finite(s)",
				"∀x:A. x ∈ s ⇒ f(x) ≤ b",
			},
			Conclusion: "sum(s, f) ≤ &card(s) * b",
		},
		func(a *Argument) {
			a.Do(By(Monotone, Const))
		}),
})}

// BoundStrict — the same pricing run strictly: against the constant
// summand the comparison is strict at the one point assumed strict.
var BoundStrict = boundStrictThm{family.Add(registry.ProofEntry{
	Name: "BoundStrict",
	Key:  "prop_fe502363ed826d2f",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → real). ∀b:real. ∀x:A.",
			Hypotheses: []string{
				"finite(s)",
				"∀i:A. i ∈ s ⇒ f(i) ≤ b",
				"x ∈ s",
				"f(x) < b",
			},
			Conclusion: "sum(s, f) < &card(s) * b",
		},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real], b *Expr[Real],
			x *Expr[A], finite, perTerm, inSet, strict Fact) {
			theConstant := a.TermAs[Fun[A, Real]]("λi:A. b")
			a.Show(
				"the constant sums to one copy of b per member, and the comparison against it is strict at x",
				By(
					Normalized,
					finite,
					perTerm,
					inSet,
					strict,
					Const.At(s, b),
					StrictMonotone.At(s, f, theConstant, x)))
		}),
})}

// BoundByAverage — a sum whose every term is at most its share of b is
// at most b. This is Bound at the share b/|s|, and what remains is
// arithmetic: |s| copies of the share make up b, provided the count is
// not zero — which is what non-emptiness is for.
var BoundByAverage = boundByAverageThm{family.Add(registry.ProofEntry{
	Name: "BoundByAverage",
	Key:  "prop_71e7e4a5d6eae174",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → real). ∀b:real.",
			Hypotheses: []string{
				"finite(s)",
				"s ≠ ∅",
				"∀x:A. x ∈ s ⇒ f(x) ≤ b / &card(s)",
			},
			Conclusion: "sum(s, f) ≤ b",
		},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real], b *Expr[Real],
			finite, nonempty, perTerm Fact) {
			share := a.TermAs[Real]("b / &card(s)")
			counted := a.Have(
				"a non-empty finite set counts at least one member",
				"card(s) ≠ 0",
				By(Normalized, finite, nonempty, cardinality.CardEqZero.At(s)))
			whole := a.Have(
				"so the count times the per-member share is the whole",
				"&card(s) * (b / &card(s)) = b",
				By(Normalized, counted, real_construction.OfNumEq, field.DivLeftMul.Read(real_field.Field)))
			a.Show(
				"and the sum, at most a share per term, is at most the whole",
				By(Normalized, finite, perTerm, whole, Bound.At(s, f, share)))
		}),
})}

// BoundStrictAll — the strict pricing from a bound strict at every
// term: a non-empty index set supplies the one strict point BoundStrict
// asks, and the rest weaken to ≤.
var BoundStrictAll = boundStrictAllThm{family.Add(registry.ProofEntry{
	Name: "BoundStrictAll",
	Key:  "prop_8a2b8e8f14cb3897",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → real). ∀b:real.",
			Hypotheses: []string{
				"finite(s)",
				"s ≠ ∅",
				"∀x:A. x ∈ s ⇒ f(x) < b",
			},
			Conclusion: "sum(s, f) < &card(s) * b",
		},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real], b *Expr[Real],
			finite, nonempty, perTerm Fact) {
			w, wIn := a.ObtainAs[A](
				"a non-empty index set has a point",
				"∃w:A. w ∈ s",
				By(nonempty, set_basic.MemberNotEmpty))
			a.Show(
				"the bound is strict at w, and everywhere it weakens to ≤",
				By(finite, perTerm, wIn, real_order_ring.LessEqOfLessThan, BoundStrict.At(s, f, b, w)))
		}),
})}

// TermBound — the pricing read back: where every term is nonnegative,
// a bound on the sum is a bound on each term, because the sum is that
// term together with a remainder that only helps. No induction is
// needed — the sum splits at the term, and the remainder is a sum of
// nonnegative terms.
var TermBound = termBoundThm{family.Add(registry.ProofEntry{
	Name: "TermBound",
	Key:  "prop_107e81ccb9964159",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → real). ∀b:real. ∀x:A.",
			Hypotheses: []string{
				"finite(s)",
				"∀x:A. x ∈ s ⇒ &0 ≤ f(x)",
				"sum(s, f) ≤ b",
				"x ∈ s",
			},
			Conclusion: "f(x) ≤ b",
		},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real], b *Expr[Real],
			finite, nonneg, whole Fact) {
			x := a.FixAs[A]()
			inSet := a.Assume()
			rest := a.TermAs[Set[A]]("delete(s, x)")

			split := a.Have(
				"the sum splits at x",
				"sum(s, f) = f(x) + sum(delete(s, x), f)",
				By(Normalized, finite, inSet, Delete.At(s, f, x), real_ring.SubAddLeft))
			restNonneg := a.Have(
				"and what the rest contributes is nonnegative",
				"&0 ≤ sum(delete(s, x), f)",
				By(Normalized, nonneg, set_basic.InDelete, Nonneg.At(rest, f)))
			a.Show(
				"so the term at x is within the sum, and the sum within the bound",
				By(
					Normalized,
					split,
					restNonneg,
					whole,
					real_order_ring.LessEqSelfAddRight,
					real_construction.LessEqTrans))
		}),
})}

// NonnegEqZero — a sum of nonnegative terms that vanishes has every
// term vanish. This is TermBound read at the bound zero: the vanishing
// sum is in particular at most zero, so each term is at most zero, and
// a nonnegative term at most zero is zero.
var NonnegEqZero = nonnegEqZeroThm{family.Add(registry.ProofEntry{
	Name: "NonnegEqZero",
	Key:  "prop_6e21f86606dbf251",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → real). ∀x:A.",
			Hypotheses: []string{
				"finite(s)",
				"∀x:A. x ∈ s ⇒ &0 ≤ f(x)",
				"sum(s, f) = &0",
				"x ∈ s",
			},
			Conclusion: "f(x) = &0",
		},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real],
			finite, nonneg, vanishes Fact) {
			x := a.FixAs[A]()
			inSet := a.Assume()
			zero := a.TermAs[Real]("&0")

			sumBound := a.Have(
				"the vanishing sum is in particular at most zero",
				"sum(s, f) ≤ &0",
				By(vanishes, real_order_ring.LessEqRefl))
			upper := a.Have(
				"so the term at x is at most zero, the rest of the sum only helping",
				"f(x) ≤ &0",
				By(finite, nonneg, sumBound, inSet, TermBound.At(s, f, zero, x)))
			lower := a.Have(
				"while it is at least zero, being one of the nonnegative terms",
				"&0 ≤ f(x)",
				By(inSet, nonneg.At(x)))
			a.Show(
				"and a nonnegative term at most zero is zero",
				By(upper, lower, real_construction.LessEqAntisym.At(f.Apply(x), zero)))
		}),
})}

// ---------------------------------------------------------------------------
// Comparing index sets
// ---------------------------------------------------------------------------
//
// The part above compares two summands over one index set; this one
// compares one summand over two index sets. The instrument is a
// partition: each index set is what it shares with the other together
// with what it keeps to itself, the shared parts contribute the same
// sum to both sides, and only the private parts have to be priced.
// Everything else in the part reads that comparison at a particular
// pair of sets — a subset against its superset, a set against a family
// of fibres that covers it, an image against what it is the image of.

// SubsetSigned — two index sets compare by their sums as soon as the
// summand is signed the right way where they differ: at most zero on
// what only u has, at least zero on what only v has. The shared part
// contributes the same to both sums, and each private part is compared
// against the zero summand over the same points.
var SubsetSigned = subsetSignedThm{family.Add(registry.ProofEntry{
	Name: "SubsetSigned",
	Key:  "prop_23b0e315a59069ef",
	Build: family.Theorem(
		Statement{
			Binders: "∀u v:set(A). ∀f:(A → real).",
			Hypotheses: []string{
				"finite(u)",
				"finite(v)",
				"(∀x:A. x ∈ u ∖ v ⇒ f(x) ≤ &0) ∧ (∀x:A. x ∈ v ∖ u ⇒ &0 ≤ f(x))",
			},
			Conclusion: "sum(u, f) ≤ sum(v, f)",
		},
		func(a *Argument, u, v *Expr[Set[A]], f *Arrow[A, Real],
			finiteU, finiteV, signed Fact) {
			shared := a.TermAs[Set[A]]("u ∩ v")
			uOnly := a.TermAs[Set[A]]("u ∖ v")
			vOnly := a.TermAs[Set[A]]("v ∖ u")
			zeros := a.TermAs[Fun[A, Real]]("λx:A. &0")

			uParts := a.Have(
				"u is what it shares with v together with what it keeps to itself",
				"u ∩ v ∪ (u ∖ v) = u",
				BySets())
			uApart := a.Have(
				"and those two parts hold no point in common",
				"disjoint(u ∩ v, u ∖ v)",
				BySets())
			vParts := a.Have(
				"v splits against u the same way",
				"u ∩ v ∪ (v ∖ u) = v",
				BySets())
			vApart := a.Have(
				"its parts likewise apart",
				"disjoint(u ∩ v, v ∖ u)",
				BySets())

			uSplit := a.Have(
				"so u's sum is the shared part's sum plus its private part's",
				"sum(u, f) = sum(u ∩ v, f) + sum(u ∖ v, f)",
				By(
					Normalized,
					finiteU,
					uParts,
					uApart,
					finite_set.FiniteInter,
					finite_set.FiniteDiff,
					Union.At(shared, uOnly, f)))
			vSplit := a.Have(
				"and v's sum splits the same way",
				"sum(v, f) = sum(u ∩ v, f) + sum(v ∖ u, f)",
				By(
					Normalized,
					finiteV,
					vParts,
					vApart,
					finite_set.FiniteInter,
					finite_set.FiniteDiff,
					Union.At(shared, vOnly, f)))

			uPrivateSum := a.TermAs[Real]("sum(u ∖ v, f)")
			vPrivateSum := a.TermAs[Real]("sum(v ∖ u, f)")
			sharedSum := a.TermAs[Real]("sum(u ∩ v, f)")
			privates := a.CalcOrder(real_order_ring.OrderCalc(a.Ctx()), uPrivateSum,
				LeLeg(
					a.TermAs[Real]("&0"),
					"what u keeps to itself contributes at most nothing "+
						"— there its summand is nowhere above the zero one",
					By(Normalized, finiteU, signed, finite_set.FiniteDiff, Monotone.At(uOnly, f, zeros), Zero)),
				LeLeg(
					vPrivateSum,
					"while what v keeps to itself contributes at least nothing",
					By(signed, Nonneg.At(vOnly, f))))
			a.Show(
				"the shared contribution is common, and the private ones compare across zero",
				By(uSplit, vSplit, privates, real_order_ring.LessEqAddLeft.At(sharedSum, uPrivateSum, vPrivateSum)))
		}),
})}

// Subset — a sum only grows from a subset to its superset, provided
// the terms picked up along the way are nonnegative. This is the
// signed comparison with one side vacuous: a subset keeps no point to
// itself, so the sign condition there asks nothing.
var Subset = subsetThm{family.Add(registry.ProofEntry{
	Name: "Subset",
	Key:  "prop_3a947934c8af12d7",
	Build: family.Theorem(
		Statement{
			Binders: "∀u v:set(A). ∀f:(A → real).",
			Hypotheses: []string{
				"finite(v)",
				"u ⊆ v",
				"∀x:A. x ∈ v ∖ u ⇒ &0 ≤ f(x)",
			},
			Conclusion: "sum(u, f) ≤ sum(v, f)",
		},
		func(a *Argument, u, v *Expr[Set[A]], f *Arrow[A, Real],
			finite, contained, offPart Fact) {
			smaller := a.Have(
				"a subset of a finite index set is itself finite",
				"finite(u)",
				By(finite, contained, finite_set.FiniteSubset.At(u, v)))
			nothingKept := a.Have(
				"and u keeps no point to itself, so the sign condition there is vacuous",
				"∀x:A. x ∈ u ∖ v ⇒ f(x) ≤ &0",
				BySets(contained))
			a.Show(
				"so the signed comparison applies, one of its two sign conditions empty",
				By(smaller, finite, nothingKept, offPart, SubsetSigned))
		}),
})}

// Covered — one sum is within another as soon as every index of the
// first is answered for by an index of the second: i sends y ∈ t to
// x ∈ s with f(x) ≤ g(y), and g is nonnegative on t. The proof reads
// real_sum(t, g) through i's fibres: over each fibre the answering point
// alone contributes at least f's value, the rest of the fibre only
// helps, and the fibres that answer for nothing still contribute at
// least zero.
var Covered = coveredThm{family.Add(registry.ProofEntry{
	Name: "Covered",
	Key:  "prop_c899c4aad65130ec",
	Build: family.Sections(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B). ∀i:(B → A). ∀f:(A → real). ∀g:(B → real).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
				"∀y:B. y ∈ t ⇒ &0 ≤ g(y)",
				"∀x:A. x ∈ s ⇒ ∃y:B. y ∈ t ∧ i(y) = x ∧ f(x) ≤ g(y)",
			},
			Conclusion: "sum(s, f) ≤ sum(t, g)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// A fibre of i over x, summed, is at least zero wherever g is
			// nonnegative on t — whether or not the fibre answers for any
			// point. This is what prices the fibres that cover nothing.
			fibreNonneg := ctx.Lemma(
				Statement{
					Binders: "∀t:set(B). ∀g:(B → real). ∀i:(B → A).",
					Hypotheses: []string{
						"∀y:B. y ∈ t ⇒ &0 ≤ g(y)",
					},
					Conclusion: "∀x:A. &0 ≤ sum({z:B | z ∈ t ∧ i(z) = x}, g)",
				},
				func(a *Argument, t *Expr[Set[B]], g *Arrow[B, Real], i *Arrow[B, A],
					nonneg Fact) {
					a.Fix("x")
					onFibre := a.Have(
						"the fibre's points are points of t, where the summand is nonnegative",
						"∀z:B. z ∈ {z:B | z ∈ t ∧ i(z) = x} ⇒ &0 ≤ g(z)",
						BySets(nonneg))
					a.Show(
						"so the fibre's sum is at least zero",
						By(onFibre, Nonneg.Inst[B]()))
				})

			// And over a point the coverage answers for, the fibre's sum
			// is at least f's value there: the answering y contributes at
			// least that much on its own, and the rest of the fibre only
			// helps.
			pointBelow := ctx.Lemma(
				"∀t:set(B). ∀g:(B → real). ∀i:(B → A). ∀s:set(A). ∀f:(A → real). "+
					"    finite(t) ⇒ "+
					"    (∀y:B. y ∈ t ⇒ &0 ≤ g(y)) ⇒ "+
					"    (∀x:A. x ∈ s ⇒ ∃y:B. y ∈ t ∧ i(y) = x ∧ f(x) ≤ g(y)) ⇒ "+
					"    ∀x:A. x ∈ s ⇒ f(x) ≤ sum({z:B | z ∈ t ∧ i(z) = x}, g)",
				func(a *Argument, t *Expr[Set[B]], g *Arrow[B, Real], i *Arrow[B, A],
					s *Expr[Set[A]], f *Arrow[A, Real], finite, nonneg, covered Fact) {
					a.Fix("x")
					inS := a.Assume()
					y, caughtBy := a.ObtainAs[B](
						"some point of t answers for x",
						"∃y:B. y ∈ t ∧ i(y) = x ∧ f(x) ≤ g(y)",
						By(inS, covered))

					fibreInT := a.Have(
						"the fibre over x lies inside t",
						"{z:B | z ∈ t ∧ i(z) = x} ⊆ t",
						BySets())
					fibreFinite := a.Have(
						"so it is finite along with t",
						"finite({z:B | z ∈ t ∧ i(z) = x})",
						By(finite, fibreInT, finite_set.FiniteSubset.Inst[B]()))
					caught := a.Have(
						"and it holds the answering point",
						"y ∈ {z:B | z ∈ t ∧ i(z) = x}",
						BySets(caughtBy))
					peel := a.Have(
						"so its sum splits off the value at y",
						"sum(delete({z:B | z ∈ t ∧ i(z) = x}, y), g) = sum({z:B | z ∈ t ∧ i(z) = x}, g) - g(y)",
						By(fibreFinite, caught, Delete.Inst[B]()))
					rest := a.TermAs[Set[B]]("delete({z:B | z ∈ t ∧ i(z) = x}, y)")
					restNonneg := a.Have(
						"what the fibre holds beyond y only helps",
						"&0 ≤ sum(delete({z:B | z ∈ t ∧ i(z) = x}, y), g)",
						Derive(func(b *Argument) {
							restOnT := b.Have(
								"what the fibre holds beyond y are points of t, where g is nonnegative",
								"∀w:B. w ∈ delete({z:B | z ∈ t ∧ i(z) = x}, y) ⇒ &0 ≤ g(w)",
								BySets(nonneg))
							b.Show(
								"so their sum is at least zero",
								By(restOnT, Nonneg.At(rest, g)))
						}))

					fibreSum := a.TermAs[Real]("sum({z:B | z ∈ t ∧ i(z) = x}, g)")
					gAtY := g.Apply(y)
					a.Show(
						"f's value at x is within g's at y, and that within the fibre's whole sum",
						real_order_ring.OrderCalc(a.Ctx()).Calc(a.TermAs[Real]("f(x)"),
							LeLeg(
								gAtY,
								"f's value at x is within g's at the answering point",
								By(caughtBy)),
							LeLeg(
								fibreSum,
								"and that within the fibre's whole sum, the rest of the fibre only helping",
								By(peel, restNonneg, real_order_ring.SubNonneg.At(fibreSum, gAtY)))))
				})

			return ctx.Theorem(headline, func(a *Argument, s *Expr[Set[A]],
				t *Expr[Set[B]], i *Arrow[B, A], f *Arrow[A, Real], g *Arrow[B, Real],
				finiteS, finiteT, nonneg, covered Fact) {
				fibreTotals := a.TermAs[Fun[A, Real]](
					"λx:A. sum({z:B | z ∈ t ∧ i(z) = x}, g)")

				grouped := a.Have(
					"summing g over t is summing each fibre of i, and the fibre totals over the image",
					"sum(t, g) = sum(image(i, t), λx:A. sum({z:B | z ∈ t ∧ i(z) = x}, g))",
					By(finiteT, Fibres.Inst(TypeBinder.BindA[B](), TypeBinder.BindB[A]())))
				pointwise := a.Have(
					"on s each summand is within its own fibre's total",
					"∀x:A. x ∈ s ⇒ f(x) ≤ sum({z:B | z ∈ t ∧ i(z) = x}, g)",
					By(finiteT, nonneg, covered, pointBelow))
				imageFinite := a.Have(
					"the image of the finite t is finite",
					"finite(image(i, t))",
					By(finiteT, finite_set.FiniteImage.Inst(TypeBinder.BindA[B](), TypeBinder.BindB[A]())))
				contained := a.Have(
					"the coverage puts every point of s in that image",
					"s ⊆ image(i, t)",
					BySets(covered))
				fibresNonneg := a.Have(
					"while every fibre total, covering or not, is at least zero",
					"∀x:A. &0 ≤ sum({z:B | z ∈ t ∧ i(z) = x}, g)",
					By(nonneg, At(fibreNonneg, t, g, i)))

				withinImageTotals := a.CalcOrder(real_order_ring.OrderCalc(a.Ctx()),
					a.TermAs[Real]("sum(s, f)"),
					LeLeg(
						a.TermAs[Real]("sum(s, λx:A. sum({z:B | z ∈ t ∧ i(z) = x}, g))"),
						"so over s the sum of f is within the sum of fibre totals",
						By(finiteS, pointwise, Monotone.At(s, f, fibreTotals))),
					LeLeg(
						a.TermAs[Real]("sum(image(i, t), λx:A. sum({z:B | z ∈ t ∧ i(z) = x}, g))"),
						"and the fibre totals only grow from s to the whole image",
						By(imageFinite, contained, fibresNonneg, Subset)))
				a.Show(
					"and the image's fibre totals add up to sum(t, g) exactly",
					By(grouped, withinImageTotals))
			})
		}),
})}

// ImageLessEq — a sum over an image is at most the sum of the
// composite over the source, wherever the composite is nonnegative.
// This is the covered comparison read at the image: f itself sends
// each source point onto the image point it answers for, at no loss —
// the two summands agree there exactly.
var ImageLessEq = imageLessEqThm{family.Add(registry.ProofEntry{
	Name: "ImageLessEq",
	Key:  "prop_b66a3e2cc9c8c4c0",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → B). ∀g:(B → real).",
			Hypotheses: []string{
				"finite(s)",
				"∀x:A. x ∈ s ⇒ &0 ≤ g(f(x))",
			},
			Conclusion: "sum(image(f, s), g) ≤ sum(s, g ∘ f)",
		},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, B], g *Arrow[B, Real],
			finite, nonneg Fact) {
			compose := a.Have(
				"the composite reads g at the image point",
				"∀y:A. (g ∘ f)(y) = g(f(y))",
				By(functions.ComposeApply.Inst(TypeBinder.BindA[A](),
					TypeBinder.BindB[B](), TypeBinder.BindC[Real]())))
			nonnegAfter := a.Have(
				"so the composite is nonnegative across s",
				"∀y:A. y ∈ s ⇒ &0 ≤ (g ∘ f)(y)",
				By(Normalized, compose, nonneg))
			imageFinite := a.Have(
				"the image of the finite s is finite",
				"finite(image(f, s))",
				By(finite, finite_set.FiniteImage))
			cover := a.Have(
				"and each image point is answered for by a source point, the two summands agreeing there",
				"∀x:B. x ∈ image(f, s) ⇒ ∃y:A. y ∈ s ∧ f(y) = x ∧ g(x) ≤ (g ∘ f)(y)",
				By(
					Normalized,
					compose,
					set_basic.InImage.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]()),
					real_order_ring.LessEqRefl))

			img := a.TermAs[Set[B]]("image(f, s)")
			gAfterF := a.TermAs[Fun[A, Real]]("g ∘ f")
			a.Show(
				"so the covered comparison prices the image sum through the source",
				By(imageFinite, finite, nonnegAfter, cover, Covered.At(img, s, f, g, gAfterF)))
		}),
})}

// ---------------------------------------------------------------------------
// The triangle inequality
// ---------------------------------------------------------------------------
//
// |Σf| ≤ Σ|f|: a sum is no larger in size than the sum of its terms'
// sizes. The two-term triangle inequality is ℝ's; carrying it to a
// finite sum is an induction on the index set, and it is the one
// induction this half of the movement runs — the members after it are
// that bound met by the comparisons already proved: a pointwise
// domination of the sizes, a per-term price on them, and its reading
// where the interval is the index set, beside the interval calculus.

// Triangle — the size of a sum is at most the sum of the sizes.
var Triangle = triangleThm{family.Add(registry.ProofEntry{
	Name: "Triangle",
	Key:  "prop_7252d1ea321e90dd",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → real).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "|sum(s, f)| ≤ sum(s, λx:A. |f(x)|)",
		},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real], finite Fact) {
			a.Show(
				"the size bound holds of every finite index set, s among them",
				ByInduction(finite_set.FiniteInductFresh, finite,

					Case(
						"∅: both sums are zero, and zero is exactly its own size",
						By(Clauses, real_sgn_abs.AbsOfZero, real_order_ring.LessEqRefl)),

					Case(
						"insert: the new term's size joins by the two-term "+
							"triangle inequality, the rest by the bound carried",
						Derive(func(b *Argument) {
							x := b.FixAs[A]()
							b.FixAs[Set[A]]("t")  // the set the point enlarges
							carried := b.Assume() // the bound at t, x ∉ t, finite(t)

							splitRaw := b.Have(
								"the enlarged sum is the new value plus the old sum",
								"sum(insert(x, t), f) = f(x) + sum(t, f)",
								By(carried, Clauses))
							splitSizes := b.Have(
								"and the sum of sizes enlarges the same way",
								"sum(insert(x, t), λy:A. |f(y)|) = |f(x)| + sum(t, λy:A. |f(y)|)",
								By(carried, Clauses))

							newSize := b.TermAs[Real]("|f(x)|")
							restSum := b.TermAs[Real]("sum(t, f)")
							restSize := b.TermAs[Real]("|sum(t, f)|")
							restSizes := b.TermAs[Real]("sum(t, λy:A. |f(y)|)")
							estimate := b.CalcOrder(real_order_ring.OrderCalc(b.Ctx()),
								b.TermAs[Real]("|sum(insert(x, t), f)|"),
								LeLeg(
									b.TermAs[Real]("|f(x)| + |sum(t, f)|"),
									"the whole's size is within the new size plus the rest's "+
										"size — the two-term triangle inequality on the split sum",
									By(splitRaw, real_sgn_abs.AbsTriangle.At(f.Apply(x), restSum))),
								LeLeg(
									b.TermAs[Real]("|f(x)| + sum(t, λy:A. |f(y)|)"),
									"and the rest's size within the rest's sum of sizes, by the bound carried",
									// the carried bound meets its shifted instance by simplification alone
									By(carried, real_order_ring.LessEqAddLeft.At(newSize, restSize, restSizes))))
							b.Show(
								"which is the enlarged sum of sizes",
								By(splitSizes, estimate))
						}))))
		}),
})}

// Dominated — anything that dominates the sizes of the terms bounds
// the size of the sum: the triangle inequality prices the sum by its
// sum of sizes, and the dominator prices that.
var Dominated = dominatedThm{family.Add(registry.ProofEntry{
	Name: "Dominated",
	Key:  "prop_beaa84a4af8985da",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f g:(A → real).",
			Hypotheses: []string{
				"finite(s)",
				"∀x:A. x ∈ s ⇒ |f(x)| ≤ g(x)",
			},
			Conclusion: "|sum(s, f)| ≤ sum(s, g)",
		},
		func(a *Argument, s *Expr[Set[A]], f, g *Arrow[A, Real],
			finite, dominates Fact) {
			sizes := a.TermAs[Fun[A, Real]]("λx:A. |f(x)|")
			a.Show(
				"so the sum's size is within g's sum",
				real_order_ring.OrderCalc(a.Ctx()).Calc(a.TermAs[Real]("|sum(s, f)|"),
					LeLeg(
						a.TermAs[Real]("sum(s, λx:A. |f(x)|)"),
						"the sum is within its own sum of sizes",
						By(finite, Triangle)),
					LeLeg(
						a.TermAs[Real]("sum(s, g)"),
						"whose terms g dominates pointwise",
						By(finite, dominates, Monotone.At(s, sizes, g)))))
		}),
})}

// TriangleBound — a uniform bound on the sizes of the terms prices the
// size of the sum by the count of its terms: the triangle inequality
// prices the sum by its sum of sizes, and the per-term price counts
// those.
var TriangleBound = triangleBoundThm{family.Add(registry.ProofEntry{
	Name: "TriangleBound",
	Key:  "prop_a503eb1604dcdc6f",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → real). ∀b:real.",
			Hypotheses: []string{
				"finite(s)",
				"∀x:A. x ∈ s ⇒ |f(x)| ≤ b",
			},
			Conclusion: "|sum(s, f)| ≤ &card(s) * b",
		},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real], b *Expr[Real],
			finite, perTerm Fact) {
			sizes := a.TermAs[Fun[A, Real]]("λx:A. |f(x)|")
			a.Show(
				"so the sum's size is within the count times the bound",
				real_order_ring.OrderCalc(a.Ctx()).Calc(a.TermAs[Real]("|sum(s, f)|"),
					LeLeg(
						a.TermAs[Real]("sum(s, λx:A. |f(x)|)"),
						"the sum is within its own sum of sizes",
						By(finite, Triangle)),
					LeLeg(
						a.TermAs[Real]("&card(s) * b"),
						"and each size at most b, so their sum is at most b per member",
						By(finite, perTerm, Bound.At(s, sizes, b)))))
		}),
})}
