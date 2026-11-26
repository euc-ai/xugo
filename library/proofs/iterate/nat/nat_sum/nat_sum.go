// nat_sum.go — the chapter: what natural addition contributes to the
// fold, and the fold's laws read at ℕ.
//
// Four parts, marked by banners:
//
// - The bridge: natural addition folds
// - The fold's laws at ℕ
// - The ℕ-proper readings
// - Common divisors and multiples

package nat_sum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The bridge: natural addition folds
// ---------------------------------------------------------------------------
//
// The fold mechanism is carrier-free: it asks of an operation only that
// it commute, associate, and have a neutral element, and everything it
// proves is proved from those three. The chapter's opening move is to
// supply them for natural addition. Once these two facts are in hand,
// every law of the mechanism instantiates at `+`.

// NeutralNatAdd — the element addition folds from is zero.
//
// `neutral_elem op` is defined by Hilbert choice: it names some element that
// is a two-sided identity for op, and says nothing about which. Nothing
// more is needed, because an identity is unique — whatever element the
// choice lands on, call it z, the two identity laws read against each
// other give z = z + 0 = 0.
var NeutralNatAdd = neutralNatAddThm{family.Add(registry.ProofEntry{
	Name: "NeutralNatAdd",
	Key:  "prop_2a4bd00f1dc9c1c0",
	Build: family.Theorem("neutral_elem(+) = 0",
		func(a *Argument) {
			// Unfolding leaves the ε-term itself as the goal's left
			// side; the identity laws pin it from both sides at once,
			// which is what the defining predicate asks for.
			a.Do(Unfold(monoidal.NeutralElemDef), By(nat_arith.AddLeftZeroClause, nat_arith.AddZero))
		}),
})}

// MonoidalNatAdd — natural addition folds: it commutes, it associates,
// and zero is its neutral element.
//
// The first two conjuncts are ℕ's additive laws verbatim, so each cite
// lands on its case whole. The third is stated about `neutral_elem(+)`
// rather than about `0`, which is why computing the neutral above had
// to come first.
var MonoidalNatAdd = monoidalNatAddThm{family.Add(registry.ProofEntry{
	Name: "MonoidalNatAdd",
	Key:  "prop_b10ea1193468d5ee",
	Build: family.Theorem("monoidal_op(+)",
		func(a *Argument) {
			a.Do(Unfold(monoidal.MonoidalOpDef), SplitConjAll(
				Case(
					"addition commutes",
					Cite(nat_arith.AddSym)),
				Case(
					"addition associates",
					Cite(nat_arith.AddAssoc)),
				// The identity conjunct is stated at `neutral_elem(+)`, so the
				// neutral is REWRITTEN to 0 and the zero law then reads the
				// conjunct whole.
				Case(
					"the neutral element is a left identity",
					Simp(Fwd(NeutralNatAdd)),
					Cite(nat_arith.AddLeftZeroClause)),
			))
		}),
})}

// CommMonoidNatAdd — natural addition, with zero, is a commutative monoid:
// the operation folds, and the bridge back from the fold mechanism's reading
// (comm_monoid.FromMonoidal) makes it the structure at its neutral element,
// which is 0.
var CommMonoidNatAdd = commMonoidNatAddThm{family.Add(registry.ProofEntry{
	Name: "CommMonoidNatAdd",
	Key:  "prop_7f89b71c2a5e805f",
	Build: family.Theorem("comm_monoid(+, 0)", By(
		Normalized,
		comm_monoid.FromMonoidal,
		MonoidalNatAdd,
		NeutralNatAdd)),
})}

// ---------------------------------------------------------------------------
// The fold's laws at ℕ
// ---------------------------------------------------------------------------
//
// With the bridge in hand the mechanism's laws are available here for
// the asking, and every member of this part is one of them read at
// natural addition. The mathematics is the fold's own, proved there of
// an arbitrary commutative monoid rather than of ℕ: `nat_sum` IS the fold
// at `+`, so unfolding the definition turns the goal into a statement
// about `iterated_op` and the law closes it. What is proper to each member
// is which law it wants, and whether reading that law at ℕ needs to
// know what the neutral element is.
//
// A law is applied, not searched for: the goal is an instance of the
// law's conclusion, and the law's antecedents — that the operation is
// monoidal, whatever the statement assumed — are already in hand. So a
// member cites the law and the bridge, bare, and nothing else is
// needed even where every leading slot of the law is higher-order (an
// operation, a property, index sets, summands): the goal spells all of
// them.

// Congruence — a sum sees the summand only on the index set, so two
// summands agreeing there give the same sum.
var Congruence = congruenceThm{family.Add(registry.ProofEntry{
	Name: "Congruence",
	Key:  "prop_918ceefbb77f71ef",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀g f:(A → num).",
			Hypotheses: []string{
				"∀x:A. x ∈ s ⇒ g(x) = f(x)",
			},
			Conclusion: "sum(s, g) = sum(s, f)",
		},
		func(a *Argument) {
			a.Do(Unfold(NatSumDef), By(monoidal.Congruence, MonoidalNatAdd))
		}),
})}

// Superset — enlarging the index set past the points where the summand
// vanishes does not change the sum.
var Superset = supersetThm{family.Add(registry.ProofEntry{
	Name: "Superset",
	Key:  "prop_5a1508c4d1fa2c24",
	Build: family.Theorem(
		Statement{
			Binders: "∀u v:set(A). ∀f:(A → num).",
			Hypotheses: []string{
				"u ⊆ v",
				"∀x:A. x ∈ v ∧ x ∉ u ⇒ f(x) = 0",
			},
			Conclusion: "sum(u, f) = sum(v, f)",
		},
		func(a *Argument) {
			a.Do(Unfold(NatSumDef), By(monoidal.Superset, MonoidalNatAdd, NeutralNatAdd))
		}),
})}

// Union — a sum splits across two disjoint finite index sets.
var Union = unionThm{family.Add(registry.ProofEntry{
	Name: "Union",
	Key:  "prop_80a451bfe249b028",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A). ∀f:(A → num).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
				"disjoint(s, t)",
			},
			Conclusion: "sum(s ∪ t, f) = sum(s, f) + sum(t, f)",
		},
		func(a *Argument) {
			a.Do(Unfold(NatSumDef), By(monoidal.Union, MonoidalNatAdd))
		}),
})}

// Restrict — summing over the part of an index set a test accepts is
// summing over the whole of it with the summand silenced where the test
// fails.
var Restrict = restrictThm{family.Add(registry.ProofEntry{
	Name: "Restrict",
	Key:  "prop_7be4fdc056e0546c",
	Build: family.Theorem(
		"∀s:set(A). ∀P:(A → bool). ∀f:(A → num). "+
			"    sum({x | x ∈ s ∧ P(x)}, f) = sum(s, λx:A. COND(P(x), f(x), 0))",
		func(a *Argument) {
			a.Do(Unfold(NatSumDef), By(monoidal.Restrict, MonoidalNatAdd, NeutralNatAdd))
		}),
})}

// Clauses — the recursion of Σ over ℕ: the empty sum is 0, and
// inserting a point into a finite index set either changes nothing,
// because the point was already there, or contributes its own value.
var Clauses = clausesThm{family.Add(registry.ProofEntry{
	Name: "Clauses",
	Key:  "prop_21b201fee3009d1b",
	Build: family.Theorem(
		"(∀f:(A → num). sum(∅, f) = 0) ∧ "+
			"(∀g:(C → num). ∀x:C. ∀s:set(C). "+
			"    finite(s) ⇒ sum(insert(x, s), g) = COND(x ∈ s, sum(s, g), g(x) + sum(s, g)))",
		func(a *Argument) {
			a.Do(Unfold(NatSumDef), By(monoidal.Clauses, MonoidalNatAdd, NeutralNatAdd))
		}),
})}

// UnionEq — the disjoint-union law read where the union is given as an
// equation: an index set u that is the union of two sets meeting in ∅
// carries the sum of their two sums. Union asks the two halves to be
// finite and disjoint, and both come out of what is given — an empty
// meet is disjointness by definition, and each half is bounded by their
// union u, which is finite.
var UnionEq = unionEqThm{family.Add(registry.ProofEntry{
	Name: "UnionEq",
	Key:  "prop_2537e6881eabb14e",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t u:set(A). ∀f:(A → num).",
			Hypotheses: []string{
				"finite(u)",
				"s ∩ t = ∅ ∧ s ∪ t = u",
			},
			Conclusion: "sum(s, f) + sum(t, f) = sum(u, f)",
		},
		func(a *Argument, s, t, u *Expr[Set[A]], f *Arrow[A, Nat], given Fact) {
			// Unfolding leaves `s ∩ t = ∅`, which is one of the given
			// conjuncts, so the unfolding closes the claim by itself.
			disjoint := a.Have(
				"an empty meet is disjointness, by definition",
				"disjoint(s, t)",
				Unfold(set_basic.DisjointDef))
			bothFinite := a.Have(
				"each half is bounded by their union u, which is finite",
				"finite(s) ∧ finite(t)",
				// Normalized: the given equation rewrites the finite union
				// into u, and the reading of the law is then in hand.
				By(Normalized, given, At(finite_set.FiniteUnion, s, t))) // finite(s ∪ t) ⇔ finite(s) ∧ finite(t)
			// Normalized: the given equation rewrites the law's union into
			// u, and its guards meet the two facts above by simplification.
			a.Show(
				"so the disjoint-union law applies, and the union it sums over is u",
				By(
					Normalized,
					given,
					disjoint,
					bothFinite,
					At(Union, s, t, f))) // nat_sum(s ∪ t, f) = nat_sum(s, f) + nat_sum(t, f)
		}),
})}

// Image — a sum over the image of a map that is one-to-one on the index
// set is the sum over the index set itself, of the summand read after
// the map: reindexing a sum changes nothing as long as no two indices
// land on one point.
var Image = imageThm{family.Add(registry.ProofEntry{
	Name: "Image",
	Key:  "prop_b128fd0ff0723f2a",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → B). ∀g:(B → num).",
			Hypotheses: []string{
				"injective_on(s, f)",
			},
			Conclusion: "sum(image(f, s), g) = sum(s, g ∘ f)",
		},
		func(a *Argument) {
			a.Do(Unfold(NatSumDef), By(monoidal.Image, MonoidalNatAdd))
		}),
})}

// Swap — a sum of sums does not care which of its two index sets is
// taken first. Both have to be finite, that being where the recursion
// reaches on either side.
var Swap = swapThm{family.Add(registry.ProofEntry{
	Name: "Swap",
	Key:  "prop_509082e88672a2c3",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B). ∀f:(A → B → num).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
			},
			Conclusion: "sum(s, λi:A. sum(t, f(i))) = sum(t, λj:B. sum(s, λi:A. f(i, j)))",
		},
		func(a *Argument) {
			a.Do(Unfold(NatSumDef), By(monoidal.Swap, MonoidalNatAdd))
		}),
})}

// Add — two sums over one finite index set add termwise. The fold
// mechanism proves this of any operation that folds (a fold of pointwise
// combinations is the combination of the folds), so the proof is that
// law read at natural addition.
var Add = addThm{family.Add(registry.ProofEntry{
	Name: "Add",
	Key:  "prop_206c35bb9394a740",
	Build: family.Theorem(
		Statement{
			Binders: "∀f g:(A → num). ∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "sum(s, f) + sum(s, g) = sum(s, λx:A. f(x) + g(x))",
		},
		func(a *Argument) {
			a.Do(Unfold(NatSumDef), By(monoidal.Pointwise, MonoidalNatAdd))
		}),
})}

// ScalarLeft — a factor common to every term of a finite sum comes out
// of it: multiplying by c keeps 0 and distributes over +, and such a map
// passes through a fold (monoidal.Homomorphic).
var ScalarLeft = scalarLeftThm{family.Add(registry.ProofEntry{
	Name: "ScalarLeft",
	Key:  "prop_97e73a4651d8ec06",
	Build: family.Theorem(
		Statement{
			Binders: "∀c:num. ∀f:(A → num). ∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "c * sum(s, f) = sum(s, λx:A. c * f(x))",
		},
		func(a *Argument, c *Expr[Nat], f *Arrow[A, Nat], s *Expr[Set[A]], finite Fact) {
			a.Do(Unfold(NatSumDef))
			scaling := a.TermAs[Fun[Nat, Nat]]("λu:num. c * u")
			keepsZero := a.Have(
				"multiplying by c keeps the element the fold starts from",
				"c * neutral_elem(+) = neutral_elem(+)",
				By(NeutralNatAdd, nat_arith.MulZero))
			keepsAddition := a.Have(
				"and distributes over addition",
				"∀u v:num. c * (u + v) = c * u + c * v",
				By(nat_arith.LeftAddDistrib))
			a.Show(
				"so it passes through the fold",
				By(finite, keepsZero, keepsAddition, MonoidalNatAdd, Where(monoidal.Homomorphic, "h", scaling)))
		}),
})}

// ---------------------------------------------------------------------------
// The ℕ-proper readings
// ---------------------------------------------------------------------------
//
// The sum below a bound reads the fold's range law at natural addition.
// A digit sum additionally uses the arithmetic of powers to split at a
// place: the index sets choose the pieces, and the powers recombine the
// shifted summands.

// BelowClauses — the empty range sums to zero, and raising the upper
// bound by one adds the new term. These are the fold's range clauses
// specialized to natural addition, whose neutral element is zero.
var BelowClauses = belowClausesThm{family.Add(registry.ProofEntry{
	Name: "BelowClauses",
	Key:  "prop_95e1894ad4a3a461",
	Build: family.Theorem(
		"∀f:(num → num). "+
			"    sum({i:num | i < 0}, f) = 0 ∧ "+
			"    ∀k:num. sum({i:num | i < suc(k)}, f) = sum({i:num | i < k}, f) + f(k)",
		func(a *Argument) {
			a.Do(Unfold(NatSumDef), By(monoidal.BelowClauses, MonoidalNatAdd, NeutralNatAdd))
		}),
})}

// DigitSumSplit — a digit sum Σ_{i∈s} B^i·b(i) over a finite set of
// places splits at any place n: the places from n on contribute a
// multiple of B^n — their digits weighted by B^(i-n) — and the places
// below n contribute as they stand.
//
// The split itself is UnionEq at the two pieces, which are disjoint and
// together are s because `n ≤ i` and `i < n` are each other's negation.
// What is proper to the digit sum is the factor B^n in front of the
// upper piece: a factor moves through a finite sum (ScalarLeft), and
// once inside it recombines with the shifted weight, B^n · B^(i-n)
// = B^i, because i - n + n = i at every place n ≤ i.
var DigitSumSplit = digitSumSplitThm{family.Add(registry.ProofEntry{
	Name: "DigitSumSplit",
	Key:  "prop_d8afe9fdd0ea907b",
	Build: family.Theorem(
		Statement{
			Binders: "∀B:num. ∀b:(num → num). ∀s:set(num). ∀n:num.",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "nat_pow(B, n) * sum({i:num | i ∈ s ∧ n ≤ i}, λi:num. nat_pow(B, i - n) * b(i)) + " +
				"sum({i:num | i ∈ s ∧ i < n}, λi:num. nat_pow(B, i) * b(i)) = " +
				"sum(s, λi:num. nat_pow(B, i) * b(i))",
			Abbrev: Abbrev{
				{Name: "upperPiece", Text: "{i:num | i ∈ s ∧ n ≤ i}"},
				{Name: "lowerPiece", Text: "{i:num | i ∈ s ∧ i < n}"},
				{Name: "digit", Text: "λi:num. nat_pow(B, i) * b(i)"},
				{Name: "shiftedDigit", Text: "λi:num. nat_pow(B, i - n) * b(i)"},
				{Name: "rescaledDigit", Text: "λi:num. nat_pow(B, n) * (nat_pow(B, i - n) * b(i))"},
			},
		},
		func(a *Argument, B *Expr[Nat], b *Arrow[Nat, Nat], s *Expr[Set[Nat]], n *Expr[Nat], finite Fact) {
			// The two pieces of s and the three summands, named once:
			// every claim below spells them this way.
			upper := a.TermAs[Set[Nat]]("«upperPiece»")
			lower := a.TermAs[Set[Nat]]("«lowerPiece»")
			weighted := a.TermAs[Fun[Nat, Nat]]("«digit»")
			shiftedWeight := a.TermAs[Fun[Nat, Nat]]("«shiftedDigit»")
			rescaledWeight := a.TermAs[Fun[Nat, Nat]]("«rescaledDigit»")
			placeWeight := a.TermAs[Nat]("nat_pow(B, n)")

			upperFinite := a.Have(
				"the upper piece is finite, being cut from s",
				"finite(«upperPiece»)",
				By(finite, At(finite_set.FiniteRestrict, s, a.Term("λi:num. n ≤ i"))))

			recombine := a.Have(
				"at every place of the upper piece the factor recombines with the shifted weight into B^i",
				"∀i:num. i ∈ «upperPiece» ⇒ nat_pow(B, n) * (nat_pow(B, i - n) * b(i)) = nat_pow(B, i) * b(i)",
				Derive(func(d *Argument) {
					i := d.FixAs[Nat]()
					inUpper := d.Assume()
					atOrAbove := d.Have(
						"a place of the upper piece is at or above n",
						"n ≤ i",
						BySets(inUpper))
					shift := d.Term("i - n")
					d.Show(
						"exponents add, and at such a place i - n + n is i",
						By(
							atOrAbove,
							At(nat_arith.PowAdd, B, n, shift), // nat_pow(B, n + (i - n)) = nat_pow(B, n) * nat_pow(B, i - n)
							At(nat_monus.SubAddCancel, i, n),  // i - n + n = i
							At(nat_arith.AddSym, n, shift),    // n + (i - n) = i - n + n
							At(nat_arith.MulAssoc, placeWeight, d.Term("nat_pow(B, i - n)"), b.Apply(i))))
				}))

			scaled := a.Have(
				"the factor B^n moves through the upper sum",
				"nat_pow(B, n) * sum(«upperPiece», «shiftedDigit») = sum(«upperPiece», «rescaledDigit»)",
				By(upperFinite, ScalarLeft.At(placeWeight, shiftedWeight, upper)))
			agree := a.Have(
				"and inside it the rescaled summand is the digit weight itself",
				"sum(«upperPiece», «rescaledDigit») = sum(«upperPiece», «digit»)",
				By(recombine, At(Congruence, upper, rescaledWeight, weighted)))

			disjoint := a.Have(
				"no place is both at or above n and below n",
				"«upperPiece» ∩ «lowerPiece» = ∅",
				BySets(nat_order.NotLessThan))
			cover := a.Have(
				"and every place of s is one or the other",
				"«upperPiece» ∪ «lowerPiece» = s",
				BySets(nat_order.NotLessThan))

			a.Show(
				"so the sum splits across the two pieces, the upper one carrying its factor",
				By(finite, scaled, agree, disjoint, cover, At(UnionEq, upper, lower, s, weighted)))
		}),
})}

// EqZero — a finite sum of naturals vanishes exactly when every term does: the
// empty sum vanishes and has no terms, and a fresh point adds its term, zero
// having only the trivial decomposition as a sum (nat_arith.AddEqZero).
var EqZero = eqZeroThm{family.Add(registry.ProofEntry{
	Name: "EqZero",
	Key:  "prop_6165553cf2d6c2ea",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(A). ∀f:(A → num).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "sum(s, f) = 0 ⇔ ∀x:A. x ∈ s ⇒ f(x) = 0",
	}, func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Nat], finite Fact) {
		a.Show(
			"so the reading holds of every finite index set, and s is one",
			ByInduction(finite_set.FiniteInductFresh, finite,
				Case(
					"the empty sum vanishes, and it has no terms",
					By(Clauses, set_basic.NotInEmpty)),
				Case(
					"a fresh point adds its term, and a sum vanishes exactly when both summands do",
					By(Clauses, nat_arith.AddEqZero, set_basic.InInsert))))
	}),
})}

// ---------------------------------------------------------------------------
// Common divisors and multiples
// ---------------------------------------------------------------------------

// DividesSum — a number dividing every term of a sum divides the
// sum: "divisible by d" holds of 0 and survives addition, so a fold of
// divisible terms is divisible (monoidal.Closed).
var DividesSum = dividesSumThm{family.Add(registry.ProofEntry{
	Name: "DividesSum",
	Key:  "prop_b862706a880f261e",
	Build: family.Theorem(
		Statement{
			Binders: "∀d:num. ∀f:(A → num). ∀s:set(A).",
			Hypotheses: []string{
				"∀x:A. x ∈ s ⇒ d ∣ f(x)",
			},
			Conclusion: "d ∣ sum(s, f)",
		},
		func(a *Argument, d *Expr[Nat], f *Arrow[A, Nat], s *Expr[Set[A]], termwise Fact) {
			// ↦ the sum read as the fold it is
			a.Do(Unfold(NatSumDef))
			dividedBy := a.TermAs[Fun[Nat, Bool]]("λu:num. d ∣ u")
			startsDivided := a.Have(
				"d divides the element the fold starts from, 0",
				"d ∣ neutral_elem(+)",
				By(NeutralNatAdd, nat_divides.DividesZero.At(d)))
			staysDivided := a.Have(
				"and a sum of two numbers it divides",
				"∀u v:num. d ∣ u ∧ d ∣ v ⇒ d ∣ u + v",
				By(nat_divides.DividesAddCancel))
			// the law asks only about the terms that are not the fold's 0
			nonzeroTerms := a.Have(
				"in particular d divides every term that is not 0",
				"∀x:A. x ∈ s ∧ f(x) ≠ neutral_elem(+) ⇒ d ∣ f(x)",
				By(termwise))
			a.Show(
				"so it divides the fold",
				By(
					nonzeroTerms,
					startsDivided,
					staysDivided,
					MonoidalNatAdd,
					Where(monoidal.Closed, "P", dividedBy)))
		}),
})}

// FinitePositiveCommonMultiple — the positive members of a finite set of
// naturals have a positive common multiple: adjoin each positive member by
// multiplying the common multiple already obtained.
var FinitePositiveCommonMultiple = finitePositiveCommonMultipleThm{family.Add(registry.ProofEntry{
	Name: "FinitePositiveCommonMultiple",
	Key:  "prop_ac3b2c51bef67b63",
	Build: family.Theorem(Statement{
		Binders:    "∀T:set(num).",
		Hypotheses: []string{"finite(T)"},
		Conclusion: "∃R:num. 0 < R ∧ (∀n:num. n ∈ T ∧ 0 < n ⇒ n ∣ R)",
	}, func(arg *Argument, T *Expr[Set[Nat]], finite Fact) {
		arg.Show(
			"finite induction builds a positive common multiple",
			ByInduction(finite_set.FiniteInduct, finite,
				Case(
					"one is a common multiple for the empty set",
					Derive(func(b *Argument) {
						b.Take(b.TermAs[Nat]("1"))
						b.Show(
							"there are no positive members to divide one",
							By(set_basic.NotInEmpty))
					})),
				Case(
					"adjoin one number to the set",
					Derive(func(b *Argument) {
						x := b.FixAs[Nat]("x")
						U := b.FixAs[Set[Nat]]("U")
						carried := b.Assume()
						r, multiple := b.UnpackAs[Nat](carried, "r")
						nonzero := b.Unless(
							b.Term("x = 0"),
							"zero imposes no additional positive divisor",
							Given(func(c *Argument, zero Fact) {
								c.Take(r)
								c.Show(
									"the old common multiple still works",
									By(multiple, zero, set_basic.InInsert, nat_order.LessThanIrrefl))
							}))
						b.Take(b.TermAs[Nat]("r * x"))
						b.Show(
							"multiply the old common multiple by the new positive member",
							SplitConj(
								Case(
									"the new common multiple is positive",
									By(nonzero, multiple, nat_order.PosIffNonzero, nat_arith.MulEqZero)),
								Case(
									"each positive member divides the enlarged product",
									Derive(func(c *Argument) {
										n := c.FixAs[Nat]("n")
										c.Show(
											"old divisors persist and the new member divides its own multiple",
											By(
												Normalized,
												multiple,
												set_basic.InInsert.At(U, x, n),
												nat_divides.DividesMul.At(n, r, x),
												nat_divides.DividesOwnMultiple.At(x, r)))
									}))))
					}))))
	}),
})}
