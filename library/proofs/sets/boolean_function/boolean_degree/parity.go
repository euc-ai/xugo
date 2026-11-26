package boolean_degree

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ToggleParity reverses cardinality parity by removing one point or inserting one.
var ToggleParity = toggleParityThm{family.Add(registry.ProofEntry{
	Name: "ToggleParity",
	Key:  "prop_bf1d3e669968e43d",
	Build: family.Theorem(Statement{
		Binders:    "∀i:A. ∀X:set(A).",
		Hypotheses: []string{"finite(X)"},
		Conclusion: "nat_even(card(set_toggle(i, X))) ⇔ ¬nat_even(card(X))",
	},
		func(a *Argument, i *Expr[A], X *Expr[Set[A]], finite Fact) {
			a.Cases(a.TermAs[Bool]("i ∈ X"))
			a.When(
				"deletion lowers the cardinality by one",
				func(b *Argument, present Fact) {
					b.Show(
						"X has one more element than the toggled set",
						By(
							finite,
							present,
							set_basic.ToggleWhenMember.At(i, X),
							cardinality.CountsOneMore.At(X, i),
							nat_parity.NatEven))
				})
			a.Otherwise(
				"insertion raises the cardinality by one",
				func(b *Argument, absent Fact) {
					b.Show(
						"the toggled set has one more element than X",
						By(
							finite,
							absent,
							set_basic.ToggleWhenAbsent.At(i, X),
							cardinality.InsertCountsOneMore.At(X, i),
							nat_parity.NatEven))
				})
		}),
})}

// InParityClass reads both conditions on an input in the chosen parity class.
var InParityClass = inParityClassThm{family.Add(registry.ProofEntry{
	Name: "InParityClass",
	Key:  "prop_4ae314c01789d1b7",
	Build: family.Theorem(
		"∀S:set(A). ∀f:(set(A) → bool). ∀b:bool. ∀X:set(A). "+
			"    X ∈ boolean_parity_class(S, f, b) ⇔ X ⊆ S ∧ ((f(X) ⇔ nat_even(card(X))) ⇔ b)",
		Chain(Unfold(ParityClassDef), BySets())),
})}

// ParityClassEdge shows that every edge internal to one class changes the Boolean value.
// The parity of the input reverses while its comparison with f stays fixed.
var ParityClassEdge = parityClassEdgeThm{family.Add(registry.ProofEntry{
	Name: "ParityClassEdge",
	Key:  "prop_e5f7c56a021f5d77",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(A). ∀f:(set(A) → bool). ∀b:bool. ∀X:set(A). ∀i:A.",
		Hypotheses: []string{
			"finite(X)",
			"X ∈ boolean_parity_class(S, f, b)",
			"set_toggle(i, X) ∈ boolean_parity_class(S, f, b)",
		},
		Conclusion: "f(X) ≠ f(set_toggle(i, X))",
	}, func(
		a *Argument,
		S *Expr[Set[A]],
		f *Arrow[Set[A], Bool],
		b *Expr[Bool],
		X *Expr[Set[A]],
		i *Expr[A],
		finite, from, to Fact,
	) {
		a.Show(
			"equal comparisons and opposite parities give opposite values",
			By(
				finite,
				from,
				to,
				InParityClass.At(S, f, b, X),
				InParityClass.At(S, f, b, a.TermAs[Set[A]]("set_toggle(i, X)")),
				ToggleParity.At(i, X)))
	}),
})}

// ParityComplement determines the parity of the omitted coordinates from the face and the input.
var ParityComplement = parityComplementThm{family.Add(registry.ProofEntry{
	Name: "ParityComplement",
	Key:  "prop_d66249cc39a8efe9",
	Build: family.Theorem(Statement{
		Binders:    "∀S X:set(A).",
		Hypotheses: []string{"finite(S)", "X ⊆ S"},
		Conclusion: "nat_even(card(S ∖ X)) ⇔ (nat_even(card(S)) ⇔ nat_even(card(X)))",
	},
		func(a *Argument, S, X *Expr[Set[A]], finite, within Fact) {
			partition := a.Have(
				"present and omitted coordinates account for the whole face",
				"card(X) + card(S ∖ X) = card(S)",
				ByArith(finite, within, cardinality.CardSubset.At(X, S), cardinality.CardDiff.At(S, X)))
			a.Show(
				"parities add modulo two",
				By(
					Normalized,
					partition,
					nat_parity.EvenAdd.At(a.TermAs[Nat]("card(X)"), a.TermAs[Nat]("card(S ∖ X)"))))
		}),
})}

// EvenComplementCounts partitions a nonempty face by the parity of the omitted coordinates.
// Its two parts are the even and odd subsets, in the order determined by the face's parity.
var EvenComplementCounts = evenComplementCountsThm{family.Add(registry.ProofEntry{
	Name: "EvenComplementCounts",
	Key:  "prop_ec2a94c47ff031d2",
	Build: family.Theorem(Statement{
		Binders:    "∀S:set(A).",
		Hypotheses: []string{"finite(S)", "S ≠ ∅"},
		Conclusion: "card(«Positive») = card(«Negative»)",
		Abbrev: Abbrev{
			{Name: "Face", Text: "{Y:set(A) | Y ⊆ S}"},
			{Name: "Positive", Text: "{X:set(A) | X ∈ «Face» ∧ nat_even(card(S ∖ X))}"},
			{Name: "Negative", Text: "{X:set(A) | X ∈ «Face» ∧ ¬nat_even(card(S ∖ X))}"},
			{Name: "Even", Text: "{X:set(A) | X ⊆ S ∧ nat_even(card(X))}"},
			{Name: "Odd", Text: "{X:set(A) | X ⊆ S ∧ nat_odd(card(X))}"},
		},
	}, func(a *Argument, S *Expr[Set[A]], finite, nonempty Fact) {
		a.Cases(a.TermAs[Bool]("nat_even(card(S))"))
		a.When(
			"an even face preserves the parity of its subsets",
			func(b *Argument, even Fact) {
				parts := b.Have(
					"the positive part consists of the even subsets",
					"«Positive» = «Even» ∧ «Negative» = «Odd»",
					BySets(finite, even, At(ParityComplement, S), nat_parity.OddIffNotEven))
				b.Show(
					"even and odd subsets have the same size",
					By(finite, nonempty, parts, nat_sum.EvenOddSubsetCounts.At(S)))
			})
		a.Otherwise(
			"an odd face reverses the parity of its subsets",
			func(b *Argument, odd Fact) {
				parts := b.Have(
					"the positive part consists of the odd subsets",
					"«Positive» = «Odd» ∧ «Negative» = «Even»",
					BySets(finite, odd, At(ParityComplement, S), nat_parity.OddIffNotEven))
				b.Show(
					"the same two counts appear in reverse order",
					By(finite, nonempty, parts, nat_sum.EvenOddSubsetCounts.At(S)))
			})
	}),
})}

// ComplementParityClass relabels the parity comparison when it counts omitted coordinates.
var ComplementParityClass = complementParityClassThm{family.Add(registry.ProofEntry{
	Name: "ComplementParityClass",
	Key:  "prop_64e6469055fc23a5",
	Build: family.Theorem(Statement{
		Binders:    "∀S:set(A). ∀f:(set(A) → bool). ∀b:bool.",
		Hypotheses: []string{"finite(S)"},
		Conclusion: "{X:set(A) | X ∈ {Y:set(A) | Y ⊆ S} ∧ ((f(X) ⇔ nat_even(card(S ∖ X))) ⇔ b)} = " +
			"boolean_parity_class(S, f, b ⇔ nat_even(card(S)))",
	},
		func(a *Argument, S *Expr[Set[A]], f *Arrow[Set[A], Bool], b *Expr[Bool], finite Fact) {
			a.Do(Unfold(ParityClassDef), Simp(Fwd(set_basic.Extension)))
			x := a.FixAs[Set[A]]("x")
			a.Cases(a.TermAs[Bool]("x ⊆ S"))
			a.When(
				"an input on the face belongs exactly when its parity comparison agrees",
				func(c *Argument, inside Fact) {
					parity := c.Have(
						"omitted coordinates use the parity of the whole face",
						"nat_even(card(S ∖ x)) ⇔ (nat_even(card(S)) ⇔ nat_even(card(x)))",
						By(finite, inside, ParityComplement.At(S, x)))
					c.Show(
						"substitute the parity of the omitted coordinates",
						By(Normalized, parity))
				})
			a.Otherwise(
				"neither class contains an input outside the face",
				func(c *Argument, outside Fact) {
					c.Show(
						"both sides require containment in S",
						BySets(Normalized, Broadcast, outside))
				})
		}),
})}
