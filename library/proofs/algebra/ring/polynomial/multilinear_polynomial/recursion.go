package multilinear_polynomial

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// MultilinearEvalInsert splits the subsets according to whether they contain the new variable.
var MultilinearEvalInsert = multilinearEvalInsertThm{family.Add(registry.ProofEntry{
	Name: "MultilinearEvalInsert",
	Key:  "prop_c7a9ece4d97dceb8",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀c:(set(B) → A). ∀S:set(B). ∀x:B.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"finite(S)",
			"x ∉ S",
			"∀T:set(B). T ⊆ insert(x, S) ⇒ c(T) ∈ R.carrier",
		},
		Conclusion: "multilinear_eval(R, c, insert(x, S)) = " +
			"multilinear_eval(R, c, S) + multilinear_eval(R, λT:set(B). c(insert(x, T)), S)",
		Abbrev: Abbrev{
			{Name: "subsets", Text: "{T:set(B) | T ⊆ S}"},
			{Name: "adjoin", Text: "λT:set(B). insert(x, T)"},
			{Name: "withX", Text: "image(«adjoin», «subsets»)"},
		},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		c *Arrow[Set[B], A],
		S *Expr[Set[B]],
		x *Expr[B],
		ring comm_ring.CommRingFact[on.R],
		finite, fresh, values Fact,
	) {
		a.Do(Unfold(MultilinearEvalDef))
		subsets := a.TermAs[Set[Set[B]]]("«subsets»")
		adjoin := a.TermAs[Fun[Set[B], Set[B]]]("«adjoin»")
		withX := a.TermAs[Set[Set[B]]]("«withX»")
		halves := a.Have(
			"the powerset splits according to the presence of x",
			"{T:set(B) | T ⊆ insert(x, S)} = «subsets» ∪ «withX»",
			// Both letters of the clauses read at B, the type of the variables: the insert
			// clause is stated at A, and a bare cite has no witness to infer B from.
			Cite(finite_set.PowersetClauses.Inst(TypeBinder.BindA[B](), TypeBinder.BindB[B]())))
		finiteSubsets := a.Have(
			"S has finitely many subsets",
			"finite(«subsets»)",
			By(finite, finite_set.FinitePowerset.At(S)))
		finiteImage := a.Have(
			"adjoining x gives another finite set of subsets",
			"finite(«withX»)",
			By(finiteSubsets, finite_set.FiniteImage.At(adjoin, subsets)))
		disjoint := a.Have(
			"only the second half contains x",
			"disjoint(«subsets», «withX»)",
			BySets(fresh))
		both := a.Have(
			"both halves index ring coefficients",
			"∀T:set(B). T ∈ «subsets» ∨ T ∈ «withX» ⇒ c(T) ∈ R.carrier",
			BySets(values, halves))
		split := a.Have(
			"sum the two halves separately",
			"module_sum(R.add, R.zero, «subsets» ∪ «withX», c) = "+
				"module_sum(R.add, R.zero, «subsets», c) + module_sum(R.add, R.zero, «withX», c)",
			By(
				finiteSubsets,
				finiteImage,
				disjoint,
				both,
				module.ModuleSumDisjointUnion.Read(module.RegularModuleOn.Read(ring)).At(subsets, withX, c)))
		raised := a.Have(
			"each enlarged subset indexes a ring coefficient",
			"∀T:set(B). T ∈ «subsets» ⇒ c(insert(x, T)) ∈ R.carrier",
			BySets(values))
		injection := a.Have(
			"removing x recovers the original subset",
			"injective_on(«subsets», «adjoin»)",
			Unfold(functions.InjectiveOnDef),
			BySets(fresh))
		reindex := a.Have(
			"enumerate the second half by subsets of S",
			"module_sum(R.add, R.zero, «withX», c) = "+
				"module_sum(R.add, R.zero, «subsets», λT:set(B). c(insert(x, T)))",
			By(
				finiteSubsets,
				injection,
				raised,
				module.ModuleSumImageMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).At(subsets, adjoin, c)))
		a.Show(
			"combine the coefficient sums with and without x",
			By(halves, split, reindex))
	}),
})}

// MultilinearCoeffInsert takes one finite difference when a variable joins the monomial.
// The subsets paired by adjoining x have opposite signs and contribute that difference.
var MultilinearCoeffInsert = multilinearCoeffInsertThm{family.Add(registry.ProofEntry{
	Name: "MultilinearCoeffInsert",
	Key:  "prop_454dd1c8ebeec1f4",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀f:(set(B) → A). ∀S:set(B). ∀x:B.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"finite(S)",
			"x ∉ S",
			"∀T:set(B). T ⊆ insert(x, S) ⇒ f(T) ∈ R.carrier",
		},
		Conclusion: "multilinear_coeff(R, f, insert(x, S)) = multilinear_coeff(R, «difference», S)",
		Abbrev: Abbrev{
			{Name: "subsets", Text: "{T:set(B) | T ⊆ S}"},
			{Name: "difference", Text: "λT:set(B). f(insert(x, T)) - f(T)"},
			{Name: "signed", Text: "λV:set(B). λg:(set(B) → A). λT:set(B). " +
				"    COND(nat_even(card(V ∖ T)), g(T), -g(T))"},
			{Name: "upper", Text: "«signed»(insert(x, S), f)"},
			{Name: "raised", Text: "λT:set(B). «upper»(insert(x, T))"},
			{Name: "paired", Text: "λT:set(B). «upper»(T) + «raised»(T)"},
			{Name: "lower", Text: "«signed»(S, «difference»)"},
		},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		f *Arrow[Set[B], A],
		S *Expr[Set[B]],
		x *Expr[B],
		ring comm_ring.CommRingFact[on.R],
		finite, fresh, values Fact,
	) {
		pointwise := a.Have(
			"pair the signed terms indexed by T and by T with x adjoined",
			"∀T:set(B). T ⊆ S ⇒ «upper»(T) + «raised»(T) = «lower»(T)",
			Derive(func(b *Argument) {
				T := b.FixAs[Set[B]]("T")
				within := b.Assume()
				missing := b.Have(
					"omitting x adds one missing variable, and adjoining x leaves the old missing variables",
					"insert(x, S) ∖ T = insert(x, S ∖ T) ∧ insert(x, S) ∖ insert(x, T) = S ∖ T ∧ x ∉ S ∖ T",
					BySets(fresh, within))
				finiteMissing := b.Have(
					"the missing variables form a finite set",
					"finite(S ∖ T)",
					By(finite, finite_set.FiniteDiff.At(S, T)))
				extra := b.Have(
					"the term omitting x has one additional missing variable",
					"card(insert(x, S) ∖ T) = suc(card(S ∖ T))",
					By(Normalized, missing, finiteMissing, cardinality.CardClauses))
				inRing := b.Have(
					"both terms in the difference are ring values",
					"f(T) ∈ R.carrier ∧ f(insert(x, T)) ∈ R.carrier",
					BySets(within, values))
				signs := b.Have(
					"the two missing-variable counts have opposite parity",
					"(nat_even(card(insert(x, S) ∖ T)) ⇔ ¬nat_even(card(S ∖ T))) ∧ "+
						"(nat_even(card(insert(x, S) ∖ insert(x, T))) ⇔ nat_even(card(S ∖ T)))",
					By(extra, missing, nat_parity.NatEven))
				b.Cases(b.Term("nat_even(card(S ∖ T))"))
				b.When(
					"an even number of missing variables gives the forward difference",
					func(c *Argument, even Fact) {
						c.Do(ByArith(ring, signs, even, inRing))
					})
				b.Otherwise(
					"an odd number gives its negative",
					func(c *Argument, odd Fact) {
						c.Do(ByArith(ring, signs, odd, inRing))
					})
			}))
		inside := a.Have(
			"changing a value's sign keeps it in the carrier",
			"∀T:set(B). T ⊆ insert(x, S) ⇒ «upper»(T) ∈ R.carrier",
			By(values, comm_ring.NegIn.Read(ring)))
		sides := a.Have(
			"both summands of each pair lie in the carrier",
			"∀T:set(B). T ∈ «subsets» ⇒ «upper»(T) ∈ R.carrier ∧ «raised»(T) ∈ R.carrier",
			BySets(inside))
		finiteSubsets := a.Have(
			"there are finitely many pairs",
			"finite(«subsets»)",
			By(finite, finite_set.FinitePowerset.At(S)))
		upper := a.TermAs[Fun[Set[B], A]]("«upper»")
		raised := a.TermAs[Fun[Set[B], A]]("«raised»")
		subsets := a.TermAs[Set[Set[B]]]("«subsets»")
		split := a.Have(
			"split the signed sum into its two coordinate slices",
			"multilinear_eval(R, «upper», insert(x, S)) = "+
				"multilinear_eval(R, «upper», S) + multilinear_eval(R, «raised», S)",
			// The evaluation's insert law is the subset sum split by the fresh x, read at the signed summand.
			By(ring, finite, fresh, inside, MultilinearEvalInsert.At(R, upper, S, x)))
		combined := a.Have(
			"the two slice sums combine term by term",
			"module_sum(R.add, R.zero, «subsets», «paired») = "+
				"module_sum(R.add, R.zero, «subsets», «upper») + module_sum(R.add, R.zero, «subsets», «raised»)",
			By(
				finiteSubsets,
				sides,
				module.ModuleSumAddMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).At(subsets, upper, raised)))
		sum := a.Have(
			"each pair contributes the signed difference",
			"module_sum(R.add, R.zero, «subsets», «paired») = module_sum(R.add, R.zero, «subsets», «lower»)",
			By(
				pointwise,
				module.ModuleSumCongruence.At(
					a.TermAs[Op[A]]("R.add"),
					a.TermAs[A]("R.zero"),
					subsets,
					a.TermAs[Fun[Set[B], A]]("«paired»"),
					a.TermAs[Fun[Set[B], A]]("«lower»"))))
		splitSum := a.Unfolded(split, MultilinearEvalDef)
		a.Do(Unfold(MultilinearCoeffDef), By(combined, sum, splitSum))
	}),
})}

// MultilinearCoeffIn keeps the alternating sum in the coefficient ring.
var MultilinearCoeffIn = multilinearCoeffInThm{family.Add(registry.ProofEntry{
	Name: "MultilinearCoeffIn",
	Key:  "prop_ae7fb9d9d7636116",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀f:(set(B) → A). ∀S:set(B).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"finite(S)",
			"∀T:set(B). T ⊆ S ⇒ f(T) ∈ R.carrier",
		},
		Conclusion: "multilinear_coeff(R, f, S) ∈ R.carrier",
		Abbrev: Abbrev{
			{Name: "signedTerm", Text: "λT:set(B). COND(nat_even(card(S ∖ T)), f(T), -f(T))"},
		},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		f *Arrow[Set[B], A],
		S *Expr[Set[B]],
		ring comm_ring.CommRingFact[on.R],
		finite, values Fact,
	) {
		a.Do(Unfold(MultilinearCoeffDef))
		terms := a.Have(
			"both possible signs give a ring value",
			"∀T:set(B). T ⊆ S ⇒ «signedTerm»(T) ∈ R.carrier",
			By(values, comm_ring.NegIn.Read(ring)))
		a.Show(
			"the finite sum is closed under addition",
			By(
				finite,
				terms,
				finite_set.FinitePowerset.At(S),
				module.ModuleSumInMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).At(
					a.TermAs[Set[Set[B]]]("{T:set(B) | T ⊆ S}"),
					a.TermAs[Fun[Set[B], A]]("«signedTerm»"))))
	}),
})}

// MultilinearEvalEmpty evaluates at the all-zero point.
var MultilinearEvalEmpty = multilinearEvalEmptyThm{family.Add(registry.ProofEntry{
	Name: "MultilinearEvalEmpty",
	Key:  "prop_d3adf6a89a0cac1c",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀c:(set(B) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"c(∅) ∈ R.carrier",
		},
		Conclusion: "multilinear_eval(R, c, ∅) = c(∅)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			c *Arrow[Set[B], A],
			ring comm_ring.CommRingFact[on.R],
			constant Fact,
		) {
			a.Do(Unfold(MultilinearEvalDef))
			only := a.Have(
				"the empty set has itself as its only subset",
				"{T:set(B) | T ⊆ ∅} ⊆ {∅} ∧ ∅ ∈ {T:set(B) | T ⊆ ∅}",
				BySets())
			a.Show(
				"the only summand is the constant coefficient",
				By(
					constant,
					only,
					module.ModuleSumSingleMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).At(
						a.TermAs[Set[Set[B]]]("{T:set(B) | T ⊆ ∅}"),
						a.TermAs[Set[B]]("∅"),
						c)))
		}),
})}

// MultilinearCoeffEmpty identifies the constant term with the value at the origin.
var MultilinearCoeffEmpty = multilinearCoeffEmptyThm{family.Add(registry.ProofEntry{
	Name: "MultilinearCoeffEmpty",
	Key:  "prop_b3242bd7c13db7a0",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀f:(set(B) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f(∅) ∈ R.carrier",
		},
		Conclusion: "multilinear_coeff(R, f, ∅) = f(∅)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			f *Arrow[Set[B], A],
			ring comm_ring.CommRingFact[on.R],
			constant Fact,
		) {
			a.Do(Unfold(MultilinearCoeffDef))
			only := a.Have(
				"the sole subset misses no variables",
				// ∅ ∖ ∅ = ∅ names no term of type set(B), so one ∅ there is pinned at B.
				"{T:set(B) | T ⊆ ∅} ⊆ {∅} ∧ ∅ ∈ {T:set(B) | T ⊆ ∅} ∧ ∅⟨A:B⟩ ∖ ∅ = ∅",
				BySets())
			positive := a.Have(
				"zero missing variables give the positive sign",
				// card(∅ ∖ ∅) names no term of type set(B), so one ∅ there is pinned at B.
				"nat_even(card(∅⟨A:B⟩ ∖ ∅))",
				// The count is of variables, not of subsets: the clauses are read at B.
				By(only, cardinality.CardClauses.Inst[B](), nat_parity.NatEven))
			a.Show(
				"the signed sum is the value at the empty set",
				By(
					constant,
					only,
					positive,
					module.ModuleSumSingleMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).At(
						a.TermAs[Set[Set[B]]]("{T:set(B) | T ⊆ ∅}"),
						a.TermAs[Set[B]]("∅"),
						a.TermAs[Fun[Set[B], A]]("λT:set(B). COND(nat_even(card(∅ ∖ T)), f(T), -f(T))"))))
		}),
})}
